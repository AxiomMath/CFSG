module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCAAction
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCACent

public section

namespace CFSG.StandardType

theorem ggKGCA_abstract {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    {m : ℕ} (hm : 5 ≤ m) (hV : Module.finrank GGKGCF V = m + 2)
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (k : V ≃ₗ[GGKGCF] V)
    (hJ : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin m) GGKGCF))
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hkJ : k ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) :
    Group.IsSolvable ↥(Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) := by
  obtain ⟨hWdim, hTdim, hTfix, hWfull⟩ := ggKGCAAction hm hV J k hJ hk3 hk1 hkJ
  have hWst : ∀ a ∈ J, ∀ w ∈ ggKGCAFix k, a w ∈ ggKGCAFix k := by
    intro a ha w hw
    have hak : a * k = k * a := (Subgroup.mem_centralizer_iff.mp hkJ) a ha
    exact (ggKGCASplit_stable hak).1 w hw
  have h2 : 2 ≤ Module.finrank GGKGCF (ggKGCAFix k) := by
    rw [hWdim]
    omega
  exact ggKGCACent J (ggKGCAFix k) (ggKGCAPlane k) (ggKGCASplit_isCompl k hk3)
    hWst hTfix hWfull h2 hTdim

theorem ggKGCCentSolv_A_ge_six {n : ℕ} (hn : 6 ≤ n) :
    GGKGCCentSolv (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1)) n := by
  intro J k hJ hk3 hk1 hkJ
  let R : Type := GaloisField 2 1
  let V : Type := Fin (n + 1) → R
  let φ : Matrix.SpecialLinearGroup (Fin (n + 1)) R →* (V ≃ₗ[R] V) :=
    Matrix.SpecialLinearGroup.toLin'
  have hφinj : Function.Injective φ := Matrix.SpecialLinearGroup.toLin'_injective
  let J' : Subgroup (V ≃ₗ[R] V) := J.map φ
  have hJ' : Nonempty (↥J' ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) R) := by
    rcases hJ with ⟨e⟩
    exact ⟨(Subgroup.equivMapOfInjective J φ hφinj).symm.trans e⟩
  let k' : V ≃ₗ[R] V := φ k
  have hk'3 : k' ^ 3 = 1 := by
    dsimp only [k']
    rw [← map_pow, hk3, map_one]
  have hk'1 : k' ≠ 1 := by
    intro h
    exact hk1 (hφinj (h.trans (map_one φ).symm))
  have hk'J : k' ∈ Subgroup.centralizer (J' : Set (V ≃ₗ[R] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
    show φ b * φ k = φ k * φ b
    rw [← map_mul, ← map_mul]
    exact congrArg φ ((Subgroup.mem_centralizer_iff.mp hkJ) b hb)
  have hV : Module.finrank GGKGCF V = (n - 1) + 2 := by
    change Module.finrank R (Fin (n + 1) → R) = (n - 1) + 2
    rw [Module.finrank_fin_fun]
    omega
  have hs : Group.IsSolvable ↥(Subgroup.centralizer (J' : Set (V ≃ₗ[R] V))) :=
    ggKGCA_abstract (V := V) (m := n - 1) (by omega) hV J' k' hJ' hk'3 hk'1 hk'J
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) R) :=
    Subgroup.centralizer (J : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) R))
  let S' : Subgroup (V ≃ₗ[R] V) := Subgroup.centralizer (J' : Set (V ≃ₗ[R] V))
  have hmem : ∀ x : ↥S, φ (x : Matrix.SpecialLinearGroup (Fin (n + 1)) R) ∈ S' := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
    show φ b * φ (x : Matrix.SpecialLinearGroup (Fin (n + 1)) R) =
      φ (x : Matrix.SpecialLinearGroup (Fin (n + 1)) R) * φ b
    rw [← map_mul, ← map_mul]
    exact congrArg φ ((Subgroup.mem_centralizer_iff.mp x.2) b hb)
  let f : ↥S →* ↥S' := (φ.domRestrict S).codRestrict S' hmem
  have hfinj : Function.Injective f :=
    (MonoidHom.injective_codRestrict (φ.domRestrict S) S' hmem).mpr
      (fun x y hxy => Subtype.ext (hφinj hxy))
  haveI : Group.IsSolvable ↥S' := hs
  exact Group.isSolvable_of_isSolvable_injective (f := f) hfinj

end CFSG.StandardType

end
