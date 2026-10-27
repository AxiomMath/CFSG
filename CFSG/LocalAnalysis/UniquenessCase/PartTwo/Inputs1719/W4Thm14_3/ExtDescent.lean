module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtCoboundary
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

private theorem map_mulVec_matRep {G : Type*} [Group G] {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] {ρ : Representation (ZMod 2) G W} [Fact ρ.IsIrreducible]
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E]
    (ιD : EndRing ρ →+* E) (g : G) (x : Fin m → EndRing ρ) :
    (fun i => ιD ((matRep b g).mulVec x i)) = matRepE b ιD g (fun i => ιD (x i)) := by
  funext i
  rw [matRepE_apply]
  exact RingHom.map_mulVec ιD (matRep b g) x i

private theorem n_dvd_of_shift_card_one {n d : ℕ} {J : Finset ℕ} (hJ : J.card = 1)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J) : n ∣ d := by
  classical
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
  have hj : j < n := hJn j (Finset.mem_singleton_self j)
  have hjd : (j + d) % n = j := by simpa using hshift
  have h1 : (j + d) % n = (j + 0) % n := by rw [hjd, add_zero, Nat.mod_eq_of_lt hj]
  exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)

theorem mem_B1_of_matRepE {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) G W) [Fact ρ.IsIrreducible] {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] (ιD : EndRing ρ →+* E)
    (c : G → W) (v : Fin m → E)
    (hv : ∀ g, (fun i => ιD (b.repr (c g) i)) = matRepE b ιD g v - v) :
    c ∈ B1 ρ := by
  classical
  let _ : Algebra (EndRing ρ) E := ιD.toAlgebra
  have halg : algebraMap (EndRing ρ) E = ιD := RingHom.algebraMap_toAlgebra ιD
  have hker : LinearMap.ker (Algebra.linearMap (EndRing ρ) E) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    rw [Algebra.coe_linearMap, RingHom.algebraMap_toAlgebra] at hxy
    exact ιD.injective hxy
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hπι : ∀ d : EndRing ρ, π (ιD d) = d := fun d => by
    have h := LinearMap.congr_fun hπ d
    rw [LinearMap.comp_apply, LinearMap.id_apply, Algebra.coe_linearMap,
      RingHom.algebraMap_toAlgebra] at h
    exact h
  have hsmul : ∀ (a : EndRing ρ) (x : E), π (ιD a * x) = a * π x := by
    intro a x
    have h1 : ιD a * x = a • x := by
      rw [← halg]
      exact (Algebra.smul_def a x).symm
    rw [h1, map_smul, smul_eq_mul]
  have hvE : ∀ g : G, (fun i => ιD (b.equivFun (c g) i)) = matRepE b ιD g v - v := by
    intro g
    rw [Module.Basis.equivFun_apply]
    exact hv g
  have key : ∀ g : G, b.equivFun (c g) = (matRep b g).mulVec (fun i => π (v i)) -
      (fun i => π (v i)) := by
    intro g
    have hvec : ∀ (w : Fin m → E) (i : Fin m), π ((matRepE b ιD g w) i) =
        ((matRep b g).mulVec (fun j => π (w j))) i := by
      intro w i
      rw [matRepE_apply, Matrix.mulVec_apply_eq_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.map_apply, hsmul]
    funext i
    have h2 : ιD (b.equivFun (c g) i) = (matRepE b ιD g v) i - v i := by
      have h := congrFun (hvE g) i
      simpa using h
    have h3 : π (ιD (b.equivFun (c g) i)) = π ((matRepE b ιD g v) i) - π (v i) := by
      rw [h2, map_sub]
    rw [hπι, hvec v i] at h3
    rw [Pi.sub_apply]
    exact h3
  refine ⟨b.equivFun.symm (fun i => π (v i)), funext fun g => ?_⟩
  have hw : b.equivFun (b.equivFun.symm (fun i => π (v i))) = fun i => π (v i) :=
    LinearEquiv.apply_symm_apply _ _
  have hcoord : ∀ w : W, (matRep b g).mulVec (b.equivFun w) = b.equivFun (ρ g w) := by
    intro w
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  show ρ g (b.equivFun.symm (fun i => π (v i))) - b.equivFun.symm (fun i => π (v i)) = c g
  apply b.equivFun.injective
  rw [map_sub, ← hcoord, hw]
  exact (key g).symm

theorem isNaturalModule_of_cocycle {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ n) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) {c : SL(2, F) → W} (hc : c ∈ Z1 ρ) (hnc : c ∉ B1 ρ) :
    IsNaturalModule ρ := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent hn1 hF ρ hnt
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, _, _, _, ιF, ιD, J, hJne, hJn, hΦ, hshift, hdimJ⟩ := hdesc b
  let _ : Algebra F E := ιF.toAlgebra
  obtain ⟨Φ⟩ := hΦ
  have hk1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  rcases Nat.lt_or_ge J.card 2 with hlt | hge
  · have hk : J.card = 1 := by omega
    have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdimJ, hk]; norm_num
    have hnd : n ∣ d := n_dvd_of_shift_card_one hk hJn hshift
    exact CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_of_dvd hn1 hF ρ hnt hDcard hdim2 hnd
  · exfalso
    let c' : SL(2, F) → (J → Fin 2) → E :=
      fun g => Φ.toLinearEquiv (fun i => ιD (b.equivFun (c g) i))
    have hΦapply : ∀ (g : SL(2, F)) (x : Fin (Module.finrank (EndRing ρ) W) → E),
        Φ.toLinearEquiv (matRepE b ιD g x) = frobTensor F E J g (Φ.toLinearEquiv x) :=
      fun g x => equiv_apply Φ g x
    have hcocy : ∀ g h : SL(2, F), c' (g * h) = c' g + frobTensor F E J g (c' h) := by
      intro g h
      have hZ : c (g * h) = c g + ρ g (c h) := hc g h
      have hx : b.equivFun (c (g * h)) =
          b.equivFun (c g) + (matRep b g).mulVec (b.equivFun (c h)) := by
        have h1 : b.equivFun (ρ g (c h)) = (matRep b g).mulVec (b.equivFun (c h)) :=
          (LinearMap.toMatrix_mulVec_repr b b (repD ρ g) (c h)).symm
        rw [hZ, map_add, h1]
      have hy : (fun i => ιD (b.equivFun (c (g * h)) i)) =
          (fun i => ιD (b.equivFun (c g) i)) +
            matRepE b ιD g (fun i => ιD (b.equivFun (c h) i)) := by
        funext i
        have h1 : b.equivFun (c (g * h)) i =
            b.equivFun (c g) i + (matRep b g).mulVec (b.equivFun (c h)) i := congrFun hx i
        have h2 : ιD (b.equivFun (c g) i + (matRep b g).mulVec (b.equivFun (c h)) i) =
            ιD (b.equivFun (c g) i) +
              (matRepE b ιD g (fun i => ιD (b.equivFun (c h) i))) i := by
          rw [show ιD (b.equivFun (c g) i + (matRep b g).mulVec (b.equivFun (c h)) i) =
              ιD (b.equivFun (c g) i) + ιD ((matRep b g).mulVec (b.equivFun (c h)) i) from
            ιD.map_add' _ _]
          rw [congrFun (map_mulVec_matRep b ιD g (b.equivFun (c h))) i]
        rw [h1, h2]
        rfl
      have key : Φ.toLinearEquiv (fun i => ιD (b.equivFun (c (g * h)) i)) =
          Φ.toLinearEquiv (fun i => ιD (b.equivFun (c g) i)) +
            frobTensor F E J g (Φ.toLinearEquiv (fun i => ιD (b.equivFun (c h) i))) := by
        rw [hy, map_add (f := Φ.toLinearEquiv), hΦapply]
      exact key
    obtain ⟨v', hv'⟩ := frobTensor_cocycle_coboundary hn hF hJn hge c' hcocy
    let v : Fin (Module.finrank (EndRing ρ) W) → E := Φ.toLinearEquiv.symm v'
    have hV : Φ.toLinearEquiv v = v' := LinearEquiv.apply_symm_apply _ _
    have hconj : ∀ g : SL(2, F),
        (fun i => ιD (b.repr (c g) i)) = matRepE b ιD g v - v := by
      intro g
      have h2 : Φ.toLinearEquiv (matRepE b ιD g v - v) = c' g := by
        rw [map_sub, hΦapply, hV, hv' g]
      have h3 : Φ.toLinearEquiv (fun i => ιD (b.equivFun (c g) i)) = c' g := rfl
      have h4 : (fun i => ιD (b.equivFun (c g) i)) = matRepE b ιD g v - v := by
        apply Φ.toLinearEquiv.injective
        rw [h3, h2]
      simpa [Module.Basis.equivFun_apply] using h4
    exact hnc (mem_B1_of_matRepE ρ b ιD c v hconj)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
