module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOdd168
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Perf
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
public import CFSG.RankThree.PartOne.KF.F1322OmegaIdx
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.KF1322
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL mem_isometrySL)
open scoped MatrixGroups

theorem nonempty_ringEquiv_zmod {F : Type} [Field F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) : Nonempty (F ≃+* ZMod p) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact hp.ne_zero)
  have := Fintype.ofFinite F
  exact ⟨(ZMod.ringEquivOfPrime F hp (by rw [← Nat.card_eq_fintype_card, hF])).symm⟩

@[expose] noncomputable def slTwoEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) : SL(2, R) ≃* SL(2, S) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

theorem false_of_perfect_card_168_in_sl2 {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {F : Type} [Field F] (hF : Nat.card F = p) {G : Type} [Group G]
    {L K : Subgroup G} (hKL : K ≤ L) (eL : ↥L ≃* SL(2, F)) (hK : Group.IsPerfect K)
    (hcard : Nat.card K = 168) : False := by
  obtain ⟨e0⟩ := nonempty_ringEquiv_zmod hp hF
  have hK' := isPerfect_comap_of_le_range (φ := L.subtype) L.subtype_injective
    (by rwa [Subgroup.range_subtype]) hK
  have := hK'.1
  exact false_of_perfect_card_168_sl2 hp hp5 (eL.trans (slTwoEquivOfRingEquiv e0))
    (K := K.comap L.subtype) (by rw [hK'.2, hcard])

theorem eq_seven_of_perfect_card_168_isometrySL {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {F : Type} [Field F] (hF : Nat.card F = p)
    {R : Matrix (Fin 3) (Fin 3) F} (hRt : Rᵀ = R) (hdet : R.det ≠ 0)
    {Q : Subgroup (isometrySL R)} (hQ : Group.IsPerfect Q) (hcard : Nat.card Q = 168) :
    p = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e0⟩ := nonempty_ringEquiv_zmod hp hF
  let e1 : F →+* ZMod p := e0.toRingHom
  set M : Matrix (Fin 3) (Fin 3) (ZMod p) := R.map e1 with hM
  have hMt : Mᵀ = M := by rw [hM, ← Matrix.transpose_map, hRt]
  have hMdet : M.det ≠ 0 := by
    have h1 : M.det = e1 R.det := (RingHom.map_det e1 R).symm
    rw [h1]
    exact fun h => hdet (e0.injective (by rw [map_zero]; exact h))
  let θ : isometrySL R →* GL (Fin 3) (ZMod p) :=
    ((Matrix.SpecialLinearGroup.toGL).comp (Matrix.SpecialLinearGroup.map e1)).comp
      (isometrySL R).subtype
  have hθinj : Function.Injective θ := by
    intro g g' h
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.map_injective e0.injective
    have := congrArg (fun x : GL (Fin 3) (ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) h
    exact this
  have hθso : ∀ g : isometrySL R, θ g ∈ soGL M := by
    intro g
    refine ⟨?_, ?_⟩
    · have hg := mem_isometrySL.mp g.2
      have := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X.map e1) hg
      simpa [Matrix.map_mul, Matrix.transpose_map, hM, θ] using this
    · exact (Matrix.SpecialLinearGroup.map e1 (g : SL(3, F))).2
  have hQ2 : Group.IsPerfect (Q.map θ) := by
    have := hQ
    exact Group.IsPerfect.map _
  have hcard2 : Nat.card (Q.map θ) = 168 := by rw [Subgroup.card_map_of_injective hθinj, hcard]
  have hle : Q.map θ ≤ soGL M := by
    rintro _ ⟨g, -, rfl⟩
    exact hθso g
  have hleΩ := le_of_isPerfect_of_relindex_two hle (index_omegaGL_soGL hp5 hMt hMdet) hQ2
  obtain ⟨hperf3, hcard3⟩ := isPerfect_comap_of_le_range (omegaGL M).subtype_injective
    (by rwa [Subgroup.range_subtype]) hQ2
  obtain ⟨eΩ⟩ := nonempty_omegaGL_equiv_psl2 hp5 hMt hMdet
  have := hperf3
  exact eq_seven_of_perfect_card_168_psl2 hp (by omega) eΩ
    (K := (Q.map θ).comap (omegaGL M).subtype) (by rw [hcard3, hcard2])

end CFSG.Quasithin.SBd19F
