module

public import CFSG.Blueprint.Catalog
import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RQuot
import CFSG.HardMathSupport.Solomon.Coordinator.L514VExpCore
import CFSG.HardMathSupport.Solomon.Proving.PSL2CentSolvableProof
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteSolv
import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U4W
import CFSG.RankThree.PartOne.K133B.Items2
import CFSG.RankThree.PartOne.KC.LinearThreeFourInnerDefining
import CFSG.RankThree.PartTwo.Sec12.Hering129KD1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup Matrix
open CFSG.Blueprint (LieModel)

theorem isSolvable_centralizer_sl_three_of_pow_eq_one {K : Type} [Field K] [Finite K] {q k : ℕ}
    (hq : q.Prime) (hK : Nat.card K = q ^ k) {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hAq : A ^ q = 1) (hA1 : A ≠ 1) :
    Group.IsSolvable ↥(centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin 3) K))) := by
  haveI := Fintype.ofFinite K
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hMq : (A : Matrix (Fin 3) (Fin 3) K) ^ q = 1 := by
    have h := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 3) K =>
      (y : Matrix (Fin 3) (Fin 3) K)) hAq
    simpa using h
  have hNq : ((A : Matrix (Fin 3) (Fin 3) K) - 1) ^ q = 0 := by
    rw [sub_pow_char_of_commute q (Commute.one_right _), hMq, one_pow, sub_self]
  have hN3 : ((A : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 :=
    CFSG.RankThree.PartOne.pow_dim_eq_zero_of_pow_eq_zero hNq
  have hN0 : (A : Matrix (Fin 3) (Fin 3) K) - 1 ≠ 0 := fun h0 =>
    hA1 (Subtype.ext (sub_eq_zero.mp h0))
  by_cases hN2 : ((A : Matrix (Fin 3) (Fin 3) K) - 1) * ((A : Matrix (Fin 3) (Fin 3) K) - 1) = 0
  · exact CFSG.RankThree.PartTwo.Sec12.Hering129KD1.isSolvable_centralizer_of_sq_eq_zero hq hK
      hN2 hN0
  · obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, ((A : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ
        (((A : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ v) ≠ 0 := by
      by_contra h
      push Not at h
      apply hN2
      ext i j
      have h' := congrFun (h (Pi.single j 1)) i
      rw [Matrix.mulVec_mulVec] at h'
      simpa [Matrix.mulVec_single_one] using h'
    exact CFSG.RankThree.PartTwo.Sec12.Hering129KD1.isSolvable_centralizer_of_isUnit_det_krylov
      (CFSG.RankThree.PartTwo.Sec12.Hering129KD1.isUnit_det_krylov_of_nilpotent hN3 hv)

theorem isSolvable_centralizer_statedProj_three {K : Type} [Field K] [Finite K] {q k : ℕ}
    (hq : q.Prime) (hq3 : q ≠ 3) (hK : Nat.card K = q ^ k) {H₀ : Subgroup (GL (Fin 3) K)}
    (hH₀ : H₀ ≤ StatedSL 3 K) {x : StatedProj H₀} (hx : orderOf x = q) :
    Group.IsSolvable ↥(centralizer ({x} : Set (StatedProj H₀))) := by
  have hq3' : ¬ q ∣ 3 := fun h => hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)
  set N := (StatedScalars (Fin 3) K).subgroupOf H₀
  have hsc : ∀ z ∈ N, z ^ 3 = 1 := fun z hz => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact StatedAPI.pow_three_eq_one_of_mem_statedScalars (Subgroup.mem_subgroupOf.1 hz)
      (StatedAPI.det_of_mem_statedSL (hH₀ z.2)))
  have hZ : Nat.Coprime (Nat.card N) q := ((Nat.Prime.coprime_iff_not_dvd hq).2
    (StatedAPI.not_dvd_card_statedScalars_subgroupOf H₀ hq hq3' fun c hc =>
      CFSG.RankThree.PartOne.K133B.scalar_pow_of_mem_statedSL c (hH₀ hc))).symm
  obtain ⟨u, rfl, huq⟩ := CFSG.OddStandard.GH71.S55.C5U.exists_lift_pow_eq_one hq hsc hq3'
    (hx ▸ pow_orderOf_eq_one x)
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [QuotientGroup.mk_one, orderOf_one] at hx
    exact hq.one_lt.ne hx
  let ι : ↥H₀ →* Matrix.SpecialLinearGroup (Fin 3) K :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.toMonoidHom.comp
      (Subgroup.inclusion hH₀)
  have hι : Function.Injective ι :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.injective.comp
      (Subgroup.inclusion_injective hH₀)
  have hιq : ι u ^ q = 1 := by rw [← map_pow, huq, map_one]
  have hι1 : ι u ≠ 1 := fun h => hu1 (hι (h.trans (map_one ι).symm))
  haveI := isSolvable_centralizer_sl_three_of_pow_eq_one hq hK hιq hι1
  let φ : ↥(centralizer ({u} : Set ↥H₀)) →*
      ↥(centralizer ({ι u} : Set (Matrix.SpecialLinearGroup (Fin 3) K))) :=
    (ι.comp (centralizer ({u} : Set ↥H₀)).subtype).codRestrict _ fun c => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, ← map_mul, h]
  haveI : Group.IsSolvable ↥(centralizer ({u} : Set ↥H₀)) :=
    Group.isSolvable_of_isSolvable_injective (f := φ) fun a b hab =>
      Subtype.ext (hι (congrArg Subtype.val hab))
  haveI : Group.IsSolvable ↥((centralizer ({u} : Set ↥H₀)).map (QuotientGroup.mk' N)) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  have hle : centralizer ({(u : StatedProj H₀)} : Set (StatedProj H₀)) ≤
      (centralizer ({u} : Set ↥H₀)).map (QuotientGroup.mk' N) := by
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine Subgroup.mem_map.2 ⟨g, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    exact (CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.commute_of_mk_commute N
      (StatedAPI.statedScalars_subgroupOf_le_center H₀) hZ (k := 1) (by rw [pow_one]; exact huq)
      (Subgroup.mem_centralizer_singleton_iff.1 hy).symm).symm
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem isSolvable_centralizer_of_lieModel {Λ : Type} [Group Λ] {q f : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3)
    (h : LieModel Λ .PSL 2 q f ∨ LieModel Λ .PSL 3 q f ∨ LieModel Λ .PSU 3 q f)
    {u : Λ} (hu : orderOf u = q) : Group.IsSolvable ↥(centralizer ({u} : Set Λ)) := by
  rcases h with h | h | h
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
    refine CFSG.ComponentClassification.AutL2Facts.isSolvable_centralizer_of_equiv e u
      (CFSG.HardMathSupport.Solomon.Coordinator.l514vexp_centSolvable
        CFSG.HardMathSupport.Solomon.Proving.psl2CentSolvable_holds fun h1 => ?_)
    rw [← MulEquiv.orderOf_eq e, h1, orderOf_one] at hu
    exact hq.one_lt.ne hu
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
    exact CFSG.ComponentClassification.AutL2Facts.isSolvable_centralizer_of_equiv e u
      (isSolvable_centralizer_statedProj_three hq hq3 hK le_rfl
        (by rw [MulEquiv.orderOf_eq]; exact hu))
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
    exact CFSG.ComponentClassification.AutL2Facts.isSolvable_centralizer_of_equiv e u
      (isSolvable_centralizer_statedProj_three hq hq3 (k := f * 2) (by rw [hK, ← pow_mul])
        (StatedAPI.statedSU_le_statedSL 3 (q ^ f) K) (by rw [MulEquiv.orderOf_eq]; exact hu))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
