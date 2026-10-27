module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLift
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestMult
public import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.PartOne.LSTD.ClsB
public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.Universal
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.PartOne.CTP.ExtPhan
public import CFSG.RankThree.PartOne.CTP.Frame1214
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.R12Final
public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.LSTD.StdFam
public import CFSG.RankThree.PartOne.LSTD.Transport
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

namespace StdSubRestThree

section Groups

variable {G : Type} [Group G]

theorem exists_ne_comm_of_isQuasisimple {D : Subgroup G} (hD : CFSG.IsQuasisimple D) :
    ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hD
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', a'.2, b', b'.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h

theorem commute_of_commutator_central {D : Subgroup G} (hD : ⁅D, D⁆ = D) {b : G}
    (hbD : ∀ y ∈ D, b * y * b⁻¹ ∈ D)
    (hc : ∀ y ∈ D, ∀ z ∈ D, (b * y * b⁻¹ * y⁻¹) * z = z * (b * y * b⁻¹ * y⁻¹)) :
    ∀ y ∈ D, b * y = y * b := by
  set T : Subgroup G := Subgroup.centralizer ({b} : Set G) with hT
  have hle : ⁅D, D⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    rw [hT, Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
    set c₁ := b * y₁ * b⁻¹ * y₁⁻¹ with hc₁
    set c₂ := b * y₂ * b⁻¹ * y₂⁻¹ with hc₂
    have e1 : b * y₁ * b⁻¹ = c₁ * y₁ := by rw [hc₁]; group
    have e2 : b * y₂ * b⁻¹ = c₂ * y₂ := by rw [hc₂]; group
    have k11 := hc y₁ hy₁ y₁ hy₁
    have k12 := hc y₁ hy₁ y₂ hy₂
    have k21 := hc y₂ hy₂ y₁ hy₁
    have k22 := hc y₂ hy₂ y₂ hy₂
    have hc₂D : c₂ ∈ D := D.mul_mem (hbD y₂ hy₂) (D.inv_mem hy₂)
    have k1c := hc y₁ hy₁ c₂ hc₂D
    rw [← hc₁] at k11 k12 k1c
    rw [← hc₂] at k21 k22
    have hconj : b * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * b⁻¹ =
        (b * y₁ * b⁻¹) * (b * y₂ * b⁻¹) * (b * y₁ * b⁻¹)⁻¹ * (b * y₂ * b⁻¹)⁻¹ := by group
    have hval : (c₁ * y₁) * (c₂ * y₂) * (c₁ * y₁)⁻¹ * (c₂ * y₂)⁻¹ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
      have k21' : y₁ * c₂ = c₂ * y₁ := k21.symm
      calc (c₁ * y₁) * (c₂ * y₂) * (c₁ * y₁)⁻¹ * (c₂ * y₂)⁻¹
          = c₁ * (y₁ * c₂) * y₂ * y₁⁻¹ * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * (c₂ * y₁) * y₂ * y₁⁻¹ * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by rw [k21']
        _ = c₁ * c₂ * (y₁ * y₂ * y₁⁻¹) * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by group
        _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
          have m1 : c₁ * (y₁ * y₂ * y₁⁻¹) = (y₁ * y₂ * y₁⁻¹) * c₁ := by
            have hy : y₁ * y₂ * y₁⁻¹ ∈ D := D.mul_mem (D.mul_mem hy₁ hy₂) (D.inv_mem hy₁)
            exact (hc y₁ hy₁ _ hy).trans rfl
          have m2 : c₂ * (y₁ * y₂ * y₁⁻¹) = (y₁ * y₂ * y₁⁻¹) * c₂ := by
            have hy : y₁ * y₂ * y₁⁻¹ ∈ D := D.mul_mem (D.mul_mem hy₁ hy₂) (D.inv_mem hy₁)
            exact hc y₂ hy₂ _ hy
          have m3 : c₁ * y₂⁻¹ = y₂⁻¹ * c₁ := by
            have := hc y₁ hy₁ _ (D.inv_mem hy₂)
            exact this
          have m4 : c₂ * y₂⁻¹ = y₂⁻¹ * c₂ := hc y₂ hy₂ _ (D.inv_mem hy₂)
          calc c₁ * c₂ * (y₁ * y₂ * y₁⁻¹) * c₁⁻¹ * y₂⁻¹ * c₂⁻¹
              = c₁ * (c₂ * (y₁ * y₂ * y₁⁻¹)) * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by group
            _ = c₁ * ((y₁ * y₂ * y₁⁻¹) * c₂) * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by rw [m2]
            _ = (c₁ * (y₁ * y₂ * y₁⁻¹)) * c₂ * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by group
            _ = ((y₁ * y₂ * y₁⁻¹) * c₁) * c₂ * c₁⁻¹ * y₂⁻¹ * c₂⁻¹ := by rw [m1]
            _ = (y₁ * y₂ * y₁⁻¹) * (c₁ * c₂ * c₁⁻¹) * y₂⁻¹ * c₂⁻¹ := by group
            _ = (y₁ * y₂ * y₁⁻¹) * c₂ * y₂⁻¹ * c₂⁻¹ := by
                rw [show c₁ * c₂ * c₁⁻¹ = c₂ from by rw [k1c]; group]
            _ = (y₁ * y₂ * y₁⁻¹) * (c₂ * y₂⁻¹) * c₂⁻¹ := by group
            _ = (y₁ * y₂ * y₁⁻¹) * (y₂⁻¹ * c₂) * c₂⁻¹ := by rw [m4]
            _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by group
    symm
    calc b * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)
        = b * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * b⁻¹ * b := by group
      _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ * b := by rw [hconj, e1, e2, hval]
  intro y hy
  have hyT : y ∈ T := hle (hD.symm ▸ hy)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyT).symm

theorem le_or_commute_of_quasisimple {C D B : Subgroup G} (hDC : D ≤ C) (hBC : B ≤ C)
    (hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) (hBn : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hD : CFSG.IsQuasisimple D) : D ≤ B ∨ ∀ d ∈ D, ∀ b ∈ B, d * b = b * d := by
  set N := (D ⊓ B).subgroupOf D with hN
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · show ((g : G) * n * (g : G)⁻¹) ∈ D
      exact D.mul_mem (D.mul_mem g.2 hn.1) (D.inv_mem g.2)
    · show ((g : G) * n * (g : G)⁻¹) ∈ B
      exact hBn g (hDC g.2) n hn.2
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hD hNn with h | h
  · left
    intro d hd
    have h1 : (⟨d, hd⟩ : D) ∈ N := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp h1).2
  · right
    intro d hd b hb
    have hperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hD.1
    have hbD : ∀ y ∈ D, b * y * b⁻¹ ∈ D := fun y hy => hDn b (hBC hb) y hy
    have hcen : ∀ y ∈ D, ∀ z ∈ D, (b * y * b⁻¹ * y⁻¹) * z = z * (b * y * b⁻¹ * y⁻¹) := by
      intro y hy z hz
      have hmD : b * y * b⁻¹ * y⁻¹ ∈ D := D.mul_mem (hbD y hy) (D.inv_mem hy)
      have hmB : b * y * b⁻¹ * y⁻¹ ∈ B := by
        have h1 : y * b⁻¹ * y⁻¹ ∈ B := hBn y (hDC hy) b⁻¹ (B.inv_mem hb)
        have h2 := B.mul_mem hb h1
        rwa [show b * (y * b⁻¹ * y⁻¹) = b * y * b⁻¹ * y⁻¹ by group] at h2
      have h3 : (⟨_, hmD⟩ : D) ∈ Subgroup.center D :=
        h (Subgroup.mem_subgroupOf.mpr ⟨hmD, hmB⟩)
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp h3 ⟨z, hz⟩)).symm
    exact (commute_of_commutator_central hperf hbD hcen d hd).symm

theorem eq_of_le_of_quasisimple {D B : Subgroup G} (hDB : D ≤ B)
    (hBn : ∀ b ∈ B, ∀ d ∈ D, b * d * b⁻¹ ∈ D) (hB : CFSG.IsQuasisimple B)
    (hD : CFSG.IsQuasisimple D) : D = B := by
  set N := D.subgroupOf B with hN
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact hBn g g.2 n hn
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hB hNn with h | h
  · refine le_antisymm hDB fun b hb => ?_
    have h1 : (⟨b, hb⟩ : B) ∈ N := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h1
  · exfalso
    obtain ⟨a, ha, c, hc, hac⟩ := exists_ne_comm_of_isQuasisimple hD
    have h1 : (⟨a, hDB ha⟩ : B) ∈ Subgroup.center B := h (Subgroup.mem_subgroupOf.mpr ha)
    exact hac (congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨c, hDB hc⟩)).symm

end Groups

end StdSubRestThree

namespace StdSubRestThreeU

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2 TableBUE IOneU
  StdSubRestU StdSubRestThree

section Diag

variable {K : Type} [Field K] [Finite K] {d : ℕ} (h : UnitaryFieldData 2 1 K)

theorem projMk_injective_four (hK : Nat.card K = (2 ^ 1) ^ 2) (hd : ¬ 3 ∣ d) :
    Function.Injective (LargeEvenProjMk (unitarySU 2 1 K d)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [LargeEvenProjMk, QuotientGroup.ker_mk']
  exact TableBUR.suScalars_eq_bot_four hK hd

omit [Finite K] in
theorem commute_of_offDiag_eq_zero {M N : Matrix (Fin d) (Fin d) K}
    (hM : ∀ i j, i ≠ j → M i j = 0) (hN : ∀ i j, i ≠ j → N i j = 0) : M * N = N * M := by
  have eM : M = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hM i j hij]
  have eN : N = Matrix.diagonal fun i => N i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hN i j hij]
  rw [eM, eN, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

include h in
theorem eltSmall_diag_two (hK : Nat.card K = (2 ^ 1) ^ 2) (hd3 : ¬ 3 ∣ d) (hd5 : 5 ≤ d)
    {A : Subgroup ↥(unitarySU 2 1 K d)} (hA : IsElemAbelian 3 A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ)
    (hcard : 3 ^ (d - 2) ≤ Nat.card A) {s t : Fin d} (hst : s ≠ t)
    (hpair : ∀ σ ∈ diagVec A, σ s = σ t) {x : ↥(unitarySU 2 1 K d)} (hxA : x ∈ A)
    (hx1 : LargeEvenProjMk (unitarySU 2 1 K d) x ≠ 1)
    {D : Subgroup (LargeEvenProj (unitarySU 2 1 K d))}
    (hDC : D ≤ Subgroup.centralizer
      ({LargeEvenProjMk (unitarySU 2 1 K d) x} : Set (LargeEvenProj (unitarySU 2 1 K d))))
    (hDn : ∀ c ∈ Subgroup.centralizer
      ({LargeEvenProjMk (unitarySU 2 1 K d) x} : Set (LargeEvenProj (unitarySU 2 1 K d))),
      ∀ e ∈ D, c * e * c⁻¹ ∈ D)
    (hDq : CFSG.IsQuasisimple D)
    (hprov : ∀ b ∈ A.map (LargeEvenProjMk (unitarySU 2 1 K d)), (∀ e ∈ D, b * e = e * b) →
      b ∈ Subgroup.zpowers (LargeEvenProjMk (unitarySU 2 1 K d) x))
    (hsm : ∀ E : Subgroup (LargeEvenProj (unitarySU 2 1 K d)), IsElemAbelian 3 E → E ≤ D →
      E ≤ A.map (LargeEvenProjMk (unitarySU 2 1 K d)) → Nat.card E < 3 ^ 3) :
    ∃ U : Subgroup (LargeEvenProj (unitarySU 2 1 K d)), U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ b ∈ A.map (LargeEvenProjMk (unitarySU 2 1 K d)), ∀ u ∈ U, b * u * b⁻¹ ∈ U) ∧
      ∃ y ∈ D, y ^ 3 = 1 ∧
        (∀ b ∈ A.map (LargeEvenProjMk (unitarySU 2 1 K d)), b * y = y * b) ∧
        y ∈ Subgroup.normalizer (U : Set (LargeEvenProj (unitarySU 2 1 K d))) ∧
        ∃ j ∈ D, y * j ≠ j * y := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 1 K d) with hπ
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hpK := dvd_card_sub_one hK hpq
  set W := diagVec A with hW
  have hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity 3 K := fun σ hσ k => by
    rw [mem_rootsOfUnity]
    exact (diagVec_props h hA hσ).1 k
  have hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1 := fun σ hσ => (diagVec_props h hA hσ).2
  have hWc : 3 ^ (d - 2) ≤ Nat.card W := by
    rw [hW, card_diagVec hdiag]
    exact hcard
  have hnp : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hd3 hz hzp
  have hker := ker_projMk_le_center (n := 1) (d := d) (K := K)
  have hπinj : Function.Injective π := projMk_injective_four hK hd3
  have hinj : ∀ y ∈ A, π y = 1 → y = 1 := fun y _ hy1 => hπinj (hy1.trans (map_one π).symm)
  obtain ⟨σx, hσx⟩ := hdiag x hxA
  have hσxW : σx ∈ W := mem_diagVec_of hxA hσx
  have hσxp : ∀ k, σx k ^ 3 = 1 := fun k => by
    have h1 := hWp σx hσxW k
    rwa [mem_rootsOfUnity] at h1
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one h hp hpq
  have hζp : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hζroot : ζ ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    exact hζp
  have hζinv : ζ ≠ ζ⁻¹ := by
    intro he
    have h2 : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ * ζ := sq ζ
        _ = ζ * ζ⁻¹ := by rw [← he]
        _ = 1 := mul_inv_cancel ζ
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [hζo] at h4
    omega
  have hζQ : ∀ k : Fin d, ∀ τ : Fin d → Kˣ, (∀ k, τ k ∈ rootsOfUnity 3 K) →
      τ k ^ (2 ^ 1 + 1) = 1 := fun k τ hτ => by
    have h1 := hτ k
    rw [mem_rootsOfUnity] at h1
    exact h1
  set Sof : Fin d → Finset (Fin d) := fun k => Finset.univ.filter fun j => σx j = σx k
    with hSof
  have hmemS : ∀ k j, j ∈ Sof k ↔ σx j = σx k := fun k j => by simp [hSof]
  have hSeig : ∀ k, ∀ i ∈ Sof k, ∀ j, j ∈ Sof k ↔ σx j = σx i := fun k i hi j => by
    rw [hmemS, (hmemS k i).mp hi]
  have hSconst : ∀ k, ∀ i ∈ Sof k, ∀ j ∈ Sof k, σx i = σx j := fun k i hi j hj => by
    rw [(hmemS k i).mp hi, (hmemS k j).mp hj]
  have hC := centralizer_map_eq_of_noTorsion π (QuotientGroup.mk'_surjective _) hker hnp
    (hA.2 x hxA)
  set B : Fin d → Subgroup (LargeEvenProj (unitarySU 2 1 K d)) := fun k =>
    (blockSU (Sof k)).map π with hB
  have hBC : ∀ k, B k ≤ Subgroup.centralizer ({π x} : Set (LargeEvenProj (unitarySU 2 1 K d))) := by
    intro k
    rintro _ ⟨y, hy, rfl⟩
    have h1 := blockSU_le_centralizer (hSconst k) hσx hy
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    rw [← map_mul, ← map_mul, h1]
  have hBn : ∀ k, ∀ c ∈ Subgroup.centralizer ({π x} : Set (LargeEvenProj (unitarySU 2 1 K d))),
      ∀ b ∈ B k, c * b * c⁻¹ ∈ B k := by
    intro k c hc b hb
    rw [hC] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨g * y * g⁻¹, conj_mem_blockSU_of_commute hσx hg (hSeig k) hy, by
      simp only [map_mul, map_inv]⟩
  have hex : ∃ k, D ≤ B k := by
    by_contra hno
    push Not at hno
    have hcomm : ∀ k, ∀ e ∈ D, ∀ b ∈ B k, e * b = b * e := fun k =>
      (le_or_commute_of_quasisimple hDC (hBC k) hDn (hBn k) hDq).resolve_left (hno k)
    have hdg : ∀ e ∈ D, ∃ g : ↥(unitarySU 2 1 K d), π g = e ∧
        ∀ i j, i ≠ j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
      intro e he
      have he' := hDC he
      rw [hC] at he'
      obtain ⟨g, hg, rfl⟩ := he'
      refine ⟨g, rfl, fun i j hij => ?_⟩
      by_cases hσij : σx i = σx j
      · set τ : Fin d → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹ with hτ
        have hτi : τ i = ζ := by
          simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one]
        have hτj : τ j = ζ⁻¹ := by
          simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm,
            one_mul]
        have hτroot : ∀ k, τ k ∈ rootsOfUnity 3 K := fun k => by
          simp only [hτ, Pi.mul_apply]
          exact (rootsOfUnity 3 K).mul_mem (mulSingle_mem hζroot k)
            (mulSingle_mem ((rootsOfUnity 3 K).inv_mem hζroot) k)
        have hτprod : ∏ k, τ k = 1 := by
          simp only [hτ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
          group
        set y : ↥(unitarySU 2 1 K d) :=
          ⟨diagHom d τ, diagHom_mem_unitarySU h (fun k => hζQ k τ hτroot) hτprod⟩ with hy
        have hjS : j ∈ Sof i := (hmemS i j).mpr hσij.symm
        have hyB : y ∈ blockSU (Sof i) := isBlockOn_diagHom fun k hk => by
          have hki : k ≠ i := fun h' => hk (h' ▸ (hmemS i i).mpr rfl)
          have hkj : k ≠ j := fun h' => hk (h' ▸ hjS)
          simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj,
            mul_one]
        have hc1 := hcomm i (π g) he (π y) ⟨y, hyB, rfl⟩
        have hgy : g * y = y * g := hπinj (by rw [map_mul, map_mul, hc1])
        have hgy' : (g : GL (Fin d) K) * diagHom d τ = diagHom d τ * g :=
          congrArg Subtype.val hgy
        exact entry_eq_zero_of_commute hgy' (by rw [hτi, hτj]; exact hζinv)
      · have hgx : (g : GL (Fin d) K) * diagHom d σx = diagHom d σx * g := by
          rw [← hσx]
          exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
        exact entry_eq_zero_of_commute hgx hσij
    obtain ⟨a₁, ha₁, a₂, ha₂, hne⟩ := exists_ne_comm_of_isQuasisimple hDq
    obtain ⟨g₁, rfl, hg₁⟩ := hdg a₁ ha₁
    obtain ⟨g₂, rfl, hg₂⟩ := hdg a₂ ha₂
    apply hne
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact commute_of_offDiag_eq_zero hg₁ hg₂
  obtain ⟨k, hDk⟩ := hex
  set S := Sof k with hSdef
  have hkS : k ∈ S := (hmemS k k).mpr rfl
  have hcommD : ∀ τ ∈ W, (∀ i ∈ S, ∀ j ∈ S, τ i = τ j) → ∃ m : ℤ, τ = σx ^ m := by
    intro τ hτW hτS
    obtain ⟨y, hyA, hyτ⟩ := mem_diagVec.mp hτW
    have hyD : ∀ e ∈ D, π y * e = e * π y := by
      intro e he
      obtain ⟨z, hz, rfl⟩ := hDk he
      rw [← map_mul, ← map_mul, (commute_blockSU_iff h hyτ).mpr hτS z hz]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hprov _ ⟨y, hyA, rfl⟩ hyD)
    refine ⟨m, ?_⟩
    have h1 : y = x ^ m := by
      have h2 : π (y * (x ^ m)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hm, mul_inv_cancel]
      have h3 := hinj _ (A.mul_mem hyA (A.inv_mem (A.zpow_mem hxA m))) h2
      exact mul_inv_eq_one.mp h3
    apply diagHom_injective d
    rw [← hyτ, h1, Subgroup.coe_zpow, hσx, map_zpow]
  have hDeq : 4 ≤ S.card → D = B k := by
    intro hS4
    have hBq : CFSG.IsQuasisimple (B k) := (TableBSymp.isQuasisimple_iff _).mp
      (SUTorus.isQuasisimple_map_blockSU h hker (show 3 ≤ (Sof k).card by rw [← hSdef]; omega)
        (by
          intro he
          have h1 := congrArg Prod.fst he
          simp only at h1
          rw [← hSdef] at h1
          omega))
    exact eq_of_le_of_quasisimple hDk (fun b hb e he => hDn b (hBC k hb) e he) hBq hDq
  by_cases hsS : s ∈ S
  · have htS : t ∈ S :=
      (hmemS k t).mpr ((hpair σx hσxW).symm.trans ((hmemS k s).mp hsS))
    have hone : ∀ k₁ k₂, k₁ ∉ S → k₂ ∉ S → k₁ = k₂ := by
      intro k₁ k₂ h1 h2
      by_contra h12
      have hk1t : k₁ ≠ t := fun h' => h1 (h' ▸ htS)
      have hk2t : k₂ ≠ t := fun h' => h2 (h' ▸ htS)
      have hsk1 : s ≠ k₁ := fun h' => h1 (h' ▸ hsS)
      have hsk2 : s ≠ k₂ := fun h' => h2 (h' ▸ hsS)
      obtain ⟨τ₁, hτ₁W, hτ₁⟩ := exists_mem_of_pair hp hpK hWp hW1 hst hsk2 hk2t hpair hWc
        (Pi.mulSingle k₁ ζ) (mulSingle_mem hζroot)
      obtain ⟨τ₃, hτ₃W, hτ₃⟩ := exists_mem_of_pair hp hpK hWp hW1 hst hsk1 hk1t hpair hWc
        (fun k => if k ∈ S then ζ else 1) (fun k => by
          split_ifs
          · exact hζroot
          · exact (rootsOfUnity 3 K).one_mem)
      have hτ₁S : ∀ i ∈ S, τ₁ i = 1 := by
        intro i hi
        have hsF : s ∈ freeSet t k₂ := mem_freeSet_iff.mpr ⟨hsk2, hst⟩
        by_cases hit : i = t
        · rw [hit, ← hpair τ₁ hτ₁W, hτ₁ s hsF, Pi.mulSingle_eq_of_ne hsk1]
        · have hik2 : i ≠ k₂ := fun h' => h2 (h' ▸ hi)
          have hik1 : i ≠ k₁ := fun h' => h1 (h' ▸ hi)
          rw [hτ₁ i (mem_freeSet_iff.mpr ⟨hik2, hit⟩), Pi.mulSingle_eq_of_ne hik1]
      have hτ₃S : ∀ i ∈ S, τ₃ i = ζ := by
        intro i hi
        have hsF : s ∈ freeSet t k₁ := mem_freeSet_iff.mpr ⟨hsk1, hst⟩
        by_cases hit : i = t
        · rw [hit, ← hpair τ₃ hτ₃W, hτ₃ s hsF]
          simp [hsS]
        · have hik1 : i ≠ k₁ := fun h' => h1 (h' ▸ hi)
          rw [hτ₃ i (mem_freeSet_iff.mpr ⟨hik1, hit⟩)]
          simp [hi]
      have hτ₁k : τ₁ k₁ = ζ := by
        rw [hτ₁ k₁ (mem_freeSet_iff.mpr ⟨h12, hk1t⟩), Pi.mulSingle_eq_same]
      obtain ⟨m₁, hm₁⟩ := hcommD τ₁ hτ₁W fun i hi j hj => by rw [hτ₁S i hi, hτ₁S j hj]
      obtain ⟨m₃, hm₃⟩ := hcommD τ₃ hτ₃W fun i hi j hj => by rw [hτ₃S i hi, hτ₃S j hj]
      have hs1 : σx s = 1 := by
        refine eq_one_of_zpow_of_zpow_ne hp (b := σx k₁) (m := m₁) (hσxp s) (hσxp k₁) ?_ ?_
        · have e1 := congrFun hm₁ s
          rw [Pi.pow_apply, hτ₁S s hsS] at e1
          exact e1.symm
        · have e1 := congrFun hm₁ k₁
          rw [Pi.pow_apply, hτ₁k] at e1
          rw [← e1]
          exact hζ1
      apply hζ1
      have e1 := congrFun hm₃ s
      rw [Pi.pow_apply, hτ₃S s hsS, hs1, _root_.one_zpow] at e1
      exact e1
    have hex : ∃ c', c' ∉ S := by
      by_contra hall
      push Not at hall
      exact hx1 (projMk_eq_one_of_const hσx (u := σx s) fun i =>
        ((hmemS k i).mp (hall i)).trans ((hmemS k s).mp hsS).symm)
    obtain ⟨c', hc'⟩ := hex
    have hc's : c' ≠ s := fun h' => hc' (h' ▸ hsS)
    have hc't : c' ≠ t := fun h' => hc' (h' ▸ htS)
    have hnotS : ∀ k, k ∉ S ↔ k = c' := fun k =>
      ⟨fun hk => hone k c' hk hc', fun hk => hk ▸ hc'⟩
    have hScard : S.card = d - 1 := by
      have h1 : S = Finset.univ.erase c' := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hk h'
          exact (hnotS k).mpr h' hk
        · intro hk
          by_contra hkS
          exact hk ((hnotS k).mp hkS)
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ c'), Finset.card_univ, Fintype.card_fin]
    set T := (S.erase s).erase t with hT
    have hTcard : 2 ≤ T.card := by
      rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hst.symm, htS⟩),
        Finset.card_erase_of_mem hsS, hScard]
      omega
    obtain ⟨c, hcT, e, heT, hce⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have hcS : c ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcT)
    have heS : e ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heT)
    have hct : c ≠ t := Finset.ne_of_mem_erase hcT
    have hcs : c ≠ s := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcT)
    have het : e ≠ t := Finset.ne_of_mem_erase heT
    have hes : e ≠ s := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase heT)
    have hc'c : c' ≠ c := fun h' => hc' (h' ▸ hcS)
    set τ : Fin d → Kˣ := Pi.mulSingle s ζ * Pi.mulSingle t ζ * Pi.mulSingle c (ζ⁻¹ ^ 2) with hτ
    have hτs : τ s = ζ := by
      simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hst,
        Pi.mulSingle_eq_of_ne hcs.symm, mul_one]
    have hτt : τ t = ζ := by
      simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hst.symm,
        Pi.mulSingle_eq_of_ne hct.symm, mul_one, one_mul]
    have hτc : τ c = ζ⁻¹ ^ 2 := by
      simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hcs,
        Pi.mulSingle_eq_of_ne hct, one_mul]
    have hτe : τ e = 1 := by
      simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hes, Pi.mulSingle_eq_of_ne het,
        Pi.mulSingle_eq_of_ne hce.symm, one_mul]
    have hτc' : τ c' = 1 := by
      simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hc's, Pi.mulSingle_eq_of_ne hc't,
        Pi.mulSingle_eq_of_ne hc'c, one_mul]
    have hζQ : ζ ∈ rootsOfUnity (2 ^ 1 + 1) K := by
      rw [mem_rootsOfUnity]
      exact hζq
    have hτmem : ∀ X : Subgroup Kˣ, ζ ∈ X → ∀ k, τ k ∈ X := fun X hX k => by
      simp only [hτ, Pi.mul_apply]
      exact X.mul_mem (X.mul_mem (mulSingle_mem hX k) (mulSingle_mem hX k))
        (mulSingle_mem (X.pow_mem (X.inv_mem hX) 2) k)
    have hτq : ∀ k, τ k ^ (2 ^ 1 + 1) = 1 := fun k => by
      have h1 := hτmem _ hζQ k
      rwa [mem_rootsOfUnity] at h1
    have hτp : τ ^ 3 = 1 := by
      funext k
      have h1 := hτmem _ hζroot k
      rw [mem_rootsOfUnity] at h1
      rw [Pi.pow_apply, h1, Pi.one_apply]
    have hτprod : ∏ k, τ k = 1 := by
      simp only [hτ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      group
    set yt : ↥(unitarySU 2 1 K d) := ⟨diagHom d τ, diagHom_mem_unitarySU h hτq hτprod⟩ with hyt
    have hytv : (yt : GL (Fin d) K) = diagHom d τ := rfl
    have hytS : yt ∈ blockSU S := isBlockOn_diagHom fun k hk => by
      rw [(hnotS k).mp hk, hτc']
    have hp2 : (3 : ℕ) ≠ 2 := by norm_num
    have hDB := hDeq (by omega)
    have hwS : swapSU h s t ∈ blockSU S := isBlockOn_permGL_swap hsS htS
    set U := (Subgroup.zpowers (swapSU h s t)).map π with hU
    have hUD : U ≤ D := by
      rw [hDB]
      exact Subgroup.map_mono (Subgroup.zpowers_le.mpr hwS)
    have hU1 : U ≠ ⊥ := by
      intro hbot
      apply projMk_swapSU_ne_one h hst
      have h1 : π (swapSU h s t) ∈ U := ⟨_, Subgroup.mem_zpowers _, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact h1
    have hU2 : IsPGroup 2 U := (isPGroup_two_zpowers (swapSU_sq h s t)).map π
    have hAU : ∀ b ∈ A.map π, ∀ u ∈ U, b * u * b⁻¹ ∈ U := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨u, hu, rfl⟩
      obtain ⟨σ', hσ'⟩ := hdiag y hy
      have hyw := commute_swapSU h hσ' (hpair σ' (mem_diagVec_of hy hσ'))
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      refine ⟨swapSU h s t ^ m, Subgroup.zpow_mem_zpowers _ _, ?_⟩
      have hc : y * swapSU h s t ^ m * y⁻¹ = swapSU h s t ^ m := by
        rw [← (Commute.zpow_left hyw m).eq, mul_inv_cancel_right]
      rw [← map_inv, ← map_mul, ← map_mul, hc]
    refine ⟨U, hUD, hU1, hU2, hAU, π yt, (by rw [hDB]; exact ⟨yt, hytS, rfl⟩), ?_, ?_, ?_,
      π (swapSU h c e), (by rw [hDB]; exact ⟨_, isBlockOn_permGL_swap hcS heS, rfl⟩), ?_⟩
    · rw [← map_pow]
      have h1 : yt ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hytv, ← map_pow, hτp, map_one]
        rfl
      rw [h1, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨σ', hσ'⟩ := hdiag y hy
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ', hytv]
      exact (diagHom_commute σ' τ).eq
    · have hwt : swapSU h s t * yt = yt * swapSU h s t :=
        commute_swapSU h hytv (by rw [hτs, hτt])
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [← map_mul, ← map_mul, (Commute.zpow_left hwt m).eq]
    · intro hcomm
      have hz : π (swapSU h c e * yt * (swapSU h c e)⁻¹ * yt⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      obtain ⟨u, hu⟩ := exists_scalar_of_projMk_eq_one hz
      have hzv : ((swapSU h c e * yt * (swapSU h c e)⁻¹ * yt⁻¹ : ↥(unitarySU 2 1 K d)) :
          GL (Fin d) K) = diagHom d ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv]
        show permGL (Equiv.swap c e) * diagHom d τ * (permGL (Equiv.swap c e))⁻¹ *
          (diagHom d τ)⁻¹ = _
        rw [permGL_mul_diagHom_mul_inv, ← map_inv, ← map_mul]
      have e1 := hu s s
      have e2 := hu c c
      rw [hzv, diagHom_apply_self] at e1 e2
      simp only [↓reduceIte] at e1 e2
      have e3 : ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) s = ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) c :=
        Units.ext (e1.trans e2.symm)
      simp only [Pi.mul_apply, Pi.inv_apply, Function.comp_apply, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hcs.symm hes.symm, Equiv.swap_apply_left, hτc, hτe,
        mul_inv_cancel, one_mul, inv_pow, inv_inv] at e3
      have h2 : ζ ^ 2 = 1 := e3.symm
      have h4 := orderOf_dvd_of_pow_eq_one h2
      rw [hζo] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
  · have htS : t ∉ S := fun ht =>
      hsS ((hmemS k s).mpr ((hpair σx hσxW).trans ((hmemS k t).mp ht)))
    have hout : ∀ c, c ∉ S → c = s ∨ c = t := by
      intro c hc
      by_contra hcst
      push Not at hcst
      obtain ⟨hcs, hct⟩ := hcst
      obtain ⟨τa, hτaW, hτa⟩ := exists_mem_of_pair hp hpK hWp hW1 hst (Ne.symm hcs) hct hpair
        hWc (Pi.mulSingle s ζ) (mulSingle_mem hζroot)
      obtain ⟨τc, hτcW, hτc⟩ := exists_mem_of_pair hp hpK hWp hW1 hst (Ne.symm hcs) hct hpair
        hWc (fun j => if j ∈ S then ζ else 1) (fun j => by
          split_ifs
          · exact hζroot
          · exact (rootsOfUnity 3 K).one_mem)
      have hfree : ∀ i ∈ S, i ∈ freeSet t c := fun i hi =>
        mem_freeSet_iff.mpr ⟨fun h' => hc (h' ▸ hi), fun h' => htS (h' ▸ hi)⟩
      have hτaS : ∀ i ∈ S, τa i = 1 := fun i hi => by
        rw [hτa i (hfree i hi), Pi.mulSingle_eq_of_ne (fun h' : i = s => hsS (h' ▸ hi))]
      have hτas : τa s = ζ := by
        rw [hτa s (mem_freeSet_iff.mpr ⟨Ne.symm hcs, hst⟩), Pi.mulSingle_eq_same]
      have hτcS : ∀ i ∈ S, τc i = ζ := fun i hi => by
        rw [hτc i (hfree i hi)]
        simp [hi]
      obtain ⟨m₁, hm₁⟩ := hcommD τa hτaW fun i hi j hj => by rw [hτaS i hi, hτaS j hj]
      obtain ⟨m₃, hm₃⟩ := hcommD τc hτcW fun i hi j hj => by rw [hτcS i hi, hτcS j hj]
      have hk1 : σx k = 1 := by
        refine eq_one_of_zpow_of_zpow_ne hp (b := σx s) (m := m₁) (hσxp k) (hσxp s) ?_ ?_
        · have e1 := congrFun hm₁ k
          rw [Pi.pow_apply, hτaS k hkS] at e1
          exact e1.symm
        · have e1 := congrFun hm₁ s
          rw [Pi.pow_apply, hτas] at e1
          rw [← e1]
          exact hζ1
      apply hζ1
      have e1 := congrFun hm₃ k
      rw [Pi.pow_apply, hτcS k hkS, hk1, _root_.one_zpow] at e1
      exact e1
    have hScard : d - 2 ≤ S.card := by
      have hsub : Sᶜ ⊆ {s, t} := by
        intro c hc
        rcases hout c (Finset.mem_compl.mp hc) with rfl | rfl <;> simp
      have h1 := Finset.card_le_card hsub
      have h2 : ({s, t} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
      have h3 := Finset.card_compl S
      rw [Fintype.card_fin] at h3
      have h4 : S.card ≤ d := by
        have := Finset.card_le_univ S
        rwa [Fintype.card_fin] at this
      omega
    rcases (show 4 ≤ S.card ∨ S.card = 3 by omega) with hS4 | hS3
    swap
    ·
      exfalso
      have hcardB : Nat.card (blockSU (K := K) (n := 1) S) = 216 := by
        have h1 := Nat.card_congr (TableBUE.blockSUEquiv S h).toEquiv
        rw [hS3] at h1
        have h2 := CFSG.RankThree.PartOne.LSTD.card_unitarySU_three h
        norm_num at h2
        rw [← h1]
        exact_mod_cast h2
      have hDdvd : Nat.card D ∣ 2 ^ 3 * 3 ^ 3 := by
        have h1 := Subgroup.card_dvd_of_le hDk
        have h2 : Nat.card (B k) = 216 := by
          rw [hB]
          dsimp only
          rw [Subgroup.card_map_of_injective hπinj, ← hSdef, hcardB]
        rw [h2] at h1
        exact h1
      obtain ⟨d1, d2, hd1, hd2, hd12⟩ := Nat.dvd_mul.mp hDdvd
      obtain ⟨a₁, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
      obtain ⟨b₁, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
      let _ : Fintype D := Fintype.ofFinite D
      have hsol := CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num) (G := D) (a := a₁) (b := b₁) (by
          rw [← Nat.card_eq_fintype_card]
          first
          | exact hd12
          | exact hd12.symm)
      have := CFSG.LocalCores.isQuasisimple_nontrivial hDq
      have := hDq.1
      exact Group.IsPerfect.not_isSolvable _ hsol
    have hDB := hDeq hS4
    exfalso
    set T := A ⊓ blockSU S with hT
    have hTcard : 3 ^ 3 ≤ Nat.card T := by
      set F := S.erase k with hF
      have hFcard : 3 ≤ F.card := by
        rw [hF, Finset.card_erase_of_mem hkS]
        omega
      have hfun : ∀ y : T, ∃ σ : Fin d → Kˣ,
          ((y : ↥(unitarySU 2 1 K d)) : GL (Fin d) K) = diagHom d σ := fun y => hdiag y y.2.1
      let f : T → (F → rootsOfUnity 3 K) := fun y i =>
        ⟨Classical.choose (hfun y) i,
          hWp _ (mem_diagVec_of y.2.1 (Classical.choose_spec (hfun y))) i⟩
      have hks : s ≠ k := fun h' => hsS (h' ▸ hkS)
      have hkt : k ≠ t := fun h' => htS (h' ▸ hkS)
      have hf : Function.Surjective f := by
        intro v
        set v' : Fin d → Kˣ := fun j => if hj : j ∈ F then (v ⟨j, hj⟩ : Kˣ) else 1 with hv'
        have hv'r : ∀ j, v' j ∈ rootsOfUnity 3 K := fun j => by
          simp only [hv']
          split_ifs
          · exact (v _).2
          · exact (rootsOfUnity 3 K).one_mem
        obtain ⟨σ, hσW, hσ⟩ := exists_mem_of_pair hp hpK hWp hW1 hst hks hkt hpair hWc v' hv'r
        obtain ⟨y, hyA, hyσ⟩ := mem_diagVec.mp hσW
        have hsF : s ∉ F := fun h' => hsS (Finset.mem_of_mem_erase h')
        have hσs : σ s = 1 := by
          rw [hσ s (mem_freeSet_iff.mpr ⟨hks, hst⟩)]
          simp [hv', hsF]
        have hσout : ∀ j, j ∉ S → σ j = 1 := fun j hj => by
          rcases hout j hj with rfl | rfl
          · exact hσs
          · rw [← hpair σ hσW, hσs]
        have hyS : y ∈ blockSU S := by
          rw [mem_blockSU, hyσ]
          exact isBlockOn_diagHom hσout
        refine ⟨⟨y, hyA, hyS⟩, ?_⟩
        funext i
        apply Subtype.ext
        have hch := Classical.choose_spec (hfun ⟨y, hyA, hyS⟩)
        have heq : Classical.choose (hfun ⟨y, hyA, hyS⟩) = σ :=
          diagHom_injective d (hch.symm.trans hyσ)
        show Classical.choose (hfun ⟨y, hyA, hyS⟩) i = v i
        rw [heq, hσ i (mem_freeSet_iff.mpr ⟨Finset.ne_of_mem_erase i.2,
          fun h' => htS (h' ▸ Finset.mem_of_mem_erase i.2)⟩)]
        simp [hv', i.2]
      have h1 := Nat.card_le_card_of_surjective f hf
      rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_finsetCard] at h1
      calc 3 ^ 3 ≤ 3 ^ F.card := Nat.pow_le_pow_right (by norm_num) hFcard
        _ ≤ Nat.card T := h1
    have hE : IsElemAbelian 3 (T.map π) :=
      TableB.isElemAbelian_map (TableB.isElemAbelian_mono hA inf_le_left) π
    have hED : T.map π ≤ D := by
      rw [hDB]
      exact Subgroup.map_mono inf_le_right
    have hEA : T.map π ≤ A.map π := Subgroup.map_mono inf_le_left
    have h2 := hsm _ hE hED hEA
    rw [Subgroup.card_map_of_injective hπinj] at h2
    omega

end Diag

section Main

variable {K : Type} [Field K] [Finite K] {d : ℕ} (h : UnitaryFieldData 2 1 K)

include h in
theorem ggStdSubTwoTorusEltNormSmall_unitary_two (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hd3 : ¬ 3 ∣ d) (hd5 : 5 ≤ d) :
    GGStdSubTwoTorusEltNormSmall 3 (d - 2) (LargeEvenProj (unitarySU 2 1 K d)) := by
  intro Ab hAb hr h3 hU a haAb ha1 D hDC hDn hDq hprov hsm
  set π := LargeEvenProjMk (unitarySU 2 1 K d) with hπ
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hnp : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hd3 hz hzp
  obtain ⟨A, hmap, -, hA, hcardA⟩ :=
    exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective _) hp hnp hAb
  obtain ⟨P, hP, hdiag⟩ := exists_conj_diag h hp hpq hA
  set c := conjSU h P hP with hc
  set A' := A.map (c : ↥(unitarySU 2 1 K d) →* ↥(unitarySU 2 1 K d)) with hA'
  have hA'ab : IsElemAbelian 3 A' := by
    have := isElemAbelian_range (H := A) (p := 3)
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2))
      ((c : ↥(unitarySU 2 1 K d) →* ↥(unitarySU 2 1 K d)).comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hdiag' : ∀ x ∈ A', ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
  have hcard' : Nat.card A' = Nat.card Ab := by
    rw [hA', ← hcardA]
    exact (Nat.card_congr (A.equivMapOfInjective _ c.injective).toEquiv).symm
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 1 K d) →*
      LargeEvenProj (unitarySU 2 1 K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  set U' := U.map (cR : LargeEvenProj (unitarySU 2 1 K d) →* LargeEvenProj (unitarySU 2 1 K d))
    with hU'
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR u ∈ U' := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.injective (h1.trans (map_one cR).symm)
  have hBU' : A'.map π ≤ Subgroup.normalizer (U' : Set _) := by
    rw [hmap']
    exact (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _)
  obtain ⟨s, t, hst, hpairF⟩ := SURepair.exists_framePair_of_twoSubgroup h
    (ker_projMk_le_center (n := 1) (d := d) (K := K)) hU'1 (hU2.map _)
    (fun u _ => QuotientGroup.mk'_surjective _ u) hBU'
  have hpair : ∀ σ ∈ diagVec A', σ s = σ t := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
    obtain ⟨hpow, -⟩ := diagVec_props h hA'ab hσ
    refine hpairF (π x) ⟨x, hx, rfl⟩ σ ⟨fun i => ?_, fun u u' hu' => ?_⟩
    · obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hpow i, Units.val_one, one_pow]
    · have hu'' : u' = x * u * x⁻¹ := by
        apply Subtype.ext
        rw [hu', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxσ]
      rw [hu'', map_mul, map_mul, map_inv]
  have hcRa : cR a ∈ A'.map π := by
    rw [hmap']
    exact ⟨a, haAb, rfl⟩
  obtain ⟨x, hxA', hxa⟩ := hcRa
  have hx1 : π x ≠ 1 := by
    rw [hxa]
    intro h1
    exact ha1 (cR.injective (h1.trans (map_one cR).symm))
  set e := cR with he
  have hmemA : ∀ b ∈ Ab, e b ∈ A'.map π := fun b hb => by
    rw [hmap']
    exact ⟨b, hb, rfl⟩
  have hmap : ∀ {X : Subgroup (LargeEvenProj (unitarySU 2 1 K d))}
      {y : LargeEvenProj (unitarySU 2 1 K d)}, y ∈ X.map e.symm.toMonoidHom ↔ e y ∈ X := by
    intro X y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨e y, hy, by simp⟩
  set D' := D.map e.toMonoidHom with hD'
  have hD'C : D' ≤ Subgroup.centralizer ({π x} : Set (LargeEvenProj (unitarySU 2 1 K d))) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hxa]
    exact StdSubSp.apply_mem_centralizer_singleton e (hDC hy)
  have hD'n : ∀ c' ∈ Subgroup.centralizer ({π x} : Set (LargeEvenProj (unitarySU 2 1 K d))),
      ∀ y ∈ D', c' * y * c'⁻¹ ∈ D' := by
    rintro c' hc' _ ⟨y, hy, rfl⟩
    rw [hxa] at hc'
    have hc'' := StdSubSp.symm_mem_centralizer_singleton e hc'
    refine ⟨e.symm c' * y * (e.symm c')⁻¹, hDn _ hc'' y hy, ?_⟩
    show e (e.symm c' * y * (e.symm c')⁻¹) = c' * e y * c'⁻¹
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
  have hD'q : CFSG.IsQuasisimple D' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (D.equivMapOfInjective _ e.injective) hDq
  have hprov' : ∀ b ∈ A'.map π, (∀ y ∈ D', b * y = y * b) → b ∈ Subgroup.zpowers (π x) := by
    intro b hb hbD
    rw [hmap'] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have h1 := hprov b₀ hb₀ fun y hy => e.injective (by
      rw [map_mul, map_mul]
      exact hbD (e y) ⟨y, hy, rfl⟩)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [hxa, ← hm, map_zpow]
    rfl
  have hsm' : ∀ E : Subgroup (LargeEvenProj (unitarySU 2 1 K d)), IsElemAbelian 3 E → E ≤ D' →
      E ≤ A'.map π → Nat.card E < 3 ^ 3 := by
    intro E hE hED hEA
    have h1 := hsm (E.map e.symm.toMonoidHom) (TableB.isElemAbelian_map hE _)
      (fun y hy => by
        rw [hmap] at hy
        obtain ⟨z, hz, hz'⟩ := hED hy
        have : z = y := e.injective hz'
        exact this ▸ hz)
      (fun y hy => by
        rw [hmap] at hy
        have h2 := hEA hy
        rw [hmap'] at h2
        obtain ⟨z, hz, hz'⟩ := h2
        have : z = y := e.injective hz'
        exact this ▸ hz)
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    rwa [Subgroup.card_map_of_injective hinj] at h1
  obtain ⟨U₀, hU₀D, hU₀1, hU₀2, hAU₀, y, hyD, hyp, hyA, hyU, j, hjD, hyj⟩ :=
    eltSmall_diag_two h hK hd3 hd5 hA'ab hdiag' (hcard' ▸ hr) hst hpair hxA' hx1 hD'C hD'n hD'q
      hprov' hsm'
  have hback : ∀ {z : LargeEvenProj (unitarySU 2 1 K d)}, z ∈ D' → e.symm z ∈ D := by
    rintro _ ⟨w, hw, rfl⟩
    simpa using hw
  refine ⟨U₀.map e.symm.toMonoidHom, ?_, ?_, hU₀2.map _, ?_, e.symm y, hback hyD, ?_, ?_, ?_,
    e.symm j, hback hjD, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hback (hU₀D hu)
  · have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
    exact hU₀1
  · intro b hb u hu
    rw [hmap] at hu ⊢
    rw [map_mul, map_mul, map_inv]
    exact hAU₀ (e b) (hmemA b hb) (e u) hu
  · rw [← map_pow, hyp, map_one]
  · intro b hb
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hyA (e b) (hmemA b hb)
  · rw [Subgroup.mem_normalizer_iff] at hyU ⊢
    intro u
    rw [hmap, hmap, map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact hyU (e u)
  · intro h1
    apply hyj
    have := congrArg e h1
    simpa using this

end Main

end StdSubRestThreeU

end CFSG.StandardType
