module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W7NineOne
import CFSG.GroupTheory.CharacteristicNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (calK8104)
open CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem P_le_of_mem_calK8104 {D : Data G} {P K L : Subgroup G}
    (hL : L ∈ calK8104 D P K) : P ≤ L := by
  intro p hp
  have hmem : (1 : G) * 1 * p ∈ (L : Set G) := by
    rw [hL.2.2.2]
    exact Set.mul_mem_mul (Set.mul_mem_mul ((pCoreOf 2 L).one_mem)
      ⟨K.one_mem, L.one_mem⟩) hp
  simpa using hmem

private theorem coe_eq_mul_of_sup_inf_normalizer {D : Data G} {P K H R' : Subgroup G}
    (hH : H ∈ calK8104 D P K) (hR'2 : IsPGroup 2 R')
    (hHR' : H ≤ normalizer (R' : Set G)) (hle : pCoreOf 2 H ≤ R') :
    (((R' ⊓ normalizer (pCoreOf 2 H : Set G)) ⊔ H : Subgroup G) : Set G) =
      (pCoreOf 2 (((R' ⊓ normalizer (pCoreOf 2 H : Set G)) ⊔ H) : Subgroup G) : Set G) *
        ((K ⊓ ((R' ⊓ normalizer (pCoreOf 2 H : Set G)) ⊔ H) : Subgroup G) : Set G) *
        (P : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hR
  set R₁ := R' ⊓ normalizer (R : Set G) with hR₁
  set H₁ := R₁ ⊔ H with hH₁
  have hHR : H ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHR₁ : H ≤ normalizer (R₁ : Set G) := by
    rw [hR₁]
    exact (le_inf hHR' (hHR.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRleR₁ : R ≤ R₁ := by
    rw [hR₁]
    exact le_inf (by rwa [hR] at hle) Subgroup.le_normalizer
  have hR₁2 : IsPGroup 2 R₁ := by
    rw [hR₁]
    exact hR'2.to_le inf_le_left
  have hH₁N : H₁ ≤ normalizer (R₁ : Set G) := sup_le Subgroup.le_normalizer hHR₁
  have hR₁core : R₁ ≤ pCoreOf 2 H₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (N := R₁) (H := H₁)
      le_sup_left hH₁N hR₁2
  have hP : P ≤ H := P_le_of_mem_calK8104 hH
  refine le_antisymm ?_ ?_
  · rw [hH₁, hR₁, hR, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hHR₁]
    rintro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨r₁, hr₁, h, hh, rfl⟩ := hx
    rw [hH.2.2.2, Set.mem_mul] at hh
    obtain ⟨y, hy, p, hp, rfl⟩ := hh
    rw [Set.mem_mul] at hy
    obtain ⟨r, hr, k, hk, rfl⟩ := hy
    refine Set.mem_mul.mpr ⟨(r₁ * r) * k, ?_, p, hp, ?_⟩
    · exact Set.mem_mul.mpr ⟨r₁ * r,
        hR₁core (R₁.mul_mem hr₁ (hRleR₁ hr)), k, ⟨hk.1, Subgroup.mem_sup_right hk.2⟩, rfl⟩
    · simp only [mul_assoc]
  · rintro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨o, ho, p, hp, rfl⟩ := hx
    rw [Set.mem_mul] at ho
    obtain ⟨o', ho', k, hk, rfl⟩ := ho
    exact H₁.mul_mem (H₁.mul_mem ((CFSG.LieType.BorelTits.pCoreOf_le 2 H₁) ho') hk.2)
      (Subgroup.mem_sup_right (hP hp))

private theorem exists_mem_calK8104_gt {D : Data G} {P K H R' : Subgroup G}
    (hH : H ∈ calK8104 D P K)
    (hR'M : R' ≤ D.M) (hR'2 : IsPGroup 2 R') (hHR' : H ≤ normalizer (R' : Set G))
    (hlt : pCoreOf 2 H < R') :
    ∃ H₁ ∈ calK8104 D P K, H < H₁ ∧ H₁ ≤ R' ⊔ H ∧ H₁ ≤ normalizer (pCoreOf 2 H : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hR
  set R₁ := R' ⊓ normalizer (R : Set G) with hR₁
  set H₁ := R₁ ⊔ H with hH₁
  have hHR : H ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHR₁ : H ≤ normalizer (R₁ : Set G) := by
    rw [hR₁]
    exact (le_inf hHR' (hHR.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hltR₁ : R < R₁ := by
    rw [hR, hR₁]
    exact CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hR'2 hlt
  have hR₁2 : IsPGroup 2 R₁ := by
    rw [hR₁]
    exact hR'2.to_le inf_le_left
  have hH₁N : H₁ ≤ normalizer (R₁ : Set G) := sup_le Subgroup.le_normalizer hHR₁
  have hR₁core : R₁ ≤ pCoreOf 2 H₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (N := R₁) (H := H₁)
      le_sup_left hH₁N hR₁2
  have hR₁ne : R₁ ≠ ⊥ := fun hbot => (not_lt_of_ge bot_le) (hbot ▸ hltR₁)
  have hcoreNe : pCoreOf 2 H₁ ≠ ⊥ := fun hbot =>
    hR₁ne (le_bot_iff.mp (hR₁core.trans (le_of_eq hbot)))
  have hH₁M : H₁ ≤ D.M := by
    rw [hH₁, hR₁]
    exact sup_le (inf_le_left.trans hR'M) hH.1
  have hKH₁ : K ≤ H₁ := by
    rw [hH₁]
    exact hH.2.2.1.trans le_sup_right
  have hset : (H₁ : Set G) = (pCoreOf 2 H₁ : Set G) *
      ((K ⊓ H₁ : Subgroup G) : Set G) * (P : Set G) := by
    rw [hH₁, hR₁, hR]
    exact coe_eq_mul_of_sup_inf_normalizer hH hR'2 hHR' hlt.le
  have hHlt : H < H₁ := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    have hR₁H : R₁ ≤ H := by
      have h : R₁ ≤ H₁ := le_sup_left
      rwa [← heq] at h
    exact hltR₁.not_ge
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR₁H hHR₁ hR₁2)
  refine ⟨H₁, ⟨hH₁M, hcoreNe, hKH₁, hset⟩, hHlt, ?_, ?_⟩
  · rw [hH₁]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  · rw [hH₁]
    exact sup_le inf_le_right hHR

private theorem normalizer_le_calCGS {R : Subgroup G} (hR : R ≠ ⊥) :
    normalizer (R : Set G) ≤ UC6.calCGS R := by
  unfold UC6.calCGS
  refine le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le le_rfl (le_iSup_of_le ?_ le_rfl)))
  rw [Subgroup.subgroupOf_self]
  infer_instance

private theorem calCGS_le_of_lt {D : Data G} {L P B H N R' : Subgroup G} (c : Cex8105 D L P B H N)
    (hR'M : R' ≤ D.M) (hR'2 : IsPGroup 2 R') (hHR' : H ≤ normalizer (R' : Set G))
    (hlt : pCoreOf 2 H < R') : UC6.calCGS (pCoreOf 2 H) ≤ D.M := by
  obtain ⟨H₁, hH₁, hHlt, -, hH₁N⟩ :=
    exists_mem_calK8104_gt (D := D) (P := P) (K := F08.KOf8103 L B) c.memH
      hR'M hR'2 hHR' hlt
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.calCGS_le_of_uniqueMax
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hH₁N (c.ih H₁ hH₁ hHlt)

private theorem eq_pCoreOf_of_le_inf {D : Data G} {L P B H N R' : Subgroup G}
    (c : Cex8105 D L P B H N)
    (hR'M : R' ≤ D.M ⊓ N) (hR'2 : IsPGroup 2 R') (hHR' : H ≤ normalizer (R' : Set G))
    (hle : pCoreOf 2 H ≤ R') : R' = pCoreOf 2 H := by
  refine le_antisymm ?_ hle
  by_contra hnot
  have hlt : pCoreOf 2 H < R' :=
    lt_of_le_of_ne hle (fun h => hnot (h ▸ le_rfl))
  have hR'M₁ : R' ≤ D.M := fun x hx => (hR'M hx).1
  have hR'N : R' ≤ N := fun x hx => (hR'M hx).2
  obtain ⟨H₁, hH₁, hHlt, hH₁le, -⟩ :=
    exists_mem_calK8104_gt (D := D) (P := P) (K := F08.KOf8103 L B) c.memH
      hR'M₁ hR'2 hHR' hlt
  have hH₁N : H₁ ≤ N := hH₁le.trans (sup_le hR'N c.memN.2)
  have hNmem : N ∈ calMOf H₁ := ⟨c.memN.1, hH₁N⟩
  rw [c.ih H₁ hH₁ hHlt] at hNmem
  exact c.neN (by simpa using hNmem)

theorem calCGS_le_of_lt_mem {D : Data G} {L P B H N H₂ : Subgroup G} (c : Cex8105 D L P B H N)
    (hH₂ : H₂ ∈ calK8104 D P (F08.KOf8103 L B)) (hlt : H < H₂) :
    UC6.calCGS (pCoreOf 2 H) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hR
  set R₂ := pCoreOf 2 H₂ with hR₂
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hR₂2 : IsPGroup 2 R₂ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₂
  have hHR₂ : H ≤ normalizer (R₂ : Set G) :=
    hlt.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₂)
  have hRR₂ : R ≤ normalizer (R₂ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHR₂
  have hsup2 : IsPGroup 2 ↥(R ⊔ R₂) := by
    have h := IsPGroup.to_sup_of_normal_left' (p := 2) (H := R₂) (K := R) hR₂2 hR2 hRR₂
    rwa [sup_comm] at h
  have hHsup : H ≤ normalizer ((R ⊔ R₂ : Subgroup G) : Set G) :=
    (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) hHR₂).trans
      (Subgroup.inf_normalizer_le_normalizer_sup R R₂)
  have hsupM : R ⊔ R₂ ≤ D.M :=
    sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans c.memH.1)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H₂).trans hH₂.1)
  by_cases hEq : R ⊔ R₂ = R
  · have hR₂R : R₂ ≤ R := hEq ▸ le_sup_right
    have hP : P ≤ H := P_le_of_mem_calK8104 c.memH
    have hH₂H : H₂ ≤ H := by
      intro x hx
      change x ∈ (H₂ : Set G) at hx
      rw [hH₂.2.2.2] at hx
      rw [Set.mem_mul] at hx
      obtain ⟨o, ho, p, hp, rfl⟩ := hx
      rw [Set.mem_mul] at ho
      obtain ⟨o', ho', k, hk, rfl⟩ := ho
      exact H.mul_mem
        (H.mul_mem (hR₂R.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H) ho')
          (c.memH.2.2.1 hk.1)) (hP hp)
    exact absurd hlt (not_lt_of_ge hH₂H)
  · refine calCGS_le_of_lt (c := c) (R' := R ⊔ R₂) hsupM hsup2 hHsup ?_
    exact lt_of_le_of_ne le_sup_left (Ne.symm hEq)

private theorem eq_pCoreOf_of_le_N {D : Data G} {L P B H N R' : Subgroup G}
    (c : Cex8105 D L P B H N)
    (hC : UC6.calCGS (pCoreOf 2 H) ≤ D.M) (hR'N : R' ≤ N) (hR'2 : IsPGroup 2 R')
    (hHR' : H ≤ normalizer (R' : Set G)) (hle : pCoreOf 2 H ≤ R') : R' = pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hR
  refine le_antisymm ?_ hle
  by_contra hnot
  have hlt : R < R' := by
    rw [hR]
    exact lt_of_le_of_ne hle (fun h => hnot (h ▸ le_rfl))
  set R₁ := R' ⊓ normalizer (R : Set G) with hR₁
  have hRne : R ≠ ⊥ := by
    rw [hR]
    exact c.memH.2.1
  have hlt₁ : R < R₁ := by
    rw [hR₁]
    exact CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hR'2 hlt
  have hR₁2 : IsPGroup 2 R₁ := by
    rw [hR₁]
    exact hR'2.to_le inf_le_left
  have hHR : H ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHR₁ : H ≤ normalizer (R₁ : Set G) := by
    rw [hR₁]
    exact (le_inf hHR' (hHR.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hC' : UC6.calCGS R ≤ D.M := by rwa [hR] at hC
  have hR₁M : R₁ ≤ D.M := by
    rw [hR₁]
    exact inf_le_right.trans ((normalizer_le_calCGS hRne).trans hC')
  have hR₁N : R₁ ≤ N := by
    rw [hR₁]
    exact inf_le_left.trans hR'N
  have hle₁ : R ≤ R₁ := by
    rw [hR₁]
    exact le_inf (by rwa [hR] at hle) Subgroup.le_normalizer
  have heq := eq_pCoreOf_of_le_inf (c := c) (R' := R₁) (le_inf hR₁M hR₁N) hR₁2 hHR₁ hle₁
  exact hlt₁.not_ge (le_of_eq heq)

theorem pCoreOf_le_of_calCGS_le {D : Data G} {L P B H N : Subgroup G} (c : Cex8105 D L P B H N)
    (hC : UC6.calCGS (pCoreOf 2 H) ≤ D.M) : pCoreOf 2 N ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 H with hR
  set Q := pCoreOf 2 N with hQ
  have hRN : R ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans c.memN.2
  have hQN : Q ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hRQ : R ≤ normalizer (Q : Set G) :=
    hRN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hsup2 : IsPGroup 2 ↥(R ⊔ Q) := by
    have h := IsPGroup.to_sup_of_normal_left' (p := 2) (H := Q) (K := R)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hRQ
    rwa [sup_comm] at h
  have hHsup : H ≤ normalizer ((R ⊔ Q : Subgroup G) : Set G) :=
    (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
      (c.memN.2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup R Q)
  have hC' : UC6.calCGS R ≤ D.M := by rwa [hR] at hC
  have heq := eq_pCoreOf_of_le_N (c := c) hC' (sup_le hRN hQN) hsup2 hHsup le_sup_left
  have hQR : Q ≤ R := by
    have h : Q ≤ R ⊔ Q := le_sup_right
    rwa [heq] at h
  rwa [hQ, hR]

theorem eq_pCoreOf_of_maximal {D : Data G} {P K H R' : Subgroup G} (hH : H ∈ calK8104 D P K)
    (hmax : ∀ H' ∈ calK8104 D P K, ¬ H < H') (hR'M : R' ≤ D.M) (hR'2 : IsPGroup 2 R')
    (hHR' : H ≤ normalizer (R' : Set G)) (hle : pCoreOf 2 H ≤ R') : R' = pCoreOf 2 H := by
  refine le_antisymm ?_ hle
  by_contra hnot
  have hlt : pCoreOf 2 H < R' :=
    lt_of_le_of_ne hle (fun h => hnot (h ▸ le_rfl))
  obtain ⟨H₁, hH₁, hHlt, -⟩ :=
    exists_mem_calK8104_gt (D := D) (P := P) (K := K) hH hR'M hR'2 hHR' hlt
  exact (hmax H₁ hH₁) hHlt

private theorem exists_char_normalizer_not_le_of_not_le_calCGS {R M : Subgroup G}
    (hC : ¬ UC6.calCGS R ≤ M) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
      ¬ normalizer (C : Set G) ≤ M := by
  by_contra hcon
  apply hC
  unfold UC6.calCGS
  refine iSup_le fun C => iSup_le fun hC1 => iSup_le fun hCR => iSup_le fun hchar => ?_
  by_contra hle
  exact hcon ⟨C, hC1, hCR, hchar, hle⟩

theorem exists_sylow_le_inf {D : Data G} {L P B H N T₁ : Subgroup G} (c : Cex8105 D L P B H N)
    (hC : ¬ UC6.calCGS (pCoreOf 2 H) ≤ D.M) (hT₁ : IsSylowOf 2 T₁ D.M)
    (hT₁R : T₁ ≤ normalizer (pCoreOf 2 H : Set G)) :
    ∃ T : Subgroup G, IsSylowOf 2 T ⊤ ∧ T ≤ D.M ⊓ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC1, hCR, hCchar, hCNM⟩ :=
    exists_char_normalizer_not_le_of_not_le_calCGS hC
  have hR2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hC1, hR2.to_le hCR, rfl⟩
  obtain ⟨N', hN'max, hCN'⟩ := exists_rankThreeIsMaxTwoLocal_ge hloc
  have hN'ne : N' ≠ D.M := fun heq => hCNM (heq ▸ hCN')
  have hNC : normalizer (pCoreOf 2 H : Set G) ≤ normalizer (C : Set G) :=
    CFSG.GroupTheory.normalizer_le_normalizer_of_characteristic hCR hCchar
  have hH_N' : H ≤ N' := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
    (hNC.trans hCN')
  have hmaxN := c.maxN N' ⟨hN'max, hH_N'⟩ hN'ne
  have hT₁N' : T₁ ≤ N' := hT₁R.trans (hNC.trans hCN')
  have hT₁_inf : T₁ ≤ D.M ⊓ N' := le_inf hT₁.le hT₁N'
  have hT₁G : Nat.card T₁ = 2 ^ (Nat.card G).factorization 2 := by
    rw [hT₁.card_eq, ← D.sylowM.card_eq]
    simpa using D.sylowG.card_eq
  have hfac_le : (Nat.card G).factorization 2 ≤
      (Nat.card (D.M ⊓ N' : Subgroup G)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (Nat.card_pos (α := ↥(D.M ⊓ N' : Subgroup G))).ne').mp (by
      rw [← hT₁G]
      exact Subgroup.card_dvd_of_le hT₁_inf)
  have hfac_ge :
      (Nat.card (D.M ⊓ N : Subgroup G)).factorization 2 ≤ (Nat.card G).factorization 2 := by
    refine ((Nat.factorization_le_iff_dvd
      (Nat.card_pos (α := ↥(D.M ⊓ N : Subgroup G))).ne'
      (Nat.card_pos (α := G)).ne').mpr ?_) 2
    simpa [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (H := D.M ⊓ N) (K := ⊤) le_top)
  have hfac_eq : (Nat.card (D.M ⊓ N : Subgroup G)).factorization 2 = (Nat.card G).factorization 2 :=
    le_antisymm hfac_ge (hfac_le.trans hmaxN)
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (D.M ⊓ N)
  refine ⟨T, ?_, hT.le⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card (P := T) (K := ⊤) le_top ?_
  rw [hT.card_eq, hfac_eq, Subgroup.card_top]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
