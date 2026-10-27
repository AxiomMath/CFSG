module

public import CFSG.LocalAnalysis.WeakClosure81.W16LRootPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75
open Subgroup

@[expose] def psuRootLine {X : Type} [Group X] (Q Q' : Sylow 2 X) : Set (Sylow 2 X) :=
  {Q'' | sylowCenter Q'' ≤ sylowCenter Q ⊔ sylowCenter Q'}

theorem mem_psuRootLine_left {X : Type} [Group X] (Q Q' : Sylow 2 X) : Q ∈ psuRootLine Q Q' :=
  show sylowCenter Q ≤ sylowCenter Q ⊔ sylowCenter Q' from le_sup_left

theorem mem_psuRootLine_right {X : Type} [Group X] (Q Q' : Sylow 2 X) :
    Q' ∈ psuRootLine Q Q' :=
  show sylowCenter Q' ≤ sylowCenter Q ⊔ sylowCenter Q' from le_sup_right

variable {P : Type} [Group P] [Finite P] {n : ℕ}

section Certified


theorem IsPSUGp.ncard_psuRootLine (hP : IsPSUGp P 3 n) {Q Q' : Sylow 2 P} (hne : Q ≠ Q') :
    (psuRootLine Q Q').ncard = 2 ^ n + 1 := by
  classical
  let L : Subgroup P := sylowCenter Q ⊔ sylowCenter Q'
  let q : ℕ := 2 ^ n
  have hpair : IsL2Pair ↥L ((sylowCenter Q).subgroupOf L) q :=
    hP.isL2Pair_sylowCenter_sup hne
  have hn2 : 2 ≤ n := two_le_of_isPSUGp hP
  have hq4 : 4 ≤ q := by
    have h : 2 ^ 2 ≤ 2 ^ n := pow_le_pow_right' (by norm_num) hn2
    simpa [q] using h
  have hqfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [pow_two, mul_self_tsub_one, Nat.mul_comm]
  have hSylowCount : Nat.card (Sylow 2 ↥L) = q + 1 := by
    obtain ⟨P₀, hP₀⟩ := hpair.exists_sylow_eq
    have hcard : Nat.card (Sylow 2 ↥L) =
        (Subgroup.normalizer (((sylowCenter Q).subgroupOf L : Subgroup ↥L)
          : Set ↥L)).index :=
      (Sylow.card_eq_index_normalizer P₀).trans
        (congrArg (fun H : Subgroup ↥L => (Subgroup.normalizer (H : Set ↥L)).index) hP₀)
    have hmul : q * (q - 1) *
        (Subgroup.normalizer (((sylowCenter Q).subgroupOf L : Subgroup ↥L)
          : Set ↥L)).index = q * (q ^ 2 - 1) := by
      rw [← hpair.card_normalizer, Subgroup.card_mul_index, hpair.card_eq_mul]
    have hidx : (Subgroup.normalizer (((sylowCenter Q).subgroupOf L : Subgroup ↥L)
        : Set ↥L)).index = q + 1 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos
        (lt_of_lt_of_le (by norm_num : 0 < 4) hq4)
        (Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num : 1 < 4) hq4)))
      calc q * (q - 1) *
            (Subgroup.normalizer (((sylowCenter Q).subgroupOf L : Subgroup ↥L)
              : Set ↥L)).index = q * (q ^ 2 - 1) := hmul
        _ = q * ((q - 1) * (q + 1)) := by rw [hqfac]
        _ = q * (q - 1) * (q + 1) := by rw [mul_assoc]
    rw [hcard, hidx]
  have hS_card : ∀ x : ↥(psuRootLine Q Q'),
      Nat.card (((sylowCenter x.1).subgroupOf L : Subgroup ↥L)) = q := by
    intro x
    calc Nat.card ((sylowCenter x.1).subgroupOf L)
        = Nat.card (sylowCenter x.1) :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (show sylowCenter x.1 ≤ L from x.2)).toEquiv
      _ = 2 ^ n := hP.isU3Shape.card_sylowCenter x.1
      _ = q := rfl
  have hT_card : ∀ T : Sylow 2 ↥L, Nat.card (T : Subgroup ↥L) = q := by
    intro T
    obtain ⟨g, hg⟩ := hpair.exists_conj_eq_sylow T
    have hcj : Nat.card
        (CFSG.CGT.Timmesfeld75.conjSubgroup g ((sylowCenter Q).subgroupOf L)) =
        Nat.card ((sylowCenter Q).subgroupOf L) := by
      unfold CFSG.CGT.Timmesfeld75.conjSubgroup
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [← hg, hcj, hpair.card_eq]
  have hF_exists : ∀ x : ↥(psuRootLine Q Q'), ∃ T : Sylow 2 ↥L,
      ((sylowCenter x.1).subgroupOf L : Subgroup ↥L) ≤ (T : Subgroup ↥L) :=
    fun x => (IsPGroup.of_card (hS_card x)).exists_le_sylow
  let F : ↥(psuRootLine Q Q') → Sylow 2 ↥L := fun x => (hF_exists x).choose
  have hF_spec : ∀ x, ((sylowCenter x.1).subgroupOf L : Subgroup ↥L) ≤
      (F x : Subgroup ↥L) := fun x => (hF_exists x).choose_spec
  have hF_inj : ∀ a b ha hb, F ⟨a, ha⟩ = F ⟨b, hb⟩ → a = b := by
    intro a b ha hb hFab
    have hSa : ((sylowCenter a).subgroupOf L : Subgroup ↥L) =
        (F ⟨a, ha⟩ : Subgroup ↥L) := by
      apply Subgroup.eq_of_le_of_card_ge (hF_spec ⟨a, ha⟩)
      exact le_of_eq ((hT_card (F ⟨a, ha⟩)).trans (hS_card ⟨a, ha⟩).symm)
    have hSb : ((sylowCenter b).subgroupOf L : Subgroup ↥L) =
        (F ⟨b, hb⟩ : Subgroup ↥L) := by
      apply Subgroup.eq_of_le_of_card_ge (hF_spec ⟨b, hb⟩)
      exact le_of_eq ((hT_card (F ⟨b, hb⟩)).trans (hS_card ⟨b, hb⟩).symm)
    have hZ : sylowCenter a = sylowCenter b := by
      have hFab' : (F ⟨a, ha⟩ : Subgroup ↥L) = (F ⟨b, hb⟩ : Subgroup ↥L) :=
        congrArg (fun S : Sylow 2 ↥L => (S : Subgroup ↥L)) hFab
      have hmap := congrArg (Subgroup.map L.subtype) (hSa.trans (hFab'.trans hSb.symm))
      rwa [Subgroup.map_subgroupOf_eq_of_le (show sylowCenter a ≤ L from ha),
        Subgroup.map_subgroupOf_eq_of_le (show sylowCenter b ≤ L from hb)] at hmap
    exact hP.sylowCenter_injective hZ
  have hF_surj : ∀ T : Sylow 2 ↥L, ∃ x : ↥(psuRootLine Q Q'), F x = T := by
    intro T
    let R : Subgroup P := (T : Subgroup ↥L).map L.subtype
    have hR_elem : IsElemAbelian 2 R :=
      isElemAbelian_map_of_hom (hpair.of_sylow T).isElemAbelian L.subtype
    have hR_card : Nat.card R = q := by
      rw [show Nat.card R = Nat.card (T : Subgroup ↥L) from
        Subgroup.card_map_of_injective L.subtype_injective, (hpair.of_sylow T).card_eq]
    obtain ⟨Q_T, hQ_T⟩ := hP.exists_sylow_sylowCenter_eq hR_elem hR_card
    have hmem : Q_T ∈ psuRootLine Q Q' := by
      show sylowCenter Q_T ≤ L
      rw [hQ_T]
      exact Subgroup.map_subtype_le _
    refine ⟨⟨Q_T, hmem⟩, ?_⟩
    have hS_eq : ((sylowCenter Q_T).subgroupOf L : Subgroup ↥L) = (T : Subgroup ↥L) := by
      rw [hQ_T]
      ext x
      rw [Subgroup.mem_subgroupOf]
      change L.subtype x ∈ (T : Subgroup ↥L).map L.subtype ↔ x ∈ (T : Subgroup ↥L)
      rw [Subgroup.mem_map_iff_mem L.subtype_injective]
    have hle : (T : Subgroup ↥L) ≤ (F ⟨Q_T, hmem⟩ : Subgroup ↥L) := by
      rw [← hS_eq]
      exact hF_spec ⟨Q_T, hmem⟩
    exact Sylow.ext (Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq ((hT_card (F ⟨Q_T, hmem⟩)).trans (hT_card T).symm))).symm
  have hbij : (psuRootLine Q Q').ncard = Nat.card (Sylow 2 ↥L) := by
    have h := Set.ncard_congr (s := psuRootLine Q Q') (t := Set.univ (α := Sylow 2 ↥L))
      (fun x hx => F ⟨x, hx⟩) (fun _ _ => Set.mem_univ _)
      (fun a b ha hb h => hF_inj a b ha hb h)
      (fun T _ => by
        obtain ⟨x, hx⟩ := hF_surj T
        exact ⟨x.1, x.2, hx⟩)
    simpa using h
  rw [hbij, hSylowCount]

theorem IsPSUGp.psuRootLine_eq_of_mem (hP : IsPSUGp P 3 n) {Q Q' z w : Sylow 2 P}
    (hne : Q ≠ Q') (hz : z ∈ psuRootLine Q Q') (hw : w ∈ psuRootLine Q Q') (hzw : z ≠ w) :
    psuRootLine z w = psuRootLine Q Q' := by
  have hle : sylowCenter z ⊔ sylowCenter w ≤ sylowCenter Q ⊔ sylowCenter Q' :=
    sup_le hz hw
  have heq : sylowCenter z ⊔ sylowCenter w = sylowCenter Q ⊔ sylowCenter Q' := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [(hP.isL2Pair_sylowCenter_sup hne).card_eq_mul,
      (hP.isL2Pair_sylowCenter_sup hzw).card_eq_mul]
  ext s
  simp only [psuRootLine, Set.mem_setOf_eq]
  rw [heq]

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
