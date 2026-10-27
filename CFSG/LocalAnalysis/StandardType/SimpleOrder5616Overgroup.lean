module

public import CFSG.LocalAnalysis.StandardType.SolvableOrSimpleDerived
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.AffineMonoid.Basic

public section

namespace CFSG.StandardType.SimpleOrderFiveSixOneSix

open CFSG.StandardType.SylowOvergroup

lemma eq_27_mul_dvd_208_of_dvd_5616_of_dvd_27 {n : ℕ} (h1 : n ∣ 5616) (h2 : 27 ∣ n) :
    n = 27 ∨ n = 54 ∨ n = 108 ∨ n = 216 ∨ n = 432 ∨ n = 351 ∨ n = 702 ∨ n = 1404 ∨
      n = 2808 ∨ n = 5616 := by
  obtain ⟨d, rfl⟩ := h2
  have hle : 27 * d ≤ 5616 := Nat.le_of_dvd (by norm_num) h1
  have hd : d ≤ 208 := by omega
  interval_cases d <;> norm_num at h1 <;> norm_num

lemma thirteen_le_card_quotient_subgroupOf_of_simple_card_5616 {Q : Type*} [Group Q] [Finite Q]
    {L Y : Subgroup Q} (hL : IsSimpleGroup ↥L) (hcard : Nat.card ↥L = 5616)
    (hHne : Y.subgroupOf L ≠ ⊤) :
    13 ≤ Nat.card (↥L ⧸ Y.subgroupOf L) := by
  by_contra hlt
  rw [not_le] at hlt
  let H : Subgroup ↥L := Y.subgroupOf L
  haveI : IsSimpleGroup ↥L := hL
  rcases hL.eq_bot_or_eq_top_of_normal (MulAction.toPermHom ↥L (↥L ⧸ H)).ker with hbot | htop
  · have hinj : Function.Injective (MulAction.toPermHom ↥L (↥L ⧸ H)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hbot
    have hdvd : Nat.card ↥L ∣ Nat.card (Equiv.Perm (↥L ⧸ H)) :=
      Subgroup.card_dvd_of_injective (MulAction.toPermHom ↥L (↥L ⧸ H)) hinj
    rw [Nat.card_perm] at hdvd
    have h13 : 13 ∣ Nat.factorial (Nat.card (↥L ⧸ H)) := by
      refine dvd_trans ?_ hdvd
      rw [hcard]; norm_num
    have hp13 : Nat.Prime 13 := by norm_num
    have := hp13.dvd_factorial.mp h13
    simp only [H] at this
    omega
  · have hcore : H.normalCore = ⊤ := by
      rw [Subgroup.normalCore_eq_ker, htop]
    have hle : (⊤ : Subgroup ↥L) ≤ H := by
      rw [← hcore]
      exact Subgroup.normalCore_le H
    exact hHne (top_le_iff.mp hle)

theorem isSolvable_of_lt_simple_card_5616 {Q : Type*} [Group Q] [Finite Q] {L Y : Subgroup Q}
    (hL : IsSimpleGroup ↥L) (hcard : Nat.card ↥L = 5616) (hYL : Y < L)
    (h27 : 27 ∣ Nat.card ↥Y) : Group.IsSolvable ↥Y := by
  have hn_dvd : Nat.card ↥Y ∣ 5616 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (le_of_lt hYL)
  have hHne : Y.subgroupOf L ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hYL) (le_antisymm (le_of_lt hYL) htop)
  have hcardH : Nat.card ↥(Y.subgroupOf L) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_of_lt hYL)).toEquiv
  have hmul : Nat.card (↥L ⧸ Y.subgroupOf L) * Nat.card ↥Y = Nat.card ↥L := by
    rw [← Subgroup.index_eq_card, ← hcardH]
    exact Subgroup.index_mul_card _
  rcases eq_27_mul_dvd_208_of_dvd_5616_of_dvd_27 hn_dvd h27 with
    h | h | h | h | h | h | h | h | h | h
  · exact isSolvable_of_coprime (a := 4) (b := 3) (m := 13) (by rw [h]; norm_num)
      (by rw [h]; norm_num)
  · exact isSolvable_of_coprime (a := 4) (b := 3) (m := 13) (by rw [h]; norm_num)
      (by rw [h]; norm_num)
  · exact isSolvable_of_coprime (a := 4) (b := 3) (m := 13) (by rw [h]; norm_num)
      (by rw [h]; norm_num)
  · exact isSolvable_of_coprime (a := 4) (b := 3) (m := 13) (by rw [h]; norm_num)
      (by rw [h]; norm_num)
  · exact isSolvable_of_coprime (a := 4) (b := 3) (m := 13) (by rw [h]; norm_num)
      (by rw [h]; norm_num)
  · haveI : Fintype ↥Y := Fintype.ofFinite _
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 3) (q := 13) (a := 3) (b := 1) (by norm_num) (by norm_num) (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, h]; norm_num
  · exfalso
    have hge := thirteen_le_card_quotient_subgroupOf_of_simple_card_5616 hL hcard hHne
    rw [h, hcard] at hmul
    omega
  · exfalso
    have hge := thirteen_le_card_quotient_subgroupOf_of_simple_card_5616 hL hcard hHne
    rw [h, hcard] at hmul
    omega
  · exfalso
    have hge := thirteen_le_card_quotient_subgroupOf_of_simple_card_5616 hL hcard hHne
    rw [h, hcard] at hmul
    omega
  · exact absurd (Subgroup.eq_of_le_of_card_ge (le_of_lt hYL) (by rw [hcard, h])) (ne_of_lt hYL)

theorem solvableOrSimpleDerived_of_le_index_two {Q : Type} [Group Q] [Finite Q]
    {M L Y P : Subgroup Q} (hLM : L ≤ M) (hidx : Nat.card ↥M = 2 * Nat.card ↥L)
    (hL : IsSimpleGroup ↥L) (hcard : Nat.card ↥L = 5616) (hYM : Y ≤ M) (hPY : P ≤ Y)
    (hPL : P ≤ L) (hP : Nat.card ↥P = 27) : SolvableOrSimpleDerived 5616 ↥Y := by
  have hP_Y1 : P ≤ Y ⊓ L := le_inf hPY hPL
  have h27 : 27 ∣ Nat.card ↥(Y ⊓ L) := by
    simpa [hP] using Subgroup.card_dvd_of_le hP_Y1
  have hcardL' : Nat.card ↥(L.subgroupOf M) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  have hidxL' : (L.subgroupOf M).index = 2 := by
    have h := Subgroup.index_mul_card (L.subgroupOf M)
    rw [hcardL', hidx] at h
    exact Nat.eq_of_mul_eq_mul_right (by rw [hcard]; norm_num) h
  haveI : (L.subgroupOf M).Normal := Subgroup.normal_of_index_eq_two hidxL'
  let φ : ↥Y →* ↥M ⧸ L.subgroupOf M :=
    (QuotientGroup.mk' (L.subgroupOf M)).comp (Subgroup.inclusion hYM)
  have hker : φ.ker = (Y ⊓ L).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hy
      refine ⟨y.2, ?_⟩
      have hy' : (Subgroup.inclusion hYM y : ↥M ⧸ L.subgroupOf M) = 1 := hy
      rw [QuotientGroup.eq_one_iff] at hy'
      simpa using (Subgroup.mem_subgroupOf.mp hy')
    · rintro ⟨-, hl⟩
      change (Subgroup.inclusion hYM y : ↥M ⧸ L.subgroupOf M) = 1
      rw [QuotientGroup.eq_one_iff]
      have : ((Subgroup.inclusion hYM y : ↥M) : Q) ∈ L := hl
      simpa using (Subgroup.mem_subgroupOf.mpr this)
  have hQcard : Nat.card (↥M ⧸ L.subgroupOf M) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hidxL'
  haveI : IsCyclic (↥M ⧸ L.subgroupOf M) := isCyclic_of_prime_card (p := 2) hQcard
  haveI : IsMulCommutative (↥M ⧸ L.subgroupOf M) := inferInstance
  rcases lt_or_eq_of_le (inf_le_right : Y ⊓ L ≤ L) with hlt | heq
  · have hsolvY1 : Group.IsSolvable ↥(Y ⊓ L) :=
      isSolvable_of_lt_simple_card_5616 hL hcard hlt h27
    haveI : Group.IsSolvable ↥((Y ⊓ L).subgroupOf Y) :=
      isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ L ≤ Y)) hsolvY1
    refine Or.inl ?_
    refine Group.isSolvable_of_ker_le_range (Subgroup.subtype ((Y ⊓ L).subgroupOf Y)) φ ?_
    rw [hker, Subgroup.range_subtype]
  · have hY1eq : Y ⊓ L = L := heq
    have hLY : L ≤ Y := by rw [← hY1eq]; exact inf_le_left
    have hkerB : φ.ker = L.subgroupOf Y := by rw [hker, hY1eq]
    haveI : (L.subgroupOf Y).Normal := by
      rw [← hkerB]
      infer_instance
    haveI : IsSimpleGroup ↥L := hL
    have hperfect : commutator ↥L = ⊤ := by
      rcases hL.eq_bot_or_eq_top_of_normal (commutator ↥L) with hbot | htop
      · exfalso
        haveI : IsMulCommutative ↥L := (commutator_eq_bot_iff (G := ↥L)).mp hbot
        have hprime : (Nat.card ↥L).Prime :=
          (Group.is_simple_iff_prime_card (α := ↥L)).mp inferInstance
        rw [hcard] at hprime
        norm_num at hprime
      · exact htop
    have hLsub : L.subgroupOf Y ≤ commutator ↥Y := by
      have hmap : (commutator ↥L).map (Subgroup.inclusion hLY) ≤ commutator ↥Y := by
        rw [commutator_def, Subgroup.map_commutator, commutator_def]
        exact Subgroup.commutator_mono le_top le_top
      have heq : (commutator ↥L).map (Subgroup.inclusion hLY) = L.subgroupOf Y := by
        rw [hperfect, Subgroup.map_top, Subgroup.inclusion_range hLY]
      rwa [heq] at hmap
    have hcomm_le : commutator ↥Y ≤ L.subgroupOf Y := by
      have hcomm_ker : commutator ↥Y ≤ φ.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm' _ _
      rwa [hkerB] at hcomm_ker
    have hcomm : commutator ↥Y = L.subgroupOf Y := le_antisymm hcomm_le hLsub
    refine Or.inr ⟨?_, ?_⟩
    · have e : ↥(commutator ↥Y) ≃* ↥L :=
        (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hLY)
      exact e.isSimpleGroup
    · have e : ↥(commutator ↥Y) ≃* ↥L :=
        (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hLY)
      rw [Nat.card_congr e.toEquiv, hcard]

end CFSG.StandardType.SimpleOrderFiveSixOneSix

end
