module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBF4

variable (K : Type) [Field K]

@[expose] def torusPow (p : ℕ) : Subgroup (adjointGroup .F4 K) where
  carrier := {g | (g : ModGL .F4 K) ∈ torusGroup .F4 K ∧ g ^ p = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    have hc : Commute a b := Subtype.ext
      (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha.1)
        (torusGroup_le_diagonalGroup hb.1))
    rw [hc.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

variable {K}

theorem mem_torusPow {p : ℕ} {g : adjointGroup .F4 K} :
    g ∈ torusPow K p ↔ (g : ModGL .F4 K) ∈ torusGroup .F4 K ∧ g ^ p = 1 :=
  Iff.rfl

theorem card_torusPow [Finite K] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) :
    Nat.card (torusPow K p) = p ^ 4 := by
  have hmap : (((torusPow K p).map (adjointGroup .F4 K).subtype : Subgroup (ModGL .F4 K)) :
      Set (ModGL .F4 K)) = {h : ModGL .F4 K | h ∈ torusGroup .F4 K ∧ h ^ p = 1} := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg.1, by rw [← map_pow, hg.2, map_one]⟩
    · rintro ⟨hh, hp1⟩
      refine ⟨⟨h, CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4 hh⟩, ⟨hh, ?_⟩, rfl⟩
      exact Subtype.ext (by rw [Subgroup.coe_pow, hp1, OneMemClass.coe_one])
  rw [← CFSG.RankThree.Chevalley.F4_natCard_torusPow (k := K) hp
    (by rw [Nat.card_units]; exact hpq), ← hmap,
    ← Subgroup.card_map_of_injective (adjointGroup .F4 K).subtype_injective]
  rfl

theorem ordF4_eq_mul {q : ℕ} (hq : 1 ≤ q) :
    CFSG.Open.ordF4 q = (q - 1) ^ 4 * (q ^ 24 * ((∑ i ∈ Finset.range 12, q ^ i) *
      (∑ i ∈ Finset.range 8, q ^ i) * (∑ i ∈ Finset.range 6, q ^ i) *
      (∑ i ∈ Finset.range 2, q ^ i))) := by
  have key : ∀ k, q ^ k - 1 = (∑ i ∈ Finset.range k, q ^ i) * (q - 1) := by
    intro k
    have h := geom_sum_mul_add (q - 1) k
    rw [Nat.sub_add_cancel hq] at h
    rw [← h, Nat.add_sub_cancel]
  rw [CFSG.Open.ordF4, key 12, key 8, key 6, key 2]
  ring

theorem not_dvd_mul_geomSums {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) :
    ¬ p ∣ q ^ 24 * ((∑ i ∈ Finset.range 12, q ^ i) * (∑ i ∈ Finset.range 8, q ^ i) *
      (∑ i ∈ Finset.range 6, q ^ i) * (∑ i ∈ Finset.range 2, q ^ i)) := by
  have hq1 : (q : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hpq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  have h1152 : ¬ p ∣ 1152 := by
    intro h
    have h' : p ∣ 2 ^ 7 * 3 ^ 2 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
      omega
  rw [← ZMod.natCast_eq_zero_iff] at h1152 ⊢
  intro h
  apply h1152
  rw [← h]
  push_cast
  simp only [hq1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  norm_num

theorem not_dvd_index_torusGroup [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup .F4 K).subgroupOf (adjointGroup .F4 K)).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := Subgroup.card_mul_index ((torusGroup .F4 K).subgroupOf (adjointGroup .F4 K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4).toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_F4,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, ordF4_eq_mul hq] at hcard
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < (Nat.card K - 1) ^ 4 := pow_pos (by omega) 4
  rw [Nat.eq_of_mul_eq_mul_left hpos hcard]
  exact not_dvd_mul_geomSums hp hp5 hq hpq

theorem exists_conj_le_torusPow [Finite K] {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((torusGroup .F4 K).subgroupOf (adjointGroup .F4 K)).index)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) :
    ∃ g : adjointGroup .F4 K, E.map (MulAut.conj g).toMonoidHom ≤ torusPow K p := by
  have := Fact.mk hp
  have : Finite (adjointGroup .F4 K) := CFSG.LieType.Chevalley.generated_group_finite .F4 K
  set H' := (torusGroup .F4 K).subgroupOf (adjointGroup .F4 K) with hH'
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p H'))
  have hPp : IsPGroup p ((P : Subgroup H').map H'.subtype) := P.isPGroup'.map _
  have hPidx : ¬ p ∣ ((P : Subgroup H').map H'.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact P.not_dvd_index h
    · exact hidx h
  obtain ⟨Q, hEQ⟩ := (TableB.isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .F4 K) Q (hPp.toSylow hPidx)
  refine ⟨g, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hmem : (MulAut.conj g).toMonoidHom e ∈ ((g • Q : Sylow p _) : Subgroup _) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    convert hEQ he using 1
    simp only [MulAut.smul_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.inv_apply,
      MulAut.conj_symm_apply]
    group
  rw [hg] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  refine ⟨?_, ?_⟩
  · rw [← hz]
    exact z.2
  · rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 e he, map_one]

end TableBF4

open TableBF4 in
@[expose] def GGF4ToralRankInput (K : Type) [Field K]
    (p : ℕ) : Prop :=
  ∀ E : Subgroup (adjointGroup .F4 K), IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
    ∃ g : adjointGroup .F4 K, E.map (MulAut.conj g).toMonoidHom = torusPow K p

open TableBF4 in
theorem GGF4ToralRankInput.card_le {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (h : GGF4ToralRankInput K p) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 4 := by
  by_contra hlt
  obtain ⟨g, hg⟩ := h E hE (not_le.mp hlt).le
  have h1 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [hg, card_torusPow hp hpq] at h1
  omega

namespace TableBF4

variable {K : Type} [Field K]


theorem ggF4ToralRankInput_of_five_le [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : GGF4ToralRankInput K p := by
  intro E hE hcard
  obtain ⟨g, hg⟩ := exists_conj_le_torusPow hp (not_dvd_index_torusGroup hp hp5 hpq) hE
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [card_torusPow hp hpq, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hcard

end TableBF4

end CFSG.StandardType
