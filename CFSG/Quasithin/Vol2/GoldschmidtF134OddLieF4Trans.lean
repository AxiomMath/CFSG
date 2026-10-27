module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Inner
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg

public section

namespace CFSG.Quasithin.H13.NQCore.F4

open CFSG.QuasithinUnique
open scoped commutatorElement

theorem false_of_centralizes {A : Type} [Group A] {p : ℕ} [hp : Fact p.Prime] {L P T : Subgroup A}
    (hcfg : OddCfg p L P T) (hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hcen : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ P, t * x * t⁻¹ = x) : False := by
  obtain ⟨a, ha, hPa⟩ := hcfg.exists_card
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall P).2 hcon, Subgroup.card_bot] at hPa
    have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.out.one_lt
    omega
  have hxp : orderOf x = p := orderOf_eq_prime (hcfg.exp x hxP) hx1
  have hQP : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.2 hxP
  have hN : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set A) := by
    have hfwd : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ y ∈ Subgroup.zpowers x,
        t * y * t⁻¹ ∈ Subgroup.zpowers x := by
      intro t ht y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← conj_zpow, hcen t ht x hxP]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd t ht y, fun hy => ?_⟩
    have h := hfwd t⁻¹ ((T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht) _ hy
    have e1 : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [e1] at h
  have hPP : ⁅P, P⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu v hv
    have h := hPcomm v hv u⁻¹ (P.inv_mem hu)
    rw [Subgroup.mem_bot, commutatorElement_def, mul_assoc u v, h]
    group
  rcases hcfg.irred _ (by rw [hPP]; exact bot_le) hQP hN with h | h
  · rw [hPP] at h
    exact hx1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers x))
  · rw [← h, Nat.card_zpowers, hxp] at hPa
    have h1 : p ^ 1 < p ^ a := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
    rw [pow_one] at h1
    omega

theorem false_of_odd_out {A : Type} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {L P T : Subgroup A} (hcfg : OddCfg p L P T)
    (hZ : Subgroup.center ↥L = ⊥) {m : ℕ} (hm : Odd m)
    (hout : ∀ α : MulAut ↥L, ∃ y : ↥L, α ^ m = MulAut.conj y)
    (hcont : ∀ (a : ℕ) (S H : Subgroup ↥L), (a = 2 ∨ a = 3) → IsSylowTwoOf S ⊤ → S ≤ H →
      Nat.card H = p ^ a * Nat.card S → H ≤ Subgroup.normalizer (S : Set ↥L))
    (hcomm : ∀ S : Subgroup ↥L, IsSylowTwoOf S ⊤ → ∀ x ∈ Subgroup.normalizer (S : Set ↥L),
      ∀ y ∈ Subgroup.normalizer (S : Set ↥L), x * y * x⁻¹ * y⁻¹ ∈ S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hLn := hcfg.normal
  have hS := hcfg.isSylowTwoOf_inf
  obtain ⟨a, ha, hPa⟩ := hcfg.exists_card
  have hS' : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hS
  have hcardsub : ∀ {S : Subgroup A}, S ≤ L → Nat.card (S.subgroupOf L) = Nat.card S :=
    fun h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hSH : (T ⊓ L).subgroupOf L ≤ (P ⊔ T ⊓ L).subgroupOf L :=
    Subgroup.subgroupOf_mono L le_sup_right
  have hHcard : Nat.card ((P ⊔ T ⊓ L).subgroupOf L) = p ^ a * Nat.card ((T ⊓ L).subgroupOf L) := by
    rw [hcardsub hcfg.sup_inf_le, hcfg.card_sup_inf hp5, hPa, hcardsub inf_le_right]
  have hHN := hcont a _ _ ha hS' hSH hHcard
  have hPN : ∀ (x : A) (hx : x ∈ P), (⟨x, hcfg.le hx⟩ : ↥L) ∈
      Subgroup.normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := fun x hx =>
    hHN (Subgroup.mem_subgroupOf.2 (le_sup_left (α := Subgroup A) hx))
  have hPU : ∀ y ∈ P, ∀ u ∈ T ⊓ L, y * u * y⁻¹ ∈ T ⊓ L := by
    intro y hy u hu
    have h := (Subgroup.mem_normalizer_iff.1 (hPN y hy) ⟨u, hu.2⟩).1
      (Subgroup.mem_subgroupOf.2 hu)
    exact Subgroup.mem_subgroupOf.1 h
  have hdisj : Disjoint P (T ⊓ L) :=
    IsPGroup.disjoint_of_ne p 2 hp2 P (T ⊓ L) hcfg.isPGroup (hcfg.sylow.2.1.to_le inf_le_left)
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 := hcomm _ hS' _ (hPN x hx) _ (hPN y hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 h1
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx))
      (P.inv_mem hy)
    have h4 := Subgroup.disjoint_def.1 hdisj h3 h2
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h4, one_mul]
  refine false_of_centralizes hcfg hPcomm fun t ht x hx => ?_
  have htU : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup A) : Set A) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht.1,
      (Subgroup.normalizer_eq_top_iff.mpr hLn).symm ▸ Subgroup.mem_top t⟩
  exact centralizes_of_odd_out hZ hS hcfg.le hp2 hcfg.isPGroup hPU hm hout
    (hcfg.sylow.2.1.to_le (Subgroup.zpowers_le.mpr ht.1)) htU ht.2 hx

end CFSG.Quasithin.H13.NQCore.F4
