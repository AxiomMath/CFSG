module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDef
public import CFSG.Quasithin.H13.NQCoreP134Group

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.QuasithinUnique

section Cfg

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem OddCfg.isSylowTwoOf_inf [Finite A] (h : OddCfg p L P T) : IsSylowTwoOf (T ⊓ L) L := by
  have := h.normal
  exact CFSG.Quasithin.A4.isSylowTwoOf_inf_normal h.sylow le_top
    (by rw [Subgroup.normalizer_eq_top])

theorem OddCfg.mul_inf (h : OddCfg p L P T) :
    ∀ t ∈ T ⊓ L, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T ⊓ L, t * x = y * s := by
  intro t ht x hx
  obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht.1 x hx
  refine ⟨y, hy, s, ⟨hs, ?_⟩, he⟩
  have hs' : s = y⁻¹ * (t * x) := by rw [he]; group
  rw [hs']
  exact L.mul_mem (L.inv_mem (h.le hy)) (L.mul_mem ht.2 (h.le hx))

theorem OddCfg.exists_card (h : OddCfg p L P T) :
    ∃ a : ℕ, (a = 2 ∨ a = 3) ∧ Nat.card P = p ^ a := by
  rcases h.card with h2 | h3
  · exact ⟨2, Or.inl rfl, h2⟩
  · exact ⟨3, Or.inr rfl, h3⟩

theorem OddCfg.isPGroup (h : OddCfg p L P T) : IsPGroup p P :=
  fun x => ⟨1, Subtype.ext (by simpa using h.exp x x.2)⟩

theorem OddCfg.card_sup_inf [Finite A] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h : OddCfg p L P T) :
    Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = Nat.card P * Nat.card (T ⊓ L : Subgroup A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (h.sylow.2.1.to_le (inf_le_left : T ⊓ L ≤ T))
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (T ⊓ L : Subgroup A)) := by
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr (by omega)
    obtain ⟨a, -, ha⟩ := h.exists_card
    rw [hk, ha]
    exact Nat.Coprime.pow _ _ h2
  exact card_sup_eq_of_mul' hcop h.mul_inf

theorem OddCfg.sup_inf_le (h : OddCfg p L P T) : P ⊔ (T ⊓ L) ≤ L :=
  sup_le h.le inf_le_right

theorem OddCfg.not_isCyclic [hp : Fact p.Prime] (h : OddCfg p L P T) : ¬ IsCyclic P := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have h1 : g ^ p = 1 := Subtype.ext (by simpa using h.exp g g.2)
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  obtain ⟨a, ha, hPa⟩ := h.exists_card
  rw [hPa] at h2
  have h3 : p ^ 2 ∣ p ^ a := pow_dvd_pow p (by omega)
  have h4 : p ^ 2 ≤ p := (Nat.le_of_dvd hp.out.pos (h3.trans h2))
  have h5 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  omega

theorem OddCfg.exists_data [Finite A] [hp : Fact p.Prime] (hp5 : 5 ≤ p) (h : OddCfg p L P T) :
    ∃ a : ℕ, (a = 2 ∨ a = 3) ∧ ∃ S H Q : Subgroup ↥L,
      IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ S ≤ H ∧ Q ≤ H ∧ Nat.card H = p ^ a * Nat.card S ∧
        Nat.card Q = p ^ a ∧ (∀ x ∈ Q, x ^ p = 1) := by
  have hS := h.isSylowTwoOf_inf
  obtain ⟨a, ha, hPa⟩ := h.exists_card
  refine ⟨a, ha, (T ⊓ L).subgroupOf L, (P ⊔ (T ⊓ L)).subgroupOf L, P.subgroupOf L,
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, hS.2.2,
    Subgroup.subgroupOf_mono L le_sup_right, Subgroup.subgroupOf_mono L le_sup_left, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sup_inf_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, h.card_sup_inf hp5, hPa]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv, hPa]
  · intro x hx
    exact Subtype.ext (by simpa using h.exp x (Subgroup.mem_subgroupOf.mp hx))

end Cfg

theorem not_isCyclic_of_card_pow {G : Type*} [Group G] {Q : Subgroup G} {p a : ℕ}
    [hp : Fact p.Prime] (ha : 2 ≤ a) (hQ : Nat.card Q = p ^ a) (hexp : ∀ x ∈ Q, x ^ p = 1) :
    ¬ IsCyclic Q := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have h1 : g ^ p = 1 := Subtype.ext (by simpa using hexp g g.2)
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg, hQ] at h2
  have h3 : p ^ 2 ∣ p ^ a := pow_dvd_pow p ha
  have h4 : p ^ 2 ≤ p := Nat.le_of_dvd hp.out.pos (h3.trans h2)
  have h5 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  omega

@[expose] def NoPExt (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], F X → ∀ (p a : ℕ), p.Prime → 5 ≤ p → (a = 2 ∨ a = 3) →
    ∀ S H Q : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index → S ≤ H → Q ≤ H →
      Nat.card H = p ^ a * Nat.card S → Nat.card Q = p ^ a → (∀ x ∈ Q, x ^ p = 1) → False

theorem noOddCfg_of_noPExt {F : ∀ (X : Type) [Group X], Prop} (h : NoPExt F) : NoOddCfg F := by
  intro A _ _ p hp L P T hp5 hFL hcfg
  obtain ⟨a, ha, S, H, Q, hS2, hSi, hSH, hQH, hH, hQ, hQe⟩ := hcfg.exists_data hp5
  exact h ↥L hFL p a hp.out hp5 ha S H Q hS2 hSi hSH hQH hH hQ hQe

end CFSG.Quasithin.H13.NQCore
