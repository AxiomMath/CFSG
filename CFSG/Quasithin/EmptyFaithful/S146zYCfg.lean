module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.H13.NQCoreP134Group
public import CFSG.Quasithin.H13.NQCoreP134Inputs

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.H13.NQCore

structure E25Config {A : Type} [Group A] (L P T : Subgroup A) : Prop where
  normal : L.Normal
  le : P ≤ L
  card : Nat.card P = 25
  exp : ∀ x ∈ P, x ^ 5 = 1
  sylow : IsSylowTwoOf T ⊤
  mul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s
  irred : ∀ U : Subgroup A, U ≤ P →
    T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) → U = ⊥ ∨ U = P

@[expose] def NoE25Config (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A), F ↥L → E25Config L P T → False

@[expose] def NoElemTwentyFive (X : Type*) [Group X] : Prop :=
  ∀ Q : Subgroup X, Nat.card Q = 25 → (∀ x ∈ Q, x ^ 5 = 1) → False

theorem NoElemTwentyFive.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoElemTwentyFive Y) : NoElemTwentyFive X := by
  intro Q hQ hexp
  refine h (Q.map e.toMonoidHom) ?_ ?_
  · rw [← hQ]
    exact (Nat.card_congr (Q.equivMapOfInjective _ e.injective).toEquiv).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

theorem not_isCyclic_of_card_twentyFive {X : Type*} [Group X] {Q : Subgroup X}
    (hQ : Nat.card Q = 25) (hexp : ∀ x ∈ Q, x ^ 5 = 1) : ¬ IsCyclic Q := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have h5 : g ^ 5 = 1 := Subtype.ext (by simpa using hexp g g.2)
  have := orderOf_dvd_of_pow_eq_one h5
  rw [hg, hQ] at this
  norm_num at this

theorem noElemTwentyFive_of_isCyclic {X : Type*} [Group X]
    (h : ∀ Q : Subgroup X, IsPGroup 5 Q → IsCyclic Q) : NoElemTwentyFive X := by
  intro Q hQ hexp
  refine not_isCyclic_of_card_twentyFive hQ hexp (h Q ?_)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  exact IsPGroup.iff_card.mpr ⟨2, by rw [hQ]; norm_num⟩

section Config

variable {A : Type} [Group A] {L P T : Subgroup A}

theorem E25Config.of_oddConfig [Finite A] (h : OddConfig 5 L P T) (hc : Nat.card P = 25) :
    E25Config L P T where
  normal := h.normal
  le := h.le
  card := hc
  exp := h.exp
  sylow := h.sylow
  mul := h.mul
  irred := by
    intro U hUP hN
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hPab : IsMulCommutative ↥P :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by simpa using hc)
    have hcomm : ⁅P, P⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hPab
    exact h.irred U (hcomm ▸ bot_le) hUP hN |>.imp (fun h' => hcomm ▸ h') id

theorem E25Config.exists_subgroup (h : E25Config L P T) :
    ∃ Q : Subgroup L, Nat.card Q = 25 ∧ ∀ x ∈ Q, x ^ 5 = 1 :=
  ⟨P.subgroupOf L, by
    rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv,
    fun x hx => Subtype.ext (by simpa using h.exp x (Subgroup.mem_subgroupOf.mp hx))⟩

theorem E25Config.twentyFive_dvd_card (h : E25Config L P T) : 25 ∣ Nat.card L :=
  h.card ▸ Subgroup.card_dvd_of_le h.le

theorem E25Config.isSylowTwoOf_inf [Finite A] (h : E25Config L P T) :
    IsSylowTwoOf (T ⊓ L) L :=
  have := h.normal
  RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow le_top
    (Subgroup.Normal.isSubnormal inferInstance).subgroupOf

theorem E25Config.mul_inf (h : E25Config L P T) :
    ∀ t ∈ T ⊓ L, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T ⊓ L, t * x = y * s := by
  intro t ht x hx
  obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht.1 x hx
  refine ⟨y, hy, s, ⟨hs, ?_⟩, he⟩
  have hs' : s = y⁻¹ * (t * x) := by rw [he]; group
  rw [hs']
  exact L.mul_mem (L.inv_mem (h.le hy)) (L.mul_mem ht.2 (h.le hx))

theorem E25Config.card_sup_inf [Finite A] (h : E25Config L P T) :
    Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = 25 * Nat.card (T ⊓ L : Subgroup A) := by
  have hT2 : IsPGroup 2 (T ⊓ L : Subgroup A) := h.sylow.2.1.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT2
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (T ⊓ L : Subgroup A)) := by
    rw [h.card, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  rw [card_sup_eq_of_mul' hcop (E25Config.mul_inf h), h.card]

theorem E25Config.sup_inf_le (h : E25Config L P T) : P ⊔ (T ⊓ L) ≤ L :=
  sup_le h.le inf_le_right

theorem E25Config.exists_model [Finite A] (h : E25Config L P T) {X : Type*} [Group X]
    (e : ↥L ≃* X) : ∃ H : Subgroup X, ∃ k : ℕ, Nat.card H = 25 * 2 ^ k ∧ 2 ^ k ∣ Nat.card X ∧
      ¬ 2 ∣ Nat.card X / 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := E25Config.isSylowTwoOf_inf h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hcardX : Nat.card X = Nat.card L := (Nat.card_congr e.toEquiv).symm
  have hidx := ((T ⊓ L).subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hk] at hidx
  refine ⟨((P ⊔ (T ⊓ L)).subgroupOf L).map e.toMonoidHom, k, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E25Config.sup_inf_le h)).toEquiv,
      E25Config.card_sup_inf h, hk]
  · rw [hcardX, ← hidx]
    exact Dvd.intro _ rfl
  · rw [hcardX, ← hidx, Nat.mul_div_cancel_left _ (by positivity)]
    exact hS.2.2

end Config

theorem noE25Config_of_noElem {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → NoElemTwentyFive X) : NoE25Config F := by
  intro A _ _ L P T hL hcfg
  obtain ⟨Q, hQ, hexp⟩ := E25Config.exists_subgroup hcfg
  exact hF L hL Q hQ hexp

theorem noE25Config_of_not_dvd {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → ¬ 25 ∣ Nat.card X) : NoE25Config F := by
  intro A _ _ L P T hL hcfg
  exact hF L hL (E25Config.twentyFive_dvd_card hcfg)

end CFSG.Quasithin.S146zY
