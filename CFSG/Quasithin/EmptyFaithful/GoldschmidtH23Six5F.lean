module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Defs
public import CFSG.Quasithin.EmptyFaithful.S151b110
public import CFSG.Quasithin.EmptyFaithful.T1515A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section FPart

variable {T Mc M : Subgroup G}

theorem V154_eq_VZ_of_six5 (h5 : Ce15Six T Mc M 5) : V154 T Mc M = VZ T M := by
  by_cases hc : Case1512Six T Mc M
  · exfalso
    have h1 := h5.card_eq
    rw [V154_eq_uJ hc] at h1
    have h2 := hc.2.2.2.1
    omega
  · exact V154_eq_VZ hc

theorem card_A₀_of_isInternalDirect {X : Type} [Group X] [Finite X] {p : ℕ} [NeZero p]
    {A A₁ A₂ : Subgroup X} (hd : IsInternalDirect A A₁ A₂) (e₁ : A₁ ≃* DihedralGroup p)
    (e₂ : A₂ ≃* DihedralGroup p) : Nat.card A = (2 * p) * (2 * p) := by
  obtain ⟨hA, hinf, hcomm⟩ := hd
  have h := (card_sup_mul_card_inf_of_commute151b A₁ A₂ hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one] at h
  rw [hA, h, Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv, Nat.card_eq_fintype_card,
    DihedralGroup.card]

theorem not_ce15Small_of_six5 (h5 : Ce15Six T Mc M 5) : ¬ Ce15Small T Mc M := by
  rintro (h4 | h3 | h7)
  · have h := h4.card_eq
    rw [h5.card_eq] at h
    omega
  · obtain ⟨-, A₁, A₂, hd, ⟨e₁⟩, ⟨e₂⟩, -⟩ := h3
    obtain ⟨-, B₁, B₂, hd', ⟨f₁⟩, ⟨f₂⟩, -⟩ := h5
    have h1 := card_A₀_of_isInternalDirect hd e₁ e₂
    have h2 := card_A₀_of_isInternalDirect hd' f₁ f₂
    omega
  · exact h5.not_seven h7

theorem exists_six5Data (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h5 : Ce15Six T Mc M 5) (hV : IsElemAbelian 2 (V154 T Mc M)) :
    ∃ d : Six5Data T M (V154 T Mc M) hV, mBar0 T Mc M = d.S.A₁ ⊔ d.S.A₂ := by
  have hTM : T ≤ M := hM.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hA0 : mBar0 T Mc M = Jhat (autI hV M) := JhatOn_eq hV
  obtain ⟨S, hA₁X, hA₂X, hτX, hsup, hcard⟩ :=
    exists_sixData151b hV hTM hMN hA0 (Or.inr rfl) h5
  exact ⟨⟨hMN, hTM, isSylowTwoOf_of_le151 hq.sylow hTM, S, hA₁X, hA₂X, hτX, hsup, hcard⟩,
    hA0.trans hsup.symm⟩

end FPart

end CFSG.Quasithin
