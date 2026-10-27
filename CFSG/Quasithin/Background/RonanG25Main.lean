module

public import CFSG.Quasithin.Background.RonanG25GroupSS
public import CFSG.Quasithin.Background.RonanG25GroupSU
public import CFSG.Quasithin.Background.RonanG25GroupU
public import CFSG.Quasithin.Background.RonanG25GroupOrd
public import CFSG.Quasithin.Background.RonanG25Tail
public import CFSG.Quasithin.Background.RonanG25Restrict
public import CFSG.Quasithin.Background.RonanG25Series

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section Main

theorem card_gf {n : ℕ} (hn : 0 < n) :
    ∃ m : ℕ, 0 < m ∧ Nat.card (GaloisField 2 n) = 2 ^ m := by
  refine ⟨n, hn, ?_⟩
  exact GaloisField.card 2 n hn.ne'

theorem two_lt_card_iff {n : ℕ} (hn : 0 < n) :
    2 < Nat.card (GaloisField 2 n) ↔ 1 < n := by
  rw [GaloisField.card 2 n hn.ne']
  constructor
  · intro h
    by_contra hle
    have : n = 1 := by omega
    subst this
    simp at h
  · intro h
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) h

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G}

theorem head_restrict {F : Type} [Field F] [Finite F] {X P : Subgroup G} {a b : ℕ}
    (h : ChainCounts F X false ⊥ P a b) (hPN : P ≤ Subgroup.normalizer (X : Set G)) :
    ChainCounts F X false ⊥ (X ⊓ P) a b := by
  have hPinv : Inv X P := h.invRight
  have hQinv : Inv X (X ⊓ P) := fun x hx q hq =>
    ⟨X.mul_mem (X.mul_mem hx hq.1) (X.inv_mem hx), hPinv x hx q hq.2⟩
  have hcomm : ∀ x ∈ X, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ X ⊓ P := by
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · have h1 : y * x⁻¹ * y⁻¹ ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (hPN hy) x⁻¹).mp (X.inv_mem hx)
        simpa [mul_assoc] using this
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact X.mul_mem hx h1
    · exact P.mul_mem (hPinv x hx y hy) (P.inv_mem hy)
  have hres := h.restrict hQinv hPinv hcomm (le_refl P)
  have e1 : (X ⊓ P) ⊓ ⊥ = ⊥ := inf_bot_eq _
  have e2 : (X ⊓ P) ⊓ P = X ⊓ P := by rw [inf_assoc, inf_idem]
  rw [e1, e2] at hres
  exact hres

theorem chain_SU_group (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord ⊥ (gS V H L ⊔ conjClosure V H) (r + s + 2)
      (if 2 < Nat.card (GaloisField 2 n) then r + s + 1 else 0) := by
  have h1 := chain_V_group St (ord := ord)
  have h2 := chain_V_S₂_group St hsub (ord := ord)
  have h3 := chain_S₂_S₃_group St hg hh hsub hsum (ord := ord)
  have h4 := chain_S₃_S_group St hg hh hsub hsum (ord := ord)
  have h5 := chain_S_SU_group St hsub (ord := ord)
  have h := (((h1.trans h2).trans h3).trans h4).trans h5
  have e1 : r + s + 2 = 1 + 0 + s + r + 1 := by omega
  have e2 : (if 2 < Nat.card (GaloisField 2 n) then r + s + 1 else 0) =
      (((if 2 < Nat.card (GaloisField 2 n) then 1 else 0) + 0 +
        if 2 < Nat.card (GaloisField 2 n) then s else 0) +
        if 2 < Nat.card (GaloisField 2 n) then r else 0) + 0 := by
    split_ifs <;> omega
  rw [e1, e2]
  exact h

theorem chain_U_group (St : L3Setting n V V₁ L T H) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord ⊥ (conjClosure V H) (s + 2)
      (if 2 < Nat.card (GaloisField 2 n) then r + 1 else 0) := by
  have h1 := chain_V_group St (ord := ord)
  have h2 := chain_V_S₂_group St hsub (ord := ord)
  have h3 := chain_S₂_WS₃_group St hg hh hV hsub hsum (ord := ord)
  have h4 := chain_WS₃_W_group St hg hh hsub hsum (ord := ord)
  have h5 := chain_W_U_group St hsub (ord := ord)
  have h := (((h1.trans h2).trans h3).trans h4).trans h5
  have e1 : s + 2 = 1 + 0 + s + 0 + 1 := by omega
  have e2 : (if 2 < Nat.card (GaloisField 2 n) then r + 1 else 0) =
      (((if 2 < Nat.card (GaloisField 2 n) then 1 else 0) + 0 + 0) +
        if 2 < Nat.card (GaloisField 2 n) then r else 0) + 0 := by
    split_ifs <;> omega
  rw [e1, e2]
  exact h

theorem counts_SU (St : L3Setting n V V₁ L T H) (hn : 0 < n) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) :
    HasChiefCounts (GaloisField 2 n) (lOne L V₁) (gS V H L ⊔ conjClosure V H) (r + s + 2)
      (if 1 < n then r + s + 1 else 0) := by
  have := (chain_SU_group St hg hh hsub hsum (ord := false)).hasChiefCounts (card_gf hn)
  simpa only [two_lt_card_iff hn] using this

theorem counts_U (St : L3Setting n V V₁ L T H) (hn : 0 < n) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) :
    HasChiefCounts (GaloisField 2 n) (lOne L V₁) (conjClosure V H) (s + 2)
      (if 1 < n then r + 1 else 0) := by
  have := (chain_U_group St hg hh hV hsub hsum (ord := false)).hasChiefCounts (card_gf hn)
  simpa only [two_lt_card_iff hn] using this

theorem counts_L₁ (St : L3Setting n V V₁ L T H) (hn : 0 < n) {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hsub : SubFacts V L H g h) {r s : ℕ}
    {φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n)}
    {φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)}
    (hsum : SumFacts St.D g h hg hh r s φ₇ φ₆) :
    HasOrdinaryTwoChiefCounts (GaloisField 2 n) (lOne L V₁) (r + s + 2)
      (if 1 < n then r + s + 1 else 0) := by
  have hSU := chain_SU_group St hg hh hsub hsum (ord := false)
  have hPN : gS V H L ⊔ conjClosure V H ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    SU_le_normalizer_lOne St hsub
  have hres := head_restrict hSU hPN
  have hres' := hres.toOrd
  have hPinv : Inv (lOne L V₁) (gS V H L ⊔ conjClosure V H) := hSU.invRight
  have hQinv : Inv (lOne L V₁) (lOne L V₁ ⊓ (gS V H L ⊔ conjClosure V H)) := fun x hx q hq =>
    ⟨(lOne L V₁).mul_mem ((lOne L V₁).mul_mem hx hq.1) ((lOne L V₁).inv_mem hx),
      hPinv x hx q hq.2⟩
  have htail : ChainCounts (GaloisField 2 n) (lOne L V₁) true
      (lOne L V₁ ⊓ (gS V H L ⊔ conjClosure V H)) (lOne L V₁) 0 0 := by
    have hQX : lOne L V₁ ⊓ (gS V H L ⊔ conjClosure V H) ≤ lOne L V₁ := inf_le_left
    have hker : ∀ x : ↥(lOne L V₁), piHom St x = 1 ↔
        (x : G) ∈ lOne L V₁ ⊓ (gS V H L ⊔ conjClosure V H) := fun x => by
      rw [piHom_ker St hsub x]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    by_cases hF : 2 < Nat.card (GaloisField 2 n)
    · exact tail_big hF hQX hQinv (piHom St) hker (piHom_surj_SL St hF)
    · have h2 : Nat.card (GaloisField 2 n) = 2 := by
        have : 1 < Nat.card (GaloisField 2 n) := Finite.one_lt_card
        omega
      exact tail_small h2 hQX hQinv (piHom St) hker
  have hall := hres'.trans htail
  simp only [add_zero] at hall
  have := hall.hasOrdinaryTwoChiefCounts (card_gf hn)
  simpa only [two_lt_card_iff hn] using this

end Main

end CFSG.Quasithin.RonanG25
