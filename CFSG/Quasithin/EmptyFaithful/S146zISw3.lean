module

public import CFSG.Quasithin.EmptyFaithful.S146zHOfour
public import CFSG.Quasithin.EmptyFaithful.S146zIAlg
public import CFSG.Quasithin.EmptyFaithful.S146zIGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Num

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.p_eq_three_of_mIdx_four (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (h4 : mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 4) :
    p = 3 ∧ Nat.card (Wsub h91 (uHi T M H H₁)) = 4 := by
  have hH : IsHTM T M H := hred.isHTM
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr₁ : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 := by
    have := h.mIdx_uK_sup_eq S hred
    omega
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4 := by
    rw [card_Wsub h91 hi₁, card_tildeOf_eq_relIndex (Z_le_uHi T M H H₁) (hi₁.trans hUZ),
      HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hi₁), hr₁]
    norm_num
  have hnt : ∃ w ∈ Wsub h91 (uHi T M H H₁), w ≠ 1 := by
    have h1 : 1 < Nat.card (Wsub h91 (uHi T M H H₁)) := by omega
    have : Nontrivial (Wsub h91 (uHi T M H H₁)) := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨w, hw⟩ := exists_ne (1 : Wsub h91 (uHi T M H H₁))
    exact ⟨w, w.2, fun e => hw (Subtype.ext e)⟩
  have hpW := h.prime_lt_card_Wsub S hred h91 hnt
  exact ⟨by omega, hcard⟩

theorem IsDecP.exists_DH_comm (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) {y : G} (hyH : y ∈ H)
    (hsw : conjSub y (uHi T M H H₁) = uHi T M H H₂) {DH : Subgroup G}
    (hDU : DH ≤ conjClosure (VZ T M) H) (hZD : quasithinOmegaOneCenter T ≤ DH)
    (hidx : DH.relIndex (conjClosure (VZ T M) H) ≤ 2) :
    ∃ d ∈ DH, d * y * d⁻¹ * y⁻¹ ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hW : Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) = ⊥ :=
    Wsub_inf_eq_bot h91 hi₁ hi₂ (Z_le_uHi T M H H₁) h.dir_inf.le
  have hinf : Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 DH = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨d, hd, hdD, rfl⟩ := exists_clsU_of_mem_Wsub h91 hDU hw.2
    have hyd : y * d * y⁻¹ * d⁻¹ ∈ quasithinOmegaOneCenter T := by
      have e : y * d * y⁻¹ * d⁻¹ = (d * y * d⁻¹ * y⁻¹)⁻¹ := by group
      rw [e, hall d hdD, inv_one]
      exact (quasithinOmegaOneCenter T).one_mem
    have h1 : rhoH h91 ⟨y, hyH⟩ (clsU h91 hd) = clsU h91 hd :=
      (rhoH_clsU_eq_iff h91 ⟨y, hyH⟩ hd).mpr hyd
    have h2 : rhoH h91 ⟨y, hyH⟩ (clsU h91 hd) ∈ Wsub h91 (uHi T M H H₂) :=
      rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₁ hsw hw.1
    rw [h1] at h2
    have h3 : clsU h91 hd ∈ Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) := ⟨hw.1, h2⟩
    rw [hW, Subgroup.mem_bot] at h3
    exact h3
  have h4 : Nat.card (Wsub h91 (uHi T M H H₁)) ≤ (Wsub h91 DH).index :=
    card_le_index_of_inf_eq_bot _ _ hinf
  have hrange : (valW h91).range =
      tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact w.val_mem
    · intro hx
      exact ⟨IntMod.mk h91.isElemAbelian_tilde ⟨x, hx⟩, rfl⟩
  have hindex : (Wsub h91 DH).index = DH.relIndex (conjClosure (VZ T M) H) := by
    unfold Wsub
    rw [Subgroup.index_comap, hrange]
    exact relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (B := quasithinOmegaOneCenter T) hZD hDU (U_le_normalizer h91)
  rw [hindex] at h4
  omega

end Num

end CFSG.Quasithin
