module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieVB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieW
public import CFSG.LocalAnalysis.EvenBN.U4.Model.RankAut

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem vee_card_A1X : Nat.card (A1X h) = (2 ^ f) ^ 4 := by
  have e : A1X h = miyamotoA1G h ⊤ (etaX h) := sg_eq_pull h _
  rw [e]
  exact card_miyamotoA1G h ⊤ (etaX h)

theorem vee_card_V : Nat.card (Ssd h (A1X h) (fStab_A1X h) ⊥) = (2 ^ f) ^ 4 := by
  rw [card_Ssd, Subgroup.card_bot, mul_one, vee_card_A1X h]

theorem vee_B_le_P {E₀ : Subgroup (MulAut (Xg h))} (hE₀ : E₀ ≤ Ssd h (Psy h) (fStab_Psy h) ⊥) :
    vee_B h E₀ ≤ miyamotoP h := by
  intro x hx
  obtain ⟨a, haE, rfl⟩ := (vee_mem_B h).1 hx
  obtain ⟨s, hs, hcj⟩ := vee_cj_of_mem_Ssd_bot h (hE₀ haE)
  have : a = s := (cj_inj h).1 hcj
  subst this
  exact hs

theorem vee_card_B {E₀ : Subgroup (MulAut (Xg h))} (hE₀ : E₀ ≤ Ssd h (Psy h) (fStab_Psy h) ⊥) :
    Nat.card (vee_B h E₀) = Nat.card E₀ := by
  unfold vee_B
  rw [Subgroup.card_map_of_injective (gramSU h (miyamotoJ4 K)).subtype_injective]
  have hr : E₀ ≤ (MulAut.conj : Xg h →* MulAut (Xg h)).range := by
    intro α hα
    obtain ⟨s, -, rfl⟩ := vee_cj_of_mem_Ssd_bot h (hE₀ hα)
    exact ⟨s, rfl⟩
  have := Subgroup.card_map_of_injective (conj_hom_injective h)
    (K := E₀.comap (MulAut.conj : Xg h →* MulAut (Xg h)))
  rw [Subgroup.map_comap_eq_self hr] at this
  exact this.symm

theorem vee_B_comm {E₀ : Subgroup (MulAut (Xg h))} (hab : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a) :
    ∀ x ∈ vee_B h E₀, ∀ y ∈ vee_B h E₀, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := (vee_mem_B h).1 hx
  obtain ⟨b, hb, rfl⟩ := (vee_mem_B h).1 hy
  have := hab _ ha _ hb
  rw [← cj_mul, ← cj_mul] at this
  exact congrArg Subtype.val ((cj_inj h).1 this)

theorem V_unique (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) (E : Subgroup (MulAut (Xg h)))
    (hE : E ≤ Ssd h (Psy h) (fStab_Psy h) F₂) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1)
    (hcard : Nat.card E = Nat.card (Ssd h (A1X h) (fStab_A1X h) ⊥)) :
    E = Ssd h (A1X h) (fStab_A1X h) ⊥ := by
  set Nin := Ssd h (Psy h) (fStab_Psy h) ⊥ with hNin
  have hq : Nat.card E = (2 ^ f) ^ 4 := hcard.trans (vee_card_V h)
  have hθ : ∀ x ∈ E, miyamotoFieldFactor h x ∈ ({1, barE h} : Set (K ≃+* K)) := by
    intro x hx
    have h2 : miyamotoFieldFactor h x * miyamotoFieldFactor h x = 1 := by
      rw [← map_mul, ← sq, hsq x hx, map_one]
    by_cases h1 : miyamotoFieldFactor h x = 1
    · exact Or.inl h1
    · exact Or.inr (eq_barE_of_mul_self h h2 h1)
  have hcount : Nat.card E ≤ Nat.card (E ⊓ Nin : Subgroup (MulAut (Xg h))) * 2 := by
    have key := card_le_card_inf_mul_ncard (H := E) (N := Nin)
      (miyamotoFieldFactor h : MulAut (Xg h) → K ≃+* K) (T := {1, barE h}) (Set.toFinite _) hθ
      (fun x hx y hy hxy => by
        refine wcl_mem_Ssd_bot_of_factor h (F := F₂) (mul_mem (inv_mem (hE hx)) (hE hy)) ?_
        rw [map_mul, map_inv, hxy, inv_mul_cancel])
    have hT : ({1, barE h} : Set (K ≃+* K)).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    exact key.trans (Nat.mul_le_mul_left _ hT)
  by_cases hEN : E ≤ Nin
  · have hBP := vee_B_le_P h hEN
    have hBA := (card_le_and_eq_A1_of_commute h hBP (vee_B_comm h hab)).2
      ((vee_card_B h hEN).trans hq).ge
    have hEV : E ≤ Ssd h (A1X h) (fStab_A1X h) ⊥ := by
      intro α hα
      obtain ⟨s, hs, rfl⟩ := vee_cj_of_mem_Ssd_bot h (hEN hα)
      have hmem : (s : GL (Fin 4) K) ∈ vee_B h E := (vee_mem_B h).2 ⟨s, hα, rfl⟩
      rw [hBA] at hmem
      exact cj_mem_Ssd h hmem
    exact Subgroup.eq_of_le_of_card_ge hEV hcard.ge
  · exfalso
    obtain ⟨x, hxE, hxN⟩ := Set.not_subset.1 hEN
    obtain ⟨s, hs, φ, hφ, rfl, -⟩ := wcl_factor_of_mem_Ssd h (hE hxE)
    have hφ1 : φ ≠ 1 := by
      rintro rfl
      exact hxN (by rw [fa_one, mul_one]; exact cj_mem_Ssd h hs)
    have hσ : ∃ k, (φ : K →+* K) k ≠ k := by
      by_contra hno
      push Not at hno
      exact hφ1 (RingEquiv.ext hno)
    have hE₀N : E ⊓ Nin ≤ Nin := inf_le_right
    have hBP := vee_B_le_P h hE₀N
    have hBc := vee_B_comm h (E₀ := E ⊓ Nin) (fun a ha b hb => hab a ha.1 b hb.1)
    have hlt := two_mul_card_lt_of_twisted h hf (φ : K →+* K) hσ 1
      ((miyamotoP h).inv_mem hs) hBP hBc (fun y hy => by
        obtain ⟨a, haE, rfl⟩ := (vee_mem_B h).1 hy
        have hcomm := hab _ hxE (cj h a) haE.1
        have hxa : (cj h s * fa h φ) a = a := by
          apply (cj_inj h).1
          rw [← aut_mul_cj_mul_inv h, hcomm]
          group
        have hxa' : s * fa h φ a * s⁻¹ = a := by
          have e : (cj h s * fa h φ) a = s * fa h φ a * s⁻¹ := by
            rw [MulAut.mul_apply, MulAut.conj_apply]
          rw [← e]
          exact hxa
        have hc := congrArg (fun z : Xg h => (z : GL (Fin 4) K)) hxa'
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_miyamotoFieldAut_apply] at hc
        have e : Matrix.GeneralLinearGroup.map (φ : K →+* K) (a : GL (Fin 4) K) =
            glAut φ (a : GL (Fin 4) K) := Units.ext rfl
        rw [map_one, one_mul, inv_inv, e]
        exact hc)
    rw [vee_card_B h hE₀N] at hlt
    omega

end CFSG.Quasithin.H13.F431.Un.OL
