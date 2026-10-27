module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Local
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Model
public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import Certificates.Certificate9549

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Quasithin.B42G2Id CFSG.Timmesfeld.RankTwo
  CFSG.RankThree.PartTwo.KFacts

section R


abbrev rMon : Submonoid (Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8) :=
  Submonoid.closure {x | ∃ g ∈ rGens, dec2 g = x}

theorem rFacts :
    (∀ e ∈ rMon, ∀ y ∈ rMon, e ^ 3 = 1 → e ≠ 1 → y ^ 7 = 1 → y ≠ 1 → e * y ≠ y * e) ∧
    (∀ e ∈ rMon, ∀ t ∈ rMon, ∀ t' ∈ rMon, e ^ 3 = 1 → e ≠ 1 → t ^ 2 = 1 → t ≠ 1 →
      t' ^ 2 = 1 → t' ≠ 1 → t ≠ t' → t * e = e * t → t' * e = e * t' → t * t' = t' * t →
        False) ∧
    (∀ e ∈ rMon, ∀ u ∈ rMon, ∀ t ∈ rMon, e ^ 3 = 1 → e ≠ 1 → u ^ 3 = 1 → u ≠ 1 → u ≠ e →
      u ≠ e * e → t ^ 2 = 1 → t ≠ 1 → t * e = e * t → t * u = u * t → u * e = e * u →
        False) :=
  have h := Certificates.certificate9549 rMon rfl
  ⟨h.1, h.2.1, h.2.2.1⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem rho_letterElt_gen {r : ℕ} (hr : r = 5 ∨ r = 0 ∨ r = 6 ∨ r = 11) :
    ∃ g ∈ rGens, M.rho (M.letterElt (8 * r + 1)) = dec2 g := by
  obtain ⟨-, -, -, h1, h2, h3, h4⟩ := Certificates.certificate9549 rMon rfl
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨rGenXb, by simp [rGens], by rw [G28Model.rho_letterElt, h1]⟩
  · exact ⟨rGenXa, by simp [rGens], by rw [G28Model.rho_letterElt, h2]⟩
  · exact ⟨rGenYa, by simp [rGens], by rw [G28Model.rho_letterElt, h3]⟩
  · exact ⟨rGenYb, by simp [rGens], by rw [G28Model.rho_letterElt, h4]⟩

@[expose] def InS (g : ↥(adjointGroup .G2 K)) : Prop := M.rho g ∈ rMon

theorem inS_one : InS M 1 := by
  unfold InS
  rw [map_one]
  exact one_mem _

theorem InS.mul_letter {g : ↥(adjointGroup .G2 K)} (hg : InS M g) {r : ℕ}
    (hr : r = 5 ∨ r = 0 ∨ r = 6 ∨ r = 11) : InS M (g * M.letterElt (8 * r + 1)) := by
  obtain ⟨gc, hgc, hρg⟩ := rho_letterElt_gen M hr
  unfold InS at hg ⊢
  rw [map_mul, hρg]
  exact mul_mem hg (Submonoid.subset_closure ⟨gc, hgc, rfl⟩)

theorem InS.mul_xPar {g : ↥(adjointGroup .G2 K)} (hg : InS M g) {r : ℕ}
    (hr : r = 5 ∨ r = 0 ∨ r = 6 ∨ r = 11) {c : K} (hc : c = 0 ∨ c = 1) :
    InS M (g * xPar (rootOperatorFamily .G2) (rootVec r) c) := by
  rcases hc with rfl | rfl
  · have h0 : xPar (rootOperatorFamily .G2) (rootVec r) (0 : K) = 1 :=
      xPar_zero (F := rootOperatorFamily .G2) (rootVec r)
    simpa [h0] using hg
  · have e1 : (8 * r + 1) / 8 = r := by omega
    have e2 : (8 * r + 1) % 8 = 1 := by omega
    have h1 : xPar (rootOperatorFamily .G2) (rootVec r) (1 : K) = M.letterElt (8 * r + 1) := by
      simp only [G28Model.letterElt, e1, e2]
      have : CFSG.Quasithin.GF8.ofNat' 1 = 1 := rfl
      rw [this, map_one]
    have key := hg.mul_letter M hr
    rw [← h1] at key
    exact key

theorem InS.mul_simple {g : ↥(adjointGroup .G2 K)} (hg : InS M g) (i : Fin Tag.G2.rank) {c : K}
    (hc : c = 0 ∨ c = 1) :
    InS M (g * xPar (rootOperatorFamily .G2) (Pi.single i 1) c) ∧
      InS M (g * xPar (rootOperatorFamily .G2) (-Pi.single i 1) c) := by
  have r5 : rootVec 5 = hexRoot 5 := by decide
  have r0 : rootVec 0 = hexRoot 0 := by decide
  have r11 : rootVec 11 = -hexRoot 5 := by decide
  have r6 : rootVec 6 = -hexRoot 0 := by decide
  fin_cases i
  · have e : (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
        rootVec 5 := by
      rw [r5]
      exact single_zero_eq_hexRoot
    have e' : (-Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
        rootVec 11 := by
      rw [r11]
      exact congrArg Neg.neg single_zero_eq_hexRoot
    refine ⟨?_, ?_⟩
    · show InS M (g * xPar (rootOperatorFamily .G2)
        (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) c)
      rw [e]
      exact hg.mul_xPar M (by norm_num) hc
    · show InS M (g * xPar (rootOperatorFamily .G2)
        (-Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) c)
      rw [e']
      exact hg.mul_xPar M (by norm_num) hc
  · have e : (Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
        rootVec 0 := by
      rw [r0]
      exact single_one_eq_hexRoot
    have e' : (-Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
        rootVec 6 := by
      rw [r6]
      exact congrArg Neg.neg single_one_eq_hexRoot
    refine ⟨?_, ?_⟩
    · show InS M (g * xPar (rootOperatorFamily .G2)
        (Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1) c)
      rw [e]
      exact hg.mul_xPar M (by norm_num) hc
    · show InS M (g * xPar (rootOperatorFamily .G2)
        (-Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1) c)
      rw [e']
      exact hg.mul_xPar M (by norm_num) hc

omit [Finite K] [CharP K 2] in
theorem eq_zero_or_one_of_card_two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2)
    (c : F) : c = 0 ∨ c = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  have h3 : ({0, 1, c} : Finset F).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, hcon.1.symm, hcon.2.symm, rfl⟩
  have h := Finset.card_le_univ ({0, 1, c} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at h
  omega

theorem g2Incl_gen (σ : K ≃+* K) {z : ModGL Tag.G2 (fixSubfield σ)}
    (hz : z ∈ adjointGroup Tag.G2 (fixSubfield σ))
    (hgen : ∃ (i : Fin Tag.G2.rank) (c : fixSubfield σ),
      (z : Module.End (fixSubfield σ) (RootModule Tag.G2 (fixSubfield σ))) =
          xOp Tag.G2 (fixSubfield σ) i c ∨
        (z : Module.End (fixSubfield σ) (RootModule Tag.G2 (fixSubfield σ))) =
          yOp Tag.G2 (fixSubfield σ) i c) :
    ∃ (i : Fin Tag.G2.rank) (c : fixSubfield σ),
      g2Incl σ ⟨z, hz⟩ = xPar (rootOperatorFamily .G2) (Pi.single i 1) (c : K) ∨
        g2Incl σ ⟨z, hz⟩ = xPar (rootOperatorFamily .G2) (-Pi.single i 1) (c : K) := by
  obtain ⟨i, c, h | h⟩ := hgen
  · refine ⟨i, c, Or.inl ?_⟩
    have hz' : z = xUnit Tag.G2 (fixSubfield σ) i c := Units.ext h
    have h2 : endHom K (xPar (rootOperatorFamily .G2) (Pi.single i 1) (c : K)) =
        xOp Tag.G2 K i (c : K) := by
      rw [xPar_simple, endHom_xElt]
    apply Subtype.ext
    apply Units.ext
    have e1 := congrArg (fun u : ModGL Tag.G2 K => (u : Module.End K (RootModule Tag.G2 K)))
      (coe_g2Incl σ ⟨z, hz⟩)
    simp only at e1
    rw [e1]
    change ((baseChangeGL (fixSubfield σ).subtype z : ModGL Tag.G2 K) :
      Module.End K (RootModule Tag.G2 K)) = _
    rw [hz', baseChangeGL_xUnit]
    exact h2.symm
  · refine ⟨i, c, Or.inr ?_⟩
    have hz' : z = yUnit Tag.G2 (fixSubfield σ) i c := Units.ext h
    have h2 : endHom K (xPar (rootOperatorFamily .G2) (-Pi.single i 1) (c : K)) =
        yOp Tag.G2 K i (c : K) := by
      rw [xPar_neg_simple, endHom_yElt]
    apply Subtype.ext
    apply Units.ext
    have e1 := congrArg (fun u : ModGL Tag.G2 K => (u : Module.End K (RootModule Tag.G2 K)))
      (coe_g2Incl σ ⟨z, hz⟩)
    simp only at e1
    rw [e1]
    change ((baseChangeGL (fixSubfield σ).subtype z : ModGL Tag.G2 K) :
      Module.End K (RootModule Tag.G2 K)) = _
    rw [hz', baseChangeGL_yUnit]
    exact h2.symm

theorem InS.mul_g2Incl_gen {σ : K ≃+* K} (hF : Nat.card (fixSubfield σ) = 2)
    {x : ↥(adjointGroup .G2 K)} (hx : InS M x) {z : ModGL Tag.G2 (fixSubfield σ)}
    (hz : z ∈ adjointGroup Tag.G2 (fixSubfield σ))
    (hgen : ∃ (i : Fin Tag.G2.rank) (c : fixSubfield σ),
      (z : Module.End (fixSubfield σ) (RootModule Tag.G2 (fixSubfield σ))) =
          xOp Tag.G2 (fixSubfield σ) i c ∨
        (z : Module.End (fixSubfield σ) (RootModule Tag.G2 (fixSubfield σ))) =
          yOp Tag.G2 (fixSubfield σ) i c) :
    InS M (x * g2Incl σ ⟨z, hz⟩) ∧ InS M (x * (g2Incl σ ⟨z, hz⟩)⁻¹) := by
  obtain ⟨i, c, h | h⟩ := g2Incl_gen σ hz hgen
  · have hcK : (c : K) = 0 ∨ (c : K) = 1 := by
      rcases eq_zero_or_one_of_card_two hF c with h | h <;> simp [h]
    rw [h, xPar_neg, CharTwo.neg_eq (c : K)]
    exact ⟨(hx.mul_simple M i hcK).1, (hx.mul_simple M i hcK).1⟩
  · have hcK : (c : K) = 0 ∨ (c : K) = 1 := by
      rcases eq_zero_or_one_of_card_two hF c with h | h <;> simp [h]
    rw [h, xPar_neg, CharTwo.neg_eq (c : K)]
    exact ⟨(hx.mul_simple M i hcK).2, (hx.mul_simple M i hcK).2⟩

theorem inS_of_mem_range (σ : K ≃+* K) (hF : Nat.card (fixSubfield σ) = 2) :
    ∀ g ∈ (g2Incl σ).range, InS M g := by
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  refine Subgroup.closure_induction_right (p := fun x hx => InS M (g2Incl σ ⟨x, hx⟩))
    ?_ ?_ ?_ hy
  · show InS M (g2Incl σ 1)
    rw [map_one]
    exact inS_one M
  · intro x hx z hz ih
    have e : (⟨x * z, Subgroup.mul_mem _ hx (Subgroup.subset_closure hz)⟩ :
        ↥(adjointGroup Tag.G2 (fixSubfield σ))) =
        ⟨x, hx⟩ * ⟨z, Subgroup.subset_closure hz⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact (ih.mul_g2Incl_gen M hF (Subgroup.subset_closure hz) hz).1
  · intro x hx z hz ih
    have e : (⟨x * z⁻¹, Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (Subgroup.subset_closure hz))⟩ :
        ↥(adjointGroup Tag.G2 (fixSubfield σ))) =
        ⟨x, hx⟩ * (⟨z, Subgroup.subset_closure hz⟩ :
          ↥(adjointGroup Tag.G2 (fixSubfield σ)))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_inv]
    exact (ih.mul_g2Incl_gen M hF (Subgroup.subset_closure hz) hz).2

include M in
theorem eq_bot_of_fixed (hK8 : Nat.card K = 8) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    {W E : Subgroup ↥(adjointGroup .G2 K)}
    (hWfix : ∀ w ∈ W, g2FieldHom K σ w = w) (hEfix : ∀ e ∈ E, g2FieldHom K σ e = e)
    (hW : ¬ 3 ∣ Nat.card W) (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEW : E ≤ Subgroup.normalizer (W : Set ↥(adjointGroup .G2 K))) : W = ⊥ := by
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hcard := card_fixSubfield_pow σ
  rw [hσ, hK8] at hcard
  have hF : Nat.card (fixSubfield σ) = 2 :=
    Nat.pow_left_injective (by norm_num : 3 ≠ 0) (hcard.trans (by norm_num))
  have hWR : W ≤ (g2Incl σ).range := fun w hw => (mem_range_g2Incl_iff hK2 σ w).mpr (hWfix w hw)
  have hER : E ≤ (g2Incl σ).range := fun e he => (mem_range_g2Incl_iff hK2 σ e).mpr (hEfix e he)
  have hRcard : Nat.card (g2Incl σ).range ∣ 12096 := by
    have h1 : Nat.card (g2Incl σ).range = Nat.card (adjointGroup .G2 (fixSubfield σ)) :=
      (Nat.card_congr (MonoidHom.ofInjective (g2Incl_injective σ)).toEquiv).symm
    rw [h1, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    norm_num [ordG2]
  obtain ⟨hF3c, hF2c, hF1c⟩ := rFacts
  have hS : ∀ g ∈ (g2Incl σ).range, M.rho g ∈ rMon := fun g hg => inS_of_mem_range M σ hF g hg
  have hpow : ∀ {a : ↥(adjointGroup .G2 K)} {n : ℕ}, a ^ n = 1 → M.rho a ^ n = 1 := fun h => by
    rw [← map_pow, h, map_one]
  have hne : ∀ {a : ↥(adjointGroup .G2 K)}, a ≠ 1 → M.rho a ≠ 1 := fun ha h =>
    ha (M.rho_injective (by rw [h, map_one]))
  have hneq : ∀ {a b : ↥(adjointGroup .G2 K)}, a ≠ b → M.rho a ≠ M.rho b := fun hab h =>
    hab (M.rho_injective h)
  have hcm : ∀ {a b : ↥(adjointGroup .G2 K)}, a * b = b * a →
      M.rho a * M.rho b = M.rho b * M.rho a := fun h => by
    rw [← map_mul, ← map_mul, h]
  refine eq_bot_of_forbidden hRcard hWR hER ?_ ?_ ?_ hW hE hE9 hEW
  ·
    intro e he y hy he3 he1 hy7 hy1 hcomm
    exact hF3c _ (hS e he) _ (hS y hy) (hpow he3) (hne he1) (hpow hy7) (hne hy1) (hcm hcomm)
  ·
    intro e he t ht t' ht' he3 he1 ht2 ht1 ht'2 ht'1 htt' hte ht'e htt'c
    exact hF2c _ (hS e he) _ (hS t ht) _ (hS t' ht') (hpow he3) (hne he1) (hpow ht2) (hne ht1)
      (hpow ht'2) (hne ht'1) (hneq htt') (hcm hte) (hcm ht'e) (hcm htt'c)
  ·
    intro e he u hu t ht he3 he1 hu3 hu1 hue hue2 ht2 ht1 hte htu hue'
    exact hF1c _ (hS e he) _ (hS u hu) _ (hS t ht) (hpow he3) (hne he1) (hpow hu3) (hne hu1)
      (hneq hue) (fun h => hue2 (M.rho_injective (by rw [h, map_mul]))) (hpow ht2) (hne ht1)
      (hcm hte) (hcm htu) (hcm hue')

end R

end CFSG.RankThree.PartTwo.Sec4.Item434G28
