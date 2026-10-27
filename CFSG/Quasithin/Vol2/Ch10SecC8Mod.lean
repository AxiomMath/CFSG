module

public import CFSG.Quasithin.Vol2.Ch10SecCL3F
public import CFSG.Quasithin.Vol2.Ch10SecC8H1A
public import CFSG.Quasithin.Vol2.Ch10SecBL32K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F

variable {W : Type} [CommGroup W] {Gm : Subgroup (MulAut W)} {Z : Subgroup W}

@[expose] def coordOf (D : L3Data Gm ⊤ Z) (w : W) : L3.Vec :=
  Multiplicative.toAdd (D.β ⟨w, Subgroup.mem_top w⟩)

theorem coordOf_mul (D : L3Data Gm ⊤ Z) (a b : W) :
    coordOf D (a * b) = coordOf D a + coordOf D b := by
  unfold coordOf
  have : (⟨a * b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
    ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem coordOf_one (D : L3Data Gm ⊤ Z) : coordOf D 1 = 0 := by
  unfold coordOf
  have : (⟨1, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = 1 := rfl
  rw [this, map_one, toAdd_one]

theorem coordOf_inv (D : L3Data Gm ⊤ Z) (a : W) : coordOf D a⁻¹ = -coordOf D a := by
  have h := coordOf_mul D a⁻¹ a
  rw [inv_mul_cancel, coordOf_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem coordOf_eq_zero_iff (D : L3Data Gm ⊤ Z) (w : W) : coordOf D w = 0 ↔ w ∈ Z := by
  rw [← D.ker_β ⟨w, Subgroup.mem_top w⟩]
  unfold coordOf
  exact ⟨fun h => by rw [← ofAdd_toAdd (D.β _), h]; rfl, fun h => by rw [h]; rfl⟩

theorem coordOf_π (D : L3Data Gm ⊤ Z) (γ : L3.Γ) (w : W) :
    coordOf D ((D.π γ : MulAut W) w) = L3.act γ (coordOf D w) := by
  unfold coordOf
  rw [D.equi γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _), toAdd_ofAdd]

theorem coordOf_surj (D : L3Data Gm ⊤ Z) (x : L3.Vec) : ∃ w : W, coordOf D w = x := by
  obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd x)
  exact ⟨u, by unfold coordOf; rw [show (⟨(u : W), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = u
    from rfl, hu, toAdd_ofAdd]⟩

theorem vec_add_self' : ∀ c : L3.Vec, c + c = 0 := by decide

theorem vec_neg_self' : ∀ c : L3.Vec, -c = c := by decide

@[expose] def secSub (D : L3Data Gm ⊤ Z) (c : L3.Vec) : Subgroup W where
  carrier := {w | coordOf D w = 0 ∨ coordOf D w = c}
  one_mem' := Or.inl (coordOf_one D)
  mul_mem' := fun {a b} ha hb => by
    change coordOf D (a * b) = 0 ∨ coordOf D (a * b) = c
    rw [coordOf_mul]
    have hc : c + c = 0 := vec_add_self' c
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · left; exact add_zero 0
    · right; exact zero_add c
    · right; exact add_zero c
    · left; exact hc
  inv_mem' := fun {a} ha => by
    change coordOf D a⁻¹ = 0 ∨ coordOf D a⁻¹ = c
    rw [coordOf_inv]
    have hc : -c = c := vec_neg_self' c
    rcases ha with ha | ha <;> rw [ha]
    · left; exact neg_zero
    · right; exact hc

theorem mem_secSub (D : L3Data Gm ⊤ Z) (c : L3.Vec) (w : W) :
    w ∈ secSub D c ↔ coordOf D w = 0 ∨ coordOf D w = c := Iff.rfl

section Module

variable (D : L3Data Gm ⊤ Z) (hsq : ∀ w : W, w ^ 2 = 1) (hZ : fixV Gm = Z)
include hsq hZ

omit hsq in
theorem π_fix_Z (γ : L3.Γ) {z : W} (hz : z ∈ Z) : (D.π γ : MulAut W) z = z := by
  rw [← hZ] at hz
  exact hz _ (D.π γ).2

theorem π_fix_of_cube {γ : L3.Γ} (hγ : γ * γ * γ = 1) (hpa : IsPa γ) {w : W}
    (hw : coordOf D w = e0) : (D.π γ : MulAut W) w = w := by
  set a : MulAut W := (D.π γ : MulAut W) with ha
  set c : W := a w * w⁻¹ with hcdef
  have hcZ : c ∈ Z := by
    rw [← coordOf_eq_zero_iff D, hcdef, coordOf_mul, coordOf_inv, ha, coordOf_π, hw,
      (act_e0_iff γ).mpr hpa]
    decide
  have hac : a c = c := π_fix_Z D hZ γ hcZ
  have haw : a w = c * w := by rw [hcdef]; group
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hsq c
  have h3 : a (a (a w)) = c * w := by
    rw [haw, map_mul, hac, haw, ← mul_assoc, hc2, one_mul, haw]
  have h1 : a (a (a w)) = w := by
    have := congrArg (fun g : ↥Gm => ((g : MulAut W) w)) (congrArg D.π hγ)
    simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, MulAut.mul_apply,
      MulAut.one_apply] at this
    exact this
  rw [h3] at h1
  have hc1 : c = 1 := mul_right_cancel (h1.trans (one_mul w).symm)
  rw [haw, hc1, one_mul]

theorem π_fix_of_ka {γ : L3.Γ} (hγ : IsKa γ) {w : W} (hw : coordOf D w = e0) :
    (D.π γ : MulAut W) w = w := by
  obtain ⟨a, haK, ha3, hb3⟩ := ka_gen γ hγ
  have hbK : IsKa (a⁻¹ * γ) := isKa_mul _ _ (isKa_inv _ haK) hγ
  have e : γ = a * (a⁻¹ * γ) := by group
  rw [e, map_mul, Subgroup.coe_mul, MulAut.mul_apply,
    π_fix_of_cube D hsq hZ hb3 hbK.1 hw, π_fix_of_cube D hsq hZ ha3 haK.1 hw]

theorem π_not_fix_γ1 [Finite W] (hFF : ∀ a ∈ Gm, a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        Nat.card (fixV (Subgroup.zpowers a)) = 4)
    (hZ2 : Nat.card Z = 2) {w : W} (hw : coordOf D w = e0) : (D.π γ1 : MulAut W) w ≠ w := by
  intro hfix
  have hγ1 : γ1 ≠ 1 := by decide
  have hγ1sq : γ1 * γ1 = 1 := by decide
  have ha1 : (D.π γ1 : MulAut W) ≠ 1 := by
    intro h
    have h1 : D.π γ1 = D.π 1 := by rw [map_one]; exact Subtype.ext h
    exact hγ1 (D.π_injective h1)
  have ha2 : (D.π γ1 : MulAut W) ^ 2 = 1 := by
    rw [pow_two, ← Subgroup.coe_mul, ← map_mul, hγ1sq, map_one, Subgroup.coe_one]
  obtain ⟨hcf, hcard⟩ := hFF _ (D.π γ1).2 ha1 ha2
  have hwZ : w ∉ Z := fun h => by
    rw [← coordOf_eq_zero_iff D, hw] at h
    exact absurd h (by decide)
  have hZa : Z ≤ fixV (Subgroup.zpowers (D.π γ1 : MulAut W)) := fun z hz =>
    B1.fixV_le_fixV (Subgroup.zpowers_le.mpr (D.π γ1).2) (by rw [hZ]; exact hz)
  have hwa : w ∈ fixV (Subgroup.zpowers (D.π γ1 : MulAut W)) := by
    rw [mem_fixV]
    intro g hg
    have hst : Subgroup.zpowers (D.π γ1 : MulAut W) ≤ MulAction.stabilizer (MulAut W) w :=
      Subgroup.zpowers_le.mpr hfix
    exact hst hg
  have hN : Subgroup.zpowers w ≤ Subgroup.normalizer (Z : Set W) :=
    le_normalizer_of_comm (X := ⊤) (fun a _ b _ => mul_comm a b) le_top le_top
  have hZw : Nat.card ↥(Z ⊔ Subgroup.zpowers w) = 4 := by
    rw [card_sup_zpowers hwZ (hsq w) hN, hZ2]
  have heq : Z ⊔ Subgroup.zpowers w = fixV (Subgroup.zpowers (D.π γ1 : MulAut W)) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZa (Subgroup.zpowers_le.mpr hwa)) (by rw [hcard, hZw])
  have hsec : fixV (Subgroup.zpowers (D.π γ1 : MulAut W)) ≤ secSub D e0 := by
    rw [← heq]
    refine sup_le (fun z hz => Or.inl ((coordOf_eq_zero_iff D z).mpr hz)) ?_
    exact Subgroup.zpowers_le.mpr (Or.inr hw)
  obtain ⟨v, hv⟩ := coordOf_surj D e1
  have hmem : (D.π γ1 : MulAut W) v * v⁻¹ ∈ commV (Subgroup.zpowers (D.π γ1 : MulAut W)) :=
    Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, v, rfl⟩
  rw [hcf] at hmem
  have h1 := hsec hmem
  rw [mem_secSub, coordOf_mul, coordOf_inv, coordOf_π, hv] at h1
  revert h1
  decide

theorem fixes_iff_ka [Finite W] (hFF : ∀ a ∈ Gm, a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        Nat.card (fixV (Subgroup.zpowers a)) = 4)
    (hZ2 : Nat.card Z = 2) {w : W} (hw : coordOf D w = e0) (γ : L3.Γ) :
    (D.π γ : MulAut W) w = w ↔ IsKa γ := by
  refine ⟨fun hfix => ?_, fun h => π_fix_of_ka D hsq hZ h hw⟩
  have hpa : IsPa γ := by
    rw [← act_e0_iff, ← hw, ← coordOf_π, hfix]
  by_contra hK
  apply π_not_fix_γ1 D hsq hZ hFF hZ2 hw
  have h1 := π_fix_of_ka D hsq hZ (pa_mul_ka γ hpa hK) hw
  have e : γ1 = γ * (γ⁻¹ * γ1) := by group
  rw [e, map_mul, Subgroup.coe_mul, MulAut.mul_apply, h1, hfix]

theorem fixes_ea_iff {w : W} : (∀ γ, IsEa γ → (D.π γ : MulAut W) w = w) ↔ w ∈ secSub D e0 := by
  constructor
  · intro h
    refine fix_Ea (coordOf D w) fun γ hγ => ?_
    rw [← coordOf_π, h γ hγ]
  · rintro (h | h) γ hγ
    · exact π_fix_Z D hZ γ ((coordOf_eq_zero_iff D w).mp h)
    · exact π_fix_of_ka D hsq hZ (ea_le γ hγ).1 h

omit hsq hZ in
theorem fixV_le_secSub [Finite W] (hFF : ∀ a ∈ Gm, a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        Nat.card (fixV (Subgroup.zpowers a)) = 4)
    {γ : L3.Γ} (hγ1 : γ ≠ 1) (hγ2 : γ * γ = 1) {c : L3.Vec}
    (hc : ∀ x : L3.Vec, L3.act γ x - x = 0 ∨ L3.act γ x - x = c) :
    fixV (Subgroup.zpowers (D.π γ : MulAut W)) ≤ secSub D c := by
  have ha1 : (D.π γ : MulAut W) ≠ 1 := by
    intro h
    have h1 : D.π γ = D.π 1 := by rw [map_one]; exact Subtype.ext h
    exact hγ1 (D.π_injective h1)
  have ha2 : (D.π γ : MulAut W) ^ 2 = 1 := by
    rw [pow_two, ← Subgroup.coe_mul, ← map_mul, hγ2, map_one, Subgroup.coe_one]
  rw [← (hFF _ (D.π γ).2 ha1 ha2).1, commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases zpow_eq_one_or_self ha2 k with h | h
  · rw [h]
    left
    rw [MulAut.one_apply, mul_inv_cancel, coordOf_one]
  · rw [h]
    change coordOf D ((D.π γ : MulAut W) v * v⁻¹) = 0 ∨ coordOf D ((D.π γ : MulAut W) v * v⁻¹) = c
    rw [coordOf_mul, coordOf_inv, coordOf_π]
    have h1 := hc (coordOf D v)
    rwa [sub_eq_add_neg] at h1

omit hsq hZ in
theorem offender_eq_ea [Finite W] (hFF : ∀ a ∈ Gm, a ≠ 1 → a ^ 2 = 1 →
      commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
        Nat.card (fixV (Subgroup.zpowers a)) = 4)
    (hZ2 : Nat.card Z = 2)
    (hE4 : ∀ A : Subgroup (MulAut W), A ≤ Gm → IsElemAbelian2 A → Nat.card A ≤ 4)
    {B : Subgroup (MulAut W)} (hBG : B ≤ Gm) (hBU : ∀ b ∈ B, ∃ γ, IsU γ ∧ (D.π γ : MulAut W) = b)
    (hB : IsElemAbelian2 B) (hB1 : B ≠ ⊥) (h16 : 16 ≤ Nat.card B * Nat.card (fixV B)) :
    (∀ b ∈ B, ∃ γ, IsEa γ ∧ (D.π γ : MulAut W) = b) ∧
      ∀ γ, IsEa γ → (D.π γ : MulAut W) ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB4 := hE4 B hBG hB
  obtain ⟨⟨b1, hb1⟩, hb1ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
  have hb1ne' : b1 ≠ 1 := fun h => hb1ne (Subtype.ext h)
  have hb1sq : b1 ^ 2 = 1 := hB.2 b1 hb1
  have hfix4 : Nat.card (fixV B) ≤ 4 := by
    rw [← (hFF b1 (hBG hb1) hb1ne' hb1sq).2]
    exact Subgroup.card_le_of_le (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hb1))
  have hBc : Nat.card B = 4 := by
    have : 16 ≤ Nat.card B * 4 := h16.trans (Nat.mul_le_mul_left _ hfix4)
    omega
  obtain ⟨b2, hb2, hb2ne, hb21⟩ : ∃ b2 ∈ B, b2 ≠ 1 ∧ b2 ≠ b1 := by
    by_contra hcon
    have hle : B ≤ Subgroup.zpowers b1 := fun b hb => by
      by_cases h : b = 1
      · rw [h]; exact Subgroup.one_mem _
      · by_cases h' : b = b1
        · rw [h']; exact Subgroup.mem_zpowers _
        · exact absurd ⟨b, hb, h, h'⟩ hcon
    have h2 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hb1sq hb1ne', hBc] at h2
    omega
  have hb2sq : b2 ^ 2 = 1 := hB.2 b2 hb2
  obtain ⟨g1, hg1U, hg1⟩ := hBU b1 hb1
  obtain ⟨g2, hg2U, hg2⟩ := hBU b2 hb2
  have hinj : ∀ x y : L3.Γ, (D.π x : MulAut W) = D.π y → x = y :=
    fun x y h => D.π_injective (Subtype.ext h)
  have hsq' : ∀ {x : L3.Γ}, (D.π x : MulAut W) ^ 2 = 1 → x * x = 1 := fun {x} h =>
    hinj _ _ (by rw [map_mul, Subgroup.coe_mul, ← pow_two, h, map_one, Subgroup.coe_one])
  have hg1sq : g1 * g1 = 1 := hsq' (hg1 ▸ hb1sq)
  have hg2sq : g2 * g2 = 1 := hsq' (hg2 ▸ hb2sq)
  have hcomm : g1 * g2 = g2 * g1 := hinj _ _ (by
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hg1, hg2]
    exact hB.1 b1 hb1 b2 hb2)
  have hg1ne : g1 ≠ 1 := fun h => hb1ne' (by rw [← hg1, h, map_one, Subgroup.coe_one])
  have hg2ne : g2 ≠ 1 := fun h => hb2ne (by rw [← hg2, h, map_one, Subgroup.coe_one])
  have hg12 : g1 ≠ g2 := fun h => hb21 (by rw [← hg1, ← hg2, h])
  have hmemB : ∀ x : L3.Γ, (x = g1 ∨ x = g2 ∨ x = g1 * g2) → (D.π x : MulAut W) ∈ B := by
    rintro x (rfl | rfl | rfl)
    · rw [hg1]; exact hb1
    · rw [hg2]; exact hb2
    · rw [map_mul, Subgroup.coe_mul, hg1, hg2]; exact B.mul_mem hb1 hb2
  rcases u3_pair g1 g2 hg1U hg2U hg1sq hg2sq hcomm hg1ne hg2ne hg12 with ⟨ha1, ha2⟩ | ⟨hb1', hb2'⟩
  ·
    have hEaB : ∀ γ, IsEa γ → (D.π γ : MulAut W) ∈ B := by
      intro γ hγ
      rcases ea_span g1 g2 ha1 ha2 hg1ne hg2ne hg12 γ hγ with h | h | h | h
      · rw [h, map_one]; exact B.one_mem
      · exact hmemB γ (Or.inl h)
      · exact hmemB γ (Or.inr (Or.inl h))
      · exact hmemB γ (Or.inr (Or.inr h))
    refine ⟨fun b hb => ?_, hEaB⟩
    let E : Subgroup (MulAut W) := (Ea.map D.π).map Gm.subtype
    have hEB : E ≤ B := by
      rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      exact hEaB γ hγ
    have hEc : Nat.card E = 4 := by
      rw [Subgroup.card_map_of_injective Gm.subtype_injective,
        Subgroup.card_map_of_injective D.π_injective, Nat.card_eq_fintype_card, ← card_Ea]
      exact Fintype.card_subtype (· ∈ Ea)
    have heq : E = B := Subgroup.eq_of_le_of_card_ge hEB (by rw [hBc, hEc])
    rw [← heq] at hb
    obtain ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩ := hb
    exact ⟨γ, hγ, rfl⟩
  ·
    exfalso
    obtain ⟨hA, hB'⟩ := eb_span g1 g2 hb1' hb2' hg1ne hg2ne hg12
    have hAB := hmemB ebA hA
    have hBB := hmemB ebB hB'
    have hle : fixV B ≤ Z := by
      intro w hw
      have h1 := fixV_le_secSub D hFF (by decide) (by decide)
        ebA_cim (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hAB) hw)
      have h2 := fixV_le_secSub D hFF (by decide) (by decide)
        ebB_cim (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hBB) hw)
      rw [← coordOf_eq_zero_iff D]
      rcases h1 with h1 | h1
      · exact h1
      · rcases h2 with h2 | h2
        · exact h2
        · exact absurd (h1.symm.trans h2) (by decide)
    have := Subgroup.card_le_of_le hle
    rw [hZ2] at this
    have : 16 ≤ 4 * 2 := hBc ▸ h16.trans (Nat.mul_le_mul_left _ this)
    omega

end Module

end CFSG.Quasithin.Vol2.Ch10.SecC
