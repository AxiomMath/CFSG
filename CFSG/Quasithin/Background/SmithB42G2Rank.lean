module

public import CFSG.Quasithin.Vol2.Ch11G2Q8OffLines

public section

namespace CFSG.Quasithin.B42G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8 Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

@[expose] def fixSub (Γ : Subgroup ↥(cayleyGroup F)) : Submodule F (Ix3 → F) where
  carrier := {x | ∀ γ ∈ Γ, g2Act γ x = x}
  add_mem' := fun {x y} hx hy γ hγ => by
    rw [map_add, hx γ hγ, hy γ hγ]
  zero_mem' := fun γ _ => map_zero (g2Act γ)
  smul_mem' := fun c {x} hx γ hγ => by
    rw [JonesParshall.g2Act_smul, hx γ hγ]

theorem mem_fixSub {Γ : Subgroup ↥(cayleyGroup F)} {x : Ix3 → F} :
    x ∈ fixSub Γ ↔ ∀ γ ∈ Γ, g2Act γ x = x := Iff.rfl

theorem fixSub_bot : fixSub (⊥ : Subgroup ↥(cayleyGroup F)) = ⊤ := by
  ext x
  simp only [mem_fixSub, Subgroup.mem_bot, forall_eq, Submodule.mem_top, iff_true, map_one]
  rfl

theorem fixD_none_iff (w : Ix3 → F) : FixD none w ↔ w ∈ fixQ (tL (1 : F)) := by
  rw [fixD_iff, mem_fixQ]
  have h := g2Act_tL (1 : F) (w (.inl 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0)) (w (.inr 1))
    (w (.inr 2))
  rw [← q6_eta w] at h
  rw [h]
  constructor
  · rintro ⟨h0, h2⟩
    have h2' : w (.inl 2) = 0 := h2
    conv_rhs => rw [q6_eta w]
    rw [h0, h2']
    simp
  · intro he
    have e0 := congrFun he (.inl 0)
    have e5 := congrFun he (.inr 2)
    rw [q6_apply_inl0] at e0
    rw [q6_apply_inr2] at e5
    exact ⟨by linear_combination e5, show w (.inl 2) = 0 by linear_combination e0⟩

theorem card_fixQ_tL_le [Finite F] : Nat.card (fixQ (tL (1 : F))) ≤ Nat.card F ^ 4 := by
  have hinj : Function.Injective (fun w : fixQ (tL (1 : F)) =>
      (![w.1 (.inl 0), w.1 (.inl 1), w.1 (.inr 1), w.1 (.inr 2)] : Fin 4 → F)) := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    obtain ⟨h0, h2⟩ := (fixD_iff none w).mp ((fixD_none_iff w).mpr hw)
    obtain ⟨h0', h2'⟩ := (fixD_iff none w').mp ((fixD_none_iff w').mpr hw')
    have h2a : w (.inl 2) = 0 := h2
    have h2b : w' (.inl 2) = 0 := h2'
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    have e2 := congrFun h 2
    have e3 := congrFun h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at e0 e1 e2 e3
    apply Subtype.ext
    funext i
    rcases i with i | i <;> fin_cases i
    · exact e0
    · exact e1
    · exact h2a.trans h2b.symm
    · exact h0.trans h0'.symm
    · exact e2
    · exact e3
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_fin] at h1

theorem mem_fixQ_conj {x t : ↥(cayleyGroup F)} {w : Ix3 → F} :
    g2Act x w ∈ fixQ (x * t * x⁻¹) ↔ w ∈ fixQ t := by
  rw [mem_fixQ, mem_fixQ, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply]
  constructor
  · intro h
    have h1 := congrArg (g2Act x⁻¹) h
    rwa [g2Act_inv_apply, g2Act_inv_apply] at h1
  · intro h
    rw [h]

theorem card_fixQ_conj [Finite F] (x t : ↥(cayleyGroup F)) :
    Nat.card (fixQ (x * t * x⁻¹)) = Nat.card (fixQ t) := by
  refine (Nat.card_congr (Equiv.ofBijective (fun w : fixQ t =>
    (⟨g2Act x w.1, mem_fixQ_conj.mpr w.2⟩ : fixQ (x * t * x⁻¹))) ⟨?_, ?_⟩)).symm
  · rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    have h1 := congrArg (fun u : fixQ (x * t * x⁻¹) => g2Act x⁻¹ u.1) h
    simp only [g2Act_inv_apply] at h1
    exact Subtype.ext h1
  · rintro ⟨u, hu⟩
    refine ⟨⟨g2Act x⁻¹ u, ?_⟩, Subtype.ext (g2Act_apply_inv x u)⟩
    rw [← mem_fixQ_conj (x := x), g2Act_apply_inv]
    exact hu

theorem card_fixQ_le [Finite F] {h : ↥(cayleyGroup F)} (hh : h * h = 1) (h1 : h ≠ 1) :
    Nat.card (fixQ h) ≤ Nat.card F ^ 4 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  obtain ⟨x, rfl⟩ := eq_conj_tL_of_fix hh h1 hlt.le
  rw [card_fixQ_conj] at hlt
  exact absurd card_fixQ_tL_le (not_le.mpr hlt)

theorem card_le_of_card_fixSub [Finite F] {Γ : Subgroup ↥(cayleyGroup F)}
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) (hne : Γ ≠ ⊥)
    (hfix : Nat.card F ^ 4 ≤ Nat.card (fixSub Γ)) : Nat.card Γ ≤ Nat.card F := by
  have := finite_cayleyGroup (F := F)
  obtain ⟨⟨t, htΓ⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hle : (fixSub Γ).toAddSubgroup ≤ fixQ t := fun x hx => mem_fixQ.mpr (hx t htΓ)
  have hct : Nat.card (fixQ t) ≤ Nat.card F ^ 4 := card_fixQ_le (hΓ1 t htΓ) ht1'
  have hc' : Nat.card (fixQ t) ≤ Nat.card ((fixSub Γ).toAddSubgroup) := hct.trans hfix
  have heq : (fixSub Γ).toAddSubgroup = fixQ t := AddSubgroup.eq_of_le_of_card_ge hle hc'
  obtain ⟨x, hx⟩ := eq_conj_tL_of_fix (hΓ1 t htΓ) ht1' (hfix.trans (by
    rw [← heq]; exact le_rfl))
  have hkey : ∀ γ ∈ Γ, ∀ w, FixD none w → g2Act (x⁻¹ * γ * x) w = w := by
    intro γ hγ w hw
    have h1 : g2Act x w ∈ fixQ t := by
      rw [hx]
      exact mem_fixQ_conj.mpr ((fixD_none_iff w).mp hw)
    rw [← heq] at h1
    have h2 : g2Act γ (g2Act x w) = g2Act x w := h1 γ hγ
    rw [g2Act_mul_apply, g2Act_mul_apply, h2, g2Act_inv_apply]
  have hmemD : ∀ γ ∈ Γ, x⁻¹ * γ * x ∈ rootD (none : Option F) := fun γ hγ =>
    mem_rootD_of_fixD (fun w hw => hkey γ hγ w (fixD_of_mem_F3 none hw)) (hkey γ hγ)
  have hinj : Function.Injective (fun γ : Γ =>
      (⟨x⁻¹ * γ.1 * x, hmemD γ.1 γ.2⟩ : ↥(rootD (none : Option F)))) := by
    rintro ⟨γ, hγ⟩ ⟨δ, hδ⟩ h
    have h1 : x⁻¹ * γ * x = x⁻¹ * δ * x := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h1)
  exact (Nat.card_le_card_of_injective _ hinj).trans (card_rootD_le none)

theorem exists_onLine_of_linear {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ d : Option F, ∀ v : F × F, a * v.1 + b * v.2 = 0 → OnLine d v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hb : b = 0
  · refine ⟨none, fun v hv => ?_⟩
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
    rw [hb, zero_mul, add_zero] at hv
    exact (mul_eq_zero.mp hv).resolve_left ha
  · refine ⟨some (a / b), fun v hv => ?_⟩
    show v.2 = a / b * v.1
    field_simp
    linear_combination hv - a * v.1 * h2

theorem exists_inf_Z1_le_rootD [Finite F] {Γ : Subgroup ↥(cayleyGroup F)}
    (hΓS : Γ ≤ stabV0 F) (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) {γ₀ : ↥(cayleyGroup F)} (hγ₀ : γ₀ ∈ Γ)
    (hM : levi1Mat γ₀ ≠ 1) : ∃ d : Option F, Γ ⊓ Z1 F ≤ rootD d := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hMM : levi1Mat γ₀ * levi1Mat γ₀ = 1 := by
    rw [← levi1Mat_mul (hΓS hγ₀) (hΓS hγ₀), hΓ1 γ₀ hγ₀, levi1Mat_one]
  have hfixv : ∀ v : F × F, g2A (uSL v.1 v.2 0) ∈ Γ →
      levi1Mat γ₀ *ᵥ ![v.1, v.2] = ![v.1, v.2] := by
    intro v hv
    have hcomm := hΓc γ₀ hγ₀ _ hv
    have hx₀ : g2Act (g2A (uSL v.1 v.2 0)) (q6 (0 : F) 0 0 1 0 0) - q6 0 0 0 1 0 0 =
        q6 0 0 0 0 v.1 v.2 := by
      rw [g2Act_uSL_v0, q6_sub]
      simp
    have hx₀3 : q6 (0 : F) 0 0 0 v.1 v.2 ∈ stdF F 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
    have hact : g2Act γ₀ (q6 (0 : F) 0 0 0 v.1 v.2) =
        g2Act (g2A (uSL v.1 v.2 0)) (g2Act γ₀ (q6 0 0 0 1 0 0)) -
          g2Act γ₀ (q6 0 0 0 1 0 0) := by
      rw [← hx₀, map_sub, ← g2Act_mul_apply, ← g2Act_mul_apply, hcomm]
    set w₁ := g2Act γ₀ (q6 (0 : F) 0 0 1 0 0) with hw₁
    have hv1 := vpart_act (hΓS hγ₀) hx₀3
    rw [hact, g2Act_g2A_uSL] at hv1
    set s := w₁ (.inr 0) with hs
    have hsu : levi1Mat γ₀ *ᵥ ![v.1, v.2] = s • ![v.1, v.2] := by
      rw [← show vpart (q6 (0 : F) 0 0 0 v.1 v.2) = ![v.1, v.2] from rfl, ← hv1]
      funext i
      fin_cases i <;> simp [vpart, q6, hs] <;> ring
    have hss : (s * s) • ![v.1, v.2] = ![v.1, v.2] := by
      have h1 : levi1Mat γ₀ *ᵥ (levi1Mat γ₀ *ᵥ ![v.1, v.2]) = ![v.1, v.2] := by
        rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
      rw [hsu, Matrix.mulVec_smul, hsu, smul_smul] at h1
      exact h1
    by_cases hu : (![v.1, v.2] : Fin 2 → F) = 0
    · rw [hu, Matrix.mulVec_zero]
    · have hs1 : s * s = 1 := by
        have h3 : (s * s - 1) • (![v.1, v.2] : Fin 2 → F) = 0 := by
          rw [sub_smul, hss, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu)
      have hs1' : s = 1 := by
        have h4 : (s + 1) * (s + 1) = 0 := by linear_combination hs1 + s * h2 + h2
        have h5 := mul_self_eq_zero.mp h4
        linear_combination h5 - h2
      rw [hsu, hs1', one_smul]
  have hrow : (levi1Mat γ₀ 0 0 - 1 ≠ 0 ∨ levi1Mat γ₀ 0 1 ≠ 0) ∨
      (levi1Mat γ₀ 1 0 ≠ 0 ∨ levi1Mat γ₀ 1 1 - 1 ≠ 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ := hcon
    apply hM
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sub_eq_zero.mp h00, h01, h10, sub_eq_zero.mp h11]
  rcases hrow with hrow | hrow
  · obtain ⟨d, hd⟩ := exists_onLine_of_linear hrow
    refine ⟨d, fun z hz => ?_⟩
    obtain ⟨v, hv⟩ := hz.2
    have hfv := hfixv v (hv ▸ hz.1)
    have e0 := congrFun hfv 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0
    exact ⟨v, hd v (by linear_combination e0), hv⟩
  · obtain ⟨d, hd⟩ := exists_onLine_of_linear hrow
    refine ⟨d, fun z hz => ?_⟩
    obtain ⟨v, hv⟩ := hz.2
    have hfv := hfixv v (hv ▸ hz.1)
    have e1 := congrFun hfv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1
    exact ⟨v, hd v (by linear_combination e1), hv⟩

theorem card_le_cube [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) : Nat.card ↥Γ ≤ Nat.card F ^ 3 := by
  have := finite_cayleyGroup (F := F)
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hconj1 : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      γ * γ = 1 := by
    rintro x _ ⟨g, hg, rfl⟩
    change x * g * x⁻¹ * (x * g * x⁻¹) = 1
    rw [show x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ by group, hΓ1 g hg]
    group
  have hconjc : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      ∀ δ ∈ Γ.map (MulAut.conj x).toMonoidHom, γ * δ = δ * γ := by
    rintro x _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    change x * g * x⁻¹ * (x * h * x⁻¹) = x * h * x⁻¹ * (x * g * x⁻¹)
    rw [show x * g * x⁻¹ * (x * h * x⁻¹) = x * (g * h) * x⁻¹ by group, hΓc g hg h hh]
    group
  have hcard : ∀ x : ↥(cayleyGroup F),
      Nat.card ↥(Γ.map (MulAut.conj x).toMonoidHom) = Nat.card ↥Γ := fun x =>
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  by_cases hA : ∃ r ∈ Γ, ∃ x, qr r x ≠ 0
  ·
    obtain ⟨r, hrΓ, x₀, hx₀⟩ := hA
    obtain ⟨p, hp⟩ := exists_qr_eq_sq (hΓ1 r hrΓ)
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply hx₀
      rw [hp]
      simp [polarQ]
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hp0
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := hΓ' ▸ hconj1 g⁻¹
    have hΓ'c : ∀ γ ∈ Γ', ∀ δ ∈ Γ', γ * δ = δ * γ := hΓ' ▸ hconjc g⁻¹
    have hc' : Nat.card ↥Γ' = Nat.card ↥Γ := hΓ' ▸ hcard g⁻¹
    have hr' : g⁻¹ * r * g ∈ Γ' := by
      have h1 := hΓ' ▸ conj_apply_mem_map g⁻¹ hrΓ
      rwa [inv_inv] at h1
    have hqr' : ∀ x, qr (g⁻¹ * r * g) x = x (.inr 0) * x (.inr 0) := by
      intro x
      have h1 := qr_conj g⁻¹ r (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      rw [h1, hp, ← polarQ_g2Act g⁻¹, g2Act_inv_apply, ← hg, g2Act_inv_apply, polarQ_eu0]
    obtain ⟨a, b, hab⟩ := eq_kerElt_of_qr (hΓ'1 _ hr') hqr'
    have hS : Γ' ≤ stabV0 F := fun s hs =>
      fix_of_qr_sq (r := g⁻¹ * r * g) (p := eu 0 1) (fun x => by rw [hqr', polarQ_eu0])
        (hΓ'c s hs _ hr')
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ A1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      have hc := hΓ'c _ hhΓ' _ hr'
      rw [hab] at hc
      obtain ⟨rfl, rfl⟩ := kerElt_eq_of_comm hc
      exact kerElt_mem_A1 α p' q'
    have h1 := card_le_mul_card_inf_R1 hF hn hS hΓ'1
    rw [← hc']
    by_cases hall : ∀ γ ∈ Γ', levi1Mat γ = 1
    ·
      have hle : Γ' ≤ A1 F := fun γ hγ =>
        hR ⟨hγ, mem_pCoreOf_stabV0_iff.mpr ⟨hS hγ, hall γ hγ⟩⟩
      exact (Subgroup.card_le_of_le hle).trans card_A1_le
    · push Not at hall
      obtain ⟨γ₀, hγ₀, hM⟩ := hall
      obtain ⟨d, hd⟩ := exists_inf_Z1_le_rootD hS hΓ'1 hΓ'c hγ₀ hM
      have h2 := card_le_mul_card_inf_Z1 hR
      have h3 : Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F) ⊓ Z1 F) ≤ Nat.card F :=
        (Subgroup.card_le_of_le (le_trans (inf_le_inf_right _ inf_le_left) hd)).trans
          (card_rootD_le d)
      calc Nat.card ↥Γ' ≤ Nat.card F * Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F)) := h1
        _ ≤ Nat.card F * (Nat.card F * Nat.card F) :=
          Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_right _ h3))
        _ = Nat.card F ^ 3 := by ring
  ·
    have hA' : ∀ r ∈ Γ, ∀ x, qr r x = 0 := fun r hr x => by
      by_contra h
      exact hA ⟨r, hr, x, h⟩
    obtain ⟨w₀, hw₀, hfix₀⟩ := exists_fix_ne_zero hΓ1
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hw₀
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := hΓ' ▸ hconj1 g⁻¹
    have hc' : Nat.card ↥Γ' = Nat.card ↥Γ := hΓ' ▸ hcard g⁻¹
    have hS : Γ' ≤ stabV0 F := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩
      show g2Act (g⁻¹ * γ * g⁻¹⁻¹) (eu 0 1) = eu 0 1
      rw [inv_inv, g2Act_mul_apply, g2Act_mul_apply, hg, hfix₀ γ hγ, ← hg, g2Act_inv_apply]
    have hq0 : ∀ r ∈ Γ', ∀ x, qr r x = 0 := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩ x
      have h1 := qr_conj g⁻¹ γ (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      change qr (g⁻¹ * γ * g⁻¹⁻¹) x = 0
      rw [inv_inv, h1, hA' γ hγ]
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ Z1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq_of_qr_zero (hq0 _ hhΓ')
      exact ⟨(p', q'), eq_uSL_of_A1⟩
    have h1 := card_le_mul_card_inf_R1 hF hn hS hΓ'1
    rw [← hc']
    calc Nat.card ↥Γ' ≤ Nat.card F * Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F)) := h1
      _ ≤ Nat.card F * Nat.card F ^ 2 :=
        Nat.mul_le_mul_left _ ((Subgroup.card_le_of_le hR).trans card_Z1_le)
      _ = Nat.card F ^ 3 := by ring

theorem card_mul_card_fixSub [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) :
    Nat.card ↥Γ * Nat.card (fixSub Γ) ≤ Nat.card F ^ 6 ∧
      (Γ ≠ ⊥ → Nat.card F ^ 6 ≤ Nat.card ↥Γ * Nat.card (fixSub Γ) →
        Nat.card ↥Γ = Nat.card F ^ 3 ∧ Nat.card (fixSub Γ) = Nat.card F ^ 3) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  by_cases hne : Γ = ⊥
  · subst hne
    refine ⟨?_, fun h => absurd rfl h⟩
    rw [fixSub_bot, Subgroup.card_bot, one_mul, Nat.card_congr Submodule.topEquiv.toEquiv,
      card_Q]
  obtain ⟨⟨t, htΓ⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hle : (fixSub Γ).toAddSubgroup ≤ fixQ t := fun x hx => mem_fixQ.mpr (hx t htΓ)
  have hc4 : Nat.card (fixSub Γ) ≤ Nat.card F ^ 4 :=
    (AddSubgroup.card_le_of_le hle).trans (card_fixQ_le (hΓ1 t htΓ) ht1')
  set d := Module.finrank F (fixSub Γ) with hd
  have hcd : Nat.card (fixSub Γ) = Nat.card F ^ d := Module.natCard_eq_pow_finrank
  rw [hcd] at hc4 ⊢
  have hd4 : d ≤ 4 := (Nat.pow_le_pow_iff_right hq).mp hc4
  have h3 := card_le_cube hF hn hΓ1 hΓc
  rcases Nat.lt_or_ge d 4 with hd3 | hd4'
  · have hd3' : d ≤ 3 := by omega
    have hprod : Nat.card ↥Γ * Nat.card F ^ d ≤ Nat.card F ^ (3 + d) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ h3
    refine ⟨hprod.trans (Nat.pow_le_pow_right (by omega) (by omega)), fun _ hge => ?_⟩
    have h6 : 6 ≤ 3 + d := (Nat.pow_le_pow_iff_right hq).mp (hge.trans hprod)
    have hd3 : d = 3 := by omega
    rw [hd3] at hge ⊢
    refine ⟨le_antisymm h3 ?_, rfl⟩
    have hpos : 0 < Nat.card F ^ 3 := by positivity
    have h7 : Nat.card F ^ 3 * Nat.card F ^ 3 ≤ Nat.card ↥Γ * Nat.card F ^ 3 := by
      rw [← pow_add]
      exact hge
    exact Nat.le_of_mul_le_mul_right h7 hpos
  · have hd44 : d = 4 := le_antisymm hd4 hd4'
    have hΓq : Nat.card ↥Γ ≤ Nat.card F :=
      card_le_of_card_fixSub hΓ1 hne (by rw [hcd, hd44])
    have hprod : Nat.card ↥Γ * Nat.card F ^ d ≤ Nat.card F ^ 5 := by
      rw [hd44, show Nat.card F ^ 5 = Nat.card F * Nat.card F ^ 4 by ring]
      exact Nat.mul_le_mul_right _ hΓq
    have h56 : Nat.card F ^ 5 < Nat.card F ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
    exact ⟨hprod.trans h56.le, fun _ hge => absurd (hge.trans hprod) (not_le.mpr h56)⟩

end CFSG.Quasithin.B42G2
