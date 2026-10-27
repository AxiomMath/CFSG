module

public import CFSG.Quasithin.Background.SmithD37Orth
public import CFSG.Quasithin.Background.SmithD37Inv
public import CFSG.Quasithin.Background.SmithD37Qhat

public section

namespace CFSG.Quasithin.SmithD37

variable {U : Type} [CommGroup U] [Finite U] {X L₁ L₂ : Subgroup (MulAut U)} {s : MulAut U}
  {F : Type} [Field F] [Fintype F] [CharP F 2] {d : ℕ}

omit [Finite U] [Fintype F] [CharP F 2] in
theorem top_ne_bot_of_pos (hd : 0 < d) : (⊤ : Submodule F (Fin d → F)) ≠ ⊥ := by
  intro h
  have h1 := congrArg (fun S : Submodule F (Fin d → F) => Module.finrank F S) h
  simp only [finrank_top, finrank_bot, Module.finrank_fin_fun] at h1
  omega

theorem cls2F_line (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F d) (hd : 2 ≤ d)
    {y : Fin d → F} (hy : y ≠ 0) {P : Subgroup (MulAut U)} (hE : IsElemAbelian2 P)
    (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    (hP : P ≤ stabSub (rowSub Mm (Submodule.span F {y})))
    (h3 : commSeries (autSub P (rowSub Mm (Submodule.span F {y}))) 3 = ⊥)
    (hne : (facAct Mm (facStepLine hy) hP (le_stabSub_rowSub_bot Mm P)).range ≠ ⊥)
    (hoff : Nat.card F ^ d ≤
      Nat.card (facAct Mm (facStepLine hy) hP (le_stabSub_rowSub_bot Mm P)).range ^ 2 *
        Nat.card ↥(fixV (facAct Mm (facStepLine hy) hP (le_stabSub_rowSub_bot Mm P)).range)) :
    Cls2F (natSub Mm ⊔ (facAct Mm (facStepLine hy) hP (le_stabSub_rowSub_bot Mm P)).range)
      (natSub Mm) (facAct Mm (facStepLine hy) hP (le_stabSub_rowSub_bot Mm P)).range := by
  have hP' := le_stabSub_rowSub_bot Mm P
  have hB2 := isPGroup_range_facAct Mm (facStepLine hy) hP hP' hE.isPGroup
  have hBN := conj_mem_natSub_of_mem_range Mm (facStepLine hy) hP hP' hPN
  refine ⟨natMod_sq, b4Hyp_natSub Mm (by omega) hC.simple (Mm.not_comm hd) hC.sqtk hB2 hBN,
    a38Types_congr (natSubEquiv Mm) hC.a38,
    ⟨le_sup_right, hne, isElemAbelian2_range_facAct Mm (facStepLine hy) hP hP' hE⟩,
    commSeries_range_facAct_line Mm hy hP hP' h3, ?_⟩
  rwa [natCard_natMod]

theorem le_choose (hd : 3 ≤ d) : d ≤ d * (d - 1) / 2 := by
  have h : 2 * d ≤ d * (d - 1) := by
    calc 2 * d = d * 2 := by ring
      _ ≤ d * (d - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem out_case
    (hC : Core X L₁ L₂ s)
    (Mm : MatModel L₁ L₂ F d) (hd : 3 ≤ d) {A : Subgroup (MulAut U)} (hA : A ∈ QhatStar X)
    {t : MulAut U} (htA : t ∈ A) (htN : t ∉ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    d = 3 ∧ Nat.card F = 2 ∧ IsPSL 2 7 1 ↥L₁ := by
  obtain ⟨r, -, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := hA
  have hAr2 : rAV A ≤ 2 := hAr.trans hr2
  obtain ⟨ht₁, ht₂⟩ := hC.swap_of_not_mem (hA2.1 htA) htN
  obtain ⟨hA0, hbound⟩ := out_bound hC Mm hd hA2 hAr2 htA ht₁ ht₂
  set A₀ := A ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) with hA₀
  have hE₀ : IsElemAbelian2 A₀ :=
    ⟨fun x hx y hy => hA2.2.2.1 x hx.1 y hy.1, fun x hx => hA2.2.2.2 x hx.1⟩
  have hPN₀ : ∀ a ∈ A₀, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer ha.2 hl
  have hsw₂ : ∀ k ∈ L₂, t * k * t⁻¹ ∈ L₁ := fun k hk => by
    rw [← ht₂]
    exact ⟨k, hk, rfl⟩
  obtain ⟨y, -, hy, hinv⟩ := exists_line_inv Mm hE₀.isPGroup hPN₀
    (Y := ⊤) (by rw [rowSub_top]; exact fun _ _ _ _ => Subgroup.mem_top _)
    (top_ne_bot_of_pos (by omega))
  have hP := le_stabSub_of_isInvBy hinv
  have hP' := le_stabSub_rowSub_bot Mm A₀
  set E := (facAct Mm (facStepLine hy) hP hP').range with hEdef
  have hcent : A₀ ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hc₁ : ∀ l ∈ L₁, x * l = l * x := fun l hl =>
      (Subgroup.mem_centralizer_iff.mp hx.2 l hl).symm
    have hxt : x * t = t * x := hA2.2.2.1 x hx.1.1 t htA
    exact eq_one_of_comm Mm hc₁ (commute_of_swap hsw₂ hxt hc₁) (e := 1)
      (by rw [pow_one]; exact hA2.2.2.2 x hx.1.1)
  have hEcard : Nat.card E = Nat.card A₀ := by
    have h := card_range_facAct_mul Mm (facStepLine hy) hP hP' hPN₀ hE₀.isPGroup
    rwa [hcent, Subgroup.card_bot, mul_one] at h
  have hA0card : 2 ≤ Nat.card A₀ := by
    have h1 : Nat.card A₀ ≠ 1 := fun h => hA0 (Subgroup.eq_bot_of_card_eq A₀ h)
    have h2 : 0 < Nat.card A₀ := Nat.card_pos
    omega
  have hEne : E ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hEcard
    omega
  have h3 : commSeries (autSub A₀ (rowSub Mm (Submodule.span F {y}))) 3 = ⊥ :=
    commSeries_autSub_eq_bot hP (le_bot_iff.mp (hA3 ▸ commSeries_mono inf_le_left 3))
  have hnt : Nontrivial (natMod F d) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    exact inferInstanceAs (Nontrivial (Multiplicative (Fin d → F)))
  have hfix := two_le_card_fixV natMod_sq
    (isPGroup_range_facAct Mm (facStepLine hy) hP hP' hE₀.isPGroup)
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hoff : Nat.card F ^ d ≤ Nat.card E ^ 2 * Nat.card ↥(fixV E) :=
    calc Nat.card F ^ d ≤ Nat.card F ^ (d * (d - 1) / 2) :=
          Nat.pow_le_pow_right (by omega) (le_choose hd)
      _ ≤ 2 * Nat.card A₀ ^ 2 := hbound
      _ = Nat.card E ^ 2 * 2 := by rw [hEcard]; ring
      _ ≤ Nat.card E ^ 2 * Nat.card ↥(fixV E) := Nat.mul_le_mul_left _ hfix
  have hcls := cls2F_line hC Mm (by omega) hy hE₀ hPN₀ hP h3 hEne hoff
  rcases cls2F_dispatch hcls hq hd (endCard_natSub Mm (by omega)) (natCard_natMod F d) with
    ⟨hd3, hq2, hL⟩ | ⟨hd4, hEq, -⟩ | ⟨hd4, hEq, -⟩
  · exact ⟨hd3, hq2, isPSL_transfer (natSubEquiv Mm) hL⟩
  · exfalso
    subst hd4
    have h1 : Nat.card F ^ 6 ≤ 2 * Nat.card F ^ 4 :=
      calc Nat.card F ^ 6 = Nat.card F ^ (4 * (4 - 1) / 2) := by norm_num
        _ ≤ 2 * Nat.card A₀ ^ 2 := hbound
        _ = 2 * Nat.card E ^ 2 := by rw [hEcard]
        _ ≤ 2 * (Nat.card F ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hEq 2)
        _ = 2 * Nat.card F ^ 4 := by ring
    have h2 : Nat.card F ^ 4 * 4 ≤ Nat.card F ^ 4 * 2 :=
      calc Nat.card F ^ 4 * 4 ≤ Nat.card F ^ 4 * Nat.card F ^ 2 :=
            Nat.mul_le_mul_left _ (by nlinarith)
        _ = Nat.card F ^ 6 := by ring
        _ ≤ 2 * Nat.card F ^ 4 := h1
        _ = Nat.card F ^ 4 * 2 := by ring
    have := Nat.le_of_mul_le_mul_left h2 (by positivity)
    omega
  · exfalso
    subst hd4
    have h1 : Nat.card F ^ 6 ≤ 2 * Nat.card F ^ 2 :=
      calc Nat.card F ^ 6 = Nat.card F ^ (4 * (4 - 1) / 2) := by norm_num
        _ ≤ 2 * Nat.card A₀ ^ 2 := hbound
        _ = 2 * Nat.card E ^ 2 := by rw [hEcard]
        _ ≤ 2 * Nat.card F ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hEq 2)
    have h2 : Nat.card F ^ 2 * 16 ≤ Nat.card F ^ 2 * 2 :=
      calc Nat.card F ^ 2 * 16 ≤ Nat.card F ^ 2 * Nat.card F ^ 4 :=
            Nat.mul_le_mul_left _ (by
              calc 16 = 2 ^ 4 := by norm_num
                _ ≤ Nat.card F ^ 4 := Nat.pow_le_pow_left hq 4)
        _ = Nat.card F ^ 6 := by ring
        _ ≤ 2 * Nat.card F ^ 2 := h1
        _ = Nat.card F ^ 2 * 2 := by ring
    have := Nat.le_of_mul_le_mul_left h2 (by positivity)
    omega

theorem in_case
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F d) (hd : 3 ≤ d)
    {A : Subgroup (MulAut U)} (hA : A ∈ QhatStar X)
    (hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (L₁ : Set (MulAut U)))
    (hnc : ∃ a ∈ A, ∃ l ∈ L₁, a * l ≠ l * a) :
    d = 3 ∧ Nat.card F = 2 ∧ IsPSL 2 7 1 ↥L₁ := by
  have hA' := hA
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := hA'
  have hE := hA2.2.2
  have hPN : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer (hAN a ha) hl
  obtain ⟨y, -, hy, hinv⟩ := exists_line_inv Mm hE.isPGroup hPN
    (Y := ⊤) (by rw [rowSub_top]; exact fun _ _ _ _ => Subgroup.mem_top _)
    (top_ne_bot_of_pos (by omega))
  set I₀ := rowSub Mm (Submodule.span F {y}) with hI₀
  have hP := le_stabSub_of_isInvBy hinv
  have hP' := le_stabSub_rowSub_bot Mm A
  have hLI : ∀ l ∈ L₁, ∀ u ∈ I₀, l u ∈ I₀ := fun l hl u hu =>
    rowSub_inv₁ Mm _ ⟨l, hl⟩ hu
  have hUA : commSub I₀ A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    obtain ⟨a, ha, l, hl, hal⟩ := hnc
    exact hal (commute_of_fix_inv (hPN a ha) hLI (fun u hu => h hu a ha)
      (faithful_line Mm hy) l hl)
  have := hC.simple
  rcases (D2_7 hC.exp hr hA hP hUA).2 with ⟨ε, hε, hQ⟩ | ⟨-, hsup⟩
  · obtain ⟨⟨hEA2, hEr⟩, hE3⟩ := hQ
    have hEr2 : rAV (autSub A I₀) < 2 := by linarith
    have hexpI : ∀ v : ↥I₀, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hC.exp v)
    have hlt := card_lt_sq_mul_fixV hexpI hEA2 hEr2
    set E := (facAct Mm (facStepLine hy) hP hP').range with hEdef
    have hcE := card_range_facAct_line Mm hy hP hP'
    have hfE := card_fixV_range_facAct_line Mm hy hP hP'
    have hI₀card : Nat.card ↥I₀ = Nat.card F ^ d := by
      rw [hI₀, card_rowSub, finrank_span_singleton hy, mul_one]
    rw [hI₀card, ← hcE, ← hfE] at hlt
    have hEne : E ≠ ⊥ := by
      intro h
      apply hEA2.2.1
      apply Subgroup.eq_bot_of_card_eq
      have h1 : Nat.card E = 1 := by rw [h, Subgroup.card_bot]
      rw [← h1, hEdef, hcE]
    have hcls := cls2F_line hC Mm (by omega) hy hE hPN hP hE3 hEne hlt.le
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    rcases cls2F_dispatch hcls hq hd (endCard_natSub Mm (by omega)) (natCard_natMod F d) with
      ⟨hd3, hq2, hL⟩ | ⟨hd4, -, n, -, hLn⟩ | ⟨-, -, hSz⟩
    · exact ⟨hd3, hq2, isPSL_transfer (natSubEquiv Mm) hL⟩
    · exfalso
      subst hd4
      exact false_of_orth hC Mm (isPSL_transfer (natSubEquiv Mm) hLn) hA2 (hAr.trans hr2) hAN
    · exfalso
      rw [natCard_natMod] at hSz
      omega
  · exfalso
    have hL0 : L₁ ≠ ⊥ := hC.ne_bot
    exact false_of_sup_fixV hLI (fun a ha u hu => (hP ha u).2 hu) hPN hsup
      (exists_not_mem_line Mm (by omega) hL0) hnc

theorem big_case
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F d)
    (hd : 3 ≤ d) : d = 3 ∧ Nat.card F = 2 ∧ IsPSL 2 7 1 ↥L₁ := by
  obtain ⟨A, hA⟩ := exists_mem_qhatStar hC.qhat
  have hA2 : IsA2 X A := by
    obtain ⟨r, -, -, ⟨⟨h, -⟩, -⟩, -⟩ := hA
    exact h
  by_cases hout : ∃ t ∈ A, t ∉ Subgroup.normalizer (L₁ : Set (MulAut U))
  · obtain ⟨t, htA, htN⟩ := hout
    exact out_case hC Mm hd hA htA htN
  push Not at hout
  by_cases hnc : ∃ a ∈ A, ∃ l ∈ L₁, a * l ≠ l * a
  · exact in_case hC Mm hd hA hout hnc
  push Not at hnc
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA2.2.1
  have hnc₂ : ∃ a ∈ A, ∃ k ∈ L₂, a * k ≠ k * a := by
    by_contra hc
    push Not at hc
    apply hb
    exact Subtype.ext (eq_one_of_comm Mm (hnc _ b.2) (hc _ b.2) (e := 1)
      (by rw [pow_one]; exact hA2.2.2.2 _ b.2))
  obtain ⟨hd3, hq2, hL₂⟩ := in_case hC.swap Mm.swap hd hA
    (fun a ha => hC.mem_normalizer₂ (hA2.1 ha) (hout a ha)) hnc₂
  exact ⟨hd3, hq2, isPSL_transfer hC.equiv hL₂⟩

end CFSG.Quasithin.SmithD37
