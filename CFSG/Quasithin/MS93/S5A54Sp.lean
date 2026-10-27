module

public import CFSG.Quasithin.MS93.S5AGeo2

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

@[expose] def IsCandSp (R A : Subgroup (Sp4 F)) : Prop :=
  A ≤ R ∧ Nat.card (V4 F) ≤ Nat.card (fixSp A) * Nat.card A ∧
    Nat.card (V4 F) ≤ Nat.card (fixSp A) * Nat.card F ^ 2

@[expose] def candMax (R : Subgroup (Sp4 F)) : Set (Subgroup (Sp4 F)) :=
  {A | IsCandSp R A ∧ ∀ B, IsCandSp R B → Nat.card B ≤ Nat.card A}

variable [Finite F]

theorem card_V4_eq : Nat.card (V4 F) = Nat.card F ^ 4 := card_V4

theorem one_lt_card_F [CharP F 2] : 1 < Nat.card F := by
  have := MSP.two_dvd_card (F := F)
  have hpos : 0 < Nat.card F := Nat.card_pos
  omega

theorem two_le_finrank_of_isCandSp [CharP F 2] {R A : Subgroup (Sp4 F)} (hA : IsCandSp R A) :
    2 ≤ Module.finrank F (fixSp A) := by
  have h := hA.2.2
  rw [card_V4, card_fixSp, ← pow_add] at h
  have := (Nat.pow_le_pow_iff_right one_lt_card_F).1 h
  omega

theorem isCandSp_bot (R : Subgroup (Sp4 F)) : IsCandSp R ⊥ := by
  have htop : fixSp (⊥ : Subgroup (Sp4 F)) = ⊤ := fixSp_eq_top_iff.2 rfl
  have hc : Nat.card ↥(⊤ : Submodule F (V4 F)) = Nat.card (V4 F) :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  refine ⟨bot_le, ?_, ?_⟩ <;> rw [htop, hc]
  · simp
  · exact Nat.le_mul_of_pos_right _ (pow_pos Nat.card_pos 2)

omit [Finite F] in
theorem isCandSp_map_conj {R A : Subgroup (Sp4 F)} (hA : IsCandSp R A) {r : Sp4 F} (hr : r ∈ R) :
    IsCandSp R (A.map (MulAut.conj r).toMonoidHom) := by
  have hcard : Nat.card (fixSp (A.map (MulAut.conj r).toMonoidHom)) = Nat.card (fixSp A) := by
    rw [fixSp_map_conj]
    have hinj : Function.Injective (mulVecLin (mat r)) := mulVec_mat_injective r
    exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv.symm
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact R.mul_mem (R.mul_mem hr (hA.1 ha)) (R.inv_mem hr)
  · rw [hcard, Subgroup.card_map_of_injective (MulAut.conj r).injective]
    exact hA.2.1
  · rw [hcard]
    exact hA.2.2

omit [Finite F] in
theorem map_conj_mem_candMax {R A : Subgroup (Sp4 F)} (hA : A ∈ candMax R) {r : Sp4 F}
    (hr : r ∈ R) : A.map (MulAut.conj r).toMonoidHom ∈ candMax R := by
  refine ⟨isCandSp_map_conj hA.1 hr, fun B hB => ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj r).injective]
  exact hA.2 B hB

theorem candMax_nonempty (R : Subgroup (Sp4 F)) : (candMax R).Nonempty := by
  obtain ⟨A, hA, hmax⟩ := Set.exists_max_image (Set.ofPred (IsCandSp R)) (fun A => Nat.card ↥A)
    (Set.toFinite _) ⟨⊥, isCandSp_bot R⟩
  exact ⟨A, hA, fun B hB => hmax B hB⟩

variable [CharP F 2]

theorem isCandSp_cases {R A : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) (hA : IsCandSp R A)
    (hA1 : A ≠ ⊥) :
    (∃ p, IsPoint p ∧ A = xPoint p) ∨
      (∃ l, IsLine l ∧ A ≤ qLine l ∧ fixSp A = l ∧ Nat.card F ^ 2 ≤ Nat.card A) := by
  have hA2 : IsPGroup 2 A := hR.to_le hA.1
  have h2 := two_le_finrank_of_isCandSp hA
  have h4 := finrank_le_four (fixSp A)
  have hne4 : Module.finrank F (fixSp A) ≠ 4 := fun h' =>
    hA1 (fixSp_eq_top_iff.1 (Submodule.eq_top_of_finrank_eq (by rw [h']; simp)))
  rcases (show Module.finrank F (fixSp A) = 2 ∨ Module.finrank F (fixSp A) = 3 by omega)
    with h | h
  · obtain ⟨hl, hAl⟩ := isLine_fixSp_of_finrank_two hA2 h
    refine Or.inr ⟨_, hl, hAl, rfl, ?_⟩
    have h1 := hA.2.1
    rw [card_V4, card_fixSp, h] at h1
    have hq : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
    have : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 2 * Nat.card A := by
      rw [← pow_add]; exact h1
    exact Nat.le_of_mul_le_mul_left this hq
  · refine Or.inl ?_
    refine eq_xPoint_of_finrank_fixSp_three h ?_
    have h1 := hA.2.1
    rw [card_V4, card_fixSp, h] at h1
    have hq : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
    have : Nat.card F ^ 3 * Nat.card F ≤ Nat.card F ^ 3 * Nat.card A := by
      rw [← pow_succ]; exact h1
    exact Nat.le_of_mul_le_mul_left this hq

omit [CharP F 2] in
theorem isCandSp_qLine_inf {R : Subgroup (Sp4 F)} {l : Submodule F (V4 F)} (hl : IsLine l)
    (h : Nat.card F ^ 2 ≤ Nat.card ↥(qLine l ⊓ R)) : IsCandSp R (qLine l ⊓ R) := by
  have hfix : Nat.card F ^ 2 ≤ Nat.card (fixSp (qLine l ⊓ R)) := by
    have hle : l ≤ fixSp (qLine l ⊓ R) := (fixSp_qLine hl).symm.le.trans
      (fixSp_antitone inf_le_left)
    have := Nat.card_le_card_of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
    rw [Module.natCard_eq_pow_finrank (K := F) (V := l), hl.1] at this
    exact this
  refine ⟨inf_le_right, ?_, ?_⟩
  · rw [card_V4, show 4 = 2 + 2 from rfl, pow_add]
    exact Nat.mul_le_mul hfix h
  · rw [card_V4, show 4 = 2 + 2 from rfl, pow_add]
    exact Nat.mul_le_mul_right _ hfix

omit [CharP F 2] in
theorem isCandSp_xPoint {R : Subgroup (Sp4 F)} {p : Submodule F (V4 F)} (hp : IsPoint p)
    (h : xPoint p ≤ R) : IsCandSp R (xPoint p) := by
  have hfix : Nat.card (fixSp (xPoint p)) = Nat.card F ^ 3 := by
    rw [fixSp_xPoint hp, Module.natCard_eq_pow_finrank (K := F), finrank_perp_point hp]
  refine ⟨h, ?_, ?_⟩
  · rw [hfix, card_xPoint hp, card_V4, ← pow_succ]
  · rw [hfix, card_V4]
    calc Nat.card F ^ 4 ≤ Nat.card F ^ 5 :=
          Nat.pow_le_pow_right Nat.card_pos (by norm_num)
      _ = Nat.card F ^ 3 * Nat.card F ^ 2 := by rw [← pow_add]

omit [CharP F 2] in
theorem card_le_card_inf_mul {p l₀ : Submodule F (V4 F)} (hp : IsPoint p) (hl₀ : IsLine l₀)
    (hpl : p ≤ l₀) {A : Subgroup (Sp4 F)} (hAp : A ≤ fixer p)
    (hA : ∀ a ∈ A, ∀ v ∈ l₀, mat a *ᵥ v - v ∈ p) :
    Nat.card A ≤ Nat.card ↥(qLine l₀ ⊓ A) * Nat.card F := by
  obtain ⟨w, hwl, hwp⟩ : ∃ w ∈ l₀, w ∉ p := by
    by_contra h
    push Not at h
    have := Submodule.finrank_mono (show l₀ ≤ p from h)
    rw [hl₀.1, hp] at this
    omega
  have hsup := eq_sup_span_of_not_mem hp hl₀ hpl hwl hwp
  let φ : A →* Multiplicative p :=
    { toFun := fun a => Multiplicative.ofAdd ⟨mat (a : Sp4 F) *ᵥ w - w, hA a a.2 w hwl⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp [mat_one]
      map_mul' := fun a b => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp only [toAdd_ofAdd, toAdd_mul, Submodule.coe_add, Subgroup.coe_mul]
        have hb := hA b b.2 w hwl
        have h1 : mat (b : Sp4 F) *ᵥ w = (mat (b : Sp4 F) *ᵥ w - w) + w := by abel
        rw [mat_mul_mulVec, h1, mulVec_add, mem_fixer.1 (hAp a.2) _ hb]
        abel }
  have hker : ∀ a : A, φ a = 1 ↔ (a : Sp4 F) ∈ qLine l₀ := by
    intro a
    constructor
    · intro ha
      have h0 : mat (a : Sp4 F) *ᵥ w - w = 0 := by
        have := congrArg (fun x => ((Multiplicative.toAdd x : p) : V4 F)) ha
        simpa [φ] using this
      rw [mem_fixer]
      intro v hv
      rw [← hsup] at hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [mulVec_add, mulVec_smul, mem_fixer.1 (hAp a.2) x hx, sub_eq_zero.1 h0]
    · intro ha
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simp [φ, mem_fixer.1 ha w hwl]
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have hk : Nat.card φ.ker = Nat.card ↥(qLine l₀ ⊓ A) := by
    have : φ.ker = (qLine l₀).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rw [this, card_subgroupOf', inf_comm]
  have hr : Nat.card φ.range ≤ Nat.card F := by
    calc Nat.card φ.range ≤ Nat.card (Multiplicative p) := Subgroup.card_le_card_group _
      _ = Nat.card F := by
        rw [show Nat.card (Multiplicative p) = Nat.card p from rfl,
          Module.natCard_eq_pow_finrank (K := F) (V := p), hp, pow_one]
  rw [← h1, hk]
  exact Nat.mul_le_mul_left _ hr
  where
    card_subgroupOf' (K L' : Subgroup (Sp4 F)) :
        Nat.card (K.subgroupOf L') = Nat.card ↥(K ⊓ L') := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective L'.subtype_injective]

theorem exists_isCandSp_ne_bot {R A : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) (hAR : A ≤ R)
    (hA1 : A ≠ ⊥) (hA : Nat.card (V4 F) ≤ Nat.card (fixSp A) * Nat.card A) :
    ∃ B, IsCandSp R B ∧ B ≠ ⊥ := by
  have hq := one_lt_card_F (F := F)
  have hA2 : IsPGroup 2 A := hR.to_le hAR
  by_cases h2 : 2 ≤ Module.finrank F (fixSp A)
  · refine ⟨A, ⟨hAR, hA, ?_⟩, hA1⟩
    rw [card_V4, card_fixSp, ← pow_add]
    exact Nat.pow_le_pow_right Nat.card_pos (by omega)
  · have hpos := finrank_pos_of_ne_bot (fixSp_ne_bot hA2)
    have hfd : Module.finrank F (fixSp A) = 1 := by omega
    set p := fixSp A with hpdef
    have hp : IsPoint p := hfd
    have hAp : A ≤ fixer p := le_fixer_iff.2 le_rfl
    obtain ⟨l₀, hl₀, hpl, hAl⟩ := exists_line_mod hp hA2 hAp
    have hbound := card_le_card_inf_mul hp hl₀ hpl hAp hAl
    have hA3 : Nat.card F ^ 3 ≤ Nat.card A := by
      rw [card_V4, card_fixSp, hfd, pow_one] at hA
      have : Nat.card F * Nat.card F ^ 3 ≤ Nat.card F * Nat.card A := by
        rw [← pow_succ']; exact hA
      exact Nat.le_of_mul_le_mul_left this Nat.card_pos
    have hq2 : Nat.card F ^ 2 ≤ Nat.card ↥(qLine l₀ ⊓ A) := by
      have : Nat.card F ^ 2 * Nat.card F ≤ Nat.card ↥(qLine l₀ ⊓ A) * Nat.card F := by
        rw [← pow_succ]; exact hA3.trans hbound
      exact Nat.le_of_mul_le_mul_right this Nat.card_pos
    have hmono : Nat.card ↥(qLine l₀ ⊓ A) ≤ Nat.card ↥(qLine l₀ ⊓ R) :=
      Subgroup.card_le_of_le (inf_le_inf_left _ hAR)
    refine ⟨qLine l₀ ⊓ R, isCandSp_qLine_inf hl₀ (hq2.trans hmono), fun h => ?_⟩
    rw [h, Subgroup.card_bot] at hmono
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero hq
    omega

omit [Finite F] [CharP F 2] in
theorem card_eq_of_mem_candMax {R A B : Subgroup (Sp4 F)} (hA : A ∈ candMax R)
    (hB : B ∈ candMax R) : Nat.card A = Nat.card B :=
  le_antisymm (hB.2 A hA.1) (hA.2 B hB.1)

theorem sp4_54 {R : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) (hne : ∃ B, IsCandSp R B ∧ B ≠ ⊥)
    (hX : ∀ p, IsPoint p → candMax R ≠ {xPoint p}) :
    (∃ A₀ l, candMax R = {A₀} ∧ IsLine l ∧ R ≤ stab l ∧ A₀ ≤ qLine l ∧
        Nat.card F ^ 2 ≤ Nat.card A₀) ∨
      (Nat.card (candMax R) = Nat.card F + 1 ∧ ∃ p, IsPoint p ∧ R = qPoint p ∧
        (⨆ A ∈ candMax R, A) = R) := by
  have hq := one_lt_card_F (F := F)
  have hq2 : Nat.card F < Nat.card F ^ 2 := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
  obtain ⟨A₀, hA₀⟩ := candMax_nonempty R
  obtain ⟨B, hB, hB1⟩ := hne
  have hA₀1 : A₀ ≠ ⊥ := by
    intro h
    have h1 := hA₀.2 B hB
    rw [h, Subgroup.card_bot] at h1
    exact hB1 (Subgroup.eq_bot_of_card_le B h1)
  have hmem1 : ∀ C ∈ candMax R, C ≠ ⊥ := fun C hC h => by
    have := card_eq_of_mem_candMax hA₀ hC
    rw [h, Subgroup.card_bot] at this
    exact hA₀1 (Subgroup.eq_bot_of_card_le A₀ this.le)
  rcases isCandSp_cases hR hA₀.1 hA₀1 with ⟨p₀, hp₀, rfl⟩ | ⟨l₀, hl₀, hA₀l, hfix₀, hcard₀⟩
  ·
    exfalso
    obtain ⟨C, hC, hCne⟩ : ∃ C ∈ candMax R, C ≠ xPoint p₀ := by
      by_contra h
      push Not at h
      exact hX p₀ hp₀ (Set.eq_singleton_iff_unique_mem.2 ⟨hA₀, h⟩)
    have hCcard := card_eq_of_mem_candMax hA₀ hC
    rw [card_xPoint hp₀] at hCcard
    rcases isCandSp_cases hR hC.1 (hmem1 C hC) with ⟨p₁, hp₁, rfl⟩ | ⟨l, -, -, -, hcl⟩
    · have hne : p₀ ≠ p₁ := fun e => hCne (e ▸ rfl)
      have hperp := le_perp_of_xPoint_le hp₀ hp₁ hne hR hA₀.1.1 hC.1.1
      have hl := isLine_sup hp₀ hp₁ hne hperp
      have hsup := card_xPoint_sup hp₀ hp₁ hne hperp
      have hle : xPoint p₀ ⊔ xPoint p₁ ≤ qLine (p₀ ⊔ p₁) ⊓ R :=
        sup_le (le_inf (xPoint_le_qLine hl le_sup_left) hA₀.1.1)
          (le_inf (xPoint_le_qLine hl le_sup_right) hC.1.1)
      have hcard := (Subgroup.card_le_of_le hle)
      have hcand := isCandSp_qLine_inf hl (hsup.trans hcard)
      have := hA₀.2 _ hcand
      rw [card_xPoint hp₀] at this
      omega
    · omega
  ·
    have hlineC : ∀ C ∈ candMax R, IsLine (fixSp C) ∧ C ≤ qLine (fixSp C) ∧
        C = qLine (fixSp C) ⊓ R ∧ Nat.card F ^ 2 ≤ Nat.card C := by
      intro C hC
      have hCc := card_eq_of_mem_candMax hA₀ hC
      rcases isCandSp_cases hR hC.1 (hmem1 C hC) with ⟨p, hp, rfl⟩ | ⟨l, hl, hCl, hfix, hcl⟩
      · rw [card_xPoint hp] at hCc
        omega
      · rw [hfix]
        refine ⟨hl, hCl, ?_, hcl⟩
        have hle : C ≤ qLine l ⊓ R := le_inf hCl hC.1.1
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        exact hC.2 _ (isCandSp_qLine_inf hl (hcl.trans (Subgroup.card_le_of_le hle)))
    by_cases hsingle : candMax R = {A₀}
    · refine Or.inl ⟨A₀, l₀, hsingle, hl₀, fun r hr => ?_, hA₀l, hcard₀⟩
      have hmap := map_conj_mem_candMax hA₀ hr
      rw [hsingle, Set.mem_singleton_iff] at hmap
      rw [← hfix₀]
      exact normalizer_le_stab_fixSp A₀ (mem_normalizer_iff_map_conj.2 hmap)
    · obtain ⟨B₁, hB₁, hB₁ne⟩ : ∃ C ∈ candMax R, C ≠ A₀ := by
        by_contra h
        push Not at h
        exact hsingle (Set.eq_singleton_iff_unique_mem.2 ⟨hA₀, h⟩)
      obtain ⟨hl₁, -, hB₁eq, -⟩ := hlineC B₁ hB₁
      obtain ⟨-, -, hA₀eq, -⟩ := hlineC A₀ hA₀
      set l₁ := fixSp B₁
      have hll : l₀ ≠ l₁ := by
        intro e
        apply hB₁ne
        rw [hB₁eq, hA₀eq, hfix₀, e]
      have hinf0 : l₀ ⊓ l₁ ≠ ⊥ := by
        have := inf_fixSp_ne_bot hR hA₀.1.1 hB₁.1.1
        rwa [hfix₀] at this
      set p := l₀ ⊓ l₁ with hpdef
      have hp : IsPoint p := isPoint_inf hl₀ hl₁ hll hinf0
      have hfixR : fixSp R = p := by
        have hle : fixSp R ≤ p := le_inf (hfix₀ ▸ fixSp_antitone hA₀.1.1)
          (fixSp_antitone hB₁.1.1)
        have hpos := finrank_pos_of_ne_bot (fixSp_ne_bot hR)
        exact Submodule.eq_of_le_of_finrank_eq hle (by
          have := Submodule.finrank_mono hle; rw [hp] at this ⊢; omega)
      have hRp : R ≤ fixer p := le_fixer_iff.2 hfixR.ge
      have hthrough : ∀ C ∈ candMax R, p ≤ fixSp C := by
        intro C hC
        have hlC := (hlineC C hC).1
        refine le_of_inf_ne_bot hl₀ hl₁ hlC hp rfl ?_ ?_
        · have := inf_fixSp_ne_bot hR hC.1.1 hA₀.1.1; rwa [hfix₀] at this
        · exact inf_fixSp_ne_bot hR hC.1.1 hB₁.1.1
      obtain ⟨m, hm, hpm, hRm⟩ := exists_line_mod hp hR hRp
      have hRstab_m : R ≤ stab m := fun r hr => mem_stab_of_le fun v hv => by
        have := hRm r hr v hv
        have e : mat r *ᵥ v = (mat r *ᵥ v - v) + v := by abel
        rw [e]
        exact m.add_mem (hpm this) hv
      obtain ⟨w, hwm, hwp⟩ : ∃ w ∈ m, w ∉ p := by
        by_contra h
        push Not at h
        have := Submodule.finrank_mono (show m ≤ p from h)
        rw [hm.1, hp] at this
        omega
      have hK : ∀ C ∈ candMax R, fixSp C ≠ m →
          C = qLine (fixSp C) ⊓ qPoint p ∧ Nat.card C = Nat.card F ^ 2 := by
        intro C hC hCm
        obtain ⟨hlC, hCl, -, hcC⟩ := hlineC C hC
        have hpC := hthrough C hC
        have hCp : C ≤ qPoint p := by
          by_contra hCp
          apply hCm
          have hwC : w ∈ fixSp C := mem_of_sub_mem hlC hp hpC hCl hCp
            (le_perp_of_le hm hpm hwm) fun c hc => hRm c (hC.1.1 hc) w hwm
          have := eq_sup_span_of_not_mem hp hm hpm hwm hwp
          rw [← this]
          exact IsLine.eq_of_le (this ▸ hm) hlC
            (sup_le hpC ((Submodule.span_singleton_le_iff_mem _ _).2 hwC)) |>.symm ▸ rfl
        have hle : C ≤ qLine (fixSp C) ⊓ qPoint p := le_inf hCl hCp
        have hc2 := card_qLine_inf_qPoint hp hlC hpC
        have heq := Subgroup.eq_of_le_of_card_ge hle (hc2 ▸ hcC)
        exact ⟨heq, by rw [heq, hc2]⟩
      obtain ⟨C₁, hC₁, hC₁m, C₂, hC₂, hC₁₂⟩ : ∃ C₁ ∈ candMax R, fixSp C₁ ≠ m ∧
          ∃ C₂ ∈ candMax R, fixSp C₁ ≠ fixSp C₂ := by
        by_cases h0 : l₀ = m
        · exact ⟨B₁, hB₁, fun e => hll (h0.trans e.symm), A₀, hA₀, by rw [hfix₀]; exact hll.symm⟩
        · exact ⟨A₀, hA₀, by rw [hfix₀]; exact h0, B₁, hB₁, by rw [hfix₀]; exact hll⟩
      obtain ⟨hC₁eq, hC₁card⟩ := hK C₁ hC₁ hC₁m
      have hN : ∀ C ∈ candMax R, Nat.card C = Nat.card F ^ 2 := fun C hC =>
        (card_eq_of_mem_candMax hC hC₁).trans hC₁card
      obtain ⟨hlC₁, -, -, -⟩ := hlineC C₁ hC₁
      have hpC₁ := hthrough C₁ hC₁
      have hQR : qPoint p ≤ R := by
        have hgen : ∀ C ∈ candMax R, fixSp C ≠ m → fixSp C₁ ≠ fixSp C → qPoint p ≤ R := by
          intro C hC hCm hne
          obtain ⟨hCeq, -⟩ := hK C hC hCm
          obtain ⟨hlC, -, -, -⟩ := hlineC C hC
          rw [← qLine_inf_qPoint_sup hp hlC₁ hlC hne hpC₁ (hthrough C hC), ← hC₁eq, ← hCeq]
          exact sup_le hC₁.1.1 hC.1.1
        by_cases hC₂m : fixSp C₂ ≠ m
        · exact hgen C₂ hC₂ hC₂m hC₁₂
        · push Not at hC₂m
          by_cases hall : R ≤ stab (fixSp C₁)
          · have hRQ : R ≤ qPoint p := le_qPoint_of_stab hp hlC₁ hm hC₁m hpC₁ hpm hR hRp hall
              hRstab_m
            obtain ⟨hlC₂, hC₂l, -, -⟩ := hlineC C₂ hC₂
            have hle : C₂ ≤ qLine (fixSp C₂) ⊓ qPoint p := le_inf hC₂l (hC₂.1.1.trans hRQ)
            have hC₂eq := Subgroup.eq_of_le_of_card_ge hle
              ((card_qLine_inf_qPoint hp hlC₂ (hthrough C₂ hC₂)).trans (hN C₂ hC₂).symm).le
            rw [← qLine_inf_qPoint_sup hp hlC₁ hlC₂ hC₁₂ hpC₁ (hthrough C₂ hC₂), ← hC₁eq,
              ← hC₂eq]
            exact sup_le hC₁.1.1 hC₂.1.1
          · obtain ⟨r, hr, hrl⟩ := Set.not_subset.1 hall
            have hC' := map_conj_mem_candMax hC₁ hr
            have hfixC' : fixSp (C₁.map (MulAut.conj r).toMonoidHom) =
                (fixSp C₁).map (mulVecLin (mat r)) := fixSp_map_conj r C₁
            refine hgen _ hC' ?_ ?_
            · rw [hfixC']
              intro e
              apply hC₁m
              have hrm : (m.map (mulVecLin (mat r))) = m := hRstab_m hr
              exact Submodule.map_injective_of_injective (mulVec_mat_injective r) (e.trans hrm.symm)
            · rw [hfixC']
              intro e
              exact hrl (mem_stab_iff.2 e.symm)
      have hRQ : R = qPoint p := by
        refine le_antisymm ?_ hQR
        by_contra hRQ
        have hlt : qPoint p < R := lt_of_le_of_ne hQR fun e => hRQ e.symm.le
        have hbound := card_le_card_inf_mul hp hm hpm hRp hRm
        have hR3 : Nat.card F ^ 3 < Nat.card R := by
          rw [← card_qPoint hp]
          exact Subgroup.card_lt_of_lt hlt
        have hqm : Nat.card F ^ 2 < Nat.card ↥(qLine m ⊓ R) := by
          by_contra hle
          push Not at hle
          have : Nat.card R ≤ Nat.card F ^ 2 * Nat.card F := hbound.trans
            (Nat.mul_le_mul_right _ hle)
          have e3 : Nat.card F ^ 2 * Nat.card F = Nat.card F ^ 3 := by ring
          omega
        have hcand := isCandSp_qLine_inf hm hqm.le
        have := hA₀.2 _ hcand
        rw [hN A₀ hA₀] at this
        omega
      have hchar : ∀ C, C ∈ candMax R ↔ ∃ l, IsLine l ∧ p ≤ l ∧ C = qLine l ⊓ qPoint p := by
        intro C
        constructor
        · intro hC
          obtain ⟨hlC, -, hCeq, -⟩ := hlineC C hC
          exact ⟨fixSp C, hlC, hthrough C hC, hRQ ▸ hCeq⟩
        · rintro ⟨l, hl, hpl, rfl⟩
          have hc := card_qLine_inf_qPoint hp hl hpl
          have hcand : IsCandSp R (qLine l ⊓ qPoint p) := by
            have := isCandSp_qLine_inf (R := R) hl (by rw [hRQ, hc])
            rw [hRQ] at this ⊢
            exact this
          refine ⟨hcand, fun D hD => ?_⟩
          rw [hc, ← hN A₀ hA₀]
          exact hA₀.2 D hD
      refine Or.inr ⟨?_, p, hp, hRQ, ?_⟩
      · rw [← card_lines_through hp]
        let e : {l : Submodule F (V4 F) // IsLine l ∧ p ≤ l} → candMax R := fun l =>
          ⟨qLine l.1 ⊓ qPoint p, (hchar _).2 ⟨l.1, l.2.1, l.2.2, rfl⟩⟩
        have he : Function.Bijective e := by
          refine ⟨fun l l' hll' => ?_, fun C => ?_⟩
          · have h1 : qLine l.1 ⊓ qPoint p = qLine l'.1 ⊓ qPoint p := congrArg Subtype.val hll'
            have hf : ∀ l : {l : Submodule F (V4 F) // IsLine l ∧ p ≤ l},
                fixSp (qLine l.1 ⊓ qPoint p) = l.1 := fun l =>
              fixSp_eq_of_le_qLine l.2.1 inf_le_left (by
                rw [card_qLine_inf_qPoint hp l.2.1 l.2.2]; exact hq2)
            exact Subtype.ext ((hf l).symm.trans (h1 ▸ hf l'))
          · obtain ⟨l, hl, hpl, hCeq⟩ := (hchar C.1).1 C.2
            exact ⟨⟨l, hl, hpl⟩, Subtype.ext hCeq.symm⟩
        exact (Nat.card_congr (Equiv.ofBijective e he)).symm
      · refine le_antisymm (iSup₂_le fun C hC => hC.1.1) ?_
        obtain ⟨hlC₂, -, -, -⟩ := hlineC C₂ hC₂
        have hQ := qLine_inf_qPoint_sup hp hlC₁ hlC₂ hC₁₂ hpC₁ (hthrough C₂ hC₂)
        refine (le_of_eq (hRQ.trans hQ.symm)).trans (sup_le ?_ ?_)
        · exact le_iSup₂_of_le (f := fun A (_ : A ∈ candMax R) => A) _
            ((hchar _).2 ⟨_, hlC₁, hpC₁, rfl⟩) le_rfl
        · exact le_iSup₂_of_le (f := fun A (_ : A ∈ candMax R) => A) _
            ((hchar _).2 ⟨_, hlC₂, hthrough C₂ hC₂, rfl⟩) le_rfl

end CFSG.Quasithin.MS93.S5
