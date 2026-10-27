module

public import CFSG.Quasithin.MS93.S5A56Sp

public section

namespace CFSG.Quasithin.MS93.S52i

open Matrix CFSG.Quasithin.MS93.MSP

variable {F : Type} [Field F]

@[expose] def commOn (A : Subgroup (Sp4 F)) (U : Submodule F (V4 F)) : Submodule F (V4 F) :=
  Submodule.span F {w | ∃ a ∈ A, ∃ u ∈ U, w = mat a *ᵥ u - u}

theorem sub_mem_commOn {A : Subgroup (Sp4 F)} {U : Submodule F (V4 F)} {a : Sp4 F} (ha : a ∈ A)
    {u : V4 F} (hu : u ∈ U) : mat a *ᵥ u - u ∈ commOn A U :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

theorem commOn_le_iff {A : Subgroup (Sp4 F)} {U W : Submodule F (V4 F)} :
    commOn A U ≤ W ↔ ∀ a ∈ A, ∀ u ∈ U, mat a *ᵥ u - u ∈ W := by
  refine ⟨fun h a ha u hu => h (sub_mem_commOn ha hu), fun h => Submodule.span_le.2 ?_⟩
  rintro _ ⟨a, ha, u, hu, rfl⟩
  exact h a ha u hu

theorem commSp_eq_commOn_top (A : Subgroup (Sp4 F)) : commSp A = commOn A ⊤ := by
  refine le_antisymm (commSp_le_iff.2 fun a ha v => sub_mem_commOn ha Submodule.mem_top) ?_
  rw [commOn_le_iff]
  exact fun a ha u _ => sub_mem_commSp ha u

theorem mulVec_mem_commOn {A B : Subgroup (Sp4 F)}
    (hBA : B ≤ Subgroup.normalizer (A : Set (Sp4 F))) {U : Submodule F (V4 F)}
    (hU : ∀ b ∈ B, ∀ u ∈ U, mat b *ᵥ u ∈ U) {b : Sp4 F} (hb : b ∈ B) {w : V4 F}
    (hw : w ∈ commOn A U) : mat b *ᵥ w ∈ commOn A U := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hx
    have hba : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hBA hb) a).1 ha
    have e : mat b *ᵥ (mat a *ᵥ u - u) = mat (b * a * b⁻¹) *ᵥ (mat b *ᵥ u) - mat b *ᵥ u := by
      rw [mulVec_sub, mat_mul_mulVec (b * a), mat_inv_mulVec, mat_mul_mulVec]
    rw [e]
    exact sub_mem_commOn hba (hU b hb u hu)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ c hx

theorem mulVec_mem_commSp {A B : Subgroup (Sp4 F)}
    (hBA : B ≤ Subgroup.normalizer (A : Set (Sp4 F))) {b : Sp4 F} (hb : b ∈ B) {w : V4 F}
    (hw : w ∈ commSp A) : mat b *ᵥ w ∈ commSp A := by
  rw [commSp_eq_commOn_top] at hw ⊢
  exact mulVec_mem_commOn hBA (fun _ _ _ _ => Submodule.mem_top) hb hw

theorem commSp_iSup_le {ι : Type*} (A : ι → Subgroup (Sp4 F))
    (hn : ∀ i j, A i ≤ Subgroup.normalizer (A j : Set (Sp4 F))) :
    commSp (⨆ i, A i) ≤ ⨆ i, commSp (A i) := by
  set W := ⨆ i, commSp (A i) with hW
  have hWinv : ∀ i, ∀ g ∈ A i, ∀ w ∈ W, mat g *ᵥ w ∈ W := by
    intro i g hg w hw
    refine Submodule.iSup_induction _ (motive := fun w => mat g *ᵥ w ∈ W) hw
      (fun j w hw => Submodule.mem_iSup_of_mem j (mulVec_mem_commSp (hn i j) hg hw)) ?_ ?_
    · rw [mulVec_zero]
      exact zero_mem _
    · intro x y hx hy
      rw [mulVec_add]
      exact add_mem hx hy
  let H : Subgroup (Sp4 F) :=
    { carrier := {g | g ∈ stab W ∧ ∀ v, mat g *ᵥ v - v ∈ W}
      one_mem' := ⟨one_mem _, fun v => by rw [mat_one, one_mulVec, sub_self]; exact zero_mem _⟩
      mul_mem' := by
        rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
        refine ⟨mul_mem hg hh, fun v => ?_⟩
        have e : mat (g * h) *ᵥ v - v = mat g *ᵥ (mat h *ᵥ v - v) + (mat g *ᵥ v - v) := by
          rw [mat_mul_mulVec, mulVec_sub]
          abel
        rw [e]
        exact add_mem (mulVec_mem_of_mem_stab hg (hh' v)) (hg' v)
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        refine ⟨inv_mem hg, fun v => ?_⟩
        have e : mat g⁻¹ *ᵥ v - v = -(mat g *ᵥ (mat g⁻¹ *ᵥ v) - mat g⁻¹ *ᵥ v) := by
          rw [mat_mulVec_inv]
          abel
        rw [e]
        exact neg_mem (hg' _) }
  have hAH : ⨆ i, A i ≤ H := iSup_le fun i g hg =>
    ⟨mem_stab_of_le fun w hw => hWinv i g hg w hw,
      fun v => Submodule.mem_iSup_of_mem i (sub_mem_commSp hg v)⟩
  rw [commSp_le_iff]
  exact fun g hg v => (hAH hg).2 v

variable [Finite F] [CharP F 2]

theorem fix_of_finrank_le_one {B : Subgroup (Sp4 F)} (hB : IsPGroup 2 B)
    {U : Submodule F (V4 F)} (hU : ∀ b ∈ B, ∀ u ∈ U, mat b *ᵥ u ∈ U)
    (h1 : Module.finrank F U ≤ 1) {b : Sp4 F} (hb : b ∈ B) {u : V4 F} (hu : u ∈ U) :
    mat b *ᵥ u = u := by
  by_cases hU0 : U = ⊥
  · subst hU0
    rw [Submodule.mem_bot] at hu
    subst hu
    exact mulVec_zero _
  obtain ⟨x, hx, hx0, hxfix⟩ := exists_fixed_ne_zero hB hU0 hU
  have hUx : U = F ∙ x := by
    refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
      ?_).symm
    rw [finrank_span_singleton hx0]
    exact h1
  rw [hUx] at hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
  rw [mulVec_smul, hxfix b hb]

omit [Finite F] [CharP F 2] in
theorem exists_mulVec_pow {g : Sp4 F} {x w : V4 F} (hx : mat g *ᵥ x = x) {c d : F}
    (hw : mat g *ᵥ w = d • x + c • w) (n : ℕ) :
    ∃ s : F, mat (g ^ n) *ᵥ w = s • x + c ^ n • w := by
  induction n with
  | zero => exact ⟨0, by rw [pow_zero, mat_one, one_mulVec, zero_smul, zero_add, pow_zero,
      one_smul]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨d + c * s, ?_⟩
    have hxn : mat (g ^ n) *ᵥ x = x := by
      clear hs
      induction n with
      | zero => rw [pow_zero, mat_one, one_mulVec]
      | succ m ihm => rw [pow_succ, mat_mul_mulVec, hx, ihm]
    rw [pow_succ, mat_mul_mulVec, hw, mulVec_add, mulVec_smul, mulVec_smul, hxn, hs, pow_succ]
    module

theorem finrank_commOn_le_one {B : Subgroup (Sp4 F)} (hB : IsPGroup 2 B)
    {U : Submodule F (V4 F)} (hU : ∀ b ∈ B, ∀ u ∈ U, mat b *ᵥ u ∈ U)
    (h2 : Module.finrank F U ≤ 2) : Module.finrank F (commOn B U) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge (Module.finrank F U) 2 with hlt | hge
  · have hbot : commOn B U = ⊥ := by
      rw [eq_bot_iff, commOn_le_iff]
      intro b hb u hu
      rw [fix_of_finrank_le_one hB hU (by omega) hb hu, sub_self]
      exact zero_mem _
    rw [hbot, finrank_bot]
    omega
  have hU0 : U ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hge
    omega
  obtain ⟨x, hx, hx0, hxfix⟩ := exists_fixed_ne_zero hB hU0 hU
  obtain ⟨w, hwU, hwx⟩ := exists_not_mem_span_of_one_lt (W := U) (by omega) x
  have hspan : Submodule.span F {x, w} = U :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.2 (by
        rintro _ (rfl | rfl)
        · exact hx
        · exact hwU))
      (by rw [finrank_span_pair hx0 hwx]; omega)
  have hli : LinearIndependent F ![x, w] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hx0, rfl⟩
    · exfalso
      apply hwx
      have : w = (-(t⁻¹ * s)) • x := by
        have h1 : t • w = -(s • x) := eq_neg_of_add_eq_zero_right hst
        calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = _ := by rw [h1, smul_neg, smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have key : ∀ b ∈ B, mat b *ᵥ w - w ∈ F ∙ x := by
    intro b hb
    have hbw : mat b *ᵥ w ∈ Submodule.span F {x, w} := hspan ▸ hU b hb w hwU
    obtain ⟨d, c, hdc⟩ := Submodule.mem_span_pair.1 hbw
    obtain ⟨e, he⟩ := hB ⟨b, hb⟩
    have hbe : b ^ 2 ^ e = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    obtain ⟨s, hs⟩ := exists_mulVec_pow (hxfix b hb) hdc.symm (2 ^ e)
    rw [hbe, mat_one, one_mulVec] at hs
    have hc : c ^ 2 ^ e = 1 := by
      have h0 : s • x + (c ^ 2 ^ e - 1) • w = 0 := by
        rw [sub_smul, one_smul]
        calc s • x + (c ^ 2 ^ e • w - w) = (s • x + c ^ 2 ^ e • w) - w := by abel
          _ = 0 := by rw [← hs, sub_self]
      have := (LinearIndependent.pair_iff.1 hli) s (c ^ 2 ^ e - 1) h0
      exact sub_eq_zero.1 this.2
    have hc1 : c = 1 := iterateFrobenius_inj F 2 e (by
      rw [iterateFrobenius_def, iterateFrobenius_def, hc, one_pow])
    rw [← hdc, hc1, one_smul, add_sub_cancel_right]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have hle : commOn B U ≤ F ∙ x := by
    rw [commOn_le_iff]
    intro b hb u hu
    rw [← hspan] at hu
    obtain ⟨d', c', rfl⟩ := Submodule.mem_span_pair.1 hu
    rw [mulVec_add, mulVec_smul, mulVec_smul, hxfix b hb]
    have e : d' • x + c' • (mat b *ᵥ w) - (d' • x + c' • w) = c' • (mat b *ᵥ w - w) := by
      rw [smul_sub]
      abel
    rw [e]
    exact Submodule.smul_mem _ c' (key b hb)
  calc Module.finrank F (commOn B U) ≤ Module.finrank F (F ∙ x) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hx0

omit [Finite F] [CharP F 2] in
theorem finrank_commSp_le_two {A : Subgroup (Sp4 F)} (hq : commSp A ≤ fixSp A) :
    Module.finrank F (commSp A) ≤ 2 := by
  have h1 := finrank_perp (commSp A)
  rw [S5.perp_commSp] at h1
  have h2 := Submodule.finrank_mono hq
  omega

theorem card_iSup_le_of_quadratic {ι : Type*} (A : ι → Subgroup (Sp4 F))
    (h2 : ∀ i, IsPGroup 2 (A i)) (hq : ∀ i, commSp (A i) ≤ fixSp (A i))
    (hn : ∀ i j, A i ≤ Subgroup.normalizer (A j : Set (Sp4 F)))
    (hA2 : IsPGroup 2 ↥(⨆ i, A i)) : Nat.card ↥(⨆ i, A i) ≤ Nat.card F ^ 3 := by
  set A' := ⨆ i, A i with hA'
  by_cases hA1 : A' = ⊥
  · rw [hA1, Subgroup.card_bot]
    exact Nat.one_le_pow _ _ Nat.card_pos
  have hfix0 : fixSp A' ≠ ⊥ := S5.fixSp_ne_bot hA2
  rcases Nat.lt_or_ge (Module.finrank F (fixSp A')) 2 with hlt | hge
  ·
    have hp : IsPoint (fixSp A') := by
      have := S5.finrank_pos_of_ne_bot hfix0
      show Module.finrank F (fixSp A') = 1
      omega
    have hfixW : ∀ i j, commOn (A i) (commSp (A j)) ≤ fixSp A' := by
      intro i j
      rw [← le_fixer_iff]
      refine iSup_le fun k g hg w hw => ?_
      have hinvk : ∀ b ∈ A k, ∀ u ∈ commSp (A j), mat b *ᵥ u ∈ commSp (A j) :=
        fun b hb u hu => mulVec_mem_commSp (hn k j) hb hu
      have hinvi : ∀ b ∈ A i, ∀ u ∈ commSp (A j), mat b *ᵥ u ∈ commSp (A j) :=
        fun b hb u hu => mulVec_mem_commSp (hn i j) hb hu
      exact fix_of_finrank_le_one (h2 k)
        (fun b hb u hu => mulVec_mem_commOn (hn k i) hinvk hb hu)
        (finrank_commOn_le_one (h2 i) hinvi (finrank_commSp_le_two (hq j))) hg hw
    have hperp : perp (fixSp A') = commSp A' := by rw [← S5.perp_commSp, perp_perp]
    have hle : A' ≤ qPoint (fixSp A') := by
      refine iSup_le fun i g hg => ⟨fun v hv => hv g (le_iSup A i hg), fun v hv => ?_⟩
      rw [hperp] at hv
      refine Submodule.iSup_induction _ (motive := fun v => mat g *ᵥ v - v ∈ fixSp A')
        (commSp_iSup_le A hn hv) (fun j w hw => hfixW i j (sub_mem_commOn hg hw)) ?_ ?_
      · rw [mulVec_zero, sub_zero]
        exact zero_mem _
      · intro x y hx hy
        have e : mat g *ᵥ (x + y) - (x + y) = (mat g *ᵥ x - x) + (mat g *ᵥ y - y) := by
          rw [mulVec_add]
          abel
        rw [e]
        exact add_mem hx hy
    calc Nat.card A' ≤ Nat.card (qPoint (fixSp A')) := Subgroup.card_le_of_le hle
      _ = Nat.card F ^ 3 := card_qPoint hp
  · obtain ⟨l, hl, -, hAl⟩ := exists_line_of_two_le_finrank_fixSp hA2 hA1 hge
    calc Nat.card A' ≤ Nat.card (qLine l) := Subgroup.card_le_of_le hAl
      _ = Nat.card F ^ 3 := card_qLine hl

end CFSG.Quasithin.MS93.S52i
