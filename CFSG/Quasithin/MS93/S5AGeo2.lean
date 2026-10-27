module

public import CFSG.Quasithin.MS93.S5AGeo

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

theorem fixer_sup (W W' : Submodule F (V4 F)) : fixer (W ⊔ W') = fixer W ⊓ fixer W' := by
  refine le_antisymm (le_inf (fixer_antitone le_sup_left) (fixer_antitone le_sup_right)) ?_
  intro g hg v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  rw [mulVec_add, mem_fixer.1 hg.1 x hx, mem_fixer.1 hg.2 y hy]

theorem le_perp_of_le {l p : Submodule F (V4 F)} (hl : IsLine l) (hpl : p ≤ l) : l ≤ perp p := by
  rw [← hl.perp_eq]
  exact perp_antitone hpl

theorem finrank_le_two_of_le_perp {W : Submodule F (V4 F)} (h : W ≤ perp W) :
    Module.finrank F W ≤ 2 := by
  have h1 := finrank_perp W
  have h2 := Submodule.finrank_mono h
  omega

theorem isPoint_ne_bot {p : Submodule F (V4 F)} (hp : IsPoint p) : p ≠ ⊥ := by
  intro h
  have := hp
  unfold IsPoint at this
  rw [h, finrank_bot] at this
  omega

theorem finrank_perp_point {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Module.finrank F (perp p) = 3 := by
  have := finrank_perp p
  unfold IsPoint at hp
  omega

theorem sup_eq_perp {l l' p : Submodule F (V4 F)} (hl : IsLine l) (hl' : IsLine l')
    (hp : IsPoint p) (hll' : l ⊓ l' = p) : l ⊔ l' = perp p := by
  have hpl : p ≤ l := hll' ▸ inf_le_left
  have hpl' : p ≤ l' := hll' ▸ inf_le_right
  refine Submodule.eq_of_le_of_finrank_eq (sup_le (le_perp_of_le hl hpl) (le_perp_of_le hl' hpl'))
    ?_
  have h := Submodule.finrank_sup_add_finrank_inf_eq l l'
  rw [hll', hl.1, hl'.1, hp, finrank_perp_point hp] at *
  omega

theorem qLine_inf_qLine {l l' p : Submodule F (V4 F)} (hl : IsLine l) (hl' : IsLine l')
    (hp : IsPoint p) (hll' : l ⊓ l' = p) : qLine l ⊓ qLine l' = xPoint p := by
  rw [qLine, qLine, ← fixer_sup, sup_eq_perp hl hl' hp hll']

theorem le_of_inf_ne_bot {l₁ l₂ l p : Submodule F (V4 F)} (h₁ : IsLine l₁) (h₂ : IsLine l₂)
    (hl : IsLine l) (hp : IsPoint p) (h12 : l₁ ⊓ l₂ = p) (h1 : l ⊓ l₁ ≠ ⊥) (h2 : l ⊓ l₂ ≠ ⊥) :
    p ≤ l := by
  by_contra hpl
  have hl1 : l ≠ l₁ := fun e => hpl (e ▸ h12 ▸ inf_le_left)
  have hl2 : l ≠ l₂ := fun e => hpl (e ▸ h12 ▸ inf_le_right)
  have hp₁ := isPoint_inf hl h₁ hl1 h1
  have hp₂ := isPoint_inf hl h₂ hl2 h2
  set W := p ⊔ (l ⊓ l₁) ⊔ (l ⊓ l₂) with hW
  have hWiso : W ≤ perp W := by
    have hpp : p ≤ perp p := le_perp_of_isPoint hp
    have hl1p : l ⊓ l₁ ≤ perp p := (inf_le_right.trans (le_perp_of_le h₁ (h12 ▸ inf_le_left)))
    have hl2p : l ⊓ l₂ ≤ perp p := (inf_le_right.trans (le_perp_of_le h₂ (h12 ▸ inf_le_right)))
    have hl12 : l ⊓ l₂ ≤ perp (l ⊓ l₁) := (inf_le_left.trans
      (le_perp_of_le hl (inf_le_left : l ⊓ l₁ ≤ l)))
    have hsymm : ∀ A B : Submodule F (V4 F), A ≤ perp B → B ≤ perp A := fun A B h v hv =>
      mem_perp.2 fun w hw => by rw [form_swap, mem_perp.1 (h hw) v hv, neg_zero]
    have key : ∀ A ∈ ({p, l ⊓ l₁, l ⊓ l₂} : Set (Submodule F (V4 F))),
        ∀ B ∈ ({p, l ⊓ l₁, l ⊓ l₂} : Set (Submodule F (V4 F))), A ≤ perp B := by
      intro A hA B hB
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
      rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl
      · exact hpp
      · exact hsymm _ _ hl1p
      · exact hsymm _ _ hl2p
      · exact hl1p
      · exact le_perp_of_le hl inf_le_left |>.trans' inf_le_left
      · exact hsymm _ _ hl12
      · exact hl2p
      · exact hl12
      · exact le_perp_of_le hl inf_le_left |>.trans' inf_le_left
    intro v hv
    rw [mem_perp]
    intro w hw
    obtain ⟨v₁, hv₁, v₃, hv₃, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨v₁, hv₁', v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 hv₁
    obtain ⟨w₁, hw₁, w₃, hw₃, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨w₁, hw₁', w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw₁
    have e : ∀ A ∈ ({p, l ⊓ l₁, l ⊓ l₂} : Set (Submodule F (V4 F))),
        ∀ B ∈ ({p, l ⊓ l₁, l ⊓ l₂} : Set (Submodule F (V4 F))),
        ∀ a ∈ A, ∀ b ∈ B, form F a b = 0 := fun A hA B hB a ha b hb =>
      mem_perp.1 (key B hB A hA hb) a ha
    simp only [map_add, LinearMap.add_apply]
    rw [e _ (by simp) _ (by simp) w₁ hw₁' v₁ hv₁', e _ (by simp) _ (by simp) w₁ hw₁' v₂ hv₂,
      e _ (by simp) _ (by simp) w₁ hw₁' v₃ hv₃, e _ (by simp) _ (by simp) w₂ hw₂ v₁ hv₁',
      e _ (by simp) _ (by simp) w₂ hw₂ v₂ hv₂, e _ (by simp) _ (by simp) w₂ hw₂ v₃ hv₃,
      e _ (by simp) _ (by simp) w₃ hw₃ v₁ hv₁', e _ (by simp) _ (by simp) w₃ hw₃ v₂ hv₂,
      e _ (by simp) _ (by simp) w₃ hw₃ v₃ hv₃]
    simp
  have hdim := finrank_le_two_of_le_perp hWiso
  have hp1 : p ≠ l ⊓ l₁ := fun e => hpl (e ▸ inf_le_left)
  have hl1W : l₁ ≤ W := by
    have hle : p ⊔ (l ⊓ l₁) ≤ l₁ := sup_le (h12 ▸ inf_le_left) inf_le_right
    have hsup := isLine_sup hp hp₁ hp1 ((inf_le_right.trans (le_perp_of_le h₁
      (h12 ▸ inf_le_left))))
    have := IsLine.eq_of_le hsup h₁ hle
    rw [← this]
    exact le_sup_left
  have hl2W : l ⊓ l₂ ≤ W := le_sup_right
  have hnot : ¬ l ⊓ l₂ ≤ l₁ := by
    intro h
    have h' : l ⊓ l₂ ≤ l₁ ⊓ l₂ := le_inf h inf_le_right
    rw [h12] at h'
    have := (Submodule.eq_of_le_of_finrank_eq h' (by rw [hp₂, hp]))
    exact hpl (this ▸ inf_le_left)
  have hlt : l₁ < l₁ ⊔ (l ⊓ l₂) := lt_of_le_of_ne le_sup_left fun e => hnot (e ▸ le_sup_right)
  have h3 : 3 ≤ Module.finrank F ↥(l₁ ⊔ (l ⊓ l₂)) := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [h₁.1] at this
    omega
  have hle : l₁ ⊔ (l ⊓ l₂) ≤ W := sup_le hl1W hl2W
  have := Submodule.finrank_mono hle
  omega

variable [Finite F] [CharP F 2]

theorem exists_fixed_mod {R : Subgroup (Sp4 F)} (hR : IsPGroup 2 R) {W D : Submodule F (V4 F)}
    (hDW : D < W) (hW : ∀ r ∈ R, ∀ w ∈ W, mat r *ᵥ w ∈ W)
    (hD : ∀ r ∈ R, ∀ d ∈ D, mat r *ᵥ d ∈ D) :
    ∃ w ∈ W, w ∉ D ∧ ∀ r ∈ R, mat r *ᵥ w - w ∈ D := by
  set D' : Submodule F W := D.comap W.subtype with hD'
  let f : R → (W →ₗ[F] W) := fun r => (mulVecLin (mat (r : Sp4 F))).restrict (hW r r.2)
  have hf : ∀ r : R, D' ≤ D'.comap (f r) := fun r x hx => hD r r.2 x hx
  let act : R → (W ⧸ D') → (W ⧸ D') := fun r => D'.mapQ D' (f r) (hf r)
  have act_mk : ∀ (r : R) (w : W), act r (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (f r w) := fun r w => Submodule.mapQ_apply _ _ _ _
  let _ : MulAction R (W ⧸ D') :=
    { smul := act
      one_smul := fun x => by
        induction x using Submodule.Quotient.induction_on with
        | H w =>
          change act 1 _ = _
          rw [act_mk]
          congr 1
          apply Subtype.ext
          change mat ((1 : R) : Sp4 F) *ᵥ (w : V4 F) = w
          rw [Subgroup.coe_one, mat_one, one_mulVec]
      mul_smul := fun r s x => by
        induction x using Submodule.Quotient.induction_on with
        | H w =>
          change act (r * s) _ = act r (act s _)
          rw [act_mk, act_mk, act_mk]
          congr 1
          apply Subtype.ext
          exact mat_mul_mulVec (r : Sp4 F) s w }
  have : Finite (W ⧸ D') := Finite.of_surjective _ (Submodule.mkQ_surjective D')
  have hmod := hR.card_modEq_card_fixedPoints (p := 2) (W ⧸ D')
  have hcard := Submodule.card_eq_card_quotient_mul_card D'
  have hD'card : Nat.card D' = Nat.card D := by
    have e : D' ≃ D :=
      { toFun := fun x => ⟨(x : W), x.2⟩
        invFun := fun x => ⟨⟨x, hDW.le x.2⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr e
  have hlt : Module.finrank F D < Module.finrank F W := Submodule.finrank_lt_finrank_of_lt hDW
  have h2 : 2 ∣ Nat.card (W ⧸ D') := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := W),
      Module.natCard_eq_pow_finrank (K := F) (V := D')] at hcard
    have hD'r : Module.finrank F D' = Module.finrank F D := by
      have e : D' ≃ₗ[F] D :=
        { toFun := fun x => ⟨(x : W), x.2⟩
          invFun := fun x => ⟨⟨x, hDW.le x.2⟩, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact e.finrank_eq
    rw [hD'r] at hcard
    have hq : 2 ∣ Nat.card F := MSP.two_dvd_card
    have hpos : 0 < Nat.card F := Nat.card_pos
    have hpow : Nat.card F ^ Module.finrank F W =
        Nat.card F ^ Module.finrank F D * Nat.card F ^ (Module.finrank F W - Module.finrank F D) :=
      by rw [← pow_add]; congr 1; omega
    rw [hpow] at hcard
    have hne : Nat.card F ^ Module.finrank F D ≠ 0 := pow_ne_zero _ hpos.ne'
    have h' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hcard
    rw [← h']
    exact hq.pow (by omega)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints R (W ⧸ D')) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h2))
  have h0 : (0 : W ⧸ D') ∈ MulAction.fixedPoints R (W ⧸ D') := fun r => by
    change act r 0 = 0
    exact map_zero _
  have hex : ∃ x ∈ MulAction.fixedPoints R (W ⧸ D'), x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hc1 : Nat.card (MulAction.fixedPoints R (W ⧸ D')) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨⟨0, h0⟩⟩⟩
    omega
  obtain ⟨x, hx, hx0⟩ := hex
  induction x using Submodule.Quotient.induction_on with
  | H w =>
  refine ⟨w, w.2, fun hwD => hx0 ((Submodule.Quotient.mk_eq_zero D').2 hwD), fun r hr => ?_⟩
  have h := hx ⟨r, hr⟩
  change act ⟨r, hr⟩ _ = _ at h
  rw [act_mk, Submodule.Quotient.eq] at h
  exact h

theorem exists_line_mod {p : Submodule F (V4 F)} (hp : IsPoint p) {R : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hRp : R ≤ fixer p) :
    ∃ l₀ : Submodule F (V4 F), IsLine l₀ ∧ p ≤ l₀ ∧ ∀ r ∈ R, ∀ v ∈ l₀, mat r *ᵥ v - v ∈ p := by
  have hpp : p ≤ perp p := le_perp_of_isPoint hp
  have hlt : p < perp p := lt_of_le_of_ne hpp fun e => by
    have h1 := finrank_perp_point hp
    rw [← e] at h1
    unfold IsPoint at hp
    omega
  obtain ⟨w, hw, hwp, hwfix⟩ := exists_fixed_mod hR hlt
    (fun r hr v hv => mulVec_mem_of_mem_stab (stab_le_stab_perp _ (fixer_le_stab _ (hRp hr))) hv)
    (fun r hr v hv => by rw [mem_fixer.1 (hRp hr) v hv]; exact hv)
  have hw0 : w ≠ 0 := fun h => hwp (h ▸ p.zero_mem)
  have hpw : p ≠ F ∙ w := fun e => hwp (e ▸ Submodule.mem_span_singleton_self w)
  have hwperp : F ∙ w ≤ perp p := (Submodule.span_singleton_le_iff_mem _ _).2 hw
  refine ⟨p ⊔ F ∙ w, isLine_sup hp (isPoint_span hw0) hpw hwperp, le_sup_left, ?_⟩
  intro r hr v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [mulVec_add, mulVec_smul, mem_fixer.1 (hRp hr) x hx]
  have : x + c • (mat r *ᵥ w) - (x + c • w) = c • (mat r *ᵥ w - w) := by
    rw [smul_sub]; abel
  rw [this]
  exact p.smul_mem c (hwfix r hr)

omit [Finite F] [CharP F 2] in
theorem mem_of_sub_mem {l p : Submodule F (V4 F)} (hl : IsLine l) (hp : IsPoint p) (hpl : p ≤ l)
    {A : Subgroup (Sp4 F)} (hA : A ≤ qLine l) (hAp : ¬ A ≤ qPoint p) {v : V4 F}
    (hv : v ∈ perp p) (hvA : ∀ a ∈ A, mat a *ᵥ v - v ∈ p) : v ∈ l := by
  by_contra hvl
  apply hAp
  have hlp : l ≤ perp p := le_perp_of_le hl hpl
  have hsup : l ⊔ F ∙ v = perp p := by
    refine Submodule.eq_of_le_of_finrank_eq
      (sup_le hlp ((Submodule.span_singleton_le_iff_mem _ _).2 hv)) ?_
    have hlt : l < l ⊔ F ∙ v := lt_of_le_of_ne le_sup_left fun e =>
      hvl (e ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_mono (sup_le hlp ((Submodule.span_singleton_le_iff_mem _ _).2 hv))
    rw [hl.1] at h1
    rw [finrank_perp_point hp] at h2 ⊢
    omega
  intro a ha
  refine ⟨fun x hx => mem_fixer.1 (hA ha) x (hpl hx), fun u hu => ?_⟩
  rw [← hsup] at hu
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [mulVec_add, mulVec_smul, mem_fixer.1 (hA ha) y hy]
  have : y + c • (mat a *ᵥ v) - (y + c • v) = c • (mat a *ᵥ v - v) := by
    rw [smul_sub]; abel
  rw [this]
  exact p.smul_mem c (hvA a ha)

omit [Finite F] in
theorem sub_mem_of_pow {p : Submodule F (V4 F)} {g : Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    (hgp : ∀ x ∈ p, mat g *ᵥ x = x) {w : V4 F} (hwp : w ∉ p) (hgw : mat g *ᵥ w ∈ p ⊔ F ∙ w) :
    mat g *ᵥ w - w ∈ p := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hgw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hpow : ∀ m : ℕ, mat (g ^ m) *ᵥ w - c ^ m • w ∈ p := by
    intro m
    induction m with
    | zero => simp [mat_one]
    | succ m ih =>
      have e : mat (g ^ (m + 1)) *ᵥ w = mat g *ᵥ (mat (g ^ m) *ᵥ w) := by
        rw [pow_succ', mat_mul_mulVec]
      rw [e]
      have h1 : mat (g ^ m) *ᵥ w = (mat (g ^ m) *ᵥ w - c ^ m • w) + c ^ m • w := by abel
      rw [h1, mulVec_add, mulVec_smul, hgp _ ih, ← hxy]
      have : mat (g ^ m) *ᵥ w - c ^ m • w + c ^ m • (x + c • w) - c ^ (m + 1) • w =
          (mat (g ^ m) *ᵥ w - c ^ m • w) + c ^ m • x := by
        rw [smul_add, smul_smul, ← pow_succ]; abel
      rw [this]
      exact p.add_mem ih (p.smul_mem _ hx)
  have h2 := hpow (2 ^ n)
  rw [hg, mat_one, one_mulVec] at h2
  have hc : c ^ 2 ^ n = 1 := by
    by_contra hne
    apply hwp
    have : w - c ^ 2 ^ n • w = (1 - c ^ 2 ^ n) • w := by rw [sub_smul, one_smul]
    rw [this] at h2
    have hu : (1 - c ^ 2 ^ n) ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have := p.smul_mem (1 - c ^ 2 ^ n)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this
  have hc1 : c = 1 := by
    have h' : (c - 1) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, hc, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n two_ne_zero) |>.1 h')
  rw [← hxy, hc1, one_smul, add_sub_cancel_right]
  exact hx

omit [Finite F] in
theorem le_qPoint_of_stab {p l l' : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l)
    (hl' : IsLine l') (hll' : l ≠ l') (hpl : p ≤ l) (hpl' : p ≤ l') {R : Subgroup (Sp4 F)}
    (hR : IsPGroup 2 R) (hRp : R ≤ fixer p) (hRl : R ≤ stab l) (hRl' : R ≤ stab l') :
    R ≤ qPoint p := by
  have hinf : l ⊓ l' = p := by
    have h0 : l ⊓ l' ≠ ⊥ := fun h => isPoint_ne_bot hp (le_bot_iff.1 (h ▸ le_inf hpl hpl'))
    have hpt := isPoint_inf hl hl' hll' h0
    exact (Submodule.eq_of_le_of_finrank_eq (le_inf hpl hpl') (by rw [hp, hpt])).symm
  have key : ∀ {m : Submodule F (V4 F)}, IsLine m → p ≤ m → R ≤ stab m →
      ∀ r ∈ R, ∀ v ∈ m, mat r *ᵥ v - v ∈ p := by
    intro m hm hpm hRm r hr v hv
    obtain ⟨w, hwm, hwp⟩ : ∃ w ∈ m, w ∉ p := by
      by_contra h
      push Not at h
      have := Submodule.finrank_mono (show m ≤ p from h)
      rw [hm.1, hp] at this
      omega
    have hmeq : p ⊔ F ∙ w = m := by
      have hw0 : w ≠ 0 := fun h => hwp (h ▸ p.zero_mem)
      have hpw : p ≠ F ∙ w := fun e => hwp (e ▸ Submodule.mem_span_singleton_self w)
      have hwperp : F ∙ w ≤ perp p :=
        ((Submodule.span_singleton_le_iff_mem _ _).2 hwm).trans (le_perp_of_le hm hpm)
      exact IsLine.eq_of_le (isLine_sup hp (isPoint_span hw0) hpw hwperp) hm
        (sup_le hpm ((Submodule.span_singleton_le_iff_mem _ _).2 hwm))
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    have hrn : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hrw : mat r *ᵥ w - w ∈ p := sub_mem_of_pow hrn (fun x hx => mem_fixer.1 (hRp hr) x hx)
      hwp (by rw [hmeq]; exact mulVec_mem_of_mem_stab (hRm hr) hwm)
    rw [← hmeq] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mulVec_add, mulVec_smul, mem_fixer.1 (hRp hr) x hx]
    have : x + c • (mat r *ᵥ w) - (x + c • w) = c • (mat r *ᵥ w - w) := by
      rw [smul_sub]; abel
    rw [this]
    exact p.smul_mem c hrw
  intro r hr
  refine ⟨fun x hx => mem_fixer.1 (hRp hr) x hx, fun u hu => ?_⟩
  rw [← sup_eq_perp hl hl' hp hinf] at hu
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  have : mat r *ᵥ (y + z) - (y + z) = (mat r *ᵥ y - y) + (mat r *ᵥ z - z) := by
    rw [mulVec_add]; abel
  rw [this]
  exact p.add_mem (key hl hpl hRl r hr y hy) (key hl' hpl' hRl' r hr z hz)

omit [Finite F] [CharP F 2] in
theorem exists_map_flag {p l : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l)
    (hpl : p ≤ l) : ∃ g : Sp4 F, (pt₀ F).map (mulVecLin (mat g)) = p ∧
      (ln₀ F).map (mulVecLin (mat g)) = l := by
  set Fl : ℕ → Submodule F (V4 F) := fun i => if i = 0 then ⊥ else if i = 1 then p else l
    with hFl
  have hflag : IsCompleteIsotropicFlag (pairedSympForm F 2) 2 Fl := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · interval_cases i
      · simp [hFl]
      · show Module.finrank F ↥p = 1
        exact hp
      · show Module.finrank F ↥l = 2
        exact hl.1
    · interval_cases i
      · simp [hFl]
      · simpa [hFl] using hpl
    · interval_cases i
      · intro x hx y hy
        simp only [hFl, ite_true, Submodule.mem_bot] at hx
        rw [hx, map_zero, LinearMap.zero_apply]
      · intro x hx y hy
        simp only [hFl, one_ne_zero, ite_false, ite_true] at hx hy
        obtain ⟨z, hz0, rfl⟩ := exists_eq_span_of_isPoint hp
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
        simp [form_self]
      · intro x hx y hy
        simp only [hFl, two_ne_zero, ite_false, OfNat.ofNat_ne_one] at hx hy
        exact hl.2 x hx y hy
  obtain ⟨g, hg⟩ := SymplecticHigher.exists_map_flag_eq hflag
  refine ⟨g, ?_, ?_⟩
  · have := hg 1 le_rfl (by norm_num)
    simpa [hFl] using this
  · have := hg 2 (by norm_num) le_rfl
    simpa [hFl] using this

omit [CharP F 2] in
theorem card_qLine_inf_qPoint {p l : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l)
    (hpl : p ≤ l) : Nat.card ↥(qLine l ⊓ qPoint p) = Nat.card F ^ 2 := by
  obtain ⟨g, rfl, rfl⟩ := exists_map_flag hp hl hpl
  rw [qLine_map_eq, qPoint_map_eq, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.card_map_of_injective (MulAut.conj g).injective, card_Q₁_inf_Q₂]

omit [CharP F 2] in
theorem qLine_inf_qPoint_sup {p l l' : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l)
    (hl' : IsLine l') (hll' : l ≠ l') (hpl : p ≤ l) (hpl' : p ≤ l') :
    (qLine l ⊓ qPoint p) ⊔ (qLine l' ⊓ qPoint p) = qPoint p := by
  have hinf : l ⊓ l' = p := by
    have h0 : l ⊓ l' ≠ ⊥ := fun h => isPoint_ne_bot hp (le_bot_iff.1 (h ▸ le_inf hpl hpl'))
    have hpt := isPoint_inf hl hl' hll' h0
    exact (Submodule.eq_of_le_of_finrank_eq (le_inf hpl hpl') (by rw [hp, hpt])).symm
  set A := qLine l ⊓ qPoint p
  set A' := qLine l' ⊓ qPoint p
  have hAA' : A ⊓ A' = xPoint p := by
    have : A ⊓ A' = (qLine l ⊓ qLine l') ⊓ qPoint p := by
      ext x; simp only [A, A', Subgroup.mem_inf]; tauto
    rw [this, qLine_inf_qLine hl hl' hp hinf, inf_eq_left.2 (xPoint_le_qPoint hp)]
  have hle : A ⊔ A' ≤ qPoint p := sup_le inf_le_right inf_le_right
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_qPoint hp]
  have hA := card_qLine_inf_qPoint hp hl hpl
  have hA' := card_qLine_inf_qPoint hp hl' hpl'
  have h1 : A'.relIndex A ≤ A'.relIndex (A ⊔ A') :=
    Subgroup.relIndex_le_of_le_right le_sup_left (by
      rw [Subgroup.relIndex]; exact (Subgroup.index_ne_zero_of_finite))
  have h2 : A'.relIndex A * Nat.card ↥(A' ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card A' A
  rw [inf_comm, hAA', card_xPoint hp, hA] at h2
  have h3 : A'.relIndex (A ⊔ A') * Nat.card ↥(A' ⊓ (A ⊔ A')) = Nat.card ↥(A ⊔ A') :=
    Subgroup.relIndex_mul_card A' (A ⊔ A')
  rw [inf_eq_left.2 le_sup_right, hA'] at h3
  have hq : 0 < Nat.card F := Nat.card_pos
  have h4 : A'.relIndex A = Nat.card F := by
    have : A'.relIndex A * Nat.card F = Nat.card F * Nat.card F := by rw [h2, sq]
    exact Nat.eq_of_mul_eq_mul_right hq this
  rw [← h3]
  calc Nat.card F ^ 3 = Nat.card F * Nat.card F ^ 2 := by ring
    _ ≤ A'.relIndex (A ⊔ A') * Nat.card F ^ 2 := Nat.mul_le_mul_right _ (h4 ▸ h1)

omit [Finite F] [CharP F 2] in
theorem eq_sup_span_of_not_mem {p l : Submodule F (V4 F)} (hp : IsPoint p) (hl : IsLine l)
    (hpl : p ≤ l) {w : V4 F} (hwl : w ∈ l) (hwp : w ∉ p) : p ⊔ F ∙ w = l := by
  have hw0 : w ≠ 0 := fun h => hwp (h ▸ p.zero_mem)
  have hpw : p ≠ F ∙ w := fun e => hwp (e ▸ Submodule.mem_span_singleton_self w)
  have hwperp : F ∙ w ≤ perp p :=
    ((Submodule.span_singleton_le_iff_mem _ _).2 hwl).trans (le_perp_of_le hl hpl)
  exact IsLine.eq_of_le (isLine_sup hp (isPoint_span hw0) hpw hwperp) hl
    (sup_le hpl ((Submodule.span_singleton_le_iff_mem _ _).2 hwl))

omit [CharP F 2] in
theorem card_lines_through {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Nat.card {l : Submodule F (V4 F) // IsLine l ∧ p ≤ l} = Nat.card F + 1 := by
  set P := perp p with hP
  set p' : Submodule F P := p.comap P.subtype with hp'
  have hpP : p ≤ P := le_perp_of_isPoint hp
  have hp'r : Module.finrank F p' = 1 := by
    have e : p' ≃ₗ[F] p :=
      { toFun := fun x => ⟨(x : P), x.2⟩
        invFun := fun x => ⟨⟨x, hpP x.2⟩, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [e.finrank_eq]
    exact hp
  have hQ : Module.finrank F (P ⧸ p') = 2 := by
    have h1 := Submodule.finrank_quotient_add_finrank p'
    rw [hp'r, finrank_perp_point hp] at h1
    omega
  have hmk : ∀ x : P, Submodule.Quotient.mk (p := p') x = 0 ↔ (x : V4 F) ∈ p := fun x =>
    (Submodule.Quotient.mk_eq_zero p')
  have hfin_l : ∀ {l : Submodule F (V4 F)}, IsLine l → p ≤ l →
      Module.finrank F ↥((l.comap P.subtype).map p'.mkQ) = 1 := by
    intro l hl hpl
    have hlP : l ≤ P := le_perp_of_le hl hpl
    obtain ⟨w, hwl, hwp⟩ : ∃ w ∈ l, w ∉ p := by
      by_contra h
      push Not at h
      have := Submodule.finrank_mono (show l ≤ p from h)
      rw [hl.1, hp] at this
      omega
    have hsup := eq_sup_span_of_not_mem hp hl hpl hwl hwp
    set w' : P := ⟨w, hlP hwl⟩
    have heq : (l.comap P.subtype).map p'.mkQ = F ∙ (Submodule.Quotient.mk (p := p') w') := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        have hx' : (x : V4 F) ∈ p ⊔ F ∙ w := hsup ▸ hx
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx'
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
        rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((c • w' - x : P) : V4 F) ∈ p
        have : ((c • w' - x : P) : V4 F) = -y := by
          simp only [Submodule.coe_sub, Submodule.coe_smul, w']
          rw [← hyz]; abel
        rw [this]
        exact p.neg_mem hy
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨w', hwl, rfl⟩
    rw [heq, finrank_span_singleton]
    intro h0
    exact hwp ((hmk w').1 h0)
  have hline_H : ∀ H : Submodule F (P ⧸ p'), Module.finrank F H = 1 →
      IsLine ((H.comap p'.mkQ).map P.subtype) ∧ p ≤ (H.comap p'.mkQ).map P.subtype := by
    intro H hH
    obtain ⟨⟨h₀, hh₀⟩, hh₀0, hspan⟩ := finrank_eq_one_iff'.mp hH
    obtain ⟨w', rfl⟩ := Submodule.mkQ_surjective p' h₀
    have hw'p : (w' : V4 F) ∉ p := fun h => hh₀0 (Subtype.ext ((hmk w').2 h))
    have hH' : H = F ∙ (Submodule.Quotient.mk (p := p') w') := by
      apply le_antisymm
      · intro x hx
        obtain ⟨c, hc⟩ := hspan ⟨x, hx⟩
        rw [Submodule.mem_span_singleton]
        exact ⟨c, congrArg Subtype.val hc⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        exact hh₀
    set w : V4 F := (w' : V4 F)
    have hw0 : w ≠ 0 := fun h => hw'p (h ▸ p.zero_mem)
    have hpw : p ≠ F ∙ w := fun e => hw'p (e ▸ Submodule.mem_span_singleton_self w)
    have hwperp : F ∙ w ≤ perp p := (Submodule.span_singleton_le_iff_mem _ _).2 w'.2
    have hC : (H.comap p'.mkQ).map P.subtype = p ⊔ F ∙ w := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        have hx' : p'.mkQ x ∈ H := hx
        rw [hH', Submodule.mem_span_singleton] at hx'
        obtain ⟨c, hc⟩ := hx'
        rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at hc
        have hcx : ((c • w' - x : P) : V4 F) ∈ p := hc
        have e : (x : V4 F) = -((c • w' - x : P) : V4 F) + c • w := by
          simp only [Submodule.coe_sub, Submodule.coe_smul, w]; abel
        show (x : V4 F) ∈ p ⊔ F ∙ w
        rw [e]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (p.neg_mem hcx))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)))
      · refine sup_le (fun x hx => ⟨⟨x, hpP hx⟩, ?_, rfl⟩) ?_
        · show Submodule.Quotient.mk (p := p') ⟨x, hpP hx⟩ ∈ H
          rw [(hmk _).2 hx]
          exact H.zero_mem
        · rw [Submodule.span_singleton_le_iff_mem]
          refine ⟨w', ?_, rfl⟩
          show Submodule.Quotient.mk (p := p') w' ∈ H
          exact hh₀
    rw [hC]
    exact ⟨isLine_sup hp (isPoint_span hw0) hpw hwperp, le_sup_left⟩
  let e : {l : Submodule F (V4 F) // IsLine l ∧ p ≤ l} ≃
      {H : Submodule F (P ⧸ p') // Module.finrank F H = 1} :=
    { toFun := fun l => ⟨(l.1.comap P.subtype).map p'.mkQ, hfin_l l.2.1 l.2.2⟩
      invFun := fun H => ⟨(H.1.comap p'.mkQ).map P.subtype, hline_H H.1 H.2⟩
      left_inv := fun l => by
        apply Subtype.ext
        change ((((l.1.comap P.subtype).map p'.mkQ).comap p'.mkQ).map P.subtype) = l.1
        rw [Submodule.comap_map_mkQ, sup_eq_right.2 (fun x hx => l.2.2 hx),
          Submodule.map_comap_subtype, inf_eq_right.2 (le_perp_of_le l.2.1 l.2.2)]
      right_inv := fun H => by
        apply Subtype.ext
        change (((H.1.comap p'.mkQ).map P.subtype).comap P.subtype).map p'.mkQ = H.1
        rw [Submodule.comap_map_eq_of_injective P.injective_subtype,
          Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective p')] }
  rw [Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule F (P ⧸ p')),
    Projectivization.card_of_finrank_two F (P ⧸ p') hQ]

end CFSG.Quasithin.MS93.S5
