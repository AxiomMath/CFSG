module

public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic
public import CFSG.Quasithin.Background.JonesParshallG2Torus

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model Matrix

variable {F : Type} [Field F]

@[expose] def ht : Ix3 → ℕ
  | .inl i => ![0, 3, 4] i
  | .inr i => ![5, 2, 1] i

@[expose] def InF (h : ℕ) (w : Ix3 → F) : Prop := ∀ k, h ≤ ht k → w k = 0

theorem ht_lt_six (k : Ix3) : ht k < 6 := by
  rcases k with k | k <;> fin_cases k <;> decide

theorem inF_six (w : Ix3 → F) : InF 6 w := fun k hk => absurd (ht_lt_six k) (by omega)

theorem eq_zero_of_inF_zero {w : Ix3 → F} (hw : InF 0 w) : w = 0 :=
  funext fun k => hw k (Nat.zero_le _)

theorem InF.mono {h h' : ℕ} (hh : h ≤ h') {w : Ix3 → F} (hw : InF h w) : InF h' w :=
  fun k hk => hw k (hh.trans hk)

theorem InF.add {h : ℕ} {w w' : Ix3 → F} (hw : InF h w) (hw' : InF h w') : InF h (w + w') :=
  fun k hk => by rw [Pi.add_apply, hw k hk, hw' k hk, add_zero]

theorem InF.sub {h : ℕ} {w w' : Ix3 → F} (hw : InF h w) (hw' : InF h w') : InF h (w - w') :=
  fun k hk => by rw [Pi.sub_apply, hw k hk, hw' k hk, sub_zero]

theorem InF.eq_zero {h : ℕ} {w : Ix3 → F} (hw : InF (h + 1) w) {k k' : Ix3} (hkk : ht k < ht k')
    (hk : h ≤ ht k) : w k' = 0 :=
  hw k' (by omega)

variable [CharP F 2]

theorem cayley_eq_one {g : ↥(cayleyGroup F)} (hg : ∀ w, g2Act g w = w) : g = 1 := by
  have hι : ∀ w, cgE g (zI w) = zI w := by
    intro w
    have h1 := g2_zI_eq g w
    rw [hg] at h1
    have hN := cg_norm g (zI w)
    rw [h1] at hN
    have hc : (cgE g (zI w)).1 = 0 := by
      set c := (cgE g (zI w)).1
      rw [q6_eta w, zI_q6, cayleyOne_eq, zmk_smul, zmk_add, cayleyNorm_zmk,
        cayleyNorm_zmk] at hN
      have hcc : c * c = 0 := by linear_combination hN
      exact mul_self_eq_zero.mp hcc
    rw [h1, hc, zero_smul, add_zero]
  have hE : cgE g (zmk 1 0 0 0 0 0 0 0) = zmk 1 0 0 0 0 0 0 0 := by
    have e : (zmk 1 0 0 0 0 0 0 0 : quasithinZorn F) =
        cayleyMul (zI (q6 1 0 0 0 0 0)) (zI (q6 0 0 0 1 0 0)) := by
      rw [zI_q6, zI_q6, cayleyMul_zmk]
      apply zmk_congr <;> ring
    rw [e, cg_mul, hι, hι]
  apply Subtype.ext
  refine LinearEquiv.ext fun x => ?_
  have hx : x = zI (zP x) + x.2.2.2 • cayleyOne F + (x.1 - x.2.2.2) • zmk 1 0 0 0 0 0 0 0 := by
    conv_lhs => rw [zorn_eta x]
    rw [show zP x = q6 (x.2.1 0) (x.2.1 1) (x.2.1 2) (x.2.2.1 0) (x.2.2.1 1) (x.2.2.1 2) from rfl,
      zI_q6, cayleyOne_eq, zmk_smul, zmk_smul, zmk_add, zmk_add]
    apply zmk_congr <;> ring
  change cgE g x = x
  rw [hx, map_add, map_add, map_smul, map_smul, hι, cg_one, hE]

@[expose] def FlagUni (g : ↥(cayleyGroup F)) : Prop :=
  ∀ h (w : Ix3 → F), InF (h + 1) w → InF h (g2Act g w - w)

theorem FlagUni.mem {g : ↥(cayleyGroup F)} (hg : FlagUni g) {h : ℕ} {w : Ix3 → F}
    (hw : InF h w) : InF h (g2Act g w) := by
  cases h with
  | zero =>
    rw [eq_zero_of_inF_zero hw, map_zero]
    exact fun _ _ => rfl
  | succ h =>
    have := (hg h w hw).mono (Nat.le_succ h)
    have e : g2Act g w = (g2Act g w - w) + w := by abel
    rw [e]
    exact this.add hw

theorem flagUni_one : FlagUni (1 : ↥(cayleyGroup F)) := by
  intro h w _ k _
  rw [map_one, AddMonoid.End.coe_one, id_eq, sub_self, Pi.zero_apply]

theorem flagUni_mul {g g' : ↥(cayleyGroup F)} (hg : FlagUni g) (hg' : FlagUni g') :
    FlagUni (g * g') := by
  intro h w hw
  have e1 : g2Act (g * g') w = g2Act g (g2Act g' w) := by rw [map_mul]; rfl
  have e : g2Act (g * g') w - w = (g2Act g (g2Act g' w) - g2Act g' w) + (g2Act g' w - w) := by
    rw [e1]
    abel
  rw [e]
  exact (hg h _ (hg'.mem hw)).add (hg' h w hw)

theorem flagUni_pow {g : ↥(cayleyGroup F)} (hg : FlagUni g) (m : ℕ) : FlagUni (g ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact flagUni_one
  | succ m ih => rw [pow_succ]; exact flagUni_mul ih hg

@[expose] def LevelUni (d : ℕ) (A : (Ix3 → F) →+ (Ix3 → F)) : Prop :=
  ∀ h (w : Ix3 → F), InF (h + d) w → InF h (A w - w)

theorem two_smul_eq_zero (x : Ix3 → F) : x + x = 0 := by
  funext k
  rw [Pi.add_apply, Pi.zero_apply, CharTwo.add_self_eq_zero]

theorem LevelUni.sq {d : ℕ} {A : (Ix3 → F) →+ (Ix3 → F)} (hA : LevelUni d A) :
    LevelUni (2 * d) (A.comp A) := by
  intro h w hw
  have e : A.comp A w - w = A (A w - w) - (A w - w) := by
    rw [AddMonoidHom.comp_apply, map_sub]
    have := two_smul_eq_zero (A w - w)
    calc A (A w) - w = A (A w) - A w - (A w - w) + ((A w - w) + (A w - w)) := by abel
      _ = A (A w) - A w - (A w - w) := by rw [this, add_zero]
  rw [e]
  have h1 : InF (h + d) (A w - w) := hA (h + d) w (by rwa [add_assoc, ← two_mul])
  exact hA h _ h1

theorem flagUni_pow_eight {g : ↥(cayleyGroup F)} (hg : FlagUni g) : g ^ 8 = 1 := by
  set A : (Ix3 → F) →+ (Ix3 → F) := g2Act g
  have h1 : LevelUni 1 A := hg
  have h8 : LevelUni 8 ((A.comp A).comp (A.comp A) |>.comp ((A.comp A).comp (A.comp A))) :=
    h1.sq.sq.sq
  apply cayley_eq_one
  intro w
  have e : g2Act (g ^ 8) w = ((A.comp A).comp (A.comp A) |>.comp ((A.comp A).comp (A.comp A))) w :=
    by rw [map_pow]; rfl
  rw [e]
  have h := h8 0 w ((inF_six w).mono (by norm_num))
  exact sub_eq_zero.mp (eq_zero_of_inF_zero h)

@[expose] def U0 (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) where
  carrier := {g | FlagUni g}
  one_mem' := flagUni_one
  mul_mem' := flagUni_mul
  inv_mem' := fun {g} hg => by
    have h8 := flagUni_pow_eight hg
    have e : g⁻¹ = g ^ 7 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact h8
    show FlagUni g⁻¹
    rw [e]
    exact flagUni_pow hg 7

theorem mem_U0 {g : ↥(cayleyGroup F)} : g ∈ U0 F ↔ FlagUni g := Iff.rfl

theorem isPGroup_U0 : IsPGroup 2 ↥(U0 F) := fun g =>
  ⟨3, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact flagUni_pow_eight g.2)⟩

theorem g2Act_g2X_e0 (α : F) (w : Ix3 → F) :
    g2Act (g2X ![α, 0, 0]) w =
      q6 (w (.inl 0) + α * α * w (.inr 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0))
        (w (.inr 1) + α * w (.inl 2)) (w (.inr 2) + α * w (.inl 1)) := by
  rw [g2Act_apply]
  change zP (xaFun _ (zI w)) = _
  rw [q6_eta w, zI_q6, xaFun_zmk, zP_zmk]
  simp only [q6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Sum.elim_inl, Sum.elim_inr, Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp [CharTwo.sub_eq_add]; try ring)

theorem g2Act_g2Y_e12 (β γ : F) (w : Ix3 → F) :
    g2Act (g2Y ![0, β, γ]) w =
      q6 (w (.inl 0) + β * w (.inr 2) + γ * w (.inr 1)) (w (.inl 1) + γ * w (.inr 0))
        (w (.inl 2) + β * w (.inr 0)) (w (.inr 0))
        (w (.inr 1) + β * (β * w (.inl 1) + γ * w (.inl 2)))
        (w (.inr 2) + γ * (β * w (.inl 1) + γ * w (.inl 2))) := by
  rw [g2Act_apply]
  change zP (ybFun _ (zI w)) = _
  rw [q6_eta w, zI_q6, ybFun_zmk, zP_zmk]
  simp only [q6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Sum.elim_inl, Sum.elim_inr, Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> simp [CharTwo.sub_eq_add] <;> ring

omit [CharP F 2] in
theorem adjugate_uSL (a b c : F) :
    adjugate ((uSL a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, -a, a * c - b; 0, 1, -c; 0, 0, 1] := by
  change (((uSL a b c)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [uSL_inv]
  rfl

theorem g2Act_g2A_uSL (a b c : F) (w : Ix3 → F) :
    g2Act (g2A (uSL a b c)) w =
      q6 (w (.inl 0) + a * w (.inl 1) + b * w (.inl 2)) (w (.inl 1) + c * w (.inl 2)) (w (.inl 2))
        (w (.inr 0)) (w (.inr 1) + a * w (.inr 0))
        (w (.inr 2) + (a * c + b) * w (.inr 0) + c * w (.inr 1)) := by
  conv_lhs => rw [q6_eta w]
  have hA : ((uSL a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, b; 0, 1, c; 0, 0, 1] := rfl
  rw [g2Act_g2A, adjugate_uSL, hA]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6, CharTwo.neg_eq, CharTwo.sub_eq_add] <;> ring

theorem g2X_mem_U0 (α : F) : g2X ![α, 0, 0] ∈ U0 F := by
  intro h w hw k hk
  rw [g2Act_g2X_e0]
  rcases k with k | k <;> fin_cases k <;>
    simp only [q6, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [hw.eq_zero (k := .inl 0) (k' := .inr 0) (by decide) hk]; ring
  · ring
  · ring
  · ring
  · rw [hw.eq_zero (k := .inr 1) (k' := .inl 2) (by decide) hk]; ring
  · rw [hw.eq_zero (k := .inr 2) (k' := .inl 1) (by decide) hk]; ring

theorem g2Y_mem_U0 (β γ : F) : g2Y ![0, β, γ] ∈ U0 F := by
  intro h w hw k hk
  rw [g2Act_g2Y_e12]
  rcases k with k | k <;> fin_cases k <;>
    simp only [q6, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [hw.eq_zero (k := .inl 0) (k' := .inr 2) (by decide) hk,
      hw.eq_zero (k := .inl 0) (k' := .inr 1) (by decide) hk]; ring
  · rw [hw.eq_zero (k := .inl 1) (k' := .inr 0) (by decide) hk]; ring
  · rw [hw.eq_zero (k := .inl 2) (k' := .inr 0) (by decide) hk]; ring
  · ring
  · rw [hw.eq_zero (k := .inr 1) (k' := .inl 1) (by decide) hk,
      hw.eq_zero (k := .inr 1) (k' := .inl 2) (by decide) hk]; ring
  · rw [hw.eq_zero (k := .inr 2) (k' := .inl 1) (by decide) hk,
      hw.eq_zero (k := .inr 2) (k' := .inl 2) (by decide) hk]; ring

theorem g2A_mem_U0 (a b c : F) : g2A (uSL a b c) ∈ U0 F := by
  intro h w hw k hk
  rw [g2Act_g2A_uSL]
  rcases k with k | k <;> fin_cases k <;>
    simp only [q6, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [hw.eq_zero (k := .inl 0) (k' := .inl 1) (by decide) hk,
      hw.eq_zero (k := .inl 0) (k' := .inl 2) (by decide) hk]; ring
  · rw [hw.eq_zero (k := .inl 1) (k' := .inl 2) (by decide) hk]; ring
  · ring
  · ring
  · rw [hw.eq_zero (k := .inr 1) (k' := .inr 0) (by decide) hk]; ring
  · rw [hw.eq_zero (k := .inr 2) (k' := .inr 0) (by decide) hk,
      hw.eq_zero (k := .inr 2) (k' := .inr 1) (by decide) hk]; ring

omit [CharP F 2] in
theorem uSL_mem_S0 (a b c : F) : uSL a b c ∈ S0 F := by
  rw [mem_S0, show ((uSL a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, a, b; 0, 1, c; 0, 0, 1] from rfl]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem stabElt_mem_U0 (α β γ a b c : F) :
    stabElt (α, β, γ, ⟨uSL a b c, uSL_mem_S0 a b c⟩) ∈ U0 F :=
  (U0 F).mul_mem ((U0 F).mul_mem (g2X_mem_U0 α) (g2Y_mem_U0 β γ)) (g2A_mem_U0 a b c)

variable [Finite F]

theorem finite_cayleyGroup : Finite ↥(cayleyGroup F) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_cayleyGroup]
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have h6 : 1 < Nat.card F ^ 6 := Nat.one_lt_pow (by norm_num) h1
  have h2 : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) h1
  exact Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero (by omega) (by omega))

theorem le_card_U0 : Nat.card F ^ 6 ≤ Nat.card ↥(U0 F) := by
  have := finite_cayleyGroup (F := F)
  let φ : (F × F × F) × ↥(Usl F) → ↥(U0 F) := fun p =>
    ⟨stabElt (p.1.1, p.1.2.1, p.1.2.2,
      ⟨(p.2 : SL3 F), by obtain ⟨a, b, c, h⟩ := p.2.2; rw [h]; exact uSL_mem_S0 a b c⟩),
      by obtain ⟨a, b, c, h⟩ := p.2.2
         have e : (⟨(p.2 : SL3 F), by rw [h]; exact uSL_mem_S0 a b c⟩ : ↥(S0 F)) =
             ⟨uSL a b c, uSL_mem_S0 a b c⟩ := Subtype.ext h
         rw [e]
         exact stabElt_mem_U0 _ _ _ a b c⟩
  have hφ : Function.Injective φ := by
    intro p p' hp
    have h := stabElt_injective (congrArg Subtype.val hp)
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact Prod.ext (Prod.ext h1 (Prod.ext h2 h3)) (Subtype.ext h4)
  have hc := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_Usl] at hc
  calc Nat.card F ^ 6 = Nat.card F * (Nat.card F * Nat.card F) * Nat.card F ^ 3 := by ring
    _ ≤ _ := hc

theorem card_U0 {n : ℕ} (hF : Nat.card F = 2 ^ n) : Nat.card ↥(U0 F) = Nat.card F ^ 6 := by
  have := finite_cayleyGroup (F := F)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_U0 (F := F))
  have hdvd := Subgroup.card_subgroup_dvd_card (U0 F)
  rw [card_cayleyGroup, hm] at hdvd
  set N := (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) with hN
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have he : Even (Nat.card F) := by
    rw [hF]
    cases n with
    | zero => rw [hF, pow_zero] at hq; exact absurd hq (lt_irrefl 1)
    | succ n => exact Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero n⟩
  have hodd : Odd N := by
    refine Nat.odd_mul.mpr ⟨?_, ?_⟩
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (Nat.even_pow.mpr ⟨he, by norm_num⟩)
        odd_one
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (Nat.even_pow.mpr ⟨he, by norm_num⟩)
        odd_one
  have hle : Nat.card ↥(U0 F) ≤ Nat.card F ^ 6 := by
    rw [hm]
    have h2 : 2 ^ m ∣ Nat.card F ^ 6 :=
      (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_right hdvd
    exact Nat.le_of_dvd (by positivity) h2
  exact le_antisymm hle le_card_U0

end CFSG.Quasithin.Vol2.Ch11.G2Q8
