module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRoot
public import CFSG.LocalAnalysis.StandardType.FS81.N7Split
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem sign_mul_eq_zero_iff {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k)
    (a : ZMod 3) : s i * a = 0 ↔ a = 0 := by
  rcases hs i with h | h <;> rw [h] <;> revert a <;> decide

theorem wt_sign_mul {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (e : Fin k → ZMod 3) :
    wt (fun i => s i * e i) = wt e := by
  unfold wt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (sign_mul_eq_zero_iff hs i (e i))

theorem sign_mul_ne_zero_vec {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) {e : Fin k → ZMod 3}
    (he : e ≠ 0) : (fun i => s i * e i) ≠ 0 := by
  intro h
  apply he
  funext i
  have : s i * e i = 0 := congrFun h i
  exact (sign_mul_eq_zero_iff hs i (e i)).mp this

theorem prod_neg_eight (v : Fin 8 → ZMod 3) : ∏ i, (-v) i = ∏ i, v i := by
  simp only [Pi.neg_apply, Fin.prod_univ_eight]
  ring

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

theorem vec_neg_eq_inv (B : Basis3 G k) (e : Coords k) : B.vec (-e) = (B.vec e)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← B.vec_add, add_neg_cancel, B.vec_zero]

theorem vec_zsmul (B : Basis3 G k) (m : ℤ) (e : Coords k) : B.vec (m • e) = B.vec e ^ m := by
  induction m with
  | zero => rw [zero_smul, zpow_zero, B.vec_zero]
  | succ n ih => rw [add_smul, one_smul, B.vec_add, ih, zpow_add_one]
  | pred n ih =>
    have h : (-(n : ℤ) - 1) • e = (-(n : ℤ)) • e + -e := by rw [sub_smul, one_smul, sub_eq_add_neg]
    rw [h, B.vec_add, B.vec_neg_eq_inv, ih, zpow_sub_one]

theorem eq_or_eq_neg_of_vec_mem_zpowers (B : Basis3 G k) {u v : Coords k} (hu : u ≠ 0)
    (h : B.vec u ∈ Subgroup.zpowers (B.vec v)) : u = v ∨ u = -v := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← B.vec_zsmul] at hm
  have huv : ((m : ZMod 3)) • v = u := by
    rw [← B.vec_injective hm]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 by decide) (m : ZMod 3) with h0 | h1 | h2
  · exact absurd (show u = 0 by rw [← huv, h0, zero_smul]) hu
  · left
    rw [← huv, h1, one_smul]
  · right
    rw [← huv, h2]
    funext i
    simp

theorem pow_val_mul (B : Basis3 G k) (i : Fin k) (a c : ZMod 3) :
    (B.b i ^ a.val) ^ c.val = B.b i ^ (a * c).val := by
  have h := pow_mod_orderOf (B.b i) (a.val * c.val)
  rw [B.ord i] at h
  rw [← pow_mul, ZMod.val_mul, h]

theorem signed_prod (B : Basis3 G k) (s : Fin k → ZMod 3) (e : Coords k) :
    (List.ofFn fun i => (B.b i ^ (s i).val) ^ (e i).val).prod = B.vec (fun i => s i * e i) := by
  unfold Basis3.vec
  congr 1
  rw [List.ofFn_inj]
  funext i
  exact B.pow_val_mul i (s i) (e i)

theorem orderOf_pow_sign (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) :
    orderOf (B.b i ^ (s i).val) = 3 := by
  rcases hs i with h | h
  · rw [show (s i).val = 1 by rw [h]; decide, pow_one, B.ord i]
  · rw [show (s i).val = 2 by rw [h]; decide, orderOf_pow' _ two_ne_zero, B.ord i]
    decide

theorem eq_zero_of_signed_prod (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s)
    (e : Coords k) (he : (List.ofFn fun i => (B.b i ^ (s i).val) ^ (e i).val).prod = 1) :
    e = 0 := by
  rw [B.signed_prod] at he
  have h0 := B.indep (fun i => s i * e i) he
  funext i
  have : s i * e i = 0 := congrFun h0 i
  exact (sign_mul_eq_zero_iff hs i (e i)).mp this

@[expose] def signed (B : Basis3 G k) (s : Fin k → ZMod 3) (hs : IsSign s) : Basis3 G k where
  b i := B.b i ^ (s i).val
  comm i j := ((B.comm i j).pow_left _).pow_right _
  ord i := B.orderOf_pow_sign hs i
  indep e he := B.eq_zero_of_signed_prod hs e he

theorem vec_signed (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s) (e : Coords k) :
    (B.signed s hs).vec e = B.vec (fun i => s i * e i) :=
  B.signed_prod s e

theorem line_signed (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s) (e : Coords k) :
    (B.signed s hs).line e = B.line (fun i => s i * e i) := by
  show Subgroup.zpowers ((B.signed s hs).vec e) = Subgroup.zpowers (B.vec _)
  rw [B.vec_signed hs]

theorem span_signed (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s) :
    (B.signed s hs).span = B.span := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact B.span.pow_mem (B.b_mem_span i) _
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    have h : B.b i = (B.signed s hs).b i ^ (s i).val := by
      show B.b i = (B.b i ^ (s i).val) ^ (s i).val
      rw [B.pow_val_mul]
      have hss : (s i * s i).val = 1 := by rcases hs i with h | h <;> rw [h] <;> decide
      rw [hss, pow_one]
    rw [h]
    exact (B.signed s hs).span.pow_mem ((B.signed s hs).b_mem_span i) _

theorem exists_conj_of_mem_xg (B : Basis3 G k) {x : GL (Fin k) (ZMod 3)}
    (hx : x ∈ (ggAutomizer ⊤ B.span).map B.glHom) :
    ∃ g ∈ Subgroup.normalizer (B.span : Set G), ∀ v : Coords k,
      g * B.vec v * g⁻¹ = B.vec ((x : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v) := by
  obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hx
  exact ⟨g, hgN, fun v => B.acts_vec (B.acts_matOf hg) v⟩

theorem exists_xg_of_mem_normalizer (B : Basis3 G k) {g : G}
    (hg : g ∈ Subgroup.normalizer (B.span : Set G)) :
    ∃ x ∈ (ggAutomizer ⊤ B.span).map B.glHom, ∀ v : Coords k,
      g * B.vec v * g⁻¹ = B.vec ((x : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v) := by
  have hφ : ∀ y : ↥B.span,
      ((B.span.normalizerMonoidHom ⟨g, hg⟩ y : ↥B.span) : G) = g * y * g⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  exact ⟨B.glHom (B.span.normalizerMonoidHom ⟨g, hg⟩),
    Subgroup.mem_map_of_mem _ (mem_ggAutomizer_iff.mpr ⟨g, trivial, hg, hφ⟩),
    fun v => B.acts_vec (B.acts_matOf hφ) v⟩

theorem isConjLine_iff_isConjLineIn (B : Basis3 G k) {b₀ : G} (hfus : Fus42 B b₀)
    (e : Coords k) : IsConjLine b₀ (B.line e) ↔ IsConjLineIn B.span b₀ (B.line e) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 : g * b₀ * g⁻¹ ∈ B.line e := hg ▸ Subgroup.mem_zpowers _
    obtain ⟨x, hx, hxe⟩ := hfus.2 g ((Subgroup.zpowers_le.mpr (B.vec_mem_span e)) h1)
    exact ⟨x, hx, by rw [← hxe]; exact hg⟩
  · rintro ⟨g, -, hg⟩
    exact ⟨g, hg⟩

theorem isConjLineIn_iff_orbV (B : Basis3 G 8) (u : Coords 8) {e : Coords 8} (he : e ≠ 0) :
    IsConjLineIn B.span (B.vec u) (B.line e) ↔
      OrbV ((ggAutomizer ⊤ B.span).map B.glHom) u e ∨
        OrbV ((ggAutomizer ⊤ B.span).map B.glHom) u (-e) := by
  constructor
  · rintro ⟨g, hgN, hg⟩
    obtain ⟨x, hx, hxv⟩ := B.exists_xg_of_mem_normalizer hgN
    rw [hxv] at hg
    have hmem : B.vec e ∈
        Subgroup.zpowers (B.vec ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u)) := by
      rw [hg]
      exact Subgroup.mem_zpowers _
    rcases B.eq_or_eq_neg_of_vec_mem_zpowers he hmem with h | h
    · exact Or.inl ⟨x, hx, h.symm⟩
    · exact Or.inr ⟨x, hx, by rw [h, neg_neg]⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · obtain ⟨g, hgN, hgv⟩ := B.exists_conj_of_mem_xg hx
      refine ⟨g, hgN, ?_⟩
      show Subgroup.zpowers _ = Subgroup.zpowers (B.vec e)
      rw [hgv, h]
    · obtain ⟨g, hgN, hgv⟩ := B.exists_conj_of_mem_xg hx
      refine ⟨g, hgN, ?_⟩
      show Subgroup.zpowers _ = Subgroup.zpowers (B.vec e)
      rw [hgv, h, B.vec_neg_eq_inv, Subgroup.zpowers_inv]

theorem n7MatHyp_xg [Finite G] (B : Basis3 G 8) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 7)
    (hK : ∀ σ : Equiv.Perm (Fin 8), spMat σ 1 ∈ B.realized ⊤) :
    N7MatHyp ((ggAutomizer ⊤ B.span).map B.glHom) where
  norm A hA hcol := by
    obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hA
    have hc : B.matOf φ *ᵥ Pi.single 0 1 = B.matOf φ 0 0 • Pi.single 0 1 := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi
        simp
      · rw [show B.matOf φ i 0 = 0 from hcol i hi, Pi.single_eq_of_ne hi, mul_zero]
    have himg := B.conj_b_of_mulVec_single hg hc
    rw [hb0] at himg
    have hgb : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
      refine mem_normalizer_zpowers_of_conj ?_
      rw [himg]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) _
    rw [← hN0]
    exact (B.mem_realized_iff _ _).mpr ⟨φ, ⟨g, hgb, hgN, hg⟩, rfl⟩
  sub M hM := B.exists_xg_of_realized _ (by rw [hN0]; exact hM)
  perm σ := B.exists_xg_of_realized _ (hK σ)

end Basis3

@[expose] def sgn7 : Fin 8 → ZMod 3 := fun i => if i = 7 then -1 else 1

theorem isSign_sgn7 : IsSign sgn7 := by
  unfold IsSign sgn7
  decide

theorem recOutTwD7_of_perm {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hfus : Fus42 B b₀)
    (hN0 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 7)
    (hK : ∀ σ : Equiv.Perm (Fin 8), spMat σ 1 ∈ B.realized ⊤) :
    ∃ B' : Basis3 G 8, Adapted B' b₀ K E ∧ RecOutTwD7 B' b₀ := by
  obtain ⟨hspan, hb0, hBK⟩ := hB
  subst hspan
  obtain ⟨-, ⟨-, -, -, -, -, hcard⟩, -⟩ := hstd
  have hM := B.n7MatHyp_xg hb0 hN0 hK
  have h5 : 2 ^ 8 * Nat.factorial 8 < Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom) := by
    rw [Subgroup.card_map_of_injective B.glHom_injective]
    exact hcard
  obtain ⟨hX, hO⟩ := orbit_evenAll0_seven _ hM h5
  obtain ⟨ε, hε, hR⟩ := orbit_root_seven _ hM h5
  have h1 : Nat.card ↥(ggAutomizer ⊤ B.span) = 696729600 := by
    rw [← hX, Subgroup.card_map_of_injective B.glHom_injective]
  have h2 : ∀ e : Coords 8, e ≠ 0 →
      (IsConjLine b₀ (B.line e) ↔ (wt e = 1 ∨ wt e = 4 ∨ wt e = 7)) := by
    intro e he
    rw [B.isConjLine_iff_isConjLineIn hfus, ← hb0, ← B.vec_single, B.isConjLineIn_iff_orbV _ he]
    have h := hO e
    have h' := hO (-e)
    unfold OrbE0 at h h'
    unfold OrbV
    rw [h, h', wt_neg, or_self]
  have h3 : ∀ e : Coords 8, e ≠ 0 → (IsConjLineIn B.span (b₀ * B.b 1) (B.line e) ↔
      (wt e = 2 ∨ (wt e = 8 ∧ ∏ i, e i = ε))) := by
    intro e he
    rw [← hb0, ← B.vec_single, ← B.vec_single, ← B.vec_add,
      show (Pi.single 0 1 + Pi.single 1 1 : Coords 8) = repW 2 by decide,
      B.isConjLineIn_iff_orbV _ he, hR, hR, wt_neg, prod_neg_eight, or_self]
  rcases hε with hε1 | hεm
  ·
    have hne : ∀ e : Coords 8, e ≠ 0 → (fun i => sgn7 i * e i) ≠ 0 :=
      fun e he => sign_mul_ne_zero_vec isSign_sgn7 he
    refine ⟨B.signed sgn7 isSign_sgn7, ⟨B.span_signed isSign_sgn7, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show B.b 0 ^ (sgn7 0).val = b₀
      rw [show (sgn7 0).val = 1 by decide, pow_one, hb0]
    · intro i hi
      exact K.pow_mem (hBK i hi) _
    · rw [B.span_signed isSign_sgn7]
      exact h1
    · intro e he
      rw [B.line_signed isSign_sgn7, h2 _ (hne e he), wt_sign_mul isSign_sgn7]
    · intro e he
      have hb1 : (B.signed sgn7 isSign_sgn7).b 1 = B.b 1 := by
        show B.b 1 ^ (sgn7 1).val = B.b 1
        rw [show (sgn7 1).val = 1 by decide, pow_one]
      have hp : ∏ i, sgn7 i * e i = -∏ i, e i := by
        rw [Finset.prod_mul_distrib, show ∏ i, sgn7 i = -1 by decide, neg_one_mul]
      rw [B.span_signed isSign_sgn7, hb1, B.line_signed isSign_sgn7, h3 _ (hne e he),
        wt_sign_mul isSign_sgn7, hε1]
      simp only [hp, neg_eq_iff_eq_neg]
      exact Iff.rfl
  · exact ⟨B, ⟨rfl, hb0, hBK⟩, h1, h2, fun e he => by rw [h3 e he, hεm]; exact Iff.rfl⟩

theorem l1N7Main_of_perm
    (hK : ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
      StdAssumptions b₀ K E Row.twD7 → ∀ B : Basis3 G (Row.twD7.n + 1), Adapted B b₀ K E →
        LocalOrthII B b₀ → Fus42 B b₀ → OddCoreTrivial E →
          B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 Row.twD7.n →
            ∀ σ : Equiv.Perm (Fin (Row.twD7.n + 1)), spMat σ 1 ∈ B.realized ⊤) :
    L1N7Main := by
  intro G _ _ b₀ K E hstd B hB hII hfus hodd hN0
  exact recOutTwD7_of_perm hstd hB hfus hN0 (hK G b₀ K E hstd B hB hII hfus hodd hN0)

end CFSG.StandardType.FrameRoute.FS81

end
