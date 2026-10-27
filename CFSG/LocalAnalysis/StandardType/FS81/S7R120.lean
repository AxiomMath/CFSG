module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
import CFSG.LocalAnalysis.StandardType.FS81.E7RowE4

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private instance instDecE8RootLine (δ : ZMod 3) (e : Coords 8) : Decidable (E8RootLine δ e) := by
  unfold E8RootLine
  infer_instance

private theorem ncard_lineImage_eq {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (p : Coords k → Prop) [DecidablePred p]
    (hne : ∀ e, p e → e ≠ 0)
    (hneg : ∀ e, p (-e) ↔ p e)
    (hcard : (Finset.univ.filter p).card = 240) :
    (B.line '' {e | p e}).ncard = 120 := by
  classical
  let Sf : Finset (Coords k) := Finset.univ.filter p
  have hSfcard : Sf.card = 240 := hcard
  have hfiber : ∀ L ∈ Sf.image B.line, (Sf.filter fun e => B.line e = L).card = 2 := by
    intro L hL
    obtain ⟨e, he, hLe⟩ := Finset.mem_image.mp hL
    have hpe : p e := (Finset.mem_filter.mp he).2
    have he0 : e ≠ 0 := hne e hpe
    have hne' : e ≠ -e := by
      intro h
      apply he0
      funext i
      exact (by decide : ∀ x : ZMod 3, x = -x → x = 0) (e i) (congrFun h i)
    have hsub : Sf.filter (fun e' => B.line e' = B.line e) = {e, -e} := by
      ext e'
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨he', hline⟩
        have hpe' : p e' := (Finset.mem_filter.mp he').2
        have he'0 : e' ≠ 0 := hne e' hpe'
        have hmem : B.vec e' ∈ Subgroup.zpowers (B.vec e) := by
          have h : B.vec e' ∈ B.line e' := Subgroup.mem_zpowers _
          rw [hline] at h
          exact h
        rcases B.eq_or_eq_neg_of_vec_mem_zpowers he'0 hmem with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨he, rfl⟩
        · refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hneg e).mpr hpe⟩, ?_⟩
          rw [Basis3.line, Basis3.line, Basis3.vec_neg_eq_inv, Subgroup.zpowers_inv]
    rw [show Sf.filter (fun e' => B.line e' = L) = Sf.filter (fun e' => B.line e' = B.line e)
      by rw [← hLe]]
    rw [hsub, Finset.card_pair hne']
  have hsum := Finset.card_eq_sum_card_fiberwise (s := Sf) (t := Sf.image B.line)
    (f := fun e => B.line e) (fun e he => Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hsum2 : Sf.card = ∑ L ∈ Sf.image B.line, 2 :=
    hsum.trans (Finset.sum_congr rfl fun L hL => hfiber L hL)
  rw [Finset.sum_const, hSfcard] at hsum2
  have hS : {e : Coords k | p e} = (↑Sf : Set (Coords k)) := by
    ext e; simp [Sf]
  have himg : B.line '' {e | p e} = ↑(Sf.image B.line) := by
    rw [hS, Finset.coe_image]
  rw [himg, Set.ncard_coe_finset]
  have h : (Sf.image B.line).card * 2 = 240 := by
    simpa [smul_eq_mul, mul_comm] using hsum2.symm
  omega

private theorem e8RootLine_neg (δ : ZMod 3) (e : Coords 8) :
    E8RootLine δ (-e) ↔ E8RootLine δ e := by
  have h4 : (∏ i : Fin 6, (-e) i.succ.succ) = ∏ i : Fin 6, e i.succ.succ := by
    rw [show (∏ i : Fin 6, (-e) i.succ.succ) = ∏ i : Fin 6, -(e i.succ.succ) from rfl,
      Finset.prod_neg, Finset.card_univ, Fintype.card_fin,
      show (-1 : ZMod 3) ^ 6 = 1 by decide, one_mul]
  simp only [E8RootLine, wt_neg, h4]
  simp only [Pi.neg_apply, neg_ne_zero, neg_eq_zero]

private theorem twD7Pred_neg (e : Coords 8) :
    (wt (-e) = 2 ∨ (wt (-e) = 8 ∧ ∏ i : Fin 8, (-e) i = -1)) ↔
      (wt e = 2 ∨ (wt e = 8 ∧ ∏ i : Fin 8, e i = -1)) := by
  rw [wt_neg e, prod_neg_eight e]

private theorem normalizerLines_eq_isConjLineIn {G : Type} [Group G] [Finite G]
    {Y E : Subgroup G} {x : G} (hxE : x ∈ E)
    (hA : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)) :
    normalizerLines Y E x = {Z : Subgroup G | IsConjLineIn E x Z} := by
  ext Z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg.2, rfl⟩
  · rintro ⟨g, hgN, rfl⟩
    obtain ⟨y, hyY, hyN, c, hcC, hgc⟩ := exists_mul_of_card_ggAutomizer_eq hA hgN
    have hcomm : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcC x hxE
    have hcx : c * x * c⁻¹ = x := by
      rw [← hcomm]; group
    refine ⟨y, Subgroup.mem_inf.mpr ⟨hyY, hyN⟩, ?_⟩
    rw [hgc]
    show Subgroup.zpowers ((y * c) * x * (y * c)⁻¹) = Subgroup.zpowers (y * x * y⁻¹)
    rw [show (y * c) * x * (y * c)⁻¹ = y * (c * x * c⁻¹) * y⁻¹ by group, hcx]

private theorem lineImage_eq_of_recOut {G : Type} [Group G] [Finite G] {B : Basis3 G 8} {x : G}
    {p : Coords 8 → Prop} (hxspan : x ∈ B.span) (hx1 : x ≠ 1)
    (hrec : ∀ e : Coords 8, e ≠ 0 → (IsConjLineIn B.span x (B.line e) ↔ p e)) :
    {Z : Subgroup G | IsConjLineIn B.span x Z} =
      B.line '' {e : Coords 8 | e ≠ 0 ∧ p e} := by
  ext Z
  constructor
  · rintro ⟨g, hgN, rfl⟩
    have hmem : g * x * g⁻¹ ∈ B.span := (Subgroup.mem_normalizer_iff.mp hgN x).mp hxspan
    obtain ⟨e, he⟩ := B.exists_vec_eq hmem
    have hlin : Subgroup.zpowers (g * x * g⁻¹) = B.line e := by rw [← he]; rfl
    have he0 : e ≠ 0 := by
      intro he0
      apply hx1
      have h1 : g * x * g⁻¹ = 1 := by rw [← he, he0, B.vec_zero]
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hpe : p e := (hrec e he0).mp ⟨g, hgN, hlin⟩
    exact ⟨e, ⟨he0, hpe⟩, hlin.symm⟩
  · rintro ⟨e, ⟨he0, hpe⟩, rfl⟩
    exact (hrec e he0).mpr hpe

theorem ncard_normalizerLines_eq_120_E7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (Row.E7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.E7 b₀ K E B Y)
    (hA : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)) :
    (normalizerLines Y E b₀).ncard = 120 := by
  classical
  have hxspan : b₀ ∈ B.span := by
    rw [← h.adapted.2.1]
    exact B.b_mem_span 0
  have hx1 : b₀ ≠ 1 := by
    intro h1
    have hord := B.ord 0
    rw [h.adapted.2.1, h1, orderOf_one] at hord
    exact absurd hord (by decide)
  have hxE : b₀ ∈ E := h.adapted.1 ▸ hxspan
  have hrec : ∀ e : Coords 8, e ≠ 0 → (IsConjLineIn B.span b₀ (B.line e) ↔ E8RootLine 1 e) := by
    intro e he
    rw [← B.isConjLine_iff_isConjLineIn h.fus e]
    exact h.recOut.2.1 e he
  have hline : {Z : Subgroup G | IsConjLineIn E b₀ Z} =
      B.line '' {e : Coords 8 | e ≠ 0 ∧ E8RootLine 1 e} := by
    rw [show E = B.span from h.adapted.1.symm]
    exact lineImage_eq_of_recOut hxspan hx1 hrec
  rw [normalizerLines_eq_isConjLineIn hxE hA, hline]
  refine ncard_lineImage_eq (k := 8) B (fun e : Coords 8 => e ≠ 0 ∧ E8RootLine 1 e)
    (fun e h => h.1) ?_ ?_
  · intro e; constructor
    · intro h
      exact ⟨neg_ne_zero.mp h.1, (e8RootLine_neg 1 e).mp h.2⟩
    · intro h
      exact ⟨neg_ne_zero.mpr h.1, (e8RootLine_neg 1 e).mpr h.2⟩
  · have h := E7Row.card_phiPred (δ := 1) (Or.inl rfl)
    rw [← h]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro e _
    by_cases he : e = 0
    · subst he
      constructor
      · intro h; exact absurd rfl h.1
      · intro h; exact absurd h (by decide)
    · constructor
      · intro h; exact (E7Row.phiPred_iff_e8 (Or.inl rfl) he).mpr h.2
      · intro h; exact ⟨he, (E7Row.phiPred_iff_e8 (Or.inl rfl) he).mp h⟩

theorem ncard_normalizerLines_eq_120_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (Row.twD7.n + 1)} {Y : Subgroup G}
    (h : RootSetting Row.twD7 b₀ K E B Y)
    (hA : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)) :
    (normalizerLines Y E (b₀ * B.b 1)).ncard = 120 := by
  classical
  have hxspan : b₀ * B.b 1 ∈ B.span := by
    rw [← h.adapted.2.1]
    exact B.span.mul_mem (B.b_mem_span 0) (B.b_mem_span 1)
  have hx1 : b₀ * B.b 1 ≠ 1 := by
    intro h1
    have h1' : B.b 0 * B.b 1 = 1 := by rwa [← h.adapted.2.1] at h1
    have h0 : B.vec (Pi.single 0 1 + Pi.single 1 1) = B.vec 0 := by
      rw [B.vec_add, B.vec_single, B.vec_single, h1', B.vec_zero]
    have hc : (Pi.single 0 1 + Pi.single 1 1 : Coords 8) 0 ≠ 0 := by decide
    exact hc (congrFun (B.vec_injective h0) 0)
  have hxE : b₀ * B.b 1 ∈ E := h.adapted.1 ▸ hxspan
  have hrec : ∀ e : Coords 8, e ≠ 0 →
      (IsConjLineIn B.span (b₀ * B.b 1) (B.line e) ↔
        (wt e = 2 ∨ (wt e = 8 ∧ ∏ i : Fin 8, e i = -1))) := by
    intro e he
    exact h.recOut.2.2 e he
  have hline : {Z : Subgroup G | IsConjLineIn E (b₀ * B.b 1) Z} =
      B.line '' {e : Coords 8 | e ≠ 0 ∧ (wt e = 2 ∨ (wt e = 8 ∧ ∏ i : Fin 8, e i = -1))} := by
    rw [show E = B.span from h.adapted.1.symm]
    exact lineImage_eq_of_recOut hxspan hx1 hrec
  rw [normalizerLines_eq_isConjLineIn hxE hA, hline]
  refine ncard_lineImage_eq B
    (fun e => e ≠ 0 ∧ (wt e = 2 ∨ (wt e = 8 ∧ ∏ i : Fin 8, e i = -1))) (fun e h => h.1) ?_ ?_
  · intro e; constructor
    · intro h
      exact ⟨neg_ne_zero.mp h.1, (twD7Pred_neg e).mp h.2⟩
    · intro h
      exact ⟨neg_ne_zero.mpr h.1, (twD7Pred_neg e).mpr h.2⟩
  · decide +kernel

end CFSG.StandardType.FrameRoute.FS81

end
