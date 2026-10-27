module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowE5
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvE7
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly E7Row
open scoped Matrix

namespace E7Row

@[expose] def flip7 (e : Coords 8) : Coords 8 := fun i => if i = 7 then -e i else e i

theorem flip7_ne_zero {e : Coords 8} (he : e ≠ 0) : flip7 e ≠ 0 := by
  intro h
  apply he
  funext i
  have := congrFun h i
  by_cases hi : i = 7
  · subst hi
    simp only [flip7, if_true, Pi.zero_apply, neg_eq_zero] at this
    exact this
  · simp only [flip7, hi, if_false, Pi.zero_apply] at this
    exact this

set_option maxRecDepth 100000 in
theorem e8e_flip7 : ∀ e : Coords 8, E8e (-1) (flip7 e) ↔ E8e 1 e := by
  decide +kernel

theorem qE8_flip7 (e : Coords 8) : qE8 (flip7 e) = qE8 e := by
  rw [qE8_eq, qE8_eq]
  simp [flip7]

end E7Row

variable {G : Type} [Group G]

namespace Basis3

theorem inv_pow_val {b : G} (hb : orderOf b = 3) (c : ZMod 3) : b⁻¹ ^ c.val = b ^ (-c).val := by
  have h3 : b ^ 3 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hb2 : b ^ 2 = b⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by decide +revert) with rfl | rfl | rfl
  · rw [neg_zero, ZMod.val_zero, pow_zero, pow_zero]
  · rw [show (1 : ZMod 3).val = 1 from rfl, show (-1 : ZMod 3).val = 2 from rfl, pow_one, hb2]
  · rw [show (2 : ZMod 3).val = 2 from rfl, show (-2 : ZMod 3).val = 1 from rfl, pow_one,
      inv_pow, hb2, inv_inv]

@[expose] def negLastB (B : Basis3 G 8) (i : Fin 8) : G := if i = 7 then (B.b i)⁻¹ else B.b i

theorem negLastB_prod (B : Basis3 G 8) (e : Coords 8) :
    (List.ofFn fun i => B.negLastB i ^ (e i).val).prod = B.vec (flip7 e) := by
  unfold vec
  congr 2
  funext i
  by_cases hi : i = 7
  · subst hi
    simp only [negLastB, flip7, if_true]
    exact inv_pow_val (B.ord 7) (e 7)
  · simp only [negLastB, flip7, hi, if_false]

@[expose] def negLast (B : Basis3 G 8) : Basis3 G 8 where
  b := B.negLastB
  comm i j := by
    unfold negLastB
    split_ifs
    · exact (B.comm i j).inv_inv
    · exact (B.comm i j).inv_left
    · exact (B.comm i j).inv_right
    · exact B.comm i j
  ord i := by
    unfold negLastB
    split_ifs
    · rw [orderOf_inv]
      exact B.ord i
    · exact B.ord i
  indep e he := by
    rw [B.negLastB_prod] at he
    have h0 := B.indep (flip7 e) he
    by_contra hne
    exact flip7_ne_zero hne h0

theorem negLast_vec (B : Basis3 G 8) (e : Coords 8) : B.negLast.vec e = B.vec (flip7 e) :=
  B.negLastB_prod e

theorem negLast_line (B : Basis3 G 8) (e : Coords 8) : B.negLast.line e = B.line (flip7 e) := by
  rw [line, line, negLast_vec]

theorem negLast_b_of_ne (B : Basis3 G 8) {i : Fin 8} (hi : i ≠ 7) : B.negLast.b i = B.b i := by
  show B.negLastB i = B.b i
  rw [negLastB, if_neg hi]

theorem negLast_span (B : Basis3 G 8) : B.negLast.span = B.span := by
  apply le_antisymm
  · rw [span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show B.negLastB i ∈ B.span
    unfold negLastB
    split_ifs
    · exact B.span.inv_mem (B.b_mem_span i)
    · exact B.b_mem_span i
  · rw [span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 7
    · subst hi
      have h := B.negLast.b_mem_span 7
      have : B.negLast.b 7 = (B.b 7)⁻¹ := by
        show B.negLastB 7 = _
        rw [negLastB, if_pos rfl]
      rw [this] at h
      simpa using B.negLast.span.inv_mem h
    · rw [← B.negLast_b_of_ne hi]
      exact B.negLast.b_mem_span i

theorem negLast_adapted {B : Basis3 G 8} {b₀ : G} {K E : Subgroup G} (hB : Adapted B b₀ K E) :
    Adapted B.negLast b₀ K E := by
  refine ⟨by rw [negLast_span]; exact hB.1, by rw [B.negLast_b_of_ne (by decide)]; exact hB.2.1,
    fun i hi => ?_⟩
  by_cases h7 : i = 7
  · subst h7
    have : B.negLast.b 7 = (B.b 7)⁻¹ := by
      show B.negLastB 7 = _
      rw [negLastB, if_pos rfl]
    rw [this]
    exact K.inv_mem (hB.2.2 7 hi)
  · rw [B.negLast_b_of_ne h7]
    exact hB.2.2 i hi

variable {k : ℕ}

private theorem vec_neg_inv (B : Basis3 G k) (e : Coords k) : B.vec (-e) = (B.vec e)⁻¹ := by
  have h : B.vec e * B.vec (-e) = 1 := by
    rw [← B.vec_add, add_neg_cancel, B.vec_zero]
  exact eq_inv_of_mul_eq_one_right h

variable [Finite G]

theorem zpowers_vec_eq_line_iff (B : Basis3 G k) {v e : Coords k} (he : e ≠ 0) :
    Subgroup.zpowers (B.vec v) = B.line e ↔ v = e ∨ v = -e := by
  constructor
  · intro h
    have hv : B.vec v ∈ B.line e := h ▸ Subgroup.mem_zpowers _
    rw [line, ← mem_powers_iff_mem_zpowers] at hv
    obtain ⟨n, hn⟩ := hv
    have hn : B.vec e ^ n = B.vec v := hn
    rw [← B.vec_nsmul] at hn
    have hv' := B.vec_injective hn
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3)] at hv'
    have k3 : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 := by decide
    rcases k3 (n : ZMod 3) with h0 | h1 | h2
    · exfalso
      rw [h0, zero_smul] at hv'
      rw [← hv', B.vec_zero, Subgroup.zpowers_one_eq_bot] at h
      apply he
      apply B.vec_injective
      rw [B.vec_zero]
      have : B.vec e ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers _
      exact Subgroup.mem_bot.mp this
    · left
      rw [← hv', h1, one_smul]
    · right
      rw [← hv', h2, neg_one_smul]
  · rintro (rfl | rfl)
    · rfl
    · rw [B.vec_neg_inv, Subgroup.zpowers_inv]
      rfl

end Basis3

variable [Finite G]

theorem isConjLine_iff_orbitLine (B : Basis3 G 8) {b₀ : G} (hb0 : B.b 0 = b₀)
    (hfus : Fus42 B b₀) {e : Coords 8} (he : e ≠ 0) :
    IsConjLine b₀ (B.line e) ↔
      OrbitLine ((ggAutomizer ⊤ B.span).map B.glHom) (Pi.single 0 1) e := by
  rw [orbitLine_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hmem : g * b₀ * g⁻¹ ∈ B.span := by
      have : g * b₀ * g⁻¹ ∈ B.line e := hg ▸ Subgroup.mem_zpowers _
      exact (Subgroup.zpowers_le.mpr (B.vec_mem_span e)) this
    obtain ⟨x, hxN, hx⟩ := hfus.2 g hmem
    have hφX : B.span.normalizerMonoidHom ⟨x, hxN⟩ ∈ ggAutomizer ⊤ B.span :=
      mem_ggAutomizer_iff.mpr ⟨x, trivial, hxN, fun b =>
        Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _⟩
    have hconj := B.acts_vec (B.acts_matOf (φ := B.span.normalizerMonoidHom ⟨x, hxN⟩) (g := x)
      (fun b => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _)) (Pi.single 0 1)
    rw [B.vec_single, hb0] at hconj
    rw [hx, hconj, B.zpowers_vec_eq_line_iff he] at hg
    exact ⟨B.glHom (B.span.normalizerMonoidHom ⟨x, hxN⟩), Subgroup.mem_map_of_mem _ hφX, hg⟩
  · rintro ⟨x, hx, hxe⟩
    obtain ⟨φ, g, -, hg, rfl⟩ := B.exists_of_mem_xg hx
    refine ⟨g, ?_⟩
    have hconj := B.acts_vec (B.acts_matOf hg) (Pi.single 0 1)
    rw [B.vec_single, hb0] at hconj
    rw [hconj]
    exact (B.zpowers_vec_eq_line_iff he).mpr hxe

theorem isConjLineIn_iff_orbitLine (B : Basis3 G 8) {v e : Coords 8} (he : e ≠ 0) :
    IsConjLineIn B.span (B.vec v) (B.line e) ↔
      OrbitLine ((ggAutomizer ⊤ B.span).map B.glHom) v e := by
  rw [orbitLine_iff]
  constructor
  · rintro ⟨g, hgN, hg⟩
    have hφX : B.span.normalizerMonoidHom ⟨g, hgN⟩ ∈ ggAutomizer ⊤ B.span :=
      mem_ggAutomizer_iff.mpr ⟨g, trivial, hgN, fun b =>
        Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _⟩
    rw [B.acts_vec (B.acts_matOf (φ := B.span.normalizerMonoidHom ⟨g, hgN⟩) (g := g)
      (fun b => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _)) v,
      B.zpowers_vec_eq_line_iff he] at hg
    exact ⟨B.glHom (B.span.normalizerMonoidHom ⟨g, hgN⟩), Subgroup.mem_map_of_mem _ hφX, hg⟩
  · rintro ⟨x, hx, hxe⟩
    obtain ⟨φ, g, hgN, hg, rfl⟩ := B.exists_of_mem_xg hx
    refine ⟨g, hgN, ?_⟩
    rw [B.acts_vec (B.acts_matOf hg) v]
    exact (B.zpowers_vec_eq_line_iff he).mpr hxe

omit [Finite G] in
theorem vec_e0_e1 (B : Basis3 G 8) {b₀ : G} (hb0 : B.b 0 = b₀) :
    b₀ * B.b 1 = B.vec (Pi.single 0 1 + Pi.single 1 1) := by
  rw [B.vec_add, B.vec_single, B.vec_single, hb0]

theorem recOutE7_of_core (hcore : E7MatCore) {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.E7) (B : Basis3 G 8) (hB : Adapted B b₀ K E)
    (hloc : LocalE7 B b₀) (hfus : Fus42 B b₀) (hodd : OddCoreTrivial E) :
    ∃ B' : Basis3 G 8, Adapted B' b₀ K E ∧ RecOutE7 B' b₀ := by
  classical
  obtain ⟨-, ⟨⟨hord, hKC, hKn, -⟩, -⟩, ⟨-, hdisj, -⟩⟩ := hstd
  have hKn' : ∀ g ∈ Subgroup.centralizer ({b₀} : Set G), ∀ y ∈ K, g * y * g⁻¹ ∈ K :=
    fun g hg y hy => Subgroup.mem_subgroupOf.mp
      (hKn.conj_mem ⟨y, hKC hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩)
  obtain ⟨hcardC, -, hH1⟩ := hloc
  have hb0 := hB.2.1
  have hK := hB.2.2
  have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by
    rw [hB.1]
    exact hdisj
  have hH1' : B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) = hSeven := hH1
  have hH : ∀ A ∈ hSeven, ∃ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A := fun A hA =>
    B.exists_xg_of_realized (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) (by rw [hH1']; exact hA)
  have hstab : ∀ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
      (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 =
        c • Pi.single 1 1) → (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven :=
    fun x hx hxe hxc => by
      rw [← hH1']
      exact B.stab_mem_realized hb0 hx hxe hxc
  have hcard : Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom ⊓ fixE0 7) = 2903040 := by
    rw [card_xg_fixE0 B hb0]
    exact hcardC
  have hoddm : ∀ N : Subgroup ↥((ggAutomizer ⊤ B.span).map B.glHom), N.Normal →
      Odd (Nat.card N) → N = ⊥ := by
    rw [← hB.1] at hodd
    intro N hNn hNodd
    set eqv := (ggAutomizer ⊤ B.span).equivMapOfInjective B.glHom B.glHom_injective
    have hinj : Function.Injective eqv.symm.toMonoidHom := eqv.symm.injective
    have h := hodd (N.map eqv.symm.toMonoidHom) (hNn.map _ eqv.symm.surjective)
      (by rwa [Subgroup.card_map_of_injective hinj])
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h
  obtain ⟨δ, hδ, hcardX, horb0, horb1⟩ := hcore _ hH hstab hcard
    (fun x hx hxe v hv => B.fix_preserves_A hb0 hord hK hdisj' hKn' hx hxe v hv) hoddm
    (B.exists_xg_moves_e0 hb0 hfus)
  have hcardG : Nat.card ↥(ggAutomizer ⊤ B.span) = 696729600 := by
    rw [← hcardX, Subgroup.card_map_of_injective B.glHom_injective]
  rcases hδ with rfl | rfl
  · refine ⟨B, hB, hcardG, fun e he => ?_, fun e he => ?_⟩
    · rw [isConjLine_iff_orbitLine B hb0 hfus he]
      exact horb0 e he
    · rw [vec_e0_e1 B hb0, isConjLineIn_iff_orbitLine B he]
      exact horb1 e he
  · refine ⟨B.negLast, Basis3.negLast_adapted hB, ?_, fun e he => ?_, fun e he => ?_⟩
    · rw [B.negLast_span]
      exact hcardG
    · rw [B.negLast_line, isConjLine_iff_orbitLine B hb0 hfus (flip7_ne_zero he)]
      exact (horb0 _ (flip7_ne_zero he)).trans
        ((e8RootLine_iff _ _).trans ((e8e_flip7 e).trans (e8RootLine_iff _ _).symm))
    · rw [B.negLast_span, B.negLast_b_of_ne (by decide), B.negLast_line, vec_e0_e1 B hb0,
        isConjLineIn_iff_orbitLine B (flip7_ne_zero he)]
      exact (horb1 _ (flip7_ne_zero he)).trans (by rw [qE8_flip7]; exact Iff.rfl)

theorem l1E7_of_core (hcore : E7MatCore) : L1E7 := by
  intro G _ _ b₀ K E hstd B hB hloc hfus hodd
  exact recOutE7_of_core hcore hstd B hB hloc hfus hodd

theorem l1E7_holds : L1E7 :=
  l1E7_of_core e7MatCore_holds

end CFSG.StandardType.FrameRoute.FS81

end
