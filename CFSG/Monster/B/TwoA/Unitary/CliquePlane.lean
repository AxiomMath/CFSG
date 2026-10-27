module

import all CFSG.Fischer.F4
public import CFSG.Monster.B.Classical.UnitarySixGraph
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Monster.B.TwoA.Unitary.Clique

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
  CFSG.Monster.B.Classical.UnitarySix
open scoped LinearAlgebra.Projectivization

@[expose] noncomputable def suEquiv (g : SU frobeniusF4 6) : V ≃ₗ[F4] V where
  toFun v := g • v
  invFun v := g⁻¹ • v
  map_add' := smul_add g
  map_smul' c v := smul_comm g c v
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g

theorem suEquiv_apply (g : SU frobeniusF4 6) (v : V) : suEquiv g v = g • v := rfl

@[expose] noncomputable def smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    Submodule F4 V :=
  X.map (suEquiv g : V →ₗ[F4] V)

theorem mem_smulSub {g : SU frobeniusF4 6} {X : Submodule F4 V} {v : V} :
    v ∈ smulSub g X ↔ g⁻¹ • v ∈ X :=
  Submodule.mem_map_equiv X

theorem smul_mem_smulSub {g : SU frobeniusF4 6} {X : Submodule F4 V} {v : V} :
    g • v ∈ smulSub g X ↔ v ∈ X := by
  rw [mem_smulSub, inv_smul_smul]

theorem smulSub_mul (g g' : SU frobeniusF4 6) (X : Submodule F4 V) :
    smulSub (g * g') X = smulSub g (smulSub g' X) := by
  ext v
  rw [mem_smulSub, mem_smulSub, mem_smulSub, _root_.mul_inv_rev, mul_smul]

theorem smulSub_one (X : Submodule F4 V) : smulSub 1 X = X := by
  ext v
  rw [mem_smulSub, inv_one, one_smul]

theorem smulSub_mono {g : SU frobeniusF4 6} {X Y : Submodule F4 V} (h : X ≤ Y) :
    smulSub g X ≤ smulSub g Y := Submodule.map_mono h

theorem finrank_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    Module.finrank F4 (smulSub g X) = Module.finrank F4 X :=
  LinearEquiv.finrank_map_eq _ _

theorem herm_inv_smul (g : SU frobeniusF4 6) (v w : V) : herm (g⁻¹ • v) w = herm v (g • w) := by
  rw [← herm_smul_smul g, smul_inv_smul]

@[expose] def IsTotIso (X : Submodule F4 V) : Prop := ∀ v ∈ X, ∀ w ∈ X, herm v w = 0

@[expose] def IsMaxIso (W : Submodule F4 V) : Prop := Module.finrank F4 W = 3 ∧ IsTotIso W

@[expose] def planePts (X : Submodule F4 V) : Set IsoPt := {p | p.1.rep ∈ X}

theorem mem_planePts {X : Submodule F4 V} {p : IsoPt} : p ∈ planePts X ↔ p.1.rep ∈ X := Iff.rfl

theorem pt_mem_planePts {X : Submodule F4 V} {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) :
    pt v hv0 hv ∈ planePts X ↔ v ∈ X := by
  obtain ⟨a, ha⟩ := rep_pt hv0 hv
  rw [mem_planePts, ← ha]
  exact Submodule.smul_mem_iff' X a

theorem smul_mem_planePts (g : SU frobeniusF4 6) (X : Submodule F4 V) (p : IsoPt) :
    g • p ∈ planePts (smulSub g X) ↔ p ∈ planePts X := by
  induction p using IsoPt.ind with
  | h v hv0 hv => rw [smul_pt, pt_mem_planePts, pt_mem_planePts, smul_mem_smulSub]

theorem planePts_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    planePts (smulSub g X) = (g • ·) '' planePts X := by
  ext q
  constructor
  · intro hq
    refine ⟨g⁻¹ • q, ?_, smul_inv_smul g q⟩
    rw [← smul_mem_planePts g, smul_inv_smul]
    exact hq
  · rintro ⟨p, hp, rfl⟩
    exact (smul_mem_planePts g X p).2 hp

theorem planePts_mono {X Y : Submodule F4 V} (h : X ≤ Y) : planePts X ⊆ planePts Y :=
  fun _ hp => h hp

theorem isTotIso_smulSub {X : Submodule F4 V} (hX : IsTotIso X) (g : SU frobeniusF4 6) :
    IsTotIso (smulSub g X) := by
  intro v hv w hw
  rw [mem_smulSub] at hv hw
  rw [← herm_smul_smul g⁻¹]
  exact hX _ hv _ hw

theorem isMaxIso_smulSub {W : Submodule F4 V} (hW : IsMaxIso W) (g : SU frobeniusF4 6) :
    IsMaxIso (smulSub g W) :=
  ⟨(finrank_smulSub g W).trans hW.1, isTotIso_smulSub hW.2 g⟩

theorem IsTotIso.mono {X Y : Submodule F4 V} (hY : IsTotIso Y) (h : X ≤ Y) : IsTotIso X :=
  fun v hv w hw => hY v (h hv) w (h hw)

theorem isTotIso_span {s : Set V} (hs : ∀ v ∈ s, ∀ w ∈ s, herm v w = 0) :
    IsTotIso (Submodule.span F4 s) := by
  have h1 : ∀ v ∈ Submodule.span F4 s, ∀ w ∈ s, herm v w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact fun w _ => herm_zero_left w
    | add x y _ _ hx hy => exact fun w hw => by rw [herm_add_left, hx w hw, hy w hw, add_zero]
    | smul c x _ hx => exact fun w hw => by rw [herm_smul_left, hx w hw, mul_zero]
  intro v hv w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h1 v hv x hx
  | zero => exact herm_zero_right v
  | add x y _ _ hx hy => rw [herm_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_right, hx, mul_zero]

abbrev u (i : Fin 6) : V := Pi.single i 1

@[expose] noncomputable def W0 : Submodule F4 V := Submodule.span F4 (Set.range ![u 0, u 1, u 2])

@[expose] noncomputable def A0 : Submodule F4 V := Submodule.span F4 (Set.range ![u 0, u 1])

theorem mem_W0_iff {v : V} : v ∈ W0 ↔ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i <;> decide
    | zero => simp
    | add x y _ _ hx hy => simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
    | smul c x _ hx => simp [hx.1, hx.2.1, hx.2.2]
  · rintro ⟨h3, h4, h5⟩
    have hv : v = v 0 • u 0 + v 1 • u 1 + v 2 • u 2 := by
      funext i
      fin_cases i <;> simp [h3, h4, h5]
    have hm : ∀ i : Fin 3, ![u 0, u 1, u 2] i ∈ W0 := fun i =>
      Submodule.subset_span (Set.mem_range_self i)
    rw [hv]
    exact add_mem (add_mem (Submodule.smul_mem _ _ (hm 0)) (Submodule.smul_mem _ _ (hm 1)))
      (Submodule.smul_mem _ _ (hm 2))

theorem mem_A0_iff {v : V} : v ∈ A0 ↔ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i <;> decide
    | zero => simp
    | add x y _ _ hx hy =>
      simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
    | smul c x _ hx => simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  · rintro ⟨h2, h3, h4, h5⟩
    have hv : v = v 0 • u 0 + v 1 • u 1 := by
      funext i
      fin_cases i <;> simp [h2, h3, h4, h5]
    have hm : ∀ i : Fin 2, ![u 0, u 1] i ∈ A0 := fun i =>
      Submodule.subset_span (Set.mem_range_self i)
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ (hm 0)) (Submodule.smul_mem _ _ (hm 1))

theorem A0_le_W0 : A0 ≤ W0 := fun v hv => by
  obtain ⟨-, h3, h4, h5⟩ := mem_A0_iff.1 hv
  exact mem_W0_iff.2 ⟨h3, h4, h5⟩

theorem mem_W0_iff_herm {v : V} :
    v ∈ W0 ↔ herm v (u 0) = 0 ∧ herm v (u 1) = 0 ∧ herm v (u 2) = 0 := by
  rw [mem_W0_iff, herm_single_right, herm_single_right, herm_single_right]
  exact ⟨fun ⟨h3, h4, h5⟩ => ⟨h5, h4, h3⟩, fun ⟨h5, h4, h3⟩ => ⟨h3, h4, h5⟩⟩

theorem linearIndependent_u3 : LinearIndependent F4 ![u 0, u 1, u 2] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrFun hc
  fin_cases i
  · simpa [Fin.sum_univ_three] using h 0
  · simpa [Fin.sum_univ_three] using h 1
  · simpa [Fin.sum_univ_three] using h 2

theorem linearIndependent_u2 : LinearIndependent F4 ![u 0, u 1] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrFun hc
  fin_cases i
  · simpa [Fin.sum_univ_two] using h 0
  · simpa [Fin.sum_univ_two] using h 1

theorem finrank_W0 : Module.finrank F4 W0 = 3 := by
  rw [W0, finrank_span_eq_card linearIndependent_u3, Fintype.card_fin]

theorem finrank_A0 : Module.finrank F4 A0 = 2 := by
  rw [A0, finrank_span_eq_card linearIndependent_u2, Fintype.card_fin]

theorem isTotIso_W0 : IsTotIso W0 := by
  intro v hv w hw
  rw [mem_W0_iff] at hv hw
  rw [herm_expand, hv.1, hv.2.1, hv.2.2, hw.1, hw.2.1, hw.2.2]
  simp

theorem isMaxIso_W0 : IsMaxIso W0 := ⟨finrank_W0, isTotIso_W0⟩

theorem u_mem_W0 (i : Fin 6) (hi : (i : ℕ) < 3) : u i ∈ W0 := by
  rw [mem_W0_iff]
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl <;> decide

theorem mem_smulSub_W0_iff {g : SU frobeniusF4 6} {v : V} :
    v ∈ smulSub g W0 ↔
      herm v (g • u 0) = 0 ∧ herm v (g • u 1) = 0 ∧ herm v (g • u 2) = 0 := by
  rw [mem_smulSub, mem_W0_iff_herm, herm_inv_smul, herm_inv_smul, herm_inv_smul]

theorem mem_smulSub_W0_of_herm {g : SU frobeniusF4 6} {v : V}
    (h : ∀ w ∈ smulSub g W0, herm v w = 0) : v ∈ smulSub g W0 :=
  mem_smulSub_W0_iff.2 ⟨h _ (smul_mem_smulSub.2 (u_mem_W0 0 (by decide))),
    h _ (smul_mem_smulSub.2 (u_mem_W0 1 (by decide))),
    h _ (smul_mem_smulSub.2 (u_mem_W0 2 (by decide)))⟩

theorem frame_herm (e : Fin 6 → V) (he : IsFrame e) (i j : Fin 6) (hi : (i : ℕ) < 3)
    (hj : (j : ℕ) < 3) : herm (e i) (e j) = 0 := by
  rw [he i j, ite_eq_right]
  intro h
  rw [h, Fin.val_rev] at hj
  omega

theorem exists_smulSub_W0_of_frame {e : Fin 6 → V} (he : IsFrame e) :
    ∃ g : SU frobeniusF4 6, ∀ v : V,
      v ∈ smulSub g W0 ↔ herm v (e 0) = 0 ∧ herm v (e 1) = 0 ∧ herm v (e 2) = 0 := by
  obtain ⟨g, hg⟩ := exists_SU_lines_of_frame he
  refine ⟨g, fun v => ?_⟩
  have key : ∀ i : Fin 6, (herm v (g • u i) = 0 ↔ herm v (e i) = 0) := by
    intro i
    obtain ⟨c, hc0, hc⟩ := hg i
    rw [smul_def, hc, herm_smul_right, mul_eq_zero,
      or_iff_right (fun h => hc0 (bar_eq_zero_iff.1 h))]
  rw [mem_smulSub_W0_iff, key, key, key]

theorem herm_eq_zero_of_basis {X : Submodule F4 V} {ι : Type*} [Fintype ι] (b : Module.Basis ι F4 X)
    {y : V} (hb : ∀ i, herm (b i : V) y = 0) {x : V} (hx : x ∈ X) : herm x y = 0 := by
  have e : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : V) := by
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this.symm
  rw [e, herm_sum_left]
  exact Finset.sum_eq_zero fun i _ => by rw [herm_smul_left, hb i, mul_zero]

theorem linearIndependent_coe_basis {X : Submodule F4 V} {ι : Type*} (b : Module.Basis ι F4 X) :
    LinearIndependent F4 fun i => (b i : V) :=
  b.linearIndependent.map' X.subtype (Submodule.ker_subtype X)

theorem exists_le_smulSub_W0 {X : Submodule F4 V} (hX : IsTotIso X) :
    ∃ g : SU frobeniusF4 6, X ≤ smulSub g W0 := by
  suffices h : ∃ e : Fin 6 → V, IsFrame e ∧ ∀ x ∈ X, ∀ j : Fin 6, (j : ℕ) < 3 →
      herm x (e j) = 0 by
    obtain ⟨e, he, hXe⟩ := h
    obtain ⟨g, hg⟩ := exists_smulSub_W0_of_frame he
    exact ⟨g, fun x hx => (hg x).2 ⟨hXe x hx 0 (by decide), hXe x hx 1 (by decide),
      hXe x hx 2 (by decide)⟩⟩
  rcases Nat.lt_or_ge (Module.finrank F4 X) 3 with hlt | hge
  · interval_cases hk : Module.finrank F4 X
    · refine ⟨_, isFrame_single, fun x hx j _ => ?_⟩
      rw [Submodule.finrank_eq_zero.1 hk] at hx
      rw [(Submodule.mem_bot F4).1 hx, herm_zero_left]
    · let b := Module.finBasisOfFinrankEq F4 X hk
      have hli := linearIndependent_coe_basis b
      have hb0 : (b 0 : V) ≠ 0 := hli.ne_zero 0
      obtain ⟨e, he, he0⟩ := exists_frame_of_isotropic hb0 (hX _ (b 0).2 _ (b 0).2)
      refine ⟨e, he, fun x hx j hj => herm_eq_zero_of_basis b (fun i => ?_) hx⟩
      rw [Fin.fin_one_eq_zero i, ← he0]
      exact frame_herm e he 0 j (by decide) hj
    · let b := Module.finBasisOfFinrankEq F4 X hk
      have hli := linearIndependent_coe_basis b
      have hli2 : LinearIndependent F4 ![(b 0 : V), (b 1 : V)] := by
        convert hli using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨e, he, he0, he1⟩ := exists_frame_of_pair hli2 (hX _ (b 0).2 _ (b 0).2)
        (hX _ (b 1).2 _ (b 1).2) (hX _ (b 0).2 _ (b 1).2)
      refine ⟨e, he, fun x hx j hj => herm_eq_zero_of_basis b (fun i => ?_) hx⟩
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · rw [← he0]
        exact frame_herm e he 0 j (by decide) hj
      · rw [← he1]
        exact frame_herm e he 1 j (by decide) hj
  · let b := Module.finBasis F4 X
    have hli := linearIndependent_coe_basis b
    let f : Fin 3 → Fin (Module.finrank F4 X) := Fin.castLE hge
    have hli3 : LinearIndependent F4 ![(b (f 0) : V), (b (f 1) : V), (b (f 2) : V)] := by
      convert hli.comp f (Fin.castLE_injective hge) using 1
      funext i
      fin_cases i <;> rfl
    obtain ⟨e, he, he0, he1, he2⟩ := exists_frame_of_triple hli3
      (hX _ (b (f 0)).2 _ (b (f 0)).2) (hX _ (b (f 0)).2 _ (b (f 1)).2)
      (hX _ (b (f 0)).2 _ (b (f 2)).2) (hX _ (b (f 1)).2 _ (b (f 1)).2)
      (hX _ (b (f 1)).2 _ (b (f 2)).2) (hX _ (b (f 2)).2 _ (b (f 2)).2)
    refine ⟨e, he, fun x hx j hj => ?_⟩
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · rw [he0]; exact hX _ hx _ (b (f 0)).2
    · rw [he1]; exact hX _ hx _ (b (f 1)).2
    · rw [he2]; exact hX _ hx _ (b (f 2)).2

theorem IsTotIso.finrank_le {X : Submodule F4 V} (hX : IsTotIso X) :
    Module.finrank F4 X ≤ 3 := by
  obtain ⟨g, hg⟩ := exists_le_smulSub_W0 hX
  calc Module.finrank F4 X ≤ Module.finrank F4 (smulSub g W0) := Submodule.finrank_mono hg
    _ = 3 := by rw [finrank_smulSub, finrank_W0]

theorem IsMaxIso.exists_eq_smulSub {W : Submodule F4 V} (hW : IsMaxIso W) :
    ∃ g : SU frobeniusF4 6, W = smulSub g W0 := by
  obtain ⟨g, hg⟩ := exists_le_smulSub_W0 hW.2
  exact ⟨g, Submodule.eq_of_le_of_finrank_eq hg (by rw [hW.1, finrank_smulSub, finrank_W0])⟩

theorem isMaxIso_iff_exists {W : Submodule F4 V} :
    IsMaxIso W ↔ ∃ g : SU frobeniusF4 6, W = smulSub g W0 :=
  ⟨IsMaxIso.exists_eq_smulSub, fun ⟨g, hg⟩ => hg ▸ isMaxIso_smulSub isMaxIso_W0 g⟩

theorem IsMaxIso.mem_of_herm {W : Submodule F4 V} (hW : IsMaxIso W) {v : V}
    (h : ∀ w ∈ W, herm v w = 0) : v ∈ W := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  exact mem_smulSub_W0_of_herm h

theorem exists_smulSub_W0_A0 {W A : Submodule F4 V} (hW : IsMaxIso W) (hAW : A ≤ W)
    (hA : Module.finrank F4 A = 2) :
    ∃ g : SU frobeniusF4 6, W = smulSub g W0 ∧ A = smulSub g A0 := by
  let b := Module.finBasisOfFinrankEq F4 A hA
  have hli := linearIndependent_coe_basis b
  have hlt : A < W := lt_of_le_of_ne hAW (fun h => by rw [h, hW.1] at hA; omega)
  obtain ⟨v₂, hv₂W, hv₂A⟩ := IsConcreteLE.exists_of_lt hlt
  have hbA : ∀ i, (b i : V) ∈ A := fun i => (b i).2
  have hli3 : LinearIndependent F4 ![(b 0 : V), (b 1 : V), v₂] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have hc2 : c 2 = 0 := by
      by_contra h2
      apply hv₂A
      have hv : v₂ = (c 2)⁻¹ • -(c 0 • (b 0 : V) + c 1 • (b 1 : V)) := by
        rw [← eq_neg_of_add_eq_zero_right hc, inv_smul_smul₀ h2]
      rw [hv]
      exact A.smul_mem _ (A.neg_mem (add_mem (A.smul_mem _ (hbA 0)) (A.smul_mem _ (hbA 1))))
    rw [hc2, zero_smul, add_zero] at hc
    have h01 := (Fintype.linearIndependent_iff.1 hli) ![c 0, c 1] (by
      simpa [Fin.sum_univ_two] using hc)
    intro i
    fin_cases i
    · exact h01 0
    · exact h01 1
    · exact hc2
  have hiso : ∀ x ∈ W, ∀ y ∈ W, herm x y = 0 := hW.2
  have h0 := hAW (hbA 0)
  have h1 := hAW (hbA 1)
  obtain ⟨e, he, he0, he1, he2⟩ := exists_frame_of_triple hli3 (hiso _ h0 _ h0)
    (hiso _ h0 _ h1) (hiso _ h0 _ hv₂W) (hiso _ h1 _ h1) (hiso _ h1 _ hv₂W)
    (hiso _ hv₂W _ hv₂W)
  obtain ⟨g, hg⟩ := exists_SU_lines_of_frame he
  have hgu : ∀ i : Fin 6, ∃ c : F4, c ≠ 0 ∧ g • u i = c • e i := fun i => by
    obtain ⟨c, hc0, hc⟩ := hg i
    exact ⟨c, hc0, by rw [smul_def, hc]⟩
  have hWle : W ≤ smulSub g W0 := by
    intro x hx
    rw [mem_smulSub_W0_iff]
    refine ⟨?_, ?_, ?_⟩ <;>
    · obtain ⟨c, -, hc⟩ := hgu _
      rw [hc, herm_smul_right]
      first
        | rw [he0, hiso _ hx _ h0, mul_zero]
        | rw [he1, hiso _ hx _ h1, mul_zero]
        | rw [he2, hiso _ hx _ hv₂W, mul_zero]
  have hWeq : W = smulSub g W0 :=
    Submodule.eq_of_le_of_finrank_eq hWle (by rw [hW.1, finrank_smulSub, finrank_W0])
  refine ⟨g, hWeq, ?_⟩
  have hle : smulSub g A0 ≤ A := by
    rw [smulSub, A0, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨c, -, hc⟩ := hgu (![0, 1] i)
    fin_cases i
    · change g • u 0 ∈ A
      have hc' : g • u 0 = c • e 0 := hc
      rw [hc', he0]
      exact A.smul_mem _ (hbA 0)
    · change g • u 1 ∈ A
      have hc' : g • u 1 = c • e 1 := hc
      rw [hc', he1]
      exact A.smul_mem _ (hbA 1)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_smulSub, finrank_A0, hA])).symm

theorem isClique_planePts {X : Submodule F4 V} (hX : IsTotIso X) :
    isoGraph.IsClique (planePts X) :=
  fun _ hp _ hq hpq => isoGraph_adj.2 ⟨hpq, hX _ hp _ hq⟩

theorem orth_rep_iff (p q : IsoPt) : Orth p.1 q.1 ↔ herm p.1.rep q.1.rep = 0 := Iff.rfl

theorem maximal_isClique_planePts {W : Submodule F4 V} (hW : IsMaxIso W) :
    Maximal isoGraph.IsClique (planePts W) := by
  refine ⟨isClique_planePts hW.2, fun T hT hWT q hq => ?_⟩
  by_contra hqW
  apply hqW
  refine hW.mem_of_herm fun w hw => ?_
  by_cases hw0 : w = 0
  · rw [hw0, herm_zero_right]
  have hwiso : herm w w = 0 := hW.2 w hw w hw
  have hpw : pt w hw0 hwiso ∈ planePts W := (pt_mem_planePts hw0 hwiso).2 hw
  have hne : q ≠ pt w hw0 hwiso := fun h => hqW (h ▸ hpw)
  have hadj := hT hq (hWT hpw) hne
  rw [isoGraph_adj] at hadj
  have := hadj.2
  rw [← pt_rep q, orth_pt] at this
  exact this

theorem maximal_isClique_iff (S : Set IsoPt) :
    Maximal isoGraph.IsClique S ↔ ∃ W : Submodule F4 V, IsMaxIso W ∧ S = planePts W := by
  constructor
  · intro hS
    set X := Submodule.span F4 ((fun p : IsoPt => p.1.rep) '' S) with hXdef
    have hX : IsTotIso X := by
      refine isTotIso_span ?_
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      by_cases hpq : p = q
      · rw [hpq]
        exact isIsoPt_of q
      · exact (isoGraph_adj.1 (hS.1 hp hq hpq)).2
    obtain ⟨g, hg⟩ := exists_le_smulSub_W0 hX
    have hWm := isMaxIso_smulSub isMaxIso_W0 g
    have hSW : S ⊆ planePts (smulSub g W0) := fun p hp =>
      hg (Submodule.subset_span ⟨p, hp, rfl⟩)
    exact ⟨_, hWm, le_antisymm hSW (hS.2 (isClique_planePts hWm.2) hSW)⟩
  · rintro ⟨W, hW, rfl⟩
    exact maximal_isClique_planePts hW

theorem card_W0_vec :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧ (v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0)} = 63 := by
  decide +kernel

theorem ncard_planePts_W0 : (planePts W0).ncard = 21 := by
  have h := card_vec_eq_three_mul (fun v : V => v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0)
    (fun c v hc => by simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or])
  rw [card_W0_vec] at h
  have e : planePts W0 = {p : IsoPt | p.1.rep 3 = 0 ∧ p.1.rep 4 = 0 ∧ p.1.rep 5 = 0} := by
    ext p
    exact mem_W0_iff
  rw [e, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  change Fintype.card {p : IsoPt // p.1.rep 3 = 0 ∧ p.1.rep 4 = 0 ∧ p.1.rep 5 = 0} = 21
  omega

theorem ncard_planePts_smulSub (g : SU frobeniusF4 6) (X : Submodule F4 V) :
    (planePts (smulSub g X)).ncard = (planePts X).ncard := by
  rw [planePts_smulSub]
  exact Set.ncard_image_of_injective _ (MulAction.injective g)

theorem IsMaxIso.ncard_planePts {W : Submodule F4 V} (hW : IsMaxIso W) :
    (planePts W).ncard = 21 := by
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  rw [ncard_planePts_smulSub, ncard_planePts_W0]

end CFSG.Monster.B.TwoA.Unitary.Clique
