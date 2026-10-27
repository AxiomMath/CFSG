module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.FS81.Realized
import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

private theorem Basis3.vec_zmod_smul {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (c : ZMod 3) (u : Coords k) : B.vec (c • u) = B.vec u ^ c.val := by
  rw [show c • u = c.val • u by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]]
  exact B.vec_nsmul c.val u

private noncomputable def Basis3.coordAddHom {k : ℕ} (u : Fin 3 → Coords k) :
    (Fin 3 → ZMod 3) →+ Coords k where
  toFun p := p 0 • u 0 + p 1 • u 1 + p 2 • u 2
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Pi.add_apply, add_smul]
    abel

private noncomputable def Basis3.coordHom {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (u : Fin 3 → Coords k) : Multiplicative (Fin 3 → ZMod 3) →* G :=
  B.span.subtype.comp (B.equiv.toMonoidHom.comp (Basis3.coordAddHom u).toMultiplicative)

private theorem Basis3.coordAddHom_single {k : ℕ} (u : Fin 3 → Coords k) (i : Fin 3) :
    Basis3.coordAddHom u (Pi.single i 1) = u i := by
  fin_cases i <;>
    simp [Basis3.coordAddHom]

private theorem Basis3.coordHom_apply {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (u : Fin 3 → Coords k) (p : Multiplicative (Fin 3 → ZMod 3)) :
    B.coordHom u p = B.vec (Basis3.coordAddHom u (Multiplicative.toAdd p)) := rfl

private abbrev e7Coord : Fin 3 → Coords 8 :=
  ![Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1, Pi.single 4 1 + Pi.single 5 1,
    Pi.single 6 1 + Pi.single 7 1]

private abbrev twCoord : Fin 3 → Coords 8 :=
  ![Pi.single 2 1, Pi.single 3 1, Pi.single 4 1 + Pi.single 5 1]

private theorem Basis3.range_coordHom {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (u : Fin 3 → Coords k) :
    (B.coordHom u).range = Subgroup.closure {B.vec (u 0), B.vec (u 1), B.vec (u 2)} := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    rw [Basis3.coordHom_apply]
    rw [show Basis3.coordAddHom u (Multiplicative.toAdd p) =
        Multiplicative.toAdd p 0 • u 0 + Multiplicative.toAdd p 1 • u 1 +
          Multiplicative.toAdd p 2 • u 2 from rfl]
    rw [B.vec_add, B.vec_add, Basis3.vec_zmod_smul, Basis3.vec_zmod_smul, Basis3.vec_zmod_smul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨Multiplicative.ofAdd (Pi.single 0 1), by
        rw [Basis3.coordHom_apply, B.vec_injective.eq_iff]
        exact Basis3.coordAddHom_single u 0⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 1 1), by
        rw [Basis3.coordHom_apply, B.vec_injective.eq_iff]
        exact Basis3.coordAddHom_single u 1⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 2 1), by
        rw [Basis3.coordHom_apply, B.vec_injective.eq_iff]
        exact Basis3.coordAddHom_single u 2⟩

private theorem Basis3.card_range_coordHom {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    (u : Fin 3 → Coords k) (hinj : Function.Injective (B.coordHom u)) :
    Nat.card (B.coordHom u).range = 27 := by
  calc Nat.card ↥(B.coordHom u).range
      = Nat.card (Multiplicative (Fin 3 → ZMod 3)) :=
        (Nat.card_congr (Equiv.ofInjective (B.coordHom u) hinj)).symm
    _ = 27 := by
        rw [Nat.card_eq_fintype_card]
        change Fintype.card (Fin 3 → ZMod 3) = 27
        rw [Fintype.card_fun]
        norm_num [ZMod.card]

private theorem Basis3.vec_e7Coord {G : Type} [Group G] (B : Basis3 G 8) :
    B.vec (e7Coord 0) = B.b 1 * B.b 2 * B.b 3 := by
  rw [show e7Coord 0 = Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 by simp [e7Coord]]
  rw [B.vec_add, B.vec_add, B.vec_single, B.vec_single, B.vec_single]

private theorem Basis3.vec_e7Coord1 {G : Type} [Group G] (B : Basis3 G 8) :
    B.vec (e7Coord 1) = B.b 4 * B.b 5 := by
  rw [show e7Coord 1 = Pi.single 4 1 + Pi.single 5 1 by simp [e7Coord]]
  rw [B.vec_add, B.vec_single, B.vec_single]

private theorem Basis3.vec_e7Coord2 {G : Type} [Group G] (B : Basis3 G 8) :
    B.vec (e7Coord 2) = B.b 6 * B.b 7 := by
  rw [show e7Coord 2 = Pi.single 6 1 + Pi.single 7 1 by simp [e7Coord]]
  rw [B.vec_add, B.vec_single, B.vec_single]

private theorem Basis3.vec_twCoord0 {G : Type} [Group G] (B : Basis3 G 8) :
    B.vec (twCoord 0) = B.b 2 := by
  rw [show twCoord 0 = Pi.single 2 1 by simp [twCoord]]
  rw [B.vec_single]

private theorem Basis3.vec_twCoord1 {G : Type} [Group G] (B : Basis3 G 8) :
    B.vec (twCoord 1) = B.b 3 := by
  rw [show twCoord 1 = Pi.single 3 1 by simp [twCoord]]
  rw [B.vec_single]

private theorem Basis3.vec_twCoord2 {G : Type} [Group G] (B : Basis3 G 8) :
    B.vec (twCoord 2) = B.b 4 * B.b 5 := by
  rw [show twCoord 2 = Pi.single 4 1 + Pi.single 5 1 by simp [twCoord]]
  rw [B.vec_add, B.vec_single, B.vec_single]

private theorem e7Coord_injective {G : Type} [Group G] (B : Basis3 G 8) :
    Function.Injective (B.coordHom e7Coord) := by
  intro p q h
  have hc : Basis3.coordAddHom e7Coord (Multiplicative.toAdd p) =
      Basis3.coordAddHom e7Coord (Multiplicative.toAdd q) := by
    apply B.vec_injective
    rw [Basis3.coordHom_apply, Basis3.coordHom_apply] at h
    exact h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · have := congrFun hc 1
    simpa [Basis3.coordAddHom, e7Coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using this
  · have := congrFun hc 4
    simpa [Basis3.coordAddHom, e7Coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using this
  · have := congrFun hc 6
    simpa [Basis3.coordAddHom, e7Coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using this

private theorem twCoord_injective {G : Type} [Group G] (B : Basis3 G 8) :
    Function.Injective (B.coordHom twCoord) := by
  intro p q h
  have hc : Basis3.coordAddHom twCoord (Multiplicative.toAdd p) =
      Basis3.coordAddHom twCoord (Multiplicative.toAdd q) := by
    apply B.vec_injective
    rw [Basis3.coordHom_apply, Basis3.coordHom_apply] at h
    exact h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · have := congrFun hc 2
    simpa [Basis3.coordAddHom, twCoord, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using this
  · have := congrFun hc 3
    simpa [Basis3.coordAddHom, twCoord, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using this
  · have := congrFun hc 4
    simpa [Basis3.coordAddHom, twCoord, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using this

private abbrev goodE7 (x : Coords 3) : Prop :=
  (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0) ∨ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1) ∨
    (x 0 = 1 ∧ x 1 ≠ 0 ∧ x 2 ≠ 0)

private abbrev goodTw (x : Coords 3) : Prop :=
  (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 0) ∨ (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0) ∨
    (x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 2 = 1)

private theorem goodE7_ne_zero {x : Coords 3} (hx : goodE7 x) : x ≠ 0 := by
  rintro h
  rcases hx with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> simp_all

private theorem goodTw_ne_zero {x : Coords 3} (hx : goodTw x) : x ≠ 0 := by
  rintro h
  rcases hx with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> simp_all

private theorem goodE7_of_nontriv : ∀ v w : Coords 3, v ≠ 0 →
    (∀ a : ZMod 3, a • v ≠ w) → ∃ a b : ZMod 3, goodE7 (a • v + b • w) := by
  decide +kernel

private theorem goodTw_of_nontriv : ∀ v w : Coords 3, v ≠ 0 →
    (∀ a : ZMod 3, a • v ≠ w) → ∃ a b : ZMod 3, goodTw (a • v + b • w) := by
  decide +kernel

private noncomputable abbrev e7E (x : Coords 3) : Coords 8 :=
  Basis3.coordAddHom e7Coord x

private noncomputable abbrev twE (x : Coords 3) : Coords 8 :=
  Basis3.coordAddHom twCoord x

private theorem recOutE7_of_goodE7 : ∀ x : Coords 3, goodE7 x →
    (wt (e7E x) = 1 ∧ (e7E x 0 ≠ 0 ∨ e7E x 1 ≠ 0)) ∨
    (wt (e7E x) = 2 ∧ e7E x 0 = 0 ∧ e7E x 1 = 0) ∨
    (wt (e7E x) = 3 ∧ e7E x 0 ≠ 0 ∧ e7E x 1 ≠ 0) ∨
    (wt (e7E x) = 7 ∧ e7E x 0 = 0 ∧ ∏ i : Fin 6, e7E x i.succ.succ = 1) ∨
    (wt (e7E x) = 7 ∧ e7E x 1 = 0 ∧ ∏ i : Fin 6, e7E x i.succ.succ = -1) := by
  decide +kernel

private theorem recOutTw_of_goodTw : ∀ x : Coords 3, goodTw x →
    wt (twE x) = 1 ∨ wt (twE x) = 4 ∨ wt (twE x) = 7 := by
  decide +kernel

private theorem addOrderOf_eq_three {v : Coords 3} (hv : v ≠ 0) : addOrderOf v = 3 := by
  apply addOrderOf_eq_prime (p := 3)
  · rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3 v, ZMod.natCast_self, zero_smul]
  · simpa using hv

private theorem exists_nontriv_of_card_nine (F : AddSubgroup (Coords 3))
    (hF : Nat.card F = 9) :
    ∃ v ∈ F, v ≠ 0 ∧ ∃ w ∈ F, ∀ a : ZMod 3, a • v ≠ w := by
  have hnt : Nontrivial ↥F :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hF]; norm_num)
  obtain ⟨v, hvne⟩ := @exists_ne ↥F hnt 0
  have hvne' : (v : Coords 3) ≠ 0 := by simpa using hvne
  have hcl : Nat.card (AddSubgroup.closure ({(v : Coords 3)} : Set (Coords 3))) = 3 := by
    rw [← AddSubgroup.zmultiples_eq_closure, Nat.card_zmultiples]
    exact addOrderOf_eq_three hvne'
  have hnotle : ¬ F ≤ AddSubgroup.closure ({(v : Coords 3)} : Set (Coords 3)) := by
    intro hle
    have hlecard : Nat.card ↥F ≤
        Nat.card ↥(AddSubgroup.closure ({(v : Coords 3)} : Set (Coords 3))) :=
      Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)
    rw [hF, hcl] at hlecard
    omega
  obtain ⟨w, hwF, hwcl⟩ := SetLike.not_le_iff_exists.mp hnotle
  refine ⟨v, v.2, hvne', w, hwF, ?_⟩
  intro a ha
  apply hwcl
  rw [← ha]
  rw [show a • (v : Coords 3) = a.val • (v : Coords 3) by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_singleton (v : Coords 3)))
    a.val

private theorem isElemAbelian_span {G : Type} [Group G] {k : ℕ} (B : Basis3 G k) :
    IsElemAbelian 3 B.span := by
  rw [Basis3.span]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    exact (B.comm i j).eq
  · rintro a ⟨i, rfl⟩
    rw [← B.ord i]
    exact pow_orderOf_eq_one (B.b i)

theorem isElemAbelian_s79A {G : Type} [Group G] {r : Row} (B : Basis3 G (r.n + 1)) :
    IsElemAbelian 3 (s79A r B) := by
  have hspan := isElemAbelian_span B
  cases r with
  | D6 =>
      show IsElemAbelian 3 (s79A Row.D6 B)
      simp only [s79A]
      exact hspan.mono bot_le
  | twD7 =>
      show IsElemAbelian 3 (s79A Row.twD7 B)
      simp only [s79A]
      refine hspan.mono ((Subgroup.closure_le _).mpr ?_)
      rintro x (rfl | rfl | rfl)
      · exact B.b_mem_span 2
      · exact B.b_mem_span 3
      · exact B.span.mul_mem (B.b_mem_span 4) (B.b_mem_span 5)
  | E7 =>
      show IsElemAbelian 3 (s79A Row.E7 B)
      simp only [s79A]
      refine hspan.mono ((Subgroup.closure_le _).mpr ?_)
      rintro x (rfl | rfl | rfl)
      · exact B.span.mul_mem (B.span.mul_mem (B.b_mem_span 1) (B.b_mem_span 2))
          (B.b_mem_span 3)
      · exact B.span.mul_mem (B.b_mem_span 4) (B.b_mem_span 5)
      · exact B.span.mul_mem (B.b_mem_span 6) (B.b_mem_span 7)

private theorem card_s79A_e7 {G : Type} [Group G] [Finite G] (B : Basis3 G 8) :
    Nat.card (s79A Row.E7 B) = 27 := by
  have hrange : (B.coordHom e7Coord).range = s79A Row.E7 B := by
    show (B.coordHom e7Coord).range =
      Subgroup.closure ({B.b 1 * B.b 2 * B.b 3, B.b 4 * B.b 5, B.b 6 * B.b 7} : Set G)
    rw [Basis3.range_coordHom, Basis3.vec_e7Coord, Basis3.vec_e7Coord1, Basis3.vec_e7Coord2]
  rw [← hrange]
  exact Basis3.card_range_coordHom B e7Coord (e7Coord_injective B)

private theorem card_s79A_twD7 {G : Type} [Group G] [Finite G] (B : Basis3 G 8) :
    Nat.card (s79A Row.twD7 B) = 27 := by
  have hrange : (B.coordHom twCoord).range = s79A Row.twD7 B := by
    show (B.coordHom twCoord).range =
      Subgroup.closure ({B.b 2, B.b 3, B.b 4 * B.b 5} : Set G)
    rw [Basis3.range_coordHom, Basis3.vec_twCoord0, Basis3.vec_twCoord1, Basis3.vec_twCoord2]
  rw [← hrange]
  exact Basis3.card_range_coordHom B twCoord (twCoord_injective B)

theorem card_s79A {G : Type} [Group G] [Finite G] {r : Row} (hr : r ≠ Row.D6)
    (B : Basis3 G (r.n + 1)) : Nat.card (s79A r B) = 27 := by
  cases r with
  | D6 => exact absurd rfl hr
  | twD7 => exact card_s79A_twD7 B
  | E7 => exact card_s79A_e7 B

private theorem exists_conj_mem_of_le_s79A_e7 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E Y : Subgroup G} {B : Basis3 G 8}
    (h : RootSetting Row.E7 b₀ K E B Y)
    (hcard : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)) {F : Subgroup G}
    (hF : F ≤ s79A Row.E7 B) (hF9 : Nat.card F = 9) : ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F := by
  have hrange : (B.coordHom e7Coord).range = s79A Row.E7 B := by
    show (B.coordHom e7Coord).range =
      Subgroup.closure ({B.b 1 * B.b 2 * B.b 3, B.b 4 * B.b 5, B.b 6 * B.b 7} : Set G)
    rw [Basis3.range_coordHom, Basis3.vec_e7Coord, Basis3.vec_e7Coord1, Basis3.vec_e7Coord2]
  have hφinj : Function.Injective (B.coordHom e7Coord) := e7Coord_injective B
  have hFrange : F ≤ (B.coordHom e7Coord).range := hF.trans hrange.ge
  let F3 : Subgroup (Multiplicative (Fin 3 → ZMod 3)) := F.comap (B.coordHom e7Coord)
  have hF3card : Nat.card F3 = 9 := by
    rw [← Subgroup.card_map_of_injective (f := B.coordHom e7Coord) hφinj]
    rw [Subgroup.map_comap_eq_self hFrange]
    exact hF9
  let Fadd : AddSubgroup (Coords 3) := Subgroup.toAddSubgroup' F3
  have hFaddcard : Nat.card Fadd = 9 := by
    change Nat.card F3 = 9
    exact hF3card
  obtain ⟨v, hvFadd, hvne, w, hwFadd, hwline⟩ := exists_nontriv_of_card_nine Fadd hFaddcard
  obtain ⟨a, b, hgood⟩ := goodE7_of_nontriv v w hvne hwline
  have hvF : B.coordHom e7Coord (Multiplicative.ofAdd v) ∈ F := by
    have : Multiplicative.ofAdd v ∈ F3 := (Subgroup.mem_toAddSubgroup' F3 v).mp hvFadd
    exact Subgroup.mem_comap.mp this
  have hwF : B.coordHom e7Coord (Multiplicative.ofAdd w) ∈ F := by
    have : Multiplicative.ofAdd w ∈ F3 := (Subgroup.mem_toAddSubgroup' F3 w).mp hwFadd
    exact Subgroup.mem_comap.mp this
  let x : Coords 3 := a • v + b • w
  have hxgood : goodE7 x := hgood
  have hxmem : B.coordHom e7Coord (Multiplicative.ofAdd x) ∈ F := by
    have hpowa : (B.coordHom e7Coord (Multiplicative.ofAdd v)) ^ a.val ∈ F :=
      F.pow_mem hvF _
    have hpowb : (B.coordHom e7Coord (Multiplicative.ofAdd w)) ^ b.val ∈ F :=
      F.pow_mem hwF _
    have hxdecomp : Multiplicative.ofAdd x =
        Multiplicative.ofAdd (a • v) * Multiplicative.ofAdd (b • w) := by
      rw [show x = a • v + b • w from rfl, ofAdd_add]
    rw [hxdecomp,
      show Multiplicative.ofAdd (a • v) = (Multiplicative.ofAdd v) ^ a.val from by
        rw [show a • v = a.val • v by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val],
          ofAdd_nsmul],
      show Multiplicative.ofAdd (b • w) = (Multiplicative.ofAdd w) ^ b.val from by
        rw [show b • w = b.val • w by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val],
          ofAdd_nsmul],
      map_mul, map_pow, map_pow]
    exact F.mul_mem hpowa hpowb
  let e : Coords 8 := e7E x
  have hvece : B.vec e ∈ F := by
    have := hxmem
    rw [Basis3.coordHom_apply] at this
    simpa [e, e7E] using this
  have hline : B.line e ≤ F := by
    rw [Basis3.line]
    exact Subgroup.zpowers_le.mpr hvece
  have hlinj : Function.Injective (Basis3.coordAddHom e7Coord) := by
    intro p q hpq
    have : Multiplicative.ofAdd p = Multiplicative.ofAdd q := by
      apply hφinj
      rw [Basis3.coordHom_apply, Basis3.coordHom_apply]
      exact congrArg B.vec hpq
    exact Multiplicative.ofAdd.injective this
  have hxne : x ≠ 0 := goodE7_ne_zero hxgood
  have he : e ≠ 0 := by
    intro he0
    apply hxne
    apply hlinj
    rw [map_zero]
    simpa [e, e7E] using he0
  have hshape := recOutE7_of_goodE7 x hxgood
  have hconj : IsConjLine b₀ (B.line e) := (h.recOut.2.1 e he).mpr hshape
  have hcard' : Nat.card (ggAutomizer Y B.span) = Nat.card (ggAutomizer ⊤ B.span) := by
    have hspanE : B.span = E := h.adapted.1
    rw [hspanE]
    exact hcard
  have hb₀ : b₀ ∈ B.span := by
    have hb0 : B.b 0 = b₀ := h.adapted.2.1
    rw [← hb0]
    exact B.b_mem_span 0
  obtain ⟨y, hyY, hy⟩ := exists_zpowers_conj_Y_of_isConjLine B hb₀ h.fus hcard' hconj
  refine ⟨y, hyY, ?_⟩
  have hmem : y * b₀ * y⁻¹ ∈ Subgroup.zpowers (y * b₀ * y⁻¹) := Subgroup.mem_zpowers _
  rw [hy] at hmem
  exact hline hmem

private theorem exists_conj_mem_of_le_s79A_twD7 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E Y : Subgroup G} {B : Basis3 G 8}
    (h : RootSetting Row.twD7 b₀ K E B Y)
    (hcard : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)) {F : Subgroup G}
    (hF : F ≤ s79A Row.twD7 B) (hF9 : Nat.card F = 9) : ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F := by
  have hrange : (B.coordHom twCoord).range = s79A Row.twD7 B := by
    show (B.coordHom twCoord).range = Subgroup.closure ({B.b 2, B.b 3, B.b 4 * B.b 5} : Set G)
    rw [Basis3.range_coordHom, Basis3.vec_twCoord0, Basis3.vec_twCoord1, Basis3.vec_twCoord2]
  have hφinj : Function.Injective (B.coordHom twCoord) := twCoord_injective B
  have hFrange : F ≤ (B.coordHom twCoord).range := hF.trans hrange.ge
  let F3 : Subgroup (Multiplicative (Fin 3 → ZMod 3)) := F.comap (B.coordHom twCoord)
  have hF3card : Nat.card F3 = 9 := by
    rw [← Subgroup.card_map_of_injective (f := B.coordHom twCoord) hφinj]
    rw [Subgroup.map_comap_eq_self hFrange]
    exact hF9
  let Fadd : AddSubgroup (Coords 3) := Subgroup.toAddSubgroup' F3
  have hFaddcard : Nat.card Fadd = 9 := by
    change Nat.card F3 = 9
    exact hF3card
  obtain ⟨v, hvFadd, hvne, w, hwFadd, hwline⟩ := exists_nontriv_of_card_nine Fadd hFaddcard
  obtain ⟨a, b, hgood⟩ := goodTw_of_nontriv v w hvne hwline
  have hvF : B.coordHom twCoord (Multiplicative.ofAdd v) ∈ F := by
    have : Multiplicative.ofAdd v ∈ F3 := (Subgroup.mem_toAddSubgroup' F3 v).mp hvFadd
    exact Subgroup.mem_comap.mp this
  have hwF : B.coordHom twCoord (Multiplicative.ofAdd w) ∈ F := by
    have : Multiplicative.ofAdd w ∈ F3 := (Subgroup.mem_toAddSubgroup' F3 w).mp hwFadd
    exact Subgroup.mem_comap.mp this
  let x : Coords 3 := a • v + b • w
  have hxgood : goodTw x := hgood
  have hxmem : B.coordHom twCoord (Multiplicative.ofAdd x) ∈ F := by
    have hpowa : (B.coordHom twCoord (Multiplicative.ofAdd v)) ^ a.val ∈ F :=
      F.pow_mem hvF _
    have hpowb : (B.coordHom twCoord (Multiplicative.ofAdd w)) ^ b.val ∈ F :=
      F.pow_mem hwF _
    have hxdecomp : Multiplicative.ofAdd x =
        Multiplicative.ofAdd (a • v) * Multiplicative.ofAdd (b • w) := by
      rw [show x = a • v + b • w from rfl, ofAdd_add]
    rw [hxdecomp,
      show Multiplicative.ofAdd (a • v) = (Multiplicative.ofAdd v) ^ a.val from by
        rw [show a • v = a.val • v by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val],
          ofAdd_nsmul],
      show Multiplicative.ofAdd (b • w) = (Multiplicative.ofAdd w) ^ b.val from by
        rw [show b • w = b.val • w by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val],
          ofAdd_nsmul],
      map_mul, map_pow, map_pow]
    exact F.mul_mem hpowa hpowb
  let e : Coords 8 := twE x
  have hvece : B.vec e ∈ F := by
    have := hxmem
    rw [Basis3.coordHom_apply] at this
    simpa [e, twE] using this
  have hline : B.line e ≤ F := by
    rw [Basis3.line]
    exact Subgroup.zpowers_le.mpr hvece
  have hlinj : Function.Injective (Basis3.coordAddHom twCoord) := by
    intro p q hpq
    have : Multiplicative.ofAdd p = Multiplicative.ofAdd q := by
      apply hφinj
      rw [Basis3.coordHom_apply, Basis3.coordHom_apply]
      exact congrArg B.vec hpq
    exact Multiplicative.ofAdd.injective this
  have hxne : x ≠ 0 := goodTw_ne_zero hxgood
  have he : e ≠ 0 := by
    intro he0
    apply hxne
    apply hlinj
    rw [map_zero]
    simpa [e, twE] using he0
  have hshape := recOutTw_of_goodTw x hxgood
  have hconj : IsConjLine b₀ (B.line e) := (h.recOut.2.1 e he).mpr hshape
  have hcard' : Nat.card (ggAutomizer Y B.span) = Nat.card (ggAutomizer ⊤ B.span) := by
    have hspanE : B.span = E := h.adapted.1
    rw [hspanE]
    exact hcard
  have hb₀ : b₀ ∈ B.span := by
    have hb0 : B.b 0 = b₀ := h.adapted.2.1
    rw [← hb0]
    exact B.b_mem_span 0
  obtain ⟨y, hyY, hy⟩ := exists_zpowers_conj_Y_of_isConjLine B hb₀ h.fus hcard' hconj
  refine ⟨y, hyY, ?_⟩
  have hmem : y * b₀ * y⁻¹ ∈ Subgroup.zpowers (y * b₀ * y⁻¹) := Subgroup.mem_zpowers _
  rw [hy] at hmem
  exact hline hmem

theorem RootSetting.exists_conj_mem_of_le_s79A {G : Type} [Group G] [Finite G] {r : Row}
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G}
    (h : RootSetting r b₀ K E B Y) (hr : r ≠ Row.D6)
    (hcard : Nat.card ↥(ggAutomizer Y E) = Nat.card ↥(ggAutomizer ⊤ E)) {F : Subgroup G}
    (hF : F ≤ s79A r B) (hF9 : Nat.card F = 9) : ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ F := by
  cases r with
  | D6 => exact absurd rfl hr
  | twD7 => exact exists_conj_mem_of_le_s79A_twD7 h hcard hF hF9
  | E7 => exact exists_conj_mem_of_le_s79A_e7 h hcard hF hF9

end CFSG.StandardType.FrameRoute.FS81
