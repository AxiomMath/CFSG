module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeTenCoreA
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTen_absIrred_on_span {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2) (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j)
    (hker : ∀ v ∈ Submodule.span (ZMod 3) (Set.range h), (∀ i, α i v = 0) → v = 0)
    (hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) (Set.range h), g w ∈ Submodule.span (ZMod 3) (Set.range h)) :
    ZS.AbsIrred 3 (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range := by
  let T : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hmemT : ∀ i, h i ∈ T := fun i => Submodule.subset_span (Set.mem_range_self i)
  let h' : ι → T := fun i => ⟨h i, hmemT i⟩
  let α' : ι → Module.Dual (ZMod 3) T := fun i => (α i).comp T.subtype
  let rA : ι → ↥A := fun i => ⟨r i, hA.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)⟩
  let r' : ι → (T ≃ₗ[ZMod 3] T) := fun i => ZS.restrictHom A T hinv (rA i)
  have hr' : ∀ i v, r' i v = v - α' i v • h' i := by
    intro i v
    apply Subtype.ext
    simpa [r', rA, α', h', ZS.restrictHom_apply] using hr i (v : V)
  have hα' : ∀ i, α' i (h' i) = 2 := fun i => by simpa [α', h'] using hα i
  have hspan' : Submodule.span (ZMod 3) (Set.range h') = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have key : ∀ y : V, ∀ hy : y ∈ T,
        (⟨y, hy⟩ : T) ∈ Submodule.span (ZMod 3) (Set.range h') := by
      intro y hy
      change y ∈ Submodule.span (ZMod 3) (Set.range h) at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          simpa [h'] using Submodule.subset_span (Set.mem_range_self i)
      | zero => exact Submodule.zero_mem _
      | add a b ha hb iha ihb => simpa using Submodule.add_mem _ iha ihb
      | smul c a ha iha => simpa using Submodule.smul_mem _ c iha
    exact key x.val x.2
  have hker' : ∀ w : T, (∀ i, α' i w = 0) → w = 0 := by
    intro w hw
    apply Subtype.ext
    exact hker (w : V) (by simpa [T] using w.2) fun i => hw i
  have hconn' : ∀ i j, Relation.ReflTransGen
      (fun a b => α' a (h' b) ≠ 0 ∧ α' b (h' a) ≠ 0) i j := by
    intro i j
    exact hconn i j
  have hrange : (ZS.restrictHom A T hinv).range = Subgroup.closure (Set.range r') := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      have key : ∀ y (hy : y ∈ Subgroup.closure (Set.range r)),
          ZS.restrictHom A T hinv (⟨y, hA.symm ▸ hy⟩ : ↥A) ∈ Subgroup.closure (Set.range r') := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem z hz =>
            obtain ⟨i, rfl⟩ := hz
            have he : (⟨r i, hA.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)⟩ : ↥A) =
                rA i := Subtype.ext rfl
            rw [he]
            change r' i ∈ Subgroup.closure (Set.range r')
            exact Subgroup.subset_closure ⟨i, rfl⟩
        | one =>
            have he : (⟨1, hA.symm ▸ Subgroup.one_mem (Subgroup.closure (Set.range r))⟩ : ↥A) =
                (1 : ↥A) := Subtype.ext rfl
            rw [he, map_one]
            exact Subgroup.one_mem _
        | mul x y hx hy ihx ihy =>
            have he : (⟨x * y, hA.symm ▸ Subgroup.mul_mem _ hx hy⟩ : ↥A) =
                (⟨x, hA.symm ▸ hx⟩ : ↥A) * ⟨y, hA.symm ▸ hy⟩ := Subtype.ext rfl
            rw [he, map_mul]
            exact Subgroup.mul_mem _ ihx ihy
        | inv x hx ihx =>
            have he : (⟨x⁻¹, hA.symm ▸ Subgroup.inv_mem _ hx⟩ : ↥A) =
                (⟨x, hA.symm ▸ hx⟩ : ↥A)⁻¹ := Subtype.ext rfl
            rw [he, map_inv]
            exact Subgroup.inv_mem _ ihx
      have hkey := key a.val (hA ▸ a.2)
      simpa using hkey
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨i, rfl⟩
      exact ⟨rA i, rfl⟩
  exact ggRC_absIrred_of_connected (p := 3) (by decide) r' h' α' hr' hα' hspan' hker' hconn'
    (ZS.restrictHom A T hinv).range hrange

theorem ggTen_absIrred {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2) (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j)
    (hker : ∀ v, (∀ i, α i v = 0) → v = 0)
    (hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) (Set.range h), g w ∈ Submodule.span (ZMod 3) (Set.range h)) :
    ZS.AbsIrred 3 (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range :=
  ggTen_absIrred_on_span h α hα r hr A hA hconn
    (fun v _ hv => hker v hv) hinv

private lemma tenCoreBAux_refl_of_hr
    {p : ℕ} [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (h : W) (α : Module.Dual (ZMod p) W) (hα : α h = 2) (h2 : (2 : ZMod p) ≠ 0)
    (r : W ≃ₗ[ZMod p] W) (hr : ∀ v, r v = v - α v • h) :
    GGLinRefl r := by
  have hh : h ≠ 0 := by
    intro h0
    have hzero : α h = 0 := by rw [h0, map_zero]
    rw [hα] at hzero
    exact h2 hzero
  constructor
  · ext v
    rw [LinearEquiv.mul_apply, hr (r v), hr v]
    have hαr : α (v - α v • h) = -α v := by
      rw [map_sub, map_smul, hα, smul_eq_mul]
      ring
    rw [hαr, neg_smul]
    abel
  · have hmove : ggLinMove r = Submodule.span (ZMod p) {h} := by
      apply le_antisymm
      · rintro w ⟨v, rfl⟩
        have hr' : (r : W →ₗ[ZMod p] W) v = v - α v • h := hr v
        have hw : ((r : W →ₗ[ZMod p] W) - (LinearMap.id : W →ₗ[ZMod p] W)) v = -(α v) • h := by
          rw [LinearMap.sub_apply, LinearMap.id_apply, hr', sub_sub_cancel_left, neg_smul]
        rw [hw]
        exact Submodule.smul_mem (Submodule.span (ZMod p) {h}) (-(α v))
          (Submodule.mem_span_singleton_self h)
      · rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        have hαc : α (-((2 : ZMod p)⁻¹) • h) = -1 := by
          rw [map_smul, hα, smul_eq_mul, neg_mul, inv_mul_cancel₀ h2]
        have hr' : (r : W →ₗ[ZMod p] W) (-((2 : ZMod p)⁻¹) • h) =
            -((2 : ZMod p)⁻¹) • h - α (-((2 : ZMod p)⁻¹) • h) • h := hr _
        refine ⟨-((2 : ZMod p)⁻¹) • h, ?_⟩
        rw [LinearMap.sub_apply, LinearMap.id_apply, hr', hαc, sub_sub_cancel_left]
        simp
    rw [hmove]
    exact finrank_span_singleton hh

theorem ggTen_Q_reflGen {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2) (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) (Set.range h), g w ∈ Submodule.span (ZMod 3) (Set.range h)) :
    (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range =
      Subgroup.closure {s | s ∈ (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range ∧
        GGLinRefl s} := by
  let T : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hmemT : ∀ i, h i ∈ T := fun i => Submodule.subset_span (Set.mem_range_self i)
  let h' : ι → T := fun i => ⟨h i, hmemT i⟩
  let α' : ι → Module.Dual (ZMod 3) T := fun i => (α i).comp T.subtype
  let rA : ι → ↥A := fun i => ⟨r i, hA.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)⟩
  let r' : ι → (T ≃ₗ[ZMod 3] T) := fun i => ZS.restrictHom A T hinv (rA i)
  have hr' : ∀ i v, r' i v = v - α' i v • h' i := by
    intro i v
    apply Subtype.ext
    simpa [r', rA, α', h', ZS.restrictHom_apply] using hr i (v : V)
  have hα' : ∀ i, α' i (h' i) = 2 := fun i => by simpa [α', h'] using hα i
  have hrefl : ∀ i, GGLinRefl (r' i) :=
    fun i => tenCoreBAux_refl_of_hr (h' i) (α' i) (hα' i) (by decide) (r' i) (hr' i)
  have hgen : (ZS.restrictHom A T hinv).range = Subgroup.closure (Set.range r') := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      have key : ∀ y (hy : y ∈ Subgroup.closure (Set.range r)),
          ZS.restrictHom A T hinv (⟨y, hA.symm ▸ hy⟩ : ↥A) ∈ Subgroup.closure (Set.range r') := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem z hz =>
            obtain ⟨i, rfl⟩ := hz
            have he : (⟨r i, hA.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)⟩ : ↥A) =
                rA i := Subtype.ext rfl
            rw [he]
            change r' i ∈ Subgroup.closure (Set.range r')
            exact Subgroup.subset_closure ⟨i, rfl⟩
        | one =>
            have he : (⟨1, hA.symm ▸ Subgroup.one_mem (Subgroup.closure (Set.range r))⟩ : ↥A) =
                (1 : ↥A) := Subtype.ext rfl
            rw [he, map_one]
            exact Subgroup.one_mem _
        | mul x y hx hy ihx ihy =>
            have he : (⟨x * y, hA.symm ▸ Subgroup.mul_mem _ hx hy⟩ : ↥A) =
                (⟨x, hA.symm ▸ hx⟩ : ↥A) * ⟨y, hA.symm ▸ hy⟩ := Subtype.ext rfl
            rw [he, map_mul]
            exact Subgroup.mul_mem _ ihx ihy
        | inv x hx ihx =>
            have he : (⟨x⁻¹, hA.symm ▸ Subgroup.inv_mem _ hx⟩ : ↥A) =
                (⟨x, hA.symm ▸ hx⟩ : ↥A)⁻¹ := Subtype.ext rfl
            rw [he, map_inv]
            exact Subgroup.inv_mem _ ihx
      have hkey := key a.val (hA ▸ a.2)
      simpa using hkey
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨i, rfl⟩
      exact ⟨rA i, rfl⟩
  change (ZS.restrictHom A T hinv).range =
    Subgroup.closure {s | s ∈ (ZS.restrictHom A T hinv).range ∧ GGLinRefl s}
  rw [hgen]
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro s ⟨i, rfl⟩
    exact ⟨Subgroup.subset_closure ⟨i, rfl⟩, hrefl i⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro s ⟨hs, _⟩
    exact hs

private lemma tenCoreBAux_apply_eq_neg_of_mem_move
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (a : V ≃ₗ[ZMod p] V) (ha : a * a = 1) {w : V} (hw : w ∈ ggLinMove a) :
    (a : V →ₗ[ZMod p] V) w = -w := by
  rcases hw with ⟨v, hv⟩
  rw [← hv]
  have hφφ : (a : V →ₗ[ZMod p] V) ((a : V →ₗ[ZMod p] V) v) = v := by
    have h : (a * a) v = (1 : V ≃ₗ[ZMod p] V) v := congrArg (fun e => e v) ha
    rw [LinearEquiv.mul_apply] at h
    simpa using h
  change (a : V →ₗ[ZMod p] V) ((((a : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)) v) =
    -((((a : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)) v)
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hφφ, neg_sub]

private lemma tenCoreBAux_finrank_move_restrictHom_eq
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (A : Subgroup (V ≃ₗ[ZMod p] V)) (W : Submodule (ZMod p) V)
    (hW : ∀ g ∈ A, ∀ w ∈ W, g w ∈ W)
    (a : ↥A) (ha : (a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V) = 1)
    (hmove : ggLinMove (a : V ≃ₗ[ZMod p] V) ≤ W) :
    Module.finrank (ZMod p) (ggLinMove (ZS.restrictHom A W hW a)) =
      Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) := by
  have hprime : p.Prime := Fact.out
  have hpgt : 2 < p := lt_of_le_of_ne hprime.two_le (Ne.symm hp2)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    exact Nat.not_dvd_of_pos_of_lt (by norm_num) hpgt hdvd
  have hneg2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2
  have hcomp :
      W.subtype.comp ((ZS.restrictHom A W hW a).toLinearMap - LinearMap.id) =
        ((a : V ≃ₗ[ZMod p] V).toLinearMap - LinearMap.id).comp W.subtype := by
    ext u
    simp [LinearMap.sub_apply, ZS.restrictHom_apply]
  have hmap : Submodule.map W.subtype (ggLinMove (ZS.restrictHom A W hW a)) =
      ggLinMove (a : V ≃ₗ[ZMod p] V) := by
    rw [ggLinMove, ggLinMove, ← LinearMap.range_comp, hcomp, LinearMap.range_comp,
      Submodule.range_subtype]
    apply le_antisymm
    · exact LinearMap.map_le_range
    · intro w hw
      rw [Submodule.mem_map]
      refine ⟨(-2 : ZMod p)⁻¹ • w, ?_, ?_⟩
      · exact Submodule.smul_mem _ _ (hmove hw)
      · have hwφ : (a : V →ₗ[ZMod p] V) w = -w :=
          tenCoreBAux_apply_eq_neg_of_mem_move (p := p) (V := V) a ha hw
        have hfw : (((a : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)) w =
            (-2 : ZMod p) • w := by
          simp only [LinearMap.sub_apply, LinearMap.id_apply]
          rw [hwφ, neg_smul, two_smul, neg_add]
          abel
        rw [map_smul, hfw, smul_smul, inv_mul_cancel₀ hneg2, one_smul]
  calc Module.finrank (ZMod p) (ggLinMove (ZS.restrictHom A W hW a))
      = Module.finrank (ZMod p) (Submodule.map W.subtype (ggLinMove (ZS.restrictHom A W hW a))) :=
        (Submodule.finrank_map_subtype_eq W (ggLinMove (ZS.restrictHom A W hW a))).symm
    _ = Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) := by rw [hmap]

private lemma tenCoreBAux_refl_iff_restrictHom
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (A : Subgroup (V ≃ₗ[ZMod p] V)) (W : Submodule (ZMod p) V)
    (hW : ∀ g ∈ A, ∀ w ∈ W, g w ∈ W)
    (hmove : ∀ g ∈ A, ggLinMove g ≤ W)
    (hfaith : ∀ g ∈ A, (∀ u ∈ W, g u = u) → g = 1) (a : ↥A) :
    GGLinRefl (a : V ≃ₗ[ZMod p] V) ↔ GGLinRefl (ZS.restrictHom A W hW a) := by
  have hmem : ggLinMove (a : V ≃ₗ[ZMod p] V) ≤ W := hmove a a.2
  constructor
  · rintro ⟨ha, hfr⟩
    refine ⟨?_, ?_⟩
    · have ha' : a * a = 1 := Subtype.ext (by simpa [Subgroup.coe_mul] using ha)
      rw [← map_mul, ha', map_one]
    · show Module.finrank (ZMod p) (ggLinMove (ZS.restrictHom A W hW a)) = 1
      rw [tenCoreBAux_finrank_move_restrictHom_eq hp2 A W hW a ha hmem]
      exact hfr
  · rintro ⟨hr2, hfr⟩
    have ha : (a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V) = 1 := by
      apply hfaith ((a : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V)) (A.mul_mem a.2 a.2)
      intro u hu
      have h1 : ZS.restrictHom A W hW (a * a) = 1 := by rw [map_mul, hr2]
      have h2 : ((ZS.restrictHom A W hW (a * a)) ⟨u, hu⟩ : V) = u := by rw [h1]; rfl
      rwa [ZS.restrictHom_apply, Subgroup.coe_mul] at h2
    refine ⟨ha, ?_⟩
    show Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) = 1
    rw [← tenCoreBAux_finrank_move_restrictHom_eq hp2 A W hW a ha hmem]
    exact hfr

theorem ggTen_linWeyl_lift {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] {ι : Type} (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2) (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hinv : ∀ g ∈ A, ∀ w ∈ Submodule.span (ZMod 3) (Set.range h), g w ∈ Submodule.span (ZMod 3) (Set.range h))
    (hfaith : ∀ g ∈ A, (∀ u ∈ Submodule.span (ZMod 3) (Set.range h), g u = u) → g = 1)
    (hQ : ZS.LinWeyl 3 (ZS.restrictHom A (Submodule.span (ZMod 3) (Set.range h)) hinv).range) :
    ZS.LinWeyl 3 A := by
  let T : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hmove : ∀ g ∈ A, ggLinMove g ≤ T := by
    intro g hg w hw
    rcases hw with ⟨v, hv⟩
    rw [← hv]
    change g v - v ∈ T
    exact ggTen_sub_mem_span h α r hr A hA g hg v
  have hfaithT : ∀ g ∈ A, (∀ u ∈ T, g u = u) → g = 1 := hfaith
  have hinj : Function.Injective (ZS.restrictHom A T hinv) := by
    have hker1 : ∀ g : ↥A, ZS.restrictHom A T hinv g = 1 → g = 1 := by
      intro g hg
      apply Subtype.ext
      apply hfaithT (g : V ≃ₗ[ZMod 3] V) g.2
      intro u hu
      have h2 : ((ZS.restrictHom A T hinv g) ⟨u, hu⟩ : V) = u := by rw [hg]; rfl
      rwa [ZS.restrictHom_apply] at h2
    intro g h hgh
    have h1 : ZS.restrictHom A T hinv (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hgh, mul_inv_cancel]
    have h2 : g * h⁻¹ = 1 := hker1 (g * h⁻¹) h1
    calc g = g * 1 := (mul_one g).symm
      _ = g * (h⁻¹ * h) := by rw [inv_mul_cancel]
      _ = g * h⁻¹ * h := by rw [mul_assoc]
      _ = 1 * h := by rw [h2]
      _ = h := one_mul h
  let e : ↥A ≃* (ZS.restrictHom A T hinv).range := MonoidHom.ofInjective hinj
  obtain ⟨κ, M, hM, f, hf⟩ := hQ
  have he : e = MonoidHom.ofInjective hinj := rfl
  refine ⟨κ, M, hM, f.trans e.symm, ?_⟩
  intro i
  change GGLinRefl (e.symm (f (M.simple i)) : V ≃ₗ[ZMod 3] V)
  have hres : ZS.restrictHom A T hinv (e.symm (f (M.simple i))) = f (M.simple i) := by
    have h1 : e (e.symm (f (M.simple i))) = f (M.simple i) := MulEquiv.apply_symm_apply e _
    have h2 : ((e (e.symm (f (M.simple i))) : (ZS.restrictHom A T hinv).range) : T ≃ₗ[ZMod 3] T) =
        ((f (M.simple i) : (ZS.restrictHom A T hinv).range) : T ≃ₗ[ZMod 3] T) := congrArg _ h1
    rw [he] at h2
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  rw [tenCoreBAux_refl_iff_restrictHom (p := 3) (by decide) A T hinv hmove hfaithT
    (e.symm (f (M.simple i))), hres]
  exact hf i


end CFSG.StandardType

end
