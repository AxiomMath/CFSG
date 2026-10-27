module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelForm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan

open Module
open CFSG.StandardType
open CFSG.StandardType.NoOffRest
open CFSG.StandardType.TableBExc.E6Three
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley

public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] def e6ModelHyp : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3) where
  carrier := {x | NoOffRest.kDotP 3 x = 0}
  add_mem' := by
    intro x y hx hy
    change NoOffRest.kDotP 3 (x + y) = 0
    rw [NoOffRest.kDotP_add, show NoOffRest.kDotP 3 x = 0 from hx,
      show NoOffRest.kDotP 3 y = 0 from hy, add_zero]
  zero_mem' := NoOffRest.kDotP_zero
  smul_mem' := by
    intro c x hx
    change NoOffRest.kDotP 3 (c • x) = 0
    rw [NoOffRest.kDotP_smul, show NoOffRest.kDotP 3 x = 0 from hx, mul_zero]

private theorem e6ModelHyp_card : Nat.card e6ModelHyp = 3 ^ 5 :=
  NoOffRest.card_hypE6

@[expose] def e6ModelCoordVal (v : V) : Fin Tag.E6.rank → ZMod 3 := fun i => α i v

theorem e6ModelCoordVal_mem (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (v : V) : e6ModelCoordVal (α := α) v ∈ e6ModelHyp := by
  have hspan := span_eq_top_of_card hP hV
  let F : V →ₗ[ZMod 3] ZMod 3 :=
    Finset.univ.sum fun i => ((NoOffRest.kE6 i : ℤ) : ZMod 3) • α i
  have hrow : ∀ j : Fin Tag.E6.rank,
      ∑ i, ((NoOffRest.kE6 i : ℤ) : ZMod 3) * ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) = 0 := by
    intro j
    have h := NoOffRest.kDot_cartan j
    rw [show Tag.cartan .E6 = CartanMatrix.E 6 from cartan_six_eq] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [cartanE_six_symm i j]
  have hF : F = 0 := by
    rw [Submodule.linearMap_eq_zero_iff_of_span_eq_top F hspan]
    rintro ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := hx
    simp only [F, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [show (∑ x, ((NoOffRest.kE6 x : ℤ) : ZMod 3) * (α x) (h j)) =
        ∑ x, ((NoOffRest.kE6 x : ℤ) : ZMod 3) * ((CartanMatrix.E 6 x j : ℤ) : ZMod 3) from
      Finset.sum_congr rfl fun x _ => by rw [hP x j]]
    exact hrow j
  have h := LinearMap.congr_fun hF v
  change NoOffRest.kDotP 3 (e6ModelCoordVal (α := α) v) = 0
  simpa [F, e6ModelCoordVal, NoOffRest.kDotP, LinearMap.sum_apply, smul_eq_mul] using h

@[expose] noncomputable def e6ModelCoordLin
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) : V →ₗ[ZMod 3] e6ModelHyp where
  toFun v := ⟨e6ModelCoordVal (α := α) v, e6ModelCoordVal_mem hP hV v⟩
  map_add' := by
    intro x y
    ext i
    exact map_add (α i) x y
  map_smul' := by
    intro c x
    ext i
    exact map_smul (α i) c x

private theorem e6ModelCoordLin_injective (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) : Function.Injective (e6ModelCoordLin hP hV) := by
  intro x y hxy
  have h : ∀ i, α i (x - y) = 0 := by
    intro i
    have h1 := congrArg (fun z : e6ModelHyp => (z : Fin Tag.E6.rank → ZMod 3)) hxy
    have h2 : (e6ModelCoordLin hP hV x : Fin Tag.E6.rank → ZMod 3) i =
        (e6ModelCoordLin hP hV y : Fin Tag.E6.rank → ZMod 3) i := by rw [h1]
    have h3 : α i x = α i y := h2
    rw [map_sub, h3]
    exact sub_self _
  exact sub_eq_zero.mp (eq_zero_of_forall_apply_eq_zero hP hV h)

theorem e6ModelCoordLin_bijective (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) : Function.Bijective (e6ModelCoordLin hP hV) := by
  refine Function.Injective.bijective_of_nat_card_le (e6ModelCoordLin_injective hP hV) ?_
  rw [e6ModelHyp_card, hV]

@[expose] noncomputable def e6ModelCoord (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) : V ≃ₗ[ZMod 3] e6ModelHyp :=
  LinearEquiv.ofBijective (e6ModelCoordLin hP hV) (e6ModelCoordLin_bijective hP hV)

private theorem e6ModelCoord_apply (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (v : V) :
    (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) = e6ModelCoordVal (α := α) v := rfl

private theorem e6ModelCoord_h (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (i : Fin Tag.E6.rank) :
    (e6ModelCoord hP hV (h i) : Fin Tag.E6.rank → ZMod 3) = e6ModelCol i := by
  funext j
  exact hP j i

private theorem e6ModelCoord_reflection (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hα : ∀ i, α i (h i) = 2) (i : Fin Tag.E6.rank) (v : V) :
    (e6ModelCoord hP hV (reflection (hα i) v) : Fin Tag.E6.rank → ZMod 3) =
      TableBExc.E6Three.adRefl .E6 3 i (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) := by
  rw [e6ModelCoord_apply, e6ModelCoord_apply, adRefl_eq]
  funext j
  have hP' : ∀ i j : Fin Tag.E6.rank, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3) := hP
  simp only [e6ModelCoordVal, e6ModelCol, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Module.reflection_apply, map_sub, map_smul, smul_eq_mul, hP' j i]
  rfl

end CFSG.StandardType.E6QTwo
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}

@[expose] noncomputable def e6ModelWeyl {h : Fin Tag.E6.rank → V}
    {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
    (hα : ∀ i, α i (h i) = 2) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  Subgroup.closure (Set.range fun i => reflection (hα i))

theorem exists_adAct_of_mem_e6Weyl (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hα : ∀ i, α i (h i) = 2) {g : V ≃ₗ[ZMod 3] V}
    (hg : g ∈ e6ModelWeyl hα) :
    ∃ w : WeylGroup .E6, ∀ x : V,
      (e6ModelCoord hP hV (g x) : Fin Tag.E6.rank → ZMod 3) =
        TableBExc.E6Three.adAct .E6 3 w (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3) := by
  classical
  refine Subgroup.closure_induction (p := fun g _ => ∃ w : WeylGroup .E6, ∀ x : V,
      (e6ModelCoord hP hV (g x) : Fin Tag.E6.rank → ZMod 3) =
        TableBExc.E6Three.adAct .E6 3 w (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨i, rfl⟩
    exact ⟨simple .E6 i, fun x => by
      rw [e6ModelCoord_reflection hP hV hα i x, TableBExc.E6Three.adAct_simple]⟩
  · refine ⟨1, fun x => ?_⟩
    rw [adAct_one]
    change (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3) =
      (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3)
    rfl
  · rintro g₁ g₂ _ _ ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
    exact ⟨w₁ * w₂, fun x => by
      rw [show (g₁ * g₂) x = g₁ (g₂ x) from rfl, hw₁, hw₂, TableBExc.E6Three.adAct_mul]⟩
  · rintro g _ ⟨w, hw⟩
    refine ⟨w⁻¹, fun x => ?_⟩
    have hz : (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3) =
        TableBExc.E6Three.adAct .E6 3 w
          (e6ModelCoord hP hV (g⁻¹ x) : Fin Tag.E6.rank → ZMod 3) := by
      have h := hw (g⁻¹ x)
      simpa using h
    rw [hz, ← TableBExc.E6Three.adAct_mul, inv_mul_cancel, adAct_one]

theorem exists_mem_e6Weyl_of_adAct (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hα : ∀ i, α i (h i) = 2) (w : WeylGroup .E6) :
    ∃ g ∈ e6ModelWeyl hα, ∀ x : V,
      (e6ModelCoord hP hV (g x) : Fin Tag.E6.rank → ZMod 3) =
        TableBExc.E6Three.adAct .E6 3 w (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3) := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective w
  induction ω with
  | nil => exact ⟨LinearEquiv.refl (ZMod 3) V, Subgroup.one_mem _, fun x => by
      rw [CoxeterSystem.wordProd_nil, adAct_one]
      change (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3) =
        (e6ModelCoord hP hV x : Fin Tag.E6.rank → ZMod 3)
      rfl⟩
  | cons i ω ih =>
    obtain ⟨g, hg, hgx⟩ := ih
    rw [CoxeterSystem.wordProd_cons]
    refine ⟨reflection (hα i) * g,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hg, fun x => ?_⟩
    rw [show (reflection (hα i) * g) x = reflection (hα i) (g x) from rfl,
      e6ModelCoord_reflection hP hV hα i (g x), hgx x, TableBExc.E6Three.adAct_mul,
      TableBExc.E6Three.adAct_simple]

private theorem e6ModelCoord_image_orbit (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hα : ∀ i, α i (h i) = 2) (v : V) :
    Subtype.val '' (e6ModelCoord hP hV '' (MulAction.orbit (e6ModelWeyl hα) v)) =
      Subtype.val '' (Set.range fun w : WeylGroup .E6 =>
        (⟨TableBExc.E6Three.adAct .E6 3 w
          (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3), NoOffRest.adAct_mem_hypE6 w
            (e6ModelCoord hP hV v).2⟩ : e6ModelHyp)) := by
  ext y
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    rw [MulAction.mem_orbit_iff] at hb
    obtain ⟨g, hgv⟩ := hb
    obtain ⟨w, hw⟩ := exists_adAct_of_mem_e6Weyl hP hV hα g.2
    refine ⟨⟨TableBExc.E6Three.adAct .E6 3 w
      (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3),
      NoOffRest.adAct_mem_hypE6 w (e6ModelCoord hP hV v).2⟩, ⟨w, rfl⟩, ?_⟩
    rw [← hgv]
    simpa [Subgroup.smul_def] using (hw v).symm
  · rintro ⟨a, ⟨w, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgw⟩ := exists_mem_e6Weyl_of_adAct hP hV hα w
    exact ⟨e6ModelCoord hP hV (g v),
      ⟨(⟨g, hg⟩ : e6ModelWeyl hα) • v, MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, rfl⟩, rfl⟩, hgw v⟩

private theorem e6ModelAdActRange_ncard (x : e6ModelHyp) :
    (Subtype.val '' (Set.range fun w : WeylGroup .E6 =>
      (⟨TableBExc.E6Three.adAct .E6 3 w (x : Fin Tag.E6.rank → ZMod 3),
        NoOffRest.adAct_mem_hypE6 w x.2⟩ : e6ModelHyp))).ncard =
      (Set.range fun w : WeylGroup .E6 =>
        TableBExc.E6Three.adAct .E6 3 w (x : Fin Tag.E6.rank → ZMod 3)).ncard := by
  rw [show Subtype.val '' (Set.range fun w : WeylGroup .E6 =>
      (⟨TableBExc.E6Three.adAct .E6 3 w (x : Fin Tag.E6.rank → ZMod 3),
        NoOffRest.adAct_mem_hypE6 w x.2⟩ : e6ModelHyp)) =
      (Set.range fun w : WeylGroup .E6 =>
        TableBExc.E6Three.adAct .E6 3 w (x : Fin Tag.E6.rank → ZMod 3)) from by
    ext y
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨⟨TableBExc.E6Three.adAct .E6 3 w (x : Fin Tag.E6.rank → ZMod 3),
        NoOffRest.adAct_mem_hypE6 w x.2⟩, ⟨w, rfl⟩, rfl⟩]

private theorem e6ModelCoord_orbit_ncard (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hα : ∀ i, α i (h i) = 2) (v : V) :
    Nat.card (MulAction.orbit (e6ModelWeyl hα) v) =
      (Set.range fun w : WeylGroup .E6 =>
        TableBExc.E6Three.adAct .E6 3 w
          (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3)).ncard := by
  calc Nat.card (MulAction.orbit (e6ModelWeyl hα) v) = (MulAction.orbit (e6ModelWeyl hα) v).ncard :=
        Nat.card_coe_set_eq _
    _ = (e6ModelCoord hP hV '' (MulAction.orbit (e6ModelWeyl hα) v)).ncard :=
        (Set.ncard_image_of_injective _ (e6ModelCoord hP hV).injective).symm
    _ = (Subtype.val '' (e6ModelCoord hP hV '' (MulAction.orbit (e6ModelWeyl hα) v))).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = (Subtype.val '' (Set.range fun w : WeylGroup .E6 =>
        (⟨TableBExc.E6Three.adAct .E6 3 w
          (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3),
          NoOffRest.adAct_mem_hypE6 w (e6ModelCoord hP hV v).2⟩ : e6ModelHyp))).ncard := by
        rw [e6ModelCoord_image_orbit hP hV hα]
    _ = _ := e6ModelAdActRange_ncard (e6ModelCoord hP hV v)

end CFSG.StandardType.E6QTwo
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelForm_e6Coord (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (a b : V) :
    e6ModelForm (e6ModelCoord hP hV a : Fin Tag.E6.rank → ZMod 3)
      (e6ModelCoord hP hV b : Fin Tag.E6.rank → ZMod 3) = 2 * B a b := by
  have hspan := span_eq_top_of_card hP hV
  have hmem : ∀ x : V, x ∈ Submodule.span (ZMod 3) (Set.range h) := by
    intro x
    have hx : x ∈ (⊤ : Submodule (ZMod 3) V) := Submodule.mem_top
    rwa [← hspan] at hx
  have hbase : ∀ i j : Fin Tag.E6.rank,
      e6ModelForm (e6ModelCoord hP hV (h i) : Fin Tag.E6.rank → ZMod 3)
        (e6ModelCoord hP hV (h j) : Fin Tag.E6.rank → ZMod 3) = 2 * B (h i) (h j) := by
    intro i j
    calc e6ModelForm (e6ModelCoord hP hV (h i) : Fin Tag.E6.rank → ZMod 3)
          (e6ModelCoord hP hV (h j) : Fin Tag.E6.rank → ZMod 3)
        = e6ModelForm (e6ModelCol i) (e6ModelCol j) := by
          rw [e6ModelCoord_h hP hV i, e6ModelCoord_h hP hV j]
      _ = 2 * ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) := e6ModelForm_col_col i j
      _ = 2 * B (h i) (h j) := by
          rw [hB i (h j)]
          congr 1
          exact (hP i j).symm
  refine Submodule.span_induction₂ (p := fun a b _ _ =>
    e6ModelForm (e6ModelCoord hP hV a : Fin Tag.E6.rank → ZMod 3)
      (e6ModelCoord hP hV b : Fin Tag.E6.rank → ZMod 3) = 2 * B a b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hmem a) (hmem b)
  · rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hbase i j
  · intro y _
    simp [e6ModelForm, E6Dep.bil6]
  · intro x _
    simp [e6ModelForm, E6Dep.bil6]
  · intro x y z _ _ _ hxz hyz
    simp only [map_add, Submodule.coe_add, LinearMap.add_apply, e6ModelForm_add_left,
      hxz, hyz, mul_add]
    try ring_nf
  · intro x y z _ _ _ hxy hxz
    simp only [map_add, Submodule.coe_add, LinearMap.add_apply, e6ModelForm_add_right,
      hxy, hxz, mul_add]
    try ring_nf
  · intro r x y _ _ hxy
    simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, LinearMap.add_apply,
      e6ModelForm_smul_left, hxy, smul_eq_mul]
    try ring_nf
  · intro r x y _ _ hxy
    simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, LinearMap.add_apply,
      e6ModelForm_smul_right, hxy, smul_eq_mul]
    try ring_nf

end CFSG.StandardType.E6QTwo
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelOrbitCases (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {v : V} (hv : v ≠ 0) :
    (B v v = 2 ∧ Nat.card (MulAction.orbit (e6ModelWeyl hα) v) = 72) ∨
      (B v v = 0 ∧ Nat.card (MulAction.orbit (e6ModelWeyl hα) v) = 80) ∨
      (B v v = 1 ∧ Nat.card (MulAction.orbit (e6ModelWeyl hα) v) = 90) := by
  have hmem : (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) ∈ hypE6 :=
    mem_hypE6.mpr (e6ModelCoord hP hV v).2
  have hne : (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) ≠ 0 := by
    intro h0
    apply hv
    have h1 : e6ModelCoord hP hV v = 0 := Subtype.ext h0
    have h2 : e6ModelCoord hP hV v = e6ModelCoord hP hV 0 := by simpa using h1
    exact (e6ModelCoord hP hV).injective h2
  have hQ : e6ModelForm (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3)
      (e6ModelCoord hP hV v : Fin Tag.E6.rank → ZMod 3) = 2 * B v v :=
    e6ModelForm_e6Coord hP hV hB v v
  have hcard := e6ModelCoord_orbit_ncard hP hV hα v
  obtain ⟨hq, hn⟩ | ⟨hq, hn⟩ | ⟨hq, hn⟩ := ggE6IsoOrbit_ncard hmem hne
  · right; left
    refine ⟨?_, hcard.trans hn⟩
    have hz : 2 * B v v = 0 := by rw [← hQ]; exact hq
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  · left
    refine ⟨?_, hcard.trans hn⟩
    have hz : 2 * B v v = 1 := by rw [← hQ]; exact hq
    calc B v v = (2 * 2 : ZMod 3) * B v v := by
          rw [show (2 * 2 : ZMod 3) = 1 by decide, one_mul]
      _ = 2 * (2 * B v v) := by ring
      _ = 2 * 1 := by rw [hz]
      _ = 2 := by decide
  · right; right
    refine ⟨?_, hcard.trans hn⟩
    have hz : 2 * B v v = 2 := by rw [← hQ]; exact hq
    calc B v v = (2 * 2 : ZMod 3) * B v v := by
          rw [show (2 * 2 : ZMod 3) = 1 by decide, one_mul]
      _ = 2 * (2 * B v v) := by ring
      _ = 2 * 2 := by rw [hz]
      _ = 1 := by decide

end CFSG.StandardType.E6QTwo
public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelWeyl_isometry (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6ModelWeyl hα) (u v : V) : B (g u) (g v) = B u v := by
  revert u v
  refine Subgroup.closure_induction (p := fun g _ => ∀ u v : V, B (g u) (g v) = B u v)
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨i, rfl⟩ u v
    exact bilinForm_reflection hP hV hB hα i u v
  · intro u v
    simp
  · rintro g₁ g₂ _ _ h₁ h₂ u v
    rw [show (g₁ * g₂) u = g₁ (g₂ u) from rfl,
      show (g₁ * g₂) v = g₁ (g₂ v) from rfl, h₁, h₂]
  · rintro g _ h u v
    have h' := h (g⁻¹ u) (g⁻¹ v)
    simpa using h'.symm

end CFSG.StandardType.E6QTwo

public section

namespace CFSG.StandardType.E6QTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin Tag.E6.rank → V} {α : Fin Tag.E6.rank → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem e6ModelForm_adAct (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (w : WeylGroup .E6) {x y : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6) (hy : y ∈ hypE6) :
    e6ModelForm (adAct .E6 3 w x) (adAct .E6 3 w y) = e6ModelForm x y := by
  obtain ⟨g, hg, hgw⟩ := exists_mem_e6Weyl_of_adAct hP hV hα w
  let a : V := (e6ModelCoord hP hV).symm ⟨x, show x ∈ e6ModelHyp from hx⟩
  let b : V := (e6ModelCoord hP hV).symm ⟨y, show y ∈ e6ModelHyp from hy⟩
  have ha : (e6ModelCoord hP hV a : Fin Tag.E6.rank → ZMod 3) = x := by simp [a]
  have hb : (e6ModelCoord hP hV b : Fin Tag.E6.rank → ZMod 3) = y := by simp [b]
  calc e6ModelForm (adAct .E6 3 w x) (adAct .E6 3 w y)
      = e6ModelForm (adAct .E6 3 w (e6ModelCoord hP hV a : Fin Tag.E6.rank → ZMod 3))
          (adAct .E6 3 w (e6ModelCoord hP hV b : Fin Tag.E6.rank → ZMod 3)) := by rw [ha, hb]
    _ = e6ModelForm (e6ModelCoord hP hV (g a) : Fin Tag.E6.rank → ZMod 3)
          (e6ModelCoord hP hV (g b) : Fin Tag.E6.rank → ZMod 3) := by rw [hgw a, hgw b]
    _ = 2 * B (g a) (g b) := e6ModelForm_e6Coord hP hV hB (g a) (g b)
    _ = 2 * B a b := by rw [e6ModelWeyl_isometry hP hV hB hα hg a b]
    _ = e6ModelForm (e6ModelCoord hP hV a : Fin Tag.E6.rank → ZMod 3)
          (e6ModelCoord hP hV b : Fin Tag.E6.rank → ZMod 3) :=
        (e6ModelForm_e6Coord hP hV hB a b).symm
    _ = e6ModelForm x y := by rw [ha, hb]

end CFSG.StandardType.E6QTwo

end
