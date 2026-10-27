module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.StandardType.E6QTwo

open Module
open CFSG.Blueprint.Chevalley

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}

abbrev spanH (h : Fin 6 → V) : Submodule (ZMod 3) V :=
  Submodule.span (ZMod 3) (Set.range h)

@[expose] def hIn (h : Fin 6 → V) : Fin 6 → spanH h :=
  fun i => ⟨h i, Submodule.subset_span ⟨i, rfl⟩⟩

@[expose] def alphaIn (α : Fin 6 → Dual (ZMod 3) V) : Fin 6 → Dual (ZMod 3) (spanH h) :=
  fun i => (α i).comp (spanH h).subtype

theorem alphaIn_hIn (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    ∀ i j, alphaIn α i (hIn h j) = (CartanMatrix.E 6 i j : ZMod 3) := by
  intro i j
  simp [alphaIn, hIn, hP i j]

theorem alphaIn_self (hα : ∀ i, α i (h i) = 2) :
    ∀ i, alphaIn α i (hIn h i) = 2 := by
  intro i
  simp [alphaIn, hIn, hα i]

theorem apply_mem_spanH_of_mem_e6Weyl (hα : ∀ i, α i (h i) = 2)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) {v : V} (hv : v ∈ spanH h) :
    g v ∈ spanH h := by
  have hgen : ∀ i, ∀ v ∈ spanH h, reflection (hα i) v ∈ spanH h := fun i v hv => by
    rw [reflection_apply]
    exact sub_mem hv (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  suffices key : ∀ v ∈ spanH h, g v ∈ spanH h from key v hv
  refine Subgroup.closure_induction''
    (p := fun g _ => ∀ v ∈ spanH h, g v ∈ spanH h) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, rfl⟩
    exact hgen i
  · rintro x ⟨i, rfl⟩
    rw [reflection_inv]
    exact hgen i
  · intro v hv
    simpa using hv
  · intro x y _ _ hx hy v hv
    rw [LinearEquiv.mul_apply]
    exact hx _ (hy v hv)

theorem reflection_restrict {hα : ∀ i, α i (h i) = 2} (i : Fin 6) (s : spanH h) :
    (⟨reflection (hα i) (s : V),
        apply_mem_spanH_of_mem_e6Weyl hα
          (Subgroup.subset_closure ⟨i, rfl⟩) s.2⟩ : spanH h) =
      reflection (alphaIn_self hα i) s := by
  apply Subtype.ext
  change reflection (hα i) (s : V) = ↑(reflection (alphaIn_self hα i) s)
  rw [reflection_apply, reflection_apply]
  simp [alphaIn, hIn]

theorem restrict_mem_e6Weyl {hα : ∀ i, α i (h i) = 2}
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) :
    ∃ g' ∈ e6Weyl (alphaIn_self hα), ∀ s : spanH h, (g' s : V) = g s := by
  refine Subgroup.closure_induction''
    (p := fun g _ => ∃ g' ∈ e6Weyl (alphaIn_self hα), ∀ s : spanH h, (g' s : V) = g s)
    ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, rfl⟩
    refine ⟨reflection (alphaIn_self hα i), Subgroup.subset_closure ⟨i, rfl⟩, fun s => ?_⟩
    exact (congrArg Subtype.val (reflection_restrict i s)).symm
  · rintro x ⟨i, rfl⟩
    refine ⟨reflection (alphaIn_self hα i), Subgroup.subset_closure ⟨i, rfl⟩, fun s => ?_⟩
    rw [reflection_inv]
    exact (congrArg Subtype.val (reflection_restrict i s)).symm
  · refine ⟨1, (e6Weyl (alphaIn_self hα)).one_mem, fun s => ?_⟩
    simp
  · intro x y _ _ hx hy
    obtain ⟨x', hx', hx_eq⟩ := hx
    obtain ⟨y', hy', hy_eq⟩ := hy
    refine ⟨x' * y', mul_mem hx' hy', fun s => ?_⟩
    calc ((x' * y') s : V) = (x' (y' s) : V) := by simp
      _ = x (y' s) := hx_eq (y' s)
      _ = x (y s) := by rw [hy_eq s]

theorem lift_mem_e6Weyl {hα : ∀ i, α i (h i) = 2}
    {g' : spanH h ≃ₗ[ZMod 3] spanH h} (hg' : g' ∈ e6Weyl (alphaIn_self hα)) :
    ∃ g ∈ e6Weyl hα, ∀ s : spanH h, (g' s : V) = g s := by
  refine Subgroup.closure_induction''
    (p := fun g _ => ∃ g₀ ∈ e6Weyl hα, ∀ s : spanH h, (g s : V) = g₀ s)
    ?_ ?_ ?_ ?_ hg'
  · rintro x ⟨i, rfl⟩
    refine ⟨reflection (hα i), Subgroup.subset_closure ⟨i, rfl⟩, fun s => ?_⟩
    exact (congrArg Subtype.val (reflection_restrict i s)).symm
  · rintro x ⟨i, rfl⟩
    refine ⟨reflection (hα i), Subgroup.subset_closure ⟨i, rfl⟩, fun s => ?_⟩
    rw [reflection_inv]
    exact (congrArg Subtype.val (reflection_restrict i s)).symm
  · refine ⟨1, (e6Weyl hα).one_mem, fun s => ?_⟩
    simp
  · intro x y _ _ hx hy
    obtain ⟨x₀, hx₀, hx_eq⟩ := hx
    obtain ⟨y₀, hy₀, hy_eq⟩ := hy
    refine ⟨x₀ * y₀, mul_mem hx₀ hy₀, fun s => ?_⟩
    calc ((x * y) s : V) = (x (y s) : V) := by simp
      _ = x₀ (y s) := hx_eq (y s)
      _ = x₀ (y₀ s) := by rw [hy_eq s]

private theorem orbit_spanH (hα : ∀ i, α i (h i) = 2) {v : V} (hv : v ∈ spanH h) :
    Subtype.val '' MulAction.orbit (e6Weyl (alphaIn_self hα)) (⟨v, hv⟩ : spanH h) =
      MulAction.orbit (e6Weyl hα) v := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.mp hs
    obtain ⟨g, hg, hgeq⟩ := lift_mem_e6Weyl (hα := hα) g'.2
    refine MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, ?_⟩
    rw [← hg']
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using (hgeq ⟨v, hv⟩).symm
  · intro hw
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hw
    obtain ⟨g', hg', hgeq⟩ := restrict_mem_e6Weyl (hα := hα) g.2
    refine ⟨g' • (⟨v, hv⟩ : spanH h),
      MulAction.mem_orbit_iff.mpr ⟨⟨g', hg'⟩, rfl⟩, ?_⟩
    rw [← hg]
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using hgeq ⟨v, hv⟩

theorem finrank_eq_six (hV : Nat.card V = 3 ^ 6) : finrank (ZMod 3) V = 6 := by
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
  rw [Nat.card_zmod, hV] at hcard
  exact (Nat.pow_right_injective (by norm_num) hcard).symm

theorem natCard_submodule {W : Type*} [AddCommGroup W] [Module (ZMod 3) W] [Finite W]
    (S : Submodule (ZMod 3) W) : Nat.card S = 3 ^ finrank (ZMod 3) S := by
  haveI : Fintype S := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]

theorem exists_bilinForm_span (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hS : Nat.card (spanH h) = 3 ^ 5) :
    ∃ B' : LinearMap.BilinForm (ZMod 3) (spanH h),
      ∀ i s, B' (hIn h i) s = alphaIn α i s :=
  exists_bilinForm (alphaIn_hIn hP) hS

theorem card_le_stabilizer_of_forall_apply_eq {hα : ∀ i, α i (h i) = 2}
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα) {x : V}
    (hAx : ∀ g ∈ A, g x = x) :
    Nat.card A ≤ Nat.card (MulAction.stabilizer (e6Weyl hα) x) := by
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (by simpa using congrFun h))
  haveI : Fintype ↥(e6Weyl hα) := Fintype.ofFinite _
  have hle : A.subgroupOf (e6Weyl hα) ≤ MulAction.stabilizer (e6Weyl hα) x := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf] at hg
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using hAx g hg
  calc Nat.card A = Nat.card (A.subgroupOf (e6Weyl hα)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv).symm
    _ ≤ Nat.card (MulAction.stabilizer (e6Weyl hα) x) := Subgroup.card_le_of_le hle

theorem stabilizer_cases_of_spanH
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hW : Nat.card (e6Weyl hα) = 51840)
    (hS_card : Nat.card (spanH h) = 3 ^ 5)
    {B' : LinearMap.BilinForm (ZMod 3) (spanH h)}
    (hB' : ∀ i s, B' (hIn h i) s = alphaIn α i s)
    {v : V} (hvS : v ∈ spanH h) (hv : v ≠ 0) :
    (B' ⟨v, hvS⟩ ⟨v, hvS⟩ = 2 ∧ Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 720) ∨
      (B' ⟨v, hvS⟩ ⟨v, hvS⟩ = 0 ∧
        Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 648) ∨
      (B' ⟨v, hvS⟩ ⟨v, hvS⟩ = 1 ∧
        Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 576) := by
  classical
  have hvS0 : (⟨v, hvS⟩ : spanH h) ≠ 0 := by
    intro h0
    apply hv
    simpa using congrArg Subtype.val h0
  have hcases := orbit_cases (alphaIn_hIn hP) hS_card hB' (alphaIn_self hα) hvS0
  have hcard_orbit : Nat.card (MulAction.orbit (e6Weyl hα) v) =
      Nat.card (MulAction.orbit (e6Weyl (alphaIn_self hα)) (⟨v, hvS⟩ : spanH h)) := by
    rw [← orbit_spanH hα hvS, Nat.card_image_of_injective Subtype.val_injective]
  have hos : Nat.card (MulAction.orbit (e6Weyl hα) v) *
      Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 51840 := by
    have : Finite (V ≃ₗ[ZMod 3] V) :=
      Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
        (fun a b h => LinearEquiv.ext (by simpa using congrFun h))
    let : Fintype ↥(e6Weyl hα) := Fintype.ofFinite _
    let : Fintype ↑(MulAction.orbit (e6Weyl hα) v) := Fintype.ofFinite _
    let : Fintype ↥(MulAction.stabilizer (e6Weyl hα) v) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥(e6Weyl hα)) v
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hW] at h
    exact h
  rcases hcases with ⟨hb, ho⟩ | ⟨hb, ho⟩ | ⟨hb, ho⟩
  · exact Or.inl ⟨hb, by rw [hcard_orbit, ho] at hos; omega⟩
  · exact Or.inr (Or.inl ⟨hb, by rw [hcard_orbit, ho] at hos; omega⟩)
  · exact Or.inr (Or.inr ⟨hb, by rw [hcard_orbit, ho] at hos; omega⟩)

theorem norm_two_and_stabilizer_of_card_six
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hW : Nat.card (e6Weyl hα) = 51840)
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα) (hcardA : 720 ≤ Nat.card A)
    {x : V} (hx : x ≠ 0) (hAx : ∀ g ∈ A, g x = x)
    (hxS : x ∈ spanH h) (hS_card : Nat.card (spanH h) = 3 ^ 5) :
    ∃ B' : LinearMap.BilinForm (ZMod 3) (spanH h),
      (∀ i s, B' (hIn h i) s = alphaIn α i s) ∧
      B' ⟨x, hxS⟩ ⟨x, hxS⟩ = 2 ∧
      Nat.card (MulAction.stabilizer (e6Weyl hα) x) = 720 := by
  obtain ⟨B', hB'⟩ := exists_bilinForm_span hP hS_card
  have hcases := stabilizer_cases_of_spanH hP hα hW hS_card hB' hxS hx
  have hle : Nat.card A ≤ Nat.card (MulAction.stabilizer (e6Weyl hα) x) :=
    card_le_stabilizer_of_forall_apply_eq hA hAx
  refine ⟨B', hB', ?_, ?_⟩
  · rcases hcases with ⟨h2, -⟩ | ⟨h0, hstab⟩ | ⟨h1, hstab⟩
    · exact h2
    · rw [hstab] at hle; omega
    · rw [hstab] at hle; omega
  · rcases hcases with ⟨h2, hstab⟩ | ⟨h0, hstab⟩ | ⟨h1, hstab⟩
    · exact hstab
    · rw [hstab] at hle; omega
    · rw [hstab] at hle; omega

theorem exists_mem_e6Weyl_apply_eq_of_mem_spanH
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hS_card : Nat.card (spanH h) = 3 ^ 5)
    {B' : LinearMap.BilinForm (ZMod 3) (spanH h)}
    (hB' : ∀ i s, B' (hIn h i) s = alphaIn α i s)
    {u v : V} (huS : u ∈ spanH h) (hvS : v ∈ spanH h) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : B' ⟨u, huS⟩ ⟨u, huS⟩ = B' ⟨v, hvS⟩ ⟨v, hvS⟩) :
    ∃ g ∈ e6Weyl hα, g u = v := by
  have huS0 : (⟨u, huS⟩ : spanH h) ≠ 0 := by
    intro h0
    apply hu
    simpa using congrArg Subtype.val h0
  have hvS0 : (⟨v, hvS⟩ : spanH h) ≠ 0 := by
    intro h0
    apply hv
    simpa using congrArg Subtype.val h0
  obtain ⟨g', hg', hg'eq⟩ := exists_mem_e6Weyl_apply_eq (alphaIn_hIn hP) hS_card hB'
    (alphaIn_self hα) huS0 hvS0 huv
  obtain ⟨g, hg, hgeq⟩ := lift_mem_e6Weyl (hα := hα) hg'
  refine ⟨g, hg, ?_⟩
  rw [← hgeq ⟨u, huS⟩, hg'eq]

end CFSG.StandardType.E6QTwo

end