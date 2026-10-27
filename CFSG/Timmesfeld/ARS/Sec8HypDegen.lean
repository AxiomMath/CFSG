module

public import CFSG.Timmesfeld.ARS.Sec8Regular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Degen

@[expose] def Equiv (Δ : Set (Subgroup G)) (X Y : Subgroup G) : Prop :=
  ∀ Z ∈ Δ, Commuting X Z ↔ Commuting Y Z

@[expose] def cl (Δ : Set (Subgroup G)) (X : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ Δ ∧ Equiv Δ X Y}

@[expose] def normCl (Δ : Set (Subgroup G)) (X Y : Subgroup G) : Subgroup G :=
  gen (cl Δ X) ⊓ stabSet (cl Δ Y)

variable {Δ : Set (Subgroup G)}

theorem Equiv.refl (X : Subgroup G) : Equiv Δ X X := fun _ _ => Iff.rfl

theorem Equiv.symm {X Y : Subgroup G} (h : Equiv Δ X Y) : Equiv Δ Y X :=
  fun Z hZ => (h Z hZ).symm

theorem Equiv.trans {X Y W : Subgroup G} (h₁ : Equiv Δ X Y) (h₂ : Equiv Δ Y W) :
    Equiv Δ X W :=
  fun Z hZ => (h₁ Z hZ).trans (h₂ Z hZ)

theorem mem_cl_self {X : Subgroup G} (hX : X ∈ Δ) : X ∈ cl Δ X := ⟨hX, Equiv.refl X⟩

theorem cl_eq_of_equiv {X Y : Subgroup G} (h : Equiv Δ X Y) : cl Δ X = cl Δ Y := by
  ext W
  exact ⟨fun hW => ⟨hW.1, h.symm.trans hW.2⟩, fun hW => ⟨hW.1, h.trans hW.2⟩⟩

theorem commuting_conjSub_iff {X Z : Subgroup G} {g : G} :
    Commuting (conjSub X g) Z ↔ Commuting X (conjSub Z g⁻¹) := by
  constructor
  · intro h
    have := h.conjSub g⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  · intro h
    have := h.conjSub g
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this

theorem Equiv.conjSub {X Y : Subgroup G} (h : Equiv Δ X Y) {g : G} (hg : g ∈ stabSet Δ) :
    Equiv Δ (conjSub X g) (conjSub Y g) := by
  intro Z hZ
  rw [commuting_conjSub_iff, commuting_conjSub_iff]
  exact h _ (conjSub_mem_of_mem_stabSet (inv_mem hg) hZ)

theorem conjSet_cl {X : Subgroup G} {g : G} (hg : g ∈ stabSet Δ) :
    conjSet (cl Δ X) g = cl Δ (conjSub X g) := by
  ext Y
  rw [mem_conjSet]
  constructor
  · rintro ⟨hY, hXY⟩
    refine ⟨?_, ?_⟩
    · have := conjSub_mem_of_mem_stabSet hg hY
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
    · have := hXY.conjSub hg
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
  · rintro ⟨hY, hXY⟩
    refine ⟨conjSub_mem_of_mem_stabSet (inv_mem hg) hY, ?_⟩
    have := hXY.conjSub (inv_mem hg)
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this

theorem mem_stabSet_cl {X : Subgroup G} {g : G} (hg : g ∈ stabSet Δ)
    (h : Equiv Δ X (conjSub X g)) : g ∈ stabSet (cl Δ X) := by
  rw [mem_stabSet, conjSet_cl hg, cl_eq_of_equiv h]

theorem equiv_of_mem_stabSet_cl {X : Subgroup G} (hX : X ∈ Δ) {g : G}
    (hgc : g ∈ stabSet (cl Δ X)) : Equiv Δ X (conjSub X g) := by
  have h1 : conjSub X g ∈ conjSet (cl Δ X) g := conjSub_mem_conjSet (mem_cl_self hX) g
  rw [mem_stabSet.1 hgc] at h1
  exact h1.2

section Basic

variable (hR : IsRootClass R) (hΔR : Δ ⊆ R)
include hR hΔR

theorem commuting_of_equiv {X Y : Subgroup G} (hX : X ∈ Δ) (h : Equiv Δ X Y) :
    Commuting X Y :=
  ((h X hX).1 (hR.commuting_self (hΔR hX))).symm

theorem commuting_of_mem_cl {X Y W : Subgroup G} (hY : Y ∈ cl Δ X) (hW : W ∈ cl Δ X) :
    Commuting Y W :=
  commuting_of_equiv hR hΔR hY.1 (hY.2.symm.trans hW.2)

theorem commuting_gen_cl (X : Subgroup G) : Commuting (gen (cl Δ X)) (gen (cl Δ X)) :=
  commuting_gen_of_pairwise fun _ hY _ hW => commuting_of_mem_cl hR hΔR hY hW

theorem mul_self_of_mem_gen_cl {X : Subgroup G} {y : G} (hy : y ∈ gen (cl Δ X)) :
    y * y = 1 := by
  refine gen_induction (p := fun y => y ∈ gen (cl Δ X) ∧ y * y = 1) hy
    (fun Y hY z hz => ⟨le_gen hY hz, hR.mul_self Y (hΔR hY.1) z hz⟩) ⟨one_mem _, mul_one 1⟩
    (fun y z hy hz => ⟨mul_mem hy.1 hz.1, ?_⟩) |>.2
  have hc : Commute y z := commuting_gen_cl hR hΔR X y hy.1 z hz.1
  calc y * z * (y * z) = y * y * (z * z) := by
        rw [mul_assoc, ← mul_assoc z y z, ← hc.eq, mul_assoc, mul_assoc]
    _ = 1 := by rw [hy.2, hz.2, mul_one]

theorem commute_of_mem_gen_cl {X Y : Subgroup G} (hY : Y ∈ cl Δ X) {y : G}
    (hy : y ∈ gen (cl Δ X)) {z : G} (hz : z ∈ Y) : Commute y z :=
  commuting_gen_cl hR hΔR X y hy z (le_gen hY hz)

theorem conjSub_eq_of_mem_gen_cl {X Y : Subgroup G} (hY : Y ∈ cl Δ X) {y : G}
    (hy : y ∈ gen (cl Δ X)) : conjSub Y y = Y :=
  conjSub_of_forall_commute fun _ hz => commute_of_mem_gen_cl hR hΔR hY hy hz

variable (hdeg : ∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y)
include hdeg

theorem opposite_of_not_commuting {X Y : Subgroup G} (hX : X ∈ Δ) (hY : Y ∈ Δ)
    (h : ¬ Commuting X Y) : Opposite X Y := by
  have hne : X ≠ Y := fun e => h (e ▸ hR.commuting_self (hΔR hX))
  rcases hR.rel X (hΔR hX) Y (hΔR hY) hne with hc | ho | hs
  · exact absurd hc h
  · exact ho
  · exact absurd hs (hdeg X hX Y hY)

theorem opposite_of_mem_cl {X Y F : Subgroup G} (hY : Y ∈ cl Δ X) (hF : F ∈ Δ)
    (hXF : ¬ Commuting X F) : Opposite Y F :=
  opposite_of_not_commuting hR hΔR hdeg hY.1 hF fun h => hXF ((hY.2 F hF).2 h)

end Basic

section Stab

variable (hR : IsRootClass R) (hΔR : Δ ⊆ R)
  (hΔconj : ∀ X ∈ Δ, ∀ g ∈ gen Δ, conjSub X g ∈ Δ)
include hR hΔR hΔconj

omit hR hΔR in
theorem mem_stabSet_of_mem_gen {g : G} (hg : g ∈ gen Δ) : g ∈ stabSet Δ := by
  refine Set.Subset.antisymm (Set.image_subset_iff.2 fun X hX => hΔconj X hX g hg) ?_
  intro Y hY
  refine ⟨conjSub Y g⁻¹, hΔconj Y hY g⁻¹ (inv_mem hg), ?_⟩
  change conjSub (conjSub Y g⁻¹) g = Y
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

omit hR hΔR hΔconj in
theorem gen_cl_le (X : Subgroup G) : gen (cl Δ X) ≤ gen Δ := gen_mono fun _ hY => hY.1

omit hΔconj in
theorem gen_cl_le_stabSet (X : Subgroup G) : gen (cl Δ X) ≤ stabSet (cl Δ X) := by
  intro y hy
  refine Set.Subset.antisymm ?_ fun Y hY => ⟨Y, hY, conjSub_eq_of_mem_gen_cl hR hΔR hY hy⟩
  rintro _ ⟨Y, hY, rfl⟩
  show conjSub Y y ∈ cl Δ X
  rw [conjSub_eq_of_mem_gen_cl hR hΔR hY hy]
  exact hY

omit hR hΔR in
theorem mem_normCl_iff {X Y : Subgroup G} (hY : Y ∈ Δ) {y : G} :
    y ∈ normCl Δ X Y ↔ y ∈ gen (cl Δ X) ∧ Equiv Δ Y (conjSub Y y) := by
  constructor
  · rintro ⟨hy, hyc⟩
    exact ⟨hy, equiv_of_mem_stabSet_cl hY hyc⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, mem_stabSet_cl (mem_stabSet_of_mem_gen hΔconj (gen_cl_le X hy)) h⟩

end Stab

section Local

variable (hR : IsRootClass R) (hΔR : Δ ⊆ R)
  (hΔconj : ∀ X ∈ Δ, ∀ g ∈ gen Δ, conjSub X g ∈ Δ) (hdeg : ∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y)
include hR hΔR hΔconj hdeg

theorem exists_mul_mem_normCl {E F X : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) (hX : X ∈ cl Δ E) {x : G} (hx : x ∈ X) :
    ∃ a ∈ E, x * a ∈ normCl Δ E F := by
  by_cases hx1 : x = 1
  · exact ⟨1, one_mem _, by rw [hx1, one_mul]; exact one_mem _⟩
  have hXF : Opposite X F := opposite_of_mem_cl hR hΔR hdeg hX hF hEF
  have hEF' : Opposite E F := opposite_of_not_commuting hR hΔR hdeg hE hF hEF
  obtain ⟨f, hf, hf1, hXf⟩ := hXF.2.1 x hx hx1
  obtain ⟨a, ha, -, hFa⟩ := hEF'.2.2 f hf hf1
  have hfΔ : f ∈ stabSet Δ := mem_stabSet_of_mem_gen hΔconj (le_gen hF hf)
  have hxΔ : x ∈ gen Δ := le_gen hX.1 hx
  have hy : x * a ∈ gen (cl Δ E) := mul_mem (le_gen hX hx) (le_gen (mem_cl_self hE) ha)
  refine ⟨a, ha, (mem_normCl_iff hΔconj hF).2 ⟨hy, ?_⟩⟩
  have h1 : Equiv Δ (conjSub F a) (conjSub F x) := by
    rw [hFa, ← hXf]
    exact hX.2.conjSub hfΔ
  have h2 := h1.conjSub (mem_stabSet_of_mem_gen hΔconj hxΔ)
  rw [← conjSub_mul, ← conjSub_mul, hR.mul_self X (hΔR hX.1) x hx, conjSub_one] at h2
  exact h2.symm

theorem exists_mul_mem_normCl_of_mem_gen {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {y : G} (hy : y ∈ gen (cl Δ E)) :
    ∃ a ∈ E, y * a ∈ normCl Δ E F := by
  refine (gen_induction
    (p := fun y => y ∈ gen (cl Δ E) ∧ ∃ a ∈ E, y * a ∈ normCl Δ E F) hy
    (fun X hX x hx => ⟨le_gen hX hx, exists_mul_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hX hx⟩)
    ⟨one_mem _, 1, one_mem _, by rw [one_mul]; exact one_mem _⟩ ?_).2
  rintro y z ⟨hy, a, ha, hya⟩ ⟨hz, c, hc, hzc⟩
  refine ⟨mul_mem hy hz, a * c, mul_mem ha hc, ?_⟩
  have hza : Commute z a := commute_of_mem_gen_cl hR hΔR (mem_cl_self hE) hz ha
  have : y * z * (a * c) = y * a * (z * c) := by
    rw [mul_assoc, ← mul_assoc z a c, hza.eq]
    simp only [mul_assoc]
  rw [this]
  exact mul_mem hya hzc

theorem mul_conj_mem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {y : G} (hy : y ∈ normCl Δ E F) {b : G} (hb : b ∈ F) :
    b * (y * b * y⁻¹) ∈ normCl Δ F E := by
  obtain ⟨hyg, hyF⟩ := (mem_normCl_iff hΔconj hF).1 hy
  have hFy : conjSub F y ∈ cl Δ F := ⟨hΔconj F hF y (gen_cl_le E hyg), hyF⟩
  have hgen : b * (y * b * y⁻¹) ∈ gen (cl Δ F) :=
    mul_mem (le_gen (mem_cl_self hF) hb) (le_gen hFy (conj_mem_conjSub y hb))
  refine (mem_normCl_iff hΔconj hE).2 ⟨hgen, ?_⟩
  by_cases hb1 : b = 1
  · rw [hb1, mul_one, mul_inv_cancel, mul_one, conjSub_one]
    exact Equiv.refl E
  have hEF' : Opposite E F := opposite_of_not_commuting hR hΔR hdeg hE hF hEF
  obtain ⟨a, ha, -, hab⟩ := hEF'.symm.2.1 b hb hb1
  have hya : y * a = a * y := (commute_of_mem_gen_cl hR hΔR (mem_cl_self hE) hyg ha).eq
  have hEy : conjSub E y = E := conjSub_eq_of_mem_gen_cl hR hΔR (mem_cl_self hE) hyg
  have h1 : conjSub (conjSub F y) a = conjSub E (y * b * y⁻¹) := by
    calc conjSub (conjSub F y) a = conjSub F (a * y) := (conjSub_mul F a y).symm
      _ = conjSub F (y * a) := by rw [hya]
      _ = conjSub (conjSub F a) y := conjSub_mul F y a
      _ = conjSub (conjSub E b) y := by rw [hab]
      _ = conjSub E (y * b * y⁻¹ * y) := by rw [inv_mul_cancel_right, conjSub_mul]
      _ = conjSub (conjSub E y) (y * b * y⁻¹) := conjSub_mul E _ y
      _ = conjSub E (y * b * y⁻¹) := by rw [hEy]
  have h2 : Equiv Δ (conjSub E (y * b * y⁻¹)) (conjSub E b) := by
    have := hyF.conjSub (mem_stabSet_of_mem_gen hΔconj (le_gen hE ha))
    rw [hab, h1] at this
    exact this.symm
  have h3 := h2.conjSub (mem_stabSet_of_mem_gen hΔconj (le_gen hF (F.inv_mem hb)))
  rw [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one,
    hR.inv_eq (hΔR hF) hb] at h3
  exact h3.symm

theorem mem_gen_cl_of_forall_commute {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {m : G} (hm : m ∈ gen (cl Δ F)) (hmE : ∀ e ∈ E, Commute m e) :
    m ∈ gen (cl Δ E) := by
  have hEF' : Opposite E F := opposite_of_not_commuting hR hΔR hdeg hE hF hEF
  obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one (hΔR hF)
  obtain ⟨a, ha, -, hfa⟩ := hEF'.symm.2.1 f hf hf1
  have hW : conjSub F (f * a) = E := by
    rw [conjSub_mul, hfa, ← conjSub_mul, hR.mul_self F (hΔR hF) f hf, conjSub_one]
  have hmfa : Commute m (f * a) :=
    (commute_of_mem_gen_cl hR hΔR (mem_cl_self hF) hm hf).mul_right (hmE a ha)
  have hfaΔ : f * a ∈ stabSet Δ :=
    mem_stabSet_of_mem_gen hΔconj (mul_mem (le_gen hF hf) (le_gen hE ha))
  have hmem : f * a * m * (f * a)⁻¹ ∈ conjSub (gen (cl Δ F)) (f * a) := conj_mem_conjSub _ hm
  rw [hmfa.symm.eq, mul_inv_cancel_right, conjSub_gen, conjSet_cl hfaΔ, hW] at hmem
  exact hmem

end Local

section Center

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hΔR : Δ ⊆ R)
  (hΔconj : ∀ X ∈ Δ, ∀ g ∈ gen Δ, conjSub X g ∈ Δ) (hdeg : ∀ X ∈ Δ, ∀ Y ∈ Δ, ¬ Special R X Y)
include hR hΔR hΔconj hdeg

omit hiso in
theorem eq_one_of_mem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {e : G} (he : e ∈ E) (heN : e ∈ normCl Δ E F) : e = 1 := by
  by_contra he1
  have hop := opposite_conjSub_of_opposite hR (hΔR hE) (hΔR hF)
    (opposite_of_not_commuting hR hΔR hdeg hE hF hEF) he he1
  exact hop.not_commuting (hR.ne_bot F (hΔR hF))
    (commuting_of_equiv hR hΔR hF ((mem_normCl_iff hΔconj hF).1 heN).2)

omit [Finite G] hiso in
theorem commutatorElement_mem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) {m a : G} (hm : m ∈ normCl Δ F E) (ha : a ∈ E) :
    ⁅m, a⁆ ∈ normCl Δ E F := by
  have h := mul_conj_mem_normCl hR hΔR hΔconj hdeg hF hE (fun h => hEF h.symm) hm ha
  have hinv : a⁻¹ = a := hR.inv_eq (hΔR hE) ha
  have e : ⁅m, a⁆ = (a * (m * a * m⁻¹))⁻¹ := by
    rw [commutatorElement_def, show (a * (m * a * m⁻¹))⁻¹ = m * a⁻¹ * m⁻¹ * a⁻¹ by group, hinv]
  rw [e]
  exact inv_mem h

omit [Finite G] hR hΔR hΔconj hiso hdeg in
theorem commute_of_mem_normCl {E F : Subgroup G} (hZ : gen (cl Δ E) ⊓ gen (cl Δ F) = ⊥)
    {n m : G} (hn : n ∈ normCl Δ E F) (hm : m ∈ normCl Δ F E) : Commute n m := by
  obtain ⟨hnE, hnF⟩ := Subgroup.mem_inf.1 hn
  obtain ⟨hmF, hmE⟩ := Subgroup.mem_inf.1 hm
  have h1 : ⁅n, m⁆ ∈ gen (cl Δ F) := by
    rw [commutatorElement_def]
    refine mul_mem ?_ (inv_mem hmF)
    have : n * m * n⁻¹ ∈ conjSub (gen (cl Δ F)) n := conj_mem_conjSub n hmF
    rwa [conjSub_gen, mem_stabSet.1 hnF] at this
  have h2 : ⁅n, m⁆ ∈ gen (cl Δ E) := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hnE ?_
    have : m * n⁻¹ * m⁻¹ ∈ conjSub (gen (cl Δ E)) m := conj_mem_conjSub m (inv_mem hnE)
    rw [conjSub_gen, mem_stabSet.1 hmE] at this
    rwa [← mul_assoc]
  have h3 : ⁅n, m⁆ ∈ gen (cl Δ E) ⊓ gen (cl Δ F) := Subgroup.mem_inf.2 ⟨h2, h1⟩
  rw [hZ, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

include hiso in
theorem eq_one_of_commute_of_mem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) (hZ : gen (cl Δ E) ⊓ gen (cl Δ F) = ⊥) {m a : G}
    (hm : m ∈ normCl Δ F E) (ha : a ∈ E) (ha1 : a ≠ 1) (hc : Commute m a) : m = 1 := by
  have hER : E ∈ R := hΔR hE
  have hmF : m ∈ gen (cl Δ F) := (Subgroup.mem_inf.1 hm).1
  have hEm : conjSub E m = E := by
    by_contra hne
    have hmem : a ∈ E ⊓ conjSub E m := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [mem_conjSub, mul_assoc, ← hc.eq, inv_mul_cancel_left]
      exact ha
    rw [inf_eq_bot hR hiso hER (hR.conjSub_mem hER m) (Ne.symm hne), Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hcE : ∀ a' ∈ E, Commute m a' := by
    intro a' ha'
    have h1 : ⁅m, a'⁆ ∈ E := by
      rw [commutatorElement_def]
      refine E.mul_mem ?_ (E.inv_mem ha')
      rw [← hEm]
      exact conj_mem_conjSub m ha'
    have h2 := commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hm ha'
    exact commutatorElement_eq_one_iff_mul_comm.1
      (eq_one_of_mem_normCl hR hΔR hΔconj hdeg hE hF hEF h1 h2)
  have hmE := mem_gen_cl_of_forall_commute hR hΔR hΔconj hdeg hE hF hEF hmF hcE
  have h3 : m ∈ gen (cl Δ E) ⊓ gen (cl Δ F) := Subgroup.mem_inf.2 ⟨hmE, hmF⟩
  rw [hZ, Subgroup.mem_bot] at h3
  exact h3

include hiso in
theorem injOn_commutatorElement_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) (hZ : gen (cl Δ E) ⊓ gen (cl Δ F) = ⊥) {a : G} (ha : a ∈ E)
    (ha1 : a ≠ 1) : Set.InjOn (fun m => ⁅m, a⁆) (normCl Δ F E : Set G) := by
  intro m hm m' hm' h
  have h' : ⁅m, a⁆ = ⁅m', a⁆ := h
  have hc : Commute (m'⁻¹ * m) a := by
    rw [commutatorElement_def, commutatorElement_def, mul_left_inj] at h'
    calc m'⁻¹ * m * a = m'⁻¹ * (m * a * m⁻¹) * m := by group
      _ = m'⁻¹ * (m' * a * m'⁻¹) * m := by rw [h']
      _ = a * (m'⁻¹ * m) := by group
  have := eq_one_of_commute_of_mem_normCl hR hiso hΔR hΔconj hdeg hE hF hEF hZ
    (mul_mem (inv_mem hm') hm) ha ha1 hc
  rw [inv_mul_eq_one] at this
  exact this.symm

include hiso in
theorem bijOn_commutatorElement_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) (hZ : gen (cl Δ E) ⊓ gen (cl Δ F) = ⊥) {a : G} (ha : a ∈ E)
    (ha1 : a ≠ 1) :
    Set.BijOn (fun m => ⁅m, a⁆) (normCl Δ F E : Set G) (normCl Δ E F : Set G) := by
  have hFE : ¬ Commuting F E := fun h => hEF h.symm
  have hZ' : gen (cl Δ F) ⊓ gen (cl Δ E) = ⊥ := by rw [inf_comm]; exact hZ
  have hmaps : Set.MapsTo (fun m => ⁅m, a⁆) (normCl Δ F E : Set G) (normCl Δ E F : Set G) :=
    fun m hm => commutatorElement_mem_normCl hR hΔR hΔconj hdeg hE hF hEF hm ha
  have hinj := injOn_commutatorElement_normCl hR hiso hΔR hΔconj hdeg hE hF hEF hZ ha ha1
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one (hΔR hF)
  have hinj' := injOn_commutatorElement_normCl hR hiso hΔR hΔconj hdeg hF hE hFE hZ' hb hb1
  have hmaps' : Set.MapsTo (fun n => ⁅n, b⁆) (normCl Δ E F : Set G) (normCl Δ F E : Set G) :=
    fun n hn => commutatorElement_mem_normCl hR hΔR hΔconj hdeg hF hE hFE hn hb
  have hle1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
  have hle2 := Set.ncard_le_ncard_of_injOn _ hmaps' hinj' (Set.toFinite _)
  refine ⟨hmaps, hinj, ?_⟩
  have himg : (fun m => ⁅m, a⁆) '' (normCl Δ F E : Set G) = (normCl Δ E F : Set G) := by
    refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps) ?_ (Set.toFinite _)
    rw [hinj.ncard_image]
    omega
  intro n hn
  rw [← himg] at hn
  exact hn

include hiso in
theorem exists_mem_cl_of_notMem_normCl {E F : Subgroup G} (hE : E ∈ Δ) (hF : F ∈ Δ)
    (hEF : ¬ Commuting E F) (hZ : gen (cl Δ E) ⊓ gen (cl Δ F) = ⊥) {x : G}
    (hx : x ∈ gen (cl Δ E)) (hxN : x ∉ normCl Δ E F) : ∃ D ∈ cl Δ E, x ∈ D ∧ x ≠ 1 := by
  obtain ⟨a, ha, hxa⟩ := exists_mul_mem_normCl_of_mem_gen hR hΔR hΔconj hdeg hE hF hEF hx
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxa
    exact hxN hxa
  obtain ⟨m, hm, hmn⟩ :=
    (bijOn_commutatorElement_normCl hR hiso hΔR hΔconj hdeg hE hF hEF hZ ha ha1).surjOn hxa
  have hmn' : ⁅m, a⁆ = x * a := hmn
  have hmΔ : m ∈ gen Δ := gen_cl_le F (Subgroup.mem_inf.1 hm).1
  refine ⟨conjSub E m, ⟨hΔconj E hE m hmΔ, equiv_of_mem_stabSet_cl hE (Subgroup.mem_inf.1 hm).2⟩,
    ?_, fun h => hxN (h ▸ one_mem _)⟩
  have e : x = m * a * m⁻¹ := by
    have h1 : m * a * m⁻¹ = x * a * a := by
      rw [← hmn', commutatorElement_def, hR.inv_eq (hΔR hE) ha, mul_assoc (m * a * m⁻¹) a a,
        hR.mul_self E (hΔR hE) a ha, mul_one]
    rw [h1, mul_assoc, hR.mul_self E (hΔR hE) a ha, mul_one]
  rw [e]
  exact conj_mem_conjSub m ha

include hiso in
theorem mem_normCl_of_mem_normCl {E F₁ F₂ : Subgroup G} (hE : E ∈ Δ) (hF₁ : F₁ ∈ Δ)
    (hF₂ : F₂ ∈ Δ) (hEF₁ : ¬ Commuting E F₁) (hEF₂ : ¬ Commuting E F₂)
    (hZ : gen (cl Δ E) ⊓ gen (cl Δ F₂) = ⊥) {x : G} (hx : x ∈ normCl Δ E F₁) :
    x ∈ normCl Δ E F₂ := by
  by_contra hxN
  obtain ⟨D, hD, hxD, hx1⟩ := exists_mem_cl_of_notMem_normCl hR hiso hΔR hΔconj hdeg hE hF₂
    hEF₂ hZ (Subgroup.mem_inf.1 hx).1 hxN
  have hDF₁ : Opposite D F₁ := opposite_of_mem_cl hR hΔR hdeg hD hF₁ hEF₁
  have hop := opposite_conjSub_of_opposite hR (hΔR hD.1) (hΔR hF₁) hDF₁ hxD hx1
  exact hop.not_commuting (hR.ne_bot F₁ (hΔR hF₁))
    (commuting_of_equiv hR hΔR hF₁ ((mem_normCl_iff hΔconj hF₁).1 hx).2)

end Center

end Degen

end CFSG.Timmesfeld.ARS
