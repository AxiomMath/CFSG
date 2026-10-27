module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModel
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

section Group

variable {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}

theorem map_ggLin_eq_e6Weyl (ι : Additive ↥Bs ≃+ V) (e : CoxeterMatrix.E₆.Group ≃* ↥A)
    (hα : ∀ i, α i (h i) = 2)
    (he : ∀ i, ggLin (p := 3) ι ((e (CoxeterMatrix.E₆.simple i) : ↥A) : MulAut ↥Bs) =
      reflection (hα i)) :
    A.map (ggLin (p := 3) ι) = e6Weyl hα := by
  let Φ : CoxeterMatrix.E₆.Group →* (V ≃ₗ[ZMod 3] V) :=
    (ggLin (p := 3) ι).comp (A.subtype.comp e.toMonoidHom)
  have hΦ : ∀ i, Φ (CoxeterMatrix.E₆.simple i) = reflection (hα i) := he
  have hkey : ∀ w : CoxeterMatrix.E₆.Group, Φ w ∈ e6Weyl hα := by
    intro w
    have hw : w ∈ Subgroup.closure (Set.range CoxeterMatrix.E₆.simple) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      rw [CoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top w
    refine Subgroup.closure_induction (k := Set.range CoxeterMatrix.E₆.simple)
      (p := fun g _ => Φ g ∈ e6Weyl hα) ?_ ?_ ?_ ?_ hw
    · rintro x ⟨i, rfl⟩
      rw [hΦ i]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · rw [map_one]
      exact (e6Weyl hα).one_mem
    · intro x y _ _ hx hy
      rw [map_mul]
      exact mul_mem hx hy
    · intro x _ hx
      rw [map_inv]
      exact inv_mem hx
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : Φ (e.symm ⟨a, ha⟩) = ggLin (p := 3) ι a := by
      simp [Φ]
    rw [← h1]
    exact hkey _
  · change Subgroup.closure (Set.range fun i => reflection (hα i)) ≤ A.map (ggLin (p := 3) ι)
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_map.mpr ⟨_, (e (CoxeterMatrix.E₆.simple i)).2, he i⟩

theorem card_e6Weyl_eq (ι : Additive ↥Bs ≃+ V) (e : CoxeterMatrix.E₆.Group ≃* ↥A)
    (hα : ∀ i, α i (h i) = 2)
    (he : ∀ i, ggLin (p := 3) ι ((e (CoxeterMatrix.E₆.simple i) : ↥A) : MulAut ↥Bs) =
      reflection (hα i)) :
    Nat.card (e6Weyl hα) = Nat.card A := by
  rw [← map_ggLin_eq_e6Weyl ι e hα he,
    Subgroup.card_map_of_injective (ggLin_injective (p := 3) ι)]

end Group

variable [Finite V] {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
  {B : LinearMap.BilinForm (ZMod 3) V}

theorem bilinForm_apply_e6Weyl (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) (u v : V) : B (g u) (g v) = B u v := by
  have key : ∀ g ∈ e6Weyl hα, ∀ u v : V, B (g u) (g v) = B u v := by
    intro g hg
    refine Subgroup.closure_induction (k := Set.range fun i => reflection (hα i))
      (p := fun g _ => ∀ u v : V, B (g u) (g v) = B u v) ?_ ?_ ?_ ?_ hg
    · rintro x ⟨i, rfl⟩ u v
      exact bilinForm_reflection hP hV hB hα i u v
    · intro u v
      simp
    · intro x y _ _ hx hy u v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
    · intro x _ hx u v
      have h := hx (x⁻¹ u) (x⁻¹ v)
      simpa using h.symm
  exact key g hg u v

theorem exists_mem_e6Weyl_apply_eq (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : B u u = B v v) :
    ∃ g ∈ e6Weyl hα, g u = v := by
  classical
  have h3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hb2 : B (h 0) (h 0) = 2 := by rw [hB 0 (h 0), hα 0]
  have hr2 : h 0 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hb2
    exact absurd hb2 (by decide)
  have hb1 : B (h 0 + h 1) (h 0 + h 1) = 1 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
    rw [hB 0 (h 0), hB 0 (h 1), hB 1 (h 0), hB 1 (h 1), hα 0, hP 0 1, hP 1 0, hα 1]
    decide
  have hr1 : h 0 + h 1 ≠ 0 := by
    intro hz
    have h2 : α 0 (h 0 + h 1) = 2 := by
      rw [map_add, hα 0, hP 0 1]
      decide
    rw [hz, map_zero] at h2
    exact absurd h2.symm (by decide)
  have hb0 : B (h 0 + h 1 + h 5) (h 0 + h 1 + h 5) = 0 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
    rw [hB 0 (h 0), hB 0 (h 1), hB 0 (h 5), hB 1 (h 0), hB 1 (h 1), hB 1 (h 5),
      hB 5 (h 0), hB 5 (h 1), hB 5 (h 5), hα 0, hP 0 1, hP 0 5, hP 1 0, hα 1, hP 1 5,
      hP 5 0, hP 5 1, hα 5]
    decide
  have hr0 : h 0 + h 1 + h 5 ≠ 0 := by
    intro hz
    have h2 : α 0 (h 0 + h 1 + h 5) = 2 := by
      rw [map_add, map_add, hα 0, hP 0 1, hP 0 5]
      decide
    rw [hz, map_zero] at h2
    exact absurd h2.symm (by decide)
  have hs2 : Nat.card (MulAction.orbit (e6Weyl hα) (h 0)) = 72 := by
    rcases orbit_cases hP hV hB hα hr2 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [hb2] at h; exact absurd h (by decide)
    · rw [hb2] at h; exact absurd h (by decide)
  have hs1 : Nat.card (MulAction.orbit (e6Weyl hα) (h 0 + h 1)) = 90 := by
    rcases orbit_cases hP hV hB hα hr1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · rw [hb1] at h; exact absurd h (by decide)
    · rw [hb1] at h; exact absurd h (by decide)
    · exact h
  have hs0 : Nat.card (MulAction.orbit (e6Weyl hα) (h 0 + h 1 + h 5)) = 80 := by
    rcases orbit_cases hP hV hB hα hr0 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [hb0] at h; exact absurd h (by decide)
    · exact h
    · rw [hb0] at h; exact absurd h (by decide)
  have horb : ∀ r : V, r ≠ 0 →
      MulAction.orbit (e6Weyl hα) r ⊆ {w : V | w ≠ 0 ∧ B w w = B r r} := by
    intro r hr w hw
    obtain ⟨g, -, rfl⟩ := MulAction.mem_orbit_iff.mp hw
    refine ⟨?_, ?_⟩
    · intro h0
      have h0' : (g : V ≃ₗ[ZMod 3] V) r = 0 := by
        simpa [Subgroup.smul_def, LinearEquiv.smul_def] using h0
      exact hr ((g : V ≃ₗ[ZMod 3] V).injective (by rw [h0', map_zero]))
    · simpa [Subgroup.smul_def, LinearEquiv.smul_def] using
        bilinForm_apply_e6Weyl hP hV hB hα g.2 r r
  have hN : Nat.card {w : V // w ≠ 0} = 242 := by
    have hsplit : Nat.card V = Nat.card {w : V // w = 0} + Nat.card {w : V // w ≠ 0} := by
      have e : ({w : V // w = 0} ⊕ {w : V // ¬(w = 0)}) ≃ V :=
        Equiv.sumCompl (fun w : V => w = 0)
      rw [← Nat.card_congr e, Nat.card_sum]
    have h1 : Nat.card {w : V // w = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩, ⟨⟨0, rfl⟩⟩⟩
    have h243 : Nat.card V = 243 := by rw [hV]; norm_num
    omega
  have hU : ∀ s t : Set V, Disjoint s t → Nat.card ↑(s ∪ t) = Nat.card ↑s + Nat.card ↑t := by
    intro s t h
    rw [Nat.card_congr (Equiv.Set.union h), Nat.card_sum]
  have hd01 : Disjoint {w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)}
      {w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} := by
    rw [Set.disjoint_left]
    rintro w ⟨-, h0⟩ ⟨-, h1⟩
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hd2 : Disjoint ({w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} ∪
      {w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)}) {w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} := by
    rw [Set.disjoint_left]
    rintro w (⟨-, h0⟩ | ⟨-, h1⟩) ⟨-, h2⟩
    · rw [h0] at h2; exact absurd h2 (by decide)
    · rw [h1] at h2; exact absurd h2 (by decide)
  have hcover : {w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} ∪
      {w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} ∪
      {w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} = {w : V | w ≠ 0} := by
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((⟨hw, -⟩ | ⟨hw, -⟩) | ⟨hw, -⟩) <;> exact hw
    · intro hw
      rcases h3 (B w w) with h | h | h
      · exact Or.inl (Or.inl ⟨hw, h⟩)
      · exact Or.inl (Or.inr ⟨hw, h⟩)
      · exact Or.inr ⟨hw, h⟩
  have hsum : Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} +
      Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} +
      Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} = 242 := by
    rw [← hU _ _ hd01, ← hU _ _ hd2, hcover]
    exact hN
  have hlb2 : 72 ≤ Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} := by
    have hsub : MulAction.orbit (e6Weyl hα) (h 0) ⊆
        {w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} := by
      have h := horb (h 0) hr2
      simpa only [hb2] using h
    have h := Nat.card_mono (Set.toFinite _) hsub
    rw [hs2] at h
    exact h
  have hlb1 : 90 ≤ Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} := by
    have hsub : MulAction.orbit (e6Weyl hα) (h 0 + h 1) ⊆
        {w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} := by
      have h := horb (h 0 + h 1) hr1
      simpa only [hb1] using h
    have h := Nat.card_mono (Set.toFinite _) hsub
    rw [hs1] at h
    exact h
  have hlb0 : 80 ≤ Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} := by
    have hsub : MulAction.orbit (e6Weyl hα) (h 0 + h 1 + h 5) ⊆
        {w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} := by
      have h := horb (h 0 + h 1 + h 5) hr0
      simpa only [hb0] using h
    have h := Nat.card_mono (Set.toFinite _) hsub
    rw [hs0] at h
    exact h
  have hcard2 : Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} = 72 := by omega
  have hcard1 : Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} = 90 := by omega
  have hcard0 : Nat.card ↑{w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} = 80 := by omega
  have hT2 : MulAction.orbit (e6Weyl hα) (h 0) =
      {w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} := by
    have hsub : MulAction.orbit (e6Weyl hα) (h 0) ⊆
        {w : V | w ≠ 0 ∧ B w w = (2 : ZMod 3)} := by
      have h := horb (h 0) hr2
      simpa only [hb2] using h
    refine Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hsub ?_
    rw [hcard2, hs2]
  have hT1 : MulAction.orbit (e6Weyl hα) (h 0 + h 1) =
      {w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} := by
    have hsub : MulAction.orbit (e6Weyl hα) (h 0 + h 1) ⊆
        {w : V | w ≠ 0 ∧ B w w = (1 : ZMod 3)} := by
      have h := horb (h 0 + h 1) hr1
      simpa only [hb1] using h
    refine Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hsub ?_
    rw [hcard1, hs1]
  have hT0 : MulAction.orbit (e6Weyl hα) (h 0 + h 1 + h 5) =
      {w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} := by
    have hsub : MulAction.orbit (e6Weyl hα) (h 0 + h 1 + h 5) ⊆
        {w : V | w ≠ 0 ∧ B w w = (0 : ZMod 3)} := by
      have h := horb (h 0 + h 1 + h 5) hr0
      simpa only [hb0] using h
    refine Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hsub ?_
    rw [hcard0, hs0]
  have finish : ∀ (t : ZMod 3) (r : V),
      MulAction.orbit (e6Weyl hα) r = {w : V | w ≠ 0 ∧ B w w = t} →
      ∀ x : V, x ≠ 0 → B x x = t → x ∈ MulAction.orbit (e6Weyl hα) r := by
    intro t r heq x hx hxt
    rw [heq]
    exact ⟨hx, hxt⟩
  rcases h3 (B u u) with ht | ht | ht
  · have hmu := finish 0 (h 0 + h 1 + h 5) hT0 u hu (by rw [ht])
    have hmv := finish 0 (h 0 + h 1 + h 5) hT0 v hv (by rw [← huv, ht])
    obtain ⟨g, -, hg⟩ := MulAction.mem_orbit_iff.mp
      (by rw [MulAction.orbit_eq_iff.mpr hmu]; exact hmv)
    exact ⟨g, g.2, by simp [Subgroup.smul_def, LinearEquiv.smul_def]⟩
  · have hmu := finish 1 (h 0 + h 1) hT1 u hu (by rw [ht])
    have hmv := finish 1 (h 0 + h 1) hT1 v hv (by rw [← huv, ht])
    obtain ⟨g, -, hg⟩ := MulAction.mem_orbit_iff.mp
      (by rw [MulAction.orbit_eq_iff.mpr hmu]; exact hmv)
    exact ⟨g, g.2, by simp [Subgroup.smul_def, LinearEquiv.smul_def]⟩
  · have hmu := finish 2 (h 0) hT2 u hu (by rw [ht])
    have hmv := finish 2 (h 0) hT2 v hv (by rw [← huv, ht])
    obtain ⟨g, -, hg⟩ := MulAction.mem_orbit_iff.mp
      (by rw [MulAction.orbit_eq_iff.mpr hmu]; exact hmv)
    exact ⟨g, g.2, by simp [Subgroup.smul_def, LinearEquiv.smul_def]⟩

theorem stabilizer_cases (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hW : Nat.card (e6Weyl hα) = 51840) {v : V} (hv : v ≠ 0) :
    (B v v = 2 ∧ Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 720) ∨
      (B v v = 0 ∧ Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 648) ∨
      (B v v = 1 ∧ Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 576) := by
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (by simpa using congrFun h))
  have hos : Nat.card (MulAction.orbit (e6Weyl hα) v) *
      Nat.card (MulAction.stabilizer (e6Weyl hα) v) = 51840 := by
    let : Fintype ↥(e6Weyl hα) := Fintype.ofFinite _
    let : Fintype ↑(MulAction.orbit (e6Weyl hα) v) := Fintype.ofFinite _
    let : Fintype ↥(MulAction.stabilizer (e6Weyl hα) v) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥(e6Weyl hα)) v
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hW] at h
    exact h
  rcases orbit_cases hP hV hB hα hv with ⟨hb, hs⟩ | ⟨hb, hs⟩ | ⟨hb, hs⟩
  · exact Or.inl ⟨hb, by rw [hs] at hos; omega⟩
  · exact Or.inr (Or.inl ⟨hb, by rw [hs] at hos; omega⟩)
  · exact Or.inr (Or.inr ⟨hb, by rw [hs] at hos; omega⟩)

theorem bilinForm_self_eq_two_of_mem_e6Weyl
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) (hV : Nat.card V = 3 ^ 5)
    (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2) {g : V ≃ₗ[ZMod 3] V}
    (hg : g ∈ e6Weyl hα) {v : V} {f : Dual (ZMod 3) V} (hfv : f v = 2)
    (hgv : ∀ u, g u = u - f u • v) : B v v = 2 := by
  have h2x : ∀ x : ZMod 3, (2 : ZMod 3) * x = -x := by decide
  have hxx : ∀ x : ZMod 3, x + x = 2 * x := by decide
  have hiso : ∀ u w : V, B (g u) (g w) = B u w := fun u w =>
    bilinForm_apply_e6Weyl hP hV hB hα hg u w
  have hsym : ∀ u w : V, B u w = B w u := fun u w => bilinForm_symm hP hV hB u w
  have hkey : ∀ u : V, f u * B v v = 2 * B v u := by
    intro u
    have h := hiso u v
    rw [hgv u, hgv v, hfv] at h
    have hv2 : v - (2 : ZMod 3) • v = -v := by module
    rw [hv2] at h
    have hexp : B (u - f u • v) (-v) = -(B u v - f u * B v v) := by
      simp only [LinearMap.BilinForm.neg_right, LinearMap.BilinForm.sub_left,
        LinearMap.BilinForm.smul_left]
      rfl
    have h2 : -(B u v - f u * B v v) = B u v := hexp.symm.trans h
    have h2' : f u * B v v - B u v = B u v :=
      (neg_sub (B u v) (f u * B v v)).symm.trans h2
    have h3 : f u * B v v = B u v + B u v := sub_eq_iff_eq_add.mp h2'
    rw [show B v u = B u v from (hsym u v).symm, h3, hxx]
  rcases (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) (B v v) with ht | ht | ht
  · have hzero : ∀ u, B v u = 0 := by
      intro u
      have h := hkey u
      rw [ht, mul_zero] at h
      have h2 : (2 : ZMod 3) * B v u = 0 := h.symm
      exact (mul_eq_zero.mp h2).resolve_left (by decide)
    have hv0 : v = 0 := bilinForm_nondegenerate hP hV hB hzero
    rw [hv0, map_zero] at hfv
    exact absurd hfv (by decide)
  · have hfe : ∀ u, f u = -(B v u) := by
      intro u
      have h := hkey u
      rw [ht, mul_one] at h
      rw [h, h2x]
    refine absurd (fun u => ?_) (not_mem_e6Weyl_reflection hP hV hB hα ht hg)
    rw [hgv u, hfe u,
      show (-(B v u)) • v = -(B v u • v) from neg_smul (B v u) v, sub_neg_eq_add]
  · exact ht

theorem bilinForm_self_eq_two_of_neg (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) {v : V} (hv : v ≠ 0) (hgv : g v = -v)
    (hgu : ∀ u, ∃ c : ZMod 3, g u - u = c • v) : B v v = 2 := by
  classical
  choose c hc using hgu
  have hinj : Function.Injective fun x : ZMod 3 => x • v := smul_left_injective (ZMod 3) hv
  have hcadd : ∀ a b : V, c (a + b) = c a + c b := by
    intro a b
    refine hinj ?_
    change c (a + b) • v = (c a + c b) • v
    rw [add_smul, ← hc a, ← hc b, ← hc (a + b), map_add]
    abel
  have hcsmul : ∀ (r : ZMod 3) (a : V), c (r • a) = r * c a := by
    intro r a
    refine hinj ?_
    change c (r • a) • v = (r * c a) • v
    calc c (r • a) • v = g (r • a) - r • a := by rw [hc (r • a)]
      _ = r • g a - r • a := by rw [map_smul]
      _ = r • (g a - a) := by rw [smul_sub]
      _ = r • (c a • v) := by rw [hc a]
      _ = (r * c a) • v := by rw [mul_smul]
  let f : Dual (ZMod 3) V :=
    { toFun := fun u => -(c u)
      map_add' := by intro a b; rw [hcadd a b]; abel
      map_smul' := by
        intro r a
        have h1 : c (r • a) = r * c a := hcsmul r a
        have h2 : r • -(c a) = -(r * c a) := by
          rw [smul_eq_mul]
          exact mul_neg r (c a)
        rw [h1]
        exact h2.symm }
  have hneg1 : (-1 : ZMod 3) • v = -v := by
    rw [show (-1 : ZMod 3) • v = -((1 : ZMod 3) • v) from neg_smul 1 v, one_smul]
  have hcv : c v = 1 := by
    have h := hc v
    rw [hgv] at h
    have h4 : -v - v = (-2 : ZMod 3) • v := by
      have hz : -v - v = (-2 : ℤ) • v := by
        calc -v - v = -(v + v) := by abel
          _ = -((2 : ℤ) • v) := by rw [two_zsmul]
          _ = (-2 : ℤ) • v := by rw [← neg_zsmul]
      rw [hz]
      exact (Int.cast_smul_eq_zsmul (R := ZMod 3) (-2) v).symm
    have h1 : c v • v = (1 : ZMod 3) • v := by
      rw [← h, one_smul, h4, show (-2 : ZMod 3) = 1 from by decide, one_smul]
    exact hinj h1
  have hfv : f v = 2 := by
    change -(c v) = 2
    rw [hcv]
    decide
  have hg' : ∀ u, g u = u - f u • v := by
    intro u
    have h := hc u
    change g u = u - (-(c u)) • v
    rw [show (-(c u)) • v = -(c u • v) from neg_smul (c u) v, sub_neg_eq_add, ← h]
    abel
  exact bilinForm_self_eq_two_of_mem_e6Weyl hP hV hB hα hg hfv hg'

end CFSG.StandardType.E6QTwo
