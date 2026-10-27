module

public import CFSG.Quasithin.EmptyFaithful.SBc15WDefs
public import CFSG.Quasithin.Background.GoldschmidtS146PWreath

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.GoldS146P
open scoped commutatorElement

namespace SBc15

namespace R3

section Generic

variable {D : Type} [Group D] {Q : Type} [Group Q]

theorem comm_of_two_point {g : Q} (hall : ∀ y : Q, y = 1 ∨ y = g) (a b : Q) : a * b = b * a := by
  rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp

theorem perfect_le_base {g : Q} (hall : ∀ y : Q, y = 1 ∨ y = g) (D' : Subgroup D) [D'.Normal]
    [Group.IsSolvable (D ⧸ D')] {N : Subgroup (D ≀ᵣ Q)} (hN : ⁅N, N⁆ = N) :
    ∀ x ∈ N, x.right = 1 ∧ ∀ i, x.left i ∈ D' := by
  have : Group.IsPerfect N := Subgroup.isPerfect_iff.mpr hN
  have : Group.IsSolvable Q := Group.isSolvable_of_comm (comm_of_two_point hall)
  have hR : ∀ x ∈ N, x.right = 1 := by
    have h := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
      ((RegularWreathProduct.rightHom : D ≀ᵣ Q →* Q).comp N.subtype)
    intro x hx
    exact DFunLike.congr_fun h ⟨x, hx⟩
  have hL : ∀ x ∈ N, ∀ y, x.left y ∈ D' := by
    intro x hx y
    let φ : N →* D ⧸ D' := MonoidHom.mk' (fun p => QuotientGroup.mk' D' ((p : D ≀ᵣ Q).left y))
      (by
        intro a b
        have ha := hR (a : D ≀ᵣ Q) a.2
        rw [Subgroup.coe_mul, left_mul_of_right_eq_one ha, map_mul])
    have h := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one φ
    have := DFunLike.congr_fun h ⟨x, hx⟩
    exact (QuotientGroup.eq_one_iff _).mp this
  exact fun x hx => ⟨hR x hx, hL x hx⟩

theorem left_inl_conj (g : Q) (x : D ≀ᵣ Q) (z : Q) :
    (RegularWreathProduct.inl g * x * (RegularWreathProduct.inl g)⁻¹ : D ≀ᵣ Q).left z =
      x.left (g⁻¹ * z) := by
  simp [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left]

theorem left_commutator_of_right_eq_one {u x : D ≀ᵣ Q} (hu : u.right = 1) (hx : x.right = 1)
    (z : Q) :
    (u * x * u⁻¹ * x⁻¹).left z = u.left z * x.left z * (u.left z)⁻¹ * (x.left z)⁻¹ := by
  simp [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left, hu, hx]

theorem eq_bot_or_eq_of_normal_le {D' : Subgroup D} [IsSimpleGroup D'] {E : Subgroup D}
    [E.Normal] (hE : E ≤ D') : E = ⊥ ∨ E = D' := by
  have : (E.subgroupOf D').Normal := Subgroup.Normal.subgroupOf inferInstance D'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.subgroupOf D') with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.mp (h.mono_right hE)
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hE h

theorem eq_one_of_forall_comm {D' : Subgroup D} [IsSimpleGroup D']
    (hnc : ∃ a b : D', a * b ≠ b * a) {c : D'} (hc : ∀ d : D', d * c = c * d) : c = 1 := by
  have : (Subgroup.center D').Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D') with h | h
  · have hmem : c ∈ Subgroup.center D' := Subgroup.mem_center_iff.mpr hc
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center D' := by rw [h]; trivial
    exact absurd ((Subgroup.mem_center_iff.mp this) b).symm hab

variable [DecidableEq Q]

theorem embW_mem_of_normal (D' : Subgroup D) [D'.Normal] [IsSimpleGroup D']
    (hnc : ∃ a b : D', a * b ≠ b * a) {N : Subgroup (D ≀ᵣ Q)} [N.Normal]
    (hNP : ∀ x ∈ N, x.right = 1 ∧ ∀ i, x.left i ∈ D') {y : Q} {x : D ≀ᵣ Q} (hx : x ∈ N)
    (hxy : x.left y ≠ 1) : ∀ d ∈ D', embW y d ∈ N := by
  set E : Subgroup D := N.comap (embW y) with hE
  have hEn : E.Normal := Subgroup.Normal.comap inferInstance _
  have hED : E ≤ D' := fun e he => by
    have := (hNP _ he).2 y
    simpa using this
  have hEne : E ≠ ⊥ := by
    intro hbot
    obtain ⟨hxr, hxl⟩ := hNP x hx
    set c : D' := ⟨x.left y, hxl y⟩ with hc
    have hc1 : c ≠ 1 := fun h => hxy (congrArg Subtype.val h)
    refine hc1 (eq_one_of_forall_comm hnc fun d => ?_)
    have hu : (embW y (d : D)).right = 1 := rfl
    have hconj : embW y (d : D) * x * (embW y (d : D))⁻¹ * x⁻¹ ∈ N :=
      N.mul_mem (‹N.Normal›.conj_mem x hx _) (N.inv_mem hx)
    have heq : embW y (d : D) * x * (embW y (d : D))⁻¹ * x⁻¹ =
        embW y ⁅(d : D), x.left y⁆ := by
      refine RegularWreathProduct.ext (funext fun z => ?_) ?_
      · rw [left_commutator_of_right_eq_one hu hxr z]
        by_cases hz : z = y
        · subst hz
          simp only [embW_left, Pi.mulSingle_eq_same]
          exact (commutatorElement_def _ _).symm
        · simp only [embW_left, Pi.mulSingle_eq_of_ne hz, inv_one, one_mul, mul_one,
            mul_inv_cancel]
      · rw [show (embW y ⁅(d : D), x.left y⁆).right = 1 from rfl]
        simp only [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hu, hxr,
          mul_one, inv_one]
    have hmem : ⁅(d : D), x.left y⁆ ∈ E := by
      show embW y _ ∈ N
      rw [← heq]
      exact hconj
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact Subtype.ext hmem
  rcases eq_bot_or_eq_of_normal_le hED with h | h
  · exact absurd h hEne
  · intro d hd
    have : d ∈ E := by rw [h]; exact hd
    exact this

theorem mem_iff_of_normal_perfect {g : Q} (hg1 : g ≠ 1) (hall : ∀ y : Q, y = 1 ∨ y = g)
    (D' : Subgroup D) [D'.Normal] [IsSimpleGroup D'] (hnc : ∃ a b : D', a * b ≠ b * a)
    [Group.IsSolvable (D ⧸ D')] {N : Subgroup (D ≀ᵣ Q)} [N.Normal] (hN : ⁅N, N⁆ = N)
    (hne : N ≠ ⊥) (w : D ≀ᵣ Q) : w ∈ N ↔ w.right = 1 ∧ ∀ i, w.left i ∈ D' := by
  have hNP := perfect_le_base hall D' hN
  refine ⟨fun hw => hNP w hw, fun ⟨hwr, hwl⟩ => ?_⟩
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : (x : D ≀ᵣ Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨y₀, hy₀⟩ : ∃ y, (x : D ≀ᵣ Q).left y ≠ 1 := by
    by_contra h
    push Not at h
    exact hx1' (RegularWreathProduct.ext (funext h) ((hNP x x.2).1))
  have hgg : g * g = 1 := by
    rcases hall (g * g) with h | h
    · exact h
    · exact absurd (mul_eq_right.mp h) hg1
  have hall' : ∀ z : Q, z = y₀ ∨ z = g * y₀ := by
    intro z
    rcases hall z with rfl | rfl <;> rcases hall y₀ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [hgg])
    · exact Or.inr (by rw [mul_one])
    · exact Or.inl rfl
  have hne' : g * y₀ ≠ y₀ := fun h => hg1 (mul_eq_right.mp h)
  have h0 := embW_mem_of_normal D' hnc hNP x.2 hy₀
  have hx'N : (RegularWreathProduct.inl g * (x : D ≀ᵣ Q) * (RegularWreathProduct.inl g)⁻¹) ∈ N :=
    ‹N.Normal›.conj_mem _ x.2 _
  have hx'1 : (RegularWreathProduct.inl g * (x : D ≀ᵣ Q) *
      (RegularWreathProduct.inl g)⁻¹ : D ≀ᵣ Q).left (g * y₀) ≠ 1 := by
    rw [left_inl_conj, inv_mul_cancel_left]
    exact hy₀
  have h1 := embW_mem_of_normal D' hnc hNP hx'N hx'1
  have hdec : w = embW y₀ (w.left y₀) * embW (g * y₀) (w.left (g * y₀)) := by
    refine RegularWreathProduct.ext (funext fun z => ?_) ?_
    · rw [left_mul_of_right_eq_one (embW_right y₀ _)]
      rcases hall' z with rfl | rfl
      · simp [Pi.mulSingle_eq_of_ne hne'.symm]
      · simp [Pi.mulSingle_eq_of_ne hne']
    · simp [hwr]
  rw [hdec]
  exact N.mul_mem (h0 _ (hwl _)) (h1 _ (hwl _))

end Generic

section Wreath

variable {D : Type} [Group D]

theorem mem_wrPerf {D' : Subgroup D} {x : D ≀ᵣ Multiplicative (ZMod 2)} :
    x ∈ wrPerf D' ↔ x.right = 1 ∧ ∀ i, x.left i ∈ D' := Iff.rfl

theorem eq_wrPerf_of_normal_perfect (D' : Subgroup D) [D'.Normal] [IsSimpleGroup D']
    (hnc : ∃ a b : D', a * b ≠ b * a) [Group.IsSolvable (D ⧸ D')]
    {N : Subgroup (D ≀ᵣ Multiplicative (ZMod 2))} [N.Normal] (hN : ⁅N, N⁆ = N) (hne : N ≠ ⊥) :
    N = wrPerf D' :=
  Subgroup.ext fun w =>
    (mem_iff_of_normal_perfect (g := Multiplicative.ofAdd (1 : ZMod 2)) (by decide) (by decide)
      D' hnc hN hne w).trans mem_wrPerf.symm

end Wreath

end R3

end SBc15

end CFSG.Quasithin
