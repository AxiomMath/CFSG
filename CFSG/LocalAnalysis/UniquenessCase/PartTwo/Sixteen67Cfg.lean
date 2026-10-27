module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Wreath
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Cfg1667 (M V W₁ W₂ : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  sup_eq : W₁ ⊔ W₂ = V
  inf_eq : W₁ ⊓ W₂ = ⊥
  card₁ : Nat.card W₁ = 4
  card₂ : Nat.card W₂ = 4
  normalizer_eq : normalizer (V : Set G) = M
  perm : ∀ m ∈ M, (conjSubgroup W₁ m = W₁ ∧ conjSubgroup W₂ m = W₂) ∨
    (conjSubgroup W₁ m = W₂ ∧ conjSubgroup W₂ m = W₁)
  centralizer_le : ∀ F : Subgroup G, F ≤ V → 4 ≤ Nat.card F → centralizer (F : Set G) ≤ M
  card_inf_le : ∀ y : G, y ∉ M → Nat.card (V ⊓ conjSubgroup V y : Subgroup G) ≤ 2
  comm_eq_bot : ∀ y : G, conjSubgroup V y ≤ M → ⁅V, conjSubgroup V y⁆ = ⊥

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G}

private theorem exists_mul_of_mem_sup {W₁ W₂ : Subgroup G}
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) {v : G}
    (hv : v ∈ W₁ ⊔ W₂) : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v := by
  rw [Subgroup.sup_eq_closure] at hv
  refine Subgroup.closure_induction (p := fun v _ => ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v)
    ?_ ?_ ?_ ?_ hv
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, W₂.one_mem, by simp⟩
    · exact ⟨1, W₁.one_mem, x, hx, by simp⟩
  · exact ⟨1, W₁.one_mem, 1, W₂.one_mem, by simp⟩
  · rintro x y hx hy ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨a₁ * b₁, W₁.mul_mem ha₁ hb₁, a₂ * b₂, W₂.mul_mem ha₂ hb₂, by
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm b₁ hb₁ a₂ ha₂]
        _ = a₁ * a₂ * (b₁ * b₂) := by group⟩
  · rintro x hx ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    exact ⟨a₁⁻¹, W₁.inv_mem ha₁, a₂⁻¹, W₂.inv_mem ha₂,
      by rw [← mul_inv_rev a₂ a₁, hcomm a₁ ha₁ a₂ ha₂]⟩

private theorem mul_eq_mul_iff {W₁ W₂ : Subgroup G} (hinf : W₁ ⊓ W₂ = ⊥)
    {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ W₁) (ha₂ : a₂ ∈ W₂) (hb₁ : b₁ ∈ W₁) (hb₂ : b₂ ∈ W₂) :
    a₁ * a₂ = b₁ * b₂ ↔ a₁ = b₁ ∧ a₂ = b₂ := by
  constructor
  · intro h
    have hmem : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
      calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
        _ = b₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by rw [h]
        _ = b₂ * a₂⁻¹ := by group
    have h1 : b₁⁻¹ * a₁ ∈ W₁ := W₁.mul_mem (W₁.inv_mem hb₁) ha₁
    have h2 : b₂ * a₂⁻¹ ∈ W₂ := W₂.mul_mem hb₂ (W₂.inv_mem ha₂)
    have hbot : b₁⁻¹ * a₁ = 1 := by
      have : b₁⁻¹ * a₁ ∈ W₁ ⊓ W₂ := ⟨h1, by rw [hmem]; exact h2⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.mp this
    have ha₁eq : a₁ = b₁ := by
      have h' : b₁ * (b₁⁻¹ * a₁) = b₁ * 1 := congrArg (fun t => b₁ * t) hbot
      calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
        _ = b₁ * 1 := h'
        _ = b₁ := by rw [mul_one]
    have h2' : a₁ * a₂ = a₁ * b₂ := by rw [h, ha₁eq]
    exact ⟨ha₁eq, mul_left_cancel h2'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem card_sup_of_commute_of_inf_eq_bot (L R : Subgroup G)
    (hcomm : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) (hinf : L ⊓ R = ⊥) :
    Nat.card (L ⊔ R : Subgroup G) = Nat.card L * Nat.card R := by
  let f : ↥L × ↥R → ↥(L ⊔ R) := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
      have hG : (x₁ : G) * (y₁ : G) = (x₂ : G) * (y₂ : G) := congrArg Subtype.val h
      have huniq := (mul_eq_mul_iff hinf x₁.2 y₁.2 x₂.2 y₂.2).mp hG
      exact Prod.ext (Subtype.ext huniq.1) (Subtype.ext huniq.2)
    · intro z
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup hcomm z.2
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem card_V (h : Cfg1667 M V W₁ W₂) : Nat.card V = 16 := by
  have hW₁V : W₁ ≤ V := by rw [← h.sup_eq]; exact le_sup_left
  have hW₂V : W₂ ≤ V := by rw [← h.sup_eq]; exact le_sup_right
  have hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm ⟨x, hW₁V hx⟩ ⟨y, hW₂V hy⟩)
  have hcard := card_sup_of_commute_of_inf_eq_bot W₁ W₂ hcomm h.inf_eq
  rw [h.sup_eq, h.card₁, h.card₂] at hcard
  simpa using hcard

theorem le_M (h : Cfg1667 M V W₁ W₂) : V ≤ M := by
  rw [← h.normalizer_eq]
  exact Subgroup.le_normalizer

private theorem conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup A B _

theorem conj (h : Cfg1667 M V W₁ W₂) (g : G) :
    Cfg1667 (conjSubgroup M g) (conjSubgroup V g) (conjSubgroup W₁ g) (conjSubgroup W₂ g) := by
  refine ⟨E3.isElemAbelian_conjSubgroup h.elemAbelian g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [← conjSubgroup_sup, h.sup_eq]
  · simp only [← E3.conjSubgroup_inf, h.inf_eq, E3.conjSubgroup_bot]
  · simp only [E3.card_conjSubgroup, h.card₁]
  · simp only [E3.card_conjSubgroup, h.card₂]
  · simp only [← E3.conjSubgroup_normalizer, h.normalizer_eq]
  · intro m hm
    set m' : G := g * m * g⁻¹ with hm'def
    have hm'M : m' ∈ M := by
      rw [hm'def]
      exact mem_conjSubgroup_iff.mp hm
    have hmul : g * m = m' * g := by rw [hm'def]; group
    have h₁ : conjSubgroup (conjSubgroup W₁ g) m = conjSubgroup (conjSubgroup W₁ m') g := by
      rw [conjSubgroup_conjSubgroup, hmul, ← conjSubgroup_conjSubgroup]
    have h₂ : conjSubgroup (conjSubgroup W₂ g) m = conjSubgroup (conjSubgroup W₂ m') g := by
      rw [conjSubgroup_conjSubgroup, hmul, ← conjSubgroup_conjSubgroup]
    rcases h.perm m' hm'M with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨h₁.trans (by rw [ha]), h₂.trans (by rw [hb])⟩
    · exact Or.inr ⟨h₁.trans (by rw [ha]), h₂.trans (by rw [hb])⟩
  · intro F hFV hF4
    set F' : Subgroup G := conjSubgroup F g⁻¹ with hF'def
    have hF'V : F' ≤ V := by
      have hmono := E3.conjSubgroup_mono_left g⁻¹ hFV
      rw [E3.conjSubgroup_conj_inv] at hmono
      rwa [hF'def]
    have hF'4 : 4 ≤ Nat.card F' := by
      rw [hF'def, E3.card_conjSubgroup]
      exact hF4
    have hle : centralizer (F' : Set G) ≤ M := h.centralizer_le F' hF'V hF'4
    have hcentral : conjSubgroup (centralizer (F' : Set G)) g = centralizer (F : Set G) := by
      rw [E3.conjSubgroup_centralizer, hF'def, E3.conjSubgroup_inv_conj]
    rw [← hcentral]
    exact E3.conjSubgroup_mono_left g hle
  · intro y hyM
    set y' : G := g * y * g⁻¹ with hy'def
    have hy'M : y' ∉ M := fun hy' => hyM (by
      rw [mem_conjSubgroup_iff]
      rwa [← hy'def])
    have hyy : g * y = y' * g := by rw [hy'def]; group
    have hc : conjSubgroup (conjSubgroup V g) y = conjSubgroup (conjSubgroup V y') g := by
      rw [conjSubgroup_conjSubgroup, hyy, ← conjSubgroup_conjSubgroup]
    have hinf : (conjSubgroup V g ⊓ conjSubgroup (conjSubgroup V g) y : Subgroup G)
        = conjSubgroup (V ⊓ conjSubgroup V y') g := by
      rw [hc, ← E3.conjSubgroup_inf]
    rw [hinf, E3.card_conjSubgroup]
    exact h.card_inf_le y' hy'M
  · intro y hyle
    set y' : G := g * y * g⁻¹ with hy'def
    have hyy : g * y = y' * g := by rw [hy'def]; group
    have hc : conjSubgroup (conjSubgroup V g) y = conjSubgroup (conjSubgroup V y') g := by
      rw [conjSubgroup_conjSubgroup, hyy, ← conjSubgroup_conjSubgroup]
    have hy'M : conjSubgroup V y' ≤ M := by
      refine (E3.conjSubgroup_le_conjSubgroup_iff (A := conjSubgroup V y') (B := M) g).mp ?_
      rw [← hc]
      exact hyle
    rw [hc, ← E3.conjSubgroup_commutator V (conjSubgroup V y') g,
      h.comm_eq_bot y' hy'M, E3.conjSubgroup_bot]

end Cfg1667

theorem inCalO_bot_swap {n : ℕ} {M V : Subgroup G} {g : G} (h : InCalO n M ⊥ V g) :
    InCalO n (conjSubgroup M g) ⊥ (conjSubgroup V g) g⁻¹ := by
  obtain ⟨hF, hD⟩ := h
  refine ⟨by simpa only [E3.conjSubgroup_bot] using (oFirst_swap n M ⊥ V g).2 hD, ?_⟩
  refine (oFirst_swap n (conjSubgroup M g) ⊥ (conjSubgroup V g) g⁻¹).1 ?_
  simpa only [E3.conjSubgroup_bot, inv_inv, conjSubgroup_conjSubgroup_inv] using hF

theorem inCalO_bot_of_mem_calO {n : ℕ} {M V : Subgroup G} (hN : normalizer (V : Set G) = M)
    {g : G} (hg : conjSubgroup V g ∈ calO n M ⊥ V) : InCalO n M ⊥ V g := by
  rw [calO, Set.mem_ofPred_eq] at hg
  obtain ⟨g', hgg', hO⟩ := hg
  have hconj : conjSubgroup V (g * g'⁻¹) = V := by
    have h := congrArg (fun X => conjSubgroup X g'⁻¹) hgg'
    rw [conjSubgroup_conjSubgroup V g g'⁻¹, E3.conjSubgroup_conj_inv V g'] at h
    exact h
  have hmem : g * g'⁻¹ ∈ M := by
    rw [← hN]
    exact conjSubgroup_eq_iff_mem_normalizer.mp hconj
  have hMeq : conjSubgroup M g = conjSubgroup M g' := by
    have hg_eq : g = (g * g'⁻¹) * g' := by group
    calc conjSubgroup M g = conjSubgroup M ((g * g'⁻¹) * g') :=
          congrArg (fun t => conjSubgroup M t) hg_eq
      _ = conjSubgroup (conjSubgroup M (g * g'⁻¹)) g' := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup M g' := by
        rw [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hmem)]
  simp only [InCalO, OFirst, ODual, E3.conjSubgroup_bot] at hO ⊢
  rw [hgg', hMeq]
  exact hO

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
