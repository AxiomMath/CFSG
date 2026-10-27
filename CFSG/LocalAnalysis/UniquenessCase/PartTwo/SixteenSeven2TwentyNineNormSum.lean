module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormSchur
public import CFSG.Quasithin.Background.D2Z1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_norm_natSum3_invariant {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : NatSum3 L J) : ∀ y ∈ L, ∀ w ∈ J, y w ∈ J := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, -, -, -, -, -, rfl⟩ := hJ
  intro y hy w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨c, hc, d, hd, rfl⟩ := Subgroup.mem_sup.mp ha
  rw [map_mul, map_mul]
  exact Subgroup.mul_mem_sup
    (Subgroup.mul_mem_sup (hi₀.1 ⟨y, hy⟩ c hc) (hi₁.1 ⟨y, hy⟩ d hd))
    (hi₂.1 ⟨y, hy⟩ b hb)

theorem s16c167_norm_card_fixV_natSum3_le (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hJ : NatSum3 L J) {P : Subgroup (MulAut W)} (hPL : P ≤ L)
    (h2 : ∀ V : Subgroup W, XMod.IsIrr ↥L V → Nat.card ↥V = 8 → Nat.card ↥(V ⊓ fixV P) ≤ 2) :
    Nat.card ↥(J ⊓ fixV P) ≤ 8 := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, rfl⟩ := hJ
  have hP0 : ∀ g ∈ P, ∀ w ∈ I₀, g w ∈ I₀ := fun g hg => hi₀.1 ⟨g, hPL hg⟩
  have hP1 : ∀ g ∈ P, ∀ w ∈ I₁, g w ∈ I₁ := fun g hg => hi₁.1 ⟨g, hPL hg⟩
  have hP2 : ∀ g ∈ P, ∀ w ∈ I₂, g w ∈ I₂ := fun g hg => hi₂.1 ⟨g, hPL hg⟩
  have hP01 : ∀ g ∈ P, ∀ w ∈ I₀ ⊔ I₁, g w ∈ I₀ ⊔ I₁ := by
    intro g hg w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hP0 g hg a ha) (hP1 g hg b hb)
  have hd01 : IsDirectSum (I₀ ⊔ I₁) I₀ I₁ := ⟨rfl, h01⟩
  have hd012 : IsDirectSum (I₀ ⊔ I₁ ⊔ I₂) (I₀ ⊔ I₁) I₂ := ⟨rfl, h012⟩
  have e1 := rk_inf_fixV_add (A := P) hd012 hP01 hP2
  have e2 := rk_inf_fixV_add (A := P) hd01 hP0 hP1
  have hr0 : rk ↥(I₀ ⊓ fixV P) ≤ 1 := by
    have hle := h2 I₀ hi₀ hc₀
    rw [card_eq_two_pow hW (I₀ ⊓ fixV P)] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hle)
  have hr1 : rk ↥(I₁ ⊓ fixV P) ≤ 1 := by
    have hle := h2 I₁ hi₁ hc₁
    rw [card_eq_two_pow hW (I₁ ⊓ fixV P)] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hle)
  have hr2 : rk ↥(I₂ ⊓ fixV P) ≤ 1 := by
    have hle := h2 I₂ hi₂ hc₂
    rw [card_eq_two_pow hW (I₂ ⊓ fixV P)] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hle)
  have hrk : rk ↥((I₀ ⊔ I₁ ⊔ I₂) ⊓ fixV P) ≤ 3 := by omega
  rw [card_eq_two_pow hW ((I₀ ⊔ I₁ ⊔ I₂) ⊓ fixV P)]
  calc (2 : ℕ) ^ rk ↥((I₀ ⊔ I₁ ⊔ I₂) ⊓ fixV P) ≤ 2 ^ 3 :=
        Nat.pow_le_pow_right (by norm_num) hrk
    _ = 8 := by norm_num

theorem s16c167_norm_exists_summand_nontrivial {L Z : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : NatSum3 L J) (hZ : Nat.card ↥Z = 7) (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) :
    ∃ V : Subgroup W, V ≤ J ∧ XMod.IsIrr ↥L V ∧ Nat.card ↥V = 8 ∧ ∃ z ∈ Z, ∃ v ∈ V, z v ≠ v := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, -, -, rfl⟩ := hJ
  have hZne : Z ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ
    omega
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
  have hzmem : (z : MulAut W) ∈ Z := z.2
  have hzne : (z : MulAut W) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨w, hwJ, hzw⟩ := hZf (z : MulAut W) hzmem hzne
  have key : (∃ v ∈ I₀, (z : MulAut W) v ≠ v) ∨
      (∃ v ∈ I₁, (z : MulAut W) v ≠ v) ∨ (∃ v ∈ I₂, (z : MulAut W) v ≠ v) := by
    by_contra hc
    have h0 : ∀ v ∈ I₀, (z : MulAut W) v = v := by
      intro v hv
      by_contra hne
      exact hc (Or.inl ⟨v, hv, hne⟩)
    have h1 : ∀ v ∈ I₁, (z : MulAut W) v = v := by
      intro v hv
      by_contra hne
      exact hc (Or.inr (Or.inl ⟨v, hv, hne⟩))
    have h2 : ∀ v ∈ I₂, (z : MulAut W) v = v := by
      intro v hv
      by_contra hne
      exact hc (Or.inr (Or.inr ⟨v, hv, hne⟩))
    refine hzw ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hwJ
    obtain ⟨c, hc, d, hd, rfl⟩ := Subgroup.mem_sup.mp ha
    simp only [map_mul, h0 c hc, h1 d hd, h2 b hb]
  rcases key with ⟨v, hv, hvne⟩ | ⟨v, hv, hvne⟩ | ⟨v, hv, hvne⟩
  · exact ⟨I₀, le_sup_left.trans le_sup_left, hi₀, hc₀, z, hzmem, v, hv, hvne⟩
  · exact ⟨I₁, le_sup_right.trans le_sup_left, hi₁, hc₁, z, hzmem, v, hv, hvne⟩
  · exact ⟨I₂, le_sup_right, hi₂, hc₂, z, hzmem, v, hv, hvne⟩

theorem s16c167_norm_fixes_natSum3_of_fixes_irr {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : NatSum3 L J) {g : MulAut W} (hgL : ∀ y ∈ L, g * y = y * g)
    (h : ∀ V : Subgroup W, V ≤ J → XMod.IsIrr ↥L V → Nat.card ↥V = 8 →
      ∃ m ∈ V, m ≠ 1 ∧ g m = m) :
    ∀ w ∈ J, g w = w := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, -, -, rfl⟩ := hJ
  have hfix₀ : ∀ v ∈ I₀, g v = v := by
    obtain ⟨m, hm, hm1, hgm⟩ := h I₀ (le_sup_left.trans le_sup_left) hi₀ hc₀
    exact s16c167_norm_fixes_irr_of_fixes_ne_one hi₀ hgL hm hm1 hgm
  have hfix₁ : ∀ v ∈ I₁, g v = v := by
    obtain ⟨m, hm, hm1, hgm⟩ := h I₁ (le_sup_right.trans le_sup_left) hi₁ hc₁
    exact s16c167_norm_fixes_irr_of_fixes_ne_one hi₁ hgL hm hm1 hgm
  have hfix₂ : ∀ v ∈ I₂, g v = v := by
    obtain ⟨m, hm, hm1, hgm⟩ := h I₂ le_sup_right hi₂ hc₂
    exact s16c167_norm_fixes_irr_of_fixes_ne_one hi₂ hgL hm hm1 hgm
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨c, hc, d, hd, rfl⟩ := Subgroup.mem_sup.mp ha
  simp only [map_mul, hfix₀ c hc, hfix₁ d hd, hfix₂ b hb]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
