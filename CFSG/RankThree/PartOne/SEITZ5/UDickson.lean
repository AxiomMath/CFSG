module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Core
public import CFSG.RankThree.PartOne.SEITZ5.UGrp

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2 sl2_eq_top_of_root_groups u2_add u2_zero)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem eq_zero_or_one_of_card_two' {F : Type} [Field F] {k : Subfield F} (hk : Nat.card k = 2)
    {c : F} (hc : c ∈ k) : c = 0 ∨ c = 1 := by
  by_contra h
  push Not at h
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  have h1 : (⟨1, k.one_mem⟩ : k) = y := huniq _ (fun h' => one_ne_zero (congrArg Subtype.val h'))
  have h2 : (⟨c, hc⟩ : k) = y := huniq _ (fun h' => h.1 (congrArg Subtype.val h'))
  exact h.2 (congrArg Subtype.val (h2.trans h1.symm))

theorem sl2_top_of_roots [CharP K 2] [Finite K] {k : Subfield K}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p) (hr2 : Nat.card (ratFix σ k) = 2)
    {S : Subgroup (SpecialLinearGroup (Fin 2) (fixSub σ))} {c b₀ : fixSub σ}
    (hc : c ∉ ratFix σ k) (hb₀ : b₀ ≠ 0) (hu1 : u2 (1 : fixSub σ) ∈ S) (huc : u2 c ∈ S)
    (hl : l2 b₀ ∈ S) : S = ⊤ := by
  have : Finite (fixSub σ) := inferInstance
  have : CharP (fixSub σ) 2 := inferInstance
  refine sl2_eq_top_of_root_groups (a₁ := 1) (a₂ := c) (b₀ := b₀) hp hp2 hK one_ne_zero
    (by simpa using hc) hb₀ ?_ hl
  intro c₁ hc₁ c₂ hc₂
  rcases eq_zero_or_one_of_card_two' hr2 hc₁ with rfl | rfl <;>
    rcases eq_zero_or_one_of_card_two' hr2 hc₂ with rfl | rfl
  · simp [u2_zero]
  · simpa using huc
  · simpa using hu1
  · rw [show (1 : fixSub σ) * 1 + 1 * c = 1 + c by ring, u2_add]
    exact S.mul_mem hu1 huc

theorem lSub_eq_top [CharP K 2] [Finite K] {k : Subfield K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p) (hr2 : Nat.card (ratFix σ k) = 2)
    {P : Frame σ n} {H : Subgroup (SUid σ n)} {c b₀ : fixSub σ} (hc : c ∉ ratFix σ k)
    (hb₀ : b₀ ≠ 0) (hu1 : u2 (1 : fixSub σ) ∈ lSub P H) (huc : u2 c ∈ lSub P H)
    (hl : l2 b₀ ∈ lSub P H) : lSub P H = ⊤ :=
  sl2_top_of_roots hp hp2 hK hr2 hc hb₀ hu1 huc hl

end CFSG.RankThree.PartOne.SEITZ5
