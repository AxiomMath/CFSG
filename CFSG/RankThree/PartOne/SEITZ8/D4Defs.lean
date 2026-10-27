module

public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Ree.Mirror

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

@[expose] noncomputable def coordAt (γ : Fin d4.rank → ℤ) (x : RootModule d4 K) : K :=
  open _root_.Classical in if h : IsRoot d4 γ then x (Sum.inr ⟨γ, h⟩) else 0

theorem coordAt_eq {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (x : RootModule d4 K) :
    coordAt γ x = x (Sum.inr ⟨γ, hγ⟩) := by
  unfold coordAt
  simp [hγ]

theorem coordAt_add (γ : Fin d4.rank → ℤ) (x y : RootModule d4 K) :
    coordAt γ (x + y) = coordAt γ x + coordAt γ y := by
  unfold coordAt
  split_ifs <;> simp

theorem coordAt_smul (γ : Fin d4.rank → ℤ) (c : K) (x : RootModule d4 K) :
    coordAt γ (c • x) = c * coordAt γ x := by
  unfold coordAt
  split_ifs <;> simp

theorem coordAt_rootVec_self {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    coordAt γ (rootVec d4 K γ) = 1 := by
  unfold coordAt rootVec
  simp [hγ]

theorem coordAt_rootVec_ne {γ δ : Fin d4.rank → ℤ} (h : γ ≠ δ) :
    coordAt γ (rootVec d4 K δ) = 0 := by
  classical
  unfold coordAt rootVec
  by_cases hγ : IsRoot d4 γ <;> by_cases hδ : IsRoot d4 δ
  · have : (⟨γ, hγ⟩ : {v // IsRoot d4 v}) ≠ ⟨δ, hδ⟩ := fun e => h (congrArg Subtype.val e)
    simp [hγ, hδ, this]
  · simp [hγ, hδ]
  · simp [hγ]
  · simp [hγ]

theorem coordAt_hVec (γ : Fin d4.rank → ℤ) (i : Fin d4.rank) :
    coordAt γ (hVec d4 K i) = 0 := by
  unfold coordAt hVec
  split_ifs <;> simp

theorem len_d4 : (Tag.rootCertificate d4).roots.length = 24 := by decide +kernel

theorem isRoot_d4 {k : ℕ} (hk : k < 24) :
    IsRoot d4 (d4Root k) :=
  isRoot_d4Root (by rw [len_d4]; exact hk)

theorem exists_pos_of_isRoot {γ : Fin d4.rank → ℤ}
    (hγ : IsRoot d4 γ) : ∃ p < 24, d4Root p = γ := by
  obtain ⟨p, hp, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check d4) hγ
  rw [len_d4] at hp
  exact ⟨p, hp, rfl⟩

theorem neg_d4Root : ∀ p < 24, ∃ q < 24, d4Root q = -d4Root p := by decide +kernel

theorem isRoot_neg_d4 {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    IsRoot d4 (-γ) := by
  obtain ⟨p, hp, rfl⟩ := exists_pos_of_isRoot hγ
  obtain ⟨q, hq, h⟩ := neg_d4Root p hp
  exact h ▸ isRoot_d4 hq

theorem d4Root_23 : d4Root 23 = -d4Root 22 := by decide +kernel

@[expose] def longPos : List ℕ := [2, 8, 19, 21, 22, 23]

theorem neg_long : ∀ σ ∈ longPos, ∃ σ' ∈ longPos, d4Root σ' = -d4Root σ := by decide +kernel

theorem lt_of_mem_longPos {p : ℕ} (hp : p ∈ longPos) : p < 24 := by
  simp only [longPos, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

end CFSG.RankThree.PartOne.SEITZ8
