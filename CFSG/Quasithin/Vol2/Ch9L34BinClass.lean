module

public import CFSG.Quasithin.Vol2.Ch9L34Bin64

public section

namespace CFSG.Quasithin.H13.Ch9.L34B

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.L34Bin
open CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups

variable {n : ℕ}

theorem eq_or_swap9 {a b c d : Fin 2 → Bool}
    (h₁ : (a = ![true, true] ∧ b = ![false, false]) ∨ (a = ![false, false] ∧ b = ![true, true]))
    (h₂ : (c = ![true, true] ∧ d = ![false, false]) ∨ (c = ![false, false] ∧ d = ![true, true])) :
    (c = a ∧ d = b) ∨ (d = a ∧ c = b) := by
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem eq_or_shift8 {a b c d : Fin 2 → Bool}
    (h₁ : (a = ![true, false] ∧ b = ![true, false]) ∨ (a = ![false, true] ∧ b = ![false, true]))
    (h₂ : (c = ![true, false] ∧ d = ![true, false]) ∨ (c = ![false, true] ∧ d = ![false, true])) :
    (c = a ∧ d = b) ∨ (c = shiftBits 2 a ∧ d = shiftBits 2 b) := by
  have hs : shiftBits 2 ![true, false] = ![false, true] ∧
      shiftBits 2 ![false, true] = ![true, false] := by decide
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [hs.1, hs.2]

theorem classify (ρ₀ : SL(3, F4) →* Matrix (Fin n) (Fin n) (ZMod 2)) (hn : 0 < n)
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hZ : ρ₀ zSL = 1) (hnt : ∃ g, ρ₀ g ≠ 1) :
    (∃ M : Matrix (Fin 9) (Fin n) (ZMod 2), Function.Bijective M.mulVec ∧
        ∀ g, M * ρ₀ g = R9 g * M) ∨
      (∃ M : Matrix (Fin 9) (Fin n) (ZMod 2), Function.Bijective M.mulVec ∧
        ∀ g, M * ρ₀ g = R9g g * M) ∨
      (∃ M : Matrix (Fin 16) (Fin n) (ZMod 2), Function.Bijective M.mulVec ∧
        ∀ g, M * ρ₀ g = R16 g * M) ∨
      (∃ M : Matrix (Fin 64) (Fin n) (ZMod 2), Function.Bijective M.mulVec ∧
        ∀ g, M * ρ₀ g = R64 g * M) := by
  obtain ⟨a, b, Y, Y', hY, hY', ⟨eY⟩, ⟨eY'⟩, htop, hd, -⟩ := exists_pair_digit ρ₀ hn hirr hZ hnt
  rcases dimT_digits5 hd with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  ·
    obtain ⟨c, d, Z, Z', ⟨eZ⟩, ⟨eZ'⟩, hcd⟩ := exists_pair9
    have hab : (a = ![true, true] ∧ b = ![false, false]) ∨
        (a = ![false, false] ∧ b = ![true, true]) := by
      rcases h with h | h <;> [exact Or.inl (Prod.ext_iff.mp h); exact Or.inr (Prod.ext_iff.mp h)]
    rcases eq_or_swap9 hab hcd with hq | hq
    · exact Or.inl (exists_iso_of_pair ρ₀ R9 hn hirr hirr9 hY hY' eY eY' htop eZ eZ' (Or.inl hq))
    · obtain ⟨W, W', ⟨eW⟩, ⟨eW'⟩⟩ := pair_gam eZ eZ'
      exact Or.inr (Or.inl
        (exists_iso_of_pair ρ₀ R9g hn hirr hirr9g hY hY' eY eY' htop eW eW' (Or.inl hq)))
  ·
    obtain ⟨c, d, Z, Z', ⟨eZ⟩, ⟨eZ'⟩, hcd⟩ := exists_pair16
    have hab : (a = ![true, false] ∧ b = ![true, false]) ∨
        (a = ![false, true] ∧ b = ![false, true]) := by
      rcases h with h | h <;> [exact Or.inl (Prod.ext_iff.mp h); exact Or.inr (Prod.ext_iff.mp h)]
    exact Or.inr (Or.inr (Or.inl (exists_iso_of_pair ρ₀ R16 hn hirr hirr16 hY hY' eY eY' htop eZ
      eZ' (eq_or_shift8 hab hcd))))
  ·
    obtain ⟨c, d, Z, Z', ⟨eZ⟩, ⟨eZ'⟩, rfl, rfl⟩ := exists_pair64
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    exact Or.inr (Or.inr (Or.inr
      (exists_iso_of_pair ρ₀ R64 hn hirr hirr64 hY hY' eY eY' htop eZ eZ' (Or.inl ⟨rfl, rfl⟩))))

end CFSG.Quasithin.H13.Ch9.L34B
