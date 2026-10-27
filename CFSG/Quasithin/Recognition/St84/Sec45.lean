module

public import CFSG.Quasithin.Recognition.St84.Sec4CommC
public import CFSG.Quasithin.Recognition.St84.Sec4CommD

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

theorem comm_Z_one (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁) :
    ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1) ∨
      (r + 1 = s ∧ Even d₀ ∧ ⁅X.Z 0, X.Z d₀⁆ ≠ ⊥) := by
  by_cases hna : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1)
  · exact Or.inl hna
  · refine Or.inr ?_
    by_cases hev : Even d₀
    · by_cases hb : r + 1 = s
      · exact ⟨hb, hev, (X.s45_Z_zero_not_central H hd₀ hd₁ hna hev).2⟩
      · obtain ⟨-, -, h68, -, -⟩ := X.s45_step8 H hd₀ hd₁ hna hev hb
        rcases h68 with h6 | h8
        · exact absurd h6 (X.s45_r_ne_six H hd₀ hd₁ hna hev hb)
        · exact absurd h8 (X.s45_r_ne_eight H hd₀ hd₁ hna hev hb)
    · exact (X.s45_false_of_b₀_odd H hd₀ hd₁ hna (Nat.not_even_iff_odd.mp hev)).elim

theorem comm_Z_one_or_swap (H : X.Sec4Hyp s r) :
    (∃ d : ℕ, X.HasB 1 d ∧
        ⁅X.Z 1, X.Z ((d : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d : ℤ) + 1)) ∨
      (r + 1 = s ∧ ∃ d : ℕ, X.swap.HasB 1 d ∧
        ⁅X.swap.Z 1, X.swap.Z ((d : ℤ) + 1)⁆ ≤
            X.swap.Z 1 ⊓ X.swap.Z ((d : ℤ) + 1) ∧
          ⁅X.swap.Z 1, X.swap.Z ((d : ℤ) + 1)⁆ ≠ ⊥) := by
  obtain ⟨d₀, hd₀⟩ := X.exists_hasB H 0
  obtain ⟨d₁, hd₁⟩ := X.exists_hasB H 1
  rcases X.comm_Z_one H hd₀ hd₁ with h | ⟨hr, hev, hne⟩
  · exact Or.inl ⟨d₁, hd₁, h⟩
  · refine Or.inr ⟨hr, d₀, ?_, ?_, ?_⟩
    · exact (X.hasB_swap (i := (1 : ℤ)) (d := d₀)).mpr (by simpa using hd₀)
    ·
      have hneg : X.HasB (-(d₀ : ℤ)) d₀ := by
        have hpar : Even ((d₀ : ℤ)) := (Int.even_coe_nat d₀).mpr hev
        exact (X.hasB_iff_of_even (i := 0) (j := -(d₀ : ℤ))
          (by simpa using hpar) d₀).mp hd₀
      have hZ0G : X.Z 0 ≤ X.Gi (-(d₀ : ℤ)) := hd₀.Z_le_Gi (by omega)
      have hZnegG : X.Z (-(d₀ : ℤ)) ≤ X.Gi 0 := hneg.Z_le_Gi (by omega)
      have hnorm0 : X.Gi 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun g hg =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 g hg)
      have hnormneg : X.Gi (-(d₀ : ℤ)) ≤ Subgroup.normalizer (X.Z (-(d₀ : ℤ)) : Set G) :=
        fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal (-(d₀ : ℤ)) g hg)
      have hle0 : ⁅X.Z 0, X.Z (-(d₀ : ℤ))⁆ ≤ X.Z 0 ⊓ X.Z (-(d₀ : ℤ)) :=
        F7.commutator_le_inf_of_normalizes (hZ0G.trans hnormneg) (hZnegG.trans hnorm0)
      rw [X.swap_Z, X.swap_Z, show (1 : ℤ) - 1 = 0 by norm_num,
        show (1 : ℤ) - ((d₀ : ℤ) + 1) = -(d₀ : ℤ) by ring]
      exact hle0
    ·
      have hneq : ⁅X.Z 0, X.Z (-(d₀ : ℤ))⁆ ≠ ⊥ := by
        obtain ⟨t, _, htref⟩ := X.exists_reflection H 0
        have ht0 : t • X.vert 0 = X.vert 0 := by simpa using htref 0
        have htd : t • X.vert (d₀ : ℤ) = X.vert (-(d₀ : ℤ)) := by
          simpa using htref (d₀ : ℤ)
        have hZ0 : X.Z 0 = conjSub t (X.Z 0) := X.Z_smul X ht0
        have hZd : X.Z (-(d₀ : ℤ)) = conjSub t (X.Z d₀) := X.Z_smul X htd
        have hcomm : conjSub t ⁅X.Z 0, X.Z d₀⁆ = ⁅X.Z 0, X.Z (-(d₀ : ℤ))⁆ := by
          rw [← conjSub_commutator t (X.Z 0) (X.Z d₀), ← hZ0, ← hZd]
        intro hbot
        apply hne
        have h1 : conjSub t ⁅X.Z 0, X.Z d₀⁆ = ⊥ := by rw [hcomm, hbot]
        have h2 := congrArg (conjSub t⁻¹) h1
        rwa [conjSub_conjSub_inv, conjSub_bot] at h2
      rw [X.swap_Z, X.swap_Z, show (1 : ℤ) - 1 = 0 by norm_num,
        show (1 : ℤ) - ((d₀ : ℤ) + 1) = -(d₀ : ℤ) by ring]
      exact hneq

end Setup

end CFSG.Quasithin.St84
