module

public import CFSG.Sporadic.Recognition.LyonsAS44Act
public import CFSG.Sporadic.Recognition.LyonsAS44Perm

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

section Gen

variable {G : Type*} [Group G]

@[expose] def gammaG (x : G) (A : Subgroup (CentQuot x)) : Subgroup (Perm ↥(ptsAG x A)) :=
  (actPerm x A).range

@[expose] def ptOf (x : G) (A : Subgroup (CentQuot x)) (w : G) (hw : w ∈ preimQ x A)
    (hc : IsConj x w) : ↥(ptsAG x A) :=
  ⟨zpowers w, mem_deltaIn_iff.2 ⟨w, hc, hw, rfl⟩⟩

theorem eq_one_of_eq_inv_of_pow_three {x : G} (h3 : x ^ 3 = 1) (h : x = x⁻¹) : x = 1 := by
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel x
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

@[expose] def toGamma (x : G) (A : Subgroup (CentQuot x)) :
    ↥(normAG x A) →* ↥(gammaG x A) := (actPerm x A).rangeRestrict

end Gen

section M11

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
  {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}

namespace LyData

variable (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y)

include D S F

theorem nat_card_pts : Nat.card ↥(ptsAG (x₁ : G) A) = 11 := by
  rw [Nat.card_coe_set_eq]
  exact D.ncard_deltaIn_AG S F

theorem gamma_sharp : ∀ a b : Fin 4 → ↥(ptsAG (x₁ : G) A), Function.Injective a →
    Function.Injective b → ∃! g : ↥(gammaG (x₁ : G) A), ∀ i, g • a i = b i := by
  refine exists_unique_of_stabilizer_sharp (pt0 (x₁ : G) A) ?_ ?_ ?_
  · intro ω
    obtain ⟨k, hk⟩ := D.exists_actPerm_eq S F (pt0 (x₁ : G) A) ω
    exact ⟨⟨actPerm (x₁ : G) A k, k, rfl⟩, hk⟩
  · intro a b ha hb hai hbi
    obtain ⟨k, hk0, hk⟩ := D.exists_actPerm_stab_three S F a b ha hb hai hbi
    exact ⟨⟨actPerm (x₁ : G) A k, k, rfl⟩, hk0, hk⟩
  · intro g hg a ha hai hfix
    obtain ⟨γ, hγ⟩ := g
    obtain ⟨k, rfl⟩ := hγ
    exact Subtype.ext (D.actPerm_eq_one_of_fix S F k hg a ha hai hfix)

omit [Finite G] in
theorem x₂_mem_AG : (x₂ : G) ∈ preimQ (x₁ : G) A := by
  refine mem_preimQ.2 ⟨mem_centralizer_singleton_iff.2 (D.comm₂₁ S), ?_⟩
  have h : projQ (x₁ : G) ⟨(x₂ : G), mem_centralizer_singleton_iff.2 (D.comm₂₁ S)⟩ =
    D.x₂Q S := rfl
  rw [h]
  have := F.mcl.norm.mem_A 0
  rwa [F.mcl.norm.zero] at this

omit [Finite G] in
theorem x₃_mem_AG : (x₃ : G) ∈ preimQ (x₁ : G) A := by
  refine mem_preimQ.2 ⟨mem_centralizer_singleton_iff.2 (D.comm₃₁ S), ?_⟩
  have h : projQ (x₁ : G) ⟨(x₃ : G), mem_centralizer_singleton_iff.2 (D.comm₃₁ S)⟩ =
    D.x₃Q S := rfl
  rw [h]
  exact F.mcl.z_mem

omit [Finite G] in
theorem A3_le_AG : A3 (x₁ : G) (x₂ : G) (x₃ : G) ≤ preimQ (x₁ : G) A := by
  refine (closure_le _).2 ?_
  intro g hg
  have : g = (x₁ : G) ∨ g = (x₂ : G) ∨ g = (x₃ : G) := by simpa using hg
  rcases this with rfl | rfl | rfl
  · exact x_mem_preimQ A
  · exact D.x₂_mem_AG S F
  · exact D.x₃_mem_AG S F

end LyData

end M11

end CFSG.Sporadic.Recognition.LyonsSims
