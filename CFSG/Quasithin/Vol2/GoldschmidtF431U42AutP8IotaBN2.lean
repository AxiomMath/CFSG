module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ]

structure BNPair (B P₁ P₂ : Subgroup Δ) (s t : Δ) (us ut : List Δ) : Prop where
  r1 : RankOne B P₁ s us
  r2 : RankOne B P₂ t ut
  braid : s * t * s * t = t * s * t * s
  us_chain : ∀ u ∈ us, t * u * t ∈ B ∧ s * (t * u * t) * s ∈ B ∧
    t * (s * (t * u * t) * s) * t ∈ B
  ut_chain : ∀ u ∈ ut, s * u * s ∈ B ∧ t * (s * u * s) * t ∈ B ∧
    s * (t * (s * u * s) * t) * s ∈ B
  us_len : us.length ≤ 2
  ut_len : ut.length ≤ 4

@[expose] def InCells (B : Subgroup Δ) (s t x : Δ) : Prop :=
  InCell B 1 x ∨ InCell B s x ∨ InCell B t x ∨ InCell B (s * t) x ∨ InCell B (t * s) x ∨
    InCell B (s * t * s) x ∨ InCell B (t * s * t) x ∨ InCell B (s * t * s * t) x

theorem InCells.lmul {B : Subgroup Δ} {s t x b : Δ} (hb : b ∈ B) (h : InCells B s t x) :
    InCells B s t (b * x) := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl (h.lmul hb)
  · exact Or.inr (Or.inl (h.lmul hb))
  · exact Or.inr (Or.inr (Or.inl (h.lmul hb)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h.lmul hb))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.lmul hb)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.lmul hb))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.lmul hb)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.lmul hb)))))))

theorem inCells_one (B : Subgroup Δ) (s t : Δ) : InCells B s t 1 :=
  Or.inl (inCell_one_iff.2 B.one_mem)

namespace BNPair

variable {B P₁ P₂ : Subgroup Δ} {s t : Δ} {us ut : List Δ}

theorem s_inv (H : BNPair B P₁ P₂ s t us ut) : s⁻¹ = s := H.r1.inv_eq

theorem t_inv (H : BNPair B P₁ P₂ s t us ut) : t⁻¹ = t := H.r2.inv_eq

theorem up_us (H : BNPair B P₁ P₂ s t us ut) {n : Δ}
    (hn : n = 1 ∨ n = t ∨ n = t * s ∨ n = t * s * t) : ∀ u ∈ us, n⁻¹ * u * n ∈ B := by
  intro u hu
  obtain ⟨h1, h2, h3⟩ := H.us_chain u hu
  rcases hn with rfl | rfl | rfl | rfl
  · simpa using H.r1.U_mem u hu
  · simpa [H.t_inv] using h1
  · simpa [mul_inv_rev, H.s_inv, H.t_inv, mul_assoc] using h2
  · simpa [mul_inv_rev, H.s_inv, H.t_inv, mul_assoc] using h3

theorem up_ut (H : BNPair B P₁ P₂ s t us ut) {n : Δ}
    (hn : n = 1 ∨ n = s ∨ n = s * t ∨ n = s * t * s) : ∀ u ∈ ut, n⁻¹ * u * n ∈ B := by
  intro u hu
  obtain ⟨h1, h2, h3⟩ := H.ut_chain u hu
  rcases hn with rfl | rfl | rfl | rfl
  · simpa using H.r2.U_mem u hu
  · simpa [H.s_inv] using h1
  · simpa [mul_inv_rev, H.s_inv, H.t_inv, mul_assoc] using h2
  · simpa [mul_inv_rev, H.s_inv, H.t_inv, mul_assoc] using h3

end BNPair

end CFSG.Quasithin.H13.F431.U42Aut
