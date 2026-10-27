module

public import CFSG.RankThree.PartOne.SEITZRF.Rank1
import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (nTwo kTwo)

open CFSG.RankThree.PartOne.CTP (slSub mem_slSub u2 l2 u2_coe l2_coe u2_zero u2_add
  sl2_eq_top_of_root_groups)


namespace SL2Two

theorem eq_zero_or_eq_one {F : Type} [Field F] {k : Subfield F} (hk : Nat.card k = 2) {c : F}
    (hc : c ∈ k) : c = 0 ∨ c = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : k)).1 hk
  by_cases h0 : (⟨c, hc⟩ : k) = 0
  · exact Or.inl (congrArg Subtype.val h0)
  · exact Or.inr (congrArg Subtype.val ((hy _ h0).trans (hy 1 one_ne_zero).symm))

end SL2Two

theorem sl2_eq_top_of_uSL_mem_two {F : Type} [Field F] [Finite F]
    [CharP F 2] {k : Subfield F} (hk : Nat.card k = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card F = 2 ^ d) {M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hM : slSub 2 k ≤ M) {s : F} (hs : s ∉ k) (hsM : uSL s ∈ M) : M = ⊤ := by
  have hu1 : u2 (1 : F) ∈ M := hM (mem_slSub.2 fun i j => by
    rw [u2_coe]
    fin_cases i <;> fin_cases j <;> simp)
  have hl1 : l2 (1 : F) ∈ M := hM (mem_slSub.2 fun i j => by
    rw [l2_coe]
    fin_cases i <;> fin_cases j <;> simp)
  have hus : u2 s ∈ M := by
    have e : (uSL s : Matrix.SpecialLinearGroup (Fin 2) F) = u2 s :=
      Subtype.ext (by rw [coe_uSL, u2_coe])
    rwa [← e]
  refine sl2_eq_top_of_root_groups (k := k) (a₁ := 1) (a₂ := s) (b₀ := 1) hd hd2
    (by rw [hk]; exact hF) one_ne_zero (by rwa [div_one]) one_ne_zero (fun c₁ hc₁ c₂ hc₂ => ?_) hl1
  rcases SL2Two.eq_zero_or_eq_one hk hc₁ with rfl | rfl <;>
    rcases SL2Two.eq_zero_or_eq_one hk hc₂ with rfl | rfl
  · simp [u2_zero]
  · simpa using hus
  · simpa using hu1
  · have e : (1 : F) * 1 + 1 * s = 1 + s := by ring
    rw [e, u2_add]
    exact M.mul_mem hu1 hus

namespace SL2Two

section Transport

variable {K : Type} [Field K] {a : ℕ}

theorem map_largeReeSigma_ne [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) {s : K}
    (hs : β s ≠ s) : β (largeReeSigma a s) ≠ largeReeSigma a s := by
  intro h
  apply hs
  have h1 := congrArg (fun x => x ^ 2 ^ a) h
  simp only [← map_pow, largeReeSigma_pow_two_pow hK] at h1
  exact h1

theorem nTwo_zero : nTwo K 0 = 1 := by
  have h : F4.fixedRelElt (⟨0, by decide⟩ : Fin F4.fixedWeylOrder) = 1 := rfl
  rw [nTwo, show kTwo 0 = ⟨0, by decide⟩ from rfl, h, canonicalRep_one]

variable [Finite K] [CharP K F4.prime]

theorem sylowA_eq_largeReeA1Hom_uSL (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : K) :
    sylowA a K s = largeReeA1Hom K a (uSL (largeReeSigma a s)) := by
  rw [largeReeA1Hom_uSL, largeReeSigma_pow_two_pow hK, sylowA_eq, twoCoordG, nTwo_zero, one_mul,
    inv_one, mul_one, stdTwoG_eq_xUnit]

end Transport

end SL2Two

theorem eq_rankOneGroupOne_of_sylowA_mem_two {K : Type}
    [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (hk : Nat.card (fixSubfield β) = 2) (hd : (2 * a + 1).Prime)
    {Y : Subgroup (ModGL F4.tag K)} (hY : Y ≤ rankOneGroupOne K a)
    (hRY : rankOneGroupOne K a ⊓ Rf K a β ≤ Y) {s : K} (hs : β s ≠ s)
    (hsY : sylowA a K s ∈ Y) : Y = rankOneGroupOne K a := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hrange : rankOneGroupOne K a = (largeReeA1Hom K a).range := rankOneGroupOne_eq_range hK
  have hΓ : ∀ g : SL2 K, largeReeA1Hom K a g ∈ F4.reeGamma K a := fun g =>
    rankOneGroupOne_le_reeGamma hK (hrange ▸ ⟨g, rfl⟩)
  have hM : Y.comap (largeReeA1Hom K a) = ⊤ := by
    refine sl2_eq_top_of_uSL_mem_two hk hd (by omega) hK ?_ (s := largeReeSigma a s) ?_ ?_
    · intro g hg
      refine hRY ⟨?_, hΓ g, (largeReeA1Hom_mem_fixGL_iff β g).2 hg⟩
      exact hrange ▸ ⟨g, rfl⟩
    · exact fun h => SL2Two.map_largeReeSigma_ne hK β hs ((mem_fixSubfield β).1 h)
    · show largeReeA1Hom K a (uSL (largeReeSigma a s)) ∈ Y
      rw [← SL2Two.sylowA_eq_largeReeA1Hom_uSL hK]
      exact hsY
  refine le_antisymm hY ?_
  rw [hrange]
  rintro _ ⟨g, rfl⟩
  have : g ∈ Y.comap (largeReeA1Hom K a) := by rw [hM]; exact Subgroup.mem_top g
  exact this

end CFSG.RankThree.PartOne.SEITZRF
