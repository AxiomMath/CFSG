module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.UniquenessCase.UC6R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013
  (Standing4 Setup4 TheoremCAt SigmaOne4 SigmaTwo4 Theorem614At UniqueFourClauseTwoAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem isStronglyPEmbedded_of_clause_one {M : Subgroup G} {p : ℕ} (hM : M ≠ ⊤)
    (hdvd : p ∣ Nat.card M)
    (h : ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ uniqueFourConj g M : Subgroup G)) :
    IsStronglyPEmbedded p M := by
  refine ⟨hM, hdvd, fun g hg => ?_⟩
  have := h g⁻¹ (by simpa using hg)
  simpa [uniqueFourConj] using this

@[expose] noncomputable def dataOfSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) : Data G where
  M := S.M
  T := S.T
  sig := uniqueFourSigma S.M
  sig1 := uniqueFourSigma S.M ∩ SigmaOne4 G
  sig2 := uniqueFourSigma S.M ∩ {p | SigmaTwo4 G p}
  sig3 := ∅
  standing := ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, le_trans (by norm_num) hS.rank⟩
  maxLocal := S.maxLocal
  sylowM := S.sylowM
  sylowG := S.sylowG
  normalizer_le := S.normalizer_le
  sig_prime := fun p hp => ⟨hp.1.1, hp.1.2.1⟩
  sig_rank := fun p hp => le_trans (by norm_num) (four_le_pRank_of_sigma hp)
  sig_sub := by
    ext p
    constructor
    · intro hp
      obtain ⟨hβ, hM0, -, P, hPM, hΓ, hcl⟩ := (hU S.M S.maxLocal ⟨p, hp⟩).1 p hp
      rcases hcl with ⟨hdvd, hstrong⟩ | ⟨h5, hsolv, hab, P₀, hP₀⟩
      · refine Or.inl (Or.inl ⟨hp, hβ, S.M, S.maxLocal, hp, ?_⟩)
        exact isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
      · exact Or.inl (Or.inr ⟨hp, hβ, S.M, S.maxLocal, hp, P, hPM, hΓ, h5, hsolv, hab, P₀, hP₀⟩)
    · rintro ((⟨hp, -⟩ | ⟨hp, -⟩) | h)
      · exact hp
      · exact hp
      · exact absurd h (by simp)

variable (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)

theorem r6_1_dataOfSetup4 : R6_1 (dataOfSetup4 hS hU S) := by
  intro p hp X hXM hXp hnc
  ext N
  constructor
  · rintro ⟨hN, hXN⟩
    have hle := sec61 hU S.maxLocal hp hXM
      (two_le_pRank_of_not_isCyclic hp.1.1 hp.1.2.1 hXp hnc) hN.1 hXN
    exact (hN.2 _ S.maxLocal.1 hle).symm
  · intro hN
    have hNM : N = S.M := hN
    subst hNM
    exact ⟨S.maxLocal, hXM⟩

theorem r6_3_dataOfSetup4 (hC : TheoremCAt S.M) : R6_3 (dataOfSetup4 hS hU S) := by
  intro r hr hr2 E hEM hEel hEcard hΓ
  have hE2 : 2 ≤ Open.pRank r E := by
    have := le_pRank_of_elemAbelian hr le_rfl hEel hEcard
    exact this
  ext N
  constructor
  · rintro ⟨hN, hEN⟩
    have hle := hC r hr hr2 E hEM (IsElemAbelian.isPGroup hEel) hE2 hΓ N hN.1 hEN
    exact (hN.2 _ S.maxLocal.1 hle).symm
  · intro hN
    have hNM : N = S.M := hN
    subst hNM
    exact ⟨S.maxLocal, hEM⟩

theorem r6_14_dataOfSetup4_iff : R6_14 (dataOfSetup4 hS hU S) ↔ Theorem614At S.M := by
  constructor
  · intro h hsub r hr hr2 hrσ R hR E hE hEel hEcard hΓ
    exact h (fun p hp => ⟨hp, hsub hp⟩) r hr hr2 hrσ R hR E hE hEel hEcard hΓ
  · intro h hsub r hr hr2 hrσ R hR E hE hEel hEcard hΓ
    exact h (fun p hp => (hsub hp).2) r hr hr2 hrσ R hR E hE hEel hEcard hΓ

end CFSG.LocalAnalysis.UniquenessCase.UC6
