module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_CartanSylowAbelian : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f r : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f →
      LieModel (K ⧸ Subgroup.center K) t m 2 f → CFSG.Open.IsQuasisimple K →
        Odd (Nat.card (Subgroup.center K)) →
          ((t = .PSL ∧ m = 3) ∨ (t = .PSL ∧ m = 4) ∨ (t = .PSU ∧ m = 6) ∨
            (t = .PSp ∧ m = 3) ∨ (t = .POmegaMinus ∧ m = 4)) →
            r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
              ∀ P : Sylow r K, IsMulCommutative (P : Subgroup K)

@[expose] def K_RankThreeCentTorus : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f p r : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f →
      LieModel (K ⧸ Subgroup.center K) t m 2 f → CFSG.Open.IsQuasisimple K →
        Odd (Nat.card (Subgroup.center K)) → Odd f →
          ((t = .PSU ∧ m = 6) ∨ (t = .POmegaMinus ∧ m = 4) ∨ (t = .PSp ∧ m = 3)) →
            p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 → r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
              ∃ E : Subgroup K, IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
                (if t = .PSp then 1 else 2) ≤
                  pRank p (⊤ : Subgroup (Subgroup.centralizer (E : Set K)))

@[expose] def K_CartanRankLarge : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f →
    2 < 2 ^ f →
    LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
      4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m →
        ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
          3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S))

theorem k_SpSixOutOrder_holds {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : LieModel K .PSp 3 2 f) : Nat.card (Outer K) ∣ 2 * f := by
  obtain ⟨F, hFld, hFin, hChar, hF, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel (L := K) hK
  letI := hFld
  letI := hFin
  letI := hChar
  have hf : 1 ≤ f := (hK.admissible).2.1
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)
  have hout : Nat.card (Outer (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp 3 F))) ∣ 2 * f := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd
      (r := 3) (p := 2) (f := f) (K := F) Nat.prime_two hf hF (by norm_num)).2
      (by norm_num : 3 ≤ 3)
    rw [hgcd, mul_one] at h
    exact h.trans (dvd_mul_left f 2)
  calc Nat.card (Outer K)
      = Nat.card (Outer (CFSG.Assembly.LowTwoRank.StatedSp 3 F)) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    _ = Nat.card (Outer (CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSp 3 F))) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
          (CFSG.SeitzReduction.F4Pilot.spProjEquiv 3 F)).toEquiv
    _ ∣ 2 * f := hout

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
