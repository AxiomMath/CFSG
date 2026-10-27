module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrSmall
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrFrom
public import CFSG.LocalAnalysis.StandardType.GGTWHLTorRow
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Defs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWKCovered (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧ p ∣ ggTorM lab

@[expose] def GGTWLCovered (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGTBTorCov p lab ∧ ¬ GGTBWExcl lab ∧ ¬ GGOutdiagTwistedLabel lab) ∨
    (lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGHL58NbrRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → x ∉ L → y ∉ K →
    (k = 1 ∨ k = 2) → 3 ≤ p → p ∣ N → (N = 5 ∨ N = 6 ∨ N = 9) →
    Nat.card ↥Bs = p ^ (N - 1) → GGTWAligned p N k Bs L J K →
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
    ¬ GGInnerDiagOnLabel GGTWKCovered p Bs K → GGTWHLAt p Bs K y

@[expose] def GGTWHKGuard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → x ∉ L →
    (k = 1 ∨ k = 2) → 3 ≤ p → p ∣ N → (N = 5 ∨ N = 6 ∨ N = 9) →
    Nat.card ↥Bs = p ^ (N - 1) → GGTWAligned p N k Bs L J K →
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y

@[expose] def GGHL58BaseRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → y ∉ K →
    3 ≤ p → p ∣ N → (N = 5 ∨ N = 6 ∨ N = 9) → Nat.card ↥Bs = p ^ (N - 1) →
    GGTWAligned p N 1 Bs K J L → ¬ GGInnerDiagOnLabel GGTWLCovered p Bs L → GGTWHLAt p Bs L x

theorem ggHL58BaseRestInput_of_hHL (h : GGTWHLSmall) : GGHL58BaseRestInput :=
  fun G _ _ p N _ B Bs x L D J y K hH hyK hp hpN hN hcard hA _ =>
    h G p N B Bs x L D J y K hH hyK hp hpN hN hcard hA

theorem ggTWHLSmall_of_rest
    (hRig : GGLabelRigidInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) (hTw : GGTWTwA5Open) (hRest : GGHL58BaseRestInput) :
    GGTWHLSmall := by
  intro G _ _ p N _ B Bs x L D J y K hH hyK hp hpN hN hcard hA
  by_cases hcov : GGInnerDiagOnLabel GGTWLCovered p Bs L
  · rcases GGInnerDiagOnLabel.elim_or hcov with h1 | h2
    · exact ggTWHL_of_tbTor_row hRig hT hLift hW hH h1
    · obtain ⟨hperf, lab, hlab, hraw⟩ := h2
      have hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
        refine largeEvenRawDatum_mono ?_ hraw
        rintro R _ I F ⟨-, -, θ, -⟩
        exact ⟨θ⟩
      obtain ⟨R, _, I, F, -, -, θ, hS3, -⟩ := largeEvenRawDatum_exists hraw
      exact (hTw G p B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) hS3.2.2.1 lab hlab hhas
        ⟨hS3.1, hS3.2.1, hS3.2.2.2⟩).2.1 ⟨rfl, rfl⟩
  · exact hRest G p N B Bs x L D J y K hH hyK hp hpN hN hcard hA hcov

theorem ggTWHKSmall_of_rest (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hW : GGTBWNormLabelInput) (hTw : GGTWTwA5Open)
    (hGuard : GGTWHKGuard) (hRest : GGHL58NbrRestInput) : GGTWHKSmall := by
  intro G _ _ p N k _ B Bs x L D J y K hH hxL hyK hk hp hpN hN hcard hA
  have hCent := hGuard G p N k B Bs x L D J y K hH hxL hk hp hpN hN hcard hA
  by_cases hK : GGInnerDiagOnLabel GGTWKCovered p Bs K
  · have hp2 : p ≠ 2 := by omega
    have hcover : GGInnerDiagOnLabel (fun p lab =>
        ((lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧ p ∣ ggTorM lab ∧ ¬ p ∣ lab.rank + 1) ∨
        (GGTWRowPred 4 p lab ∨
          (lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1))) p Bs K := by
      refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_ hK
      intro lab _ _ hc
      obtain ⟨hct, hc3, hcM⟩ := hc
      by_cases hd : p ∣ lab.rank + 1
      · by_cases hE : p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1
        · refine Or.inr (Or.inr ⟨?_, hE.2.1, hE.1, hE.1 ▸ hE.2.2⟩)
          rcases hct with htA | htw
          · exfalso
            obtain ⟨tag, r, n⟩ := lab
            simp only at htA hcM hE
            subst htA
            rw [ggTWR_ggTorM_A] at hcM
            have h2 : p ∣ 2 := by
              have hsub := Nat.dvd_sub hE.2.2 hcM
              have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
              have he : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
              rwa [he] at hsub
            exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2)
          · exact htw
        · refine Or.inr (Or.inl ⟨hct, ?_, hd, hcM, hE⟩)
          by_contra hlt
          have hr : lab.rank = 3 := by omega
          have h4 : p ∣ 2 ^ 2 := by
            rw [hr] at hd
            simpa using hd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1
            ((Fact.out : p.Prime).dvd_of_dvd_pow h4))
      · exact Or.inl ⟨hct, hc3, hcM, hd⟩
    rcases GGInnerDiagOnLabel.elim_or hcover with h1 | h23
    · exact ggHL58Nbr_small_of_inputs hRig hT hLift hW hH hyK hCent h1
    · rcases GGInnerDiagOnLabel.elim_or h23 with h2 | h3
      · exact ggHL58Nbr_of_inputs_from (r₀ := 4) (le_refl 4) hRig
          (ggTBTorAFrom_of_all (le_refl 4) hT) (ggTBTorLiftAFrom_of_rows (le_refl 4) hLift) hW
          hH hCent h2
      · obtain ⟨hperf, lab, hlab, hraw⟩ := h3
        have hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
          refine largeEvenRawDatum_mono ?_ hraw
          rintro R _ I F ⟨-, -, θ, -⟩
          exact ⟨θ⟩
        obtain ⟨R, _, I, F, -, -, θ, hS3, -⟩ := largeEvenRawDatum_exists hraw
        exact (hTw G p B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) hS3.2.2.1 lab hlab hhas
          ⟨hS3.1, hS3.2.1, hS3.2.2.2⟩).2.2 ⟨rfl, rfl⟩ hyK hCent
  · exact hRest G p N k B Bs x L D J y K hH hxL hyK hk hp hpN hN hcard hA hCent hK

end CFSG.StandardType

end
