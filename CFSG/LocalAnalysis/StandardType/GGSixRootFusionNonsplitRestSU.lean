module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestSUWit
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepResidual

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.Classical (permGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Inputs

@[expose] def GGSUNonsplitTwoBlockInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ →
      GGSixStepOne p B Bs x L D J → ¬ p ∣ 2 ^ (f + 1) + 1 →
        ∃ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
          (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
              (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n)
          (d : ℕ) (a : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)),
          2 ≤ d ∧ 4 * d ≤ n ∧
            SURep.ggFrameU (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP a ∈
              Bs ∧
            (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * permGL (SURep.ggPairPerm n d) =
              permGL (SURep.ggPairPerm n d) * (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) ∧
            TableBUE.IsBlockOn (SUNS.midSet n d)ᶜ
              ((a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
                Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) ∧
            (∀ v : Fin n → GaloisField 2 (2 * (f + 1)),
              ((a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
                Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *ᵥ v = v →
                  ∀ k ∉ SUNS.midSet n d, v k = 0) ∧
            (∀ v : Fin n → GaloisField 2 (2 * (f + 1)),
              v ᵥ* ((a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
                Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = v →
                  ∀ k ∉ SUNS.midSet n d, v k = 0) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer
              (((TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1)
                (SUNS.midSet n d)).map (SURep.ggFrameU
                  (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) :
                    Subgroup G) : Set G) : Subgroup G) ≤ p ^ 2

theorem ggSixRootFusionSURepNonsplitInput_of_twoBlock (hT : GGSUNonsplitTwoBlockInput) :
    GGSixRootFusionSURepNonsplitInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 s2 E r hch hC hodd hns l hl2 hln
  obtain ⟨P, hP, d, a, hd2, hd4, hbB, hcomm, hblock, hV, hV', hbound⟩ :=
    hT G p B Bs x L D J n f ψ hctx s1 hns
  set hK := card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f) with hKdef
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hdata : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hFk : SURep.GGFrameKer (SURep.ggFrameU hK ψ P hP) :=
    SURep.ggFrameKer_ggFrameU hK ψ P hP (by omega)
      (fun h => by have h1 : n = 3 := congrArg Prod.fst h; omega) hker
  have hrangeφ : (SURep.ggFrameU hK ψ P hP).range = ggG0 p B x L D J :=
    (SURep.range_ggFrameU hK ψ P hP).trans hrange
  have hle : ψ.range ≤ ggM p B x L D J := hrange ▸ Subgroup.le_normalizer
  have hcardM := SUNS.card_midSet n d
  have hd0 : 0 < d := by omega
  have hiM : (⟨d, by omega⟩ : Fin n) ∈ SUNS.midSet n d := by
    rw [SUNS.mem_midSet]
    simp only
    omega
  have h0M : (⟨0, by omega⟩ : Fin n) ∉ SUNS.midSet n d := by
    rw [SUNS.mem_midSet]
    simp only
    omega
  have hap : a ^ p = 1 :=
    SUNS.pow_eq_one_of_frame hFk hblock hiM (hctx.2.1.2.1.2 _ hbB)
  have hb1 : SURep.ggFrameU hK ψ P hP a ≠ 1 := SUNS.frame_ne_one hFk hblock hV hiM h0M
  have hW : GGSixFusionWitness p Bs D E (ggG0 p B x L D J) .PSU (f + 1)
      (SURep.ggFrameU hK ψ P hP a) := by
    have hcomp := SUNS.isComponentOf_map_blockSU_of_fix hK hdata hFk hp hns hap hblock hV hV'
      (by omega) (fun h => by have h1 := congrArg Prod.fst h; simp only at h1; omega) h0M
    rw [hrangeφ] at hcomp
    exact ⟨hb1, Or.inr (Or.inr ⟨hbB, _, hcomp, Or.inl hbound⟩)⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Equiv.Perm (Fin n),
      (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * permGL (ρ * SURep.ggPairPerm n l * ρ⁻¹) =
        permGL (ρ * SURep.ggPairPerm n l * ρ⁻¹) * (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) := by
    rcases lt_or_ge l d with hld | hld
    · obtain ⟨ρ, hρ⟩ := SUNS.exists_perm_conj_fix (n := n) (d := d) (l := l) (by omega)
      exact ⟨ρ, Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact SUNS.commute_permGL_of_isBlockOn hblock hρ)⟩
    · refine ⟨1, ?_⟩
      rw [one_mul, inv_one, mul_one]
      have hτ := SUNS.ggPairPerm_mul_fix (n := n) hld
      have hinv : SURep.ggPairPerm n d * SURep.ggPairPerm n d = 1 := by
        nth_rewrite 1 [← SURep.ggPairPerm_inv n d]
        exact inv_mul_cancel _
      have hsplit : SURep.ggPairPerm n l =
          SURep.ggPairPerm n d * (SURep.ggPairPerm n d * SURep.ggPairPerm n l) := by
        rw [← mul_assoc, hinv, one_mul]
      have h1 : (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          permGL (SURep.ggPairPerm n d * SURep.ggPairPerm n l) =
          permGL (SURep.ggPairPerm n d * SURep.ggPairPerm n l) *
            (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) := Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact SUNS.commute_permGL_of_isBlockOn hblock hτ)
      rw [hsplit, map_mul]
      calc (a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) *
            (permGL (SURep.ggPairPerm n d) *
              permGL (SURep.ggPairPerm n d * SURep.ggPairPerm n l)) =
          ((a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * permGL (SURep.ggPairPerm n d)) *
            permGL (SURep.ggPairPerm n d * SURep.ggPairPerm n l) := by group
        _ = permGL (SURep.ggPairPerm n d) * ((a : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) *
            permGL (SURep.ggPairPerm n d * SURep.ggPairPerm n l)) := by rw [hcomm]; group
        _ = permGL (SURep.ggPairPerm n d) * (permGL (SURep.ggPairPerm n d *
            SURep.ggPairPerm n l) * (a : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) := by rw [h1]
        _ = _ := by group
  obtain ⟨w, hw⟩ := SURep.exists_conj_ggInvSU_frame hK ψ P hP hdata (by omega) hln ρ
  have hcommb : SURep.ggFrameU hK ψ P hP a *
      SURep.ggFrameU hK ψ P hP ⟨permGL (ρ * SURep.ggPairPerm n l * ρ⁻¹),
        SURep.permGL_mem_unitarySU hdata _⟩ =
      SURep.ggFrameU hK ψ P hP ⟨permGL (ρ * SURep.ggPairPerm n l * ρ⁻¹),
        SURep.permGL_mem_unitarySU hdata _⟩ * SURep.ggFrameU hK ψ P hP a := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hρ
  rw [hw] at hcommb
  exact SURep.ggRootFusionWitnessAlt_of_conj_commU ψ hcommb (hle ⟨w, rfl⟩) hW

theorem ggSixRootFusionSURepInput_of_twoBlock_known (hT : GGSUNonsplitTwoBlockInput)
    (h1 : GGSUBlockNotExcludedInput) (h2 : GGSUSixAlphaInput) : GGSixRootFusionSURepInput :=
  ggSixRootFusionSURepInput_of_nonsplit_known (ggSixRootFusionSURepNonsplitInput_of_twoBlock hT)
    h1 h2

end Inputs

end CFSG.StandardType
