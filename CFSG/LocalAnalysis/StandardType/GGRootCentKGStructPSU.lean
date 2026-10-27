module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructND
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSU
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal
open CFSG.LieType.Universal.Unitary (SU rootDatum)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Matrix

section Tags

theorem ggRootCentKGStructTag_PSU_of
    (hpieces : ∀ (f m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]
      (h : UnitaryFieldData 2 f K), 3 ≤ m →
        KGND.KGPiecesD (AutPSU.inndiag h (n := m + 1))
          (AutPSU.projU h (AutPSU.rootU (K := K) (f := f) m))) :
    GGRootCentKGStructTag .PSU := by
  change ∀ (G : Type) [Group G] [Finite G] (p n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    p.Prime → p ≠ 2 → StatedLieAdmissible .PSU n 2 f → 2 ≤ (ggU .PSU n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU .PSU n f).K → commutator ↥ψ.range = ⊤ →
    LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) .PSU n 2 f →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) →
    (∃ Bs : Subgroup G, IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧
        ∀ b ∈ Bs, GGPsiInnerDiag (ggU .PSU n f).D ψ b) →
    ∀ r : G, GGRootInvolution (ggU .PSU n f).D .PSU ψ r →
      ¬ Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer {r}) →
    ∀ E : Subgroup G, E ≤ Subgroup.normalizer (ψ.range : Set G) →
      E ≤ Subgroup.centralizer {r} → IsPGroup p E →
      (∀ e ∈ E, GGPsiInnerDiag (ggU .PSU n f).D ψ e) →
      ∃ 𝒥 : Set (Subgroup G),
        (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {r} → ⁅P, P⁆ = P →
          P ≤ sSup 𝒥) ∧
        ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {r}) E J
  intro G _ _ p n f
  by_cases hf : 1 ≤ f
  · have e : ggU .PSU n f =
        ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ _ _ _ hrank hker _ _ hC _ hBs r hr _ E hEN hEC _ hEinn
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrank
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 3 ≤ m := by omega
    have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      card_galoisField_two_mul 2 f hf
    have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
      RootDetectSU.unitaryFieldData_two hK hf
    obtain ⟨w, hw⟩ := AutPSU.exists_conj_rootU_of_rootInvolution (f := f) (m := m)
      (K := GaloisField 2 (2 * f)) hK hr
    set Θ : AutPSU.PJ h (m + 1) ≃* ψ.range :=
      AutPSU.projEquivU h hn hker hC with hΘ
    set ψ' : AutPSU.PJ h (m + 1) →* G :=
      (ψ.range.subtype).comp Θ.toMonoidHom with hψ'
    set w' : AutPSU.PJ h (m + 1) := AutPSU.projU h w with hw'
    set z : AutPSU.PJ h (m + 1) :=
      AutPSU.projU h (AutPSU.rootU (K := GaloisField 2 (2 * f)) (f := f) m) with hz
    have hψ'range : ψ'.range = ψ.range := by
      rw [hψ', MonoidHom.range_comp]
      have htop : Θ.toMonoidHom.range = ⊤ :=
        MonoidHom.range_eq_top.mpr Θ.surjective
      rw [htop, Subgroup.map_top, Subgroup.range_subtype]
    have hψ'inj : Function.Injective ψ' := by
      intro x y hxy
      exact Θ.injective (Subtype.ext hxy)
    have hψ'proj : ∀ v : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1),
        ψ' (AutPSU.projU h v) = ψ v := by
      intro v
      rw [hψ', hΘ]
      exact AutPSU.projEquivU_projU h hn hker hC v
    have hΘw : (Θ w' : G) = ψ w := by
      rw [hw', hΘ]
      exact AutPSU.projEquivU_projU h hn hker hC w
    have hΘr : (Θ z : G) = ψ (AutPSU.rootU (K := GaloisField 2 (2 * f)) (f := f) m) := by
      rw [hz, hΘ]
      exact AutPSU.projEquivU_projU h hn hker hC _
    have hβz : ψ' ((MulAut.conj w') z) = r := by
      show ψ' (w' * z * w'⁻¹) = r
      have e1 : ψ' (w' * z * w'⁻¹) =
          (Θ w' : G) * (Θ z : G) * (Θ w' : G)⁻¹ := by
        simp only [hψ', MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
        rfl
      rw [e1, hΘw, hΘr]
      exact hw.symm
    have hβ : (MulAut.conj w') ∈ (AutPSU.inndiag h :
        Subgroup (MulAut (AutPSU.PJ h (m + 1)))) :=
      AutPSU.inn_le_inndiag h ⟨w', rfl⟩
    have hDz : KGND.KGPiecesD (AutPSU.inndiag h) ((MulAut.conj w') z) :=
      KGND.KGPiecesD.map_of_mem (hpieces f m (GaloisField 2 (2 * f)) h hm) hβ
    have hact : ∀ ε ∈ E, ∃ δ ∈ (AutPSU.inndiag h :
        Subgroup (MulAut (AutPSU.PJ h (m + 1)))),
        ∀ u : AutPSU.PJ h (m + 1), ε⁻¹ * ψ' u * ε = ψ' (δ u) := by
      intro ε hε
      obtain ⟨A, hA, hAact⟩ :=
        InnerDiagSU.suInnerDiagConj hK hn G ψ hker ε (hEinn ε hε)
      have hεnorm : ε⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
        (Subgroup.normalizer (ψ.range : Set G)).inv_mem (hEN hε)
      have hX : ∀ u : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1),
          ε⁻¹ * ψ u * (ε⁻¹)⁻¹ = ψ (InnerDiagSU.conjSU A hA u) := by
        intro u
        simpa using hAact u
      have hInd := NoOffUO.inducedAut_eq_conj h hn hker hC hA hX hεnorm
      refine ⟨primeFormConjHom h _ ⟨A, SURepair.mem_primeFormUnitary_of_isJUnitary h hA⟩,
        ⟨⟨A, SURepair.mem_primeFormUnitary_of_isJUnitary h hA⟩, rfl⟩, fun x => ?_⟩
      have hx := NoOffUO.inducedAut_spec h hn hker hC ⟨ε⁻¹, hεnorm⟩ x
      rw [hInd] at hx
      simpa [hψ'] using hx.symm
    have hEsub : E ≤ Subgroup.centralizer ({ψ' ((MulAut.conj w') z)} : Set G) := by
      rw [hβz]
      exact hEC
    obtain ⟨𝒥, hcover, hpiece⟩ := hDz G ψ' hψ'inj E hEsub hact
    have hC₀ : ψ.range ⊓ Subgroup.centralizer ({r} : Set G) =
        ψ'.range ⊓ Subgroup.centralizer ({ψ' ((MulAut.conj w') z)} : Set G) := by
      rw [hψ'range, hβz]
    refine ⟨𝒥, ?_, ?_⟩
    · intro P hP hPperf
      rw [hC₀] at hP
      exact hcover P hP hPperf
    · intro J hJ
      rw [hC₀]
      exact hpiece J hJ
  · intro ψ _ _ hadm
    exact absurd hadm.2.1 hf

end Tags

end CFSG.StandardType

end
