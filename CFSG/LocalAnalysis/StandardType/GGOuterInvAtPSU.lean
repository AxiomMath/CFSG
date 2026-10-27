module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvModelData
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Open (IsElemAbelian)

@[expose] def PSUGraphNone : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) (n : ℕ),
    4 ≤ n → ∀ i β : MulAut (AutPSU.PJ h n), i ∈ AutPSU.inndiag h → β ∈ AutPSU.inndiag h →
      Odd (orderOf β) →
      let α := i * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ (unitaryInvolution K 2 f)
      α * α = 1 → α * β = β * α → (∀ g, β g = g → α g = g) →
      ∀ L₁ : Subgroup (AutPSU.PJ h n), (∀ g ∈ L₁, β g = g) → Group.IsSolvable L₁

theorem ggOuterInv_ker_projU_eq_center {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) {n : ℕ} (hn : 4 ≤ n) :
    (AutPSU.projU h (n := n)).ker = Subgroup.center (Unitary.SU (unitaryInvolution K 2 f) n) := by
  ext x
  rw [MonoidHom.mem_ker, AutPSU.projU_apply, QuotientGroup.eq_one_iff,
    ← CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h AutPSU.isPrimeFormGram_gramJ
      (by omega) (AutPSU.not_three_of_four hn),
    ← AutPSU.symm_mem_center_iff h, MulEquiv.symm_apply_apply]

theorem ggOuterInv_psuMarking
    {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n)
    {G : Type} [Group G] (ψ : Unitary.SU (unitaryInvolution K 2 f) n →* G)
    (hker : ψ.ker = Subgroup.center (Unitary.SU (unitaryInvolution K 2 f) n))
    {c : G} (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hdiag : GGPsiInnerDiag (Unitary.rootDatum hK n) ψ c) :
    ∃ φ ∈ AutPSU.inndiag h (n := n), ∀ u u', c * ψ u * c⁻¹ = ψ u' →
      φ (AutPSU.projU h u) = AutPSU.projU h u' := by
  obtain ⟨s, hsU, hs⟩ :=
    ClassicalPosition.exists_isGLLift_PSU hK n (by omega) ψ hker.le hcN hdiag
  have hsU' : s ∈ primeFormUnitary h ((AutPSU.gramJ n : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, AutPSU.coe_gramJ, ← RootDetectSU.map_eq_map_bar h]
    exact hsU
  refine ⟨primeFormConjHom h _ (⟨s, hsU'⟩⁻¹), ⟨_, rfl⟩, fun u u' hcu => ?_⟩
  obtain ⟨v, hv, hvψ⟩ := hs u'
  have hψ : ψ v = ψ u := by
    rw [← hvψ, ← hcu]
    group
  have hvu : AutPSU.projU h v = AutPSU.projU h u := by
    rw [MonoidHom.eq_iff, ggOuterInv_ker_projU_eq_center h hn, ← hker, ← MonoidHom.eq_iff]
    exact hψ
  rw [← hvu, AutPSU.projU_apply, AutPSU.projU_apply, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (s⁻¹ : GL (Fin n) K) * (v : GL (Fin n) K) * (s⁻¹)⁻¹ = (u' : GL (Fin n) K)
  have hv' : (v : GL (Fin n) K) = s * (u' : GL (Fin n) K) * s⁻¹ := hv
  rw [hv']
  group

theorem ggOuterInvModelDataAt_PSU_of
    (hC : PSUGraphNone) : GGOuterInvModelDataAt .PSU := by
  intro n f hadm
  have hf : 1 ≤ f := hadm.2.1
  have e : ggU .PSU n f =
      ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [e]
  intro hrank
  have hn : 4 ≤ n := by
    change 2 ≤ n / 2 at hrank
    omega
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    RootDetectSU.unitaryFieldData_two (card_galoisField_two_mul 2 f hf) hf
  refine ⟨AutPSU.PJ h n, inferInstance, AutPSU.projU h, AutPSU.inndiag h,
    (QuotientGroup.mk'_surjective _).comp (AutPSU.suEquiv h).surjective,
    ggOuterInv_ker_projU_eq_center h hn, AutPSU.inn_le_inndiag h, AutPSU.odd_relIndex_inn_inndiag h, ?_, ?_⟩
  · intro G _ ψ hker c hc hdiag
    exact ggOuterInv_psuMarking h (card_galoisField_two_mul 2 f hf) hn ψ hker hc hdiag
  · intro p β α E hp hp2 _ hβE hEI hEab _ hEα hα2 hαI hL hfix
    obtain ⟨L₁, hL₁β, hL₁⟩ := hL
    have hβI := hEI hβE
    have hodd : Odd (orderOf β) := by
      have h1 : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one (hEab.2 _ hβE)
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · rw [h]
        exact odd_one
      · rw [h]
        exact hp.odd_of_ne_two hp2
    have hcomm : α * β = β * α := by
      have := hEα hβE
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    obtain ⟨i, hi, c, hcC, rfl⟩ := AutPSU.exists_mul_compl h hn α
    have hIn := AutPSU.inndiag_normal h hn
    have hc2 : c ^ 2 = 1 := by
      have hmem : c ^ 2 ∈ AutPSU.inndiag h ⊓ AutPSU.compl h (n := n) := by
        refine ⟨?_, pow_mem hcC 2⟩
        have hα : i * c * (i * c) = 1 := hα2
        have e2 : c ^ 2 = i⁻¹ * ((i * c) * i⁻¹ * (i * c)⁻¹) := by
          rw [show (i * c)⁻¹ = i * c from (eq_inv_of_mul_eq_one_left hα).symm, pow_two]
          group
        rw [e2]
        exact (AutPSU.inndiag h).mul_mem ((AutPSU.inndiag h).inv_mem hi)
          (hIn.conj_mem _ ((AutPSU.inndiag h).inv_mem hi) _)
      rw [AutPSU.inndiag_inf_compl h hn, Subgroup.mem_bot] at hmem
      exact hmem
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hαI (by rw [mul_one]; exact hi)
    have hcσ := AutPSU.involution_compl h hn hcC hc2 hc1
    subst hcσ
    exact hL₁ (hC f (GaloisField 2 (2 * f)) h n hn i β hi hβI hodd hα2 hcomm hfix L₁ hL₁β)

theorem ggOuterInvAt_PSU_of
    (h2 : GGO2CentralizerG0At .PSU) (hC : PSUGraphNone) :
    GGOuterInvAt .PSU :=
  ggOuterInvAt_of_modelData ggSteinbergCorrectionAt_PSU h2 (ggOuterInvModelDataAt_PSU_of hC)

end CFSG.StandardType
