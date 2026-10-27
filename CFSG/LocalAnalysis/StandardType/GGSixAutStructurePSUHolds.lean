module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUCoreCases
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SU rootDatum)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace AutPSU

section Iso

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) {n : ℕ}
  {G : Type*} [Group G] {ψ : SU (unitaryInvolution K 2 f) n →* G}

omit [Finite K] [CharP K 2] in
theorem ker_eq_center {U : Type*} [Group U] {φ : U →* G} (hker : φ.ker ≤ Subgroup.center U)
    (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) : φ.ker = Subgroup.center U := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : φ z ∈ Subgroup.centralizer (φ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

noncomputable abbrev psiJ (ψ : SU (unitaryInvolution K 2 f) n →* G) : XJ h n →* G :=
  ψ.comp (suEquiv h).symm.toMonoidHom

theorem range_psiJ : (psiJ h ψ).range = ψ.range := by
  rw [psiJ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map]

theorem symm_mem_center_iff (x : XJ h n) :
    (suEquiv h).symm x ∈ Subgroup.center (SU (unitaryInvolution K 2 f) n) ↔
      x ∈ Subgroup.center (XJ h n) := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro hx g
    have e := congrArg (suEquiv h) (hx ((suEquiv h).symm g))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using e
  · intro hx g
    apply (suEquiv h).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx _

theorem ker_psiJ (hn : 4 ≤ n) (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    (psiJ h ψ).ker = normOneScalars h (XJ h n) n := by
  rw [← CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h isPrimeFormGram_gramJ
    (by omega) (not_three_of_four hn)]
  ext x
  rw [MonoidHom.mem_ker]
  change ψ ((suEquiv h).symm x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_eq_center hker hC, symm_mem_center_iff]

@[expose] noncomputable def projEquivU (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) : PJ h n ≃* ψ.range :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_psiJ h hn hker hC).symm).trans
    (QuotientGroup.quotientKerEquivRange (psiJ h ψ))).trans
    (MulEquiv.subgroupCongr (range_psiJ h))

theorem projEquivU_projU (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (u : SU (unitaryInvolution K 2 f) n) :
    ((projEquivU h hn hker hC (projU h u) : ψ.range) : G) = ψ u :=
  rfl

end Iso

section Root

variable {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type*} [Group G]

theorem exists_conj_rootU_of_rootInvolution (hF : Nat.card K = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G} {r : G}
    (hr : GGRootInvolution (rootDatum hF (m + 1)) .PSU ψ r) :
    ∃ w : SU (unitaryInvolution K 2 f) (m + 1), r = ψ w * ψ (rootU m) * (ψ w)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hr2, γ, ⟨-, hlong⟩, u₀, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_longRoot hF (hlong (Or.inl rfl)) hx hx1
  refine ⟨u₀ * a, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha, map_mul, map_inv]
  group

end Root

end AutPSU

section Family

theorem ggAutStructureAt_PSU : GGAutStructureAt .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have e : ggU .PSU n f =
        ⟨SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ G₀ _ hrank hrange hker _ _ hC _ _ r hr
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrank
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 3 ≤ m := by omega
    have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
      RootDetectSU.unitaryFieldData_two (card_galoisField_two_mul 2 f hf) hf
    have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact hC
    obtain ⟨w, hw⟩ :=
      AutPSU.exists_conj_rootU_of_rootInvolution (card_galoisField_two_mul 2 f hf) hr
    set Θ : AutPSU.PJ h (m + 1) ≃* G₀ :=
      (AutPSU.projEquivU h hn hker hC').trans (MulEquiv.subgroupCongr hrange)
    obtain ⟨I', C', h1, h2, h3, h4, h5, h6⟩ := AutPSL.autStructure_congr Θ
      (AutPSU.inndiag_normal h hn) (AutPSU.inn_le_inndiag h) (AutPSU.odd_relIndex_inn_inndiag h)
      (AutPSU.exists_mul_compl h hn) (AutPSU.inndiag_inf_compl h hn)
      (fun c hc _ _ e he => AutPSU.goodAut_compl h hm hc he)
    refine ⟨I', C', h1, h2, h3, h4, h5, fun c hc hc2 hc1 e he => ?_⟩
    have hr' : r = Θ (AutPSU.projU h w) * Θ (AutPSU.projU h (AutPSU.rootU m)) *
        (Θ (AutPSU.projU h w))⁻¹ := by
      apply Subtype.ext
      rw [hw]
      rfl
    rw [ggGoodOuterAut_iff, hr']
    exact (h6 c hc hc2 hc1 e he).of_conj _
  · intro ψ G₀ hadm
    exact absurd hadm.2.1 hf

theorem ggAutStructureRest_of_PSU (hSp : GGAutStructureAt .PSp)
    (hP : GGAutStructureAt .POmegaPlus) (hM : GGAutStructureAt .POmegaMinus)
    (hF4 : GGAutStructureAt .F4) (hE6 : GGAutStructureAt .E6) (hE7 : GGAutStructureAt .E7)
    (hE8 : GGAutStructureAt .E8) (h2E6 : GGAutStructureAt .twistedE6) : GGAutStructureRest :=
  ⟨ggAutStructureAt_PSU, hSp, hP, hM, hF4, hE6, hE7, hE8, h2E6⟩

end Family

end CFSG.StandardType
