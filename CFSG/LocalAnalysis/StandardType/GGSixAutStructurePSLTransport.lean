module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLFixed

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AutPSL

section Transport

variable {P H : Type*} [Group P] [Group H] (Θ : P ≃* H)

theorem congr_conj (y : P) : MulAut.congr Θ (MulAut.conj y) = MulAut.conj (Θ y) := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem autStructure_congr {I C : Subgroup (MulAut P)} {r : P} (hI : I.Normal)
    (hKI : (MulAut.conj : P →* MulAut P).range ≤ I)
    (hodd : Odd ((MulAut.conj : P →* MulAut P).range.relIndex I))
    (hIC : ∀ σ : MulAut P, ∃ i ∈ I, ∃ c ∈ C, σ = i * c) (hIC' : I ⊓ C = ⊥)
    (hgood : ∀ c ∈ C, c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ I, GGGoodAut r (e * c * e⁻¹)) :
    ∃ I' C' : Subgroup (MulAut H), I'.Normal ∧ (MulAut.conj : H →* MulAut H).range ≤ I' ∧
      Odd ((MulAut.conj : H →* MulAut H).range.relIndex I') ∧
      (∀ σ : MulAut H, ∃ i ∈ I', ∃ c ∈ C', σ = i * c) ∧ I' ⊓ C' = ⊥ ∧
      ∀ c ∈ C', c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ I', GGGoodAut (Θ r) (e * c * e⁻¹) := by
  set φ := MulAut.congr Θ
  have hφ : Function.Injective φ.toMonoidHom := φ.injective
  have hInn : (MulAut.conj : H →* MulAut H).range =
      (MulAut.conj : P →* MulAut P).range.map φ.toMonoidHom := by
    ext σ
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨MulAut.conj (Θ.symm x), ⟨_, rfl⟩, ?_⟩
      change φ (MulAut.conj (Θ.symm x)) = MulAut.conj x
      rw [congr_conj, MulEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨Θ y, (congr_conj Θ y).symm⟩
  refine ⟨I.map φ.toMonoidHom, C.map φ.toMonoidHom, hI.map _ φ.surjective, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hInn]
    exact Subgroup.map_mono hKI
  · rw [hInn, Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hodd
  · intro σ
    obtain ⟨i, hi, c, hc, h⟩ := hIC (φ.symm σ)
    refine ⟨φ i, ⟨i, hi, rfl⟩, φ c, ⟨c, hc, rfl⟩, ?_⟩
    rw [← map_mul, ← h, MulEquiv.apply_symm_apply]
  · rw [← Subgroup.map_inf_eq _ _ _ hφ, hIC', Subgroup.map_bot]
  · rintro _ ⟨c, hc, rfl⟩ hc2 hc1 _ ⟨e, he, rfl⟩
    have hc2' : c ^ 2 = 1 := φ.injective (by
      rw [map_pow, map_one]
      exact hc2)
    have hc1' : c ≠ 1 := by
      rintro rfl
      exact hc1 (map_one φ.toMonoidHom)
    have h := (hgood c hc hc2' hc1' e he).congr Θ
    change GGGoodAut (Θ r) (φ e * φ c * (φ e)⁻¹)
    rwa [← map_inv, ← map_mul, ← map_mul]

end Transport

section Iso

variable {m : ℕ} {K : Type} [Field K] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) K →* G}

theorem ker_eq_scalars (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) : ψ.ker = scalars (m + 1) K := by
  rw [scalars_eq_center]
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

@[expose] noncomputable def projEquiv
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) : projectiveSL (m + 1) K ≃* ψ.range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq_scalars hker hC).symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)

theorem projEquiv_proj
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (y : SpecialLinearGroup (Fin (m + 1)) K) :
    ((projEquiv hker hC (proj (m + 1) K y) : ψ.range) : G) = ψ y :=
  rfl

theorem exists_conj_rootInv_of_rootInvolution [Finite K] [CharP K 2] (hm : 1 ≤ m)
    {t : StatedLieTag} {r : G} (hr : GGRootInvolution (SpecialLinear.rootDatum m K) t ψ r) :
    ∃ w : SpecialLinearGroup (Fin (m + 1)) K, r = ψ w * ψ (rootInv hm) * (ψ w)⁻¹ := by
  obtain ⟨hr2, γ, -, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨i, j, hij, c, hc, rfl⟩ := exists_transvection_of_mem_rootGroup hz hz1
  obtain ⟨g, hg⟩ := exists_conj_transvection_eq hm hij hc
  rw [ggInvSL_eq_rootInv hm] at hg
  refine ⟨u * g⁻¹, ?_⟩
  have e : SpecialLinearGroup.transvection hij c = g⁻¹ * rootInv hm * g := by
    rw [← hg]
    group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e, map_mul, map_inv]
  group

end Iso

section Family

@[expose] def PSLCoreInput : Prop :=
  ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m →
    ∀ c ∈ (compl : Subgroup (MulAut (projectiveSL (m + 1) K))), c ^ 2 = 1 → c ≠ 1 →
    ∀ Q : Subgroup (projectiveSL (m + 1) K), (∀ q ∈ Q, c q = q) → IsPGroup 2 Q →
      (∀ y : projectiveSL (m + 1) K, c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥

@[expose] def PSLThreeRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ)
    (ψ : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* G), 1 ≤ f →
    ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f)) →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ (p : ℕ) (Bs : Subgroup G), p.Prime → p ≠ 2 → IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) →
      (∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum 2 (GaloisField 2 f)) ψ b) → False

theorem ggAutStructureAt_PSL_of_inputs (hcore : PSLCoreInput) (hthree : PSLThreeRankInput) :
    GGAutStructureAt .PSL := by
  intro G _ _ n f ψ G₀ hadm hrank hrange hker _ _ hC hBs _ r hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm2 : 2 ≤ m := hrank
  have hf : 1 ≤ f := hadm.2.1
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · exfalso
    obtain ⟨p, Bs, hp, hp2, hBsE, hcard, hBsN, hBsI⟩ := hBs
    rw [← hrange] at hBsN
    exact hthree G f ψ hf hker hC' p Bs hp hp2 hBsE hcard hBsN hBsI
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_conj_rootInv_of_rootInvolution (K := GaloisField 2 f) (m := m)
      (G := G) (ψ := ψ) (by omega) hr
    set Θ : projectiveSL (m + 1) (GaloisField 2 f) ≃* G₀ :=
      (projEquiv (K := GaloisField 2 f) (m := m) hker hC').trans (MulEquiv.subgroupCongr hrange)
    obtain ⟨I', C', h1, h2, h3, h4, h5, h6⟩ := autStructure_congr Θ (inndiag_normal (by omega))
      inn_le_inndiag odd_relIndex_inn_inndiag (exists_mul_compl (by omega))
      (inndiag_inf_compl (by omega))
      (fun c hc hc2 hc1 e he =>
        goodAut_of_core hm3 hc (hcore m (GaloisField 2 f) hm3 c hc hc2 hc1) he)
    refine ⟨I', C', h1, h2, h3, h4, h5, fun c hc hc2 hc1 e he => ?_⟩
    have hr' : r = Θ (proj (m + 1) (GaloisField 2 f) w) *
        Θ (proj (m + 1) (GaloisField 2 f) (rootInv (by omega))) *
          (Θ (proj (m + 1) (GaloisField 2 f) w))⁻¹ := by
      apply Subtype.ext
      rw [hw]
      rfl
    rw [ggGoodOuterAut_iff, hr']
    exact (h6 c hc hc2 hc1 e he).of_conj _

end Family

end AutPSL

end CFSG.StandardType
