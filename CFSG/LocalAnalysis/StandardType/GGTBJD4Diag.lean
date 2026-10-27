module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmFrame
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCorank
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmEigen
import CFSG.LocalAnalysis.StandardType.GGA8NbrOmFrameCore
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  Polynomial
open CFSG.StandardType.KGCentOm (kgcDiag)

theorem ggTBJD4_supported_fix {n : ℕ} {F : Type} [Field F]
    {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {w : Fin n ⊕ Fin n → F}
    (hxa : ∀ v c, x v c = w c * v c) {μ : F} (hμ : μ ≠ 0)
    {g : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hg : g ∈ supportedBlock (quadPlus n F) x (X - C μ)) {c : Fin n ⊕ Fin n} (hc : w c ≠ μ)
    (hc' : w c ≠ μ⁻¹) : g (Pi.single c 1) = Pi.single c 1 := by
  classical
  have hv : ∀ b, w b ≠ w c → (Pi.single c (1 : F) : Fin n ⊕ Fin n → F) b = 0 := fun b hb =>
    Pi.single_eq_of_ne (fun h => hb (congrArg w h)) _
  have hxv : x (Pi.single c 1) = w c • (Pi.single c 1 : Fin n ⊕ Fin n → F) :=
    (jcoreOm_eigen_iff hxa (w c) _).mpr hv
  have hv0 : (Pi.single c (1 : F) : Fin n ⊕ Fin n → F) ≠ 0 := by
    intro h
    have h' := congrFun h c
    rw [Pi.single_eq_same, Pi.zero_apply] at h'
    exact one_ne_zero h'
  have hfac : X - C (w c) ∈ primaryFactors x.toLinearMap :=
    CFSG.RankThree.PartOne.KCUnitaryScalar.X_sub_C_mem_primaryFactors
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hxv, hv0⟩)
  have hmem : (Pi.single c (1 : F) : Fin n ⊕ Fin n → F) ∈
      primaryComponent x.toLinearMap (X - C (w c)) :=
    CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C.mpr hxv
  have hne : X - C (w c) ≠ X - C μ := fun h => hc (C_inj.mp (sub_right_inj.mp h))
  have hne' : X - C (w c) ≠ reciprocalPolynomial (X - C μ) := by
    rw [A8Coord.omf_reciprocalPolynomial_X_sub_C hμ]
    exact fun h => hc' (C_inj.mp (sub_right_inj.mp h))
  exact apply_eq_of_mem_supportedBlock hg hfac hne hne' hmem

theorem ggTBJD4_commute_of_diag {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {x g d : (ι → F) ≃ₗ[F] (ι → F)} {w e : ι → F} (hxa : ∀ v c, x v c = w c * v c)
    (hd : ∀ v c, d v c = e c * v c) (hgx : ∀ v, g (x v) = x (g v)) {S : Set F}
    (he : ∀ c, w c ∈ S → e c = 1) (hg : ∀ c, w c ∉ S → g (Pi.single c 1) = Pi.single c 1) :
    Commute g d := by
  have hsingle : ∀ (y : ι → F) (c b : ι), y b * (Pi.single c (1 : F) : ι → F) b =
      y c * (Pi.single c (1 : F) : ι → F) b := by
    intro y c b
    by_cases hb : b = c
    · rw [hb]
    · rw [Pi.single_eq_of_ne hb, mul_zero, mul_zero]
  have hdc : ∀ c, d (Pi.single c 1) = e c • Pi.single c 1 := fun c => by
    funext b
    rw [hd, Pi.smul_apply, smul_eq_mul, hsingle]
  have key : ∀ c, g (d (Pi.single c 1)) = d (g (Pi.single c 1)) := by
    intro c
    by_cases hS : w c ∈ S
    · rw [hdc, he c hS, one_smul]
      have hxc : x (Pi.single c 1) = w c • Pi.single c 1 := by
        funext b
        rw [hxa, Pi.smul_apply, smul_eq_mul, hsingle]
      have h1 : x (g (Pi.single c 1)) = w c • g (Pi.single c 1) := by
        rw [← hgx, hxc, map_smul]
      funext b
      rw [hd]
      by_cases hvb : g (Pi.single c 1) b = 0
      · rw [hvb, mul_zero]
      · have hb := congrFun h1 b
        rw [hxa, Pi.smul_apply, smul_eq_mul] at hb
        rw [he b (mul_right_cancel₀ hvb hb ▸ hS), one_mul]
    · rw [hdc, map_smul, hg c hS, ← hdc]
  refine LinearEquiv.toLinearMap_injective (LinearMap.pi_ext fun c t => ?_)
  have ht : (Pi.single c t : ι → F) = t • Pi.single c 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  change g (d (Pi.single c t)) = d (g (Pi.single c t))
  rw [ht, map_smul, map_smul, key, map_smul, map_smul]

theorem ggTBJD4_sq_le_ncard {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) {J : Subgroup (spinGroup (quadPlus n K))}
    {x y : spinGroup (quadPlus n K)} (hx : x ∈ ggTorus (plusDatum n K hn))
    (hy : y ∈ ggTorus (plusDatum n K hn)) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxJ : x ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus n K))))
    (hyJ : y ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus n K))))
    {m₁ m₂ : Fin n ⊕ Fin n} (hx₁ : kgcDiag x m₁ ≠ 1) (hx₂ : kgcDiag x m₂ = 1)
    (hy₂ : kgcDiag y m₂ ≠ 1) :
    p ^ 2 ≤ Set.ncard {h | h ∈ ggTorus (plusDatum n K hn) ∧ h ^ p = 1 ∧
      h ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus n K)))} := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : {h | h ∈ ggTorus (plusDatum n K hn) ∧ h ^ p = 1 ∧
      h ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus n K)))}.Finite := by
    have : Finite (spinGroup (quadPlus n K)) :=
      Finite.of_injective (fun σ => ⇑(spinAction (quadPlus n K) σ))
        fun a b h => RootCentOmega.spinAction_quadPlus_injective (DFunLike.coe_injective h)
    exact Set.toFinite _
  have hpow1 : ∀ {z : spinGroup (quadPlus n K)} (m : Fin n ⊕ Fin n),
      z ∈ ggTorus (plusDatum n K hn) → z ^ p = 1 → kgcDiag z m ^ p = 1 := by
    intro z m hz hzp
    rw [← KGCentOm.kgcDiag_pow hn hz, hzp, KGCentOm.kgcDiag_one]
  have hprim : ∀ {z : spinGroup (quadPlus n K)} {m : Fin n ⊕ Fin n},
      z ∈ ggTorus (plusDatum n K hn) → z ^ p = 1 → kgcDiag z m ≠ 1 →
        IsPrimitiveRoot (kgcDiag z m) p := by
    intro z m hz hzp h1
    rw [← orderOf_eq_prime (hpow1 m hz hzp) h1]
    exact IsPrimitiveRoot.orderOf _
  have hv : ∀ (a b : ℕ) m, kgcDiag (x ^ a * y ^ b) m = kgcDiag x m ^ a * kgcDiag y m ^ b :=
    fun a b m => by
      rw [KGCentOm.kgcDiag_mul hn (pow_mem hx a), KGCentOm.kgcDiag_pow hn hx,
        KGCentOm.kgcDiag_pow hn hy]
  have hy0 : kgcDiag y m₁ ≠ 0 := by
    intro h0
    have h := hpow1 m₁ hy hyp
    rw [h0, zero_pow hp.ne_zero] at h
    exact zero_ne_one h
  have hf : Function.Injective fun ab : Fin p × Fin p => x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 := congrArg (kgcDiag · m₁) h
    have h2 := congrArg (kgcDiag · m₂) h
    simp only [hv, hx₂, one_pow, one_mul] at h1 h2
    have hb : b = b' := Fin.ext ((hprim hy hyp hy₂).pow_inj b.2 b'.2 h2)
    subst hb
    exact Prod.ext (Fin.ext ((hprim hx hxp hx₁).pow_inj a.2 a'.2
      (mul_right_cancel₀ (pow_ne_zero _ hy0) h1))) rfl
  have hrange : Set.range (fun ab : Fin p × Fin p => x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ)) ⊆
      {h | h ∈ ggTorus (plusDatum n K hn) ∧ h ^ p = 1 ∧
        h ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus n K)))} := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    refine ⟨mul_mem (pow_mem hx _) (pow_mem hy _), ?_, mul_mem (pow_mem hxJ _) (pow_mem hyJ _)⟩
    show (x ^ (a : ℕ) * y ^ (b : ℕ)) ^ p = 1
    rw [((KGCentOm.commute_of_mem_ggTorus_plus hn hx hy).pow_pow _ _).mul_pow, pow_right_comm x,
      hxp, one_pow, pow_right_comm y, hyp, one_pow, one_mul]
  calc p ^ 2 = Set.ncard (Set.range fun ab : Fin p × Fin p => x ^ (ab.1 : ℕ) * y ^ (ab.2 : ℕ)) := by
        rw [Set.ncard_range_of_injective hf, Nat.card_prod, Nat.card_fin, sq]
    _ ≤ _ := Set.ncard_le_ncard hrange hfin

theorem ggTBJD4_nonempty_mulEquiv {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) {J : Subgroup (spinGroup (quadPlus n F))}
    {T : Subgroup ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))}
    (hT : ∀ z, z ∈ J ↔ spinAction (quadPlus n F) z ∈ T)
    (hTle : T ≤ orthDerived (quadPlus n F)) : Nonempty (↥J ≃* ↥T) := by
  have hinj : Function.Injective (spinAction (quadPlus n F)) :=
    RootCentOmega.spinAction_quadPlus_injective
  have hmap : J.map (spinAction (quadPlus n F)) = T := by
    ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hT z).mp hz
    · intro hg
      have hgr : g ∈ (spinAction (quadPlus n F)).range := by
        rw [range_spinAction_quadPlus_eq_commutator hn]
        exact hTle hg
      obtain ⟨z, rfl⟩ := hgr
      exact ⟨z, (hT z).mpr hg, rfl⟩
  exact ⟨(J.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hmap)⟩

end CFSG.StandardType

end
