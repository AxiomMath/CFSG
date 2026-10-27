module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Action
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightOmega
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem eq_glBlockCentralizer_of_finrank_six_POmegaPlus
    {k f : ℕ}
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hdim : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 6) :
    J' = (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
      Subgroup (ggU .POmegaPlus (k + 3) f).K) := by
  classical
  have hrankeq : e.rank =
      Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) := by
    rw [Matrix.rank_eq_finrank_range_toLin e (Pi.basisFun (GaloisField 2 f) _)
      (Pi.basisFun (GaloisField 2 f) _), Matrix.toLin_eq_toLin']
  have hrank : e.rank = 2 * 3 := by omega
  have hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]) := by
    rintro ⟨hfour, -⟩
    omega
  have h1 : bmsdop_geom₁ k f S e :=
    bmsdop_block_idem_and_degree k f S hS hodd he hadj hdeg hnm
  have h2 : bmsdop_geom₂ k f S e :=
    bmsdop_block_trivial_and_split k f S hSU hS hodd he hadj hdeg hnm
  rcases bmsdop_theta k f S h1 h2 3 hrank (by norm_num) with
    ⟨θ, hθ⟩ | ⟨β, γ, hirr, θ, hθ⟩
  · obtain ⟨_, _, _, _, _, hJ'⟩ :=
      bmsdop_plus_embedding k f S h1 h2 hS he.1 hJe 3 le_rfl hrank θ hθ
    exact hJ'
  · let _hAC : Algebra.IsCentral (GaloisField 2 f)
        (CliffordAlgebra (Spin.quadMinus 3 (GaloisField 2 f) β γ)) :=
      Spin.isCentral_cliffordAlgebra_quadMinus 3 β γ hirr
    have hnd : (QuadraticMap.polarBilin
        (Spin.quadMinus 3 (GaloisField 2 f) β γ)).Nondegenerate :=
      Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (GaloisField 2 f) hirr
    have hE : bmsdop_ExtProps k f S e (Spin.quadMinus 3 (GaloisField 2 f) β γ) hnd θ
        (bmsdop_glue k f S h1 θ) := by
      obtain ⟨hb1, hb2, hb3, hb4⟩ := bmsdop_glue_basic k f S h1 h2
        (Spin.quadMinus 3 (GaloisField 2 f) β γ) θ hθ
      exact ⟨hb1, hb2, hb3, hb4,
        fun g => bmsdop_glue_omegaGroup k f S h1 h2
          (Spin.quadMinus 3 (GaloisField 2 f) β γ) θ hθ hnd g⟩
    obtain ⟨ι₁, hι₁inj, hι₁range, -, -⟩ :=
      bmsdop_iota₁ k f S h1 h2 hS he.1 (Spin.quadMinus 3 (GaloisField 2 f) β γ) hnd
        (bmsdop_glue k f S h1 θ) θ hE hθ (bmsdop_r3m_range f β γ hirr)
    exact bmsdop_component_eq k f S h1 h2 (Spin.quadMinus 3 (GaloisField 2 f) β γ)
      (bmsdop_r3m_quasisimple f β γ hirr) ι₁ ⟨hι₁inj, hι₁range⟩ hJe

theorem rckIIp_POmegaPlus_selfDual_fixed
    {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      e.mulVec x = x → e.mulVec y = y → Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))))
    (hA8 : Nonempty ((↥(J'.map φ) ⧸ Subgroup.center ↥(J'.map φ)) ≃* alternatingGroup (Fin 8))) :
    f = 1 ∧
      J' = (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
        Subgroup (ggU .POmegaPlus (k + 3) f).K) ∧
      Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 6 := by
  classical
  obtain ⟨t', m, ι, _β₀, hcase, _hlong, hcenter, hrange, _hframe⟩ :=
    exists_blockModel_selfDual_POmegaPlus_explicit k f hf S hSU hS hodd he hadj hdeg hnm hJe
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let φ' : ↥(spinGroup Q) →* X := φ
  let π : (ggU t' m f).K →* X := φ'.comp ι
  have hπrange : π.range = J'.map φ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ι y, le_of_eq hrange (MonoidHom.mem_range.mpr ⟨y, rfl⟩), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp (le_of_eq hrange.symm hy)
      exact ⟨z, rfl⟩
  have hφ'k : φ'.ker ≤ Subgroup.center ↥(spinGroup Q) := hφk
  have hπker : π.ker ≤ Subgroup.center (ggU t' m f).K := by
    intro y hy
    apply hcenter
    apply hφ'k
    show φ' (ι y) = 1
    exact hy
  have hodd' : Odd (Nat.card (Subgroup.center ↥π.range)) := by
    rw [hπrange]
    exact hoddJ
  have hA8' : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπrange]
    exact hA8
  rcases hcase with ⟨htag, hm3, hfin⟩ | ⟨htag, hm2, _hfin4⟩
  · rcases htag with ht | ht
    · subst ht
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · have hm3' : m = 3 := by omega
        subst hm3'
        have hf1 : f = 1 :=
          rckIIp_eq_one_of_alt_eight_POmegaPlus_three hf π hπker hodd' hA8'
        refine ⟨hf1, ?_, ?_⟩
        · exact eq_glBlockCentralizer_of_finrank_six_POmegaPlus S hSU hS hodd he hadj hdeg
            hJe (by omega)
        · omega
      · exact (rckIIp_false_of_alt_eight_POmegaPlus (r := m) hm4 hf π hπker hodd' hA8').elim
    · subst ht
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · have hm3' : m = 3 := by omega
        subst hm3'
        exact (rckIIp_false_of_alt_eight_POmegaMinus_three hf π hπker hodd' hA8').elim
      · exact (rckIIp_false_of_alt_eight_POmegaMinus (r := m) hm4 hf π hπker hodd' hA8').elim
  · subst htag
    subst hm2
    let π' : Matrix.SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 f) →* X := π
    have hπ'ker : π'.ker ≤ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 f)) := hπker
    have hodd'' : Odd (Nat.card (Subgroup.center ↥π'.range)) := hodd'
    have hA8'' : Nonempty ((↥π'.range ⧸ Subgroup.center ↥π'.range) ≃*
        alternatingGroup (Fin 8)) := hA8'
    have hk : (1 : ℕ) = 3 :=
      (rckIIp_eq_three_one_of_alt_eight (k := 1) (h := f) hf π' hπ'ker hodd'' hA8'').1
    exact absurd hk (by norm_num)

end CFSG.StandardType.RCKC1
