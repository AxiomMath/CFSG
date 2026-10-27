module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
public import CFSG.RankThree.GF2n.Parrott.Lemma14
public import CFSG.RankThree.GF2n.Parrott.Section2Theorem1Assembly
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.SylowIntersectionControl.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.RankThree.GF2n.Parrott.Parrott77Lemma6
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_conj_mem_cosets_of_involution {x : G} (hxH : x ∈ H z) (hxJ : x ∉ J z)
    (hx2 : orderOf x = 2) :
    ∃ k ∈ H z, cosetJ (z := z) (tH D) (k * x * k⁻¹) ∨
      cosetJ (z := z) (tH D * uH D) (k * x * k⁻¹) ∨
      cosetJ (z := z) (uH D * vH D) (k * x * k⁻¹) ∨
      cosetJ (z := z) (uH D * vH D * tH D) (k * x * k⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxq2 : orderOf (qH D ⟨x, hxH⟩) = 2 := by
    apply orderOf_eq_prime
    · have hsq : (⟨x, hxH⟩ : ↥(H z)) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← hx2]
        exact pow_orderOf_eq_one x)
      rw [← map_pow, hsq, map_one]
    · intro h1
      exact hxJ (Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1))
  have key : ∀ s : ↥(H z), IsConj (qH D ⟨x, hxH⟩) (qH D s) →
      ∃ k ∈ H z, cosetJ (z := z) s (k * x * k⁻¹) := by
    intro s hs
    obtain ⟨c, hc⟩ := isConj_iff.mp hs
    obtain ⟨k, rfl⟩ := qH_surjective D c
    have h1 : qH D (s⁻¹ * (k * ⟨x, hxH⟩ * k⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
    have h2 : ((s⁻¹ * (k * ⟨x, hxH⟩ * k⁻¹) : ↥(H z)) : G) ∈ J z :=
      Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
    refine ⟨k, k.2, _, h2, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rcases qa45_involution_classes (qH D ⟨x, hxH⟩) hxq2 with h1 | h2 | h3 | h4
  · obtain ⟨k, hk, hc⟩ := key (tH D) (by rw [qH_tH]; exact h1)
    exact ⟨k, hk, Or.inl hc⟩
  · have htu : qH D (tH D * uH D) =
        (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨t, t_mem_A⟩ := by
      rw [map_mul, qH_tH, qH_uH]
      exact Subtype.ext t_commute_u
    obtain ⟨k, hk, hc⟩ := key (tH D * uH D) (by rw [htu]; exact h2)
    exact ⟨k, hk, Or.inr (Or.inl hc)⟩
  · have hv : IsConj (⟨v, v_mem_A⟩ : QA45.originalSubgroup)
        ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) :=
      isConj_iff.mpr ⟨⟨beta, beta_mem_A⟩, conj_v_uvt_QA45⟩
    obtain ⟨k, hk, hc⟩ := key (uH D * vH D * tH D)
      (by rw [map_mul, map_mul, qH_uH, qH_vH, qH_tH]; exact h3.trans hv)
    exact ⟨k, hk, Or.inr (Or.inr (Or.inr hc))⟩
  · obtain ⟨k, hk, hc⟩ := key (uH D * vH D)
      (by rw [map_mul, qH_uH, qH_vH]; exact h4)
    exact ⟨k, hk, Or.inr (Or.inr (Or.inl hc))⟩

theorem no_conj_z_out_of_cosets (_h : Tim79a.ParrottHyp z)
    (ht : ∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x)
    (htu : ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x)
    (huv : ∀ x : G, cosetJ (z := z) (uH D * vH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x)
    (huvt : ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x := by
  intro x hxH hxJ hx2 g hg
  obtain ⟨k, -, hcos⟩ := exists_conj_mem_cosets_of_involution D hxH hxJ hx2
  have hy2 : orderOf (k * x * k⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj k) x
    rwa [MulAut.conj_apply, hx2] at this
  have hyz : (k * g) * z * (k * g)⁻¹ = k * x * k⁻¹ := by rw [← hg]; group
  rcases hcos with h1 | h2 | h3 | h4
  · exact ht _ h1 hy2 _ hyz
  · exact htu _ h2 hy2 _ hyz
  · exact huv _ h3 hy2 _ hyz
  · exact huvt _ h4 hy2 _ hyz

theorem eq_centralizer_sup_pPrimeCore_of_cosets (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z →
      ∀ g : G, g * z * g⁻¹ ≠ j)
    (ht : ∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x)
    (htu : ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x)
    (huv : ∀ x : G, cosetJ (z := z) (uH D * vH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x)
    (huvt : ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    H z ⊔ pPrimeCore 2 G = ⊤ :=
  eq_centralizer_sup_pPrimeCore_of_classes (z := z) h hJ
    (no_conj_z_out_of_cosets (z := z) D h ht htu huv huvt)
end CFSG.RankThree.GF2n.Parrott
