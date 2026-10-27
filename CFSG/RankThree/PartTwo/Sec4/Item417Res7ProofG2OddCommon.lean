module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.LocalAnalysis.EvenBN.G2.Torus
public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate8026Base

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley

namespace Res417Seven

theorem descent_of_fixed {G : Type*} [Group G] (s : G →* G) (hs : ∀ g, s (s g) = g) {n d y : G}
    (hn : s n = n) (hn2 : n * n = 1) (hd : n * d * n⁻¹ = s d)
    (hE : s (y * d * y⁻¹) = y * d * y⁻¹) :
    (y⁻¹ * s y * n⁻¹) * d = d * (y⁻¹ * s y * n⁻¹) ∧
    (y⁻¹ * s y * n⁻¹) * (n * s (y⁻¹ * s y * n⁻¹) * n⁻¹) = 1 ∧
    ∀ x, s x = x → x * (y * d * y⁻¹) = (y * d * y⁻¹) * x →
      (y⁻¹ * x * y) * d = d * (y⁻¹ * x * y) ∧
      (y⁻¹ * s y * n⁻¹) * (n * s (y⁻¹ * x * y) * n⁻¹) * (y⁻¹ * s y * n⁻¹)⁻¹ = y⁻¹ * x * y := by
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have hE' : s y * (n * d * n⁻¹) * (s y)⁻¹ = y * d * y⁻¹ := by
    rw [hd, ← map_inv, ← map_mul, ← map_mul]
    exact hE
  refine ⟨?_, ?_, fun x hx hxE => ⟨?_, ?_⟩⟩
  ·
    have h1 : (y⁻¹ * s y * n⁻¹) * d * (y⁻¹ * s y * n⁻¹)⁻¹ = d := by
      calc (y⁻¹ * s y * n⁻¹) * d * (y⁻¹ * s y * n⁻¹)⁻¹ =
          y⁻¹ * (s y * (n⁻¹ * d * n) * (s y)⁻¹) * y := by group
        _ = y⁻¹ * (s y * (n * d * n⁻¹) * (s y)⁻¹) * y := by rw [hninv]
        _ = y⁻¹ * (y * d * y⁻¹) * y := by rw [hE']
        _ = d := by group
    calc (y⁻¹ * s y * n⁻¹) * d =
        ((y⁻¹ * s y * n⁻¹) * d * (y⁻¹ * s y * n⁻¹)⁻¹) * (y⁻¹ * s y * n⁻¹) := by group
      _ = d * (y⁻¹ * s y * n⁻¹) := by rw [h1]
  ·
    rw [map_mul, map_mul, map_inv, map_inv, hs, hn]
    calc y⁻¹ * s y * n⁻¹ * (n * ((s y)⁻¹ * y * n⁻¹) * n⁻¹) = n⁻¹ * n⁻¹ := by group
      _ = 1 := by rw [hninv, hn2]
  ·
    calc y⁻¹ * x * y * d = y⁻¹ * (x * (y * d * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * d * y⁻¹) * x) * y := by rw [hxE]
      _ = d * (y⁻¹ * x * y) := by group
  ·
    rw [map_mul, map_mul, map_inv, hx]
    group

section Longest


theorem g2LongestWeyl_smul_eq_neg (v : Fin Tag.G2.rank → ℤ) : g2LongestWeyl • v = -v := by
  conv_lhs => rw [g2_eq_smul_add v]
  conv_rhs => rw [g2_eq_smul_add v]
  rw [smul_add, smul_comm _ (v g2ia), smul_comm _ (v g2ir), g2LongestWeyl_smul_g2a,
    g2LongestWeyl_smul_g2r, smul_neg, smul_neg, neg_add]

theorem g2LongestWeyl_mul_self : g2LongestWeyl * g2LongestWeyl = 1 :=
  weyl_G2_ext (by rw [mul_smul, g2LongestWeyl_smul_eq_neg, g2LongestWeyl_smul_eq_neg, neg_neg,
    one_smul]) (by rw [mul_smul, g2LongestWeyl_smul_eq_neg, g2LongestWeyl_smul_eq_neg, neg_neg,
    one_smul])

variable {L : Type} [Field L]

theorem g2_longest_mul_self [CharP L 2] :
    canonicalRep (coxeterSystem .G2) L g2LongestWeyl *
      canonicalRep (coxeterSystem .G2) L g2LongestWeyl = 1 := by
  rw [← CFSG.LocalAnalysis.EvenBN.G2.Model.canonicalRep_mul_two, g2LongestWeyl_mul_self,
    canonicalRep_one]

theorem g2_longest_conj_rootDiagUnit (c : Fin Tag.G2.rank → Lˣ) :
    canonicalRep (coxeterSystem .G2) L g2LongestWeyl * rootDiagUnit .G2 c *
      (canonicalRep (coxeterSystem .G2) L g2LongestWeyl)⁻¹ = rootDiagUnit .G2 c⁻¹ :=
  ((rootDiagUnit_eq_conj_canonicalRep_iff c⁻¹ c g2LongestWeyl).mpr fun v => by
    rw [g2LongestWeyl_smul_eq_neg, rootChar_neg_eq_inv, rootChar_inv_apply, inv_inv]).symm



theorem g2_longest_conj_pinnedX [CharP L 2] {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (x : L) :
    canonicalRep (coxeterSystem .G2) L g2LongestWeyl * pinnedX .G2 L α x *
      (canonicalRep (coxeterSystem .G2) L g2LongestWeyl)⁻¹ = pinnedX .G2 L (-α) x := by
  rw [canonicalRep_conj g2LongestWeyl hα x, g2LongestWeyl_smul_eq_neg]

theorem baseChangeGL_g2_longest (σ : L →+* L) :
    baseChangeGL σ (canonicalRep (coxeterSystem .G2) L g2LongestWeyl) =
      canonicalRep (coxeterSystem .G2) L g2LongestWeyl :=
  baseChangeGL_canonicalRep σ g2LongestWeyl

end Longest

section Frobenius

variable
  {L : Type} [Field L]

theorem baseChangeGL_involutive {σ : L →+* L} (hσ : ∀ c, σ (σ c) = c) (g : ModGL .G2 L) :
    baseChangeGL σ (baseChangeGL σ g) = g := by
  rw [baseChangeGL_baseChangeGL, show σ.comp σ = RingHom.id L from RingHom.ext hσ,
    baseChangeGL_id]

theorem baseChangeGL_rootDiagUnit_mulSingle {σ : L →+* L} {ζ : Lˣ} (hζ : σ ζ = (ζ⁻¹ : Lˣ))
    (i : Fin Tag.G2.rank) :
    baseChangeGL σ (rootDiagUnit .G2 (Pi.mulSingle i ζ)) =
      rootDiagUnit .G2 (Pi.mulSingle i ζ)⁻¹ := by
  rw [baseChangeGL_rootDiagUnit]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.mulSingle_eq_same, Pi.inv_apply]
    exact Units.ext hζ
  · simp only [Pi.mulSingle_eq_of_ne hj, Pi.inv_apply, inv_one]
    exact Units.ext (map_one σ)

theorem baseChangeGL_mem_adjointGroup_G2
    (σ : L →+* L) {g : ModGL .G2 L} (hg : g ∈ adjointGroup .G2 L) :
    baseChangeGL σ g ∈ adjointGroup .G2 L :=
  baseChangeGL_mem_adjointGroup σ hg

end Frobenius

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
