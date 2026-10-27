module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
import CFSG.Adapters.LinearFieldTransport
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Open.StatedCenterThree
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.StandardType.GGHalf

section Cover

theorem sl3_or_psl_of_quotient {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hodd : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hP : LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) F4) ∨
      Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) := by
  have hP' : CFSG.Quasithin.IsPSL 3 2 2 (X ⧸ Subgroup.center X) :=
    CFSG.Blueprint.LieModel.statedClassicalModel hP (by decide)
  obtain ⟨F, hF, hFfin, hFcard, hor⟩ :=
    CFSG.Quasithin.H13.S126P31.exists_mulEquiv_psl_or_sl_of_quotient hperf hodd hP'
  letI : Field F := hF
  letI : Finite F := hFfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : Nat.card F = 2 ^ 2 := by simpa using hFcard
  let e : F ≃+* F4 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 2 (by norm_num) h4
  rcases hor with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exact Or.inr ⟨ψ.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv e (Fin 3)))⟩
  · exact Or.inl ⟨ψ.trans
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.trans
        (CFSG.ClassicalModels.specialLinearFieldEquiv e (Fin 3)))⟩

end Cover

end CFSG.StandardType.GGSixE6Two
