module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartTwo.Census.Models
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank Matrix

noncomputable section

def statedProjEquivProjImage {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : StatedProj H ≃* projImage H :=
  CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk H

theorem statedSL_eq_ker_det (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det n K

theorem projImage_statedSL (n : ℕ) (K : Type) [Field K] :
    projImage (StatedSL n K) = projSL n K :=
  CFSG.PGLModel.projImage_statedSL n K

def typeAGroupEquivProjSL (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) [Fact q.p.Prime] :
    TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩ ≃*
      projSL (r + 1) (GaloisField q.p q.exponent) :=
  (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
    ((projectiveSpecialLinearGroupEquivStatedProj _ _).trans
      ((statedProjEquivProjImage _).trans (MulEquiv.subgroupCongr (projImage_statedSL _ _))))

theorem projImage_statedSU (n p f : ℕ) [Fact p.Prime] :
    projImage (StatedSU n (p ^ f) (GaloisField p (2 * f))) = projSU n p f :=
  CFSG.PGLModel.projImage_statedSU n p f

def typeTwistedAGroupEquivProjSU (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) [Fact q.p.Prime] :
    TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩ ≃* projSU (r + 1) q.p q.exponent :=
  (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv).trans
    ((statedProjEquivProjImage _).trans (MulEquiv.subgroupCongr (projImage_statedSU _ _ _)))

theorem item433Case_A_five_two (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 5 q).Valid)
    (hp : q.p = 2) (hf : q.exponent = 1) : Item433Case (.lie ⟨.A 5 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := hf
  exact fun _ _ _ _ e => iiModel_of_projSL_six_two (e.trans (typeAGroupEquivProjSL 5 _ hv))

theorem item433Case_A_six_two (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 6 q).Valid)
    (hp : q.p = 2) (hf : q.exponent = 1) : Item433Case (.lie ⟨.A 6 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := hf
  exact fun _ _ _ _ e => iiModel_of_projSL_seven_two (e.trans (typeAGroupEquivProjSL 6 _ hv))

theorem item433Case_A_three_four (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 3 q).Valid) (hp : q.p = 2) (hf : q.exponent = 2) :
    Item433Case (.lie ⟨.A 3 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 2 := hf
  exact fun _ _ _ _ e => iiModel_of_projSL_four_four (e.trans (typeAGroupEquivProjSL 3 _ hv))

theorem item433Case_twistedA_four_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid) (hp : q.p = 2) (hf : q.exponent = 1) :
    Item433Case (.lie ⟨.twistedA 4 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := hf
  exact fun _ _ _ _ e => iiModel_of_projSU_five_two (e.trans (typeTwistedAGroupEquivProjSU 4 _ hv))

theorem item433Case_twistedA_five_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hp : q.p = 2) (hf : q.exponent = 1) :
    Item433Case (.lie ⟨.twistedA 5 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := hf
  exact fun _ _ _ _ e => iiModel_of_projSU_six_two (e.trans (typeTwistedAGroupEquivProjSU 5 _ hv))

theorem item433Case_twistedA_four_eight (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid) (hp : q.p = 2) (hf : q.exponent = 3) :
    Item433Case (.lie ⟨.twistedA 4 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 3 := hf
  exact fun _ _ _ _ e =>
    iiModel_of_projSU_five_eight (e.trans (typeTwistedAGroupEquivProjSU 4 _ hv))

end

end CFSG.RankThree.PartTwo.Census
