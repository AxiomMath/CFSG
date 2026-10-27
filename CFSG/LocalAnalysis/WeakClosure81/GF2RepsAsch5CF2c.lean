module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (uc22p20bSimpSec uc22p20b_simpSec_of_cf uc22p20b_simpSec_restrict
    uc22p20b_simpSec_of_surjective uc22p20b_simpSec_comm uc22p20b_simpSec_simple)

theorem outSolvable_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : OutSolvable A) : OutSolvable B := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  let φ : MulAut A →* MulAut B := (MulAut.congr e).toMonoidHom
  have hφ : Function.Surjective φ := (MulAut.congr e).surjective
  rw [← map_derivedSeries_eq hφ n]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨a, rfl⟩ := hn hy
  refine ⟨e a, ?_⟩
  ext b
  simp [φ, MulAut.congr_apply]

theorem nonempty_mulEquiv_of_simpSec_genFittingFStar {K : Type} [Group K] [Finite K]
    {Λ : Type} [Group Λ] (hnc : ∃ a b : Λ, a * b ≠ b * a) (hs : uc22p20bSimpSec K Λ)
    {X : Type} [Group X] (hX : IsSimpleGroup X) (hXout : OutSolvable X)
    (e : ↥(CFSG.Open.genFittingFStar K) ≃* X) : Nonempty (X ≃* Λ) := by
  haveI : (CFSG.Open.genFittingFStar K).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal K
  have hC : Subgroup.centralizer (CFSG.Open.genFittingFStar K : Set K) ≤
      CFSG.Open.genFittingFStar K :=
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le K
  have hout : OutSolvable ↥(CFSG.Open.genFittingFStar K) := outSolvable_of_mulEquiv e.symm hXout
  haveI : Group.IsSolvable (K ⧸ CFSG.Open.genFittingFStar K) :=
    isSolvable_quotient_of_outSolvable _ hC hout
  rcases uc22p20b_simpSec_restrict (CFSG.Open.genFittingFStar K) hs with h1 | h2
  · haveI := hX
    haveI : IsSimpleGroup ↥(CFSG.Open.genFittingFStar K) := e.isSimpleGroup
    obtain ⟨e'⟩ := uc22p20b_simpSec_simple hnc h1
    exact ⟨e.symm.trans e'⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h2 a b)

theorem cfShape_of_fStarMod {Q : Type} [Group Q] [Finite Q] {H N : Subgroup Q}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hsolv : Group.IsSolvable ↥N)
    {P : ∀ (X : Type) [Group X], Prop} (hP : IsoInvPred P)
    (hX : ∀ (X : Type) [Group X] [Finite X], P X →
      IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ OutSolvable X)
    (h : HasQuotShape (fStarMod N H) (N : Set Q) P) : CFShape ↥H P := by
  obtain ⟨X, hXg, hPX, ⟨e⟩⟩ := exists_mulEquiv_genFittingFStar_of_hasQuotShape hN h
  haveI : Finite X := Finite.of_equiv _ e.toEquiv
  obtain ⟨hXs, -, hXout⟩ := hX X hPX
  intro Λ _ hcf hnc
  haveI := hN
  have hcore : (N.subgroupOf H).normalCore = N.subgroupOf H := Subgroup.normalCore_eq_self _
  have hNs : Group.IsSolvable ↥(N.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNH).injective
  rcases uc22p20b_simpSec_restrict (N.subgroupOf H) (uc22p20b_simpSec_of_cf hcf) with h1 | h2
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h1 a b)
  · have h2' : uc22p20bSimpSec (↥H ⧸ (N.subgroupOf H).normalCore) Λ :=
      uc22p20b_simpSec_of_surjective (QuotientGroup.quotientMulEquivOfEq hcore).toMonoidHom
        (QuotientGroup.quotientMulEquivOfEq hcore).surjective h2
    obtain ⟨e'⟩ := nonempty_mulEquiv_of_simpSec_genFittingFStar hnc h2' hXs hXout e
    exact hP X Λ ⟨e'⟩ hPX

end CFSG.LocalAnalysis.WeakClosure81
