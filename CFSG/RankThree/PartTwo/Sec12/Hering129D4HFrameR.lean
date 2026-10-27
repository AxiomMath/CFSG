module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HQv
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec19


section FrameR

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X} (P : D4Par n X σ)
  {L : Type} [Field L] [Algebra X L] [IsAlgClosure X L] [CharP L 2]
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {ε : ℤ}
  {ζ : Lˣ} (hζ : orderOf ζ = 3) {g : ModGL TwistTag.D4.tag L}
  (hgG : g ∈ adjointGroup TwistTag.D4.tag L) (hFg : trialityFrob L Fr g = g * threeSixN L ε)

include P hFr hζ hgG hFg

theorem phi_mem_adjoint (x : C0 σ) : threeSixEmb' L X σ g x ∈ adjointGroup TwistTag.D4.tag L := by
  have hrange := range_threeSixEmb Nat.prime_two P.one_le P.card P.frob Fr hFr
  exact ((mem_range_threeSixEmb' (K := X) (σ := σ) hrange hgG hFg _).1 ⟨x, rfl⟩).1

theorem phi_mem_R_iff (x : C0 σ) :
    x ∈ threeSixSingularR L X σ Fr ε vT g ↔ threeSixEmb' L X σ g x ∈ d4A2Qv L vT := by
  have hrange := range_threeSixEmb Nat.prime_two P.one_le P.card P.frob Fr hFr
  rw [threeSixSingularR_eq_comap hrange hgG hFg vT]
  exact Iff.rfl

theorem y_mem_R {y : C0 σ} (hy : threeSixEmb' L X σ g y = nw L wT) :
    y ∈ threeSixSingularR L X σ Fr ε vT g :=
  (phi_mem_R_iff P hFr hζ hgG hFg y).2 (by rw [hy]; exact nwT_mem_Qv hζ)

theorem c_mem_R {c : C0 σ}
    (hc : threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT)) :
    c ∈ threeSixSingularR L X σ Fr ε vT g :=
  (phi_mem_R_iff P hFr hζ hgG hFg c).2 (by rw [hc]; exact cE_mem_Qv hζ)

theorem phi_mem_M {c : C0 σ}
    (hc : threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT)) {u : C0 σ}
    (hu : u ∈ Subgroup.centralizer ({c} : Set (C0 σ))) :
    threeSixEmb' L X σ g u ∈ toralCentralizer TwistTag.D4.tag L (tup ζ gT) := by
  have hrange := range_threeSixEmb Nat.prime_two P.one_le P.card P.frob Fr hFr
  have hinj : Function.Injective (threeSixEmb' L X σ g) := threeSixEmb'_injective g
  refine mem_toralCentralizer.2 ⟨phi_mem_adjoint P hFr hζ hgG hFg u, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hu
  have h := congrArg (threeSixEmb' L X σ g) hu
  rw [map_mul, map_mul, hc] at h
  rw [mul_inv_eq_iff_eq_mul]
  exact h.symm

theorem R_comm_c {c : C0 σ}
    (hc : threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT)) :
    ∀ r ∈ threeSixSingularR L X σ Fr ε vT g, r * c = c * r := by
  intro r hr
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed X
  have hinj : Function.Injective (threeSixEmb' L X σ g) := threeSixEmb'_injective g
  have hrQ := (phi_mem_R_iff P hFr hζ hgG hFg r).1 hr
  obtain ⟨hQM, -⟩ := Qv_le_and_derived (Ω := L) hζ
  have hM := mem_toralCentralizer.1 (hQM hrQ)
  apply hinj
  rw [map_mul, map_mul, hc]
  have := hM.2
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem comm_le_R {c : C0 σ}
    (hc : threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT)) :
    ⁅Subgroup.centralizer ({c} : Set (C0 σ)), Subgroup.centralizer ({c} : Set (C0 σ))⁆ ≤
      threeSixSingularR L X σ Fr ε vT g := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed X
  rw [Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨-, hder⟩ := Qv_le_and_derived (Ω := L) hζ
  rw [phi_mem_R_iff P hFr hζ hgG hFg, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
    map_inv]
  rw [← hder]
  exact Subgroup.commutator_mem_commutator (phi_mem_M P hFr hζ hgG hFg hc hu)
    (phi_mem_M P hFr hζ hgG hFg hc hv)

end FrameR

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
