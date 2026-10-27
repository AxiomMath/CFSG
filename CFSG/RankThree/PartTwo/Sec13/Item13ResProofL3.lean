module

public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3Proof
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofQuot
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCenter
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartOne.LIT.RankProjective
public import CFSG.GroupTheory.LocalCores.Components

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi)

theorem exists_centerQuot_equiv_projImage {X : Type} [Group X] {q : ℕ}
    (hX : Sec4.IsSLThreePiAt X q) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      p ^ f = q ∧ Nonempty (X ⧸ Subgroup.center X ≃* projImage (slPi π 3 (p ^ f) K)) := by
  obtain ⟨π, p, f, K, _, hK, hq, hpq, ⟨e⟩⟩ := Sec12.Item128StepsProof.exists_model hX
  refine ⟨π, p, f, K, inferInstance, hK, hq, hpq, ?_⟩
  have hc : (Subgroup.center X).map (e : X →* slPi π 3 (p ^ f) K) =
      Subgroup.center (slPi π 3 (p ^ f) K) := Subgroup.map_center_eq e
  have hcen : Subgroup.center (slPi π 3 (p ^ f) K) =
      (Subgroup.center (GL (Fin 3) K)).subgroupOf (slPi π 3 (p ^ f) K) := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      obtain ⟨ζ, -, hζ⟩ := KFacts.exists_scalar_of_mem_center hK hq hz
      rw [hζ, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨ζ, rfl⟩
    · intro hz
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp hz (y : GL (Fin 3) K))
  exact ⟨(QuotientGroup.congr _ _ e hc).trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (CFSG.RankThree.PartOne.LIT.projEquiv _))⟩

theorem isLThreePi_quotient_center_of_isSLThreePi {X : Type} [Group X]
    (hX : Sec4.IsSLThreePi X) : IsLThreePi (X ⧸ Subgroup.center X) := by
  obtain ⟨q, hXq⟩ := hX
  obtain ⟨π, p, f, K, _, hK, hq, -, ⟨e⟩⟩ := exists_centerQuot_equiv_projImage hXq
  exact isLThreePi_of_mulEquiv e (isLThreePi_projImage_slPi hK hq)

theorem isQuasisimple_quotient_center {X : Type} [Group X] (hX : IsQuasisimple X) :
    IsQuasisimple (X ⧸ Subgroup.center X) := by
  obtain ⟨-, hs, hnc⟩ := hX
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem exists_rank_three_centralizer_of_isSLThreePi {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (hnq : ¬ IsQuasisimple X) (hO2 : CFSG.pCore 2 X = ⊥)
    (hO : IsQuasisimple (X ⧸ CFSG.oddCore X))
    (hbar : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (hSL : Sec4.IsSLThreePi (X ⧸ aschbacherSolvableCore 3 X))
    {z : X} (hzZ : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ ∃ t : X, orderOf t = 2 ∧
      ∃ P : Subgroup X, P ≤ Subgroup.centralizer {t} ∧ 3 ≤ CFSG.pRank r P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.zpowers z with hNdef
  have hNZ : N ≤ Subgroup.center X := Subgroup.zpowers_le.mpr hzZ
  have : N.Normal := Subgroup.normal_of_le_center hNZ
  have hN3 : Nat.card N = 3 := by rw [Nat.card_zpowers, hz3]
  set θ := aschbacherSolvableCore 3 X with hθ
  set ρ := QuotientGroup.mk' θ with hρ
  have hθX := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hZ : Subgroup.center (X ⧸ θ) = N.map ρ := by
    have hle : N.map ρ ≤ Subgroup.center (X ⧸ θ) := by
      rintro _ ⟨n, hn, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hNZ hn) x]
    have hinj : Set.InjOn ρ N := by
      intro a ha b hb hab
      have hmem : a⁻¹ * b ∈ θ := by
        rw [← QuotientGroup.eq]
        exact hab
      have hNmem : a⁻¹ * b ∈ N := N.mul_mem (N.inv_mem ha) hb
      have h1 : orderOf (a⁻¹ * b) ∣ 3 := by
        rw [← hN3, ← Subgroup.orderOf_mk _ hNmem]
        exact orderOf_dvd_natCard _
      have h2 : orderOf (a⁻¹ * b) ∣ Nat.card θ := by
        rw [← Subgroup.orderOf_mk _ hmem]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime 3 (Nat.card θ) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθX.2.2.1
      have h3 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
      rw [inv_mul_eq_one] at h3
      exact h3
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_center_of_isSLThreePi hSL, card_map_eq_of_injOn ρ hinj, hN3]
  have hYnq : ¬ IsQuasisimple (X ⧸ N) := not_isQuasisimple_quotient N hNZ hnq
  have hYO2 : CFSG.pCore 2 (X ⧸ N) = ⊥ := pCore_two_quotient_eq_bot N hNZ hN3 hO2
  have hYO : IsQuasisimple ((X ⧸ N) ⧸ CFSG.oddCore (X ⧸ N)) := by
    obtain ⟨e⟩ := nonempty_quotient_oddCore_equiv N hN3
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hO
  obtain ⟨eθ⟩ := nonempty_quotient_theta_equiv N hbar hZ
  have hYbar : IsQuasisimple ((X ⧸ N) ⧸ aschbacherSolvableCore 3 (X ⧸ N)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eθ.symm (isQuasisimple_quotient_center hbar)
  obtain ⟨p, e, hp, he, hL⟩ :=
    isLThreePi_of_mulEquiv eθ (isLThreePi_quotient_center_of_isSLThreePi hSL)
  obtain ⟨r, hr, hr3, t, ht, P, hPt, hP⟩ :=
    L3Proof.exists_rank_three_centralizer hYnq hYO2 hYO hYbar he hL
  obtain ⟨s, hs, P', hP's, hP'⟩ :=
    exists_lift_involution_rank N hNZ hN3 hr (by omega) ht hPt hP
  exact ⟨r, hr, hr3, s, hs, P', hP's, hP'⟩

end CFSG.RankThree.PartTwo.Sec13.ResProof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item135L3 : Item135L3 := by
  intro G _ _ A c L hD _ hnq hO2 hm hO htype
  rcases htype with hL3 | ⟨q, -, hSL⟩
  · exact item135SimpleL3 G A c L hD hnq hO2 hm hO hL3
  · have hLc := hD.mem_thetaComponentsAt
    have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
    have hbar : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
      Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
    have hnq' : ¬ IsQuasisimple L := fun hq => hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientBot (G := L)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hO2).symm) hq)
    have hSL' : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) := ⟨q, hSL⟩
    have hcL : c ∈ L := ResProof.mem_of_three_dvd_card_center hD
      (by rw [card_center_of_isSLThreePi hSL'])
    have hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer l.2))
    have hc3 : orderOf (⟨c, hcL⟩ : L) = 3 := by rw [Subgroup.orderOf_mk, hD.orderOf_eq]
    obtain ⟨r, hr, hr3, t, ht, P, hPt, hP⟩ :=
      ResProof.exists_rank_three_centralizer_of_isSLThreePi hnq' hO2 hO hbar hSL' hcZ hc3
    have hcomm : ∀ h ∈ P.map L.subtype, h * (t : G) = (t : G) * h := by
      rintro _ ⟨x, hx, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hPt hx)
      exact congrArg Subtype.val h
    have hloc := Sec4.Census.pRank_le_localRank_of_centralizes hr (by omega)
      (H := P.map L.subtype) (t := (t : G)) (by rw [Subgroup.orderOf_coe]; exact ht) hcomm
    have hrank : CFSG.pRank r (P.map L.subtype) = CFSG.pRank r P :=
      pRank_congr_mulEquiv hr.one_lt (P.equivMapOfInjective _ L.subtype_injective).symm
    have hlt := hD.localRank_lt r hr hr3
    omega

end CFSG.RankThree.PartTwo.Sec13
