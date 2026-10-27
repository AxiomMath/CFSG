module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoroot
public import CFSG.Assembly.LargeEvenDefs
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCBExponentFourLayer
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotBLiftYBasic
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot
import CFSG.LieType.Steinberg.Adjoint.Pairs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRouteBBasic
import CFSG.RankThree.PartOne.KE.E8FourA1Family
import CFSG.RankThree.PartOne.KF4.EvenDescent

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TwE6RootKill


theorem exists_endNode_of_datum (hRK : RootKill) (hCore : TwE6CorootCore) {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (h2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ q + 1)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ)
    (hA : IsElemAbelian p A) (hr : p ^ (if p = 3 then 4 else 5) ≤ Nat.card A)
    (hU : TwNormTwo K σ A) (D : TwLangData K σ q A) (hc : D.c = 1)
    (hv : ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ) :
    ∃ t : twistedE6RootGroup K σ, (t : ModGL TwistTag.E6.tag K) ∈ A ∧ t ≠ 1 ∧
      ∃ L : Subgroup (twistedE6RootGroup K σ),
        LargeEvenLayer (Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ))) = L ∧
        IsComponentOf L (Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ))) ∧
        7 ∣ Nat.card L ∧
        (∀ s ∈ A, (∀ d ∈ L, s * (d : ModGL TwistTag.E6.tag K) = d * s) →
          s ∈ Subgroup.zpowers (t : ModGL TwistTag.E6.tag K)) ∧
        ∃ u ∈ L, u ≠ 1 ∧ (∃ m : ℕ, u ^ 2 ^ m = 1) ∧
          ∀ s ∈ A, Commute (u : ModGL TwistTag.E6.tag K) s := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (two_dvd_of_card hK h2)).mp hpq
    omega
  have hpK : ringChar K ≠ p := fun h => hp2 (h.symm.trans h2)
  obtain ⟨β, hβ, hkill⟩ := hRK K σ q hK hσ h2 p hp hpq A hAI hA hr hU D
  have hA0 : 0 < Nat.card A := lt_of_lt_of_le (pow_pos hp.pos _) hr
  have hcard : p ^ 5 < 6 * Nat.card A := by
    split_ifs at hr with h3
    · subst h3
      norm_num at hr ⊢
      omega
    · calc p ^ 5 ≤ Nat.card A := hr
        _ < 6 * Nat.card A := by omega
  obtain ⟨γ, hγ, -, ζ, hζp, hζ1, x, hxA, hx⟩ :=
    exists_corootTuple_mem_of_kills D hp hpK hA hcard hβ hkill
  rw [hc, one_mul, inv_one, mul_one] at hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one, inv_mul_cancel] at hx
    have hco := CFSG.LieType.Chevalley.rootDiagUnit_injective
      (hx.trans CFSG.LieType.Chevalley.rootDiagUnit_one.symm)
    obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hγ
    have hγγ : iform γ γ = 2 := by
      rw [hj, show TwistTag.E6.tag.symmetrizer = 1 from rfl, Matrix.one_apply_eq, mul_one]
    have h3 := rootChar_corootTuple γ γ ζ
    rw [hco, hγγ] at h3
    have h4 : rootChar (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) γ = 1 := by
      simp [rootChar]
    have hz2 : ζ ^ 2 = 1 := by
      rw [pow_two, ← zpow_two, ← h3, h4]
    have hdvd := orderOf_dvd_of_pow_eq_one hz2
    rw [orderOf_eq_prime hζp hζ1] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  obtain ⟨X, L, hXL, hXc, hXodd, hXcen, hLq, -, h7, -, hmem⟩ := hCore K σ q hK hσ h2 p hp hpq
    D.Fr D.hFr D.v hv D.g0 D.hg0C D.hg0 x (hAI hxA) γ hγ ζ hζp hζ1 hx.symm
  have hxL : ∀ d ∈ L, x * (d : ModGL TwistTag.E6.tag K) = d * x := by
    intro d hd
    have hd' : d ∈ (Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ) := by
      rw [hXL]
      exact (le_sup_right : L ≤ X ⊔ L) hd
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hd'
    exact hd'.symm
  obtain ⟨t, htX, htx⟩ := Subgroup.mem_map.1 (hmem x (hAI hxA) rfl hxL)
  have htx' : (t : ModGL TwistTag.E6.tag K) = x := htx
  subst htx'
  have ht1 : t ≠ 1 := fun h => hx1 (by simp [h])
  have htp : t ^ p = 1 := Subtype.ext (by simpa using hA.2 _ hxA)
  have hC : Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ)) = X ⊔ L := by
    rw [← hXL]
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨hlay, hcomp⟩ := TwE6D3.layer_sup_eq hXc hXcen
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hLq)
  rw [hlay] at hcomp
  have hcent : ∀ s ∈ A, (∀ d ∈ L, s * (d : ModGL TwistTag.E6.tag K) = d * s) →
      s ∈ Subgroup.zpowers (t : ModGL TwistTag.E6.tag K) := by
    intro s hs hsL
    obtain ⟨y, hyX, rfl⟩ := Subgroup.mem_map.1 (hmem s (hAI hs) (hA.comm hs hxA) hsL)
    haveI : Finite X := Nat.finite_of_card_ne_zero hXodd.pos.ne'
    have hy : y ∈ Subgroup.zpowers t :=
      CFSG.LocalAnalysis.GorensteinLyons.mem_of_pow_eq_one_of_isCyclic hXc
        (Subgroup.zpowers_le.2 htX) hp.pos
        (by rw [Nat.card_zpowers]; exact orderOf_eq_prime htp ht1) hyX
        (Subtype.ext (by simpa using hA.2 _ hs))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simp⟩
  obtain ⟨u, huC, hu1, ⟨m, hum⟩, hucomm⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K σ q (by rw [h2]; norm_num)
      hσ hK A D β hβ hkill
  rw [h2] at hum
  have huX : (⟨u, huC⟩ : twistedE6RootGroup K σ) ∈ X ⊔ L := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hucomm _ hxA).eq
  have huL : (⟨u, huC⟩ : twistedE6RootGroup K σ) ∈ L :=
    CFSG.SeitzReduction.TwistedE6Pilot.mem_of_mem_sup_of_odd_of_pow_two_pow hXcen hXodd huX
      (Subtype.ext (by simpa using hum))
  refine ⟨t, hxA, ht1, L, by rw [hC, hlay], by rw [hC]; exact hcomp, h7, hcent, ⟨u, huC⟩, huL,
    fun h => hu1 (congrArg Subtype.val h), ⟨m, Subtype.ext (by simpa using hum)⟩, hucomm⟩

end CFSG.StandardType.TwE6RootAs

end
