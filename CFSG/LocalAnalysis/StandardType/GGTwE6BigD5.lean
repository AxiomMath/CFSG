module

public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Class
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.SCFourCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

private theorem ggTwE6BigD5_ringChar_eq_two_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) : ringChar K = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  exact ringChar.eq K 2

private theorem ggTwE6BigD5_eq_twD_of_dict {lab : LargeEvenLabel}
    (ht : markTag lab = .POmegaMinus) (hr : markRank lab = 5) (hd : markDeg lab = 1) :
    lab = ⟨.twD, 5, 1⟩ := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [markTag, markRank, markDeg] at ht hr hd
  case twD =>
    by_cases hl2 : l = 2
    · rw [if_pos hl2] at ht
      exact absurd ht (by decide)
    by_cases hl3 : l = 3
    · rw [if_neg hl2, if_pos hl3] at ht
      exact absurd ht (by decide)
    · rw [if_neg hl2, if_neg hl3] at hr
      rw [if_neg hl2] at hd
      subst hr
      subst hd
      rfl
  all_goals ((try split_ifs at ht) <;> exact absurd ht (by decide))

theorem ggTwE6BigD5_holds :
    GGTwE6BigD5 := by
  intro K _ _ σ hK hσ h hh1 hh3 hdim J hJ
  have hchar : ringChar K = 2 := ggTwE6BigD5_ringChar_eq_two_of_card_four hK
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have he : D.e = 1 := by
    have h1 := D.hqe
    rw [hchar] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans (pow_one 2).symm)
  have hq2 : D.S.D.q = 2 := D.hSq.trans D.hqe.symm
  have h3q : 3 ∣ D.S.D.q + 1 := by norm_num [hq2]
  have hk : (kernelRoots (rootCharHom D.a)).ncard = 40 := by
    have := D.hker
    omega
  obtain ⟨i, hqs, hJi⟩ := D.exists_rationalComponent hJ
  obtain ⟨t, ht, Fr, hFr, hΦ0⟩ := D.hS
  obtain rfl : t = .E6 := by
    cases t
    · rfl
    · exact absurd ht (by decide)
  have hΦ : D.S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr :=
    MonoidHom.ext fun g => (hΦ0 g).trans rfl
  obtain ⟨r, e, hr, hqr, hmodel⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.d5_class_strongModel
      D.S hFr hΦ D.hL3 D.hT D.hap h3q hk i
  haveI := D.hchar
  obtain rfl : r = 2 := by
    rw [← hr, ringChar.eq (AlgebraicClosure K) (ringChar K), hchar]
  obtain rfl : e = 1 :=
    Nat.pow_right_injective (le_refl 2) (hqr.symm.trans (hq2.trans (pow_one 2).symm))
  have hmark := largeEvenMarking_of_lieModel_centerQuot hqs.1.commutator_eq_top hmodel.1
  have hmark' : LargeEvenMarking
      ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)
      (fun lab' _ _ _ _ _ => lab' = ⟨.twD, 5, 1⟩) :=
    largeEvenMarking_mono
      (fun lab _ _ _ _ _ hdict => ggTwE6BigD5_eq_twD_of_dict hdict.1 hdict.2.1 hdict.2.2.2)
      hmark
  let eJ := (J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi)
  exact largeEvenMarking_of_mulEquiv eJ hmark'

end CFSG.StandardType

end
