module

public import CFSG.RankThree.PartTwo.Sec8.Hering88CEng
public import CFSG.RankThree.PartTwo.Sec8.Hering88CL2
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels
import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88C

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem outThreeCyclic_of_projSp {Q : Type} [Group Q] {f : ℕ}
    (e : Q ≃* projSp 2 (GaloisField 2 f)) : KFacts.OutThreeCyclic Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f with hFdef
  exact (KFacts.outThreeCyclic_psp4Even F).of_mulEquiv
    (e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm)

theorem false_of_projSL_le_projSp {X : Type} [Group X] [Finite X] {Kb C : Subgroup X} {n : ℕ}
    (hn1 : 1 ≤ n) (hle : Kb ≤ C) (eK : Kb ≃* projSL 2 (GaloisField 2 (3 * n)))
    (eC : C ≃* projSp 2 (GaloisField 2 n)) : False := by
  have hdvd : Nat.card Kb ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  by_cases h2 : n = 2
  · subst h2
    rw [Nat.card_congr eK.toEquiv, Nat.card_congr eC.toEquiv,
      Sec21.card_projSL_two (3 * 2) (by norm_num),
      Sec19.Step1911Proof.card_projSp_two (by norm_num)] at hdvd
    norm_num at hdvd
  · refine Item86ResProof.false_of_profile_dvd (Item86ResProof.profile_projSL_two (by omega) eK)
      (Item86ResProof.profile_of_projSp_two hn1 eC) hdvd (by omega) (by omega)
      (Item86ResProof.zA_one_self _) ?_
    rw [Timmesfeld.Orders.zBC_two_iff]
    intro h
    have h' : 3 * n ∣ n * 4 - 3 * n := Nat.dvd_sub h dvd_rfl
    exact Item86ResProof.false_of_dvd_of_lt h' (by omega) (by omega)

theorem inducesOuterTheta_of_sp4 {G : Type} [Group G] [Finite G] {Y : Subgroup G} {x d : G}
    {m : ℕ} (hm1 : 1 ≤ m)
    (hkind : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField)
    (hx3 : x ^ 3 = 1) (hdx : d * x = x * d)
    (eY : Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 2 (GaloisField 2 (3 * m)))
    (eK : imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
      projSL 2 (GaloisField 2 (3 * m))) :
    Sec4.InducesOuterTheta x
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) := by
  have hout : Sec4.InducesOuterTheta x Y := by
    rcases hkind with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h (by decide)
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) := hout.choose
  by_contra hnot
  obtain ⟨k', hk'L, hk'a, hk'3, hle⟩ :=
    Item86ResProof.Item8KFactsOuter.exists_twist_of_not_outer hm1 hxN
      (mem_normalizer_residual_centralizer hxN hdx) hx3 eK hnot
  have hk'N : k' ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hk'L
  have ha'N : x * k'⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hk'N)
  have ha'3 : (x * k'⁻¹) ^ 3 = 1 := by
    have hc : Commute x k'⁻¹ := (Commute.symm hk'a).inv_right
    rw [hc.mul_pow, hx3, inv_pow, hk'3, inv_one, one_mul]
  have hout' := Item86ResProof.Item8KFactsOuter.inducesOuterTheta_mul_inv_of_mem hout hk'L
  obtain ⟨-, ⟨eC⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) ha'3 hout' ⟨eY⟩
  exact false_of_projSL_le_projSp hm1 hle eK eC

theorem kF88StepDCaseFive_of
    (h45 : Sec4.Item4_5) (hC : KF88SwapCent) (hF : KF84Field)
    (hSp : Item8KFacts3.KF84Sp4ThreeCent) : KF88StepDCaseFive := by
  rintro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hY5, hC5, -⟩
  obtain ⟨eY⟩ := hY5
  obtain ⟨eC⟩ := hC5
  obtain ⟨hAc, hA3⟩ := pair_commute_pow_three h
  have hxA : x ∈ A := by
    rcases hx with rfl | rfl
    · exact h.mem_A
    · exact (Item87Proof.isGammaIndex_cases h.isGammaIndex).1
  have hout : Sec4.InducesOuterTheta x Y := by
    rcases hxY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) := hout.choose
  have hm1 : 1 ≤ m := by
    by_contra hm0
    obtain rfl : m = 0 := by omega
    have hcard : Nat.card (barCentralizer (Subgroup.zpowers x) Y) =
        Nat.card (Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Nat.card_congr eC.toEquiv, Nat.card_congr eY.toEquiv]
    have htop := Subgroup.eq_top_of_card_eq _ hcard
    rw [Sec4.barCentralizer_zpowers_eq_autFix hxN] at htop
    refine hout.choose_spec ⟨1, ?_⟩
    ext z
    have hz : z ∈ Sec4.autFix (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨x, hxN⟩)) :=
      htop ▸ Subgroup.mem_top z
    rw [MulAut.conj_apply]
    simp only [map_one, inv_one, one_mul, mul_one]
    exact (Sec4.mem_autFix.mp hz).symm
  obtain ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne⟩ := exists_inner_d h45 hC hF h hY hIJ hx hxY
    (outThreeCyclic_of_projSp eY)
  have hck : ¬ (KFacts.InducesStdKind Y d .field ∨ KFacts.InducesStdKind Y d .graphField) := by
    rintro (h' | h')
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).choose_spec hin
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).choose_spec hin
  obtain ⟨eK⟩ := Item8KFacts3.sp4_residual hSp hdN hd3 hck hne (f := 3 * m) (by omega) eY
  exact ⟨d, hdcl, hdx, good88_of_outer hm1 (hA3 x hxA)
    (inducesOuterTheta_of_sp4 hm1 hxY (hA3 x hxA) (hAc d hdA x hxA) eY eK) eK⟩

end Hering88C

end CFSG.RankThree.PartTwo.Sec8
