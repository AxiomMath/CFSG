module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Odd361
import CFSG.RankThree.PartTwo.Sec11.SimsR1L38TwoStar
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddLF

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.OddTwoStar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

section Tools

variable {G : Type} [Group G] [Finite G]

private theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  by_contra hlt
  have : p = 4 := by omega
  subst this
  exact absurd hp (by norm_num)

private theorem closure_pair_eq_sup (c d : G) :
    Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

private theorem centralizer_le_normalizer_thetaCent (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (thetaCent c : Set G) :=
  fun _ hk => Subgroup.mem_normalizer_fintype fun _ hn => k4_thetaCent_conj hk hn

theorem pCore_inf_thetaCent_eq_bot {c d : G} {L : Subgroup G}
    (hP0 : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G)) = ⊥) (hdL : d ∈ L)
    (hcent : ⁅L, thetaCent c⁆ = ⊥) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G)) ⊓ thetaCent c = ⊥ := by
  have hθC : thetaCent c ≤ Subgroup.centralizer ({c} : Set G) := Subgroup.map_subtype_le _
  have hθd : thetaCent c ≤ Subgroup.centralizer ({d} : Set G) := by
    intro v hv
    have h1 : ⁅d, v⁆ ∈ ⁅L, thetaCent c⁆ := Subgroup.commutator_mem_commutator hdL hv
    rw [hcent, Subgroup.mem_bot] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have h1 : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({d} : Set G)) ⊓ thetaCent c ≤
      inSubgroup (CFSG.pCore 2) (thetaCent c) := by
    rw [inf_comm]
    exact SteinbergBY.inf_inSubgroup_pCore_le (le_inf hθC hθd)
  have h2 : inSubgroup (CFSG.pCore 2) (thetaCent c) ≤
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G)) :=
    SteinbergBY.inSubgroup_pCore_mono hθC (centralizer_le_normalizer_thetaCent c)
  exact le_bot_iff.mp (h1.trans (h2.trans hP0.le))

end Tools

section Residue


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem pCore_eq_bot_of_not_mem_closure (hB : KFacts.BlackburnRankTwo)
    (hDk : SimsR1L2CubeTwoLocal) (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) (hodd : IsL2OddCharOne L) {y : G} (hyA : y ∈ A)
    (hyB : y ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) = ⊥ := by
  have hLC := TwoStarProof.le_centralizer_of_config h
  refine SimsR1.eq_bot_of_twoSubgroup_normalized_odd hB hDk h45 h hT hodd
    (SteinbergBY.isPGroup_inSubgroup_pCore 2 _)
    ((SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left) hyA
    (by rwa [closure_pair_eq_sup]) ?_
  intro k hk
  have hk' := k4_sec11K_le L y hk
  exact SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ ⟨hLC hk'.1, hk'.2⟩

theorem isCyclic_pCore_d (hC3 : SimsR1L2CubeCentThree) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hodd : IsL2OddCharOne L)
    (hQθ : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G)) ⊓ thetaCent c = ⊥) :
    IsCyclic ↥(inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({d} : Set G))) := by
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  have hp5 := five_le_of_prime hp.out hp3
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set N := Subgroup.normalizer (L : Set G) with hN
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({d} : Set G)) with hP
  set ψ := TwoStarProof.autHom L with hψ
  have hCL : C ≤ N := TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hdL := TwoStarProof.d_mem_L h
  have hd3 : d ^ 3 = 1 := h.mem_partTwoF.1.2 d h.d_mem
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({d} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  have hPN : P ≤ N := (hPC.trans inf_le_left).trans hCL
  have hx3 : ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ^ 3 = 1 := by
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hx1 : ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ≠ 1 := by
    intro h1
    have h2 : (⟨d, hdL⟩ : L) ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp h1
    have hd1 : d = 1 := eq_one_of_mem_inSubgroup_theta ⟨_, h2, rfl⟩ hd3
    exact h.not_mem_zpowers (hd1 ▸ Subgroup.one_mem _)
  have hord : orderOf ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 3 :=
    orderOf_eq_prime hx3 hx1
  let f : ↥P →* MulAut (L ⧸ aschbacherSolvableCore 3 L) := ψ.comp (Subgroup.inclusion hPN)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hqK : (q : G) ∈ Sec4.thetaQuotCentralizer L :=
      L38TwoStar.mem_thetaQuotCentralizer_of_autHom_eq_one (hPN q.2) hq
    have hqθ := L38TwoStar.pCore_d_inf_thetaQuotCentralizer_le h45 h hT ⟨q.2, hqK⟩
    have hq1 : (q : G) ∈ P ⊓ thetaCent c := ⟨q.2, hqθ⟩
    rw [hQθ, Subgroup.mem_bot] at hq1
    exact Subtype.ext hq1
  have hrange2 : IsPGroup 2 f.range := hP2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfix : ∀ τ ∈ f.range, τ ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
    rintro _ ⟨q, rfl⟩
    have hqd : (q : G) * d = d * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPC q.2).2
    show Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨(q : G), hPN q.2⟩)
      ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change (q : G) * d * (q : G)⁻¹ = d
    rw [hqd]
    group
  have hcyc : IsCyclic f.range :=
    hC3 p hp5 (L ⧸ aschbacherSolvableCore 3 L) ⟨e⟩ _ hord f.range hrange2 hfix
  exact isCyclic_of_injective f.rangeRestrict (MonoidHom.rangeRestrict_injective_iff.mpr hfinj)

theorem commutator_pCore_d_eq_bot (h : ResidueConfig G A c L a R Y d)
    (hcyc : IsCyclic ↥(inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({d} : Set G)))) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({d} : Set G)), A⁆ = ⊥ := by
  have hAe := h.mem_partTwoF.1
  have hAc := L38TwoStar.comm_of_mem_A h
  rw [← le_bot_iff, Subgroup.commutator_le]
  intro q hq α hα
  have hαN : α ∈ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2)
      (Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) : Subgroup G) :
        Set G) :=
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hAc α hα c h.mem_A),
        Subgroup.mem_centralizer_singleton_iff.mpr (hAc α hα d h.d_mem)⟩
  have hcent := L38TwoStar.mem_centralizer_of_pow_three_of_isCyclic hcyc
    (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) hαN (hAe.2 α hα)
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hcent q hq)

end Residue

end CFSG.RankThree.PartTwo.Sec11.SimsR1.OddTwoStar

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

section Residue


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem twoStarConditionAt_c_odd_of_cent (hB : KFacts.BlackburnRankTwo)
    (hDk : SimsR1L2CubeTwoLocal) (hC3 : SimsR1L2CubeCentThree) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d)
    (hodd : IsL2OddCharOne L)
    (hcent : ⁅L, thetaCent c⁆ = ⊥ ∧ aschbacherSolvableCore 3 L = ⊥) :
    TwoStarConditionAt A c := by
  have _ := hR1
  obtain ⟨hcentL, -⟩ := hcent
  have hAe := h.mem_partTwoF.1
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  have hAc := L38TwoStar.comm_of_mem_A h
  have hdA := h.d_mem
  have hdL := TwoStarProof.d_mem_L h
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 h.mem_A h.ne_one hdA
    h.not_mem_zpowers
  have haV : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro ha
    have hle : A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [← h.closure_eq, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact ha
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcd9] at this
    norm_num at this
  have hP0 := pCore_two_centralizer_c_eq_bot_odd hB h45 h hT hodd
  have hQθ := OddTwoStar.pCore_inf_thetaCent_eq_bot hP0 hdL hcentL
  have hcyc := OddTwoStar.isCyclic_pCore_d hC3 h45 h hT hodd hQθ
  refine Theta.twoStarConditionAt_of_centralizers hAc h.mem_A (hAe.2 c h.mem_A) h.a_mem
    (fun hac => haV (Subgroup.mem_sup_left hac)) ?_ ?_
  ·
    intro y hyA hyc
    by_cases hyB : y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
    · have hplane := TwoStarProof.zpowers_sup_eq_of_mem h.card_eq h.mem_A h.ne_one hdA
        h.not_mem_zpowers hyA hyc hyB
      have hCy : Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) =
          Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
        rw [← CFSG.RankThreeEvenClassification.Helpers.centralizer_join_zpowers,
          ← CFSG.RankThreeEvenClassification.Helpers.centralizer_join_zpowers, hplane]
      rw [hCy, OddTwoStar.commutator_pCore_d_eq_bot h hcyc]
      exact bot_le
    · rw [OddTwoStar.pCore_eq_bot_of_not_mem_closure hB hDk h45 h hT hodd hyA hyB,
        Subgroup.commutator_bot_left]
      exact bot_le
  ·
    intro u hu
    have hua := hu a h.a_mem fun hac => haV (Subgroup.mem_sup_left hac)
    rw [OddTwoStar.pCore_eq_bot_of_not_mem_closure hB hDk h45 h hT hodd h.a_mem haV,
      Subgroup.mem_bot] at hua
    rw [hP0, Subgroup.mem_bot]
    exact hua

theorem twoStarConditionAt_c_odd (hB : KFacts.BlackburnRankTwo) (hDk : SimsR1L2CubeTwoLocal)
    (hFF : SimsR1L2CubeFaithfulFix) (hSF : SimsR1L2CubeSolvableFix)
    (hC3 : SimsR1L2CubeCentThree) (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d) (hodd : IsL2OddCharOne L) :
    TwoStarConditionAt A c :=
  twoStarConditionAt_c_odd_of_cent hB hDk hC3 h45 h hT hR1 hodd
    (commutator_L_thetaCent_c_eq_bot_odd hB hDk hFF hSF h45 h hT hodd)

end Residue

end CFSG.RankThree.PartTwo.Sec11.SimsR1

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

section Certified


theorem residueR1TwoStarCOdd_of (hB : KFacts.BlackburnRankTwo) (hDk : SimsR1L2CubeTwoLocal)
    (hFF : SimsR1L2CubeFaithfulFix) (hSF : SimsR1L2CubeSolvableFix)
    (hC3 : SimsR1L2CubeCentThree) (h45 : Sec4.Item4_5) : ResidueR1TwoStarCOdd := by
  intro G _ _ A c L a R Y d h hT hR1 hodd
  exact SimsR1.twoStarConditionAt_c_odd hB hDk hFF hSF hC3 h45 h hT hR1 hodd

end Certified

end CFSG.RankThree.PartTwo.Sec11
