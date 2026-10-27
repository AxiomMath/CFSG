module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NBeta
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSwapRest
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.LieType.Ree

theorem card_inSubgroup_perfectResidual_of_isoPGUThree {Q : Type} [Group Q] [Finite Q]
    {R : Subgroup Q} {m : ℕ} (hm : 2 ≤ m) (h : IsoPGUThree R (2 ^ m)) :
    Nat.card (inSubgroup perfectResidual R) = CFSG.Open.ordTwistedA 2 (2 ^ m) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hPi : Sec4.PiField false 2 m K := ⟨Nat.prime_two, by omega, hK⟩
  have hq2 : 2 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hU := hPi.unitary
  have hSP : CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi false 3 (2 ^ m) K) ≤
      CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi false 3 (2 ^ m) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hU))
  have e1 : inSubgroup perfectResidual R ≃*
      CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi false 3 (2 ^ m) K) :=
    ((perfectResidual R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
      ((Item8KFacts2Proof.perfectResidualEquivOfMulEquiv e).trans
        ((MulEquiv.subgroupCongr
          (Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hPi hq2)).trans
          (Subgroup.subgroupOfEquivOfLe hSP)))
  have e2 := CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
    (Sec4.slPi false 3 (2 ^ m) K)
  rw [Nat.card_congr e1.toEquiv]
  show Nat.card ↥(Subgroup.map Matrix.ProjGenLinGroup.mk (Sec4.slPi false 3 (2 ^ m) K)) = _
  rw [← Nat.card_congr e2.toEquiv]
  rw [show Sec4.slPi false 3 (2 ^ m) K = CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K from rfl,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by omega) hK
      (by norm_num), CFSG.Open.ordTwistedA]


theorem even_two_part_of_isGammaIndex {G : Type} [Group G] [Finite G] {A M : Subgroup G}
    {a v : G} {n : ℕ} (hn2 : 2 ≤ n) (hv : IsGammaIndex A M v n)
    (hUn : ∀ g : ℕ, ¬ IsUnitaryTwo (M ⧸ aschbacherSolvableCore 3 M) g) (ha3 : a ^ 3 = 1)
    (hk : KFacts.InducesStdKind M a .field ∨ KFacts.InducesStdKind M a .graphField)
    (hg2 : Sec8PairGTwo M a n) :
    ∃ N r : ℕ, Even N ∧ Odd r ∧
      Nat.card (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual
          (M ⊓ Subgroup.centralizer ({a} : Set G)))) = 2 ^ N * r := by
  classical
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases hv
  have haN : a ∈ Subgroup.normalizer (M : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have haout : Sec4.InducesOuterTheta a M := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
  have hWM : inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ≤ M :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hW_img : imageModTheta M (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G))) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  set C := barCentralizer (Subgroup.zpowers a) M with hCdef
  have key : Group.IsPerfect C → IsSimpleGroup C →
      Nat.card (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual
          (M ⊓ Subgroup.centralizer ({a} : Set G)))) = Nat.card C := fun hP hS => by
    have hCres : inSubgroup perfectResidual C = C := inSubgroup_perfectResidual_of_isPerfect (R := C) hP
    have hS' : IsSimpleGroup (inSubgroup perfectResidual C) := by
      rw [hCres]
      exact hS
    rw [card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS', hCres]
  rcases hcases with ⟨hRee, -⟩ | ⟨htype, -⟩
  ·
    obtain ⟨k₀, hk₀, hkp, ⟨e₀⟩⟩ := hRee
    have hRT : CFSG.Blueprint.ReeTitsModel (M ⧸ aschbacherSolvableCore 3 M) .twistedF4 2
        (2 * k₀ + 1) :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
    obtain ⟨-, a', ha'1, hka, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
    obtain ⟨b', k', _, _, _, hk', hb', ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 haout
    have hn : n = 2 * b' + 1 := by omega
    have hb1 : 1 ≤ b' := by omega
    have hperfF : Group.IsPerfect (ReeTag.F4.reeGamma k' b') :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb1 hk'⟩
    haveI hsimpF : IsSimpleGroup (ReeTag.F4.reeGamma k' b') :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb1 hk'
    have hCperf : Group.IsPerfect C :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    rw [key hCperf φ.isSimpleGroup, Nat.card_congr φ.toEquiv,
      Item86ResProof.card_of_mulEquiv_reeGamma b' k' hk' (MulEquiv.refl _)]
    obtain ⟨s, hs, hseq⟩ :=
      (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (f := 2 * b' + 1) (by omega)).two
    exact ⟨_, s, ⟨(2 * b' + 1) * 6, by ring⟩, hs, hseq⟩
  · rcases htype with hD | ⟨q, hq2, hqe, hGq⟩ | hU | hSU | hSp
    ·
      have hG2C : IsoGTwoEven C n := hg2 (Or.inl hD)
      have hP : Group.IsPerfect C := by
        have := Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven hn2 hG2C
        rw [← this]
        exact Item87Proof.isPerfect_residual C
      have hS : IsSimpleGroup C := by
        have h1 := Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hn2 hG2C
        rwa [Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven hn2 hG2C] at h1
      obtain ⟨K, _, _, hK, ⟨eG⟩⟩ := hG2C
      rw [key hP hS, Nat.card_congr eG.toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      obtain ⟨s, hs, hseq⟩ := (CFSG.Timmesfeld.Orders.profile_ordG2 (f := n) (by omega)).two
      exact ⟨_, s, ⟨n * 3, by ring⟩, hs, hseq⟩
    ·
      have hG2C : IsoGTwoEven C n :=
        hg2 (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq))
      have hP : Group.IsPerfect C := by
        have := Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven hn2 hG2C
        rw [← this]
        exact Item87Proof.isPerfect_residual C
      have hS : IsSimpleGroup C := by
        have h1 := Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hn2 hG2C
        rwa [Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven hn2 hG2C] at h1
      obtain ⟨K, _, _, hK, ⟨eG⟩⟩ := hG2C
      rw [key hP hS, Nat.card_congr eG.toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      obtain ⟨s, hs, hseq⟩ := (CFSG.Timmesfeld.Orders.profile_ordG2 (f := n) (by omega)).two
      exact ⟨_, s, ⟨n * 3, by ring⟩, hs, hseq⟩
    · exact (hUn (3 * n) (Or.inl hU)).elim
    · exact (hUn (3 * n) (Or.inr hSU)).elim
    ·
      obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) ha3 haout hSp
      have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
      have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      set ψ : C ≃* CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 n)) :=
        ι.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm with hψ
      have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
        (GaloisField 2 n) 2 (by norm_num) (Or.inl (Or.inr h4))
      have h4' : ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
        have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
          Finset (GaloisField 2 n))) (n := 4) (by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
            exact h4)
        exact ⟨s, hs⟩
      have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
        (GaloisField 2 n) (Or.inl h4')
      have hpC : Group.IsPerfect C := hp.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
      rw [key hpC ψ.isSimpleGroup, Nat.card_congr ι.toEquiv,
        Sec19.Step1911Proof.card_projSp_two (by omega)]
      refine ⟨n * 4, ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1), ⟨n * 2, by ring⟩, ?_, rfl⟩
      exact (Item87Proof.odd_two_pow_sq_sub_one (by omega)).mul
        (by
          have h := Item87Proof.odd_two_pow_sq_sub_one (f := 2 * n) (by omega)
          rwa [← pow_mul, show 2 * n * 2 = n * 4 by ring, pow_mul] at h)

theorem false_of_swap_pgu (h84 : Pair84A)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hcX : IsGammaIndex A X c n)
    (hn2 : 2 ≤ n)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hbN : b ∈ Subgroup.normalizer (Y : Set G)) {m : ℕ} (hodd : Odd m) (hm2 : 2 ≤ m)
    (hP : IsoPGUThree (barCentralizer (Subgroup.zpowers b) Y) (2 ^ m)) : False := by
  have ha3 : a ^ 3 = 1 := (Hering88C.pair_commute_pow_three h).2 a h.a_mem
  have hJ := Item812Res6.sec8J_ne_bot_of_gTwoPartner kF87INontriv_holds h84 h
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
  have hM1 := Hering88E.imageModTheta_sec8J_eq_perfectResidual kF87Cent_holds h84 h hJ hY hJY
    hbN hS
  have hNY := card_quot_theta_eq_of_isSimpleGroup hJY hM1 hS
  rw [card_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP] at hNY
  obtain ⟨N, r, hN, hr, hNr⟩ := even_two_part_of_isGammaIndex hn2 hcX
    h.not_unitary ha3 (h84 G A c L a b X n h) (h.gTwoPartner n)
  exact KFacts.ne_ordTwistedA_two hr hN hodd (hNr.symm.trans hNY)

theorem kF88Case1ClassBSwapRest_of (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4)
    (h84 : Pair84A) (hPG : PartnerGamma88) : KF88Case1ClassBSwapRest := by
  intro G _ _ A c L a b X n h Y hY hIJ x hxb hxc hxY A₀ d' m hodd hc1 hcov d hdcl hdx hdA hd3
    hdN hin hne _
  subst hxb
  obtain ⟨-, -, hn1, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  rcases Nat.lt_or_ge n 2 with hn | hn2
  · obtain rfl : n = 1 := by omega
    exact classBSwapOne h45 h47 h84 hPG h hY hIJ hxY hodd hc1 hdcl hdx hdA hd3 hdN hin hne
  · exfalso
    have hbN : x ∈ Subgroup.normalizer (Y : Set G) :=
      hxY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
    rcases hc1.2.2 with hG2 | ⟨-, hP, -⟩
    · exact hcov ⟨rfl, hn2, Or.inl hG2⟩
    · rcases Nat.lt_or_ge m 2 with hm | hm2
      · have hm1 : m = 1 := by have := hodd.pos; omega
        exact hcov ⟨rfl, hn2, Or.inr ⟨hm1, hP⟩⟩
      · exact false_of_swap_pgu h84 h (hPG _ _ _ _ _ _ _ _ h _ hY hIJ _ _ _ _ hodd hc1) hn2 hY hIJ
          hbN hodd hm2 hP

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
