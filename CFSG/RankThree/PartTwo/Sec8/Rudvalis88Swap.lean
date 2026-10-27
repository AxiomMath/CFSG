module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NBeta
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSwap
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeField
public import CFSG.RankThree.PartTwo.Sec8.Hering88FReeAbs
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSwapRest

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Hering88F



theorem pairRel_symm_of_mem_gammaSet {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hc : c ∈ gammaSet A X) : PairRel A b X c L := by
  obtain ⟨m', hem'⟩ := hc
  obtain ⟨hΩe, ⟨m, hbm⟩, hX, hKX, -⟩ := h.pairRel
  have hLe : L ∈ thetaComponentsAt 3 c := hΩe.2.2.1
  have hLeC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp hLe).1
  obtain ⟨hKe, -, hKe1⟩ := Item87Proof.residual_of_isGammaIndex hLe hbm
  obtain ⟨hKb, -, -⟩ := Item87Proof.residual_of_isGammaIndex hX hem'
  set Ke := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKedef
  set Kb := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hKbdef
  have hKeLe : Ke ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKeKb : Ke ≤ Kb :=
    KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
      (le_inf hKX (hKeLe.trans hLeC))
  have hKb' : Kb ∈ thetaComponentsIn (Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b}) := by
    rwa [inf_comm] at hKb
  have heq : Ke = Kb := Sec6.eq_of_mem_thetaComponentsIn_of_le hKe hKb'
    (Item87Proof.isPerfect_residual _) hKe1 le_rfl hKeKb
  refine ⟨h.mem_pairOmega, ⟨m', hem'⟩, hLe, ?_, ?_⟩
  · show Kb ≤ L
    rw [← heq]
    exact hKeLe
  · show L ≠ Kb ⊔ inSubgroup (aschbacherSolvableCore 3) L
    rw [← heq]
    intro hsup
    have htop := Item87Proof.imageModTheta_eq_top_of_eq_sup hKeLe hsup
    let ι : L ⧸ aschbacherSolvableCore 3 L ≃* imageModTheta L Ke :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    obtain ⟨-, -, hm, hcases⟩ := Item87Proof.isGammaIndex_cases hbm
    rcases hcases with ⟨hRee, F, hF, hFf, hFc, ⟨φ⟩⟩ | ⟨hL2, ⟨φ⟩⟩
    · exact (kF84Proper _ m hm).1 hRee ⟨F, hF, hFf, hFc, ⟨ι.trans φ⟩⟩
    · exact (kF84Proper _ m hm).2 hL2 ⟨ι.trans φ⟩

theorem classB_swap_L2_of_rel (h45 : Sec4.Item4_5) (hF : KF84Field) (h84 : Pair84A)
    (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    (hrel' : PairRel A b X c L) (hn2 : 2 ≤ n)
    (hKL2 : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hbY : KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField)
    {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m) (hm2 : 2 ≤ m)
    (hc1 : Case83One Y b A₀ d' m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers b) Y) m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdb : d ∉ Subgroup.zpowers b)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hAel := h.mem_partTwoF.1
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) :=
    hbY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hbout : Sec4.InducesOuterTheta b Y := by
    rcases hbY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  have hbd : b * d = d * b := hAc b hbA d hdA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hAp
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu b hbA)) X hX
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X :=
    h.pairRel.2.2.2.1
  have hLX : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) ≤ L :=
    hrel'.2.2.2.1
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨T₀, hT₀p, hT₀, hT₀le, hT₀d⟩ := exists_T₀ hF h hn2 hdcl
  have hda : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc d hdA a h.a_mem)
  have hdJ : d ∈ Subgroup.normalizer (sec8J X a : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAX hdA, Subgroup.le_normalizer hda⟩)
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hT₀J : T₀ ≤ sec8J X a :=
    KFacts.le_inSubgroup_perfectResidual hT₀p
      (le_inf (hT₀le.trans (inf_le_left.trans hKX)) (hT₀le.trans inf_le_right))
  have hJ : sec8J X a ≠ ⊥ := fun hbot => hT₀ (le_bot_iff.mp (hbot ▸ hT₀J))
  have hM1 := Hering88E.imageModTheta_sec8J_eq_perfectResidual_of_isoGTwoEven kF87Cent_holds h84 h
    hJ hY hJY hbN hm2 hG2
  rw [inSubgroup_perfectResidual_eq_of_isoGTwoEven hm2 hG2] at hM1
  have hCdb : Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {b} ≤
      Subgroup.centralizer {b} ⊓ Subgroup.centralizer {c} := by
    refine Item87Proof.inf_centralizer_le_of_mem_closure hAel hbA h.mem_A ?_ hb1 hdb
    rwa [Set.pair_comm]
  set T := inSubgroup perfectResidual (sec8J X a ⊓ Subgroup.centralizer ({d} : Set G)) with hT
  have hTI : T ≤ sec8J X a ⊓ Subgroup.centralizer ({d} : Set G) := Item87Proof.residual_le _
  have hTX : T ≤ X := hTI.trans (inf_le_left.trans hJX)
  have hTb : T ≤ Subgroup.centralizer ({b} : Set G) := hTX.trans hXb
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := fun w hw =>
    (hCdb ⟨hTI.trans inf_le_right hw, hTb hw⟩).2
  have hTL : T ≤ L := (KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
    (le_inf hTX hTc)).trans hLX
  have hTK : T ≤ K := KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
    (le_inf hTL hTb)
  obtain ⟨e⟩ := hKL2
  have hTcomm : ∀ P : Subgroup G, P ≤ T → IsPGroup 3 P → ∀ u ∈ P, ∀ v ∈ P, u * v = v * u :=
    fun P hPT hP => commute_of_isPGroup_of_imageModTheta hKL (by omega) e (hPT.trans hTK) hP
  exact classB_core_abs hdN hd3 hJY hdJ hM1 hTcomm
    (classBDichotomy_of_case1 h47 hbN hdN hbd hb3 hd3 hbout hin hne hm2 hodd hc1 hG2)


theorem partner_isGammaTypeRee_of_rel {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) (hrel' : PairRel A b X c L) (hn2 : 2 ≤ n)
    (hSU : IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G)))) (2 ^ (3 * n))) :
    IsGammaTypeRee (X ⧸ aschbacherSolvableCore 3 X) n := by
  have hLX : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) ≤ L :=
    hrel'.2.2.2.1
  obtain ⟨n', hn'⟩ := hrel'.2.1
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X :=
    h.pairRel.2.2.2.1
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKeq : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) = K := by
    refine le_antisymm ?_ ?_
    · exact KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
        (le_inf hLX ((Item87Proof.residual_le _).trans (inf_le_left.trans hXb)))
    · exact KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
        (le_inf hKX (hKL.trans hLc))
  obtain ⟨-, -, hn1', hcases⟩ := Item87Proof.isGammaIndex_cases hn'
  rw [hKeq] at hcases
  obtain ⟨F, _, _, hF, ⟨ε⟩⟩ := hSU
  have hθL : NoThetaNormal ↥(imageModTheta L K) :=
    Item87Proof.NoThetaNormal.of_mulEquiv ε (Item87Proof.noThetaNormal_statedSU hF (by omega))
  obtain ⟨χL, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hKL hθL
  rcases hcases with ⟨hReeX, F', _, _, hF', ⟨ε'⟩⟩ | ⟨hL2X, ⟨ψ⟩⟩
  ·
    have hθX : NoThetaNormal ↥(imageModTheta X K) :=
      Item87Proof.NoThetaNormal.of_mulEquiv ε'
        (Item87Proof.noThetaNormal_statedSU hF' (by omega))
    obtain ⟨χX, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta (hKX) hθX
    have hcard : Nat.card ↥(imageModTheta X K) = Nat.card ↥(imageModTheta L K) :=
      Nat.card_congr (χX.symm.trans χL).toEquiv
    have hU1 := Item86ResProof.unitarySig_of_isoSUThree (X := ↥(imageModTheta L K)) (g := 3 * n)
      (by omega) ⟨F, inferInstance, inferInstance, hF, ⟨ε⟩⟩
    have hU2 := Item86ResProof.unitarySig_of_isoSUThree (X := ↥(imageModTheta X K)) (g := 3 * n')
      (by omega) ⟨F', inferInstance, inferInstance, hF', ⟨ε'⟩⟩
    have := Item86ResProof.two_eq hU2.profile (Item86ResProof.profile_of_eq hU1.profile hcard)
    have hnn : n' = n := by omega
    rwa [hnn] at hReeX
  ·
    exfalso
    have hcard : Nat.card ↥(imageModTheta L K) = Nat.card (projSL 2 (GaloisField 2 (3 * n'))) := by
      have hθX : NoThetaNormal ↥(imageModTheta X K) :=
        Item87Proof.NoThetaNormal.of_mulEquiv ψ
          (Item87Proof.noThetaNormal_projSL_two (by omega))
      obtain ⟨χX, -⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hKX hθX
      exact Nat.card_congr ((χL.symm.trans χX).trans ψ).toEquiv
    exact not_card_eq_projSL_statedSU (n := n) (n' := n') (by omega) hn1' hF
      (by rw [← hcard, Nat.card_congr ε.toEquiv])


theorem classB_swap_covered_of_partner (h45 : Sec4.Item4_5) (hF : KF84Field) (h84 : Pair84A)
    (hPG : PartnerGamma88) (hG2Two : G2TwoCentThreeSolvable)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hbY : KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField)
    {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m) (hc1 : Case83One Y b A₀ d' m)
    (hcov : ClassBCovered b c b L Y n m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdb : d ∉ Subgroup.zpowers b)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  have hrel : PairRel A b X c L :=
    pairRel_symm_of_mem_gammaSet h ⟨n, hPG G A c L a b X n h Y hY hIJ b A₀ d' m hodd hc1⟩
  obtain ⟨-, hn2, hclause⟩ := hcov
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) :=
    hbY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hZ := center_eq_bot_of_case1 hc1.1
  rcases hclause with hG2 | ⟨hm1, hP⟩
  · rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by have := hodd.pos; omega
      exact (false_of_small_swap h45 hF hG2Two h hn2 hIJ hbN hZ (Or.inl hG2) hdcl hdA hd3 hdN hin
        hne).elim
    · obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
      rcases hcases with ⟨-, hSU⟩ | ⟨-, hKL2⟩
      · exfalso
        have hReeX := partner_isGammaTypeRee_of_rel h hrel hn2 hSU
        have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
        have hXa := h84 G A c L a b X n h
        have haN : a ∈ Subgroup.normalizer (X : Set G) :=
          hXa.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
        have hout : Sec4.InducesOuterTheta a X := by
          rcases hXa with h' | h'
          · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
          · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
        have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X :=
          h.pairRel.2.2.2.1
        obtain ⟨T₀, hT₀p, hT₀, hT₀le, -⟩ := exists_T₀ hF h hn2 hdcl
        have hT₀J : T₀ ≤ sec8J X a :=
          KFacts.le_inSubgroup_perfectResidual hT₀p
            (le_inf (hT₀le.trans (inf_le_left.trans hKX)) (hT₀le.trans inf_le_right))
        have hJ : sec8J X a ≠ ⊥ := fun hbot => hT₀ (le_bot_iff.mp (hbot ▸ hT₀J))
        have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
        have hM1 := Hering88E.imageModTheta_sec8J_eq_perfectResidual_of_isoGTwoEven kF87Cent_holds
          h84 h hJ hY hJY hbN hm2 hG2
        exact false_of_ree_abs (E := X) (I' := sec8J X a) haN ha3 hout hn2 hReeX rfl hJY hM1 hodd
          hm2 hG2
      · exact classB_swap_L2_of_rel h45 hF h84 Hering88C.inputs47ClassesD4_holds h hrel hn2 hKL2 hY hIJ hbY
          hodd hm2 hc1 hG2 hdcl hdb hdA hd3 hdN hin hne
  · subst hm1
    exact (false_of_small_swap h45 hF hG2Two h hn2 hIJ hbN hZ (Or.inr hP) hdcl hdA hd3 hdN hin
      hne).elim


theorem kF88Case1ClassBSwap_of_partner (h45 : Sec4.Item4_5) (hF : KF84Field) (h84 : Pair84A)
    (hPG : PartnerGamma88) (hG2Two : G2TwoCentThreeSolvable) (hR : KF88Case1ClassBSwapRest) :
    KF88Case1ClassBSwap := by
  intro G _ _ A c L a b X n h Y hY hIJ x hxb hxc hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN hin
    hne hE
  by_cases hcov : ClassBCovered b c x L Y n m
  · subst hxb
    exact classB_swap_covered_of_partner h45 hF h84 hPG hG2Two h hY hIJ hxY hodd hc1 hcov hdcl hdx
      hdA hd3 hdN hin hne
  · exact hR G A c L a b X n h Y hY hIJ x hxb hxc hxY A₀ d' m hodd hc1 hcov d hdcl hdx hdA hd3 hdN
      hin hne hE

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
