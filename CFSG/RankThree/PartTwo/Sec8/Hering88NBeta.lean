module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NThm1
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def PartnerGamma88 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
    ∀ (x : G) (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → Case83One Y x A₀ d' m →
      IsGammaIndex A X c n

theorem classBSwapOne (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4) (h84 : Pair84A)
    (hPG : PartnerGamma88)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} (h : Sec8Pair G A c L a b X 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hbY : KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField)
    {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m) (hc1 : Case83One Y b A₀ d' m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdb : d ∉ Subgroup.zpowers b)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  classical
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hAel := h.mem_partTwoF.1
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := (PartOne.mem_thetaComponentsAt_iff.mp hX).1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hb3 hb1 hAp
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu b hbA)) X hX
  have hk := h84 G A c L a b X 1 h
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have haoutX : Sec4.InducesOuterTheta a X := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) :=
    hbY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hbout : Sec4.InducesOuterTheta b Y := by
    rcases hbY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  have hJdef : sec8J X a = inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) :=
    rfl
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hJb : sec8J X a ≤ Subgroup.centralizer ({b} : Set G) := hJX.trans hXb
  have hJp : Group.IsPerfect (sec8J X a) := Item87Proof.isPerfect_residual _
  have hJ : sec8J X a ≠ ⊥ := Item812Res6.sec8J_ne_bot_of_gTwoPartner kF87INontriv_holds h84 h
  have hJX_img : imageModTheta X (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haX ⟨1, by simpa using ha3⟩
  have hcX : IsGammaIndex A X c 1 := hPG G A c L a b X 1 h Y hY hIJ b A₀ d' m hodd hc1
  have hXside := lside_abs hcX (h.not_unitary 3) ha3 hk
  rw [← hJdef] at hXside
  have hN6048 : (IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) 1 ∨
      IsoGTwoEven (X ⧸ aschbacherSolvableCore 3 X) (3 * 1)) →
      Nat.card (sec8J X a ⧸ aschbacherSolvableCore 3 (sec8J X a)) = 6048 := fun hX1 => by
    have hG2X := h.gTwoPartner 1 hX1
    rw [card_quot_theta_eq_of_isSimpleGroup hJX hJX_img
      (isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2X),
      card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2X]
  rcases hc1.2.2 with hG2 | ⟨-, hP, -⟩
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by have := hodd.pos; omega
      have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2
      have hM1 := Hering88E.imageModTheta_sec8J_eq_perfectResidual kF87Cent_holds h84 h hJ hY hJY
        hbN hS
      have hNY : Nat.card (sec8J X a ⧸ aschbacherSolvableCore 3 (sec8J X a)) = 6048 := by
        rw [card_quot_theta_eq_of_isSimpleGroup hJY hM1 hS,
          card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2]
      rcases hXside with ⟨hX1, hKc⟩ | hle | ⟨hge, -⟩
      ·
        have hda : d ∈ Subgroup.centralizer ({a} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (hAc d hdA a h.a_mem)
        have hca : c ∈ Subgroup.centralizer ({a} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr (hAc c h.mem_A a h.a_mem)
        have hdJ : d ∈ Subgroup.normalizer (sec8J X a : Set G) :=
          CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
            _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAX hdA, Subgroup.le_normalizer hda⟩)
        have hcJ : c ∈ Subgroup.normalizer (sec8J X a : Set G) :=
          CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
            _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAX h.mem_A, Subgroup.le_normalizer hca⟩)
        have hdcl' : d ∈ Subgroup.closure ({b, c} : Set G) := by rwa [Set.pair_comm]
        have hcd : sec8J X a ⊓ Subgroup.centralizer ({d} : Set G) =
            sec8J X a ⊓ Subgroup.centralizer ({c} : Set G) :=
          inf_centralizer_eq_of_mem_closure hAel hbA h.mem_A hdcl' hb1 hdb hJb
        exact classOne_transfer h47 haX ha3 haoutX (hAX h.mem_A) hc3 (hAc a h.a_mem c h.mem_A) hX1
          (h.gTwoPartner 1 hX1) hKc hc1.1 hbN hb3 hbout hG2 hJdef hJY hM1 hdN hd3
          (hAc b hbA d hdA) hin hne hdJ hcJ hcd
      · omega
      · omega
    · exfalso
      have hS := Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hm2 hG2
      have hM1 := Hering88E.imageModTheta_sec8J_eq_perfectResidual kF87Cent_holds h84 h hJ hY hJY
        hbN hS
      have hNY : 251596800 ≤ Nat.card (sec8J X a ⧸ aschbacherSolvableCore 3 (sec8J X a)) := by
        rw [card_quot_theta_eq_of_isSimpleGroup hJY hM1 hS]
        exact card_inSubgroup_perfectResidual_ge_of_isoGTwoEven hm2 hG2
      rcases hXside with ⟨hX1, -⟩ | hle | ⟨-, hle⟩
      · have := hN6048 hX1
        omega
      · omega
      · omega
  ·
    exfalso
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by have := hodd.pos; omega
      exact false_of_isSolvable_barCentralizer hbN hb3 hJY hJb hJp hJ
        (Hering88F.isSolvable_of_isoPGUThree_two hP)
    · have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
      have hM1 := Hering88E.imageModTheta_sec8J_eq_perfectResidual kF87Cent_holds h84 h hJ hY hJY
        hbN hS
      have hNY := card_quot_theta_eq_of_isSimpleGroup hJY hM1 hS
      have h3 := card_le_three_mul_card_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
      have hle := Subgroup.card_le_of_le
        (Item87Proof.residual_le (barCentralizer (Subgroup.zpowers b) Y))
      have hcard := CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree (by omega) hP
      rw [← hNY, hcard] at h3
      rw [← hNY, hcard] at hle
      refine false_of_pgu_bounds hodd hm2 h3 hle ?_
      rcases hXside with ⟨hX1, -⟩ | hle' | hge
      · exact Or.inl (hN6048 hX1)
      · exact Or.inr (Or.inl hle')
      · exact Or.inr (Or.inr hge)

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
