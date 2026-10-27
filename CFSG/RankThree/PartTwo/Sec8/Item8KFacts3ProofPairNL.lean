module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
public import CFSG.RankThree.PartTwo.Sec8.Item84PairProof86
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairSetup

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item86ResProof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Pre

variable {G : Type} [Group G] [Finite G]

theorem nonempty_quot_projSL_of_data {L : Subgroup G} {d : G} {n : ℕ} (hn1 : 1 ≤ n)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n)))) :
    Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
      aschbacherSolvableCore 3
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
      projSL 2 (GaloisField 2 (3 * n))) := by
  obtain ⟨eK⟩ := hK
  obtain ⟨χ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta
    ((Item87Proof.residual_le _).trans inf_le_left)
    (Item87Proof.NoThetaNormal.of_mulEquiv eK (Item87Proof.noThetaNormal_projSL_two (by omega)))
  exact ⟨χ.trans eK⟩

theorem isQuasisimple_central_of_isoSUThree {Q : Type} [Group Q] {m : ℕ} (hm : Odd m)
    (h : IsoSUThree Q (2 ^ (3 * m))) :
    IsQuasisimple Q ∧ ∃ x : Q, (∀ y, x * y = y * x) ∧ x ≠ 1 ∧ x ^ 3 = 1 := by
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := h
  have hm1 : 1 ≤ m := hm.pos
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * m) F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨z, hz, hz1, hz3⟩ := KFacts.exists_mem_center_statedSU_ne_one hU
    (KFacts.three_dvd_two_pow_three_mul_add_one hm)
  have hq := (Item87Proof.isQuasisimple_statedSU_three hF (by omega)).1
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv ψ.symm hq, ψ.symm z, ?_, ?_, ?_⟩
  · intro y
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp hz (ψ y)).symm
  · intro h1
    apply hz1
    rw [← MulEquiv.apply_symm_apply ψ z, h1, map_one]
  · rw [← map_pow, hz3, map_one]

end Pre


section Shapes

variable {G : Type} [Group G] [Finite G]

theorem eq_three_mul_of_residual_projSL {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}
    {n : ℕ} (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))))
    {k : ℕ} (hk : 2 ≤ k)
    (hM : Nonempty (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G))) ≃* projSL 2 (GaloisField 2 k))) :
    k = 3 * n := by
  have hn1 : 1 ≤ n := h.data83.odd.pos
  obtain ⟨-, -, hLb⟩ := partner_data h hb hrel
  obtain ⟨eM⟩ := hM
  have hq : IsQuasisimple (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G)))) :=
    LocalCores.isQuasisimple_of_mulEquiv eM.symm (Item87Proof.isQuasisimple_projSL_two hk)
  have heq := residual_eq_of_isQuasisimple h hb hrel hq
  rw [hLb] at heq
  obtain ⟨χL⟩ := nonempty_quot_projSL_of_data hn1 hK
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ X := by
    rw [heq]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have eM' : imageModTheta X (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 k) :=
    (MulEquiv.subgroupCongr (congrArg (imageModTheta X) heq)).trans eM
  obtain ⟨χX⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKX
    (Item87Proof.NoThetaNormal.of_mulEquiv eM' (Item87Proof.noThetaNormal_projSL_two hk))
  have e : projSL 2 (GaloisField 2 k) ≃* projSL 2 (GaloisField 2 (3 * n)) :=
    (eM'.symm.trans χX.symm).trans χL
  have hc := Nat.card_congr e.toEquiv
  obtain ⟨r, hr, hcr⟩ := card_projSL_two_eq (g := k) (by omega)
  obtain ⟨s, hs, hcs⟩ := card_projSL_two_eq (g := 3 * n) (by omega)
  rw [hcr, hcs] at hc
  exact CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs hc

theorem false_of_residual_central {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))))
    (hq : IsQuasisimple (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G)))))
    (hx : ∃ x : imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G))), (∀ y, x * y = y * x) ∧ x ≠ 1 ∧ x ^ 3 = 1) :
    False := by
  have hn1 : 1 ≤ n := h.data83.odd.pos
  obtain ⟨-, -, hLb⟩ := partner_data h hb hrel
  have heq := residual_eq_of_isQuasisimple h hb hrel hq
  rw [hLb] at heq
  obtain ⟨χL⟩ := nonempty_quot_projSL_of_data hn1 hK
  have hKX : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ X := by
    rw [heq]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hZ := KFacts.center_eq_bot_of_mulEquiv_fwd χL.symm
    (center_projSL_two_eq_bot (k := 3 * n) (by omega))
  set e := MulEquiv.subgroupCongr (congrArg (imageModTheta X) heq) with he
  obtain ⟨x, hxc, hx1, hx3⟩ := hx
  refine false_of_central_three hKX hZ (x := e.symm x) (fun y => ?_) (fun h1 => hx1 ?_) ?_
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hxc]
  · rw [← MulEquiv.apply_symm_apply e x, h1, map_one]
  · rw [← map_pow, hx3, map_one]

theorem false_of_residual_subsingleton {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}
    {n : ℕ} (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X)
    (hs : Subsingleton (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G))))) : False := by
  obtain ⟨hbΓ, -, -⟩ := partner_data h hb hrel
  obtain ⟨-, -, hK1⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKX : K ≤ X := hrel.2.2.2.1
  have hKM : K ≤ inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) :=
    KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
      (le_inf hKX (hKL.trans hLc))
  apply hK1
  refine Item87Proof.eq_bot_of_imageModTheta_eq_bot hKX (Item87Proof.isPerfect_residual _) ?_
  rw [eq_bot_iff]
  intro y hy
  have hle : imageModTheta X K ≤ imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G))) := Subgroup.map_mono (fun z hz => hKM hz)
  have hyM := hle hy
  have h1 : (⟨y, hyM⟩ : imageModTheta X _) = 1 := Subsingleton.elim _ _
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

theorem eq_of_residualShape {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G))
    {X : Subgroup G} (hrel : PairRel A c L b X)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))))
    {k : ℕ} (hk : 2 ≤ k)
    (hS : ResidualShape (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G)))) k) :
    k = 3 * n ∧ Nonempty (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))) := by
  rcases hS with hM | ⟨hq, hx⟩ | hs
  · have hk3 := eq_three_mul_of_residual_projSL h hb hrel hK hk hM
    subst hk3
    exact ⟨rfl, hM⟩
  · exact (false_of_residual_central h hb hrel hK hq hx).elim
  · exact (false_of_residual_subsingleton h hb hrel hs).elim

end Shapes

theorem pair84GammaNL_of (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hL : Item82TwoList)
    (hC : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus) (hA : Sec11.KS11Lie4Proof.G2ThreeACentMinus)
    (hSp : KF84Sp4ThreeCent) : Pair84GammaNL := by
  intro G _ _ A c L a d n h _ hK b X hb hrel hXU
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  have hKB : KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO hR)
  have hG2 : KF83IndepGTwo := kF83IndepGTwo_holds
  have hInd : KF83Indep := kF83Indep_of hG2
  have hn1 : 1 ≤ n := h.data83.odd.pos
  have hcN := le_normalizer_of_partner h45 h hb hrel h.mem_A
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  obtain ⟨-, hck⟩ := kinds_of_partner h418 hF h hb hrel
  have hne := Item812Res7.ne_one_of_partner h hb hrel hcN
  obtain ⟨m, hm, hD | ⟨q, hq2, hqe, hG⟩ | hRee | hSpX⟩ :=
    nonUnitary_cases (isList82Two_of_partner hL h45 h418 hF hKB hInd hG2 h hb hrel) hXU
  ·
    obtain ⟨hm1, K, _, _, σ, hKc, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hD
    obtain ⟨hk, eM⟩ := eq_of_residualShape h hb hrel hK (by omega)
      (d4_residualShape hcN hc3 hck hne hm1 hKc hσ E)
    have hmn : m = n := by omega
    subst hmn
    exact ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨Or.inl hD, eM⟩⟩
  ·
    obtain ⟨K, _, _, hKc, ⟨E⟩⟩ := Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG
    have hm1 : 1 ≤ m := hm.pos
    obtain ⟨hk, eM⟩ := eq_of_residualShape h hb hrel hK (by omega)
      (g2_residualShape hC hA hcN hc3 hck hne (f := 3 * m) (by omega) hKc E)
    have hmn : m = n := by omega
    subst hmn
    exact ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨Or.inr (Or.inl ⟨q, hq2, hqe, hG⟩), eM⟩⟩
  ·
    exfalso
    obtain ⟨hq, hx⟩ := isQuasisimple_central_of_isoSUThree hm (ree_residual hcN hc3 hck hne hRee)
    exact false_of_residual_central h hb hrel hK hq hx
  ·
    obtain ⟨eSp⟩ := hSpX
    have hm1 : 1 ≤ m := hm.pos
    obtain ⟨hk, eM⟩ := eq_of_residualShape h hb hrel hK (by omega)
      (Or.inl (sp4_residual hSp hcN hc3 hck hne (f := 3 * m) (by omega) eSp))
    have hmn : m = n := by omega
    subst hmn
    exact ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨eSp⟩))), eM⟩⟩

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
