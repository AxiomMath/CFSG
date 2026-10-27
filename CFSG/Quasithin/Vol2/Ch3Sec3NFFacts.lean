module

public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313FB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem nf_le_centralizer_Z (h36 : A36ForSQTK) (h : Hyp331 G T M L D)
    {H₀ K : Subgroup G} (hH₀ : InH T H₀) (hK : K ∈ cComp H₀)
    (hKf : ¬ quasithinIsFaithfulLocal T K) :
    K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hF : CharTwo H₀ := charTwo_of_inH' h.qtke h.sylow hH₀
  have hred := (conjClosure_isTwoReducedIn_of_charTwo
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hH₀.1) hF
    (Z := quasithinOmegaOneCenter T) le_rfl).2.2
  have hZle : conjClosure (quasithinOmegaOneCenter T) H₀ ≤ twoReducedJoin H₀ :=
    le_iSup₂_of_le (conjClosure (quasithinOmegaOneCenter T) H₀) hred le_rfl
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  subst hS
  have hTFAE := lemma_1_2_10_of_a36 h.qtke h.simple h.nonabelian h36 S hH₀ hK
  have hno : ⁅twoReducedJoin H₀, K⁆ = ⊥ := by
    by_contra hne
    exact hKf ((hTFAE.out 1 3).mpr hne)
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ twoReducedJoin H₀ := hZle (le_conjClosure _ _ hz)
  have hc : ⁅z, k⁆ ∈ ⁅twoReducedJoin H₀, K⁆ := Subgroup.commutator_mem_commutator hz' hk
  rw [hno, Subgroup.mem_bot, commutatorElement_def] at hc
  have h1 : z * k * z⁻¹ = k := mul_inv_eq_one.mp hc
  calc z * k = (z * k * z⁻¹) * z := by group
    _ = k * z := by rw [h1]

theorem nf_conjClosure_le_centralizer_Z (h36 : A36ForSQTK) (h : Hyp331 G T M L D)
    {H₀ K : Subgroup G} (hH₀ : InH T H₀) (hK : K ∈ cComp H₀)
    (hKf : ¬ quasithinIsFaithfulLocal T K) :
    conjClosure K T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hKC := nf_le_centralizer_Z h36 h hH₀ hK hKf
  have hTC := CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  refine conjClosure_le fun t ht k hk => ?_
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTC ht) (hKC hk)) (Subgroup.inv_mem _ (hTC ht))

structure NFConfig (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) : Prop where
  hyp : Hyp331 G T M L D
  inH : InH T H
  HLT : H ≤ L ⊔ T
  wreath : Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2)
  O : pCoreOf 2 (H ⊔ D) ≠ ⊥
  K_comp : K ∈ cComp (H ⊔ D)
  Kq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  YK : oTwoUpper H ≤ conjClosure K T
  TK : ¬ T ≤ Subgroup.normalizer (K : Set G)
  nonfaithful : ¬ quasithinIsFaithfulLocal T K
  model : ∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1

namespace NFConfig

variable {H K : Subgroup G} (c : NFConfig G T M L D H K)
include c

theorem isSylowTwoOf_H₀ : IsSylowTwoOf T (H ⊔ D) :=
  isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow (c.inH.1.trans le_sup_left)

theorem inH_H₀ : InH T (H ⊔ D) := ⟨c.inH.1.trans le_sup_left, c.O⟩

theorem K_isLocal : quasithinIsLocal T K :=
  isLocal_of_mem_cComp_of_sylow c.isSylowTwoOf_H₀ c.O c.K_comp

theorem K_lt_conjClosure : K < conjClosure K T := by
  refine lt_of_le_of_ne (le_conjClosure K T) fun he => c.TK ?_
  rw [he]
  exact le_normalizer_conjClosure K T

theorem isMaximalLocal (h128 : Lemma128Two) :
    quasithinIsMaximalLocal T K := by
  obtain ⟨q, hq, h24, hmod⟩ := c.model
  rcases lemma_1_2_8_three h128 c.hyp.qtke c.hyp.simple c.hyp.nonabelian c.K_isLocal
      c.K_lt_conjClosure with hm | hA5
  · exact hm
  · exact (Lem3313F.not_fiveShape_of_psl2 hq h24 hmod (Or.inr (Or.inr (Or.inl hA5)))).elim

theorem uniqueM (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    IsUniqueM (K ⊔ T) (Subgroup.normalizer (conjClosure K T : Set G)) :=
  lemma_1_2_7_three c.hyp.qtke c.hyp.simple c.hyp.nonabelian (a37ForSQTK_of_cat h37)
    (a38ForSQTK_of_cat h38) (a39ForSQTK_of_cat h39) c.hyp.sylow (c.isMaximalLocal h128)

theorem H₀_le_normalizer (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) :
    H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  have := c.hyp.simple
  exact Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot
    (qtkeCore_of_cat c.hyp.nonabelian c.hyp.qtke).1 h37 h38 c.O c.isSylowTwoOf_H₀ c.K_comp

theorem not_le_normalizer (h5 : Stmt3_3_5) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ¬ mPlus L T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  intro hLT
  have hU := (h5 G T M L c.hyp.toSetup331).2.1
  have hM : Subgroup.normalizer (conjClosure K T : Set G) = M :=
    hU.2 _ ⟨(c.uniqueM h128 h37 h38 h39).1.1, hLT⟩
  exact Hyp331.not_D_le c.hyp (hM ▸ le_sup_right.trans (c.H₀_le_normalizer h37 h38))

theorem inf_centralizer_mPlus_eq_bot (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) = ⊥ := by
  by_contra hne
  set P := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) with hP
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le _).2 fun _ hz => hz.1.1
  have hTC := CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hKC := nf_le_centralizer_Z h36 c.hyp c.inH_H₀ c.K_comp c.nonfaithful
  have hP2 : IsPGroup 2 P := c.hyp.sylow.1.to_le (inf_le_left.trans hZT)
  have hcentP : ∀ X : Subgroup G, X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      X ≤ Subgroup.normalizer (P : Set G) := by
    intro X hX x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_iff.mp (hX hx) p hp.1
  have hL₀P : mPlus L T ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp hp.2 x hx).symm
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hne, hP2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hKT : K ⊔ T ≤ Subgroup.normalizer (P : Set G) := sup_le (hcentP K hKC) (hcentP T hTC)
  have hM'eq : M' = Subgroup.normalizer (conjClosure K T : Set G) :=
    (c.uniqueM h128 h37 h38 h39).2 M' ⟨hM', hKT.trans hle⟩
  refine c.not_le_normalizer h5 h128 h37 h38 h39 ?_
  rw [← hM'eq]
  exact (sup_le hL₀P (hcentP T hTC)).trans hle

end NFConfig

end CFSG.Quasithin.H13
