module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCaseThree
public import CFSG.Quasithin.SteinbergBKPairedCentralSeeds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Basic
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace A5Pair18

variable {D : Data G} {V₀ V L K : Subgroup G}

theorem barSub_ne_bot_or (c : A5Pair18 D V₀ V L K) (h61 : UC6.R6_1 D) (h127 : R127 D) :
    barSub V₀ V c.elemAbelian L ≠ ⊥ ∨ barSub V₀ V c.elemAbelian K ≠ ⊥ := by
  by_contra h
  simp only [not_or, ne_eq, not_not] at h
  obtain ⟨hLbot, hKbot⟩ := h
  have hp := c.data.hyp
  have hp125 := hp.hyp125
  have hcard : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hp125.pairFacts.elemAbelian₀).1 hp.small
  have hMC₀ : D.M ≤ Subgroup.centralizer (V₀ : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (CFSG.Walter.JT.commute_of_card_le_two hcard
      (hp125.pairFacts.le_normalizer₀ hm) s hs).symm
  have hLC₀ : L ≤ Subgroup.centralizer (V₀ : Set G) := c.mem_calC_L.1.le.trans hMC₀
  have hKC₀ : K ≤ Subgroup.centralizer (V₀ : Set G) := c.mem_calC.1.le.trans hMC₀
  have hLCtilde : L ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff c.elemAbelian
      hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀ c.mem_calC_L.1.le).1 hLbot
  have hKCtilde : K ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff c.elemAbelian
      hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀ c.mem_calC.1.le).1 hKbot
  have hV₀ab : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hp125.pairFacts.elemAbelian₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLC : L ≤ Subgroup.centralizer (V : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNine.le_centralizer_of_perfect_of_sub
      c.data.hyp.hL.1.2.1 hV₀ab hLC₀ (fun l hl v hv =>
        CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde c.elemAbelian
          hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀
          (hLCtilde hl) v hv)
  have hKC : K ≤ Subgroup.centralizer (V : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNine.le_centralizer_of_perfect_of_sub
      c.mem_calC.2.1 hV₀ab hKC₀ (fun k hk v hv =>
        CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde c.elemAbelian
          hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀
          (hKCtilde hk) v hv)
  have hrank : CFSG.Open.pRank 5 (L ⊔ K) = 2 :=
    pRank_five_sup_eq_two_of_calC c.mem_calC_L c.mem_calC c.ne_L c.data.alt c.alt_K
      c.commutator_le
  obtain ⟨A, hAK, hAel, hAcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_elemAbelian_card_of_le_pRank
      (M := L ⊔ K) Nat.prime_five (k := 2) (by rw [hrank])
  have hAp : IsPGroup 5 A := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hAel.2 (g : G) g.2)⟩
  have hAnc : ¬ IsCyclic A :=
    CFSG.LocalAnalysis.RankThreeUC.S15.not_isCyclic_of_isElemAbelian Nat.prime_five
      (by norm_num) hAel hAcard
  have hKM : L ⊔ K ≤ D.M := sup_le c.mem_calC_L.1.le c.mem_calC.1.le
  have hUK : UniqueMax D.M (L ⊔ K) :=
    c23_uniqueMax_of_noncyclic D h61 hp.hp hAp hAnc hAK hKM
  have hTI := uc22p22u_isTI_of_uniqueMax D c.elemAbelian hp125.pairFacts.le_normalizer
    (sup_le hLC hKC) hUK
  exact (twelve_nine D h127 hp125).1 hTI

theorem barSub_ne_bot_of_swap (c : A5Pair18 D V₀ V L K) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hsw : UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = CFSG.Quasithin.conjSubgroup L x) :
    barSub V₀ V c.elemAbelian L ≠ ⊥ ∧ barSub V₀ V c.elemAbelian K ≠ ⊥ := by
  obtain ⟨-, x, hxM, hK⟩ := hsw
  have hV : IsElemAbelian 2 V := c.elemAbelian
  have hp125 := c.data.hyp.hyp125
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := c.mem_calC_L.1.le.trans hMS
  have hxS : x⁻¹ ∈ stabTil V₀ V := hMS (D.M.inv_mem hxM)
  have hconj : barSub V₀ V hV (CFSG.Quasithin.conjSubgroup L x) =
      (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨x⁻¹, hxS⟩)).toMonoidHom :=
    TwelveTwentyThree.barSub_map_conj (V₀ := V₀) (V := V) hV hLS hxS
  have hiff : barSub V₀ V hV (CFSG.Quasithin.conjSubgroup L x) = ⊥ ↔
      barSub V₀ V hV L = ⊥ := by
    rw [hconj]
    constructor
    · intro hbot
      rw [Subgroup.map_eq_bot_iff] at hbot
      have hker : (MulAut.conj
          (actTil V₀ V hV ⟨x⁻¹, hxS⟩)).toMonoidHom.ker = ⊥ := by
        rw [MonoidHom.ker_eq_bot_iff]
        exact (MulAut.conj _).injective
      rw [hker] at hbot
      exact le_bot_iff.1 hbot
    · intro hbot
      rw [hbot]
      simp
  rcases barSub_ne_bot_or c h61 h127 with hL | hKne
  · exact ⟨hL, fun hb => hL ((hK.symm ▸ hiff).mp hb)⟩
  · exact ⟨fun hb => hKne ((hK.symm ▸ hiff).mpr hb), hKne⟩

theorem barSub_L_ne_barSub_K (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ = ⊥)
    (hL1 : barSub V₀ V c.elemAbelian L ≠ ⊥) (hK1 : barSub V₀ V c.elemAbelian K ≠ ⊥) :
    barSub V₀ V c.elemAbelian L ≠ barSub V₀ V c.elemAbelian K := by
  subst hV₀
  intro hEq
  classical
  have hV : IsElemAbelian 2 V := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.data.hyp.hyp125
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀
  have h2M : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 D.M) = ⊥ :=
    barSub_pCoreOf_eq_bot_of_hyp125 hp125
  have hLM : L ≤ D.M := c.mem_calC_L.1.le
  have hKM : K ≤ D.M := c.mem_calC.1.le
  let W := Vtil (⊥ : Subgroup G) V hV
  let A : Subgroup (Bar2 D.M) := UC22.barImage D.M L
  let B : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  let φ : Bar2 D.M →* MulAut W :=
    (barSub (⊥ : Subgroup G) V hV D.M).subtype.comp (bar2ActTilHom hV hMS h2M)
  have hφmk : ∀ (x : ↥D.M) (hgs : (x : G) ∈ stabTil (⊥ : Subgroup G) V),
      φ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x) =
        actTil (⊥ : Subgroup G) V hV ⟨(x : G), hgs⟩ := by
    intro x hgs
    have h1 : ((bar2ActTilHom hV hMS h2M
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) x) :
        ↥(barSub (⊥ : Subgroup G) V hV D.M)) : MulAut W) =
        actTil (⊥ : Subgroup G) V hV ⟨(x : G), hMS x.2⟩ := by
      change ((bar2ActTilHom hV hMS h2M (QuotientGroup.mk x) :
        ↥(barSub (⊥ : Subgroup G) V hV D.M)) : MulAut W) =
        actTil (⊥ : Subgroup G) V hV ⟨(x : G), hMS x.2⟩
      rw [bar2ActTilHom_mk]
    exact h1.trans (congrArg (actTil (⊥ : Subgroup G) V hV) (Subtype.ext rfl))
  have hmemA : ∀ q ∈ A, φ q ∈ barSub (⊥ : Subgroup G) V hV L := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hφmk x (hMS x.2)]
    exact actTil_mem_barSub (⊥ : Subgroup G) V hV (Subgroup.mem_subgroupOf.mp hx) (hMS x.2)
  have hmemB : ∀ q ∈ B, φ q ∈ barSub (⊥ : Subgroup G) V hV K := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hφmk x (hMS x.2)]
    exact actTil_mem_barSub (⊥ : Subgroup G) V hV (Subgroup.mem_subgroupOf.mp hx) (hMS x.2)
  have hsurjA : ∀ x ∈ barSub (⊥ : Subgroup G) V hV L, ∃ q ∈ A, φ q = x := by
    intro x hx
    obtain ⟨g, hgL, hgact⟩ := (mem_barSub (⊥ : Subgroup G) V hV L x).1 hx
    have hgM : (g : G) ∈ D.M := hLM hgL
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), hgM⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgL), ?_⟩
    rw [hφmk ⟨(g : G), hgM⟩ (hMS hgM)]
    exact hgact
  have hsurjB : ∀ x ∈ barSub (⊥ : Subgroup G) V hV K, ∃ q ∈ B, φ q = x := by
    intro x hx
    obtain ⟨g, hgK, hgact⟩ := (mem_barSub (⊥ : Subgroup G) V hV K x).1 hx
    have hgM : (g : G) ∈ D.M := hKM hgK
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), hgM⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hgK), ?_⟩
    rw [hφmk ⟨(g : G), hgM⟩ (hMS hgM)]
    exact hgact
  have hφA : A.map φ = barSub (⊥ : Subgroup G) V hV L := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hmemA q hq
    · intro hx
      obtain ⟨q, hq, hqφ⟩ := hsurjA x hx
      exact ⟨q, hq, hqφ⟩
  have hφB : B.map φ = barSub (⊥ : Subgroup G) V hV K := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hmemB q hq
    · intro hx
      obtain ⟨q, hq, hqφ⟩ := hsurjB x hx
      exact ⟨q, hq, hqφ⟩
  have hA5card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨eA⟩ := s13_bar_equiv c.mem_calC_L
  obtain ⟨eB⟩ := s13_bar_equiv c.mem_calC
  have hcardA : Nat.card ↥A = 60 := by
    obtain ⟨e2⟩ := c.data.alt
    calc Nat.card ↥A = Nat.card (Bar2 L) := (Nat.card_congr eA.toEquiv).symm
      _ = Nat.card ↥(alternatingGroup (Fin 5)) := Nat.card_congr e2.toEquiv
      _ = 60 := hA5card
  have hcardB : Nat.card ↥B = 60 := by
    obtain ⟨e2⟩ := c.alt_K
    calc Nat.card ↥B = Nat.card (Bar2 K) := (Nat.card_congr eB.toEquiv).symm
      _ = Nat.card ↥(alternatingGroup (Fin 5)) := Nat.card_congr e2.toEquiv
      _ = 60 := hA5card
  have hLs : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSimpleGroup_bar2_of_isAlt_five
      c.data.alt
  obtain ⟨eJ⟩ := barSubBar2Equiv_of_isSimpleGroup hp125 c.mem_calC_L hL1 hLs
  have hcardJ : Nat.card ↥(barSub (⊥ : Subgroup G) V hV L) = 60 := by
    obtain ⟨e2⟩ := c.data.alt
    calc Nat.card ↥(barSub (⊥ : Subgroup G) V hV L) = Nat.card (Bar2 L) :=
        (Nat.card_congr eJ.toEquiv).symm
      _ = Nat.card ↥(alternatingGroup (Fin 5)) := Nat.card_congr e2.toEquiv
      _ = 60 := hA5card
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
    CFSG.Quasithin.modO2Image_commute c.commutator_le
  have hdisj : A ⊓ B = ⊥ :=
    barImage_inf_eq_bot_of_calC c.mem_calC_L c.mem_calC c.ne_L
      c.data.alt hcomm
  have hHcard : Nat.card ↥(A ⊔ B) = 3600 := by
    rw [← Nat.card_congr
      (CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcomm hdisj).toEquiv,
      Nat.card_prod, hcardA, hcardB]
  let ψ : ↥(A ⊔ B) →* MulAut W := φ.comp (A ⊔ B).subtype
  have hψrange : ψ.range = barSub (⊥ : Subgroup G) V hV L := by
    have h1 : ψ.range = (A ⊔ B).map φ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨(y : Bar2 D.M), y.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [h1, Subgroup.map_sup, hφA, hφB, hEq, sup_idem]
  have hcardN : Nat.card ↥ψ.ker = 60 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψrange, hHcard, hcardJ] at h
    omega
  let e := CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcomm hdisj
  let N' : Subgroup (↥A × ↥B) := ψ.ker.map e.symm.toMonoidHom
  have hN'card : Nat.card ↥N' = 60 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hcardN
  have hN'normal : N'.Normal :=
    (MonoidHom.normal_ker ψ).map e.symm.toMonoidHom e.symm.surjective
  have hN'ne_bot : N' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥N' = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hN'ne_top : N' ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥N' = Nat.card ↥(⊤ : Subgroup (↥A × ↥B)) := by rw [htop]
    rw [Subgroup.card_top, Nat.card_prod, hcardA, hcardB] at h1
    omega
  have hAsimp : IsSimpleGroup ↥A :=
    (eA.symm.trans c.data.alt.some).isSimpleGroup_congr.mpr
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5)))
  have hBsimp : IsSimpleGroup ↥B :=
    (eB.symm.trans c.alt_K.some).isSimpleGroup_congr.mpr
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5)))
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr c.data.hyp.hL.1.2.1
  have hbarperf : Group.IsPerfect (Bar2 L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  have hAperf : Group.IsPerfect ↥A :=
    Group.IsPerfect.ofSurjective (f := eA.toMonoidHom) eA.surjective
  have hAnc : ¬ IsMulCommutative ↥A := fun h => hAperf.not_isMulCommutative ↥A h
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr c.mem_calC.2.1
  have hbarperfK : Group.IsPerfect (Bar2 K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  have hBperf : Group.IsPerfect ↥B :=
    Group.IsPerfect.ofSurjective (f := eB.toMonoidHom) eB.surjective
  have hBnc : ¬ IsMulCommutative ↥B := fun h => hBperf.not_isMulCommutative ↥B h
  have hcases := @CFSG.Quasithin.SteinbergBK.PairedSeeds.normal_eq_ker_snd_or_ker_fst
    ↥A ↥B _ _ hAsimp hBsimp hAnc hBnc N' hN'normal hN'ne_bot hN'ne_top
  have hnonemptyJ : ∃ q ∈ A, φ q ≠ 1 := by
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hL1
    have hxJ : (x : MulAut W) ∈ barSub (⊥ : Subgroup G) V hV L := x.2
    obtain ⟨q, hq, hqφ⟩ := Subgroup.mem_map.mp (by rw [hφA]; exact hxJ)
    refine ⟨q, hq, fun hq1 => hxne (Subtype.ext ?_)⟩
    rw [← hqφ, hq1]
    simp
  have hnonemptyK : ∃ q ∈ B, φ q ≠ 1 := by
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK1
    have hxJ : (x : MulAut W) ∈ barSub (⊥ : Subgroup G) V hV K := x.2
    obtain ⟨q, hq, hqφ⟩ := Subgroup.mem_map.mp (by rw [hφB]; exact hxJ)
    refine ⟨q, hq, fun hq1 => hxne (Subtype.ext ?_)⟩
    rw [← hqφ, hq1]
    simp
  rcases hcases with hsnd | hfst
  · have hAker : ∀ (q : Bar2 D.M) (hq : q ∈ A),
        (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(A ⊔ B)) ∈ ψ.ker := by
      intro q hq
      have hEsymm : e.symm (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(A ⊔ B)) = (⟨q, hq⟩, 1) := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact Subtype.ext (by
          rw [CFSG.Quasithin.Vol2.Ch10.SecE.coe_prodEquivSup]
          simp)
      have hmem : e.symm (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(A ⊔ B)) ∈ N' := by
        rw [hsnd, hEsymm]
        exact MonoidHom.mem_ker.mpr rfl
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
      have hy' : y = (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(A ⊔ B)) := by
        have h1 : e (e.symm y) = e (e.symm (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(A ⊔ B))) :=
          congrArg e hyx
        rwa [e.apply_symm_apply, e.apply_symm_apply] at h1
      rwa [hy'] at hy
    obtain ⟨q, hqA, hqφ⟩ := hnonemptyJ
    exact hqφ (by simpa [ψ] using MonoidHom.mem_ker.mp (hAker q hqA))
  · have hBker : ∀ (q : Bar2 D.M) (hq : q ∈ B),
        (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(A ⊔ B)) ∈ ψ.ker := by
      intro q hq
      have hEsymm : e.symm (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(A ⊔ B)) = (1, ⟨q, hq⟩) := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact Subtype.ext (by
          rw [CFSG.Quasithin.Vol2.Ch10.SecE.coe_prodEquivSup]
          simp)
      have hmem : e.symm (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(A ⊔ B)) ∈ N' := by
        rw [hfst, hEsymm]
        exact MonoidHom.mem_ker.mpr rfl
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
      have hy' : y = (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(A ⊔ B)) := by
        have h1 : e (e.symm y) = e (e.symm (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(A ⊔ B))) :=
          congrArg e hyx
        rwa [e.apply_symm_apply, e.apply_symm_apply] at h1
      rwa [hy'] at hy
    obtain ⟨q, hqB, hqφ⟩ := hnonemptyK
    exact hqφ (by simpa [ψ] using MonoidHom.mem_ker.mp (hBker q hqB))

end A5Pair18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
