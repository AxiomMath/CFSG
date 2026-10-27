module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415
public import CFSG.Quasithin.H13.U3ModelsExclude
import CFSG.GroupTheory.PCoreSurjective

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centerQuot_of_barO2Z {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {X : Type} [Group X] (h : Nonempty (BarO2Z17 L ≃* X)) :
    Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃* X) := by
  obtain ⟨e1⟩ := barO2Z17_equiv_barInf hL
  obtain ⟨e2⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨e⟩ := h
  exact ⟨((e1.trans e2).symm).trans e⟩

theorem exists_permutes_three_of_alt_ge_eight {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (hn : 8 ≤ n) (hshape : Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      alternatingGroup (Fin n))) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e⟩ := hshape
  obtain ⟨eA⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.alt_of_center_odd
    hq hn e hodd
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hHle : L ⊔ D.T ≤ D.M := sup_le hLM D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T) := by
    rw [CFSG.Open.IsSubnormal.iff_subgroupOf le_sup_left]
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (B := L) (L := L ⊔ D.T) (K := D.M)
      hHle ((CFSG.Open.IsSubnormal.iff_subgroupOf hLM).mp hL.1)
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 D.T (L ⊔ D.T) :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 (TwelveShort.isSylowIn_of_le D le_sup_right)
  obtain ⟨P, hPle, hPe, hP9, hPperm, -⟩ :=
    TwelveThirteen.exists_three_subgroup (X := L) (T := D.T) hn hsub hT ⟨eA⟩
  have hPM : P ≤ D.M := hPle.trans hHle
  have hPp : IsPGroup 3 ↥P := CFSG.Open.IsElemAbelian.isPGroup hPe
  have hPexp : ∀ x ∈ P, x ^ 3 = 1 := hPe.2
  have hPnc : ¬ IsCyclic ↥P := by
    refine CFSG.Quasithin.H13.U3.not_isCyclic_of_exponent_three ?_ hPexp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1 : k ≤ 1 := by omega
      have h2 : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      rw [hk] at hP9
      omega
    rw [hk]
    refine ⟨3 ^ (k - 2), ?_⟩
    rw [show k = 2 + (k - 2) by omega, pow_add]
    norm_num
  exact ⟨P, hPM, fun hbot => by
    have : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
    omega, hPp, hPexp, hPnc, hPperm⟩

theorem exists_permutes_three_of_alt_seven (hKA1 : Inputs1719.K_A7Permuting)
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty ((Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      alternatingGroup (Fin 7))) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T := by
  refine exists_permutes_three_of_calC (D := D) (L := L) hL ?_
  intro Y _ _ K hKn hKq hKodd he hcent hidx S hS
  obtain ⟨e⟩ := he
  have eZ : (↥K ⧸ Subgroup.center ↥K) ≃*
      (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  obtain ⟨h7⟩ := hshape
  exact hKA1 Y K S ⟨hKn, hKq, hKodd, hcent, hidx, hS⟩ ⟨eZ.trans h7⟩

theorem false_of_k_eq_one_of_permutes {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (hk : D.k = 1)
    (hX : ∃ X : Subgroup G, X ≤ D.M ∧ X ≠ ⊥ ∧ IsPGroup 3 ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X ∧ Permutes X D.T) : False := by
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 :=
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Data.k_eq_two_iff D).2 hns
    omega
  obtain ⟨X, hXM, -, hXp, hXexp, hXnc, hperm⟩ := hX
  have hin : F11.InP11 D X :=
    inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM hXp hXexp hXnc hperm
  have hk2 : D.k = 2 := (h17_1.2 ⟨X, hin⟩).2.1
  omega

theorem eq_of_mem_calC_of_imageOTwoQuot_eq {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (h : CFSG.Quasithin.imageOTwoQuot D.M L = CFSG.Quasithin.imageOTwoQuot D.M K) :
    L = K := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK1 : CFSG.IsComponent (CFSG.Quasithin.imageOTwoQuot D.M L) := isComponent_K1 hL
  let π : ↥D.M →* CFSG.Quasithin.OTwoQuot D.M :=
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)
  have hcomm : ⁅L, K⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.calC_commutator_le_of_ne hL hK hne).trans
      (inf_le_left.trans (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hL.1))
  have hbot : ⁅CFSG.Quasithin.imageOTwoQuot D.M L,
      CFSG.Quasithin.imageOTwoQuot D.M K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨lx, hlx, hxl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ky, hky, hyk⟩ := Subgroup.mem_map.mp hy
    have hlxG : ((lx : ↥D.M) : G) ∈ L := hlx
    have hkyG : ((ky : ↥D.M) : G) ∈ K := hky
    have hmemG : ⁅((lx : ↥D.M) : G), ((ky : ↥D.M) : G)⁆ ∈ CFSG.Open.pCoreOf 2 D.M :=
      hcomm (Subgroup.commutator_mem_commutator hlxG hkyG)
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hmemG
    have hw' : w = ⁅lx, ky⁆ := Subtype.ext (hwv.trans
      (map_commutatorElement (f := D.M.subtype) (g₁ := lx) (g₂ := ky)).symm)
    have hmem : ⁅lx, ky⁆ ∈ CFSG.Open.pCore 2 ↥D.M := by
      rw [← hw']
      exact hw
    have hπ1 : π ⁅lx, ky⁆ = 1 := (QuotientGroup.eq_one_iff ⁅lx, ky⁆).mpr hmem
    have hxy : ⁅x, y⁆ = 1 := by
      rw [← hxl, ← hyk, ← map_commutatorElement]
      exact hπ1
    simpa using hxy
  have hbot' : ⁅CFSG.Quasithin.imageOTwoQuot D.M L,
      CFSG.Quasithin.imageOTwoQuot D.M L⁆ = ⊥ := by
    rw [← h] at hbot
    exact hbot
  exact CFSG.Quasithin.C2Push.commutator_ne_bot_of_isComponent hK1 hbot'

theorem le_normalizer_of_le_normalizer_imageOTwoQuot {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M)
    (h : CFSG.Quasithin.imageOTwoQuot D.M D.T ≤
      Subgroup.normalizer (CFSG.Quasithin.imageOTwoQuot D.M L :
        Set (CFSG.Quasithin.OTwoQuot D.M))) :
    D.T ≤ Subgroup.normalizer (L : Set G) := by
  intro t ht
  have htM : t ∈ D.M := D.sylowM.le ht
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have htbar : (QuotientGroup.mk ⟨t, htM⟩ : CFSG.Quasithin.OTwoQuot D.M) ∈
      CFSG.Quasithin.imageOTwoQuot D.M D.T := by
    refine Subgroup.mem_map.mpr ⟨⟨t, htM⟩, ht, rfl⟩
  have hnorm : CFSG.Quasithin.imageOTwoQuot D.M (CFSG.Quasithin.conjByElt t L) =
      CFSG.Quasithin.imageOTwoQuot D.M L := by
    rw [CFSG.Quasithin.C2Push.imageOTwoQuot_conjByElt htM hLM]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (h htbar))
  have hMM : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htM)
  have hLt : CFSG.Quasithin.conjByElt t L ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMM hL
  have heq : CFSG.Quasithin.conjByElt t L = L :=
    eq_of_mem_calC_of_imageOTwoQuot_eq hLt hL hnorm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

section Certified

theorem false_of_bBar_le_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G) (h111 : W3Thm111 G)
    (h126 : R126 D) (hk : D.k = 1)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hU : UniqueMax D.M (L ⊔ D.T)) (hUc : UniqueMax D.M (UC22.conjClosure D.M L))
    (hInFSq : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T))
    (hb : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2)
    (hm : MBarGT D.M V₀ V 3)
    (hO2 : ∀ g : G, g ∉ D.M → ¬ twoResidual (L ⊔ D.T) ≤ conjSubgroup D.M g) : False := by
  have hmbar : 3 < mBar D.M V₀ V hV.isElemAbelian :=
    (hV.mBarGT_iff_lt_mBar 3).1 hm
  by_cases hV0 : V₀ = ⊥
  · have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV hV0 hL.1 hL.2.2 hL1 hUc
    omega
  · let Δ : Finset (Subgroup G) := {L ⊔ D.T}
    have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
      intro H hH
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact ⟨le_sup_right, sup_le (CFSG.Quasithin.A3.subnormal_le hL.1) D.sylowM.le⟩
    have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
      rw [← Finset.sup_eq_iSup]
      have hsup : Δ.sup (fun H => H) = L ⊔ D.T := by simp [Δ]
      rw [hsup]
      exact hU
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq (1 : ℕ) H := by
      intro H hH
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact hInFSq
    have hmax : Δ.sup (fun _ => 1) = 1 := by simp [Δ]
    have hmk : D.k + 1 < mBar D.M V₀ V hV.isElemAbelian := by
      rw [hk]
      omega
    have hO2' : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
      intro H hH g hg
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact hO2 g hg
    have hbound := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183
      hV hV0 hL.1 hL.2.2 hL1 hΔ hΔU (fun _ => 1) hι hO2' hmax hmk
    omega

end Certified

theorem bar2_comap_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) (P : Subgroup Y) :
    Nonempty (Bar2 (P.comap f) ≃* Bar2 P) := by
  let L : Subgroup X := P.comap f
  let g : ↥L →* ↥P :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hgs : Function.Surjective g := by
    intro p
    obtain ⟨x, hx⟩ := hf (p : Y)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show f x ∈ P
    rw [hx]
    exact p.2
  have hkg : IsPGroup 2 g.ker := by
    have hsub : g.ker ≤ f.ker.subgroupOf L := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    let κ : ↥g.ker →* ↥f.ker :=
      { toFun := fun x => ⟨((x : ↥L) : X), hsub x.2⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp }
    have hκ : Function.Injective κ := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥f.ker => (z : X)) hab))
    exact IsPGroup.of_injective hker κ hκ
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker g hgs hkg

theorem exists_s3_pair_comap {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    {S : Subgroup X} {P₁ P₂ : Subgroup Y}
    (hS₁ : S.map f ≤ P₁) (hS₂ : S.map f ≤ P₂) (hsup : P₁ ⊔ P₂ = ⊤)
    (hq₁ : Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)))
    (hq₂ : Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))) :
    ∃ L₁ L₂ : Subgroup X, S ≤ L₁ ∧ S ≤ L₂ ∧ L₁ ⊔ L₂ = ⊤ ∧
      Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) := by
  refine ⟨P₁.comap f, P₂.comap f, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hS₁ (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  · intro s hs
    exact hS₂ (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  · have hmap : (P₁.comap f ⊔ P₂.comap f).map f = ⊤ := by
      rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hf,
        Subgroup.map_comap_eq_self_of_surjective hf, hsup]
    have hkerle : f.ker ≤ P₁.comap f ⊔ P₂.comap f := by
      intro x hx
      have hx1 : x ∈ P₁.comap f := by
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
        exact P₁.one_mem
      exact Subgroup.mem_sup_left hx1
    have := Subgroup.comap_map_eq_self hkerle
    rw [hmap, Subgroup.comap_top] at this
    exact this.symm
  · obtain ⟨e⟩ := bar2_comap_mulEquiv f hf hker P₁
    obtain ⟨eq⟩ := hq₁
    exact ⟨e.trans eq⟩
  · obtain ⟨e⟩ := bar2_comap_mulEquiv f hf hker P₂
    obtain ⟨eq⟩ := hq₂
    exact ⟨e.trans eq⟩

theorem kyForm_twoQuotient {H : Type} [Group H] [Finite H] {K S : Subgroup H}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K) :
    letI : (CFSG.GroupTheory.twoQuotientC K S).Normal :=
      CFSG.GroupTheory.twoQuotientC_normal hSK
    Inputs1719.KYForm (CFSG.GroupTheory.twoQuotientY K S
        (CFSG.GroupTheory.twoQuotientC_normal hSK))
      (CFSG.GroupTheory.twoQuotientKY K S (CFSG.GroupTheory.twoQuotientC_normal hSK))
      (CFSG.GroupTheory.twoQuotientSY K S (CFSG.GroupTheory.twoQuotientC_normal hSK)) := by
  letI : (CFSG.GroupTheory.twoQuotientC K S).Normal :=
    CFSG.GroupTheory.twoQuotientC_normal hSK
  obtain ⟨eK⟩ := CFSG.GroupTheory.twoQuotientK_nonempty_equiv_K hZ hS hSK
  refine ⟨CFSG.GroupTheory.twoQuotientKY_normal hSK, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.Goldschmidt.G37.open_isQuasisimple_of_mulEquiv eK.symm hKq
  · rw [Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
    exact hZ
  · exact CFSG.GroupTheory.twoQuotient_centralizer_eq_center hZ hS hSK hSyl
  · exact CFSG.GroupTheory.twoQuotientKY_index_eq_pow hS hSK
  · exact CFSG.GroupTheory.twoQuotientSY_isSylowIn hS hSK hSyl

theorem nonempty_bar2_mulEquiv_map_subtype {H : Subgroup G} (X : Subgroup ↥H) :
    Nonempty (Bar2 X ≃* Bar2 (X.map H.subtype)) := by
  let e : ↥X ≃* ↥(X.map H.subtype) :=
    Subgroup.equivMapOfInjective X H.subtype H.subtype_injective
  exact ⟨QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(X.map H.subtype)) e
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

