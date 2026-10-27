module

public import CFSG.LocalAnalysis.StandardType.GGF4N2OmegaK
public import CFSG.LocalAnalysis.StandardType.GGSecFiveQTwoInternal
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic
public import CFSG.GroupTheory.GLS2.GroupTheory.Quasisimple
public import CFSG.LocalAnalysis.StandardType.GGF4OriginalRankOne
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusRankOne
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGSharedInvolution
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
public import CFSG.GroupTheory.GLS2.GroupTheory.PiComponents

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.RootSystem
open Module

theorem GGTorusModelAt.iSup_rankOneIn_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X C : Subgroup G}
    (hCX : C ≤ Subgroup.centralizer (X : Set G))
    (hsplit : Bs = C ⊔ (Bs ⊓ X)) (hdisj : Disjoint C (Bs ⊓ X))
    (hM : GGTorusModelAt p ((Bs ⊓ X).subgroupOf X)) :
    (⨆ r : MulAut Bs, ⨆ (_ : r ∈ ggAutomizer X Bs),
      ⨆ (_ : GGIsReflection p r), ggRankOneIn X Bs r) = X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, τ, ι, w, s, S, hι, hτ, hτP, hws, hs, hfix, -, hwS, hcomp, -, hgen⟩ := hM
  let : Nonempty ι := hι
  let T := Fin k → Multiplicative (ZMod p)
  let P := Bs ⊓ X
  let eT : T ≃* P :=
    (MonoidHom.ofInjective hτ).trans ((MulEquiv.subgroupCongr hτP).trans
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ≤ X)))
  have hcomm : ∀ c ∈ C, ∀ z ∈ P, c * z = z * c := by
    intro c hc z hz
    exact (Subgroup.mem_centralizer_iff.mp (hCX hc) z hz.2).symm
  let eSup := CFSG.GH74.E2.prodSupEquiv C P hcomm (disjoint_iff.mp hdisj)
  let κ : C × T ≃* Bs :=
    ((MulEquiv.refl C).prodCongr eT).trans (eSup.trans (MulEquiv.subgroupCongr hsplit.symm))
  have hκ : ∀ c f, (κ (c, f) : G) = c * (τ f : G) := by
    intro c f
    change (eSup (c, eT f) : G) = c * (τ f : G)
    rw [CFSG.GH74.E2.prodSupEquiv_apply]
    rfl
  let r : ι → MulAut Bs := fun i =>
    MulAut.congr κ ((MulEquiv.refl C).prodCongr (s i))
  have hr : ∀ i, GGIsReflection p (r i) := fun i =>
    ggIsReflection_congr_prod_id hp hp2 κ (s i) (by simpa only [pow_two] using hs i) (hfix i)
  have hact : ∀ i b, ((r i b : Bs) : G) = (w i : G) * b * (w i : G)⁻¹ := by
    intro i b
    obtain ⟨⟨c, f⟩, rfl⟩ := κ.surjective b
    dsimp only [r]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (κ (c, s i f) : G) = (w i : G) * (κ (c, f) : G) * (w i : G)⁻¹
    rw [hκ, hκ]
    have hc : c * (w i : G) = (w i : G) * c :=
      (Subgroup.mem_centralizer_iff.mp (hCX c.2) (w i) (w i).2).symm
    have hw : (w i : G) * (τ f : G) * (w i : G)⁻¹ = (τ (s i f) : G) :=
      congrArg Subtype.val (hws i f)
    rw [← hw]
    calc
      (c : G) * ((w i : G) * (τ f : G) * (w i : G)⁻¹) =
          c * (w i : G) * (τ f : G) * (w i : G)⁻¹ := by group
      _ = (w i : G) * c * (τ f : G) * (w i : G)⁻¹ := by rw [hc]
      _ = (w i : G) * (c * (τ f : G)) * (w i : G)⁻¹ := by group
  have hn : ∀ i, (w i : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro i
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      change (w i : G) * b * (w i : G)⁻¹ ∈ Bs
      rw [← hact i ⟨b, hb⟩]
      exact (r i ⟨b, hb⟩).2
    · intro hz
      refine ⟨((r i).symm ⟨z, hz⟩ : G), ((r i).symm ⟨z, hz⟩).2, ?_⟩
      change (w i : G) * ((r i).symm ⟨z, hz⟩ : G) * (w i : G)⁻¹ = z
      rw [← hact i ((r i).symm ⟨z, hz⟩), MulEquiv.apply_symm_apply]
  have hA : ∀ i, r i ∈ ggAutomizer X Bs := fun i =>
    mem_ggAutomizer_iff.mpr ⟨w i, (w i).2, hn i, hact i⟩
  have hS2 : ∀ i, (⊤ : Subgroup (S i)) ≤
      Subgroup.closure {z : S i | ∃ n : ℕ, z ^ (2 ^ n) = 1} := by
    intro i
    let wi : S i := ⟨w i, hwS i⟩
    have hri : ggConjAut Bs (hn i) = r i := by
      ext b
      exact (hact i b).symm
    have hwcard : (w i : G) ^ orderOf wi = 1 :=
      congrArg (fun z : S i => ((z : X) : G)) (pow_orderOf_eq_one wi)
    have hpow : r i ^ orderOf wi = 1 := by
      ext b
      have h := ggConjAut_pow_apply Bs (hn i) (orderOf wi) b
      rw [hri, hwcard] at h
      simpa using h
    have horder : orderOf (r i) = 2 :=
      orderOf_eq_prime (hr i).1 ((hr i).ne_one hp)
    have h2 : 2 ∣ Nat.card (S i) := by
      have hd : 2 ∣ orderOf wi := by
        rw [← horder]
        exact orderOf_dvd_of_pow_eq_one hpow
      exact hd.trans (orderOf_dvd_natCard wi)
    have ht := CFSG.SecondGeneration.oPrimeResidual_eq_top_of_isQuasisimple
      (p := 2) ((TableBSymp.isQuasisimple_iff (S i)).mp (hcomp i).2.2) h2
    change Subgroup.closure {z : S i | ∃ n : ℕ, z ^ (2 ^ n) = 1} = ⊤ at ht
    exact ht.ge
  have hSle : ∀ i, (S i).map X.subtype ≤ ggRankOneIn X Bs (r i) := by
    intro i
    let φ : S i →* G := X.subtype.comp (S i).subtype
    have hφ : φ.range ≤ X ⊓ Subgroup.centralizer (ggHyperplane Bs (r i) : Set G) := by
      rintro z ⟨u, rfl⟩
      refine ⟨(u : X).2, ?_⟩
      change ((u : X) : G) ∈ Subgroup.centralizer (ggHyperplane Bs (r i) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨⟨c, f⟩, rfl⟩ := κ.surjective b
      have hsf : s i f = f := by
        change r i (κ (c, f)) = κ (c, f) at hb
        dsimp only [r] at hb
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hb
        change κ (c, s i f) = κ (c, f) at hb
        exact congrArg Prod.snd (κ.injective hb)
      have ht : Commute (τ f) (u : X) :=
        Subgroup.mem_centralizer_iff.mp ((hcomp i).1 u.2) (τ f) ⟨f, hsf, rfl⟩
      have htG : Commute (τ f : G) ((u : X) : G) := congrArg Subtype.val ht.eq
      have hc : Commute (c : G) ((u : X) : G) :=
        (Subgroup.mem_centralizer_iff.mp (hCX c.2) (u : X) (u : X).2).symm
      change (κ (c, f) : G) * ((u : X) : G) = ((u : X) : G) * (κ (c, f) : G)
      rw [hκ]
      exact (hc.mul_left htG).eq
    have hle := OTwoGen.range_le_ggOTwoPrime φ hφ (hS2 i)
    simpa only [ggRankOneIn, φ, MonoidHom.range_comp, Subgroup.range_subtype] using hle
  have htop : (⨆ i, S i) = ⊤ := by
    apply top_unique
    calc
      ⊤ = ⨆ i, ⨆ (_ : i ≠ Classical.arbitrary ι), S i := (hgen _).symm
      _ ≤ ⨆ i, S i := iSup_le fun i => iSup_le fun _ => le_iSup S i
  apply le_antisymm
  · exact iSup_le fun r => iSup_le fun _ => iSup_le fun _ => ggRankOneIn_le X Bs r
  · calc
      X = (⨆ i, S i).map X.subtype := by rw [htop, Subgroup.map_top, Subgroup.range_subtype]
      _ ≤ _ := by
        rw [Subgroup.map_iSup]
        exact iSup_le fun i => (hSle i).trans
          (le_iSup_of_le (r i) (le_iSup_of_le (hA i) (le_iSup_of_le (hr i) le_rfl)))

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

theorem ggN2_iSup_rankOneIn_eq_of_selfCent
    {G : Type} [Group G] [Finite G] {Bs X C : Subgroup G}
    (hBs : IsElemAbelian 5 Bs)
    (hsc : ∀ {g : G}, g ∈ X → g ^ 5 = 1 →
      (∀ a ∈ Bs ⊓ X, g * a = a * g) → g ∈ Bs ⊓ X)
    (hX : GGCentralImage .POmegaMinus 4 2 X)
    (hCX : C ≤ Subgroup.centralizer (X : Set G))
    (hsplit : Bs = C ⊔ (Bs ⊓ X)) (hdisj : Disjoint C (Bs ⊓ X)) :
    (⨆ r : MulAut Bs, ⨆ (_ : r ∈ ggAutomizer X Bs),
      ⨆ (_ : GGIsReflection 5 r), ggRankOneIn X Bs r) = X := by
  classical
  let F := GaloisField 2 2
  let Q := quadMinus 4 F (minusCoeffs 2 2).1 (minusCoeffs 2 2).2
  have hbc : ∀ a : F, a ^ 2 + (minusCoeffs 2 2).1 * a + (minusCoeffs 2 2).2 ≠ 0 :=
    minusCoeffs_irr 2 2
  obtain ⟨hQ, -⟩ := regular_quadMinus (by norm_num : 4 ≤ 4) hbc
  obtain ⟨e⟩ := ggN2OrthDerived_model_of_centralImage hX
  let P : Subgroup X := (Bs ⊓ X).subgroupOf X
  let E : Subgroup ↥(orthDerived Q) := P.map e.toMonoidHom
  have hP : IsElemAbelian 5 P := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hBs.comm a.2.1 b.2.1))⟩⟩, ?_⟩
    intro a ha
    exact Subtype.ext (hBs.2 a ha.1)
  have hE : IsElemAbelian 5 E := TableB.isElemAbelian_map hP e.toMonoidHom
  have hF : Nat.card F = 4 := by simpa using GaloisField.card 2 2 (by decide)
  have hdim : finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 2 * 4 := by simp
  have hnative : GGTorusModelAt 5 E :=
    OmNsRootGen.ggTorusModelAt_of_selfCentralizing hQ Nat.prime_five (by decide)
      (by rw [hF]) (by rw [hF]) hdim (by decide) hE
      (ggF4N2Bstar_native_selfCent_of_inf hsc e)
  have hback : E.map e.symm.toMonoidHom = P := by
    ext z
    simp only [E, Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  have hmodel : GGTorusModelAt 5 P := by
    have hm := hnative.map e.symm
    rw [hback] at hm
    exact hm
  exact hmodel.iSup_rankOneIn_eq Nat.prime_five (by decide) hCX hsplit hdisj

theorem ggF4N2OmegaK_iSup_rankOneIn_eq
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    (⨆ r : MulAut Bs, ⨆ (_ : r ∈ ggAutomizer K Bs),
      ⨆ (_ : GGIsReflection 5 r), ggRankOneIn K Bs r) = K := by
  obtain ⟨hSplit, hDisj⟩ := ggF4N2OmegaK_Bstar_split hR hNbr hL hK
  have hYC : Subgroup.zpowers y ≤ Subgroup.centralizer (K : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hNbr.1]
    exact inf_le_right
  exact ggN2_iSup_rankOneIn_eq_of_selfCent hR.1.2.1.2.1
    (fun hg hg5 hc => ggF4N2OmegaK_inf_K_selfCent hR hNbr hL hK hg hg5 hc)
    hK hYC hSplit hDisj

section AlternateJoin

theorem ggF4N2OmegaK_le_sup_of_automizer_le
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K A : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .POmegaMinus 4 2 K)
    (hF4A : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer A Bs))
    (hKA : ggAutomizer K Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer A Bs) :
    K ≤ L ⊔ A := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨eNew, heNew⟩ := hF4A
  have hEl : IsElemAbelian 5 Bs := hR.1.2.1.2.1
  have hNT : GGNoTransvection 5 Bs := hR.2.2.2.1
  have hcfg : GGConfig 5 B Bs x L D J := hR.1
  obtain ⟨-, -, hxBs, -, hBs4⟩ := hcfg.tableB_facts
  have hB : B = Bs := ggF4N2_B_eq_Bs hR hL
  have hyBs : y ∈ Bs := hR.1.2.1.1 hNbr.1.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hy1 : y ≠ 1 := hNbr.1.2.2.1
  have hLsub : CFSG.Assembly.IsSubnormal L (Subgroup.centralizer ({x} : Set G)) :=
    hR.1.1.2.2.2.2.2.2.1.2.2.2.1.2.1
  have hKsub : CFSG.Assembly.IsSubnormal K (Subgroup.centralizer ({y} : Set G)) :=
    hNbr.1.2.2.2.2.1.2.1
  have hBL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    hcfg.bstar_le_normalizer (ggLNoncyclicInput_holds G 5 B x L hcfg.1)
  have hZL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 5 := by
    rw [hcfg.bstar_inf_centralizer_L, Nat.card_zpowers,
      orderOf_eq_prime (hEl.2 x hxBs) hx1]
  have hZK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = 5 := by
    have hz := inf_centralizer_eq_zpowers_of_sHat hNbr.1
    rw [hB] at hz
    rw [hz, Nat.card_zpowers, orderOf_eq_prime (hEl.2 y hyBs) hy1]
  obtain ⟨hqL, -, -, -⟩ := plusMember_facts_of_image ggInnerDiagMpInput_holds
    Nat.prime_five hEl hNT hBs4 (le_refl 2) (by norm_num) hL hR.2.2.1.1 hZL
  obtain ⟨hqK, -, -, -⟩ := plusMember_facts_of_image ggInnerDiagMpInput_holds
    Nat.prime_five hEl hNT hBs4 (le_refl 2) (by norm_num) hK
      (hR.2.2.1.2 y K hNbr) hZK
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres 5 (ggAutomizer L Bs ⊔ ggAutomizer A Bs)
      CoxeterMatrix.F₄ eNew := ⟨hF4W, heNew⟩
  have hWind : ggAutomizer L Bs ⊔ ggAutomizer A Bs ≤ ggInduced ⊤ Bs := by
    intro r hr
    have ht : r ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hr
    rw [ggAutomizer_eq] at ht
    exact ht
  have hWH : ggAutomizer L Bs ⊔ ggAutomizer A Bs ≤ ggAutomizer (L ⊔ A) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  obtain ⟨-, -, eL, -, hPL⟩ := ggF4N2Bstar_B3_frame hR hL
  have hfamily : GGOriginalRankOneFamily 5 L (L ⊔ A) Bs (ggCoxRefl CoxeterMatrix.F₄ eNew) :=
    ggOriginalRankOneFamily_of_b3 Nat.prime_five (by decide) hEl hNT hxBs hLsub hBL
      le_sup_left hWH hpres le_sup_left eL hPL.2 (Equiv.refl _) (fun _ _ => rfl)
      (fun r hr hrr => (hqL r hr hrr).1)
  have hnotG2 : ¬ ∃ e' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex e' := by
    rintro ⟨e', -⟩
    simpa using Fintype.card_congr e'
  have hKH : K ≤ L ⊔ A := by
    rw [← ggF4N2OmegaK_iSup_rankOneIn_eq hR hNbr hL hK]
    refine iSup_le fun r => iSup_le fun hrK => iSup_le fun hrr => ?_
    have hrW := hKA hrK
    obtain ⟨i, g, hg⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G 5 Bs
      Nat.prime_five (by decide) hEl hNT _ hWind (Fin 4) CoxeterMatrix.F₄ hF4W
      hnotG2 eNew heNew ⟨r, hrW⟩ hrr
    have hrR : r ∈ ggCoxRefl CoxeterMatrix.F₄ eNew := ⟨g, i, congrArg Subtype.val hg⟩
    obtain ⟨hSH, hSC, hBS, hrS, -⟩ := hfamily.1 r hrR
    have hyH : y ∈ ggHyperplane Bs r := by
      obtain ⟨n, hnK, -, hn⟩ := mem_ggAutomizer_iff.mp hrK
      refine Subgroup.mem_map.mpr ⟨⟨y, hyBs⟩, ?_, rfl⟩
      change r ⟨y, hyBs⟩ = ⟨y, hyBs⟩
      apply Subtype.ext
      rw [hn, Subgroup.mem_centralizer_singleton_iff.mp (hKsub.le hnK), mul_inv_cancel_right]
    have hKC := ggRankOneIn_isComponentOf_centralizer hyH hKsub (hqK r hrK hrr).1
    have hEq := eq_of_isComponentOf_of_mem_ggAutomizer hSC hKC
      (fun b hb h => eq_one_of_mul_self_eq_one_of_isElemAbelian (by decide) hEl hb h)
      hBS hrS (mem_ggAutomizer_ggRankOneIn hrK hrr.1) hrr.1 (hrr.ne_one Nat.prime_five)
    rw [hEq] at hSH
    exact hSH
  exact hKH

theorem ggF4N2Omega_sup_eq_of_automizer_inclusion
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K A : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .POmegaMinus 4 2 K)
    (hA : A ≤ L ⊔ K)
    (hF4A : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer A Bs))
    (hAA : ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    L ⊔ K = L ⊔ A := by
  classical
  obtain ⟨eOld, -⟩ := hF4
  obtain ⟨eNew, heNew⟩ := hF4A
  have hWle : ggAutomizer L Bs ⊔ ggAutomizer A Bs ≤
      ggAutomizer L Bs ⊔ ggAutomizer K Bs := sup_le le_sup_left hAA
  have hWcard := Nat.card_congr (eOld.symm.trans eNew).toEquiv
  have hWeq : ggAutomizer L Bs ⊔ ggAutomizer A Bs =
      ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    Subgroup.eq_of_le_of_card_ge hWle hWcard.le
  have hKA : ggAutomizer K Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer A Bs := by
    rw [hWeq]
    exact le_sup_right
  have hKH := ggF4N2OmegaK_le_sup_of_automizer_le hR hNbr hL hK ⟨eNew, heNew⟩ hKA
  exact le_antisymm (sup_le le_sup_left hKH) (sup_le le_sup_left hA)

end AlternateJoin

end CFSG.StandardType
