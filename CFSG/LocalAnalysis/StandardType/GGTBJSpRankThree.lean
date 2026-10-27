module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumGammaB3
public import CFSG.LocalAnalysis.StandardType.GGTBJSpAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTBJSpModelTwo
public import CFSG.LocalAnalysis.StandardType.GGTBJSpCount
public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGTBJSpRow
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyInputs
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearSplitA
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrGate

public section

namespace CFSG.StandardType
open CFSG CFSG.Open CFSG.Assembly TableB CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSp3_labelAll_adjoint {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel}
    (hs : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusLift p 3 R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
        (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K 3)), p ∣ Nat.card K - 1 ∧
          I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, hr, hpn⟩ := hs
  dsimp only at hr hpn htag
  subst r
  have step (Q : LargeEvenRawCont) (hQ : LargeEvenRecipeSymplectic 3 (2 ^ n) false Q) :
      LargeEvenRecipeSymplectic 3 (2 ^ n) false fun R _ I F =>
        Q R I F ∧ GGTorusLift p 3 R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (_ : CharP K 2) (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K 3)),
            p ∣ Nat.card K - 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have hch : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ,
      TableBSymp.ggTorusLift_symplectic hp hp2 hpq (by decide), K, inferInstance, inferInstance,
      hch, MulEquiv.refl _, hpq, TableBSymp.sp_I_subset_inn⟩
  rcases htag with h | h <;> subst t <;> intro Q hQ <;> exact step Q hQ


theorem ggTBJ_sp3_l_of_model
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y X)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (ψ : L →* LargeEvenProj (LargeEvenSpGroup K 3))
    (hA : GGTorusTBGroup p 3 (LargeEvenProj (LargeEvenSpGroup K 3))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K 3)))) L ψ (ggGamma L hN).range) :
    GGResSideDatum p Bs L J := by
  classical
  have hp : p.Prime := Fact.out
  have hcfg := hH.1
  have hnb := hH.2.2.2.2.1
  obtain ⟨_, hBs, hxBs, hLx, _⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC := hcfg.2.1.2.2.2
  have hNT := hH.2.2.2.1
  have hBsB : Bs = B := ggTBJ_sp_bstar_eq hp hp2 hcfg L hN hpq ψ hA
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hCompD : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hCompD.1.trans inf_le_left
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hnb.2.1, Subgroup.centralizer_closure]
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hl, _, hy⟩
      exact ⟨hl, hy⟩
    · rintro ⟨hl, hy⟩
      exact ⟨hl, Subgroup.mem_centralizer_iff.mp (hLx hl) x (by simp), hy⟩
  have hCompY : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rwa [hcent] at hCompD
  have hCompΓ : CFSG.Assembly.IsComponentOf (J.subgroupOf L) (ggFix (ggGamma L hN ⟨y, hyBs⟩)) := by
    have h := isComponentOf_subgroupOf_ggAutFixed (hN hyBs) hJL hCompY
    exact h
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hyNot : y ∉ Subgroup.zpowers x := (ggNbr_facts hcfg hnb).2.2.2.1
  have hv1 : ggGamma L hN ⟨y, hyBs⟩ ≠ 1 := by
    intro hv
    have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
      (ggGamma_eq_one_iff L hN ⟨y, hyBs⟩).mp hv
    have hyIn : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hyC⟩
    rw [inf_centralizer_eq_zpowers_of_sstar hp hS] at hyIn
    exact hyNot hyIn
  have hZle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤ B ⊓ Subgroup.centralizer (L : Set G) := by
    rintro g ⟨⟨hg, _⟩, hgc⟩
    exact ⟨hBsB ▸ hg, hgc⟩
  have hxOrder : orderOf x = p := orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p := by
    have h := Subgroup.card_le_of_le hZle
    rw [inf_centralizer_eq_zpowers_of_sstar hp hS, Nat.card_zpowers, hxOrder] at h
    exact h
  have hcount : p ^ 2 * Nat.card ↥((ggGamma L hN).range ⊓
      ⨅ j : J.subgroupOf L, MulAction.stabilizer (MulAut L) (j : L)) ≤
        Nat.card ↥(ggGamma L hN).range := ggTBJ_card_fixingJ_mul_le hcfg hN
  obtain ⟨b, f, hb, hrefl, hJΓ, hW⟩ := ggTBJ_sp_cover_rank_three_frame hp hp2 hpq ψ _ hA
    (ggGamma L hN ⟨y, hyBs⟩) ⟨⟨y, hyBs⟩, rfl⟩ hv1 ((isComponentOf_iff_open).mp hCompΓ) hcount
  exact ggResSideDatum_of_B3_gamma_frame hp2 hJL hBs hSC hNT hN hZ hW b hb f hrefl hJΓ


theorem ggTBJ_sp3_k_of_model
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y X) (hJK : J ≤ X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (ψ : X →* LargeEvenProj (LargeEvenSpGroup K 3))
    (hA : GGTorusTBGroup p 3 (LargeEvenProj (LargeEvenSpGroup K 3))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K 3)))) X ψ (ggGamma X hN).range) :
    GGResSideDatum p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  have hcfg := hH.1
  have hnb := hH.2.2.2.2.1
  obtain ⟨_, hBs, hxBs, _hLx, _⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC := hcfg.2.1.2.2.2
  have hNT := hH.2.2.2.1
  have hBsB : Bs = B := ggTBJ_sp_bstar_eq hp hp2 hcfg X hN hpq ψ hA
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxOrder : orderOf x = p := orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1
  have hyOrder : orderOf y = p := orderOf_eq_prime (hBs.2 y hyBs) hnb.1.2.2.1
  have hyNot : y ∉ Subgroup.zpowers x := (ggNbr_facts hcfg hnb).2.2.2.1
  have hxNot : x ∉ Subgroup.zpowers y := by
    intro hxIn
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hxIn
    have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hxOrder, hyOrder])
    exact hyNot (heq ▸ Subgroup.mem_zpowers y)
  have hv1 : ggGamma X hN ⟨x, hxBs⟩ ≠ 1 := by
    intro hv
    have hxC : x ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hN ⟨x, hxBs⟩).mp hv
    have hxB : x ∈ B := hS.2.1
    have hxIn : x ∈ B ⊓ Subgroup.centralizer (X : Set G) := ⟨hxB, hxC⟩
    rw [inf_centralizer_eq_zpowers_of_sHat hnb.1] at hxIn
    exact hxNot hxIn
  have hZle : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) ≤ B ⊓ Subgroup.centralizer (X : Set G) := by
    rintro g ⟨⟨hg, _⟩, hgc⟩
    exact ⟨hBsB ▸ hg, hgc⟩
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
    have h := Subgroup.card_le_of_le hZle
    rw [inf_centralizer_eq_zpowers_of_sHat hnb.1, Nat.card_zpowers, hyOrder] at h
    exact h
  have hCompX : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hCompΓ : CFSG.Assembly.IsComponentOf (J.subgroupOf X) (ggFix (ggGamma X hN ⟨x, hxBs⟩)) :=
    isComponentOf_subgroupOf_ggAutFixed (hN hxBs) hJK hCompX
  have hcount : p ^ 2 * Nat.card ↥((ggGamma X hN).range ⊓
      ⨅ j : J.subgroupOf X, MulAction.stabilizer (MulAut X) (j : X)) ≤
        Nat.card ↥(ggGamma X hN).range :=
    ggTBJ_card_fixingJ_mul_le_nbr_of_bstar_eq hcfg hnb hJK hBsB hN
  obtain ⟨b, f, hb, hrefl, hJΓ, hW⟩ := ggTBJ_sp_cover_rank_three_frame hp hp2 hpq ψ _ hA
    (ggGamma X hN ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hv1 ((isComponentOf_iff_open).mp hCompΓ) hcount
  exact ggResSideDatum_of_B3_gamma_frame hp2 hJK hBs hSC hNT hN hZ hW b hb f hrefl hJΓ


theorem ggTBJLeftOn_sp_three : GGTBJLeftOn ggTBJSpRankThreeLabel := by
  intro G _ _ p B Bs x L D J y X hH _ hMark _hXD
  classical
  have hp : p.Prime := Fact.out
  have hcfg := hH.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => ggTBJSpRankThreeLabel p lab)
    (fun lab _ hs => nbrC_labelAll_guard (ggSp3_labelAll_adjoint hp hp2 hs))
    (fun _ _ _ _ _ _ hP => hP.1) hMark
  obtain ⟨R, _, I, F, _, _, θ, ⟨_hs, hN, h3I⟩, hlift, K, _, _, _, e, hpq, hIinn⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN h3I hb
  have hTB := ggTorusTBGroup_of_L hcfg hXc θ hN hBsI hlift
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSpGroup K 3) →* MulAut (LargeEvenProj (LargeEvenSpGroup K 3))))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hIinn hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  exact Or.inl (ggTBJ_sp3_l_of_model hH hN hpq (e.toMonoidHom.comp (ggQuotHom θ)) hTB')

theorem ggTBJNbOn_sp_three (hI3 : GGNbrSubcomponentInput) : GGTBJNbrOn ggTBJSpRankThreeLabel := by
  intro G _ _ p B Bs x L D J y X hH _ hMark _hXD
  classical
  have hp : p.Prime := Fact.out
  have hcfg := hH.1
  have hnb := hH.2.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hJK : J ≤ X := hI3 G p B x L D J hH.1.1 hH.1.2.2 y X hnb
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => ggTBJSpRankThreeLabel p lab)
    (fun lab _ hs => nbrC_labelAll_guard (ggSp3_labelAll_adjoint hp hp2 hs))
    (fun _ _ _ _ _ _ hP => hP.1) hMark
  obtain ⟨R, _, I, F, _, _, θ, ⟨_hs, hN, h3I⟩, hlift, K, _, _, _, e, hpq, hIinn⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN h3I hb
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hXc θ hN hBsI hlift
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSpGroup K 3) →* MulAut (LargeEvenProj (LargeEvenSpGroup K 3))))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hIinn hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  exact Or.inl (ggTBJ_sp3_k_of_model hH hJK hN hpq (e.toMonoidHom.comp (ggQuotHom θ)) hTB')

theorem ggTBJOrderRest_of_restSpRankThree (hI3 : GGNbrSubcomponentInput)
    (h : GGTBJOrderRestSplitAUnitSpRankThreeInput) : GGTBJOrderRestUnitaryCoprimeF4Input :=
  GGTBJOrdinaryOutside.of_proved ggTBJLeftOn_sp_three (ggTBJNbOn_sp_three hI3) h


end CFSG.StandardType
