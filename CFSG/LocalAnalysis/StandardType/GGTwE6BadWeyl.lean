module

public import CFSG.LocalAnalysis.StandardType.GGTwE6BadModel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
import CFSG.LocalAnalysis.StandardType.GGWeylESystem
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem existsUnique_overGamma_of_weylReflSet {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p)
    (hW : ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma K hN).range)) :
    ∀ a ∈ ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range,
      ∃! c : MulAut ↥Bs, c ∈ ggAutomizer K Bs ∧ GGOverGamma hN c a := by
  intro a ha
  obtain ⟨c, hcl, hover⟩ := exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW a ha
  have hCle : Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ} ≤
      ggAutomizer K Bs := (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1)
  refine ⟨c, ⟨hCle hcl, hover⟩, ?_⟩
  rintro d ⟨hd, hdover⟩
  have h1 : GGOverGamma hN (c⁻¹ * d) 1 := by
    have h := hover.inv.mul hdover
    rwa [inv_mul_cancel] at h
  have hκ : c⁻¹ * d ∈ ggAutomizer K Bs :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hCle hcl)) hd
  exact (inv_mul_eq_one.mp (eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hκ h1)).symm

private abbrev tw_WeylE6 : Type :=
  CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E6

private abbrev tw_simpleE6 (i : Fin 6) : tw_WeylE6 :=
  CFSG.LieType.Chevalley.simple CFSG.Blueprint.Chevalley.Tag.E6 i

private theorem tw_coxeterMatrixE6_eq :
    CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6) =
      CoxeterMatrix.E₆ :=
  coxeterMatrix_eq_of_ggIntCartan
    (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6)
    (by
      rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E6 =
          CartanMatrix.E 6 from CFSG.LieType.Chevalley.cartanE_eq 6]
      exact ggIntCartan_E₆)

private theorem tw_simple_braid (i j : Fin 6) :
    (tw_simpleE6 i * tw_simpleE6 j) ^ (CoxeterMatrix.E₆ i j) = 1 := by
  have h := CoxeterSystem.simple_mul_simple_pow
    (CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.Tag.E6) i j
  have hM : (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E6)) i j =
      CoxeterMatrix.E₆ i j :=
    congrFun (congrFun (congrArg CoxeterMatrix.M tw_coxeterMatrixE6_eq) i) j
  rw [← hM]
  exact h

private theorem tw_innerDiagOnLab {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) :
    GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L := by
  refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hM
  obtain ⟨⟨ht, hp3, hpn⟩, hBN, hBI⟩ := hP
  refine ⟨⟨ht, hp3, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, by rw [hp3]; exact hpn⟩), hBN, hBI⟩
  · rw [ht]; exact fun h => h
  · rw [ht]; decide

theorem ggTwE6Bad_weylOfType_of_rank
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs) {X : Subgroup G}
    (hX : GGInnerDiagOnLabel GGTwE6BadLabel p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hr : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range)
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p) :
    GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer X Bs) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨Φ, T, w, h⟩ := ggTwE6Bad_model_of_rank hcfg hX hN hr
  obtain ⟨-, _, _, hraw⟩ := hX
  obtain ⟨_, _, _, _, _, _, _, hP, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hp3, -⟩ := hP
  subst hp3
  have hW : ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range ≤
      Subgroup.closure (ggTorusReflSet 3 (ggGamma X hN).range) :=
    h.automizer_le_reflGen.trans
      (Subgroup.closure_mono (Set.range_subset_iff.mpr h.conjAut_mem_ggTorusReflSet))
  have hS3 : ∀ a ∈ ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range,
      ∃! c : MulAut ↥Bs, c ∈ ggAutomizer X Bs ∧ GGOverGamma hN c a :=
    existsUnique_overGamma_of_weylReflSet (K := X) hp hp2 hBs hSC hNoTr hN hZ hW
  have hexists : ∀ i : Fin 6, ∃ φ : MulAut ↥Bs,
      φ ∈ ggAutomizer X Bs ∧ GGIsReflection 3 φ ∧ GGOverGamma hN φ (h.conjAut i) := by
    intro i
    obtain ⟨g, hgL, hg, hrefl, hover⟩ :=
      exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN
        (h.torusWeylElt_w i) (h.conj_w_mem_normalizer i) (h.conjAut_isReflection i)
    exact ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgL hg, hrefl, hover⟩
  choose φ hφ using hexists
  have hφauto : ∀ i : Fin 6, φ i ∈ ggAutomizer X Bs := fun i => (hφ i).1
  have hφrefl : ∀ i : Fin 6, GGIsReflection 3 (φ i) := fun i => (hφ i).2.1
  have hφover : ∀ i : Fin 6, GGOverGamma hN (φ i) (h.conjAut i) := fun i => (hφ i).2.2
  let hAut : tw_WeylE6 →* MulAut ↥(ggGamma X hN).range :=
    { toFun := h.weylAut
      map_one' := h.weylAut_one
      map_mul' := h.weylAut_mul }
  have hweylpow : ∀ (u : tw_WeylE6) (k : ℕ), (h.weylAut u) ^ k = h.weylAut (u ^ k) :=
    fun u k => (map_pow hAut u k).symm
  have hrel : CoxeterMatrix.E₆.IsLiftable φ := by
    intro i j
    have hone : (h.conjAut i * h.conjAut j) ^ (CoxeterMatrix.E₆ i j) = 1 := by
      rw [← h.weylAut_simple i, ← h.weylAut_simple j, ← h.weylAut_mul,
        hweylpow (tw_simpleE6 i * tw_simpleE6 j) (CoxeterMatrix.E₆ i j),
        tw_simple_braid i j, h.weylAut_one]
    have hover : GGOverGamma hN ((φ i * φ j) ^ (CoxeterMatrix.E₆ i j))
        ((h.conjAut i * h.conjAut j) ^ (CoxeterMatrix.E₆ i j)) :=
      ((hφover i).mul (hφover j)).pow _
    rw [hone] at hover
    exact eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (hφauto i) (hφauto j)) _) hover
  have hGen : Subgroup.closure (Set.range φ) = ggAutomizer X Bs := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr hφauto)
    · intro c hc
      let A : Subgroup (MulAut ↥X) := (ggGamma X hN).range
      obtain ⟨g, hgL, hg, hcg⟩ := mem_ggAutomizer_iff.mp hc
      have hceq : c = ggConjAut Bs hg := by
        apply MulEquiv.ext
        intro b
        apply Subtype.ext
        rw [ggConjAut_apply]
        exact hcg b
      let a : MulAut ↥A := ggConjAut A (conj_mem_normalizer_range_ggGamma hN hgL hg)
      have ha : a ∈ ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A :=
        ggConjAut_mem_ggAutomizer (H := (MulAut.conj : ↥X →* MulAut ↥X).range)
          (MonoidHom.mem_range.mpr ⟨⟨g, hgL⟩, rfl⟩)
          (conj_mem_normalizer_range_ggGamma hN hgL hg)
      have hoverc : GGOverGamma hN c a := by
        rw [hceq]
        exact ggOverGamma_conjAut (hN := hN) hgL hg
      have haS : a ∈ Subgroup.closure (Set.range h.conjAut) := by
        rw [← h.automizer_eq_reflGen]
        exact ha
      have hclos : ∀ a' ∈ Subgroup.closure (Set.range h.conjAut),
          ∃ c' ∈ Subgroup.closure (Set.range φ), GGOverGamma hN c' a' := by
        intro a' ha'
        refine Subgroup.closure_induction
          (p := fun x _ => ∃ c' ∈ Subgroup.closure (Set.range φ), GGOverGamma hN c' x)
          ?_ ?_ ?_ ?_ ha'
        · rintro x ⟨i, rfl⟩
          exact ⟨φ i, Subgroup.subset_closure ⟨i, rfl⟩, hφover i⟩
        · exact ⟨1, Subgroup.one_mem _, GGOverGamma.one⟩
        · rintro x y _ _ ⟨cx, hcx, hox⟩ ⟨cy, hcy, hoy⟩
          exact ⟨cx * cy, Subgroup.mul_mem _ hcx hcy, hox.mul hoy⟩
        · rintro x _ ⟨cx, hcx, hox⟩
          exact ⟨cx⁻¹, Subgroup.inv_mem _ hcx, hox.inv⟩
      obtain ⟨c', hc', hover'⟩ := hclos a haS
      have hκ : c⁻¹ * c' ∈ ggAutomizer X Bs :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hc)
          ((Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr hφauto) hc')
      have h1 : GGOverGamma hN (c⁻¹ * c') 1 := by
        have hh := hoverc.inv.mul hover'
        rwa [inv_mul_cancel] at hh
      have heq : c⁻¹ * c' = 1 := eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hκ h1
      rwa [inv_mul_eq_one.mp heq]
  have hcard_lower : 51840 ≤ Nat.card ↥(ggAutomizer X Bs) := by
    let A : Subgroup (MulAut ↥X) := (ggGamma X hN).range
    let S : Subgroup (MulAut ↥A) := Subgroup.closure (Set.range h.conjAut)
    have hSA : S ≤ ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range A :=
      h.reflGen_le_automizer
    have hS_range : ∀ x ∈ S, ∃ u : tw_WeylE6, h.weylAut u = x := by
      intro x hx
      refine Subgroup.closure_induction
        (p := fun x _ => ∃ u : tw_WeylE6, h.weylAut u = x) ?_ ?_ ?_ ?_ hx
      · rintro x ⟨i, rfl⟩
        exact ⟨tw_simpleE6 i, h.weylAut_simple i⟩
      · exact ⟨1, h.weylAut_one⟩
      · rintro x y _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, h.weylAut_mul u v⟩
      · rintro x _ ⟨u, rfl⟩
        exact ⟨u⁻¹, h.weylAut_inv u⟩
    have hcardS : Nat.card S = 51840 := by
      have hbij : Function.Bijective
          (fun u : tw_WeylE6 => (⟨h.weylAut u, h.weylAut_mem u⟩ : S)) := by
        constructor
        · intro u v huv
          exact h.weylAut_injective (congrArg Subtype.val huv)
        · rintro ⟨x, hx⟩
          obtain ⟨u, hu⟩ := hS_range x hx
          exact ⟨u, Subtype.ext hu⟩
      have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
      rw [NoOffExc.card_weyl_E6] at hcard
      exact hcard.symm
    let f : S → ↥(ggAutomizer X Bs) := fun x =>
      ⟨Classical.choose (hS3 x.1 (hSA x.2)),
        (Classical.choose_spec (hS3 x.1 (hSA x.2))).1.1⟩
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have hox : GGOverGamma hN (f x).1 x.1 :=
        (Classical.choose_spec (hS3 x.1 (hSA x.2))).1.2
      have hoy : GGOverGamma hN (f y).1 y.1 :=
        (Classical.choose_spec (hS3 y.1 (hSA y.2))).1.2
      have hc : (f x).1 = (f y).1 := congrArg Subtype.val hxy
      have hoy' : GGOverGamma hN (f x).1 y.1 := by rw [hc]; exact hoy
      exact Subtype.ext (GGOverGamma.unique hox hoy')
    have hle := Nat.card_le_card_of_injective f hf_inj
    rw [hcardS] at hle
    exact hle
  have hE6card : Nat.card CoxeterMatrix.E₆.Group = 51840 := by
    rw [← tw_coxeterMatrixE6_eq]
    exact NoOffExc.card_weyl_E6
  let F : CoxeterMatrix.E₆.Group →* MulAut ↥Bs :=
    CoxeterMatrix.E₆.toCoxeterSystem.lift ⟨φ, hrel⟩
  have hFsimple : ∀ i : Fin 6, F (CoxeterMatrix.E₆.simple i) = φ i := by
    intro i
    rw [← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  have hFrange : F.range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map,
      ← CoxeterMatrix.E₆.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  have hFrange' : F.range = ggAutomizer X Bs := hFrange.trans hGen
  let F' : CoxeterMatrix.E₆.Group →* ↥(ggAutomizer X Bs) :=
    F.codRestrict (ggAutomizer X Bs) (by
      intro x
      rw [← hFrange']
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hF'surj : Function.Surjective F' := by
    intro y
    have hy : (y : MulAut ↥Bs) ∈ F.range := by rw [hFrange']; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hF'card : Nat.card CoxeterMatrix.E₆.Group ≤ Nat.card ↥(ggAutomizer X Bs) := by
    rw [hE6card]; exact hcard_lower
  have hF'bij : Function.Bijective F' :=
    @Function.Surjective.bijective_of_nat_card_le CoxeterMatrix.E₆.Group
      ↥(ggAutomizer X Bs) (Nat.finite_of_card_ne_zero (by rw [hE6card]; norm_num))
      F' hF'surj hF'card
  refine ⟨MulEquiv.ofBijective F' hF'bij, ?_⟩
  intro i
  show GGIsReflection 3 (F (CoxeterMatrix.E₆.simple i))
  rw [hFsimple i]
  exact hφrefl i

theorem ggTwE6Bad_weylOfType
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) :
    GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs) := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  have hM' : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L := tw_innerDiagOnLab hL
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
    ggTwE6ThreeBstarRankInput_holds G p B Bs x L D J hcfg hM' hN
  exact ggTwE6Bad_weylOfType_of_rank hcfg hHyp.2.2.2.1 hL hN hr hZ

theorem card_ggAutomizer_of_twE6Bad_nbr
    (hRig : GGLabelRigidInput) (hTE6R : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hK : GGInnerDiagOnLabel GGTwE6BadLabel p Bs K)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    Nat.card ↥(ggAutomizer K Bs) = 51840 := by
  have hbad : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGTwE6BadLabel p lab :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hbl⟩ := largeEvenMarking_exists_hasLabel hbad
  have hp3 : p = 3 := hbl.2.1
  subst hp3
  have hInnL : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    ggInnerDiagOnLab_of_twE6BadMarking hRig hInnK hbad
  obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    hTE6R G 3 B Bs x L D J hcfg rfl y K hnb hInnL hN
      (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)
  obtain ⟨e, -⟩ := ggTwE6Bad_weylOfType_of_rank hcfg hNoTr hK hN hr hZ
  rw [← Nat.card_congr e.toEquiv, card_coxeterE6_group]

end CFSG.StandardType

end
