module

public import CFSG.GroupTheory.InvolutionPair
public import CFSG.GroupTheory.TISylowLocal
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.Quasithin.Vol2.Ch10SecD32C
public import CFSG.Quasithin.Background.RonanE42SetS5
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Quasithin.Background.S1567BYE
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private abbrev perm5KleinSet (a b : Equiv.Perm (Fin 5)) : Finset (Equiv.Perm (Fin 5)) :=
  {1, a, b, a * b}

private abbrev Perm5KleinNormalizes (a b c e : Equiv.Perm (Fin 5)) : Prop :=
  (c * e * c⁻¹) * a * (c * e * c⁻¹)⁻¹ ∈ perm5KleinSet a b ∧
    (c * e * c⁻¹) * b * (c * e * c⁻¹)⁻¹ ∈ perm5KleinSet a b

private abbrev Perm5KleinGoodConj (a b c : Equiv.Perm (Fin 5)) : Prop :=
  c.sign = 1 ∧ (∀ e ∈ perm5KleinSet a b, e ≠ 1 → ¬Perm5KleinNormalizes a b c e) ∧
    (∀ e ∈ perm5KleinSet a b, e ≠ 1 → ¬Perm5KleinNormalizes a b c⁻¹ e)

private abbrev Perm5KleinHasGoodConj (a b : Equiv.Perm (Fin 5)) : Prop :=
  a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b →
    ∃ c : Equiv.Perm (Fin 5), Perm5KleinGoodConj a b c

private instance : DecidablePred (fun a : Equiv.Perm (Fin 5) =>
    ∀ b : Equiv.Perm (Fin 5), Perm5KleinHasGoodConj a b) :=
  fun a => Fintype.decidableForallFintype (p := fun b => Perm5KleinHasGoodConj a b)

private lemma perm5_klein_pair_check : ∀ a b : Equiv.Perm (Fin 5),
    a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b →
    ∃ c : Equiv.Perm (Fin 5), Perm5KleinGoodConj a b c := by
  decide +kernel

private lemma mem_perm5KleinSet_iff {a b x : Equiv.Perm (Fin 5)} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab1 : a ≠ b) :
    x ∈ perm5KleinSet a b ↔ x ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 5))) := by
  have hset : (Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5))) =
      {1, a, b, a * b} := CFSG.GroupTheory.coe_closure_pair_eq ha hb hab ha1 hb1 hab1
  change x ∈ perm5KleinSet a b ↔ x ∈ (Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 5))) : Set
    (Equiv.Perm (Fin 5)))
  rw [hset]
  simp [perm5KleinSet, eq_comm]

private lemma perm5_invol_conj_check : ∀ α : Equiv.Perm (Fin 5), α ^ 2 = 1 → α ≠ 1 →
    (∃ x : Equiv.Perm (Fin 5), x.sign = 1 ∧
        (α * (x * α * x⁻¹)) ^ 3 = 1 ∧ α * (x * α * x⁻¹) ≠ 1) ∧
      ∃ y : Equiv.Perm (Fin 5), y.sign = 1 ∧
        (α * (y * α * y⁻¹)) ^ 2 = 1 ∧ α * (y * α * y⁻¹) ≠ 1 := by
  decide +kernel +revert

theorem perm5_invol_conj_orders (α : Equiv.Perm (Fin 5)) (hα : α ^ 2 = 1) (hα1 : α ≠ 1) :
    (∃ x ∈ alternatingGroup (Fin 5), orderOf (α * (x * α * x⁻¹)) = 3) ∧
      ∃ y ∈ alternatingGroup (Fin 5), orderOf (α * (y * α * y⁻¹)) = 2 := by
  obtain ⟨⟨x, hxsign, hx3, hx3ne⟩, ⟨y, hysign, hy2, hy2ne⟩⟩ :=
    perm5_invol_conj_check α hα hα1
  constructor
  · exact ⟨x, Equiv.Perm.mem_alternatingGroup.mpr hxsign,
      orderOf_eq_prime (p := 3) hx3 hx3ne⟩
  · exact ⟨y, Equiv.Perm.mem_alternatingGroup.mpr hysign,
      orderOf_eq_prime (p := 2) hy2 hy2ne⟩

theorem perm5_klein_conj_normalizer (E : Subgroup (Equiv.Perm (Fin 5)))
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) : ∃ c ∈ alternatingGroup (Fin 5),
      (∀ e ∈ E, e ∈ normalizer (conjSubgroup E c : Set (Equiv.Perm (Fin 5))) → e = 1) ∧
      (∀ e ∈ E, e ∈ normalizer (conjSubgroup E c⁻¹ : Set (Equiv.Perm (Fin 5))) → e = 1) := by
  classical
  have : IsMulCommutative E := hE.1
  have hEcard : Nat.card E = 4 := h4
  have hnontriv : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; norm_num)
  obtain ⟨a, ha1⟩ := exists_ne (1 : E)
  have hlt : ({1, a} : Finset E).card < Fintype.card E := by
    have hpair : ({1, a} : Finset E).card = 2 := Finset.card_pair ha1.symm
    rw [hpair, ← Nat.card_eq_fintype_card, hEcard]
    norm_num
  obtain ⟨b, -, hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset E)) (t := Finset.univ) hlt
  have hb1 : b ≠ 1 := by intro h; exact hbnot (by simp [h])
  have hba : b ≠ a := by intro h; exact hbnot (by simp [h])
  let A : Equiv.Perm (Fin 5) := (a : Equiv.Perm (Fin 5))
  let B : Equiv.Perm (Fin 5) := (b : Equiv.Perm (Fin 5))
  have hA2 : A * A = 1 := by
    have := hE.2 A a.2
    simpa [A, pow_two] using this
  have hB2 : B * B = 1 := by
    have := hE.2 B b.2
    simpa [B, pow_two] using this
  have hAB : A * B = B * A := congrArg Subtype.val (mul_comm' a b)
  have hA1 : A ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hB1 : B ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hABne : A ≠ B := fun h => hba (Subtype.ext h.symm)
  have hcardC : Nat.card (Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin 5)))) = 4 :=
    CFSG.GroupTheory.card_closure_pair_eq_four hA2 hB2 hAB hA1 hB1 hABne
  have hCle : Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin 5))) ≤ E := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact a.2
    · exact b.2
  have hEeq : E = Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin 5))) :=
    (Subgroup.eq_of_le_of_card_ge hCle (le_of_eq (h4.trans hcardC.symm))).symm
  obtain ⟨c, hcsign, hc1, hc2⟩ := perm5_klein_pair_check A B hA2 hB2 hAB hA1 hB1 hABne
  have hconj : ∀ (H : Subgroup (Equiv.Perm (Fin 5))) (u e : Equiv.Perm (Fin 5)),
      e ∈ normalizer (conjSubgroup H u : Set (Equiv.Perm (Fin 5))) →
        u * e * u⁻¹ ∈ normalizer (H : Set (Equiv.Perm (Fin 5))) := by
    intro H u e he
    have h1 : conjSubgroup H u = H.map (MulAut.conj u⁻¹).toMonoidHom := rfl
    rw [h1, ← Subgroup.map_equiv_normalizer_eq H (MulAut.conj u⁻¹),
      Subgroup.mem_map_equiv] at he
    rwa [show (MulAut.conj u⁻¹).symm e = u * e * u⁻¹ by
      rw [MulEquiv.symm_apply_eq]
      simp [mul_assoc]] at he
  have hgen : ∀ g : Equiv.Perm (Fin 5),
      g ∈ normalizer (E : Set (Equiv.Perm (Fin 5))) ↔
        g * A * g⁻¹ ∈ E ∧ g * B * g⁻¹ ∈ E := by
    intro g
    constructor
    · intro hg
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg A).mp ?_,
        (Subgroup.mem_normalizer_iff.mp hg B).mp ?_⟩
      · rw [hEeq]
        exact Subgroup.subset_closure (by simp)
      · rw [hEeq]
        exact Subgroup.subset_closure (by simp)
    · rintro ⟨ha, hb⟩
      have hle : E.map (MulAut.conj g).toMonoidHom ≤ E := by
        rw [hEeq, MonoidHom.map_closure, Subgroup.closure_le]
        rintro x ⟨y, hy, rfl⟩
        rcases hy with rfl | rfl
        · simpa [hEeq, MulAut.conj_apply] using ha
        · simpa [hEeq, MulAut.conj_apply] using hb
      have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))
  refine ⟨c, Equiv.Perm.mem_alternatingGroup.mpr hcsign, ?_, ?_⟩
  · intro e heE heN
    have heN' := hconj E c e heN
    have hmem : e ∈ perm5KleinSet A B :=
      (mem_perm5KleinSet_iff hA2 hB2 hAB hA1 hB1 hABne).mpr (by rwa [← hEeq])
    have hgenN := (hgen (c * e * c⁻¹)).mp heN'
    have h1 : (c * e * c⁻¹) * A * (c * e * c⁻¹)⁻¹ ∈ perm5KleinSet A B :=
      (mem_perm5KleinSet_iff hA2 hB2 hAB hA1 hB1 hABne).mpr (by
        rw [← hEeq]
        exact hgenN.1)
    have h2 : (c * e * c⁻¹) * B * (c * e * c⁻¹)⁻¹ ∈ perm5KleinSet A B :=
      (mem_perm5KleinSet_iff hA2 hB2 hAB hA1 hB1 hABne).mpr (by
        rw [← hEeq]
        exact hgenN.2)
    by_cases he1 : e = 1
    · exact he1
    · exact absurd ⟨h1, h2⟩ (hc1 e hmem he1)
  · intro e heE heN
    have heN' := hconj E c⁻¹ e heN
    have hmem : e ∈ perm5KleinSet A B :=
      (mem_perm5KleinSet_iff hA2 hB2 hAB hA1 hB1 hABne).mpr (by rwa [← hEeq])
    have hgenN := (hgen (c⁻¹ * e * (c⁻¹)⁻¹)).mp heN'
    have h1 : (c⁻¹ * e * (c⁻¹)⁻¹) * A * (c⁻¹ * e * (c⁻¹)⁻¹)⁻¹ ∈ perm5KleinSet A B :=
      (mem_perm5KleinSet_iff hA2 hB2 hAB hA1 hB1 hABne).mpr (by
        rw [← hEeq]
        exact hgenN.1)
    have h2 : (c⁻¹ * e * (c⁻¹)⁻¹) * B * (c⁻¹ * e * (c⁻¹)⁻¹)⁻¹ ∈ perm5KleinSet A B :=
      (mem_perm5KleinSet_iff hA2 hB2 hAB hA1 hB1 hABne).mpr (by
        rw [← hEeq]
        exact hgenN.2)
    by_cases he1 : e = 1
    · exact he1
    · exact absurd ⟨h1, h2⟩ (hc2 e hmem he1)

private lemma fusionIsTI_of_isTI {X : Type} [Group X] [Finite X] {Q : Subgroup X}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI Q) : CFSG.Open.fusionIsTI Q := by
  intro g hg
  rcases hTI g with h | h
  · exact h
  · exfalso
    have hle : Q ≤ Q.map (MulAut.conj g).toMonoidHom := by
      calc Q = Q ⊓ Q.map (MulAut.conj g).toMonoidHom := h.symm
        _ ≤ Q.map (MulAut.conj g).toMonoidHom := inf_le_right
    have hcard : Nat.card (Q.map (MulAut.conj g).toMonoidHom) = Nat.card Q :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    exact hg (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

private lemma normalizer_center_le_normalizer_of_fusionIsTI {X : Type} [Group X] [Finite X]
    (Q : Sylow 2 X) (hTI : CFSG.Open.fusionIsTI (Q : Subgroup X))
    (hZ : (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype ≠ ⊥) :
    Subgroup.normalizer ((Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype : Set X) ≤
      Subgroup.normalizer (Q : Set X) := by
  intro n hn
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  have hzZ : (z : X) ∈ (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype := z.2
  have hzQ : (z : X) ∈ Q := Subgroup.map_subtype_le _ hzZ
  have hznZ : n * (z : X) * n⁻¹ ∈
      (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype :=
    (Subgroup.mem_normalizer_iff.mp hn (z : X)).mp hzZ
  have hznQ : n * (z : X) * n⁻¹ ∈ Q := Subgroup.map_subtype_le _ hznZ
  exact CFSG.Quasithin.Vol2.Ch10.SecD.mem_normalizer_of_fusionIsTI hTI hzQ
    (fun h => hz1 (Subtype.ext h)) hznQ

theorem k_U34KleinNormalizer_holds :
    ∀ (X : Type) [Group X] [Finite X], IsU3 X 2 →
      ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E = 4 →
        ∃ x : X, (∀ e ∈ E, e ∈ normalizer (conjSubgroup E x : Set X) → e = 1) ∧
          (∀ e ∈ E, e ∈ normalizer (conjSubgroup E x⁻¹ : Set X) → e = 1) := by
  intro X _ _ hX E hE h4
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  obtain ⟨eU⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel le_rfl hSC
  have hB0 : CFSG.Open.fusionBenderBorel (CFSG.Open.PSU3 2 2) (2 ^ 2) 3 :=
    CFSG.Open.bender_psu3_borel_full 2 (by norm_num)
  have hB : CFSG.Open.fusionBenderBorel X (2 ^ 2) 3 := hB0.map_mulEquiv eU.symm
  have hE2 : IsPGroup 2 E := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hE
  obtain ⟨Q, hEQ⟩ := hE2.exists_le_sylow
  obtain ⟨hSE, -, hZexp, hZcard, hQcard⟩ := hB Q
  let Z : Subgroup X := (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype
  have hZcard' : Nat.card Z = 4 := by
    dsimp [Z]
    rw [Subgroup.card_map_of_injective (Q : Subgroup X).subtype_injective, hZcard]
    norm_num
  have hZne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard'
    norm_num at hZcard'
  have hEcenter_le : E ≤ Z := by
    intro e he
    have heQ : e ∈ Q := hEQ he
    have heC : (⟨e, heQ⟩ : ↥Q) ∈ Subgroup.center (Q : Subgroup X) := by
      by_cases he1 : e = 1
      · subst he1
        exact Subgroup.one_mem _
      · refine Subgroup.mem_center_iff.mpr ?_
        intro q
        have heord : orderOf e = 2 :=
          orderOf_eq_prime (p := 2) (by simpa [pow_two] using hE.2 e he) he1
        have hcomm : Commute (q : X) e :=
          CFSG.Timmesfeld.Connectivity.commute_of_mem_sylow Q hSE heQ heord q.2
        exact Subtype.ext hcomm.eq
    exact Subgroup.mem_map.mpr ⟨⟨e, heQ⟩, heC, rfl⟩
  have hEcenter : E = Z :=
    Subgroup.eq_of_le_of_card_ge hEcenter_le (by rw [hZcard', h4])
  have hSE' : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder
      (Subgroup.normalizer (Q : Set X)) :=
    (CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded_iff _).mp hSE
  have hTI : CFSG.CGT.Timmesfeld75.IsTI (Q : Subgroup X) :=
    CFSG.GroupTheory.isTI_of_isStronglyEmbeddedOrder_normalizer hSE'
  have hTI' : CFSG.Open.fusionIsTI (Q : Subgroup X) := fusionIsTI_of_isTI hTI
  have hNcenter : Subgroup.normalizer (Z : Set X) ≤ Subgroup.normalizer (Q : Set X) :=
    normalizer_center_le_normalizer_of_fusionIsTI Q hTI' hZne
  have hcenter_le_Q : Z ≤ Q := Subgroup.map_subtype_le _
  obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top (Subgroup.normalizer (Q : Set X)) hSE.1
  have key : ∀ g : X, g ∉ Subgroup.normalizer (Q : Set X) →
      ∀ e ∈ E, e ∈ Subgroup.normalizer (conjSubgroup E g : Set X) → e = 1 := by
    intro g hg e heE heN
    by_contra he1
    have heord : orderOf e = 2 :=
      orderOf_eq_prime (p := 2) (by simpa [pow_two] using hE.2 e heE) he1
    have heCenter : e ∈ Z := hEcenter ▸ heE
    have heM : e ∈ Subgroup.normalizer (Q : Set X) := Subgroup.le_normalizer (hcenter_le_Q heCenter)
    have hgN : g * e * g⁻¹ ∈ Subgroup.normalizer (E : Set X) := by
      have h1 : conjSubgroup E g = E.map (MulAut.conj g⁻¹).toMonoidHom := rfl
      have h2 := heN
      rw [h1, ← Subgroup.map_equiv_normalizer_eq E (MulAut.conj g⁻¹),
        Subgroup.mem_map_equiv] at h2
      rwa [show (MulAut.conj g⁻¹).symm e = g * e * g⁻¹ by
        rw [MulEquiv.symm_apply_eq]
        simp [mul_assoc]] at h2
    have hgN' : g * e * g⁻¹ ∈ Subgroup.normalizer (Q : Set X) := by
      rw [hEcenter] at hgN
      exact hNcenter hgN
    have heMap : e ∈ (Subgroup.normalizer (Q : Set X)).map (MulAut.conj g⁻¹).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨g * e * g⁻¹, hgN', ?_⟩
      simp [mul_assoc]
    have hginv : g⁻¹ ∉ Subgroup.normalizer (Q : Set X) :=
      fun h => hg (by simpa using Subgroup.inv_mem _ h)
    have hodd := CFSG.Timmesfeld.Connectivity.odd_card_inf_map_conj hSE hginv
    exact (CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card hodd heord)
      (Subgroup.mem_inf.mpr ⟨heM, heMap⟩)
  refine ⟨x, key x hx, key x⁻¹ ?_⟩
  exact fun h => hx (by simpa using Subgroup.inv_mem _ h)

theorem mQuot_le_two_U34_inner_19 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hLn : (L.subgroupOf D.M).Normal) (hU3 : IsU3 (Bar2 L) 2)
    (hin : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T)) :
    E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) ≤ 2 := by
  classical
  obtain ⟨hAT, g, hAg, hmq⟩ := hA
  have hV0 : InCalV D.M V₀ := by
    rcases h.hyp.hyp125.1 with ⟨-, hbot⟩ | ⟨hV0, -⟩
    · exact absurd hbot (ne_bot_of_one_lt_mSub h.hyp.big)
    · exact hV0.1
  have hAeq : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV0.2.2.2.isPGroup g) hAg).1 hmq
  have hAel : IsElemAbelian 2 A :=
    hAeq ▸ E3.isElemAbelian_conjSubgroup hV0.2.2.2 g
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hAel.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have : IsMulCommutative A := hAel.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hMN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hMN
  have hTH : D.T ≤ L ⊔ D.T := le_sup_right
  have hTsyl : IsSylowIn 2 D.T (L ⊔ D.T) := TwelveShort.isSylowIn_of_le D hTH
  let Q : Subgroup G := pCoreOf 2 (L ⊔ D.T)
  have hQT : Q ≤ D.T :=
    CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hTH D.sylowM.isPGroup hTsyl.2.2
  have hpLQ : pCoreOf 2 L = L ⊓ Q :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hLQnorm : L ≤ normalizer (Q : Set G) :=
    (le_sup_left : L ≤ L ⊔ D.T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ D.T))
  have hTQnorm : D.T ≤ normalizer (Q : Set G) :=
    (le_sup_right : D.T ≤ L ⊔ D.T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ D.T))
  have hQleO2 : Q ≤ pCoreOf 2 (L ⊔ Q) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right ?_
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf (L ⊔ D.T))
    exact sup_le hLQnorm Subgroup.le_normalizer
  have hO2leQ : pCoreOf 2 (L ⊔ Q) ≤ Q := by
    refine CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 ?_ ?_
    · exact sup_le le_sup_left (hQT.trans le_sup_right)
    · refine sup_le ?_ ?_
      · exact (le_inf Subgroup.le_normalizer hLQnorm).trans
          (Subgroup.inf_normalizer_le_normalizer_sup L Q)
      · exact (le_inf hTL hTQnorm).trans
          (Subgroup.inf_normalizer_le_normalizer_sup L Q)
  have hO2K : pCoreOf 2 (L ⊔ Q) = Q := le_antisymm hO2leQ hQleO2
  have hAZ : A ≤ L ⊔ Q :=
    hin.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  have hmq' := CFSG.Quasithin.RonanE42.Gen.mQuot_le_pRank_of_le (K := L ⊔ Q) (Z := L ⊔ Q)
    (A := A) le_rfl hAZ hA2 hAc
  have hQL : Q.subgroupOf L = CFSG.pCore 2 ↥L := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 L, hpLQ, Subgroup.inf_subgroupOf_left]
  have hQK : Q.subgroupOf (L ⊔ Q) = CFSG.pCore 2 ↥(L ⊔ Q) := by
    have h1 : Q.subgroupOf (L ⊔ Q) = (pCoreOf 2 (L ⊔ Q)).subgroupOf (L ⊔ Q) := by
      rw [hO2K]
    exact h1.trans (CFSG.openPCoreOf_subgroupOf 2 (L ⊔ Q))
  have hQnormL : (Q.subgroupOf L).Normal := by
    rw [← Subgroup.inf_subgroupOf_left Q L]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (Subgroup.le_normalizer_inf Subgroup.le_normalizer hLQnorm)
  have hQnormK : (Q.subgroupOf (L ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hLQnorm Subgroup.le_normalizer)
  let e₁ : Bar2 L ≃* (↥L ⧸ Q.subgroupOf L) :=
    (QuotientGroup.quotientMulEquivOfEq hQL).symm
  let e₂ : (↥(L ⊔ Q) ⧸ Q.subgroupOf (L ⊔ Q)) ≃*
      (↥(L ⊔ Q) ⧸ CFSG.pCore 2 ↥(L ⊔ Q)) :=
    QuotientGroup.quotientMulEquivOfEq hQK
  let e : Bar2 L ≃* (↥(L ⊔ Q) ⧸ CFSG.pCore 2 ↥(L ⊔ Q)) :=
    e₁.trans ((QuotientGroup.quotientInfEquivProdNormalizerQuotient L Q hLQnorm).trans e₂)
  have hbar2 : CFSG.Open.pRank 2 (⊤ : Subgroup (Bar2 L)) = 2 := by
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.kU34Data_twoRank
      (X := Bar2 L) hU3
    have hbr : CFSG.pRank 2 ↥(⊤ : Subgroup (Bar2 L)) =
        CFSG.Open.pRank 2 (⊤ : Subgroup (Bar2 L)) :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(⊤ : Subgroup (Bar2 L))).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2)
          (⊤ : Subgroup (Bar2 L))).symm
    rwa [hbr] at h
  have hquot : CFSG.Open.pRank 2
      (⊤ : Subgroup (↥(L ⊔ Q) ⧸ CFSG.pCore 2 ↥(L ⊔ Q))) = 2 := by
    have he := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) e
    rw [← he]
    exact hbar2
  change E3.mQuot A (A ⊓ Q) ≤ 2
  rw [← hO2K]
  refine hmq'.trans ?_
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact hquot.le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
