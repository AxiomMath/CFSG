module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xe
import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

namespace P22x

section Thompson

theorem isMax_of_mem_family {T : Subgroup G} {A : Subgroup ↥T}
    (hA : A ∈ CFSG.elemThompsonFamily ↥T 2) :
    CFSG.Quasithin.IsMaxElemAbelian T (A.map T.subtype) := by
  rw [CFSG.Quasithin.BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily,
    CFSG.Quasithin.BlueprintB2.subgroupOf_map_subtype_self]
  exact ⟨CFSG.Quasithin.BlueprintB2.map_subtype_le_self A, hA⟩

theorem le_jOf_of_isMax {T A : Subgroup G} (hA : CFSG.Quasithin.IsMaxElemAbelian T A) :
    A ≤ jOf T := by
  rw [show jOf T = CFSG.Quasithin.thompsonJ T from
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ T]
  exact le_iSup₂_of_le A hA le_rfl

theorem jOf_le_of_forall_isMax {T R : Subgroup G}
    (h : ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian T A → A ≤ R) : jOf T ≤ R := by
  rw [show jOf T = CFSG.Quasithin.thompsonJ T from
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ T]
  exact iSup₂_le fun A hA => h A hA

theorem exists_mem_elemThompsonFamily (T : Type) [Group T] [Finite T] :
    ∃ A : Subgroup T, A ∈ CFSG.elemThompsonFamily T 2 := by
  have hne : {r : ℕ | ∃ A : Subgroup T, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r}.Nonempty :=
    ⟨0, ⊥, CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp (isElemAbelian_bot 2),
      by simp⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup T, CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card T, ?_⟩
    rintro r ⟨A, -, hA⟩
    have h1 : 2 ^ r ≤ Nat.card T := hA ▸ Subgroup.card_le_card_group A
    exact (Nat.lt_two_pow_self.le).trans h1
  obtain ⟨A, hAel, hAcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨A, hAel, hAcard⟩

end Thompson

section DataSetup

theorem uc22p22xf_hV (D : Data G) : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T

theorem uc22p22xf_hel (D : Data G) : IsElemAbelian 2 D.U :=
  (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2

theorem uc22p22xf_UleT (D : Data G) : D.U ≤ D.T := by
  obtain ⟨hU1, -⟩ := uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  exact (hU1.trans inf_le_left).trans (uc22p22e_pCoreOf_le_T D)

theorem mbarImage_mono (M V : Subgroup G) {X Y : Subgroup G} (h : X ≤ Y) :
    mbarImage M V X ≤ mbarImage M V Y :=
  Subgroup.map_mono fun x hx => h hx

@[expose] def stabSub {X : Type} [Group X] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (w : W) : Subgroup X where
  carrier := {g | ρ g w = w}
  mul_mem' {a b} ha hb := by
    change ρ (a * b) w = w
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by
    change ρ 1 w = w
    rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    change ρ a⁻¹ w = w
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

variable {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod]

theorem card_module_eq (D : Data G) (e : ↥D.U ≃* Multiplicative Umod) :
    Nat.card Umod = Nat.card D.U :=
  (Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd)).symm

theorem relIndex_mul_card_fixSub (D : Data G) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ)
    {A' : Subgroup G} (hA'M : A' ≤ D.M) :
    (centralizer (A' : Set G)).relIndex D.U * Nat.card (fixSub ρ (mbarImage D.M D.U A')) =
      Nat.card Umod := by
  rw [fixSub_mbarImage (uc22p22xf_hV D) e ρ hc hA'M]
  have h1 : bsub e (centralizer (A' : Set G)) = bsub e (centralizer (A' : Set G) ⊓ D.U) := by
    rw [bsub_inf, bsub_V, inf_top_eq]
  rw [h1, card_bsub e (W := centralizer (A' : Set G) ⊓ D.U) inf_le_right, card_module_eq D e]
  exact Subgroup.relIndex_mul_card (H := centralizer (A' : Set G)) (K := D.U)

end DataSetup

end P22x

open P22x

theorem uc22p22xf_relIndex_le {T U A' : Subgroup G} (hUT : U ≤ T) (hU : IsElemAbelian 2 U)
    (hA : CFSG.Quasithin.IsMaxElemAbelian T A') :
    (centralizer (A' : Set G)).relIndex U ≤ (centralizer (U : Set G)).relIndex A' := by
  obtain ⟨hA'T, hA'el, hA'max⟩ := hA
  have hUc : U ≤ centralizer (U : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun v hv => hU.comm hv hu
  have hext : ∀ X : Subgroup G, A' ≤ X → X ≤ T → IsElemAbelian 2 X → X = A' := fun X hAX hXT hXel =>
    (Subgroup.eq_of_le_of_card_ge hAX (hA'max X hXT hXel)).symm
  have hCUle : centralizer (A' : Set G) ⊓ U ≤ A' := by
    have hX := hext (A' ⊔ (centralizer (A' : Set G) ⊓ U)) le_sup_left
      (sup_le hA'T (inf_le_right.trans hUT))
      (hA'el.sup_of_commute (hU.mono inf_le_right) fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 hb.1 a ha)
    exact le_sup_right.trans hX.le
  have hA₁U : ∀ a ∈ centralizer (U : Set G) ⊓ A', ∀ u ∈ U, a * u = u * a := fun a ha u hu =>
    (Subgroup.mem_centralizer_iff.1 ha.1 u hu).symm
  have hX₂el : IsElemAbelian 2 (centralizer (U : Set G) ⊓ A' ⊔ U) :=
    (hA'el.mono inf_le_right).sup_of_commute hU hA₁U
  have hX₂T : centralizer (U : Set G) ⊓ A' ⊔ U ≤ T := sup_le (inf_le_right.trans hA'T) hUT
  have hle := hA'max _ hX₂T hX₂el
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (centralizer (U : Set G) ⊓ A') U hA₁U
  have hinf : (centralizer (U : Set G) ⊓ A') ⊓ U = centralizer (A' : Set G) ⊓ U := by
    ext x
    constructor
    · rintro ⟨⟨_, hxA⟩, hxU⟩
      exact ⟨Subgroup.mem_centralizer_iff.2 fun h hh => hA'el.comm hh hxA, hxU⟩
    · rintro ⟨hxc, hxU⟩
      exact ⟨⟨hUc hxU, hCUle ⟨hxc, hxU⟩⟩, hxU⟩
  rw [hinf] at hprod
  have h1 := Subgroup.relIndex_mul_card (H := centralizer (U : Set G)) (K := A')
  have h2 := Subgroup.relIndex_mul_card (H := centralizer (A' : Set G)) (K := U)
  have hc_pos : 0 < Nat.card ↥(centralizer (A' : Set G) ⊓ U) := Nat.card_pos
  have ha_pos : 0 < Nat.card ↥(centralizer (U : Set G) ⊓ A') := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(centralizer (A' : Set G) ⊓ U) *
    Nat.card ↥(centralizer (U : Set G) ⊓ A')) ?_ (Nat.mul_pos hc_pos ha_pos)
  calc (centralizer (A' : Set G)).relIndex U *
        (Nat.card ↥(centralizer (A' : Set G) ⊓ U) * Nat.card ↥(centralizer (U : Set G) ⊓ A'))
      = Nat.card U * Nat.card ↥(centralizer (U : Set G) ⊓ A') := by rw [← h2]; ring
    _ = Nat.card ↥(centralizer (U : Set G) ⊓ A' ⊔ U) *
          Nat.card ↥(centralizer (A' : Set G) ⊓ U) := by rw [mul_comm, hprod]
    _ ≤ Nat.card A' * Nat.card ↥(centralizer (A' : Set G) ⊓ U) := Nat.mul_le_mul_right _ hle
    _ = (centralizer (U : Set G)).relIndex A' *
        (Nat.card ↥(centralizer (A' : Set G) ⊓ U) * Nat.card ↥(centralizer (U : Set G) ⊓ A')) := by
      rw [← h1]; ring

theorem uc22p22xf_noStrictOffender_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) :
    ∀ A : Subgroup ↥D.T, A ∈ CFSG.elemThompsonFamily ↥D.T 2 →
      (centralizer (D.U : Set G)).relIndex (A.map D.T.subtype) ≤
        (centralizer ((A.map D.T.subtype : Subgroup G) : Set G)).relIndex D.U := by
  classical
  intro A hA
  obtain ⟨m, Nb, hNb⟩ := h2 hH c
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hmax := isMax_of_mem_family hA
  have hA'M : A.map D.T.subtype ≤ D.M := hmax.1.trans D.sylowM.le
  have hA'N : A.map D.T.subtype ≤ proofN D :=
    (le_jOf_of_isMax hmax).trans (uc22p22e_jOf_le D.sylowM)
  have hAb : mbarImage D.M D.U (A.map D.T.subtype) ≤ mbarImage D.M D.U (proofN D) :=
    mbarImage_mono D.M D.U hA'N
  have hAbp : IsPGroup 2 (mbarImage D.M D.U (A.map D.T.subtype)) :=
    ((uc22p22e_isPGroup_of_elem hmax.2.1).comap_subtype (K := D.M)).map _
  have hno := d.not_strict_offender hAb hAbp
  rw [← relIndex_mul_card_fixSub D e ρ hc hA'M,
    uc22br4_card_mbarImage D.M D.U _ (uc22p22xf_hV D) hA'M] at hno
  exact Nat.le_of_mul_le_mul_right hno Nat.card_pos

theorem uc22p22xf_eleCU_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) : H1930 D → ∀ _ : Ctx22c D Ch, proofE D ≤ centralizer (D.U : Set G) := by
  intro hH c
  obtain ⟨A, hA⟩ := exists_mem_elemThompsonFamily ↥D.T
  exact uc22p22xa_omegaZJ_le_centralizer_of_not_strict D.sylowM.isPGroup (uc22p22xf_UleT D)
    (uc22p22xf_hel D) A hA (uc22p22xf_noStrictOffender_of D Ch h2 h3 h51 hH c A hA)

theorem uc22p22xf_imgEI_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) :
    H1930 D → ∀ _ : Ctx22c D Ch, ∀ (Umod : Type) [AddCommGroup Umod] [Module (ZMod 2) Umod]
      [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
      (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod),
      ConjModule D.M D.U e ρ →
      ∀ w ∈ modI D ρ, (∀ a ∈ mbarImage D.M D.U (jOf D.T), ρ a w - w ∈ modCI D ρ) →
        ∀ a ∈ mbarImage D.M D.U (jOf D.T), ρ a w = w := by
  classical
  intro hH c Umod _ _ _ e ρ hc w hw hwC
  obtain ⟨m, Nb, hNb⟩ := h2 hH c
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  have hJ : jOf D.T ≤ ((stabSub ρ w).comap
      (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype := by
    refine jOf_le_of_forall_isMax fun A' hmax => ?_
    have hA'M : A' ≤ D.M := hmax.1.trans D.sylowM.le
    have hA'J := le_jOf_of_isMax hmax
    have hA'N : A' ≤ proofN D := hA'J.trans (uc22p22e_jOf_le D.sylowM)
    have hAb : mbarImage D.M D.U A' ≤ mbarImage D.M D.U (proofN D) :=
      mbarImage_mono D.M D.U hA'N
    have hAbp : IsPGroup 2 (mbarImage D.M D.U A') :=
      ((uc22p22e_isPGroup_of_elem hmax.2.1).comap_subtype (K := D.M)).map _
    have hoff : Nat.card Umod ≤ Nat.card (mbarImage D.M D.U A') *
        Nat.card (fixSub ρ (mbarImage D.M D.U A')) := by
      rw [← relIndex_mul_card_fixSub D e ρ hc hA'M, uc22br4_card_mbarImage D.M D.U _ hV hA'M]
      exact Nat.mul_le_mul_right _
        (uc22p22xf_relIndex_le (uc22p22xf_UleT D) (uc22p22xf_hel D) hmax)
    obtain ⟨heq, -⟩ := d.offender_eq hAb hAbp hoff
    have hwF : w ∈ natF ρ (mbarImage D.M D.U (proofN D)) (mbarImage D.M D.U A') :=
      ⟨hw, fun a ha => hwC a (mbarImage_mono D.M D.U hA'J ha)⟩
    rw [heq] at hwF
    intro x hx
    exact ⟨⟨x, hA'M hx⟩, hwF.2 _ ⟨⟨x, hA'M hx⟩, hx, rfl⟩, rfl⟩
  intro a ha
  obtain ⟨y, hy, rfl⟩ := ha
  obtain ⟨z, hz, hzy⟩ := hJ hy
  have : z = y := Subtype.ext hzy
  subst this
  exact hz

end CFSG.LocalAnalysis.UniquenessCase.UC22
