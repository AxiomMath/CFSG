module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.IsomorphismTransport
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.Timmesfeld.Bridge.Asc72WreathConn
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Data.Finite.Perm
import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Plus
import TauCeti.Data.Fin.Basic
public import CFSG.Certificates.CosetTableShort
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.LocalAnalysis.WeakClosure81.SevenFour
import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.OddTranspositions.PartThree

open IsoTransport
open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open scoped commutatorElement

section WreathFactors

private abbrev P2 : Type := CFSG.Theory.Comparator.PSL2Model 2

private abbrev W2 : Type := L2Wreath 2 2

private def sw : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private theorem permAct_apply_two (σ : Equiv.Perm (Fin 2)) (h : Fin 2 → P2) (i : Fin 2) :
    (permAct (Fin 2) P2 σ) h i = h (σ⁻¹ i) := rfl

private theorem swapCore_zero : Equiv.swapCore (0 : Fin 2) 1 0 = 1 := by decide

private theorem swapCore_one : Equiv.swapCore (0 : Fin 2) 1 1 = 0 := by decide

private theorem commutator_P2 : commutator P2 = ⊤ := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup P2 := .isPSL2 2 le_rfl (MulEquiv.refl _)
  haveI : IsSimpleGroup P2 := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB
  obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator P2) with h | h
  · exfalso
    have hc : ⁅a, b⁆ ∈ commutator P2 := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hc
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hc)
  · exact h

private theorem commutator_base : commutator (Fin 2 → P2) = ⊤ := by
  have htop : (⊤ : Subgroup (Fin 2 → P2)) = Subgroup.pi Set.univ (fun _ => ⊤) :=
    (Subgroup.pi_top Set.univ).symm
  rw [commutator_def, htop, Subgroup.commutator_pi_pi_of_finite]
  have h : (fun _ : Fin 2 => ⁅(⊤ : Subgroup P2), ⊤⁆) = fun _ => (⊤ : Subgroup P2) := by
    funext i
    rw [show ⁅(⊤ : Subgroup P2), ⊤⁆ = commutator P2 from rfl, commutator_P2]
  rw [h, Subgroup.pi_top]

private theorem card_W2 : Nat.card W2 = 7200 := by
  have hbase : Nat.card (Fin 2 → P2) = 3600 := by
    rw [Nat.card_fun, CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by norm_num)]
    norm_num
  have h := Nat.card_congr
    (SemidirectProduct.equivProd (φ := permAct (Fin 2) P2))
  rw [h, Nat.card_prod, hbase, Nat.card_perm]
  norm_num

private noncomputable def factor (i : Fin 2) : Subgroup W2 := (SetupQ.coordHom 2 2 i).range

private theorem factor_iso (i : Fin 2) : Nonempty (factor i ≃* P2) :=
  ⟨(MonoidHom.ofInjective (SetupQ.coordHom_injective (f := 2) (n := 2) i)).symm⟩

private theorem factor_commute : ∀ a ∈ factor 0, ∀ b ∈ factor 1, Commute a b := by
  rintro a ⟨p, rfl⟩ b ⟨q, rfl⟩
  exact SetupQ.coordHom_commute (f := 2) (n := 2) (by decide : (0 : Fin 2) ≠ 1) p q

private theorem factor_inf : factor 0 ⊓ factor 1 = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  rw [Subgroup.mem_bot]
  have hpq : (MonoidHom.mulSingle (fun _ : Fin 2 => P2) 0) p =
      (MonoidHom.mulSingle (fun _ : Fin 2 => P2) 1) q :=
    SemidirectProduct.inl_injective (hp.trans hq.symm)
  have hp1 : p = 1 := by
    have := congrFun hpq 0
    simpa [MonoidHom.mulSingle_apply] using this
  subst hp1
  simpa using hp.symm

private theorem factor_sup_eq_base : factor 0 ⊔ factor 1 = l2WreathBase 2 2 := by
  rw [SetupQ.l2WreathBase_eq_iSup]
  apply le_antisymm
  · apply sup_le
    · exact le_iSup (fun i : Fin 2 => (SetupQ.coordHom 2 2 i).range) 0
    · exact le_iSup (fun i : Fin 2 => (SetupQ.coordHom 2 2 i).range) 1
  · apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right

private theorem commutator_eq_base :
    commutator W2 = (SemidirectProduct.inl : (Fin 2 → P2) →* W2).range := by
  apply le_antisymm
  · let S : Subgroup W2 := (SemidirectProduct.inr : Equiv.Perm (Fin 2) →* W2).range
    haveI : IsMulCommutative (Equiv.Perm (Fin 2)) := by
      rw [Equiv.Perm.isMulCommutative_iff_card_le_two]
      simp
    have hScomm : IsMulCommutative S := inferInstance
    have hsup : (SemidirectProduct.inl : (Fin 2 → P2) →* W2).range ⊔ S = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
        (SemidirectProduct.inl_left_mul_inr_right x).symm
      rw [hx]
      have hxbase : SemidirectProduct.inl x.left ∈
          (SemidirectProduct.inl : (Fin 2 → P2) →* W2).range := ⟨x.left, rfl⟩
      have hxinr : SemidirectProduct.inr x.right ∈ S := ⟨x.right, rfl⟩
      exact Subgroup.mul_mem_sup hxbase hxinr
    have hN : ((SemidirectProduct.inl : (Fin 2 → P2) →* W2).range).Normal := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hScomm
  · haveI : Group.IsPerfect (Fin 2 → P2) := Group.isPerfect_def.mpr commutator_base
    have hBperf : Group.IsPerfect (SemidirectProduct.inl : (Fin 2 → P2) →* W2).range :=
      Group.IsPerfect.range (f := (SemidirectProduct.inl : (Fin 2 → P2) →* W2))
    intro x hx
    have hx' : x ∈ ⁅(SemidirectProduct.inl : (Fin 2 → P2) →* W2).range,
        (SemidirectProduct.inl : (Fin 2 → P2) →* W2).range⁆ := by
      rw [Subgroup.isPerfect_iff.mp hBperf]
      exact hx
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top hx'

private theorem commutator_index : (commutator W2).index = 2 := by
  rw [commutator_eq_base, SemidirectProduct.range_inl_eq_ker_rightHom, Subgroup.index_ker]
  have hrange : (SemidirectProduct.rightHom : W2 →* Equiv.Perm (Fin 2)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective
  rw [hrange, Subgroup.card_top, Nat.card_perm]
  norm_num

private theorem factor_sup_eq_commutator : factor 0 ⊔ factor 1 = commutator W2 := by
  rw [factor_sup_eq_base, commutator_eq_base]
  rfl

private theorem conj_inl (h : Fin 2 → P2) (ρ : Equiv.Perm (Fin 2)) (f : Fin 2 → P2) :
    (SemidirectProduct.inl (φ := permAct (Fin 2) P2) h *
        SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ) *
      SemidirectProduct.inl (φ := permAct (Fin 2) P2) f *
        (SemidirectProduct.inl (φ := permAct (Fin 2) P2) h *
          SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ)⁻¹ =
      SemidirectProduct.inl (φ := permAct (Fin 2) P2)
        (h * (permAct (Fin 2) P2 ρ) f * h⁻¹) := by
  rw [show (SemidirectProduct.inl (φ := permAct (Fin 2) P2) h *
        SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ) *
      SemidirectProduct.inl (φ := permAct (Fin 2) P2) f *
        (SemidirectProduct.inl (φ := permAct (Fin 2) P2) h *
          SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ)⁻¹ =
      SemidirectProduct.inl (φ := permAct (Fin 2) P2) h *
        (SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ *
          SemidirectProduct.inl (φ := permAct (Fin 2) P2) f *
          (SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ)⁻¹) *
        (SemidirectProduct.inl (φ := permAct (Fin 2) P2) h)⁻¹ by group]
  rw [show (SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ)⁻¹ =
    SemidirectProduct.inr (φ := permAct (Fin 2) P2) ρ⁻¹ by simp]
  rw [← SemidirectProduct.inl_aut]
  rw [show (SemidirectProduct.inl (φ := permAct (Fin 2) P2) h)⁻¹ =
    SemidirectProduct.inl (φ := permAct (Fin 2) P2) h⁻¹ by simp]
  rw [← map_mul, ← map_mul]

private theorem conj_coordHom (y : W2) (hy : y.right = sw) (p : P2) :
    y * SetupQ.coordHom 2 2 0 p * y⁻¹ =
      SetupQ.coordHom 2 2 1 (y.left 1 * p * (y.left 1)⁻¹) := by
  obtain ⟨h, ρ⟩ := y
  change ρ = sw at hy
  subst hy
  rw [show (⟨h, sw⟩ : W2) = SemidirectProduct.inl h * SemidirectProduct.inr sw from
    (SemidirectProduct.inl_left_mul_inr_right _).symm]
  rw [SetupQ.coordHom_apply, conj_inl, SetupQ.coordHom_apply]
  congr 1
  funext k
  fin_cases k <;> simp [sw, permAct_apply_two, Pi.mulSingle, Equiv.swap,
      MonoidHom.mulSingle_apply, Function.update_self, Function.update_of_ne,
      swapCore_zero, swapCore_one]

private theorem factor_swap (y : W2) (hy : y ∉ commutator W2) :
    (factor 0).map (MulAut.conj y).toMonoidHom = factor 1 := by
  have hright : y.right ≠ 1 := by
    intro hr
    apply hy
    rw [commutator_eq_base]
    exact ⟨y.left, by ext <;> simp [hr]⟩
  have hrσ : y.right = sw := (TauCeti.perm_fin_two_eq_one_or_swap y.right).resolve_left hright
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨p, rfl⟩ := ha
    change y * SetupQ.coordHom 2 2 0 p * y⁻¹ ∈ factor 1
    rw [conj_coordHom y hrσ p]
    exact ⟨y.left 1 * p * (y.left 1)⁻¹, rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨SetupQ.coordHom 2 2 0 ((y.left 1)⁻¹ * q * y.left 1), ⟨_, rfl⟩, ?_⟩
    change y * SetupQ.coordHom 2 2 0 ((y.left 1)⁻¹ * q * y.left 1) * y⁻¹ =
      SetupQ.coordHom 2 2 1 q
    rw [conj_coordHom y hrσ]
    congr 1
    group

private theorem card_centralizer_mk (a : P2) :
    Nat.card (Subgroup.centralizer ({(⟨![a, a⁻¹], sw⟩ : W2)} : Set W2)) = 120 := by
  let w : W2 := ⟨![a, a⁻¹], sw⟩
  have hconj : IsConj (SemidirectProduct.inr (Equiv.swap 0 1) : W2) w :=
    WreathConn.isConj_two_mk a
  have hclass : conjugatesOf w =
      Set.range (fun b : P2 => (⟨![b, b⁻¹], sw⟩ : W2)) := by
    rw [← IsConj.conjugatesOf_eq hconj]
    ext y
    constructor
    · intro hy
      exact ⟨y.left 0, (WreathConn.eq_two_mk (f := 2) hy).symm⟩
    · rintro ⟨b, rfl⟩
      exact WreathConn.isConj_two_mk b
  have hinj : Function.Injective (fun b : P2 => (⟨![b, b⁻¹], sw⟩ : W2)) := by
    intro b c hbc
    have h := congrArg (fun z : W2 => z.left 0) hbc
    simpa using h
  have hncard : (conjugatesOf w).ncard = 60 := by
    rw [hclass, Set.ncard_range_of_injective hinj,
      CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by norm_num)]
    norm_num
  have hidx : (Subgroup.centralizer {w}).index = 60 := by
    rw [Subgroup.index_centralizer_eq_ncard, hncard]
  have hmul : Nat.card (Subgroup.centralizer {w}) * 60 = 7200 := by
    have h := Subgroup.card_mul_index (H := Subgroup.centralizer {w})
    change Nat.card (Subgroup.centralizer {w}) * (Subgroup.centralizer {w}).index =
      Nat.card W2 at h
    rw [hidx, card_W2] at h
    exact h
  have h2 : Nat.card (Subgroup.centralizer {w}) * 60 = 120 * 60 := by
    rw [hmul]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

private theorem card_centralizer_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hmap : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
    ext y
    constructor
    · intro hy
      have himage : e.toMonoidHom '' ({x} : Set G) = ({e x} : Set H) := by
        ext z
        simp
      simpa [himage] using Subgroup.map_centralizer_le_centralizer_image _ _ hy
    · intro hy
      obtain ⟨z, rfl⟩ := e.surjective y
      refine ⟨z, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      apply e.injective
      rw [map_mul, map_mul, hy]
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

theorem exists_factors_l2Wreath_two {Y : Type} [Group Y] (φ : Y ≃* L2Wreath 2 2) :
    ∃ A₁ A₂ : Subgroup Y, Nonempty (A₁ ≃* CFSG.Theory.Comparator.PSL2Model 2) ∧
      Nonempty (A₂ ≃* CFSG.Theory.Comparator.PSL2Model 2) ∧ (∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b) ∧
      A₁ ⊓ A₂ = ⊥ ∧ A₁ ⊔ A₂ = commutator Y ∧ (commutator Y).index = 2 ∧
      ∀ y : Y, y ∉ commutator Y → A₁.map (MulAut.conj y).toMonoidHom = A₂ := by
  refine ⟨(factor 0).map φ.symm.toMonoidHom, (factor 1).map φ.symm.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(φ.symm.subgroupMap (factor 0)).symm.trans (Classical.choice (factor_iso 0))⟩
  · exact ⟨(φ.symm.subgroupMap (factor 1)).symm.trans (Classical.choice (factor_iso 1))⟩
  · intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact (factor_commute a₀ ha₀ b₀ hb₀).map φ.symm
  · rw [← Subgroup.map_inf_eq (factor 0) (factor 1) φ.symm.toMonoidHom
      φ.symm.injective, factor_inf, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, factor_sup_eq_commutator,
      map_commutator_eq, MonoidHom.range_eq_top.mpr φ.symm.surjective]
    rfl
  · have hmapc : (commutator Y).map φ.toMonoidHom = commutator W2 := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr φ.surjective]
      rfl
    have hidxmap : (commutator Y).index = (commutator W2).index := by
      rw [← Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective
        (commutator Y), hmapc]
    rw [hidxmap, commutator_index]
  · intro y hy
    have hmapc : (commutator Y).map φ.toMonoidHom = commutator W2 := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr φ.surjective]
      rfl
    have hyW : φ y ∉ commutator W2 := by
      intro h
      apply hy
      rw [← hmapc] at h
      obtain ⟨z, hz, hzy⟩ := h
      rwa [φ.injective hzy] at hz
    have hconjmap : ((factor 0).map φ.symm.toMonoidHom).map
          (MulAut.conj y).toMonoidHom =
        ((factor 0).map (MulAut.conj (φ y)).toMonoidHom).map φ.symm.toMonoidHom := by
      simpa using conj_map φ.symm (factor 0) (φ y)
    rw [hconjmap, factor_swap (φ y) hyW]

theorem card_centralizer_l2Wreath_two {Y : Type} [Group Y] [Finite Y] (φ : Y ≃* L2Wreath 2 2)
    {Λ : Set Y} (hS : Setup Y Λ) {x : Y} (hx : x ∈ Λ) :
    Nat.card (Subgroup.centralizer {x}) = 120 := by
  have h1 : ∀ d ∈ Λ, φ d ≠ 1 := fun d hd h =>
    hS.oddT.ne_one hd (φ.injective (h.trans φ.map_one.symm))
  have hS' : Setup W2 (φ '' Λ) := hS.map φ.toMonoidHom φ.surjective h1
  have hx' : φ x ∈ φ '' Λ := Set.mem_image_of_mem φ hx
  have hr : (φ x).right ≠ 1 := CFSG.OddTranspositions.PartFour.right_ne_one_of_mem hS φ hx
  have hww : φ x * φ x = 1 := by
    have h2 : orderOf (φ x) = 2 := hS'.oddT.1 (φ x) hx'
    have h := pow_orderOf_eq_one (φ x)
    rwa [h2, pow_two] at h
  obtain ⟨hrσ, hleft⟩ :=
    CFSG.OddTranspositions.PartFour.eq_mk_of_mul_self_eq_one hww hr
  have hform : φ x = (⟨![(φ x).left 0, ((φ x).left 0)⁻¹], sw⟩ : W2) := by
    refine SemidirectProduct.ext ?_ ?_
    · funext i
      fin_cases i <;> simp [hleft]
    · simpa [sw] using hrσ
  rw [← card_centralizer_mulEquiv φ x, hform, card_centralizer_mk]

end WreathFactors

end CFSG.OddTranspositions.PartThree
