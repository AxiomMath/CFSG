module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonPSL2Partition
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Transfer

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic torus normalizers for Dickson's classification

This module isolates the maximal cyclic representatives and reflection/dihedral
normalizer package used in Huppert II.8.22.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u v

public theorem huppert_II_8_22_maximal_cyclic_representatives
    {H : Type u} [Group H] [Finite H] (p : ℕ) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) := by
  classical
  let : MulAction H (Subgroup H) :=
    { smul := fun g W => W.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro W
        change W.map (MulAut.conj (1 : H)).toMonoidHom = W
        have h :
            (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by
          ext x
          simp
        rw [h, Subgroup.map_id]
      mul_smul := by
        intro g h W
        change W.map (MulAut.conj (g * h)).toMonoidHom =
          (W.map (MulAut.conj h).toMonoidHom).map
            (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have hcyclic_smul (g : H) (W : Subgroup H)
      (hW : IsCyclic W) : IsCyclic ↥(g • W : Subgroup H) := by
    let e : W ≃* ↥(g • W : Subgroup H) :=
      (MulAut.conj g).subgroupMap W
    let : IsCyclic W := hW
    rcases IsCyclic.exists_zpow_surjective (G := W) with ⟨x, hx⟩
    apply IsCyclic.mk
    refine ⟨e x, ?_⟩
    intro y
    obtain ⟨n, hn⟩ := hx (e.symm y)
    refine ⟨n, ?_⟩
    change (e x) ^ n = y
    rw [← map_zpow]
    simpa using congrArg e hn
  have hcard_smul (g : H) (W : Subgroup H) :
      Nat.card ↥(g • W : Subgroup H) = Nat.card W := by
    let e : W ≃* ↥(g • W : Subgroup H) :=
      (MulAut.conj g).subgroupMap W
    exact (Nat.card_congr e.toEquiv).symm
  have helig_smul (g : H) (W : Subgroup H)
      (hW : IsCyclic W ∧ 1 < Nat.card W ∧
        Nat.Coprime p (Nat.card W) ∧
        ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) :
      IsCyclic ↥(g • W : Subgroup H) ∧
        1 < Nat.card ↥(g • W : Subgroup H) ∧
        Nat.Coprime p (Nat.card ↥(g • W : Subgroup H)) ∧
        ∀ V : Subgroup H, IsCyclic V →
          (g • W : Subgroup H) ≤ V → V = (g • W : Subgroup H) := by
    refine ⟨hcyclic_smul g W hW.1, ?_, ?_, ?_⟩
    · simpa [hcard_smul g W] using hW.2.1
    · simpa [hcard_smul g W] using hW.2.2.1
    · intro V hV hle
      have hback_cyclic : IsCyclic ↥(g⁻¹ • V : Subgroup H) :=
        hcyclic_smul g⁻¹ V hV
      have hback_le : W ≤ (g⁻¹ • V : Subgroup H) := by
        have hmap := Subgroup.map_mono
          (f := (MulAut.conj g⁻¹).toMonoidHom) hle
        change (g⁻¹ • (g • W) : Subgroup H) ≤
          (g⁻¹ • V : Subgroup H) at hmap
        simpa using hmap
      have heq : (g⁻¹ • V : Subgroup H) = W :=
        hW.2.2.2 (g⁻¹ • V : Subgroup H) hback_cyclic hback_le
      have hfront := congrArg (fun T : Subgroup H => g • T) heq
      simpa using hfront
  let C := {W : Subgroup H //
    IsCyclic W ∧ 1 < Nat.card W ∧ Nat.Coprime p (Nat.card W) ∧
      ∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W}
  let : MulAction H C :=
    { smul := fun g W =>
        ⟨g • (W : Subgroup H), helig_smul g W W.property⟩
      one_smul := by
        intro W
        apply Subtype.ext
        exact one_smul H (W : Subgroup H)
      mul_smul := by
        intro g h W
        apply Subtype.ext
        exact mul_smul g h (W : Subgroup H) }
  let O := Quotient (MulAction.orbitRel H C)
  let : Fintype O := Fintype.ofFinite O
  let r := Fintype.card O
  let e : Fin r ≃ O := (Fintype.equivFin O).symm
  let Z : Fin r → Subgroup H := fun i => ((e i).out : C)
  refine ⟨r, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((e i).out : C).property.1
  · intro i
    exact ((e i).out : C).property.2.1
  · intro i
    exact ((e i).out : C).property.2.2.1
  · intro i W hW hle
    exact ((e i).out : C).property.2.2.2 W hW hle
  · intro W hW hWcard hWcop hWmax
    let c : C := ⟨W, hW, hWcard, hWcop, hWmax⟩
    let q : O := Quotient.mk (MulAction.orbitRel H C) c
    let i : Fin r := e.symm q
    have heq : e i = q := by simp [i]
    have hquot :
        Quotient.mk (MulAction.orbitRel H C) (e i).out =
          Quotient.mk (MulAction.orbitRel H C) c := by
      rw [Quotient.out_eq, heq]
    have hrel :
        (e i).out ∈ MulAction.orbit H c :=
      Quotient.exact hquot
    rcases MulAction.mem_orbit_iff.mp hrel with ⟨g, hg⟩
    refine ⟨i, g⁻¹, ?_⟩
    have hgval :
        (g • W : Subgroup H) = Z i := by
      have hg' := congrArg Subtype.val hg
      change (g • W : Subgroup H) = ((e i).out : C) at hg'
      exact hg'
    have hback :=
      congrArg (fun T : Subgroup H => g⁻¹ • T) hgval
    change W = (g⁻¹ • Z i : Subgroup H)
    simpa using hback
  · intro i j g hg
    let ci : C := (e i).out
    let cj : C := (e j).out
    have hgc : g • ci = cj := by
      apply Subtype.ext
      exact hg
    have hrel : ci ∈ MulAction.orbit H cj := by
      rw [MulAction.mem_orbit_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [← hgc]
      simp
    have hq : e i = e j := by
      calc
        e i = Quotient.mk (MulAction.orbitRel H C) ci :=
          (Quotient.out_eq (e i)).symm
        _ = Quotient.mk (MulAction.orbitRel H C) cj :=
          Quotient.sound hrel
        _ = e j := Quotient.out_eq (e j)
    exact e.injective hq

public theorem cyclic_le_unique_partition_family
    {G : Type*} [Group G]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    {x : G} (hx : x ≠ 1)
    {T V : Subgroup G}
    (hxT : x ∈ T) (hTfamily : Family T)
    (hxV : x ∈ V) (hVcyclic : IsCyclic V) :
    V ≤ T := by
  let : IsCyclic V := hVcyclic
  rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
  have hv_ne : (v : G) ≠ 1 := by
    intro hv_one
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v ^ n : V) = ⟨x, hxV⟩ := hn
    have hnval' := congrArg Subtype.val hnval
    change ((v : G) ^ n) = x at hnval'
    simp [hv_one] at hnval'
    exact hx hnval'.symm
  obtain ⟨Tv, hvTv, _hTv_unique⟩ := hpartition (v : G) hv_ne
  have hxTv : x ∈ Tv := by
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v : G) ^ n = x := congrArg Subtype.val hn
    have hvpow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
    rwa [hnval] at hvpow
  have hTvT : Tv = T :=
    (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
  intro y hyV
  obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
  have hnval : (v : G) ^ n = y := congrArg Subtype.val hn
  have hypow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
  rw [hTvT, hnval] at hypow
  exact hypow

private theorem equiv_torus_reflection_data
    {G : Type u} [Group G] [Finite G]
    (T0 : Subgroup G) (w0 : G)
    (hcyclic0 : IsCyclic T0)
    (hw0_normalizer : w0 ∈ Subgroup.normalizer (T0 : Set G))
    (hw0_not_mem : w0 ∉ T0) (hw0_sq : w0 * w0 = 1)
    (hw0_inv : ∀ t : G, t ∈ T0 → w0 * t * w0⁻¹ = t⁻¹)
    (hcard0 : Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) =
      2 * Nat.card T0)
    (hnormalizer0 : ∀ R : Subgroup G, R ≤ T0 → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T0 ⊔ Subgroup.zpowers w0)
    (e : G ≃* G) :
    let T := T0.map e.toMonoidHom
    let w := e w0
    IsCyclic T ∧
      w ∈ Subgroup.normalizer (T : Set G) ∧
      w ∉ T ∧
      w * w = 1 ∧
      (∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (T ⊔ Subgroup.zpowers w : Subgroup G) = 2 * Nat.card T ∧
      ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w := by
  dsimp only
  have hcyclic : IsCyclic (T0.map e.toMonoidHom) := by
    let : IsCyclic T0 := hcyclic0
    exact isCyclic_of_surjective (e.subgroupMap T0).toMonoidHom
      (e.subgroupMap T0).surjective
  have hw_normalizer :
      e w0 ∈ Subgroup.normalizer (T0.map e.toMonoidHom : Set G) := by
    have hw_map : e w0 ∈
        (Subgroup.normalizer (T0 : Set G)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hw0_normalizer
    rwa [Subgroup.map_equiv_normalizer_eq T0 e] at hw_map
  have hw_not_mem : e w0 ∉ T0.map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    simpa using hw0_not_mem
  have hw_sq : e w0 * e w0 = 1 := by
    simpa using congrArg e hw0_sq
  have hw_inv : ∀ t : G, t ∈ T0.map e.toMonoidHom →
      e w0 * t * (e w0)⁻¹ = t⁻¹ := by
    intro t ht
    have ht0 : e.symm t ∈ T0 :=
      Subgroup.mem_map_equiv.mp ht
    simpa using congrArg e (hw0_inv (e.symm t) ht0)
  have hcard : Nat.card
      (T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) : Subgroup G) =
      2 * Nat.card (T0.map e.toMonoidHom) := by
    have heq : (T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom =
        T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) := by
      simpa using
        (Subgroup.map_sup T0 (Subgroup.zpowers w0) e.toMonoidHom).trans
          (congrArg (fun K : Subgroup G => T0.map e.toMonoidHom ⊔ K)
            (MonoidHom.map_zpowers e.toMonoidHom w0))
    calc
      Nat.card (T0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) : Subgroup G) =
          Nat.card ((T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom) :=
        congrArg (fun K : Subgroup G => Nat.card K) heq.symm
      _ = Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) := by
        rw [Subgroup.card_map_of_injective e.injective]
      _ = 2 * Nat.card (T0 : Subgroup G) := hcard0
      _ = 2 * Nat.card (T0.map e.toMonoidHom) := by
        rw [Subgroup.card_map_of_injective e.injective]
  refine ⟨hcyclic, hw_normalizer, hw_not_mem, hw_sq, hw_inv, hcard, ?_⟩
  intro R hR_le hR_ne
  let R0 : Subgroup G := R.map e.symm.toMonoidHom
  have hR0_le : R0 ≤ T0 := by
    intro x hx
    have hex : e x ∈ R := by
      change x ∈ R.map e.symm.toMonoidHom at hx
      rwa [Subgroup.mem_map_equiv] at hx
    have hexT : e x ∈ T0.map e.toMonoidHom := hR_le hex
    rw [Subgroup.mem_map_equiv] at hexT
    simpa using hexT
  have hR0_ne : R0 ≠ ⊥ := by
    intro hR0
    apply hR_ne
    apply (Subgroup.map_eq_bot_iff_of_injective R
      (f := e.symm.toMonoidHom) e.symm.injective).mp
    exact hR0
  have hR0_map : R0.map e.toMonoidHom = R := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := R0) (e := e)).mp
    rfl
  have hmap := congrArg
    (fun K : Subgroup G => K.map e.toMonoidHom)
    (hnormalizer0 R0 hR0_le hR0_ne)
  change (Subgroup.normalizer (R0 : Set G)).map e.toMonoidHom =
    (T0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom at hmap
  rw [Subgroup.map_equiv_normalizer_eq R0 e, hR0_map,
    Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
  exact hmap

private theorem conjugate_torus_reflection_data
    {G : Type u} [Group G] [Finite G]
    (T0 : Subgroup G) (w0 : G)
    (hcyclic0 : IsCyclic T0)
    (hw0_normalizer : w0 ∈ Subgroup.normalizer (T0 : Set G))
    (hw0_not_mem : w0 ∉ T0) (hw0_sq : w0 * w0 = 1)
    (hw0_inv : ∀ t : G, t ∈ T0 → w0 * t * w0⁻¹ = t⁻¹)
    (hcard0 : Nat.card (T0 ⊔ Subgroup.zpowers w0 : Subgroup G) =
      2 * Nat.card T0)
    (hnormalizer0 : ∀ R : Subgroup G, R ≤ T0 → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T0 ⊔ Subgroup.zpowers w0)
    (g : G) :
    let T := T0.map (MulAut.conj g).toMonoidHom
    let w := MulAut.conj g w0
    IsCyclic T ∧
      w ∈ Subgroup.normalizer (T : Set G) ∧
      w ∉ T ∧
      w * w = 1 ∧
      (∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (T ⊔ Subgroup.zpowers w : Subgroup G) = 2 * Nat.card T ∧
      ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w := by
  exact equiv_torus_reflection_data T0 w0 hcyclic0 hw0_normalizer hw0_not_mem
    hw0_sq hw0_inv hcard0 hnormalizer0 (MulAut.conj g)

public theorem relIndex_le_two_of_inter_eq
    {G : Type u} [Group G] [Finite G]
    (T B N A : Subgroup G)
    (hB_le : B ≤ N) (hinter : T ⊓ B = A)
    (hindex : T.relIndex N = 2) :
    A.relIndex B ≤ 2 := by
  rw [← hinter, Subgroup.inf_relIndex_right]
  rw [← hindex]
  exact Subgroup.relIndex_le_of_le_right hB_le (by
    rw [Subgroup.relIndex]
    exact Nat.card_pos.ne')

public theorem relIndex_eq_two_of_card_eq_two_mul
    {G : Type u} [Group G] [Finite G]
    (T N : Subgroup G) (hT_le : T ≤ N)
    (hcard : Nat.card N = 2 * Nat.card T) :
    T.relIndex N = 2 := by
  rw [Subgroup.relIndex]
  have hsubcard : Nat.card (T.subgroupOf N) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le).toEquiv
  have hmul := (T.subgroupOf N).index_mul_card
  rw [hsubcard, hcard] at hmul
  exact Nat.mul_right_cancel Nat.card_pos hmul

private theorem mulEquiv_dihedral_of_cyclic_reflection
    {G : Type u} [Group G] [Finite G]
    (C : Subgroup G) (hC : IsCyclic C) (w : G)
    (hw_not_mem : w ∉ C) (hw_sq : w * w = 1)
    (hw_inv : ∀ c : G, c ∈ C → w * c * w⁻¹ = c⁻¹)
    (hindex : C.index = 2) :
    Nonempty (G ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C :=
    zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → G := fun i =>
    (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C :=
    (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) :
      rot (i + j) = rot i * rot j := by
    exact congrArg Subtype.val (e.map_mul
      (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) :
      rot (-i) = (rot i)⁻¹ := by
    exact congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := by
    exact congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) :
      w * rot i = rot (-i) * w := by
    calc
      w * rot i = (w * rot i * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hw_inv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) :
      rot i * w = w * rot (-i) := by
    calc
      rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* G :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc
            w * rot (j - i) = w * rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc
            rot (j - i) = rot (-i + j) := by
              rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * rot i) * (w * rot j) := by
              calc
                rot (-i) * rot j = (w * w) * (rot (-i) * rot j) := by
                  rw [hw_sq, one_mul]
                _ = (w * (w * rot (-i))) * rot j := by
                  simp only [mul_assoc]
                _ = (w * (rot i * w)) * rot j := by
                  rw [hrot_mul_w]
                _ = (w * rot i) * (w * rot j) := by
                  simp only [mul_assoc] }
  have hhom_injective : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact hij
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw_not_mem
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := by
        rw [← hij]
        exact hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw_not_mem
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := by
        rw [hij]
        exact hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
        apply e.injective
        apply Subtype.ext
        exact mul_left_cancel hij
      exact congrArg Multiplicative.toAdd heq
  have hhom_surjective : Function.Surjective hom := by
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      refine ⟨DihedralGroup.r i.toAdd, ?_⟩
      exact congrArg Subtype.val hi
    · have hxw : w * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        simp [hw_not_mem, hx]
      obtain ⟨i, hi⟩ := e.surjective ⟨w * x, hxw⟩
      refine ⟨DihedralGroup.sr i.toAdd, ?_⟩
      change w * rot i.toAdd = x
      have hi' : rot i.toAdd = w * x := congrArg Subtype.val hi
      rw [hi', ← mul_assoc, hw_sq, one_mul]
  exact ⟨(MulEquiv.ofBijective hom
    ⟨hhom_injective, hhom_surjective⟩).symm⟩

private theorem outside_reflection_of_mem_sup
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (hT : IsCyclic T) (w g : G)
    (hw_not_mem : w ∉ T) (hw_sq : w * w = 1)
    (hw_inv : ∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹)
    (hg : g ∈ T ⊔ Subgroup.zpowers w) (hg_not_mem : g ∉ T) :
    g * g = 1 ∧ ∀ t : G, t ∈ T → g * t * g⁻¹ = t⁻¹ := by
  let : IsCyclic T := hT
  have hw_inv_eq : w⁻¹ = w :=
    (eq_inv_of_mul_eq_one_left hw_sq).symm
  have hw_ne_one : w ≠ 1 := by
    intro hw
    apply hw_not_mem
    rw [hw]
    exact T.one_mem
  have horder : orderOf w = 2 := by
    have hpow : w ^ 2 = 1 := by simpa [pow_two] using hw_sq
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact (hw_ne_one (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hw_normalizer : w ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hw_inv y hy]
      exact T.inv_mem hy
    · intro hy
      have hdouble : w * (w * y * w⁻¹) * w⁻¹ ∈ T := by
        rw [hw_inv (w * y * w⁻¹) hy]
        exact T.inv_mem hy
      have heq : w * (w * y * w⁻¹) * w⁻¹ = y := by
        calc
          w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w) := by
            rw [hw_inv_eq]
            group
          _ = y := by simp [hw_sq]
      rwa [heq] at hdouble
  have hz_normalizer :
      Subgroup.zpowers w ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.2 hw_normalizer
  have hproduct :
      ((Subgroup.zpowers w : Subgroup G) : Set G) * (T : Set G) =
        (T ⊔ Subgroup.zpowers w : Subgroup G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers w) T hz_normalizer, sup_comm]
  have hg_product :
      g ∈ ((Subgroup.zpowers w : Subgroup G) : Set G) * (T : Set G) := by
    rw [hproduct]
    exact hg
  rcases hg_product with ⟨z, hz, t, ht, hzt⟩
  change z * t = g at hzt
  have hz_eq_one_or_w : z = 1 ∨ z = w := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk]
    have hmod := Int.emod_two_eq_zero_or_one k
    have hreduce : w ^ (k % (orderOf w : ℤ)) = w ^ k :=
      zpow_mod_orderOf w k
    rw [horder] at hreduce
    rcases hmod with hmod | hmod
    · left
      calc
        w ^ k = w ^ (k % (2 : ℤ)) := hreduce.symm
        _ = 1 := by rw [hmod, zpow_zero]
    · right
      calc
        w ^ k = w ^ (k % (2 : ℤ)) := hreduce.symm
        _ = w := by rw [hmod, zpow_one]
  have hz_eq_w : z = w := by
    rcases hz_eq_one_or_w with hz_one | hz_w
    · exfalso
      apply hg_not_mem
      rw [hz_one, one_mul] at hzt
      rwa [← hzt]
    · exact hz_w
  subst z
  have hg_eq : g = w * t := hzt.symm
  have hwt : w * t = t⁻¹ * w := by
    calc
      w * t = (w * t * w⁻¹) * w := by
        rw [hw_inv_eq, mul_assoc, hw_sq, mul_one]
      _ = t⁻¹ * w := by rw [hw_inv t ht]
  constructor
  · rw [hg_eq]
    calc
      (w * t) * (w * t) = (w * t) * (t⁻¹ * w) :=
        congrArg (fun x => (w * t) * x) hwt
      _ = w * (t * t⁻¹) * w := by group
      _ = w * w := by rw [mul_inv_cancel, mul_one]
      _ = 1 := hw_sq
  · intro y hy
    have hcomm : t * y = y * t := setLike_mul_comm ht hy
    rw [hg_eq, mul_inv_rev]
    calc
      w * t * y * (t⁻¹ * w⁻¹) =
          w * (t * y * t⁻¹) * w⁻¹ := by simp only [mul_assoc]
      _ = w * y * w⁻¹ := by rw [hcomm]; simp [mul_assoc]
      _ = y⁻¹ := hw_inv y hy

/-- The torus-normalizer part of Huppert II.8.22. -/
public theorem huppert_II_8_22_torus_normalizer_data
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i) :
    ∃ s : Fin r → ℕ,
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i, Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
  classical
  let P0 : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    huppert_II_8_5_a_psl2_partition hFcard P0
  let Family : Subgroup (PSL2MatrixGroup F) → Prop := fun T =>
    (∃ g, T = (P0 : Subgroup (PSL2MatrixGroup F)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! T : Subgroup (PSL2MatrixGroup F), x ∈ T ∧ Family T := by
    simpa [Family] using hpartition
  obtain ⟨U0, wU0, hU0cyclic, hU0card, hwU0N, hwU0T,
      hwU0sq, hwU0inv, hU0candidate, hU0normalizer⟩ :=
    huppert_II_8_3_split_torus_reflection_data hFcard
  obtain ⟨S0, wS0, hS0cyclic, hS0card, hwS0N, hwS0T,
      hwS0sq, hwS0inv, hS0candidate, hS0normalizer⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data hFcard
  have hP0card :
      Nat.card (P0 : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard P0
    exact (Nat.card_congr eP.toEquiv).symm
  have hU0cardU : Nat.card U0 = Nat.card U := hU0card.trans hUcard.symm
  have hS0cardS : Nat.card S0 = Nat.card S := hS0card.trans hScard.symm
  have hUalign : ∃ g : PSL2MatrixGroup F,
      U0 = U.map (MulAut.conj g).toMonoidHom := by
    by_cases hUbot : U = ⊥
    · have hbotU0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = U0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hU0cardU, hUbot]
      refine ⟨1, ?_⟩
      rw [← hbotU0, hUbot]
      simp
    · have hU0ne : U0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hU0cardU]
        exact (Subgroup.one_lt_card_iff_ne_bot U).2 hUbot
      obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU0ne
      have huG : (u : PSL2MatrixGroup F) ≠ 1 := by
        intro hu
        apply hu_ne
        apply Subtype.ext
        exact hu
      obtain ⟨T, huT, hTfamily⟩ :=
        (hpartition' (u : PSL2MatrixGroup F) huG).exists
      have hU0leT : U0 ≤ T :=
        cyclic_le_unique_partition_family Family hpartition'
          huG huT hTfamily u.property hU0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hP0card, hU0card]
          exact (hq_coprime_split_order
            (Nat.card F) Nat.card_pos).symm
        exact huG (hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
      · refine ⟨g, ?_⟩
        calc
          U0 = T := Subgroup.eq_of_le_of_card_ge hU0leT (by
            rw [hTg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective, hU0cardU])
          _ = U.map (MulAut.conj g).toMonoidHom := hTg
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hScard, hU0card]
          exact hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))
        exact huG (hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
  have hSalign : ∃ g : PSL2MatrixGroup F,
      S0 = S.map (MulAut.conj g).toMonoidHom := by
    by_cases hSbot : S = ⊥
    · have hbotS0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = S0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hS0cardS, hSbot]
      refine ⟨1, ?_⟩
      rw [← hbotS0, hSbot]
      simp
    · have hS0ne : S0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hS0cardS]
        exact (Subgroup.one_lt_card_iff_ne_bot S).2 hSbot
      obtain ⟨s0, hs0_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS0ne
      have hs0G : (s0 : PSL2MatrixGroup F) ≠ 1 := by
        intro hs0
        apply hs0_ne
        apply Subtype.ext
        exact hs0
      obtain ⟨T, hs0T, hTfamily⟩ :=
        (hpartition' (s0 : PSL2MatrixGroup F) hs0G).exists
      have hS0leT : S0 ≤ T :=
        cyclic_le_unique_partition_family Family hpartition'
          hs0G hs0T hTfamily s0.property hS0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hP0card, hS0card]
          exact (hq_coprime_nonsplit_order
            (Nat.card F) Nat.card_pos).symm
        exact hs0G (hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective, hUcard, hS0card]
          exact (hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))).symm
        exact hs0G (hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · refine ⟨g, ?_⟩
        calc
          S0 = T := Subgroup.eq_of_le_of_card_ge hS0leT (by
            rw [hTg, Subgroup.card_map_of_injective
              (MulAut.conj g).injective, hS0cardS])
          _ = S.map (MulAut.conj g).toMonoidHom := hTg
  obtain ⟨gU, hUalign⟩ := hUalign
  obtain ⟨gS, hSalign⟩ := hSalign
  let eU : PSL2MatrixGroup F ≃* PSL2MatrixGroup F := (MulAut.conj gU).symm
  let eS : PSL2MatrixGroup F ≃* PSL2MatrixGroup F := (MulAut.conj gS).symm
  let wU : PSL2MatrixGroup F := eU wU0
  let wS : PSL2MatrixGroup F := eS wS0
  have hUback : U0.map eU.toMonoidHom = U := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := U)
      (e := MulAut.conj gU)).mpr
    exact hUalign.symm
  have hSback : S0.map eS.toMonoidHom = S := by
    apply (Subgroup.map_symm_eq_iff_map_eq (K := S)
      (e := MulAut.conj gS)).mpr
    exact hSalign.symm
  have hUdata :
      IsCyclic U ∧
      wU ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) ∧
      wU ∉ U ∧
      wU * wU = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U → wU * t * wU⁻¹ = t⁻¹) ∧
      Nat.card (U ⊔ Subgroup.zpowers wU : Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card U ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ U → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          U ⊔ Subgroup.zpowers wU := by
    have h := equiv_torus_reflection_data U0 wU0 hU0cyclic hwU0N hwU0T
      hwU0sq hwU0inv hU0candidate hU0normalizer eU
    change IsCyclic (U0.map eU.toMonoidHom) ∧
      wU ∈ Subgroup.normalizer
        (U0.map eU.toMonoidHom : Set (PSL2MatrixGroup F)) ∧
      wU ∉ U0.map eU.toMonoidHom ∧
      wU * wU = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ U0.map eU.toMonoidHom →
        wU * t * wU⁻¹ = t⁻¹) ∧
      Nat.card (U0.map eU.toMonoidHom ⊔ Subgroup.zpowers wU :
        Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card (U0.map eU.toMonoidHom) ∧
      ∀ R : Subgroup (PSL2MatrixGroup F),
        R ≤ U0.map eU.toMonoidHom → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            U0.map eU.toMonoidHom ⊔ Subgroup.zpowers wU at h
    rwa [hUback] at h
  have hSdata :
      IsCyclic S ∧
      wS ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∧
      wS ∉ S ∧
      wS * wS = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S → wS * t * wS⁻¹ = t⁻¹) ∧
      Nat.card (S ⊔ Subgroup.zpowers wS : Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card S ∧
      ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ S → R ≠ ⊥ →
        Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
          S ⊔ Subgroup.zpowers wS := by
    have h := equiv_torus_reflection_data S0 wS0 hS0cyclic hwS0N hwS0T
      hwS0sq hwS0inv hS0candidate hS0normalizer eS
    change IsCyclic (S0.map eS.toMonoidHom) ∧
      wS ∈ Subgroup.normalizer
        (S0.map eS.toMonoidHom : Set (PSL2MatrixGroup F)) ∧
      wS ∉ S0.map eS.toMonoidHom ∧
      wS * wS = 1 ∧
      (∀ t : PSL2MatrixGroup F, t ∈ S0.map eS.toMonoidHom →
        wS * t * wS⁻¹ = t⁻¹) ∧
      Nat.card (S0.map eS.toMonoidHom ⊔ Subgroup.zpowers wS :
        Subgroup (PSL2MatrixGroup F)) =
        2 * Nat.card (S0.map eS.toMonoidHom) ∧
      ∀ R : Subgroup (PSL2MatrixGroup F),
        R ≤ S0.map eS.toMonoidHom → R ≠ ⊥ →
          Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
            S0.map eS.toMonoidHom ⊔ Subgroup.zpowers wS at h
    rwa [hSback] at h
  rcases hUdata with
    ⟨hUcyclic', hwUN, hwUT, hwUsq, hwUinv, hUcandidate, hUnormalizer⟩
  rcases hSdata with
    ⟨hScyclic', hwSN, hwST, hwSsq, hwSinv, hScandidate, hSnormalizer⟩
  have hmap_subtype_cyclic (A : Subgroup H) (hA : IsCyclic A) :
      IsCyclic (A.map H.subtype) := by
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective A H.subtype H.subtype_injective)).mp hA
  have hcomap_cyclic (A : Subgroup (PSL2MatrixGroup F))
      (hA : IsCyclic A) : IsCyclic (A.comap H.subtype) := by
    let : IsCyclic A := hA
    have hmap_cyclic' : IsCyclic ((A.comap H.subtype).map H.subtype) :=
      Subgroup.isCyclic_of_le (Subgroup.map_comap_le H.subtype A)
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective
        (A.comap H.subtype) H.subtype H.subtype_injective)).mpr hmap_cyclic'
  have hambient (i : Fin r) :
      ∃ T : Subgroup (PSL2MatrixGroup F),
        ∃ w : PSL2MatrixGroup F,
        (IsCyclic T ∧
          w ∈ Subgroup.normalizer (T : Set (PSL2MatrixGroup F)) ∧
          w ∉ T ∧
          w * w = 1 ∧
          (∀ t : PSL2MatrixGroup F, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
          Nat.card (T ⊔ Subgroup.zpowers w : Subgroup (PSL2MatrixGroup F)) =
            2 * Nat.card T ∧
          ∀ R : Subgroup (PSL2MatrixGroup F), R ≤ T → R ≠ ⊥ →
            Subgroup.normalizer (R : Set (PSL2MatrixGroup F)) =
              T ⊔ Subgroup.zpowers w) ∧
        (Z i).map H.subtype ≤ T ∧
        T.comap H.subtype = Z i ∧
        ((Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
    let A : Subgroup (PSL2MatrixGroup F) := (Z i).map H.subtype
    have hZi_ne : Z i ≠ ⊥ :=
      (Subgroup.one_lt_card_iff_ne_bot (Z i)).mp (hnontrivial i)
    have hA_ne : A ≠ ⊥ := by
      intro hA
      apply hZi_ne
      apply (Subgroup.map_eq_bot_iff_of_injective (Z i)
        (f := H.subtype) H.subtype_injective).mp
      exact hA
    have hAcyclic : IsCyclic A := hmap_subtype_cyclic (Z i) (hcyclic i)
    obtain ⟨a, ha_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA_ne
    have haG : (a : PSL2MatrixGroup F) ≠ 1 := by
      intro ha
      apply ha_ne
      apply Subtype.ext
      exact ha
    obtain ⟨T, haT, hTfamily⟩ :=
      (hpartition' (a : PSL2MatrixGroup F) haG).exists
    have hA_le_T : A ≤ T :=
      cyclic_le_unique_partition_family Family hpartition'
        haG haT hTfamily a.property hAcyclic
    have hTcomap (hTcyclic : IsCyclic T) : T.comap H.subtype = Z i := by
      have hWcyclic : IsCyclic (T.comap H.subtype) :=
        hcomap_cyclic T hTcyclic
      have hZ_le : Z i ≤ T.comap H.subtype :=
        Subgroup.map_le_iff_le_comap.mp hA_le_T
      exact hmaximal i (T.comap H.subtype) hWcyclic hZ_le
    rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
    · exfalso
      have hcop : Nat.Coprime (Nat.card A) (Nat.card T) := by
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hP0card, hFcard]
        exact ((hcoprime i).pow_left f).symm
      exact haG (hmem_eq_one_of_coprime_card A T hcop
        a.property (hA_le_T a.property))
    · let w : PSL2MatrixGroup F := MulAut.conj g wU
      have hTdata := equiv_torus_reflection_data U wU hUcyclic' hwUN hwUT
        hwUsq hwUinv hUcandidate hUnormalizer (MulAut.conj g)
      rw [← hTg] at hTdata
      refine ⟨T, w, hTdata, hA_le_T, hTcomap hTdata.1, Or.inl ?_⟩
      · have hdvd := Subgroup.card_dvd_of_le hA_le_T
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hUcard] at hdvd
        exact hdvd
    · let w : PSL2MatrixGroup F := MulAut.conj g wS
      have hTdata := equiv_torus_reflection_data S wS hScyclic' hwSN hwST
        hwSsq hwSinv hScandidate hSnormalizer (MulAut.conj g)
      rw [← hTg] at hTdata
      refine ⟨T, w, hTdata, hA_le_T, hTcomap hTdata.1, Or.inr ?_⟩
      · have hdvd := Subgroup.card_dvd_of_le hA_le_T
        rw [show Nat.card A = Nat.card (Z i) by
              exact Subgroup.card_map_of_injective H.subtype_injective,
          hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hScard] at hdvd
        exact hdvd
  let s : Fin r → ℕ := fun i =>
    (Z i).relIndex (Subgroup.normalizer (Z i : Set H))
  have hlocal (i : Fin r) :
      (0 < s i ∧ s i ≤ 2) ∧
      Nat.card (Subgroup.normalizer (Z i : Set H)) =
        Nat.card (Z i) * s i ∧
      (s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      ((Nat.card (Z i) ∣
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (Nat.card (Z i) ∣
          (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) := by
    obtain ⟨T, w, hdata, hA_le_T, hTcomap, hdvd⟩ := hambient i
    rcases hdata with
      ⟨hTcyclic, _hwN, hwT, hwsq, hwinv, hcandidate_card, hnormalizer⟩
    let A : Subgroup (PSL2MatrixGroup F) := (Z i).map H.subtype
    let B : Subgroup (PSL2MatrixGroup F) :=
      (Subgroup.normalizer (Z i : Set H)).map H.subtype
    let N : Subgroup (PSL2MatrixGroup F) := T ⊔ Subgroup.zpowers w
    have hA_ne : A ≠ ⊥ := by
      intro hA
      have hZi_bot : Z i = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (Z i)
          (f := H.subtype) H.subtype_injective).mp hA
      exact (hnontrivial i).ne (by rw [hZi_bot]; simp)
    have hB_le : B ≤ N := by
      have hmap : B ≤ Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) :=
        Subgroup.le_normalizer_map H.subtype
      rw [hnormalizer A hA_le_T hA_ne] at hmap
      exact hmap
    have hinter : T ⊓ B = A := by
      apply le_antisymm
      · intro x hx
        rcases hx.2 with ⟨y, hyN, rfl⟩
        have hyT : y ∈ T.comap H.subtype := hx.1
        rw [hTcomap] at hyT
        exact ⟨y, hyT, rfl⟩
      · exact le_inf hA_le_T
          (Subgroup.map_mono Subgroup.le_normalizer)
    have hTindex : T.relIndex N = 2 :=
      relIndex_eq_two_of_card_eq_two_mul T N le_sup_left hcandidate_card
    have hambient_index : A.relIndex B ≤ 2 :=
      relIndex_le_two_of_inter_eq T B N A hB_le hinter hTindex
    have hs_eq : s i = A.relIndex B := by
      exact (Subgroup.relIndex_map_map_of_injective
        (Z i) (Subgroup.normalizer (Z i : Set H))
        H.subtype_injective).symm
    have hs_pos : 0 < s i := by
      rw [hs_eq, Subgroup.relIndex]
      exact Nat.card_pos
    have hs_le : s i ≤ 2 := by
      rw [hs_eq]
      exact hambient_index
    let NH : Subgroup H := Subgroup.normalizer (Z i : Set H)
    let C : Subgroup NH := (Z i).subgroupOf NH
    let eC : C ≃* Z i :=
      Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
    have hCcard : Nat.card C = Nat.card (Z i) :=
      Nat.card_congr eC.toEquiv
    have hnormalizer_card :
        Nat.card (Subgroup.normalizer (Z i : Set H)) =
          Nat.card (Z i) * s i := by
      calc
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card NH := rfl
        _ = Nat.card C * C.index := C.card_mul_index.symm
        _ = Nat.card (Z i) * s i := by
          rw [hCcard]
          rfl
    have hdihedral (hs_two : s i = 2) :
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i))) := by
      have hCindex : C.index = 2 := by
        change ((Z i).subgroupOf
          (Subgroup.normalizer (Z i : Set H))).index = 2
        exact hs_two
      obtain ⟨a, ha_not, _ha_cosets⟩ :=
        Subgroup.index_eq_two_iff_exists_notMem_and.mp hCindex
      have haB : (((a : NH) : H) : PSL2MatrixGroup F) ∈ B :=
        ⟨((a : NH) : H), a.property, rfl⟩
      have haN : (((a : NH) : H) : PSL2MatrixGroup F) ∈ N := hB_le haB
      have ha_not_T : (((a : NH) : H) : PSL2MatrixGroup F) ∉ T := by
        intro haT
        have ha_comap : ((a : NH) : H) ∈ T.comap H.subtype := haT
        rw [hTcomap] at ha_comap
        apply ha_not
        exact ha_comap
      obtain ⟨ha_sq_ambient, ha_inv_ambient⟩ :=
        outside_reflection_of_mem_sup T hTcyclic w
          (((a : NH) : H) : PSL2MatrixGroup F)
          hwT hwsq hwinv haN ha_not_T
      have ha_sq : a * a = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact ha_sq_ambient
      have ha_inv : ∀ c : NH, c ∈ C → a * c * a⁻¹ = c⁻¹ := by
        intro c hc
        apply Subtype.ext
        apply Subtype.ext
        apply ha_inv_ambient
        apply hA_le_T
        exact ⟨((c : NH) : H), hc, rfl⟩
      have hCcyclic : IsCyclic C :=
        (MulEquiv.isCyclic eC).mpr (hcyclic i)
      have hdih := mulEquiv_dihedral_of_cyclic_reflection
        C hCcyclic a ha_not ha_sq ha_inv hCindex
      rw [hCcard] at hdih
      exact hdih
    exact ⟨⟨hs_pos, hs_le⟩, hnormalizer_card, hdihedral, hdvd⟩
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact fun i => (hlocal i).1
  · exact fun i => (hlocal i).2.1
  · exact fun i => (hlocal i).2.2.1
  · exact fun i => (hlocal i).2.2.2

end Dickson
end CFSG.Glauberman
