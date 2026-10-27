module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveStab
import CFSG.Mathlib.GroupTheory.ClosureSubgroupOf

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

set_option backward.isDefEq.respectTransparency false

@[expose] def signSetIn (k : ℕ) (ε π : Bool)
    (U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) :
    Set (Fin (k + 1) → ZMod 5) :=
  {w | w ∈ U ∧ fiveForm k ε w w ≠ 0 ∧ (IsSquare (fiveForm k ε w w) ↔ π = true)}

theorem mem_signSetIn {k : ℕ} {ε π : Bool}
    {U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} {w : Fin (k + 1) → ZMod 5} :
    w ∈ signSetIn k ε π U ↔ w ∈ U ∧ fiveForm k ε w w ≠ 0 ∧
      (IsSquare (fiveForm k ε w w) ↔ π = true) :=
  Iff.rfl

theorem fiveForm_zero_right (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5) :
    fiveForm k ε x 0 = 0 := by
  simp only [fiveForm, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

theorem fiveReflectionGroupIn_mulVec_eq_of_mem_fiveOrth {k : ℕ} {ε π : Bool}
    {H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} {n : Fin (k + 1) → ZMod 5}
    (hn : n ∈ fiveOrth k ε H) :
    ∀ g ∈ fiveReflectionGroupIn k ε π H,
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n = n := by
  intro g hg
  rw [fiveReflectionGroupIn] at hg
  refine Subgroup.closure_induction (k := fiveReflectionsIn k ε π H)
    (p := fun (g : GL (Fin (k + 1)) (ZMod 5)) _ =>
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ n = n) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨v, hv, hQ, hπ, hgv⟩
    rw [hgv n, mem_fiveOrth.mp hn v hv]
    simp
  · simp
  · intro a b _ _ iha ihb
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ihb, iha]
  · intro a _ iha
    have h := congrArg (fun z => ((a⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z) iha
    simpa [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul] using h.symm

theorem fiveReflOf_ne_of_fiveForm_eq_zero {k : ℕ} {ε : Bool} {a w : Fin (k + 1) → ZMod 5}
    (ha : fiveForm k ε a a ≠ 0) (haw : fiveForm k ε a w = 0) :
    fiveReflOf k ε w ≠ fiveReflOf k ε a := by
  intro h
  have h1 : (fiveReflOf k ε w : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a := by
    rw [fiveReflOf_mulVec, haw]
    simp
  have h2 : (fiveReflOf k ε a : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = -a := by
    rw [fiveReflOf_mulVec]
    have hc : (2 * fiveForm k ε a a * (fiveForm k ε a a)⁻¹) = 2 := by
      rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    rw [hc, two_smul]
    abel
  rw [h] at h1
  have hae : a = -a := h1.symm.trans h2
  have h2a : (2 : ZMod 5) • a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hae]
    abel
  have ha0 : a = 0 := by
    have h := congrArg (fun x => (2 : ZMod 5)⁻¹ • x) h2a
    simpa [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0)] using h
  exact ha (by rw [ha0]; exact fiveForm_zero_right k ε 0)

theorem finrank_fiveOrth_span_singleton {k : ℕ} {ε : Bool} {a : Fin (k + 1) → ZMod 5}
    (ha : fiveForm k ε a a ≠ 0) :
    Module.finrank (ZMod 5) (fiveOrth k ε (Submodule.span (ZMod 5) {a})) = k := by
  have ha0 : a ≠ 0 := by
    intro h
    exact ha (by rw [h]; exact fiveForm_zero_right k ε 0)
  have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := ⊤)
    (U := Submodule.span (ZMod 5) {a}) (isFiveNondeg_top k ε) le_top
  have hspan : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {a}) = 1 :=
    finrank_span_singleton ha0
  have htop : Module.finrank (ZMod 5) (⊤ : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) =
      k + 1 := by
    rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
  rw [top_inf_eq, hspan, htop] at h
  omega

theorem span_signSet_inf_fiveOrth_span {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (hW4 : 4 ≤ Module.finrank (ZMod 5) W) {z : Fin (k + 1) → ZMod 5} (hzW : z ∈ W)
    (hz0 : z ≠ 0) :
    Submodule.span (ZMod 5)
        (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) =
      W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) := by
  by_cases hQ : fiveForm k ε z z = 0
  ·
    obtain ⟨x₀, hx₀W, hx₀⟩ : ∃ x₀ ∈ W, fiveForm k ε z x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz0 (isFiveNondeg_iff.1 hW z hzW hcon)
    have hx₀z : fiveForm k ε x₀ z ≠ 0 := fun h => hx₀ (by rwa [fiveForm_comm] at h)
    let P : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
      Submodule.span (ZMod 5) ({z, x₀} : Set (Fin (k + 1) → ZMod 5))
    have hP_le_W : P ≤ W := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hzW, hx₀W⟩
    have hPnd : IsFiveNondeg k ε P := by
      rw [isFiveNondeg_iff]
      intro x hx hxorth
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
      have h1 : fiveForm k ε (α • z + β • x₀) z = 0 :=
        hxorth z (Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩)
      have h2 : fiveForm k ε (α • z + β • x₀) x₀ = 0 :=
        hxorth x₀ (Submodule.mem_span_pair.mpr ⟨0, 1, by simp⟩)
      rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left] at h1 h2
      rw [hQ, mul_zero, zero_add] at h1
      have hβ : β = 0 := (mul_eq_zero.mp h1).resolve_right hx₀z
      rw [hβ, zero_mul, add_zero] at h2
      have hα : α = 0 := (mul_eq_zero.mp h2).resolve_right hx₀
      rw [hα, hβ, zero_smul, zero_smul, add_zero]
    let M : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) := W ⊓ fiveOrth k ε P
    have hMnd : IsFiveNondeg k ε M := isFiveNondeg_inf_fiveOrth hW hPnd hP_le_W
    have hPle2 : Module.finrank (ZMod 5) P ≤ 2 := by
      have hle : P ≤ Submodule.span (ZMod 5) ({z} : Set (Fin (k + 1) → ZMod 5)) ⊔
          Submodule.span (ZMod 5) ({x₀} : Set (Fin (k + 1) → ZMod 5)) := by
        rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self z),
          Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₀)⟩
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (Submodule.span (ZMod 5) ({z} : Set (Fin (k + 1) → ZMod 5)))
        (Submodule.span (ZMod 5) ({x₀} : Set (Fin (k + 1) → ZMod 5)))
      have hz1 : Module.finrank (ZMod 5)
          (Submodule.span (ZMod 5) ({z} : Set (Fin (k + 1) → ZMod 5))) = 1 :=
        finrank_span_singleton hz0
      have hx1 : Module.finrank (ZMod 5)
          (Submodule.span (ZMod 5) ({x₀} : Set (Fin (k + 1) → ZMod 5))) = 1 :=
        finrank_span_singleton (fun h => hx₀ (by rw [h]; exact fiveForm_zero_right k ε z))
      have : Module.finrank (ZMod 5)
          ↥(Submodule.span (ZMod 5) ({z} : Set (Fin (k + 1) → ZMod 5)) ⊔
            Submodule.span (ZMod 5) ({x₀} : Set (Fin (k + 1) → ZMod 5))) ≤ 2 := by
        omega
      exact (Submodule.finrank_mono hle).trans this
    have hMdim : Module.finrank (ZMod 5) M + Module.finrank (ZMod 5) P =
        Module.finrank (ZMod 5) W :=
      finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := W) (U := P) hW hP_le_W
    have hM2 : 2 ≤ Module.finrank (ZMod 5) M := by omega
    have hc : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
    obtain ⟨x, hxM, hxQ⟩ := exists_fiveForm_eq_of_nondeg hMnd hM2 (c := fiveSignRep π)
    have hxW : x ∈ W := hxM.1
    have hxP : x ∈ fiveOrth k ε P := hxM.2
    have hxz : fiveForm k ε x z = 0 :=
      (mem_fiveOrth.mp hxP) z (Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩)
    have hxN : x ∈ W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) := by
      refine ⟨hxW, mem_fiveOrth.2 fun q hq => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
      rw [fiveForm_smul_right, hxz, mul_zero]
    have hxS : x ∈ signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})) := by
      rw [mem_signSetIn]
      exact ⟨hxN, by rw [hxQ]; exact fiveSignRep_ne_zero π,
        by rw [hxQ]; exact isSquare_fiveSignRep_iff π⟩
    have hxzsW : x + z ∈ W := W.add_mem hxW hzW
    have hxzsQ : fiveForm k ε (x + z) (x + z) = fiveSignRep π := by
      rw [fiveForm_self_add, hxQ, hQ, hxz, mul_zero, add_zero, add_zero]
    have hxzsN : x + z ∈ W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) := by
      refine ⟨hxzsW, mem_fiveOrth.2 fun q hq => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
      rw [fiveForm_smul_right, fiveForm_add_left, hxz, hQ, add_zero, mul_zero]
    have hxzsS : x + z ∈ signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})) := by
      rw [mem_signSetIn]
      exact ⟨hxzsN, by rw [hxzsQ]; exact fiveSignRep_ne_zero π,
        by rw [hxzsQ]; exact isSquare_fiveSignRep_iff π⟩
    have hz_spanS : z ∈ Submodule.span (ZMod 5)
        (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) := by
      have h1 : x + z ∈ Submodule.span (ZMod 5)
          (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) :=
        Submodule.subset_span hxzsS
      have h2 : x ∈ Submodule.span (ZMod 5)
          (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) :=
        Submodule.subset_span hxS
      have h := Submodule.sub_mem (Submodule.span (ZMod 5)
        (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})))) h1 h2
      simpa using h
    have hM_le : M ≤ Submodule.span (ZMod 5)
        (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) := by
      have hspanM : Submodule.span (ZMod 5)
          {m | m ∈ M ∧ fiveForm k ε m m = fiveSignRep π} = M :=
        span_fiveForm_eq_of_nondeg hMnd hM2 hc
      rw [← hspanM]
      apply Submodule.span_mono
      rintro m ⟨hmM, hmQ⟩
      rw [mem_signSetIn]
      have hmN : m ∈ W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) := by
        refine ⟨hmM.1, mem_fiveOrth.2 fun q hq => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
        rw [fiveForm_smul_right,
          (mem_fiveOrth.mp hmM.2) z (Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩), mul_zero]
      exact ⟨hmN, by rw [hmQ]; exact fiveSignRep_ne_zero π,
        by rw [hmQ]; exact isSquare_fiveSignRep_iff π⟩
    have hN_le : W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) ≤
        Submodule.span (ZMod 5)
          (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) := by
      intro w hw
      have hwz : fiveForm k ε w z = 0 :=
        (mem_fiveOrth.mp hw.2) z (Submodule.mem_span_singleton_self z)
      set m : Fin (k + 1) → ZMod 5 :=
        fiveForm k ε z x₀ • w - fiveForm k ε w x₀ • z
      have hmW : m ∈ W := W.sub_mem (W.smul_mem _ hw.1) (W.smul_mem _ hzW)
      have hmz : fiveForm k ε m z = 0 := by
        rw [show m = fiveForm k ε z x₀ • w - fiveForm k ε w x₀ • z from rfl,
          fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left, hwz, hQ]
        ring
      have hmu : fiveForm k ε m x₀ = 0 := by
        rw [show m = fiveForm k ε z x₀ • w - fiveForm k ε w x₀ • z from rfl,
          fiveForm_sub_left, fiveForm_smul_left, fiveForm_smul_left]
        ring
      have hmP : m ∈ fiveOrth k ε P := by
        refine mem_fiveOrth.2 fun q hq => ?_
        obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hq
        rw [fiveForm_add_right, fiveForm_smul_right, fiveForm_smul_right,
          hmz, hmu, mul_zero, mul_zero, add_zero]
      have hmM : m ∈ M := ⟨hmW, hmP⟩
      have hmS : m ∈ Submodule.span (ZMod 5)
          (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) := hM_le hmM
      have hw_split : fiveForm k ε z x₀ • w = m + fiveForm k ε w x₀ • z := by
        rw [show m = fiveForm k ε z x₀ • w - fiveForm k ε w x₀ • z from rfl]
        abel
      have hw_eq : w = (fiveForm k ε z x₀)⁻¹ • (m + fiveForm k ε w x₀ • z) := by
        rw [← hw_split, smul_smul, inv_mul_cancel₀ hx₀, one_smul]
      rw [hw_eq, smul_add, smul_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hmS)
        (Submodule.smul_mem _ _ hz_spanS)
    exact le_antisymm (Submodule.span_le.mpr (fun w hw => (mem_signSetIn.mp hw).1)) hN_le
  ·
    have hspan_le : Submodule.span (ZMod 5) {z} ≤ W :=
      Submodule.span_le.mpr (by simpa using hzW)
    have hN : IsFiveNondeg k ε (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})) :=
      isFiveNondeg_inf_fiveOrth hW (isFiveNondeg_span_singleton hQ) hspan_le
    have hfin : Module.finrank (ZMod 5)
        ↥(W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})) =
        Module.finrank (ZMod 5) W - 1 := by
      have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := W)
        (U := Submodule.span (ZMod 5) {z}) hW hspan_le
      have hz1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {z}) = 1 :=
        finrank_span_singleton hz0
      rw [hz1] at h
      omega
    have h2 : 2 ≤ Module.finrank (ZMod 5)
        ↥(W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})) := by omega
    have hc : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
    have hSc : {x | x ∈ W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) ∧
        fiveForm k ε x x = fiveSignRep π} ⊆
        signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z})) := by
      rintro x ⟨hxN, hxQ⟩
      rw [mem_signSetIn]
      exact ⟨hxN, by rw [hxQ]; exact fiveSignRep_ne_zero π,
        by rw [hxQ]; exact isSquare_fiveSignRep_iff π⟩
    refine le_antisymm (Submodule.span_le.mpr (fun w hw => (mem_signSetIn.mp hw).1)) ?_
    calc W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) =
          Submodule.span (ZMod 5) {x | x ∈ W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) ∧
            fiveForm k ε x x = fiveSignRep π} := (span_fiveForm_eq_of_nondeg hN h2 hc).symm
      _ ≤ Submodule.span (ZMod 5)
            (signSetIn k ε π (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}))) :=
          Submodule.span_mono hSc

theorem span_singleton_eq_of_fiveOrth_eq {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (hW4 : 4 ≤ Module.finrank (ZMod 5) W) {z z' : Fin (k + 1) → ZMod 5} (hzW : z ∈ W)
    (hz'W : z' ∈ W) (hz0 : z ≠ 0) (hz'0 : z' ≠ 0)
    (h : ∀ w, fiveForm k ε w w ≠ 0 → (IsSquare (fiveForm k ε w w) ↔ π = true) → w ∈ W →
      (fiveForm k ε z w = 0 ↔ fiveForm k ε z' w = 0)) :
    Submodule.span (ZMod 5) {z} = Submodule.span (ZMod 5) {z'} := by
  set N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z}) with hNdef
  set N' : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {z'}) with hN'def
  have hsign : signSetIn k ε π N = signSetIn k ε π N' := by
    ext w
    rw [mem_signSetIn, mem_signSetIn]
    constructor
    · rintro ⟨hwN, hwQ, hwπ⟩
      have hwW : w ∈ W := hwN.1
      have hwz : fiveForm k ε z w = 0 := by
        rw [fiveForm_comm k ε z w]
        exact (mem_fiveOrth.mp hwN.2) z (Submodule.mem_span_singleton_self z)
      have hwz' : fiveForm k ε z' w = 0 := (h w hwQ hwπ hwW).1 hwz
      refine ⟨⟨hwW, mem_fiveOrth.2 fun q hq => ?_⟩, hwQ, hwπ⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
      rw [fiveForm_smul_right, fiveForm_comm k ε w z', hwz', mul_zero]
    · rintro ⟨hwN, hwQ, hwπ⟩
      have hwW : w ∈ W := hwN.1
      have hwz' : fiveForm k ε z' w = 0 := by
        rw [fiveForm_comm k ε z' w]
        exact (mem_fiveOrth.mp hwN.2) z' (Submodule.mem_span_singleton_self z')
      have hwz : fiveForm k ε z w = 0 := (h w hwQ hwπ hwW).2 hwz'
      refine ⟨⟨hwW, mem_fiveOrth.2 fun q hq => ?_⟩, hwQ, hwπ⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
      rw [fiveForm_smul_right, fiveForm_comm k ε w z, hwz, mul_zero]
  have hspanN : Submodule.span (ZMod 5) (signSetIn k ε π N) = N := by
    rw [hNdef]
    exact span_signSet_inf_fiveOrth_span hW hW4 hzW hz0
  have hspanN' : Submodule.span (ZMod 5) (signSetIn k ε π N') = N' := by
    rw [hN'def]
    exact span_signSet_inf_fiveOrth_span hW hW4 hz'W hz'0
  have hNN' : N = N' := by rw [← hspanN, hsign, hspanN']
  have hspanz_le : Submodule.span (ZMod 5) {z} ≤ W :=
    Submodule.span_le.mpr (by simpa using hzW)
  have hfinN : Module.finrank (ZMod 5) N = Module.finrank (ZMod 5) W - 1 := by
    have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := W)
      (U := Submodule.span (ZMod 5) {z}) hW hspanz_le
    have hz1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {z}) = 1 :=
      finrank_span_singleton hz0
    rw [← hNdef, hz1] at h
    omega
  have hz_mem : z ∈ W ⊓ fiveOrth k ε N := by
    refine ⟨hzW, mem_fiveOrth.2 fun q hq => ?_⟩
    rw [fiveForm_comm k ε z q]
    exact (mem_fiveOrth.mp hq.2) z (Submodule.mem_span_singleton_self z)
  have hz'_mem : z' ∈ W ⊓ fiveOrth k ε N := by
    refine ⟨hz'W, mem_fiveOrth.2 fun q hq => ?_⟩
    have hq'' : q ∈ N' := by rw [← hNN']; exact hq
    rw [fiveForm_comm k ε z' q]
    exact (mem_fiveOrth.mp hq''.2) z' (Submodule.mem_span_singleton_self z')
  have hfin : Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε N) = 1 := by
    have h := finrank_inf_fiveOrth_add (k := k) (ε := ε) (W := W) (U := N) hW inf_le_left
    rw [hfinN] at h
    omega
  have hspanW : W ⊓ fiveOrth k ε N = Submodule.span (ZMod 5) {z} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin hz_mem hz0
  have hspanW' : W ⊓ fiveOrth k ε N = Submodule.span (ZMod 5) {z'} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin hz'_mem hz'0
  rw [← hspanW, hspanW']

end CFSG.OddTranspositions.PartThree

end
