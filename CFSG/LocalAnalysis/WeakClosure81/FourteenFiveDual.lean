module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open Classical
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace FourteenFive

private abbrev E (V : Subgroup G) (hV : IsElemAbelian 2 V) := Additive (IntMod V hV)

private noncomputable instance instModuleE (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Module (ZMod 2) (E V hV) :=
  AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    show Additive.toMul (2 • x) = Additive.toMul 0
    rw [two_nsmul, toMul_add, toMul_zero, ← pow_two]
    exact IntMod.sq_eq_one (Additive.toMul x))

private def ev {V : Subgroup G} {hV : IsElemAbelian 2 V} (x : E V hV) : G :=
  (Additive.toMul x : IntMod V hV).val

private theorem ev_mem {V : Subgroup G} {hV : IsElemAbelian 2 V} (x : E V hV) :
    ev x ∈ V := IntMod.val_mem _

private theorem ev_add {V : Subgroup G} {hV : IsElemAbelian 2 V} (x y : E V hV) :
    ev (x + y) = ev x * ev y := rfl

private theorem ev_zero {V : Subgroup G} {hV : IsElemAbelian 2 V} : ev (0 : E V hV) = 1 := rfl

private def ofG {V : Subgroup G} (hV : IsElemAbelian 2 V) (v : G) (hv : v ∈ V) : E V hV :=
  Additive.ofMul (IntMod.mk hV ⟨v, hv⟩)

private theorem ev_ofG {V : Subgroup G} {hV : IsElemAbelian 2 V} {v : G} (hv : v ∈ V) :
    ev (ofG hV v hv) = v := rfl

private theorem comm_of_mem {V : Subgroup G} {hV : IsElemAbelian 2 V} {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  have h := IntMod.val_comm (hV := hV) (IntMod.mk hV ⟨a, ha⟩) (IntMod.mk hV ⟨b, hb⟩)
  exact h

private theorem zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private noncomputable def bit (P : Prop) : ZMod 2 := if P then 0 else 1

private noncomputable def formFun {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (D : Subgroup G) (x : G) (z : E V hV) : ZMod 2 :=
  bit (x * ev z * x⁻¹ * (ev z)⁻¹ ∈ D)

private theorem formFun_zero {V : Subgroup G} {hV : IsElemAbelian 2 V} (D : Subgroup G)
    (x : G) : formFun D x (0 : E V hV) = 0 := by
  unfold formFun bit
  rw [ev_zero]
  simp

private theorem formFun_one {V : Subgroup G} {hV : IsElemAbelian 2 V} (D : Subgroup G)
    (z : E V hV) : formFun D 1 z = 0 := by
  unfold formFun bit
  simp

private theorem zmod2_indicator_add {P Q : Prop} :
    bit P + bit Q = bit (P ↔ Q) := by
  unfold bit
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ] <;> decide

private theorem zmod2_indicator_eq_iff {P Q : Prop} (h : bit P = bit Q) : P ↔ Q := by
  unfold bit at h
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all

private theorem commutator_mul_mem_iff {V V₀ D H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    {x v w : G} (hx : x ∈ H) (hv : v ∈ V) (hw : w ∈ V) :
    x * (v * w) * x⁻¹ * (v * w)⁻¹ ∈ D ↔
      (x * v * x⁻¹ * v⁻¹ ∈ D ↔ x * w * x⁻¹ * w⁻¹ ∈ D) := by
  have hcw : x * w * x⁻¹ ∈ V := by
    have h := V.mul_mem (hV₀ (hHV x hx w hw)) hw
    rwa [show (x * w * x⁻¹ * w⁻¹) * w = x * w * x⁻¹ by group] at h
  have hmul : x * (v * w) * x⁻¹ * (v * w)⁻¹ =
      (x * v * x⁻¹ * v⁻¹) * (x * w * x⁻¹ * w⁻¹) := by
    rw [← commutatorElement_def x (v * w),
      ← commutatorElement_def x v,
      ← commutatorElement_def x w,
      commutatorElement_mul_right_eq_mul_conj]
    have hcomm : v * ⁅x, w⁆ = ⁅x, w⁆ * v :=
      comm_of_mem (hV := hV) hv (hV₀ (hHV x hx w hw))
    have h2 : v * ⁅x, w⁆ * v⁻¹ = ⁅x, w⁆ := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [show ⁅x, v⁆ * v * ⁅x, w⁆ * v⁻¹ = ⁅x, v⁆ * (v * ⁅x, w⁆ * v⁻¹) by group, h2]
  rw [hmul]
  have hf := Subgroup.mul_mem_iff_of_index_two (H := D.subgroupOf V₀) hD2
      (a := (⟨x * v * x⁻¹ * v⁻¹, hHV x hx v hv⟩ : V₀))
      (b := (⟨x * w * x⁻¹ * w⁻¹, hHV x hx w hw⟩ : V₀))
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subtype.coe_mk] using hf

private theorem formFun_add {V V₀ D H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    {x : G} (hx : x ∈ H) (a b : E V hV) :
    formFun D x (a + b) = formFun D x a + formFun D x b := by
  have hkey := commutator_mul_mem_iff hV hV₀ hD hD2 hHV hx (ev_mem a) (ev_mem b)
  unfold formFun
  rw [ev_add, hkey]
  exact (zmod2_indicator_add
    (P := x * ev a * x⁻¹ * (ev a)⁻¹ ∈ D)
    (Q := x * ev b * x⁻¹ * (ev b)⁻¹ ∈ D)).symm

private theorem formFun_mul {V V₀ D H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    (hHV₀ : ∀ x ∈ H, ∀ v ∈ V₀, x * v * x⁻¹ * v⁻¹ ∈ D)
    (a b : H) (z : E V hV) :
    formFun D ((a : G) * (b : G)) z = formFun D (a : G) z + formFun D (b : G) z := by
  have hzV : ev z ∈ V := ev_mem z
  have ht : (b : G) * ev z * (b : G)⁻¹ * (ev z)⁻¹ ∈ V₀ := hHV b b.2 (ev z) hzV
  have hu : (a : G) * ev z * (a : G)⁻¹ * (ev z)⁻¹ ∈ V₀ := hHV a a.2 (ev z) hzV
  set t := (b : G) * ev z * (b : G)⁻¹ * (ev z)⁻¹ with htdef
  set u := (a : G) * ev z * (a : G)⁻¹ * (ev z)⁻¹ with hudef
  have htV₀ : t ∈ V₀ := by rw [htdef]; exact ht
  have huV₀ : u ∈ V₀ := by rw [hudef]; exact hu
  have hd : (a : G) * t * (a : G)⁻¹ * t⁻¹ ∈ D := hHV₀ a a.2 t htV₀
  have hkeyD : ((a : G) * (b : G)) * ev z * ((a : G) * (b : G))⁻¹ * (ev z)⁻¹ ∈ D ↔
      t * u ∈ D := by
    have heq : ((a : G) * (b : G)) * ev z * ((a : G) * (b : G))⁻¹ * (ev z)⁻¹ =
        ((a : G) * t * (a : G)⁻¹ * t⁻¹) * t * u := by
      rw [htdef, hudef]
      group
    rw [heq, show ((a : G) * t * (a : G)⁻¹ * t⁻¹) * t * u =
        ((a : G) * t * (a : G)⁻¹ * t⁻¹) * (t * u) by group]
    exact D.mul_mem_cancel_left hd
  have hkey : t * u ∈ D ↔ (t ∈ D ↔ u ∈ D) := by
    have hf := Subgroup.mul_mem_iff_of_index_two (H := D.subgroupOf V₀) hD2
        (a := (⟨t, htV₀⟩ : V₀)) (b := (⟨u, huV₀⟩ : V₀))
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subtype.coe_mk] using hf
  unfold formFun
  rw [hkeyD, hkey, add_comm]
  exact (zmod2_indicator_add (P := t ∈ D) (Q := u ∈ D)).symm

private noncomputable def form {V V₀ D H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀) (x : H) :
    Module.Dual (ZMod 2) (E V hV) :=
  { toFun := fun z => formFun D (x : G) z
    map_add' := fun a b => formFun_add hV hV₀ hD hD2 hHV x.2 a b
    map_smul' := fun c z => by
      rcases zmod_two_eq_zero_or_one c with rfl | rfl
      · simp [formFun_zero]
      · simp }

private noncomputable def formL {V V₀ D H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀) :
    H → Module.Dual (ZMod 2) (E V hV) :=
  fun x => form hV hV₀ hD hD2 hHV x

private theorem formL_apply {V V₀ D H : Subgroup G} {hV : IsElemAbelian 2 V}
    (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    (x : H) (z : E V hV) :
    formL hV hV₀ hD hD2 hHV x z = formFun D (x : G) z := rfl

private noncomputable def formW {V W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : W.relIndex V = 2) : Module.Dual (ZMod 2) (E V hV) :=
  { toFun := fun z => bit (ev z ∈ W)
    map_add' := fun a b => by
      have hkey : ev a * ev b ∈ W ↔ (ev a ∈ W ↔ ev b ∈ W) := by
        have hf := Subgroup.mul_mem_iff_of_index_two (H := W.subgroupOf V) hW
            (a := (⟨ev a, ev_mem a⟩ : V)) (b := (⟨ev b, ev_mem b⟩ : V))
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subtype.coe_mk] using hf
      show bit (ev (a + b) ∈ W) = bit (ev a ∈ W) + bit (ev b ∈ W)
      rw [ev_add, hkey]
      exact (zmod2_indicator_add (P := ev a ∈ W) (Q := ev b ∈ W)).symm
    map_smul' := fun c z => by
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp [bit, ev_zero] }

private theorem formW_apply {V W : Subgroup G} {hV : IsElemAbelian 2 V}
    (hW : W.relIndex V = 2) (z : E V hV) :
    formW hV hW z = bit (ev z ∈ W) := rfl

theorem exists_mem_forall_commutator_mem_iff {V V₀ D H W : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) (hD : D ≤ V₀) (hD2 : D.relIndex V₀ = 2)
    (hHV : ∀ x ∈ H, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀)
    (hHV₀ : ∀ x ∈ H, ∀ v ∈ V₀, x * v * x⁻¹ * v⁻¹ ∈ D)
    (hker : ∀ v ∈ V, (∀ x ∈ H, x * v * x⁻¹ * v⁻¹ ∈ D) → v ∈ V₀)
    (hWV : W ≤ V) (hV₀W : V₀ ≤ W) (hW : W.relIndex V = 2) :
    ∃ x ∈ H, ∀ v ∈ V, (x * v * x⁻¹ * v⁻¹ ∈ D ↔ v ∈ W) := by
  let Ψ : Submodule (ZMod 2) (Module.Dual (ZMod 2) (E V hV)) :=
    { carrier := Set.range (formL hV hV₀ hD hD2 hHV)
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        refine ⟨x * y, ?_⟩
        ext z
        rw [formL_apply, LinearMap.add_apply, formL_apply, formL_apply]
        exact formFun_mul hV hV₀ hD hD2 hHV hHV₀ x y z
      zero_mem' := by
        refine ⟨1, ?_⟩
        ext z
        rw [formL_apply, LinearMap.zero_apply]
        exact formFun_one D z
      smul_mem' := by
        rintro c _ ⟨x, rfl⟩
        rcases zmod_two_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul]
          refine ⟨1, ?_⟩
          ext z
          rw [formL_apply, LinearMap.zero_apply]
          exact formFun_one D z
        · rw [one_smul]
          exact ⟨x, rfl⟩ }
  have hspan : Submodule.span (ZMod 2) (Set.range (formL hV hV₀ hD hD2 hHV)) = Ψ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro f hf
      exact hf
    · exact Submodule.subset_span
  have hker_le : ⨅ x : H, LinearMap.ker (formL hV hV₀ hD hD2 hHV x) ≤
      LinearMap.ker (formW hV hW) := by
    intro z hz
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_iInf] at hz
    have hzD : ∀ x ∈ H, x * ev z * x⁻¹ * (ev z)⁻¹ ∈ D := by
      intro x hx
      have h0 : formFun D x z = 0 := by
        have hx0 : formL hV hV₀ hD hD2 hHV ⟨x, hx⟩ z = 0 := by
          have := hz ⟨x, hx⟩
          rwa [LinearMap.mem_ker] at this
        simpa only [formL_apply] using hx0
      unfold formFun at h0
      by_contra h
      rw [show bit (x * ev z * x⁻¹ * (ev z)⁻¹ ∈ D) = (1 : ZMod 2) by
        unfold bit; rw [if_neg h]] at h0
      exact one_ne_zero h0
    rw [formW_apply, show bit (ev z ∈ W) = (0 : ZMod 2) by
      unfold bit; rw [if_pos (hV₀W (hker (ev z) (ev_mem z) hzD))]]
  have hmem : formW hV hW ∈
      Submodule.span (ZMod 2) (Set.range (formL hV hV₀ hD hD2 hHV)) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker hker_le
  have hψΨ : formW hV hW ∈ Ψ := by
    rw [← hspan]
    exact hmem
  obtain ⟨x, hxψ⟩ := hψΨ
  refine ⟨(x : G), x.2, ?_⟩
  intro v hv
  have hfun : formFun D (x : G) (ofG hV v hv) = bit (v ∈ W) := by
    have h : formL hV hV₀ hD hD2 hHV x (ofG hV v hv) =
        formW hV hW (ofG hV v hv) :=
      congrArg (fun f : Module.Dual (ZMod 2) (E V hV) => f (ofG hV v hv)) hxψ
    simpa only [formL_apply, formW_apply, ev_ofG] using h
  unfold formFun at hfun
  rw [ev_ofG] at hfun
  exact zmod2_indicator_eq_iff hfun

end FourteenFive

end CFSG.LocalAnalysis.WeakClosure81
