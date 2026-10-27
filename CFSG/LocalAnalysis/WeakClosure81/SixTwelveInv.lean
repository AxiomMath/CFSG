module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.GroupTheory.CommutatorMemSubgroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma b612_mul_self {E : Subgroup G} (h : IsElemAbelian 2 E) {x : G}
    (hx : x ∈ E) : x * x = 1 := by
  have h2 := h.2 x hx
  rwa [pow_two] at h2

private lemma b612_mul_comm {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  haveI : IsMulCommutative ↥E := h.1
  have h' := mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩
  exact Subtype.ext_iff.mp h'

private lemma b612_isPGroup {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) : IsPGroup p E :=
  fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using h.2 (x : G) x.2)⟩

private lemma b612_commutator_eq {V : Subgroup G} (hV : IsElemAbelian 2 V) {a v : G}
    (hv : v ∈ V) : ⁅v, a⁆ = v * (a * v * a⁻¹) := by
  have hvv : v * v = 1 := b612_mul_self hV hv
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hvv]
  group

private lemma b612_le_of_commutator_mem {V W P : Subgroup G} (hV : IsElemAbelian 2 V)
    (hWV : W ≤ V) {a : G} (haW : a ∈ normalizer (W : Set G))
    (hP : ∀ v : G, v ∈ P ↔ v ∈ V ∧ ⁅v, a⁆ ∈ W) : W ≤ P := by
  intro w hw
  rw [hP]
  refine ⟨hWV hw, ?_⟩
  have hadj : a * w * a⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 haW w).1 hw
  rw [b612_commutator_eq hV (hWV hw)]
  exact W.mul_mem hw hadj

theorem exists_subgroup_two_mul_mQuot_le {V W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hWV : W ≤ V) {a : G} (haV : a ∈ normalizer (V : Set G)) (haW : a ∈ normalizer (W : Set G))
    (ha2 : a * a = 1) :
    ∃ P : Subgroup G, (∀ v : G, v ∈ P ↔ v ∈ V ∧ ⁅v, a⁆ ∈ W) ∧
      2 * E3.mQuot V P ≤ E3.mQuot V W := by
  classical
  haveI : IsMulCommutative ↥V := hV.1
  have hVW : V ≤ normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWV).mp inferInstance
  set P : Subgroup G := CFSG.GroupTheory.commMemSubgroup V W hVW a with hPdef
  have hP : ∀ v : G, v ∈ P ↔ v ∈ V ∧ ⁅v, a⁆ ∈ W := by
    intro v; rw [hPdef, CFSG.GroupTheory.mem_commMemSubgroup]
  have hPleV : P ≤ V := fun v hv => (hP v).1 hv |>.1
  have hWleP : W ≤ P := b612_le_of_commutator_mem hV hWV haW hP
  have haV' : ∀ v ∈ V, a * v * a⁻¹ ∈ V :=
    fun v hv => (Subgroup.mem_normalizer_iff.1 haV v).1 hv
  let ψ : ↥V →* ↥V := MonoidHom.mk' (fun v =>
      ⟨v * (a * v * a⁻¹), V.mul_mem v.2 (haV' v v.2)⟩) (by
    intro v w
    apply Subtype.ext
    show (v * w : G) * (a * (v * w) * a⁻¹) =
      (v * (a * v * a⁻¹)) * (w * (a * w * a⁻¹))
    have h1 : (a * v * a⁻¹ : G) * w = w * (a * v * a⁻¹) :=
      b612_mul_comm hV (haV' v v.2) w.2
    calc (v * w : G) * (a * (v * w) * a⁻¹)
        = v * w * ((a * v * a⁻¹) * (a * w * a⁻¹)) := by group
      _ = v * (w * (a * v * a⁻¹)) * (a * w * a⁻¹) := by group
      _ = v * ((a * v * a⁻¹) * w) * (a * w * a⁻¹) := by rw [h1]
      _ = (v * (a * v * a⁻¹)) * (w * (a * w * a⁻¹)) := by group)
  have hψ : ∀ v : ↥V, ((ψ v : ↥V) : G) = (v : G) * (a * (v : G) * a⁻¹) := fun v => rfl
  have hfix : ∀ v : ↥V, a * ((ψ v : ↥V) : G) * a⁻¹ = ((ψ v : ↥V) : G) := by
    intro v
    rw [hψ]
    have h1 : (a * (v : G) * a⁻¹) * (v : G) = (v : G) * (a * (v : G) * a⁻¹) :=
      b612_mul_comm hV (haV' v v.2) v.2
    have h2 : a * (a * (v : G) * a⁻¹) * a⁻¹ = (v : G) := by
      calc a * (a * (v : G) * a⁻¹) * a⁻¹ = (a * a) * (v : G) * (a * a)⁻¹ := by group
        _ = (v : G) := by rw [ha2]; group
    calc a * ((v : G) * (a * (v : G) * a⁻¹)) * a⁻¹
        = (a * (v : G) * a⁻¹) * (a * (a * (v : G) * a⁻¹) * a⁻¹) := by group
      _ = (a * (v : G) * a⁻¹) * (v : G) := by rw [h2]
      _ = (v : G) * (a * (v : G) * a⁻¹) := h1
  have hψP : ∀ v : ↥V, ψ v ∈ P.subgroupOf V := by
    intro v
    rw [Subgroup.mem_subgroupOf, hP]
    refine ⟨(ψ v).2, ?_⟩
    have h1 : ⁅((ψ v : ↥V) : G), a⁆ = 1 := by
      rw [b612_commutator_eq hV (ψ v).2, hfix v, ← pow_two]
      exact hV.2 _ (ψ v).2
    rw [h1]
    exact W.one_mem
  let f : ↥V →* ↥V ⧸ W.subgroupOf V := (QuotientGroup.mk' (W.subgroupOf V)).comp ψ
  have hker : f.ker = P.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hP]
    constructor
    · intro hv
      have hw : ((ψ v : ↥V) : G) ∈ W := by
        rw [← Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (ψ v)]
        exact hv
      exact ⟨v.2, by rw [b612_commutator_eq hV v.2]; exact hw⟩
    · rintro ⟨-, hvW⟩
      change (ψ v : ↥V ⧸ W.subgroupOf V) = 1
      rw [QuotientGroup.eq_one_iff (ψ v), Subgroup.mem_subgroupOf, hψ v,
        ← b612_commutator_eq hV v.2]
      exact hvW
  have hrange_le : f.range ≤ (P.subgroupOf V).map (QuotientGroup.mk' (W.subgroupOf V)) := by
    intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨v, rfl⟩ := hy
    exact Subgroup.mem_map_of_mem _ (hψP v)
  have hidx : P.relIndex V = Nat.card f.range := by
    show (P.subgroupOf V).index = Nat.card f.range
    rw [← hker, Subgroup.index_ker]
  have hmap_card : Nat.card ((P.subgroupOf V).map (QuotientGroup.mk' (W.subgroupOf V)))
      = W.relIndex P := by
    rw [← Subgroup.relIndex_ker (K := P.subgroupOf V)
        (f := QuotientGroup.mk' (W.subgroupOf V)), QuotientGroup.ker_mk',
      Subgroup.relIndex_subgroupOf hPleV]
  have hrel : P.relIndex V ≤ W.relIndex P := by
    rw [hidx, ← hmap_card]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hrange_le)
      (Subgroup.inclusion_injective hrange_le)
  have hP2 : IsPGroup 2 P :=
    (b612_isPGroup hV).of_injective (Subgroup.inclusion hPleV)
      (Subgroup.inclusion_injective hPleV)
  have hm : E3.mQuot V P ≤ E3.mQuot P W := by
    have h1 : 2 ^ E3.mQuot V P ≤ 2 ^ E3.mQuot P W := by
      rw [← E3.relIndex_eq_two_pow (b612_isPGroup hV) P, ← E3.relIndex_eq_two_pow hP2 W]
      exact hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  refine ⟨P, hP, ?_⟩
  have hsum := E3.mQuot_add hWleP hPleV
  rw [hsum]
  omega

theorem exists_mem_sdiff_commutator_mem {V W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hWV : W ≤ V) (hne : W ≠ V) {a : G} (haV : a ∈ normalizer (V : Set G))
    (haW : a ∈ normalizer (W : Set G)) (ha2 : a * a = 1) :
    ∃ v ∈ V, v ∉ W ∧ ⁅v, a⁆ ∈ W := by
  classical
  obtain ⟨P, hP, hineq⟩ := exists_subgroup_two_mul_mQuot_le hV hWV haV haW ha2
  have hWleP : W ≤ P := b612_le_of_commutator_mem hV hWV haW hP
  by_contra h
  rw [not_exists] at h
  have hPleW : P ≤ W := by
    intro v hv
    by_contra hvW
    exact h v ⟨(hP v).1 hv |>.1, hvW, (hP v).1 hv |>.2⟩
  have hPeq : P = W := le_antisymm hPleW hWleP
  have hm0 : E3.mQuot V W = 0 := by
    rw [hPeq] at hineq
    omega
  exact hne ((E3.mQuot_eq_zero_iff (b612_isPGroup hV) hWV).1 hm0)

theorem mQuot_add_one_le_of_mem {A C M : Subgroup G} (hA : IsElemAbelian 2 A) (hCA : C ≤ A)
    (hCM : C ≤ M) {a : G} (haA : a ∈ A) (haM : a ∈ M) (haC : a ∉ C) :
    E3.mQuot A M + 1 ≤ E3.mQuot A C := by
  set U : Subgroup G := M ⊓ A with hUdef
  have hCU : C ≤ U := le_inf hCM hCA
  have hne : C ≠ U := by
    intro h
    have haU : a ∈ U := ⟨haM, haA⟩
    rw [← h] at haU
    exact haC haU
  have hU2 : IsPGroup 2 U :=
    (b612_isPGroup hA).of_injective (Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  have hmU : 0 < E3.mQuot U C := Nat.pos_of_ne_zero (by
    intro h0
    exact hne ((E3.mQuot_eq_zero_iff hU2 hCU).1 h0))
  have hUeq : E3.mQuot A U = E3.mQuot A M := by
    rw [E3.mQuot, E3.mQuot, hUdef, Subgroup.inf_relIndex_right]
  have hsum := E3.mQuot_add hCU inf_le_right
  rw [← hUeq, hsum]
  omega

end CFSG.LocalAnalysis.WeakClosure81
