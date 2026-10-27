module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7ModelAlg
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7SqA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod Equiv
open CFSG.LieType.BorelTits
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Gap7

namespace Model

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

structure Hyp (S : Subgroup G) (ρ : Geo H M) : Prop where
  hA : F53Amalgam H M S
  h26 : Hss26AAt H M
  hs : Sit43 ρ
  h3 : bMin H M = 3
  hS : ∀ δ ∈ nbrs ρ, Nat.card (Vn δ) = 2 ^ 6

omit [Finite G] in
theorem conj_mem_Wn {ρ : Geo H M} {g w : G} (hg : g ∈ stab ρ) (hw : w ∈ Wn ρ) :
    g * w * g⁻¹ ∈ Wn ρ :=
  (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn ρ hg) w).mp hw

omit [Finite G] in
theorem conj_mem_Vn {δ : Geo H M} {g v : G} (hg : g ∈ stab δ) (hv : v ∈ Vn δ) :
    g * v * g⁻¹ ∈ Vn δ :=
  (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg) v).mp hv

namespace Hyp

variable {S : Subgroup G} {ρ : Geo H M}

theorem hb (hy : Hyp S ρ) : 3 ≤ bMin H M := hy.h3.ge

theorem hρ (hy : Hyp S ρ) : vtype ρ = false := hy.hs.vα

theorem vtype_nbr (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) : vtype δ = true :=
  Sit43.vtype_true_of_adj hy.hρ hδ

theorem Wn_le_Qv (hy : Hyp S ρ) : Wn ρ ≤ Qv ρ := hy.hs.Wn_le_Qv hy.hA hy.hb

theorem comm_Wn_Qv (hy : Hyp S ρ) : ⁅Wn ρ, Qv ρ⁆ ≤ Zv ρ := by
  obtain ⟨δ, hδ⟩ := hy.hs.exists_adj hy.hA
  exact hy.hs.comm_Wn_Qv_le hy.hA hy.h26 hy.hb hy.hρ hδ (hy.hS δ hδ)

theorem comm_mem_of_mem_Qv (hy : Hyp S ρ) {w q : G} (hw : w ∈ Wn ρ) (hq : q ∈ Qv ρ) :
    ⁅w, q⁆ ∈ Zv ρ :=
  hy.comm_Wn_Qv (Subgroup.commutator_mem_commutator hw hq)

theorem comm_mem (hy : Hyp S ρ) {w w' : G} (hw : w ∈ Wn ρ) (hw' : w' ∈ Wn ρ) :
    ⁅w, w'⁆ ∈ Zv ρ :=
  comm_Wn_le_Zv hy.hA hy.h26 hy.hs hy.h3 hy.hρ hy.hS (Subgroup.commutator_mem_commutator hw hw')

theorem cen (hy : Hyp S ρ) {q z : G} (hq : q ∈ Qv ρ) (hz : z ∈ Zv ρ) : q * z = z * q :=
  (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hy.hA ρ hq) z hz).symm

theorem conj_eq_self (hy : Hyp S ρ) {q z : G} (hq : q ∈ Qv ρ) (hz : z ∈ Zv ρ) :
    q * z * q⁻¹ = z := by
  rw [hy.cen hq hz, mul_inv_cancel_right]

theorem Zv_comm (hy : Hyp S ρ) {z z' : G} (hz : z ∈ Zv ρ) (hz' : z' ∈ Zv ρ) :
    z * z' = z' * z :=
  comm_of_mem_isElemAbelian (isElemAbelian_Zv hy.hA ρ) hz hz'

theorem Zv_sq (hy : Hyp S ρ) {z : G} (hz : z ∈ Zv ρ) : z * z = 1 := by
  rw [← pow_two]
  exact (isElemAbelian_Zv hy.hA ρ).2 z hz

theorem conj_mem_Zv (hy : Hyp S ρ) {g z : G} (hg : g ∈ stab ρ) (hz : z ∈ Zv ρ) :
    g * z * g⁻¹ ∈ Zv ρ :=
  (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hy.hA ρ hg) z).mp hz

theorem Vn_le_Wn (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) : Vn δ ≤ Wn ρ :=
  hy.hs.Vn_le_Wn hy.hA hy.h26 hδ

theorem Vn_comm (hy : Hyp S ρ) {δ : Geo H M} {v v' : G} (hv : v ∈ Vn δ) (hv' : v' ∈ Vn δ) :
    v * v' = v' * v :=
  comm_of_mem_isElemAbelian (isElemAbelian_Vn hy.hA hy.hb δ) hv hv'

theorem Vn_sq (hy : Hyp S ρ) {δ : Geo H M} {v : G} (hv : v ∈ Vn δ) : v * v = 1 := by
  rw [← pow_two]
  exact (isElemAbelian_Vn hy.hA hy.hb δ).2 v hv

theorem Qv_le_stab_nbr (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) : Qv ρ ≤ stab δ :=
  Qv_le_stab_of_mem_nbrs hy.hA hδ

theorem Zv_le_Qv_nbr (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) : Zv ρ ≤ Qv δ :=
  hy.hs.Zv_le_Qv_of_dist_lt_false hy.hρ (by rw [dist_eq_one_iff_adj.mpr hδ, hy.h3]; omega)

theorem conj_eq_of_mem_Qv (hy : Hyp S ρ) {q w : G} (hq : q ∈ Qv ρ) (hw : w ∈ Wn ρ) :
    ∃ z ∈ Zv ρ, q * w * q⁻¹ = z * w := by
  refine ⟨⁅q, w⁆, ?_, by rw [commutatorElement_def]; group⟩
  rw [← commutatorElement_inv]
  exact (Zv ρ).inv_mem (hy.comm_mem_of_mem_Qv hw hq)

theorem comm_mem_Yv_of_mem_Qv (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {x : G}
    (hxW : x ∈ Wn ρ) (hxQ : x ∈ Qv δ) {v : G} (hv : v ∈ Vn δ) : ⁅v, x⁆ ∈ Yv δ :=
  hy.hs.comm_Vn_inf_le hy.hA hy.h26 hy.hρ hδ
    (Subgroup.commutator_mem_commutator hv ⟨hy.Wn_le_Qv hxW, hxQ⟩)

theorem comm_mem_Yv_of_mem_Qv' (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {x : G}
    (hxW : x ∈ Wn ρ) (hxQ : x ∈ Qv δ) {v : G} (hv : v ∈ Vn δ) : ⁅x, v⁆ ∈ Yv δ := by
  rw [← commutatorElement_inv]
  exact (Yv δ).inv_mem (hy.comm_mem_Yv_of_mem_Qv hδ hxW hxQ hv)

theorem comm_mul_inv_mem_Yv (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {x x' : G}
    (hx : x ∈ Wn ρ) (hx' : x' ∈ Wn ρ) (hxQ : x ∉ Qv δ) (hxQ' : x' ∉ Qv δ) {v : G}
    (hv : v ∈ Vn δ) : ⁅x, v⁆ * ⁅x', v⁆⁻¹ ∈ Yv δ := by
  have hxQρ := hy.Wn_le_Qv hx
  have hxe : x ∈ stab ρ ⊓ stab δ := ⟨pCoreOf_le 2 _ hxQρ, hy.Qv_le_stab_nbr hδ hxQρ⟩
  have hxe' : x' ∈ stab ρ ⊓ stab δ :=
    ⟨pCoreOf_le 2 _ (hy.Wn_le_Qv hx'), hy.Qv_le_stab_nbr hδ (hy.Wn_le_Qv hx')⟩
  have hc : x⁻¹ * x' ∈ Qv δ :=
    inv_mul_mem_of_relIndex_two (Sit43.relIndex_Qv_edge hy.hA hy.hρ hδ) hxe hxe' hxQ hxQ'
  have hcW : x⁻¹ * x' ∈ Wn ρ := (Wn ρ).mul_mem ((Wn ρ).inv_mem hx) hx'
  have hY : ⁅x⁻¹ * x', v⁆ ∈ Yv δ := hy.comm_mem_Yv_of_mem_Qv' hδ hcW hc hv
  have hYZ : ⁅x⁻¹ * x', v⁆ ∈ Zv ρ := Yv_le_Zv (nbrs_symm hδ) hY
  have e : ⁅x', v⁆ = ⁅x⁻¹ * x', v⁆ * ⁅x, v⁆ := by
    have e1 : x' = x * (x⁻¹ * x') := by group
    conv_lhs => rw [e1]
    rw [comm_mul_left_eq, hy.cen hxQρ hYZ, mul_inv_cancel_right]
  rw [e, mul_inv_rev, mul_inv_cancel_left]
  exact (Yv δ).inv_mem hY

theorem mem_Zv_of_comm_mem_Yv (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {x : G}
    (hxW : x ∈ Wn ρ) (hxQ : x ∉ Qv δ) {v : G} (hv : v ∈ Vn δ) (hvx : ⁅v, x⁆ ∈ Yv δ) :
    v ∈ Zv ρ := by
  have hδv := hy.vtype_nbr hδ
  have hρδ : ρ ∈ nbrs δ := nbrs_symm hδ
  have hxQρ := hy.Wn_le_Qv hxW
  have hxC : x ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) :=
    Sit43.Qv_le_centralizer_Yv hy.hA hρδ hxQρ
  have hxe : x ∈ stab ρ ⊓ stab δ := ⟨pCoreOf_le 2 _ hxQρ, hxC.1⟩
  have hL3 := hy.hs.comm_sup_Yv_eq hy.hA hy.h26 hy.hb hδv hρδ hxe hxC.2 hxQ (hy.hS δ hδ)
  have hYZ : Yv δ ≤ Zv ρ := Yv_le_Zv hρδ
  have hf : ∀ w ∈ Vn δ, ⁅w, x⁆ ∈ Zv ρ := fun w hw =>
    hy.comm_mem_of_mem_Qv (hy.Vn_le_Wn hδ hw) hxQρ
  have hfmul : ∀ a ∈ Vn δ, ∀ b ∈ Vn δ, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro a ha b hb
    rw [comm_mul_left_eq, hy.conj_eq_self (hy.Wn_le_Qv (hy.Vn_le_Wn hδ ha)) (hf b hb),
      hy.Zv_comm (hf b hb) (hf a ha)]
  let R : Subgroup G :=
    { carrier := {r | r ∈ Zv ρ ∧ ∃ w ∈ Vn δ, ⁅w, x⁆⁻¹ * r ∈ Yv δ}
      one_mem' := ⟨(Zv ρ).one_mem, 1, (Vn δ).one_mem, by simp⟩
      mul_mem' := by
        rintro r r' ⟨hr, w, hw, hwr⟩ ⟨hr', w', hw', hwr'⟩
        refine ⟨(Zv ρ).mul_mem hr hr', w * w', (Vn δ).mul_mem hw hw', ?_⟩
        have e : ⁅w * w', x⁆⁻¹ * (r * r') = (⁅w, x⁆⁻¹ * r) * (⁅w', x⁆⁻¹ * r') := by
          rw [hfmul w hw w' hw', mul_inv_rev,
            hy.Zv_comm ((Zv ρ).inv_mem (hf w' hw')) ((Zv ρ).inv_mem (hf w hw))]
          have h1 := hy.Zv_comm hr ((Zv ρ).inv_mem (hf w' hw'))
          calc ⁅w, x⁆⁻¹ * ⁅w', x⁆⁻¹ * (r * r') = ⁅w, x⁆⁻¹ * (⁅w', x⁆⁻¹ * r) * r' := by group
            _ = ⁅w, x⁆⁻¹ * (r * ⁅w', x⁆⁻¹) * r' := by rw [h1]
            _ = ⁅w, x⁆⁻¹ * r * (⁅w', x⁆⁻¹ * r') := by group
        rw [e]
        exact (Yv δ).mul_mem hwr hwr'
      inv_mem' := by
        rintro r ⟨hr, w, hw, hwr⟩
        refine ⟨(Zv ρ).inv_mem hr, w⁻¹, (Vn δ).inv_mem hw, ?_⟩
        have hw1 : ⁅w⁻¹, x⁆ = ⁅w, x⁆⁻¹ := by
          have h1 := hfmul w hw w⁻¹ ((Vn δ).inv_mem hw)
          rw [mul_inv_cancel, commutatorElement_one_left] at h1
          exact (eq_inv_of_mul_eq_one_right h1.symm)
        have e : ⁅w⁻¹, x⁆⁻¹ * r⁻¹ = (⁅w, x⁆⁻¹ * r)⁻¹ := by
          rw [hw1, inv_inv, mul_inv_rev, inv_inv, hy.Zv_comm ((Zv ρ).inv_mem hr) (hf w hw)]
        rw [e]
        exact (Yv δ).inv_mem hwr }
  have hxR : x ∈ Subgroup.normalizer (R : Set G) :=
    Three.mem_normalizer_of_conjSub_eq (Three.conjSub_eq_self fun r hr => hy.cen hxQρ hr.1)
  have hcR : ⁅Vn δ, Subgroup.zpowers x⁆ ≤ R :=
    commutator_zpowers_le hxR fun w hw => ⟨hf w hw, w, hw, by
      rw [inv_mul_cancel]
      exact (Yv δ).one_mem⟩
  have hYR : Yv δ ≤ R := fun y hy' => ⟨hYZ hy', 1, (Vn δ).one_mem, by simpa using hy'⟩
  have hZR : Zv ρ ≤ R := hL3 ▸ sup_le hcR hYR
  let Y' : Subgroup ↥(Zv ρ) := (Yv δ).subgroupOf (Zv ρ)
  have hYn : Y'.Normal := ⟨fun n hn g => by
    have e : ((g * n * g⁻¹ : ↥(Zv ρ)) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hy.Zv_comm g.2 n.2, mul_inv_cancel_right]
    show ((g * n * g⁻¹ : ↥(Zv ρ)) : G) ∈ Yv δ
    rw [e]
    exact hn⟩
  let f : ↥(Vn δ) →* ↥(Zv ρ) :=
    { toFun := fun w => ⟨⁅(w : G), x⁆, hf w w.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul]
        exact hfmul a a.2 b b.2 }
  let F : ↥(Vn δ) →* ↥(Zv ρ) ⧸ Y' := (QuotientGroup.mk' Y').comp f
  have hFs : Function.Surjective F := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨-, w, hw, hwz⟩ := hZR z.2
    refine ⟨⟨w, hw⟩, ?_⟩
    show (QuotientGroup.mk (f ⟨w, hw⟩) : ↥(Zv ρ) ⧸ Y') = QuotientGroup.mk z
    rw [QuotientGroup.eq]
    exact hwz
  have hker : ∀ w : ↥(Vn δ), w ∈ F.ker ↔ ⁅(w : G), x⁆ ∈ Yv δ := by
    intro w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rfl
  have hidx : F.ker.index = 4 := by
    have e1 : F.ker.index = Y'.index :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F hFs).toEquiv
    rw [e1]
    have h1 := Subgroup.relIndex_mul_card (Yv δ) (Zv ρ)
    rw [inf_eq_left.mpr hYZ, hy.hs.card_Zv_false hy.hρ, hy.hs.card_Yv hy.hA hy.h26 hδv] at h1
    show (Yv δ).relIndex (Zv ρ) = 4
    omega
  have hZker : (Zv ρ).subgroupOf (Vn δ) ≤ F.ker := fun w hw => by
    have hw' : (w : G) ∈ Zv ρ := Subgroup.mem_subgroupOf.mp hw
    rw [hker, (commutatorElement_eq_one_iff_mul_comm).mpr (hy.cen hxQρ hw').symm]
    exact (Yv δ).one_mem
  have hZidx : ((Zv ρ).subgroupOf (Vn δ)).index = 4 :=
    hy.hs.relIndex_Zv_Vn hy.hρ hδ (hy.hS δ hδ)
  have h2 := Subgroup.relIndex_mul_index hZker
  rw [hidx, hZidx] at h2
  have h3 : ((Zv ρ).subgroupOf (Vn δ)).relIndex F.ker = 1 := by omega
  have hmem : (⟨v, hv⟩ : ↥(Vn δ)) ∈ F.ker := (hker _).mpr hvx
  exact Subgroup.mem_subgroupOf.mp (Subgroup.relIndex_eq_one.mp h3 hmem)

theorem comm_not_mem_Yv (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {x : G}
    (hxW : x ∈ Wn ρ) (hxQ : x ∉ Qv δ) {v : G} (hv : v ∈ Vn δ) (hvZ : v ∉ Zv ρ) :
    ⁅x, v⁆ ∉ Yv δ := fun h =>
  hvZ (hy.mem_Zv_of_comm_mem_Yv hδ hxW hxQ hv (by
    rw [← commutatorElement_inv]
    exact (Yv δ).inv_mem h))

theorem mem_Qv_of_comm_mem_Yv (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {x : G}
    (hxW : x ∈ Wn ρ) {v : G} (hv : v ∈ Vn δ) (hvZ : v ∉ Zv ρ) (h : ⁅x, v⁆ ∈ Yv δ) :
    x ∈ Qv δ := by
  by_contra hxQ
  exact hy.comm_not_mem_Yv hδ hxW hxQ hv hvZ h

theorem pcond_one (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {a b : G} (ha : a ∈ Vn δ)
    (hb : b ∈ Vn δ) {x x' : G} (hx : x ∈ Wn ρ) (hx' : x' ∈ Wn ρ) :
    (⁅x, a⁆ ∈ Yv δ ∧ ⁅x, b⁆ ∈ Yv δ) ∨ (⁅x', a⁆ ∈ Yv δ ∧ ⁅x', b⁆ ∈ Yv δ) ∨
      (⁅x, a⁆ * ⁅x', a⁆⁻¹ ∈ Yv δ ∧ ⁅x, b⁆ * ⁅x', b⁆⁻¹ ∈ Yv δ) := by
  by_cases hxQ : x ∈ Qv δ
  · exact Or.inl ⟨hy.comm_mem_Yv_of_mem_Qv' hδ hx hxQ ha, hy.comm_mem_Yv_of_mem_Qv' hδ hx hxQ hb⟩
  by_cases hxQ' : x' ∈ Qv δ
  · exact Or.inr (Or.inl ⟨hy.comm_mem_Yv_of_mem_Qv' hδ hx' hxQ' ha,
      hy.comm_mem_Yv_of_mem_Qv' hδ hx' hxQ' hb⟩)
  exact Or.inr (Or.inr ⟨hy.comm_mul_inv_mem_Yv hδ hx hx' hxQ hxQ' ha,
    hy.comm_mul_inv_mem_Yv hδ hx hx' hxQ hxQ' hb⟩)

theorem pcond_two (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {a b : G} (ha : a ∈ Vn δ)
    (hb : b ∈ Vn δ) (haZ : a ∉ Zv ρ) (hbZ : b ∉ Zv ρ) (habZ : a * b⁻¹ ∉ Zv ρ) {x : G}
    (hx : x ∈ Wn ρ) (h : ¬ (⁅x, a⁆ ∈ Yv δ ∧ ⁅x, b⁆ ∈ Yv δ)) :
    ⁅x, a⁆ ∉ Yv δ ∧ ⁅x, b⁆ ∉ Yv δ ∧ ⁅x, a⁆ * ⁅x, b⁆⁻¹ ∉ Yv δ := by
  have hxQ : x ∉ Qv δ := fun hxQ =>
    h ⟨hy.comm_mem_Yv_of_mem_Qv' hδ hx hxQ ha, hy.comm_mem_Yv_of_mem_Qv' hδ hx hxQ hb⟩
  refine ⟨hy.comm_not_mem_Yv hδ hx hxQ ha haZ, hy.comm_not_mem_Yv hδ hx hxQ hb hbZ, ?_⟩
  have hbW : b ∈ Wn ρ := hy.Vn_le_Wn hδ hb
  have hz : ⁅x, b⁆⁻¹ ∈ Zv ρ := (Zv ρ).inv_mem (hy.comm_mem hx hbW)
  have e : ⁅x, a * b⁻¹⁆ = ⁅x, a⁆ * ⁅x, b⁆⁻¹ := by
    rw [comm_mul_right_eq, comm_inv_right_eq,
      show b⁻¹ * ⁅x, b⁆⁻¹ * b = ⁅x, b⁆⁻¹ by
        rw [mul_assoc, ← hy.cen (hy.Wn_le_Qv hbW) hz, inv_mul_cancel_left],
      hy.conj_eq_self (hy.Wn_le_Qv (hy.Vn_le_Wn hδ ha)) hz]
  rw [← e]
  exact hy.comm_not_mem_Yv hδ hx hxQ ((Vn δ).mul_mem ha ((Vn δ).inv_mem hb)) habZ

theorem Vn_le_sup_closure (hy : Hyp S ρ) {δ : Geo H M} (hδ : δ ∈ nbrs ρ) {a b : G}
    (ha : a ∈ Vn δ) (hb : b ∈ Vn δ) (haZ : a ∉ Zv ρ) (hbZ : b ∉ Zv ρ) (habZ : a * b⁻¹ ∉ Zv ρ) :
    Vn δ ≤ Zv ρ ⊔ Subgroup.closure {a, b} := by
  set N : Subgroup G := Zv ρ ⊔ Subgroup.closure {a, b} with hN
  have hZN : Zv ρ ≤ N := le_sup_left
  have haN : a ∈ N := (le_sup_right : Subgroup.closure {a, b} ≤ N)
    (Subgroup.subset_closure (by simp))
  have hbN : b ∈ N := (le_sup_right : Subgroup.closure {a, b} ≤ N)
    (Subgroup.subset_closure (by simp))
  have hNV : N ≤ Vn δ := sup_le (Sit43.Zv_le_Vn hδ)
    ((Subgroup.closure_le _).mpr (by simp [Set.insert_subset_iff, ha, hb]))
  have h4 : (Zv ρ).relIndex (Vn δ) = 4 := hy.hs.relIndex_Zv_Vn hy.hρ hδ (hy.hS δ hδ)
  have hmul := Subgroup.relIndex_mul_relIndex (Zv ρ) N (Vn δ) hZN hNV
  rw [h4] at hmul
  have h1 : (Zv ρ).relIndex N ≠ 1 := fun h => haZ (Subgroup.relIndex_eq_one.mp h haN)
  have h2 : (Zv ρ).relIndex N ≠ 2 := fun h => by
    have h' := inv_mul_mem_of_relIndex_two h haN hbN haZ hbZ
    apply habZ
    have e : a * b⁻¹ = (a⁻¹ * b)⁻¹ := by
      rw [mul_inv_rev, inv_inv, hy.Vn_comm ha ((Vn δ).inv_mem hb)]
    rw [e]
    exact (Zv ρ).inv_mem h'
  have hr : (Zv ρ).relIndex N = 4 := by
    have hpos : 0 < (Zv ρ).relIndex N := by
      rcases Nat.eq_zero_or_pos ((Zv ρ).relIndex N) with h | h
      · rw [h, zero_mul] at hmul
        omega
      · exact h
    have hle : (Zv ρ).relIndex N ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
    interval_cases hr : (Zv ρ).relIndex N
    · exact absurd rfl h1
    · exact absurd rfl h2
    · omega
    · rfl
  rw [hr] at hmul
  have h3 : N.relIndex (Vn δ) = 1 := by omega
  exact Subgroup.relIndex_eq_one.mp h3

end Hyp

end Model

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
