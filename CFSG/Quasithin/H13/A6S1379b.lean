module

public import CFSG.Quasithin.H13.A6S1514
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def R8GenAt (σ : Perm (Fin 6)) : Prop :=
  σ ∈ R8 → σ ≠ 1 → σ ≠ swap 4 5 →
    σ * ((swap 0 1 * swap 1 2) * σ * (swap 0 1 * swap 1 2)⁻¹) ∈ K4L ∧
      σ * ((swap 0 1 * swap 1 2) * σ * (swap 0 1 * swap 1 2)⁻¹) ≠ 1

instance (σ : Perm (Fin 6)) : Decidable (R8GenAt σ) := by unfold R8GenAt; infer_instance

theorem r8GenAt_all : ∀ σ : Perm (Fin 6), R8GenAt σ := by decide +kernel

theorem K4L_orbit_c012 : ∀ κ ∈ K4L, κ ≠ 1 → ∀ τ ∈ K4L, τ ≠ 1 →
    τ = κ ∨ τ = (swap 0 1 * swap 1 2) * κ * (swap 0 1 * swap 1 2)⁻¹ ∨
      τ = (swap 0 1 * swap 1 2) * ((swap 0 1 * swap 1 2) * κ * (swap 0 1 * swap 1 2)⁻¹) *
        (swap 0 1 * swap 1 2)⁻¹ := by decide +kernel

@[expose] def CommW3At (x : P6) : Prop :=
  InW4 x → ∀ σ ∈ R8, InW3 (act4f σ x * x⁻¹)

instance (x : P6) : Decidable (CommW3At x) := by unfold CommW3At; infer_instance

theorem commW3At_all : ∀ x : P6, CommW3At x := by decide +kernel

@[expose] def W3CommAt (w : P6) : Prop :=
  InW4 w → InW3 w → ∃ σ ∈ K4L, ∃ x : P6, InW4 x ∧ w = act4f σ x * x⁻¹

instance (w : P6) : Decidable (W3CommAt w) := by unfold W3CommAt; infer_instance

theorem w3CommAt_all : ∀ w : P6, W3CommAt w := by decide +kernel

@[expose] def W3FixK4At (w : P6) : Prop :=
  InW4 w → InW3 w → act4f (swap 0 1 * swap 2 3) w = w → act4f (swap 0 2 * swap 1 3) w = w →
    w = 1 ∨ w = e0123

instance (w : P6) : Decidable (W3FixK4At w) := by unfold W3FixK4At; infer_instance

theorem w3FixK4At_all : ∀ w : P6, W3FixK4At w := by decide +kernel

theorem e0123_comm_W3 : ∃ σ ∈ K4L, ∃ w : P6, InW4 w ∧ InW3 w ∧ e0123 = act4f σ w * w⁻¹ := by
  decide

theorem fixW3_one : FixW3 1 := by decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pCoreOf_G1_le_QH {H : Subgroup G} (hT : T ≤ H) (hH1 : H ≤ S.G1) :
    pCoreOf 2 S.G1 ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le_of_sylow S.h13.sylow (hT.trans hH1)).trans hT)
    (hH1.trans (le_normalizer_pCoreOf 2 S.G1)) (pCoreOf_isPGroup 2 S.G1)

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hab in
theorem QH_le_T : pCoreOf 2 H ≤ T :=
  pCoreOf_le_of_sylow S.h13.sylow (S.hypF91 hNS h13315 h1356two hH).T_le_H

omit hab in
theorem rho_QH_mem_R8 {q : G} (hq : q ∈ pCoreOf 2 H) :
    ∃ hqN : q ∈ Subgroup.normalizer (V : Set G), S.frame.ρ ⟨q, hqN⟩ ∈ R8 := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hqN : q ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.T_le (S.QH_le_T hNS h13315 h1356two hH hq)
  refine ⟨hqN, mem_R8 _ ?_ ?_⟩
  ·
    have hqz : q * S.z * q⁻¹ = S.z := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hH.2.1 (pCoreOf_le 2 H hq))
      rw [h, mul_inv_cancel_right]
    have := (S.conj_eq_iff ⟨q, hqN⟩ ⟨S.z, S.z_mem_V⟩).1 hqz
    rw [S.psi_z] at this
    exact congrArg Subtype.val this
  ·
    intro x hx
    have hv3 := S.symm_mem_V3 (x := ⟨x, hx.1⟩) hx.2
    set v : G := ((S.frame.ψ.symm ⟨x, hx.1⟩ : ↥V) : G) with hv
    have hc := hF.commutator_conjClosure_le v (le_conjClosure _ _ hv3) q hq
    have hc' : q * v * q⁻¹ * v⁻¹ ∈ fsuV1 T V := by
      have e : q * v * q⁻¹ * v⁻¹ = (v * q * v⁻¹ * q⁻¹)⁻¹ := by group
      rw [e]
      exact (fsuV1 T V).inv_mem hc
    have hvV : v ∈ V := S.V3_le_V hv3
    have hm : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hqN v).mp hvV
    have hw : q * v * q⁻¹ * v⁻¹ ∈ V := V.mul_mem hm (V.inv_mem hvV)
    have hψ : ((S.frame.ψ ⟨_, hw⟩ : ↥W4) : P6) = act4f (S.frame.ρ ⟨q, hqN⟩) x * x⁻¹ := by
      have e : (⟨_, hw⟩ : ↥V) = ⟨_, hm⟩ * (⟨v, hvV⟩ : ↥V)⁻¹ := rfl
      have hψv : S.frame.ψ ⟨v, hvV⟩ = ⟨x, hx.1⟩ := S.frame.ψ.apply_symm_apply _
      rw [e, map_mul, map_inv, S.psi_conj ⟨q, hqN⟩ ⟨v, hvV⟩, hψv]
      rfl
    rw [← hψ]
    rcases S.mem_V1_iff.1 hc' with h1 | hz
    · left
      have : (⟨_, hw⟩ : ↥V) = 1 := Subtype.ext h1
      rw [this, map_one]
      rfl
    · right
      have : (⟨_, hw⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext hz
      rw [this, S.psi_z]

omit hab in
theorem K4_le_rho_QH (h13314 : Stmt13_3_14) :
    ∀ κ ∈ K4L, ∃ q ∈ pCoreOf 2 H, ∃ hqN : q ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨q, hqN⟩ = κ := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  obtain ⟨q, hq, hqN, hR, h1, h45⟩ : ∃ q ∈ pCoreOf 2 H, ∃ hqN : q ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨q, hqN⟩ ∈ R8 ∧ S.frame.ρ ⟨q, hqN⟩ ≠ 1 ∧ S.frame.ρ ⟨q, hqN⟩ ≠ swap 4 5 := by
    by_contra hcon
    push Not at hcon
    apply h13314 G T L V S.V2 S.h13 S.irr S.zv S.isV2 S.not_iso_a5
    intro x hx
    have hg1 : g1 T V = S.G1 := S.normalizer_V1
    rw [hg1] at hx
    have hxQ : x ∈ pCoreOf 2 H := S.pCoreOf_G1_le_QH hF.T_le_H hH.2.1 hx
    obtain ⟨hxN, hR⟩ := S.rho_QH_mem_R8 hNS h13315 h1356two hH hxQ
    have hfix : FixW3 (S.frame.ρ ⟨x, hxN⟩) := by
      by_cases h1 : S.frame.ρ ⟨x, hxN⟩ = 1
      · rw [h1]
        exact fixW3_one
      · rw [hcon x hxQ hxN hR h1]
        exact t_facts.1
    exact Subgroup.centralizer_le S.V2_le_V3 (S.centralizer_of_fixW3 hfix)
  obtain ⟨c, hcL1, hc⟩ := S.exists_L1_c012
  have hcH : (c : G) ∈ H := hF.L₁T_le_H (Subgroup.mem_sup_left hcL1)
  have hQN := le_normalizer_pCoreOf 2 H
  have hconj : ∀ y ∈ pCoreOf 2 H, ∀ hyN : y ∈ Subgroup.normalizer (V : Set G),
      ∃ y' ∈ pCoreOf 2 H, ∃ hy'N : y' ∈ Subgroup.normalizer (V : Set G),
        S.frame.ρ ⟨y', hy'N⟩ = (swap 0 1 * swap 1 2) * S.frame.ρ ⟨y, hyN⟩ *
          (swap 0 1 * swap 1 2)⁻¹ := by
    intro y hy hyN
    refine ⟨(c : G) * y * (c : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hQN hcH) y).mp hy,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hyN) (Subgroup.inv_mem _ c.2), ?_⟩
    have e : (⟨(c : G) * y * (c : G)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hyN)
        (Subgroup.inv_mem _ c.2)⟩ : ↥(Subgroup.normalizer (V : Set G))) = c * ⟨y, hyN⟩ * c⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_inv, hc]
  obtain ⟨q', hq', hq'N, hρq'⟩ := hconj q hq hqN
  obtain ⟨hK, hK1⟩ := r8GenAt_all _ hR h1 h45
  have hκ₀ : S.frame.ρ ⟨q * q', Subgroup.mul_mem _ hqN hq'N⟩ =
      S.frame.ρ ⟨q, hqN⟩ * ((swap 0 1 * swap 1 2) * S.frame.ρ ⟨q, hqN⟩ *
        (swap 0 1 * swap 1 2)⁻¹) := by
    have e : (⟨q * q', Subgroup.mul_mem _ hqN hq'N⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨q, hqN⟩ * ⟨q', hq'N⟩ := rfl
    rw [e, map_mul, hρq']
  intro κ hκ
  by_cases hκ1 : κ = 1
  · exact ⟨1, (pCoreOf 2 H).one_mem, Subgroup.one_mem _, by rw [hκ1]; exact map_one _⟩
  have hqq' : q * q' ∈ pCoreOf 2 H := (pCoreOf 2 H).mul_mem hq hq'
  rcases K4L_orbit_c012 _ hK hK1 κ hκ hκ1 with h | h | h
  · exact ⟨_, hqq', _, hκ₀.trans h.symm⟩
  · obtain ⟨y, hy, hyN, hρy⟩ := hconj _ hqq' (Subgroup.mul_mem _ hqN hq'N)
    exact ⟨y, hy, hyN, by rw [hρy, hκ₀, h]⟩
  · obtain ⟨y, hy, hyN, hρy⟩ := hconj _ hqq' (Subgroup.mul_mem _ hqN hq'N)
    obtain ⟨y', hy', hy'N, hρy'⟩ := hconj y hy hyN
    exact ⟨y', hy', hy'N, by rw [hρy', hρy, hκ₀, h]⟩

omit hab in
theorem comm_V_QH_mem_V3 {v q : G} (hv : v ∈ V)
    (hq : q ∈ pCoreOf 2 H) : q * v * q⁻¹ * v⁻¹ ∈ S.V3 := by
  obtain ⟨hqN, hR⟩ := S.rho_QH_mem_R8 hNS h13315 h1356two hH hq
  have hm : q * v * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hqN v).mp hv
  have hw : q * v * q⁻¹ * v⁻¹ ∈ V := V.mul_mem hm (V.inv_mem hv)
  refine S.mem_pre.2 ⟨hw, ?_⟩
  show InW3 ((S.frame.ψ ⟨_, hw⟩ : ↥W4) : P6)
  have e : (⟨_, hw⟩ : ↥V) = ⟨_, hm⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul, map_inv, S.psi_conj ⟨q, hqN⟩ ⟨v, hv⟩, Subgroup.coe_mul, Subgroup.coe_inv]
  exact commW3At_all _ (S.frame.ψ ⟨v, hv⟩).2 _ hR

omit hab in
theorem exists_comm_V_QH (h13314 : Stmt13_3_14) {w : G}
    (hw : w ∈ S.V3) : ∃ v ∈ V, ∃ q ∈ pCoreOf 2 H, w = q * v * q⁻¹ * v⁻¹ := by
  obtain ⟨hwV, hw3⟩ := S.mem_pre.1 hw
  obtain ⟨σ, hσ, x, hx, hwx⟩ := w3CommAt_all _ (S.frame.ψ ⟨w, hwV⟩).2 hw3
  obtain ⟨q, hq, hqN, hρq⟩ := S.K4_le_rho_QH hNS h13315 h1356two hH h13314 σ hσ
  set v : ↥V := S.frame.ψ.symm ⟨x, hx⟩ with hv
  have hψv : S.frame.ψ v = ⟨x, hx⟩ := S.frame.ψ.apply_symm_apply _
  have hm : q * (v : G) * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hqN v).mp v.2
  have hc : q * (v : G) * q⁻¹ * (v : G)⁻¹ ∈ V := V.mul_mem hm (V.inv_mem v.2)
  refine ⟨v, v.2, q, hq, ?_⟩
  have h1 : S.frame.ψ ⟨_, hc⟩ = S.frame.ψ ⟨w, hwV⟩ := by
    apply Subtype.ext
    have e : (⟨_, hc⟩ : ↥V) = ⟨_, hm⟩ * v⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_conj ⟨q, hqN⟩ v, hψv, Subgroup.coe_mul, Subgroup.coe_inv,
      hρq]
    exact hwx.symm
  exact (congrArg Subtype.val (S.frame.ψ.injective h1)).symm

omit hab in
theorem exists_z_comm_V3_QH (h13314 : Stmt13_3_14) :
    ∃ w ∈ S.V3, ∃ q ∈ pCoreOf 2 H, S.z = q * w * q⁻¹ * w⁻¹ := by
  obtain ⟨σ, hσ, y, hy4, hy3, hyz⟩ := e0123_comm_W3
  obtain ⟨q, hq, hqN, hρq⟩ := S.K4_le_rho_QH hNS h13315 h1356two hH h13314 σ hσ
  set w : ↥V := S.frame.ψ.symm ⟨y, hy4⟩ with hw
  have hψw : S.frame.ψ w = ⟨y, hy4⟩ := S.frame.ψ.apply_symm_apply _
  have hw3 : (w : G) ∈ S.V3 := S.symm_mem_V3 (x := ⟨y, hy4⟩) hy3
  have hm : q * (w : G) * q⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hqN w).mp w.2
  have hc : q * (w : G) * q⁻¹ * (w : G)⁻¹ ∈ V := V.mul_mem hm (V.inv_mem w.2)
  refine ⟨w, hw3, q, hq, ?_⟩
  have h1 : S.frame.ψ ⟨_, hc⟩ = S.frame.ψ ⟨S.z, S.z_mem_V⟩ := by
    apply Subtype.ext
    have e : (⟨_, hc⟩ : ↥V) = ⟨_, hm⟩ * w⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_conj ⟨q, hqN⟩ w, hψw, Subgroup.coe_mul, Subgroup.coe_inv,
      hρq, S.psi_z]
    exact hyz.symm
  exact (congrArg Subtype.val (S.frame.ψ.injective h1)).symm

omit hab in
theorem mem_V1_of_fix_QH (h13314 : Stmt13_3_14) {w : G}
    (hw : w ∈ S.V3) (hfix : ∀ q ∈ pCoreOf 2 H, q * w * q⁻¹ = w) : w ∈ fsuV1 T V := by
  obtain ⟨hwV, hw3⟩ := S.mem_pre.1 hw
  rw [S.mem_V1_iff]
  have key : ∀ σ ∈ K4L, act4f σ (S.frame.ψ ⟨w, hwV⟩ : P6) = (S.frame.ψ ⟨w, hwV⟩ : P6) := by
    intro σ hσ
    obtain ⟨q, hq, hqN, hρq⟩ := S.K4_le_rho_QH hNS h13315 h1356two hH h13314 σ hσ
    have h := (S.conj_eq_iff ⟨q, hqN⟩ ⟨w, hwV⟩).1 (hfix q hq)
    rw [hρq] at h
    exact congrArg Subtype.val h
  rcases w3FixK4At_all _ (S.frame.ψ ⟨w, hwV⟩).2 hw3 (key _ (by decide)) (key _ (by decide))
    with h | h
  · left
    have : (⟨w, hwV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
    exact congrArg Subtype.val this
  · right
    have : (⟨w, hwV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h)
    exact congrArg Subtype.val this

omit hab in
theorem comm_VH_QH_eq (h13314 : Stmt13_3_14) :
    ⁅conjClosure V H, pCoreOf 2 H⁆ = conjClosure S.V3 H := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hUN := le_normalizer_conjClosure S.V3 H
  have hQN := le_normalizer_pCoreOf 2 H
  apply le_antisymm
  ·
    let X : Subgroup G :=
      { carrier := {a | a ∈ H ∧ ∀ b ∈ pCoreOf 2 H, a * b * a⁻¹ * b⁻¹ ∈ conjClosure S.V3 H}
        mul_mem' := by
          rintro a₁ a₂ ⟨h1H, h1⟩ ⟨h2H, h2⟩
          refine ⟨H.mul_mem h1H h2H, fun b hb => ?_⟩
          have e : a₁ * a₂ * b * (a₁ * a₂)⁻¹ * b⁻¹ =
              a₁ * (a₂ * b * a₂⁻¹ * b⁻¹) * a₁⁻¹ * (a₁ * b * a₁⁻¹ * b⁻¹) := by group
          rw [e]
          exact (conjClosure S.V3 H).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hUN h1H) _).mp (h2 b hb)) (h1 b hb)
        one_mem' := ⟨H.one_mem, fun b _ => by simp⟩
        inv_mem' := by
          rintro a ⟨haH, h⟩
          refine ⟨H.inv_mem haH, fun b hb => ?_⟩
          have e : a⁻¹ * b * a⁻¹⁻¹ * b⁻¹ = a⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp (hUN (H.inv_mem haH)) _).mp
            ((conjClosure S.V3 H).inv_mem (h b hb)) }
    have hX : conjClosure V H ≤ X := by
      refine conjClosure_le fun h hh v hv => ⟨H.mul_mem (H.mul_mem hh (hF.V_le_H hv))
        (H.inv_mem hh), fun b hb => ?_⟩
      have hb' : h⁻¹ * b * h⁻¹⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hQN (H.inv_mem hh)) b).mp hb
      have hc := S.comm_V_QH_mem_V3 hNS h13315 h1356two hH hv hb'
      have hc' : v * (h⁻¹ * b * h⁻¹⁻¹) * v⁻¹ * (h⁻¹ * b * h⁻¹⁻¹)⁻¹ ∈ conjClosure S.V3 H := by
        have e : v * (h⁻¹ * b * h⁻¹⁻¹) * v⁻¹ * (h⁻¹ * b * h⁻¹⁻¹)⁻¹ =
            ((h⁻¹ * b * h⁻¹⁻¹) * v * (h⁻¹ * b * h⁻¹⁻¹)⁻¹ * v⁻¹)⁻¹ := by group
        rw [e]
        exact (conjClosure S.V3 H).inv_mem (le_conjClosure _ _ hc)
      have e : h * v * h⁻¹ * b * (h * v * h⁻¹)⁻¹ * b⁻¹ =
          h * (v * (h⁻¹ * b * h⁻¹⁻¹) * v⁻¹ * (h⁻¹ * b * h⁻¹⁻¹)⁻¹) * h⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hUN hh) _).mp hc'
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (hX ha).2 b hb
  · refine conjClosure_le fun h hh w hw => ?_
    obtain ⟨v, hv, q, hq, rfl⟩ := S.exists_comm_V_QH hNS h13315 h1356two hH h13314 hw
    have e : h * (q * v * q⁻¹ * v⁻¹) * h⁻¹ = ⁅h * q * h⁻¹, h * v * h⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [e, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator
      ((Subgroup.mem_normalizer_iff.mp (hQN hh) q).mp hq) (mem_conjClosure hh hv)

end Abelian

end Setting4

end CFSG.Quasithin.H13.A6
