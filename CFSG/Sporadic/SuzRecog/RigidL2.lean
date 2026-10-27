module

public import CFSG.Sporadic.SuzRecog.RigidL2Core
public import CFSG.Sporadic.Co1Patterson.AmalgamTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.RigidL2

open Subgroup CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

theorem invE_le_suzM : invE 1 ≤ suzM := fun _ hx => (invE_le_centM (by norm_num) hx).2

@[expose] noncomputable def t1' : ↥suzM := ⟨suzInv 1, invE_le_suzM SuzB0.suzInv_mem_invE⟩

@[expose] noncomputable def wq : ↥suzM := ⟨qVec 1, invE_le_suzM (qVec_mem_invE 1)⟩

theorem coe_t1' : ((t1' : ↥suzM) : Equiv.Perm (Fin 1782)) = suzInv 1 := rfl

theorem comm_t1' {x : ↥suzM} (hx : (x : Equiv.Perm (Fin 1782)) ∈ invE 1) : x * t1' = t1' * x :=
  Subtype.ext (comm_t1 ⟨_, hx⟩)

theorem mem_invE_iff {x : ↥suzM} :
    (x : Equiv.Perm (Fin 1782)) ∈ invE 1 ↔ x * t1' = t1' * x := by
  refine ⟨comm_t1', fun h => ?_⟩
  rw [invE_eq_centM (by norm_num)]
  exact ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val h), x.2⟩

theorem isoOn_conjM {c : ↥suzM} (hc : (c : Equiv.Perm (Fin 1782)) ∈ invE 1) :
    IsoOn (fun x : ↥(invE 1) => c * Subgroup.inclusion invE_le_suzM x * c⁻¹) K0
      (C[t1'] ⊓ C[c * wq * c⁻¹]) := by
  have hct : c * t1' = t1' * c := comm_t1' hc
  have hct' : c * t1' * c⁻¹ = t1' := by rw [hct, mul_inv_cancel_right]
  have hxt : ∀ x : ↥(invE 1), Subgroup.inclusion invE_le_suzM x ∈ C[t1'] := fun x =>
    mem_centralizer_singleton_iff.2 (comm_t1' x.2)
  have hxw : ∀ x ∈ K0, Subgroup.inclusion invE_le_suzM x ∈ C[wq] := fun x hx =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (coe_mem_K0.1 hx))
  refine ⟨fun x hx => mem_inf.2 ⟨?_, (mem_cent_conj_iff c _ wq).1 (hxw x hx)⟩,
    fun x _ y _ => ?_, fun x _ y _ h => ?_, fun y hy => ?_⟩
  · rw [← hct']
    exact (mem_cent_conj_iff c _ t1').1 (hxt x)
  · simp only [map_mul]
    group
  · exact Subgroup.inclusion_injective _ (mul_left_cancel (mul_right_cancel h))
  · obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
    have e1 : c⁻¹ * t1' * c⁻¹⁻¹ = t1' := by
      rw [inv_inv, mul_assoc, ← hct, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : c⁻¹ * (c * wq * c⁻¹) * c⁻¹⁻¹ = wq := by group
    have hz1 := (mem_cent_conj_iff c⁻¹ y t1').1 hy1
    have hz2 := (mem_cent_conj_iff c⁻¹ y _).1 hy2
    rw [e1] at hz1
    rw [e2] at hz2
    have hzE : ((c⁻¹ * y * c⁻¹⁻¹ : ↥suzM) : Equiv.Perm (Fin 1782)) ∈ invE 1 :=
      mem_invE_iff.2 (mem_centralizer_singleton_iff.1 hz1)
    refine ⟨⟨_, hzE⟩, coe_mem_K0.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz2)),
      ?_⟩
    have e3 : Subgroup.inclusion invE_le_suzM ⟨_, hzE⟩ = c⁻¹ * y * c⁻¹⁻¹ := rfl
    rw [e3]
    group

theorem coreOf_K0_le : coreOf K0 ≤ R0 :=
  le_R0 (coreOf_le K0)
    (fun k hk _ hp => (isoOn_conj k fun y => ⟨fun hy => mul_mem (mul_mem hk hy) (inv_mem hk),
      fun hy => by
        have e : y = k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hk) hy) (inv_mem (inv_mem hk))⟩).map_mem_coreOf hp)
    ((CFSG.pCore_isPGroup (p := 2)).map K0.subtype)

theorem autInnerModAt_of_conj {c : ↥suzM} (hc : (c : Equiv.Perm (Fin 1782)) ∈ invE 1) :
    AutInnerModAt t1' (c * wq * c⁻¹) := by
  intro ψ hψt hψw hψc
  obtain ⟨j, hj, hjt, hjw⟩ : ∃ j : ↥(invE 1) → ↥suzM,
      IsoOn j K0 (C[t1'] ⊓ C[c * wq * c⁻¹]) ∧ j t1C = t1' ∧ j w0C = c * wq * c⁻¹ :=
    ⟨_, isoOn_conjM hc, by
      have e : Subgroup.inclusion invE_le_suzM t1C = t1' := rfl
      rw [e, comm_t1' hc, mul_inv_cancel_right], rfl⟩
  have hE := isoOn_extFun ψ
  have hf : IsoOn (fun x => hj.inv (extFun ψ (j x))) K0 K0 := (hj.comp hE).comp hj.isoOn_inv
  have hfix : ∀ x ∈ K0, (∀ g : ↥(C[t1'] ⊓ C[c * wq * c⁻¹]), (g : ↥suzM) = j x → ψ g = g) →
      hj.inv (extFun ψ (j x)) = x := by
    intro x hx hψx
    have hxK := hj.map_mem x hx
    rw [extFun_of_mem ψ hxK, hψx ⟨_, hxK⟩ rfl]
    exact hj.inv_apply hx
  have ht := hfix _ (mem_K0.2 t1C_comm_w0C) fun g hg => hψt g (hg.trans hjt)
  have hw := hfix _ (mem_K0.2 rfl) fun g hg => hψw g (hg.trans hjw)
  have hfV : ∀ v ∈ vSub, hj.inv (extFun ψ (j v)) = v := by
    intro v hv
    rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
    · exact hf.map_one
    · exact ht
    · exact hw
    · rw [hf.map_mul _ (mem_K0.2 rfl) _ (mem_K0.2 t1C_comm_w0C), ht, hw]
  have hfR : ∀ g ∈ K0, hj.inv (extFun ψ (j g)) * g⁻¹ ∈ R0 := by
    intro g hg
    have hgK := hj.map_mem g hg
    have hc' : extFun ψ (j g) * (j g)⁻¹ ∈ coreOf (C[t1'] ⊓ C[c * wq * c⁻¹]) := by
      have h1 := (mem_coreOf_coe _).2 (hψc ⟨_, hgK⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [extFun_of_mem ψ hgK]
      exact h1
    have h2 := hj.isoOn_inv.map_mem_coreOf hc'
    have e : hj.inv (extFun ψ (j g) * (j g)⁻¹) = hj.inv (extFun ψ (j g)) * g⁻¹ := by
      rw [hj.isoOn_inv.map_mul _ (hE.map_mem _ hgK) _ (inv_mem hgK), hj.isoOn_inv.map_inv hgK,
        hj.inv_apply hg]
    rw [e] at h2
    exact coreOf_K0_le h2
  obtain ⟨s, hs, hfs⟩ := exists_conj_R0 hf hfV hfR
  refine ⟨j s, hj.map_mem s (R0_le_K0 hs), fun g' => ?_⟩
  have hg'K := g'.2
  have hgK₀ := hj.inv_mem hg'K
  have h1 := congrArg j (hfs _ hgK₀)
  have e1 : j (hj.inv (extFun ψ (j (hj.inv (g' : ↥suzM))))) = (ψ g' : ↥suzM) := by
    rw [hj.apply_inv hg'K, hj.apply_inv (hE.map_mem _ hg'K), extFun_of_mem ψ hg'K]
  have e2 : j (s * hj.inv (g' : ↥suzM) * s⁻¹) = j s * g' * (j s)⁻¹ := by
    rw [hj.map_conj (R0_le_K0 hs) hgK₀, hj.apply_inv hg'K]
  rw [← e1, ← e2]
  exact h1

theorem autInnerModAt_t1_wq : AutInnerModAt t1' wq := by
  have h := autInnerModAt_of_conj (c := 1) (one_mem _)
  rwa [one_mul, inv_one, mul_one] at h

end CFSG.Sporadic.SuzRecog.RigidL2
