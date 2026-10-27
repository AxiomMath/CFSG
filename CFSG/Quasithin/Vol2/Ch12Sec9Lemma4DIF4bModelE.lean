module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelT
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelK2

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def psiN (Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)) :
    CFSG.pCore 2 ↥(Hm ⊓ Ω) →* ↥Hm :=
  (Subgroup.inclusion (inf_le_left : Hm ⊓ Ω ≤ Hm)).comp (CFSG.pCore 2 ↥(Hm ⊓ Ω)).subtype

theorem psiN_val (Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)) (n : CFSG.pCore 2 ↥(Hm ⊓ Ω)) :
    ((psiN Ω n : ↥Hm) : VM ≃ₗ[ZMod 2] VM) = ((n : ↥(Hm ⊓ Ω)) : VM ≃ₗ[ZMod 2] VM) := rfl

theorem conj_mem_inf {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) {g : VM ≃ₗ[ZMod 2] VM} (hg : g ∈ Hm) :
    ∀ x ∈ Hm ⊓ Ω, g * x * g⁻¹ ∈ Hm ⊓ Ω := by
  intro x hx
  refine Subgroup.mem_inf.2 ⟨?_, conj_mem_Omega hΩG hrel ((mem_Hm_iff g).1 hg).1
    (Subgroup.mem_inf.1 hx).2⟩
  exact Hm.mul_mem (Hm.mul_mem hg (Subgroup.mem_inf.1 hx).1) (Hm.inv_mem hg)

theorem Fx_invariant {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) (h : ↥Hm) (c : TX)
    (hc : ∀ m : CFSG.pCore 2 ↥(Hm ⊓ Ω), psiN Ω m • c = c)
    (m : CFSG.pCore 2 ↥(Hm ⊓ Ω)) : psiN Ω m • (h • c) = h • c := by
  have hgH : ((h : VM ≃ₗ[ZMod 2] VM))⁻¹ ∈ Hm := Hm.inv_mem h.2
  have hg : ∀ x ∈ Hm ⊓ Ω, ((h : VM ≃ₗ[ZMod 2] VM))⁻¹ * x * ((h : VM ≃ₗ[ZMod 2] VM))⁻¹⁻¹ ∈
      Hm ⊓ Ω := conj_mem_inf hΩG hrel hgH
  have hg' : ∀ x ∈ Hm ⊓ Ω, ((h : VM ≃ₗ[ZMod 2] VM))⁻¹⁻¹ * x * ((h : VM ≃ₗ[ZMod 2] VM))⁻¹ ∈
      Hm ⊓ Ω := by
    intro x hx
    rw [inv_inv]
    exact conj_mem_inf hΩG hrel h.2 x hx
  have hmem := pCoreOf_conj_mem 2 (Hm ⊓ Ω) ((h : VM ≃ₗ[ZMod 2] VM))⁻¹ hg hg'
    ((m : ↥(Hm ⊓ Ω)) : VM ≃ₗ[ZMod 2] VM) (Subgroup.mem_map.2 ⟨m.1, m.2, rfl⟩)
  obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 hmem
  have hwv : ((w : ↥(Hm ⊓ Ω)) : VM ≃ₗ[ZMod 2] VM) =
      (h : VM ≃ₗ[ZMod 2] VM)⁻¹ * ((m : ↥(Hm ⊓ Ω)) : VM ≃ₗ[ZMod 2] VM) * (h : VM ≃ₗ[ZMod 2] VM) := by
    have := hwg
    rw [inv_inv] at this
    exact this
  have hym : psiN Ω ⟨w, hw⟩ = (h⁻¹ : ↥Hm) * psiN Ω m * h := by
    apply Subtype.ext
    rw [psiN_val]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hwv]
    rfl
  have hsm : psiN Ω m = h * ((h⁻¹ : ↥Hm) * psiN Ω m * h) * h⁻¹ := by group
  rw [hsm, mul_smul, mul_smul, inv_smul_smul, ← hym, hc ⟨w, hw⟩]

theorem exists_fixed_TX {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} :
    ∃ c0 : TX, ∀ n : CFSG.pCore 2 ↥(Hm ⊓ Ω), psiN Ω n • c0 = c0 := by
  letI : MulAction (CFSG.pCore 2 ↥(Hm ⊓ Ω)) TX := MulAction.compHom TX (psiN Ω)
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥(Hm ⊓ Ω)) :=
    CFSG.pCore_isPGroup (p := 2) (G := ↥(Hm ⊓ Ω))
  have hcong := hp.card_modEq_card_fixedPoints (α := TX)
  have h9 : Nat.card TX = 9 := by
    rw [Nat.card_eq_fintype_card, card_TX]
  have hne : Nat.card (MulAction.fixedPoints (CFSG.pCore 2 ↥(Hm ⊓ Ω)) TX) ≠ 0 := by
    intro h0
    rw [h9, h0] at hcong
    exact absurd hcong (by decide)
  obtain ⟨⟨c0, hc0⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  exact ⟨c0, fun n => MulAction.mem_fixedPoints.1 hc0 n⟩

theorem pCore_fixes_TX {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) (n : CFSG.pCore 2 ↥(Hm ⊓ Ω)) (c : TX) :
    psiN Ω n • c = c := by
  obtain ⟨c0, hc0⟩ := exists_fixed_TX (Ω := Ω)
  obtain ⟨g, hg⟩ := Hm_trans_TX c0 c
  have hc : ∀ m : CFSG.pCore 2 ↥(Hm ⊓ Ω), psiN Ω m • c0 = c0 := hc0
  have hfix : ∀ m : CFSG.pCore 2 ↥(Hm ⊓ Ω), psiN Ω m • (g • c0) = g • c0 :=
    fun m => Fx_invariant hΩG hrel g c0 hc m
  rw [← hg]
  exact hfix n

theorem gamma_on_U {γ : VM ≃ₗ[ZMod 2] VM} (hγ : γ ∈ Hm) {u : VM} (hu : inU u)
    (hfix : projU (γ u) = u) : ∃ a : ZMod 2, γ u = a • e0 + u := by
  have hγ' := (mem_Hm_iff γ).1 hγ
  have hr : (γ u) (Sum.inr 0) = 0 := by
    rw [← bM_e0_right (γ u), ← hγ'.2, bM_of_GM hγ'.1 u e0, bM_e0_right]
    exact hu.2
  have h := projU_decomp (γ u)
  rw [hr, hfix, zero_smul, add_zero] at h
  exact ⟨_, h⟩

theorem Kw_of_fixU {γ : VM ≃ₗ[ZMod 2] VM} (hγ : γ ∈ Hm)
    (h1 : ∃ a : ZMod 2, γ E1 = a • e0 + E1) (h2 : ∃ a : ZMod 2, γ E2 = a • e0 + E2)
    (h3 : ∃ a : ZMod 2, γ F1 = a • e0 + F1) (h4 : ∃ a : ZMod 2, γ F2 = a • e0 + F2) : γ ∈ Kw := by
  have hγ' := (mem_Hm_iff γ).1 hγ
  refine (mem_Kw_iff γ).2 ⟨hγ'.1, hγ'.2, fun x hx => ?_⟩
  let Good : Submodule (ZMod 2) VM :=
    { carrier := {v | γ v - v ∈ Submodule.span (ZMod 2) ({e0} : Set VM)}
      add_mem' := fun {v w} hv hw => by
        change γ (v + w) - (v + w) ∈ Submodule.span (ZMod 2) ({e0} : Set VM)
        have e : γ (v + w) - (v + w) = (γ v - v) + (γ w - w) := by
          rw [map_add]
          abel
        rw [e]
        exact Submodule.add_mem _ hv hw
      zero_mem' := by
        change γ 0 - 0 ∈ Submodule.span (ZMod 2) ({e0} : Set VM)
        rw [map_zero, sub_self_VM]
        exact Submodule.zero_mem _
      smul_mem' := fun a {v} hv => by
        change γ (a • v) - (a • v) ∈ Submodule.span (ZMod 2) ({e0} : Set VM)
        have e : γ (a • v) - (a • v) = a • (γ v - v) := by
          rw [map_smul]
          exact (smul_sub a (γ v) v).symm
        rw [e]
        exact Submodule.smul_mem _ _ hv }
  have hmem : ∀ v ∈ ({e0, E1, E2, F1, F2} : Set VM),
      v ∈ (Good : Submodule (ZMod 2) VM) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    change γ v - v ∈ Submodule.span (ZMod 2) ({e0} : Set VM)
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [hγ'.2, sub_self_VM]
      exact Submodule.zero_mem _
    · obtain ⟨a, ha⟩ := h1
      rw [ha]
      have e : a • e0 + E1 - E1 = a • e0 := by abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e0)
    · obtain ⟨a, ha⟩ := h2
      rw [ha]
      have e : a • e0 + E2 - E2 = a • e0 := by abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e0)
    · obtain ⟨a, ha⟩ := h3
      rw [ha]
      have e : a • e0 + F1 - F1 = a • e0 := by abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e0)
    · obtain ⟨a, ha⟩ := h4
      rw [ha]
      have e : a • e0 + F2 - F2 = a • e0 := by abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e0)
  have hspan : Submodule.span (ZMod 2) ({e0, E1, E2, F1, F2} : Set VM) ≤ Good :=
    Submodule.span_le.2 (fun v hv => hmem v hv)
  have hx' : x (Sum.inr 0) = 0 := by
    rw [← bM_e0_right x]
    exact hx
  have hdec : x = x (Sum.inl 0) • e0 + x (Sum.inl 1) • E1 + x (Sum.inl 2) • E2 +
      x (Sum.inr 1) • F1 + x (Sum.inr 2) • F2 := by
    have := decomp6 x
    rw [hx', zero_smul, add_zero] at this
    exact this
  have hxmem : x ∈ Submodule.span (ZMod 2) ({e0, E1, E2, F1, F2} : Set VM) := by
    rw [hdec]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
      ?_) ?_) ?_ <;> exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact hspan hxmem

theorem pCore_le_Kw {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) (γ : VM ≃ₗ[ZMod 2] VM) (hγ : γ ∈ CFSG.Open.pCoreOf 2 (Hm ⊓ Ω)) :
    γ ∈ Kw := by
  obtain ⟨m, hm, hmγ⟩ := Subgroup.mem_map.1 hγ
  have hγH : γ ∈ Hm := (Subgroup.mem_inf.1 m.2).1 |> fun h => by
    rw [← hmγ]
    exact h
  have hpsi : ((psiN Ω ⟨m, hm⟩ : ↥Hm) : VM ≃ₗ[ZMod 2] VM) = γ := by
    rw [psiN_val]
    exact hmγ
  have hf : ∀ u : VM, inU u → qM u = 0 → u ≠ 0 → projU (γ u) = u := by
    intro u hu hq h0
    have h : projU (((psiN Ω ⟨m, hm⟩ : ↥Hm) : VM ≃ₗ[ZMod 2] VM) u) = u :=
      congrArg Subtype.val (pCore_fixes_TX hΩG hrel ⟨m, hm⟩ ⟨u, hu, hq, h0⟩)
    rw [hpsi] at h
    exact h
  have hE1 := gamma_on_U hγH (by decide) (hf E1 (by decide) (by decide) (by decide))
  have hE2 := gamma_on_U hγH (by decide) (hf E2 (by decide) (by decide) (by decide))
  have hF1 := gamma_on_U hγH (by decide) (hf F1 (by decide) (by decide) (by decide))
  have hF2 := gamma_on_U hγH (by decide) (hf F2 (by decide) (by decide) (by decide))
  exact Kw_of_fixU hγH hE1 hE2 hF1 hF2

theorem model_w_claims {Ω : Subgroup (VM ≃ₗ[ZMod 2] VM)} (hΩG : Ω ≤ GM)
    (hrel : Ω.relIndex GM = 2) :
    Nat.card (CFSG.Open.pCoreOf 2 (Hm ⊓ Ω)) = 16 ∧
    ∀ γ ∈ Hm ⊓ Ω, (∀ x, bM x e0 = 0 → γ x - x ∈ Submodule.span (ZMod 2) {e0}) ↔
      γ ∈ CFSG.Open.pCoreOf 2 (Hm ⊓ Ω) := by
  have heq : Kw = CFSG.Open.pCoreOf 2 (Hm ⊓ Ω) :=
    le_antisymm (Kw_le_pCoreOf hΩG hrel) (fun γ hγ => pCore_le_Kw hΩG hrel γ hγ)
  refine ⟨?_, ?_⟩
  · rw [← heq, Kw_card]
  · intro γ hγ
    have hγH : γ ∈ Hm := (Subgroup.mem_inf.1 hγ).1
    constructor
    · intro hk
      rw [← heq]
      exact (mem_Kw_iff γ).2 ⟨((mem_Hm_iff γ).1 hγH).1, ((mem_Hm_iff γ).1 hγH).2, hk⟩
    · intro hmem
      rw [← heq] at hmem
      exact ((mem_Kw_iff γ).1 hmem).2.2

end CFSG.Quasithin.H13.C1294.Model

end
