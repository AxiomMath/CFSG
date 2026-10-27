module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off8

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

abbrev q0Sub (H : Type*) [Group H] (x : H) : Subgroup H :=
  oQ H ⊓ Subgroup.centralizer {x}

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

omit [Finite H] in
theorem mem_q0Sub {y : H} : y ∈ q0Sub H x ↔ y ∈ oQ H ∧ y * x = x * y :=
  and_congr Iff.rfl Subgroup.mem_centralizer_singleton_iff

omit [Finite H] in
theorem q0Sub_le_Q : q0Sub H x ≤ oQ H := inf_le_left

omit [Finite H] in
theorem nQ_q0_comm {n q : H} (hn : n ∈ nQ H x) (hq : q ∈ q0Sub H x) : n * q = q * n :=
  (mem_oneCenter.1 (nQ_le x hn)).2.2 q (mem_q0Sub.1 hq).1

theorem Hyp3.q0_eq (h : Hyp3 H S x) :
    q0Sub H x = oQ H ⊓ Subgroup.centralizer (oL H : Set H) := by
  ext y
  refine ⟨fun hy => ⟨(mem_q0Sub.1 hy).1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩,
    fun hy => mem_q0Sub.2 ⟨hy.1, ?_⟩⟩
  · have hle : oL H ≤ Subgroup.centralizer {y} := by
      rw [h.oL_eq]
      refine sup_le (fun n hn => Subgroup.mem_centralizer_singleton_iff.2
        (nQ_q0_comm hn hy)) (Subgroup.zpowers_le.2
        (Subgroup.mem_centralizer_singleton_iff.2 (mem_q0Sub.1 hy).2.symm))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hl)
  · have hxL : x ∈ oL H := by
      rw [h.oL_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    exact (Subgroup.mem_centralizer_iff.1 hy.2 x hxL).symm

theorem Hyp3.q0_normal (h : Hyp3 H S x) : (q0Sub H x).Normal := by
  rw [h.q0_eq]
  have : (oL H).Normal := oL_normal
  infer_instance

theorem Hyp3.nQ_inf_q0 (h : Hyp3 H S x) {n : H} (hn : n ∈ nQ H x) (hq : n ∈ q0Sub H x) :
    n = 1 := by
  refine nQ_fix (mul_mul_eq_one_of_orderOf h.ord) hn ?_
  have := (mem_q0Sub.1 hq).2
  rw [← this]
  group

theorem Hyp3.decomp (h : Hyp3 H S x) {q : H} (hq : q ∈ oQ H) :
    ∃ n ∈ nQ H x, ∃ q₀ ∈ q0Sub H x, q = n * q₀ := by
  have hx3 := mul_mul_eq_one_of_orderOf h.ord
  have hNn : (nQ H x).Normal := h.sig.nQ_normal h.ord
  have hQn : (oQ H).Normal := inferInstance
  obtain ⟨c, hc⟩ : ∃ c : H, c = x * q * x⁻¹ * q⁻¹ := ⟨_, rfl⟩
  have hcq : x * q * x⁻¹ = c * q := by rw [hc]; group
  have hcN : c ∈ nQ H x := by
    rw [← h.oL_inf_Q, hc]
    exact ⟨comm_mem_oL h.ord q, (oQ H).mul_mem (hQn.conj_mem q hq x) ((oQ H).inv_mem hq)⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : H, c₂ = x * c * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : H, c₃ = x * c₂ * x⁻¹ := ⟨_, rfl⟩
  have hc₂N : c₂ ∈ nQ H x := hc₂ ▸ hNn.conj_mem c hcN x
  have hc₃N : c₃ ∈ nQ H x := hc₃ ▸ hNn.conj_mem c₂ hc₂N x
  have hsq : ∀ y ∈ nQ H x, y * y = 1 := fun y hy => (mem_oneCenter.1 (nQ_le x hy)).2.1
  have hcomm : ∀ y ∈ nQ H x, ∀ z ∈ nQ H x, y * z = z * y := fun y hy z hz =>
    elem_comm (nQ_elem x) hy hz
  have hxc₃ : x * c₃ * x⁻¹ = c := by
    calc x * c₃ * x⁻¹ = (x * x * x) * c * (x * x * x)⁻¹ := by rw [hc₃, hc₂]; group
      _ = c := by rw [hx3]; group
  have hnorm : c * c₂ * c₃ = 1 := by
    refine nQ_fix hx3 ((nQ H x).mul_mem ((nQ H x).mul_mem hcN hc₂N) hc₃N) ?_
    calc x * (c * c₂ * c₃) * x⁻¹ = (x * c * x⁻¹) * (x * c₂ * x⁻¹) * (x * c₃ * x⁻¹) := by group
      _ = c₂ * c₃ * c := by rw [← hc₂, ← hc₃, hxc₃]
      _ = c₂ * (c₃ * c) := mul_assoc _ _ _
      _ = c₂ * (c * c₃) := by rw [hcomm c₃ hc₃N c hcN]
      _ = (c₂ * c) * c₃ := (mul_assoc _ _ _).symm
      _ = (c * c₂) * c₃ := by rw [hcomm c₂ hc₂N c hcN]
  have hrel : c₂ * (c₃ * c) = 1 := by
    calc c₂ * (c₃ * c) = c₂ * (c * c₃) := by rw [hcomm c₃ hc₃N c hcN]
      _ = (c₂ * c) * c₃ := (mul_assoc _ _ _).symm
      _ = (c * c₂) * c₃ := by rw [hcomm c₂ hc₂N c hcN]
      _ = 1 := hnorm
  have hrel' : c₃ * c = c₂⁻¹ := eq_inv_of_mul_eq_one_right hrel
  have hc₃inv : c₃⁻¹ = c₃ := inv_eq_of_mul_eq_one_right (hsq c₃ hc₃N)
  refine ⟨c₂, hc₂N, c₂⁻¹ * q, mem_q0Sub.2 ⟨?_, ?_⟩, by group⟩
  · exact (oQ H).mul_mem ((oQ H).inv_mem (oneCenter_le (nQ_le x hc₂N))) hq
  · have hfix : x * (c₂⁻¹ * q) * x⁻¹ = c₂⁻¹ * q := by
      calc x * (c₂⁻¹ * q) * x⁻¹ = (x * c₂ * x⁻¹)⁻¹ * (x * q * x⁻¹) := by group
        _ = c₃⁻¹ * (c * q) := by rw [← hc₃, hcq]
        _ = (c₃ * c) * q := by rw [hc₃inv, mul_assoc]
        _ = c₂⁻¹ * q := by rw [hrel']
    calc c₂⁻¹ * q * x = (x * (c₂⁻¹ * q) * x⁻¹) * x := by rw [hfix]
      _ = x * (c₂⁻¹ * q) := by group

end CFSG.Quasithin.Fan86.Sigma3
