module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H] [Finite H]

theorem e34_decomp {C : Subgroup H} (hC : IsComponent C) {e : H} (he : e ∈ layer H) :
    ∃ c ∈ C, ∃ d : H, (∀ w ∈ C, w * d = d * w) ∧ e = c * d := by
  obtain ⟨x, rfl⟩ := LocalCores.exists_layerMul_eq he
  let K : LocalCores.ComponentIndex H := ⟨C, hC⟩
  refine ⟨(x K : H), (x K).2, LocalCores.layerMul H (Function.update x K 1), ?_,
    LocalCores.layerMul_eq_mul_update x K⟩
  intro w hw
  exact (LocalCores.commute_layerMul_update x K hw).eq

theorem e34_conj_unique (hO : pPrimeCore 3 H = ⊥)
    (hS : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S) {C : Subgroup H}
    (hC : IsComponent C) {c c' : H} (hc : c ∈ C) (hc' : c' ∈ C)
    (h : ∀ w ∈ C, c * w * c⁻¹ = c' * w * c'⁻¹) : c = c' := by
  have h1 : c'⁻¹ * c = 1 := by
    refine e34_comp_center_trivial hO hS hC (C.mul_mem (C.inv_mem hc') hc) fun w hw => ?_
    have := h w hw
    calc w * (c'⁻¹ * c) = c'⁻¹ * (c' * w * c'⁻¹) * c := by group
      _ = c'⁻¹ * (c * w * c⁻¹) * c := by rw [this]
      _ = c'⁻¹ * c * w := by group
  exact (inv_mul_eq_one.mp h1).symm

theorem e34_exists_rho (hO : pPrimeCore 3 H = ⊥)
    (hS : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S) {C : Subgroup H}
    (hC : IsComponent C) :
    ∃ ρ : ↥(layer H) →* ↥C, ∀ (e : ↥(layer H)) (w : H), w ∈ C →
      (e : H) * w * (e : H)⁻¹ = (ρ e : H) * w * (ρ e : H)⁻¹ := by
  have hex : ∀ e : ↥(layer H), ∃ c : ↥C, ∀ w : H, w ∈ C →
      (e : H) * w * (e : H)⁻¹ = (c : H) * w * (c : H)⁻¹ := by
    intro e
    obtain ⟨c, hc, d, hd, hed⟩ := e34_decomp hC e.2
    refine ⟨⟨c, hc⟩, fun w hw => ?_⟩
    show (e : H) * w * (e : H)⁻¹ = c * w * c⁻¹
    rw [hed]
    have := hd w hw
    calc c * d * w * (c * d)⁻¹ = c * (d * w) * d⁻¹ * c⁻¹ := by group
      _ = c * (w * d) * d⁻¹ * c⁻¹ := by rw [this]
      _ = c * w * c⁻¹ := by group
  choose f hf using hex
  have huniq : ∀ c c' : ↥C, (∀ w : H, w ∈ C → (c : H) * w * (c : H)⁻¹ = (c' : H) * w * (c' : H)⁻¹) →
      c = c' := fun c c' h => Subtype.ext (e34_conj_unique hO hS hC c.2 c'.2 h)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · apply huniq
    intro w hw
    rw [← hf 1 w hw]
    simp
  · intro e e'
    apply huniq
    intro w hw
    rw [← hf (e * e') w hw]
    have h2 : (f e' : H) * w * (f e' : H)⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (f e').2 hw) (C.inv_mem (f e').2)
    have h3 := hf e _ h2
    show (e : H) * (e' : H) * w * ((e : H) * (e' : H))⁻¹ = _
    calc (e : H) * (e' : H) * w * ((e : H) * (e' : H))⁻¹
        = (e : H) * ((e' : H) * w * (e' : H)⁻¹) * (e : H)⁻¹ := by group
      _ = (f e : H) * ((f e' : H) * w * (f e' : H)⁻¹) * (f e : H)⁻¹ := by
        rw [hf e' w hw]; exact h3
      _ = _ := by simp [mul_assoc]

end CFSG.RankThree.PartTwo.Sec21.FF79
