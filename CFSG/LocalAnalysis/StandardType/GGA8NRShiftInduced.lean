module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggA8NR_shiftInduced {G : Type} [Group G] {Bs K : Subgroup G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (hdec : ∀ b ∈ Bs, ∃ k ∈ K, k ∈ Bs ∧ k⁻¹ * b ∈ Subgroup.centralizer (K : Set G)) :
    ∃ φ ∈ ggAutomizer K Bs, ∃ n : ↥K, ρ n = ggSL9Shift ∧
      ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) = (n : G) * (b : G) * (n : G)⁻¹ := by
  let n : ↥K := ρ.symm ggSL9Shift
  have hnρ : ρ n = ggSL9Shift := ρ.apply_symm_apply ggSL9Shift
  have hpre : ∀ x : ↥K, ρ x ∈ ggSL9Torus ↔ (x : G) ∈ Bs := by
    intro x
    constructor
    · intro hx
      have hx' : ρ x ∈ ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom := by
        rwa [hρ]
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
      have hzx' : z = x := ρ.injective hzx
      rw [hzx'] at hz
      exact (Subgroup.mem_subgroupOf.mp hz).1
    · intro hx
      rw [← hρ]
      exact Subgroup.mem_map.mpr
        ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩, rfl⟩
  have hconj_torus : ∀ f : Multiplicative (Fin 3 → ZMod 7),
      ggSL9Shift⁻¹ * ggSL9TorusCoord f * ggSL9Shift =
        ggSL9TorusCoord (ggSL9ShiftCoord.symm f) := by
    intro f
    have h := ggSL9Shift_conj_torusCoord (ggSL9ShiftCoord.symm f)
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h]
    group
  have hconjK : ∀ k : ↥K, (k : G) ∈ Bs → (n : G) * (k : G) * (n : G)⁻¹ ∈ Bs := by
    intro k hk
    have hkρ : ρ k ∈ ggSL9Torus := (hpre k).mpr hk
    have hmem : ρ (n * k * n⁻¹) ∈ ggSL9Torus := by
      rw [← range_ggSL9TorusCoord] at hkρ ⊢
      obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hkρ
      refine ⟨ggSL9ShiftCoord f, ?_⟩
      rw [map_mul, map_mul, map_inv, hnρ, ← hf, ggSL9Shift_conj_torusCoord]
    have h := (hpre (n * k * n⁻¹)).mp hmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hconjK_inv : ∀ k : ↥K, (k : G) ∈ Bs → (n : G)⁻¹ * (k : G) * (n : G) ∈ Bs := by
    intro k hk
    have hkρ : ρ k ∈ ggSL9Torus := (hpre k).mpr hk
    have hmem : ρ (n⁻¹ * k * n) ∈ ggSL9Torus := by
      rw [← range_ggSL9TorusCoord] at hkρ ⊢
      obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp hkρ
      refine ⟨ggSL9ShiftCoord.symm f, ?_⟩
      rw [map_mul, map_mul, map_inv, hnρ, ← hf]
      exact (hconj_torus f).symm
    have h := (hpre (n⁻¹ * k * n)).mp hmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hcomm_conj : ∀ {a x : G}, a * x = x * a → a * x * a⁻¹ = x := by
    intro a x h
    calc a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [h]
      _ = x := by group
  have hcomm_inv : ∀ {a x : G}, a * x = x * a → x * a⁻¹ = a⁻¹ * x := by
    intro a x h
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * x := by group
  have hconjBs : ∀ x ∈ Bs, (n : G) * x * (n : G)⁻¹ ∈ Bs := by
    intro x hx
    obtain ⟨k, hkK, hkB, hc⟩ := hdec x hx
    have hnk : (n : G) * k * (n : G)⁻¹ ∈ Bs := hconjK ⟨k, hkK⟩ hkB
    have hcB : k⁻¹ * x ∈ Bs := Bs.mul_mem (Bs.inv_mem hkB) hx
    have hcomm : (n : G) * (k⁻¹ * x) = (k⁻¹ * x) * (n : G) :=
      (Subgroup.mem_centralizer_iff.mp hc) (n : G) n.2
    have hnc : (k⁻¹ * x) * (n : G)⁻¹ = (n : G)⁻¹ * (k⁻¹ * x) := hcomm_inv hcomm
    have hmain : (n : G) * x * (n : G)⁻¹ =
        ((n : G) * k * (n : G)⁻¹) * (k⁻¹ * x) := by
      calc (n : G) * x * (n : G)⁻¹
          = (n : G) * (k * (k⁻¹ * x)) * (n : G)⁻¹ := by
              conv_lhs => rw [show x = k * (k⁻¹ * x) by group]
        _ = (n : G) * k * ((k⁻¹ * x) * (n : G)⁻¹) := by group
        _ = (n : G) * k * ((n : G)⁻¹ * (k⁻¹ * x)) := by rw [hnc]
        _ = ((n : G) * k * (n : G)⁻¹) * (k⁻¹ * x) := by group
    rw [hmain]
    exact Bs.mul_mem hnk hcB
  have hconjBs_inv : ∀ x ∈ Bs, (n : G)⁻¹ * x * (n : G) ∈ Bs := by
    intro x hx
    obtain ⟨k, hkK, hkB, hc⟩ := hdec x hx
    have hnk : (n : G)⁻¹ * k * (n : G) ∈ Bs := hconjK_inv ⟨k, hkK⟩ hkB
    have hcB : k⁻¹ * x ∈ Bs := Bs.mul_mem (Bs.inv_mem hkB) hx
    have hcomm : (n : G) * (k⁻¹ * x) = (k⁻¹ * x) * (n : G) :=
      (Subgroup.mem_centralizer_iff.mp hc) (n : G) n.2
    have hnc : (k⁻¹ * x) * (n : G) = (n : G) * (k⁻¹ * x) := hcomm.symm
    have hmain : (n : G)⁻¹ * x * (n : G) =
        ((n : G)⁻¹ * k * (n : G)) * (k⁻¹ * x) := by
      calc (n : G)⁻¹ * x * (n : G)
          = (n : G)⁻¹ * (k * (k⁻¹ * x)) * (n : G) := by
              conv_lhs => rw [show x = k * (k⁻¹ * x) by group]
        _ = (n : G)⁻¹ * k * ((k⁻¹ * x) * (n : G)) := by group
        _ = (n : G)⁻¹ * k * ((n : G) * (k⁻¹ * x)) := by rw [hnc]
        _ = ((n : G)⁻¹ * k * (n : G)) * (k⁻¹ * x) := by group
    rw [hmain]
    exact Bs.mul_mem hnk hcB
  have hn : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact hconjBs b
    · intro hb
      have h := hconjBs_inv ((n : G) * b * (n : G)⁻¹) hb
      have hb' : (n : G)⁻¹ * ((n : G) * b * (n : G)⁻¹) * (n : G) = b := by group
      rw [hb'] at h
      exact h
  refine ⟨ggConjAut Bs hn, ggConjAut_mem_ggAutomizer n.2 hn, n, hnρ, ?_⟩
  exact fun b => ggConjAut_apply Bs hn b

end CFSG.StandardType

end
