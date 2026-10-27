module

public import CFSG.RankThree.GF2n.Smith81.S81QM2

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem T0_le_EAut0 : T0 K ≤ EAut0 K := by
  rw [← range_lamGHom]
  exact Subgroup.map_le_range _ _

theorem conj_T0g_mem_URge {τ : Gp K} (hτ : τ ∈ T0g K) {g : Gp K} (hg : g ∈ URge K Rd6 1) :
    τ * g * τ⁻¹ ∈ URge K Rd6 1 := by
  refine Subgroup.iSup_induction
    (fun i : {i : Fin (Tag.rank .E7) // i ≠ node1} => e7Data_valid.torus K i.1)
    (C := fun τ => ∀ g ∈ URge K Rd6 1, τ * g * τ⁻¹ ∈ URge K Rd6 1) hτ ?_ ?_ ?_ g hg
  · intro i τ hτ g hg
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_torus K).1 hτ
    refine URge_induction
      (C := fun g => e7Data_valid.hm K i.1 c * g * (e7Data_valid.hm K i.1 c)⁻¹ ∈ URge K Rd6 1) hg ?_ ?_ ?_
    · intro α hα hαh b
      rw [e7Data_valid.hm_conj_xm K (closed_Rd6.root α hα) i.1 c b]
      exact xE_mem_URge hα hαh _
    · simp
    · intro x y hx hy
      have : e7Data_valid.hm K i.1 c * (x * y) * (e7Data_valid.hm K i.1 c)⁻¹ =
          (e7Data_valid.hm K i.1 c * x * (e7Data_valid.hm K i.1 c)⁻¹) *
            (e7Data_valid.hm K i.1 c * y * (e7Data_valid.hm K i.1 c)⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
  · intro g hg
    simpa using hg
  · intro x y hx hy g hg
    have : x * y * g * (x * y)⁻¹ = x * (y * g * y⁻¹) * x⁻¹ := by group
    rw [this]
    exact hx _ (hy g hg)

theorem conj_T0_mem_posU0 {t h : W K ≃ₗ[K] W K} (ht : t ∈ T0 K) (hh : h ∈ posU0 K) :
    t * h * t⁻¹ ∈ posU0 K := by
  obtain ⟨τ, hτ, rfl⟩ := ht
  rw [posU0_eq_map] at hh ⊢
  obtain ⟨u, hu, rfl⟩ := hh
  refine ⟨τ * u * τ⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact conj_T0g_mem_URge hτ hu

theorem T0_le_normalizer_posU0 :
    T0 K ≤ Subgroup.normalizer (posU0 K : Set (W K ≃ₗ[K] W K)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_T0_mem_posU0 ht hh, fun hh => ?_⟩
  have h1 := conj_T0_mem_posU0 (inv_mem ht) hh
  have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
  rwa [e] at h1

end Torus

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isPGroup_posU0 : IsPGroup 2 (posU0 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_perpLevi_eq (K := K)
  have h1 : IsPGroup 2 ((posPerpU K).subgroupOf (EPilot.perpLevi .E7 K)) := by
    rw [← hS]
    exact S.isPGroup'
  have h2 : IsPGroup 2 (ULG K) := by
    rw [← SK.psiD_map_posPerpU]
    exact h1.map _
  have h3 : IsPGroup 2 ((URge K Rd6 1).subgroupOf (LamG K)) := by
    rw [← ULG_eq_URge]
    exact h2.comap_of_injective (LamG K).subtype (LamG K).subtype_injective
  rw [posU0_eq_map]
  exact h3.map _

end Sylow

end CFSG.RankThree.GF2n.Smith81.D6Spin
