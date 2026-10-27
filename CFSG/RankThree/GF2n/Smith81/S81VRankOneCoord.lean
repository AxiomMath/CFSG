module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOne

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

namespace RankOneData

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (D : RankOneData K V)

theorem span_translates_eq_top :
    Submodule.span K (Set.range fun g : D.Pg => D.τ.comp (D.Ad g).toLinearMap) = ⊤ := by
  refine Submodule.span_eq_top_of_ne_zero ?_
  intro z hz
  obtain ⟨g, hg⟩ := D.lemmaS z hz
  exact ⟨D.τ.comp (D.Ad g).toLinearMap, ⟨g, rfl⟩, hg⟩

theorem exists_crd {v : V} (hv : v ≠ 0) : ∃ c : V →ₗ[K] K, c v = 1 :=
  Module.Projective.exists_dual_eq_one K hv

@[expose] def Psi (c : V →ₗ[K] K) : V →ₗ[K] (D.N → K) where
  toFun w := fun n => c (D.ρ n w - w)
  map_add' w w' := by
    funext n
    simp only [Pi.add_apply]
    rw [← map_add]
    congr 1
    rw [map_add]
    abel
  map_smul' a w := by
    funext n
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    rw [map_smul, smul_sub]

theorem Psi_apply (c : V →ₗ[K] K) (w : V) (n : D.N) : D.Psi c w n = c (D.ρ n w - w) := rfl

theorem rho_sub_eq_Psi_smul [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v' : V}
    (hv' : v' ∈ D.fix) (hv'0 : v' ≠ 0) {c : V →ₗ[K] K} (hc : c v' = 1)
    {β : V →ₗ[K] V →ₗ[K] K} {w : V} (hw : w ∈ D.V1 β) (n : D.N) :
    D.ρ n w - w = (D.Psi c w n) • v' := by
  have hmem : D.ρ n w - w ∈ D.fix := (D.mem_V1.1 hw).2 n
  have hne : (⟨v', hv'⟩ : D.fix) ≠ 0 := fun h => hv'0 (congrArg Subtype.val h)
  obtain ⟨μ, hμ⟩ := exists_smul_eq_of_finrank_eq_one hfix hne ⟨D.ρ n w - w, hmem⟩
  have hval : μ • v' = D.ρ n w - w := congrArg Subtype.val hμ
  have hPsi : D.Psi c w n = μ := by
    rw [Psi_apply, ← hval, map_smul, hc, smul_eq_mul, mul_one]
  rw [hPsi, hval]

theorem fix_le_V1 [FiniteDimensional K V] (hfix : finrank K D.fix = 1)
    {β : V →ₗ[K] V →ₗ[K] K} (hβalt : ∀ v, β v v = 0) : D.fix ≤ D.V1 β := by
  intro z hz
  rw [D.mem_V1]
  refine ⟨fun v hv => ?_, fun n => ?_⟩
  · by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    · have hne : (⟨v, hv⟩ : D.fix) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
      obtain ⟨ν, hν⟩ := exists_smul_eq_of_finrank_eq_one hfix hne ⟨z, hz⟩
      have hzv : z = ν • v := (congrArg Subtype.val hν).symm
      rw [hzv, map_smul, hβalt, smul_zero]
  · rw [(D.mem_fix.1 hz) n, sub_self]
    exact D.fix.zero_mem

theorem finrank_map_Psi_le [FiniteDimensional K V] (hfix : finrank K D.fix = 1)
    {β : V →ₗ[K] V →ₗ[K] K} (hβalt : ∀ v, β v v = 0) (c : V →ₗ[K] K)
    (hV1 : finrank K (D.V1 β) ≤ finrank K D.N + 1) :
    finrank K (Submodule.map (D.Psi c) (D.V1 β)) ≤ finrank K D.N := by
  have hfix_ne : D.fix ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨v', hv', hv'0⟩ := (Submodule.ne_bot_iff D.fix).mp hfix_ne
  have hPsi0 : D.Psi c v' = 0 := by
    funext n
    rw [Psi_apply, D.mem_fix.1 hv' n, sub_self, map_zero, Pi.zero_apply]
  have hker_mem : (⟨v', fix_le_V1 D hfix hβalt hv'⟩ : D.V1 β)
      ∈ LinearMap.ker ((D.Psi c).domRestrict (D.V1 β)) := by
    rw [LinearMap.mem_ker]
    exact hPsi0
  have hne : (⟨v', fix_le_V1 D hfix hβalt hv'⟩ : D.V1 β) ≠ 0 :=
    fun h => hv'0 (congrArg Subtype.val h)
  have hker : 1 ≤ finrank K (LinearMap.ker ((D.Psi c).domRestrict (D.V1 β))) :=
    Submodule.one_le_finrank_iff.mpr ((Submodule.ne_bot_iff _).mpr ⟨_, hker_mem, hne⟩)
  have hrn := LinearMap.finrank_range_add_finrank_ker ((D.Psi c).domRestrict (D.V1 β))
  rw [LinearMap.range_domRestrict] at hrn
  omega

theorem card_map_Psi_le [FiniteDimensional K V] (hfix : finrank K D.fix = 1)
    {β : V →ₗ[K] V →ₗ[K] K} (hβalt : ∀ v, β v v = 0) (c : V →ₗ[K] K)
    (hV1 : finrank K (D.V1 β) ≤ finrank K D.N + 1) :
    Nat.card (Submodule.map (D.Psi c) (D.V1 β)) ≤ Fintype.card K ^ finrank K D.N := by
  rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
  exact Nat.pow_le_pow_right Fintype.card_pos (finrank_map_Psi_le D hfix hβalt c hV1)

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
