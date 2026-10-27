module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Reduction
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

open CosetGeom Equiv
open scoped Pointwise

theorem exists_card_eight_sup_eq_top {y : Equiv.Perm (Fin 5)} (hy : y ≠ 1) :
    ∃ P : Subgroup (Equiv.Perm (Fin 5)), Nat.card P = 8 ∧
      ∀ K : Subgroup (Equiv.Perm (Fin 5)), P ≤ K → y ∈ K → K = ⊤ := by
  obtain ⟨p, hp⟩ : ∃ p, y p ≠ p := not_forall.mp fun h => hy (Equiv.ext h)
  set σ : Perm (Fin 5) := swap 4 p
  have hσ4 : σ 4 = p := swap_apply_left 4 p
  have hcard : Nat.card (conjSub σ D0) = 8 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj σ).injective, D0_card]
  refine ⟨conjSub σ D0, hcard, fun K hPK hyK => F5b_core _ K hcard p ?_ hPK fun hK => hp (hK hyK)⟩
  intro q j hq hj
  have hq' : σ⁻¹ q ≠ 4 := fun h => hq (by rw [Perm.inv_eq_iff_eq.mp h, hσ4])
  have hj' : σ⁻¹ j ≠ 4 := fun h => hj (by rw [Perm.inv_eq_iff_eq.mp h, hσ4])
  obtain ⟨d, hd, hdq⟩ := D0_trans (σ⁻¹ q) hq' (σ⁻¹ j) hj'
  refine ⟨σ * d * σ⁻¹, mul_mem_conjSub (show d ∈ D0 from hd), ?_⟩
  rw [Perm.mul_apply, Perm.mul_apply, hdq, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_nbr_le_sup (hA : F53Amalgam H M S) {δ : Geo H M} (hv : vtype δ = false)
    {Y : Subgroup G} (hY : Y ≤ stab δ) (hYQ : ¬ Y ≤ Qv δ) :
    ∃ μ ∈ nbrs δ, stab δ ≤ (stab δ ⊓ stab μ) ⊔ Y := by
  obtain ⟨n, ψ, hn, hsurj, hker⟩ := exists_quotHom hA δ
  obtain rfl : n = 5 := by
    rcases hn with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [hv] at h; exact absurd h Bool.false_ne_true
  obtain ⟨y, hyY, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hYQ
  obtain ⟨P, hP8, hPtop⟩ := exists_card_eight_sup_eq_top (y := ψ ⟨y, hY hyY⟩)
    fun h => hyQ ((hker _).mp h)
  obtain ⟨μ₀, hμ₀⟩ := exists_adj δ
  have hμ₀' : μ₀ ∈ nbrs δ := hμ₀
  have hkerQ : ψ.ker = (Qv δ).subgroupOf (stab δ) := by
    ext x; rw [MonoidHom.mem_ker, hker x, Subgroup.mem_subgroupOf]
  set T₀ : Subgroup (Perm (Fin 5)) := ((stab δ ⊓ stab μ₀).subgroupOf (stab δ)).map ψ with hT₀
  have hT8 : Nat.card T₀ = 8 := by
    rw [hT₀, ← Subgroup.relIndex_ker, hkerQ, Subgroup.relIndex_subgroupOf inf_le_left,
      relIndex_Qv_inf_false hA hμ₀' hv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP8
  obtain ⟨hT2, hTs, -⟩ := sylow_of_card_eight T₀ hT8
  obtain ⟨π, hπ⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hT2.toSylow hTs) (hP2.toSylow hPs)
  have hPeq : P = MulAut.conj π • T₀ := by
    have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hπ
    simpa [Sylow.coe_subgroup_smul] using this.symm
  obtain ⟨g, rfl⟩ := hsurj π
  obtain ⟨g', hg'⟩ : ∃ g' : ↥(H ⊔ M), (g' : G) = g := ⟨⟨g, stab_le δ g.2⟩, rfl⟩
  have hμ : g' • μ₀ ∈ nbrs δ := by
    have h := (smul_adj g').mpr hμ₀
    rwa [smul_eq_of_mem_stab (hg' ▸ g.2)] at h
  refine ⟨g' • μ₀, hμ, fun x hx => ?_⟩
  set W := (stab δ ⊓ stab (g' • μ₀)) ⊔ Y
  have hTW : stab δ ⊓ stab (g' • μ₀) ≤ W := le_sup_left
  have hK : (W.subgroupOf (stab δ)).map ψ = ⊤ := by
    refine hPtop _ ?_ ⟨⟨y, hY hyY⟩, Subgroup.mem_subgroupOf.mpr (le_sup_right (a := stab δ ⊓
      stab (g' • μ₀)) hyY), rfl⟩
    rw [hPeq]
    intro z hz
    obtain ⟨t, ht, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    have hs' : (s : G) ∈ stab δ ⊓ stab μ₀ := Subgroup.mem_subgroupOf.mp hs
    refine ⟨g * s * g⁻¹,
      Subgroup.mem_subgroupOf.mpr (hTW (Subgroup.mem_inf.mpr ⟨(g * s * g⁻¹).2, ?_⟩)), ?_⟩
    · rw [stab_smul, mem_conjSub, hg']
      simpa [mul_assoc] using hs'.2
    · rw [MulAut.smul_def, MulAut.conj_apply, map_mul, map_mul, map_inv]
  obtain ⟨w, hw, hwx⟩ : ψ ⟨x, hx⟩ ∈ (W.subgroupOf (stab δ)).map ψ := by rw [hK]; trivial
  have h1 : ψ (w⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hwx, inv_mul_cancel]
  have h2 : ((w⁻¹ * ⟨x, hx⟩ : ↥(stab δ)) : G) ∈ W := hTW (Qv_le_inf hA hμ ((hker _).mp h1))
  have := W.mul_mem (Subgroup.mem_subgroupOf.mp hw) h2
  simpa using this

end F53.Stellmacher

end CFSG.Quasithin
