module

public import CFSG.Quasithin.Vol2.Ch10SecKRSv

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open C10P4F

variable {G : Type} [Group G] [Finite G] {J : Subgroup G} (ρ : ↥J →* SL5) {P : Subgroup G}
  (hPJ : P ≤ J) (hQ : img ρ P = Q1)
include hPJ hQ

omit [Finite G] in
theorem img_pre_uniSL : img ρ (pre ρ P (uniSL 5)) = uniSL 5 := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hxJ⟩, hx, rfl⟩
    exact ((mem_pre hPJ).mp (Subgroup.mem_subgroupOf.mp hx)).2
  · intro g hg
    have hgQ : g ∈ img ρ P := hQ ▸ M_le_Q1 (le_refl 2) (uniSL_le_M 2 hg)
    obtain ⟨⟨x, hxJ⟩, hxP, rfl⟩ := hgQ
    exact ⟨⟨x, hxJ⟩, Subgroup.mem_subgroupOf.mpr ((mem_pre hPJ).mpr
      ⟨Subgroup.mem_subgroupOf.mp hxP, hg⟩), rfl⟩

theorem map_pre_M3 {t c : G} (hσP : P.map (MulAut.conj t⁻¹).toMonoidHom = P)
    (hσS : (pre ρ P (uniSL 5)).map (MulAut.conj t⁻¹).toMonoidHom = pre ρ P (uniSL 5))
    (hc : c ∈ pre ρ P (M 2)) (hcS : c ∉ pre ρ P (uniSL 5))
    (h4 : t⁻¹ * c * t ∈ pre ρ P (M 4)) (h2 : t⁻¹ * (t⁻¹ * c * t) * t ∈ pre ρ P (M 2)) :
    (pre ρ P (M 3)).map (MulAut.conj t⁻¹).toMonoidHom = pre ρ P (M 3) := by
  set σ := (MulAut.conj t⁻¹).toMonoidHom with hσ
  have hσinj : Function.Injective σ := (MulAut.conj t⁻¹).injective
  have hσapp : ∀ x, σ x = t⁻¹ * x * t := fun x => by
    rw [hσ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hSP : pre ρ P (uniSL 5) ≤ P := inf_le_left
  have hkerS : ∀ x (hx : x ∈ P), ρ ⟨x, hPJ hx⟩ = 1 → x ∈ pre ρ P (uniSL 5) := fun x hx h1 =>
    (mem_pre hPJ).mpr ⟨hx, h1 ▸ (uniSL 5).one_mem⟩
  have hSU := img_pre_uniSL ρ hPJ hQ
  have hSX : ∀ j, pre ρ P (uniSL 5) ≤ pre ρ P (M j) := fun j x hx => by
    obtain ⟨hxP, hxU⟩ := (mem_pre hPJ).mp hx
    exact (mem_pre hPJ).mpr ⟨hxP, uniSL_le_M j hxU⟩
  have hXP : ∀ j, pre ρ P (M j) ≤ P := fun _ => inf_le_left
  have hσX : ∀ j, 2 ≤ j → j ≤ 4 →
      ∃ k, 2 ≤ k ∧ k ≤ 4 ∧ (pre ρ P (M j)).map σ = pre ρ P (M k) := by
    intro j hj2 hj4
    have h3 : (pre ρ P (uniSL 5)).relIndex ((pre ρ P (M j)).map σ) = 3 := by
      rw [← hσS, Subgroup.relIndex_map_map_of_injective _ _ hσinj]
      exact relIndex_pre_M ρ hSP hPJ hkerS hSU hQ.ge hj2 hj4
    exact exists_M_of_relIndex ρ hPJ hkerS hSU hQ.le (hσS.ge.trans (Subgroup.map_mono (hSX j)))
      ((Subgroup.map_mono (hXP j)).trans hσP.le) h3
  have hmeet : ∀ j k, j ≠ k → ∀ x, x ∈ pre ρ P (M j) → x ∈ pre ρ P (M k) →
      x ∈ pre ρ P (uniSL 5) := by
    intro j k hjk x hxj hxk
    obtain ⟨hxP, hj⟩ := (mem_pre hPJ).mp hxj
    obtain ⟨_, hk⟩ := (mem_pre hPJ).mp hxk
    exact (mem_pre hPJ).mpr ⟨hxP, M_inf_M hjk ⟨hj, hk⟩⟩
  have hσS' : ∀ x, σ x ∈ pre ρ P (uniSL 5) → x ∈ pre ρ P (uniSL 5) := fun x hx => by
    rw [← hσS] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [hσinj hyx] at hy
  have hσc4 : σ c ∈ pre ρ P (M 4) := by rw [hσapp]; exact h4
  have hσσc2 : σ (σ c) ∈ pre ρ P (M 2) := by rw [hσapp, hσapp]; exact h2
  have h24 : (pre ρ P (M 2)).map σ = pre ρ P (M 4) := by
    obtain ⟨k, -, -, hk⟩ := hσX 2 le_rfl (by norm_num)
    rw [hk]
    have hck : σ c ∈ pre ρ P (M k) := by rw [← hk]; exact Subgroup.mem_map_of_mem σ hc
    by_contra hne
    have hk' : k ≠ 4 := fun h => hne (by rw [h])
    exact hcS (hσS' c (hmeet k 4 hk' _ hck hσc4))
  have h42 : (pre ρ P (M 4)).map σ = pre ρ P (M 2) := by
    obtain ⟨k, -, -, hk⟩ := hσX 4 (by norm_num) le_rfl
    rw [hk]
    have hck : σ (σ c) ∈ pre ρ P (M k) := by rw [← hk]; exact Subgroup.mem_map_of_mem σ hσc4
    by_contra hne
    have hk' : k ≠ 2 := fun h => hne (by rw [h])
    exact hcS (hσS' c (hσS' _ (hmeet k 2 hk' _ hck hσσc2)))
  obtain ⟨k, hk2, hk4, hk⟩ := hσX 3 (by norm_num) (by norm_num)
  rw [hk]
  rcases (show k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl
  · exfalso
    have h34 : pre ρ P (M 3) = pre ρ P (M 4) :=
      Subgroup.map_injective hσinj (hk.trans h42.symm)
    exact hcS (hσS' c (hmeet 3 4 (by norm_num) _ (by rw [h34]; exact hσc4) hσc4))
  · rfl
  · exfalso
    have h32 : pre ρ P (M 3) = pre ρ P (M 2) :=
      Subgroup.map_injective hσinj (hk.trans h24.symm)
    exact hcS (hmeet 2 3 (by norm_num) c hc (by rw [h32]; exact hc))

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
