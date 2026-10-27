module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylow
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotPerm
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotNormal

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem le_F1_of_odd_normal {R : Subgroup X} (hFR : S.F1 ≤ R) (hRH : R ≤ S.H)
    (hnorm : ∀ h ∈ S.H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hodd : Odd (S.F1.relIndex R)) :
    R ≤ S.F1 := by
  let T : Finset (Fin 8) := Finset.univ.erase 0
  let M : Subgroup (Equiv.Perm (Fin 8)) := (R.subgroupOf S.H).map S.permHom
  haveI : (S.F1.subgroupOf R).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact S.conj_mem_F1 (hRH g.2) hn
  have hM : M = ⊥ := by
    refine perm_eq_bot_of_normal_of_odd T ?_ ?_ ?_ ?_
    · show 5 ≤ T.card
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
        Fintype.card_fin]
      norm_num
    · intro m hm i hi
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
      have hi0 : i = 0 := by
        by_contra h
        exact hi (by simp [T, h])
      rw [hi0]
      exact S.permHom_zero z
    · intro g hg m hm
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
      have h0T : (0 : Fin 8) ∉ T := by simp [T]
      have hg0 : g 0 = 0 := hg 0 h0T
      obtain ⟨y, hy, -⟩ := S.exists_permHom_eq hg0
      rw [← hy]
      refine Subgroup.mem_map.mpr ⟨y * z * y⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hnorm (y : X) y.2 (z : X) ((Subgroup.mem_subgroupOf).mp hz)
      · simp only [map_mul, map_inv]
    · intro m hm
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
      refine ⟨S.F1.relIndex R, hodd, ?_⟩
      have hzpow : (z : X) ^ S.F1.relIndex R ∈ S.F1 := by
        have hpow := Subgroup.pow_index_mem (S.F1.subgroupOf R)
          (⟨(z : X), (Subgroup.mem_subgroupOf).mp hz⟩ : R)
        have hmem := (Subgroup.mem_subgroupOf).mp hpow
        simpa [Subgroup.relIndex, Subgroup.coe_pow] using hmem
      have hperm1 : S.permHom (z ^ S.F1.relIndex R) = 1 :=
        (S.permHom_eq_one_iff_mem_F1 (z ^ S.F1.relIndex R)).mpr (by simpa using hzpow)
      simpa [map_pow] using hperm1
  intro r hr
  let y : S.H := ⟨r, hRH hr⟩
  have hyM : S.permHom y ∈ M :=
    Subgroup.mem_map.mpr ⟨y, by rw [Subgroup.mem_subgroupOf]; exact hr, rfl⟩
  rw [hM] at hyM
  have hy1 : S.permHom y = 1 := Subgroup.mem_bot.mp hyM
  have hmem := (S.permHom_eq_one_iff_mem_F1 y).mp hy1
  simpa using hmem

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
