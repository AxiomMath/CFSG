module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open Matrix Subgroup
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Comb_four exists_conj_into_d8Tor_su
  permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD weyl₁ weyl₂ mapL mapL_conj card_mapL
  line_cases conj_weyl₁ conj_weyl₂ card_rootsOfUnity_three)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

private theorem weyl_lines {ω : rootsOfUnity 3 F} :
    weyl₁ ∈ SU (unitaryInvolution F 2 b) 4 ∧
      weyl₂ ∈ SU (unitaryInvolution F 2 b) 4 ∧
      Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) =
        (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map
          (MulAut.conj weyl₁).toMonoidHom ∧
      Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
        (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
          (MulAut.conj weyl₂).toMonoidHom := by
  refine ⟨permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide),
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide), ?_, ?_⟩
  · rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₁ ((ω, 1) : D8Mod 3 F)).symm
  · rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm

theorem u4_conj_line (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {ℓ : Subgroup (GL (Fin 4) F)}
    (hℓ : ℓ ≤ SU (unitaryInvolution F 2 b) 4) (h3 : Nat.card ℓ = 3) :
    ∃ g ∈ SU (unitaryInvolution F 2 b) 4,
      ℓ = (zpowers (torusD ((ω, 1) : D8Mod 3 F))).map (MulAut.conj g).toMonoidHom ∨
        ℓ = (zpowers (torusD ((ω, ω) : D8Mod 3 F))).map (MulAut.conj g).toMonoidHom := by
  have hμ := card_rootsOfUnity_three hbe hF
  set Y : Subgroup (GL (Fin 4) F) := SU (unitaryInvolution F 2 b) 4 with hY
  have hX : ∀ x ∈ ℓ.subgroupOf Y, x ^ 3 = 1 := by
    intro x hx
    have h := pow_card_eq_one' (G := ℓ) (x := ⟨(x : GL (Fin 4) F), hx⟩)
    rw [h3] at h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_conj_into_d8Tor_su (n := 4) (Or.inl rfl) d8Comb_four hF
    Nat.prime_three (by norm_num)
    (CFSG.RankThree.PartTwo.Sec21.three_dvd_two_pow_sub_one hbe) (ℓ.subgroupOf Y) hX
  have hT : mapL (MulAut.conj g) ℓ ≤ d8Tor 3 F 4 := by
    rw [mapL_conj g hℓ]
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hℓ hx⟩ hx
  have h3' : Nat.card (mapL (MulAut.conj g) ℓ) = 3 := by
    rw [card_mapL _ hℓ, h3]
  have hℓg : ℓ.map (MulAut.conj (g : GL (Fin 4) F)).toMonoidHom =
      mapL (MulAut.conj g) ℓ := (mapL_conj g hℓ).symm
  have hginv : ((g : GL (Fin 4) F))⁻¹ ∈ Y := Y.inv_mem g.2
  obtain ⟨hw₁, hw₂, hL₂, hL₄⟩ := weyl_lines (F := F) (b := b) (ω := ω)
  rcases line_cases hμ hω hT h3' with h | h | h | h
  · refine ⟨((g : GL (Fin 4) F))⁻¹, hginv, Or.inl ?_⟩
    have hL : ℓ.map (MulAut.conj (g : GL (Fin 4) F)).toMonoidHom =
        Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) := hℓg.trans h
    rw [← hL, CFSG.GroupTheory.map_conj_map_conj_inv]
  · refine ⟨((g : GL (Fin 4) F))⁻¹ * weyl₁, Y.mul_mem hginv hw₁, Or.inl ?_⟩
    have hL : ℓ.map (MulAut.conj (g : GL (Fin 4) F)).toMonoidHom =
        Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) := hℓg.trans h
    rw [← CFSG.GroupTheory.map_conj_map_conj ((g : GL (Fin 4) F))⁻¹ weyl₁, ← hL₂, ← hL,
      CFSG.GroupTheory.map_conj_map_conj_inv]
  · refine ⟨((g : GL (Fin 4) F))⁻¹, hginv, Or.inr ?_⟩
    have hL : ℓ.map (MulAut.conj (g : GL (Fin 4) F)).toMonoidHom =
        Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) := hℓg.trans h
    rw [← hL, CFSG.GroupTheory.map_conj_map_conj_inv]
  · refine ⟨((g : GL (Fin 4) F))⁻¹ * weyl₂, Y.mul_mem hginv hw₂, Or.inr ?_⟩
    have hL : ℓ.map (MulAut.conj (g : GL (Fin 4) F)).toMonoidHom =
        Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) := hℓg.trans h
    rw [← CFSG.GroupTheory.map_conj_map_conj ((g : GL (Fin 4) F))⁻¹ weyl₂, ← hL₄, ← hL,
      CFSG.GroupTheory.map_conj_map_conj_inv]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
