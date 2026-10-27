module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightTwo
import CFSG.LieType.Universal.Unitary.Extras.Basic

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType

theorem rckIIp_false_of_PSU_le_two
    {X : Type} [Group X] {n g : ℕ} (hn : n ≤ 2) (hg : 1 ≤ g)
    (φ : (ggU .PSU n g).K →* X) {J : Subgroup X} (hJ : J ≤ φ.range)
    (hA8 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))) : False := by
  classical
  obtain ⟨g0, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * (g0 + 1))
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 (g0 + 1)
  let G : Subgroup (ggU .PSU n (g0 + 1)).K := J.comap φ
  let π : ↥G →* X := φ.comp G.subtype
  have hπrange : π.range = J := by
    change (φ.comp G.subtype).range = J
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self hJ
  have hA8' : Nonempty
      ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπrange]
    exact hA8
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  ·
    have hn1 : n ≤ 1 := by omega
    have hsubSU : Subsingleton ↥(Unitary.SU σ n) := by
      have hn0 : n = 0 ∨ n = 1 := by omega
      rcases hn0 with rfl | rfl
      · constructor
        intro a b
        apply Subtype.ext
        apply Units.ext
        ext i j
        exact Fin.elim0 i
      · refine ⟨fun A B => ?_⟩
        apply CFSG.LieType.Universal.Unitary.SUExtras.mat_injective
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        rw [hi, hj]
        have hA : (A.1 : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
          have h := A.2.1
          rwa [Matrix.det_fin_one] at h
        have hB : (B.1 : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
          have h := B.2.1
          rwa [Matrix.det_fin_one] at h
        simp only [CFSG.LieType.Universal.Unitary.SUExtras.mat_apply]
        rw [hA, hB]
    have hfinSU : Finite ↥(Unitary.SU σ n) := inferInstance
    have : Finite (ggU .PSU n (g0 + 1)).K := hfinSU
    have : Finite ↥G := Finite.of_injective G.subtype (Subgroup.subtype_injective G)
    have : Finite ↥J := by
      have h : Finite ↥π.range :=
        Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
      rwa [hπrange] at h
    have : Finite (Subgroup.center ↥J) := inferInstance
    have hG1 : Nat.card (ggU .PSU n (g0 + 1)).K = 1 := by
      have hcard : Nat.card (ggU .PSU n (g0 + 1)).K =
          Nat.card ↥(Unitary.SU σ n) := rfl
      rw [hcard]
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsubSU, ⟨1⟩⟩
    have hJle : Nat.card ↥J ≤ Nat.card (ggU .PSU n (g0 + 1)).K := by
      have hJG : Nat.card ↥J ≤ Nat.card ↥G := by
        have h := Nat.card_le_card_of_surjective π.rangeRestrict π.rangeRestrict_surjective
        rwa [hπrange] at h
      have hGG : Nat.card ↥G ≤ Nat.card (ggU .PSU n (g0 + 1)).K :=
        Nat.card_le_card_of_injective G.subtype (Subgroup.subtype_injective G)
      exact le_trans hJG hGG
    have hcardJ : Nat.card ↥J = 20160 * Nat.card (Subgroup.center ↥J) := by
      have h := rckIIp_card_range_of_alt_eight π hA8'
      rwa [hπrange] at h
    have hJge : 20160 ≤ Nat.card ↥J := by
      rw [hcardJ]
      calc 20160 = 20160 * 1 := (mul_one _).symm
        _ ≤ 20160 * Nat.card (Subgroup.center ↥J) :=
          Nat.mul_le_mul_left _ (Nat.card_pos (α := Subgroup.center ↥J))
    omega
  ·
    have hn2' : n = 2 := by omega
    subst n
    let j : ↥G →* GL (Fin 2) F := (Unitary.SU σ 2).subtype.comp G.subtype
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subgroup.subtype_injective G
        (Subgroup.subtype_injective (Unitary.SU σ 2) hxy)
    let : Finite ↥G := Finite.of_injective j hj
    exact rckIIp_false_of_alt_eight_of_GL_two (F := F) (ι := Fin 2) (by simp) j hj π hA8'

end CFSG.StandardType.RCKC1
