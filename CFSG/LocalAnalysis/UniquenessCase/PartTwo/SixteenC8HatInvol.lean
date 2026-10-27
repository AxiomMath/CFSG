module

import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrder
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem c8h_matrix_sq_eq_one_or_neg_one {g : ↥(StatedSL 2 (ZMod 7))} (hg : g ^ 2 = 1) :
    ((g : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = 1 ∨
      ((g : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = -1 := by
  have hdet : ((g : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL g.2
  have hsq : ((g : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) *
      ((g : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = 1 := by
    have h2 : (g : GL (Fin 2) (ZMod 7)) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hg
    have h3 := congrArg (fun u : GL (Fin 2) (ZMod 7) =>
      (u : Matrix (Fin 2) (Fin 2) (ZMod 7))) h2
    simpa [pow_two] using h3
  exact CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one
    (by decide : (2 : ZMod 7) ≠ 0) hdet hsq

private theorem c8h_eq_of_matrix_eq_neg {g u : ↥(StatedSL 2 (ZMod 7))}
    (hg : ((g : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = -1)
    (hu : ((u : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = -1) :
    g = u := by
  apply Subtype.ext
  apply Units.ext
  rw [hg, hu]

theorem c8h_invol_of_sl2 {Γ : Type} [Group Γ] [Finite Γ]
    (hl3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1) (ρ : Γ →* ↥(StatedSL 2 (ZMod 7)))
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ CFSG.pPrimeCore 3 Γ) :
    ∀ t : Γ, t ^ 2 = 1 → t ∈ CFSG.pPrimeCore 3 Γ := by
  intro t ht
  have hcard : Nat.card (Γ ⧸ CFSG.pPrimeCore 3 Γ) = 168 :=
    CFSG.LocalAnalysis.WeakClosure81.card_eq_of_isL3 hl3
  have hidx : (CFSG.pPrimeCore 3 Γ).index = 168 := hcard
  have hS : Nat.card ↥(StatedSL 2 (ZMod 7)) = 336 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two (ZMod 7), Nat.card_zmod]
    norm_num
  have hindex : ((CFSG.pPrimeCore 3 Γ).map ρ).index = (CFSG.pPrimeCore 3 Γ).index :=
    Subgroup.index_map_eq _ hρ hker
  have hcardmap : Nat.card ↥((CFSG.pPrimeCore 3 Γ).map ρ) * 168 = 336 := by
    have h := Subgroup.card_mul_index ((CFSG.pPrimeCore 3 Γ).map ρ)
    rw [hindex, hidx, hS] at h
    exact h
  have hcardI : Nat.card ↥((CFSG.pPrimeCore 3 Γ).map ρ) = 2 := by omega
  haveI : Nontrivial ↥((CFSG.pPrimeCore 3 Γ).map ρ) :=
    (Finite.one_lt_card_iff_nontrivial).1 (by rw [hcardI]; norm_num)
  obtain ⟨u, hu_ne⟩ := exists_ne (1 : ↥((CFSG.pPrimeCore 3 Γ).map ρ))
  have hu2 : u ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := u)
    rwa [hcardI] at h
  have hu_mat : ((u : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) = -1 := by
    have hu2' : (u : ↥(StatedSL 2 (ZMod 7))) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hu2
    rcases c8h_matrix_sq_eq_one_or_neg_one hu2' with h | h
    · exact absurd (Subtype.ext (Subtype.ext (by apply Units.ext; simpa using h))) hu_ne
    · exact h
  have hρt2 : (ρ t) ^ 2 = 1 := by
    simpa [map_pow] using congrArg ρ ht
  rcases c8h_matrix_sq_eq_one_or_neg_one (g := ρ t) hρt2 with h1 | h1
  · have hρt : ρ t = 1 := by
      apply Subtype.ext
      apply Units.ext
      simpa using h1
    exact hker (MonoidHom.mem_ker.mpr hρt)
  · have hρtu : ρ t = (u : ↥(StatedSL 2 (ZMod 7))) := c8h_eq_of_matrix_eq_neg h1 hu_mat
    obtain ⟨i, hiI, hiu⟩ := Subgroup.mem_map.1 u.2
    have hmem : i⁻¹ * t ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hiu, hρtu, inv_mul_cancel]
    have hiIt : i⁻¹ * t ∈ CFSG.pPrimeCore 3 Γ := hker hmem
    have ht_eq : t = i * (i⁻¹ * t) := by group
    rw [ht_eq]
    exact (CFSG.pPrimeCore 3 Γ).mul_mem hiI hiIt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
