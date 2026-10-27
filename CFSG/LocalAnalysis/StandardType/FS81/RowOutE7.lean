module

public import CFSG.LocalAnalysis.StandardType.FS81.RowCent
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly


theorem rowOutAt_E7 : RowOutAt Row.E7 := by
  intro G _ _ b₀ K E hstd _ _ _ _
  obtain ⟨hsimple, hhyp, hcanon⟩ := hstd
  obtain ⟨hA, hmaxE, hb₀E, hEcard, hm7, hbig⟩ := hhyp
  obtain ⟨hb₀, hKC, hKn, hKz, hmark, hcyc, hm23, hweak⟩ := hA
  obtain ⟨hrow, hdisj, hsup, hmaxK, hAcard, hCK⟩ := hcanon
  obtain ⟨lab, hlabP, hlab⟩ := exists_glaLabel hrow
  obtain ⟨t, r, n⟩ := lab
  have hn1 : n = 1 := hlabP.1
  subst hn1
  have ht : t = .E7 := by
    obtain ⟨-, hcases⟩ := hlabP
    rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hKz
  have hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hK2 : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  apply le_antisymm
  · intro c hc
    let ψ := φ.symm.trans ((ggConjAut K (hKN hc)).trans φ)
    obtain ⟨y, hy⟩ := TableBExcTwo.mem_range_conj_adjoint (Or.inl rfl) hK2 ψ
    let k : ↥K := φ.symm y
    have hkey : ∀ x : ↥K, (k : G) * (x : G) * (k : G)⁻¹ = c * (x : G) * c⁻¹ := by
      intro x
      have h1 : y * φ x * y⁻¹ = φ ((ggConjAut K (hKN hc)) x) := by
        have h := DFunLike.congr_fun hy (φ x)
        simpa [ψ, MulEquiv.trans_apply, MulAut.conj_apply] using h
      have h2 : k * x * k⁻¹ = ggConjAut K (hKN hc) x := by
        have h := congrArg (fun z => φ.symm z) h1
        simpa [k, map_mul, map_inv] using h
      have h3 := congrArg (fun z : ↥K => (z : G)) h2
      simpa [ggConjAut_apply] using h3
    have hmem : (k : G)⁻¹ * c ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := hkey ⟨x, hx⟩
      change (k : G) * x * (k : G)⁻¹ = c * x * c⁻¹ at h
      calc x * ((k : G)⁻¹ * c)
          = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * c := by group
        _ = (k : G)⁻¹ * (c * x * c⁻¹) * c := by rw [h]
        _ = ((k : G)⁻¹ * c) * x := by group
    have hk : (k : G) ∈ K := (k : ↥K).2
    have hmemC : (k : G)⁻¹ * c ∈ Subgroup.centralizer ({b₀} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hk)) hc
    rw [show c = (k : G) * ((k : G)⁻¹ * c) by group]
    exact Subgroup.mul_mem_sup hk ⟨hmemC, hmem⟩
  · exact sup_le hKC inf_le_left

theorem rowCentAt_E7 : RowCentAt Row.E7 :=
  rowCentAt_of_rowOutAt rowOutAt_E7

end CFSG.StandardType.FrameRoute.FS81
