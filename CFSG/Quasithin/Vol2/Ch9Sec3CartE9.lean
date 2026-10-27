module

public import CFSG.Quasithin.Vol2.Ch9Sec3Cart

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {D : Subgroup G}

theorem exists_e9 (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) :
    ∃ a ∈ D, ∃ b ∈ D, a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ∉ Subgroup.zpowers a := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have : Nontrivial Kˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  obtain ⟨a, haD, haL, hψa⟩ := exists_mem_of_diag hdiag ω 1
  obtain ⟨b, hbD, hbL, hψb⟩ := exists_mem_of_diag hdiag 1 ω
  have hdiag1 : (diagOf (1 : Kˣ) : SpecialLinearGroup (Fin 2) K) = 1 := (diagHom K).map_one
  have hdiagω : (diagOf ω : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
    intro h
    apply hω
    have h00 := congrArg
      (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [coe_diagOf, Matrix.SpecialLinearGroup.coe_one] at h00
    exact Units.ext (by simpa using h00)
  refine ⟨a, haD, b, hbD, hc.mul_comm_of_mem h37c h38c hD hdiag haD hbD,
    hc.pow_three_eq_one h37c h38c h2 hD hdiag haD, hc.pow_three_eq_one h37c h38c h2 hD hdiag hbD,
    ?_, ?_⟩
  · intro ha1
    apply hdiagω
    have h1 : ψ ⟨a, haL⟩ = 1 := by
      rw [show (⟨a, haL⟩ : ↥(fsuL0 T L)) = 1 from Subtype.ext ha1, map_one]
    rw [hψa] at h1
    exact congrArg Prod.fst h1
  · intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    apply hdiagω
    have h1 : ψ ⟨b, hbL⟩ = ψ ⟨a, haL⟩ ^ k := by
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [hψa, hψb] at h1
    have h2 := congrArg Prod.snd h1
    rw [Prod.pow_snd, hdiag1, _root_.one_zpow] at h2
    exact h2

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
