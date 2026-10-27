module

public import CFSG.Quasithin.H13.GoldschmidtU43BK2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Swap

variable [Finite G] {z t w a : G} (s : Swap z t w) (ha : Good z t a)
include s ha

theorem exists_conj_to_z {y : G} (hy : y ∈ Eg z t w a) (hy1 : y ≠ 1) :
    ∃ k ∈ Subgroup.normalizer (Eg z t w a : Set G), k * z * k⁻¹ = y := by
  classical
  have h := s.hyp
  set E := Eg z t w a with hE
  set K := Subgroup.normalizer (E : Set G) with hK
  let O : Set G := {y | ∃ k ∈ K, k * z * k⁻¹ = y}
  have hz : z ∈ E := z_mem_Eg
  have hΩ : ∀ g ∈ K, ∀ y ∈ O, g * y * g⁻¹ ∈ O := by
    rintro g hg y ⟨k, hk, rfl⟩
    exact ⟨g * k, mul_mem hg hk, by group⟩
  have hzO : z ∈ O := ⟨1, one_mem _, by group⟩
  have hcount := card_eq_ncard_mul_card_inf_centralizer K O z hΩ hzO (fun y hy => hy)
  have hKP : K ⊓ Subgroup.centralizer ({z} : Set G) = Pg z t w a := inf_comm _ _
  rw [hKP, s.card_P ha, s.card_normalizer_Eg ha] at hcount
  have hO15 : O.ncard = 15 := by omega
  have hOsub : O ⊆ (E : Set G) \ {1} := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hk z).mp hz, fun e => h.z_ne_one ?_⟩
    have e' : k * z * k⁻¹ = 1 := e
    calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
      _ = 1 := by rw [e']; group
  have hE15 : ((E : Set G) \ {1}).ncard = 15 := by
    have := Set.ncard_sdiff_singleton_of_mem (s := (E : Set G)) (a := 1) (one_mem _)
    rw [this]
    have h16 : (E : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact s.card_Eg ha
    omega
  have heq := Set.eq_of_subset_of_ncard_le hOsub (by omega) (Set.toFinite _)
  have hyO : y ∈ O := by
    rw [heq]
    exact ⟨hy, hy1⟩
  exact hyO

end Swap

end CFSG.Quasithin.H13.U43
