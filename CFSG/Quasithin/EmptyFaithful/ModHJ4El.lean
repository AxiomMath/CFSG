module

public import CFSG.Quasithin.EmptyFaithful.ModHJ2Core
public import CFSG.Quasithin.EmptyFaithful.ModHEl
public import CFSG.Quasithin.EmptyFaithful.A38c8J4
public import CFSG.Sporadic.J4.QT2LocUniq

public section

namespace CFSG.Quasithin.ModH.J4El

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.R3c14
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.ModH.SylowCore

theorem strongSylow_J
    (hF : J4Facts) : StrongSylow ↥J := by
  have hM : MatFacts := hF.mat
  let P0s : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  have hP0s : (P0s : Subgroup J) = P0 := Sylow.coe_ofCard _ _
  have hEP0 : Eg uJ 11 ≤ P0 := Eg_le_P0
  have hZ1 : Zc 1 = ZE [0, 1131] := Zc_eq hM hF 1 (by norm_num)
  have hz1 : eta uJ 11 1131 ∈ Zc 1 := by
    rw [hZ1]
    exact ⟨1131, by simp, rfl⟩
  have hcentral : ∀ x ∈ P0, (∀ y ∈ P0, x * y * x⁻¹ * y⁻¹ = 1) → x = 1 ∨ x = eta uJ 11 1131 := by
    intro x hx hcomm
    have hx1 : x ∈ Zc 1 := ⟨hx, fun y hy => by rw [hcomm y hy]; exact Set.mem_singleton _⟩
    rw [hZ1] at hx1
    obtain ⟨c, hc, rfl⟩ := hx1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inl (eta_zero _ _)
    · exact Or.inr rfl
  refine ⟨P0s, eta uJ 11 1131, by rw [hP0s]; exact eta_mem_P0 1131, ?_, ?_⟩
  · intro t ht
    rw [hP0s] at ht
    have h1 : eta uJ 11 1131 * t * (eta uJ 11 1131)⁻¹ * t⁻¹ = 1 := hz1.2 t ht
    calc eta uJ 11 1131 * t = (eta uJ 11 1131 * t * (eta uJ 11 1131)⁻¹ * t⁻¹) * t *
          eta uJ 11 1131 := by group
      _ = t * eta uJ 11 1131 := by rw [h1]; group
  · intro α hfix
    rw [hP0s] at hfix
    obtain ⟨k, hk⟩ := aut_of_maps_P0 hF α (fun x hx => by rw [hfix x hx]; exact hx)
    have hkc : ∀ t ∈ P0, k * t * k⁻¹ = t := fun t ht => by rw [← hk t, hfix t ht]
    have hkE : k ∈ Eg uJ 11 := by
      have hkH : k ∈ Hj := by
        refine mem_Hj_of_big_inter hF (V := Eg uJ 11) le_rfl (fun v hv => ?_) (by
          rw [card_Eg_uJ hM]; norm_num)
        have h1 := hkc v (hEP0 hv)
        have : k⁻¹ * v * k = v := by
          calc k⁻¹ * v * k = k⁻¹ * (k * v * k⁻¹) * k := by rw [h1]
            _ = v := by group
        rw [this]
        exact hv
      exact centralizer_Hj hM hF k hkH fun y hy => by
        have h1 := hkc y (hEP0 hy)
        calc k * y = (k * y * k⁻¹) * k := by group
          _ = y * k := by rw [h1]
    rcases hcentral k (hEP0 hkE) (fun y hy => by rw [hkc y hy]; group) with rfl | rfl
    · left
      exact MulEquiv.ext fun x => by rw [hk x]; simp
    · right
      exact MulEquiv.ext fun x => by rw [hk x, MulAut.conj_apply]

theorem strongSylow_j4 :
    StrongSylow (NativeSporadic.Carrier .J4) :=
  @StrongSylow.of_equiv (NativeSporadic.Carrier .J4) ↥J _ _ _
    (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
    (strongSylow_J CFSG.Sporadic.J4.j4Facts)

theorem not_elConfig_j4 :
    ¬ ElConfig (NativeSporadic.Carrier .J4) := by
  have hs := strongSylow_j4
  have hZ : Subgroup.center (NativeSporadic.Carrier .J4) = ⊥ :=
    A38c8.center_eq_bot_of_isSporadic_j4 ⟨MulEquiv.refl _⟩
  have : Finite (NativeSporadic.Carrier .J4) := (CFSG.Sporadic.J4.fam_j4_simplicity).1
  obtain ⟨P, hP⟩ := hs.exists_center_small hZ
  exact ModH.not_elConfig_of_center hs.pointwise
    (ModH.centerSmall_of_one (K1.isSylowTwoOf_top_iff.2 ⟨P.isPGroup', P.not_dvd_index⟩) hP)

end CFSG.Quasithin.ModH.J4El
