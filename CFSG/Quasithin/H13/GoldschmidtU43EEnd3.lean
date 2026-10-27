module

public import CFSG.Quasithin.H13.GoldschmidtU43EEnd2
public import CFSG.Quasithin.H13.GoldschmidtU43Assembly
public import CFSG.Quasithin.H13.GoldschmidtU43ModOne
public import CFSG.GH74.GLS.Stage12.McLEndgame

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.LieType.Multipliers.U43 (X₀ card_X₀)

theorem u43Endgame_of_oneClass (h : X0OneClass) : U43Endgame := by
  intro G _ _ z hz X hHX hXeq
  obtain ⟨e⟩ := hXeq
  by_contra hXtop
  have h' : ∀ u v : X₀, orderOf u = 2 → orderOf v = 2 → IsConj u v := h
  have hs : IsSimpleGroup ↥X := by
    have := isSimpleGroup_X₀
    exact MulEquiv.isSimpleGroup e
  have hzo : orderOf z = 2 := hz.orderOf_z
  have hzH : z ∈ Hz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzX : z ∈ X := hHX hzH
  have honeX : ∀ u v : ↥X, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
    intro u v hu hv
    have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (e v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    obtain ⟨c, hc⟩ := isConj_iff.mp (h' (e u) (e v) hu' hv')
    refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  have hev : Even (Nat.card ↥X) := by
    have h1 : orderOf (⟨z, hzX⟩ : ↥X) ∣ Nat.card ↥X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hzo] at h1
    exact even_iff_two_dvd.mpr h1
  have hcent : ∀ u : G, u ∈ X → orderOf u = 2 → Subgroup.centralizer ({u} : Set G) ≤ X := by
    intro u hu huo y hy
    have hu' : orderOf (⟨u, hu⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk]; exact huo
    have hz' : orderOf (⟨z, hzX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk]; exact hzo
    obtain ⟨c, hc⟩ := isConj_iff.mp (honeX ⟨u, hu⟩ ⟨z, hzX⟩ hu' hz')
    have hc' : (c : G) * u * (c : G)⁻¹ = z := congrArg Subtype.val hc
    have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hyc : (c : G) * y * (c : G)⁻¹ ∈ Hz z := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hc']
      calc (c : G) * y * (c : G)⁻¹ * ((c : G) * u * (c : G)⁻¹)
          = (c : G) * (y * u) * (c : G)⁻¹ := by group
        _ = (c : G) * (u * y) * (c : G)⁻¹ := by rw [hyu]
        _ = (c : G) * u * (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) := by group
    have hyX := hHX hyc
    have hy' : y = (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * (c : G) := by group
    rw [hy']
    exact X.mul_mem (X.mul_mem (X.inv_mem c.2) hyX) c.2
  have hSE := CFSG.GH74.GLS.Stage12.McLRec.isStronglyEmbedded_of_centralizers X hXtop hev honeX
    hcent
  have hnot2 : ¬ IsPGroup 2 ↥X := by
    intro hp
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    have hcard : Nat.card ↥X = 3265920 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_X₀
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn, hcard]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨g, hgU, hgz, -⟩ := hz.exists_g
  have hyo : orderOf (g⁻¹ * z * g) = 2 := by
    have := (MulAut.conj g⁻¹).orderOf_eq z
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hzo]
  have hyH : g⁻¹ * z * g ∈ Hz z := Uz_le_Hz z hgU
  have hxy : z * (g⁻¹ * z * g) = (g⁻¹ * z * g) * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp hyH).symm
  exact false_of_stronglyEmbedded_simple hSE hs hnot2 hzX hzo hyo hxy hgz.symm

end CFSG.Quasithin.H13.U43
