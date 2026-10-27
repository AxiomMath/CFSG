module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm2
public import CFSG.Quasithin.H13.GoldschmidtU43EQCoset

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem Ng_inf_Hz_eq {g : G} (hgN : g ∈ S.Ng) (hgH : g ∈ Hz z) :
    ∃ d ∈ S.Dg, ∃ t ∈ S.Tg, g = d * t := by
  have hgT := S.normalizer_Tg_of_Ng_Hz hgN hgH
  have hnR : (⟨g, hgH⟩ : ↥(Hz z)) ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) :=
    S.mem_normalizer_R_of hgT
  obtain ⟨r, hr, w, hw, hact⟩ := S.exists_coset ⟨g, hgH⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  have hwN : w ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) := by
    rcases hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact S.hu
    · exact S.hv
    · exact S.huv
  have hwD : (w : G) ∈ S.Dg := by
    rcases hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact S.u_mem_Dg
    · exact S.v_mem_Dg
    · exact mul_mem S.u_mem_Dg S.v_mem_Dg
  have hk1 : S.hyp.act ((w * r)⁻¹ * ⟨g, hgH⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, hact]
    group
  have hkN : (w * r)⁻¹ * (⟨g, hgH⟩ : ↥(Hz z)) ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) :=
    mul_mem (inv_mem (mul_mem hwN (Subgroup.le_normalizer hr))) hnR
  have hgk : (⟨g, hgH⟩ : ↥(Hz z)) = w * r * ((w * r)⁻¹ * ⟨g, hgH⟩) := by group
  have hgkG : g = (w : G) * r * (((w * r)⁻¹ * ⟨g, hgH⟩ : ↥(Hz z)) : G) := congrArg Subtype.val hgk
  rcases S.hR.normalizer_inf_ker hkN (MonoidHom.mem_ker.mpr hk1) with h1 | h1
  · refine ⟨w, hwD, r, S.coe_mem_Tg hr, ?_⟩
    rw [hgkG, h1, mul_one]
  · refine ⟨(w : G) * z, mul_mem hwD S.z_mem_Dg, r, S.coe_mem_Tg hr, ?_⟩
    rw [hgkG, h1]
    have hzr : (r : G) * z = z * (r : G) := z_comm_H r
    calc (w : G) * r * z = (w : G) * (r * z) := by group
      _ = (w : G) * (z * r) := by rw [hzr]
      _ = (w : G) * z * r := by group

omit [Finite G] in
theorem Dg_le_normalizer_Tg : S.Dg ≤ Subgroup.normalizer (S.Tg : Set G) := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact S.v_normalizer_Tg
  · exact S.u_normalizer_Tg

theorem normalizer_Dg_le {x : G} (hxN : x ∈ S.Ng) (hx : x ∈ Subgroup.normalizer (S.Dg : Set G)) :
    x ∈ S.Dg := by
  have hzD : z ∈ S.Dg := S.z_mem_Dg
  have hzc : ∀ d ∈ S.Dg, z * d = d * z := fun d hd =>
    (Subgroup.mem_centralizer_singleton_iff.mp (S.Dg_le_Hz hd)).symm
  have hw : x * z * x⁻¹ ∈ S.Dg := (Subgroup.mem_normalizer_iff.mp hx z).mp hzD
  have hwc : ∀ d ∈ S.Dg, (x * z * x⁻¹) * d = d * (x * z * x⁻¹) := by
    intro d hd
    have hd' : x⁻¹ * d * x ∈ S.Dg := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S.Dg : Set G)).inv_mem hx)
        d).mp hd
      simpa using this
    have hc := hzc _ hd'
    calc (x * z * x⁻¹) * d = x * (z * (x⁻¹ * d * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * d * x) * z) * x⁻¹ := by rw [hc]
      _ = d * (x * z * x⁻¹) := by group
  have hxz : x * z * x⁻¹ = z := by
    rcases S.center_Dg hw hwc with h | h
    · exfalso
      apply S.hyp.z_ne_one
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hxH : x ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hxz]
  obtain ⟨d, hd, t, ht, rfl⟩ := S.Ng_inf_Hz_eq hxN hxH
  have htN : t ∈ Subgroup.normalizer (S.Dg : Set G) := by
    have := mul_mem ((Subgroup.normalizer (S.Dg : Set G)).inv_mem
      (Subgroup.le_normalizer hd)) hx
    simpa [mul_assoc] using this
  have htc : ∀ d' ∈ S.Dg, t * d' = d' * t := by
    intro d' hd'
    have h1 : t * d' * t⁻¹ ∈ S.Dg := (Subgroup.mem_normalizer_iff.mp htN d').mp hd'
    have h2 : d' * t⁻¹ * d'⁻¹ ∈ S.Tg := by
      have := (Subgroup.mem_normalizer_iff.mp (S.Dg_le_normalizer_Tg hd') t⁻¹).mp
        (S.Tg.inv_mem ht)
      simpa using this
    have h3 : t * d' * t⁻¹ * d'⁻¹ ∈ S.Tg := by
      have := S.Tg.mul_mem ht h2
      simpa [mul_assoc] using this
    have h4 : t * d' * t⁻¹ * d'⁻¹ ∈ S.Dg := S.Dg.mul_mem h1 (S.Dg.inv_mem hd')
    have h5 : t * d' * t⁻¹ * d'⁻¹ = 1 := S.Dg_inf_Mg h4 (S.Tg_le_Mg h3)
    calc t * d' = (t * d' * t⁻¹ * d'⁻¹) * (d' * t) := by group
      _ = d' * t := by rw [h5, one_mul]
  have hvc : t * (S.v : G) = (S.v : G) * t := htc _ S.v_mem_Dg
  have hvt : (S.v : G)⁻¹ * t * S.v = t⁻¹ := S.v_inv_Tg ht
  have htt : t = t⁻¹ := by
    rw [← hvt]
    calc t = (S.v : G)⁻¹ * ((S.v : G) * t) := by group
      _ = (S.v : G)⁻¹ * (t * S.v) := by rw [hvc]
      _ = (S.v : G)⁻¹ * t * S.v := by group
  have ht2 : t * t = 1 := mul_eq_one_iff_eq_inv.mpr htt
  have ht3 : t ^ 3 = 1 := S.pow_three_Tg ht
  have ht1 : t = 1 := by
    calc t = (t * t * t) * (t * t)⁻¹ := by group
      _ = 1 := by rw [← pow_three', ht3, ht2]; simp
  rw [ht1, mul_one]
  exact hd

theorem exists_sylow_Dg : ∃ P : Sylow 2 ↥S.Ng, (P : Subgroup ↥S.Ng) = S.Dg.subgroupOf S.Ng := by
  have hle : S.Dg ≤ S.Ng := S.Dg_le_Ng
  have h8 : Nat.card (S.Dg.subgroupOf S.Ng) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, S.card_Dg]
  have hD2 : IsPGroup 2 (S.Dg.subgroupOf S.Ng) :=
    IsPGroup.of_card (n := 3) (h8.trans (by norm_num))
  refine u43_exists_sylow_eq hD2 ?_
  intro x hxN _
  have fwd : ∀ k : ↥S.Ng, k ∈ Subgroup.normalizer (↑(S.Dg.subgroupOf S.Ng) : Set ↥S.Ng) →
      ∀ y ∈ S.Dg, (k : G) * y * (k : G)⁻¹ ∈ S.Dg := by
    intro k hk y hy
    exact (Subgroup.mem_normalizer_iff.mp hk ⟨y, hle hy⟩).mp hy
  have hx : (x : G) ∈ Subgroup.normalizer (S.Dg : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fwd x hxN y
    · intro hy
      have := fwd x⁻¹ ((Subgroup.normalizer _).inv_mem hxN) _ hy
      have h2 : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * ((x : G)⁻¹)⁻¹ ∈ S.Dg := this
      have e : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * ((x : G)⁻¹)⁻¹ = y := by group
      rwa [e] at h2
  exact S.normalizer_Dg_le x.2 hx

end JWSetup

end CFSG.Quasithin.H13.U43
