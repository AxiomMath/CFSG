module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm8

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

noncomputable abbrev zbar : S.Nbar := S.piN ⟨z, S.z_mem_Ng⟩

theorem zbar_sq : S.zbar * S.zbar = 1 := by
  rw [← map_mul]
  have : (⟨z, S.z_mem_Ng⟩ : ↥S.Ng) * ⟨z, S.z_mem_Ng⟩ = 1 := Subtype.ext S.z_sq
  rw [this, map_one]

theorem zbar_ne_one : S.zbar ≠ 1 := by
  intro h
  have hz : z ∈ S.Mg := (QuotientGroup.eq_one_iff (⟨z, S.z_mem_Ng⟩ : ↥S.Ng)).mp h
  have hodd := ((S.mem_Mg).1 hz).2
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact S.z_sq) S.hyp.z_ne_one
  rw [hz2] at hodd
  exact absurd hodd (by decide)

theorem centralizer_zbar_le {x : S.Nbar}
    (hx : x ∈ Subgroup.centralizer ({S.zbar} : Set S.Nbar)) : x ∈ S.Dbar := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  have hc : S.piN n * S.zbar = S.zbar * S.piN n :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hc' : S.piN (n * ⟨z, S.z_mem_Ng⟩) = S.piN (⟨z, S.z_mem_Ng⟩ * n) := by
    rw [map_mul, map_mul]
    exact hc
  have hm : (n * ⟨z, S.z_mem_Ng⟩)⁻¹ * (⟨z, S.z_mem_Ng⟩ * n) ∈ S.Mg.subgroupOf S.Ng :=
    QuotientGroup.eq.mp hc'
  have hm₀M : ((n : G) * z)⁻¹ * (z * (n : G)) ∈ S.Mg := hm
  set m₀ : G := ((n : G) * z)⁻¹ * (z * (n : G)) with hm₀
  have hzi : z⁻¹ = z := S.z_inv
  have hw : (n : G)⁻¹ * z * n = z * m₀ := by
    rw [hm₀]
    calc (n : G)⁻¹ * z * n = z * (z⁻¹ * (n : G)⁻¹ * z * n) := by group
      _ = z * (((n : G) * z)⁻¹ * (z * (n : G))) := by group
  have h3 : (z * m₀) * (z * m₀) = 1 := by
    rw [← hw]
    calc (n : G)⁻¹ * z * n * ((n : G)⁻¹ * z * n) = (n : G)⁻¹ * (z * z) * n := by group
      _ = 1 := by rw [S.z_sq]; group
  have h4 : m₀ * m₀ * m₀ = 1 := by
    rw [← pow_three']
    exact S.pow_three_Mg m₀ hm₀M
  have h1 : m₀ * z * m₀ = z := by
    calc m₀ * z * m₀ = (z * z) * m₀ * z * m₀ := by rw [S.z_sq, one_mul]
      _ = z * ((z * m₀) * (z * m₀)) := by group
      _ = z := by rw [h3, mul_one]
  have h2 : m₀ * z = z * (m₀ * m₀) := by
    calc m₀ * z = m₀ * z * (m₀ * m₀ * m₀) := by rw [h4, mul_one]
      _ = (m₀ * z * m₀) * m₀ * m₀ := by group
      _ = z * (m₀ * m₀) := by rw [h1]; group
  have e1 : z * (n : G) = (n : G) * (z * m₀) := by
    calc z * (n : G) = (n : G) * ((n : G)⁻¹ * z * n) := by group
      _ = (n : G) * (z * m₀) := by rw [hw]
  have hk : z * ((n : G) * m₀) = ((n : G) * m₀) * z := by
    calc z * ((n : G) * m₀) = (z * (n : G)) * m₀ := by group
      _ = ((n : G) * (z * m₀)) * m₀ := by rw [e1]
      _ = (n : G) * (z * (m₀ * m₀)) := by group
      _ = (n : G) * (m₀ * z) := by rw [← h2]
      _ = ((n : G) * m₀) * z := by group
  have hkN : (n : G) * m₀ ∈ S.Ng := mul_mem n.2 (S.Mg_le_Ng hm₀M)
  have hkH : (n : G) * m₀ ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk.symm
  obtain ⟨d, hd, t, ht, hdt⟩ := S.Ng_inf_Hz_eq hkN hkH
  refine ⟨⟨d, S.Dg_le_Ng hd⟩, hd, ?_⟩
  apply QuotientGroup.eq.mpr
  show ((⟨d, S.Dg_le_Ng hd⟩ : ↥S.Ng)⁻¹ * n : ↥S.Ng).1 ∈ S.Mg
  have e : d⁻¹ * (n : G) = t * m₀⁻¹ := by
    have : (n : G) = d * t * m₀⁻¹ := by
      rw [← hdt]
      group
    rw [this]
    group
  have hval : ((⟨d, S.Dg_le_Ng hd⟩ : ↥S.Ng)⁻¹ * n : ↥S.Ng).1 = d⁻¹ * (n : G) := rfl
  rw [hval, e]
  exact mul_mem (S.Tg_le_Mg ht) (inv_mem hm₀M)

theorem card_centralizer_zbar :
    Nat.card (Subgroup.centralizer ({S.zbar} : Set S.Nbar)) = 8 := by
  have hle : Subgroup.centralizer ({S.zbar} : Set S.Nbar) ≤ S.Dbar := fun x hx =>
    S.centralizer_zbar_le hx
  have hge : S.Dbar ≤ Subgroup.centralizer ({S.zbar} : Set S.Nbar) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdz : (d : G) * z = z * (d : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (S.Dg_le_Hz hd)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdz
  have : S.Dbar = Subgroup.centralizer ({S.zbar} : Set S.Nbar) := le_antisymm hge hle
  rw [← this]
  exact S.card_Dbar

end JWSetup

end CFSG.Quasithin.H13.U43
