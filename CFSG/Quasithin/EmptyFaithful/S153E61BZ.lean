module

public import CFSG.Quasithin.EmptyFaithful.S153E61BE
public import CFSG.Quasithin.EmptyFaithful.S153E61BB
public import CFSG.Quasithin.EmptyFaithful.S153E61Def

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem inv_K_not_U (cx : Ctx15350 T Mc M V₁ V₂ t) (hD : S153E61.Data61 cx)
    (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∀ x ∈ oTwoUpper Mc, x ∉ UH153 T M V₁ Mc → x * x = 1 →
      ∃ k ∈ oTwoUpper Mc, ∃ a ∈ VZ T M, ∃ u ∈ UH153 T M V₁ Mc, (∀ w ∈ VZ T M, u * w = w * u) ∧
        k * x * k⁻¹ = a * u := by
  intro x hxK hxU hx2
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨K, W₁, W₂, π, hS, hperf, hπ⟩ := hD
  have hxM : x ∈ Mc := oTwoUpper_le Mc hxK
  obtain ⟨a, haV, haU⟩ := S153E61B.exists_a_V_not_U cx c
  have haMc : a ∈ Mc := S153E59.VZ_le_Mc cx haV
  have haN : a ∈ S153E57.NZ T := S153E57.Mc_le_NZ cx haMc
  have haa : a * a = 1 := by
    have := cx.c.hyp.elemAbelian.2 a haV
    rwa [pow_two] at this
  let xm : ↥Mc := ⟨x, hxM⟩
  let am : ↥Mc := ⟨a, haMc⟩
  have hρxK : S153E59.rho cx xm ∈ oTwoUpper (HStar153 T M V₁ Mc) := by
    rw [← S153E59.map_rho_oTwoUpper cx]
    exact Subgroup.mem_map.mpr ⟨xm, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
  have hρaK : S153E59.rho cx am ∈ oTwoUpper (HStar153 T M V₁ Mc) :=
    S153E61B.rho_a_mem_K cx c haV haU
  have hρx1 : S153E59.rho cx xm ≠ 1 := fun h =>
    hxU (c.h59.one ▸ (S153E59.rho_eq_one_iff cx xm).1 h)
  have hρa1 : S153E59.rho cx am ≠ 1 := fun h =>
    haU (c.h59.one ▸ (S153E59.rho_eq_one_iff cx am).1 h)
  have hρx2 : S153E59.rho cx xm * S153E59.rho cx xm = 1 := by
    rw [← map_mul, show xm * xm = 1 from Subtype.ext hx2, map_one]
  have hρa2 : S153E59.rho cx am * S153E59.rho cx am = 1 := by
    rw [← map_mul, show am * am = 1 from Subtype.ext haa, map_one]
  obtain ⟨r, hr, hrconj⟩ := S153E61B.invol_conj_oTwoUpper hS hπ hperf hρxK hρx1 hρx2 hρaK hρa1 hρa2
  rw [← S153E59.map_rho_oTwoUpper cx] at hr
  obtain ⟨k, hk, hkr⟩ := Subgroup.mem_map.mp hr
  have hkK : (k : G) ∈ oTwoUpper Mc := Subgroup.mem_subgroupOf.mp hk
  let um : ↥Mc := am⁻¹ * (k * xm * k⁻¹)
  have hρu : S153E59.rho cx um = 1 := by
    have h1 : S153E59.rho cx (k * xm * k⁻¹) = S153E59.rho cx am := by
      rw [map_mul, map_mul, map_inv, hkr]
      exact hrconj
    rw [show um = am⁻¹ * (k * xm * k⁻¹) from rfl, map_mul, map_inv, h1, inv_mul_cancel]
  have huU : (um : G) ∈ UH153 T M V₁ Mc := by
    rw [c.h59.one]
    exact (S153E59.rho_eq_one_iff cx um).1 hρu
  have hum : (um : G) = a⁻¹ * ((k : G) * x * (k : G)⁻¹) := rfl
  have hkxk : (k : G) * x * (k : G)⁻¹ = a * (um : G) := by
    rw [hum]
    group
  have hau : a * (um : G) * (a * (um : G)) = 1 := by
    rw [← hkxk]
    calc (k : G) * x * (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) = (k : G) * (x * x) * (k : G)⁻¹ := by
          group
      _ = 1 := by rw [hx2]; group
  have hconj : a * (um : G) * a⁻¹ = (um : G)⁻¹ := by
    have h1 : a * (um : G) * a = (um : G)⁻¹ := by
      have h2 : a * (um : G) * a * (um : G) = 1 := by
        calc a * (um : G) * a * (um : G) = a * (um : G) * (a * (um : G)) := by group
          _ = 1 := hau
      exact mul_eq_one_iff_eq_inv.1 h2
    have h3 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rw [h3]
    exact h1
  have hq : ∀ q : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), q * q = 1 := by
    intro q
    have := cx.hF.isElemAbelian_tilde.2 q q.2
    exact Subtype.ext (by simpa [pow_two] using this)
  have hρfix : S153E57.rho cx ⟨a, haN⟩ (S153E57.piU cx ⟨(um : G), huU⟩) =
      S153E57.piU cx ⟨(um : G), huU⟩ := by
    have h := S153E57.piU_conj cx ⟨a, haN⟩ haMc ⟨(um : G), huU⟩
    have e : (⟨(↑(⟨a, haN⟩ : S153E57.NZ T) : G) * ((⟨(um : G), huU⟩ : ↥(UH153 T M V₁ Mc)) : G) *
        (↑(⟨a, haN⟩ : S153E57.NZ T) : G)⁻¹, S153E.U_conj_mem haMc huU⟩ : ↥(UH153 T M V₁ Mc)) =
        ⟨(um : G), huU⟩⁻¹ := Subtype.ext hconj
    calc S153E57.rho cx ⟨a, haN⟩ (S153E57.piU cx ⟨(um : G), huU⟩)
        = S153E57.piU cx (⟨(um : G), huU⟩⁻¹) := h.symm.trans (congrArg (S153E57.piU cx) e)
      _ = (S153E57.piU cx ⟨(um : G), huU⟩)⁻¹ := map_inv _ _
      _ = S153E57.piU cx ⟨(um : G), huU⟩ := inv_eq_of_mul_eq_one_right (hq _)
  exact ⟨k, hkK, a, haV, um, huU, S153E61B.centralizer_of_fix cx c haV haU haN huU hρfix, hkxk⟩

end S153E

end CFSG.Quasithin
