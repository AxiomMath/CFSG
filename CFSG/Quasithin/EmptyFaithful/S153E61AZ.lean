module

public import CFSG.Quasithin.EmptyFaithful.S153E61AC
public import CFSG.Quasithin.EmptyFaithful.S153E58N
public import CFSG.Quasithin.EmptyFaithful.S153E61AB
public import CFSG.Quasithin.EmptyFaithful.S153E61Def

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem inv_U_conj_V (cx : Ctx15350 T Mc M V₁ V₂ t) (hD : S153E61.Data61 cx)
    (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∀ u ∈ UH153 T M V₁ Mc, u * u = 1 → ∃ h ∈ Mc, h * u * h⁻¹ ∈ VZ T M := by
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨K, W₁, W₂, π, hS, hperf, hπ⟩ := hD
  have c56 : Chain15356 cx N₁ N₂ g s y t₁ := c.toChain15356
  have hK : oTwoUpper (HStar153 T M V₁ Mc) = K := hS.oTwoUpper_eq hπ hperf
  obtain ⟨a, haV, ha1, haK⟩ := S153E61A.exists_a_mem_K cx c
  rw [hK] at haK
  have haH : a ∈ HStar153 T M V₁ Mc := hS.KH haK
  obtain ⟨e, hT, -⟩ := S153E58.exists_coords_of_realizes hπ
  obtain ⟨w₁, hw₁, hne₁⟩ : ∃ w ∈ W₁, a w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact ha1 (hS.eq_one_of_triv₁ hT haH hcon)
  obtain ⟨w₂, hw₂, hne₂⟩ : ∃ w ∈ W₂, a w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact ha1 (S153E61A.eq_one_of_triv₂ hS hπ haK hcon)
  have hPt : ∀ w, a w * w⁻¹ ∈ S153E58.Pt T M V₁ Mc := by
    intro w
    rw [← S153E58.commIn153_eq_Pt cx c56]
    exact Subgroup.subset_closure ⟨a, haV, w, Subgroup.mem_top _, rfl⟩
  intro u hu hsq
  have hq0 : S153E61A.qU cx (S153E57.piU cx ⟨u, hu⟩) = 0 := by
    rw [S153E61A.qU_piU cx c.h56]
    have h2 : u ^ 2 = 1 := by rw [pow_two]; exact hsq
    simp [pwr153, h2]
  obtain ⟨k', hk'K, hk'Pt⟩ := S153E61A.exists_conj_mem_of_singular hS hπ (S153E61A.qU cx)
    (S153E61A.qU_mul cx c.h56) (fun k hk x => S153E61A.qU_apply_HStar cx c.h56 (hS.KH hk) x)
    (Pt := S153E58.Pt T M V₁ Mc) (S153E61A.qU_Pt cx c.h56)
    (W₁.mul_mem (hS.inv₁ a haK w₁ hw₁) (W₁.inv_mem hw₁)) (fun h => hne₁ (mul_inv_eq_one.1 h)) (hPt w₁)
    (W₂.mul_mem (hS.inv₂ a haK w₂ hw₂) (W₂.inv_mem hw₂)) (fun h => hne₂ (mul_inv_eq_one.1 h)) (hPt w₂)
    _ hq0
  obtain ⟨k, hkN, hkK, hkρ⟩ := S153E61A.exists_lift_K cx (k' := k') (by rw [hK]; exact hk'K)
  have hkMc : k ∈ Mc := oTwoUpper_le Mc hkK
  refine ⟨k, hkMc, ?_⟩
  have h1 := S153E57.piU_conj cx ⟨k, hkN⟩ hkMc ⟨u, hu⟩
  rw [hkρ] at h1
  have h2 := hk'Pt
  rw [← h1] at h2
  exact ((S153E58.mem_Pt_iff cx _).1 h2).1

end S153E

end CFSG.Quasithin
