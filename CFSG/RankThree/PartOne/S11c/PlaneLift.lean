module

public import CFSG.RankThree.PartOne.S11c.CentralLift
public import CFSG.RankThree.PartOne.S11.CatalogLeaves
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG

theorem conj_injective_of_center_bot {T : Type*} [Group T] (h : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  intro g g' hgg
  have hc : g'⁻¹ * g ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut T => α x) hgg
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem isElementaryAbelian_of_mulEquiv_lift {p : ℕ} {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : IsElementaryAbelian p G) : IsElementaryAbelian p H :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem planeCentralizes_of_central_lift {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥) {p : ℕ} {E : Subgroup (MulAut T)} {U : Subgroup T}
    (hplane : PlaneOn p E U) (hE : E ≤ (MulAut.conj : T →* MulAut T).range) {M : Type}
    [Group M] [Finite M] (π : M →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center M) (hpk : ¬ p ∣ Nat.card π.ker)
    (key : ∀ F' U' : Subgroup M, IsElementaryAbelian p F' → Nat.card F' = p ^ 2 →
      IsPGroup 2 U' → (∀ x ∈ F', ∀ u ∈ U', x * u * x⁻¹ ∈ U') →
        ∀ x ∈ F', ∀ u ∈ U', x * u = u * x) :
    PlaneCentralizes E U := by
  classical
  have hp := hplane.prime
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_of_center_bot hZ
  let E' : Subgroup T := E.comap (MulAut.conj : T →* MulAut T)
  have hE'map : E'.map (MulAut.conj : T →* MulAut T) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hE
  let eEE' : E' ≃* E :=
    (Subgroup.equivMapOfInjective E' MulAut.conj hinj).trans (MulEquiv.subgroupCongr hE'map)
  have hE'el : IsElementaryAbelian p E' :=
    isElementaryAbelian_of_mulEquiv_lift eEE'.symm hplane.elementary
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [Nat.card_congr eEE'.toEquiv]
    exact hplane.card
  have hE'U : ∀ x ∈ E', ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun x hx u hu =>
    hplane.normalized (MulAut.conj x) hx u hu
  obtain ⟨F', hF'p, hF'map, hF'inj⟩ := exists_pSubgroup_lift π hπ hpk
    (IsElementaryAbelian.isPGroup p E')
  obtain ⟨U', hU'2, hU'map, hU'norm⟩ := exists_twoSubgroup_lift π hπ hker hplane.two_group
  have eF : F' ≃* E' :=
    (MonoidHom.ofInjective hF'inj).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hF'map]))
  have hF'el : IsElementaryAbelian p F' := isElementaryAbelian_of_mulEquiv_lift eF.symm hE'el
  have hF'card : Nat.card F' = p ^ 2 := by
    rw [Nat.card_congr eF.toEquiv]
    exact hE'card
  have hmem : ∀ x ∈ F', π x ∈ E' := fun x hx => hF'map ▸ Subgroup.mem_map_of_mem π hx
  have hnorm : ∀ x ∈ F', ∀ u ∈ U', x * u * x⁻¹ ∈ U' := fun x hx u hu =>
    hU'norm x (fun v hv => hE'U _ (hmem x hx) v hv) (fun v hv => by
      have := hE'U (π x)⁻¹ (E'.inv_mem (hmem x hx)) v hv
      rwa [inv_inv] at this) u hu
  have hcomm := key F' U' hF'el hF'card hU'2 hnorm
  intro β hβ u hu
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ E', MulAut.conj x = β := by
    have : β ∈ E'.map (MulAut.conj : T →* MulAut T) := hE'map ▸ hβ
    obtain ⟨x, hx, hxβ⟩ := this
    exact ⟨x, hx, hxβ⟩
  have hx' : x ∈ F'.map π := by rw [hF'map]; exact hx
  have hu'' : u ∈ U'.map π := by rw [hU'map]; exact hu
  obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hx'
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu''
  change π f * π u' * (π f)⁻¹ = π u'
  rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, hcomm f hf u' hu']

end CFSG.RankThree.PartOne
