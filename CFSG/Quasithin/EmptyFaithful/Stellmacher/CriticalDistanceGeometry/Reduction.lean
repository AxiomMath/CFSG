module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SmallGroups
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom Equiv

theorem exists_quotHom (hA : F53Amalgam H M S) (δ : Geo H M) :
    ∃ (n : ℕ) (ψ : ↥(stab δ) →* Perm (Fin n)), (n = 5 ∧ vtype δ = false ∨ n = 3 ∧ vtype δ = true) ∧
      Function.Surjective ψ ∧ ∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ := by
  have key : ∀ (n : ℕ), Nonempty (OTwoQuot (stab δ) ≃* Perm (Fin n)) →
      ∃ ψ : ↥(stab δ) →* Perm (Fin n), Function.Surjective ψ ∧
        ∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ := by
    rintro n ⟨e⟩
    refine ⟨(e : OTwoQuot (stab δ) →* Perm (Fin n)).comp
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(stab δ))), fun p => ?_, fun x => ?_⟩
    · obtain ⟨q, rfl⟩ := e.surjective p
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, rfl⟩
    · have hx : ((e : OTwoQuot (stab δ) →* Perm (Fin n)).comp
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(stab δ)))) x = e (QuotientGroup.mk x) := rfl
      rw [hx, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]
      rfl
  cases hv : vtype δ with
  | false =>
    obtain ⟨ψ, h1, h2⟩ := key 5 (quot_stab_five hA hv)
    exact ⟨5, ψ, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
  | true =>
    obtain ⟨ψ, h1, h2⟩ := key 3 (quot_stab_three hA hv)
    exact ⟨3, ψ, Or.inr ⟨rfl, rfl⟩, h1, h2⟩

theorem odd_mem_of_normal (hA : F53Amalgam H M S) {δ : Geo H M} {U D : Subgroup G}
    (hU : U ≤ stab δ) (hDU : D ≤ U) (hDn : U ≤ Subgroup.normalizer (D : Set G))
    (hD : ¬ D ≤ pCoreOf 2 U) :
    ∀ u ∈ U, Odd (orderOf u) → ∃ d ∈ D, ∃ e ∈ U ⊓ Qv δ, u = d * e := by
  obtain ⟨n, ψ, hn, hsurj, hker⟩ := exists_quotHom hA δ
  have hn' : n = 3 ∨ n = 5 := by rcases hn with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  set U' : Subgroup ↥(stab δ) := U.subgroupOf (stab δ) with hU'
  set D' : Subgroup ↥(stab δ) := D.subgroupOf (stab δ) with hD'
  have hDs : D ≤ stab δ := hDU.trans hU
  have hD'U' : D' ≤ U' := fun x hx => hDU hx
  have hNK : D'.map ψ ≤ U'.map ψ := Subgroup.map_mono hD'U'
  have hnorm : ∀ k ∈ U'.map ψ, ∀ y ∈ D'.map ψ, k * y * k⁻¹ ∈ D'.map ψ := by
    rintro k ⟨u', hu', rfl⟩ y ⟨d', hd', rfl⟩
    refine ⟨u' * d' * u'⁻¹, ?_, by simp⟩
    have h1 : (u' : G) ∈ U := hu'
    have h2 : (d' : G) ∈ D := hd'
    have := (Subgroup.mem_normalizer_iff.mp (hDn h1) (d' : G)).mp h2
    show (u' : G) * (d' : G) * (u' : G)⁻¹ ∈ D
    simpa using this
  have hp2 : ¬ IsPGroup 2 (D'.map ψ) := by
    intro hp
    apply hD
    have hker2 : IsPGroup 2 ψ.ker := by
      have : ψ.ker = (Qv δ).subgroupOf (stab δ) := by
        ext x; rw [MonoidHom.mem_ker, hker x, Subgroup.mem_subgroupOf]
      rw [this]
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (G := G) (r := 2) (stab δ)).comap_subtype
    have h3 : IsPGroup 2 ((D'.map ψ).comap ψ) := hp.comap_of_ker_isPGroup ψ hker2
    have h4 : IsPGroup 2 D' := h3.to_le (Subgroup.le_comap_map ψ D')
    have h5 : IsPGroup 2 D := by
      have := h4.map (stab δ).subtype
      rwa [show D'.map (stab δ).subtype = D from Subgroup.map_subgroupOf_eq_of_le hDs] at this
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hDU hDn h5
  intro u hu huo
  have hus : u ∈ stab δ := hU hu
  have hodd : Odd (orderOf (ψ ⟨u, hus⟩)) := by
    have hdvd := orderOf_map_dvd ψ (⟨u, hus⟩ : ↥(stab δ))
    have hor : orderOf (⟨u, hus⟩ : ↥(stab δ)) = orderOf u := (Subgroup.orderOf_coe ⟨u, hus⟩).symm
    rw [hor] at hdvd
    exact Odd.of_dvd_nat huo hdvd
  obtain ⟨d', hd', hdψ⟩ := mem_of_normal_odd hn' (U'.map ψ) (D'.map ψ) hNK hnorm hp2
    (ψ ⟨u, hus⟩) ⟨⟨u, hus⟩, hu, rfl⟩ hodd
  have hd'D : (d' : G) ∈ D := hd'
  have hd'U : (d' : G) ∈ U := hDU hd'D
  refine ⟨d', hd'D, (d' : G)⁻¹ * u, ⟨U.mul_mem (U.inv_mem hd'U) hu, ?_⟩, by group⟩
  have h1 : ψ (d'⁻¹ * ⟨u, hus⟩) = 1 := by rw [map_mul, map_inv, hdψ, inv_mul_cancel]
  have := (hker _).mp h1
  simpa using this

end F53

end CFSG.Quasithin
