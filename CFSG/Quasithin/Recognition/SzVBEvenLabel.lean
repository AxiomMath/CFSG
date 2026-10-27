module

public import CFSG.Quasithin.Recognition.SzVBEvenBasic
public import CFSG.Quasithin.Recognition.SzVBEvenType0

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Helpers

omit [Finite G] in
private theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {x y : G} (hx : x * x = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

omit [Finite G] in
private theorem conjSub_zpowers_eq_zpowers_conj (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
private theorem le_normalizer_zpowers_of_commute {P : Subgroup G} {u : G}
    (hP : ∀ x ∈ P, x * u = u * x) :
    P ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
  have hcent : P ≤ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hz : Subgroup.zpowers u ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hP x hx).symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hz hw)
  exact hcent.trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
private theorem relIndex_inf_centralizer_dvd_two {U P : Subgroup G} {u : G}
    (hU : IsElemAbelian 2 U) (hcard : Nat.card ↥U = 4) (hu : u ∈ U) (hu1 : u ≠ 1)
    (hN : P ≤ Subgroup.normalizer (U : Set G)) (hcent : ∀ c ∈ P, c * u = u * c) :
    (P ⊓ Subgroup.centralizer (U : Set G)).relIndex P ∣ 2 := by
  obtain ⟨t, htU, ht1, htu⟩ := exists_klein_ne u hcard
  have huu : u * u = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hU hu
  have hκ : ∀ c ∈ P, c * t * c⁻¹ * t⁻¹ = 1 ∨ c * t * c⁻¹ * t⁻¹ = u := fun c hc =>
    commutator_mem_klein hU hcard hu hu1 (hcent c hc)
      (F7.conjSub_eq_of_mem_normalizer (hN hc)) htU
  have hmem : ∀ c ∈ P, c * t * c⁻¹ * t⁻¹ = 1 → c ∈ Subgroup.centralizer (U : Set G) := by
    intro c hc h1
    have hct : c * t = t * c := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    have hcu : c * u = u * c := hcent c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases klein_cases hU hcard hu hu1 htU ht1 htu ha with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact hcu.symm
    · rw [h]
      exact hct.symm
    · rw [h]
      calc t * u * c = t * (u * c) := mul_assoc _ _ _
        _ = t * (c * u) := by rw [hcu]
        _ = t * c * u := (mul_assoc _ _ _).symm
        _ = c * t * u := by rw [hct]
        _ = c * (t * u) := mul_assoc _ _ _
  rw [Subgroup.relIndex, Subgroup.index_dvd_two_iff]
  by_cases hex : ∃ a ∈ P, a * t * a⁻¹ * t⁻¹ = u
  · obtain ⟨a, haP, ha⟩ := hex
    have ha' : a * t * a⁻¹ = u * t := mul_inv_eq_iff_eq_mul.mp ha
    refine ⟨⟨a, haP⟩, fun b => ?_⟩
    by_cases hb : (b : G) * t * (b : G)⁻¹ * t⁻¹ = 1
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr ⟨b.2, hmem b b.2 hb⟩)
    · left
      have hb' : (b : G) * t * (b : G)⁻¹ = u * t :=
        mul_inv_eq_iff_eq_mul.mp ((hκ b b.2).resolve_left hb)
      have hbu : (b : G) * u * (b : G)⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr (hcent b b.2)
      have key : (b : G) * a * t * ((b : G) * a)⁻¹ * t⁻¹ = 1 := by
        calc (b : G) * a * t * ((b : G) * a)⁻¹ * t⁻¹
            = (b : G) * (a * t * a⁻¹) * (b : G)⁻¹ * t⁻¹ := by group
          _ = (b : G) * (u * t) * (b : G)⁻¹ * t⁻¹ := by rw [ha']
          _ = ((b : G) * u * (b : G)⁻¹) * ((b : G) * t * (b : G)⁻¹) * t⁻¹ := by group
          _ = u * (u * t) * t⁻¹ := by rw [hbu, hb']
          _ = u * u := by group
          _ = 1 := huu
      exact Subgroup.mem_subgroupOf.mpr ⟨P.mul_mem b.2 haP, hmem _ (P.mul_mem b.2 haP) key⟩
  · refine ⟨1, fun b => Or.inr ?_⟩
    have hb := (hκ b b.2).resolve_right fun h => hex ⟨b, b.2, h⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨b.2, hmem b b.2 hb⟩

end Helpers

section Local

variable (hC : GeoCtx G₀ G₁ G₂ T V z)

include hC

omit [Finite G] in
private theorem inf_centralizer_singleton_eq : G₁ ⊓ Subgroup.centralizer ({z} : Set G) = T := by
  have hTG₁ : T ≤ G₁ := hC.hyp.sylow₁.1
  have hTG₂ : T ≤ G₂ := hC.hyp.sylow₂.1
  have hTC : T ≤ G₁ ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine le_inf hTG₁ fun t ht => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hC.klein.z_cent t (hTG₂ ht)
  have hCne : ¬ G₁ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro h
    have hdvd := relIndex_inf_centralizer_dvd_two hC.klein.elemAbelian hC.klein.card_eq
      hC.klein.z_mem hC.klein.z_ne_one hC.hyp.normalizes fun c hc =>
        Subgroup.mem_centralizer_singleton_iff.mp (h hc)
    rw [hC.natS3.index_eq] at hdvd
    exact absurd hdvd (by omega)
  have hmul := Subgroup.relIndex_mul_relIndex T (G₁ ⊓ Subgroup.centralizer ({z} : Set G)) G₁
    hTC inf_le_left
  rw [hC.index3] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hmul) with h1 | h3
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hTC
  · rw [h3] at hmul
    have h1 : (G₁ ⊓ Subgroup.centralizer ({z} : Set G)).relIndex G₁ = 1 := by omega
    exact absurd ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right) hCne

omit [Finite G] in
private theorem eq_of_Zv_eq_adj_γ₀ {y y' : CosetGeom G₀ G₁ G₂}
    (hy : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) y) (hy' : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) y')
    (heq : Zv z y = Zv z y') : y = y' := by
  have hN₂ := le_normalizer_zpowers_of_commute hC.klein.z_cent
  obtain ⟨k, hk1, hk2⟩ := exists_stab_smul_eq
    (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)) hy
  obtain ⟨k', hk1', hk2'⟩ := exists_stab_smul_eq
    (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)) hy'
  have hkA : (k : G) ∈ G₁ := by
    have := mem_stab_of_smul_eq hk1
    rwa [stab_γ₀ hC.hyp.le₁] at this
  have hkA' : (k' : G) ∈ G₁ := by
    have := mem_stab_of_smul_eq hk1'
    rwa [stab_γ₀ hC.hyp.le₁] at this
  rw [← hk2, ← hk2', Zv_smul_γ₁ hN₂, Zv_smul_γ₁ hN₂, conjSub_zpowers_eq_zpowers_conj,
    conjSub_zpowers_eq_zpowers_conj] at heq
  have hzz : z * z = 1 := z_mul_self hC
  have hc2 : ((k' : G) * z * (k' : G)⁻¹) * ((k' : G) * z * (k' : G)⁻¹) = 1 := by
    calc ((k' : G) * z * (k' : G)⁻¹) * ((k' : G) * z * (k' : G)⁻¹)
        = (k' : G) * (z * z) * (k' : G)⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hmem : (k : G) * z * (k : G)⁻¹ ∈ Subgroup.zpowers ((k' : G) * z * (k' : G)⁻¹) :=
    heq ▸ Subgroup.mem_zpowers _
  have hne : (k : G) * z * (k : G)⁻¹ ≠ 1 := by
    intro h1
    apply hC.klein.z_ne_one
    have := congrArg (fun w : G => (k : G)⁻¹ * w * (k : G)) h1
    simpa [mul_assoc] using this
  have hee : (k : G) * z * (k : G)⁻¹ = (k' : G) * z * (k' : G)⁻¹ :=
    (eq_one_or_eq_of_mem_zpowers_of_mul_self hc2 hmem).resolve_left hne
  have hcomm : ((k' : G)⁻¹ * k) * z = z * ((k' : G)⁻¹ * k) := by
    have h1 := congrArg (fun w : G => (k' : G)⁻¹ * w * (k : G)) hee
    have e1 : (k' : G)⁻¹ * ((k : G) * z * (k : G)⁻¹) * (k : G) = (k' : G)⁻¹ * k * z := by group
    have e2 : (k' : G)⁻¹ * ((k' : G) * z * (k' : G)⁻¹) * (k : G) = z * ((k' : G)⁻¹ * k) := by
      group
    rw [e1, e2] at h1
    exact h1
  have hmemC : (k' : G)⁻¹ * k ∈ G₁ ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨G₁.mul_mem (G₁.inv_mem hkA') hkA, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [inf_centralizer_singleton_eq hC] at hmemC
  have hkk : (k'⁻¹ * k : ↥G₀) • γ₁ G₀ G₁ G₂ = γ₁ G₀ G₁ G₂ :=
    smul_γ₁_of_mem hC.hyp.le₂ (hC.hyp.sylow₂.1 hmemC)
  rw [← hk2, ← hk2']
  have h2 := congrArg (fun v => k' • v) hkk
  simp only [mul_smul] at h2
  simpa using h2

omit [Finite G] in
theorem Zv_ne_of_adj {x y y' : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hy : (graph G₀ G₁ G₂).Adj x y) (hy' : (graph G₀ G₁ G₂).Adj x y') (hne : y ≠ y') :
    Zv z y ≠ Zv z y' := by
  intro heq
  have hN₂ := le_normalizer_zpowers_of_commute hC.klein.z_cent
  obtain ⟨a, rfl⟩ := exists_smul_eq_γ₀ hx
  have hy0 : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (a⁻¹ • y) := by
    have := (smul_adj a⁻¹).mpr hy
    rwa [inv_smul_smul] at this
  have hy0' : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (a⁻¹ • y') := by
    have := (smul_adj a⁻¹).mpr hy'
    rwa [inv_smul_smul] at this
  have h1 : Zv z (a⁻¹ • y) = Zv z (a⁻¹ • y') := by
    rw [Zv_smul hN₂, Zv_smul hN₂, heq]
  have h2 := eq_of_Zv_eq_adj_γ₀ hC hy0 hy0' h1
  apply hne
  have := congrArg (fun v => a • v) h2
  simpa using this

theorem Zv_sup_eq {x y y' : CosetGeom G₀ G₁ G₂} (hx : vtype x = false)
    (hy : (graph G₀ G₁ G₂).Adj x y) (hy' : (graph G₀ G₁ G₂).Adj x y') (hne : y ≠ y') :
    Zv z y ⊔ Zv z y' = Vv V x := by
  have hN₂ := le_normalizer_zpowers_of_commute hC.klein.z_cent
  have hvy : vtype y = true := vtype_eq_true_of_adj hy hx
  have hvy' : vtype y' = true := vtype_eq_true_of_adj hy' hx
  have hle : Zv z y ⊔ Zv z y' ≤ Vv V x :=
    sup_le (Zv_le_Vv_of_adj hC.klein.z_mem hC.hyp.normalizes hN₂ hy hx)
      (Zv_le_Vv_of_adj hC.klein.z_mem hC.hyp.normalizes hN₂ hy' hx)
  have hc1 : Nat.card (Zv z y) = 2 := card_Zv hC hvy
  have hc2 : Nat.card (Zv z y') = 2 := card_Zv hC hvy'
  have h4 : Nat.card (Vv V x) = 4 := card_Vv hC hx
  have hne' : Zv z y ≠ Zv z y' := Zv_ne_of_adj hC hx hy hy' hne
  have d1 : 2 ∣ Nat.card ↥(Zv z y ⊔ Zv z y') := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Zv z y ≤ Zv z y ⊔ Zv z y')
    rwa [hc1] at this
  have d2 : Nat.card ↥(Zv z y ⊔ Zv z y') ≤ 4 := (Subgroup.card_le_of_le hle).trans h4.le
  have d3 : 0 < Nat.card ↥(Zv z y ⊔ Zv z y') := Nat.card_pos
  have d4 : Nat.card ↥(Zv z y ⊔ Zv z y') ≠ 2 := by
    intro h2
    apply hne'
    have e1 : Zv z y = Zv z y ⊔ Zv z y' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (h2.trans hc1.symm).le
    have e2 : Zv z y' = Zv z y ⊔ Zv z y' :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (h2.trans hc2.symm).le
    exact e1.trans e2.symm
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

end Local

end CFSG.Quasithin.SzVB
