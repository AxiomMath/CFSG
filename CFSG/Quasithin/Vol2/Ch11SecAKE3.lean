module

public import CFSG.Quasithin.Vol2.Ch11SecAKE2
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.QuasithinUnique

namespace C10KH

theorem mem_normalizer_of_conj_le {G : Type} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]))

variable {Q : Type} [Group Q] {S U : Subgroup Q}

theorem mem_normalizer_of_inner [Finite Q] (hS : S.Normal)
    (hinn : ∀ u : Q, ∃ s ∈ S, ∀ x ∈ S, u * x * u⁻¹ = s * x * s⁻¹)
    (hZ : ∀ z ∈ S, (∀ x ∈ S, z * x = x * z) → z = 1) (hU : IsSylowTwoOf U ⊤) {n : Q}
    (hn : n ∈ S) (hnU : ∀ y ∈ U, y ∈ S → n * y * n⁻¹ ∈ U) :
    n ∈ Subgroup.normalizer (U : Set Q) := by
  have hU0 : IsSylowTwoOf (U ⊓ S) S := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hU le_top
    (Subgroup.normalizer_eq_top_iff.mpr hS).ge
  refine mem_normalizer_of_conj_le fun u hu => ?_
  obtain ⟨s, hs, hsx⟩ := hinn u
  have hcx : ∀ x ∈ S, s⁻¹ * u * x = x * (s⁻¹ * u) := by
    intro x hx
    calc s⁻¹ * u * x = s⁻¹ * (u * x * u⁻¹) * u := by group
      _ = s⁻¹ * (s * x * s⁻¹) * u := by rw [hsx x hx]
      _ = x * (s⁻¹ * u) := by group
  obtain ⟨k, hk⟩ := hU.2.1 ⟨u, hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute s (s⁻¹ * u) := (hcx s hs).symm
  have hsk : s ^ 2 ^ k = 1 := by
    have h1 : u = s * (s⁻¹ * u) := by group
    have h2 : s ^ 2 ^ k * (s⁻¹ * u) ^ 2 ^ k = 1 := by rw [← hcomm.mul_pow, ← h1, hk']
    refine hZ _ (pow_mem hs _) fun x hx => ?_
    rw [eq_inv_of_mul_eq_one_left h2]
    exact ((Commute.pow_left (hcx x hx) _).inv_left : _)
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  have hsN : Subgroup.zpowers s ≤ Subgroup.normalizer ((U ⊓ S : Subgroup Q) : Set Q) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_le fun y hy => ?_
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨?_, hS.conj_mem y hy.2 s⟩
    rw [← hsx y hy.2]
    exact U.mul_mem (U.mul_mem hu hy.1) (U.inv_mem hu)
  have hX := hU0.eq_of_le (le_sup_right : U ⊓ S ≤ Subgroup.zpowers s ⊔ (U ⊓ S))
    (sup_le (Subgroup.zpowers_le.mpr hs) inf_le_right) (hs2.to_sup_of_normal_right' hU0.2.1 hsN)
  have hsU : s ∈ U := by
    have h : s ∈ Subgroup.zpowers s ⊔ (U ⊓ S) := Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
    rw [hX] at h
    exact h.1
  have hcn : s⁻¹ * u * n⁻¹ = n⁻¹ * (s⁻¹ * u) := hcx n⁻¹ (inv_mem hn)
  have h1 : n * u * n⁻¹ = n * s * n⁻¹ * (s⁻¹ * u) := by
    calc n * u * n⁻¹ = n * s * (s⁻¹ * u * n⁻¹) := by group
      _ = n * s * (n⁻¹ * (s⁻¹ * u)) := by rw [hcn]
      _ = n * s * n⁻¹ * (s⁻¹ * u) := by group
  rw [h1]
  exact mul_mem (hnU s hsU hs) (mul_mem (inv_mem hsU) hu)

open CFSG.Quasithin.E2P.SporB CFSG.Sporadic.J1


theorem exists_inner_of_j1
    [S.Normal] (e : ↥S ≃* ↥J)
    (u : Q) : ∃ s ∈ S, ∀ x ∈ S, u * x * u⁻¹ = s * x * s⁻¹ := by
  obtain ⟨g, hg⟩ := j1_inner (e.symm.trans ((MulAut.conjNormal u).trans e))
  refine ⟨(e.symm g : Q), (e.symm g).2, fun x hx => ?_⟩
  have h := congrArg (fun φ : MulAut ↥J => e.symm (φ (e ⟨x, hx⟩))) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul,
    map_inv] at h
  have h2 := congrArg Subtype.val h
  rw [MulAut.conjNormal_apply] at h2
  simpa using h2

theorem center_of_j1 (e : ↥S ≃* ↥J) :
    ∀ z ∈ S, (∀ x ∈ S, z * x = x * z) → z = 1 := by
  intro z hz hzx
  have hw : e ⟨z, hz⟩ ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hzx x hx).symm)
  rw [j1_center_eq_bot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hw
  exact congrArg Subtype.val hw

end C10KH

open CFSG.Quasithin.E2P.SporB CFSG.Sporadic.J1 C10KH


theorem factJ1_holds : FactJ1 := by
  intro Q _ _ S U B hS hJ hU hBS hB1 hBB _
  obtain ⟨e₀⟩ := hJ
  let e : ↥S ≃* ↥J := e₀.trans nativeEquiv
  have hU0 : IsSylowTwoOf (U ⊓ S) S := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hU le_top
    (Subgroup.normalizer_eq_top_iff.mpr hS).ge
  have hT : IsSylowTwoOf (U.subgroupOf S) ⊤ := by
    rw [← Subgroup.inf_subgroupOf_right]
    refine ⟨le_top, hU0.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU0.1).symm, ?_⟩
    have h := Subgroup.relIndex_top_right ((U ⊓ S).subgroupOf S)
    rw [Subgroup.relIndex] at h
    rw [h]
    exact hU0.2.2
  have hBmap : (B.subgroupOf S).map S.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hBS
  have hB' : ⁅B.subgroupOf S, B.subgroupOf S⁆ = B.subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, hBmap, hBB]
  have hB'1 : B.subgroupOf S ≠ ⊥ := by
    intro h
    apply hB1
    rw [← hBmap, h, Subgroup.map_bot]
  have htop := j1_sup_normalizer_eq_top e hT hB' hB'1
  have hS' : S = (B.subgroupOf S ⊔ Subgroup.normalizer (U.subgroupOf S : Set ↥S)).map
      S.subtype := by
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hS', Subgroup.map_sup, hBmap]
  refine sup_le_sup_left ?_ B
  rintro _ ⟨n, hn, rfl⟩
  refine mem_normalizer_of_inner hS (exists_inner_of_j1 e) (center_of_j1 e) hU n.2
    fun y hy hyS => ?_
  have h := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hyS⟩).mp (by
    rw [Subgroup.mem_subgroupOf]
    exact hy)
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

end CFSG.Quasithin.Vol2.Ch11.SecA
