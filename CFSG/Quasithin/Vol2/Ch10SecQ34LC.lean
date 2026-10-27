module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LB
public import CFSG.Quasithin.Vol2.Ch10SecQ34LA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

variable {G : Type*} [Group G]

noncomputable def conjAutHom (V : Subgroup G) :
    ↥(Subgroup.normalizer (V : Set G)) →* MulAut ↥V where
  toFun a := conjAutOf a.2
  map_one' := by
    ext v
    rw [conjAutOf_apply]
    simp
  map_mul' a b := by
    ext v
    rw [MulAut.mul_apply, conjAutOf_apply, conjAutOf_apply, conjAutOf_apply]
    simp [mul_assoc]

theorem conjAutHom_apply (V : Subgroup G) (a : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAutHom V a v : ↥V) : G) = (a : G) * v * (a : G)⁻¹ := conjAutOf_apply a.2 v

theorem card_mulAut_dvd_six {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 4) :
    Nat.card (MulAut V) ∣ 6 := by
  classical
  have := Fintype.ofFinite V
  let res : MulAut V →* Equiv.Perm {v : V // v ≠ 1} :=
    { toFun := fun σ => σ.toEquiv.subtypeEquiv fun v => by
        simp only [ne_eq, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.map_eq_one_iff]
      map_one' := by ext; rfl
      map_mul' := fun σ τ => by ext; rfl }
  have hinj : Function.Injective res := by
    intro σ τ h
    ext v
    by_cases hv : v = 1
    · rw [hv, map_one, map_one]
    · have := congrArg (fun f : Equiv.Perm {v : V // v ≠ 1} => (f ⟨v, hv⟩ : V)) h
      exact this
  have hcard : Nat.card (Equiv.Perm {v : V // v ≠ 1}) = 6 := by
    rw [Nat.card_perm]
    have : Nat.card {v : V // v ≠ 1} = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, hV]
    rw [this]
    rfl
  rw [← hcard]
  exact Subgroup.card_dvd_of_injective res hinj

theorem card_normalizer_dvd [Finite G] {V : Subgroup G} (hV : Nat.card V = 4)
    (hC : Subgroup.centralizer (V : Set G) = V) :
    Nat.card (Subgroup.normalizer (V : Set G)) ∣ 24 := by
  set φ := conjAutHom V with hφ
  have hker : φ.ker = V.subgroupOf (Subgroup.normalizer (V : Set G)) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine hC.le (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
      have h1 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) h
      simp only [hφ, conjAutHom_apply, MulAut.one_apply] at h1
      calc v * (a : G) = (a : G) * v * (a : G)⁻¹ * a := by rw [h1]
        _ = a * v := by group
    · intro ha
      ext v
      rw [hφ, conjAutHom_apply, MulAut.one_apply]
      have hac : (a : G) ∈ Subgroup.centralizer (V : Set G) := hC.ge ha
      have h1 := Subgroup.mem_centralizer_iff.mp hac v v.2
      rw [← h1]
      group
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hV] at h1
  have h2 : Nat.card φ.range ∣ 6 :=
    (Subgroup.card_subgroup_dvd_card _).trans (card_mulAut_dvd_six hV)
  rw [← h1]
  exact Nat.mul_dvd_mul_left 4 h2

theorem mem_of_odd_of_le_normalizer [Finite G] {V Y : Subgroup G}
    (hN : Nat.card (Subgroup.normalizer (V : Set G)) ∣ 24)
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) (hY : Nat.card Y = 12) {a : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hodd : Odd (orderOf a)) : a ∈ Y := by
  set Y' := Y.subgroupOf (Subgroup.normalizer (V : Set G)) with hY'
  have hcardY' : Nat.card Y' = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv, hY]
  have h1 := Subgroup.card_mul_index Y'
  rw [hcardY'] at h1
  have hidx : Y'.index = 1 ∨ Y'.index = 2 := by
    rw [← h1] at hN
    obtain ⟨k, hk⟩ := hN
    have hk' : Y'.index * k = 2 := by nlinarith
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk'
      exact absurd hk' (by norm_num)
    · have hle : Y'.index ≤ 2 := by nlinarith
      interval_cases h : Y'.index
      · simp at hk'
      · exact Or.inl rfl
      · exact Or.inr rfl
  rcases hidx with h | h
  · have htop := Subgroup.index_eq_one.mp h
    have hmem : (⟨a, ha⟩ : ↥(Subgroup.normalizer (V : Set G))) ∈ Y' := htop ▸ Subgroup.mem_top _
    exact hmem
  · have hmem := odd_mem_of_index_two h (x := ⟨a, ha⟩) (by rw [Subgroup.orderOf_mk]; exact hodd)
    exact hmem

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
