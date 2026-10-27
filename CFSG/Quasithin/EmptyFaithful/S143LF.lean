module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.S143

section DihEquiv

variable {D : Type*} [Group D]

@[expose] def dihMap (c w : D) : DihedralGroup 4 → D
  | .r i => c ^ i.val
  | .sr i => w * c ^ i.val

variable {c w : D}

theorem dihPow_val_add (hc4 : c ^ 4 = 1) (i j : ZMod 4) :
    c ^ (i + j).val = c ^ i.val * c ^ j.val := by
  rw [ZMod.val_add, ← pow_add]
  have h : ∀ n : ℕ, c ^ (n % 4) = c ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, hc4, one_pow, one_mul]
  exact h _

theorem dihPow_val_sub (hc4 : c ^ 4 = 1) (i j : ZMod 4) :
    c ^ (j - i).val = (c ^ i.val)⁻¹ * c ^ j.val := by
  have h := dihPow_val_add hc4 (j - i) i
  rw [sub_add_cancel] at h
  rw [h, (Commute.pow_pow_self c (j - i).val i.val).eq]
  group

theorem dihPow_comm_w (hw2 : w * w = 1) (hw : w * c * w⁻¹ = c⁻¹) (k : ℕ) :
    c ^ k * w = w * (c ^ k)⁻¹ := by
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h1 : w * c ^ k * w⁻¹ = (c ^ k)⁻¹ := by
    have := conj_zpow (a := w) (b := c) (i := (k : ℤ))
    rw [hw] at this
    simpa using this.symm
  rw [hww] at h1
  calc c ^ k * w = (w * w) * c ^ k * w := by rw [hw2, one_mul]
    _ = w * (w * c ^ k * w) := by group
    _ = w * (c ^ k)⁻¹ := by rw [h1]

theorem dihMap_mul (hc4 : c ^ 4 = 1) (hw2 : w * w = 1) (hw : w * c * w⁻¹ = c⁻¹)
    (x y : DihedralGroup 4) : dihMap c w (x * y) = dihMap c w x * dihMap c w y := by
  cases x with
  | r i =>
    cases y with
    | r j =>
      show c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact dihPow_val_add hc4 i j
    | sr j =>
      show w * c ^ (j - i).val = c ^ i.val * (w * c ^ j.val)
      calc w * c ^ (j - i).val = w * ((c ^ i.val)⁻¹ * c ^ j.val) := by rw [dihPow_val_sub hc4]
        _ = (w * (c ^ i.val)⁻¹) * c ^ j.val := by rw [mul_assoc]
        _ = (c ^ i.val * w) * c ^ j.val := by rw [dihPow_comm_w hw2 hw]
        _ = c ^ i.val * (w * c ^ j.val) := by rw [mul_assoc]
  | sr i =>
    cases y with
    | r j =>
      show w * c ^ (i + j).val = w * c ^ i.val * c ^ j.val
      rw [dihPow_val_add hc4, mul_assoc]
    | sr j =>
      show c ^ (j - i).val = w * c ^ i.val * (w * c ^ j.val)
      calc c ^ (j - i).val = (c ^ i.val)⁻¹ * c ^ j.val := dihPow_val_sub hc4 i j
        _ = (w * w) * (c ^ i.val)⁻¹ * c ^ j.val := by rw [hw2, one_mul]
        _ = w * (w * (c ^ i.val)⁻¹) * c ^ j.val := by rw [mul_assoc w w]
        _ = w * (c ^ i.val * w) * c ^ j.val := by rw [dihPow_comm_w hw2 hw]
        _ = w * c ^ i.val * (w * c ^ j.val) := by group

theorem exists_mulEquiv_dihedral_of_inverting [Finite D] (c w : D) (hc4 : c ^ 4 = 1)
    (hc2 : c ^ 2 ≠ 1) (hw2 : w * w = 1) (hw : w * c * w⁻¹ = c⁻¹)
    (hwC : w ∉ Subgroup.zpowers c) (hcard : Nat.card D = 8) :
    Nonempty (D ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c) (by simpa using hc2) (by simpa using hc4)
    simpa using h
  let f : DihedralGroup 4 →* D := MonoidHom.mk' (dihMap c w) (dihMap_mul hc4 hw2 hw)
  have hf : ∀ x, f x = dihMap c w x := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf] at hx
    cases x with
    | r i =>
      have h1 : c ^ i.val = 1 := hx
      have h2 : 4 ∣ i.val := by
        have := orderOf_dvd_of_pow_eq_one h1
        rwa [hord] at this
      have h3 : i.val < 4 := ZMod.val_lt i
      have h4 : i.val = 0 := by omega
      have h5 : i = 0 := (ZMod.val_eq_zero i).mp h4
      rw [h5, DihedralGroup.r_zero]
    | sr i =>
      exfalso
      apply hwC
      have h1 : w * c ^ i.val = 1 := hx
      have : w = (c ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, DihedralGroup.nat_card])
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

section Klein

variable [Finite D]

theorem kleinSubgroup_cases {K : Subgroup D} (hK : Nat.card K = 4) {a b : D} (ha : a ∈ K) (hb : b ∈ K)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1) :
    ∀ x ∈ K, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hxa, hxb, hxab⟩ := hcon
  have hnd : [1, a, b, a * b, x].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ha1.symm, hb1.symm, hab1.symm, hx1.symm⟩, ⟨hab, ?_, hxa.symm⟩,
      ⟨?_, hxb.symm⟩, ⟨hxab.symm, not_false, List.nodup_nil⟩⟩
    · intro h; exact hb1 (by simpa using h)
    · intro h; exact ha1 (by simpa using h)
  have hS : ([1, a, b, a * b, x].toFinset).card = 5 := by
    rw [List.toFinset_card_of_nodup hnd]; rfl
  have hsub : (([1, a, b, a * b, x].toFinset : Finset D) : Set D) ⊆ (K : Set D) := by
    intro y hy
    simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact K.one_mem
    · exact ha
    · exact hb
    · exact K.mul_mem ha hb
    · exact hx
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (K : Set D).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hK
  rw [Set.ncard_coe_finset, hS, h2] at h1
  omega

end Klein
section NonComm

variable [Finite D]

theorem mulEquiv_dihedral_of_noncomm {z : D} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ x : D, x * z = z * x) (D₀ : Subgroup D) [D₀.Normal] (hzD₀ : z ∈ D₀)
    (hsq : ∀ x ∈ D₀, x * x = 1) (hcomm : ∀ x ∈ D₀, ∀ y ∈ D₀, x * y = y * x)
    (hc4 : Nat.card D₀ = 4) (hD8 : Nat.card D = 8)
    {d δ : D} (hδ : δ ∈ D₀) (hnc : d * δ * d⁻¹ ≠ δ) : Nonempty (D ≃* DihedralGroup 4) := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzconj : ∀ x : D, x * z * x⁻¹ = z := fun x => by rw [hzc x]; group
  have hδ1 : δ ≠ 1 := fun h => hnc (by rw [h]; group)
  have hδz : δ ≠ z := fun h => hnc (by rw [h, hzconj])
  have hδδ : δ * δ = 1 := hsq δ hδ
  have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδδ
  have hzδ1 : z * δ ≠ 1 := fun h => hδz (by
    have := eq_inv_of_mul_eq_one_right h
    rw [hz] at this; exact this)
  have hcases := kleinSubgroup_cases hc4 hzD₀ hδ hz1 hδ1 (Ne.symm hδz) hzδ1
  have he : d * δ * d⁻¹ = z * δ := by
    have hmem : d * δ * d⁻¹ ∈ D₀ := Subgroup.Normal.conj_mem inferInstance δ hδ d
    rcases hcases _ hmem with h | h | h | h
    · exact absurd (by simpa using h) hδ1
    · exfalso
      apply hδz
      have : δ = d⁻¹ * z * d := by rw [← h]; group
      rw [this, show d⁻¹ * z * d = z from by
        have := hzconj d⁻¹; simpa using this]
    · exact absurd h hnc
    · exact h
  have hdz : d * δ = z * δ * d := by
    calc d * δ = (d * δ * d⁻¹) * d := by group
      _ = z * δ * d := by rw [he]
  have hdD₀ : d ∉ D₀ := fun hd => hnc (by
    have := hcomm d hd δ hδ
    calc d * δ * d⁻¹ = (δ * d) * d⁻¹ := by rw [this]
      _ = δ := by group)
  have hidx : D₀.index = 2 := by
    have h := Subgroup.card_mul_index D₀
    rw [hc4, hD8] at h
    omega
  have hd2mem : d * d ∈ D₀ := by
    have := Subgroup.pow_index_mem D₀ d
    rwa [hidx, pow_two] at this
  have hdd : d * d = 1 ∨ d * d = z := by
    rcases hcases _ hd2mem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hnc
      calc d * δ * d⁻¹ = d * (d * d) * d⁻¹ := by rw [h]
        _ = d * d := by group
        _ = δ := h
    · exfalso
      have h1 : d * (z * δ) * d⁻¹ = z * δ := by
        calc d * (z * δ) * d⁻¹ = d * (d * d) * d⁻¹ := by rw [h]
          _ = d * d := by group
          _ = z * δ := h
      have h2 : d * (z * δ) * d⁻¹ = δ := by
        calc d * (z * δ) * d⁻¹ = (d * z * d⁻¹) * (d * δ * d⁻¹) := by group
          _ = z * (z * δ) := by rw [hzconj, he]
          _ = δ := by rw [← mul_assoc, hz2, one_mul]
      apply hz1
      have := h1.symm.trans h2
      simpa using this
  obtain ⟨w, hw2, hwδ, hwD₀⟩ : ∃ w : D, w * w = 1 ∧ w * δ * w⁻¹ = z * δ ∧ w ∉ D₀ := by
    rcases hdd with h | h
    · exact ⟨d, h, he, hdD₀⟩
    · refine ⟨d * δ, ?_, ?_, ?_⟩
      · calc d * δ * (d * δ) = (z * δ * d) * (d * δ) := by rw [hdz]
          _ = z * δ * (d * d) * δ := by group
          _ = z * δ * z * δ := by rw [h]
          _ = (z * z) * (δ * δ) := by
            calc z * δ * z * δ = z * (δ * z) * δ := by group
              _ = z * (z * δ) * δ := by rw [← hzc δ]
              _ = (z * z) * (δ * δ) := by group
          _ = 1 := by rw [hz2, hδδ, one_mul]
      · calc d * δ * δ * (d * δ)⁻¹ = (d * δ * d⁻¹) * (δ * δ⁻¹) := by group
          _ = z * δ := by rw [he]; group
      · intro hmem
        apply hdD₀
        have := D₀.mul_mem hmem (D₀.inv_mem hδ)
        simpa using this
  have hw1 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwδ' : w * δ * w = z * δ := by rw [hw1] at hwδ; exact hwδ
  obtain ⟨c, hc⟩ : ∃ c : D, c = w * δ := ⟨_, rfl⟩
  have hcc : c * c = z := by
    calc c * c = (w * δ * w) * δ := by rw [hc]; group
      _ = z * (δ * δ) := by rw [hwδ']; group
      _ = z := by rw [hδδ, mul_one]
  have hc2 : c ^ 2 ≠ 1 := by rw [pow_two, hcc]; exact hz1
  have hc4' : c ^ 4 = 1 := by
    calc c ^ 4 = (c * c) * (c * c) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [hcc, hz2]
  have hwc : w * c * w⁻¹ = c⁻¹ := by
    have hcinv : c⁻¹ = δ * w := by
      rw [hc, mul_inv_rev, hδinv, hw1]
    rw [hcinv, hw1, hc]
    calc w * (w * δ) * w = (w * w) * δ * w := by group
      _ = δ * w := by rw [hw2, one_mul]
  have hwC : w ∉ Subgroup.zpowers c := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm' : w * c = c * w := by rw [← hk]; exact (Commute.zpow_self c k).eq
    apply hc2
    have h1 : c = c⁻¹ := by
      calc c = (w * c) * w⁻¹ := by rw [hcomm']; group
        _ = c⁻¹ := hwc
    calc c ^ 2 = c * c := pow_two c
      _ = c * c⁻¹ := by rw [← h1]
      _ = 1 := by group
  exact exists_mulEquiv_dihedral_of_inverting c w hc4' hc2 hw2 hwc hwC hD8

end NonComm

section Small

variable [Finite D]

theorem orderOf_r_two : orderOf (DihedralGroup.r 2 : DihedralGroup 4) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [pow_two, DihedralGroup.r_mul_r]; decide
  · intro h
    have h' : (DihedralGroup.r 2 : DihedralGroup 4) = DihedralGroup.r 0 := h
    injection h' with h2
    revert h2; decide

omit [Finite D] in
theorem exists_embedding_dihedral_of_card_two (h : Nat.card D = 2) :
    ∃ X : Subgroup (DihedralGroup 4), Nonempty (D ≃* X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : Nat.card D = 2 := h
  have hcyc : IsCyclic D := isCyclic_of_prime_card hD
  refine ⟨Subgroup.zpowers (DihedralGroup.r 2), ?_⟩
  have hX : Nat.card (Subgroup.zpowers (DihedralGroup.r 2 : DihedralGroup 4)) = 2 := by
    rw [Nat.card_zpowers, orderOf_r_two]
  exact ⟨mulEquivOfCyclicCardEq (by rw [hD, hX])⟩


@[expose] def kleinDihFun : DihedralGroup 2 → DihedralGroup 4
  | .r i => .r (2 * (i.val : ZMod 4))
  | .sr i => .sr (2 * (i.val : ZMod 4))

theorem kleinDihFun_mul : ∀ x y : DihedralGroup 2, kleinDihFun (x * y) = kleinDihFun x * kleinDihFun y := by
  decide

theorem kleinDihFun_inj : Function.Injective kleinDihFun := by
  intro x y
  revert x y
  decide

theorem exists_embedding_dihedral_of_card_four (h : Nat.card D = 4) :
    ∃ X : Subgroup (DihedralGroup 4), Nonempty (D ≃* X) := by
  by_cases hcyc : ∃ g : D, orderOf g = 4
  · obtain ⟨g, hg⟩ := hcyc
    have hC : IsCyclic D := isCyclic_of_orderOf_eq_card g (by rw [hg, h])
    refine ⟨Subgroup.zpowers (DihedralGroup.r 1), ⟨mulEquivOfCyclicCardEq ?_⟩⟩
    rw [h, Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  · push Not at hcyc
    have hord : ∀ g : D, g ≠ 1 → orderOf g = 2 := by
      intro g hg1
      have h4 : orderOf g ∣ 4 := h ▸ orderOf_dvd_natCard g
      have h4' : orderOf g ≠ 4 := hcyc g
      have h1 : orderOf g ≠ 1 := fun h' => hg1 (orderOf_eq_one_iff.mp h')
      have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) h4
      have hpos : 0 < orderOf g := orderOf_pos g
      generalize orderOf g = m at *
      interval_cases m <;> simp_all
    have hnt : Nontrivial D := by
      have := Fintype.ofFinite D
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, h]
      norm_num
    have hexp : Monoid.exponent D = 2 :=
      (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr hord
    have : IsKleinFour D := ⟨h, hexp⟩
    obtain ⟨e⟩ : Nonempty (D ≃* DihedralGroup 2) := IsKleinFour.nonempty_mulEquiv
    let ι : DihedralGroup 2 →* DihedralGroup 4 := MonoidHom.mk' kleinDihFun kleinDihFun_mul
    exact ⟨ι.range, ⟨e.trans (MonoidHom.ofInjective (f := ι) kleinDihFun_inj)⟩⟩

end Small

section Classify

variable [Finite D]

theorem exists_embedding_dihedral_of_structure {z : D} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ x : D, x * z = z * x) (D₀ : Subgroup D) [D₀.Normal] (hzD₀ : z ∈ D₀)
    (hsq : ∀ x ∈ D₀, x * x = 1) (hcomm : ∀ x ∈ D₀, ∀ y ∈ D₀, x * y = y * x)
    (hc : Nat.card D₀ ≤ 4) (hidx : D₀.index ≤ 2)
    (hnc : Nat.card D₀ = 4 → D₀.index = 2 → ∃ d δ : D, δ ∈ D₀ ∧ d * δ * d⁻¹ ≠ δ) :
    (∃ X : Subgroup (DihedralGroup 4), Nonempty (D ≃* X)) ∧
      (Nat.card D = 8 → Nonempty (D ≃* DihedralGroup 4)) := by
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hord : orderOf z = 2 := orderOf_eq_prime hz2' hz1
  have hdvd : 2 ∣ Nat.card D₀ := by
    have := orderOf_dvd_natCard (⟨z, hzD₀⟩ : D₀)
    rwa [Subgroup.orderOf_mk, hord] at this
  have hpos : 0 < Nat.card D₀ := Nat.card_pos
  have hc' : Nat.card D₀ = 2 ∨ Nat.card D₀ = 4 := by
    generalize Nat.card D₀ = m at *
    obtain ⟨k, rfl⟩ := hdvd
    omega
  have hipos : 0 < D₀.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hmul := Subgroup.card_mul_index D₀
  rcases hc' with h2 | h4
  · rcases (by omega : D₀.index = 1 ∨ D₀.index = 2) with i1 | i2
    · have hD : Nat.card D = 2 := by rw [← hmul, h2, i1]
      exact ⟨exists_embedding_dihedral_of_card_two hD, fun h => by omega⟩
    · have hD : Nat.card D = 4 := by rw [← hmul, h2, i2]
      exact ⟨exists_embedding_dihedral_of_card_four hD, fun h => by omega⟩
  · rcases (by omega : D₀.index = 1 ∨ D₀.index = 2) with i1 | i2
    · have hD : Nat.card D = 4 := by rw [← hmul, h4, i1]
      exact ⟨exists_embedding_dihedral_of_card_four hD, fun h => by omega⟩
    · have hD : Nat.card D = 8 := by rw [← hmul, h4, i2]
      obtain ⟨d, δ, hδ, hne⟩ := hnc h4 i2
      have e : Nonempty (D ≃* DihedralGroup 4) :=
        mulEquiv_dihedral_of_noncomm hz2 hz1 hzc D₀ hzD₀ hsq hcomm h4 hD hδ hne
      obtain ⟨e⟩ := e
      exact ⟨⟨⊤, ⟨e.trans (Subgroup.topEquiv).symm⟩⟩, fun _ => ⟨e⟩⟩

end Classify

end DihEquiv


end CFSG.Quasithin.S143
