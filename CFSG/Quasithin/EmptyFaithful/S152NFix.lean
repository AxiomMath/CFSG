module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152N

theorem normalizes_of_normalizes {H T Z A : Subgroup G}
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y ≤ H → Y = T ∨ Y = H) (hTH : T ≤ H)
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) (hAH : A ≤ H)
    (hAT : ¬ A ≤ T) (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) :
    H ≤ Subgroup.normalizer (Z : Set G) := by
  have hTY : T ≤ H ⊓ Subgroup.normalizer (Z : Set G) := le_inf hTH hTZ
  rcases hmax _ hTY inf_le_left with h | h
  · exact absurd (fun x hx => by
      have : x ∈ H ⊓ Subgroup.normalizer (Z : Set G) := ⟨hAH hx, hAZ hx⟩
      rw [h] at this
      exact this) hAT
  · intro x hx
    have : x ∈ H ⊓ Subgroup.normalizer (Z : Set G) := by rw [h]; exact hx
    exact this.2

variable [Finite G]

theorem relIndex_le_of_centralizer_eq {H T Z : Subgroup G} {z₀ : G} (hz₀Z : z₀ ∈ Z) (hz₀ : z₀ ≠ 1)
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hC : H ⊓ Subgroup.centralizer ({z₀} : Set G) = T) :
    T.relIndex H ≤ Nat.card Z - 1 := by
  let S : Set G := (Z : Set G) \ {1}
  have hS : Nat.card S = Nat.card Z - 1 := by
    have h1 : ((Z : Set G) \ {1}).ncard = (Z : Set G).ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem (one_mem Z)
    rw [Nat.card_coe_set_eq, h1, ← Nat.card_coe_set_eq]
    rfl
  have hmem : ∀ h : ↥H, (h : G) * z₀ * (h : G)⁻¹ ∈ S := fun h => by
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHZ h.2) z₀).mp hz₀Z, fun h1 => hz₀ ?_⟩
    have h2 : (h : G) * z₀ * (h : G)⁻¹ = 1 := h1
    have h3 : z₀ = (h : G)⁻¹ * ((h : G) * z₀ * (h : G)⁻¹) * (h : G) := by group
    rw [h2] at h3
    simpa using h3
  let f : ↥H ⧸ T.subgroupOf H → S := Quotient.lift
    (fun h : ↥H => ⟨(h : G) * z₀ * (h : G)⁻¹, hmem h⟩)
    (by
      intro a b hab
      have h1 : a⁻¹ * b ∈ T.subgroupOf H := QuotientGroup.leftRel_apply.mp hab
      have h2 : ((a⁻¹ * b : ↥H) : G) ∈ T := h1
      have h3 : ((a⁻¹ * b : ↥H) : G) ∈ H ⊓ Subgroup.centralizer ({z₀} : Set G) := by
        rw [hC]; exact h2
      have h4 := Subgroup.mem_centralizer_iff.mp h3.2 z₀ (Set.mem_singleton _)
      apply Subtype.ext
      show (a : G) * z₀ * (a : G)⁻¹ = (b : G) * z₀ * (b : G)⁻¹
      have h5 : (a : G)⁻¹ * (b : G) * z₀ = z₀ * ((a : G)⁻¹ * (b : G)) := h4.symm
      have h6 : (b : G) * z₀ * (b : G)⁻¹ = (a : G) * (((a : G)⁻¹ * (b : G)) * z₀ *
          ((a : G)⁻¹ * (b : G))⁻¹) * (a : G)⁻¹ := by group
      rw [h6, h5]
      group)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
    have h1 : (a : G) * z₀ * (a : G)⁻¹ = (b : G) * z₀ * (b : G)⁻¹ := congrArg Subtype.val hxy
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    show ((a⁻¹ * b : ↥H) : G) ∈ T
    rw [← hC]
    refine ⟨(a⁻¹ * b).2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h2 : (a : G)⁻¹ * (b : G) * x * ((a : G)⁻¹ * (b : G))⁻¹ = x := by
      have h3 : (a : G)⁻¹ * (b : G) * x * ((a : G)⁻¹ * (b : G))⁻¹ =
          (a : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (a : G) := by group
      rw [h3, ← h1]; group
    have := congrArg (fun t => t * ((a : G)⁻¹ * (b : G))) h2
    simpa [mul_assoc] using this.symm
  have := Nat.card_le_card_of_injective f hf
  rw [hS] at this
  exact this

theorem exists_ne_one_mem_center {T Z : Subgroup G} (hT2 : IsPGroup 2 T) (hZT : Z ≤ T)
    (hZ1 : Z ≠ ⊥) (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ t ∈ T, t * z = z * t := by
  have hTnil : Group.IsNilpotent T := hT2.isNilpotent
  have hWn : (Z.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZT).mpr hTZ
  have hWT' : Z.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hZ1
    rw [← Subgroup.map_subgroupOf_eq_of_le hZT, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hWT')
  refine ⟨(w : G), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1,
    fun h => hw1 (Subtype.ext (Subtype.ext h)), fun t ht => ?_⟩
  have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨t, ht⟩
  simpa using congrArg Subtype.val this

theorem centralizes_of_odd {H T Z : Subgroup G} (hT2 : IsPGroup 2 T)
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y ≤ H → Y = T ∨ Y = H) (hTH : T ≤ H)
    (hidx : T.relIndex H = 9)
    (hZT : Z ≤ T) (hZ2 : ∀ a ∈ Z, a ^ 2 = 1)
    (hZ4 : Nat.card Z = 4)
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) :
    ∀ x ∈ H, Odd (orderOf x) → x ∈ Subgroup.centralizer (Z : Set G) := by
  intro x hx hxodd
  have hZ1 : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ4
    omega
  obtain ⟨z₀, hz₀Z, hz₀1, hz₀T⟩ := exists_ne_one_mem_center hT2 hZT hZ1 hTZ
  have hH0 : H ≤ Subgroup.centralizer ({z₀} : Set G) := by
    have hTC : T ≤ H ⊓ Subgroup.centralizer ({z₀} : Set G) := by
      refine le_inf hTH (fun t ht => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hz₀T t ht).symm
    rcases hmax _ hTC inf_le_left with h | h
    · exfalso
      have := relIndex_le_of_centralizer_eq hz₀Z hz₀1 hHZ h
      omega
    · intro y hy
      have : y ∈ H ⊓ Subgroup.centralizer ({z₀} : Set G) := by rw [h]; exact hy
      exact this.2
  have hz₀x : x * z₀ = z₀ * x :=
    (Subgroup.mem_centralizer_iff.mp (hH0 hx) z₀ (Set.mem_singleton _)).symm
  have hz₀2 : z₀ ^ 2 = 1 := hZ2 z₀ hz₀Z
  have hZn : (Z : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hZ4
  obtain ⟨a, haZ, ha⟩ : ∃ a ∈ (Z : Set G), a ∉ ({1, z₀} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Z : Set G) ⊆ {1, z₀} := hcon
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z₀} : Set G).ncard = 2 := Set.ncard_pair (Ne.symm hz₀1)
    omega
  have ha1 : a ≠ 1 := fun h => ha (Or.inl h)
  have haz : a ≠ z₀ := fun h => ha (Or.inr h)
  have haZ' : a ∈ Z := haZ
  have haz₀Z : a * z₀ ∈ Z := Z.mul_mem haZ' hz₀Z
  have hinv : z₀⁻¹ = z₀ := by
    have : z₀ * z₀ = 1 := by simpa [pow_two] using hz₀2
    exact inv_eq_of_mul_eq_one_right this
  have hd1 : a * z₀ ≠ 1 := fun h => haz (by
    have := eq_inv_of_mul_eq_one_left h
    rw [hinv] at this; exact this)
  have hd2 : z₀ ≠ a * z₀ := fun h => ha1 (by
    have : a * z₀ = 1 * z₀ := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this)
  have hd3 : a ≠ a * z₀ := fun h => hz₀1 (by
    have : a * z₀ = a * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this)
  have hsub : ({1, z₀, a, a * z₀} : Set G) ⊆ (Z : Set G) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hz₀Z
    · exact haZ'
    · exact haz₀Z
  have hcard : (Z : Set G).ncard ≤ ({1, z₀, a, a * z₀} : Set G).ncard := by
    rw [hZn]
    have h1 : (1 : G) ∉ ({z₀, a, a * z₀} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz₀1.symm, ha1.symm, hd1.symm⟩
    have h2 : z₀ ∉ ({a, a * z₀} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨haz.symm, hd2⟩
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair hd3]
  have hset : ({1, z₀, a, a * z₀} : Set G) = (Z : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hxa : x * a = a * x := by
    have hw : x * a * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hHZ hx) a).mp haZ'
    have hw' : x * a * x⁻¹ ∈ ({1, z₀, a, a * z₀} : Set G) := by rw [hset]; exact hw
    have hne1 : x * a * x⁻¹ ≠ 1 := fun h => ha1 (by
      have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [h] at this; simpa using this)
    have hx0 : x⁻¹ * z₀ * x = z₀ := by
      have : z₀ * x = x * z₀ := hz₀x.symm
      calc x⁻¹ * z₀ * x = x⁻¹ * (z₀ * x) := by rw [mul_assoc]
        _ = x⁻¹ * (x * z₀) := by rw [this]
        _ = z₀ := by group
    have hne2 : x * a * x⁻¹ ≠ z₀ := fun h => haz (by
      have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [h, hx0] at this; exact this)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    rcases hw' with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hne2
    · calc x * a = (x * a * x⁻¹) * x := by group
        _ = a * x := by rw [h]
    · exfalso
      have h3 : x * z₀ * x⁻¹ = z₀ := by
        have : x * z₀ = z₀ * x := hz₀x
        rw [this]; group
      have h2 : x ^ 2 * a * (x ^ 2)⁻¹ = a := by
        have e1 : x ^ 2 * a * (x ^ 2)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
        rw [e1, h]
        have e2 : x * (a * z₀) * x⁻¹ = (x * a * x⁻¹) * (x * z₀ * x⁻¹) := by
          simp only [mul_assoc, inv_mul_cancel_left]
        rw [e2, h, h3]
        have : z₀ * z₀ = 1 := by simpa [pow_two] using hz₀2
        calc a * z₀ * z₀ = a * (z₀ * z₀) := by rw [mul_assoc]
          _ = a := by rw [this, mul_one]
      have hcomm : Commute (x ^ 2) a := by
        have : x ^ 2 * a = a * x ^ 2 := by
          calc x ^ 2 * a = (x ^ 2 * a * (x ^ 2)⁻¹) * x ^ 2 := by group
            _ = a * x ^ 2 := by rw [h2]
        exact this
      obtain ⟨j, hj⟩ := hxodd
      have hxj : x ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
      have hxx : (x ^ 2) ^ (j + 1) = x := by
        calc (x ^ 2) ^ (j + 1) = x ^ (2 * j + 1) * x := by
              rw [← pow_mul, ← pow_succ]; ring_nf
          _ = x := by rw [hxj, one_mul]
      have hcx : Commute x a := by
        rw [← hxx]; exact hcomm.pow_left _
      have : x * a * x⁻¹ = a := by
        have : x * a = a * x := hcx
        rw [this]; group
      rw [this] at h
      have : a * z₀ = a * 1 := by rw [mul_one]; exact h.symm
      exact hz₀1 (mul_left_cancel this)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ ({1, z₀, a, a * z₀} : Set G) := by rw [hset]; exact hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
  rcases hy' with h | h | h | h <;> rw [h]
  · simp
  · exact hz₀x.symm
  · exact hxa.symm
  · calc a * z₀ * x = a * (z₀ * x) := by rw [mul_assoc]
      _ = a * (x * z₀) := by rw [hz₀x]
      _ = (a * x) * z₀ := by rw [mul_assoc]
      _ = (x * a) * z₀ := by rw [hxa]
      _ = x * (a * z₀) := by rw [mul_assoc]

theorem normalizes_and_oTwoUpper_le_centralizer {H T Z A : Subgroup G} (hT : IsSylowTwoOf T H)
    (hmax : ∀ Y : Subgroup G, T ≤ Y → Y ≤ H → Y = T ∨ Y = H) (hidx : T.relIndex H = 9)
    (hZT : Z ≤ T) (hZe : IsElemAbelian 2 Z) (hZ4 : Nat.card Z = 4)
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) (hAH : A ≤ H) (hAT : ¬ A ≤ T)
    (hAZ : A ≤ Subgroup.centralizer (Z : Set G)) :
    H ≤ Subgroup.normalizer (Z : Set G) ∧ oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) := by
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) :=
    normalizes_of_normalizes hmax hT.1 hTZ hAH hAT (hAZ.trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hHZ, ?_⟩
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact centralizes_of_odd hT.2.1 hmax hT.1 hidx hZT hZe.2 hZ4 hTZ hHZ x hx.1 hx.2

end S152N

end CFSG.Quasithin
