module

public import CFSG.Quasithin.Vol2.Ch3xC58NSLin2

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.Quasithin.C58
  Subgroup

variable {G : Type} [Group G]

theorem card_le_of_isSylowTwoOf [Finite G] {T M₀ P : Subgroup G} (hT : IsSylowTwoOf T M₀)
    (hP : IsPGroup 2 P) (hPM₀ : P ≤ M₀) : Nat.card P ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf M₀) := hT.2.1.comap_of_injective _ Subtype.val_injective
  let Sy : Sylow 2 ↥M₀ := hT'.toSylow hT.2.2
  have hP' : IsPGroup 2 (P.subgroupOf M₀) := hP.comap_of_injective _ Subtype.val_injective
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have h1 : Nat.card Q = Nat.card Sy := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 : Nat.card (P.subgroupOf M₀) ≤ Nat.card Q := Subgroup.card_le_of_le hQ
  have e1 : Nat.card (P.subgroupOf M₀) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM₀).toEquiv
  have e2 : Nat.card (T.subgroupOf M₀) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  have e3 : Nat.card Sy = Nat.card (T.subgroupOf M₀) := rfl
  omega

theorem conj_le_of_odd_of_hor [Finite G] {M₁ Q U : Subgroup G} {y : G} (hyM : y ∈ M₁)
    (hUQ : U ≤ Q)
    (hor : ∀ m ∈ M₁, m ∈ normalizer (Q : Set G) ∨ m * y⁻¹ ∈ normalizer (Q : Set G))
    (hodd : Odd (orderOf y)) : conjSubgroup U y ≤ Q := by
  have hyQ : y ∈ normalizer (Q : Set G) := by
    rcases hor (y * y) (mul_mem hyM hyM) with h | h
    · obtain ⟨k, hk⟩ := hodd
      have hy : y = (y * y) ^ (k + 1) := by
        rw [← pow_two, ← pow_mul]
        have : y ^ (2 * (k + 1)) = y ^ (orderOf y) * y := by
          rw [hk, ← pow_succ]; ring_nf
        rw [this, pow_orderOf_eq_one, one_mul]
      rw [hy]
      exact pow_mem h _
    · simpa using h
  have h1 := conjSubgroup_mono hUQ y
  rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hyQ] at h1

theorem exists_good_elt_of_hor [Finite G] {T M₀ K₁ S Q D : Subgroup G} {y : G}
    (hT : IsSylowTwoOf T M₀) (hM₀S : M₀ ≤ normalizer (S : Set G))
    (hidx : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≤ 2)
    (hQdef : Q = S ⊓ centralizer (blockU K₁ : Set G)) (hDdef : D = Q ⊓ centralizer (K₁ : Set G))
    (hQ : Q = blockU K₁ ⊔ D) (hUS : blockU K₁ ≤ S) (hyM₀ : y ∈ M₀)
    (hyF : y ∈ normalizer ((sqSub D : Subgroup G) : Set G))
    (hyU : ¬ conjSubgroup (blockU K₁) y ≤ Q)
    (hor : ∀ m ∈ M₀ ⊓ normalizer ((sqSub D : Subgroup G) : Set G),
      m ∈ normalizer (Q : Set G) ∨ m * y⁻¹ ∈ normalizer (Q : Set G))
    (hDle : ∀ g ∈ M₀ ⊓ normalizer ((sqSub D : Subgroup G) : Set G), conjSubgroup D g ≤ Q) :
    ¬ T ≤ normalizer (K₁ : Set G) ∧ ∃ x ∈ M₀,
      x ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) ∧
      ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTM₀ : T ≤ M₀ := hT.1
  set U₁ := blockU K₁ with hU₁
  set F := sqSub D with hF
  set M₁ := M₀ ⊓ normalizer (F : Set G) with hM₁
  set N' := M₁ ⊓ normalizer (Q : Set G) with hN'
  have hUQ : U₁ ≤ Q := hQ ▸ le_sup_left
  have hyM₁ : y ∈ M₁ := ⟨hyM₀, hyF⟩
  have hyQ : y ∉ normalizer (Q : Set G) := by
    intro hyQ
    apply hyU
    have h1 := conjSubgroup_mono hUQ y
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hyQ] at h1
  have hyy : y * y ∈ normalizer (Q : Set G) := by
    rcases hor (y * y) (mul_mem hyM₁ hyM₁) with h | h
    · exact h
    · exfalso; apply hyQ; simpa using h
  have hidx2 : N'.relIndex M₁ = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyM₁⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, coe_mul, hN', mem_inf]
    have hbM₁ : (b : G) ∈ M₁ := b.2
    by_cases hb : (b : G) ∈ normalizer (Q : Set G)
    · refine Or.inr ⟨⟨hbM₁, hb⟩, ?_⟩
      rintro ⟨-, hby⟩
      apply hyQ
      have := mul_mem (inv_mem hb) hby
      simpa using this
    · refine Or.inl ⟨⟨mul_mem hbM₁ hyM₁, ?_⟩, fun h => hb h.2⟩
      have h1 := (hor b hbM₁).resolve_left hb
      have : (b : G) * y = (b * y⁻¹) * (y * y) := by group
      rw [this]; exact mul_mem h1 hyy
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  have hT₁S : T₁ ≤ normalizer (S : Set G) := inf_le_left.trans (hTM₀.trans hM₀S)
  have hT₁U : T₁ ≤ normalizer (U₁ : Set G) := fun t ht => C1.mem_normalizer_blockU ht.2
  have hT₁Q : T₁ ≤ normalizer (Q : Set G) := fun t ht => by
    rw [hQdef]
    exact mem_normalizer_inf (hT₁S ht) (mem_normalizer_centralizer (hT₁U ht))
  have hT₁D : T₁ ≤ normalizer (D : Set G) := fun t ht => by
    rw [hDdef]
    exact mem_normalizer_inf (hT₁Q ht) (mem_normalizer_centralizer ht.2)
  have hT₁F : T₁ ≤ normalizer (F : Set G) := fun t ht =>
    conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_sqSub_of_mem_normalizer (hT₁D ht))
  have hT₁N' : T₁ ≤ N' := fun t ht => ⟨⟨hTM₀ ht.1, hT₁F ht⟩, hT₁Q ht⟩
  have hT₁M₁ : T₁ ≤ M₁ := hT₁N'.trans inf_le_left
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  obtain ⟨T₀, hT₀, hT₁T₀⟩ := A4.exists_isSylowTwoOf_ge hT₁M₁ hT₁2
  have hT₀N' : ¬ T₀ ≤ N' := by
    intro hle
    apply hT₀.2.2
    show 2 ∣ T₀.relIndex M₁
    rw [← Subgroup.relIndex_mul_relIndex T₀ N' M₁ hle inf_le_left, hidx2]
    exact dvd_mul_left 2 _
  obtain ⟨x, hxT₀, hxN'⟩ := IsConcreteLE.not_le_iff_exists.mp hT₀N'
  have hxM₁ : x ∈ M₁ := hT₀.1 hxT₀
  have hxQ : x ∉ normalizer (Q : Set G) := fun h => hxN' ⟨hxM₁, h⟩
  have hT₀card : Nat.card T₀ ≤ Nat.card T :=
    card_le_of_isSylowTwoOf hT hT₀.2.1 (hT₀.1.trans inf_le_left)
  have hne : T₁ ≠ T₀ := fun h => hxQ (hT₁Q (h ▸ hxT₀))
  have hidx₀ : 2 ≤ T₁.relIndex T₀ := by
    have hpos : T₁.relIndex T₀ ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf T₀)
    have h1 : T₁.relIndex T₀ ≠ 1 := fun h =>
      hne (le_antisymm hT₁T₀ (Subgroup.relIndex_eq_one.mp h))
    omega
  have hcard₀ : Nat.card T₀ = Nat.card T₁ * T₁.relIndex T₀ := card_eq_card_mul_relIndex hT₁T₀
  have hcardT : Nat.card T = Nat.card T₁ * T₁.relIndex T := card_eq_card_mul_relIndex inf_le_left
  have hpos₁ : 0 < Nat.card T₁ := Nat.card_pos
  have hns : ¬ T ≤ normalizer (K₁ : Set G) := by
    intro hTK
    have h1 : T₁ = T := le_antisymm inf_le_left (le_inf le_rfl hTK)
    rw [h1] at hcard₀ hidx₀
    have : Nat.card T * T.relIndex T₀ ≤ Nat.card T * 1 := by
      rw [← hcard₀, mul_one]; exact hT₀card
    have := Nat.le_of_mul_le_mul_left this (Nat.card_pos)
    omega
  refine ⟨hns, x, hxM₁.1, ?_, ?_⟩
  ·
    have hidxT : T₁.relIndex T = 2 := by
      have h1 : T₁.relIndex T ≠ 1 := fun h =>
        hns ((Subgroup.relIndex_eq_one.mp h).trans inf_le_right)
      have h0 : T₁.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf T)
      omega
    have h2 : T₁.relIndex T₀ = 2 := by
      have : Nat.card T₁ * T₁.relIndex T₀ ≤ Nat.card T₁ * 2 := by
        rw [← hcard₀, ← hidxT, ← hcardT]; exact hT₀card
      have := Nat.le_of_mul_le_mul_left this hpos₁
      omega
    have hn : (T₁.subgroupOf T₀).Normal := Subgroup.normal_of_index_eq_two h2
    exact (normal_subgroupOf_iff_le_normalizer hT₁T₀).mp hn hxT₀
  ·
    intro hle
    apply hxQ
    have hxS : x ∈ normalizer (S : Set G) := hM₀S hxM₁.1
    have hUx : conjSubgroup U₁ x ≤ Q := by
      rw [hQdef]
      refine le_inf ?_ hle
      have := conjSubgroup_mono hUS x
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hxS] at this
    have hDx : conjSubgroup D x ≤ Q := hDle x hxM₁
    have hQx : conjSubgroup Q x ≤ Q := by
      have e : conjSubgroup Q x = conjSubgroup U₁ x ⊔ conjSubgroup D x := by
        conv_lhs => rw [hQ]
        exact conjSubgroup_sup _ _ _
      rw [e]
      exact sup_le hUx hDx
    have := Subgroup.eq_of_le_of_card_ge hQx (by rw [card_conjSubgroup])
    exact conjSubgroup_eq_iff_mem_normalizer.mp this

theorem lin2_conj_le_of_odd [Finite G] {K S : Subgroup G} (hK : IsShort2 K) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type K n) (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (K : Set G))
    (hsyl : IsSylowTwoOf S (K ⊔ S)) (hc542 : S ≤ (S ⊓ K) ⊔ pCoreOf 2 (K ⊔ S)) {y : G}
    (hy : y ∈ normalizer (S : Set G)) (hodd : Odd (orderOf y)) :
    conjSubgroup (blockU K) y ≤ centralizer (blockU K : Set G) := by
  by_contra h
  have hP := pairDataZ_of_lin2 hK hn hlin hS2 hSN hsyl hc542 hy h
  exact h ((hP.conj_le_of_odd hy hP.mem_normalizer_sqSub hodd).trans inf_le_right)

theorem lin2_exists_good_elt [Finite G] {T M₀ K S : Subgroup G} (hK : IsShort2 K) {n : ℕ}
    (hn : 1 < n) (hlin : IsLin2Type K n) (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (K : Set G))
    (hsyl : IsSylowTwoOf S (K ⊔ S)) (hc542 : S ≤ (S ⊓ K) ⊔ pCoreOf 2 (K ⊔ S))
    (hT : IsSylowTwoOf T M₀) (hM₀S : M₀ ≤ normalizer (S : Set G))
    (hidx : (T ⊓ normalizer (K : Set G)).relIndex T ≤ 2) {y : G} (hyM₀ : y ∈ M₀)
    (hyU : ¬ conjSubgroup (blockU K) y ≤ centralizer (blockU K : Set G)) :
    ¬ T ≤ normalizer (K : Set G) ∧ ∃ x ∈ M₀,
      x ∈ normalizer ((T ⊓ normalizer (K : Set G) : Subgroup G) : Set G) ∧
      ¬ conjSubgroup (blockU K) x ≤ centralizer (blockU K : Set G) := by
  have hyS : y ∈ normalizer (S : Set G) := hM₀S hyM₀
  have hP := pairDataZ_of_lin2 hK hn hlin hS2 hSN hsyl hc542 hyS hyU
  exact exists_good_elt_of_hor hT hM₀S hidx rfl rfl hP.hQ
    (C5.Rank1.U_le_B hP.rank1) hyM₀ hP.mem_normalizer_sqSub hP.hx1
    (fun m hm => hP.mem_or_mem (hM₀S hm.1) hm.2) (fun g hg => hP.conj_D_le (hM₀S hg.1) hg.2)

end CFSG.Quasithin.C58NS
