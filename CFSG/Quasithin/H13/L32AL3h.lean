module

public import CFSG.Quasithin.H13.L32AL3a

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_centralizer_eq_card (K : Subgroup G) (x : G) (S : Finset G)
    (hS : ∀ y, y ∈ S ↔ ∃ k ∈ K, y = k * x * k⁻¹) :
    (Subgroup.centralizer ({x} : Set G)).relIndex K = S.card := by
  classical
  let C' : Subgroup ↥K := (Subgroup.centralizer ({x} : Set G)).subgroupOf K
  have key : ∀ a b : ↥K, (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹ ↔ a⁻¹ * b ∈ C' := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * b := by rw [h]
        _ = x * ((a : G)⁻¹ * b) := by group
    · intro h
      calc (a : G) * x * (a : G)⁻¹ = (a : G) * (x * ((a : G)⁻¹ * b)) * (b : G)⁻¹ := by group
        _ = (a : G) * ((a : G)⁻¹ * b * x) * (b : G)⁻¹ := by rw [h]
        _ = (b : G) * x * (b : G)⁻¹ := by group
  let Φ : (↥K ⧸ C') → ↥(S : Set G) := Quotient.lift
    (fun k : ↥K => ⟨(k : G) * x * (k : G)⁻¹, (hS _).mpr ⟨k, k.2, rfl⟩⟩) (by
      intro a b hab
      exact Subtype.ext ((key a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨a⟩ ⟨b⟩ hab
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((key a b).mp
        (congrArg Subtype.val hab)))
    · rintro ⟨y, hy⟩
      obtain ⟨k, hk, rfl⟩ := (hS y).mp hy
      exact ⟨Quotient.mk _ ⟨k, hk⟩, rfl⟩
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective Φ hΦ),
    Nat.card_coe_set_eq, Set.ncard_coe_finset]

variable {VY TY : Subgroup G} {z z' : G} (h : A114Hyp VY z z')
  (hTN : TY ≤ Subgroup.normalizer (VY : Set G))
  (hTz : TY ≤ Subgroup.centralizer ({z} : Set G)) (hT2 : IsPGroup 2 TY)
  (hOT : pCoreOf 2 (a114Y z z') ≤ TY) (hQT : twoCoreCentralizer z ≤ TY)

include h

theorem sup_le_normalizer (hTN : TY ≤ Subgroup.normalizer (VY : Set G)) :
    a114Y z z' ⊔ TY ≤ Subgroup.normalizer (VY : Set G) :=
  sup_le (a114_one h).1 hTN

include hOT hQT in
theorem mem_of_fix {y : G} (hy : y ∈ a114Y z z') (hyz : y * z * y⁻¹ = z) : y ∈ TY := by
  obtain ⟨hYN, -, hker, -⟩ := a114_one h
  have hyN := hYN hy
  have hmemO : ∀ u ∈ a114Y z z', u * z * u⁻¹ = z → u * z' * u⁻¹ = z' → u ∈ TY := by
    intro u hu h1 h2
    apply hOT
    rw [← hker]
    exact ⟨hu, h.mem_centralizer_of_fixes h1 h2⟩
  have hz'V : y * z' * y⁻¹ ∈ VY := (Subgroup.mem_normalizer_iff.mp hyN z').mp h.mem₂
  rcases h.mem_V_cases hz'V with h0 | h0 | h0 | h0
  · exfalso
    apply h.ne_one₂
    calc z' = y⁻¹ * (y * z' * y⁻¹) * y := by group
      _ = 1 := by rw [h0]; group
  · exfalso
    apply h.ne
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = y⁻¹ * (y * z' * y⁻¹) * y := by rw [hyz, h0]
      _ = z' := by group
  · exact hmemO y hy hyz h0
  · obtain ⟨a₁, -, ha₁, -, h₁, -⟩ := h.exists_gens
    have ha₁z : a₁ * z * a₁⁻¹ = z := A114Hyp.conj_self a₁ ha₁
    have ha₁Y : a₁ ∈ a114Y z z' := Subgroup.mem_sup_left ha₁
    have hc : a₁ * y ∈ TY := by
      refine hmemO _ (Subgroup.mul_mem _ ha₁Y hy) ?_ ?_
      · calc a₁ * y * z * (a₁ * y)⁻¹ = a₁ * (y * z * y⁻¹) * a₁⁻¹ := by group
          _ = z := by rw [hyz, ha₁z]
      · calc a₁ * y * z' * (a₁ * y)⁻¹ = a₁ * (y * z' * y⁻¹) * a₁⁻¹ := by group
          _ = a₁ * (z * z') * a₁⁻¹ := by rw [h0]
          _ = (a₁ * z * a₁⁻¹) * (a₁ * z' * a₁⁻¹) := by group
          _ = z' := by rw [ha₁z, h₁, h.v_alg₁]
    have := TY.mul_mem (TY.inv_mem (hQT ha₁)) hc
    rwa [inv_mul_cancel_left] at this

include hTN hTz hOT hQT in
theorem inf_centralizer_le :
    (a114Y z z' ⊔ TY) ⊓ Subgroup.centralizer ({z} : Set G) ≤ TY := by
  have hTY₀ : TY ≤ Subgroup.normalizer (a114Y z z' : Set G) := hTN.trans (a114_two h).2.2
  intro y hyY
  obtain ⟨hy, hyz⟩ := Subgroup.mem_inf.mp hyY
  obtain ⟨y₀, hy₀, τ, hτ, rfl⟩ := exists_mul_of_mem_sup hTY₀ hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyz
  have hτz : τ * z * τ⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hTz hτ)
    rw [this, mul_inv_cancel_right]
  have hy₀z : y₀ * z * y₀⁻¹ = z := by
    have e : y₀ * τ * z = z * (y₀ * τ) := hyz
    calc y₀ * z * y₀⁻¹ = y₀ * (τ * z * τ⁻¹) * y₀⁻¹ := by rw [hτz]
      _ = (y₀ * τ * z) * (y₀ * τ)⁻¹ := by group
      _ = z := by rw [e]; group
  exact TY.mul_mem (mem_of_fix h hOT hQT hy₀ hy₀z) hτ

theorem exists_conj_of_mem {w : G} (hw : w ∈ VY) (hw1 : w ≠ 1) :
    ∃ y ∈ a114Y z z', y * z * y⁻¹ = w := by
  obtain ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩ := h.exists_gens
  rcases h.mem_V_cases hw with rfl | rfl | rfl | rfl
  · exact absurd rfl hw1
  · exact ⟨1, Subgroup.one_mem _, by group⟩
  · exact ⟨a₁ * a₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂),
      h.y_act₁ ha₁ h₁ h₂⟩
  · exact ⟨a₂, Subgroup.mem_sup_right ha₂, h₂⟩

include hTN hTz hOT hQT in
theorem relIndex_eq_three : TY.relIndex (a114Y z z' ⊔ TY) = 3 := by
  classical
  have hTeq : TY = Subgroup.centralizer ({z} : Set G) ⊓ (a114Y z z' ⊔ TY) := by
    refine le_antisymm (le_inf hTz le_sup_right) ?_
    rw [inf_comm]
    exact inf_centralizer_le h hTN hTz hOT hQT
  have hYN := sup_le_normalizer h hTN
  have hS : ∀ y, y ∈ ({z, z', z * z'} : Finset G) ↔
      ∃ k ∈ a114Y z z' ⊔ TY, y = k * z * k⁻¹ := by
    intro y
    constructor
    · intro hy
      have hyV : y ∈ VY := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact h.mem₁
        · exact h.mem₂
        · exact VY.mul_mem h.mem₁ h.mem₂
      have hy1 : y ≠ 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact h.ne_one₁
        · exact h.ne_one₂
        · intro h1
          apply h.ne
          calc z = z * (z' * z') := by rw [h.v₂_mul_self, mul_one]
            _ = (z * z') * z' := by group
            _ = z' := by rw [h1, one_mul]
      obtain ⟨k, hk, hkz⟩ := exists_conj_of_mem h hyV hy1
      exact ⟨k, Subgroup.mem_sup_left hk, hkz.symm⟩
    · rintro ⟨k, hk, rfl⟩
      have hkz : k * z * k⁻¹ ∈ VY := (Subgroup.mem_normalizer_iff.mp (hYN hk) z).mp h.mem₁
      have hk1 : k * z * k⁻¹ ≠ 1 := fun h1 => h.ne_one₁ (by
        calc z = k⁻¹ * (k * z * k⁻¹) * k := by group
          _ = 1 := by rw [h1]; group)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h.mem_V_cases hkz with h0 | h0 | h0 | h0
      · exact absurd h0 hk1
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr h0)
  have hcard : ({z, z', z * z'} : Finset G).card = 3 := by
    have hzz' : z ≠ z' := h.ne
    have hz1 : z ≠ z * z' := fun h1 => h.ne_one₂ (by
      calc z' = z⁻¹ * (z * z') := by group
        _ = 1 := by rw [← h1]; group)
    have hz'1 : z' ≠ z * z' := fun h1 => h.ne_one₁ (by
      calc z = (z * z') * z'⁻¹ := by group
        _ = 1 := by rw [← h1]; group)
    rw [Finset.card_insert_of_notMem (by simp [hzz', hz1]),
      Finset.card_insert_of_notMem (by simp [hz'1]), Finset.card_singleton]
  calc TY.relIndex (a114Y z z' ⊔ TY)
      = (Subgroup.centralizer ({z} : Set G) ⊓ (a114Y z z' ⊔ TY)).relIndex (a114Y z z' ⊔ TY) := by
        rw [← hTeq]
    _ = (Subgroup.centralizer ({z} : Set G)).relIndex (a114Y z z' ⊔ TY) := by
        rw [Subgroup.inf_relIndex_right]
    _ = 3 := by rw [relIndex_centralizer_eq_card _ z _ hS, hcard]

include hTN hTz hT2 hOT hQT in
theorem isSylowTwoOf_sup : IsSylowTwoOf TY (a114Y z z' ⊔ TY) := by
  refine ⟨le_sup_right, hT2, ?_⟩
  change ¬ 2 ∣ TY.relIndex (a114Y z z' ⊔ TY)
  rw [relIndex_eq_three h hTN hTz hOT hQT]
  decide

omit h in
theorem pCoreOf_le_of_isSylowTwoOf {S X : Subgroup G} (hS : IsSylowTwoOf S X) :
    pCoreOf 2 X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf X) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 X := hS'.toSylow hS.2.2
  have : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 X ≤ (P : Subgroup X) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) P
  have h2 := Subgroup.map_mono (f := X.subtype) h1
  have h3 : (P : Subgroup X).map X.subtype = S := by
    change (S.subgroupOf X).map X.subtype = S
    rw [Subgroup.map_subgroupOf_eq_of_le hS.1]
  change Subgroup.map X.subtype (CFSG.Open.pCore 2 X) ≤ S
  rw [← h3]
  exact h2

include hTN hTz hT2 hOT hQT in
theorem pCoreOf_sup_eq : pCoreOf 2 (a114Y z z' ⊔ TY) =
    (a114Y z z' ⊔ TY) ⊓ Subgroup.centralizer (VY : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYN := sup_le_normalizer h hTN
  have hCz : Subgroup.centralizer (VY : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.mem₁)
  apply le_antisymm
  · intro p hp
    have hpY : p ∈ a114Y z z' ⊔ TY := pCoreOf_le 2 _ hp
    have hpT : ∀ q ∈ pCoreOf 2 (a114Y z z' ⊔ TY), q * z * q⁻¹ = z := fun q hq => by
      have := Subgroup.mem_centralizer_singleton_iff.mp
        (hTz (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_sup h hTN hTz hT2 hOT hQT) hq))
      rw [this, mul_inv_cancel_right]
    obtain ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩ := h.exists_gens
    set y := a₁ * a₂ with hy
    have hyY : y ∈ a114Y z z' ⊔ TY :=
      Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁)
        (Subgroup.mem_sup_right ha₂))
    have hyz : y * z * y⁻¹ = z' := h.y_act₁ ha₁ h₁ h₂
    have hq : y⁻¹ * p * y ∈ pCoreOf 2 (a114Y z z' ⊔ TY) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 _ (Subgroup.inv_mem _ hyY)) p).mp hp
      simpa using this
    have h1 := hpT _ hq
    have h2 : p * z' * p⁻¹ = z' := by
      rw [← hyz]
      calc p * (y * z * y⁻¹) * p⁻¹ = y * ((y⁻¹ * p * y) * z * (y⁻¹ * p * y)⁻¹) * y⁻¹ := by
            group
        _ = y * z * y⁻¹ := by rw [h1]
    exact ⟨hpY, h.mem_centralizer_of_fixes (hpT p hp) h2⟩
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, ?_⟩) (hT2.to_le ?_)
    · show y ∈ Subgroup.normalizer ((Subgroup.centralizer (VY : Set G) : Subgroup G) : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hyN := hYN hy
      constructor
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro v hv
        have hv' : y⁻¹ * v * y ∈ VY := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) v).mp hv
          simpa using this
        have := hx _ hv'
        calc v * (y * x * y⁻¹) = y * ((y⁻¹ * v * y) * x) * y⁻¹ := by group
          _ = y * (x * (y⁻¹ * v * y)) * y⁻¹ := by rw [this]
          _ = y * x * y⁻¹ * v := by group
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro v hv
        have hv' : y * v * y⁻¹ ∈ VY := (Subgroup.mem_normalizer_iff.mp hyN v).mp hv
        have := hx _ hv'
        calc v * x = y⁻¹ * ((y * v * y⁻¹) * (y * x * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * x * y⁻¹) * (y * v * y⁻¹)) * y := by rw [this]
          _ = x * v := by group
    · exact (inf_le_inf_left _ hCz).trans (inf_centralizer_le h hTN hTz hOT hQT)

omit [Finite G] h in
theorem relIndex_centralizer_le_two_of {A : Subgroup G} {u w : G}
    (hA : ∀ a ∈ A, a * u * a⁻¹ = u ∨ a * u * a⁻¹ = w) :
    (Subgroup.centralizer ({u} : Set G)).relIndex A ≤ 2 := by
  classical
  set S : Finset G := ({u, w} : Finset G).filter (fun y => ∃ a ∈ A, y = a * u * a⁻¹) with hSdef
  have hS : ∀ y, y ∈ S ↔ ∃ a ∈ A, y = a * u * a⁻¹ := by
    intro y
    rw [hSdef, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, a, ha, rfl⟩
      rcases hA a ha with h1 | h1 <;> simp [h1]
  rw [relIndex_centralizer_eq_card A u S hS]
  exact (Finset.card_filter_le _ _).trans Finset.card_le_two

include hTN hTz hT2 hOT hQT in
theorem relIndex_pCoreOf_le_two : (pCoreOf 2 (a114Y z z' ⊔ TY)).relIndex TY ≤ 2 := by
  have h1 : Subgroup.centralizer ({z'} : Set G) ⊓ TY ≤ pCoreOf 2 (a114Y z z' ⊔ TY) := by
    rw [pCoreOf_sup_eq h hTN hTz hT2 hOT hQT]
    rintro x ⟨hxz', hxT⟩
    refine ⟨Subgroup.mem_sup_right hxT, h.mem_centralizer_of_fixes ?_ ?_⟩
    · have := Subgroup.mem_centralizer_singleton_iff.mp (hTz hxT)
      rw [this, mul_inv_cancel_right]
    · have := Subgroup.mem_centralizer_singleton_iff.mp hxz'
      rw [this, mul_inv_cancel_right]
  have h2 : (Subgroup.centralizer ({z'} : Set G)).relIndex TY ≤ 2 := by
    refine relIndex_centralizer_le_two_of (w := z * z') fun a ha => ?_
    have haz : a * z * a⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hTz ha)
      rw [this, mul_inv_cancel_right]
    have hz'V : a * z' * a⁻¹ ∈ VY := (Subgroup.mem_normalizer_iff.mp (hTN ha) z').mp h.mem₂
    rcases h.mem_V_cases hz'V with h0 | h0 | h0 | h0
    · exfalso
      apply h.ne_one₂
      calc z' = a⁻¹ * (a * z' * a⁻¹) * a := by group
        _ = 1 := by rw [h0]; group
    · exfalso
      apply h.ne
      calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
        _ = a⁻¹ * (a * z' * a⁻¹) * a := by rw [haz, h0]
        _ = z' := by group
    · exact Or.inl h0
    · exact Or.inr h0
  calc (pCoreOf 2 (a114Y z z' ⊔ TY)).relIndex TY
      ≤ (Subgroup.centralizer ({z'} : Set G) ⊓ TY).relIndex TY :=
        Subgroup.relIndex_le_of_le_left h1 Subgroup.index_ne_zero_of_finite
    _ = (Subgroup.centralizer ({z'} : Set G)).relIndex TY := Subgroup.inf_relIndex_right _ _
    _ ≤ 2 := h2

end CFSG.Quasithin.H13.L32A.L2
