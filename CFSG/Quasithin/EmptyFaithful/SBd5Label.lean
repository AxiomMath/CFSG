module

public import CFSG.Quasithin.EmptyFaithful.SBd4Close
public import CFSG.Quasithin.EmptyFaithful.SBdK36Model
public import CFSG.Quasithin.EmptyFaithful.SBd2L3Branch2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd5

section S3

theorem perm3_sq_of_pow_four : ∀ x : Equiv.Perm (Fin 3), x ^ 4 = 1 → x * x = 1 := by decide

theorem perm3_eq_one_of_comm :
    ∀ σ a : Equiv.Perm (Fin 3), σ * σ = 1 → a ^ 3 = 1 → a ≠ 1 → σ * a * σ⁻¹ = a → σ = 1 := by
  set_option synthInstance.maxSize 2000 in
  set_option synthInstance.maxHeartbeats 400000 in
  decide

theorem perm3_eq_one_of_inv : ∀ a : Equiv.Perm (Fin 3), a ^ 3 = 1 → a = a⁻¹ → a = 1 := by decide

end S3

section Pair

theorem pair_key : ∀ (ς α γ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)), ς ^ 4 = 1 → α ^ 3 = 1 →
    γ ^ 3 = 1 → α ≠ 1 → γ ≠ 1 → ς * γ * ς⁻¹ = γ → ς * α * ς⁻¹ = α⁻¹ →
      (α.2 = 1 ∧ γ.1 = 1) ∨ (α.1 = 1 ∧ γ.2 = 1) := by
  rintro ⟨s₁, s₂⟩ ⟨a₁, a₂⟩ ⟨c₁, c₂⟩ hs ha hc ha1 hc1 hcs has
  have hs1 : s₁ ^ 4 = 1 := by simpa using congrArg Prod.fst hs
  have hs2 : s₂ ^ 4 = 1 := by simpa using congrArg Prod.snd hs
  have ha31 : a₁ ^ 3 = 1 := by simpa using congrArg Prod.fst ha
  have ha32 : a₂ ^ 3 = 1 := by simpa using congrArg Prod.snd ha
  have hcs1 : s₁ * c₁ * s₁⁻¹ = c₁ := by simpa using congrArg Prod.fst hcs
  have hcs2 : s₂ * c₂ * s₂⁻¹ = c₂ := by simpa using congrArg Prod.snd hcs
  have has1 : s₁ * a₁ * s₁⁻¹ = a₁⁻¹ := by simpa using congrArg Prod.fst has
  have has2 : s₂ * a₂ * s₂⁻¹ = a₂⁻¹ := by simpa using congrArg Prod.snd has
  have hc31 : c₁ ^ 3 = 1 := by simpa using congrArg Prod.fst hc
  have hc32 : c₂ ^ 3 = 1 := by simpa using congrArg Prod.snd hc
  have hsq1 := perm3_sq_of_pow_four s₁ hs1
  have hsq2 := perm3_sq_of_pow_four s₂ hs2
  by_cases h₁ : s₁ = 1
  ·
    have ha₁ : a₁ = 1 := by
      rw [h₁] at has1
      simp only [inv_one, one_mul, mul_one] at has1
      exact perm3_eq_one_of_inv a₁ ha31 has1
    have ha₂ : a₂ ≠ 1 := by
      intro h
      apply ha1
      simp [ha₁, h]
    have hs₂ : s₂ ≠ 1 := by
      intro h
      rw [h] at has2
      simp only [inv_one, one_mul, mul_one] at has2
      exact ha₂ (perm3_eq_one_of_inv a₂ ha32 has2)
    have hc₂ : c₂ = 1 := by
      by_contra hne
      exact hs₂ (perm3_eq_one_of_comm s₂ c₂ hsq2 hc32 hne hcs2)
    exact Or.inr ⟨ha₁, hc₂⟩
  · have hc₁ : c₁ = 1 := by
      by_contra hne
      exact h₁ (perm3_eq_one_of_comm s₁ c₁ hsq1 hc31 hne hcs1)
    have hc₂ : c₂ ≠ 1 := by
      intro h
      apply hc1
      simp [hc₁, h]
    have hs₂ : s₂ = 1 := perm3_eq_one_of_comm s₂ c₂ hsq2 hc32 hc₂ hcs2
    have ha₂ : a₂ = 1 := by
      rw [hs₂] at has2
      simp only [inv_one, one_mul, mul_one] at has2
      exact perm3_eq_one_of_inv a₂ ha32 has2
    exact Or.inl ⟨ha₂, hc₁⟩

end Pair

section X

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {tb : MulAut W}

theorem mem_L₁_of_snd_eq_one (hS : OfourStruct X L₁ L₂ tb)
    (e : ↥(L₁ ⊔ L₂) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (he₁ : ∀ (l : MulAut W) (hl : l ∈ L₁), (e ⟨l, Subgroup.mem_sup_left hl⟩).2 = 1)
    (he₂ : ∀ (l : MulAut W) (hl : l ∈ L₂), (e ⟨l, Subgroup.mem_sup_right hl⟩).1 = 1)
    {x : MulAut W} (hx : x ∈ L₁ ⊔ L₂) (h : (e ⟨x, hx⟩).2 = 1) : x ∈ L₁ := by
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hS.comm hx
  have hmul : e ⟨l₁ * l₂, hx⟩ = e ⟨l₁, Subgroup.mem_sup_left hl₁⟩ * e ⟨l₂, Subgroup.mem_sup_right hl₂⟩ := by
    rw [← map_mul]
    rfl
  have h2 : (e ⟨l₂, Subgroup.mem_sup_right hl₂⟩).2 = 1 := by
    have := congrArg Prod.snd hmul
    rw [h] at this
    simpa [he₁ l₁ hl₁] using this.symm
  have h3 : e ⟨l₂, Subgroup.mem_sup_right hl₂⟩ = 1 := Prod.ext (he₂ l₂ hl₂) h2
  have h4 : (⟨l₂, Subgroup.mem_sup_right hl₂⟩ : ↥(L₁ ⊔ L₂)) = 1 := e.injective (by rw [h3, map_one])
  have h5 : l₂ = 1 := congrArg Subtype.val h4
  rw [h5, mul_one]
  exact hl₁

theorem mem_L₂_of_fst_eq_one (hS : OfourStruct X L₁ L₂ tb)
    (e : ↥(L₁ ⊔ L₂) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (he₁ : ∀ (l : MulAut W) (hl : l ∈ L₁), (e ⟨l, Subgroup.mem_sup_left hl⟩).2 = 1)
    (he₂ : ∀ (l : MulAut W) (hl : l ∈ L₂), (e ⟨l, Subgroup.mem_sup_right hl⟩).1 = 1)
    {x : MulAut W} (hx : x ∈ L₁ ⊔ L₂) (h : (e ⟨x, hx⟩).1 = 1) : x ∈ L₂ := by
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute hS.comm hx
  have hmul : e ⟨l₁ * l₂, hx⟩ = e ⟨l₁, Subgroup.mem_sup_left hl₁⟩ * e ⟨l₂, Subgroup.mem_sup_right hl₂⟩ := by
    rw [← map_mul]
    rfl
  have h2 : (e ⟨l₁, Subgroup.mem_sup_left hl₁⟩).1 = 1 := by
    have := congrArg Prod.fst hmul
    rw [h] at this
    simpa [he₂ l₂ hl₂] using this.symm
  have h3 : e ⟨l₁, Subgroup.mem_sup_left hl₁⟩ = 1 := Prod.ext h2 (he₁ l₁ hl₁)
  have h4 : (⟨l₁, Subgroup.mem_sup_left hl₁⟩ : ↥(L₁ ⊔ L₂)) = 1 := e.injective (by rw [h3, map_one])
  have h5 : l₁ = 1 := congrArg Subtype.val h4
  rw [h5, one_mul]
  exact hl₂

theorem label_X (hS : OfourStruct X L₁ L₂ tb) {σ a c : MulAut W} (hσ : σ ∈ L₁ ⊔ L₂)
    (hσ4 : σ ^ 4 = 1) (ha : a ∈ oTwoUpper X) (hc : c ∈ oTwoUpper X) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hcσ : σ * c * σ⁻¹ = c) (haσ : σ * a * σ⁻¹ = a⁻¹) :
    (a ∈ L₁ ∧ c ∈ L₂) ∨ (a ∈ L₂ ∧ c ∈ L₁) := by
  obtain ⟨e, he₁, he₂⟩ := SBd.exists_mulEquiv_sup_perm hS
  have haP : a ∈ L₁ ⊔ L₂ := hS.oTwoUpper_le_sup ha
  have hcP : c ∈ L₁ ⊔ L₂ := hS.oTwoUpper_le_sup hc
  have ha3 : a ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper ha
  have hc3 : c ^ 3 = 1 := hS.pow_three_of_mem_oTwoUpper hc
  have hα3 : e ⟨a, haP⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, haP⟩ : ↥(L₁ ⊔ L₂)) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hγ3 : e ⟨c, hcP⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcP⟩ : ↥(L₁ ⊔ L₂)) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hς4 : e ⟨σ, hσ⟩ ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨σ, hσ⟩ : ↥(L₁ ⊔ L₂)) ^ 4 = 1 := Subtype.ext (by simpa using hσ4)
    rw [this, map_one]
  have hα1 : e ⟨a, haP⟩ ≠ 1 := by
    intro h
    apply ha1
    have : (⟨a, haP⟩ : ↥(L₁ ⊔ L₂)) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hγ1 : e ⟨c, hcP⟩ ≠ 1 := by
    intro h
    apply hc1
    have : (⟨c, hcP⟩ : ↥(L₁ ⊔ L₂)) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hcσ' : e ⟨σ, hσ⟩ * e ⟨c, hcP⟩ * (e ⟨σ, hσ⟩)⁻¹ = e ⟨c, hcP⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hcσ)
  have haσ' : e ⟨σ, hσ⟩ * e ⟨a, haP⟩ * (e ⟨σ, hσ⟩)⁻¹ = (e ⟨a, haP⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using haσ)
  rcases pair_key _ _ _ hς4 hα3 hγ3 hα1 hγ1 hcσ' haσ' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨mem_L₁_of_snd_eq_one hS e he₁ he₂ haP h1, mem_L₂_of_fst_eq_one hS e he₁ he₂ hcP h2⟩
  · exact Or.inr ⟨mem_L₂_of_fst_eq_one hS e he₁ he₂ haP h1, mem_L₁_of_snd_eq_one hS e he₁ he₂ hcP h2⟩

end X

section Generic

theorem eq_of_mem_card_three {H : Type*} [Group H] {A : Subgroup H} (hA : Nat.card A = 3) {u x : H}
    (hu : u ∈ A) (hu1 : u ≠ 1) (hx : x ∈ A) : x = 1 ∨ x = u ∨ x = u⁻¹ := by
  have hord : orderOf u = 3 := by
    have h3 : orderOf u ∣ 3 := by
      have h1 : orderOf (⟨u, hu⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hA] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hzp : Subgroup.zpowers u = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) (by rw [Nat.card_zpowers, hord, hA])
  rw [← hzp] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hu3 : u ^ (3 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hord] at h
    simpa using h
  have hmod : u ^ k = u ^ (k % 3) := by
    have h1 := zpow_mod_orderOf u k
    rw [hord, Nat.cast_ofNat] at h1
    exact h1.symm
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h
  · left; rw [hmod, h, zpow_zero]
  · right; left; rw [hmod, h, zpow_one]
  · right; right
    rw [hmod, h]
    have : u ^ (2 : ℤ) * u = 1 := by
      rw [← zpow_add_one]
      simpa using hu3
    exact eq_inv_of_mul_eq_one_left this

theorem pow_card_eq_one_of_mem {H : Type*} [Group H] {A : Subgroup H} {x : H} (hx : x ∈ A) :
    x ^ Nat.card A = 1 := by
  have := pow_card_eq_one' (G := ↥A) (x := ⟨x, hx⟩)
  exact congrArg Subtype.val this

end Generic

section Line

variable {G : Type} [Group G] [Finite G]

theorem line_eq {V Y B M : Subgroup G} {hV : IsElemAbelian 2 V}
    {La Lb : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}
    (hS : OfourStruct (autI hV M) La Lb tb) (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (hcore : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G))
    (hYe : autI hV Y = oTwoUpper (autI hV M)) (hBY : B ≤ Y) (hBO : B = oTwoUpper B)
    (hYB : Y ≤ Subgroup.normalizer (B : Set G))
    (hB : autI hV B = Lb ⊓ oTwoUpper (autI hV M)) :
    B = oTwoUpper (Y ⊓ Subgroup.centralizer
      (((commV La).map (inclMod hV) : Subgroup G) : Set G)) := by
  set Va : Subgroup G := (commV La).map (inclMod hV) with hVa
  have hVaV : Va ≤ V := map_inclMod_le hV _
  have hiff : ∀ (z : G) (hz : z ∈ Y), z ∈ Subgroup.centralizer (Va : Set G) →
      convI hV ⟨z, hYN hz⟩ ∈ autI hV B := by
    intro z hz hzC
    have hzP : convI hV ⟨z, hYN hz⟩ ∈ oTwoUpper (autI hV M) := by
      rw [← hYe]
      exact convI_mem_autI hV hz (hYN hz)
    have hzX : convI hV ⟨z, hYN hz⟩ ∈ autI hV M := oTwoUpper_le _ hzP
    have hzLb : convI hV ⟨z, hYN hz⟩ ∈ Lb :=
      (hS.mem_L₂_iff hzX).2 ((mem_centralizer_map_inclMod_iff hV (hYN hz) (commV La)).1 hzC)
    rw [hB]
    exact ⟨hzLb, hzP⟩
  refine le_antisymm ?_ ?_
  · have hBle : B ≤ Y ⊓ Subgroup.centralizer (Va : Set G) := by
      intro g hg
      refine ⟨hBY hg, ?_⟩
      have hgN := hYN (hBY hg)
      have h1 : convI hV ⟨g, hgN⟩ ∈ autI hV B := convI_mem_autI hV hg hgN
      rw [hB] at h1
      have hgX : convI hV ⟨g, hgN⟩ ∈ autI hV M := oTwoUpper_le _ h1.2
      exact (mem_centralizer_map_inclMod_iff hV hgN (commV La)).2 ((hS.mem_L₂_iff hgX).1 h1.1)
    calc B = oTwoUpper B := hBO
      _ ≤ oTwoUpper (Y ⊓ Subgroup.centralizer (Va : Set G)) := oTwoUpper_mono hBle
  · have hZY : Y ⊓ Subgroup.centralizer (Va : Set G) ≤ Y := inf_le_left
    refine szN3_oTwoUpper_le_of_decomp (K := pCoreOf 2 Y) (fun g hg => hYB hg.1)
      (pCoreOf_isPGroup 2 Y) ?_ ?_
    · rw [hcore]
      exact inf_le_inf_left _ (Subgroup.centralizer_le hVaV)
    · exact szN3_decomp (hV := hV) hYN hcore hBY hZY (fun z hz => hiff z hz.1 hz.2)

theorem card_autI_eq_three {V Y A M : Subgroup G} {hV : IsElemAbelian 2 V}
    {La Lb : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}
    (hS : OfourStruct (autI hV M) La Lb tb) (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (hcore : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G))
    (hYe : autI hV Y = oTwoUpper (autI hV M)) (hAY : A ≤ Y)
    (hA3 : padicValNat 3 (Nat.card A) = 1) (hnot : ¬ A ≤ pCoreOf 2 Y) :
    Nat.card ↥(autI hV A) = 3 := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : autI hV A ≤ oTwoUpper (autI hV M) := hYe ▸ autI_mono hV hAY
  have hP3 : IsPGroup 3 ↥(autI hV A) := fun g =>
    ⟨1, Subtype.ext (by simpa using hS.pow_three_of_mem_oTwoUpper (hle g.2))⟩
  obtain ⟨k, hk⟩ := hP3.exists_card_eq
  have hdvd : Nat.card ↥(autI hV A) ∣ Nat.card A :=
    Dvd.intro _ (card_autI_mul_card_inf hV (hAY.trans hYN))
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hk1 : k ≤ 1 := by
    rw [hk] at hdvd
    have := (padicValNat_dvd_iff_le hA0).mp hdvd
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hnot
    have hbot : autI hV A = ⊥ := Subgroup.card_eq_one.mp (by simpa using hk)
    have h0 := (autI_eq_bot_iff hV (hAY.trans hYN)).mp hbot
    rw [hcore]
    exact fun x hx => ⟨hAY hx, h0 hx⟩
  have hk' : k = 1 := by omega
  rw [hk, hk']
  simp

theorem line_of_elem {V Y A M : Subgroup G} {hV : IsElemAbelian 2 V}
    {La Lb : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}
    (hS : OfourStruct (autI hV M) La Lb tb) (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (hcore : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G))
    (hYe : autI hV Y = oTwoUpper (autI hV M)) (hAY : A ≤ Y)
    (hA3 : padicValNat 3 (Nat.card A) = 1) (hnot : ¬ A ≤ pCoreOf 2 Y) (hAO : A = oTwoUpper A)
    (hYA : Y ≤ Subgroup.normalizer (A : Set G)) {x : MulAut (IntMod V hV)} (hx : x ∈ autI hV A)
    (hx1 : x ≠ 1) (hxL : x ∈ Lb) :
    A = oTwoUpper (Y ⊓ Subgroup.centralizer
      (((commV La).map (inclMod hV) : Subgroup G) : Set G)) := by
  have hcard : Nat.card ↥(autI hV A) = 3 := card_autI_eq_three hS hYN hcore hYe hAY hA3 hnot
  have hle : autI hV A ≤ oTwoUpper (autI hV M) := hYe ▸ autI_mono hV hAY
  have hLb : autI hV A ≤ Lb := by
    have h1 : Nat.card ↥(Lb ⊓ autI hV A) ∣ 3 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (inf_le_right : Lb ⊓ autI hV A ≤ autI hV A)
    have hint : Lb ⊓ autI hV A = autI hV A := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exfalso
        have hb : Lb ⊓ autI hV A = ⊥ := Subgroup.card_eq_one.mp h
        have hmem : x ∈ Lb ⊓ autI hV A := ⟨hxL, hx⟩
        rw [hb, Subgroup.mem_bot] at hmem
        exact hx1 hmem
      · exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcard])
    calc autI hV A = Lb ⊓ autI hV A := hint.symm
      _ ≤ Lb := inf_le_left
  have hbot : autI hV A ≠ ⊥ := fun h => by
    rw [h] at hx
    exact hx1 (Subgroup.mem_bot.mp hx)
  have hEq : autI hV A = Lb ⊓ oTwoUpper (autI hV M) :=
    szN3_eq_of_le_of_ne_bot (le_inf hLb hle) hbot (szN3_card_inf_oTwoUpper_dvd hS)
  exact line_eq hS hYN hcore hYe hAY hAO hYA hEq

omit [Finite G] in
theorem convI_conj {V : Subgroup G} (hV : IsElemAbelian 2 V) {g h : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hh : h ∈ Subgroup.normalizer (V : Set G)) :
    convI hV ⟨g, hg⟩ * convI hV ⟨h, hh⟩ * (convI hV ⟨g, hg⟩)⁻¹ =
      convI hV ⟨g * h * g⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem hg hh)
        ((Subgroup.normalizer (V : Set G)).inv_mem hg)⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite G] in
theorem convI_comm {V : Subgroup G} (hV : IsElemAbelian 2 V) {g h : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hh : h ∈ Subgroup.normalizer (V : Set G)) :
    convI hV ⟨g, hg⟩ * convI hV ⟨h, hh⟩ * (convI hV ⟨g, hg⟩)⁻¹ * (convI hV ⟨h, hh⟩)⁻¹ =
      convI hV ⟨g * h * g⁻¹ * h⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem
          ((Subgroup.normalizer (V : Set G)).mul_mem hg hh)
          ((Subgroup.normalizer (V : Set G)).inv_mem hg))
        ((Subgroup.normalizer (V : Set G)).inv_mem hh)⟩ := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rfl

end Line

section Main

variable {G : Type} [Group G] [Finite G]

theorem l3YLLabel_of_l3 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hres : L3SolvableOverSylow) : L3YLLabel := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV0 hYY
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 hh c.ctx.inH hLc
  have hcomm : ⁅YL153 Yp L, Sgp153 T V₁ ⊓ L⁆ = YL153 Yp L :=
    SBd2.yLCommSL_of_l3 hres G T Mc M V₁ V₂ Yp I L t c hq c12
  obtain ⟨hYpeq, hLg3, hCg3, hQ⟩ := c12
  subst hYY
  set Y : Subgroup G := Y153 Mc M with hYdef
  have hYM : Y ≤ M := Y153_le Mc M
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := hyp.le_normalizer
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hMN
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_Y153 Mc M
  have hcore : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rcases Hyp153.lemma_15_3_7_cases h113 hyp with ⟨hcore, -⟩ | ⟨hP, -⟩
    · exact hcore
    · exfalso
      have h9 := S153F.card_eq_nine_of_isElemAbelianOfRank hQ
      have h27 := hP.2.1
      rw [h9] at h27
      norm_num at h27
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := hh.decomp.model
  have hYe : autI hV Y = oTwoUpper (autI hV M) := hyp.autOn_Y153 h113
  have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := hyp.isSylowTwoOf_autI
  set YL : Subgroup G := YL153 Y L with hYL
  set YC : Subgroup G := YC153 Y L with hYC
  set P : Subgroup G := pCoreOf 2 L with hP
  set Pp : Subgroup G := pCoreOf 2 Y with hPp
  have hYLle : YL ≤ Y ⊓ L := oTwoUpper_le _
  have hYLY : YL ≤ Y := hYLle.trans inf_le_left
  have hYCsec : YC ≤ centralizerSection Y L P := oTwoUpper_le _
  have hYCY : YC ≤ Y := fun y hy => (hYCsec hy).1
  have hYLO : YL = oTwoUpper YL := (A4.oTwoUpper_oTwoUpper _).symm
  have hYCO : YC = oTwoUpper YC := (A4.oTwoUpper_oTwoUpper _).symm
  have hYNL : Y ≤ Subgroup.normalizer (YL : Set G) := fun g hg =>
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(Subgroup.le_normalizer hg : g ∈ Subgroup.normalizer (Y : Set G)), hYpL hg⟩)
  have hPN' : Y ≤ Subgroup.normalizer (P : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hYpL hg)
  have hYNC : Y ≤ Subgroup.normalizer (YC : Set G) := fun g hg =>
    normalizer_le_normalizer_oTwoUpper _ (A4.mem_normalizer_of_conj_mem fun k hk =>
      conj_mem_centralizerSection (Subgroup.le_normalizer hg) (hYpL hg) (hPN' hg) hk)
  have hPLYp : P ⊓ Y ≤ Pp :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hPN' hg, Subgroup.le_normalizer hg⟩)
      ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
  have hLnot : ¬ YL ≤ Pp := SBd2.not_le_pCoreOf_of_padicValNat hLg3
  have hCnot : ¬ YC ≤ Pp := SBd2.not_le_pCoreOf_of_padicValNat hCg3
  obtain ⟨s, hsS, a₀, ha₀, hs0⟩ :
      ∃ s ∈ Sgp153 T V₁ ⊓ L, ∃ a ∈ YL, ¬ (s * a * s⁻¹ * a⁻¹ ∈ Pp) := by
    by_contra hno
    push Not at hno
    apply hLnot
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr fun a ha s hs => ?_
    have h1 := hno s hs a ha
    have e : ⁅a, s⁆ = (s * a * s⁻¹ * a⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Pp.inv_mem h1
  obtain ⟨c₀, hc₀, hc₀P⟩ : ∃ c ∈ YC, c ∉ Pp := by
    by_contra hno
    push Not at hno
    exact hCnot hno
  have hsSg : s ∈ Sgp153 T V₁ := hsS.1
  have hsL : s ∈ L := hsS.2
  have hsM : s ∈ M := hyp.T_le hsSg.1
  have hsN : s ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hsM
  have hsY : s ∈ Subgroup.normalizer (Y : Set G) := hMY hsM
  have hsYL : s ∈ Subgroup.normalizer (YL : Set G) :=
    normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hsY, Subgroup.le_normalizer hsL⟩)
  have ha₀Y : a₀ ∈ Y := hYLY ha₀
  have hc₀Y : c₀ ∈ Y := hYCY hc₀
  have ha₀N : a₀ ∈ Subgroup.normalizer (VZ T M : Set G) := hYN ha₀Y
  have hc₀N : c₀ ∈ Subgroup.normalizer (VZ T M : Set G) := hYN hc₀Y
  set σ := convI hV ⟨s, hsN⟩ with hσdef
  set ab := convI hV ⟨a₀, ha₀N⟩ with habdef
  set cb := convI hV ⟨c₀, hc₀N⟩ with hcbdef
  have hab : ab ∈ oTwoUpper (autI hV M) := by
    rw [← hYe]
    exact convI_mem_autI hV ha₀Y ha₀N
  have hcb : cb ∈ oTwoUpper (autI hV M) := by
    rw [← hYe]
    exact convI_mem_autI hV hc₀Y hc₀N
  have habL : ab ∈ autI hV YL := convI_mem_autI hV ha₀ ha₀N
  have hcbC : cb ∈ autI hV YC := convI_mem_autI hV hc₀ hc₀N
  have hsS' : s ∈ T ⊓ Subgroup.normalizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := hV₁ ▸ hsSg
  have hσmem : σ ∈ autI hV T ⊓ (L₁ ⊔ L₂) := by
    rw [← autI_nS hV hS hyp.T_le]
    exact convI_mem_autI hV hsS' hsN
  have hσ4 : σ ^ 4 = 1 := by
    have h := pow_card_eq_one_of_mem hσmem
    rwa [hS.card_S hsyl] at h
  have hκ : s * a₀ * s⁻¹ * a₀⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hsY a₀).mp ha₀Y) (Y.inv_mem ha₀Y)
  have hκC : s * a₀ * s⁻¹ * a₀⁻¹ ∉ Subgroup.centralizer (VZ T M : Set G) := fun h =>
    hs0 (hcore ▸ ⟨hκ, h⟩)
  have hκ1 : σ * ab * σ⁻¹ * ab⁻¹ ≠ 1 := by
    rw [hσdef, habdef, convI_comm hV hsN ha₀N]
    intro h
    exact hκC ((convI_eq_one_iff hV _).1 h)
  have hab1 : ab ≠ 1 := by
    intro h
    apply hκ1
    rw [h]
    simp
  have hσab : σ * ab * σ⁻¹ ≠ ab := by
    intro h
    apply hκ1
    rw [h]
    simp
  have hcardL : Nat.card ↥(autI hV YL) = 3 :=
    card_autI_eq_three hS hYN hcore hYe hYLY hLg3 hLnot
  have hσabmem : σ * ab * σ⁻¹ ∈ autI hV YL := by
    have h1 : s * a₀ * s⁻¹ ∈ YL := (Subgroup.mem_normalizer_iff.mp hsYL a₀).mp ha₀
    have h2 := convI_mem_autI hV h1 (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsN ha₀N) (inv_mem hsN))
    rw [hσdef, habdef, convI_conj hV hsN ha₀N]
    exact h2
  have haσ : σ * ab * σ⁻¹ = ab⁻¹ := by
    rcases eq_of_mem_card_three hcardL habL hab1 hσabmem with h | h | h
    · exfalso
      apply hab1
      have : ab = σ⁻¹ * (σ * ab * σ⁻¹) * σ := by group
      rw [this, h]
      group
    · exact absurd h hσab
    · exact h
  have hcb1 : cb ≠ 1 := by
    intro h
    exact hc₀P (hcore ▸ ⟨hc₀Y, (convI_eq_one_iff hV ⟨c₀, hc₀N⟩).1 h⟩)
  have hcσ : σ * cb * σ⁻¹ = cb := by
    have h1 : s * c₀ * s⁻¹ * c₀⁻¹ ∈ P := (hYCsec hc₀).2.2.2 s hsL
    have h2 : s * c₀ * s⁻¹ * c₀⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hsY c₀).mp hc₀Y) (Y.inv_mem hc₀Y)
    have h3 : s * c₀ * s⁻¹ * c₀⁻¹ ∈ Pp := hPLYp ⟨h1, h2⟩
    have h4 : s * c₀ * s⁻¹ * c₀⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := (hcore ▸ h3).2
    have hκcN : s * c₀ * s⁻¹ * c₀⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      (Subgroup.normalizer (VZ T M : Set G)).mul_mem
        ((Subgroup.normalizer (VZ T M : Set G)).mul_mem
          ((Subgroup.normalizer (VZ T M : Set G)).mul_mem hsN hc₀N)
          ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hsN))
        ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hc₀N)
    have h5 : convI hV ⟨s * c₀ * s⁻¹ * c₀⁻¹, hκcN⟩ = 1 := (convI_eq_one_iff hV _).2 h4
    rw [← convI_comm hV hsN hc₀N] at h5
    exact mul_inv_eq_one.mp h5
  rw [hV₁, hV₂]
  rcases label_X hS hσmem.2 hσ4 hab hcb hab1 hcb1 hcσ haσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨?_, ?_⟩
    · exact line_of_elem hS.symm hYN hcore hYe hYLY hLg3 hLnot hYLO hYNL habL hab1 h1
    · exact line_of_elem hS hYN hcore hYe hYCY hCg3 hCnot hYCO hYNC hcbC hcb1 h2
  · refine Or.inl ⟨?_, ?_⟩
    · exact line_of_elem hS hYN hcore hYe hYLY hLg3 hLnot hYLO hYNL habL hab1 h1
    · exact line_of_elem hS.symm hYN hcore hYe hYCY hCg3 hCnot hYCO hYNC hcbC hcb1 h2

end Main

end SBd5

end CFSG.Quasithin
