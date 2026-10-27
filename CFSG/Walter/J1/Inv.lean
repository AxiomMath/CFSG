module

public import CFSG.Walter.J1.Coprime

public section

namespace CFSG.Walter.J1

section General

variable {G : Type*} [Group G]

theorem card_inf_mul_ncard_inv [Finite G] {A : Subgroup G}
    (habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hodd : Odd (Nat.card A)) {s : G}
    (hs : s * s = 1) (hsA : s ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) *
      {a | a ∈ A ∧ s * a * s⁻¹ = a⁻¹}.ncard = Nat.card A := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hσ : ∀ a ∈ A, s * a * s⁻¹ ∈ A := fun a ha => (Subgroup.mem_normalizer_iff.mp hsA a).mp ha
  let f : A →* A :=
    { toFun := fun a => ⟨a * (s * a * s⁻¹)⁻¹, A.mul_mem a.2 (A.inv_mem (hσ a a.2))⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have h1 := habel _ (A.inv_mem (hσ a a.2)) _ (A.mul_mem b.2 (A.inv_mem (hσ b b.2)))
        calc (a : G) * b * (s * (a * b) * s⁻¹)⁻¹
            = a * (b * (s * b * s⁻¹)⁻¹ * (s * a * s⁻¹)⁻¹) := by group
          _ = a * ((s * a * s⁻¹)⁻¹ * (b * (s * b * s⁻¹)⁻¹)) := by rw [h1]
          _ = a * (s * a * s⁻¹)⁻¹ * (b * (s * b * s⁻¹)⁻¹) := by group }
  have hf : ∀ a : A, ((f a : A) : G) = a * (s * a * s⁻¹)⁻¹ := fun _ => rfl
  have hker : Nat.card f.ker = Nat.card (A ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
    have : f.ker = (Subgroup.centralizer ({s} : Set G)).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro ha
        have := congrArg Subtype.val ha
        rw [hf] at this
        have h2 : s * a * s⁻¹ = a := (mul_inv_eq_one.mp this).symm
        calc (a : G) * s = s * a * s⁻¹ * s := by rw [h2]
          _ = s * a := by group
      · intro ha
        apply Subtype.ext
        rw [hf, ← ha, mul_inv_cancel_right, mul_inv_cancel]
        rfl
    rw [this, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm]
  have hrange : Nat.card f.range = {a | a ∈ A ∧ s * a * s⁻¹ = a⁻¹}.ncard := by
    have hset : {a | a ∈ A ∧ s * a * s⁻¹ = a⁻¹} = Subtype.val '' (f.range : Set A) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, MonoidHom.mem_range]
      constructor
      · rintro ⟨hx, hsx⟩
        obtain ⟨j, hj⟩ := hodd
        refine ⟨⟨x, hx⟩, ⟨⟨x, hx⟩ ^ (j + 1), ?_⟩, rfl⟩
        apply Subtype.ext
        rw [hf]
        simp only [SubgroupClass.coe_pow]
        rw [← conj_pow, hsx, inv_pow, inv_inv, ← pow_add]
        have hxn : x ^ Nat.card A = 1 := pow_card_eq_one_of_mem hx
        rw [show j + 1 + (j + 1) = Nat.card A + 1 by omega, pow_succ, hxn, one_mul]
      · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
        refine ⟨(f a).2, ?_⟩
        rw [hf]
        generalize (a : G) = b
        simp only [mul_inv_rev, inv_inv, hsinv, mul_assoc, hs, mul_one]
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact (Nat.card_coe_set_eq _).symm
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem mul_mul_self_eq_one_iff {a s : G} (hs : s * s = 1) :
    a * s * (a * s) = 1 ↔ s * a * s⁻¹ = a⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [hsinv]
  constructor
  · intro h1
    calc s * a * s = a⁻¹ * (a * s * (a * s)) := by group
      _ = a⁻¹ := by rw [h1, mul_one]
  · intro h1
    calc a * s * (a * s) = a * (s * a * s) * (s⁻¹ * s) := by group
      _ = 1 := by rw [h1, inv_mul_cancel, mul_one, mul_inv_cancel]

theorem card_centralizer_map_conj [Finite G] (X : Subgroup G) (g : G) :
    Nat.card (Subgroup.centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (Subgroup.centralizer (X : Set G)) := by
  have hle : ∀ (Y : Subgroup G) (k : G), Nat.card (Subgroup.centralizer (Y : Set G)) ≤
      Nat.card (Subgroup.centralizer ((Y.map (MulAut.conj k).toMonoidHom : Subgroup G) :
        Set G)) := by
    intro Y k
    have h1 := Subgroup.map_centralizer_le_centralizer_image (Y : Set G)
      (MulAut.conj k).toMonoidHom
    rw [← Subgroup.coe_map] at h1
    calc Nat.card (Subgroup.centralizer (Y : Set G))
        = Nat.card ((Subgroup.centralizer (Y : Set G)).map (MulAut.conj k).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj k).injective).symm
      _ ≤ _ := Subgroup.card_le_of_le h1
  refine le_antisymm ?_ (hle X g)
  have := hle (X.map (MulAut.conj g).toMonoidHom) g⁻¹
  rwa [map_conj_inv_map_conj] at this

end General

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem exists_split {p : ℕ} (hp : p = 3 ∨ p = 5) {X : Subgroup G} (hX : Nat.card X = p) :
    ∃ z τ : G, ∃ A : Subgroup G, IsFour z τ ∧ (∀ u ∈ X, τ * u * τ⁻¹ = u⁻¹) ∧
      IsMaxInv z τ A ∧ A ≤ Subgroup.centralizer (X : Set G) ∧ X ≤ A ∧
      A ⊓ Subgroup.centralizer ({z} : Set G) = X ∧
      Nat.card A * 2 = Nat.card (Subgroup.centralizer (X : Set G)) ∧
      (∀ y ∈ A, ∀ w ∈ A, y * w = w * y) ∧ (Nat.card A = p ∨ Nat.card A = 15) ∧
      z ∈ Subgroup.centralizer (X : Set G) ∧ z ∉ A ∧
      ∀ w ∈ Subgroup.centralizer (X : Set G), w ∈ A ∨ w * z ∈ A := by
  obtain ⟨z, hz, hXz⟩ := h.exists_involution_of_card hp hX
  obtain ⟨τ, A, hT, hτX, hM, hAC, hXA, hAz, hA2, -, habel, hAcard⟩ :=
    h.bender_4_1_of_centralizer hp hX hz hXz
  set C := Subgroup.centralizer (X : Set G)
  have hzC : z ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hXz hx))
  have hzA : z ∉ A := by
    intro hzA
    have h1 : orderOf z ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hzA
    rw [hz] at h1
    exact (Nat.not_even_iff_odd.mpr hM.1.1) (even_iff_two_dvd.mpr h1)
  have hidx : (A.subgroupOf C).index = 2 := by
    have h1 := (A.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, ← hA2] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    nlinarith
  refine ⟨z, τ, A, hT, hτX, hM, hAC, hXA, hAz, hA2, habel, hAcard, hzC, hzA, ?_⟩
  intro w hw
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨w, hw⟩) (b := ⟨z, hzC⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  by_cases hwA : w ∈ A
  · exact Or.inl hwA
  · exact Or.inr (key.mpr (iff_of_false hwA hzA))

include h in
theorem ncard_centralizing_mul {p : ℕ} (hp : p = 3 ∨ p = 5) {X : Subgroup G}
    (hX : Nat.card X = p) :
    {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (X : Set G)}.ncard * (2 * p) =
      Nat.card (Subgroup.centralizer (X : Set G)) := by
  obtain ⟨z, τ, A, hT, -, hM, hAC, -, hAz, hA2, habel, -, hzC, hzA, hsplit⟩ := h.exists_split hp hX
  have hz2 := hT.mul_self_a
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hset : {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (X : Set G)} =
      (fun a => a * z) '' {a | a ∈ A ∧ z * a * z⁻¹ = a⁻¹} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hu, huC⟩
      have huA : u ∉ A := by
        intro huA
        have h1 : orderOf u ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A huA
        rw [hu] at h1
        exact (Nat.not_even_iff_odd.mpr hM.1.1) (even_iff_two_dvd.mpr h1)
      have huz : u * z ∈ A := (hsplit u huC).resolve_left huA
      refine ⟨u * z, ⟨huz, ?_⟩, by rw [mul_assoc, hz2, mul_one]⟩
      have huzz : u * z * z = u := by rw [mul_assoc, hz2, mul_one]
      rw [← mul_mul_self_eq_one_iff hz2, huzz]
      exact (orderOf_eq_two_iff.mp hu).1
    · rintro ⟨a, ⟨haA, ha⟩, rfl⟩
      refine ⟨orderOf_eq_two_iff.mpr ⟨(mul_mul_self_eq_one_iff hz2).mpr ha, fun h1 => hzA ?_⟩,
        Subgroup.mul_mem _ (hAC haA) hzC⟩
      have : z = a⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact A.inv_mem haA
  rw [hset, Set.ncard_image_of_injective _ (mul_left_injective z)]
  have := card_inf_mul_ncard_inv habel hM.1.1 hz2 hM.1.2.1
  rw [hAz, hX] at this
  rw [← hA2, ← this]
  ring

include h in
theorem ncard_inverting {X : Subgroup G} (hX : Nat.card X = 3) :
    (Nat.card (Subgroup.centralizer (X : Set G)) = 6 ∧
        {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹}.ncard = 6) ∨
      (Nat.card (Subgroup.centralizer (X : Set G)) = 30 ∧
        {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹}.ncard = 18) := by
  obtain ⟨z, τ, A, hT, hτX, hM, hAC, -, hAz, hA2, habel, hAcard, hzC, hzA, hsplit⟩ :=
    h.exists_split (Or.inl rfl) hX
  have hz2 := hT.mul_self_a
  have hτ2 := hT.mul_self_b
  have hzτ2 := hT.mul_self_mul
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set S₁ := {a | a ∈ A ∧ τ * a * τ⁻¹ = a⁻¹}
  set S₂ := {a | a ∈ A ∧ (z * τ) * a * (z * τ)⁻¹ = a⁻¹}
  have hcomm : ∀ w ∈ Subgroup.centralizer (X : Set G), ∀ x ∈ X, w * x * w⁻¹ = x := by
    intro w hw x hx
    rw [← Subgroup.mem_centralizer_iff.mp hw x hx, mul_inv_cancel_right]
  have hXinv : ∀ w ∈ A, (∀ x ∈ X, w * x * w⁻¹ = x⁻¹) → False := by
    intro w hwA hw
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card hX (by norm_num)
    have h1 := hw x hx
    rw [hcomm w (hAC hwA) x hx] at h1
    have hx3 : x ^ 3 = 1 := by rw [← hX]; exact pow_card_eq_one_of_mem hx
    have h2 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x
    apply hx1
    rw [pow_three, h2, mul_one] at hx3
    exact hx3
  have hzτX : ∀ x ∈ X, z * τ * x * (z * τ)⁻¹ = x⁻¹ := by
    intro x hx
    rw [mul_inv_rev, show z * τ * x * (τ⁻¹ * z⁻¹) = z * (τ * x * τ⁻¹) * z⁻¹ by group, hτX x hx,
      hcomm z hzC _ (X.inv_mem hx)]
  have hset : {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹} =
      (fun a => a * τ) '' S₁ ∪ (fun a => a * (z * τ)) '' S₂ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, S₁, S₂]
    constructor
    · rintro ⟨hu, huX⟩
      have hu2 := (orderOf_eq_two_iff.mp hu).1
      have hwC : u * τ ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 : u * τ * x * (u * τ)⁻¹ = x := by
          rw [mul_inv_rev, show u * τ * x * (τ⁻¹ * u⁻¹) = u * (τ * x * τ⁻¹) * u⁻¹ by group,
            hτX x hx, show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group, huX x hx, inv_inv]
        calc x * (u * τ) = u * τ * x * (u * τ)⁻¹ * (u * τ) := by rw [h1]
          _ = u * τ * x := by group
      have hwτ : u * τ * τ = u := by rw [mul_assoc, hτ2, mul_one]
      rcases hsplit _ hwC with hwA | hwA
      · refine Or.inl ⟨u * τ, ⟨hwA, ?_⟩, hwτ⟩
        rw [← mul_mul_self_eq_one_iff hτ2, hwτ]
        exact hu2
      · have hu' : u * τ * z * (z * τ) = u := by
          rw [show u * τ * z * (z * τ) = u * τ * (z * z) * τ by group, hz2, mul_one, hwτ]
        refine Or.inr ⟨u * τ * z, ⟨hwA, ?_⟩, hu'⟩
        rw [← mul_mul_self_eq_one_iff hzτ2, hu']
        exact hu2
    · rintro (⟨a, ⟨haA, ha⟩, rfl⟩ | ⟨a, ⟨haA, ha⟩, rfl⟩)
      · refine ⟨orderOf_eq_two_iff.mpr ⟨(mul_mul_self_eq_one_iff hτ2).mpr ha, fun h1 => ?_⟩, ?_⟩
        · have : τ = a⁻¹ := eq_inv_of_mul_eq_one_right h1
          exact hXinv τ (this ▸ A.inv_mem haA) hτX
        · intro x hx
          rw [mul_inv_rev, show a * τ * x * (τ⁻¹ * a⁻¹) = a * (τ * x * τ⁻¹) * a⁻¹ by group,
            hτX x hx, hcomm a (hAC haA) _ (X.inv_mem hx)]
      · refine ⟨orderOf_eq_two_iff.mpr ⟨(mul_mul_self_eq_one_iff hzτ2).mpr ha, fun h1 => ?_⟩,
          ?_⟩
        · have : z * τ = a⁻¹ := eq_inv_of_mul_eq_one_right h1
          exact hXinv (z * τ) (this ▸ A.inv_mem haA) hzτX
        · intro x hx
          rw [mul_inv_rev,
            show a * (z * τ) * x * ((z * τ)⁻¹ * a⁻¹) = a * (z * τ * x * (z * τ)⁻¹) * a⁻¹ by
              group, hzτX x hx, hcomm a (hAC haA) _ (X.inv_mem hx)]
  have hdisj : Disjoint ((fun a => a * τ) '' S₁) ((fun a => a * (z * τ)) '' S₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ⟨haA, -⟩, rfl⟩ ⟨b, ⟨hbA, -⟩, hab⟩
    have hab : b * (z * τ) = a * τ := hab
    apply hzA
    have : z = b⁻¹ * a := by
      calc z = b⁻¹ * (b * (z * τ)) * τ⁻¹ := by group
        _ = b⁻¹ * (a * τ) * τ⁻¹ := by rw [hab]
        _ = b⁻¹ * a := by group
    rw [this]
    exact A.mul_mem (A.inv_mem hbA) haA
  have hcard : {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹}.ncard =
      S₁.ncard + S₂.ncard := by
    rw [hset, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ (mul_left_injective τ),
      Set.ncard_image_of_injective _ (mul_left_injective (z * τ))]
  have h1 : Nat.card (A ⊓ Subgroup.centralizer ({τ} : Set G) : Subgroup G) * S₁.ncard =
      Nat.card A := card_inf_mul_ncard_inv habel hM.1.1 hτ2 hM.1.2.2
  have h2 : Nat.card (A ⊓ Subgroup.centralizer ({z * τ} : Set G) : Subgroup G) * S₂.ncard =
      Nat.card A := card_inf_mul_ncard_inv habel hM.1.1 hzτ2 hM.1.mul_mem
  have h3 := h.card_eq_mul hT hM.1
  rw [hAz, hX] at h3
  set c₁ := Nat.card (A ⊓ Subgroup.centralizer ({τ} : Set G) : Subgroup G)
  set c₂ := Nat.card (A ⊓ Subgroup.centralizer ({z * τ} : Set G) : Subgroup G)
  rw [hcard, ← hA2]
  rw [mul_assoc] at h3
  rcases hAcard with hA | hA <;> rw [hA] at h1 h2 h3
  · left
    have hc : c₁ * c₂ = 1 := by omega
    rw [Nat.dvd_one.mp (Dvd.intro _ hc)] at h1
    rw [Nat.dvd_one.mp (Dvd.intro_left _ hc)] at h2
    omega
  · right
    have hc : c₁ * c₂ = 5 := by omega
    have hc₁ : c₁ ∣ 5 := Dvd.intro _ hc
    rcases (Nat.dvd_prime (by norm_num : (5 : ℕ).Prime)).mp hc₁ with hc1 | hc1 <;>
      rw [hc1] at hc h1 <;> [rw [show c₂ = 5 by omega] at h2; rw [show c₂ = 1 by omega] at h2] <;>
      omega

include h in
theorem exists_card_odd {p : ℕ} (hp : p = 3 ∨ p = 5) : ∃ X : Subgroup G, Nat.card X = p := by
  have := Fact.mk (prime_of_three_or_five hp)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := h.F) p (by
    rw [h.card_F]; rcases hp with rfl | rfl <;> norm_num)
  exact ⟨Subgroup.zpowers (u : G), by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hu]⟩

include h in
theorem card_centralizer_eq_of_card {p : ℕ} (hp : p = 3 ∨ p = 5) {X Y : Subgroup G}
    (hX : Nat.card X = p) (hY : Nat.card Y = p) :
    Nat.card (Subgroup.centralizer (X : Set G)) = Nat.card (Subgroup.centralizer (Y : Set G)) := by
  obtain ⟨x, hx, hXx⟩ := h.exists_involution_of_card hp hX
  obtain ⟨y, hy, hYy⟩ := h.exists_involution_of_card hp hY
  obtain ⟨g, hg⟩ := h.exists_conj_of_good hp hX hY hx hy hXx hYy
  rw [← hg, card_centralizer_map_conj]

include h in
theorem card_centralizer_thirty {p q : ℕ} (hpq : p = 3 ∧ q = 5 ∨ p = 5 ∧ q = 3)
    {X Y : Subgroup G} (hX : Nat.card X = p) (hY : Nat.card Y = q)
    (h30 : Nat.card (Subgroup.centralizer (X : Set G)) = 30) :
    Nat.card (Subgroup.centralizer (Y : Set G)) = 30 := by
  have hp : p = 3 ∨ p = 5 := by rcases hpq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have hq : q = 3 ∨ q = 5 := by rcases hpq with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  obtain ⟨-, -, A, -, -, -, -, hXA, -, hA2, habel, -, -, -, -⟩ := h.exists_split hp hX
  have hA : Nat.card A = 15 := by omega
  have := Fact.mk (prime_of_three_or_five hq)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := A) q (by
    rw [hA]; rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num)
  set W := Subgroup.zpowers (w : G)
  have hW : Nat.card W = q := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
  have hXW : X ≤ Subgroup.centralizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (habel _ w.2 x (hXA hx)) k).eq
  have hdvd := Subgroup.card_dvd_of_le hXW
  rw [hX] at hdvd
  rw [h.card_centralizer_eq_of_card hq hY hW]
  rcases h.card_centralizer_odd hq hW with h1 | h1 <;> rw [h1] at hdvd ⊢
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at hdvd

include h in
theorem exists_d : ∃ d : ℕ, (d = 1 ∨ d = 3) ∧
    (∀ X : Subgroup G, Nat.card X = 3 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (X : Set G)}.ncard = 2 * d - 1 ∧
      {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹}.ncard = 6 * d) ∧
    (∀ P : Subgroup G, Nat.card P = 5 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (P : Set G)}.ncard = d) := by
  obtain ⟨X₀, hX₀⟩ := h.exists_card_odd (Or.inl rfl)
  by_cases h30 : Nat.card (Subgroup.centralizer (X₀ : Set G)) = 30
  · refine ⟨3, Or.inr rfl, fun X hX => ?_, fun P hP => ?_⟩
    · have hC : Nat.card (Subgroup.centralizer (X : Set G)) = 30 := by
        rw [h.card_centralizer_eq_of_card (Or.inl rfl) hX hX₀, h30]
      have h1 := h.ncard_centralizing_mul (Or.inl rfl) hX
      refine ⟨by omega, ?_⟩
      rcases h.ncard_inverting hX with ⟨h2, -⟩ | ⟨-, h2⟩
      · omega
      · exact h2
    · have hC := h.card_centralizer_thirty (Or.inl ⟨rfl, rfl⟩) hX₀ hP h30
      have h1 := h.ncard_centralizing_mul (Or.inr rfl) hP
      omega
  · refine ⟨1, Or.inl rfl, fun X hX => ?_, fun P hP => ?_⟩
    · have hC : Nat.card (Subgroup.centralizer (X : Set G)) = 6 := by
        rw [h.card_centralizer_eq_of_card (Or.inl rfl) hX hX₀]
        rcases h.card_centralizer_odd (Or.inl rfl) hX₀ with h1 | h1
        · exact h1
        · exact absurd h1 h30
      have h1 := h.ncard_centralizing_mul (Or.inl rfl) hX
      refine ⟨by omega, ?_⟩
      rcases h.ncard_inverting hX with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact h2
      · omega
    · have hC : Nat.card (Subgroup.centralizer (P : Set G)) = 10 := by
        rcases h.card_centralizer_odd (Or.inr rfl) hP with h1 | h1
        · exact h1
        · exact absurd (h.card_centralizer_thirty (Or.inr ⟨rfl, rfl⟩) hP hX₀ h1) h30
      have h1 := h.ncard_centralizing_mul (Or.inr rfl) hP
      omega

end JankoHyp

end CFSG.Walter.J1
