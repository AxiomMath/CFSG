module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowGen

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

variable {S : Type*} [Group S]

theorem closure_mul_comm {T : Set S} (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {e f : S}
    (he : e ∈ Subgroup.closure T) (hf : f ∈ Subgroup.closure T) : e * f = f * e := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T :=
    (Subgroup.closure_le _).mpr fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => hT b hb a ha
  have h2 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure T : Set S) :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (h1 hb) a ha).symm
  exact Subgroup.mem_centralizer_iff.mp (h2 hf) e he

theorem closure_pow_three {T : Set S} (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hT3 : ∀ a ∈ T, a ^ 3 = 1) {e : S} (he : e ∈ Subgroup.closure T) : e ^ 3 = 1 := by
  induction he using Subgroup.closure_induction with
  | mem a ha => exact hT3 a ha
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    rw [Commute.mul_pow (closure_mul_comm hT ha hb) 3, iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

theorem exists_abelian_sup [Finite S] (Z : Subgroup S)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ3 : ∀ a ∈ Z, a ^ 3 = 1) (hZ9 : 9 ≤ Nat.card Z)
    {u : S} (hu3 : u ^ 3 = 1) (huZ : u ∉ Z) (huc : ∀ a ∈ Z, a * u = u * a) :
    ∃ E : Subgroup S, u ∈ E ∧ Z ≤ E ∧ (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) ∧
      (∀ e ∈ E, e ^ 3 = 1) ∧ 27 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : ∀ a ∈ insert u (Z : Set S), ∀ b ∈ insert u (Z : Set S), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (huc b hb).symm
    · exact huc a ha
    · exact hZc a ha b hb
  have hT3 : ∀ a ∈ insert u (Z : Set S), a ^ 3 = 1 := by
    intro a ha
    rcases ha with rfl | ha
    · exact hu3
    · exact hZ3 a ha
  have huE : u ∈ Subgroup.closure (insert u (Z : Set S)) :=
    Subgroup.subset_closure (Set.mem_insert u _)
  have hZE : Z ≤ Subgroup.closure (insert u (Z : Set S)) := fun z hz =>
    Subgroup.subset_closure (Set.mem_insert_of_mem u hz)
  have hE3 : ∀ e ∈ Subgroup.closure (insert u (Z : Set S)), e ^ 3 = 1 := fun e he =>
    closure_pow_three hT hT3 he
  refine ⟨Subgroup.closure (insert u (Z : Set S)), huE, hZE,
    fun e he f hf => closure_mul_comm hT he hf, hE3, ?_⟩
  have hpE : IsPGroup 3 (Subgroup.closure (insert u (Z : Set S))) := fun g =>
    ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one]; exact hE3 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpE
  have hdvd : Nat.card Z ∣ Nat.card (Subgroup.closure (insert u (Z : Set S))) :=
    Subgroup.card_dvd_of_le hZE
  rw [hn] at hdvd
  obtain ⟨m, -, hmZ⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hlt : Nat.card Z < Nat.card (Subgroup.closure (insert u (Z : Set S))) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hZE fun h => huZ (by rw [h]; exact huE))
  rw [hn, hmZ] at hlt
  rw [hmZ] at hZ9
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    interval_cases m <;> norm_num at hZ9
  have hmn : m < n := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h
    omega
  rw [hn]
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem L143Rows.of_central [Finite S] (P : Sylow 3 S) (Z : Subgroup S)
    (hZP : Z ≤ (P : Subgroup S)) (hZc : ∀ z ∈ Z, ∀ g ∈ (P : Subgroup S), z * g = g * z)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (hZ9 : 9 ≤ Nat.card Z) {y : S} (hyP : y ∈ (P : Subgroup S))
    (hy3 : y ^ 3 = 1) (hyZ : y ∉ Z) : L143Rows S := by
  refine L143Rows.of_sylow P fun x hxP hx3 _ => ?_
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a ha b (hZP hb)
  by_cases hxZ : x ∈ Z
  · obtain ⟨E, -, hZE, hEc, hE3, hE⟩ :=
      exists_abelian_sup Z hZab hZ3 hZ9 hy3 hyZ fun a ha => hZc a ha y hyP
    exact L143Row.of_mem E (hZE hxZ) hEc hE3 hE
  · obtain ⟨E, hxE, -, hEc, hE3, hE⟩ :=
      exists_abelian_sup Z hZab hZ3 hZ9 hx3 hxZ fun a ha => hZc a ha x hxP
    exact L143Row.of_mem E hxE hEc hE3 hE

theorem card_le_card_ker_pow_three {A : Type*} [Group A] [Finite A] (φ : A →* A)
    (hφ : ∀ a, φ (φ (φ a)) = 1) : Nat.card A ≤ Nat.card φ.ker ^ 3 := by
  have step : ∀ H : Subgroup A, Nat.card H ≤ Nat.card φ.ker * Nat.card (H.map φ) := by
    intro H
    have hk : Nat.card (φ.ker.subgroupOf H) ≤ Nat.card φ.ker := by
      rw [← Subgroup.card_map_of_injective (K := φ.ker.subgroupOf H) H.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_le_of_le inf_le_left
    rw [← Subgroup.card_ker_mul_card_range (φ.domRestrict H), MonoidHom.domRestrict_range,
      MonoidHom.ker_domRestrict]
    exact Nat.mul_le_mul_right _ hk
  have h1 := step ⊤
  have h2 := step ((⊤ : Subgroup A).map φ)
  have h3 := step (((⊤ : Subgroup A).map φ).map φ)
  have h4 : (((⊤ : Subgroup A).map φ).map φ).map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨_, ⟨_, ⟨a, -, rfl⟩, rfl⟩, rfl⟩
    exact Subgroup.mem_bot.mpr (hφ a)
  rw [h4, Subgroup.card_bot, mul_one] at h3
  rw [Subgroup.card_top] at h1
  calc Nat.card A ≤ Nat.card φ.ker * Nat.card ((⊤ : Subgroup A).map φ) := h1
    _ ≤ Nat.card φ.ker * (Nat.card φ.ker * Nat.card (((⊤ : Subgroup A).map φ).map φ)) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card φ.ker * (Nat.card φ.ker * Nat.card φ.ker) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = Nat.card φ.ker ^ 3 := by ring

private theorem word_eq_one {A : Subgroup S} (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) {a b c : S}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) :
    a * c⁻¹ * b * c⁻¹ * b * a⁻¹ * b * c⁻¹ = 1 := by
  have h1 : (c⁻¹ * b * c⁻¹ * b) * a⁻¹ = a⁻¹ * (c⁻¹ * b * c⁻¹ * b) :=
    hAc _ (A.mul_mem (A.mul_mem (A.mul_mem (A.inv_mem hc) hb) (A.inv_mem hc)) hb) _
      (A.inv_mem ha)
  have h2 : c⁻¹ * b = b * c⁻¹ := hAc _ (A.inv_mem hc) _ hb
  have h3 : (c⁻¹ * c⁻¹) * (b * b) = (b * b) * (c⁻¹ * c⁻¹) :=
    hAc _ (A.mul_mem (A.inv_mem hc) (A.inv_mem hc)) _ (A.mul_mem hb hb)
  calc a * c⁻¹ * b * c⁻¹ * b * a⁻¹ * b * c⁻¹
      = a * ((c⁻¹ * b * c⁻¹ * b) * a⁻¹) * b * c⁻¹ := by group
    _ = a * (a⁻¹ * (c⁻¹ * b * c⁻¹ * b)) * b * c⁻¹ := by rw [h1]
    _ = (c⁻¹ * b) * c⁻¹ * b * b * c⁻¹ := by group
    _ = (b * c⁻¹) * c⁻¹ * b * b * c⁻¹ := by rw [h2]
    _ = b * ((c⁻¹ * c⁻¹) * (b * b)) * c⁻¹ := by group
    _ = b * ((b * b) * (c⁻¹ * c⁻¹)) * c⁻¹ := by rw [h3]
    _ = (b * b * b) * (c * c * c)⁻¹ := by group
    _ = 1 := by rw [← pow_three', ← pow_three', hb3, hc3, inv_one, one_mul]

private theorem comm_iter_three (x a : S) :
    x * (x * (x * a * x⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹) * x⁻¹ *
        (x * (x * a * x⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹)⁻¹ =
      (x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹) * (x * (x * a * x⁻¹) * x⁻¹)⁻¹ * (x * a * x⁻¹) *
        (x * (x * a * x⁻¹) * x⁻¹)⁻¹ * (x * a * x⁻¹) * a⁻¹ * (x * a * x⁻¹) *
        (x * (x * a * x⁻¹) * x⁻¹)⁻¹ := by
  group

theorem exists_centralizer_nine [Finite S] (A : Subgroup S)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hA81 : 81 ≤ Nat.card A)
    {x : S} (hx3 : x ^ 3 = 1) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    ∃ Z : Subgroup S, Z ≤ A ∧ (∀ z ∈ Z, z * x = x * z) ∧ 9 ≤ Nat.card Z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : A →* A :=
    { toFun := fun a => ⟨x * a * x⁻¹ * (a : S)⁻¹, A.mul_mem (hxA a a.2) (A.inv_mem a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show x * ((a : S) * b) * x⁻¹ * ((a : S) * b)⁻¹ =
          (x * a * x⁻¹ * (a : S)⁻¹) * (x * b * x⁻¹ * (b : S)⁻¹)
        have hc : (x * b * x⁻¹ * (b : S)⁻¹) * (a : S)⁻¹ =
            (a : S)⁻¹ * (x * b * x⁻¹ * (b : S)⁻¹) :=
          hAc _ (A.mul_mem (hxA b b.2) (A.inv_mem b.2)) _ (A.inv_mem a.2)
        calc x * ((a : S) * b) * x⁻¹ * ((a : S) * b)⁻¹
            = x * a * x⁻¹ * ((x * b * x⁻¹ * (b : S)⁻¹) * (a : S)⁻¹) := by group
          _ = x * a * x⁻¹ * ((a : S)⁻¹ * (x * b * x⁻¹ * (b : S)⁻¹)) := by rw [hc]
          _ = (x * a * x⁻¹ * (a : S)⁻¹) * (x * b * x⁻¹ * (b : S)⁻¹) := by group }
  have hφ : ∀ a : A, (φ a : S) = x * a * x⁻¹ * (a : S)⁻¹ := fun _ => rfl
  have hφ3 : ∀ a : A, φ (φ (φ a)) = 1 := by
    intro a
    apply Subtype.ext
    rw [hφ, hφ, hφ, Subgroup.coe_one, comm_iter_three]
    have hbA : x * (a : S) * x⁻¹ ∈ A := hxA a a.2
    have hcA : x * (x * (a : S) * x⁻¹) * x⁻¹ ∈ A := hxA _ hbA
    have hd : x * (x * (x * (a : S) * x⁻¹) * x⁻¹) * x⁻¹ = a := by
      calc x * (x * (x * (a : S) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by
            group
        _ = a := by rw [← pow_three', hx3, one_mul, inv_one, mul_one]
    rw [hd]
    exact word_eq_one hAc a.2 hbA hcA (hA3 _ hbA) (hA3 _ hcA)
  have hcard := card_le_card_ker_pow_three φ hφ3
  have hpA : IsPGroup 3 A := fun g =>
    ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one]; exact hA3 g g.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hpA.to_subgroup φ.ker)
  rw [hj, ← pow_mul] at hcard
  have hj2 : 2 ≤ j := by
    by_contra h
    push Not at h
    interval_cases j <;> norm_num at hcard <;> omega
  refine ⟨φ.ker.map A.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : x * (a : S) * x⁻¹ * (a : S)⁻¹ = 1 := by
      rw [← hφ]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    show (a : S) * x = x * a
    calc (a : S) * x = (x * (a : S) * x⁻¹ * (a : S)⁻¹)⁻¹ * (x * a) := by group
      _ = x * a := by rw [h1, inv_one, one_mul]
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hj]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2

theorem L143Rows.of_normal [Finite S] (P : Sylow 3 S) (A : Subgroup S)
    (hAn : ∀ g ∈ (P : Subgroup S), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hA81 : 81 ≤ Nat.card A) : L143Rows S := by
  refine L143Rows.of_sylow P fun x hxP hx3 _ => ?_
  by_cases hxA : x ∈ A
  · exact L143Row.of_mem A hxA hAc hA3 (by omega)
  · obtain ⟨Z, hZA, hZx, hZ9⟩ := exists_centralizer_nine A hAc hA3 hA81 hx3 (hAn x hxP)
    obtain ⟨E, hxE, -, hEc, hE3, hE⟩ :=
      exists_abelian_sup Z (fun a ha b hb => hAc a (hZA ha) b (hZA hb))
        (fun a ha => hA3 a (hZA ha)) hZ9 hx3 (fun h => hxA (hZA h)) hZx
    exact L143Row.of_mem E hxE hEc hE3 hE

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
