module

public import CFSG.Quasithin.Vol2.Ch10SecQ4S3
public import CFSG.Quasithin.Vol2.Ch10SecB3A5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

abbrev A5 : Type := alternatingGroup (Fin 5)

theorem card_le_four_of_isPGroup {P : Subgroup A5} (hP : IsPGroup 2 P) : Nat.card P ≤ 4 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 2 ^ k ∣ 60 := hk ▸ SecB.card_alt5 ▸ Subgroup.card_subgroup_dvd_card P
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := this.trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

theorem card_of_isSylowTwoOf {P : Subgroup A5} (hP : IsSylowTwoOf P ⊤) : Nat.card P = 4 := by
  obtain ⟨-, hp, hodd⟩ := hP
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 := Subgroup.relIndex_mul_card P ⊤
  rw [inf_top_eq, Subgroup.card_top, SecB.card_alt5, hk] at h1
  have hodd' : ¬ 2 ∣ P.relIndex ⊤ := hodd
  have hk5 : k ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : 0 < P.relIndex ⊤ := Nat.pos_of_ne_zero (by rintro h'; rw [h'] at h1; omega)
    have := Nat.le_mul_of_pos_left (2 ^ k) h0
    omega
  rw [hk]
  interval_cases k <;> omega

theorem mul_self_eq_one_of_card_four {P : Subgroup A5} (hP : Nat.card P = 4) {x : A5}
    (hx : x ∈ P) : x * x = 1 := by
  have h4 : x ^ 4 = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨x, hx⟩)
    rw [hP] at this
    exact congrArg Subtype.val this
  have h2 := sq_of_pow_four (x : Equiv.Perm (Fin 5)) x.2 (by
    rw [← Subgroup.coe_pow, h4, Subgroup.coe_one])
  apply Subtype.ext
  rw [Subgroup.coe_mul, ← pow_two, h2, Subgroup.coe_one]

theorem exists_pair_of_card_four {P : Subgroup A5} (hP : Nat.card P = 4) :
    ∃ a ∈ P, ∃ b ∈ P, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      b ∉ Subgroup.zpowers a := by
  have hne : P ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hP; omega
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have haa := mul_self_eq_one_of_card_four hP a.2
  have hao : orderOf (a : A5) = 2 := orderOf_eq_prime (by rw [pow_two]; exact haa)
    (fun h => ha1 (Subtype.ext h))
  have hb : ∃ b ∈ P, b ∉ Subgroup.zpowers (a : A5) := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show P ≤ Subgroup.zpowers (a : A5) from h)
    rw [hP, Nat.card_zpowers, hao] at hle
    omega
  obtain ⟨b, hbP, hbz⟩ := hb
  have hcomm : IsMulCommutative ↥P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hP]; norm_num)
  refine ⟨a, a.2, b, hbP, haa, mul_self_eq_one_of_card_four hP hbP, ?_,
    fun h => ha1 (Subtype.ext h), fun h => hbz (h ▸ Subgroup.one_mem _),
    fun h => hbz (h ▸ Subgroup.mem_zpowers _), hbz⟩
  have := congrArg Subtype.val (hcomm.is_comm.comm a ⟨b, hbP⟩)
  exact this

theorem eq_one_of_commute_three {x c : A5} (hx : x * x = 1) (hc : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hxc : x * c = c * x) : x = 1 := by
  have h6 : ((x * c : A5) : Equiv.Perm (Fin 5)) ^ 6 = 1 := by
    rw [← Subgroup.coe_pow, (Commute.mul_pow hxc 6)]
    have h1 : x ^ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_two, hx, one_pow]
    have h2 : c ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hc, one_pow]
    rw [h1, h2, one_mul, Subgroup.coe_one]
  rcases sq_or_cube_of_pow_six _ (x * c).2 h6 with h | h
  · exfalso
    apply hc1
    have h2 : (x * c) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
    rw [Commute.mul_pow hxc, pow_two x, hx, one_mul] at h2
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc, h2]; group
  · have h3 : (x * c) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
    rw [Commute.mul_pow hxc, hc, mul_one] at h3
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [h3, hx]; group

theorem exists_three_normalizer {P : Subgroup A5} (hP : Nat.card P = 4) :
    ∃ c : A5, c ^ 3 = 1 ∧ c ≠ 1 ∧ c ∈ Subgroup.normalizer (P : Set A5) := by
  obtain ⟨a, haP, b, hbP, haa, hbb, hab, ha1, hb1, hne, hbz⟩ := exists_pair_of_card_four hP
  have hcoe : ∀ {x y : A5}, x ≠ y → (x : Equiv.Perm (Fin 5)) ≠ y := fun h e => h (Subtype.ext e)
  obtain ⟨c, hcs, hc3, hc1, hca, hcb⟩ := exists_three_normalizing a b
    (congrArg Subtype.val haa) (congrArg Subtype.val hbb) (congrArg Subtype.val hab)
    (hcoe ha1) (hcoe hb1) (hcoe hne) a.2 b.2
  set c' : A5 := ⟨c, hcs⟩
  have hQ : Subgroup.closure ({a, b} : Set A5) = P := by
    have hle : Subgroup.closure ({a, b} : Set A5) ≤ P :=
      (Subgroup.closure_le _).mpr
        (Set.insert_subset_iff.mpr ⟨haP, Set.singleton_subset_iff.mpr hbP⟩)
    have hza : Subgroup.zpowers a ≤ Subgroup.closure ({a, b} : Set A5) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
    have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
    have h2 : 2 ∣ Nat.card (Subgroup.closure ({a, b} : Set A5)) := by
      have := Subgroup.card_dvd_of_le hza
      rwa [Nat.card_zpowers, hao] at this
    have h4 : Nat.card (Subgroup.closure ({a, b} : Set A5)) ∣ 4 := hP ▸ Subgroup.card_dvd_of_le hle
    have hne2 : Nat.card (Subgroup.closure ({a, b} : Set A5)) ≠ 2 := by
      intro h
      have heq : Subgroup.zpowers a = Subgroup.closure ({a, b} : Set A5) :=
        Subgroup.eq_of_le_of_card_ge hza (by rw [h, Nat.card_zpowers, hao])
      exact hbz (heq ▸ Subgroup.subset_closure (by simp))
    have hcard : Nat.card (Subgroup.closure ({a, b} : Set A5)) = 4 := by
      have hpos := Nat.pos_of_dvd_of_pos h4 (by norm_num)
      have hle4 := Nat.le_of_dvd (by norm_num) h4
      interval_cases h : Nat.card (Subgroup.closure ({a, b} : Set A5)) <;> omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hP])
  have hmap : ∀ g : A5, (g = c' ∨ g = c'⁻¹) → ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    have h0 : ∀ x ∈ Subgroup.closure ({a, b} : Set A5), c' * x * c'⁻¹ ∈ P := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with hy | hy
        · rw [hy, show c' * a * c'⁻¹ = b from Subtype.ext hca]
          exact hbP
        · rw [Set.mem_singleton_iff.mp hy, show c' * b * c'⁻¹ = a * b from Subtype.ext hcb]
          exact P.mul_mem haP hbP
      | one => simp
      | mul y z _ _ hy hz =>
        have e : c' * (y * z) * c'⁻¹ = (c' * y * c'⁻¹) * (c' * z * c'⁻¹) := by group
        rw [e]; exact Subgroup.mul_mem _ hy hz
      | inv y _ hy =>
        have e : c' * y⁻¹ * c'⁻¹ = (c' * y * c'⁻¹)⁻¹ := by group
        rw [e]; exact Subgroup.inv_mem _ hy
    have h1 : ∀ x ∈ P, c' * x * c'⁻¹ ∈ P := fun x hx => h0 x (hQ ▸ hx)
    have hc3' : c' * (c' * c') = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← pow_three]; exact hc3)
    have hcinv : c'⁻¹ = c' * c' := (eq_inv_of_mul_eq_one_right hc3').symm
    rintro g (rfl | rfl) x hx
    · exact h1 x hx
    · have h2 : c'⁻¹ * c'⁻¹ = c' := by
        rw [hcinv]
        calc c' * c' * (c' * c') = (c' * (c' * c')) * c' := by group
          _ = c' := by rw [hc3', one_mul]
      have e : c'⁻¹ * x * c'⁻¹⁻¹ = c' * (c' * x * c'⁻¹) * c'⁻¹ := by
        calc c'⁻¹ * x * c'⁻¹⁻¹ = (c' * c') * x * c' := by rw [inv_inv, hcinv]
          _ = c' * (c' * x * (c'⁻¹ * c'⁻¹)) := by rw [h2]; group
          _ = c' * (c' * x * c'⁻¹) * c'⁻¹ := by group
      rw [e]
      exact h1 _ (h1 x hx)
  refine ⟨c', Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3), fun h => hc1 (congrArg
    Subtype.val h), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hmap c' (Or.inl rfl) x, fun h => ?_⟩
  have := hmap c'⁻¹ (Or.inr rfl) _ h
  simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
