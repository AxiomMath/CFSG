module

public import CFSG.Quasithin.EmptyFaithful.SzN32Frat

public section

namespace CFSG.Quasithin.SzN32

namespace Hx

theorem comm_of_closure {G : Type*} [Group G] {s : Set G}
    (hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) {a b : G} (ha : a ∈ Subgroup.closure s)
    (hb : b ∈ Subgroup.closure s) : a * b = b * a := by
  have := Subgroup.isMulCommutative_closure (k := s) (fun a ha b hb _ => hs a ha b hb)
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure s) ⟨b, hb⟩)

theorem comm_of_card_dvd_nine {G : Type*} [Group G] (h : Nat.card G ∣ 9) (a b : G) :
    a * b = b * a := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.dvd_prime_pow Nat.prime_three] at h
  obtain ⟨k, hk, hk'⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  interval_cases k
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by simpa using hk')).1
    rw [Subsingleton.elim a b]
  · have := isCyclic_of_prime_card (p := 3) (by simpa using hk')
    exact mul_comm' a b
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hk'
    exact mul_comm' a b

theorem eq_sup_zpowers {G : Type*} [Group G] [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hcard : Nat.card B = 3 * Nat.card A) {b : G} (hb : b ∈ B) (hbA : b ∉ A) :
    B = A ⊔ Subgroup.zpowers b := by
  have hAD : A ≤ A ⊔ Subgroup.zpowers b := le_sup_left
  have hDB : A ⊔ Subgroup.zpowers b ≤ B := sup_le hAB ((Subgroup.zpowers_le).2 hb)
  have hbD : b ∈ A ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAD
  have hA0 : 0 < Nat.card A := Nat.card_pos
  have hdvd : Nat.card A * k ∣ Nat.card A * 3 := by
    rw [← hk, mul_comm, ← hcard]
    exact Subgroup.card_dvd_of_le hDB
  have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hA0 hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with rfl | rfl
  · exfalso
    apply hbA
    have : A = A ⊔ Subgroup.zpowers b := Subgroup.eq_of_le_of_card_ge hAD (by omega)
    rw [this]
    exact hbD
  · exact (Subgroup.eq_of_le_of_card_ge hDB (by omega)).symm

theorem card_center_le {X : Type*} [Group X] [Finite X] (h27 : Nat.card X = 27)
    (hnc : ∃ x y : X, x * y ≠ y * x) : Nat.card (Subgroup.center X) ≤ 3 := by
  obtain ⟨m, hm, hm'⟩ : ∃ m ≤ 3, Nat.card (Subgroup.center X) = 3 ^ m := by
    refine (Nat.dvd_prime_pow Nat.prime_three).1 ?_
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨x, y, hxy⟩ := hnc
  interval_cases m
  · rw [hm']; norm_num
  · rw [hm']; norm_num
  · exfalso
    have hidx : (Subgroup.center X).index = 3 := by
      have := Subgroup.index_mul_card (Subgroup.center X)
      rw [h27, hm'] at this
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic (X ⧸ Subgroup.center X) := isCyclic_of_prime_card (p := 3) hidx
    have := (QuotientGroup.mk' (Subgroup.center X)).isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.ker_mk' _).le
    exact hxy (mul_comm' x y)
  · exfalso
    have htop : Subgroup.center X = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h27, hm']; norm_num)
    have hx : x ∈ Subgroup.center X := htop ▸ Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.1 hx y).symm

theorem exists_gen_pair {G : Type*} [Group G] [Finite G] {X X0 : Subgroup G} (hXX0 : X0 ≤ X)
    (h27 : Nat.card X = 27) (h9 : Nat.card X0 = 9)
    (hnc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) :
    ∃ x0 ∈ X0, ∃ x1 ∈ X, Subgroup.closure ({x0, x1} : Set G) = X := by
  obtain ⟨x1, hx1, hx1X0⟩ : ∃ x1 ∈ X, x1 ∉ X0 := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show X ≤ X0 from hall)
    omega
  have hX : X = X0 ⊔ Subgroup.zpowers x1 := eq_sup_zpowers hXX0 (by omega) hx1 hx1X0
  obtain ⟨x0, hx0, hx01⟩ : ∃ x0 ∈ X0, x0 * x1 ≠ x1 * x0 := by
    by_contra hall
    push Not at hall
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have hle : X ≤ Subgroup.closure ((X0 : Set G) ∪ {x1}) := by
      rw [hX]
      exact sup_le (fun y hy => Subgroup.subset_closure (Or.inl hy))
        ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inr rfl)))
    refine hab (comm_of_closure (s := (X0 : Set G) ∪ {x1}) ?_ (hle ha) (hle hb))
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact congrArg Subtype.val
        (comm_of_card_dvd_nine (G := X0) (by rw [h9]) ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [Set.mem_singleton_iff.1 hb]
      exact hall a ha
    · rw [Set.mem_singleton_iff.1 ha]
      exact (hall b hb).symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  refine ⟨x0, hx0, x1, hx1, ?_⟩
  have hY : Subgroup.closure ({x0, x1} : Set G) ≤ X := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hXX0 hx0
    · exact hx1
  have hdvd : Nat.card (Subgroup.closure ({x0, x1} : Set G)) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le hY
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk3 : k = 3 := by
    by_contra hne
    have hdvd9 : Nat.card (Subgroup.closure ({x0, x1} : Set G)) ∣ 9 := by
      rw [hk', show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact pow_dvd_pow 3 (by omega)
    exact hx01 (congrArg Subtype.val (comm_of_card_dvd_nine hdvd9
      ⟨x0, Subgroup.subset_closure (by simp)⟩ ⟨x1, Subgroup.subset_closure (by simp)⟩))
  exact Subgroup.eq_of_le_of_card_ge hY (by rw [hk', hk3, h27]; norm_num)

theorem commute_of_cm_eq {G : Type*} [Group G] (x g g' : G) (h : cm x g⁻¹ = cm x g'⁻¹) :
    x * (g'⁻¹ * g) = g'⁻¹ * g * x := by
  have e : ∀ g : G, g * x * g⁻¹ = x * cm x g⁻¹ := by
    intro g
    simp [cm, mul_assoc]
  have h2 : g * x * g⁻¹ = g' * x * g'⁻¹ := by rw [e g, e g', h]
  calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
    _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h2]
    _ = g'⁻¹ * g * x := by group

theorem index_centralizer_le {G : Type*} [Group G] [Finite G] {X X0 X1 : Subgroup G}
    (h3 : Nat.card X1 = 3) (h9 : Nat.card X0 = 9)
    (hc1 : ∀ h ∈ X0, ∀ g : G, cm h g ∈ X1) (hc0 : ∀ h ∈ X, ∀ g : G, cm h g ∈ X0)
    {x0 x1 : G} (hx0 : x0 ∈ X0) (hx1 : x1 ∈ X)
    (hgen : Subgroup.closure ({x0, x1} : Set G) = X) :
    (Subgroup.centralizer (X : Set G)).index ≤ 27 := by
  have hC : Subgroup.centralizer (X : Set G) = Subgroup.centralizer {x0, x1} := by
    conv_lhs => rw [← hgen]
    exact Subgroup.centralizer_closure _
  let C := Subgroup.centralizer (X : Set G)
  let F : G → X1 × X0 := fun g => (⟨cm x0 g⁻¹, hc1 x0 hx0 g⁻¹⟩, ⟨cm x1 g⁻¹, hc0 x1 hx1 g⁻¹⟩)
  have hF : Function.Injective (fun q : G ⧸ C => F q.out) := by
    intro q q' h
    have h' := Prod.ext_iff.1 h
    have e0 : cm x0 (q.out)⁻¹ = cm x0 (q'.out)⁻¹ := congrArg Subtype.val h'.1
    have e1 : cm x1 (q.out)⁻¹ = cm x1 (q'.out)⁻¹ := congrArg Subtype.val h'.2
    have hmem : (q'.out)⁻¹ * q.out ∈ Subgroup.centralizer (X : Set G) := by
      rw [hC, Subgroup.mem_centralizer_iff]
      rintro y (rfl | rfl)
      · exact commute_of_cm_eq _ _ _ e0
      · exact commute_of_cm_eq _ _ _ e1
    have := QuotientGroup.eq.2 hmem
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    exact this.symm
  calc C.index = Nat.card (G ⧸ C) := rfl
    _ ≤ Nat.card (X1 × X0) := Nat.card_le_card_of_injective _ hF
    _ = 27 := by rw [Nat.card_prod, h3, h9]

theorem relIndex_centralizer {G : Type*} [Group G] (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).relIndex X = (Subgroup.center X).index := by
  have : (Subgroup.centralizer (X : Set G)).subgroupOf X = Subgroup.center X := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g g.2)
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩)
  rw [Subgroup.relIndex, this]

theorem index_sup_centralizer_le {G : Type*} [Group G] [Finite G] {X : Subgroup G} [X.Normal]
    (h27 : Nat.card X = 27) (hcen : Nat.card (Subgroup.center X) ≤ 3)
    (hidx : (Subgroup.centralizer (X : Set G)).index ≤ 27) :
    (X ⊔ Subgroup.centralizer (X : Set G)).index ≤ 3 := by
  have h1 := Subgroup.relIndex_mul_index
    (le_sup_right : Subgroup.centralizer (X : Set G) ≤ X ⊔ Subgroup.centralizer (X : Set G))
  rw [Subgroup.relIndex_sup_right X (Subgroup.centralizer (X : Set G)), relIndex_centralizer]
    at h1
  have h2 := Subgroup.index_mul_card (Subgroup.center X)
  rw [h27] at h2
  have hc0 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
  have h9 : 9 ≤ (Subgroup.center X).index := by
    by_contra h
    push Not at h
    nlinarith
  by_contra h
  push Not at h
  nlinarith

theorem exists_zpowers_sup_eq_top {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    {N : Subgroup G} (hN : N.index ≤ 3) : ∃ g : G, Subgroup.zpowers g ⊔ N = ⊤ := by
  by_cases hNtop : N = ⊤
  · exact ⟨1, by simp [hNtop]⟩
  · obtain ⟨g, hg⟩ : ∃ g, g ∉ N := by
      by_contra h
      push Not at h
      exact hNtop (eq_top_iff.2 fun x _ => h x)
    refine ⟨g, ?_⟩
    have hlt : N < Subgroup.zpowers g ⊔ N := by
      refine lt_of_le_of_ne le_sup_right fun h => hg ?_
      rw [h]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
    have hlt' := Subgroup.index_strictAnti hlt
    obtain ⟨n, hn⟩ := hG.index (Subgroup.zpowers g ⊔ N)
    rcases n with _ | n
    · exact Subgroup.index_eq_one.1 (by simpa using hn)
    · exfalso
      have : 3 ≤ (Subgroup.zpowers g ⊔ N).index := by
        rw [hn]
        exact Nat.le_self_pow (Nat.succ_ne_zero n) 3
      omega

end Hx

theorem hx {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G) (X : Subgroup G) [X.Normal]
    (h27 : Nat.card X = 27) (hnc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) : ¬ X ≤ frattini G := by
  intro hΦ
  have hbotX : (⊥ : Subgroup G) < X := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at h27
    omega
  obtain ⟨X0, hX0n, -, hX0X, hX0card, hX0c⟩ := exists_normal_index_three hG hbotX
  have h9 : Nat.card X0 = 9 := by omega
  have := hX0n
  have hbot0 : (⊥ : Subgroup G) < X0 := by
    rw [bot_lt_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at h9
    omega
  obtain ⟨X1, hX1n, -, hX1X0, hX1card, hX1c⟩ := exists_normal_index_three hG hbot0
  have h3 : Nat.card X1 = 3 := by omega
  obtain ⟨x0, hx0, x1, hx1, hgen⟩ := Hx.exists_gen_pair hX0X h27 h9 hnc
  have hidx := Hx.index_centralizer_le h3 h9 hX1c hX0c hx0 hx1 hgen
  have hcen : Nat.card (Subgroup.center X) ≤ 3 := by
    refine Hx.card_center_le h27 ?_
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  obtain ⟨g0, hg0⟩ := Hx.exists_zpowers_sup_eq_top hG
    (Hx.index_sup_centralizer_le h27 hcen hidx)
  have hg0C : Subgroup.zpowers g0 ⊔ Subgroup.centralizer (X : Set G) = ⊤ := by
    apply frattini_nongenerating
    rw [eq_top_iff, ← hg0]
    exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le (hΦ.trans le_sup_right) (le_sup_right.trans le_sup_left))
  have hcyc : IsCyclic (G ⧸ Subgroup.centralizer (X : Set G)) := by
    refine isCyclic_iff_exists_zpowers_eq_top.2
      ⟨QuotientGroup.mk' (Subgroup.centralizer (X : Set G)) g0, ?_⟩
    have := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.centralizer (X : Set G)))) hg0C
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    exact this
  have hcomm := ((QuotientGroup.mk' (Subgroup.centralizer (X : Set G))).comp
    X.subtype).isMulCommutative_of_isCyclic_of_ker_le_center ?_
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : X) ⟨y, hy⟩))
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxC : (x : G) ∈ Subgroup.centralizer (X : Set G) := (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC y y.2)

end CFSG.Quasithin.SzN32
