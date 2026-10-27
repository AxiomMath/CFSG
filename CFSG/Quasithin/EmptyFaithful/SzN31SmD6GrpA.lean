module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.Quasithin.SzN31

namespace SmD6Grp

variable {Q : Type*} [Group Q]

omit [Group Q] in
theorem finite_of_card_27 (hQ : Nat.card Q = 27) : Finite Q :=
  Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)

theorem isPGroup_three_of_card_27 (hQ : Nat.card Q = 27) : IsPGroup 3 Q :=
  IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)

theorem nontrivial_of_nonabelian (hnc : ∃ u v : Q, u * v ≠ v * u) : Nontrivial Q := by
  obtain ⟨u, v, huv⟩ := hnc
  exact ⟨⟨u, v, fun h => huv (by rw [h])⟩⟩

theorem mul_comm_of_isCyclic_quotient_center [IsCyclic (Q ⧸ Subgroup.center Q)] (u v : Q) :
    u * v = v * u := by
  have h : IsMulCommutative Q :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Q))
      (by rw [QuotientGroup.ker_mk'])
  exact (IsMulCommutative.is_comm (M := Q)).comm u v

theorem card_center_eq_three (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) :
    Nat.card (Subgroup.center Q) = 3 := by
  have : Finite Q := finite_of_card_27 hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial Q := nontrivial_of_nonabelian hnc
  obtain ⟨u, v, huv⟩ := hnc
  have : Nontrivial (Subgroup.center Q) := (isPGroup_three_of_card_27 hQ).center_nontrivial
  have hdvd : Nat.card (Subgroup.center Q) ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center Q)
    rw [hQ] at this
    simpa using this
  obtain ⟨i, hi, hZi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hpos : 1 < Nat.card (Subgroup.center Q) := Finite.one_lt_card
  interval_cases i
  · rw [pow_zero] at hZi
    omega
  · simpa using hZi
  · exfalso
    have hidx := Subgroup.card_mul_index (Subgroup.center Q)
    rw [hZi, hQ] at hidx
    have h3 : Nat.card (Q ⧸ Subgroup.center Q) = 3 := by
      rw [← Subgroup.index_eq_card]
      norm_num at hidx
      omega
    have : IsCyclic (Q ⧸ Subgroup.center Q) := isCyclic_of_prime_card h3
    exact huv (mul_comm_of_isCyclic_quotient_center u v)
  · exfalso
    have htop : Subgroup.center Q = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hZi, hQ]; norm_num)
    have : v ∈ Subgroup.center Q := by rw [htop]; exact Subgroup.mem_top v
    exact huv (Subgroup.mem_center_iff.mp this u)

theorem card_quotient_center_eq_nine (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) :
    Nat.card (Q ⧸ Subgroup.center Q) = 9 := by
  have h := Subgroup.card_mul_index (Subgroup.center Q)
  rw [card_center_eq_three hQ hnc, hQ] at h
  rw [← Subgroup.index_eq_card]
  omega

theorem isMulCommutative_quotient_center (hQ : Nat.card Q = 27)
    (hnc : ∃ u v : Q, u * v ≠ v * u) : IsMulCommutative (Q ⧸ Subgroup.center Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    ((card_quotient_center_eq_nine hQ hnc).trans (by norm_num))

theorem commutator_mem_center (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) (g h : Q) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center Q := by
  have := isMulCommutative_quotient_center hQ hnc
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  generalize (g : Q ⧸ Subgroup.center Q) = a
  generalize (h : Q ⧸ Subgroup.center Q) = b
  rw [(IsMulCommutative.is_comm (M := Q ⧸ Subgroup.center Q)).comm a b]
  group

theorem cube_mem_center (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) (g : Q) :
    g ^ 3 ∈ Subgroup.center Q := by
  by_contra hg
  have : Finite Q := finite_of_card_27 hQ
  have hcard := card_quotient_center_eq_nine hQ hnc
  have h1 : orderOf (g : Q ⧸ Subgroup.center Q) ∣ 9 := hcard ▸ orderOf_dvd_natCard _
  have h3 : ¬ orderOf (g : Q ⧸ Subgroup.center Q) ∣ 3 := by
    intro h
    apply hg
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have h9 : orderOf (g : Q ⧸ Subgroup.center Q) = 9 := by
    have hle := Nat.le_of_dvd (by norm_num) h1
    generalize orderOf (g : Q ⧸ Subgroup.center Q) = n at h1 h3 hle ⊢
    interval_cases n <;> omega
  have : IsCyclic (Q ⧸ Subgroup.center Q) := isCyclic_of_orderOf_eq_card _ (h9.trans hcard.symm)
  obtain ⟨u, v, huv⟩ := hnc
  exact huv (mul_comm_of_isCyclic_quotient_center u v)

theorem pow_three_eq_one_of_mem_center (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u)
    {z : Q} (hz : z ∈ Subgroup.center Q) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center Q))
  rw [card_center_eq_three hQ hnc] at h
  simpa using congrArg Subtype.val h

theorem pow_nine_eq_one (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) (g : Q) :
    g ^ 9 = 1 := by
  have := pow_three_eq_one_of_mem_center hQ hnc (cube_mem_center hQ hnc g)
  rw [← pow_mul] at this
  exact this

theorem mul_pow_three (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) (g h : Q) :
    (g * h) ^ 3 = g ^ 3 * h ^ 3 := by
  have hcm : h * g * h⁻¹ * g⁻¹ ∈ Subgroup.center Q := commutator_mem_center hQ hnc h g
  have hc3 := pow_three_eq_one_of_mem_center hQ hnc hcm
  generalize hc : h * g * h⁻¹ * g⁻¹ = c at hcm hc3
  have hcen : ∀ a b : Q, a * (c * b) = c * (a * b) := fun a b => by
    rw [← mul_assoc, Subgroup.mem_center_iff.mp hcm a, mul_assoc]
  have hhg : ∀ X : Q, h * (g * X) = c * (g * (h * X)) := fun X => by
    rw [← hc]
    group
  have h1 : (g * h) ^ 3 = c * (c * (c * (g * (g * (g * (h * (h * h))))))) := by
    rw [pow_three']
    simp only [mul_assoc, hhg, hcen]
  rw [h1, ← mul_assoc, ← mul_assoc, ← pow_three', hc3, one_mul, pow_three', pow_three']
  simp only [mul_assoc]

theorem pow_three_eq_one_of_commute (hQ : Nat.card Q = 27) {x : Q} (hx3 : x ^ 3 = 1)
    (hxc : ∃ g : Q, g * x ≠ x * g) {g : Q} (hg : g * x = x * g) : g ^ 3 = 1 := by
  have hnc : ∃ u v : Q, u * v ≠ v * u := let ⟨g, hg⟩ := hxc; ⟨g, x, hg⟩
  by_contra hg3
  have : Finite Q := finite_of_card_27 hQ
  have hord : orderOf g = 9 := by
    have h1 : orderOf g ∣ 9 := orderOf_dvd_of_pow_eq_one (pow_nine_eq_one hQ hnc g)
    have h3 : ¬ orderOf g ∣ 3 := fun h => hg3 (orderOf_dvd_iff_pow_eq_one.mp h)
    have hle := Nat.le_of_dvd (by norm_num) h1
    generalize orderOf g = n at h1 h3 hle ⊢
    interval_cases n <;> omega
  have hgZ : g ∉ Subgroup.center Q := fun h => hg3 (pow_three_eq_one_of_mem_center hQ hnc h)
  have hzC : Subgroup.zpowers g ≤ Subgroup.centralizer ({g} : Set Q) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
  have h9C : 9 ∣ Nat.card (Subgroup.centralizer ({g} : Set Q)) := by
    have := Subgroup.card_dvd_of_le hzC
    rwa [Nat.card_zpowers, hord] at this
  have hCQ : Nat.card (Subgroup.centralizer ({g} : Set Q)) ∣ 27 :=
    hQ ▸ Subgroup.card_subgroup_dvd_card _
  have hCne : Nat.card (Subgroup.centralizer ({g} : Set Q)) ≠ 27 := by
    intro h
    have htop : Subgroup.centralizer ({g} : Set Q) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h, hQ])
    exact hgZ (Subgroup.centralizer_eq_top_iff_subset.mp htop rfl)
  have hC9 : Nat.card (Subgroup.centralizer ({g} : Set Q)) = 9 := by
    have hle := Nat.le_of_dvd (by norm_num) hCQ
    generalize Nat.card (Subgroup.centralizer ({g} : Set Q)) = m at h9C hCQ hCne hle ⊢
    interval_cases m <;> omega
  have hCeq : Subgroup.zpowers g = Subgroup.centralizer ({g} : Set Q) :=
    Subgroup.eq_of_le_of_card_ge hzC (by rw [hC9, Nat.card_zpowers, hord])
  have hxC : x ∈ Subgroup.zpowers g := by
    rw [hCeq]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxC
  have hk3 : g ^ (k * 3) = 1 := by
    rw [zpow_mul]
    simpa [hk] using hx3
  have hdvd : (9 : ℤ) ∣ k * 3 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hk3
    rwa [hord] at this
  obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 3 * m := ⟨k / 3, by omega⟩
  have hxZ : x ∈ Subgroup.center Q := by
    rw [← hk, hm, zpow_mul]
    exact zpow_mem (by simpa using cube_mem_center hQ hnc g) m
  obtain ⟨g', hg'⟩ := hxc
  exact hg' (Subgroup.mem_center_iff.mp hxZ g')

theorem mem_zpowers_of_mem_center (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hz1 : z ≠ 1) (hw : w ∈ Subgroup.center Q) :
    w ∈ Subgroup.zpowers z := by
  have : Finite Q := finite_of_card_27 hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf z = 3 := orderOf_eq_prime (pow_three_eq_one_of_mem_center hQ hnc hz) hz1
  have hZeq : Subgroup.zpowers z = Subgroup.center Q :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [card_center_eq_three hQ hnc, Nat.card_zpowers, hord])
  rw [hZeq]
  exact hw

theorem center_dichotomy (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) (σ : Q →* Q)
    (hσ : ∀ g, σ (σ g) = g) :
    (∀ w ∈ Subgroup.center Q, σ w = w) ∨ (∀ w ∈ Subgroup.center Q, σ w = w⁻¹) := by
  have : Finite Q := finite_of_card_27 hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard := card_center_eq_three hQ hnc
  have hσZ : ∀ w ∈ Subgroup.center Q, σ w ∈ Subgroup.center Q := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro h
    calc h * σ w = σ (σ h) * σ w := by rw [hσ]
      _ = σ (σ h * w) := (map_mul σ _ _).symm
      _ = σ (w * σ h) := by rw [Subgroup.mem_center_iff.mp hw (σ h)]
      _ = σ w * σ (σ h) := map_mul σ _ _
      _ = σ w * h := by rw [hσ]
  have : Nontrivial (Subgroup.center Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hZcard]; norm_num)
  obtain ⟨⟨z0, hz0⟩, hz0ne⟩ := exists_ne (1 : Subgroup.center Q)
  have hz01 : z0 ≠ 1 := fun h => hz0ne (Subtype.ext h)
  have hz03 : z0 ^ 3 = 1 := pow_three_eq_one_of_mem_center hQ hnc hz0
  have hord : orderOf z0 = 3 := orderOf_eq_prime hz03 hz01
  have hgen : ∀ w ∈ Subgroup.center Q, ∃ k : ℤ, z0 ^ k = w := fun w hw =>
    Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_mem_center hQ hnc hz0 hz01 hw)
  obtain ⟨j, hj⟩ := hgen (σ z0) (hσZ z0 hz0)
  have hj' : σ z0 = z0 ^ (j % 3) := by
    rw [← hj]
    have := zpow_mod_orderOf z0 j
    rw [hord] at this
    simpa using this.symm
  have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hj3 with h | h | h
  · exfalso
    rw [h, zpow_zero] at hj'
    exact hz01 (by rw [← hσ z0, hj', map_one])
  · left
    rw [h, zpow_one] at hj'
    intro w hw
    obtain ⟨k, rfl⟩ := hgen w hw
    rw [map_zpow, hj']
  · right
    rw [h] at hj'
    have hinv : z0 ^ (2 : ℤ) = z0⁻¹ :=
      (inv_eq_of_mul_eq_one_right (by rw [← hz03]; group)).symm
    rw [hinv] at hj'
    intro w hw
    obtain ⟨k, rfl⟩ := hgen w hw
    rw [map_zpow, hj', inv_zpow]

theorem comm_mul (hcc : ∀ g h : Q, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center Q) (x g h : Q) :
    g * h * x * (g * h)⁻¹ * x⁻¹ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) := by
  have hd := hcc h x
  have e1 : g * h * x * (g * h)⁻¹ * x⁻¹
      = g * (h * x * h⁻¹ * x⁻¹) * (x * g⁻¹ * x⁻¹) := by group
  rw [e1, Subgroup.mem_center_iff.mp hd (g * x * g⁻¹ * x⁻¹), Subgroup.mem_center_iff.mp hd g]
  group

theorem comm_inv (hcc : ∀ g h : Q, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center Q) (x g : Q) :
    g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
  have h := comm_mul hcc x g g⁻¹
  have h1 : g * g⁻¹ * x * (g * g⁻¹)⁻¹ * x⁻¹ = 1 := by group
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem commute_of_comm_eq_one {x g : Q} (h : g * x * g⁻¹ * x⁻¹ = 1) : g * x = x * g := by
  have h' : g * x * g⁻¹ = x := mul_inv_eq_one.mp h
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h']

theorem sigma_comm (hcc : ∀ g h : Q, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center Q) (σ : Q →* Q) {x : Q}
    (hσx : σ x = x⁻¹) (y : Q) :
    σ (y * x * y⁻¹ * x⁻¹) = (σ y * x * (σ y)⁻¹ * x⁻¹)⁻¹ := by
  simp only [map_mul, map_inv, hσx, inv_inv]
  generalize σ y = y0
  have he := Subgroup.mem_center_iff.mp (hcc y0 x⁻¹) x
  rw [inv_inv] at he
  calc y0 * x⁻¹ * y0⁻¹ * x = (y0 * x⁻¹ * y0⁻¹ * x * x) * x⁻¹ := by group
    _ = (x * (y0 * x⁻¹ * y0⁻¹ * x)) * x⁻¹ := by rw [he]
    _ = (y0 * x * y0⁻¹ * x⁻¹)⁻¹ := by group

theorem exp_three_of_inverting_aut (hQ : Nat.card Q = 27) {x : Q} (hx3 : x ^ 3 = 1)
    (hxc : ∃ g : Q, g * x ≠ x * g) (σ : Q →* Q) (hσ : ∀ g, σ (σ g) = g) (hσx : σ x = x⁻¹) :
    ∀ y : Q, y ^ 3 = 1 := by
  have hnc : ∃ u v : Q, u * v ≠ v * u := let ⟨g, hg⟩ := hxc; ⟨g, x, hg⟩
  have hcc := commutator_mem_center hQ hnc
  have hcomm : ∀ g : Q, g * x * g⁻¹ * x⁻¹ = 1 → g ^ 3 = 1 := fun g h =>
    pow_three_eq_one_of_commute hQ hx3 hxc (commute_of_comm_eq_one h)
  intro y
  suffices h6 : y ^ 3 * y ^ 3 = 1 by
    have h9 := pow_nine_eq_one hQ hnc y
    have : y ^ 9 = y ^ 3 * y ^ 3 * y ^ 3 := by rw [← pow_add, ← pow_add]
    rw [this, h6, one_mul] at h9
    exact h9
  have hkey := sigma_comm hcc σ hσx y
  rcases center_dichotomy hQ hnc σ hσ with hid | hinv
  · rw [hid _ (hcc y x)] at hkey
    have h1 : (σ y * y) * x * (σ y * y)⁻¹ * x⁻¹ = 1 := by
      rw [comm_mul hcc x (σ y) y, hkey]
      exact mul_inv_cancel _
    have h2 := hcomm _ h1
    rw [mul_pow_three hQ hnc, ← map_pow, hid _ (cube_mem_center hQ hnc y)] at h2
    exact h2
  · rw [hinv _ (hcc y x)] at hkey
    have hkey' := inv_injective hkey
    have h1 : (σ y * y⁻¹) * x * (σ y * y⁻¹)⁻¹ * x⁻¹ = 1 := by
      rw [comm_mul hcc x (σ y) y⁻¹, comm_inv hcc x y, ← hkey']
      exact mul_inv_cancel _
    have h2 := hcomm _ h1
    rw [mul_pow_three hQ hnc, ← map_pow, hinv _ (cube_mem_center hQ hnc y), inv_pow,
      ← mul_inv_rev, inv_eq_one] at h2
    exact h2

theorem exists_conj_hom {G : Type*} [Group G] {P : Subgroup G} (a : G)
    (haP : ∀ g ∈ P, a * g * a⁻¹ ∈ P) :
    ∃ σ : P →* P, ∀ g : P, (σ g : G) = a * g * a⁻¹ :=
  ⟨{ toFun := fun g => ⟨a * g * a⁻¹, haP g g.2⟩
     map_one' := Subtype.ext (by simp)
     map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) },
    fun _ => rfl⟩

end SmD6Grp

theorem isExtraspecial_three_of_card_27 {Q : Type*} [Group Q] (hQ : Nat.card Q = 27)
    (hnc : ∃ u v : Q, u * v ≠ v * u) (hexp : ∀ x : Q, x ^ 3 = 1) :
    CFSG.IsExtraspecial 3 Q where
  center_order_p := SmD6Grp.card_center_eq_three hQ hnc
  quotient_elementary_abelian := by
    have := SmD6Grp.isMulCommutative_quotient_center hQ hnc
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    induction a using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hexp, QuotientGroup.mk_one]
  quotient_nontrivial := by
    have : Finite Q := SmD6Grp.finite_of_card_27 hQ
    exact Finite.one_lt_card_iff_nontrivial.mp
      (by rw [SmD6Grp.card_quotient_center_eq_nine hQ hnc]; norm_num)

theorem exp_three_of_inverting_involution {G : Type*} [Group G] {P : Subgroup G}
    (hP : Nat.card P = 27) {x a : G} (hx : x ∈ P) (hx3 : x ^ 3 = 1)
    (hxc : ∃ g ∈ P, g * x ≠ x * g) (ha2 : a * a = 1) (haP : ∀ g ∈ P, a * g * a⁻¹ ∈ P)
    (hax : a * x * a⁻¹ = x⁻¹) : ∀ y ∈ P, y ^ 3 = 1 := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨σ, hσ⟩ := SmD6Grp.exists_conj_hom a haP
  have hσσ : ∀ g : P, σ (σ g) = g := fun g => by
    apply Subtype.ext
    rw [hσ, hσ, hainv]
    calc a * (a * (g : G) * a) * a = (a * a) * (g : G) * (a * a) := by group
      _ = g := by rw [ha2]; group
  have hσx : σ ⟨x, hx⟩ = (⟨x, hx⟩ : P)⁻¹ := Subtype.ext (by rw [hσ]; simpa using hax)
  have hxc' : ∃ g : P, g * (⟨x, hx⟩ : P) ≠ (⟨x, hx⟩ : P) * g := by
    obtain ⟨g, hg, hne⟩ := hxc
    exact ⟨⟨g, hg⟩, fun h => hne (congrArg Subtype.val h)⟩
  have hx3' : (⟨x, hx⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  intro y hy
  simpa using congrArg Subtype.val (SmD6Grp.exp_three_of_inverting_aut hP hx3' hxc' σ hσσ hσx ⟨y, hy⟩)

theorem card_center_eq_three_of_card_27 {Q : Type*} [Group Q] (hQ : Nat.card Q = 27)
    (hnc : ∃ u v : Q, u * v ≠ v * u) : Nat.card (Subgroup.center Q) = 3 :=
  SmD6Grp.card_center_eq_three hQ hnc

theorem exp_three_of_dihedral_frame {G : Type*} [Group G] {P : Subgroup G}
    (hP : Nat.card P = 27) {x₀ x₁ a₀ a₁ : G} (hx₀ : x₀ ∈ P) (hx₁ : x₁ ∈ P)
    (hx₀3 : x₀ ^ 3 = 1) (hx₁3 : x₁ ^ 3 = 1) (hx₀1 : x₀ ≠ 1) (hne : x₁ ∉ Subgroup.zpowers x₀)
    (hnc : ∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) (_hcomm : x₀ * x₁ = x₁ * x₀)
    (ha₀ : a₀ * a₀ = 1) (ha₁ : a₁ * a₁ = 1)
    (haP₀ : ∀ g ∈ P, a₀ * g * a₀⁻¹ ∈ P) (haP₁ : ∀ g ∈ P, a₁ * g * a₁⁻¹ ∈ P)
    (hax₀ : a₀ * x₀ * a₀⁻¹ = x₀⁻¹) (hax₁ : a₁ * x₁ * a₁⁻¹ = x₁⁻¹) : ∀ y ∈ P, y ^ 3 = 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := hnc
  have hncP : ∃ u v : P, u * v ≠ v * u :=
    ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv (congrArg Subtype.val h)⟩
  by_cases h0 : ∃ g ∈ P, g * x₀ ≠ x₀ * g
  · exact exp_three_of_inverting_involution hP hx₀ hx₀3 h0 ha₀ haP₀ hax₀
  · refine exp_three_of_inverting_involution hP hx₁ hx₁3 ?_ ha₁ haP₁ hax₁
    by_contra h1
    apply hne
    have hz : (⟨x₀, hx₀⟩ : P) ∈ Subgroup.center P := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (by_contra fun h => h0 ⟨g, g.2, h⟩)
    have hw : (⟨x₁, hx₁⟩ : P) ∈ Subgroup.center P := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (by_contra fun h => h1 ⟨g, g.2, h⟩)
    have hz1 : (⟨x₀, hx₀⟩ : P) ≠ 1 := fun h => hx₀1 (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (SmD6Grp.mem_zpowers_of_mem_center hP hncP hz hz1 hw)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.Quasithin.SzN31
