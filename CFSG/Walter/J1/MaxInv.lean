module

public import CFSG.Walter.J1.Complement
public import CFSG.Walter.J1.Signalizer

public section

namespace CFSG.Walter.J1

variable {G : Type*} [Group G]

@[expose] def IsFour (a b : G) : Prop :=
  orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a

@[expose] def IsInv (a b : G) (M : Subgroup G) : Prop :=
  Odd (Nat.card M) ∧ a ∈ Subgroup.normalizer (M : Set G) ∧ b ∈ Subgroup.normalizer (M : Set G)

@[expose] def IsMaxInv (a b : G) (M : Subgroup G) : Prop :=
  IsInv a b M ∧ ∀ M' : Subgroup G, IsInv a b M' → M ≤ M' → M' = M

namespace IsFour

variable {a b : G}

theorem mul_self_a (hT : IsFour a b) : a * a = 1 := (orderOf_eq_two_iff.mp hT.1).1

theorem mul_self_b (hT : IsFour a b) : b * b = 1 := (orderOf_eq_two_iff.mp hT.2.1).1

theorem a_ne_one (hT : IsFour a b) : a ≠ 1 := (orderOf_eq_two_iff.mp hT.1).2

theorem b_ne_one (hT : IsFour a b) : b ≠ 1 := (orderOf_eq_two_iff.mp hT.2.1).2

theorem mul_ne_one (hT : IsFour a b) : a * b ≠ 1 := by
  intro h1
  apply hT.2.2.1
  rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hT.mul_self_a]

theorem mul_ne_a (hT : IsFour a b) : a * b ≠ a := fun h1 => hT.b_ne_one (by simpa using h1)

theorem mul_ne_b (hT : IsFour a b) : a * b ≠ b := fun h1 => hT.a_ne_one (by simpa using h1)

theorem mul_self_mul (hT : IsFour a b) : a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hT.2.2.2]
    _ = 1 := by rw [← mul_assoc, hT.mul_self_a, one_mul, hT.mul_self_b]

theorem orderOf_mul (hT : IsFour a b) : orderOf (a * b) = 2 :=
  orderOf_eq_two_iff.mpr ⟨hT.mul_self_mul, hT.mul_ne_one⟩

theorem swap (hT : IsFour a b) : IsFour b a := ⟨hT.2.1, hT.1, hT.2.2.1.symm, hT.2.2.2.symm⟩

theorem a_mul_mul (hT : IsFour a b) : a * (a * b) = b := by
  rw [← mul_assoc, hT.mul_self_a, one_mul]

theorem b_mul_mul (hT : IsFour a b) : b * (a * b) = a := by
  rw [← mul_assoc, ← hT.2.2.2, mul_assoc, hT.mul_self_b, mul_one]

theorem mul_mul_a (hT : IsFour a b) : a * b * a = b := by
  rw [mul_assoc, ← hT.2.2.2, ← mul_assoc, hT.mul_self_a, one_mul]

theorem mul_right (hT : IsFour a b) : IsFour a (a * b) :=
  ⟨hT.1, hT.orderOf_mul, hT.mul_ne_a.symm, by rw [hT.a_mul_mul, hT.mul_mul_a]⟩

end IsFour

namespace IsInv

variable {a b : G} {M : Subgroup G}

theorem swap (hM : IsInv a b M) : IsInv b a M := ⟨hM.1, hM.2.2, hM.2.1⟩

theorem mul_right (hM : IsInv a b M) : IsInv a (a * b) M :=
  ⟨hM.1, hM.2.1, Subgroup.mul_mem _ hM.2.1 hM.2.2⟩

theorem of_mul_right (hT : IsFour a b) (hM : IsInv a (a * b) M) : IsInv a b M :=
  ⟨hM.1, hM.2.1, by rw [← hT.a_mul_mul]; exact Subgroup.mul_mem _ hM.2.1 hM.2.2⟩

theorem mul_mem (hM : IsInv a b M) : a * b ∈ Subgroup.normalizer (M : Set G) :=
  Subgroup.mul_mem _ hM.2.1 hM.2.2

end IsInv

namespace IsMaxInv

variable {a b : G} {M : Subgroup G}

theorem swap (hM : IsMaxInv a b M) : IsMaxInv b a M :=
  ⟨hM.1.swap, fun M' hM' hle => hM.2 M' hM'.swap hle⟩

theorem mul_right (hT : IsFour a b) (hM : IsMaxInv a b M) : IsMaxInv a (a * b) M :=
  ⟨hM.1.mul_right, fun M' hM' hle => hM.2 M' (hM'.of_mul_right hT) hle⟩

end IsMaxInv

theorem exists_isMaxInv [Finite G] {a b : G} {M₀ : Subgroup G} (hM₀ : IsInv a b M₀) :
    ∃ M, M₀ ≤ M ∧ IsMaxInv a b M := by
  have hfin : ({M : Subgroup G | IsInv a b M} : Set (Subgroup G)).Finite := Set.toFinite _
  obtain ⟨M, hM₀M, hmax⟩ := hfin.exists_le_maximal hM₀
  exact ⟨M, hM₀M, hmax.1, fun M' hM' hle => (hmax.2 hM' hle).antisymm hle⟩

theorem mem_normalizer_inf_centralizer [Finite G] {M : Subgroup G} {x y : G}
    (hyM : y ∈ Subgroup.normalizer (M : Set G)) (hxy : x * y = y * x) :
    y ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun z hz => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hyM z).mp hz.1
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    calc y * z * y⁻¹ * x = y * z * (y⁻¹ * x) := by group
      _ = y * z * (x * y⁻¹) := by
        rw [show y⁻¹ * x = x * y⁻¹ by
          calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
            _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hxy]
            _ = x * y⁻¹ := by group]
      _ = y * (z * x) * y⁻¹ := by group
      _ = y * (x * z) * y⁻¹ := by rw [hzx]
      _ = (y * x) * z * y⁻¹ := by group
      _ = x * (y * z * y⁻¹) := by rw [← hxy]; group

theorem kleinFour_le_normalizer {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsInv a b M) :
    GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b hT.2.2.2 ≤
      Subgroup.normalizer (M : Set G) := by
  intro x hx
  rcases (mem_kleinFour_iff hT.mul_self_a hT.mul_self_b hT.2.2.2).mp hx with
    rfl | rfl | rfl | rfl
  · exact hM.mul_mem
  · exact hM.2.1
  · exact hM.2.2
  · exact Subgroup.one_mem _

theorem maxInv_of_complement [Finite G] {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsMaxInv a b M) {X : Subgroup G} (hX : IsInv a b X)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) {O : Subgroup G}
    (hOK : O ≤ Subgroup.normalizer (X : Set G))
    (hON : (O.subgroupOf (Subgroup.normalizer (X : Set G))).Normal) (hO2 : ¬ 2 ∣ Nat.card O)
    (hOcard : Nat.card O * 4 = Nat.card (Subgroup.normalizer (X : Set G)))
    (hOodd : ∀ g ∈ Subgroup.normalizer (X : Set G), Odd (orderOf g) → g ∈ O) :
    (∀ g ∈ Subgroup.normalizer (X : Set G), Odd (orderOf g) → g ∈ M) ∧
      ∀ g ∈ Subgroup.normalizer (X : Set G), ∃ m ∈ M, ∃ s : G,
        (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) ∧ g = m * s := by
  classical
  set K := Subgroup.normalizer (X : Set G)
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b
    hT.2.2.2
  have hT4 : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one hT.2.2.1 _
  have hOinv : IsInv a b O := by
    have hnorm : ∀ s ∈ K, s ∈ Subgroup.normalizer (O : Set G) := by
      intro s hs
      refine mem_normalizer_of_conj_mem fun x hx => ?_
      have := hON.conj_mem ⟨x, hOK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨s, hs⟩
      simpa [Subgroup.mem_subgroupOf] using this
    refine ⟨Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hO2), hnorm a hX.2.1, hnorm b hX.2.2⟩
  have hMO : M ≤ O := fun m hm =>
    hOodd m (hMX hm) (Odd.of_dvd_nat hM.1.1 (Subgroup.orderOf_dvd_natCard M hm))
  have hOM : O = M := hM.2 O hOinv hMO
  subst hOM
  refine ⟨hOodd, fun g hg => ?_⟩
  have hTM : T ≤ Subgroup.normalizer (O : Set G) := kleinFour_le_normalizer hT hM.1
  have hdisj : Disjoint O T := by
    rw [Subgroup.disjoint_def]
    intro x hxO hxT
    have h1 : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    have h2 : orderOf x ∣ 4 := hT4.card_four ▸ Subgroup.orderOf_dvd_natCard T hxT
    have hcop : Nat.Coprime (Nat.card O) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr
        (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hO2))) |>.symm.symm |> fun h => by
          simpa using h
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1
      hcop) h2)
  have hsup : O ⊔ T = K := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hOK (fun x hx => by
      rcases (mem_kleinFour_iff hT.mul_self_a hT.mul_self_b hT.2.2.2).mp hx with
        rfl | rfl | rfl | rfl
      · exact hX.mul_mem
      · exact hX.2.1
      · exact hX.2.2
      · exact Subgroup.one_mem _))
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O T hTM hdisj,
      hT4.card_four, hOcard]
  have hgOT : g ∈ ((O ⊔ T : Subgroup G) : Set G) := by rw [hsup]; exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O T hTM] at hgOT
  obtain ⟨m, hm, s, hs, rfl⟩ := hgOT
  refine ⟨m, hm, s, ?_, rfl⟩
  rcases (mem_kleinFour_iff hT.mul_self_a hT.mul_self_b hT.2.2.2).mp hs with
    rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem inf_centralizer_four_eq_bot {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : Odd (Nat.card M)) :
    M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  exact h.eq_one_of_commute_four hT.1 hT.2.1 hT.2.2.1 hT.2.2.2
    (Odd.of_dvd_nat hM (Subgroup.orderOf_dvd_natCard M hy.1.1))
    (Subgroup.mem_centralizer_singleton_iff.mp hy.1.2)
    (Subgroup.mem_centralizer_singleton_iff.mp hy.2)

include h in
theorem card_eq_mul {a b : G} (hT : IsFour a b) {M : Subgroup G} (hM : IsInv a b M) :
    Nat.card M = Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
      Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) *
      Nat.card (M ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) := by
  have hBW := card_mul_card_sq_eq_mul hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one
    hT.2.2.1 hT.2.2.2 M hM.2.1 hM.2.2 hM.1
  rw [h.inf_centralizer_four_eq_bot hT hM.1, Subgroup.card_bot, one_pow, mul_one] at hBW
  exact hBW

include h in
theorem card_inf_centralizer {x : G} (hx : orderOf x = 2) {M : Subgroup G}
    (hM : Odd (Nat.card M)) :
    Nat.card (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 1 ∨
      Nat.card (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 3 ∨
      Nat.card (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 5 := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hx
  have hodd : Odd (Nat.card (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) :=
    Odd.of_dvd_nat hM (Subgroup.card_dvd_of_le inf_le_left)
  have hle := (h.conj g).le_F_of_odd (K := M ⊓ Subgroup.centralizer ({x} : Set G))
    (by rw [hg]; exact inf_le_right) hodd
  exact A5Sub.card_odd (h.conj g).iso hle hodd

theorem commute_of_inf_eq_bot {x : G} (hx : x * x = 1) {M : Subgroup G}
    (hxM : x ∈ Subgroup.normalizer (M : Set G))
    (hM : M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) :
    ∀ y ∈ M, ∀ z ∈ M, y * z = z * y := by
  intro y hy z hz
  have := le_centralizer_of_inv (inv_of_inf_centralizer_eq_bot hx hxM hM) hy
  exact (Subgroup.mem_centralizer_iff.mp this z hz).symm

include h in
theorem maxInv_normalizer {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsMaxInv a b M) {X : Subgroup G} (hX : IsInv a b X)
    (hXa : X ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥)
    (hXab : X ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) :
    (∀ g ∈ Subgroup.normalizer (X : Set G), Odd (orderOf g) → g ∈ M) ∧
      ∀ g ∈ Subgroup.normalizer (X : Set G), ∃ m ∈ M, ∃ s : G,
        (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) ∧ g = m * s := by
  classical
  set K := Subgroup.normalizer (X : Set G)
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b
    hT.2.2.2
  have hT4 : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one hT.2.2.1 _
  have hX1 : X ≠ ⊥ := fun h0 => hXa (by rw [h0, bot_inf_eq])
  obtain ⟨O, hOK, hON, hO2, hOcard, hOodd⟩ := exists_odd_complement_four (K := K)
    hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one hT.2.2.1 hT.2.2.2 hX.2.1 hX.2.2
    (by
      intro R hRK hR2 hTR
      have h4 := h.card_dvd_four_of_le_normalizer hX.1 hX1 hR2 hRK
      exact (Subgroup.eq_of_le_of_card_ge hTR (by
        rw [hT4.card_four]; exact Nat.le_of_dvd (by norm_num) h4)).symm)
    (fun z => X ⊓ Subgroup.centralizer ({z} : Set G) ≠ ⊥) hXa (by simpa using hXab)
    (by
      intro n hn z hz hcon
      apply hz
      rw [eq_bot_iff]
      intro y hy
      have hy' : n * y * n⁻¹ ∈ X ⊓ Subgroup.centralizer ({n * z * n⁻¹} : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn y).mp hy.1, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
        calc n * y * n⁻¹ * (n * z * n⁻¹) = n * (y * z) * n⁻¹ := by group
          _ = n * (z * y) * n⁻¹ := by rw [hyz]
          _ = n * z * n⁻¹ * (n * y * n⁻¹) := by group
      rw [hcon, Subgroup.mem_bot] at hy'
      rw [Subgroup.mem_bot]
      have := congrArg (fun w => n⁻¹ * w * n) hy'
      simpa [mul_assoc] using this)
  exact maxInv_of_complement hT hM hX hMX hOK hON hO2 hOcard hOodd

end JankoHyp

end CFSG.Walter.J1
