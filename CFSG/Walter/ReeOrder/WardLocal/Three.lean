module

public import CFSG.Walter.ReeOrder.WardLocal.Block
public import CFSG.Walter.ReeOrder.WardLocal.Tools

public section

open scoped BigOperators Classical

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ}
  {S : WardSetup G L q (-1)} {D : S.EtaData} {m : ℕ} (B : Block S D m)

namespace Block

theorem three_part {k n : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hG : n = q ^ 3 * (q ^ 3 + 1) * (q - 1)) :
    3 ^ n.factorization 3 = q ^ 3 := by
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have h1 : ¬ 3 ∣ q ^ 3 + 1 := by
    rw [hq, ← pow_mul]
    intro h
    have : 3 ∣ 3 ^ ((2 * k + 1) * 3) := dvd_pow_self 3 (by positivity)
    omega
  have h2 : ¬ 3 ∣ q - 1 := by
    rw [hq]
    intro h
    have : 3 ∣ 3 ^ (2 * k + 1) := dvd_pow_self 3 (by positivity)
    have h3 : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hc : Nat.Coprime 3 ((q ^ 3 + 1) * (q - 1)) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h1)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h2)
  have hq0 : 0 < q - 1 := by
    rw [hq]
    have : 3 ≤ 3 ^ (2 * k + 1) := Nat.le_self_pow (by omega) 3
    omega
  have hnot : ¬ 3 ∣ (q ^ 3 + 1) * (q - 1) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc h
  rw [hG, mul_assoc, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (n := (q ^ 3 + 1) * (q - 1)) hnot, add_zero, hq,
    ← pow_mul, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]

theorem irr_2 : B.ξ₂ ∈ BlocksIrr G := (mem_supp.mp (show B.ξ₂ ∈ S.S1 by rw [B.hS1]; simp)).1
theorem irr_3 : B.ξ₃ ∈ BlocksIrr G := (mem_supp.mp (show B.ξ₃ ∈ S.S1 by rw [B.hS1]; simp)).1
theorem irr_4 : B.ξ₄ ∈ BlocksIrr G := (mem_supp.mp (show B.ξ₄ ∈ S.S1 by rw [B.hS1]; simp)).1

theorem sum_S1 {M : Type*} [AddCommMonoid M] (f : (G → ℂ) → M) :
    ∑ χ ∈ S.S1, f χ = f 1 + f B.ξ₂ + f B.ξ₃ + f B.ξ₄ :=
  sum_four B.hS1 B.n12 B.n13 B.n14 B.n23 B.n24 B.n34 f

theorem col_d1 {x : G} (hx : Odd (orderOf x)) :
    1 - B.ξ₂ x + B.ξ₃ x - B.ξ₄ x = 0 := by
  have h := S.orth S.d1 (fun χ hχ => S.inner_Φ1 hχ) hx
  rw [sum_irr_eq_sum_of_vanish (supp_sub S.d1) _ (fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van1 hχ hnot]; simp)] at h
  rw [show supp S.d1 = S.S1 from rfl, B.sum_S1, S.one_row.1, B.d1_2, B.d1_3, B.d1_4] at h
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_add, map_mul, map_neg, map_one, map_zero, Pi.one_apply, Int.cast_one,
    Int.cast_neg, RCLike.conj_conj] at h'
  linear_combination h'

include B in
theorem eta_eq_eta' {x : G} (hx : Odd (orderOf x)) (i : S.W.RFam) : D.η i x = D.η' i x := by
  have h := S.orth (S.dR · i.1) (fun χ hχ => S.hR_inner i.1 i.2 χ hχ) hx
  rw [D.sum_split] at h
  have h1 : ∑ j, ((S.dR (D.η j) i.1 : ℤ) : ℂ) * starRingEnd ℂ (D.η j x) =
      D.ε * starRingEnd ℂ (D.η i x) := by
    simp only [D.dR_η, apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h2 : ∑ j, ((S.dR (D.η' j) i.1 : ℤ) : ℂ) * starRingEnd ℂ (D.η' j x) =
      -D.ε' * starRingEnd ℂ (D.η' i x) := by
    simp only [D.dR_η', apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Int.cast_neg]
  have h3 : ∑ χ ∈ D.NE, ((S.dR χ i.1 : ℤ) : ℂ) * starRingEnd ℂ (χ x) = 0 := by
    refine Finset.sum_eq_zero fun χ hχ => ?_
    rw [D.dR_other (D.mem_NE.mp hχ).1 (D.NE_ne_η hχ) (D.NE_ne_η' hχ) i]
    simp
  rw [h1, h2, h3, B.ε_eq, ← (D.ε_eq_ε').1, B.ε_eq] at h
  have h' : starRingEnd ℂ (D.η i x) = starRingEnd ℂ (D.η' i x) := by
    push_cast at h; linear_combination h
  exact (starRingEnd ℂ).injective h'

variable {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
include hq hG

theorem xi3_eq_zero {A : G} (h3 : 3 ∣ orderOf A) : B.ξ₃ A = 0 := by
  have hI : B.ξ₃ ∈ BlocksIrr G := (mem_supp.mp (show B.ξ₃ ∈ S.S1 by rw [B.hS1]; simp)).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine defect_zero_vanish hI 3 ?_ h3
  rw [three_part hq hG, B.deg_3]
  push_cast
  exact dvd_rfl

omit hG in
theorem not_Kset {x : G} (hx : Odd (orderOf x)) (h3 : 3 ∣ orderOf x) (a : G) :
    a⁻¹ * x * a ∉ S.Kset := by
  rintro ⟨y, ⟨g, hg, hg1⟩, h | h⟩
  · have hord : orderOf x = orderOf (g⁻¹ * y * g) := by
      rw [show orderOf (g⁻¹ * y * g) = orderOf y by
          rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by group, ← MulAut.conj_apply,
            MulEquiv.orderOf_eq],
        ← S.orderOf_κ y, ← h, show a⁻¹ * x * a = a⁻¹ * x * a⁻¹⁻¹ by group, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq]
    have hdvd : orderOf (g⁻¹ * y * g) ∣ Nat.card S.W.Ro := by
      rw [← Subgroup.orderOf_mk _ hg]
      exact orderOf_dvd_natCard _
    have hR := S.W.Ro_card
    have h3R : 3 ∣ Nat.card S.W.Ro := hord ▸ h3 |>.trans hdvd
    have hqm : (q : ℤ) % 8 = 3 := by have := S.W.q_mod; omega
    obtain ⟨t, ht⟩ := hq ▸ (show 3 ∣ (3 : ℕ) ^ (2 * k + 1) from dvd_pow_self 3 (by omega))
    omega
  · have hy : Odd (orderOf y) := by
      have h1 : Odd (orderOf (g⁻¹ * y * g)) := S.orderOf_Ro_odd hg
      rwa [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by group, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq] at h1
    have h1 : orderOf (a⁻¹ * x * a) = orderOf x := by
      rw [show a⁻¹ * x * a = a⁻¹ * x * a⁻¹⁻¹ by group, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq]
    rw [h, S.orderOf_J_mul hy] at h1
    rw [← h1] at hx
    exact (Nat.not_even_iff_odd.mpr hx) (even_two_mul _)

theorem eta_eq_one {x : G} (hx : Odd (orderOf x)) (h3 : 3 ∣ orderOf x) (i : S.W.RFam) :
    D.η i x = 1 ∧ D.η' i x = 1 ∧ B.ξ₂ x + B.ξ₄ x = 1 := by
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have hconst : ∀ j, D.η j x = D.η i x := fun j => D.val x (not_Kset hq hx h3) j i
  have hcol := sum_irr_mul_conj x (S.κ r)
  have hnc : ¬ IsConj x (S.κ r) := by
    intro hc
    have ho : orderOf x = orderOf r := by
      rw [← S.orderOf_κ r]
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      rw [← hc, show c * x * c⁻¹ = c * x * c⁻¹ from rfl, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq]
    have hdvd : orderOf r ∣ Nat.card S.W.Ro := by
      rw [← Subgroup.orderOf_mk _ hr]
      exact orderOf_dvd_natCard _
    have hR := S.W.Ro_card
    have h3R : 3 ∣ Nat.card S.W.Ro := (ho ▸ h3).trans hdvd
    obtain ⟨t, ht⟩ := hq ▸ (show 3 ∣ (3 : ℕ) ^ (2 * k + 1) from dvd_pow_self 3 (by omega))
    omega
  simp only [hnc, ↓reduceIte] at hcol
  rw [D.sum_split] at hcol
  have hθ : ∀ j : S.W.RFam, starRingEnd ℂ (j.1 r) = j.1 r := fun j => by
    have := congrFun (S.W.conj_R j.1 j.2) r
    simpa using this
  have hsumθ : ∑ j : S.W.RFam, j.1 r = -1 := by
    rw [Finset.sum_coe_sort S.W.RFam (fun θ => θ r), S.W.sum_R_Ro hr hr1]
    simp
  have hτ : ∀ j, D.η j (S.κ r) = D.ε * j.1 r := fun j => WardSetup.EtaData.τ_η_eq D j hr hr1
  have hτ' : ∀ j, D.η' j (S.κ r) = D.ε * j.1 r :=
    fun j => WardSetup.EtaData.τ_η'_eq D j hr hr1
  have e1 : ∑ j, D.η j x * starRingEnd ℂ (D.η j (S.κ r)) = -D.η i x := by
    simp only [hτ, B.ε_eq, Int.cast_one, one_mul, hθ, hconst]
    rw [← Finset.mul_sum, hsumθ, mul_neg_one]
  have e2 : ∑ j, D.η' j x * starRingEnd ℂ (D.η' j (S.κ r)) = -D.η i x := by
    simp only [hτ', B.ε_eq, Int.cast_one, one_mul, hθ, ← B.eta_eq_eta' hx, hconst]
    rw [← Finset.mul_sum, hsumθ, mul_neg_one]
  have e3 : ∑ χ ∈ D.NE, χ x * starRingEnd ℂ (χ (S.κ r)) = 1 + B.ξ₂ x + B.ξ₃ x + B.ξ₄ x := by
    have hsub : S.S1 ⊆ D.NE := fun χ hχ => D.S1_NE hχ
    rw [← Finset.sum_subset hsub (fun χ hχ hnot => by
      rw [D.τ_NE hχ hr hr1, D.z_off hχ hnot]; simp)]
    rw [B.sum_S1]
    simp only [D.τ_NE (D.S1_NE (show (1 : G → ℂ) ∈ S.S1 from S.one_S1)) hr hr1,
      D.τ_NE (D.S1_NE (show B.ξ₂ ∈ S.S1 by rw [B.hS1]; simp)) hr hr1,
      D.τ_NE (D.S1_NE (show B.ξ₃ ∈ S.S1 by rw [B.hS1]; simp)) hr hr1,
      D.τ_NE (D.S1_NE (show B.ξ₄ ∈ S.S1 by rw [B.hS1]; simp)) hr hr1,
      WardSetup.EtaData.z_one (S := S), B.z_2, B.z_3, B.z_4]
    simp
  rw [e1, e2, e3, B.xi3_eq_zero hq hG h3] at hcol
  have hd1 := B.col_d1 hx
  rw [B.xi3_eq_zero hq hG h3] at hd1
  have h24 : B.ξ₂ x + B.ξ₄ x = 1 := by linear_combination -hd1
  have hη : D.η i x = 1 := by linear_combination (-1 / 2 : ℂ) * hcol + (1 / 2 : ℂ) * h24
  exact ⟨hη, by rw [← B.eta_eq_eta' hx]; exact hη, h24⟩

omit hq in
theorem r_part {r : ℕ} [hr : Fact r.Prime] (hrR : r ∣ Nat.card S.W.Ro) :
    r ^ (Nat.card G).factorization r ∣ Nat.card S.W.Ro := by
  have hR := S.W.Ro_card
  have hq27 := S.q_ge
  have hRo : 2 * Nat.card S.W.Ro = q - 1 := by omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    have := S.Ro_odd
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr hrR)
  have hrq1 : r ∣ q - 1 := hRo ▸ dvd_mul_of_dvd_right hrR 2
  have hrq : ¬ r ∣ q := by
    intro h
    have h1 : r ∣ q - (q - 1) := Nat.dvd_sub h hrq1
    rw [show q - (q - 1) = 1 by omega] at h1
    exact hr.out.one_lt.ne' (Nat.dvd_one.mp h1)
  have hrq3 : ¬ r ∣ q ^ 3 + 1 := by
    intro h
    obtain ⟨t, ht⟩ := hrq1
    have hq' : q = r * t + 1 := by omega
    rw [hq'] at h
    have : r ∣ 2 := by
      have h2 : (r * t + 1) ^ 3 + 1 = r * (r ^ 2 * t ^ 3 + 3 * r * t ^ 2 + 3 * t) + 2 := by ring
      rw [h2] at h
      exact (Nat.dvd_add_right (dvd_mul_right r _)).mp h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).mp this)
  have hfac : (Nat.card G).factorization r = (Nat.card S.W.Ro).factorization r := by
    rw [hG, Nat.factorization_mul (by positivity) (by omega), Nat.factorization_mul
      (by positivity) (by positivity), Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hrq (hr.out.dvd_of_dvd_pow h)),
      Nat.factorization_eq_zero_of_not_dvd hrq3, zero_add, zero_add, ← hRo,
      Nat.factorization_mul (by norm_num) (by have := Nat.card_pos (α := S.W.Ro); omega),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun h => hr2
        ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).mp h)), zero_add]
  rw [hfac]
  exact Nat.ordProj_dvd _ _

omit hq in
theorem exists_conj_Ro {y : G} {r : ℕ} [hr : Fact r.Prime] (hy : orderOf y = r)
    (hrR : r ∣ Nat.card S.W.Ro) : ∃ g : G, ∃ ρ ∈ S.W.Ro, ρ ≠ 1 ∧ g⁻¹ * y * g = S.κ ρ := by
  have hH : r ^ (Nat.card G).factorization r ∣ Nat.card (S.W.Ro.map S.κ) := by
    rw [Subgroup.card_map_of_injective S.κ_inj]
    exact r_part hG hrR
  have hp : IsPGroup r (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hy, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_full _ hH hp
  obtain ⟨ρ, hρ, hρy⟩ := Subgroup.mem_map.mp hg
  refine ⟨g, ρ, hρ, ?_, hρy.symm⟩
  rintro rfl
  rw [map_one] at hρy
  have : y = 1 := by
    have h1 : g⁻¹ * y * g = 1 := hρy.symm
    have := congrArg (fun t => g * t * g⁻¹) h1
    simpa [mul_assoc] using this
  rw [this, orderOf_one] at hy
  exact hr.out.one_lt.ne hy

include B in
theorem card_centralizer_dvd {x : G} (hx : Odd (orderOf x)) (h3 : 3 ∣ orderOf x) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * q ^ 3 := by
  obtain ⟨i⟩ : Nonempty S.W.RFam := by
    have := WardSetup.EtaData.card_ge (S := S)
    exact Fintype.card_pos_iff.mp (by omega)
  have hη := (B.eta_eq_one hq hG hx h3 i).1
  have hdvd := omega_dvd (D.mem i) x (t := 1) (by rw [hη]; simp)
  have hdeg : deg (D.η i) = (q : ℤ) ^ 3 + 1 := by
    rw [← B.dη_eq]
    have h1 := D.η_one i
    have h2 := deg_eq (D.mem i)
    rw [h1] at h2
    exact_mod_cast h2
  rw [hdeg, mul_one] at hdvd
  have hcls := card_conjClass_mul_card_centralizer x
  set c := Nat.card (Subgroup.centralizer ({x} : Set G)) with hc
  have hq1 : 1 ≤ q := by have := S.q_ge; omega
  have hdvd' : q ^ 3 + 1 ∣ Nat.card (ConjClasses.mk x).carrier := by exact_mod_cast hdvd
  obtain ⟨t, ht⟩ := hdvd'
  have hct : c * t = q ^ 3 * (q - 1) := by
    have h1 : (q ^ 3 + 1) * (t * c) = (q ^ 3 + 1) * (q ^ 3 * (q - 1)) := by
      rw [← mul_assoc, ← ht, hcls, hG]; ring
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    linarith
  have hR := S.W.Ro_card
  have hq27 := S.q_ge
  have hRo : q - 1 = 2 * Nat.card S.W.Ro := by omega
  have hcop : Nat.Coprime c (Nat.card S.W.Ro) := by
    apply Nat.coprime_of_dvd
    intro r hr hrc hrR
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set G))
      r hrc
    obtain ⟨g, ρ, hρ, hρ1, hg⟩ := exists_conj_Ro hG (y := (y : G))
      (by rw [Subgroup.orderOf_coe]; exact hy) hrR
    have hcomm : (g⁻¹ * x * g) * S.κ ρ = S.κ ρ * (g⁻¹ * x * g) := by
      have hyx : (y : G) * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp y.2
      rw [← hg]
      calc g⁻¹ * x * g * (g⁻¹ * ↑y * g) = g⁻¹ * (x * y) * g := by group
        _ = g⁻¹ * (y * x) * g := by rw [hyx]
        _ = g⁻¹ * ↑y * g * (g⁻¹ * x * g) := by group
    have hmem : g⁻¹ * x * g ∈ Subgroup.centralizer ({S.κ ρ} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hord : orderOf (g⁻¹ * x * g) ∣ Nat.card (Subgroup.centralizer ({S.κ ρ} : Set G)) := by
      rw [← Subgroup.orderOf_mk _ hmem]
      exact orderOf_dvd_natCard _
    rw [S.card_centralizer_κR hρ hρ1, S.W.Ro_centralizer ρ hρ hρ1] at hord
    have hox : orderOf (g⁻¹ * x * g) = orderOf x := by
      rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq]
    rw [hox] at hord
    have h3' : 3 ∣ 2 * Nat.card S.W.Ro := h3.trans hord
    obtain ⟨t', ht'⟩ := hq ▸ (show 3 ∣ (3 : ℕ) ^ (2 * k + 1) from dvd_pow_self 3 (by omega))
    omega
  have hc2 : c ∣ q ^ 3 * 2 * Nat.card S.W.Ro := by
    rw [mul_assoc, ← hRo, ← hct]; exact dvd_mul_right c t
  have := hcop.dvd_of_dvd_mul_right hc2
  rwa [mul_comm] at this

end Block

end CFSG.Walter.WardLocal
