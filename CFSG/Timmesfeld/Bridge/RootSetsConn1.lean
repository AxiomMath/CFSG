module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Closure.MinCex

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

structure ConnCex (D : Set G) : Prop where
  setting : Setting D
  disc : Disconnected D
  simple : IsSimpleGroup G
  faith : ker setting.normal = ⊥
  m2 : ∀ L : Subgroup G, L ≠ ⊤ → ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → d ∈ L → e ∈ L →
    L ≤ compStab setting.normal d

namespace ConnCex

variable (hC : ConnCex D)
include hC

theorem isClass : ∃ d₀ : G, D = {g | IsConj d₀ g} := by
  obtain ⟨d, hd, -⟩ := hC.setting.nondeg
  refine ⟨d, Set.ext fun g => ⟨fun hg => isConj_of_disconnected hC.setting.root hC.disc hd hg,
    fun hg => ?_⟩⟩
  obtain ⟨h, rfl⟩ := isConj_iff.1 hg
  exact hC.setting.normal h d hd

theorem reach_of_special {x y : G} (hx : x ∈ D) (hy : y ∈ D) (h4 : orderOf (x * y) = 4) :
    Reach D x y := by
  by_contra h
  obtain ⟨-, hodd⟩ := opposite_of_not_reach hC.setting.root hx hy h
  rw [h4] at hodd
  exact absurd hodd (by decide)

theorem reach_of_orderOf_dvd_four {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (h : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 4) : Reach D x y := by
  have hD := hC.setting.root
  rcases h with h | h | h
  · rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq hy] at h
    rw [h]
    exact reach_refl y
  · refine reach_of_commute hx hy ?_
    rw [commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hy), ← h]
    exact pow_orderOf_eq_one _
  · exact hC.reach_of_special hx hy h

theorem mul_mul_self_of_commute {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hc : Commute a b) :
    a * b * (a * b) = 1 := by
  have hD := hC.setting.root
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hc.eq]
    _ = 1 := by rw [← mul_assoc, hD.mul_self_eq_one ha, one_mul, hD.mul_self_eq_one hb]

theorem mul_ne_one_of_ne {a b : G} (hb : b ∈ D) (hab : a ≠ b) : a * b ≠ 1 := by
  intro h
  apply hab
  have := eq_inv_of_mul_eq_one_left h
  rwa [hC.setting.root.inv_eq hb] at this

theorem exists_thirdKind {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) (hc : Commute a b)
    (hnD : a * b ∉ D) :
    ∃ x ∈ D, ¬ Reach D a x ∧ ∃ n : ℕ, Odd n ∧ orderOf (x * (a * b)) = 2 * n := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hclass := hC.isClass
  by_contra hno
  push Not at hno
  have hu2 := hC.mul_mul_self_of_commute ha hb hc
  have hu1 := hC.mul_ne_one_of_ne hb hab
  have hker : a * b ∈ ker hN := by
    rw [mem_ker_iff]
    intro y hy
    by_cases hay : Reach D a y
    · have h1 := reach_conj hN (a * b) hay
      have hua : a * b * a * (a * b)⁻¹ = a := by
        rw [((Commute.refl a).mul_left hc.symm).eq, mul_inv_cancel_right]
      rw [hua] at h1
      exact reach_trans (reach_symm hay) h1
    · have hyD' : a * b * y * (a * b)⁻¹ ∈ D := hN _ y hy
      have hsq : y * (a * b * y * (a * b)⁻¹) = (y * (a * b)) ^ 2 := by
        rw [inv_eq_of_mul_eq_one_right hu2, pow_two]
        group
      rcases Nat.even_or_odd (orderOf (y * (a * b))) with ⟨m, hm⟩ | hodd
      · have hm0 : 0 < orderOf (y * (a * b)) := orderOf_pos _
        have hord2 : orderOf ((y * (a * b)) ^ 2) = m := by
          rw [orderOf_pow' _ two_ne_zero, hm, Nat.gcd_eq_right ⟨m, by ring⟩]
          omega
        have hmeven : ¬ Odd m := fun hmo => hno y hy hay m hmo (by omega)
        apply hC.reach_of_orderOf_dvd_four hy hyD'
        rw [hsq, hord2]
        have hroot := hD.orderOf_mul hy hyD'
        rw [hsq, hord2] at hroot
        rcases hroot with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h hmeven
      · exact absurd (mem_of_odd_orderOf_mul hclass hD hy hu2 hodd) hnD
  rw [hC.faith, Subgroup.mem_bot] at hker
  exact hu1 hker

theorem thirdKind_commute {a b x : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hc : Commute a b) (hx : x ∈ D) (hax : ¬ Reach D a x) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * (a * b)) = 2 * n) :
    (x * (a * b)) ^ n * (a * b) ∈ D ∧ Reach D a ((x * (a * b)) ^ n * (a * b)) ∧
      Commute ((x * (a * b)) ^ n * (a * b)) a ∧ Commute ((x * (a * b)) ^ n * (a * b)) b := by
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hclass := hC.isClass
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hx2 := hD.mul_self_eq_one hx
  have hu2 := hC.mul_mul_self_of_commute ha hb hc
  have hu1 := hC.mul_ne_one_of_ne hb hab
  set u := a * b with hu
  set r := x * u with hr
  set z := r ^ n with hz
  set c := z * u with hcdef
  clear_value c z r u
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hxinv : x⁻¹ = x := hD.inv_eq hx
  have hou : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two, hu2]) hu1
  have hau : Commute a u := by
    rw [hu]
    exact (Commute.refl a).mul_right hc
  have hbu : Commute b u := by
    rw [hu]
    exact hc.symm.mul_right (Commute.refl b)
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, huinv, hxinv, ← mul_assoc, hx2, one_mul]
  have hr2n : r ^ (2 * n) = 1 := by rw [← hord]; exact pow_orderOf_eq_one r
  have hz2 : z * z = 1 := by rw [hz, ← pow_add, ← two_mul, hr2n]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hn0 : 0 < n := hn.pos
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz] at h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd hn0 hdvd
    omega
  have hoz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two, hz2]) hz1
  have hxz : Commute x z := by
    have h1 : x * z * x⁻¹ = z := by
      rw [hz, ← conj_pow, hxr, inv_pow, ← hz, hzinv]
    show x * z = z * x
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h1]
  have hrz : Commute r z := by
    rw [hz]
    exact Commute.self_pow r n
  have hux : u = x * r := by rw [hr, ← mul_assoc, hx2, one_mul]
  have huz : Commute u z := by
    rw [hux]
    exact hxz.mul_left hrz
  have hc2 : c * c = 1 := by
    have e : c * c = z * z * (u * u) := by
      rw [hcdef, mul_assoc, ← mul_assoc u z u, huz.eq]
      simp only [mul_assoc]
    rw [e, hz2, hu2, one_mul]
  have hxc : x * c = r ^ (n + 1) := by
    rw [hcdef, ← mul_assoc, hxz.eq, mul_assoc, ← hr, hz, ← pow_succ]
  have hxc_pow : (x * c) ^ n = 1 := by
    obtain ⟨j, hj⟩ := hn
    rw [hxc, ← pow_mul, show (n + 1) * n = 2 * n * (j + 1) by rw [hj]; ring, pow_mul, hr2n,
      one_pow]
  have hoddxc : Odd (orderOf (x * c)) := hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxc_pow)
  have hcD : c ∈ D := mem_of_odd_orderOf_mul hclass hD hx hc2 hoddxc
  have hcu : Commute c u := by
    rw [hcdef]
    exact huz.symm.mul_left (Commute.refl u)
  have hcz : Commute c z := by
    rw [hcdef]
    exact (Commute.refl z).mul_left huz
  have hac : Reach D a c := by
    by_contra hnr
    obtain ⟨hnc, hodd⟩ := opposite_of_not_reach hD ha hcD hnr
    have hcb : c * b = c * a * u := by
      rw [hu, mul_assoc c a, ← mul_assoc a a b, ha2, one_mul]
    have hoddca : Odd (orderOf (c * a)) := by
      rw [show c * a = (a * c)⁻¹ by rw [mul_inv_rev, hD.inv_eq hcD, hD.inv_eq ha], orderOf_inv]
      exact hodd
    have h2 := orderOf_mul_eq_two_mul_of_odd (hcu.mul_left hau) hoddca hou
    rw [← hcb] at h2
    rcases hD.orderOf_mul hcD hb with h | h | h
    · have h1 : orderOf (c * a) = 1 := by omega
      rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq ha] at h1
      exact hnc (by rw [h1])
    · have h1 : orderOf (c * a) = 2 := by omega
      rw [h1] at hoddca
      exact absurd hoddca (by decide)
    · rw [h2] at h
      exact (Nat.not_even_iff_odd.2 h) (even_two_mul _)
  have hca : Commute c a := by
    by_contra hnca
    have hab' : a = b * u := by rw [hu, ← mul_assoc, ← hc.eq, mul_assoc, hb2, mul_one]
    have hba' : b = a * u := by rw [hu, ← mul_assoc, ha2, one_mul]
    have hncb : ¬ Commute c b := fun h => hnca (by rw [hab']; exact h.mul_right hcu)
    have hspec : ∀ y w : G, y ∈ D → w ∈ D → Commute y u → w = y * u → ¬ Commute c y →
        orderOf (c * y) = 4 := by
      intro y w hy hw hyu hwy hncy
      rcases commute_or_orderOf_mul_eq_four_or_odd hD hcD hy with h | h | ⟨hodd, -⟩
      · exact absurd h hncy
      · exact h
      · exfalso
        have h2 := orderOf_mul_eq_two_mul_of_odd (hcu.mul_left hyu) hodd hou
        rw [mul_assoc, ← hwy] at h2
        have hy1 : orderOf (c * y) ≠ 1 := fun h1 => hncy (by
          rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq hy] at h1
          rw [h1])
        rcases hD.orderOf_mul hcD hw with h' | h' | h'
        · omega
        · have h3 : orderOf (c * y) = 2 := by omega
          rw [h3] at hodd
          exact absurd hodd (by decide)
        · rw [h2] at h'
          exact (Nat.not_even_iff_odd.2 h') (even_two_mul _)
    have h4b : orderOf (c * b) = 4 := hspec b a hb ha hbu hab' hncb
    obtain ⟨hdD, hcd, -, -⟩ := sq_mem_of_orderOf_eq_four hD hcD hb h4b
    set d := (c * b) ^ 2 with hd
    have hzc : z = c * u := by rw [hcdef, mul_assoc, hu2, mul_one]
    have hucb : Commute u (c * b) := hcu.symm.mul_right hbu.symm
    have h1 : z * (c * b) * z⁻¹ = (c * b)⁻¹ := by
      rw [hzc, show c * u * (c * b) * (c * u)⁻¹ = c * (u * (c * b) * u⁻¹) * c⁻¹ by group,
        hucb.eq, mul_inv_cancel_right, mul_inv_rev, hD.inv_eq hcD, hD.inv_eq hb]
      calc c * (c * b) * c = c * c * b * c := by group
        _ = b * c := by rw [hc2, one_mul]
    have hzd : Commute z d := by
      have h2 : z * d * z⁻¹ = d := by
        rw [hd, ← conj_pow, h1, inv_pow, ← hd, hD.inv_eq hdD]
      show z * d = d * z
      calc z * d = z * d * z⁻¹ * z := by group
        _ = d * z := by rw [h2]
    have hdx : ¬ Reach D d x := fun h =>
      hax (reach_trans (reach_trans hac (reach_of_commute hcD hdD hcd)) h)
    obtain ⟨-, hodd_dx⟩ := opposite_of_not_reach hD hdD hx hdx
    obtain ⟨g, hg, hgd⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hdD) hx2 hodd_dx
    obtain ⟨h, hh, hhx⟩ := exists_conj_of_odd_orderOf_mul hx2 hc2 hoddxc
    have hcen : ∀ y w : G, Commute y z → Commute w z →
        ∀ k ∈ Subgroup.closure ({y, w} : Set G), Commute k z := by
      intro y w hy hw k hk
      have hle : Subgroup.closure ({y, w} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.closure_le]
        rintro t (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 hy.eq
        · exact Subgroup.mem_centralizer_singleton_iff.2 hw.eq
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
    have hgz : Commute g z := hcen d x hzd.symm hxz g hg
    have hhz : Commute h z := hcen x c hxz hcz h hh
    set k := h * g with hk
    have hkd : k * d * k⁻¹ = c := by
      rw [hk, show h * g * d * (h * g)⁻¹ = h * (g * d * g⁻¹) * h⁻¹ by group, hgd, hhx]
    have hkz : Commute k z := hhz.mul_left hgz
    have hcz' : c * z = u := by rw [hzc, ← mul_assoc, hc2, one_mul]
    have hdz : k * (d * z) * k⁻¹ = u := by
      rw [show k * (d * z) * k⁻¹ = k * d * k⁻¹ * (k * z * k⁻¹) by group, hkd, hkz.eq,
        mul_inv_cancel_right, hcz']
    have hconjc : c * b * c * (c * b)⁻¹ = d * c := by
      rw [hd, mul_inv_rev, hD.inv_eq hb, hD.inv_eq hcD, pow_two]
      group
    have hdz' : c * b * z * (c * b)⁻¹ = d * z := by
      rw [hzc, show c * b * (c * u) * (c * b)⁻¹ =
          c * b * c * (c * b)⁻¹ * (c * b * u * (c * b)⁻¹) by group, hconjc, ← hucb.eq,
        mul_inv_cancel_right, mul_assoc]
    set g' := (c * b)⁻¹ * k⁻¹ with hg'
    have e1 : d * z = k⁻¹ * u * k := by rw [← hdz]; group
    have e2 : z = (c * b)⁻¹ * (d * z) * (c * b) := by rw [← hdz']; group
    have hzu : z = g' * u * g'⁻¹ := by
      rw [e2, e1, hg']
      group
    have hzef : z = g' * a * g'⁻¹ * (g' * b * g'⁻¹) := by
      rw [hzu, hu]
      group
    have heD : g' * a * g'⁻¹ ∈ D := hN g' a ha
    have hfD : g' * b * g'⁻¹ ∈ D := hN g' b hb
    have hef : Commute (g' * a * g'⁻¹) (g' * b * g'⁻¹) := (Commute.conj_iff g').2 hc
    have hez : Commute (g' * a * g'⁻¹) z := by
      rw [hzef]
      exact (Commute.refl _).mul_right hef
    have key : ∀ y ∈ D, Commute y z → Reach D y (g' * a * g'⁻¹) := by
      intro y hy hyz
      by_contra hnr
      obtain ⟨-, hodd_ye⟩ := opposite_of_not_reach hD hy heD hnr
      have hnyf : ¬ Reach D y (g' * b * g'⁻¹) := fun h' =>
        hnr (reach_trans h' (reach_symm (reach_of_commute heD hfD hef)))
      obtain ⟨-, hodd_yf⟩ := opposite_of_not_reach hD hy hfD hnyf
      have hyf : y * (g' * a * g'⁻¹) * z = y * (g' * b * g'⁻¹) := by
        rw [hzef, ← mul_assoc, mul_assoc y, hD.mul_self_eq_one heD, mul_one]
      have h2 := orderOf_mul_eq_two_mul_of_odd (hyz.mul_left hez) hodd_ye hoz
      rw [hyf] at h2
      rw [h2] at hodd_yf
      exact (Nat.not_even_iff_odd.2 hodd_yf) (even_two_mul _)
    exact hax (reach_trans hac (reach_trans (key c hcD hcz) (reach_symm (key x hx hxz))))
  refine ⟨hcD, hac, hca, ?_⟩
  rw [show b = a * u by rw [hu, ← mul_assoc, ha2, one_mul]]
  exact hca.mul_right hcu

end ConnCex

end CFSG.Timmesfeld.Bridge
