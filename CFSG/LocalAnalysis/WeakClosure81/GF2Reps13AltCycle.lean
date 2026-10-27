module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationL32Tab
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

open CFSG.Quasithin Equiv
open scoped commutatorElement

section ThreeCycle

variable {X : Type} [Group X] [Finite X] {n : ℕ}

omit [Finite X] in
private theorem pow_three_of_mem_center (hZ3 : Nat.card (Subgroup.center X) = 3)
    {z : X} (hz : z ∈ Subgroup.center X) : z ^ 3 = 1 := by
  have h : orderOf (⟨z, hz⟩ : Subgroup.center X) ∣ 3 := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center X)
    rwa [hZ3] at this
  have h2 : (⟨z, hz⟩ : Subgroup.center X) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  simpa using congrArg Subtype.val h2

omit [Finite X] in
private theorem exists_lift (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n))
    (y : alternatingGroup (Fin n)) : ∃ g : X, e (g : X ⧸ Subgroup.center X) = y := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm y)
  exact ⟨g, by rw [hg, MulEquiv.apply_symm_apply]⟩

private theorem involution_fixed (m : ℕ) (hm : m = 6 ∨ m = 7) (σ : Perm (Fin m))
    (h1 : σ * σ = 1) (h2 : σ ≠ 1) (h3 : Perm.sign σ = 1) : ∃ f : Fin m, σ f = f := by
  rcases hm with rfl | rfl
  · have key : ∀ π : Perm (Fin 6), π * π = 1 → π ≠ 1 → Perm.sign π = 1 →
        ∃ f : Fin 6, π f = f := by
      decide +kernel
    exact key σ h1 h2 h3
  ·
    have hσ : σ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact h1
    exact Perm.exists_fixed_point_of_prime (p := 2) (n := 1) (by decide) hσ

omit [Finite X] in
private theorem involution_comm (x u c : X) (hu : u * u = 1) (hc3 : c ^ 3 = 1)
    (hcz : ∀ g : X, g * c = c * g) (hc : u * x = x * u * c) : u * x = x * u := by
  have h1 : u * x * u = x * c := by
    calc u * x * u = x * u * c * u := by rw [hc]
      _ = x * (u * c) * u := by simp only [mul_assoc]
      _ = x * (c * u) * u := by rw [hcz u]
      _ = x * c := by simp only [mul_assoc, hu, mul_one]
  have h2 : x = x * c * c := by
    calc x = (u * u) * x * (u * u) := by rw [hu, one_mul, mul_one]
      _ = u * (u * x * u) * u := by simp only [mul_assoc]
      _ = u * (x * c) * u := by rw [h1]
      _ = (u * x) * (c * u) := by simp only [mul_assoc]
      _ = (u * x) * (u * c) := by rw [← hcz u]
      _ = (u * x * u) * c := by simp only [mul_assoc]
      _ = (x * c) * c := by rw [h1]
  have h3 : c * c = 1 := by
    have h4 : x * (c * c) = x * 1 := by
      rw [mul_one, ← mul_assoc]
      exact h2.symm
    exact mul_left_cancel h4
  have hc1 : c = 1 := by
    calc c = c * (c * c) := by rw [h3, mul_one]
      _ = c ^ 3 := (pow_three c).symm
      _ = 1 := hc3
  rw [hc1, mul_one] at hc
  exact hc

omit [Finite X] in
theorem pow_three_eq_one_of_isThreeCycle (hn : 5 ≤ n) (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) {x : X}
    (hx : ((e x : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle) : x ^ 3 = 1 := by
  have h5 : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hinv : (((e x)⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle := by
    rw [Subgroup.coe_inv]
    exact hx.inv
  obtain ⟨c, hc⟩ := isConj_iff.mp (alternatingGroup.isThreeCycle_isConj h5 hx hinv)
  obtain ⟨g, hg⟩ := exists_lift e c
  have hmk : (QuotientGroup.mk (g * x * g⁻¹) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk x⁻¹ := by
    apply e.injective
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hg]
    exact hc
  obtain ⟨c0, hc0, hw⟩ : ∃ c0 ∈ Subgroup.center X, g * x * g⁻¹ = x⁻¹ * c0 := by
    have h := QuotientGroup.eq.mp hmk.symm
    rw [inv_inv] at h
    exact ⟨x * (g * x * g⁻¹), h, (inv_mul_cancel_left x _).symm⟩
  have hcomm : Commute x⁻¹ c0 := Subgroup.mem_center_iff.mp hc0 x⁻¹
  have hpow : (e x) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have h := pow_orderOf_eq_one ((e x : alternatingGroup (Fin n)) : Perm (Fin n))
    rwa [hx.orderOf] at h
  have hd : x ^ 3 ∈ Subgroup.center X := by
    refine (QuotientGroup.eq_one_iff (x ^ 3)).mp ?_
    apply e.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow, hpow]
  have hconj : g * x ^ 3 * g⁻¹ = (x ^ 3)⁻¹ := by
    rw [← conj_pow, hw, hcomm.mul_pow, pow_three_of_mem_center hZ3 hc0, mul_one, inv_pow]
  have hgd : g * x ^ 3 * g⁻¹ = x ^ 3 := by
    rw [Subgroup.mem_center_iff.mp hd g, mul_inv_cancel_right]
  have heq : x ^ 3 = (x ^ 3)⁻¹ := hgd.symm.trans hconj
  have hd2 : (x ^ 3) ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.mpr heq
  have hd3 : (x ^ 3) ^ 3 = 1 := pow_three_of_mem_center hZ3 hd
  calc x ^ 3 = (x ^ 3) ^ 4 := by
        rw [show (x ^ 3) ^ 4 = (x ^ 3) ^ 3 * x ^ 3 from pow_succ (x ^ 3) 3, hd3, one_mul]
    _ = ((x ^ 3) ^ 2) ^ 2 := show (x ^ 3) ^ 4 = ((x ^ 3) ^ 2) ^ 2 from pow_mul (x ^ 3) 2 2
    _ = 1 := by rw [hd2, one_pow]

omit [Finite X] in
theorem exists_isThreeCycle_conj_eq_inv (hn : n = 6 ∨ n = 7)
    (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) {l : X}
    (hl2 : l ^ 2 ∈ Subgroup.center X) (hl : l ∉ Subgroup.center X) :
    ∃ x : X, ((e x : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle ∧
      l * x * l⁻¹ = x⁻¹ := by
  have hσσ : e (QuotientGroup.mk l) * e (QuotientGroup.mk l) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← sq, (QuotientGroup.eq_one_iff (l ^ 2)).mpr hl2,
      map_one]
  have h1 : (e (QuotientGroup.mk l) : Perm (Fin n)) * (e (QuotientGroup.mk l) : Perm (Fin n))
      = 1 := by
    have h := congrArg Subtype.val hσσ
    rwa [Subgroup.coe_mul, Subgroup.coe_one] at h
  have h2 : (e (QuotientGroup.mk l) : Perm (Fin n)) ≠ 1 := by
    intro h
    apply hl
    have h' : e (QuotientGroup.mk l) = 1 := Subtype.ext (h.trans (Subgroup.coe_one _).symm)
    exact (QuotientGroup.eq_one_iff l).mp (e.injective (h'.trans (map_one e).symm))
  have h3 : Perm.sign (e (QuotientGroup.mk l) : Perm (Fin n)) = 1 :=
    Perm.mem_alternatingGroup.mp (e (QuotientGroup.mk l)).2
  set σ : Perm (Fin n) := (e (QuotientGroup.mk l) : Perm (Fin n)) with hσdef
  obtain ⟨p0, hp0⟩ := involution_fixed n hn σ h1 h2 h3
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    exact h2 (Equiv.ext fun y => by rw [Perm.one_apply]; exact hcon y)
  have hinv : ∀ y, σ (σ y) = y := fun y => by
    rw [← Perm.mul_apply, h1, Perm.one_apply]
  have hap : a ≠ p0 := fun h => ha (by rw [h, hp0])
  have hbp : σ a ≠ p0 := by
    intro h
    apply ha
    have h' : a = p0 := by
      calc a = σ (σ a) := (hinv a).symm
        _ = σ p0 := by rw [h]
        _ = p0 := hp0
    rw [h', hp0]
  have hab : a ≠ σ a := fun h => ha h.symm
  have hsw1 : σ * swap a (σ a) * σ⁻¹ = swap (σ a) a := by
    rw [← swap_apply_apply, hinv]
  have hsw2 : σ * swap a p0 * σ⁻¹ = swap (σ a) p0 := by
    rw [← swap_apply_apply, hp0]
  have hτconj : σ * (swap a (σ a) * swap a p0) * σ⁻¹ = (swap a (σ a) * swap a p0)⁻¹ := by
    have key : swap a p0 = swap a (σ a) * swap (σ a) p0 * (swap a (σ a))⁻¹ := by
      have h := swap_apply_apply (swap a (σ a)) (σ a) p0
      rwa [swap_apply_right, swap_apply_of_ne_of_ne hap.symm hbp.symm] at h
    rw [show σ * (swap a (σ a) * swap a p0) * σ⁻¹ =
        (σ * swap a (σ a) * σ⁻¹) * (σ * swap a p0 * σ⁻¹) by group, hsw1, hsw2, mul_inv_rev,
      swap_inv, swap_inv, swap_comm (σ a) a, key, inv_mul_cancel_right]
  have hτ3 : Perm.IsThreeCycle (swap a (σ a) * swap a p0) :=
    Perm.isThreeCycle_swap_mul_swap_same hab hap hbp
  obtain ⟨x₀, hx₀⟩ :=
    exists_lift e ⟨swap a (σ a) * swap a p0, hτ3.mem_alternatingGroup⟩
  have hmk2 : (QuotientGroup.mk (l * x₀ * l⁻¹) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk x₀⁻¹ := by
    apply e.injective
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hx₀]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hτconj
  have hcZ0 : x₀ * (l * x₀ * l⁻¹) ∈ Subgroup.center X := by
    have h := QuotientGroup.eq.mp hmk2.symm
    rwa [inv_inv] at h
  obtain ⟨c, hcZ, hc⟩ : ∃ c ∈ Subgroup.center X, l * x₀ * l⁻¹ = x₀⁻¹ * c :=
    ⟨x₀ * (l * x₀ * l⁻¹), hcZ0, (inv_mul_cancel_left x₀ _).symm⟩
  have hc3 : c ^ 3 = 1 := pow_three_of_mem_center hZ3 hcZ
  have hcx : ∀ g : X, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hcZ g
  have hcomm' : Commute x₀⁻¹ c := hcx x₀⁻¹
  have hcinv : c⁻¹ = c * c := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hc3)
  have hlc : l * c * l⁻¹ = c := by rw [hcx l, mul_inv_cancel_right]
  refine ⟨x₀ * c, ?_, ?_⟩
  · have hxe : e ((x₀ * c : X) : X ⧸ Subgroup.center X) =
        e ((x₀ : X) : X ⧸ Subgroup.center X) := by
      rw [QuotientGroup.mk_mul, map_mul, (QuotientGroup.eq_one_iff c).mpr hcZ, map_one, mul_one]
    rw [hxe, hx₀]
    exact hτ3
  · calc l * (x₀ * c) * l⁻¹ = (l * x₀ * l⁻¹) * (l * c * l⁻¹) := by group
      _ = (x₀⁻¹ * c) * c := by rw [hc, hlc]
      _ = x₀⁻¹ * (c * c) := mul_assoc _ _ _
      _ = c * c * x₀⁻¹ := (hcomm'.mul_right hcomm').eq
      _ = c⁻¹ * x₀⁻¹ := by rw [hcinv]
      _ = (x₀ * c)⁻¹ := (mul_inv_rev x₀ c).symm

omit [Finite X] in
theorem exists_isThreeCycle_commute_involution (hZ3 : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7)) :
    ∃ x u : X, ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle ∧
      u ^ 2 = 1 ∧ u ≠ 1 ∧ u * x = x * u := by
  have hp3 : Perm.IsThreeCycle (swap (0 : Fin 7) 1 * swap 0 2) :=
    Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hq_alt : swap (3 : Fin 7) 4 * swap 5 6 ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul,
      Perm.sign_swap (show (3 : Fin 7) ≠ 4 by decide),
      Perm.sign_swap (show (5 : Fin 7) ≠ 6 by decide), Int.units_mul_self]
  have hPQ : swap (0 : Fin 7) 1 * swap 0 2 * (swap 3 4 * swap 5 6) =
      swap (3 : Fin 7) 4 * swap 5 6 * (swap 0 1 * swap 0 2) := by
    decide
  have hq2 : swap (3 : Fin 7) 4 * swap 5 6 * (swap 3 4 * swap 5 6) = 1 := by decide
  have hq1 : swap (3 : Fin 7) 4 * swap 5 6 ≠ 1 := by decide
  obtain ⟨P, hPdef⟩ : ∃ P : alternatingGroup (Fin 7),
      ((P : alternatingGroup (Fin 7)) : Perm (Fin 7)) = swap 0 1 * swap 0 2 :=
    ⟨⟨_, hp3.mem_alternatingGroup⟩, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : alternatingGroup (Fin 7),
      ((Q : alternatingGroup (Fin 7)) : Perm (Fin 7)) = swap 3 4 * swap 5 6 :=
    ⟨⟨_, hq_alt⟩, rfl⟩
  have hPQ' : P * Q = Q * P := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hPdef, hQdef]
    exact hPQ)
  have hPQc : Commute P Q := hPQ'
  have hQ2 : Q ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hQdef, Subgroup.coe_one, sq]
    exact hq2)
  have hQ1 : Q ≠ 1 := fun h => hq1 (by
    rw [← hQdef, h, Subgroup.coe_one])
  have hQ3 : Q ^ 3 = Q := by
    rw [show Q ^ 3 = Q ^ 2 * Q from pow_succ Q 2, hQ2, one_mul]
  obtain ⟨x₀, hx₀⟩ := exists_lift e P
  obtain ⟨u₀, hu₀⟩ := exists_lift e Q
  have hmkpow : ∀ k : ℕ, e ((u₀ ^ k : X) : X ⧸ Subgroup.center X) = Q ^ k := fun k => by
    rw [QuotientGroup.mk_pow, map_pow, hu₀]
  have hd : u₀ ^ 2 ∈ Subgroup.center X := by
    refine (QuotientGroup.eq_one_iff (u₀ ^ 2)).mp ?_
    apply e.injective
    rw [map_one, hmkpow 2, hQ2]
  have hu2 : (u₀ ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_three_of_mem_center hZ3 hd
  have hu1 : u₀ ^ 3 ≠ 1 := by
    intro h
    have h1 : Q ^ 3 = 1 := by
      rw [← hmkpow 3, h, QuotientGroup.mk_one, map_one]
    exact hQ1 (hQ3.symm.trans h1)
  have hcomm1 : e ((u₀ ^ 3 * x₀ : X) : X ⧸ Subgroup.center X) =
      e ((x₀ * u₀ ^ 3 : X) : X ⧸ Subgroup.center X) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, hmkpow 3, hx₀]
    exact (hPQc.pow_right 3).symm.eq
  obtain ⟨c, hcZ, hc⟩ : ∃ c ∈ Subgroup.center X, u₀ ^ 3 * x₀ = x₀ * u₀ ^ 3 * c :=
    ⟨(x₀ * u₀ ^ 3)⁻¹ * (u₀ ^ 3 * x₀), QuotientGroup.eq.mp (e.injective hcomm1).symm,
      (mul_inv_cancel_left (x₀ * u₀ ^ 3) (u₀ ^ 3 * x₀)).symm⟩
  have hcz : ∀ g : X, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hcZ g
  have hc3 : c ^ 3 = 1 := pow_three_of_mem_center hZ3 hcZ
  have hu2' : u₀ ^ 3 * u₀ ^ 3 = 1 := (sq (u₀ ^ 3)).symm.trans hu2
  refine ⟨x₀, u₀ ^ 3, ?_, hu2, hu1, ?_⟩
  · rw [hx₀, hPdef]
    exact hp3
  · exact involution_comm x₀ (u₀ ^ 3) c hu2' hc3 hcz hc

end ThreeCycle

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

end
