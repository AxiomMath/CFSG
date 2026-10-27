module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

variable {N : Type*} [Group N]

section Plain

private theorem b15_BarAut_eq_top_of_chain {p : ℕ} (hp : p.Prime) [Finite N]
    (hcard : Nat.card N = p ^ 3) {Z A C : Subgroup N} (hZ : Nat.card Z = p) (hZA : Z ≤ A)
    (hAC : A ≤ C) (hZA' : Z ≠ A) (hAC' : A ≠ C) : C = ⊤ := by
  have hdvdC : Nat.card C ∣ p ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hdvdA : Nat.card A ∣ p ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card A
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdC
  obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvdA
  have hlt1 : Nat.card Z < Nat.card A := by
    by_contra hle
    exact hZA' (Subgroup.eq_of_le_of_card_ge hZA (not_lt.1 hle))
  have hlt2 : Nat.card A < Nat.card C := by
    by_contra hle
    exact hAC' (Subgroup.eq_of_le_of_card_ge hAC (not_lt.1 hle))
  rw [hZ, hi] at hlt1
  rw [hi, hj] at hlt2
  have hi2 : 1 < i := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by simpa using hlt1)
  have hij : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt2
  have hj' : j = 3 := by omega
  apply Subgroup.eq_top_of_card_eq
  rw [hj, hj', hcard]

private def b15_BarAut_fixMod (σ : MulAut N) : Subgroup N where
  carrier := {y | σ y * y⁻¹ ∈ Subgroup.center N}
  one_mem' := by
    show σ 1 * (1 : N)⁻¹ ∈ Subgroup.center N
    simpa using (Subgroup.center N).one_mem
  mul_mem' := by
    intro y y' hy hy'
    have hy' : σ y' * y'⁻¹ ∈ Subgroup.center N := hy'
    have hy : σ y * y⁻¹ ∈ Subgroup.center N := hy
    show σ (y * y') * (y * y')⁻¹ ∈ Subgroup.center N
    have hc := Subgroup.mem_center_iff.1 hy' y⁻¹
    have h : σ (y * y') * (y * y')⁻¹ = (σ y * y⁻¹) * (σ y' * y'⁻¹) := by
      calc σ (y * y') * (y * y')⁻¹ = σ y * ((σ y' * y'⁻¹) * y⁻¹) := by
            rw [map_mul, mul_inv_rev]; group
        _ = σ y * (y⁻¹ * (σ y' * y'⁻¹)) := by rw [hc]
        _ = (σ y * y⁻¹) * (σ y' * y'⁻¹) := by group
    rw [h]
    exact (Subgroup.center N).mul_mem hy hy'
  inv_mem' := by
    intro y hy
    have hy : σ y * y⁻¹ ∈ Subgroup.center N := hy
    show σ y⁻¹ * (y⁻¹)⁻¹ ∈ Subgroup.center N
    have hc := Subgroup.mem_center_iff.1 ((Subgroup.center N).inv_mem hy) y⁻¹
    have h : σ y⁻¹ * (y⁻¹)⁻¹ = (σ y * y⁻¹)⁻¹ := by
      calc σ y⁻¹ * (y⁻¹)⁻¹ = y⁻¹ * (σ y * y⁻¹)⁻¹ * y := by rw [map_inv]; group
        _ = (σ y * y⁻¹)⁻¹ * y⁻¹ * y := by rw [hc]
        _ = (σ y * y⁻¹)⁻¹ := by group
    rw [h]
    exact (Subgroup.center N).inv_mem hy

end Plain

section Basic

variable {p : ℕ} [Fact p.Prime] [hN : CFSG.IsExtraspecial p N]

include hN

private theorem b15_BarAut_commutator_mem_center (a b : N) : ⁅a, b⁆ ∈ Subgroup.center N := by
  haveI := CFSG.IsExtraspecial.quotient_elementary_abelian p N
  have h : ((⁅a, b⁆ : N) : N ⧸ Subgroup.center N) = 1 := by
    change (QuotientGroup.mk' (Subgroup.center N)) ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' _ _)
  exact (QuotientGroup.eq_one_iff _).1 h

private theorem b15_BarAut_pow_mem_center (a : N) : a ^ p ∈ Subgroup.center N := by
  haveI := CFSG.IsExtraspecial.quotient_elementary_abelian p N
  have h : ((a ^ p : N) : N ⧸ Subgroup.center N) = 1 := by
    change (QuotientGroup.mk' (Subgroup.center N)) (a ^ p) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p p (N ⧸ Subgroup.center N)) _
  exact (QuotientGroup.eq_one_iff _).1 h

private theorem b15_BarAut_center_pow {z : N} (hz : z ∈ Subgroup.center N) : z ^ p = 1 := by
  have h : (⟨z, hz⟩ : Subgroup.center N) ^ Nat.card (Subgroup.center N) = 1 := pow_card_eq_one'
  rw [CFSG.IsExtraspecial.center_order_p p N] at h
  simpa using congrArg Subtype.val h

private theorem b15_BarAut_eq_one_of_mul_self (hp2 : p ≠ 2) {t : N}
    (ht : t ∈ Subgroup.center N) (h : t * t = 1) : t = 1 := by
  have hp : t ^ p = 1 := b15_BarAut_center_pow ht
  have h2 : t ^ 2 = 1 := by rw [pow_two]; exact h
  have hcop : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (Ne.symm hp2)
  have hd : orderOf t ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hp)
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)

private theorem b15_BarAut_mem_center_of_sq (hp2 : p ≠ 2) {x : N}
    (hx : x ^ 2 ∈ Subgroup.center N) : x ∈ Subgroup.center N := by
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h1 : x = x ^ p * ((x ^ 2) ^ m)⁻¹ := by
    rw [hm, ← pow_mul]
    group
  rw [h1]
  exact Subgroup.mul_mem _ (b15_BarAut_pow_mem_center x)
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ hx m))

theorem mulAut_pm_of_isExtraspecial [Finite N] (hp2 : p ≠ 2) (hcard : Nat.card N = p ^ 3)
    (σ : MulAut N) (hσσ : ∀ x, σ (σ x) = x) (hσZ : ∀ z ∈ Subgroup.center N, σ z = z) :
    (∀ x, σ x * x⁻¹ ∈ Subgroup.center N) ∨ (∀ x, σ x * x ∈ Subgroup.center N) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨a, ha⟩ := not_forall.1 h1
  obtain ⟨b, hb⟩ := not_forall.1 h2
  have hcomm : ∀ x y : N, ⁅x, y⁆ ∈ Subgroup.center N := b15_BarAut_commutator_mem_center (p := p)
  have hcen : ∀ z ∈ Subgroup.center N, ∀ g : N, g * z = z * g :=
    fun z hz g => Subgroup.mem_center_iff.1 hz g
  have e1 : ∀ (x y z : N), z ∈ Subgroup.center N → ⁅x * z, y⁆ = ⁅x, y⁆ := by
    intro x y z hz
    have h : z * y * z⁻¹ = y := by rw [← hcen z hz y]; group
    rw [commutatorElement_def, commutatorElement_def]
    calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [h]
  have e2 : ∀ x y : N, ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
    intro x y
    have hw := hcen _ ((Subgroup.center N).inv_mem (hcomm x y)) y⁻¹
    have h : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]; group
    rw [h, hw]
    group
  obtain ⟨xm, hxm_def⟩ : ∃ x : N, x = a⁻¹ * σ a := ⟨_, rfl⟩
  obtain ⟨xp, hxp_def⟩ : ∃ x : N, x = b * σ b := ⟨_, rfl⟩
  have hxm : xm ∉ Subgroup.center N := by
    intro hz
    apply ha
    have h : σ a * a⁻¹ = a * xm * a⁻¹ := by rw [hxm_def]; group
    rw [h, hcen xm hz a]
    simpa using hz
  have hxp : xp ∉ Subgroup.center N := by
    intro hz
    apply hb
    have h : σ b * b = b⁻¹ * xp * b := by rw [hxp_def]; group
    rw [h, hcen xp hz b⁻¹]
    simpa using hz
  have hσxm : σ xm = xm⁻¹ := by
    rw [hxm_def, map_mul, map_inv, hσσ]; group
  obtain ⟨ζ, hζ_def⟩ : ∃ ζ : N, ζ = ⁅(σ b)⁻¹, b⁻¹⁆ := ⟨_, rfl⟩
  have hζ : ζ ∈ Subgroup.center N := by rw [hζ_def]; exact hcomm _ _
  have hσxp : σ xp = xp * ζ := by
    rw [hxp_def, hζ_def, map_mul, hσσ, commutatorElement_def]; group
  have hcz : ⁅xp, xm⁆ ∈ Subgroup.center N := hcomm _ _
  have ht : ⁅xp, xm⁆ = 1 := by
    have hfix : σ ⁅xp, xm⁆ = ⁅xp, xm⁆ := hσZ _ hcz
    rw [map_commutatorElement, hσxp, hσxm, e1 _ _ _ hζ, e2] at hfix
    apply b15_BarAut_eq_one_of_mul_self hp2 hcz
    calc ⁅xp, xm⁆ * ⁅xp, xm⁆ = ⁅xp, xm⁆ * ⁅xp, xm⁆⁻¹ := by rw [hfix]
      _ = 1 := mul_inv_cancel _
  set F : Subgroup N := b15_BarAut_fixMod σ with hF
  set C : Subgroup N := Subgroup.centralizer ({xp} : Set N) with hC
  have hxpF : xp ∈ F := by
    show σ xp * xp⁻¹ ∈ Subgroup.center N
    have : σ xp * xp⁻¹ = ζ := by
      rw [hσxp]
      calc xp * ζ * xp⁻¹ = xp * (ζ * xp⁻¹) := by group
        _ = xp * (xp⁻¹ * ζ) := by rw [← hcen ζ hζ xp⁻¹]
        _ = ζ := by group
    rw [this]; exact hζ
  have hxpC : xp ∈ C := Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]
  have hxmC : xm ∈ C := Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact commutatorElement_eq_one_iff_mul_comm.1 ht
  have hxmF : xm ∉ F := by
    intro hmem
    have hmem : σ xm * xm⁻¹ ∈ Subgroup.center N := hmem
    rw [hσxm] at hmem
    apply hxm
    apply b15_BarAut_mem_center_of_sq hp2
    have : xm ^ 2 = (xm⁻¹ * xm⁻¹)⁻¹ := by group
    rw [this]
    exact (Subgroup.center N).inv_mem hmem
  have hZF : Subgroup.center N ≤ F ⊓ C := fun z hz => by
    refine ⟨?_, Subgroup.center_le_centralizer _ hz⟩
    show σ z * z⁻¹ ∈ Subgroup.center N
    rw [hσZ z hz, mul_inv_cancel]
    exact (Subgroup.center N).one_mem
  have htop : C = ⊤ := by
    refine b15_BarAut_eq_top_of_chain (Fact.out : p.Prime) hcard
      (CFSG.IsExtraspecial.center_order_p p N) hZF inf_le_right ?_ ?_
    · intro h
      exact hxp (by rw [h]; exact ⟨hxpF, hxpC⟩)
    · intro h
      have : xm ∈ F ⊓ C := by rw [h]; exact hxmC
      exact hxmF this.1
  apply hxp
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ C := by rw [htop]; exact Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.1 hg xp (Set.mem_singleton xp)).symm

theorem mulAut_apply_eq_of_forall_mul_inv_mem_center (hp2 : p ≠ 2) (σ : MulAut N)
    (hσσ : ∀ x, σ (σ x) = x) (hσZ : ∀ z ∈ Subgroup.center N, σ z = z)
    (h : ∀ x, σ x * x⁻¹ ∈ Subgroup.center N) (x : N) : σ x = x := by
  have hz := h x
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = σ x * x⁻¹ := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have e : σ x = z * x := by rw [hzdef]; group
  have h3 : z * (z * x) = x := by
    have h4 := hσσ x
    rw [e, map_mul, hσZ z hz, e] at h4
    exact h4
  have h4 : z * z = 1 := by
    have : z * z * x = 1 * x := by rw [one_mul, mul_assoc]; exact h3
    exact mul_right_cancel this
  rw [e, b15_BarAut_eq_one_of_mul_self hp2 hz h4, one_mul]

theorem mulAut_comp_apply_eq_of_pm (hp2 : p ≠ 2) (σ τ : MulAut N)
    (hσσ : ∀ x, σ (σ x) = x) (hττ : ∀ x, τ (τ x) = x) (hστ : ∀ x, σ (τ x) = τ (σ x))
    (hσZ : ∀ z ∈ Subgroup.center N, σ z = z) (hτZ : ∀ z ∈ Subgroup.center N, τ z = z)
    (hσ : ∀ x, σ x * x ∈ Subgroup.center N) (hτ : ∀ x, τ x * x ∈ Subgroup.center N) (x : N) :
    σ (τ x) = x := by
  refine mulAut_apply_eq_of_forall_mul_inv_mem_center hp2 (σ * τ) ?_ ?_ ?_ x
  · intro y
    show σ (τ (σ (τ y))) = y
    rw [← hστ (τ y), hττ, hσσ]
  · intro z hz
    show σ (τ z) = z
    rw [hτZ z hz, hσZ z hz]
  · intro y
    show σ (τ y) * y⁻¹ ∈ Subgroup.center N
    have h1 := hτ y
    have h2 := hσ y
    obtain ⟨z1, hz1⟩ : ∃ z1 : N, z1 = τ y * y := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : N, w = σ y * y := ⟨_, rfl⟩
    rw [← hz1] at h1
    rw [← hw] at h2
    have e1 : τ y = z1 * y⁻¹ := by rw [hz1]; group
    have e2 : σ y = w * y⁻¹ := by rw [hw]; group
    have hc : y * w⁻¹ = w⁻¹ * y := Subgroup.mem_center_iff.1 ((Subgroup.center N).inv_mem h2) y
    have h : σ (τ y) * y⁻¹ = z1 * w⁻¹ := by
      rw [e1, map_mul, hσZ z1 h1, map_inv, e2]
      calc z1 * (w * y⁻¹)⁻¹ * y⁻¹ = z1 * (y * w⁻¹ * y⁻¹) := by group
        _ = z1 * w⁻¹ := by rw [hc]; group
    rw [h]
    exact (Subgroup.center N).mul_mem h1 ((Subgroup.center N).inv_mem h2)

theorem index_ker_le_two_of_isExtraspecial [Finite N] (hp2 : p ≠ 2) (hcard : Nat.card N = p ^ 3)
    {A : Type*} [Group A] (ρ : A →* MulAut N) (hcomm : ∀ a a' : A, a * a' = a' * a)
    (hsq : ∀ a : A, a * a = 1) (hZ : ∀ a : A, ∀ z ∈ Subgroup.center N, ρ a z = z) :
    ρ.ker.index ≤ 2 := by
  have hinv : ∀ a : A, ∀ x, ρ a (ρ a x) = x := fun a x => by
    rw [← MulAut.mul_apply, ← map_mul, hsq, map_one]; rfl
  have hpm : ∀ a : A, a ∈ ρ.ker ∨ ∀ x, ρ a x * x ∈ Subgroup.center N := by
    intro a
    rcases mulAut_pm_of_isExtraspecial hp2 hcard (ρ a) (hinv a) (hZ a) with h | h
    · left
      rw [MonoidHom.mem_ker]
      ext x
      exact mulAut_apply_eq_of_forall_mul_inv_mem_center hp2 (ρ a) (hinv a) (hZ a) h x
    · right; exact h
  have hdvd : ρ.ker.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    by_cases hall : ∀ b : A, b ∈ ρ.ker
    · exact ⟨1, fun b => Or.inr (hall b)⟩
    · obtain ⟨a₀, ha₀⟩ := not_forall.1 hall
      refine ⟨a₀, fun b => ?_⟩
      by_cases hb : b ∈ ρ.ker
      · exact Or.inr hb
      · left
        have hb' := (hpm b).resolve_left hb
        have ha' := (hpm a₀).resolve_left ha₀
        rw [MonoidHom.mem_ker]
        ext x
        rw [map_mul]
        exact mulAut_comp_apply_eq_of_pm hp2 (ρ b) (ρ a₀) (hinv b) (hinv a₀)
          (fun y => by
            rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hcomm])
          (hZ b) (hZ a₀) hb' ha' x
  exact Nat.le_of_dvd (by norm_num) hdvd

end Basic

end CFSG.LocalAnalysis.WeakClosure81
