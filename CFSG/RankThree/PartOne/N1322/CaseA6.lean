module

public import CFSG.RankThree.PartOne.N1322.Pure
public import CFSG.RankThree.PartOne.N1322.CaseConj
public import CFSG.RankThree.PartOne.N1322.CaseInner
public import CFSG.RankThree.PartOne.N1322.CasePair

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

theorem A6_orders : ∀ σ : alternatingGroup (Fin 6),
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 ∨ σ ^ 5 = 1 := by decide +kernel

theorem A6_noncomm : ∃ x y : alternatingGroup (Fin 6), x * y ≠ y * x := by decide +kernel

@[expose] def a6₀ : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem A6_conj0 : ∀ b : alternatingGroup (Fin 6), b * b = 1 → b ≠ 1 →
    ∃ k : alternatingGroup (Fin 6), k * a6₀ * k⁻¹ = b := by decide +kernel

theorem A6_conj (a b : alternatingGroup (Fin 6)) (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b * b = 1)
    (hb1 : b ≠ 1) : ∃ k : alternatingGroup (Fin 6), k * a * k⁻¹ = b := by
  obtain ⟨ka, hka⟩ := A6_conj0 a ha ha1
  obtain ⟨kb, hkb⟩ := A6_conj0 b hb hb1
  refine ⟨kb * ka⁻¹, ?_⟩
  rw [← hka, ← hkb]
  group

@[expose] def a6₁ : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 4, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem A6_ord5 : ∃ x y : alternatingGroup (Fin 6), x * x = 1 ∧ x ≠ 1 ∧ y * y = 1 ∧ y ≠ 1 ∧
    (x * y) ^ 5 = 1 ∧ x * y ≠ 1 := by
  refine ⟨a6₀, a6₁, ?_⟩
  decide +kernel

theorem case5_false (hN : KF1322ThreeA6Norm) {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)}
    (h : CoreHyp d) {H : Subgroup (GL (Fin 3) (ZMod p))} (hHX : H ≤ d.X)
    (hnorm : ∀ g ∈ d.X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hperf : Group.IsPerfect H) (hcard : Nat.card (Subgroup.center H) = 3)
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) : False := by
  have h4 := four_ne_zero_of_five_le h.p5
  have hcen3 : ∀ z : H, z ∈ Subgroup.center H → z ^ 3 = 1 := by
    intro z hz
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center H)
    rw [hcard] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    simpa using congrArg (fun w : Subgroup.center H => (w : H)) h2
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := A6_noncomm
    obtain ⟨a', ha'⟩ := QuotientGroup.mk_surjective (e.symm x)
    obtain ⟨b', hb'⟩ := QuotientGroup.mk_surjective (e.symm y)
    refine ⟨(a' : GL (Fin 3) (ZMod p)), a'.2, (b' : GL (Fin 3) (ZMod p)), b'.2, fun hc => hxy ?_⟩
    have hab : a' * b' = b' * a' := Subtype.ext hc
    have h1 : e.symm x * e.symm y = e.symm y * e.symm x := by
      rw [← ha', ← hb', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab]
    simpa using congrArg e h1
  have hsch := scalar_commutant_of_noncomm hirr hnc
  have hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 :=
    fun x hx => det_eq_one_of_perfect hx
  have hZ3 : ∀ z ∈ H, (∀ g : GL (Fin 3) (ZMod p), g * z = z * g) → z ^ 3 = 1 := by
    intro z hz hc
    have hzc : (⟨z, hz⟩ : H) ∈ Subgroup.center H :=
      Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (hc y))
    simpa using congrArg Subtype.val (hcen3 ⟨z, hz⟩ hzc)
  have hin : ∀ t ∈ d.D, ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹ := by
    intro t ht
    obtain ⟨h₀, hh₀, z, hzc, htz⟩ :=
      hN p h.p5 H hirr hperf hcard ⟨e⟩ t (hnorm t (mem_X_of_mem_D h ht))
    refine ⟨h₀, hh₀, fun x hx => ?_⟩
    rw [htz]
    calc h₀ * z * x * (h₀ * z)⁻¹ = h₀ * (z * x) * z⁻¹ * h₀⁻¹ := by group
      _ = h₀ * (x * z) * z⁻¹ * h₀⁻¹ := by rw [hzc x]
      _ = h₀ * x * h₀⁻¹ := by group
  obtain ⟨-, t₀, -, ht₀D, -⟩ := exists_refl_pair h
  obtain ⟨h₁, hh₁, hin₁⟩ := hin _ ht₀D
  obtain ⟨a₁, ha₁, ha₁sq, ht₁⟩ := refl_neg_of_inner hdet hZ3 hsch (h.refl _ ht₀D) hh₁ hin₁
  have hinv : ∀ (a : GL (Fin 3) (ZMod p)) (ha : a ∈ H), a * a = 1 →
      (-1 : GL (Fin 3) (ZMod p)) * a ∈ d.D →
      e (QuotientGroup.mk (⟨a, ha⟩ : H)) * e (QuotientGroup.mk (⟨a, ha⟩ : H)) = 1 ∧
        e (QuotientGroup.mk (⟨a, ha⟩ : H)) ≠ 1 := by
    intro a ha hsq hD
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← QuotientGroup.mk_mul]
      have : (⟨a, ha⟩ : H) * ⟨a, ha⟩ = 1 := Subtype.ext hsq
      rw [this, QuotientGroup.mk_one, map_one]
    · intro h1
      have h2 : (QuotientGroup.mk (⟨a, ha⟩ : H) : H ⧸ Subgroup.center H) = 1 :=
        e.injective (h1.trans (map_one e).symm)
      have h3 := (QuotientGroup.eq_one_iff _).mp h2
      have hc : ∀ g : GL (Fin 3) (ZMod p), g * a = a * g :=
        central_of_center hsch (fun x hx => by
          have := Subgroup.mem_center_iff.mp h3 ⟨x, hx⟩
          simpa using congrArg Subtype.val this)
      have hcube := hZ3 a ha hc
      have ha1 : a = 1 := by
        calc a = a * (a * a) := by rw [hsq, mul_one]
          _ = a ^ 3 := (pow_three a).symm
          _ = 1 := hcube
      apply IsRefl.ne_neg_one h4 (h.refl _ hD)
      rw [ha1, mul_one]
      simp
  have hD₁ : (-1 : GL (Fin 3) (ZMod p)) * a₁ ∈ d.D := by rw [← ht₁]; exact ht₀D
  obtain ⟨hi₁, hne₁⟩ := hinv a₁ ha₁ ha₁sq hD₁
  obtain ⟨x, y, hx2, hx1, hy2, hy1, hxy5, hxy1⟩ := A6_ord5
  obtain ⟨kx, hkx⟩ := A6_conj _ _ hi₁ hne₁ hx2 hx1
  obtain ⟨ky, hky⟩ := A6_conj _ _ hi₁ hne₁ hy2 hy1
  obtain ⟨kHx, hkHx⟩ := QuotientGroup.mk_surjective (e.symm kx)
  obtain ⟨kHy, hkHy⟩ := QuotientGroup.mk_surjective (e.symm ky)
  have hkHx' : e (QuotientGroup.mk kHx) = kx := by rw [hkHx, e.apply_symm_apply]
  have hkHy' : e (QuotientGroup.mk kHy) = ky := by rw [hkHy, e.apply_symm_apply]
  have hconjD : ∀ k : H, (-1 : GL (Fin 3) (ZMod p)) * ((k * ⟨a₁, ha₁⟩ * k⁻¹ : H) :
      GL (Fin 3) (ZMod p)) ∈ d.D := by
    intro k
    have hmemD := h.Dconj _ (hHX k.2) _ hD₁
    have heq : (k : GL (Fin 3) (ZMod p)) * ((-1 : GL (Fin 3) (ZMod p)) * a₁) *
        (k : GL (Fin 3) (ZMod p))⁻¹ = (-1) * ((k * ⟨a₁, ha₁⟩ * k⁻¹ : H) : GL (Fin 3) (ZMod p)) := by
      calc (k : GL (Fin 3) (ZMod p)) * ((-1) * a₁) * (k : GL (Fin 3) (ZMod p))⁻¹
          = ((k : GL (Fin 3) (ZMod p)) * (-1)) * a₁ * (k : GL (Fin 3) (ZMod p))⁻¹ := by
            simp only [mul_assoc]
        _ = ((-1) * (k : GL (Fin 3) (ZMod p))) * a₁ * (k : GL (Fin 3) (ZMod p))⁻¹ := by
            rw [← neg_one_comm (k : GL (Fin 3) (ZMod p))]
        _ = (-1) * ((k : GL (Fin 3) (ZMod p)) * a₁ * (k : GL (Fin 3) (ZMod p))⁻¹) := by
            simp only [mul_assoc]
        _ = (-1) * ((k * ⟨a₁, ha₁⟩ * k⁻¹ : H) : GL (Fin 3) (ZMod p)) := rfl
    rw [← heq]
    exact hmemD
  set u₁ : H := ⟨a₁, ha₁⟩ with hu₁
  set a : H := kHx * u₁ * kHx⁻¹ with ha
  set b : H := kHy * u₁ * kHy⁻¹ with hb
  have hu₁2 : u₁ * u₁ = 1 := Subtype.ext ha₁sq
  have ha2 : a * a = 1 := by
    calc a * a = kHx * (u₁ * u₁) * kHx⁻¹ := by rw [ha]; group
      _ = 1 := by rw [hu₁2]; group
  have hb2 : b * b = 1 := by
    calc b * b = kHy * (u₁ * u₁) * kHy⁻¹ := by rw [hb]; group
      _ = 1 := by rw [hu₁2]; group
  have hea : e (QuotientGroup.mk a) = x := by
    rw [ha, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hkHx']
    exact hkx
  have heb : e (QuotientGroup.mk b) = y := by
    rw [hb, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hkHy']
    exact hky
  have hDa : (-1 : GL (Fin 3) (ZMod p)) * (a : GL (Fin 3) (ZMod p)) ∈ d.D := hconjD kHx
  have hDb : (-1 : GL (Fin 3) (ZMod p)) * (b : GL (Fin 3) (ZMod p)) ∈ d.D := hconjD kHy
  have hu5 : (a * b) ^ 5 = 1 := by
    have h1 : e (QuotientGroup.mk ((a * b) ^ 5)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, QuotientGroup.mk_mul, map_mul, hea, heb]
      exact hxy5
    have h2 : (a * b) ^ 5 ∈ Subgroup.center H :=
      (QuotientGroup.eq_one_iff _).mp (e.injective (h1.trans (map_one e).symm))
    have hz3 := hcen3 _ h2
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hinvab : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
      calc a * (a * b) * a⁻¹ = (a * a) * b * a⁻¹ := by group
        _ = b * a := by rw [ha2, one_mul, ha']
        _ = (a * b)⁻¹ := by rw [_root_.mul_inv_rev, ha', hb']
    have hzc : a * (a * b) ^ 5 * a⁻¹ = (a * b) ^ 5 := by
      have hc := Subgroup.mem_center_iff.1 h2 a
      calc a * (a * b) ^ 5 * a⁻¹ = ((a * b) ^ 5 * a) * a⁻¹ := by rw [hc]
        _ = (a * b) ^ 5 := by group
    have hzi : a * (a * b) ^ 5 * a⁻¹ = ((a * b) ^ 5)⁻¹ := by
      rw [← conj_pow, hinvab, inv_pow]
    have hz2 : ((a * b) ^ 5) ^ 2 = 1 := by
      have : (a * b) ^ 5 = ((a * b) ^ 5)⁻¹ := hzc.symm.trans hzi
      calc ((a * b) ^ 5) ^ 2 = (a * b) ^ 5 * (a * b) ^ 5 := sq _
        _ = (a * b) ^ 5 * ((a * b) ^ 5)⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel _
    calc (a * b) ^ 5 = ((a * b) ^ 5) ^ 3 * (((a * b) ^ 5) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; simp
  have hab1 : a * b ≠ 1 := by
    intro h1
    apply hxy1
    rw [← hea, ← heb, ← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
  have hord5 : orderOf ((a : GL (Fin 3) (ZMod p)) * (b : GL (Fin 3) (ZMod p))) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg Subtype.val hu5
      simpa using this
    · intro h1
      apply hab1
      exact Subtype.ext (by simpa using h1)
  have hprodneg : ((-1 : GL (Fin 3) (ZMod p)) * (a : GL (Fin 3) (ZMod p))) *
      ((-1 : GL (Fin 3) (ZMod p)) * (b : GL (Fin 3) (ZMod p))) =
      (a : GL (Fin 3) (ZMod p)) * (b : GL (Fin 3) (ZMod p)) := by
    calc ((-1 : GL (Fin 3) (ZMod p)) * (a : GL (Fin 3) (ZMod p))) * ((-1) * (b : GL (Fin 3) (ZMod p)))
        = (-1) * ((a : GL (Fin 3) (ZMod p)) * (-1)) * (b : GL (Fin 3) (ZMod p)) := by
          simp only [mul_assoc]
      _ = (-1) * ((-1) * (a : GL (Fin 3) (ZMod p))) * (b : GL (Fin 3) (ZMod p)) := by
          rw [neg_one_comm (a : GL (Fin 3) (ZMod p))]
      _ = ((-1 : GL (Fin 3) (ZMod p)) * (-1)) * (a : GL (Fin 3) (ZMod p)) *
          (b : GL (Fin 3) (ZMod p)) := by simp only [mul_assoc]
      _ = (a : GL (Fin 3) (ZMod p)) * (b : GL (Fin 3) (ZMod p)) := by
          rw [neg_one_mul_neg_one, one_mul]
  have hko := h.kO _ hDa _ hDb (by rw [hprodneg, hord5]; decide)
  rw [hprodneg, hord5] at hko
  omega

end CFSG.RankThree.PartOne.N1322
