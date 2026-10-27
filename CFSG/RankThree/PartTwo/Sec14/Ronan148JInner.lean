module

public import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
public import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofJ2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

theorem sup_eq_of_forall_inner {X : Type} [Group X] {A J : Subgroup X}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (hZ : J ⊓ Subgroup.centralizer (J : Set X) = ⊥)
    (hAJ : A ≤ Subgroup.normalizer (J : Set X))
    (hinner : ∀ a ∈ A, ∃ u ∈ J, ∀ x ∈ J, a * x * a⁻¹ = u * x * u⁻¹) :
    A ⊓ Subgroup.centralizer (J : Set X) ⊔ A ⊓ J = A := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  intro a ha
  obtain ⟨u, hu, hau⟩ := hinner a ha
  have hN : ∀ g ∈ A, ∀ x ∈ J, g * x * g⁻¹ ∈ J := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAJ hg) x).mp hx
  have huC : ∀ a' ∈ A, a' * u = u * a' := by
    intro a' ha'
    have hcomm : a' * a = a * a' := hAab a' ha' a ha
    have e1 : a'⁻¹ * a = a * a'⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * a') * a'⁻¹ := by group
        _ = a'⁻¹ * (a' * a) * a'⁻¹ := by rw [hcomm]
        _ = a * a'⁻¹ := by group
    have e2 : a' * a⁻¹ = a⁻¹ * a' := by
      calc a' * a⁻¹ = a⁻¹ * (a * a') * a⁻¹ := by group
        _ = a⁻¹ * (a' * a) * a⁻¹ := by rw [hcomm]
        _ = a⁻¹ * a' := by group
    have hv : ∀ x ∈ J, a' * u * a'⁻¹ * x * (a' * u * a'⁻¹)⁻¹ = u * x * u⁻¹ := by
      intro x hx
      have hz : a'⁻¹ * x * a' ∈ J := by
        have := hN a'⁻¹ (A.inv_mem ha') x hx
        rwa [inv_inv] at this
      have hz' := hau _ hz
      have hx' := hau x hx
      have key : a * (a'⁻¹ * x * a') * a⁻¹ = a'⁻¹ * (a * x * a⁻¹) * a' := by
        calc a * (a'⁻¹ * x * a') * a⁻¹ = (a * a'⁻¹) * x * (a' * a⁻¹) := by group
          _ = (a'⁻¹ * a) * x * (a⁻¹ * a') := by rw [← e1, e2]
          _ = a'⁻¹ * (a * x * a⁻¹) * a' := by group
      rw [key, hx'] at hz'
      calc a' * u * a'⁻¹ * x * (a' * u * a'⁻¹)⁻¹
          = a' * (u * (a'⁻¹ * x * a') * u⁻¹) * a'⁻¹ := by group
        _ = a' * (a'⁻¹ * (u * x * u⁻¹) * a') * a'⁻¹ := by rw [hz']
        _ = u * x * u⁻¹ := by group
    have htJ : a' * u * a'⁻¹ * u⁻¹ ∈ J := J.mul_mem (hN a' ha' u hu) (J.inv_mem hu)
    have htC : a' * u * a'⁻¹ * u⁻¹ ∈ Subgroup.centralizer (J : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      have hy : u⁻¹ * h * u ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hu) hh) hu
      have hy' : a' * u * a'⁻¹ * (u⁻¹ * h * u) * (a' * u * a'⁻¹)⁻¹ = h := by
        rw [hv _ hy]
        group
      have hc : (a' * u * a'⁻¹ * u⁻¹) * h = h * (a' * u * a'⁻¹ * u⁻¹) := by
        calc (a' * u * a'⁻¹ * u⁻¹) * h
            = (a' * u * a'⁻¹ * (u⁻¹ * h * u) * (a' * u * a'⁻¹)⁻¹) * (a' * u * a'⁻¹ * u⁻¹) := by
              group
          _ = h * (a' * u * a'⁻¹ * u⁻¹) := by rw [hy']
      exact hc.symm
    have ht1 : a' * u * a'⁻¹ * u⁻¹ = 1 := by
      have h1 : a' * u * a'⁻¹ * u⁻¹ ∈ J ⊓ Subgroup.centralizer (J : Set X) :=
        Subgroup.mem_inf.mpr ⟨htJ, htC⟩
      rw [hZ] at h1
      exact Subgroup.mem_bot.mp h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp ht1)
  have hpow : ∀ k : ℕ, ∀ x ∈ J, a ^ k * x * (a ^ k)⁻¹ = u ^ k * x * (u ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hy : u ^ k * x * (u ^ k)⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem (pow_mem hu k) hx) (J.inv_mem (pow_mem hu k))
      calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹
          = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by
            simp only [pow_succ', mul_assoc, mul_inv_rev]
        _ = a * (u ^ k * x * (u ^ k)⁻¹) * a⁻¹ := by rw [ih x hx]
        _ = u * (u ^ k * x * (u ^ k)⁻¹) * u⁻¹ := hau _ hy
        _ = u ^ (k + 1) * x * (u ^ (k + 1))⁻¹ := by
            simp only [pow_succ', mul_assoc, mul_inv_rev]
  have hu3 : u ^ 3 = 1 := by
    have hC : ∀ h ∈ J, h * u ^ 3 = u ^ 3 * h := by
      intro h hh
      have e := hpow 3 h hh
      rw [show a ^ 3 = 1 from hA3 a ha, inv_one, mul_one, one_mul] at e
      exact (mul_inv_eq_iff_eq_mul.mp e.symm).symm
    have h3 : u ^ 3 ∈ J ⊓ Subgroup.centralizer (J : Set X) :=
      Subgroup.mem_inf.mpr ⟨pow_mem hu 3, Subgroup.mem_centralizer_iff.mpr hC⟩
    rw [hZ] at h3
    exact Subgroup.mem_bot.mp h3
  have huA : u ∈ A :=
    hF3 u (Subgroup.mem_centralizer_iff.mpr fun a' ha' => huC a' ha') hu3
  have hinvA : u⁻¹ * a ∈ A := A.mul_mem (A.inv_mem huA) ha
  have hinvC : u⁻¹ * a ∈ Subgroup.centralizer (J : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hah : a * h = u * h * u⁻¹ * a := by
      calc a * h = a * h * a⁻¹ * a := by group
        _ = u * h * u⁻¹ * a := by rw [hau h hh]
    calc h * (u⁻¹ * a) = u⁻¹ * (u * h * u⁻¹ * a) := by group
      _ = u⁻¹ * (a * h) := by rw [hah]
      _ = u⁻¹ * a * h := by group
  have hmem : u * (u⁻¹ * a) ∈ A ⊓ Subgroup.centralizer (J : Set X) ⊔ A ⊓ J :=
    mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨huA, hu⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hinvA, hinvC⟩))
  rwa [mul_inv_cancel_left] at hmem

theorem exists_inner_of_j2
    {X : Type} [Group X] {J : Subgroup X}
    (φ : ↥J ≃* CFSG.Blueprint.NativeSporadic.J2) {a : X}
    (haJ : a ∈ Subgroup.normalizer (J : Set X)) (ha3 : a ^ 3 = 1) :
    ∃ u ∈ J, ∀ x ∈ J, a * x * a⁻¹ = u * x * u⁻¹ := by
  have hσ3 : (J.normalizerMonoidHom ⟨a, haJ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨a, haJ⟩ : Subgroup.normalizer (J : Set X)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [h3, map_one]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp
    (CFSG.RankThree.PartTwo.KFacts.ks17J2AutThree_of_outer
      CFSG.RankThree.PartTwo.Sec13.Res2Proof.nonempty_outer_j2 ↥J ⟨φ⟩ _ hσ3)
  refine ⟨(g : X), g.2, fun x hx => ?_⟩
  have h := congrArg (fun τ : MulAut ↥J => ((τ ⟨x, hx⟩ : ↥J) : X)) hg
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  exact h.symm

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
