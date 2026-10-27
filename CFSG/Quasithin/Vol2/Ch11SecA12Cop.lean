module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G]

theorem exists_mem_centralizer_of_coprime {p : ℕ} (hp : p.Prime) {A B N : Subgroup G}
    (hA : IsPGroup p A) (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hNB : N ≤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N))
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N) {b : G} (hb : b ∈ B) :
    ∃ c ∈ B ⊓ Subgroup.centralizer (A : Set G), c⁻¹ * b ∈ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A B hAB
  have hc' : ∀ a ∈ A, ∀ y ∈ B, y⁻¹ * (a * y * a⁻¹) ∈ N := fun a ha y hy => by
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBN hy)) _).mp
      (hc a ha y hy)
    convert h1 using 1
    group
  let fibre : SubMulAction A B :=
    { carrier := {y : B | (y : G)⁻¹ * b ∈ N}
      smul_mem' := by
        intro a y hy
        change ((a : G) * y * (a : G)⁻¹)⁻¹ * b ∈ N
        have e : ((a : G) * y * (a : G)⁻¹)⁻¹ * b =
            ((y : G)⁻¹ * ((a : G) * y * (a : G)⁻¹))⁻¹ * ((y : G)⁻¹ * b) := by group
        rw [e]
        exact N.mul_mem (N.inv_mem (hc' a a.2 y y.2)) hy }
  have hcard : Nat.card fibre = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun y => ⟨((y.1 : B) : G)⁻¹ * b, y.2⟩
        invFun := fun n => ⟨⟨b * (n : G)⁻¹, B.mul_mem hb (B.inv_mem (hNB n.2))⟩, by
          change (b * (n : G)⁻¹)⁻¹ * b ∈ N
          rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
          exact n.2⟩
        left_inv := fun y => Subtype.ext (Subtype.ext (by simp))
        right_inv := fun n => Subtype.ext (by simp) }
  have hndvd : ¬ p ∣ Nat.card fibre := by
    rw [hcard]
    exact hp.coprime_iff_not_dvd.mp hcop
  obtain ⟨y, hy⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card fibre hndvd
  refine ⟨y.1.1, ⟨y.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, y.2⟩
  have h1 := congrArg (fun z : fibre => ((z.1 : B) : G)) (hy ⟨a, ha⟩)
  change a * ((y.1 : B) : G) * a⁻¹ = ((y.1 : B) : G) at h1
  calc a * ((y.1 : B) : G) = a * ((y.1 : B) : G) * a⁻¹ * a := by group
    _ = ((y.1 : B) : G) * a := by rw [h1]

end CFSG.Quasithin.Vol2.Ch11.SecA
