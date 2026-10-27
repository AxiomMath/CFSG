module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open CFSG

variable {G : Type*} [Group G]

theorem card_inf_centralizer_eq_nine [Finite G] {A : Subgroup G} {d : G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hdA : d ∈ Subgroup.normalizer (A : Set G)) (hd3 : d ^ 3 = 1)
    (hexp : ∀ a ∈ A, (a * d) ^ 3 = 1) (hnc : ∃ a ∈ A, a * d ≠ d * a) :
    Nat.card (A ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) = 9 := by
  have hcomm : ∀ x y : A, x * y = y * x := fun x y => hA.1.is_comm.comm x y
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := fun x y => hcomm x y }
  have hexpA : ∀ x : A, x ^ 3 = 1 := fun x => Subtype.ext (hA.2 (x : G) x.2)
  have hconj : ∀ a ∈ A, d * a * d⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hdA a).mp ha
  obtain ⟨δ, hδ⟩ : ∃ δ : A →* A, ∀ b : A, ((δ b : A) : G) = d * (b : G) * d⁻¹ :=
    ⟨MonoidHom.mk' (fun b : A => ⟨d * (b : G) * d⁻¹, hconj (b : G) b.2⟩)
      (fun a b => Subtype.ext (by simp [mul_assoc])), fun b => rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : A →* A, ∀ a : A, φ a = δ a * a⁻¹ :=
    ⟨MonoidHom.mk' (fun a : A => δ a * a⁻¹)
      (fun a b => by rw [map_mul, mul_inv, mul_mul_mul_comm]), fun a => rfl⟩
  have hφ : ∀ a : A, ((φ a : A) : G) = d * (a : G) * d⁻¹ * (a : G)⁻¹ := fun a => by
    rw [hφdef a, Subgroup.coe_mul, hδ a, Subgroup.coe_inv]
  have hF5 : ∀ a : A,
      (a : G) * (d * (a : G) * d⁻¹) * (d * (d * (a : G) * d⁻¹) * d⁻¹) = 1 := by
    intro a
    have h := hexp (a : G) a.2
    rw [pow_three'] at h
    calc (a : G) * (d * (a : G) * d⁻¹) * (d * (d * (a : G) * d⁻¹) * d⁻¹)
        = ((a : G) * d) * ((a : G) * d) * ((a : G) * d) * (d ^ 3)⁻¹ := by group
      _ = 1 := by rw [h, hd3, inv_one, mul_one]
  have hxyz : ∀ a : A, a * δ a * δ (δ a) = 1 := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hδ (δ a), hδ a, Subgroup.coe_one]
    exact hF5 a
  have hφφ : ∀ a : A, φ (φ a) = 1 := by
    intro a
    have hy3 : δ a ^ 3 = 1 := hexpA (δ a)
    have hy1 : (δ a)⁻¹ = δ a * δ a :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact hy3)
    rw [hφdef (φ a), hφdef a, map_mul, map_inv, mul_inv, inv_inv, hy1]
    calc δ (δ a) * (δ a * δ a) * (δ a * δ a * a)
        = (a * δ a * δ (δ a)) * (δ a * δ a * δ a) := by ac_rfl
      _ = 1 := by
        rw [hxyz a, one_mul]
        exact (pow_three' (δ a)).symm.trans hy3
  have hker : ∀ a : A, φ a = 1 ↔ (a : G) * d = d * (a : G) := by
    intro a
    constructor
    · intro ha
      have h1 : d * (a : G) * d⁻¹ * (a : G)⁻¹ = 1 := by
        rw [← hφ a]
        exact congrArg Subtype.val ha
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
    · intro ha
      have h2 : d * (a : G) * d⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr ha.symm
      have h3 : ((φ a : A) : G) = 1 := by rw [hφ a, h2, mul_inv_cancel]
      exact Subtype.ext h3
  have hrk : φ.range ≤ φ.ker := by
    intro w hw
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hw
    exact MonoidHom.mem_ker.mpr (hφφ a)
  have hcard_le : Nat.card φ.range ≤ Nat.card φ.ker := Subgroup.card_le_of_le hrk
  have hfirst : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hEq : Nat.card φ.ker = Nat.card (A ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨x.1.2,
          Subgroup.mem_centralizer_singleton_iff.mpr ((hker x.1).mp (MonoidHom.mem_ker.mp x.2))⟩⟩
        invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
          MonoidHom.mem_ker.mpr ((hker ⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩).mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2))⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  rw [← hEq]
  have hdvd : Nat.card φ.ker ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_subgroup_dvd_card φ.ker
  obtain ⟨m, hm, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases m
  · exfalso
    rw [pow_zero] at hk
    rw [hk] at hfirst hcard_le
    omega
  · exfalso
    rw [pow_one] at hk
    rw [hk] at hfirst hcard_le
    omega
  · exact hk.trans (by norm_num)
  · exfalso
    have htop : φ.ker = ⊤ :=
      Subgroup.eq_top_of_card_eq φ.ker (by rw [hk, hA27] <;> norm_num)
    obtain ⟨a, ha, hne⟩ := hnc
    have hmem : (⟨a, ha⟩ : A) ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hne ((hker ⟨a, ha⟩).mp (MonoidHom.mem_ker.mp hmem))

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
