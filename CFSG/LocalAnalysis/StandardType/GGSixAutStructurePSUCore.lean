module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSURoot
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLCoreCases

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (antidiag)

namespace AutPSU

section Lift

variable {X : Type*} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]

omit [Finite X] [Z.Normal] in
theorem eq_one_of_mem_of_pow (hZ : Odd (Nat.card Z)) {z : X} (hz : z ∈ Z) {a : ℕ}
    (ha : z ^ 2 ^ a = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf z ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard _ hz
  have hcop : Nat.Coprime (2 ^ a) (Nat.card Z) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hZ)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_lift_of_odd (hZc : Z ≤ Subgroup.center X) (hZ : Odd (Nat.card Z))
    (Q : Subgroup (X ⧸ Z)) (hQ : IsPGroup 2 Q) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ S.map (QuotientGroup.mk' Z) = Q ∧ S ⊓ Z = ⊥ ∧
      ∀ x : X, (x : X ⧸ Z) ∈ Q → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z
  set Qt := Q.comap π
  have hcardQt : Nat.card (Z.subgroupOf Qt) * Nat.card Q = Nat.card Qt := by
    set g : Qt →* X ⧸ Z := π.comp Qt.subtype
    have hgk : g.ker = Z.subgroupOf Qt := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have hgr : g.range = Q := by
      ext e
      constructor
      · rintro ⟨a, rfl⟩
        exact a.2
      · intro he
        obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective e
        exact ⟨⟨A, he⟩, rfl⟩
    rw [← Subgroup.card_ker_mul_card_range g, hgk, hgr]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card Qt := ⟨Nat.card (Z.subgroupOf Qt), by rw [← hcardQt, hk, mul_comm]⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set S := H.map Qt.subtype
  have hScard : Nat.card S = 2 ^ k := by
    rw [Subgroup.card_map_of_injective Qt.subtype_injective, hH]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card hScard
  have hSQt : S ≤ Qt := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hSZ : S ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxZ⟩
    have hx : x ^ 2 ^ k = 1 := by
      rw [← hScard]
      have := pow_card_eq_one' (G := S) (x := ⟨x, hxS⟩)
      exact congrArg Subtype.val this
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_of_pow hZ hxZ hx
  have hSQ : S.map π = Q := by
    have hinj : Function.Injective (π.comp S.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha
      have ha' : (a : X) ∈ Z := (QuotientGroup.eq_one_iff _).mp ha
      have h' : (a : X) ∈ S ⊓ Z := ⟨a.2, ha'⟩
      rw [hSZ, Subgroup.mem_bot] at h'
      rw [Subgroup.mem_bot]
      exact Subtype.ext h'
    have hrange : (π.comp S.subtype).range = S.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hSQt hx
    · rw [hk, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hScard]
  refine ⟨S, hS2, hSQ, hSZ, fun x hxQ ⟨a, ha⟩ => ?_⟩
  rw [← hSQ] at hxQ
  obtain ⟨s, hsS, hs⟩ := hxQ
  have hz : s⁻¹ * x ∈ Z := QuotientGroup.eq.mp hs
  have hcomm : Commute s⁻¹ x := by
    have hz' := Subgroup.mem_center_iff.mp (hZc hz) s
    change s⁻¹ * x = x * s⁻¹
    calc s⁻¹ * x = (s⁻¹ * x) * s * s⁻¹ := by group
      _ = s * (s⁻¹ * x) * s⁻¹ := by rw [← hz']
      _ = x * s⁻¹ := by group
  have hsk : s ^ 2 ^ k = 1 := by
    rw [← hScard]
    have := pow_card_eq_one' (G := S) (x := ⟨s, hsS⟩)
    exact congrArg Subtype.val this
  have hz1 : (s⁻¹ * x) ^ 2 ^ (a + k) = 1 := by
    rw [hcomm.mul_pow, inv_pow, pow_add, pow_mul, pow_mul, ha, one_pow, mul_one, ← pow_mul,
      mul_comm, pow_mul, hsk, one_pow, inv_one]
  have hone := eq_one_of_mem_of_pow hZ hz hz1
  rw [← inv_mul_eq_one.mp hone]
  exact hsS

omit [Finite X] in
theorem conj_mem_lift_of {Q : Subgroup (X ⧸ Z)} {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hSQ : S.map (QuotientGroup.mk' Z) = Q)
    (hS : ∀ x : X, (x : X ⧸ Z) ∈ Q → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ S)
    {y : X} (hy : ∀ q ∈ Q, (y : X ⧸ Z) * q * ((y : X ⧸ Z)⁻¹ : X ⧸ Z) ∈ Q) {s : X}
    (hs : s ∈ S) : y * s * y⁻¹ ∈ S := by
  refine hS _ ?_ ?_
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hy _ (hSQ ▸ ⟨s, hs, rfl⟩)
  · obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [conj_pow, hk', mul_one, mul_inv_cancel]

end Lift

section Scalars

variable {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem odd_card_normOneScalars (H : Subgroup (GL (Fin n) K)) :
    Odd (Nat.card (normOneScalars h H n)) := by
  classical
  have : Fintype (normOneScalars h H n) := Fintype.ofFinite _
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.card_eq_fintype_card] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hodd
  obtain ⟨c, -, -, hc⟩ := x.2
  have hpow : x ^ Nat.card Kˣ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (((x : H) : GL (Fin n) K)) ^ Nat.card Kˣ = 1
    rw [hc, ← map_pow, pow_card_eq_one', map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [hx] at hdvd
  exact (Nat.not_even_iff_odd.mpr AutPSL.odd_card_units) (even_iff_two_dvd.mpr hdvd)

end Scalars

section Entry

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem entry_eq_bar_inv {g : GL (Fin n) K} (hg : g ∈ XJ h n) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) i j =
      h.bar (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (Fin.rev j) (Fin.rev i)) := by
  have hg1 : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * antidiag n *
      (g : Matrix (Fin n) (Fin n) K) = antidiag n := hg.1
  have h1 : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * antidiag n =
      antidiag n * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * antidiag n =
        ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * antidiag n *
          ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * antidiag n *
          (g : Matrix (Fin n) (Fin n) K)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg1]
  have h2 := congrFun (congrFun h1 j) (Fin.rev i)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, antidiag,
    Matrix.of_apply, Fin.rev_inj, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h2
  rw [← h2, h.bar_bar]

end Entry

end AutPSU

end CFSG.StandardType
