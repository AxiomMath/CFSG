module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentInitial.IrreducibleOperatorField
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.LocalAnalysis.ComponentInitial

theorem isLeast_pow_modEq_one_of_generator {F : Type*} [Field F] {q n p : ℕ} (hq : q.Prime)
    (hn : 1 ≤ n) (hF : Nat.card F = q ^ n) (hp : p.Prime) {τ : F} (hτp : τ ^ p = 1)
    (hτ1 : τ ≠ 1) (hgen : ∀ σ : F ≃+* F, σ τ = τ → σ = 1) :
    IsLeast {j : ℕ | 0 < j ∧ q ^ j ≡ 1 [MOD p]} n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσa, hσord, -⟩ := finite_field_automorphism_fixed_field_cardinality hq hn hF
  have hpow : ∀ (j : ℕ) (x : F), (σ ^ j) x = x ^ q ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', RingAut.mul_apply, ih, hσa, ← pow_mul, pow_succ]
  have hτ0 : τ ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hτp
    exact zero_ne_one hτp
  have hτord : orderOf τ = p := orderOf_eq_prime hτp hτ1
  have key : ∀ j : ℕ, σ ^ j = 1 ↔ p ∣ q ^ j - 1 := by
    intro j
    have hqj : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq.pos
    have e : τ ^ q ^ j = τ ↔ τ ^ (q ^ j - 1) = 1 := by
      conv_lhs => rw [show q ^ j = (q ^ j - 1) + 1 by omega, pow_succ]
      exact mul_eq_right₀ hτ0
    constructor
    · intro h
      have h1 : (σ ^ j) τ = τ := by rw [h]; rfl
      rw [hpow, e] at h1
      exact hτord ▸ orderOf_dvd_of_pow_eq_one h1
    · intro h
      apply hgen
      rw [hpow, e]
      exact orderOf_dvd_iff_pow_eq_one.mp (hτord ▸ h)
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · have h := (key n).mp (hσord ▸ pow_orderOf_eq_one σ)
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).mpr h).symm
  · rintro j ⟨hj, hjmod⟩
    have h := (key j).mpr ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).mp hjmod.symm)
    exact Nat.le_of_dvd hj (hσord ▸ orderOf_dvd_of_pow_eq_one h)

theorem binary_order_small_cases {p d : ℕ} (hp : p.Prime)
    (hd : IsLeast {j : ℕ | 0 < j ∧ 2 ^ j ≡ 1 [MOD p]} d) :
    (3 < p → d ≤ 4 → (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) ∧
      (3 < p → Even d → d ≤ 6 → p = 5 ∧ d = 4) := by
  obtain ⟨⟨hd0, hdmod⟩, hmin⟩ := hd
  have hdvd : p ∣ 2 ^ d - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hdmod.symm
  have hle : p ≤ 2 ^ d - 1 :=
    Nat.le_of_dvd (by have := Nat.one_lt_two_pow (n := d) (by omega); omega) hdvd
  constructor
  · intro hp3 hd4
    interval_cases d <;> interval_cases p <;> simp_all (config := { decide := true })
  · intro hp3 hev hd6
    interval_cases d
    · simp_all (config := { decide := true })
    · simp at hle; omega
    · simp_all (config := { decide := true })
    · interval_cases p <;> simp_all (config := { decide := true })
    · simp_all (config := { decide := true })
    · interval_cases p <;> first
        | exact absurd (hmin ⟨by norm_num, by decide⟩ : 6 ≤ 3) (by norm_num)
        | simp_all (config := { decide := true })

theorem binary_irreducible_prime_action_degree {p : ℕ} (hp : p.Prime) {A : Type*}
    [Group A] [Finite A] [IsElementaryAbelian p A] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : A →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ a : A, ∀ v ∈ W, (ρ a : V →ₗ[ZMod 2] V) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ρ.range ≠ ⊥) :
    IsCyclic ρ.range ∧ Nat.card ρ.range = p ∧
      IsLeast {j : ℕ | 0 < j ∧ 2 ^ j ≡ 1 [MOD p]} (Module.finrank (ZMod 2) V) ∧
      (3 < p → Module.finrank (ZMod 2) V ≤ 4 →
        (p = 7 ∧ Module.finrank (ZMod 2) V = 3) ∨ (p = 5 ∧ Module.finrank (ZMod 2) V = 4)) ∧
      (3 < p → Even (Module.finrank (ZMod 2) V) → Module.finrank (ZMod 2) V ≤ 6 →
        p = 5 ∧ Module.finrank (ZMod 2) V = 4) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set d := Module.finrank (ZMod 2) V with hd
  set T := ρ.range with hT
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm a b]
  have hirrT : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ T, ∀ w ∈ W, (g : Module.End (ZMod 2) V) w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun a v hv => hW (ρ a) ⟨a, rfl⟩ v hv
  obtain ⟨hF, hFcard, -⟩ := irreducible_abelian_operator_algebra_field (p := 2) hd1 rfl hcomm hirrT
  let : Field (operatorAlgebra T) := hF.toField
  have hexp : ∀ g ∈ T, g ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) a, map_one]
  have hmemF : ∀ g ∈ T,
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) ∈
        operatorAlgebra T :=
    fun g hg => Algebra.subset_adjoin ⟨g, hg, rfl⟩
  let φ : T →* (operatorAlgebra T)ˣ :=
    { toFun := fun g => ⟨⟨_, hmemF g g.2⟩, ⟨_, hmemF _ (inv_mem g.2)⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun g h => Units.ext (Subtype.ext (by simp)) }
  have hφinj : Function.Injective φ := fun g h hgh => by
    have := congrArg (fun u : (operatorAlgebra T)ˣ =>
      ((u : operatorAlgebra T) : Module.End (ZMod 2) V)) hgh
    exact Subtype.ext (Units.ext this)
  have hroot : ∀ g : T, φ g ∈ rootsOfUnity p (operatorAlgebra T) := by
    intro g
    rw [mem_rootsOfUnity, ← map_pow]
    have hg : g ^ p = 1 := Subtype.ext (hexp g g.2)
    rw [hg, map_one]
  have hTfin : Finite T := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hTle : Nat.card T ≤ p := by
    let φ' : T →* rootsOfUnity p (operatorAlgebra T) := φ.codRestrict _ hroot
    have h := Nat.card_le_card_of_injective φ'
      (fun a b h => hφinj (congrArg Subtype.val h))
    exact h.trans (card_rootsOfUnity _ p)
  have hTp : IsPGroup p T :=
    (IsElementaryAbelian.isPGroup p A).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hT1 : 1 < Nat.card T := (Subgroup.one_lt_card_iff_ne_bot T).mpr hnt
  have hTcard : Nat.card T = p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
    have h1 : 1 ≤ k := by
      rcases k with _ | k
      · rw [hk, pow_zero] at hT1
        exact absurd hT1 (lt_irrefl 1)
      · omega
    have h2 : k ≤ 1 := by
      by_contra h
      have : p ^ 1 < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
      rw [pow_one, ← hk] at this
      omega
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨isCyclic_of_prime_card hTcard, hTcard, ?_⟩
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hT1
  obtain ⟨t, ht1⟩ := exists_ne (1 : T)
  have htp : t ^ p = 1 := Subtype.ext (hexp t t.2)
  have htord : orderOf t = p := orderOf_eq_prime htp ht1
  have hzp : ∀ g : T, ∃ k : ℕ, t ^ k = g := by
    intro g
    have htop : Subgroup.zpowers t = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, htord, hTcard]
    have hg : g ∈ Subgroup.zpowers t := htop ▸ Subgroup.mem_top g
    obtain ⟨k, hk⟩ := ((isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers).mpr hg
    exact ⟨k, hk⟩
  set τ : operatorAlgebra T := ⟨_, hmemF t t.2⟩ with hτ
  have hτpow : ∀ k : ℕ, τ ^ k = ⟨_, hmemF (t ^ k : T) (t ^ k).2⟩ := fun k =>
    Subtype.ext (by simp [hτ])
  have hτp : τ ^ p = 1 := by
    rw [hτpow, htp]
    exact Subtype.ext (by simp)
  have hτ1 : τ ≠ 1 := by
    intro h
    apply ht1
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  have hgen : ∀ σ : operatorAlgebra T ≃+* operatorAlgebra T, σ τ = τ → σ = 1 := by
    intro σ hσ
    refine RingEquiv.ext fun x => ?_
    obtain ⟨y, hy⟩ := x
    change σ ⟨y, hy⟩ = ⟨y, hy⟩
    have hy' : y ∈ Algebra.adjoin (ZMod 2)
        ((fun g : LinearMap.GeneralLinearGroup (ZMod 2) V => (g : Module.End (ZMod 2) V)) ''
          (T : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) := hy
    induction hy' using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨k, hk⟩ := hzp ⟨g, hg⟩
      have he : (⟨_, hy⟩ : operatorAlgebra T) = τ ^ k := by
        rw [hτpow]
        exact Subtype.ext (by rw [hk])
      rw [he, map_pow, hσ]
    | algebraMap r =>
      have he : (⟨_, hy⟩ : operatorAlgebra T) = algebraMap (ZMod 2) (operatorAlgebra T) r := rfl
      rw [he]
      exact DFunLike.congr_fun (RingHom.ext_zmod ((σ : operatorAlgebra T →+* operatorAlgebra T).comp
        (algebraMap (ZMod 2) (operatorAlgebra T))) (algebraMap (ZMod 2) (operatorAlgebra T))) r
    | add x z hx hz ihx ihz =>
      have he : (⟨_, hy⟩ : operatorAlgebra T) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
      rw [he, map_add, ihx hx, ihz hz]
    | mul x z hx hz ihx ihz =>
      have he : (⟨_, hy⟩ : operatorAlgebra T) = ⟨x, hx⟩ * ⟨z, hz⟩ := rfl
      rw [he, map_mul, ihx hx, ihz hz]
  have hleast := isLeast_pow_modEq_one_of_generator Nat.prime_two hd1 hFcard hp hτp hτ1 hgen
  exact ⟨hleast, (binary_order_small_cases hp hleast).1, (binary_order_small_cases hp hleast).2⟩

end CFSG.RankThree.GroupTheory
