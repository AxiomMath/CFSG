module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofSLThree
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Res423Four

section Heis

variable {G : Type*} [Group G]

theorem mul_pow_heis {y₁ y₂ s : G} (hs : ∀ g : G, g * s = s * g) (h : y₁ * y₂ = s * y₂ * y₁)
    (d : ℕ) : y₁ * y₂ ^ d = s ^ d * y₂ ^ d * y₁ := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc y₁ * y₂ ^ (d + 1) = (y₁ * y₂ ^ d) * y₂ := by rw [pow_succ, mul_assoc]
      _ = s ^ d * y₂ ^ d * (y₁ * y₂) := by rw [ih]; group
      _ = s ^ d * y₂ ^ d * (s * y₂ * y₁) := by rw [h]
      _ = s ^ d * (y₂ ^ d * s) * y₂ * y₁ := by group
      _ = s ^ d * (s * y₂ ^ d) * y₂ * y₁ := by rw [hs]
      _ = s ^ (d + 1) * y₂ ^ (d + 1) * y₁ := by rw [pow_succ, pow_succ]; group

theorem pow_mul_pow_heis {y₁ y₂ s : G} (hs : ∀ g : G, g * s = s * g)
    (h : y₁ * y₂ = s * y₂ * y₁) (a d : ℕ) :
    y₁ ^ a * y₂ ^ d = s ^ (a * d) * y₂ ^ d * y₁ ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc y₁ ^ (a + 1) * y₂ ^ d = y₁ ^ a * (y₁ * y₂ ^ d) := by rw [pow_succ, mul_assoc]
      _ = y₁ ^ a * (s ^ d * y₂ ^ d * y₁) := by rw [mul_pow_heis hs h d]
      _ = (y₁ ^ a * s ^ d) * y₂ ^ d * y₁ := by group
      _ = s ^ d * (y₁ ^ a * y₂ ^ d) * y₁ := by
          rw [show y₁ ^ a * s ^ d = s ^ d * y₁ ^ a from
            ((Commute.pow_right (show Commute y₁ s from hs y₁) d).pow_left a).eq]
          group
      _ = s ^ d * (s ^ (a * d) * y₂ ^ d * y₁ ^ a) * y₁ := by rw [ih]
      _ = s ^ ((a + 1) * d) * y₂ ^ d * y₁ ^ (a + 1) := by
          rw [add_mul, one_mul, pow_add, pow_succ]
          have hc : s ^ d * s ^ (a * d) = s ^ (a * d) * s ^ d := (Commute.pow_pow_self s _ _).eq
          calc s ^ d * (s ^ (a * d) * y₂ ^ d * y₁ ^ a) * y₁ =
              (s ^ d * s ^ (a * d)) * y₂ ^ d * (y₁ ^ a * y₁) := by group
            _ = s ^ (a * d) * s ^ d * y₂ ^ d * (y₁ ^ a * y₁) := by rw [hc]

theorem heis_conj_pow {y₁ y₂ s : G} (hs : ∀ g : G, g * s = s * g) (h : y₁ * y₂ = s * y₂ * y₁)
    (a b c d : ℕ) :
    (y₁ ^ a * y₂ ^ b) * (y₁ ^ c * y₂ ^ d) * (y₁ ^ a * y₂ ^ b)⁻¹ =
      s ^ (a * d) * (s ^ (b * c))⁻¹ * (y₁ ^ c * y₂ ^ d) := by
  have hpow : ∀ n : ℕ, ∀ g : G, g * s ^ n = s ^ n * g := fun n g =>
    ((Commute.pow_right (show Commute g s from hs g) n)).eq
  have hinv : ∀ n : ℕ, ∀ g : G, g * (s ^ n)⁻¹ = (s ^ n)⁻¹ * g := fun n g =>
    ((Commute.pow_right (show Commute g s from hs g) n).inv_right).eq
  have h1 : y₂ ^ b * y₁ ^ c = (s ^ (c * b))⁻¹ * (y₁ ^ c * y₂ ^ b) := by
    rw [pow_mul_pow_heis hs h c b]
    group
  have h2 : y₂ ^ d * y₁ ^ a = (s ^ (a * d))⁻¹ * (y₁ ^ a * y₂ ^ d) := by
    rw [pow_mul_pow_heis hs h a d]
    group
  have huv : (y₁ ^ a * y₂ ^ b) * (y₁ ^ c * y₂ ^ d) =
      (s ^ (c * b))⁻¹ * (y₁ ^ a * y₁ ^ c * (y₂ ^ b * y₂ ^ d)) := by
    calc (y₁ ^ a * y₂ ^ b) * (y₁ ^ c * y₂ ^ d) = y₁ ^ a * (y₂ ^ b * y₁ ^ c) * y₂ ^ d := by group
      _ = y₁ ^ a * ((s ^ (c * b))⁻¹ * (y₁ ^ c * y₂ ^ b)) * y₂ ^ d := by rw [h1]
      _ = (y₁ ^ a * (s ^ (c * b))⁻¹) * (y₁ ^ c * y₂ ^ b) * y₂ ^ d := by group
      _ = (s ^ (c * b))⁻¹ * (y₁ ^ a * y₁ ^ c * (y₂ ^ b * y₂ ^ d)) := by rw [hinv]; group
  have hvu : (y₁ ^ c * y₂ ^ d) * (y₁ ^ a * y₂ ^ b) =
      (s ^ (a * d))⁻¹ * (y₁ ^ c * y₁ ^ a * (y₂ ^ d * y₂ ^ b)) := by
    calc (y₁ ^ c * y₂ ^ d) * (y₁ ^ a * y₂ ^ b) = y₁ ^ c * (y₂ ^ d * y₁ ^ a) * y₂ ^ b := by group
      _ = y₁ ^ c * ((s ^ (a * d))⁻¹ * (y₁ ^ a * y₂ ^ d)) * y₂ ^ b := by rw [h2]
      _ = (y₁ ^ c * (s ^ (a * d))⁻¹) * (y₁ ^ a * y₂ ^ d) * y₂ ^ b := by group
      _ = (s ^ (a * d))⁻¹ * (y₁ ^ c * y₁ ^ a * (y₂ ^ d * y₂ ^ b)) := by rw [hinv]; group
  have hca : y₁ ^ a * y₁ ^ c = y₁ ^ c * y₁ ^ a := by rw [← pow_add, ← pow_add, add_comm]
  have hbd : y₂ ^ b * y₂ ^ d = y₂ ^ d * y₂ ^ b := by rw [← pow_add, ← pow_add, add_comm]
  have key : (y₁ ^ a * y₂ ^ b) * (y₁ ^ c * y₂ ^ d) =
      s ^ (a * d) * (s ^ (b * c))⁻¹ * ((y₁ ^ c * y₂ ^ d) * (y₁ ^ a * y₂ ^ b)) := by
    rw [huv, hvu, hca, hbd, mul_comm c b]
    have hcomm : s ^ (a * d) * (s ^ (b * c))⁻¹ * (s ^ (a * d))⁻¹ = (s ^ (b * c))⁻¹ := by
      rw [mul_assoc, hinv (a * d) (s ^ (b * c))⁻¹, mul_inv_cancel_left]
    calc (s ^ (b * c))⁻¹ * (y₁ ^ c * y₁ ^ a * (y₂ ^ d * y₂ ^ b)) =
        (s ^ (a * d) * (s ^ (b * c))⁻¹ * (s ^ (a * d))⁻¹) *
          (y₁ ^ c * y₁ ^ a * (y₂ ^ d * y₂ ^ b)) := by rw [hcomm]
      _ = s ^ (a * d) * (s ^ (b * c))⁻¹ *
          ((s ^ (a * d))⁻¹ * (y₁ ^ c * y₁ ^ a * (y₂ ^ d * y₂ ^ b))) := by group
  rw [key]
  group

end Heis

section Coords

variable {B : Type*} [Group B]

theorem pow_val_add {x : B} (hx3 : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 3, pow_add, pow_mul, hx3, one_pow, mul_one]

@[expose] def coordHomOfPair {x y : B} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) : Multiplicative (Fin 2 → ZMod 3) →* B where
  toFun v := x ^ (Multiplicative.toAdd v 0).val * y ^ (Multiplicative.toAdd v 1).val
  map_one' := by simp
  map_mul' u v := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [pow_val_add hx3, pow_val_add hy3]
    have hc : y ^ (Multiplicative.toAdd u 1).val * x ^ (Multiplicative.toAdd v 0).val =
        x ^ (Multiplicative.toAdd v 0).val * y ^ (Multiplicative.toAdd u 1).val :=
      ((Commute.pow_pow (show Commute x y from hxy) _ _)).eq.symm
    calc x ^ (Multiplicative.toAdd u 0).val * x ^ (Multiplicative.toAdd v 0).val *
          (y ^ (Multiplicative.toAdd u 1).val * y ^ (Multiplicative.toAdd v 1).val) =
        x ^ (Multiplicative.toAdd u 0).val * (x ^ (Multiplicative.toAdd v 0).val *
          y ^ (Multiplicative.toAdd u 1).val) * y ^ (Multiplicative.toAdd v 1).val := by group
      _ = x ^ (Multiplicative.toAdd u 0).val * (y ^ (Multiplicative.toAdd u 1).val *
          x ^ (Multiplicative.toAdd v 0).val) * y ^ (Multiplicative.toAdd v 1).val := by rw [hc]
      _ = _ := by group

theorem coordHomOfPair_injective {x y : B} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) :
    Function.Injective (coordHomOfPair hx3 hy3 hxy) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [injective_iff_map_eq_one]
  intro v hv'
  set w := Multiplicative.toAdd v with hwdef
  have hv : x ^ (w 0).val * y ^ (w 1).val = 1 := hv'
  have hyx : y ^ (w 1).val = (x ^ (w 0).val)⁻¹ := eq_inv_of_mul_eq_one_right hv
  have hy1 : (w 1).val = 0 := by
    by_contra hne
    have hlt : (w 1).val < 3 := ZMod.val_lt _
    apply hy
    have hmem : y ^ (w 1).val ∈ Subgroup.zpowers x := by
      rw [hyx]
      exact inv_mem (pow_mem (Subgroup.mem_zpowers x) _)
    rcases (show (w 1).val = 1 ∨ (w 1).val = 2 by omega) with h1 | h2
    · rwa [h1, pow_one] at hmem
    · rw [h2] at hmem
      have : y = (y ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hy3, one_mul, pow_one]
      rw [this]
      exact pow_mem hmem 2
  rw [hy1, pow_zero, mul_one] at hv
  have hx0 : (w 0).val = 0 := by
    by_contra hne
    have hlt : (w 0).val < 3 := ZMod.val_lt _
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have := orderOf_dvd_of_pow_eq_one hv
    rw [hord] at this
    exact hne (Nat.eq_zero_of_dvd_of_lt this hlt)
  have h0 : w 0 = 0 := (ZMod.val_eq_zero _).mp hx0
  have h1 : w 1 = 0 := (ZMod.val_eq_zero _).mp hy1
  have hw : w = 0 := funext fun i => by fin_cases i <;> simp [h0, h1]
  change Multiplicative.ofAdd w = 1
  rw [hw]
  rfl

@[expose] noncomputable def coordOfPair [Finite B] (hB9 : Nat.card B = 9) {x y : B}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy : y ∉ Subgroup.zpowers x) : Multiplicative (Fin 2 → ZMod 3) ≃* B :=
  MulEquiv.ofBijective (coordHomOfPair hx3 hy3 hxy)
    ((coordHomOfPair_injective hx3 hy3 hxy hx1 hy).bijective_of_nat_card_le (by
      rw [hB9, Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
        ZMod.card, Fintype.card_fin]
      norm_num))

theorem coordOfPair_apply [Finite B] (hB9 : Nat.card B = 9) {x y : B}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy : y ∉ Subgroup.zpowers x) (v : Fin 2 → ZMod 3) :
    coordOfPair hB9 hx3 hy3 hxy hx1 hy (Multiplicative.ofAdd v) = x ^ (v 0).val * y ^ (v 1).val :=
  rfl

end Coords

@[expose] noncomputable def glEquivTwo :
    GL (Fin 2) (ZMod 3) ≃* ((Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glEquivTwo_apply (g : GL (Fin 2) (ZMod 3)) (v : Fin 2 → ZMod 3) :
    glEquivTwo g v = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).mulVec v := by
  simp [glEquivTwo, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]

@[expose] def q8I : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![0, 1; -1, 0], by decide⟩

@[expose] def q8J : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 1, -1], by decide⟩

@[expose] def q8Fun : QuaternionGroup 2 → Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)
  | .a k => q8I ^ k.val
  | .xa k => q8J * q8I ^ k.val

set_option maxRecDepth 100000 in
theorem q8Fun_mul : ∀ x y : QuaternionGroup 2, q8Fun (x * y) = q8Fun x * q8Fun y := by
  decide

set_option maxRecDepth 100000 in
theorem q8Fun_injective : Function.Injective q8Fun := by
  intro x y
  revert x y
  decide

@[expose] def q8Hom : QuaternionGroup 2 →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) where
  toFun := q8Fun
  map_one' := by decide
  map_mul' := q8Fun_mul

set_option maxRecDepth 100000 in
theorem mem_range_q8Hom_of_pow_eight :
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), g ^ 8 = 1 → ∃ x, q8Fun x = g := by
  decide

theorem sl23_cases (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (h8 : 8 ∣ Nat.card S) : Nonempty (S ≃* QuaternionGroup 2) ∨ S = ⊤ := by
  have h24 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
    rw [Matrix.card_SL_field, ZMod.card]
    simp [Fin.prod_univ_two]
  have hdvd : Nat.card S ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card S
  obtain ⟨k, hk⟩ := h8
  have hk3 : k ∣ 3 := by
    rw [hk, show (24 : ℕ) = 8 * 3 from rfl] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8) hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
  · left
    have hinj := q8Fun_injective
    have hR : q8Hom.range = S := by
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · intro g hg
        have h1 : (⟨g, hg⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
        rw [hk, mul_one] at h1
        obtain ⟨x, hx⟩ := mem_range_q8Hom_of_pow_eight g (by simpa using congrArg Subtype.val h1)
        exact ⟨x, hx⟩
      · rw [hk, mul_one, ← Nat.card_congr (MonoidHom.ofInjective (f := q8Hom) hinj).toEquiv]
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    exact ⟨(MulEquiv.subgroupCongr hR.symm).trans (MonoidHom.ofInjective (f := q8Hom) hinj).symm⟩
  · right
    exact Subgroup.eq_top_of_card_eq S (by rw [hk, h24])

section TypeOne

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem not_mem_zPi_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K y 1) : y ∉ zPi π 3 (p ^ f) K := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := h1
  intro hy
  have hcz : y * z ∈ zPi π 3 (p ^ f) K := mul_mem hy hz
  have hs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hcz
  have hgc := commute_of_mem_statedScalars hs g
  have hconj : g⁻¹ * (y * z) * g = y * z := by rw [mul_assoc, ← hgc, inv_mul_cancel_left]
  rw [hconj] at hD
  obtain ⟨c, hc⟩ := hs
  have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hD
  have h22 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hD
  simp only [← hc, coe_scalar_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, coe_diagTau_eq_diagonal, Matrix.diagonal_apply_eq] at h00 h22
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h00 h22
  exact hτ1 (h00.symm.trans h22)

theorem type1_conj_mul (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {a₁ s z : GL (Fin 3) K}
    (h1 : Type123 π (p ^ f) K a₁ 1) (hs : s ∈ glPi π 3 (p ^ f) K)
    (hz : z ∈ zPi π 3 (p ^ f) K) : Type123 π (p ^ f) K (s * a₁ * s⁻¹ * z) 1 := by
  obtain ⟨τ, hτ, hτ1, z₁, hz₁, g₁, hg₁, hD⟩ := h1
  refine ⟨τ, hτ, hτ1, z⁻¹ * z₁, mul_mem (inv_mem hz) hz₁, s * g₁, mul_mem hs hg₁, ?_⟩
  have hz₁c : ∀ g : GL (Fin 3) K, g * z₁ = z₁ * g :=
    commute_of_mem_statedScalars (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₁)
  have hs₁ : s⁻¹ * z₁ * s = z₁ := by
    rw [mul_assoc, ← hz₁c s, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (s * g₁)⁻¹ * (s * a₁ * s⁻¹ * z * (z⁻¹ * z₁)) * (s * g₁) =
      g₁⁻¹ * (a₁ * (s⁻¹ * z₁ * s)) * g₁ := by group
    _ = g₁⁻¹ * (a₁ * z₁) * g₁ := by rw [hs₁]
    _ = diagTau hτ := hD

end TypeOne

section Frame

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem false_of_frame_of_transitive (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {E : Subgroup H}
    (hE : ∀ a ∈ E, ∃ y, IsPGLAtP e a y) (h3 : ∀ a ∈ E, a ^ 3 = 1)
    (h9 : Nat.card (pglHomP hK hq E hE).range = 9) {b : Fin 3 → (Fin 3 → K)}
    (hb : LinearIndependent K b)
    (hd : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHomP hK hq E hE).range →
        ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K).mulVec (b i) = c • b i)
    (htrans : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer (E : Set H), n * x * n⁻¹ = y) : False := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set R := (pglHomP hK hq E hE).range with hR
  set D : Subgroup (GL (Fin 3) K) :=
    R.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hD
  have hmemD : ∀ y, y ∈ D ↔ (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R ∧
      y ∈ glPi π 3 (p ^ f) K := fun y => Iff.rfl
  have hRpow := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hE) h3
  have hmap : D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = R := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ((hmemD y).mp hy).1
    · rintro x ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hE a a.2
      refine ⟨y, (hmemD y).mpr ⟨mk_mem_range_pglHomP a.2 hy, hy.1⟩, ?_⟩
      exact (pglHomP_apply a hy).symm
  have hC : IsTypeC π (p ^ f) K D := by
    refine ⟨inf_le_right, fun a ha => ?_, by rw [hmap, h9], b, hb, fun a ha => hd a
      ((hmemD a).mp ha).1⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hRpow _ ((hmemD a).mp ha).1
  obtain ⟨a₁, ha₁D, ha₁T, hchar⟩ := isTypeC_types hK hq hC
  obtain ⟨ha₁R, ha₁H⟩ := (hmemD a₁).mp ha₁D
  set m := (a₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) with hm
  have hm3 : m ^ 3 = 1 := hRpow m ha₁R
  obtain ⟨r, hrR, hrm⟩ : ∃ r ∈ R, r ∉ Subgroup.zpowers m := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ Subgroup.zpowers m := fun r hr => hcon r hr
    have : Finite (Subgroup.zpowers m) :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hm3⟩).finite_zpowers
    have h1 := Subgroup.card_le_of_le hle
    rw [h9, Nat.card_zpowers] at h1
    have h2 : orderOf m ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hm3
    omega
  have hrR' := hrR
  obtain ⟨⟨x, hx⟩, hxr⟩ := hrR
  obtain ⟨a, ha⟩ := hE x hx
  have hra : r = (a : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
    rw [← hxr]
    exact pglHomP_apply ⟨x, hx⟩ ha
  have haD : a ∈ D := (hmemD a).mpr ⟨hra ▸ hrR', ha.1⟩
  have haZ : a ∉ StatedScalars (Fin 3) K := fun h => hrm (by
    rw [hra, (QuotientGroup.eq_one_iff a).mpr h]
    exact Subgroup.one_mem _)
  have hnot1 : ¬ Type123 π (p ^ f) K a 1 := by
    intro h1
    rcases (hchar a haD haZ).1.mp h1 with h | h
    · apply hrm
      have : (a : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = m := by
        rw [hm, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
        exact h
      rw [hra, this]
      exact Subgroup.mem_zpowers m
    · apply hrm
      have : (a : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) = m⁻¹ := by
        rw [hm, ← QuotientGroup.mk_inv, QuotientGroup.eq_iff_div_mem, div_inv_eq_mul]
        exact h
      rw [hra, this]
      exact inv_mem (Subgroup.mem_zpowers m)
  obtain ⟨x₁, hx₁, hx₁a⟩ := exists_isPGLAtP_of_mk_mem ha₁H ha₁R
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hrm
    have h1 : (⟨1, hx⟩ : E) = 1 := rfl
    rw [← hxr, h1, map_one]
    exact Subgroup.one_mem _
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    have h1 := isPGLAtP_inv_mul_mem hK hq (isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _))
      hx₁a
    rw [inv_one, one_mul] at h1
    exact not_mem_zPi_of_type1 hK hq ha₁T ((zPi_eq hπ hq' hτ hτ1) ▸ ⟨ha₁H, h1⟩)
  obtain ⟨n, ⟨hnL, -⟩, hn⟩ := htrans x₁ hx₁ hx₁1 x hx hx1
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨n, hnL⟩).2
  have hns : IsPGLAtP e n s := isPGLAtP_of_mem e hπ hnL hs hse.symm
  have hns' : IsPGLAtP e n⁻¹ s⁻¹ := by
    refine isPGLAtP_of_mem e hπ (L.inv_mem hnL) (inv_mem hs) ?_
    have h1 : (⟨n⁻¹, L.inv_mem hnL⟩ : L) = (⟨n, hnL⟩ : L)⁻¹ := rfl
    rw [h1, map_inv, Subgroup.coe_inv, ← hse, map_inv]
  have hxs : IsPGLAtP e x (s * a₁ * s⁻¹) := by
    rw [← hn]
    exact isPGLAtP_mul e (isPGLAtP_mul e hns hx₁a) hns'
  have hz := isPGLAtP_inv_mul_mem hK hq hxs ha
  have hsH := slPi_le_glPi hπ hs
  have hzH : (s * a₁ * s⁻¹)⁻¹ * a ∈ glPi π 3 (p ^ f) K :=
    (glPi π 3 (p ^ f) K).mul_mem ((glPi π 3 (p ^ f) K).inv_mem
      ((glPi π 3 (p ^ f) K).mul_mem ((glPi π 3 (p ^ f) K).mul_mem hsH ha₁H)
        ((glPi π 3 (p ^ f) K).inv_mem hsH))) ha.1
  have hzPi : (s * a₁ * s⁻¹)⁻¹ * a ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.mpr ⟨hzH, hz⟩
  have h1 := type1_conj_mul hK hq ha₁T hsH hzPi
  rw [show s * a₁ * s⁻¹ * ((s * a₁ * s⁻¹)⁻¹ * a) = a by group] at h1
  exact hnot1 h1

end Frame

section Det

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_isPGLAtP_of_mem (hπ : π = false → UnitaryFieldData p f K)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {l : H} (hl : l ∈ L) :
    ∃ s ∈ slPi π 3 (p ^ f) K, IsPGLAtP e l s ∧ IsPGLAtP e l⁻¹ s⁻¹ := by
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
  refine ⟨s, hs, isPGLAtP_of_mem e hπ hl hs hse.symm, ?_⟩
  refine isPGLAtP_of_mem e hπ (L.inv_mem hl) (inv_mem hs) ?_
  have h1 : (⟨l⁻¹, L.inv_mem hl⟩ : L) = (⟨l, hl⟩ : L)⁻¹ := rfl
  rw [h1, map_inv, Subgroup.coe_inv, ← hse, map_inv]

theorem modEq_of_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {g x₁ x₂ : H} (hgL : g ∈ L)
    {y₁ y₂ : GL (Fin 3) K} (h₁ : IsPGLAtP e x₁ y₁) (h₂ : IsPGLAtP e x₂ y₂) {ζ : Kˣ}
    (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂) {a b c d : ℕ}
    (hab : g * x₁ * g⁻¹ = x₁ ^ a * x₂ ^ b) (hcd : g * x₂ * g⁻¹ = x₁ ^ c * x₂ ^ d) :
    1 + b * c ≡ a * d [MOD 3] := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set sc := Matrix.GeneralLinearGroup.scalar (Fin 3) ζ with hsc
  have hscc : ∀ w : GL (Fin 3) K, w * sc = sc * w := fun w =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ w).eq
  obtain ⟨s, -, hs, hs'⟩ := exists_isPGLAtP_of_mem hπ e hgL
  have hu : IsPGLAtP e (x₁ ^ a * x₂ ^ b) (s * y₁ * s⁻¹) := by
    rw [← hab]
    exact isPGLAtP_mul e (isPGLAtP_mul e hs h₁) hs'
  have hv : IsPGLAtP e (x₁ ^ c * x₂ ^ d) (s * y₂ * s⁻¹) := by
    rw [← hcd]
    exact isPGLAtP_mul e (isPGLAtP_mul e hs h₂) hs'
  have hu' := isPGLAtP_mul e (isPGLAtP_pow h₁ a) (isPGLAtP_pow h₂ b)
  have hv' := isPGLAtP_mul e (isPGLAtP_pow h₁ c) (isPGLAtP_pow h₂ d)
  have hsheis : (s * y₁ * s⁻¹) * (s * y₂ * s⁻¹) * (s * y₁ * s⁻¹)⁻¹ = sc * (s * y₂ * s⁻¹) := by
    calc (s * y₁ * s⁻¹) * (s * y₂ * s⁻¹) * (s * y₁ * s⁻¹)⁻¹ = s * (y₁ * y₂ * y₁⁻¹) * s⁻¹ := by
          group
      _ = s * (sc * y₂) * s⁻¹ := by rw [hζ]
      _ = (s * sc) * y₂ * s⁻¹ := by group
      _ = sc * (s * y₂ * s⁻¹) := by rw [hscc s]; group
  have huv := heis_of_mul_scalar (isPGLAtP_inv_mul_mem hK hq hu hu')
    (isPGLAtP_inv_mul_mem hK hq hv hv') hsheis
  have hrel : y₁ * y₂ = sc * y₂ * y₁ := by
    calc y₁ * y₂ = (y₁ * y₂ * y₁⁻¹) * y₁ := by group
      _ = sc * y₂ * y₁ := by rw [hζ]
  rw [heis_conj_pow hscc hrel a b c d] at huv
  have hsc' : sc ^ (a * d) * (sc ^ (b * c))⁻¹ = sc := mul_right_cancel huv
  have hsc'' : sc ^ (1 + b * c) = sc ^ (a * d) := by
    calc sc ^ (1 + b * c) = sc * sc ^ (b * c) := by rw [pow_add, pow_one]
      _ = sc ^ (a * d) * (sc ^ (b * c))⁻¹ * sc ^ (b * c) := by rw [hsc']
      _ = sc ^ (a * d) := by group
  rw [hsc, ← map_pow, ← map_pow] at hsc''
  have hζpow : ζ ^ (1 + b * c) = ζ ^ (a * d) := scalar_injective_three hsc''
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  rw [pow_eq_pow_iff_modEq, hord] at hζpow
  exact hζpow

end Det

section Auto

variable {H : Type} [Group H] [Finite H]

theorem nonempty_autIn_inf_equiv {L A : Subgroup H} {c : H}
    (hc : c ∈ Subgroup.centralizer (L : Set H)) (hA : A = (A ⊓ L) ⊔ Subgroup.zpowers c) :
    Nonempty (autIn L A ≃* autIn L (A ⊓ L)) := by
  set E := A ⊓ L with hEdef
  set M := L ⊓ Subgroup.normalizer (A : Set H) with hM
  have hML : M ≤ L := inf_le_left
  have hMN : M ≤ Subgroup.normalizer (A : Set H) := inf_le_right
  have hMN' : M ≤ Subgroup.normalizer (E : Set H) := fun g hg =>
    Item424Proof.mem_normalizer_inf (hML hg) (hMN hg)
  have hcg : ∀ g ∈ L, g * c * g⁻¹ = c := fun g hg => by
    rw [Subgroup.mem_centralizer_iff.mp hc g hg, mul_inv_cancel_right]
  have hNA : ∀ g ∈ L, g ∈ Subgroup.normalizer (E : Set H) →
      g ∈ Subgroup.normalizer (A : Set H) := by
    intro g hgL hgE
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : A ≤ A.comap (MulAut.conj g).toMonoidHom := by
      conv_lhs => rw [hA]
      refine sup_le (fun y hy => ?_) ?_
      · show g * y * g⁻¹ ∈ A
        exact ((Subgroup.mem_normalizer_iff.mp hgE y).mp hy).1
      · rw [Subgroup.zpowers_le]
        show g * c * g⁻¹ ∈ A
        rw [hcg g hgL]
        have : c ∈ (A ⊓ L) ⊔ Subgroup.zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
        rwa [← hA] at this
    exact hle hx
  let Φ₁ : M →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hMN)
  let Φ₂ : M →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hMN')
  have hr₁ : Φ₁.range = autIn L A := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hr₂ : Φ₂.range = autIn L E := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact mem_autIn_iff.mpr ⟨g, hMN' g.2, hML g.2, rfl⟩
    · intro σ hσ
      obtain ⟨g, hgN, hgL, rfl⟩ := mem_autIn_iff.mp hσ
      exact ⟨⟨g, hgL, hNA g hgL hgN⟩, rfl⟩
  have hk : Φ₁.ker = Φ₂.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      refine MulEquiv.ext fun y => Subtype.ext ?_
      have h2 := congrArg (fun φ : MulAut A => ((φ ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ : A) : H)) h1
      exact h2
    · intro h1
      have hcen : ∀ y ∈ E, (g : H) * y * (g : H)⁻¹ = y := by
        intro y hy
        have h2 := congrArg (fun φ : MulAut E => ((φ ⟨y, hy⟩ : E) : H)) h1
        exact h2
      have hle : A ≤ Subgroup.centralizer ({(g : H)} : Set H) := by
        conv_lhs => rw [hA]
        refine sup_le (fun y hy => ?_) ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc y * (g : H) = ((g : H) * y * (g : H)⁻¹) * g := by rw [hcen y hy]
            _ = g * y := by group
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          calc c * (g : H) = ((g : H) * c * (g : H)⁻¹) * g := by rw [hcg g (hML g.2)]
            _ = g * c := by group
      refine MulEquiv.ext fun y => Subtype.ext ?_
      change (g : H) * y * (g : H)⁻¹ = y
      have := Subgroup.mem_centralizer_singleton_iff.mp (hle y.2)
      rw [← this, mul_inv_cancel_right]
  obtain ⟨φ⟩ := Item424Proof.nonempty_range_mulEquiv_of_ker_eq Φ₁ Φ₂ hk
  exact ⟨(MulEquiv.subgroupCongr hr₁.symm).trans (φ.trans (MulEquiv.subgroupCongr hr₂))⟩

omit [Finite H] in
theorem eight_dvd_card_autIn {L E : Subgroup H} (hE9 : Nat.card E = 9) {x₁ : H} (hx₁ : x₁ ∈ E)
    (hx₁1 : x₁ ≠ 1)
    (htrans : ∀ y ∈ E, y ≠ 1 → ∃ n ∈ L ⊓ Subgroup.normalizer (E : Set H), n * x₁ * n⁻¹ = y) :
    8 ∣ Nat.card (autIn L E) := by
  set S := autIn L E with hS
  set x : E := ⟨x₁, hx₁⟩ with hx
  have horb : MulAction.orbit S x = (Set.univ : Set E) \ {1} := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨σ, rfl⟩ h1
      apply hx₁1
      have h2 : (σ : MulAut E) x = 1 := h1
      rw [MulEquiv.map_eq_one_iff] at h2
      exact congrArg Subtype.val h2
    · intro hy1
      obtain ⟨n, ⟨hnL, hnN⟩, hn⟩ := htrans y y.2 (fun h => hy1 (Subtype.ext h))
      refine ⟨⟨E.normalizerMonoidHom ⟨n, hnN⟩, mem_autIn_iff.mpr ⟨n, hnN, hnL, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      exact hn
  have hcard : (MulAction.orbit S x).ncard = 8 := by
    rw [horb, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hE9]
  rw [← hcard, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

end Auto

section Embed

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_injective_sl23 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {E : Subgroup H}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {x₁ x₂ : H}
    (hx₁ : x₁ ∈ E) (hx₂ : x₂ ∈ E) {y₁ y₂ : GL (Fin 3) K} (h₁ : IsPGLAtP e x₁ y₁)
    (h₂ : IsPGLAtP e x₂ y₂) {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    ∃ Ψ : autIn L E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Injective Ψ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set sc := Matrix.GeneralLinearGroup.scalar (Fin 3) ζ with hsc
  set u : E := ⟨x₁, hx₁⟩ with hu
  set v : E := ⟨x₂, hx₂⟩ with hv
  have hu3 : u ^ 3 = 1 := Subtype.ext (hEe.2 x₁ hx₁)
  have hv3 : v ^ 3 = 1 := Subtype.ext (hEe.2 x₂ hx₂)
  have huv : u * v = v * u := hEe.1.is_comm.comm u v
  have hcomm_of : ∀ k : ℕ, IsPGLAtP e (x₁ ^ k) y₂ → False := by
    intro k hk
    have hs := isPGLAtP_inv_mul_mem hK hq (isPGLAtP_pow h₁ k) hk
    obtain ⟨w, hw⟩ := hs
    have hy₂ : y₂ = y₁ ^ k * Matrix.GeneralLinearGroup.scalar (Fin 3) w := by
      rw [hw]; group
    have h1 : y₁ * y₂ * y₁⁻¹ = y₂ := by
      rw [hy₂]
      have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar w y₁).eq.symm
      calc y₁ * (y₁ ^ k * Matrix.GeneralLinearGroup.scalar (Fin 3) w) * y₁⁻¹ =
          (y₁ * y₁ ^ k) * Matrix.GeneralLinearGroup.scalar (Fin 3) w * y₁⁻¹ := by group
        _ = (y₁ ^ k * y₁) * Matrix.GeneralLinearGroup.scalar (Fin 3) w * y₁⁻¹ := by
            rw [(Commute.self_pow y₁ k).eq]
        _ = y₁ ^ k * (y₁ * Matrix.GeneralLinearGroup.scalar (Fin 3) w) * y₁⁻¹ := by group
        _ = y₁ ^ k * (Matrix.GeneralLinearGroup.scalar (Fin 3) w * y₁) * y₁⁻¹ := by rw [hc]
        _ = y₁ ^ k * Matrix.GeneralLinearGroup.scalar (Fin 3) w := by group
    rw [hζ] at h1
    have h2 : sc = 1 := by
      have := congrArg (· * y₂⁻¹) h1
      simpa using this
    exact hζ1 (scalar_injective_three (by rw [map_one]; exact h2))
  have hu1 : u ≠ 1 := by
    intro h
    have hx : x₁ = 1 := congrArg Subtype.val h
    apply hcomm_of 0
    rw [pow_zero]
    have hk := isPGLAtP_of_mem_centralizer e (Subgroup.one_mem (Subgroup.centralizer (L : Set H)))
    have h1 := isPGLAtP_inv_mul_mem hK hq (hx ▸ h₁) hk
    rw [mul_one] at h1
    have h2 : y₁ ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      have := inv_mem h1
      rwa [inv_inv] at this
    exfalso
    have hc : y₁ * y₂ * y₁⁻¹ = y₂ := by
      rw [(Subgroup.mem_center_iff.mp h2 y₂).symm, mul_inv_cancel_right]
    rw [hζ] at hc
    have h3 : sc = 1 := by
      have := congrArg (· * y₂⁻¹) hc
      simpa using this
    exact hζ1 (scalar_injective_three (by rw [map_one]; exact h3))
  have hvu : v ∉ Subgroup.zpowers u := by
    intro h
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr h)
    apply hcomm_of k
    have hk' : x₁ ^ k = x₂ := congrArg Subtype.val hk
    rw [hk']
    exact h₂
  set fE := coordOfPair hE9 hu3 hv3 huv hu1 hvu with hfE
  let Ψ₀ : MulAut E →* GL (Fin 2) (ZMod 3) :=
    glEquivTwo.symm.toMonoidHom.comp (Sec12.coordHom fE)
  have hΨ₀inj : Function.Injective Ψ₀ :=
    glEquivTwo.symm.injective.comp (Sec12.coordHom_injective fE)
  have hentry : ∀ (σ : MulAut E) (i j : Fin 2),
      (Ψ₀ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j =
        Multiplicative.toAdd (fE.symm (σ (fE (Multiplicative.ofAdd (Pi.single j 1))))) i := by
    intro σ i j
    have h1 : glEquivTwo (Ψ₀ σ) = Sec12.coordHom fE σ := by
      simp [Ψ₀]
    have h2 : glEquivTwo (Ψ₀ σ) (Pi.single j 1) = Sec12.coordHom fE σ (Pi.single j 1) := by
      rw [h1]
    rw [glEquivTwo_apply, Matrix.mulVec_single_one, Sec12.coordHom_apply] at h2
    exact congrFun h2 i
  have hf0 : fE (Multiplicative.ofAdd (Pi.single 0 1)) = u := by
    rw [hfE, coordOfPair_apply]
    simp [ZMod.val_one]
  have hf1 : fE (Multiplicative.ofAdd (Pi.single 1 1)) = v := by
    rw [hfE, coordOfPair_apply]
    simp [ZMod.val_one]
  have hfapp : ∀ w : Fin 2 → ZMod 3, ((fE (Multiplicative.ofAdd w) : E) : H) =
      x₁ ^ (w 0).val * x₂ ^ (w 1).val := by
    intro w
    rw [hfE, coordOfPair_apply, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
  have hdet : ∀ σ ∈ autIn L E, (Ψ₀ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    intro σ hσ
    obtain ⟨g, hgN, hgL, rfl⟩ := mem_autIn_iff.mp hσ
    set σ := E.normalizerMonoidHom ⟨g, hgN⟩ with hσdef
    set w₁ := Multiplicative.toAdd (fE.symm (σ u)) with hw₁
    set w₂ := Multiplicative.toAdd (fE.symm (σ v)) with hw₂
    have hσu : g * x₁ * g⁻¹ = x₁ ^ (w₁ 0).val * x₂ ^ (w₁ 1).val := by
      rw [← hfapp, hw₁, ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rfl
    have hσv : g * x₂ * g⁻¹ = x₁ ^ (w₂ 0).val * x₂ ^ (w₂ 1).val := by
      rw [← hfapp, hw₂, ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rfl
    have hmod := modEq_of_heis hK hq hgL h₁ h₂ hζ1 hζ3 hζ hσu hσv
    rw [Matrix.det_fin_two, hentry, hentry, hentry, hentry, hf0, hf1]
    rw [← hw₁, ← hw₂]
    have hcast := (ZMod.natCast_eq_natCast_iff _ _ 3).mpr hmod
    push_cast [ZMod.natCast_val, ZMod.cast_id', id] at hcast
    rw [← hcast]
    ring
  refine ⟨{ toFun := fun σ => ⟨(Ψ₀ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)), hdet σ σ.2⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    simp
  · intro σ τ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rfl
  · intro σ τ h
    have h1 : (Ψ₀ σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = Ψ₀ τ := congrArg Subtype.val h
    exact Subtype.ext (hΨ₀inj (Units.ext h1))

end Embed

end Res423Four

open Res423Four

theorem k423L3HeisFrame_holds : K423L3HeisFrame := by
  intro H _ _ L _ π p f K _ hLq hK hq hq2 e A c hA hA27 hc3 hAc hpgl hsup htype htrans
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect L := hLq.1
  have := isPerfect_projImage_of_equiv e
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAe := hA.prop
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set H) := hAc ▸ Subgroup.mem_zpowers c
  set E := A ⊓ L with hEdef
  have hALC : A ≤ L ⊔ Subgroup.centralizer (L : Set H) := by
    intro x hx
    have h1 : x ∈ A ⊔ L := Subgroup.mem_sup_left hx
    rw [hsup] at h1
    exact (sup_le ((Subgroup.zpowers_le.mpr hcAC.2).trans le_sup_right) le_sup_left) h1
  have hE9 : Nat.card E = 9 := by
    have h1 : Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set H)) : Subgroup H) =
        Nat.card (A ⊓ L : Subgroup H) * 3 := card_inf_sup_centralizer hA hLC hc3 hAc
    rw [inf_eq_left.mpr hALC, hA27] at h1
    change Nat.card (A ⊓ L : Subgroup H) = 9
    omega
  have hAeq : A = E ⊔ Subgroup.zpowers c := by
    have h1 := inf_sup_centralizer_eq hA hLC hAc
    rwa [inf_eq_left.mpr hALC] at h1
  obtain ⟨eAE⟩ := nonempty_autIn_inf_equiv hcAC.2 hAeq
  have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (hAcomm x x.2.1 y y.2.1)⟩⟩, fun x hx => hA3 x hx.1⟩
  have hpglE : ∀ x ∈ E, ∃ y, IsPGLAtP e x y := fun x hx => hpgl x hx.1
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => hA3 x hx.1
  have hEC : E ⊓ Subgroup.centralizer (L : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ L ⊓ Subgroup.centralizer (L : Set H) := ⟨hx.1.2, hx.2⟩
    rwa [hLC] at h1
  have hR9 : Nat.card (pglHomP hK hq E hpglE).range = 9 := by
    have h1 := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (A' := E) (hA' := hpglE)
    rw [hEC, Subgroup.card_bot, one_mul, hE9] at h1
    exact h1.symm
  have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpglE)
    (fun x hx y hy => hAcomm x hx.1 y hy.1)
  have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpglE) hE3
  rcases frame_or_heis h3K hτ hτ1 _ hRcomm hRexp (by rw [hR9]; norm_num) with
    ⟨b, hb, hd, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · exact (false_of_frame_of_transitive hK hq hpglE hE3 hR9 hb hd htrans).elim
  obtain ⟨⟨x₁, hx₁⟩, hx₁y⟩ := hy₁
  obtain ⟨⟨x₂, hx₂⟩, hx₂y⟩ := hy₂
  obtain ⟨z₁, hz₁⟩ := hpglE x₁ hx₁
  obtain ⟨z₂, hz₂⟩ := hpglE x₂ hx₂
  have hm₁ : y₁⁻¹ * z₁ ∈ StatedScalars (Fin 3) K :=
    QuotientGroup.eq.mp (hx₁y.symm.trans (pglHomP_apply ⟨x₁, hx₁⟩ hz₁))
  have hm₂ : y₂⁻¹ * z₂ ∈ StatedScalars (Fin 3) K :=
    QuotientGroup.eq.mp (hx₂y.symm.trans (pglHomP_apply ⟨x₂, hx₂⟩ hz₂))
  have hheis := heis_of_mul_scalar hm₁ hm₂ hζ
  set sc := Matrix.GeneralLinearGroup.scalar (Fin 3) ζ with hsc
  have hscc : ∀ w : GL (Fin 3) K, w * sc = sc * w := fun w =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ w).eq
  have hrel : z₁ * z₂ = sc * z₂ * z₁ := by
    calc z₁ * z₂ = (z₁ * z₂ * z₁⁻¹) * z₁ := by group
      _ = sc * z₂ * z₁ := by rw [hheis]
  have hζ3 : ζ ^ 3 = 1 := by
    have hz₁3 := mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPiP hK hq (hE3 x₁ hx₁) hz₁)
    have h1 := pow_mul_pow_heis hscc hrel 3 1
    rw [pow_one, mul_one] at h1
    have h2 : z₂ * z₁ ^ 3 = sc ^ 3 * z₂ * z₁ ^ 3 := by
      rw [commute_of_mem_statedScalars hz₁3 z₂]
      exact h1
    have h3 : z₂ = sc ^ 3 * z₂ := mul_right_cancel h2
    have h4 : sc ^ 3 = 1 := mul_right_cancel (h3.symm.trans (one_mul z₂).symm)
    apply scalar_injective_three
    rw [map_pow, map_one]
    exact h4
  obtain ⟨Ψ, hΨ⟩ := exists_injective_sl23 (L := L) hK hq hEe hE9 hx₁ hx₂ hz₁ hz₂ hζ1 hζ3 hheis
  set S := Ψ.range with hS
  let eS : autIn L E ≃* S := MonoidHom.ofInjective hΨ
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    have h1 := isPGLAtP_inv_mul_mem hK hq
      (isPGLAtP_of_mem_centralizer e (Subgroup.one_mem (Subgroup.centralizer (L : Set H)))) hz₁
    rw [inv_one, one_mul] at h1
    have h2 : z₁ * z₂ * z₁⁻¹ = z₂ := by
      rw [← commute_of_mem_statedScalars h1 z₂, mul_inv_cancel_right]
    rw [hheis] at h2
    have h3 : sc = 1 := mul_right_cancel (h2.trans (one_mul z₂).symm)
    exact hζ1 (scalar_injective_three (by rw [map_one]; exact h3))
  have h8 : 8 ∣ Nat.card S := by
    rw [← Nat.card_congr eS.toEquiv]
    exact eight_dvd_card_autIn hE9 hx₁ hx₁1 (fun y hy hy1 => htrans x₁ hx₁ hx₁1 y hy hy1)
  rcases sl23_cases S h8 with ⟨⟨eQ⟩⟩ | hStop
  · exact Or.inl ⟨eAE.trans (eS.trans eQ)⟩
  · exact Or.inr ⟨eAE.trans (eS.trans ((MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv))⟩

end CFSG.RankThree.PartTwo.Sec4
