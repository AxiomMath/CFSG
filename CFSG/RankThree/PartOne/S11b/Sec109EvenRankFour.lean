module

public import CFSG.RankThree.PartOne.S11b.Sec109SixFiveArith
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Rot
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.SectionRank.ClassicalEven (rotMatrix rotCol det_rotMatrix rotMatrix_pow_three
  rotMatrix_commute rotMatrix_mulVec_left rotMatrix_mulVec_of_ne)
open scoped Matrix

namespace Sec109

section Radical

variable {n : ℕ} {K : Type*} [Field K]

def PlaneSupported (v : Fin n → K) : Prop :=
  ∀ j : Fin n, 2 ≤ (j : ℕ) → v j = 0

theorem PlaneSupported.add {v w : Fin n → K} (hv : PlaneSupported v) (hw : PlaneSupported w) :
    PlaneSupported (v + w) :=
  fun j hj => by simp [hv j hj, hw j hj]

theorem PlaneSupported.neg {v : Fin n → K} (hv : PlaneSupported v) : PlaneSupported (-v) :=
  fun j hj => by simp [hv j hj]

theorem planeSupported_zero : PlaneSupported (0 : Fin n → K) :=
  fun _ _ => rfl

def twoPlaneRadical (n : ℕ) (K : Type*) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) K) where
  carrier := {A | (∀ v : Fin n → K, PlaneSupported (A • v - v)) ∧
    ∀ v : Fin n → K, PlaneSupported v → A • v = v}
  one_mem' := ⟨fun v => by simpa using planeSupported_zero, fun v _ => one_smul _ _⟩
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := (hA1 (B • v)).add (hB1 v)
      simpa [mul_smul] using this
    · rw [mul_smul, hB2 v hv, hA2 v hv]
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have h := (hA1 (A⁻¹ • v)).neg
      rw [smul_inv_smul] at h
      simpa using h
    · have := hA2 v hv
      calc A⁻¹ • v = A⁻¹ • (A • v) := by rw [this]
        _ = v := inv_smul_smul _ _

theorem twoPlaneRadical_smul_smul (h2 : (2 : K) = 0) {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hA : A ∈ twoPlaneRadical n K) (v : Fin n → K) : A • A • v = v := by
  have hw : A • (A • v - v) = A • v - v := hA.2 _ (hA.1 v)
  have hAv : A • v = v + (A • v - v) := by abel
  have : A • A • v = A • v + (A • v - v) := by
    calc A • A • v = A • (v + (A • v - v)) := by rw [← hAv]
      _ = A • v + A • (A • v - v) := smul_add _ _ _
      _ = A • v + (A • v - v) := by rw [hw]
  rw [this]
  ext j
  simp only [Pi.add_apply, Pi.sub_apply]
  linear_combination ((A • v) j - v j) * h2

theorem twoPlaneRadical_mul_self (h2 : (2 : K) = 0) {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hA : A ∈ twoPlaneRadical n K) : A * A = 1 := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  have h1 : (↑(A * A) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1 := by
    have := twoPlaneRadical_smul_smul h2 hA (Pi.single i 1)
    rw [← mul_smul] at this
    exact this
  rw [h1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem twoPlaneRadical_isPGroup (h2 : (2 : K) = 0) : IsPGroup 2 (twoPlaneRadical n K) :=
  fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (twoPlaneRadical_mul_self h2 g.2)⟩

theorem twoPlaneRadical_ne_bot (hn : 3 ≤ n) : twoPlaneRadical n K ≠ ⊥ := by
  intro hbot
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have key : ∀ v : Fin n → K, Matrix.SpecialLinearGroup.transvection h02 (1 : K) • v =
      v + (v ⟨2, by omega⟩) • Pi.single (⟨0, by omega⟩ : Fin n) 1 := by
    intro v
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe]
    change ((1 + Matrix.single _ _ 1 : Matrix (Fin n) (Fin n) K)) *ᵥ v = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul]
  have hmem : Matrix.SpecialLinearGroup.transvection h02 (1 : K) ∈ twoPlaneRadical n K := by
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [key, add_sub_cancel_left]
      intro j hj
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      subst h
      simp at hj
    · rw [key, hv _ (by simp), zero_smul, add_zero]
  rw [hbot, Subgroup.mem_bot] at hmem
  have h := key (Pi.single ⟨2, by omega⟩ 1)
  rw [hmem, one_smul] at h
  have := congrFun h ⟨0, by omega⟩
  simp [Fin.ext_iff] at this

def twoPlaneLevi (n : ℕ) (K : Type*) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) K) where
  carrier := {g | ∀ v : Fin n → K, PlaneSupported v →
    PlaneSupported (g • v) ∧ PlaneSupported (g⁻¹ • v)}
  one_mem' := fun v hv => by simpa using And.intro hv hv
  mul_mem' := by
    rintro g h hg hh v hv
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact (hg _ (hh v hv).1).1
    · rw [_root_.mul_inv_rev, mul_smul]
      exact (hh _ (hg v hv).2).2
  inv_mem' := fun {g} hg v hv => by
    simpa using (hg v hv).symm

theorem twoPlaneLevi_le_normalizer :
    twoPlaneLevi n K ≤ Subgroup.normalizer (twoPlaneRadical n K : Set _) := by
  have conj : ∀ g ∈ twoPlaneLevi n K, ∀ h ∈ twoPlaneRadical n K,
      g * h * g⁻¹ ∈ twoPlaneRadical n K := by
    intro g hg h hh
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have : (g * h * g⁻¹) • v - v = g • (h • (g⁻¹ • v) - g⁻¹ • v) := by
        rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
      rw [this]
      exact (hg _ (hh.1 _)).1
    · have hv' := (hg v hv).2
      rw [mul_smul, mul_smul, hh.2 _ hv', smul_inv_smul]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj g hg h
  · intro h'
    have := conj g⁻¹ (inv_mem hg) _ h'
    simpa [mul_assoc] using this

end Radical

section Rotations

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def rotationSL (i j : Fin n) : Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨rotMatrix i j, det_rotMatrix i j⟩

theorem rotationSL_smul_def (i j : Fin n) (v : Fin n → K) :
    (rotationSL (K := K) i j) • v = rotMatrix i j *ᵥ v :=
  rfl

theorem rotationSL_pow_three (i j : Fin n) : rotationSL (K := K) i j ^ 3 = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact rotMatrix_pow_three i j)

theorem rotationSL_commute {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Commute (rotationSL (K := K) i j) (rotationSL k l) :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact (rotMatrix_commute hik hil hjk hjl).eq)

theorem rotMatrix_apply_eq_zero_of_planePair {i j k b : Fin n}
    (hij : (i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val)) (hk : 2 ≤ k.val)
    (hb : b.val < 2) : rotMatrix (K := K) i j k b = 0 := by
  simp only [rotMatrix, Matrix.of_apply, rotCol]
  split_ifs with h1 h2
  · have h1' : b.val = i.val := congrArg Fin.val h1
    have hk1 : ¬ (k.val = j.val) := by omega
    simp [Fin.ext_iff, hk1]
  · have h2' : b.val = j.val := congrArg Fin.val h2
    have hk1 : ¬ (k.val = i.val) := by omega
    have hk2 : ¬ (k.val = j.val) := by omega
    simp [Fin.ext_iff, hk1, hk2]
  · have hk1 : ¬ (k.val = b.val) := by omega
    simp [Fin.ext_iff, hk1]

theorem rotationSL_smul_planeSupported {i j : Fin n}
    (hij : (i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val)) {v : Fin n → K}
    (hv : PlaneSupported v) : PlaneSupported (rotationSL (K := K) i j • v) := by
  intro k hk
  rw [rotationSL_smul_def, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : 2 ≤ b.val
  · rw [hv b hb, mul_zero]
  · rw [rotMatrix_apply_eq_zero_of_planePair hij hk (by omega), zero_mul]

theorem rotationSL_mem_twoPlaneLevi {i j : Fin n}
    (hij : (i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val)) :
    rotationSL (K := K) i j ∈ twoPlaneLevi n K := by
  intro v hv
  have hinv : (rotationSL (K := K) i j)⁻¹ = rotationSL i j * rotationSL i j := by
    have h3 : rotationSL (K := K) i j * (rotationSL i j * rotationSL i j) = 1 := by
      rw [← pow_three]
      exact rotationSL_pow_three i j
    exact inv_eq_of_mul_eq_one_right h3
  refine ⟨rotationSL_smul_planeSupported hij hv, ?_⟩
  rw [hinv, mul_smul]
  exact rotationSL_smul_planeSupported hij (rotationSL_smul_planeSupported hij hv)

theorem sl_ne_of_smul_single {g h : Matrix.SpecialLinearGroup (Fin n) K} {a b : Fin n}
    (hab : a ≠ b) (hg : g • (Pi.single a 1 : Fin n → K) = Pi.single a 1)
    (hh : h • (Pi.single a 1 : Fin n → K) = Pi.single b 1) : g ≠ h := by
  intro hgh
  rw [hgh, hh] at hg
  have := congrFun hg b
  simp [hab.symm] at this

theorem rotationSL_smul_single_of_ne {i j b : Fin n} (hi : b ≠ i) (hj : b ≠ j) :
    rotationSL (K := K) i j • (Pi.single b 1 : Fin n → K) = Pi.single b 1 :=
  rotMatrix_mulVec_of_ne hi hj

theorem rotationSL_pow_smul_single_of_ne {i j b : Fin n} (hi : b ≠ i) (hj : b ≠ j) (m : ℕ) :
    (rotationSL (K := K) i j ^ m) • (Pi.single b 1 : Fin n → K) = Pi.single b 1 := by
  induction m with
  | zero => rw [pow_zero, one_smul]
  | succ m ih => rw [pow_succ, mul_smul, rotationSL_smul_single_of_ne hi hj, ih]

theorem rotationSL_smul_single_left (i j : Fin n) :
    rotationSL (K := K) i j • (Pi.single i 1 : Fin n → K) = Pi.single j 1 :=
  rotMatrix_mulVec_left i j

end Rotations

section ElementaryAbelian

theorem exists_elemAbelian_four_gens {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    {x y z w : G} (hxN : x ∈ N) (hyN : y ∈ N) (hzN : z ∈ N) (hwN : w ∈ N)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) (hw : w ^ 3 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hxw : Commute x w)
    (hyz : Commute y z) (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) (hz1 : ∀ n m : ℕ, x ^ n * y ^ m ≠ z)
    (hw1 : ∀ n m k : ℕ, x ^ n * y ^ m * z ^ k ≠ w) :
    ∃ X : Subgroup G, X ≤ N ∧ IsMulCommutative X ∧ (∀ g ∈ X, g ^ 3 = 1) ∧
      Nat.card X = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ 3 = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = 3 ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := CFSG.SectionRank.exists_extend hc₀ hp₀ hcard₀
    B₀.subtype Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := CFSG.SectionRank.exists_extend hc₁ hp₁ hcard₁ F₁
    hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ n m : ℕ, F₂ a = x ^ n * y ^ m := fun a => by
    obtain ⟨b, m, hb⟩ := hr₂ a
    obtain ⟨n, hn⟩ := hr₁' b
    exact ⟨n, m, by rw [hb, hn]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, hr₃⟩ := CFSG.SectionRank.exists_extend hc₂ hp₂ hcard₂ F₂
    hF₂ (y := z) hz
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, hnm⟩ := hr₂' a
      exact hz1 n m (hnm ▸ ha))
    (fun a => by
      obtain ⟨n, m, hnm⟩ := hr₂' a
      rw [hnm]
      exact (hxz.pow_left n).mul_left (hyz.pow_left m))
  have hr₃' : ∀ a, ∃ n m k : ℕ, F₃ a = x ^ n * y ^ m * z ^ k := fun a => by
    obtain ⟨b, k, hb⟩ := hr₃ a
    obtain ⟨n, m, hnm⟩ := hr₂' b
    exact ⟨n, m, k, by rw [hb, hnm]⟩
  obtain ⟨F₄, hF₄, hc₄, hp₄, hcard₄, hr₄⟩ := CFSG.SectionRank.exists_extend hc₃ hp₃ hcard₃ F₃
    hF₃ (y := w) hw
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, k, hnmk⟩ := hr₃' a
      exact hw1 n m k (hnmk ▸ ha))
    (fun a => by
      obtain ⟨n, m, k, hnmk⟩ := hr₃' a
      rw [hnmk]
      exact ((hxw.pow_left n).mul_left (hyw.pow_left m)).mul_left (hzw.pow_left k))
  refine ⟨F₄.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, l, hbl⟩ := hr₄ a
    obtain ⟨n, m, k, hnmk⟩ := hr₃' b
    rw [hbl, hnmk]
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.pow_mem hxN n) (N.pow_mem hyN m))
      (N.pow_mem hzN k)) (N.pow_mem hwN l)
  · exact ⟨⟨by
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      refine Subtype.ext ?_
      change F₄ a * F₄ b = F₄ b * F₄ a
      rw [← map_mul, ← map_mul, hc₄ a b]⟩⟩
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hp₄ a, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hF₄).toEquiv]
    exact hcard₄

end ElementaryAbelian

section Normalizer

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_elemAbelian_normalizer_radical [Finite K] (hn : 8 ≤ n) :
    ∃ X : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
      X ≤ Subgroup.normalizer (twoPlaneRadical n K : Set _) ∧ IsMulCommutative X ∧
        (∀ g ∈ X, g ^ 3 = 1) ∧ Nat.card X = 3 ^ 4 := by
  obtain ⟨ι, hι⟩ : ∃ ι : Fin 8 → Fin n, ι = Fin.castLE hn := ⟨_, rfl⟩
  have hinj : Function.Injective ι := hι ▸ Fin.castLE_injective hn
  have hval : ∀ a : Fin 8, (ι a : ℕ) = a := fun a => hι ▸ Fin.val_castLE _ _
  have hne : ∀ a b : Fin 8, a ≠ b → ι a ≠ ι b := fun a b h => hinj.ne h
  have hlevi : ∀ a b : Fin 8, ((a : ℕ) < 2 ∧ (b : ℕ) < 2) ∨ (2 ≤ (a : ℕ) ∧ 2 ≤ (b : ℕ)) →
      rotationSL (K := K) (ι a) (ι b) ∈ Subgroup.normalizer (twoPlaneRadical n K : Set _) :=
    fun a b h => twoPlaneLevi_le_normalizer
      (rotationSL_mem_twoPlaneLevi (by simpa only [hval] using h))
  refine exists_elemAbelian_four_gens (N := Subgroup.normalizer (twoPlaneRadical n K : Set _))
    (x := rotationSL (K := K) (ι 0) (ι 1)) (y := rotationSL (K := K) (ι 2) (ι 3))
    (z := rotationSL (K := K) (ι 4) (ι 5)) (w := rotationSL (K := K) (ι 6) (ι 7))
    (hlevi _ _ (by decide)) (hlevi _ _ (by decide)) (hlevi _ _ (by decide))
    (hlevi _ _ (by decide))
    (rotationSL_pow_three _ _) (rotationSL_pow_three _ _) (rotationSL_pow_three _ _)
    (rotationSL_pow_three _ _)
    (rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (rotationSL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)))
    (sl_ne_of_smul_single (hne _ _ (by decide)) (one_smul _ _)
      (rotationSL_smul_single_left _ _)).symm
    (fun m => sl_ne_of_smul_single (hne _ _ (by decide))
      (rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m)
      (rotationSL_smul_single_left _ _))
    (fun m k => sl_ne_of_smul_single (hne _ _ (by decide)) (by
      rw [mul_smul, rotationSL_pow_smul_single_of_ne (hne _ _ (by decide))
        (hne _ _ (by decide)) k,
        rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m])
      (rotationSL_smul_single_left _ _))
    (fun m k l => sl_ne_of_smul_single (hne _ _ (by decide)) (by
      rw [mul_smul, mul_smul,
        rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) l,
        rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) k,
        rotationSL_pow_smul_single_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m])
      (rotationSL_smul_single_left _ _))

end Normalizer

section TwoElementField

variable {K : Type} [Field K] [Finite K]

theorem units_eq_one_of_card_eq_two (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card Kˣ = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim u 1

theorem two_eq_zero_of_card_eq_two (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact CharP.cast_eq_zero K 2

theorem scalars_eq_bot_of_card_eq_two (hK : Nat.card K = 2) (n : ℕ) : scalars n K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hA, units_eq_one_of_card_eq_two hK c, Units.val_one, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem proj_injective_of_card_eq_two (hK : Nat.card K = 2) (n : ℕ) :
    Function.Injective (proj n K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_bot_of_card_eq_two hK]

end TwoElementField

theorem four_le_localRank_three_SL {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn : 8 ≤ n) : 4 ≤ localRank 3 (Matrix.SpecialLinearGroup (Fin n) K) := by
  obtain ⟨X, hXN, hXc, hXe, hXcard⟩ := exists_elemAbelian_normalizer_radical (K := K) hn
  exact Sec9Excl.le_localRank_of_normalizes (by norm_num : 1 < 3)
    (twoPlaneRadical_ne_bot (by omega)) (twoPlaneRadical_isPGroup (two_eq_zero_of_card_eq_two hK))
    hXc hXe hXcard hXN

theorem lnTwoEvenRankFour : LnTwoEvenRankFour := by
  intro L _ _ n hmodel hn8
  obtain ⟨⟨-, -, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e' : L ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have : Finite (projectiveSL n K) := Finite.of_equiv L e'.toEquiv
  let eSL : Matrix.SpecialLinearGroup (Fin n) K ≃* projectiveSL n K :=
    MulEquiv.ofBijective (proj n K) ⟨proj_injective_of_card_eq_two hK2 n, proj_surjective n K⟩
  calc 4 ≤ localRank 3 (Matrix.SpecialLinearGroup (Fin n) K) := four_le_localRank_three_SL hK2 hn8
    _ ≤ localRank 3 (projectiveSL n K) :=
        CFSG.RankThree.PartTwo.Census.localRank_le_of_mulEquiv eSL Nat.prime_three
    _ ≤ localRank 3 L :=
        CFSG.RankThree.PartTwo.Census.localRank_le_of_mulEquiv e'.symm Nat.prime_three
    _ ≤ evenRank L :=
        CFSG.RankThree.OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)

end Sec109

end CFSG.RankThree.PartOne
