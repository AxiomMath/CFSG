module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.J4

open DihedralGroup

abbrev D8 : Type := DihedralGroup 4

section DihedralHom

variable {G : Type*} [Group G]

private theorem rel_zpow_mul {ρ σ : G} (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    σ * ρ ^ t = ρ ^ (-(t : ℤ)) * σ := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h' : σ * ρ = ρ⁻¹ * σ := by
        simpa [mul_assoc] using congrArg (fun x : G => x * σ) hrel
      calc
        σ * ρ ^ (t + 1) = σ * (ρ ^ t * ρ) := by rw [pow_succ]
        _ = (σ * ρ ^ t) * ρ := by rw [mul_assoc]
        _ = (ρ ^ (-(t : ℤ)) * σ) * ρ := by rw [ih]
        _ = ρ ^ (-(t : ℤ)) * (σ * ρ) := by rw [mul_assoc]
        _ = ρ ^ (-(t : ℤ)) * (ρ⁻¹ * σ) := by rw [h']
        _ = (ρ ^ (-(t : ℤ)) * ρ⁻¹) * σ := by rw [mul_assoc]
        _ = ρ ^ (-((t + 1 : ℕ) : ℤ)) * σ := by
              rw [← zpow_neg_one ρ, ← zpow_add]
              exact congrArg (fun e : ℤ => ρ ^ e * σ) (by omega)

private theorem zpow_mul_rel {ρ σ : G} (hσ2 : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    ρ ^ t * σ = σ * ρ ^ (-(t : ℤ)) := by
  have h1 := rel_zpow_mul (ρ := ρ) (σ := σ) hrel t
  have hstep : ρ ^ t = σ * ρ ^ (-(t : ℤ)) * σ := by
    calc
      ρ ^ t = (σ * σ) * ρ ^ t := by rw [← pow_two, hσ2, one_mul]
      _ = σ * (σ * ρ ^ t) := by rw [mul_assoc]
      _ = σ * (ρ ^ (-(t : ℤ)) * σ) := by rw [h1]
      _ = σ * ρ ^ (-(t : ℤ)) * σ := by rw [mul_assoc]
  calc
    ρ ^ t * σ = (σ * ρ ^ (-(t : ℤ)) * σ) * σ := by rw [hstep]
    _ = σ * ρ ^ (-(t : ℤ)) * (σ * σ) := by group
    _ = σ * ρ ^ (-(t : ℤ)) := by rw [← pow_two, hσ2, mul_one]

private theorem pow_val_add_eq {ρ : G} (hx : ρ ^ 4 = 1) (i j : ZMod 4) :
    ρ ^ ((i + j).val) = ρ ^ i.val * ρ ^ j.val := by
  have hcong : (i.val + j.val) % 4 ≡ i.val + j.val [MOD 4] := Nat.mod_modEq (i.val + j.val) 4
  calc
    ρ ^ ((i + j).val) = ρ ^ ((i.val + j.val) % 4) := by rw [ZMod.val_add (n := 4) i j]
    _ = ρ ^ (i.val + j.val) := pow_eq_pow_of_modEq hcong hx
    _ = ρ ^ i.val * ρ ^ j.val := by rw [pow_add]

private theorem pow_val_sub_zpow {ρ : G} (hx : ρ ^ 4 = 1) (i j : ZMod 4) :
    ρ ^ ((j - i).val) = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
  have hji : (i + (j - i) : ZMod 4) = j := by simp [sub_eq_add_neg]
  have hval : j.val = (i.val + (j - i).val) % 4 := by
    calc
      j.val = (i + (j - i) : ZMod 4).val := by rw [hji]
      _ = (i.val + (j - i).val) % 4 := ZMod.val_add (n := 4) i (j - i)
  have hcong : j.val ≡ i.val + (j - i).val [MOD 4] := by
    rw [hval]
    exact Nat.mod_modEq _ _
  have hp : ρ ^ j.val = ρ ^ i.val * ρ ^ ((j - i).val) := by
    calc
      ρ ^ j.val = ρ ^ (i.val + (j - i).val) := pow_eq_pow_of_modEq hcong hx
      _ = ρ ^ i.val * ρ ^ ((j - i).val) := by rw [pow_add]
  calc
    ρ ^ ((j - i).val) = (ρ ^ i.val)⁻¹ * ρ ^ j.val := by rw [hp]; group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ (j.val : ℤ) := by
          rw [← zpow_natCast (a := ρ) (n := i.val), ← zpow_neg (a := ρ) (n := (i.val : ℤ)),
            ← zpow_natCast (a := ρ) (n := j.val)]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_add]
          exact congrArg (fun e : ℤ => ρ ^ e) (by ring)

private theorem map_mul_rs {ρ σ : G} (hx : ρ ^ 4 = 1) (hσ2 : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (i j : ZMod 4) :
    ρ ^ i.val * (σ * ρ ^ j.val) = σ * ρ ^ (j - i).val := by
  calc
    ρ ^ i.val * (σ * ρ ^ j.val) = (ρ ^ i.val * σ) * ρ ^ j.val := by rw [mul_assoc]
    _ = (σ * ρ ^ (-(i.val : ℤ))) * ρ ^ j.val := by rw [zpow_mul_rel hσ2 hrel i.val]
    _ = σ * (ρ ^ (-(i.val : ℤ)) * ρ ^ j.val) := by rw [mul_assoc]
    _ = σ * ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_natCast (a := ρ) (n := j.val), ← zpow_add]
          exact congrArg (fun e : ℤ => σ * ρ ^ e) (by ring)
    _ = σ * ρ ^ (j - i).val := by rw [pow_val_sub_zpow hx i j]

private theorem map_mul_ss {ρ σ : G} (hx : ρ ^ 4 = 1) (hσ2 : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (i j : ZMod 4) :
    (σ * ρ ^ i.val) * (σ * ρ ^ j.val) = ρ ^ (j - i).val := by
  calc
    (σ * ρ ^ i.val) * (σ * ρ ^ j.val) = σ * (ρ ^ i.val * σ) * ρ ^ j.val := by group
    _ = σ * (σ * ρ ^ (-(i.val : ℤ))) * ρ ^ j.val := by rw [zpow_mul_rel hσ2 hrel i.val]
    _ = (σ * σ) * (ρ ^ (-(i.val : ℤ)) * ρ ^ j.val) := by group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ j.val := by rw [← pow_two, hσ2, one_mul]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_natCast (a := ρ) (n := j.val), ← zpow_add]
          exact congrArg (fun e : ℤ => ρ ^ e) (by ring)
    _ = ρ ^ (j - i).val := by rw [pow_val_sub_zpow hx i j]

private theorem map_mul_sr {ρ σ : G} (hx : ρ ^ 4 = 1) (i j : ZMod 4) :
    σ * ρ ^ (i + j).val = (σ * ρ ^ i.val) * ρ ^ j.val := by
  rw [pow_val_add_eq hx i j, mul_assoc]

@[expose] def d8Hom (ρ σ : G) (hx : ρ ^ 4 = 1) (hσ2 : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) : D8 →* G where
  toFun x := match x with
    | r i => ρ ^ i.val
    | sr i => σ * ρ ^ i.val
  map_one' := by
    rw [DihedralGroup.one_def]
    simp
  map_mul' := by
    intro x y
    match x with
    | r i =>
        match y with
        | r j => simpa [DihedralGroup.r_mul_r] using pow_val_add_eq hx i j
        | sr j => simpa [DihedralGroup.r_mul_sr] using (map_mul_rs hx hσ2 hrel i j).symm
    | sr i =>
        match y with
        | r j => simpa [DihedralGroup.sr_mul_r] using map_mul_sr hx i j
        | sr j => simpa [DihedralGroup.sr_mul_sr] using (map_mul_ss hx hσ2 hrel i j).symm

end DihedralHom

theorem mem_center_D8 (x : D8) : x ∈ Subgroup.center D8 ↔ x = r 0 ∨ x = r 2 := by
  rw [Subgroup.mem_center_iff]
  revert x
  decide

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

@[expose] def ind2 (x : D8) : ZMod 2 := if x = r 2 then 1 else 0

theorem ind2_mul {x y : D8} (hx : x ∈ Subgroup.center D8) (hy : y ∈ Subgroup.center D8) :
    ind2 (x * y) = ind2 x + ind2 y := by
  rcases (mem_center_D8 x).1 hx with rfl | rfl <;> rcases (mem_center_D8 y).1 hy with rfl | rfl <;>
    decide

theorem ind2_inv {x : D8} (hx : x ∈ Subgroup.center D8) : ind2 x⁻¹ = ind2 x := by
  rcases (mem_center_D8 x).1 hx with rfl | rfl <;> decide

@[expose] def centralTuples (n : ℕ) : Subgroup (Fin n → D8) where
  carrier := {f | (∀ i, f i ∈ Subgroup.center D8) ∧ ∑ i, ind2 (f i) = 0}
  mul_mem' {f g} hf hg := by
    refine ⟨fun i => Subgroup.mul_mem _ (hf.1 i) (hg.1 i), ?_⟩
    show ∑ i, ind2 (f i * g i) = 0
    rw [Finset.sum_congr rfl fun i _ => ind2_mul (hf.1 i) (hg.1 i), Finset.sum_add_distrib, hf.2,
      hg.2, add_zero]
  one_mem' := by
    refine ⟨fun i => Subgroup.one_mem _, ?_⟩
    show ∑ _i : Fin n, ind2 1 = 0
    have h : ind2 1 = 0 := by decide
    rw [h, Finset.sum_const_zero]
  inv_mem' {f} hf := by
    refine ⟨fun i => Subgroup.inv_mem _ (hf.1 i), ?_⟩
    show ∑ i, ind2 (f i)⁻¹ = 0
    rw [Finset.sum_congr rfl fun i _ => ind2_inv (hf.1 i), hf.2]

theorem centralTuples_le_center (n : ℕ) : centralTuples n ≤ Subgroup.center (Fin n → D8) := by
  intro f hf
  rw [Subgroup.mem_center_iff]
  intro g
  funext i
  exact (Subgroup.mem_center_iff.1 (hf.1 i)) (g i)

instance (n : ℕ) : (centralTuples n).Normal :=
  Subgroup.normal_of_le_center (centralTuples_le_center n)

abbrev D8CentralProduct (n : ℕ) : Type := (Fin n → D8) ⧸ centralTuples n

theorem card_centralTuples {n : ℕ} (hn : 0 < n) : Nat.card (centralTuples n) = 2 ^ (n - 1) := by
  classical
  let toV : centralTuples n → (Fin n → ZMod 2) := fun f i => ind2 (f.1 i)
  let ofV : (Fin n → ZMod 2) → (Fin n → D8) := fun v i => if v i = 0 then r 0 else r 2
  have hS : ∀ v : Fin n → ZMod 2, ∑ i, v i = 0 → ofV v ∈ centralTuples n := by
    intro v hv
    refine ⟨fun i => ?_, ?_⟩
    · show (if v i = 0 then r 0 else r 2) ∈ Subgroup.center D8
      rw [mem_center_D8]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · show ∑ i, ind2 (if v i = 0 then r 0 else r 2) = 0
      calc ∑ i, ind2 (if v i = 0 then r 0 else r 2) = ∑ i, v i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rcases zmod2_cases (v i) with h | h <;> rw [h] <;> decide
        _ = 0 := hv
  have e : centralTuples n ≃ {v : Fin n → ZMod 2 // ∑ i, v i = 0} :=
    { toFun := fun f => ⟨toV f, f.2.2⟩
      invFun := fun v => ⟨ofV v.1, hS v.1 v.2⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext i
        show (if ind2 (f.1 i) = 0 then r 0 else r 2) = f.1 i
        rcases (mem_center_D8 _).1 (f.2.1 i) with h | h <;> rw [h] <;> decide
      right_inv := fun v => by
        apply Subtype.ext
        funext i
        show ind2 (if v.1 i = 0 then r 0 else r 2) = v.1 i
        rcases zmod2_cases (v.1 i) with h | h <;> rw [h] <;> decide }
  rw [Nat.card_congr e]
  let s : (Fin n → ZMod 2) →+ ZMod 2 :=
    { toFun := fun v => ∑ i, v i
      map_zero' := by simp
      map_add' := fun v w => by simp [Finset.sum_add_distrib] }
  have hsurj : Function.Surjective s := by
    intro c
    refine ⟨Pi.single ⟨0, hn⟩ c, ?_⟩
    show ∑ i, Pi.single (⟨0, hn⟩ : Fin n) c i = c
    simp
  have hker : Nat.card s.ker = 2 ^ (n - 1) := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup s.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective s hsurj).toEquiv] at h
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Nat.card_zmod] at h
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  rw [← hker]
  rfl

theorem card_D8CentralProduct {n : ℕ} (hn : 0 < n) :
    Nat.card (D8CentralProduct n) = 2 ^ (2 * n + 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (centralTuples n)
  rw [card_centralTuples hn, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    DihedralGroup.nat_card] at h
  have h8 : (2 * 4 : ℕ) ^ n = 2 ^ (2 * n + 1) * 2 ^ (n - 1) := by
    rw [show (2 * 4 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [h8] at h
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm

theorem nonempty_mulEquiv_D8CentralProduct {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 0 < n)
    (a b : Fin n → G) (z : G) (ha : ∀ i, a i ^ 2 = 1) (hb : ∀ i, b i ^ 2 = 1)
    (hab : ∀ i, (a i * b i) ^ 2 = z) (hz : z ^ 2 = 1)
    (hcomm : ∀ i j, i ≠ j → Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j))
    (hgen : Subgroup.closure (Set.range a ∪ Set.range b) = ⊤)
    (hcard : Nat.card G = 2 ^ (2 * n + 1)) : Nonempty (G ≃* D8CentralProduct n) := by
  classical
  have hainv : ∀ i, (a i)⁻¹ = a i := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha i)
  have hbinv : ∀ i, (b i)⁻¹ = b i := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb i)
  have hρ4 : ∀ i, (a i * b i) ^ 4 = 1 := fun i => by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hab, hz]
  have hrel : ∀ i, a i * (a i * b i) * (a i)⁻¹ = (a i * b i)⁻¹ := fun i => by
    calc a i * (a i * b i) * (a i)⁻¹ = a i ^ 2 * b i * (a i)⁻¹ := by
          rw [sq, mul_assoc (a i) (a i) (b i)]
      _ = (a i * b i)⁻¹ := by rw [ha i, one_mul, mul_inv_rev, hbinv]
  let φ : ∀ i : Fin n, D8 →* G := fun i => d8Hom (a i * b i) (a i) (hρ4 i) (ha i) (hrel i)
  have hmemφ : ∀ i x, φ i x ∈ Subgroup.closure ({a i, b i} : Set G) := by
    intro i x
    have hai : a i ∈ Subgroup.closure ({a i, b i} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hbi : b i ∈ Subgroup.closure ({a i, b i} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases x with k | k
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hai hbi) _
    · exact Subgroup.mul_mem _ hai (Subgroup.pow_mem _ (Subgroup.mul_mem _ hai hbi) _)
  have hcommφ : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) := by
    intro i j hij x y
    have hle : Subgroup.closure ({a j, b j} : Set G) ≤
        Subgroup.centralizer (Subgroup.closure ({a i, b i} : Set G) : Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.closure_le]
      rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
        rintro _ (rfl | rfl)
      · exact (hcomm i j hij).1
      · exact ((hcomm j i (Ne.symm hij)).2.1).symm
      · exact (hcomm i j hij).2.1
      · exact (hcomm i j hij).2.2
    exact Subgroup.mem_centralizer_iff.1 (hle (hmemφ j y)) _ (hmemφ i x)
  let Φ : (Fin n → D8) →* G := MonoidHom.noncommPiCoprod φ hcommφ
  let χ : Multiplicative (ZMod 2) →* G :=
    { toFun := fun c => z ^ (Multiplicative.toAdd c).val
      map_one' := by simp
      map_mul' := fun c d => by
        induction c using Multiplicative.rec with | ofAdd c =>
        induction d using Multiplicative.rec with | ofAdd d =>
        show z ^ (c + d).val = z ^ c.val * z ^ d.val
        rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl
        · simp
        · simp
        · simp
        · rw [show ((1 : ZMod 2) + 1).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl,
            pow_zero, pow_one, ← sq, hz] }
  have hfi : ∀ f ∈ centralTuples n, ∀ i, φ i (f i) = χ (Multiplicative.ofAdd (ind2 (f i))) := by
    intro f hf i
    rcases (mem_center_D8 _).1 (hf.1 i) with h | h <;> rw [h]
    · show (a i * b i) ^ (0 : ZMod 4).val = z ^ (ind2 (r 0)).val
      have h0 : ind2 (r 0) = 0 := by decide
      rw [h0, ZMod.val_zero, ZMod.val_zero, pow_zero, pow_zero]
    · show (a i * b i) ^ (2 : ZMod 4).val = z ^ (ind2 (r 2)).val
      have h1 : ind2 (r 2) = 1 := by decide
      rw [h1]
      show (a i * b i) ^ 2 = z ^ 1
      rw [hab, pow_one]
  have hker : centralTuples n ≤ Φ.ker := by
    intro f hf
    rw [MonoidHom.mem_ker]
    calc Φ f = Finset.univ.noncommProd (fun i => φ i (f i))
          (fun _ _ _ _ h => hcommφ h _ _) := rfl
      _ = Finset.univ.noncommProd (fun i => χ (Multiplicative.ofAdd (ind2 (f i))))
            (fun _ _ _ _ _ => (Commute.all _ _).map χ) :=
          Finset.noncommProd_congr rfl (fun i _ => hfi f hf i) _
      _ = χ (Finset.univ.noncommProd (fun i => Multiplicative.ofAdd (ind2 (f i)))
            (fun _ _ _ _ _ => Commute.all _ _)) := (Finset.map_noncommProd _ _ _ χ).symm
      _ = χ (∏ i, Multiplicative.ofAdd (ind2 (f i))) := by rw [Finset.noncommProd_eq_prod]
      _ = 1 := by rw [← ofAdd_sum, hf.2, ofAdd_zero, map_one]
  let Ψ : D8CentralProduct n →* G := QuotientGroup.lift _ Φ hker
  have hrange : Φ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨Pi.mulSingle i (sr 0), ?_⟩
      rw [MonoidHom.noncommPiCoprod_mulSingle]
      show a i * (a i * b i) ^ (0 : ZMod 4).val = a i
      rw [ZMod.val_zero, pow_zero, mul_one]
    · refine ⟨Pi.mulSingle i (sr 1), ?_⟩
      rw [MonoidHom.noncommPiCoprod_mulSingle]
      show a i * (a i * b i) ^ (1 : ZMod 4).val = b i
      rw [show (1 : ZMod 4).val = 1 from rfl, pow_one, ← mul_assoc, ← sq, ha i, one_mul]
  have hsurj : Function.Surjective Ψ := by
    intro g
    obtain ⟨f, hf⟩ := (MonoidHom.range_eq_top.1 hrange) g
    exact ⟨QuotientGroup.mk f, hf⟩
  have hbij : Function.Bijective Ψ :=
    hsurj.bijective_of_nat_card_le (by rw [card_D8CentralProduct hn, hcard])
  exact ⟨(MulEquiv.ofBijective Ψ hbij).symm⟩

end CFSG.Quasithin.H13.J4
