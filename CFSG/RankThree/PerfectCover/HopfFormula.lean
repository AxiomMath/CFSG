module

public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public noncomputable section

namespace CFSG.RankThree.PerfectCover

open Subgroup Finsupp groupHomology
open scoped commutatorElement

universe v

section Chains

variable {S : Type} [Group S]

@[expose] def chainBoundary₂ : (S × S →₀ ℤ) →+ (S →₀ ℤ) :=
  Finsupp.liftAddHom fun x => singleAddHom x.2 - singleAddHom (x.1 * x.2) + singleAddHom x.1

theorem chainBoundary₂_single (x : S × S) (n : ℤ) :
    chainBoundary₂ (single x n) = single x.2 n - single (x.1 * x.2) n + single x.1 n := by
  simp [chainBoundary₂]

theorem chainBoundary₂_eq (c : S × S →₀ ℤ) :
    chainBoundary₂ c = d₂₁ (Rep.trivial ℤ S ℤ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single x n =>
    rw [chainBoundary₂_single,
      show (single x n : S × S →₀ ℤ) = single x (n : Rep.trivial ℤ S ℤ) from rfl, d₂₁_single]
    simp

theorem mem_cycles₂_iff_chainBoundary₂ (c : S × S →₀ ℤ) :
    c ∈ cycles₂ (Rep.trivial ℤ S ℤ) ↔ chainBoundary₂ c = 0 := by
  rw [chainBoundary₂_eq]
  rfl

@[expose] def chainBoundary₃ : (S × S × S →₀ ℤ) →+ (S × S →₀ ℤ) :=
  Finsupp.liftAddHom fun x => singleAddHom (x.2.1, x.2.2) - singleAddHom (x.1 * x.2.1, x.2.2) +
    singleAddHom (x.1, x.2.1 * x.2.2) - singleAddHom (x.1, x.2.1)

theorem chainBoundary₃_single (x : S × S × S) (n : ℤ) :
    chainBoundary₃ (single x n) = single (x.2.1, x.2.2) n - single (x.1 * x.2.1, x.2.2) n +
      single (x.1, x.2.1 * x.2.2) n - single (x.1, x.2.1) n := by
  simp [chainBoundary₃]

theorem chainBoundary₃_eq (c : S × S × S →₀ ℤ) :
    chainBoundary₃ c = d₃₂ (Rep.trivial ℤ S ℤ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single x n =>
    rw [chainBoundary₃_single,
      show (single x n : S × S × S →₀ ℤ) = single x (n : Rep.trivial ℤ S ℤ) from rfl,
      d₃₂_single]
    simp

theorem mem_boundaries₂_iff_chainBoundary₃ (c : S × S →₀ ℤ) :
    c ∈ boundaries₂ (Rep.trivial ℤ S ℤ) ↔ ∃ y, chainBoundary₃ y = c := by
  change c ∈ LinearMap.range _ ↔ _
  rw [LinearMap.mem_range]
  simp only [chainBoundary₃_eq]

end Chains

section Pairing

variable {S : Type} {E : Type v} [Group E]

@[expose] def chainPairingCenter (f : S × S → E) (hf : ∀ x, f x ∈ center E) :
    (S × S →₀ ℤ) →+ Additive (center E) :=
  letI : CommGroup (center E) := IsMulCommutative.instCommGroup
  Finsupp.liftAddHom fun x => zmultiplesHom (Additive (center E)) (Additive.ofMul ⟨f x, hf x⟩)

@[expose] def chainPairing (f : S × S → E) (hf : ∀ x, f x ∈ center E) (c : S × S →₀ ℤ) : E :=
  ((Additive.toMul (chainPairingCenter f hf c) : center E) : E)

theorem chainPairing_single (f : S × S → E) (hf : ∀ x, f x ∈ center E) (x : S × S) (n : ℤ) :
    chainPairing f hf (single x n) = f x ^ n := by
  let : CommGroup (center E) := IsMulCommutative.instCommGroup
  simp [chainPairing, chainPairingCenter]

theorem chainPairing_add (f : S × S → E) (hf : ∀ x, f x ∈ center E) (c d : S × S →₀ ℤ) :
    chainPairing f hf (c + d) = chainPairing f hf c * chainPairing f hf d := by
  simp [chainPairing, map_add]

theorem chainPairing_zero (f : S × S → E) (hf : ∀ x, f x ∈ center E) :
    chainPairing f hf 0 = 1 := by
  simp [chainPairing]

theorem chainPairing_neg (f : S × S → E) (hf : ∀ x, f x ∈ center E) (c : S × S →₀ ℤ) :
    chainPairing f hf (-c) = (chainPairing f hf c)⁻¹ := by
  simp [chainPairing, map_neg]

theorem chainPairing_sub (f : S × S → E) (hf : ∀ x, f x ∈ center E) (c d : S × S →₀ ℤ) :
    chainPairing f hf (c - d) = chainPairing f hf c * (chainPairing f hf d)⁻¹ := by
  rw [sub_eq_add_neg, chainPairing_add, chainPairing_neg]

theorem chainPairing_mem_center (f : S × S → E) (hf : ∀ x, f x ∈ center E)
    (c : S × S →₀ ℤ) : chainPairing f hf c ∈ center E :=
  (Additive.toMul (chainPairingCenter f hf c)).2

theorem chainPairing_mem (f : S × S → E) (hf : ∀ x, f x ∈ center E) {K : Subgroup E}
    (hK : ∀ x, f x ∈ K) (c : S × S →₀ ℤ) : chainPairing f hf c ∈ K := by
  induction c using Finsupp.induction_linear with
  | zero => rw [chainPairing_zero]; exact one_mem K
  | add c d hc hd => rw [chainPairing_add]; exact mul_mem hc hd
  | single x n => rw [chainPairing_single]; exact zpow_mem (hK x) n

end Pairing

section Cocycles

variable {S : Type} [Group S] {E : Type v} [Group E]

theorem chainPairingCenter_chainBoundary₃ (f : S × S → E) (hf : ∀ x, f x ∈ center E)
    (hcoc : ∀ g h k : S, f (h, k) * f (g, h * k) = f (g, h) * f (g * h, k))
    (y : S × S × S →₀ ℤ) : chainPairingCenter f hf (chainBoundary₃ y) = 0 := by
  let : CommGroup (center E) := IsMulCommutative.instCommGroup
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  | single x n =>
    obtain ⟨g, h, k⟩ := x
    have key : (Additive.ofMul (⟨f (h, k), hf _⟩ : center E) +
        Additive.ofMul (⟨f (g, h * k), hf _⟩ : center E) : Additive (center E)) =
        Additive.ofMul (⟨f (g, h), hf _⟩ : center E) +
          Additive.ofMul (⟨f (g * h, k), hf _⟩ : center E) := by
      rw [← ofMul_mul, ← ofMul_mul]
      congr 1
      exact Subtype.ext (hcoc g h k)
    rw [chainBoundary₃_single]
    simp only [map_add, map_sub, chainPairingCenter, liftAddHom_apply_single, zmultiplesHom_apply]
    rw [show ∀ A B C D : Additive (center E),
        n • A - n • B + n • C - n • D = n • (A + C) - n • (D + B) from fun A B C D => by
          simp only [smul_add]; abel, key, sub_self]

theorem chainPairing_chainBoundary₃ (f : S × S → E) (hf : ∀ x, f x ∈ center E)
    (hcoc : ∀ g h k : S, f (h, k) * f (g, h * k) = f (g, h) * f (g * h, k))
    (y : S × S × S →₀ ℤ) : chainPairing f hf (chainBoundary₃ y) = 1 := by
  simp [chainPairing, chainPairingCenter_chainBoundary₃ f hf hcoc y]

@[expose] def chainPairingCenter₁ (φ : S → E) (hφ : ∀ s, φ s ∈ center E) :
    (S →₀ ℤ) →+ Additive (center E) :=
  letI : CommGroup (center E) := IsMulCommutative.instCommGroup
  Finsupp.liftAddHom fun s => zmultiplesHom (Additive (center E)) (Additive.ofMul ⟨φ s, hφ s⟩)

theorem chainPairingCenter_coboundary (f f' : S × S → E) (hf : ∀ x, f x ∈ center E)
    (hf' : ∀ x, f' x ∈ center E) (φ : S → E) (hφ : ∀ s, φ s ∈ center E)
    (hrel : ∀ g h : S, f' (g, h) = f (g, h) * (φ h * (φ (g * h))⁻¹ * φ g))
    (c : S × S →₀ ℤ) : chainPairingCenter f' hf' c =
      chainPairingCenter f hf c + chainPairingCenter₁ φ hφ (chainBoundary₂ c) := by
  let : CommGroup (center E) := IsMulCommutative.instCommGroup
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]; abel
  | single x n =>
    obtain ⟨g, h⟩ := x
    have key : (Additive.ofMul (⟨f' (g, h), hf' _⟩ : center E) : Additive (center E)) =
        Additive.ofMul (⟨f (g, h), hf _⟩ : center E) + (Additive.ofMul (⟨φ h, hφ _⟩ : center E) -
          Additive.ofMul (⟨φ (g * h), hφ _⟩ : center E) +
            Additive.ofMul (⟨φ g, hφ _⟩ : center E)) := by
      rw [← ofMul_div, ← ofMul_mul, ← ofMul_mul]
      congr 1
      apply Subtype.ext
      change f' (g, h) = f (g, h) * (φ h / φ (g * h) * φ g)
      rw [hrel, div_eq_mul_inv]
    rw [chainBoundary₂_single]
    simp only [map_add, map_sub, chainPairingCenter, chainPairingCenter₁, liftAddHom_apply_single,
      zmultiplesHom_apply]
    rw [key]
    simp only [smul_add, smul_sub]

theorem chainPairing_coboundary_of_cycle (f f' : S × S → E) (hf : ∀ x, f x ∈ center E)
    (hf' : ∀ x, f' x ∈ center E) (φ : S → E) (hφ : ∀ s, φ s ∈ center E)
    (hrel : ∀ g h : S, f' (g, h) = f (g, h) * (φ h * (φ (g * h))⁻¹ * φ g))
    {z : S × S →₀ ℤ} (hz : chainBoundary₂ z = 0) : chainPairing f' hf' z = chainPairing f hf z := by
  simp [chainPairing, chainPairingCenter_coboundary f f' hf hf' φ hφ hrel z, hz]

omit [Group S] in
theorem chainPairing_map {E₂ : Type*} [Group E₂] (ψ : E →* E₂) (f : S × S → E)
    (hf : ∀ x, f x ∈ center E) (hf₂ : ∀ x, ψ (f x) ∈ center E₂) (c : S × S →₀ ℤ) :
    chainPairing (fun x => ψ (f x)) hf₂ c = ψ (chainPairing f hf c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [chainPairing_zero]
  | add c d hc hd => rw [chainPairing_add, chainPairing_add, hc, hd, map_mul]
  | single x n => rw [chainPairing_single, chainPairing_single, map_zpow]

end Cocycles

section Collection

variable {S : Type} [Group S] {E : Type v} [Group E]

@[expose] def sectionCocycle (e : S → E) (x : S × S) : E := e x.1 * e x.2 * (e (x.1 * x.2))⁻¹

theorem sectionCocycle_mem_ker (q : E →* S) {e : S → E} (he : ∀ s, q (e s) = s) (x : S × S) :
    sectionCocycle e x ∈ q.ker := by
  rw [MonoidHom.mem_ker, sectionCocycle, map_mul, map_mul, map_inv, he, he, he, mul_inv_cancel]

theorem sectionCocycle_cocycle {e : S → E} (hcen : ∀ x, sectionCocycle e x ∈ center E)
    (g h k : S) : sectionCocycle e (h, k) * sectionCocycle e (g, h * k) =
      sectionCocycle e (g, h) * sectionCocycle e (g * h, k) := by
  have hc : e g * sectionCocycle e (h, k) = sectionCocycle e (h, k) * e g :=
    mem_center_iff.mp (hcen (h, k)) (e g)
  have hassoc : g * (h * k) = g * h * k := (mul_assoc g h k).symm
  simp only [sectionCocycle] at hc ⊢
  rw [hassoc]
  calc e h * e k * (e (h * k))⁻¹ * (e g * e (h * k) * (e (g * h * k))⁻¹)
      = (e h * e k * (e (h * k))⁻¹ * e g) * e (h * k) * (e (g * h * k))⁻¹ := by group
    _ = (e g * (e h * e k * (e (h * k))⁻¹)) * e (h * k) * (e (g * h * k))⁻¹ := by rw [← hc]
    _ = e g * e h * (e (g * h))⁻¹ * (e (g * h) * e k * (e (g * h * k))⁻¹) := by group

omit [Group S] in
@[expose] def freeAbel : FreeGroup S →* Multiplicative (S →₀ ℤ) :=
  FreeGroup.lift fun s => Multiplicative.ofAdd (single s 1)

omit [Group S] in
theorem freeAbel_eq_one_of_mem_commutator {w : FreeGroup S}
    (hw : w ∈ commutator (FreeGroup S)) : freeAbel w = 1 :=
  Abelianization.commutator_subset_ker freeAbel hw

theorem inv_eq_mul_of_mem_center {a b c : E} (hc : c ∈ center E) :
    b⁻¹ = (a * b * c⁻¹)⁻¹ * c⁻¹ * a := by
  have h := mem_center_iff.mp hc (b⁻¹ * a⁻¹)
  calc b⁻¹ = b⁻¹ * a⁻¹ * c * c⁻¹ * a := by group
    _ = c * (b⁻¹ * a⁻¹) * c⁻¹ * a := by rw [h]
    _ = (a * b * c⁻¹)⁻¹ * c⁻¹ * a := by group

theorem exists_chain_collect (t : FreeGroup S →* E)
    (hf : ∀ x, sectionCocycle (fun s => t (FreeGroup.of s)) x ∈ center E) (w : FreeGroup S) :
    ∃ c : S × S →₀ ℤ, t w = chainPairing _ hf c * t (FreeGroup.of (hopfEval S w)) ∧
      Multiplicative.toAdd (freeAbel w) = chainBoundary₂ c + single (hopfEval S w) 1 := by
  have he1 : sectionCocycle (fun s => t (FreeGroup.of s)) (1, 1) = t (FreeGroup.of 1) := by
    simp [sectionCocycle]
  have h1c : t (FreeGroup.of 1) ∈ center E := he1 ▸ hf (1, 1)
  induction w using FreeGroup.induction_on with
  | one =>
    refine ⟨-single (1, 1) 1, ?_, ?_⟩
    · rw [chainPairing_neg, chainPairing_single, zpow_one, he1, map_one, map_one, inv_mul_cancel]
    · rw [map_one, map_neg, chainBoundary₂_single]
      simp
  | of s =>
    refine ⟨0, ?_, ?_⟩
    · rw [chainPairing_zero, one_mul]
      simp
    · simp [freeAbel]
  | inv_of s _ =>
    refine ⟨-single (s⁻¹, s) 1 - single (1, 1) 1, ?_, ?_⟩
    · rw [chainPairing_sub, chainPairing_neg, chainPairing_single, chainPairing_single, zpow_one,
        zpow_one, he1, map_inv, map_inv]
      simp only [sectionCocycle, inv_mul_cancel, hopfEval, FreeGroup.lift_apply_of, id]
      exact inv_eq_mul_of_mem_center h1c
    · rw [map_inv, toAdd_inv, map_sub, map_neg, chainBoundary₂_single, chainBoundary₂_single]
      simp [freeAbel]
      abel
  | mul u v hu hv =>
    obtain ⟨cu, htu, hau⟩ := hu
    obtain ⟨cv, htv, hav⟩ := hv
    refine ⟨cu + cv + single (hopfEval S u, hopfEval S v) 1, ?_, ?_⟩
    · have hPv := mem_center_iff.mp (chainPairing_mem_center _ hf cv)
        (t (FreeGroup.of (hopfEval S u)))
      rw [map_mul, htu, htv, chainPairing_add, chainPairing_add, chainPairing_single, zpow_one,
        map_mul (hopfEval S)]
      simp only [sectionCocycle]
      calc chainPairing _ hf cu * t (FreeGroup.of (hopfEval S u)) *
            (chainPairing _ hf cv * t (FreeGroup.of (hopfEval S v)))
          = chainPairing _ hf cu * (t (FreeGroup.of (hopfEval S u)) * chainPairing _ hf cv) *
            t (FreeGroup.of (hopfEval S v)) := by group
        _ = chainPairing _ hf cu * (chainPairing _ hf cv * t (FreeGroup.of (hopfEval S u))) *
            t (FreeGroup.of (hopfEval S v)) := by rw [hPv]
        _ = _ := by group
    · rw [map_mul, toAdd_mul, hau, hav, map_add, map_add, chainBoundary₂_single, map_mul]
      abel

theorem exists_cycle_chainPairing_eq (t : FreeGroup S →* E)
    (hf : ∀ x, sectionCocycle (fun s => t (FreeGroup.of s)) x ∈ center E) {w : FreeGroup S}
    (hwD : w ∈ commutator (FreeGroup S)) (hwR : hopfEval S w = 1) :
    ∃ z : S × S →₀ ℤ, chainBoundary₂ z = 0 ∧ chainPairing _ hf z = t w := by
  obtain ⟨c, htc, hac⟩ := exists_chain_collect t hf w
  rw [freeAbel_eq_one_of_mem_commutator hwD, toAdd_one, hwR] at hac
  rw [hwR] at htc
  refine ⟨c + single (1, 1) 1, ?_, ?_⟩
  · rw [map_add, chainBoundary₂_single, hac]
    simp only [mul_one]
    abel
  · rw [chainPairing_add, chainPairing_single, zpow_one, htc]
    simp [sectionCocycle]

end Collection

section Twist

variable (S : Type) [Group S]

abbrev chainBoundaries : AddSubgroup (S × S →₀ ℤ) := (chainBoundary₃ (S := S)).range

abbrev ChainQuot : Type := (S × S →₀ ℤ) ⧸ chainBoundaries S

variable {S}

@[expose] def twistCocycle (g h : S) : ChainQuot S :=
  ((single (g, h) 1 - single (1, 1) 1 : S × S →₀ ℤ) : ChainQuot S)

theorem mk_chainBoundary₃ (y : S × S × S →₀ ℤ) :
    ((chainBoundary₃ y : S × S →₀ ℤ) : ChainQuot S) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨y, rfl⟩

theorem twistCocycle_one_left (h : S) : twistCocycle 1 h = 0 := by
  have hb := mk_chainBoundary₃ (S := S) (single (1, 1, h) 1)
  rw [chainBoundary₃_single] at hb
  simp only [mul_one, one_mul, sub_add_cancel] at hb
  exact hb

theorem twistCocycle_one_right (g : S) : twistCocycle g 1 = 0 := by
  have hb := mk_chainBoundary₃ (S := S) (single (g, 1, 1) 1)
  rw [chainBoundary₃_single] at hb
  simp only [mul_one, sub_add_cancel] at hb
  rw [twistCocycle, ← neg_sub, QuotientAddGroup.mk_neg, hb, neg_zero]

theorem twistCocycle_cocycle (g h k : S) :
    twistCocycle g h + twistCocycle (g * h) k = twistCocycle h k + twistCocycle g (h * k) := by
  have hb := mk_chainBoundary₃ (S := S) (single (g, h, k) 1)
  rw [chainBoundary₃_single] at hb
  simp only [twistCocycle, ← QuotientAddGroup.mk_add] at hb ⊢
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, ← neg_eq_zero, ← QuotientAddGroup.mk_neg]
  rw [← hb]
  congr 1
  abel

theorem twistCocycle_inv (g : S) : twistCocycle g⁻¹ g = twistCocycle g g⁻¹ := by
  have h := twistCocycle_cocycle g g⁻¹ g
  rw [mul_inv_cancel, inv_mul_cancel, twistCocycle_one_left, twistCocycle_one_right] at h
  simp only [add_zero] at h
  exact h.symm

end Twist

section TwistGroup

variable (S : Type) [Group S]

@[ext]
structure HopfTwist where
  fst : ChainQuot S
  snd : S

variable {S}

instance : Mul (HopfTwist S) :=
  ⟨fun x y => ⟨x.fst + y.fst + twistCocycle x.snd y.snd, x.snd * y.snd⟩⟩

instance : One (HopfTwist S) := ⟨⟨0, 1⟩⟩

instance : Inv (HopfTwist S) := ⟨fun x => ⟨-x.fst - twistCocycle x.snd⁻¹ x.snd, x.snd⁻¹⟩⟩

theorem HopfTwist.mul_fst (x y : HopfTwist S) :
    (x * y).fst = x.fst + y.fst + twistCocycle x.snd y.snd := rfl

theorem HopfTwist.mul_snd (x y : HopfTwist S) : (x * y).snd = x.snd * y.snd := rfl

theorem HopfTwist.one_fst : (1 : HopfTwist S).fst = 0 := rfl

theorem HopfTwist.one_snd : (1 : HopfTwist S).snd = 1 := rfl

theorem HopfTwist.inv_fst (x : HopfTwist S) :
    x⁻¹.fst = -x.fst - twistCocycle x.snd⁻¹ x.snd := rfl

theorem HopfTwist.inv_snd (x : HopfTwist S) : x⁻¹.snd = x.snd⁻¹ := rfl

instance : Group (HopfTwist S) :=
  Group.ofLeftAxioms
    (fun x y z => by
      ext
      · simp only [HopfTwist.mul_fst, HopfTwist.mul_snd]
        have h := twistCocycle_cocycle x.snd y.snd z.snd
        calc x.fst + y.fst + twistCocycle x.snd y.snd + z.fst +
              twistCocycle (x.snd * y.snd) z.snd
            = x.fst + y.fst + z.fst +
              (twistCocycle x.snd y.snd + twistCocycle (x.snd * y.snd) z.snd) := by abel
          _ = x.fst + y.fst + z.fst +
              (twistCocycle y.snd z.snd + twistCocycle x.snd (y.snd * z.snd)) := by rw [h]
          _ = _ := by abel
      · exact mul_assoc _ _ _)
    (fun x => by
      ext
      · simp only [HopfTwist.mul_fst, HopfTwist.one_fst, HopfTwist.one_snd, twistCocycle_one_left,
          zero_add, add_zero]
      · exact one_mul _)
    (fun x => by
      ext
      · simp only [HopfTwist.mul_fst, HopfTwist.inv_fst, HopfTwist.inv_snd, HopfTwist.one_fst]
        abel
      · exact inv_mul_cancel _)

@[expose] def hopfTwistProj : HopfTwist S →* S where
  toFun x := x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hopfTwistProj_surjective : Function.Surjective (hopfTwistProj (S := S)) :=
  fun s => ⟨⟨0, s⟩, rfl⟩

theorem hopfTwistProj_ker_le_center :
    (hopfTwistProj (S := S)).ker ≤ center (HopfTwist S) := by
  intro x hx
  have hx1 : x.snd = 1 := hx
  rw [mem_center_iff]
  intro y
  ext
  · simp only [HopfTwist.mul_fst, hx1, twistCocycle_one_left, twistCocycle_one_right, add_zero]
    abel
  · simp only [HopfTwist.mul_snd, hx1, mul_one, one_mul]

@[expose] def hopfTwistIncl : Multiplicative (ChainQuot S) →* HopfTwist S where
  toFun a := ⟨Multiplicative.toAdd a, 1⟩
  map_one' := rfl
  map_mul' a b := by
    ext
    · simp [HopfTwist.mul_fst, twistCocycle_one_left]
    · simp [HopfTwist.mul_snd]

theorem hopfTwistIncl_apply (a : Multiplicative (ChainQuot S)) :
    hopfTwistIncl a = ⟨Multiplicative.toAdd a, 1⟩ := rfl

@[expose] def chainAug₂ : (S × S →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

@[expose] def chainAug₁ : (S →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

theorem chainAug₁_chainBoundary₂ (c : S × S →₀ ℤ) : chainAug₁ (chainBoundary₂ c) = chainAug₂ c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add]
  | single x n =>
    rw [chainBoundary₂_single, map_add, map_sub]
    simp [chainAug₁, chainAug₂]

theorem sectionCocycle_hopfTwist (x : S × S) :
    sectionCocycle (fun s => (⟨0, s⟩ : HopfTwist S)) x = ⟨twistCocycle x.1 x.2, 1⟩ := by
  obtain ⟨g, h⟩ := x
  have h1 : ((⟨0, g * h⟩ : HopfTwist S)⁻¹).snd = (g * h)⁻¹ := rfl
  have h2 : ((⟨0, g * h⟩ : HopfTwist S)⁻¹).fst = -0 - twistCocycle (g * h)⁻¹ (g * h) := rfl
  ext
  · simp only [sectionCocycle, HopfTwist.mul_fst, HopfTwist.mul_snd, h1, h2, twistCocycle_inv]
    abel
  · simp only [sectionCocycle, HopfTwist.mul_snd, h1, mul_inv_cancel]

end TwistGroup

section SectionChange

variable {S : Type} [Group S] {E : Type v} [Group E]

theorem sectionCocycle_mul_central {e c : S → E} (hc : ∀ s, c s ∈ center E) (x : S × S) :
    sectionCocycle (fun s => e s * c s) x =
      sectionCocycle e x * (c x.2 * (c (x.1 * x.2))⁻¹ * c x.1) := by
  obtain ⟨g, h⟩ := x
  simp only [sectionCocycle]
  have hg : e h * c g = c g * e h := mem_center_iff.mp (hc g) (e h)
  have hK : c g * c h * (c (g * h))⁻¹ ∈ center E :=
    mul_mem (mul_mem (hc g) (hc h)) (inv_mem (hc (g * h)))
  have hKe : (e (g * h))⁻¹ * (c g * c h * (c (g * h))⁻¹) =
      c g * c h * (c (g * h))⁻¹ * (e (g * h))⁻¹ := mem_center_iff.mp hK (e (g * h))⁻¹
  have hKc : c h * (c (g * h))⁻¹ * c g = c g * c h * (c (g * h))⁻¹ := by
    rw [mem_center_iff.mp (hc g) (c h * (c (g * h))⁻¹), mul_assoc]
  calc e g * c g * (e h * c h) * (e (g * h) * c (g * h))⁻¹
      = e g * (c g * e h) * c h * (c (g * h))⁻¹ * (e (g * h))⁻¹ := by group
    _ = e g * (e h * c g) * c h * (c (g * h))⁻¹ * (e (g * h))⁻¹ := by rw [hg]
    _ = e g * e h * (c g * c h * (c (g * h))⁻¹ * (e (g * h))⁻¹) := by group
    _ = e g * e h * ((e (g * h))⁻¹ * (c g * c h * (c (g * h))⁻¹)) := by rw [hKe]
    _ = e g * e h * (e (g * h))⁻¹ * (c h * (c (g * h))⁻¹ * c g) := by rw [hKc]; group

end SectionChange

section TwistPairing

variable {S : Type} [Group S]

theorem chainPairing_hopfTwist_std
    (hf : ∀ x, sectionCocycle (fun s => (⟨0, s⟩ : HopfTwist S)) x ∈ center (HopfTwist S))
    (c : S × S →₀ ℤ) : chainPairing _ hf c = hopfTwistIncl (Multiplicative.ofAdd
      ((c : ChainQuot S) - chainAug₂ c • ((single (1, 1) 1 : S × S →₀ ℤ) : ChainQuot S))) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [chainPairing_zero]
  | add c d hc hd =>
    rw [chainPairing_add, hc, hd, ← map_mul, ← ofAdd_add]
    congr 2
    rw [QuotientAddGroup.mk_add, map_add, add_zsmul]
    abel
  | single x n =>
    rw [chainPairing_single, sectionCocycle_hopfTwist,
      show (⟨twistCocycle x.1 x.2, 1⟩ : HopfTwist S) =
        hopfTwistIncl (Multiplicative.ofAdd (twistCocycle x.1 x.2)) from rfl, ← map_zpow,
      ← ofAdd_zsmul]
    congr 2
    have hs : (single x n : S × S →₀ ℤ) = n • single x 1 := by rw [smul_single_one]
    rw [hs, QuotientAddGroup.mk_zsmul, map_zsmul, twistCocycle, QuotientAddGroup.mk_sub,
      zsmul_sub]
    simp [chainAug₂]

theorem chainPairing_hopfTwist_of_cycle (e' : S → HopfTwist S)
    (he' : ∀ s, hopfTwistProj (e' s) = s)
    (hf' : ∀ x, sectionCocycle e' x ∈ center (HopfTwist S)) {z : S × S →₀ ℤ}
    (hz : chainBoundary₂ z = 0) :
    chainPairing _ hf' z = hopfTwistIncl (Multiplicative.ofAdd (z : ChainQuot S)) := by
  set e₀ : S → HopfTwist S := fun s => ⟨0, s⟩ with he₀
  have hf₀ : ∀ x, sectionCocycle e₀ x ∈ center (HopfTwist S) := fun x =>
    hopfTwistProj_ker_le_center (sectionCocycle_mem_ker hopfTwistProj (fun _ => rfl) x)
  set c : S → HopfTwist S := fun s => (e₀ s)⁻¹ * e' s with hcdef
  have hc : ∀ s, c s ∈ center (HopfTwist S) := by
    intro s
    apply hopfTwistProj_ker_le_center
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_inv, he']
    exact inv_mul_cancel s
  have he'eq : (fun s => e₀ s * c s) = e' := funext fun s => by
    simp only [hcdef, mul_inv_cancel_left]
  have hrel : ∀ g h : S, sectionCocycle e' (g, h) =
      sectionCocycle e₀ (g, h) * (c h * (c (g * h))⁻¹ * c g) := by
    intro g h
    rw [← sectionCocycle_mul_central hc (g, h), he'eq]
  rw [chainPairing_coboundary_of_cycle _ _ hf₀ hf' c hc hrel hz, chainPairing_hopfTwist_std,
    ← chainAug₁_chainBoundary₂, hz, map_zero, zero_zsmul, sub_zero]

theorem mem_chainBoundaries_of_chainPairing_eq_one (e' : S → HopfTwist S)
    (he' : ∀ s, hopfTwistProj (e' s) = s)
    (hf' : ∀ x, sectionCocycle e' x ∈ center (HopfTwist S)) {z : S × S →₀ ℤ}
    (hz : chainBoundary₂ z = 0) (h1 : chainPairing _ hf' z = 1) : z ∈ chainBoundaries S := by
  rw [chainPairing_hopfTwist_of_cycle e' he' hf' hz] at h1
  have h2 := congrArg HopfTwist.fst h1
  rw [hopfTwistIncl_apply, HopfTwist.one_fst, toAdd_ofAdd] at h2
  exact (QuotientAddGroup.eq_zero_iff _).mp h2

end TwistPairing

section HopfFormula

variable {S : Type} [Group S] [Group.IsPerfect S]

theorem nonempty_mulEquiv_hopfMultiplier :
    Nonempty (Multiplicative (H2 (Rep.trivial ℤ S ℤ)) ≃* hopfMultiplier S) := by
  classical
  have hsurj : Function.Surjective (hopfCoverMap S) := hopfCoverMap_surjective
  set t := freeLift (hopfCoverMap S) hsurj with htdef
  have ht : (hopfCoverMap S).comp t = hopfEval S := comp_freeLift _ hsurj
  have he : ∀ s, hopfCoverMap S (t (FreeGroup.of s)) = s := fun s => by
    rw [← MonoidHom.comp_apply, ht]
    simp
  have hfM : ∀ x, sectionCocycle (fun s => t (FreeGroup.of s)) x ∈ hopfMultiplier S :=
    sectionCocycle_mem_ker _ he
  have hf : ∀ x, sectionCocycle (fun s => t (FreeGroup.of s)) x ∈ center (HopfCover S) :=
    fun x => hopfMultiplier_le_center (hfM x)
  have hcoc := sectionCocycle_cocycle hf
  let : CommGroup (center (HopfCover S)) := IsMulCommutative.instCommGroup
  set Φ : (cycles₂ (Rep.trivial ℤ S ℤ)) →ₗ[ℤ] Additive (center (HopfCover S)) :=
    (chainPairingCenter (sectionCocycle fun s => t (FreeGroup.of s)) hf).toIntLinearMap.comp
      (cycles₂ (Rep.trivial ℤ S ℤ)).subtype with hΦ
  set π₂ := (H2π (Rep.trivial ℤ S ℤ)).hom with hπ₂
  have hπ₂s : Function.Surjective π₂ :=
    (ModuleCat.epi_iff_surjective (H2π (Rep.trivial ℤ S ℤ))).mp inferInstance
  have hmemK : ∀ z, z ∈ LinearMap.ker π₂ ↔ z.1 ∈ boundaries₂ (Rep.trivial ℤ S ℤ) := fun z =>
    H2π_eq_zero_iff z
  have hK : LinearMap.ker π₂ ≤ LinearMap.ker Φ := by
    intro z hz
    obtain ⟨y, hy⟩ := (mem_boundaries₂_iff_chainBoundary₃ z.1).mp ((hmemK z).mp hz)
    rw [LinearMap.mem_ker, hΦ, LinearMap.comp_apply, Submodule.subtype_apply,
      AddMonoidHom.coe_toIntLinearMap, ← hy]
    exact chainPairingCenter_chainBoundary₃ _ hf hcoc y
  set hX := hopfLift hopfTwistProj (hopfTwistProj_surjective (S := S))
    hopfTwistProj_ker_le_center with hhX
  have hXc : hopfTwistProj.comp hX = hopfCoverMap S := comp_hopfLift _ _ _
  have hker : LinearMap.ker Φ ≤ LinearMap.ker π₂ := by
    intro z hz
    rw [hmemK, mem_boundaries₂_iff_chainBoundary₃]
    have hz1 : chainBoundary₂ z.1 = 0 := (mem_cycles₂_iff_chainBoundary₂ z.1).mp z.2
    have h1 : chainPairing (sectionCocycle fun s => t (FreeGroup.of s)) hf z.1 = 1 := by
      have h := congrArg (fun a : Additive (center (HopfCover S)) =>
        ((Additive.toMul a : center (HopfCover S)) : HopfCover S)) hz
      exact h
    set e' : S → HopfTwist S := fun s => hX (t (FreeGroup.of s)) with he'def
    have he' : ∀ s, hopfTwistProj (e' s) = s := fun s => by
      rw [he'def, ← MonoidHom.comp_apply, hXc, he]
    have hf' : ∀ x, sectionCocycle e' x ∈ center (HopfTwist S) := fun x =>
      hopfTwistProj_ker_le_center (sectionCocycle_mem_ker _ he' x)
    have hmap : ∀ x, sectionCocycle e' x = hX (sectionCocycle (fun s => t (FreeGroup.of s)) x) :=
      fun x => by simp only [sectionCocycle, he'def, map_mul, map_inv]
    have hf'' : ∀ x, hX (sectionCocycle (fun s => t (FreeGroup.of s)) x) ∈
        center (HopfTwist S) := fun x => hmap x ▸ hf' x
    have h2 : chainPairing (sectionCocycle e') hf' z.1 = 1 := by
      have h := chainPairing_map hX _ hf hf'' z.1
      rw [h1, map_one] at h
      rw [← h]
      congr 1
      exact funext hmap
    obtain ⟨y, hy⟩ := mem_chainBoundaries_of_chainPairing_eq_one e' he' hf' hz1 h2
    exact ⟨y, hy⟩
  set Ψ₀ := (LinearMap.ker π₂).liftQ Φ hK with hΨ₀
  have hΨ₀inj : Function.Injective Ψ₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot _ _ _ hker]
  set iso := LinearMap.quotKerEquivOfSurjective π₂ hπ₂s with hiso
  set Ψ : H2 (Rep.trivial ℤ S ℤ) →ₗ[ℤ] Additive (center (HopfCover S)) :=
    Ψ₀.comp iso.symm.toLinearMap with hΨ
  have hΨinj : Function.Injective Ψ := hΨ₀inj.comp iso.symm.injective
  have hΨmk : ∀ z, Ψ (iso (Submodule.Quotient.mk z)) = Φ z := fun z => by
    rw [hΨ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hΨ₀,
      Submodule.liftQ_apply]
  have hΨM : ∀ x, ((Additive.toMul (Ψ x) : center (HopfCover S)) : HopfCover S) ∈
      hopfMultiplier S := by
    intro x
    obtain ⟨q, rfl⟩ := iso.surjective x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hΨmk]
    exact chainPairing_mem _ hf hfM z.1
  let F : Multiplicative (H2 (Rep.trivial ℤ S ℤ)) →* hopfMultiplier S :=
    { toFun := fun x => ⟨_, hΨM (Multiplicative.toAdd x)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp }
  refine ⟨MulEquiv.ofBijective F ⟨fun x y hxy => ?_, fun m => ?_⟩⟩
  · have h := congrArg (fun m : hopfMultiplier S => (m : HopfCover S)) hxy
    have h' : Ψ (Multiplicative.toAdd x) = Ψ (Multiplicative.toAdd y) :=
      Additive.toMul.injective (Subtype.ext h)
    exact Multiplicative.toAdd.injective (hΨinj h')
  ·
    have : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect
    obtain ⟨u, hu⟩ := hopfLift_surjective (hopfCoverMap S) hsurj hopfMultiplier_le_center
      (m : HopfCover S)
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective u
    rw [hopfLift_mk] at hu
    have hu' : t d = m := hu
    have hdR : hopfEval S d = 1 := by
      rw [← ht, MonoidHom.comp_apply, hu']
      exact m.2
    obtain ⟨z, hz, hzd⟩ := exists_cycle_chainPairing_eq t hf d.2 hdR
    have hzc : z ∈ cycles₂ (Rep.trivial ℤ S ℤ) := (mem_cycles₂_iff_chainBoundary₂ z).mpr hz
    refine ⟨Multiplicative.ofAdd (iso (Submodule.Quotient.mk ⟨z, hzc⟩)), Subtype.ext ?_⟩
    change ((Additive.toMul (Ψ (iso (Submodule.Quotient.mk ⟨z, hzc⟩))) :
      center (HopfCover S)) : HopfCover S) = m
    rw [hΨmk]
    change chainPairing _ hf z = m
    rw [hzd, hu']

end HopfFormula

section Griess

variable (S : Type) [Group S]

@[expose] def hopfMultiplierEquivGriess :
    CFSG.Open.griessHopfMultiplier S ≃* hopfMultiplier S := by
  let ψ : ↥(CFSG.Open.griessHopfRelations S ⊓ commutator (FreeGroup S)) →* hopfMultiplier S :=
    { toFun := fun r => ⟨((⟨r, r.2.2⟩ : commutator (FreeGroup S)) : HopfCover S), r.2.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψs : Function.Surjective ψ := by
    rintro ⟨m, hm⟩
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective m
    exact ⟨⟨d, hm, d.2⟩, rfl⟩
  have hker : ψ.ker = (⁅(⊤ : Subgroup (FreeGroup S)), CFSG.Open.griessHopfRelations S⁆).subgroupOf
      (CFSG.Open.griessHopfRelations S ⊓ commutator (FreeGroup S)) := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (⟨r, r.2.2⟩ : commutator (FreeGroup S))).mp h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff
        (⟨r, r.2.2⟩ : commutator (FreeGroup S))).mpr h)
  exact (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)

end Griess

section Main

variable {S : Type} [Group S] [Group.IsPerfect S]

theorem hopf_formula_hopfMultiplier [Finite S] :
    Nonempty (Multiplicative (H2 (Rep.trivial ℤ S ℤ)) ≃* hopfMultiplier S) ∧
      Nonempty (Multiplicative (H2 (Rep.trivial ℤ S ℤ)) ≃* CFSG.Open.griessHopfMultiplier S) := by
  obtain ⟨F⟩ := nonempty_mulEquiv_hopfMultiplier (S := S)
  exact ⟨⟨F⟩, ⟨F.trans (hopfMultiplierEquivGriess S).symm⟩⟩

theorem perfect_central_kernel_quotient_of_schur_multiplier [Finite S] {E : Type v} [Group E]
    [Finite E] [Group.IsPerfect E] (p : E →* S) (hp : Function.Surjective p)
    (hC : p.ker ≤ center E) :
    (IsPerfectCentralExtension S (hopfCoverMap S) ∧
      ∀ (E' : Type v) [Group E'] (q : E' →* S), IsCentralExtension S q →
        ∃! h : HopfCover S →* E', q.comp h = hopfCoverMap S) ∧
    (∃ h : HopfCover S →* E, p.comp h = hopfCoverMap S ∧
      (∀ h' : HopfCover S →* E, p.comp h' = hopfCoverMap S → h' = h) ∧
      Function.Surjective h ∧ (hopfMultiplier S).map h = p.ker ∧
      ∃ e : hopfMultiplier S ⧸ (h.comp (hopfMultiplier S).subtype).ker ≃* p.ker,
        ∀ m : hopfMultiplier S, (e (m : hopfMultiplier S ⧸ (h.comp
          (hopfMultiplier S).subtype).ker) : E) = h m) ∧
    Nonempty (Multiplicative (H2 (Rep.trivial ℤ S ℤ)) ≃* hopfMultiplier S) ∧
    ∃ f : Multiplicative (H2 (Rep.trivial ℤ S ℤ)) →* E, f.range = p.ker := by
  obtain ⟨hU, hh⟩ := perfect_central_kernel_quotient_of_hopf_multiplier p hp hC
  obtain ⟨F⟩ := nonempty_mulEquiv_hopfMultiplier (S := S)
  obtain ⟨h, -, -, -, hmap, -⟩ := id hh
  refine ⟨hU, hh, ⟨F⟩, ((h.comp (hopfMultiplier S).subtype).comp F.toMonoidHom), ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr F.surjective, ← MonoidHom.range_eq_map,
    MonoidHom.range_comp, Subgroup.range_subtype, hmap]

end Main

end CFSG.RankThree.PerfectCover
