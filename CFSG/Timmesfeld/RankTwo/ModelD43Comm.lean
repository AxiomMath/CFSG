module

public import CFSG.Timmesfeld.RankTwo.ModelD43Words
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LieType.Steinberg.G2.Extras

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Chevalley.RootWalk CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_commute {x y z : G} (h : Commute ⁅y, z⁆ x) :
    ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, ← h.eq]
  group

theorem commutatorElement_mul_right_of_commute {x y z : G} (h : Commute ⁅x, z⁆ y) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ y, ← h.eq]
  group

theorem commutator_mul3_mul3 {a₁ a₂ a₃ b₁ b₂ b₃ : G} (Z : Subgroup G)
    (hZ : ∀ z ∈ Z, Commute z a₁ ∧ Commute z a₂ ∧ Commute z b₁ ∧ Commute z b₂)
    (hmem : ∀ x ∈ [a₁, a₂, a₃], ∀ y ∈ [b₁, b₂, b₃], ⁅x, y⁆ ∈ Z) :
    ⁅a₁ * a₂ * a₃, b₁ * b₂ * b₃⁆ = ⁅a₃, b₁⁆ * ⁅a₃, b₂⁆ * ⁅a₃, b₃⁆ *
      (⁅a₂, b₁⁆ * ⁅a₂, b₂⁆ * ⁅a₂, b₃⁆) * (⁅a₁, b₁⁆ * ⁅a₁, b₂⁆ * ⁅a₁, b₃⁆) := by
  have hR : ∀ x ∈ [a₁, a₂, a₃], ⁅x, b₁ * b₂ * b₃⁆ = ⁅x, b₁⁆ * ⁅x, b₂⁆ * ⁅x, b₃⁆ := by
    intro x hx
    have h3 := hZ _ (hmem x hx b₃ (by simp))
    have h2 := hZ _ (hmem x hx b₂ (by simp))
    rw [commutatorElement_mul_right_of_commute (h3.2.2.1.mul_right h3.2.2.2),
      commutatorElement_mul_right_of_commute h2.2.2.1]
  have hRZ : ∀ x ∈ [a₁, a₂, a₃], ⁅x, b₁ * b₂ * b₃⁆ ∈ Z := fun x hx => by
    rw [hR x hx]
    exact mul_mem (mul_mem (hmem x hx b₁ (by simp)) (hmem x hx b₂ (by simp)))
      (hmem x hx b₃ (by simp))
  have h3 := hZ _ (hRZ a₃ (by simp))
  have h2 := hZ _ (hRZ a₂ (by simp))
  rw [commutatorElement_mul_left_of_commute (h3.1.mul_right h3.2.1),
    commutatorElement_mul_left_of_commute h2.1, ← mul_assoc, hR a₃ (by simp), hR a₂ (by simp),
    hR a₁ (by simp)]

theorem commutatorElement_eq_conj_mul_inv (g h : G) : ⁅g, h⁆ = MulAut.conj g h * h⁻¹ := by
  rw [commutatorElement_def, MulAut.conj_apply]

theorem conj_eq_commutatorElement_mul (g h : G) : MulAut.conj g h = ⁅g, h⁆ * h := by
  rw [commutatorElement_def, MulAut.conj_apply]
  group

theorem mul_eq_commutatorElement_mul (g h : G) : g * h = ⁅g, h⁆ * h * g := by
  rw [commutatorElement_def]
  group

theorem commutatorElement_mul_right_conj (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * MulAut.conj b ⁅a, c⁆ := by
  rw [MulAut.conj_apply, commutatorElement_mul_right_eq_mul_conj]
  group

theorem mul_rearrange8 {a b c z d e f g : G} (h1 : Commute z d) (h2 : Commute e f)
    (h3 : Commute e g) (h4 : Commute f g) :
    a * b * c * (z * d * e) * f * g = a * b * c * d * z * (g * f * e) := by
  have h5 : e * f * g = g * f * e := by
    rw [h2.eq, mul_assoc, h3.eq, ← mul_assoc, h4.eq]
  calc a * b * c * (z * d * e) * f * g = a * b * c * (z * d) * (e * f * g) := by group
    _ = a * b * c * d * z * (g * f * e) := by rw [h1.eq, h5]; group

theorem prod_map_eq_of_sum_eq {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (f : ι → R → G) (hadd : ∀ i a b, f i (a + b) = f i a * f i b)
    (hcomm : ∀ i j, i ≠ j → ∀ a b, Commute (f i a) (f j b)) {L L' : List (ι × R)}
    (h : (L.map fun p => (Pi.single p.1 p.2 : ι → R)).sum =
      (L'.map fun p => (Pi.single p.1 p.2 : ι → R)).sum) :
    (L.map fun p => f p.1 p.2).prod = (L'.map fun p => f p.1 p.2).prod := by
  have h0 : ∀ i, f i 0 = 1 := fun i => by
    have := hadd i 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  let φ : ∀ i : ι, Multiplicative R →* G := fun i =>
    { toFun := fun a => f i a.toAdd
      map_one' := h0 i
      map_mul' := fun a b => hadd i a.toAdd b.toAdd }
  have hφ : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) := fun i j hij x y =>
    hcomm i j hij x.toAdd y.toAdd
  set Φ := MonoidHom.noncommPiCoprod φ hφ
  have key : ∀ L : List (ι × R), (L.map fun p => f p.1 p.2).prod =
      Φ (fun j => Multiplicative.ofAdd ((L.map fun p => (Pi.single p.1 p.2 : ι → R)).sum j)) := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Pi.zero_apply, ofAdd_zero]
      exact (map_one Φ).symm
    | cons p L ih =>
      have e : (fun j => Multiplicative.ofAdd (((p :: L).map
          fun p => (Pi.single p.1 p.2 : ι → R)).sum j)) =
          Pi.mulSingle p.1 (Multiplicative.ofAdd p.2) *
            fun j => Multiplicative.ofAdd ((L.map fun p => (Pi.single p.1 p.2 : ι → R)).sum j) := by
        funext j
        by_cases hj : j = p.1
        · subst hj
          simp
        · simp [Pi.mulSingle_eq_of_ne hj, Pi.single_eq_of_ne hj]
      rw [List.map_cons, List.prod_cons, ih, e, map_mul, MonoidHom.noncommPiCoprod_mulSingle]
      rfl
  rw [key, key, h]

end Group

section D4

variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily d4)

@[expose] def d4PosReps : List (ℕ × ℕ × List Factor) := [
  (0, 7, [(1, 1, 12, 1)]), (0, 9, [(1, 1, 13, -1)]), (1, 5, [(1, 1, 12, 1)]),
  (1, 9, [(1, 1, 15, -1)]), (3, 5, [(1, 1, 13, 1)]), (3, 7, [(1, 1, 15, 1)]),
  (0, 15, [(1, 1, 19, 1)]), (1, 13, [(1, 1, 19, 1)]), (3, 12, [(1, 1, 19, 1)]),
  (0, 2, [(1, 1, 5, -1)]), (1, 2, [(1, 1, 7, -1)]), (3, 2, [(1, 1, 9, 1)]),
  (5, 15, [(1, 1, 22, 1)]), (7, 13, [(1, 1, 22, 1)]), (9, 12, [(1, 1, 22, -1)]),
  (19, 2, [(1, 1, 22, -1)])]

theorem d4PosReps_check : repsCheck d4 d4PosReps = true := by decide +kernel

variable [CharP K 2]

theorem d4_comm {a b g : ℕ} {C : ℤ} (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps)
    (hC : C = 1 ∨ C = -1) (s t : K) :
    ⁅𝕩 (d4Root a) s, 𝕩 (d4Root b) t⁆ = 𝕩 (d4Root g) (s * t) := by
  have hr : repCheck d4 a b [(1, 1, g, C)] = true := by
    have := d4PosReps_check
    simp only [repsCheck, List.all_eq_true] at this
    exact this _ h
  rw [commutator_xPar_of_repCheck hr]
  have hC' : (C : K) = 1 := by
    rcases hC with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  simp [hC']

theorem d4_conj {a b g : ℕ} {C : ℤ} (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps)
    (hC : C = 1 ∨ C = -1) (s t : K) :
    MulAut.conj (𝕩 (d4Root a) s) (𝕩 (d4Root b) t) = 𝕩 (d4Root g) (s * t) * 𝕩 (d4Root b) t := by
  rw [conj_eq_commutatorElement_mul, d4_comm h hC]

omit [CharP K 2] in
@[expose] def d4CommOk (a b : ℕ) : Bool :=
  decide (a < (Tag.rootCertificate d4).roots.length) &&
    decide (b < (Tag.rootCertificate d4).roots.length) && decide (a ≠ b) &&
    decide (0 < CFSG.LieType.Steinberg.ht (d4Root a)) &&
    decide (0 < CFSG.LieType.Steinberg.ht (d4Root b)) &&
    !(Tag.stringData d4).memDec (Tag.rootCertificate d4) (d4Root a + d4Root b)

omit [CharP K 2] in
theorem d4_commute {a b : ℕ} (h : d4CommOk a b = true) (s t : K) :
    Commute (𝕩 (d4Root a) s) (𝕩 (d4Root b) t) := by
  simp only [d4CommOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, hpa⟩, hpb⟩, hs⟩ := h
  have hra := isRoot_rootCertificate_root ha
  have hrb := isRoot_rootCertificate_root hb
  refine commute_xPar hra hrb (fun he => hab ?_) (fun he => ?_) (fun hr => ?_) s t
  · exact rootCertificate_root_injOn ha hb he
  · have e : CFSG.LieType.Steinberg.ht (d4Root a) = -CFSG.LieType.Steinberg.ht (d4Root b) := by
      simp only [d4Root, he, CFSG.LieType.Steinberg.ht, Pi.neg_apply, Finset.sum_neg_distrib]
    linarith
  · rw [← StringData.memDec_iff (Tag.rootCertificate_check d4) (Tag.stringData_check d4),
      hs] at hr
    exact Bool.false_ne_true hr

omit [CharP K 2] in
theorem d4_conj_of_commute {a b : ℕ} (h : d4CommOk a b = true) (s t : K) :
    MulAut.conj (𝕩 (d4Root a) s) (𝕩 (d4Root b) t) = 𝕩 (d4Root b) t := by
  rw [MulAut.conj_apply, (d4_commute h s t).eq, mul_inv_cancel_right]

theorem d4_inv (γ : Fin d4.rank → ℤ) (c : K) : (𝕩 γ c)⁻¹ = 𝕩 γ c :=
  xPar_inv_eq γ c

theorem d4_comm_symm {a b g : ℕ} {C : ℤ} (h : (a, b, [(1, 1, g, C)]) ∈ d4PosReps)
    (hC : C = 1 ∨ C = -1) (s t : K) :
    ⁅𝕩 (d4Root b) t, 𝕩 (d4Root a) s⁆ = 𝕩 (d4Root g) (s * t) := by
  rw [← commutatorElement_inv, d4_comm h hC, d4_inv]

omit [CharP K 2] in
theorem d4_comm_one {a b : ℕ} (h : d4CommOk a b = true) (s t : K) :
    ⁅𝕩 (d4Root a) s, 𝕩 (d4Root b) t⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (d4_commute h s t)

end D4

section Twisted

variable {K : Type} [Field K] [CharP K 2] (σ : K →+* K)

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem twistSign_charTwo (γ : Fin d4.rank → ℤ) : twistSign σ γ = 1 := by
  rcases twistSign_eq_one_or σ γ with h | h
  · exact h
  · rw [h]
    exact CharTwo.neg_eq 1

theorem xOrbit_eq (γ : Fin d4.rank → ℤ) (c : K) :
    xOrbit σ γ c = 𝕩 γ c * 𝕩 (rho γ) (σ c) * 𝕩 (rho (rho γ)) (σ (σ c)) := by
  rw [xOrbit, twistSign_charTwo, twistSign_charTwo, one_mul, one_mul, one_mul]

omit [CharP K 2] in
theorem rho_d4Root_0 : rho (d4Root 0) = d4Root 1 := by
  funext k
  fin_cases k <;> decide

omit [CharP K 2] in
theorem rho_d4Root_1 : rho (d4Root 1) = d4Root 3 := by
  funext k
  fin_cases k <;> decide

omit [CharP K 2] in
theorem rho_d4Root_15 : rho (d4Root 15) = d4Root 13 := by
  funext k
  fin_cases k <;> decide

omit [CharP K 2] in
theorem rho_d4Root_13 : rho (d4Root 13) = d4Root 12 := by
  funext k
  fin_cases k <;> decide

omit [CharP K 2] in
theorem rho_d4Root_5 : rho (d4Root 5) = d4Root 7 := by
  funext k
  fin_cases k <;> decide

omit [CharP K 2] in
theorem rho_d4Root_7 : rho (d4Root 7) = d4Root 9 := by
  funext k
  fin_cases k <;> decide

theorem xOrbit_d4Root_0 (c : K) : xOrbit σ (d4Root 0) c =
    𝕩 (d4Root 0) c * 𝕩 (d4Root 1) (σ c) * 𝕩 (d4Root 3) (σ (σ c)) := by
  rw [xOrbit_eq, rho_d4Root_0, rho_d4Root_1]

theorem xOrbit_d4Root_15 (c : K) : xOrbit σ (d4Root 15) c =
    𝕩 (d4Root 15) c * 𝕩 (d4Root 13) (σ c) * 𝕩 (d4Root 12) (σ (σ c)) := by
  rw [xOrbit_eq, rho_d4Root_15, rho_d4Root_13]

theorem xOrbit_d4Root_5 (c : K) : xOrbit σ (d4Root 5) c =
    𝕩 (d4Root 5) c * 𝕩 (d4Root 7) (σ c) * 𝕩 (d4Root 9) (σ (σ c)) := by
  rw [xOrbit_eq, rho_d4Root_5, rho_d4Root_7]

end Twisted

section Relations

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

local notation "𝕩" => xPar (rootOperatorFamily d4)

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

theorem isRoot_d4Root {k : ℕ} (hk : k < 24) : IsRoot d4 (d4Root k) :=
  isRoot_rootCertificate_root hk

omit [CharP K 2] in
theorem commute4_of_mem {k a b c d : ℕ} (hk : k < 24) (ha : d4CommOk k a = true)
    (hb : d4CommOk k b = true) (hc : d4CommOk k c = true) (hd : d4CommOk k d = true)
    (sa sb sc sd : K) :
    ∀ z ∈ 𝕏 (d4Root k), Commute z (𝕩 (d4Root a) sa) ∧ Commute z (𝕩 (d4Root b) sb) ∧
      Commute z (𝕩 (d4Root c) sc) ∧ Commute z (𝕩 (d4Root d) sd) := by
  intro z hz
  obtain ⟨e, rfl⟩ := (mem_rootGroup_iff (isRoot_d4Root hk) z).1 hz
  exact ⟨d4_commute ha _ _, d4_commute hb _ _, d4_commute hc _ _, d4_commute hd _ _⟩

include hσ in
theorem d43_comm02 (s t : K) :
    ⁅xOrbit σ (d4Root 0) s, xOrbit σ (d4Root 15) t⁆ = 𝕩 (d4Root 19) (d43Tr hσ (s * t) : K) := by
  have c1 := d4_comm_one (K := K) (a := 3) (b := 15) (by decide +kernel)
  have c2 := d4_comm_one (K := K) (a := 3) (b := 13) (by decide +kernel)
  have c3 := d4_comm (K := K) (a := 3) (b := 12) (g := 19) (by decide) (Or.inl rfl)
  have c4 := d4_comm_one (K := K) (a := 1) (b := 15) (by decide +kernel)
  have c5 := d4_comm (K := K) (a := 1) (b := 13) (g := 19) (by decide) (Or.inl rfl)
  have c6 := d4_comm_one (K := K) (a := 1) (b := 12) (by decide +kernel)
  have c7 := d4_comm (K := K) (a := 0) (b := 15) (g := 19) (by decide) (Or.inl rfl)
  have c8 := d4_comm_one (K := K) (a := 0) (b := 13) (by decide +kernel)
  have c9 := d4_comm_one (K := K) (a := 0) (b := 12) (by decide +kernel)
  rw [xOrbit_d4Root_0, xOrbit_d4Root_15, commutator_mul3_mul3 (𝕏 (d4Root 19))
    (commute4_of_mem (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ _ _)]
  · simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, one_mul, mul_one, ← xPar_add]
    congr 1
    simp only [coe_d43Tr, map_mul]
    ring
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
      simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9] <;>
      first | exact one_mem _ | exact xPar_mem (isRoot_d4Root (by decide)) _

include hσ in
theorem d43_comm24 (s t : K) :
    ⁅xOrbit σ (d4Root 15) s, xOrbit σ (d4Root 5) t⁆ = 𝕩 (d4Root 22) (d43Tr hσ (s * t) : K) := by
  have c1 := d4_comm_one (K := K) (a := 12) (b := 5) (by decide +kernel)
  have c2 := d4_comm_one (K := K) (a := 12) (b := 7) (by decide +kernel)
  have c3 := d4_comm_symm (K := K) (a := 9) (b := 12) (g := 22) (by decide) (Or.inr rfl)
  have c4 := d4_comm_one (K := K) (a := 13) (b := 5) (by decide +kernel)
  have c5 := d4_comm_symm (K := K) (a := 7) (b := 13) (g := 22) (by decide) (Or.inl rfl)
  have c6 := d4_comm_one (K := K) (a := 13) (b := 9) (by decide +kernel)
  have c7 := d4_comm_symm (K := K) (a := 5) (b := 15) (g := 22) (by decide) (Or.inl rfl)
  have c8 := d4_comm_one (K := K) (a := 15) (b := 7) (by decide +kernel)
  have c9 := d4_comm_one (K := K) (a := 15) (b := 9) (by decide +kernel)
  rw [xOrbit_d4Root_15, xOrbit_d4Root_5, commutator_mul3_mul3 (𝕏 (d4Root 22))
    (commute4_of_mem (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ _ _)]
  · simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, one_mul, mul_one, ← xPar_add]
    congr 1
    simp only [coe_d43Tr, map_mul]
    ring
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;>
      simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9] <;>
      first | exact one_mem _ | exact xPar_mem (isRoot_d4Root (by decide)) _

omit [CharP K 2] in
theorem coe_fixedField_mul (s t : fixedField σ) : ((s * t : fixedField σ) : K) = s * t := rfl

theorem d43_comm15 (s t : fixedField σ) :
    ⁅𝕩 (d4Root 19) (s : K), 𝕩 (d4Root 2) (t : K)⁆ = 𝕩 (d4Root 22) ((s * t : fixedField σ) : K) :=
  d4_comm (a := 19) (b := 2) (g := 22) (by decide) (Or.inr rfl) _ _

theorem d43_commute01 (s t : K) : Commute (xOrbit σ (d4Root 0) s) (𝕩 (d4Root 19) t) := by
  rw [xOrbit_d4Root_0]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

theorem d43_commute03 (s t : K) : Commute (xOrbit σ (d4Root 0) s) (𝕩 (d4Root 22) t) := by
  rw [xOrbit_d4Root_0]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

theorem d43_commute12 (s t : K) : Commute (𝕩 (d4Root 19) s) (xOrbit σ (d4Root 15) t) := by
  rw [xOrbit_d4Root_15]
  exact ((d4_commute (by decide +kernel) _ _).mul_right
    (d4_commute (by decide +kernel) _ _)).mul_right (d4_commute (by decide +kernel) _ _)

omit [CharP K 2] in
theorem d43_commute13 (s t : K) : Commute (𝕩 (d4Root 19) s) (𝕩 (d4Root 22) t) :=
  d4_commute (by decide +kernel) _ _

theorem d43_commute14 (s t : K) : Commute (𝕩 (d4Root 19) s) (xOrbit σ (d4Root 5) t) := by
  rw [xOrbit_d4Root_5]
  exact ((d4_commute (by decide +kernel) _ _).mul_right
    (d4_commute (by decide +kernel) _ _)).mul_right (d4_commute (by decide +kernel) _ _)

theorem d43_commute23 (s t : K) : Commute (xOrbit σ (d4Root 15) s) (𝕩 (d4Root 22) t) := by
  rw [xOrbit_d4Root_15]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

theorem d43_commute25 (s t : K) : Commute (xOrbit σ (d4Root 15) s) (𝕩 (d4Root 2) t) := by
  rw [xOrbit_d4Root_15]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

theorem d43_commute34 (s t : K) : Commute (𝕩 (d4Root 22) s) (xOrbit σ (d4Root 5) t) := by
  rw [xOrbit_d4Root_5]
  exact ((d4_commute (by decide +kernel) _ _).mul_right
    (d4_commute (by decide +kernel) _ _)).mul_right (d4_commute (by decide +kernel) _ _)

omit [CharP K 2] in
theorem d43_commute35 (s t : K) : Commute (𝕩 (d4Root 22) s) (𝕩 (d4Root 2) t) :=
  d4_commute (by decide +kernel) _ _

theorem d43_commute45 (s t : K) : Commute (xOrbit σ (d4Root 5) s) (𝕩 (d4Root 2) t) := by
  rw [xOrbit_d4Root_5]
  exact ((d4_commute (by decide +kernel) _ _).mul_left
    (d4_commute (by decide +kernel) _ _)).mul_left (d4_commute (by decide +kernel) _ _)

include hσ in
theorem d43_comm05 (s u : K) (hu : σ u = u) :
    ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 2) u⁆ =
      𝕩 (d4Root 19) (u * (s * σ s * σ (σ s))) * xOrbit σ (d4Root 15) (u * (σ s * σ (σ s))) *
        𝕩 (d4Root 22) (u ^ 2 * (s * σ s * σ (σ s))) * xOrbit σ (d4Root 5) (u * s) := by
  have k1 := d4_conj (K := K) (a := 3) (b := 2) (g := 9) (by decide) (Or.inl rfl)
  have k2 := d4_conj (K := K) (a := 1) (b := 9) (g := 15) (by decide) (Or.inr rfl)
  have k3 := d4_conj (K := K) (a := 1) (b := 2) (g := 7) (by decide) (Or.inr rfl)
  have k4 := d4_conj (K := K) (a := 0) (b := 15) (g := 19) (by decide) (Or.inl rfl)
  have k5 := d4_conj (K := K) (a := 0) (b := 9) (g := 13) (by decide) (Or.inr rfl)
  have k6 := d4_conj (K := K) (a := 0) (b := 7) (g := 12) (by decide) (Or.inl rfl)
  have k7 := d4_conj (K := K) (a := 0) (b := 2) (g := 5) (by decide) (Or.inr rfl)
  have hsw : ∀ a b : K, 𝕩 (d4Root 9) a * 𝕩 (d4Root 12) b =
      𝕩 (d4Root 22) (a * b) * 𝕩 (d4Root 12) b * 𝕩 (d4Root 9) a := fun a b => by
    rw [mul_eq_commutatorElement_mul, d4_comm (a := 9) (b := 12) (g := 22) (by decide) (Or.inr rfl)]
  calc ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 2) u⁆ =
      𝕩 (d4Root 19) (s * (σ s * (σ (σ s) * u))) * 𝕩 (d4Root 15) (σ s * (σ (σ s) * u)) *
        𝕩 (d4Root 13) (s * (σ (σ s) * u)) * (𝕩 (d4Root 9) (σ (σ s) * u) *
          𝕩 (d4Root 12) (s * (σ s * u))) * 𝕩 (d4Root 7) (σ s * u) * 𝕩 (d4Root 5) (s * u) := by
        rw [commutatorElement_eq_conj_mul_inv, xOrbit_d4Root_0]
        simp only [map_mul, MulAut.mul_apply, k1, k2, k3, k4, k5, k6, k7]
        group
    _ = 𝕩 (d4Root 19) (s * (σ s * (σ (σ s) * u))) * 𝕩 (d4Root 15) (σ s * (σ (σ s) * u)) *
        𝕩 (d4Root 13) (s * (σ (σ s) * u)) * (𝕩 (d4Root 22) (σ (σ s) * u * (s * (σ s * u))) *
          𝕩 (d4Root 12) (s * (σ s * u)) * 𝕩 (d4Root 9) (σ (σ s) * u)) *
            𝕩 (d4Root 7) (σ s * u) * 𝕩 (d4Root 5) (s * u) := by rw [hsw]
    _ = 𝕩 (d4Root 19) (s * (σ s * (σ (σ s) * u))) * 𝕩 (d4Root 15) (σ s * (σ (σ s) * u)) *
        𝕩 (d4Root 13) (s * (σ (σ s) * u)) * 𝕩 (d4Root 12) (s * (σ s * u)) *
          𝕩 (d4Root 22) (σ (σ s) * u * (s * (σ s * u))) * (𝕩 (d4Root 5) (s * u) *
            𝕩 (d4Root 7) (σ s * u) * 𝕩 (d4Root 9) (σ (σ s) * u)) :=
        mul_rearrange8 (d4_commute (by decide +kernel) _ _) (d4_commute (by decide +kernel) _ _)
          (d4_commute (by decide +kernel) _ _) (d4_commute (by decide +kernel) _ _)
    _ = _ := by
        rw [xOrbit_d4Root_15, xOrbit_d4Root_5]
        simp only [map_mul, hσ, hu, mul_assoc]
        repeat' (first | rfl | (congr 1; ring1) | congr 1)

local notation "𝕪" => fun (i : Fin 5) => 𝕩 (d4Root (![19, 15, 13, 12, 22] i))

omit [CharP K 2] in
theorem d4_commute_five : ∀ i j : Fin 5, i ≠ j →
    d4CommOk (![19, 15, 13, 12, 22] i) (![19, 15, 13, 12, 22] j) = true := by
  decide +kernel

include hσ in
theorem d43_comm04 (s t : K) :
    ⁅xOrbit σ (d4Root 0) s, xOrbit σ (d4Root 5) t⁆ =
      𝕩 (d4Root 19) (d43Tr hσ (d43Sharp σ s * t) : K) * xOrbit σ (d4Root 15) (d43Cross σ s t) *
        𝕩 (d4Root 22) (d43Tr hσ (s * d43Sharp σ t) : K) := by
  have hA0 : ∀ c : K, ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 5) c⁆ =
      𝕩 (d4Root 19) (σ s * (σ (σ s) * c)) * 𝕩 (d4Root 13) (σ (σ s) * c) *
        𝕩 (d4Root 12) (σ s * c) := fun c => by
    rw [commutatorElement_eq_conj_mul_inv, xOrbit_d4Root_0]
    simp only [map_mul, MulAut.mul_apply,
      d4_conj (K := K) (a := 3) (b := 5) (g := 13) (by decide) (Or.inl rfl),
      d4_conj (K := K) (a := 1) (b := 13) (g := 19) (by decide) (Or.inl rfl),
      d4_conj (K := K) (a := 1) (b := 5) (g := 12) (by decide) (Or.inl rfl),
      d4_conj_of_commute (K := K) (a := 0) (b := 19) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 0) (b := 13) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 0) (b := 12) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 0) (b := 5) (by decide +kernel)]
    group
  have hA1 : ∀ c : K, ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 7) c⁆ = 𝕩 (d4Root 19) (s * (σ (σ s) * c)) *
      𝕩 (d4Root 15) (σ (σ s) * c) * 𝕩 (d4Root 12) (s * c) := fun c => by
    rw [commutatorElement_eq_conj_mul_inv, xOrbit_d4Root_0]
    simp only [map_mul, MulAut.mul_apply,
      d4_conj (K := K) (a := 3) (b := 7) (g := 15) (by decide) (Or.inl rfl),
      d4_conj_of_commute (K := K) (a := 1) (b := 15) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 1) (b := 7) (by decide +kernel),
      d4_conj (K := K) (a := 0) (b := 15) (g := 19) (by decide) (Or.inl rfl),
      d4_conj (K := K) (a := 0) (b := 7) (g := 12) (by decide) (Or.inl rfl)]
    group
  have hA3 : ∀ c : K, ⁅xOrbit σ (d4Root 0) s, 𝕩 (d4Root 9) c⁆ = 𝕩 (d4Root 19) (s * (σ s * c)) *
      𝕩 (d4Root 15) (σ s * c) * 𝕩 (d4Root 13) (s * c) := fun c => by
    rw [commutatorElement_eq_conj_mul_inv, xOrbit_d4Root_0]
    simp only [map_mul, MulAut.mul_apply,
      d4_conj_of_commute (K := K) (a := 3) (b := 9) (by decide +kernel),
      d4_conj (K := K) (a := 1) (b := 9) (g := 15) (by decide) (Or.inr rfl),
      d4_conj (K := K) (a := 0) (b := 15) (g := 19) (by decide) (Or.inl rfl),
      d4_conj (K := K) (a := 0) (b := 9) (g := 13) (by decide) (Or.inr rfl)]
    group
  have hP : ⁅xOrbit σ (d4Root 0) s, xOrbit σ (d4Root 5) t⁆ =
      ([(0, σ s * (σ (σ s) * t)), (2, σ (σ s) * t), (3, σ s * t),
        (0, s * (σ (σ s) * σ t)), (4, t * (σ (σ s) * σ t)), (1, σ (σ s) * σ t), (3, s * σ t),
        (0, s * (σ s * σ (σ t))), (4, t * (σ s * σ (σ t))), (1, σ s * σ (σ t)),
        (4, σ t * (s * σ (σ t))), (2, s * σ (σ t))].map fun p : Fin 5 × K => 𝕪 p.1 p.2).prod := by
    rw [xOrbit_d4Root_5, mul_assoc, commutatorElement_mul_right_conj,
      commutatorElement_mul_right_conj, hA0, hA1, hA3]
    simp only [map_mul,
      d4_conj_of_commute (K := K) (a := 7) (b := 19) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 7) (b := 15) (by decide +kernel),
      d4_conj (K := K) (a := 7) (b := 13) (g := 22) (by decide) (Or.inl rfl),
      d4_conj_of_commute (K := K) (a := 5) (b := 19) (by decide +kernel),
      d4_conj (K := K) (a := 5) (b := 15) (g := 22) (by decide) (Or.inl rfl),
      d4_conj_of_commute (K := K) (a := 5) (b := 12) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 5) (b := 22) (by decide +kernel),
      d4_conj_of_commute (K := K) (a := 5) (b := 13) (by decide +kernel),
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    simp only [Matrix.cons_val, mul_assoc]
  have hQ : 𝕩 (d4Root 19) (d43Tr hσ (d43Sharp σ s * t) : K) *
      xOrbit σ (d4Root 15) (d43Cross σ s t) * 𝕩 (d4Root 22) (d43Tr hσ (s * d43Sharp σ t) : K) =
      ([(0, (d43Tr hσ (d43Sharp σ s * t) : K)), (1, d43Cross σ s t),
        (2, σ (d43Cross σ s t)), (3, σ (σ (d43Cross σ s t))),
        (4, (d43Tr hσ (s * d43Sharp σ t) : K))].map fun p : Fin 5 × K => 𝕪 p.1 p.2).prod := by
    rw [xOrbit_d4Root_15]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val, mul_assoc]
  rw [hP, hQ]
  refine prod_map_eq_of_sum_eq _ (fun i a b => xPar_add _ a b)
    (fun i j hij a b => d4_commute (d4_commute_five i j hij) a b) ?_
  funext j
  fin_cases j <;>
    simp [coe_d43Tr, d43Sharp, d43Cross, map_mul, map_add, hσ] <;> ring

end Relations

end CFSG.Timmesfeld.RankTwo
