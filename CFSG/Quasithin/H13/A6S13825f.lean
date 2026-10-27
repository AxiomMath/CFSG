module

public import CFSG.Quasithin.H13.A6S13825d
public import CFSG.Quasithin.H13.A6S13825e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

namespace L4Ind

abbrev Ablk (m : M4) : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![m 0 0, m 0 1; m 1 0, m 1 1]

abbrev Dblk (m : M4) : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![m 2 2, m 2 3; m 3 2, m 3 3]

theorem inQ2_mul {m m' : M4} (hm : InQ2 m) (hm' : InQ2 m') : InQ2 (m * m') := by
  obtain ⟨a, b, c, d⟩ := hm
  obtain ⟨a', b', c', d'⟩ := hm'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_four, a, b, c, d, a', b', c', d']

theorem Ablk_mul {m m' : M4} (hm' : InQ2 m') : Ablk (m * m') = Ablk m * Ablk m' := by
  obtain ⟨a, b, c, d⟩ := hm'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, a, b, c, d]

theorem Dblk_mul {m m' : M4} (hm : InQ2 m) : Dblk (m * m') = Dblk m * Dblk m' := by
  obtain ⟨a, b, c, d⟩ := hm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, a, b, c, d]

theorem Ablk_pow {m : M4} (hm : InQ2 m) : ∀ k : ℕ, Ablk (m ^ k) = Ablk m ^ k
  | 0 => by rw [pow_zero, pow_zero]; decide
  | k + 1 => by rw [pow_succ, Ablk_mul hm, Ablk_pow hm k, pow_succ]

theorem Dblk_pow {m : M4} (hm : InQ2 m) : ∀ k : ℕ, Dblk (m ^ k) = Dblk m ^ k
  | 0 => by rw [pow_zero, pow_zero]; decide
  | k + 1 => by rw [pow_succ', Dblk_mul hm, Dblk_pow hm k, pow_succ']

abbrev allM2 : List (Matrix (Fin 2) (Fin 2) (ZMod 2)) := allB

theorem mem_allM2 (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) : A ∈ allM2 := mem_allB A

@[expose] def exp6B : Bool := allM2.all fun A => allM2.all fun B =>
  !decide (A * B = 1) || decide (A ^ 6 = 1)

theorem exp6B_eq : exp6B = true := by
  decide

theorem exp6 {A B : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : A * B = 1) : A ^ 6 = 1 := by
  have := exp6B_eq
  simp only [exp6B, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at this
  exact (this A (mem_allM2 A) B (mem_allM2 B)).resolve_left (not_not.mpr h)

@[expose] def cList : List (Matrix (Fin 2) (Fin 2) (ZMod 2) × Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  [(!![0, 1; 1, 0], !![0, 1; 1, 0]), (!![0, 1; 1, 1], !![1, 1; 1, 0])]

abbrev CondC (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Prop :=
  ∃ pr ∈ cList, pr.1 * pr.2 = 1 ∧ (pr.1 * A * pr.2 * A) ^ 3 = 1 ∧ pr.1 * A * pr.2 * A ≠ 1

@[expose] def condCB (A B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Bool :=
  !decide (A * B = 1 ∧ A ≠ 1 ∧ A ^ 2 = 1) || decide (CondC A)

theorem condCB_eq : (allM2.all fun A => allM2.all fun B => condCB A B) = true := by
  decide

theorem condC_of {A B : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hAB : A * B = 1) (hA : A ≠ 1)
    (hA2 : A ^ 2 = 1) : CondC A := by
  have h0 := condCB_eq
  simp only [List.all_eq_true] at h0
  have h := h0 A (mem_allM2 A) B (mem_allM2 B)
  simp only [condCB, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  exact h.resolve_left (not_not.mpr ⟨hAB, hA, hA2⟩)

abbrev liftA (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : M4 :=
  !![C 0 0, C 0 1, 0, 0; C 1 0, C 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

abbrev liftD (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : M4 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, C 0 0, C 0 1; 0, 0, C 1 0, C 1 1]

theorem liftA_mul : ∀ C C' : Matrix (Fin 2) (Fin 2) (ZMod 2),
    liftA C * liftA C' = liftA (C * C') := by
  decide

theorem liftD_mul : ∀ C C' : Matrix (Fin 2) (Fin 2) (ZMod 2),
    liftD C * liftD C' = liftD (C * C') := by
  decide

theorem liftA_one : liftA 1 = 1 := by
  decide

theorem liftD_one : liftD 1 = 1 := by
  decide

theorem eq_one_of_three {Z : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h3 : Z ^ 3 = 1) {k : ℕ}
    (hk : Z ^ 2 ^ k = 1) : Z = 1 := by
  have h := pow_gcd_eq_one.2 ⟨hk, h3⟩
  have hc : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  rwa [hc, pow_one] at h

theorem sq_eq_one_of {A : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h6 : A ^ 6 = 1) {k : ℕ}
    (hk : A ^ 2 ^ k = 1) : A ^ 2 = 1 := by
  rcases k with _ | k
  · rw [pow_zero, pow_one] at hk
    rw [hk, one_pow]
  · refine eq_one_of_three (Z := A ^ 2) (k := k) ?_ ?_
    · rw [← pow_mul]
      exact h6
    · rw [← pow_mul, ← pow_succ']
      exact hk

theorem Ablk_liftA (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Ablk (liftA C) = C := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem Dblk_liftD (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Dblk (liftD C) = C := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_rB_of_normal {N : Subgroup SL4} (hNQ : ∀ n ∈ N, InQ2 (n : M4))
    (hnorm : ∀ q : SL4, InQ2 (q : M4) → ∀ n ∈ N, q * n * q⁻¹ ∈ N) (h2 : IsPGroup 2 ↥N) :
    ∀ n ∈ N, ∃ b, n = rB b := by
  have hpow : ∀ n ∈ N, ∃ k : ℕ, (n : M4) ^ 2 ^ k = 1 := fun n hn => by
    obtain ⟨k, hk⟩ := h2 ⟨n, hn⟩
    refine ⟨k, ?_⟩
    rw [← Matrix.SpecialLinearGroup.coe_pow]
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [this, Matrix.SpecialLinearGroup.coe_one]
  have hinvA : ∀ n ∈ N, Ablk (n : M4) * Ablk ((n⁻¹ : SL4) : M4) = 1 := fun n hn => by
    rw [← Ablk_mul (hNQ _ (N.inv_mem hn)), ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
    decide
  have hinvD : ∀ n ∈ N, Dblk (n : M4) * Dblk ((n⁻¹ : SL4) : M4) = 1 := fun n hn => by
    rw [← Dblk_mul (hNQ _ hn), ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
    decide
  have hA : ∀ n ∈ N, Ablk (n : M4) = 1 := by
    intro n hn
    by_contra hne
    obtain ⟨k, hk⟩ := hpow n hn
    have hAk : Ablk (n : M4) ^ 2 ^ k = 1 := by
      rw [← Ablk_pow (hNQ n hn), hk]
      decide
    have hA2 := sq_eq_one_of (exp6 (hinvA n hn)) hAk
    obtain ⟨pr, -, hpr, hZ3, hZ1⟩ := condC_of (hinvA n hn) hne hA2
    set q : SL4 := mkSL (liftA pr.1) (liftA pr.2) (by rw [liftA_mul, hpr, liftA_one]) with hq
    have hqQ : InQ2 (q : M4) := ⟨rfl, rfl, rfl, rfl⟩
    have hqi : ((q⁻¹ : SL4) : M4) = liftA pr.2 := coe_mkSL_inv _ _ _
    have hy : q * n * q⁻¹ * n ∈ N := N.mul_mem (hnorm q hqQ n hn) hn
    obtain ⟨k', hk'⟩ := hpow _ hy
    have hqc : (q : M4) = liftA pr.1 := rfl
    have hAy : Ablk ((q * n * q⁻¹ * n : SL4) : M4) =
        pr.1 * Ablk (n : M4) * pr.2 * Ablk (n : M4) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [Ablk_mul (hNQ n hn), Ablk_mul (by rw [hqi]; exact ⟨rfl, rfl, rfl, rfl⟩),
        Ablk_mul (hNQ n hn), hqi, hqc, Ablk_liftA, Ablk_liftA]
    apply hZ1
    refine eq_one_of_three hZ3 (k := k') ?_
    rw [← hAy, ← Ablk_pow (hNQ _ hy), hk']
    decide
  have hD : ∀ n ∈ N, Dblk (n : M4) = 1 := by
    intro n hn
    by_contra hne
    obtain ⟨k, hk⟩ := hpow n hn
    have hDk : Dblk (n : M4) ^ 2 ^ k = 1 := by
      rw [← Dblk_pow (hNQ n hn), hk]
      decide
    have hD2 := sq_eq_one_of (exp6 (hinvD n hn)) hDk
    obtain ⟨pr, -, hpr, hZ3, hZ1⟩ := condC_of (hinvD n hn) hne hD2
    set q : SL4 := mkSL (liftD pr.1) (liftD pr.2) (by rw [liftD_mul, hpr, liftD_one]) with hq
    have hqQ : InQ2 (q : M4) := ⟨rfl, rfl, rfl, rfl⟩
    have hqi : ((q⁻¹ : SL4) : M4) = liftD pr.2 := coe_mkSL_inv _ _ _
    have hqiQ : InQ2 ((q⁻¹ : SL4) : M4) := by rw [hqi]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hy : q * n * q⁻¹ * n ∈ N := N.mul_mem (hnorm q hqQ n hn) hn
    obtain ⟨k', hk'⟩ := hpow _ hy
    have hqc : (q : M4) = liftD pr.1 := rfl
    have hDy : Dblk ((q * n * q⁻¹ * n : SL4) : M4) =
        pr.1 * Dblk (n : M4) * pr.2 * Dblk (n : M4) := by
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [Dblk_mul (inQ2_mul (inQ2_mul hqQ (hNQ n hn)) hqiQ), Dblk_mul (inQ2_mul hqQ (hNQ n hn)),
        Dblk_mul hqQ, hqi, hqc, Dblk_liftD, Dblk_liftD]
    apply hZ1
    refine eq_one_of_three hZ3 (k := k') ?_
    rw [← hDy, ← Dblk_pow (hNQ _ hy), hk']
    decide
  intro n hn
  obtain ⟨a, b, c, d⟩ := hNQ n hn
  have ha := hA n hn
  have hd := hD n hn
  have h00 : (n : M4) 0 0 = 1 := congrFun (congrFun ha 0) 0
  have h01 : (n : M4) 0 1 = 0 := congrFun (congrFun ha 0) 1
  have h10 : (n : M4) 1 0 = 0 := congrFun (congrFun ha 1) 0
  have h11 : (n : M4) 1 1 = 1 := congrFun (congrFun ha 1) 1
  have h22 : (n : M4) 2 2 = 1 := congrFun (congrFun hd 0) 0
  have h23 : (n : M4) 2 3 = 0 := congrFun (congrFun hd 0) 1
  have h32 : (n : M4) 3 2 = 0 := congrFun (congrFun hd 1) 0
  have h33 : (n : M4) 3 3 = 1 := congrFun (congrFun hd 1) 1
  refine ⟨![![(n : M4) 0 2, (n : M4) 0 3], ![(n : M4) 1 2, (n : M4) 1 3]], Subtype.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rB, coe_mkSL, a, b, c, d, h00, h01, h10, h11, h22, h23, h32, h33]

variable {M : Type*} [CommGroup M] {φ : SL4 →* MulAut M}

theorem fixSub_anti {T T' : Set SL4} (h : T ⊆ T') : fixSub φ T' ≤ fixSub φ T :=
  fun _ hv a ha => hv a (h ha)

theorem fixSub_conj (g : SL4) (T : Set SL4) :
    fixSub φ ((fun a => g * a * g⁻¹) '' T) = (fixSub φ T).comap (φ g⁻¹).toMonoidHom := by
  ext v
  simp only [mem_fixSub, Subgroup.mem_comap, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, MulEquiv.coe_toMonoidHom]
  refine forall₂_congr fun a _ => ?_
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro h
    have := congrArg (φ g⁻¹) h
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this
  · intro h
    rw [h, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem index_fixSub_conj (g : SL4) (T : Set SL4) :
    (fixSub φ ((fun a => g * a * g⁻¹) '' T)).index = (fixSub φ T).index := by
  rw [fixSub_conj]
  exact Subgroup.index_comap_of_surjective _ (φ g⁻¹).surjective

end L4Ind

namespace L4Ind

theorem fixed_x4 : ∀ v : V4, (∀ s : Fin 3, B42Ln.xM4 s *ᵥ v = v) → v = 0 ∨ v = e0 := by
  decide

@[expose] def gTab : List (M4 × M4) :=
  [(!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]),
   (!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]),
   (!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1])]

theorem gTab_spec : ∀ x ∈ allV2, x ≠ 0 → ∃ pr ∈ gTab, pr.1 * pr.2 = 1 ∧
    pr.1 * rBM (fcA x) * pr.2 = a2M ∧ pr.1 * rBM (fcB x) * pr.2 = a3M := by
  decide

theorem conj_d2 : d2 * a2 * d2⁻¹ = a3 := by
  rw [d2, conj_mkSL]
  exact Subtype.ext (by decide)

theorem conj_d23 : d23 * (a2 * a3) * d23⁻¹ = a3 := by
  rw [d23, conj_mkSL]
  exact Subtype.ext (by decide)

variable {M : Type*} [CommGroup M] {φ : SL4 →* MulAut M} {m₀ m₁ : M}

theorem index_one [Finite M] (hG : Gen φ m₀ m₁) (hq : Quad23 φ) (β : M →* Multiplicative V4)
    (hβ : ∀ g v, Multiplicative.toAdd (β (φ g v)) = (g : M4) *ᵥ Multiplicative.toAdd (β v))
    (hβ0 : Multiplicative.toAdd (β m₀) = e0) (hne : φ g0 m₀ ≠ m₀) {u : SL4}
    (hu : u = a2 ∨ u = a3 ∨ u = a2 * a3) : 8 ≤ (fixSub φ {u}).index := by
  have h3 := index_a3 hG hq β hβ hβ0 hne
  rcases hu with rfl | rfl | rfl
  · rw [← index_fixSub_conj d2, Set.image_singleton, conj_d2]
    exact h3
  · exact h3
  · rw [← index_fixSub_conj d23, Set.image_singleton, conj_d23]
    exact h3

theorem e01_add_e0 : e0 + e1 + e0 = e1 := by
  decide

open scoped commutatorElement in
theorem conj_quad {G : Type*} [Group G] {U X : Subgroup G} (h : ⁅⁅U, X⁆, X⁆ = ⊥) {k x y u : G}
    (hu : k⁻¹ * u * k ∈ U) (hx : x ∈ X) (hy : y ∈ X) :
    k * x * k⁻¹ * (k * y * k⁻¹ * u * (k * y * k⁻¹)⁻¹ * u⁻¹) * (k * x * k⁻¹)⁻¹ =
      k * y * k⁻¹ * u * (k * y * k⁻¹)⁻¹ * u⁻¹ := by
  have hzm : ⁅y, k⁻¹ * u * k⁆ ∈ ⁅U, X⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hy hu
  have h1 := Subgroup.commutator_mem_commutator hzm hx
  rw [h, Subgroup.mem_bot, commutatorElement_def, commutatorElement_def] at h1
  calc k * x * k⁻¹ * (k * y * k⁻¹ * u * (k * y * k⁻¹)⁻¹ * u⁻¹) * (k * x * k⁻¹)⁻¹
      = k * ((y * (k⁻¹ * u * k) * y⁻¹ * (k⁻¹ * u * k)⁻¹ * x *
          (y * (k⁻¹ * u * k) * y⁻¹ * (k⁻¹ * u * k)⁻¹)⁻¹ * x⁻¹)⁻¹ *
          (y * (k⁻¹ * u * k) * y⁻¹ * (k⁻¹ * u * k)⁻¹)) * k⁻¹ := by group
    _ = k * y * k⁻¹ * u * (k * y * k⁻¹)⁻¹ * u⁻¹ := by
      rw [h1, inv_one, one_mul]
      group

theorem card_map_subgroupOf {G Γ : Type*} [Group G] [Group Γ] {H Q X : Subgroup G}
    (ρ : ↥H →* Γ) (hρk : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ Q) (hXH : X ≤ H) :
    Nat.card ↥((X.subgroupOf H).map ρ) = (X ⊓ Q).relIndex X := by
  have hker : ρ.ker = Q.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρk]
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hXH,
    Subgroup.inf_relIndex_left]

theorem ncard_le_four {α : Type*} {s : Set α} {a b c d : α}
    (h : ∀ x ∈ s, x = a ∨ x = b ∨ x = c ∨ x = d) : s.ncard ≤ 4 := by
  classical
  calc s.ncard ≤ (({a, b, c, d} : Finset α) : Set α).ncard :=
        Set.ncard_le_ncard (fun x hx => by simpa using h x hx) (Finset.finite_toSet _)
    _ = ({a, b, c, d} : Finset α).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

theorem ncard_le_three {α : Type*} {s : Set α} {a b c : α}
    (h : ∀ x ∈ s, x = a ∨ x = b ∨ x = c) : s.ncard ≤ 3 := by
  classical
  calc s.ncard ≤ (({a, b, c} : Finset α) : Set α).ncard :=
        Set.ncard_le_ncard (fun x hx => by simpa using h x hx) (Finset.finite_toSet _)
    _ = ({a, b, c} : Finset α).card := Set.ncard_coe_finset _
    _ ≤ 3 := Finset.card_le_three

end L4Ind

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

open L4Ind L13825 CFSG.LieType.BorelTits in
open scoped commutatorElement in
theorem natL4_of_case2 (hA21 : AsA21SQTKSection)
    (h21 : Lem13821) (h16 : Lem13816) (h1334 : Stmt13_3_4) (h18 : Lem13818Four)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V))
    (hKn : IsPSL 4 2 1 ↥(S.KSt H K)) (hhat : IsHatA6 L) (hTK : T ≤ K ⊔ pCoreOf 2 H) :
    S.NatL4 H := by
  classical
  have hF98 := hS.hF H hH
  have hF := hF98.toHypF91
  set U := conjClosure S.V3 H with hU
  have hab := isElemAbelian_UH hS hH
  have : IsMulCommutative ↥U := hab.1
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := hab.2
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure S.V3 H
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1TH : S.L1 ⊔ T ≤ H := sup_le hL1H hTH
  have hV1U : fsuV1 T V ≤ U := (S.V1_le_V2.trans S.V2_le_V3).trans (le_conjClosure _ _)
  have hHV1 : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  obtain ⟨W, ⟨hV₁W, hWU, hHW⟩, hWmax⟩ : ∃ W : Subgroup G,
      (fsuV1 T V ≤ W ∧ W < U ∧ H ≤ Subgroup.normalizer (W : Set G)) ∧
        ∀ W' : Subgroup G, (fsuV1 T V ≤ W' ∧ W' < U ∧ H ≤ Subgroup.normalizer (W' : Set G)) →
          W ≤ W' → W' = W := by
    have hne : (fsuV1 T V ≤ fsuV1 T V ∧ fsuV1 T V < U ∧
        H ≤ Subgroup.normalizer (fsuV1 T V : Set G)) := by
      refine ⟨le_rfl, lt_of_le_of_ne hV1U fun h => ?_, hHV1⟩
      exact S.v2_not_mem_V1 (h ▸ S.v2_mem_UH H)
    obtain ⟨W, hW, hWm⟩ := (Set.toFinite {W' : Subgroup G | fsuV1 T V ≤ W' ∧ W' < U ∧
      H ≤ Subgroup.normalizer (W' : Set G)}).exists_maximal ⟨_, hne⟩
    exact ⟨W, hW, fun W' hW' hle => (hWm hW' hle).antisymm hle⟩
  have hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ U → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = U := by
    intro W' hle hW'U hHW'
    by_cases h : W' = U
    · exact Or.inr h
    · exact Or.inl (hWmax W' ⟨hV₁W.trans hle, lt_of_le_of_ne hW'U h, hHW'⟩ hle)
  obtain ⟨ρ, β, hρs, hρk, hρQ, hρQ', hρU, hβs, hβk, hβe⟩ :=
    top_coords hA21 h21 h16 h1334 hS hH hK hKn hhat hTK hnt hV₁W hWU hHW hmax
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := sigmaH (S := S) hH with hσ
  have hσ1 : ∀ h : ↥H, σ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := sigmaH_eq_one_iff hH hF
  have hkerσ : ρ.ker ≤ σ.ker := fun h hh => by
    rw [MonoidHom.mem_ker] at hh ⊢
    exact (hσ1 h).2 ((hρk h).1 hh)
  set φ := ρ.liftOfRightInverse (Function.surjInv hρs) (Function.rightInverse_surjInv hρs)
    ⟨σ, hkerσ⟩ with hφdef
  have hφ : ∀ h : ↥H, φ (ρ h) = σ h := fun h =>
    ρ.liftOfRightInverse_comp_apply _ _ ⟨σ, hkerσ⟩ h
  have hβrho : ∀ (h : ↥H) (u : ↥U), Multiplicative.toAdd (β (Setup.rho U H hHU h u)) =
      (ρ h : M4) *ᵥ Multiplicative.toAdd (β u) := fun h u =>
    hβe h u _ (Setup.rho_apply_coe _ _ _)
  have hβV1 : ((fsuV1 T V).subgroupOf U).subgroupOf (⊤ : Subgroup ↥U) ≤
      (β.comp (⊤ : Subgroup ↥U).subtype).ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (hβk _).2 (hV₁W hx)
  obtain ⟨f, βM, hf1, hfσ, hfs, hβM⟩ :
      ∃ (f : ↥U →* Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U))
        (βM : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U) →* Multiplicative V4),
        (∀ x, f x = 1 ↔ (x : G) ∈ fsuV1 T V) ∧
        (∀ h u, σ h (f u) = f (Setup.rho U H hHU h u)) ∧ Function.Surjective f ∧
        ∀ u, βM (f u) = β u :=
    ⟨InternalSec.secMk _, QuotientGroup.lift _ (β.comp (⊤ : Subgroup ↥U).subtype) hβV1,
      A6Mod.secMk_eq_one_iff, fun _ _ => rfl, InternalSec.secMk_surjective _, fun _ => rfl⟩
  have hsq : ∀ x : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U), x * x = 1 := fun x => by
    rw [← pow_two]
    exact sec_sq_eq_one hU2 x
  have hβsq : ∀ y : Multiplicative V4, y * y = 1 := fun y =>
    Multiplicative.toAdd.injective (by rw [toAdd_mul, add_self_V4, toAdd_one])
  have hcong : ∀ x y : ↥U, (x : G) * (y : G) ∈ fsuV1 T V → f x = f y ∧ β x = β y := by
    intro x y hxy
    have h1 : f (x * y) = 1 := (hf1 _).2 hxy
    have h2 : β (x * y) = 1 := (hβk _).2 (hV₁W hxy)
    rw [map_mul] at h1 h2
    exact ⟨(eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right (hsq _)),
      (eq_inv_of_mul_eq_one_left h2).trans (inv_eq_of_mul_eq_one_right (hβsq _))⟩
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hgH : (g : G) ∈ H := hL1H hgL
  have hv2sq : S.v2 * S.v2 = 1 := by
    rw [← pow_two]
    exact hU2 _ (S.v2_mem_UH H)
  have hv2i : S.v2⁻¹ = S.v2 := inv_eq_of_mul_eq_one_right hv2sq
  set v₂ : ↥U := ⟨S.v2, S.v2_mem_UH H⟩ with hv₂
  have hv2U : v₂ * v₂ = 1 := Subtype.ext hv2sq
  set vg : ↥U := ⟨(g : G) * S.v2 * (g : G)⁻¹, le_conjClosure _ _ (S.conj_v2_mem_V3 hg)⟩ with hvg
  have hvgrho : Setup.rho U H hHU ⟨g, hgH⟩ v₂ = vg := Subtype.ext (Setup.rho_apply_coe _ _ _)
  have hβv2 : Multiplicative.toAdd (β v₂) = e0 := by
    have hfix : ∀ s : Fin 3, B42Ln.xM4 s *ᵥ Multiplicative.toAdd (β v₂) =
        Multiplicative.toAdd (β v₂) := by
      intro s
      obtain ⟨h, ht, hh⟩ := hρU _ (x4_mem_unitriangular s)
      have e1 := hβrho h v₂
      rw [hh, B42Ln.coe_x4] at e1
      have hc := S.comm_T_v2 ht
      rw [hv2i] at hc
      have hc' : ((Setup.rho U H hHU h v₂ : ↥U) : G) * (v₂ : G) ∈ fsuV1 T V := by
        rw [Setup.rho_apply_coe]
        exact hc
      rw [← e1, (hcong _ _ hc').2]
    rcases fixed_x4 _ hfix with h0 | h0
    · exact absurd ((hβk v₂).1 (Multiplicative.toAdd.injective (by rw [h0, toAdd_one])))
        (S.v2_not_mem hH hV₁W hWU hHW)
    · exact h0
  set w := Multiplicative.toAdd (β vg) with hw
  have hwg : w = (ρ ⟨g, hgH⟩ : M4) *ᵥ e0 := by
    rw [hw, ← hvgrho, hβrho, hβv2]
  have hwL : InL0 w := by
    rw [hwg]
    exact ((inQ2_iff _).1 (hρQ ⟨g, hgH⟩ (Subgroup.mem_sup_left hgL))).1
  have hw0 : w ≠ 0 := by
    intro h0
    have hvgW : (g : G) * S.v2 * (g : G)⁻¹ ∈ W :=
      (hβk vg).1 (Multiplicative.toAdd.injective (by rw [toAdd_one]; exact h0))
    apply S.v2_not_mem hH hV₁W hWU hHW
    have := (Subgroup.mem_normalizer_iff.mp (hHW (H.inv_mem hgH)) _).mp hvgW
    simpa [mul_assoc] using this
  have hwe : w ≠ e0 := by
    intro h0
    apply S.comm_v2_not_mem hH hV₁W hWU hHW hgL hg
    have h1 : β (vg * v₂⁻¹) = 1 := by
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_one, hβv2,
        show Multiplicative.toAdd (β vg) = e0 from h0, add_neg_cancel]
    exact (hβk _).1 h1
  have hwc : w = e1 ∨ w = e0 + e1 := by
    rcases inL0_cases w hwL with h | h | h | h
    · exact absurd h hw0
    · exact absurd h hwe
    · exact Or.inl h
    · exact Or.inr h
  set u₁ : ↥U := if w = e1 then vg else vg * v₂ with hu₁
  have hβu₁ : Multiplicative.toAdd (β u₁) = e1 := by
    rw [hu₁]
    split_ifs with h
    · exact h
    · rw [map_mul, toAdd_mul, hβv2, show Multiplicative.toAdd (β vg) = w from rfl,
        hwc.resolve_left h]
      exact e01_add_e0
  have hu₁V3 : (u₁ : G) ∈ S.V3 := by
    rw [hu₁]
    split_ifs
    · exact S.conj_v2_mem_V3 hg
    · exact S.V3.mul_mem (S.conj_v2_mem_V3 hg) S.v2_mem_V3
  have hvgu : vg = u₁ ∨ vg = u₁ * v₂ := by
    rw [hu₁]
    split_ifs
    · exact Or.inl rfl
    · right
      rw [mul_assoc, hv2U, mul_one]
  obtain ⟨m₀, hm₀⟩ : ∃ m, m = f v₂ := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m, m = f u₁ := ⟨_, rfl⟩
  have hPmul : ∀ x y : ↥U, f x = mvec m₀ m₁ (Multiplicative.toAdd (β x)) →
      f y = mvec m₀ m₁ (Multiplicative.toAdd (β y)) →
      f (x * y) = mvec m₀ m₁ (Multiplicative.toAdd (β (x * y))) := by
    intro x y hx hy
    rw [map_mul, map_mul, toAdd_mul, mvec_add hsq, hx, hy]
  have hPV1 : ∀ x : ↥U, (x : G) ∈ fsuV1 T V →
      f x = mvec m₀ m₁ (Multiplicative.toAdd (β x)) := by
    intro x hx
    rw [(hf1 x).2 hx, (hβk x).2 (hV₁W hx), toAdd_one, mvec_zero]
  have hPv2 : f v₂ = mvec m₀ m₁ (Multiplicative.toAdd (β v₂)) := by
    rw [hβv2, mvec_e0, hm₀]
  have hPu1 : f u₁ = mvec m₀ m₁ (Multiplicative.toAdd (β u₁)) := by
    rw [hβu₁, mvec_e1, hm₁]
  have hPvg : f vg = mvec m₀ m₁ (Multiplicative.toAdd (β vg)) := by
    rcases hvgu with h | h <;> rw [h]
    · exact hPu1
    · exact hPmul _ _ hPu1 hPv2
  have hL0add : ∀ z z' : V4, InL0 z → InL0 z' → InL0 (z + z') := fun z z' hz hz' =>
    ⟨by rw [Pi.add_apply, hz.1, hz'.1, add_zero], by rw [Pi.add_apply, hz.2, hz'.2, add_zero]⟩
  have hL0v2 : InL0 (Multiplicative.toAdd (β v₂)) := by
    rw [hβv2]
    exact ⟨rfl, rfl⟩
  have hV3 : ∀ v : ↥U, (v : G) ∈ S.V3 →
      f v = mvec m₀ m₁ (Multiplicative.toAdd (β v)) ∧ InL0 (Multiplicative.toAdd (β v)) := by
    intro v hv
    have hP2 : ∀ c : ↥U, (v : G) * (c : G) ∈ fsuV1 T V →
        f c = mvec m₀ m₁ (Multiplicative.toAdd (β c)) → InL0 (Multiplicative.toAdd (β c)) →
        f v = mvec m₀ m₁ (Multiplicative.toAdd (β v)) ∧ InL0 (Multiplicative.toAdd (β v)) := by
      intro c hvc hc hcL
      obtain ⟨h1, h2⟩ := hcong v c hvc
      rw [h1, h2]
      exact ⟨hc, hcL⟩
    rcases S.mem_V3_cases hg hv with h | h | h | h
    · refine ⟨hPV1 v h, ?_⟩
      rw [(hβk v).2 (hV₁W h), toAdd_one]
      exact ⟨rfl, rfl⟩
    · exact hP2 v₂ h hPv2 hL0v2
    · exact hP2 vg h hPvg hwL
    · rw [← S.v2_mul_conj hg] at h
      refine hP2 (v₂ * vg) h (hPmul _ _ hPv2 hPvg) ?_
      rw [map_mul, toAdd_mul]
      exact hL0add _ _ hL0v2 hwL
  have hL0V3 : ∀ z : V4, InL0 z →
      ∃ x : ↥U, (x : G) ∈ S.V3 ∧ Multiplicative.toAdd (β x) = z := by
    intro z hz
    rcases inL0_cases z hz with rfl | rfl | rfl | rfl
    · exact ⟨1, S.V3.one_mem, by rw [map_one, toAdd_one]⟩
    · exact ⟨v₂, S.v2_mem_V3, hβv2⟩
    · exact ⟨u₁, hu₁V3, hβu₁⟩
    · exact ⟨v₂ * u₁, S.V3.mul_mem S.v2_mem_V3 hu₁V3, by rw [map_mul, toAdd_mul, hβv2, hβu₁]⟩
  have hG : Gen φ m₀ m₁ := by
    refine ⟨hsq, ?_, ?_⟩
    · intro p hp z hz
      obtain ⟨h, hhLT, rfl⟩ := hρQ' p hp
      obtain ⟨x, hxV3, rfl⟩ := hL0V3 z hz
      have hxh : ((Setup.rho U H hHU h x : ↥U) : G) ∈ S.V3 := by
        rw [Setup.rho_apply_coe]
        exact (Subgroup.mem_normalizer_iff.mp (S.L1T_le_NV3 hhLT) _).mp hxV3
      rw [← (hV3 x hxV3).1, hφ, hfσ, (hV3 _ hxh).1, hβrho]
    · rw [eq_top_iff]
      rintro y -
      obtain ⟨u, rfl⟩ := hfs y
      have hle : U ≤ ((Subgroup.closure {x | ∃ g : SL4, ∃ z : V4, InL0 z ∧
          φ g (mvec m₀ m₁ z) = x}).comap f).map U.subtype :=
        conjClosure_le fun h hh z hz => by
          refine ⟨Setup.rho U H hHU ⟨h, hh⟩ ⟨z, le_conjClosure _ _ hz⟩, ?_,
            Setup.rho_apply_coe _ _ _⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, ← hfσ, (hV3 _ hz).1, ← hφ]
          exact Subgroup.subset_closure ⟨_, _, (hV3 _ hz).2, rfl⟩
      obtain ⟨n, hn, hnu⟩ := hle u.2
      rw [← Subtype.ext hnu]
      exact hn
  have hβφ : ∀ (p : SL4) (v : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U)),
      Multiplicative.toAdd (βM (φ p v)) = (p : M4) *ᵥ Multiplicative.toAdd (βM v) := by
    intro p v
    obtain ⟨h, rfl⟩ := hρs p
    obtain ⟨u, rfl⟩ := hfs v
    rw [hφ, hfσ, hβM, hβM, hβrho]
  have hβ0 : Multiplicative.toAdd (βM m₀) = e0 := by rw [hm₀, hβM, hβv2]
  have hβ1 : Multiplicative.toAdd (βM m₁) = e1 := by rw [hm₁, hβM, hβu₁]
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKT : K ⊔ T = H := (h21 G T L V S hS H hH K hK).2.2.1.1
  have hKnH : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hHK : H = K ⊔ (S.L1 ⊔ T) :=
    le_antisymm (hKT.symm.le.trans (sup_le_sup_left le_sup_right K)) (sup_le hKH hL1TH)
  obtain ⟨γ, γ', g', s, hDγ, hDH, hpos, hle, c, hcH, hcV⟩ := case2_data hS hH hnt
  have hm := h18 G T L V S hS H hH K hK hKnH hHK hnt γ γ' g' s hDγ hDH hle
  set Vγ := F8.Uγ V H (g' : G) with hVγ
  set Vα := CFSG.Quasithin.conjSub c Vγ with hVα
  have hVαH : Vα ≤ H := hcV.trans ((pCoreOf_le 2 _).trans hL1TH)
  have hcomm : ⁅⁅U, Vα⁆, Vα⁆ = ⊥ := by
    have h1 := congrArg (CFSG.Quasithin.conjSub c) (S.comm_comm_UH_Vγ hF98 s)
    rwa [← CFSG.Quasithin.conjSub_commutator, ← CFSG.Quasithin.conjSub_commutator,
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 H hcH),
      CFSG.Quasithin.conjSub_bot] at h1
  have hSR : ∀ y ∈ (Vα.subgroupOf H).map ρ, ∃ b, y = rB b := by
    have hN := eq_rB_of_normal (N := ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map ρ) ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hN _ ⟨x, Subgroup.mem_subgroupOf.mpr (hcV (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρQ x (pCoreOf_le 2 _ (Subgroup.mem_subgroupOf.mp hx))
    · intro q hq n hn
      obtain ⟨h₀, hh₀, rfl⟩ := hρQ' q hq
      obtain ⟨x, hx, rfl⟩ := hn
      refine ⟨h₀ * x * h₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T) hh₀) _).mp
        (Subgroup.mem_subgroupOf.mp hx)
      exact this
    · exact ((pCoreOf_isPGroup 2 _).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 _).trans hL1TH)).symm).map ρ
  have h4 : 4 ≤ Nat.card ↥((Vα.subgroupOf H).map ρ) := by
    rw [card_map_subgroupOf ρ hρk hVαH]
    have hY2 : IsPGroup 2 ↥Vα := (pCoreOf_isPGroup 2 _).to_le hcV
    rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
    have hQ : CFSG.Quasithin.conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
    rw [hVα, ← hQ, ← CFSG.Quasithin.conjSub_inf, F9.mIdx_conjSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mIdx Vγ (Vγ ⊓ pCoreOf 2 H) := Nat.pow_le_pow_right (by norm_num) hm
  have hconj : ∀ k x : ↥H, ρ k * ρ x * (ρ k)⁻¹ = ρ (k * x * k⁻¹) := fun k x => by
    rw [map_mul, map_mul, map_inv]
  have hquad : QuadHyp φ ((Vα.subgroupOf H).map ρ) := by
    intro h a ha a' ha' v
    obtain ⟨k, rfl⟩ := hρs h
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := ha'
    obtain ⟨u, rfl⟩ := hfs v
    rw [hconj, hconj, hφ, hφ, hfσ, ← map_inv f u, ← map_mul f, hfσ]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    have hku := (Subgroup.mem_normalizer_iff.mp (hHU (H.inv_mem k.2)) _).mp u.2
    rw [inv_inv] at hku
    exact conj_quad hcomm hku (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
  have hfix : φ g0 m₀ = m₀ := by
    rcases nfc_or_fc hSR h4 with ⟨b, b', hb, hb', hbb⟩ | ⟨x, hx0, hxa, hxb, hxS⟩
    · exact fix_of_nfc hG hquad hb hb' hbb
    by_contra hne
    obtain ⟨pr, -, hpr, hpa, hpb⟩ := gTab_spec x (mem_allV2 x) hx0
    obtain ⟨gS, hgA, hgB⟩ : ∃ gS : SL4,
        gS * rB (fcA x) * gS⁻¹ = a2 ∧ gS * rB (fcB x) * gS⁻¹ = a3 :=
      ⟨L4Ind.mkSL pr.1 pr.2 hpr, Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, L4Ind.coe_mkSL,
          L4Ind.coe_mkSL_inv]
        exact hpa), Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, L4Ind.coe_mkSL,
          L4Ind.coe_mkSL_inv]
        exact hpb)⟩
    have hq23 : Quad23 φ := by
      intro h v
      have := hquad (h * gS) _ hxa _ hxb v
      rwa [show h * gS * rB (fcA x) * (h * gS)⁻¹ = h * a2 * h⁻¹ by rw [← hgA]; group,
        show h * gS * rB (fcB x) * (h * gS)⁻¹ = h * a3 * h⁻¹ by rw [← hgB]; group] at this
    set Uγ := F8.Uγ S.V3 H (g' : G) with hUγ
    have hUγH : Uγ ≤ H := hF98.Uγ_le_H s
    have hqc := (hF98.F916_2_aux s hpos hle).1
    set q : SL4 := gS * ρ ⟨c, hcH⟩ with hq
    have hidx : (fixSub φ ((fun a => q * a * q⁻¹) '' ((Uγ.subgroupOf H).map ρ : Set SL4))).index
        ≤ ((Uγ ⊓ pCoreOf 2 H).relIndex Uγ) ^ 2 := by
      rw [index_fixSub_conj]
      refine le_trans ?_ ((A6Mod.index_fixV_le hHU (Setting4.le_normalizer_UV1 hH) hUγH).trans
        hqc.2.2.2.2)
      apply Subgroup.index_antitone
      intro m hm
      rw [mem_fixSub]
      rintro _ ⟨h, hh, rfl⟩
      rw [hφ]
      exact (mem_fixV.mp hm) _ (by rw [autSec_eq_map hH hUγH]; exact ⟨h, hh, rfl⟩)
    have hcardA : ((fun a => q * a * q⁻¹) '' ((Uγ.subgroupOf H).map ρ : Set SL4)).ncard =
        (Uγ ⊓ pCoreOf 2 H).relIndex Uγ := by
      rw [Set.ncard_image_of_injective _ fun a b hab => mul_left_cancel (mul_right_cancel hab),
        ← card_map_subgroupOf ρ hρk hUγH]
      exact (Nat.card_coe_set_eq _).symm
    have hpow : (Uγ ⊓ pCoreOf 2 H).relIndex Uγ =
        2 ^ mIdx Uγ (F8.Dγ S.V3 (fsuV1 T V) H (g' : G)) := by
      rw [hF98.Dγ_eq_inf_pCoreOf s]
      exact HypF98.relIndex_eq_two_pow_mIdx (F7.isPGroup_of_isElemAbelian hF98.isElemAbelian_Uγ)
    have hA'S : ∀ a ∈ (fun a => q * a * q⁻¹) '' ((Uγ.subgroupOf H).map ρ : Set SL4),
        a = 1 ∨ a = a2 ∨ a = a3 ∨ a = a2 * a3 := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hcu : ρ ⟨c, hcH⟩ * ρ u * (ρ ⟨c, hcH⟩)⁻¹ ∈ (Vα.subgroupOf H).map ρ := by
        rw [hconj]
        refine ⟨⟨c, hcH⟩ * u * ⟨c, hcH⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
        rw [hVα, CFSG.Quasithin.mem_conjSub]
        show c⁻¹ * (c * (u : G) * c⁻¹) * c ∈ Vγ
        rw [show c⁻¹ * (c * (u : G) * c⁻¹) * c = u by group]
        exact hF98.Uγ_le_Vγ (Subgroup.mem_subgroupOf.mp hu)
      have hqe : q * ρ u * q⁻¹ = gS * (ρ ⟨c, hcH⟩ * ρ u * (ρ ⟨c, hcH⟩)⁻¹) * gS⁻¹ := by
        rw [hq]
        group
      dsimp only
      rw [hqe]
      rcases hxS _ hcu with h | h | h | h <;> rw [h]
      · left
        group
      · exact Or.inr (Or.inl hgA)
      · exact Or.inr (Or.inr (Or.inl hgB))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [rB_add, ← hgA, ← hgB]
        group
    have hr1 : 1 ≤ mIdx Uγ (F8.Dγ S.V3 (fsuV1 T V) H (g' : G)) := hpos
    have hA4 : 2 ^ mIdx Uγ (F8.Dγ S.V3 (fsuV1 T V) H (g' : G)) ≤ 4 := by
      rw [← hpow, ← hcardA]
      exact ncard_le_four hA'S
    obtain ⟨r, hr⟩ : ∃ r, r = mIdx Uγ (F8.Dγ S.V3 (fsuV1 T V) H (g' : G)) := ⟨_, rfl⟩
    rw [← hr] at hr1 hA4 hpow
    have hr3 : r < 3 := by
      by_contra h3
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp h3)
      omega
    have hidx' := hidx
    rw [hpow] at hidx'
    interval_cases r
    ·
      obtain ⟨u, hu, hu1⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hcardA, hpow]; norm_num)
        (1 : SL4)
      have h8 := index_one hG hq23 βM hβφ hβ0 hne ((hA'S u hu).resolve_left hu1)
      have := Subgroup.index_antitone (fixSub_anti (φ := φ) (Set.singleton_subset_iff.mpr hu))
      omega
    ·
      have hmem : ∀ b, (b = a2 ∨ b = a3) →
          b ∈ (fun a => q * a * q⁻¹) '' ((Uγ.subgroupOf H).map ρ : Set SL4) := by
        rintro b hb
        by_contra hnot
        have h3 : ((fun a => q * a * q⁻¹) '' ((Uγ.subgroupOf H).map ρ : Set SL4)).ncard ≤ 3 := by
          rcases hb with rfl | rfl
          · exact ncard_le_three fun a ha => by
              rcases hA'S a ha with h | h | h | h
              · exact Or.inl h
              · exact absurd (h ▸ ha) hnot
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
          · exact ncard_le_three fun a ha => by
              rcases hA'S a ha with h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact absurd (h ▸ ha) hnot
              · exact Or.inr (Or.inr h)
        rw [hcardA, hpow] at h3
        norm_num at h3
      have hsub : ({a2, a3} : Set SL4) ⊆
          (fun a => q * a * q⁻¹) '' ((Uγ.subgroupOf H).map ρ : Set SL4) := by
        rintro b (rfl | rfl)
        · exact hmem _ (Or.inl rfl)
        · exact hmem _ (Or.inr rfl)
      have h32 := index_E hG hq23 βM hβφ hβ0 hne
      have := Subgroup.index_antitone (fixSub_anti (φ := φ) hsub)
      omega
  have hinj := injective_of_fix hG hfix βM hβφ hβ0 hβ1
  have hWV1 : ∀ u : ↥U, β u = 1 ↔ (u : G) ∈ fsuV1 T V := by
    intro u
    refine ⟨fun h1 => ?_, fun h1 => (hβk u).2 (hV₁W h1)⟩
    have : f u = 1 := hinj (by rw [hβM, map_one, h1])
    exact (hf1 u).1 this
  refine ⟨(G11.P4GL.slEquiv 4).toMonoidHom.comp ρ, (G11.P4GL.slEquiv 4).surjective.comp hρs,
    fun h => ?_, β, hβs, hWV1, fun h u v huv => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hρk]
  · rw [hβe h u v huv]
    rfl

end Setting4

open L13825 in
theorem lem13825Nat_of (hA21 : AsA21SQTKSection)
    (h21 : Lem13821) (h16 : Lem13816) (h1334 : Stmt13_3_4) (h18 : Lem13818Four) :
    Lem13825Nat := by
  intro G _ _ T L V S hS H hH K hK hnt hKn hhat hTK _
  exact Setting4.natL4_of_case2 hA21 h21 h16 h1334 h18 hS hH hK hnt hKn hhat hTK

end CFSG.Quasithin.H13.A6
