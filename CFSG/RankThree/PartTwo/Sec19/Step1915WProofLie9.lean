module

public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie9Gen
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1915WProof

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.Sec19.Step1917Steps

section DiagNine

variable {K : Type} [Field K]

theorem diagUnits_one' : diagUnits (1 : Kˣ) 1 1 = 1 := by
  apply Units.ext
  rw [coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits_inv' (a b c : Kˣ) : (diagUnits a b c)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits_mul]
  apply Units.ext
  rw [coe_diagUnits, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagUnits_pow' (a b c : Kˣ) (n : ℕ) : diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n)
    (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, diagUnits_one']
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, pow_succ, pow_succ, pow_succ]

@[expose] def diagNine (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ a b c : Kˣ, a ^ 9 = 1 ∧ b ^ 9 = 1 ∧ c ^ 9 = 1 ∧ g = diagUnits a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, ha, hb, hc, rfl⟩ ⟨a', b', c', ha', hb', hc', rfl⟩
    exact ⟨a * a', b * b', c * c', by rw [mul_pow, ha, ha', one_mul],
      by rw [mul_pow, hb, hb', one_mul], by rw [mul_pow, hc, hc', one_mul],
      diagUnits_mul _ _ _ _ _ _⟩
  one_mem' := ⟨1, 1, 1, one_pow _, one_pow _, one_pow _, diagUnits_one'.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, ha, hb, hc, rfl⟩
    exact ⟨a⁻¹, b⁻¹, c⁻¹, by rw [inv_pow, ha, inv_one], by rw [inv_pow, hb, inv_one],
      by rw [inv_pow, hc, inv_one], diagUnits_inv' _ _ _⟩

theorem diagUnits_mem_diagNine {a b c : Kˣ} (ha : a ^ 9 = 1) (hb : b ^ 9 = 1) (hc : c ^ 9 = 1) :
    diagUnits a b c ∈ diagNine K :=
  ⟨a, b, c, ha, hb, hc, rfl⟩

theorem isPGroup_diagNine : IsPGroup 3 (diagNine K) := by
  rintro ⟨_, a, b, c, ha, hb, hc, rfl⟩
  refine ⟨2, Subtype.ext ?_⟩
  change diagUnits a b c ^ 9 = 1
  rw [diagUnits_pow', ha, hb, hc, diagUnits_one']

theorem cycThree_mem_normalizer_diagNine :
    (cycThree : GL (Fin 3) K) ∈ Subgroup.normalizer (diagNine K : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    rw [cycThree_conj_diagUnits]
    exact diagUnits_mem_diagNine hc ha hb
  · rintro ⟨a, b, c, ha, hb, hc, hg⟩
    have : g = cycThree⁻¹ * diagUnits a b c * cycThree := by rw [← hg]; group
    rw [this]
    have e : (cycThree : GL (Fin 3) K)⁻¹ * diagUnits a b c * cycThree = diagUnits b c a := by
      rw [← cycThree_conj_diagUnits b c a]
      group
    rw [e]
    exact diagUnits_mem_diagNine hb hc ha

theorem isPGroup_diagNine_sup :
    IsPGroup 3
      (diagNine K ⊔ Subgroup.zpowers (cycThree : GL (Fin 3) K) : Subgroup (GL (Fin 3) K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isPGroup_diagNine.to_sup_of_normal_left' ?_
    (Subgroup.zpowers_le.mpr cycThree_mem_normalizer_diagNine)
  rintro ⟨_, n, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change ((cycThree : GL (Fin 3) K) ^ n) ^ 3 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
    cycThree_pow_three, _root_.one_zpow]

end DiagNine

section Centralizer

variable {K : Type} [Field K]

theorem eq_zero_of_mul_eq_mul {x a b : K} (hab : a ≠ b) (h : x * a = b * x) : x = 0 := by
  have h' : x * (a - b) = 0 := by rw [mul_sub, h, mul_comm, sub_self]
  exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hab)

theorem offDiag_eq_zero_of_comm_y {l : Kˣ} (hl1 : (l : K) ≠ 1) (hl2 : (l : K) ^ 2 ≠ 1)
    (hl3 : (l : K) ^ 3 ≠ 1) (x : GL (Fin 3) K)
    (hy : ProjGenLinGroup.mk x * ProjGenLinGroup.mk (diagUnits l l⁻¹ 1) =
      ProjGenLinGroup.mk (diagUnits l l⁻¹ 1) * ProjGenLinGroup.mk x) :
    ∀ i j, i ≠ j → (x : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at hy
  obtain ⟨u, hu⟩ := hy
  set v : Fin 3 → K := ![(l : K), ((l⁻¹ : Kˣ) : K), ((1 : Kˣ) : K)] with hv
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply]
    at hm
  have e : ∀ i j, (x : Matrix (Fin 3) (Fin 3) K) i j * (v j * u) =
      v i * (x : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    have := congrFun (congrFun hm i) j
    rw [mul_diagonal, mul_diagonal, diagonal_mul] at this
    rw [← this, mul_assoc]
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hvi : ((l⁻¹ : Kˣ) : K) = (l : K)⁻¹ := Units.val_inv_eq_inv_val l
  have hrel : ∀ i j, (x : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 → v j * u = v i := by
    intro i j hij
    have := e i j
    rw [mul_comm (v i)] at this
    exact mul_left_cancel₀ hij this
  have hrow : ∀ i, ∃ j, (x : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact (Matrix.GeneralLinearGroup.det_ne_zero x) (Matrix.det_eq_zero_of_row_eq_zero i h)
  have hv0 : v 0 = l := rfl
  have hv1 : v 1 = (l : K)⁻¹ := hvi
  have hv2 : v 2 = 1 := Units.val_one
  have hrow' : ∀ i, (l : K) * u = v i ∨ (l : K)⁻¹ * u = v i ∨ (u : K) = v i := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    have h := hrel i j hj
    fin_cases j
    · exact Or.inl h
    · exact Or.inr (Or.inl (hv1 ▸ h))
    · exact Or.inr (Or.inr (by simpa [hv2] using h))
  have hu1 : (u : K) = 1 := by
    rcases hrow' 2 with h2 | h2 | h2 <;> rw [hv2] at h2
    ·
      exfalso
      rcases hrow' 0 with h0 | h0 | h0 <;> rw [hv0] at h0
      · exact hl1 (h2.symm.trans h0).symm
      · rw [inv_mul_eq_iff_eq_mul₀ hl0] at h0
        rw [h0] at h2
        exact hl3 (by linear_combination h2)
      · rw [h0] at h2
        exact hl2 (by linear_combination h2)
    ·
      exfalso
      rw [inv_mul_eq_iff_eq_mul₀ hl0, mul_one] at h2
      rcases hrow' 1 with h1 | h1 | h1 <;> rw [hv1, h2] at h1
      · rw [← mul_eq_one_iff_eq_inv₀ hl0] at h1
        exact hl3 (by linear_combination h1)
      · rw [inv_mul_cancel₀ hl0] at h1
        exact hl1 (inv_eq_one.mp h1.symm)
      · rw [← mul_eq_one_iff_eq_inv₀ hl0] at h1
        exact hl2 (by linear_combination h1)
    · exact h2
  have hl' : (l : K) ≠ (l : K)⁻¹ := by
    intro h
    apply hl2
    have : (l : K) * l = l * (l : K)⁻¹ := by rw [← h]
    rw [mul_inv_cancel₀ hl0] at this
    rw [sq]
    exact this
  have hl1' : (l : K)⁻¹ ≠ 1 := by
    intro h
    apply hl1
    rw [← inv_inv (l : K), h, inv_one]
  intro i j hij
  have := e i j
  rw [hu1, mul_one] at this
  refine eq_zero_of_mul_eq_mul ?_ this
  fin_cases i <;> fin_cases j <;> simp [hv] at hij ⊢
  all_goals first
    | exact hl'.symm
    | exact hl1.symm
    | exact hl'
    | exact hl1
    | exact fun h => hl1 (by rw [h, Units.val_one])

theorem mk_eq_of_comm {l : Kˣ} (hl1 : (l : K) ≠ 1) (hl2 : (l : K) ^ 2 ≠ 1)
    (hl3 : (l : K) ^ 3 ≠ 1) {τ : K} (hτ : τ ^ 3 = 1) (hs : 1 + τ + τ ^ 2 = 0)
    (x : GL (Fin 3) K)
    (hy : ProjGenLinGroup.mk x * ProjGenLinGroup.mk (diagUnits l l⁻¹ 1) =
      ProjGenLinGroup.mk (diagUnits l l⁻¹ 1) * ProjGenLinGroup.mk x)
    (hc : ProjGenLinGroup.mk x * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) =
      ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk x) :
    ProjGenLinGroup.mk x = 1 ∨ ProjGenLinGroup.mk x = ProjGenLinGroup.mk (diagTau hτ) ∨
      ProjGenLinGroup.mk x = (ProjGenLinGroup.mk (diagTau hτ))⁻¹ := by
  have off := offDiag_eq_zero_of_comm_y hl1 hl2 hl3 x hy
  set X := (x : Matrix (Fin 3) (Fin 3) K) with hX
  have h01 := off 0 1 (by decide)
  have h02 := off 0 2 (by decide)
  have h10 := off 1 0 (by decide)
  have h12 := off 1 2 (by decide)
  have h20 := off 2 0 (by decide)
  have h21 := off 2 1 (by decide)
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at hc
  obtain ⟨u, hu⟩ := hc
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_cycThree, Matrix.scalar_apply]
    at hm
  have e10 := congrFun (congrFun hm 1) 0
  have e21 := congrFun (congrFun hm 2) 1
  have e02 := congrFun (congrFun hm 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, ← hX, h01, h02, h10, h12, h20, h21] at e10 e21 e02
  have ha0 : X 0 0 ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero x
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j
    · exact h0
    · exact h01
    · exact h02
  have hu3 : (u : K) ^ 3 = 1 := by
    have : X 0 0 * ((u : K) ^ 3 - 1) = 0 := by
      linear_combination (u : K) ^ 2 * e02 + (u : K) * e21 + e10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
  have hroots : ((u : K) - 1) * ((u : K) - τ) * ((u : K) - τ ^ 2) = 0 := by
    linear_combination hu3 - hτ - (u : K) ^ 2 * hs + (u : K) * τ * hs
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  rcases mul_eq_zero.mp hroots with h | h
  · rcases mul_eq_zero.mp h with h | h
    ·
      left
      have hu1 : (u : K) = 1 := sub_eq_zero.mp h
      rw [hu1, mul_one] at e10 e21 e02
      rw [← map_one ProjGenLinGroup.mk]
      refine mk_eq_of_coe_eq_smul (a := X 0 0) ?_
      rw [← hX, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ← e10, ← e21]
    ·
      right; right
      have hu1 : (u : K) = τ := sub_eq_zero.mp h
      rw [hu1] at e10 e21 e02
      rw [← map_inv]
      refine mk_eq_of_coe_eq_smul (a := X 0 0 * τ) ?_
      rw [← hX, show (((diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] from rfl]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]
      · linear_combination (-(X 0 0)) * hτ
      · linear_combination (-(X 1 1)) * hτ + τ ^ 2 * e10
      · linear_combination -e02
  ·
    right; left
    have hu1 : (u : K) = τ ^ 2 := sub_eq_zero.mp h
    rw [hu1] at e10 e21 e02
    refine mk_eq_of_coe_eq_smul (a := X 0 0 * τ ^ 2) ?_
    rw [← hX, coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]
    · linear_combination (-(X 0 0)) * hτ
    · linear_combination (-(X 1 1)) * (τ ^ 3 + 1) * hτ + τ ^ 4 * e10
    · linear_combination -e02

end Centralizer

section Elements

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_orderNine (hK : PiField π p f K) (h9 : 9 ∣ qSubPi π (p ^ f)) :
    ∃ l : Kˣ, l ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧ l ^ 9 = 1 ∧ (l : K) ≠ 1 ∧
      (l : K) ^ 2 ≠ 1 ∧ (l : K) ^ 3 ≠ 1 := by
  have := hK.finite
  have hcard : Nat.card (rootsOfUnity 9 K) = 9 :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (h9.trans (qSubPi_dvd hK))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity 9 K)
  rw [hcard] at hg
  set l : Kˣ := (g : Kˣ) with hl
  have hlo : orderOf l = 9 := by rw [hl, Subgroup.orderOf_coe, hg]
  have hne : ∀ k, 0 < k → k < 9 → (l : K) ^ k ≠ 1 := by
    intro k hk0 hk9 h
    apply pow_ne_one_of_lt_orderOf (n := k) (by omega) (by omega : k < orderOf l)
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, h])
  have hl9 : l ^ 9 = 1 := by rw [← hlo]; exact pow_orderOf_eq_one l
  refine ⟨l, ?_, hl9, by simpa using hne 1 (by norm_num) (by norm_num), hne 2 (by norm_num)
    (by norm_num), hne 3 (by norm_num) (by norm_num)⟩
  obtain ⟨k, hk⟩ := h9
  rw [mem_rootsOfUnity, hk, pow_mul, hl9, one_pow]

theorem diagUnits_mem_slPi (hK : PiField π p f K) {a b c : Kˣ}
    (ha : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hb : b ∈ rootsOfUnity (qSubPi π (p ^ f)) K)
    (hc : c ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hdet : a * b * c = 1) :
    diagUnits a b c ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [mem_slPi_iff hπ]
  refine ⟨diagUnits_mem_glPi hK ha hb hc, ?_⟩
  rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [← Units.val_mul, ← Units.val_mul, hdet, Units.val_one]

theorem mk_commutator_cyc_w {l : Kˣ} (hl9 : l ^ 9 = 1) (hτ : ((l : K) ^ 3) ^ 3 = 1) :
    ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) *
        (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ *
          (ProjGenLinGroup.mk (diagUnits l l (l ^ 7)))⁻¹ =
      ProjGenLinGroup.mk (diagTau hτ) := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, cycThree_conj_diagUnits,
    diagUnits_inv', diagUnits_mul]
  refine mk_eq_of_coe_eq_smul (a := (l : K) ^ 3) ?_
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have h9 : (l : K) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hl9, Units.val_one]
  rw [coe_diagUnits, coe_diagTau_eq_diagonal, ← diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp [Units.val_inv_eq_inv_val] <;> field_simp
  all_goals first
    | linear_combination h9
    | linear_combination -h9

theorem diagTau_comm_diagUnits {τ : K} (hτ : τ ^ 3 = 1) (a b c : Kˣ) :
    diagTau hτ * diagUnits a b c = diagUnits a b c * diagTau hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagTau_eq_diagonal, coe_diagUnits, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mk_diagTau_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ProjGenLinGroup.mk (diagTau hτ) ≠ 1 :=
  CFSG.RankThree.PartTwo.Sec13.Item138Proof.mk_diagTau_ne_one hτ hτ1

end Elements

section Main

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem threeCentralZ2_projImage (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) : ThreeCentralZ2 (projImage (slPi π 3 (p ^ f) K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨l, hlR, hl9, hl1, hl2, hl3⟩ := exists_orderNine hK h9
  set τ : K := (l : K) ^ 3 with hτdef
  have hτ : τ ^ 3 = 1 := by
    rw [hτdef, ← pow_mul, ← Units.val_pow_eq_pow_val, hl9, Units.val_one]
  have hτ1 : τ ≠ 1 := hl3
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have h3 : (3 : K) ≠ 0 := by
    intro h0
    apply hτ1
    have : (τ - 1) ^ 2 = 0 := by linear_combination hs - τ * h0
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  set M := projImage (slPi π 3 (p ^ f) K) with hM
  have hmem : ∀ g ∈ slPi π 3 (p ^ f) K, ProjGenLinGroup.mk g ∈ M := fun g hg =>
    Subgroup.mem_map_of_mem _ hg
  have hlR' : l⁻¹ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := inv_mem hlR
  have h1R : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
  have hl7R : l ^ 7 ∈ rootsOfUnity (qSubPi π (p ^ f)) K := pow_mem hlR 7
  have hy : diagUnits l l⁻¹ 1 ∈ slPi π 3 (p ^ f) K :=
    diagUnits_mem_slPi hK hlR hlR' h1R (by group)
  have hw : diagUnits l l (l ^ 7) ∈ slPi π 3 (p ^ f) K :=
    diagUnits_mem_slPi hK hlR hlR hl7R (by rw [← hl9]; group)
  have hc : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hd : diagTau hτ ∈ slPi π 3 (p ^ f) K := diagTau_mem_slPi hπ hq' hτ
  have hF : fourierGL h3 hs ∈ slPi π 3 (p ^ f) K := fourierGL_mem_slPi hK hq hτ h3 hs
  set y : M := ⟨_, hmem _ hy⟩ with hydef
  set w : M := ⟨_, hmem _ hw⟩ with hwdef
  set c : M := ⟨_, hmem _ hc⟩ with hcdef
  set d : M := ⟨_, hmem _ hd⟩ with hddef
  set F : M := ⟨_, hmem _ hF⟩ with hFdef
  set Ŝ : Subgroup (GL (Fin 3) K) := diagNine K ⊔ Subgroup.zpowers (cycThree : GL (Fin 3) K)
    with hŜ
  set S₀ : Subgroup M := (Ŝ.map ProjGenLinGroup.mk).comap M.subtype with hS₀
  have hS₀3 : IsPGroup 3 S₀ := (isPGroup_diagNine_sup.map _).comap_subtype
  have hS₀mem : ∀ g ∈ Ŝ, ∀ hg : ProjGenLinGroup.mk g ∈ M, (⟨_, hg⟩ : M) ∈ S₀ :=
    fun g hg _ => Subgroup.mem_map_of_mem _ hg
  have hyS : y ∈ S₀ := hS₀mem _ (le_sup_left (b := Subgroup.zpowers cycThree)
    (diagUnits_mem_diagNine hl9 (by rw [inv_pow, hl9, inv_one]) (one_pow _))) _
  have hwS : w ∈ S₀ := hS₀mem _ (le_sup_left (b := Subgroup.zpowers cycThree)
    (diagUnits_mem_diagNine hl9 hl9 (by rw [← pow_mul, show 7 * 9 = 9 * 7 by norm_num,
      pow_mul, hl9, one_pow]))) _
  have hcS : c ∈ S₀ := hS₀mem _ (le_sup_right (a := diagNine K) (Subgroup.mem_zpowers _)) _
  have hcw : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) *
      ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) *
        (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ *
          (ProjGenLinGroup.mk (diagUnits l l (l ^ 7)))⁻¹ =
        ProjGenLinGroup.mk (diagTau hτ) := mk_commutator_cyc_w hl9 hτ
  have hdc := mk_diagTau_cycThree hτ
  have hdw : ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) =
      ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) * ProjGenLinGroup.mk (diagTau hτ) := by
    rw [← map_mul, ← map_mul, diagTau_comm_diagUnits]
  have hFc := mk_fourier_cycThree hτ h3 hs
  have hd1 := mk_diagTau_ne_one hτ hτ1
  refine threeCentralZ2_of_data hS₀3 (u := y) (v := c) (z := d) (a := c) (b := w) (g := F)
    hyS hcS ?_ hcS hwS ?_ ?_ ?_ ?_
  ·
    rintro ⟨x, hx⟩ hxy hxc
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
    have h1 := congrArg Subtype.val hxy
    have h2 := congrArg Subtype.val hxc
    simp only [Subgroup.coe_mul] at h1 h2
    rcases mk_eq_of_comm hl1 hl2 hl3 hτ hs g h1 h2 with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  ·
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcw]
    exact hdc
  ·
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcw]
    exact hdw
  ·
    intro h
    apply hd1
    have h' : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) *
        ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) =
        ProjGenLinGroup.mk (diagUnits l l (l ^ 7)) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) :=
      congrArg Subtype.val h
    rw [← hcw, h']
    group
  ·
    apply Subtype.ext
    change ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (fourierGL h3 hs) =
      ProjGenLinGroup.mk (fourierGL h3 hs) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
    rw [← hFc]
    group

theorem step1917Z2KLie9 : Step1917Z2KLie9 := by
  intro p e _ he
  have hp : p.Prime := Fact.out
  constructor
  · intro h9
    rw [projSL_eq_projImage (p ^ e)]
    refine threeCentralZ2_projImage (π := true) ⟨hp, he, ?_⟩ ?_ ?_
    · rw [GaloisField.card p e (by omega)]
      rfl
    · change p ^ e % 3 = 1
      omega
    · change 9 ∣ p ^ e - 1
      omega
  · intro h9
    rw [projSU_eq_projImage]
    refine threeCentralZ2_projImage (π := false) ⟨hp, he, ?_⟩ ?_ ?_
    · rw [GaloisField.card p (2 * e) (by omega)]
      change p ^ (2 * e) = (p ^ e) ^ 2
      rw [← pow_mul, mul_comm]
    · change p ^ e % 3 = 2
      omega
    · change 9 ∣ p ^ e + 1
      omega

end Main

end CFSG.RankThree.PartTwo.Sec19.Step1915WProof
