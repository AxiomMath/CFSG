module

public import CFSG.Sporadic.SchreierLemmas.MooreCosets
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public noncomputable section

namespace CFSG.Sporadic.SchreierLemmas

open Equiv Equiv.Perm
open CFSG.ComponentClassification.PresentationLocal

variable {n : ℕ}

@[expose] def moorePerm (n i : ℕ) : Perm (Fin n) :=
  if h : i = 1 ∧ 2 < n then
    swap ⟨0, by omega⟩ ⟨2, h.2⟩ * swap ⟨0, by omega⟩ ⟨1, by omega⟩
  else if h' : 2 ≤ i ∧ i + 1 < n then
    swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨i, by omega⟩ ⟨i + 1, h'.2⟩
  else 1

theorem moorePerm_one (hn : 3 ≤ n) :
    moorePerm n 1 = swap ⟨0, by omega⟩ ⟨2, by omega⟩ * swap ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rw [moorePerm, dite_eq_left ⟨rfl, by omega⟩]

theorem moorePerm_of_two_le {i : ℕ} (h2 : 2 ≤ i) (hi : i + 1 < n) :
    moorePerm n i = swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨i, by omega⟩ ⟨i + 1, hi⟩ := by
  rw [moorePerm, dite_eq_right (by omega), dite_eq_left ⟨h2, hi⟩]

theorem sign_moorePerm (i : ℕ) : sign (moorePerm n i) = 1 := by
  unfold moorePerm
  split_ifs with h h'
  · rw [sign_mul, sign_swap (by simp [Fin.ext_iff]), sign_swap (by simp [Fin.ext_iff])]
    rfl
  · rw [sign_mul, sign_swap (by simp [Fin.ext_iff]), sign_swap (by simp [Fin.ext_iff])]
    rfl
  · exact sign_one

@[expose] def mooreCycle (n i : ℕ) : alternatingGroup (Fin n) :=
  ⟨moorePerm n i, (mem_alternatingGroup).2 (sign_moorePerm i)⟩

theorem coe_mooreCycle (i : ℕ) : (mooreCycle n i : Perm (Fin n)) = moorePerm n i := rfl

theorem swap_mul_swap_pow_three {α : Type*} [Fintype α] [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : (swap a b * swap a c) ^ 3 = 1 := by
  rw [← (isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf, pow_orderOf_eq_one]

theorem swap_mul_swap_pow_three' {α : Type*} [Fintype α] [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : (swap b a * swap a c) ^ 3 = 1 := by
  rw [swap_comm b a]
  exact swap_mul_swap_pow_three hab hac hbc

theorem swap_mul_swap_comm {α : Type*} [DecidableEq α] {a b c d : α} (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  have h := swap_apply_apply (swap a b) c d
  rw [swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_of_ne_of_ne had.symm hbd.symm,
    swap_inv] at h
  conv_rhs => rw [h]
  exact (mul_swap_mul_self _ _ _).symm

theorem isMooreFamily_mooreCycle (hn : 3 ≤ n) : IsMooreFamily (n - 2) (mooreCycle n) := by
  have hne : ∀ {a b : ℕ} (ha : a < n) (hb : b < n), a ≠ b →
      (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := fun _ _ h e => h (Fin.ext_iff.1 e)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [Subgroup.coe_pow, coe_mooreCycle, moorePerm_one hn, OneMemClass.coe_one]
    exact swap_mul_swap_pow_three (hne _ _ (by omega)) (hne _ _ (by omega)) (hne _ _ (by omega))
  · intro j h2 hj
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, coe_mooreCycle, moorePerm_of_two_le h2 (by omega),
      OneMemClass.coe_one]
    exact swap_mul_swap_sq_eq_one (hne _ _ (by omega)) (hne _ _ (by omega))
      (hne _ _ (by omega)) (hne _ _ (by omega))
  · intro j h2 hj
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_mooreCycle, coe_mooreCycle,
      moorePerm_of_two_le h2 (by omega), OneMemClass.coe_one]
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · obtain rfl : j = 2 := by omega
      rw [show (2 - 1 : ℕ) = 1 from rfl, moorePerm_one hn, mul_assoc, swap_mul_self_mul]
      exact swap_mul_swap_pow_three' (hne _ _ (by omega)) (hne _ _ (by omega))
        (hne _ _ (by omega))
    · rw [moorePerm_of_two_le (i := j - 1) (by omega) (by omega)]
      rw [swap_mul_swap_comm (hne _ _ (by omega)) (hne _ _ (by omega)) (hne _ _ (by omega))
          (hne _ _ (by omega)), mul_assoc, swap_mul_self_mul]
      have e : (⟨j - 1 + 1, by omega⟩ : Fin n) = ⟨j, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]
      exact swap_mul_swap_pow_three' (hne _ _ (by omega)) (hne _ _ (by omega))
        (hne _ _ (by omega))
  · intro i j hi hij hj
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_mooreCycle, coe_mooreCycle,
      moorePerm_of_two_le (i := j) (by omega) (by omega), OneMemClass.coe_one]
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · obtain rfl : i = 1 := by omega
      rw [moorePerm_one hn, mul_assoc, swap_mul_self_mul]
      exact swap_mul_swap_sq_eq_one (hne _ _ (by omega)) (hne _ _ (by omega))
        (hne _ _ (by omega)) (hne _ _ (by omega))
    · rw [moorePerm_of_two_le hi2 (by omega),
        swap_mul_swap_comm (hne _ _ (by omega)) (hne _ _ (by omega)) (hne _ _ (by omega))
          (hne _ _ (by omega)), mul_assoc, swap_mul_self_mul]
      exact swap_mul_swap_sq_eq_one (hne _ _ (by omega)) (hne _ _ (by omega))
        (hne _ _ (by omega)) (hne _ _ (by omega))

theorem carmichaelPerm_succ {k : ℕ} (h2 : 2 ≤ k) (hk : k + 1 < n) :
    carmichaelPerm (⟨⟨k + 1, hk⟩, by simp; omega⟩ : CarmichaelIndex n) =
      (moorePerm n k * carmichaelPerm (⟨⟨k, by omega⟩, h2⟩ : CarmichaelIndex n) *
        moorePerm n k)⁻¹ := by
  set z : Fin n := ⟨0, by omega⟩
  set o : Fin n := ⟨1, by omega⟩
  set p : Fin n := ⟨k, by omega⟩
  set q : Fin n := ⟨k + 1, hk⟩
  have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
  have hzp : z ≠ p := by simp [z, p, Fin.ext_iff]; omega
  have hzq : z ≠ q := by simp [z, q, Fin.ext_iff]
  have hop : o ≠ p := by simp [o, p, Fin.ext_iff]; omega
  have hoq : o ≠ q := by simp [o, q, Fin.ext_iff]; omega
  have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
  have hσ : moorePerm n k = swap z o * swap p q := moorePerm_of_two_le h2 hk
  change swap z q * swap z o = (moorePerm n k * (swap z p * swap z o) * moorePerm n k)⁻¹
  rw [hσ]
  set σ := swap z o * swap p q
  have hσinv : σ⁻¹ = σ := by
    rw [mul_inv_rev, swap_inv, swap_inv]
    exact swap_mul_swap_comm hzp.symm hop.symm hzq.symm hoq.symm
  have h0 : σ z = o := by
    simp only [σ, Perm.mul_apply, swap_apply_of_ne_of_ne hzp hzq, swap_apply_left]
  have h1 : σ o = z := by
    simp only [σ, Perm.mul_apply, swap_apply_of_ne_of_ne hop hoq, swap_apply_right]
  have hp : σ p = q := by
    simp only [σ, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hzq.symm hoq.symm]
  have hconj : σ * (swap z p * swap z o) * σ = swap o q * swap o z :=
    calc σ * (swap z p * swap z o) * σ = σ * (swap z p * swap z o) * σ⁻¹ := by rw [hσinv]
      _ = (σ * swap z p * σ⁻¹) * (σ * swap z o * σ⁻¹) := by group
      _ = swap (σ z) (σ p) * swap (σ z) (σ o) := by rw [← swap_apply_apply, ← swap_apply_apply]
      _ = swap o q * swap o z := by rw [h0, hp, h1]
  rw [hconj, mul_inv_rev, swap_inv, swap_inv]
  ext x
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem closure_mooreCycle (hn : 3 ≤ n) :
    Subgroup.closure (mooreCycle n '' Set.Icc 1 (n - 2)) = ⊤ := by
  set K := Subgroup.closure (mooreCycle n '' Set.Icc 1 (n - 2))
  have hmem : ∀ i, 1 ≤ i → i ≤ n - 2 → mooreCycle n i ∈ K := fun i h1 h2 =>
    Subgroup.subset_closure ⟨i, ⟨h1, h2⟩, rfl⟩
  have hc : ∀ d (k : ℕ) (h2 : 2 ≤ k) (hk : k < n), k - 2 = d →
      carmichaelCycle (⟨⟨k, hk⟩, h2⟩ : CarmichaelIndex n) ∈ K := by
    intro d
    induction d with
    | zero =>
      intro k h2 hk hd
      obtain rfl : k = 2 := by omega
      have e : carmichaelCycle (⟨⟨2, hk⟩, h2⟩ : CarmichaelIndex n) = mooreCycle n 1 :=
        Subtype.ext (by rw [coe_mooreCycle, moorePerm_one hn]; rfl)
      rw [e]
      exact hmem 1 le_rfl (by omega)
    | succ d ih =>
      intro k h2 hk hd
      have hprev := ih (k - 1) (by omega) (by omega) (by omega)
      have e : carmichaelCycle (⟨⟨k, hk⟩, h2⟩ : CarmichaelIndex n) =
          (mooreCycle n (k - 1) * carmichaelCycle (⟨⟨k - 1, by omega⟩, by simp; omega⟩ :
            CarmichaelIndex n) * mooreCycle n (k - 1))⁻¹ := by
        refine Subtype.ext ?_
        have := carmichaelPerm_succ (n := n) (k := k - 1) (by omega) (by omega)
        simp only [show k - 1 + 1 = k by omega] at this
        exact this
      rw [e]
      exact inv_mem (mul_mem (mul_mem (hmem _ (by omega) (by omega)) hprev)
        (hmem _ (by omega) (by omega)))
  rw [eq_top_iff, ← closure_range_carmichaelCycle hn, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact hc _ k.1 k.2 k.1.isLt rfl

theorem IsMooreFamily.prod {G H : Type*} [Group G] [Group H] {M : ℕ} {x : ℕ → G} {y : ℕ → H}
    (hx : IsMooreFamily M x) (hy : IsMooreFamily M y) :
    IsMooreFamily M (fun i => (x i, y i)) :=
  ⟨Prod.ext (by simpa using hx.cube_one) (by simpa using hy.cube_one),
    fun j h2 hj => Prod.ext (by simpa using hx.sq_eq_one j h2 hj)
      (by simpa using hy.sq_eq_one j h2 hj),
    fun j h2 hj => Prod.ext (by simpa using hx.cube_adjacent j h2 hj)
      (by simpa using hy.cube_adjacent j h2 hj),
    fun i j hi hij hj => Prod.ext (by simpa using hx.sq_distant i j hi hij hj)
      (by simpa using hy.sq_distant i j hi hij hj)⟩

theorem exists_hom_mooreCycle (hn : 3 ≤ n) {J : Type*} [Group J] (x : ℕ → J)
    (hx : IsMooreFamily (n - 2) x) :
    ∃ φ : alternatingGroup (Fin n) →* J, ∀ i ∈ Set.Icc 1 (n - 2), φ (mooreCycle n i) = x i := by
  let y : ℕ → alternatingGroup (Fin n) × J := fun i => (mooreCycle n i, x i)
  set K := Subgroup.closure (y '' Set.Icc 1 (n - 2))
  obtain ⟨hKfin, hKcard⟩ :=
    finite_closure_and_card_le_of_moore (n - 2) y ((isMooreFamily_mooreCycle hn).prod hx)
  let p : K →* alternatingGroup (Fin n) := (MonoidHom.fst _ _).comp K.subtype
  have hp : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_mooreCycle hn, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨⟨y i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩, rfl⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hbij : Function.Bijective p := hp.bijective_of_nat_card_le (by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rwa [show n - 2 + 2 = n by omega] at hKcard)
  let E := MulEquiv.ofBijective p hbij
  refine ⟨((MonoidHom.snd _ _).comp K.subtype).comp E.symm.toMonoidHom, fun i hi => ?_⟩
  have hE : E.symm (mooreCycle n i) = ⟨y i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩ :=
    E.symm_apply_eq.2 rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hE]
  rfl

theorem hom_ext_mooreCycle (hn : 3 ≤ n) {L : Type*} [Group L]
    {φ ψ : alternatingGroup (Fin n) →* L}
    (h : ∀ i ∈ Set.Icc 1 (n - 2), φ (mooreCycle n i) = ψ (mooreCycle n i)) : φ = ψ := by
  refine MonoidHom.eq_of_eqOn_dense (closure_mooreCycle hn) ?_
  rintro _ ⟨i, hi, rfl⟩
  exact h i hi

@[expose] def mooreFreeGen (M i : ℕ) : FreeGroup (Fin M) :=
  if h : 1 ≤ i ∧ i ≤ M then FreeGroup.of ⟨i - 1, by omega⟩ else 1

variable (M : ℕ) in
@[expose] def mooreRels : Set (FreeGroup (Fin M)) :=
  {mooreFreeGen M 1 ^ 3} ∪
    {r | ∃ j, 2 ≤ j ∧ j ≤ M ∧
      (r = mooreFreeGen M j ^ 2 ∨ r = (mooreFreeGen M (j - 1) * mooreFreeGen M j) ^ 3)} ∪
    {r | ∃ i j, 1 ≤ i ∧ i + 2 ≤ j ∧ j ≤ M ∧ r = (mooreFreeGen M i * mooreFreeGen M j) ^ 2}

theorem lift_mooreFreeGen {G : Type*} [Group G] {M : ℕ} (x : ℕ → G) {i : ℕ} (h1 : 1 ≤ i)
    (hi : i ≤ M) : FreeGroup.lift (fun k : Fin M => x (k + 1)) (mooreFreeGen M i) = x i := by
  rw [mooreFreeGen, dite_eq_left ⟨h1, hi⟩, FreeGroup.lift_apply_of]
  congr 1
  simp only
  omega

theorem lift_mooreRels {G : Type*} [Group G] {M : ℕ} (hM : 1 ≤ M) {x : ℕ → G}
    (hx : IsMooreFamily M x) :
    ∀ r ∈ mooreRels M, FreeGroup.lift (fun k : Fin M => x (k + 1)) r = 1 := by
  rintro r ((rfl | ⟨j, h2, hj, rfl | rfl⟩) | ⟨i, j, hi, hij, hj, rfl⟩)
  · rw [map_pow, lift_mooreFreeGen x le_rfl hM, hx.cube_one]
  · rw [map_pow, lift_mooreFreeGen x (by omega) hj, hx.sq_eq_one j h2 hj]
  · rw [map_pow, map_mul, lift_mooreFreeGen x (by omega) (by omega),
      lift_mooreFreeGen x (by omega) hj, hx.cube_adjacent j h2 hj]
  · rw [map_pow, map_mul, lift_mooreFreeGen x hi (by omega), lift_mooreFreeGen x (by omega) hj,
      hx.sq_distant i j hi hij hj]

theorem isMooreFamily_presented (M : ℕ) :
    IsMooreFamily M (fun i => PresentedGroup.mk (mooreRels M) (mooreFreeGen M i)) := by
  refine ⟨?_, fun j h2 hj => ?_, fun j h2 hj => ?_, fun i j hi hij hj => ?_⟩
  · rw [← map_pow]
    exact PresentedGroup.one_of_mem (Or.inl (Or.inl rfl))
  · rw [← map_pow]
    exact PresentedGroup.one_of_mem (Or.inl (Or.inr ⟨j, h2, hj, Or.inl rfl⟩))
  · rw [← map_mul, ← map_pow]
    exact PresentedGroup.one_of_mem (Or.inl (Or.inr ⟨j, h2, hj, Or.inr rfl⟩))
  · rw [← map_mul, ← map_pow]
    exact PresentedGroup.one_of_mem (Or.inr ⟨i, j, hi, hij, hj, rfl⟩)

theorem moore_alternating_presentation (hn : 3 ≤ n) {J : Type*} [Group J] (x : ℕ → J)
    (hx : IsMooreFamily (n - 2) x) :
    (IsMooreFamily (n - 2) (mooreCycle n) ∧
      Subgroup.closure (mooreCycle n '' Set.Icc 1 (n - 2)) = ⊤) ∧
    (∃! φ : alternatingGroup (Fin n) →* J, ∀ i ∈ Set.Icc 1 (n - 2), φ (mooreCycle n i) = x i) ∧
    (∀ φ : alternatingGroup (Fin n) →* J, (∀ i ∈ Set.Icc 1 (n - 2), φ (mooreCycle n i) = x i) →
      φ.range = Subgroup.closure (x '' Set.Icc 1 (n - 2))) ∧
    (∃ e : PresentedGroup (mooreRels (n - 2)) ≃* alternatingGroup (Fin n),
      ∀ k : Fin (n - 2), e (PresentedGroup.of k) = mooreCycle n (k + 1)) ∧
    Nat.card (Subgroup.closure (x '' Set.Icc 1 (n - 2))) ∣ n.factorial / 2 ∧
    (5 ≤ n → (∃ i ∈ Set.Icc 1 (n - 2), x i ≠ 1) →
      (∀ φ : alternatingGroup (Fin n) →* J,
        (∀ i ∈ Set.Icc 1 (n - 2), φ (mooreCycle n i) = x i) → Function.Injective φ) ∧
      Nonempty (alternatingGroup (Fin n) ≃* Subgroup.closure (x '' Set.Icc 1 (n - 2)))) := by
  have hrange : ∀ φ : alternatingGroup (Fin n) →* J,
      (∀ i ∈ Set.Icc 1 (n - 2), φ (mooreCycle n i) = x i) →
        φ.range = Subgroup.closure (x '' Set.Icc 1 (n - 2)) := by
    intro φ hφ
    rw [MonoidHom.range_eq_map, ← closure_mooreCycle hn, MonoidHom.map_closure, Set.image_image]
    congr 1
    exact Set.image_congr fun i hi => hφ i hi
  obtain ⟨φ, hφ⟩ := exists_hom_mooreCycle hn x hx
  have hinj : 5 ≤ n → (∃ i ∈ Set.Icc 1 (n - 2), x i ≠ 1) →
      ∀ ψ : alternatingGroup (Fin n) →* J,
        (∀ i ∈ Set.Icc 1 (n - 2), ψ (mooreCycle n i) = x i) → Function.Injective ψ := by
    rintro h5 ⟨i, hi, hxi⟩ ψ hψ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact h5)
    rcases this.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ψ).1 h
    · exfalso
      have hmem : mooreCycle n i ∈ ψ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hψ i hi] at hmem
      exact hxi hmem
  refine ⟨⟨isMooreFamily_mooreCycle hn, closure_mooreCycle hn⟩,
    ⟨φ, hφ, fun ψ hψ => hom_ext_mooreCycle hn fun i hi => by rw [hψ i hi, hφ i hi]⟩, hrange,
    ?_, ?_, fun h5 hne => ⟨hinj h5 hne, ?_⟩⟩
  ·
    have hM : 1 ≤ n - 2 := by omega
    let f := PresentedGroup.toGroup (lift_mooreRels hM (isMooreFamily_mooreCycle hn))
    have hf : ∀ k : Fin (n - 2), f (PresentedGroup.of k) = mooreCycle n (k + 1) := fun k =>
      PresentedGroup.toGroup.of _
    obtain ⟨ψ, hψ⟩ := exists_hom_mooreCycle hn _ (isMooreFamily_presented (n - 2))
    have hgen : ∀ i (hi : i ∈ Set.Icc 1 (n - 2)),
        PresentedGroup.mk (mooreRels (n - 2)) (mooreFreeGen (n - 2) i) =
          PresentedGroup.of ⟨i - 1, by have := hi.2; omega⟩ := by
      intro i hi
      rw [mooreFreeGen, dite_eq_left ⟨hi.1, hi.2⟩]
      rfl
    refine ⟨MonoidHom.toMulEquiv f ψ ?_ ?_, hf⟩
    · refine PresentedGroup.ext fun k => ?_
      rw [MonoidHom.comp_apply, hf, hψ _ ⟨by omega, by omega⟩, hgen _ ⟨by omega, by omega⟩,
        MonoidHom.id_apply]
      congr 1
    · refine hom_ext_mooreCycle hn fun i hi => ?_
      rw [MonoidHom.comp_apply, hψ i hi, hgen i hi, hf, MonoidHom.id_apply]
      congr 1
      have := hi.1
      show i - 1 + 1 = i
      omega
  ·
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h := Subgroup.card_range_dvd φ
    rw [nat_card_alternatingGroup, Nat.card_fin] at h
    rw [← hrange φ hφ]
    exact h
  ·
    exact ⟨(MonoidHom.ofInjective (hinj h5 hne φ hφ)).trans
      (MulEquiv.subgroupCongr (hrange φ hφ))⟩

end CFSG.Sporadic.SchreierLemmas
