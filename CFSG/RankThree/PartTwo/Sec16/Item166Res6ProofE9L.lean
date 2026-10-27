module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofFix
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofNT

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {K : Type*} [Field K]

local notation "SL3" => Matrix.SpecialLinearGroup (Fin 3) K

theorem sl_ext {A B : SL3} (h : (A : Matrix (Fin 3) (Fin 3) K) = (B : Matrix (Fin 3) (Fin 3) K)) :
    A = B :=
  Matrix.SpecialLinearGroup.ext A B fun i j => by rw [h]

@[expose] def diagVec (u : Kˣ × Kˣ) : Fin 3 → K :=
  ![(u.1 : K), (u.2 : K), ((u.1 * u.2)⁻¹ : Kˣ)]

theorem det_diagVec (u : Kˣ × Kˣ) : (diagonal (diagVec u)).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_three]
  simp only [diagVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [mul_assoc, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, Units.val_one]

@[expose] noncomputable def diagSL : Kˣ × Kˣ →* SL3 where
  toFun u := ⟨diagonal (diagVec u), det_diagVec u⟩
  map_one' := by
    apply sl_ext
    change diagonal (diagVec 1) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [diagVec]
  map_mul' u v := by
    apply sl_ext
    change diagonal (diagVec (u * v)) = diagonal (diagVec u) * diagonal (diagVec v)
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> (simp [diagVec]; try ring)

theorem coe_diagSL (u : Kˣ × Kˣ) :
    ((diagSL u : SL3) : Matrix (Fin 3) (Fin 3) K) = diagonal (diagVec u) := rfl

@[expose] noncomputable def permSL : SL3 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [det_fin_three]⟩

theorem coe_permSL : ((permSL : SL3) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

theorem permSL_mul_diagSL (u : Kˣ × Kˣ) :
    permSL * diagSL u = diagSL ((u.1 * u.2)⁻¹, u.1) * (permSL : SL3) := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_permSL,
    coe_diagSL, coe_diagSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagVec, Matrix.mul_apply, Fin.sum_univ_three]

theorem permSL_pow_three : (permSL : SL3) ^ 3 = 1 := by
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_permSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem permSL_not_mem_range : (permSL : SL3) ∉ (diagSL (K := K)).range := by
  rintro ⟨u, hu⟩
  have h := congrArg (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) K) 0 2) hu
  simp [coe_diagSL, permSL] at h

theorem diagSL_injective : Function.Injective (diagSL (K := K)) := by
  intro u v h
  have h0 := congrArg (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h1 := congrArg (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp [coe_diagSL, diagVec] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem permSL_conj_diagSL (u : Kˣ × Kˣ) :
    permSL * diagSL u * permSL⁻¹ = diagSL ((u.1 * u.2)⁻¹, u.1) := by
  rw [permSL_mul_diagSL, mul_inv_cancel_right]

@[expose] noncomputable def diagSub (P : Subgroup Kˣ) : Subgroup SL3 :=
  (P.prod P).map diagSL

theorem diagSub_le_range (P : Subgroup Kˣ) : diagSub P ≤ (diagSL (K := K)).range := by
  rintro _ ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

theorem card_diagSub (P : Subgroup Kˣ) : Nat.card (diagSub P) = Nat.card P ^ 2 := by
  rw [diagSub, Subgroup.card_map_of_injective diagSL_injective,
    Nat.card_congr (Subgroup.prodEquiv P P).toEquiv, Nat.card_prod, sq]

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {x : G}
    (h : ∀ g ∈ H, x * g * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  let f : H → H := fun k => ⟨x * k * x⁻¹, h k k.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hg⟩
  have hkg : (k : G) = g := by
    have := congrArg Subtype.val hk
    simpa [f] using this
  exact hkg ▸ k.2

variable [Finite K]

theorem permSL_mem_normalizer_diagSub (P : Subgroup Kˣ) :
    (permSL : SL3) ∈ Subgroup.normalizer (diagSub P : Set SL3) := by
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [permSL_conj_diagSL]
  exact ⟨((u.1 * u.2)⁻¹, u.1), ⟨P.inv_mem (P.mul_mem hu.1 hu.2), hu.1⟩, rfl⟩

omit [Finite K] in
theorem diagSL_commute (u v : Kˣ × Kˣ) : diagSL u * diagSL v = diagSL v * (diagSL u : SL3) := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem diagSub_le_normalizer (P Q : Subgroup Kˣ) :
    diagSub P ≤ Subgroup.normalizer (diagSub Q : Set SL3) := by
  rintro _ ⟨u, -, rfl⟩
  refine mem_normalizer_of_conj_mem ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [diagSL_commute u v, mul_inv_cancel_right]
  exact ⟨v, hv, rfl⟩

@[expose] noncomputable def fourSL : Subgroup SL3 := diagSub (rootsOfUnity 2 K)

@[expose] noncomputable def fourPSL : Subgroup (projectiveSL 3 K) :=
  (fourSL (K := K)).map (proj 3 K)

omit [Finite K] in
theorem isPGroup_fourSL : IsPGroup 2 (fourSL (K := K)) := by
  rintro ⟨_, u, hu, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change diagSL u ^ 2 = 1
  rw [← map_pow]
  have h1 : u.1 ^ 2 = 1 := (mem_rootsOfUnity 2 u.1).mp hu.1
  have h2 : u.2 ^ 2 = 1 := (mem_rootsOfUnity 2 u.2).mp hu.2
  rw [show u ^ 2 = 1 from Prod.ext h1 h2, map_one]

omit [Finite K] in
theorem isPGroup_fourPSL : IsPGroup 2 (fourPSL (K := K)) := isPGroup_fourSL.map _

omit [Finite K] in
theorem fourPSL_ne_bot (h2 : (2 : K) ≠ 0) : fourPSL (K := K) ≠ ⊥ := by
  intro hbot
  have hmem : proj 3 K (diagSL (-1, -1)) ∈ fourPSL (K := K) :=
    ⟨diagSL (-1, -1), ⟨(-1, -1), ⟨(mem_rootsOfUnity 2 _).mpr neg_one_sq,
      (mem_rootsOfUnity 2 _).mpr neg_one_sq⟩, rfl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot, proj_eq_one_iff, mem_scalars] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  have h0 := congrFun (congrFun hc 0) 0
  have h22 := congrFun (congrFun hc 2) 2
  simp [coe_diagSL, diagVec] at h0 h22
  apply h2
  rw [← h22] at h0
  linear_combination -h0

omit [Finite K] in
theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj x : G →* G) = H := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx g).mp hg
  · intro hy
    refine ⟨x⁻¹ * y * x, (Subgroup.mem_normalizer_iff.mp hx _).mpr ?_, ?_⟩
    · simpa [mul_assoc] using hy
    · simp [mul_assoc]

omit [Finite K] in
theorem map_conj_fourPSL {x : SL3} (hx : x ∈ Subgroup.normalizer (fourSL (K := K) : Set SL3)) :
    (fourPSL (K := K)).map (MulAut.conj (proj 3 K x) : projectiveSL 3 K →* projectiveSL 3 K) =
      fourPSL := by
  have hcomp : (MulAut.conj (proj 3 K x) : projectiveSL 3 K →* projectiveSL 3 K).comp
      (proj 3 K) = (proj 3 K).comp (MulAut.conj x : SL3 →* SL3) := by
    ext g
    simp [MulAut.conj_apply]
  rw [fourPSL, Subgroup.map_map, hcomp, ← Subgroup.map_map, map_conj_eq_of_mem_normalizer hx]

@[expose] noncomputable def stabSL (P : Subgroup Kˣ) : Subgroup SL3 :=
  Subgroup.normalizer (fourSL (K := K) : Set SL3) ⊓ Subgroup.normalizer (diagSub P : Set SL3)

theorem three_pow_dvd_card_stabSL (P : Subgroup Kˣ) {a : ℕ} (hP : Nat.card P = 3 ^ a) :
    3 ^ (2 * a + 1) ∣ Nat.card (stabSL (K := K) P) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := stabSL (K := K) P with hHdef
  have hDH : diagSub P ≤ H := le_inf (diagSub_le_normalizer P _) Subgroup.le_normalizer
  have hπH : (permSL : SL3) ∈ H :=
    ⟨permSL_mem_normalizer_diagSub _, permSL_mem_normalizer_diagSub P⟩
  set D := (diagSub P).subgroupOf H with hD
  have hDn : D.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDH).mpr inf_le_right
  have hcardD : Nat.card D = 3 ^ (2 * a) := by
    rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv, card_diagSub, hP, ← pow_mul,
      mul_comm]
  set πb : H ⧸ D := QuotientGroup.mk ⟨permSL, hπH⟩ with hπb
  have hπ3 : πb ^ 3 = 1 := by
    rw [hπb, ← QuotientGroup.mk_pow]
    have : (⟨permSL, hπH⟩ : H) ^ 3 = 1 := Subtype.ext permSL_pow_three
    rw [this, QuotientGroup.mk_one]
  have hπ1 : πb ≠ 1 := by
    rw [hπb, Ne, QuotientGroup.eq_one_iff, hD, Subgroup.mem_subgroupOf]
    exact fun h => permSL_not_mem_range (diagSub_le_range P h)
  have hord : orderOf πb = 3 := orderOf_eq_prime hπ3 hπ1
  have h3 : 3 ∣ Nat.card (H ⧸ D) := by
    have h := orderOf_dvd_natCard πb
    rwa [hord] at h
  rw [D.card_eq_card_quotient_mul_card_subgroup, hcardD, pow_succ, mul_comm (3 ^ (2 * a)) 3]
  exact Nat.mul_dvd_mul h3 dvd_rfl

theorem not_three_dvd_index_stabSL (hq : Nat.card K % 3 = 1) (P : Sylow 3 Kˣ) :
    ¬ 3 ∣ (stabSL (K := K) (P : Subgroup Kˣ)).index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hP : Nat.card (P : Subgroup Kˣ) = 3 ^ (Nat.card K - 1).factorization 3 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_units]
  obtain ⟨c, hc3, hcard⟩ := exists_three_pow_mul_card_SL hq hq2
  have hSL : Nat.card SL3 = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [card_SL_eq (n := 3) (by norm_num), show 3 * (3 - 1) / 2 = 3 from rfl,
      show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  obtain ⟨k, hk⟩ := three_pow_dvd_card_stabSL (K := K) (P : Subgroup Kˣ) hP
  have hmul := (stabSL (K := K) (P : Subgroup Kˣ)).card_mul_index
  rw [hk, hSL, hcard, mul_assoc] at hmul
  have hck : k * (stabSL (K := K) (P : Subgroup Kˣ)).index = c :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) hmul
  exact fun h => hc3 (hck ▸ Dvd.dvd.mul_left h k)

omit [Finite K] in
theorem map_mul_aut {G : Type*} [Group G] (α β : MulAut G) (H : Subgroup G) :
    H.map ((α * β : MulAut G) : G →* G) = (H.map (β : G →* G)).map (α : G →* G) := by
  rw [Subgroup.map_map]
  rfl

omit [Finite K] in
theorem map_eq_self_of_forall {G : Type*} [Group G] {H : Subgroup G} {f : G →* G}
    (h : ∀ x ∈ H, f x = x) : H.map f = H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [h x hx]
    exact hx
  · intro hy
    exact ⟨y, hy, h y hy⟩

omit [Finite K] in
theorem ringEquiv_apply_of_sq_eq_one (σ : K ≃+* K) {x : Kˣ} (hx : x ∈ rootsOfUnity 2 K) :
    σ (x : K) = x := by
  have h : (x : K) * x = 1 := by
    rw [← Units.val_mul, ← sq, (mem_rootsOfUnity 2 x).mp hx, Units.val_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1 <;> rw [h1] <;> simp

omit [Finite K] in
theorem mul_self_of_mem_fourSL {g : SL3} (hg : g ∈ fourSL (K := K)) : g * g = 1 := by
  have h := isPGroup_fourSL ⟨g, hg⟩
  obtain ⟨u, hu, rfl⟩ := hg
  rw [← map_mul]
  have h1 : u.1 * u.1 = 1 := by rw [← sq]; exact (mem_rootsOfUnity 2 u.1).mp hu.1
  have h2 : u.2 * u.2 = 1 := by rw [← sq]; exact (mem_rootsOfUnity 2 u.2).mp hu.2
  rw [show u * u = 1 from Prod.ext h1 h2, map_one]

omit [Finite K] in
theorem map_dualAut_fourPSL :
    (fourPSL (K := K)).map (dualAut 3 K : projectiveSL 3 K →* projectiveSL 3 K) = fourPSL := by
  refine map_eq_self_of_forall ?_
  rintro _ ⟨g, hg, rfl⟩
  change dualAut 3 K (proj 3 K g) = proj 3 K g
  rw [dualAut_proj]
  congr 1
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (mul_self_of_mem_fourSL hg)
  rw [hinv]
  obtain ⟨u, -, rfl⟩ := hg
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_diagSL, diagonal_transpose]

omit [Finite K] in
theorem map_fieldAut_fourPSL (σ : K ≃+* K) :
    (fourPSL (K := K)).map (fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K) = fourPSL := by
  refine map_eq_self_of_forall ?_
  rintro _ ⟨g, hg, rfl⟩
  change fieldAut 3 K σ (proj 3 K g) = proj 3 K g
  rw [fieldAut_proj]
  congr 1
  obtain ⟨u, hu, rfl⟩ := hg
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_diagSL, RingHom.mapMatrix_apply,
    diagonal_map (map_zero _)]
  congr 1
  funext i
  have hw : (u.1 * u.2)⁻¹ ∈ rootsOfUnity 2 K :=
    (rootsOfUnity 2 K).inv_mem ((rootsOfUnity 2 K).mul_mem hu.1 hu.2)
  fin_cases i
  · exact ringEquiv_apply_of_sq_eq_one σ hu.1
  · exact ringEquiv_apply_of_sq_eq_one σ hu.2
  · exact ringEquiv_apply_of_sq_eq_one σ hw

omit [Finite K] in
theorem conjAut_toGL (X : SL3) :
    conjAut 3 K (Matrix.SpecialLinearGroup.toGL X) = MulAut.conj (proj 3 K X) := by
  ext y
  obtain ⟨Y, rfl⟩ := proj_surjective 3 K y
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

@[expose] noncomputable def diagFirst (d : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![(d : K), 1, 1])
    (by simp [det_diagonal, Fin.prod_univ_three])

omit [Finite K] in
theorem coe_diagFirst (d : Kˣ) :
    ((diagFirst d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(d : K), 1, 1] := rfl

omit [Finite K] in
theorem map_conjAut_diagFirst_fourPSL (d : Kˣ) :
    (fourPSL (K := K)).map (conjAut 3 K (diagFirst d) : projectiveSL 3 K →* projectiveSL 3 K) =
      fourPSL := by
  refine map_eq_self_of_forall ?_
  rintro _ ⟨g, hg, rfl⟩
  change conjAut 3 K (diagFirst d) (proj 3 K g) = proj 3 K g
  rw [conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  obtain ⟨u, -, rfl⟩ := hg
  have hc : diagFirst d * Matrix.SpecialLinearGroup.toGL (diagSL u) =
      Matrix.SpecialLinearGroup.toGL (diagSL u) * diagFirst d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change diagonal ![(d : K), 1, 1] * diagonal (diagVec u) =
      diagonal (diagVec u) * diagonal ![(d : K), 1, 1]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hc, mul_inv_cancel_right]

omit [Finite K] in
theorem map_conjAut_fourPSL (A : GL (Fin 3) K) :
    (fourPSL (K := K)).map (conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K) ∈
      conjOrbit (proj 3 K) (fourPSL (K := K)) := by
  set d := Matrix.GeneralLinearGroup.det A with hd
  set B := A * (diagFirst d)⁻¹ with hB
  have hdetB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hB, map_mul, map_inv]
    have hdD : Matrix.GeneralLinearGroup.det (diagFirst d) = d := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagFirst, det_diagonal, Fin.prod_univ_three]
      simp
    rw [hdD, hd, mul_inv_cancel, Units.val_one]
  set X : SL3 := ⟨B, hdetB⟩ with hX
  have hXB : Matrix.SpecialLinearGroup.toGL X = B := Units.ext rfl
  have hA : A = Matrix.SpecialLinearGroup.toGL X * diagFirst d := by
    rw [hXB, hB, inv_mul_cancel_right]
  refine ⟨X, ?_⟩
  rw [hA, map_mul, conjAut_toGL, map_mul_aut, map_conjAut_diagFirst_fourPSL]

theorem map_aut_fourPSL (α : MulAut (projectiveSL 3 K)) :
    (fourPSL (K := K)).map (α : projectiveSL 3 K →* projectiveSL 3 K) ∈
      conjOrbit (proj 3 K) (fourPSL (K := K)) := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  have hδ : (fourPSL (K := K)).map ((dualAut 3 K ^ ε : MulAut (projectiveSL 3 K)) :
      projectiveSL 3 K →* projectiveSL 3 K) = fourPSL := by
    interval_cases ε
    · exact map_eq_self_of_forall fun x _ => rfl
    · rw [pow_one]
      exact map_dualAut_fourPSL
  rw [map_mul_aut, map_mul_aut, hδ, map_fieldAut_fourPSL]
  exact map_conjAut_fourPSL A

theorem exists_fixed_fourGroup_projectiveSL (h2 : (2 : K) ≠ 0) (hq : Nat.card K % 3 = 1)
    (E : Subgroup (MulAut (projectiveSL 3 K))) (hE : IsPGroup 3 E) :
    ∃ S : Subgroup (projectiveSL 3 K), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      ∀ σ ∈ E, S.map (σ : projectiveSL 3 K →* projectiveSL 3 K) = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : DecidableEq K := Classical.decEq K
  let P : Sylow 3 Kˣ := default
  obtain ⟨x, hx⟩ := exists_fixed_conj (proj 3 K) (proj_surjective 3 K) (fourPSL (K := K))
    map_aut_fourPSL (stabSL (K := K) (P : Subgroup Kˣ)) (fun y hy => map_conj_fourPSL hy.1)
    (not_three_dvd_index_stabSL hq P) E hE
  refine ⟨_, ?_, isPGroup_fourPSL.map _, hx⟩
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (proj 3 K x)).injective]
  exact fourPSL_ne_bot h2

end Linear

end CFSG.RankThree.PartTwo.Sec16.Proof166Res6
