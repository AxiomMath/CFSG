module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphAlgebra

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

private theorem psuC2a_commuting_join {G : Type*} [Group G] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ι → Subgroup G)
    (hsolv : ∀ i ∈ s, Group.IsSolvable ↥(H i))
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, x * y = y * x) :
    Group.IsSolvable ↥(⨆ i ∈ s, H i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hbot : (⨆ i ∈ (∅ : Finset ι), H i) = (⊥ : Subgroup G) := by simp
      rw [hbot]
      exact isSolvable_of_comm (fun p q => Subsingleton.elim (p * q) (q * p))
  | insert a t ha ih =>
      rw [Finset.iSup_insert]
      set J : Subgroup G := ⨆ i ∈ t, H i with hJ
      have ht : Group.IsSolvable ↥J :=
        ih (fun i hi => hsolv i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj hij => hcomm i (Finset.mem_insert_of_mem hi)
            j (Finset.mem_insert_of_mem hj) hij)
      have hcommAJ : ∀ x ∈ H a, ∀ y ∈ J, x * y = y * x := by
        intro x hx y hy
        have hle : J ≤ Subgroup.centralizer ({x} : Set G) := by
          rw [hJ]
          rw [iSup_le_iff]
          intro i
          rw [iSup_le_iff]
          intro hi w hw
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact hcomm a (Finset.mem_insert_self a t) i
            (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi) x hx w hw
        have hy' := hle hy
        rw [Subgroup.mem_centralizer_iff] at hy'
        exact hy' x (by rw [Set.mem_singleton_iff])
      let φ : ↥(H a) × ↥J →* G :=
        { toFun := fun p => (p.1 : G) * (p.2 : G)
          map_one' := by simp
          map_mul' := by
            intro p q
            show ((p.1 * q.1 : ↥(H a)) : G) * ((p.2 * q.2 : ↥J) : G) =
              ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
                = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by noncomm_ring
              _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                    rw [hcommAJ (q.1 : G) q.1.property (p.2 : G) p.2.property]
              _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by noncomm_ring }
      have hrange : φ.range = H a ⊔ J := by
        apply le_antisymm
        · rintro z ⟨w, rfl⟩
          exact mul_mem (Subgroup.mem_sup_left w.1.property) (Subgroup.mem_sup_right w.2.property)
        · rw [sup_le_iff]
          constructor
          · intro x hx
            exact ⟨(⟨x, hx⟩, 1), by simp [φ]⟩
          · intro y hy
            exact ⟨(1, ⟨y, hy⟩), by simp [φ]⟩
      haveI : Group.IsSolvable ↥(H a) := hsolv a (Finset.mem_insert_self a t)
      haveI : Group.IsSolvable ↥J := ht
      exact solvable_of_surjective
        (f := φ.codRestrict (H a ⊔ J) (fun w => hrange ▸ ⟨w, rfl⟩))
        (fun z =>
          let ⟨w, hw⟩ := MonoidHom.mem_range.mp
            (show (z : G) ∈ φ.range by rw [hrange]; exact z.property)
          ⟨w, Subtype.ext hw⟩)

private theorem psuC2a_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  have hgen : ∀ a ∈ psuAlg B, a * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * a := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => x * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * x) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rfl
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    · intro x y hx hy hpx hpy
      rw [add_mul, mul_add, hpx, hpy]
    · intro x y hx hy hpx hpy
      rw [Matrix.mul_assoc x y (B : Matrix (Fin n) (Fin n) K), hpy,
        ← Matrix.mul_assoc x (B : Matrix (Fin n) (Fin n) K) y, hpx,
        Matrix.mul_assoc (B : Matrix (Fin n) (Fin n) K) x y]
  intro a ha b hb
  refine Algebra.adjoin_induction (p := fun x _ => a * x = x * a) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hgen a ha
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro x y hx hy hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y hx hy hpx hpy
    rw [← Matrix.mul_assoc a x y, hpx, Matrix.mul_assoc x a y, hpy,
      ← Matrix.mul_assoc x y a]

private theorem psuC2a_dag_perm {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, psuDag h e ∈ P := by
  intro e he
  exact primFamily_map_mem hP (psuDag h) (psuDag_add h) (psuDag_mul h)
    (fun a ha => (psuGraph_star_mem S a ha).1) (fun a _ => psuDag_dag h a) (psuC2a_comm B) e he

private theorem psuC2a_orbit_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, psuOrbitIdem h e ∈ psuAlg B ∧ psuDag h (psuOrbitIdem h e) = psuOrbitIdem h e ∧
      psuOrbitIdem h e * psuOrbitIdem h e = psuOrbitIdem h e := by
  classical
  intro e he
  have heA : e ∈ psuAlg B := ((hP.1 e).mp he).1
  have hprim : IsPrimIdemIn (psuAlg B) e := (hP.1 e).1 he
  have hdagP : psuDag h e ∈ P := psuC2a_dag_perm S P hP e he
  have hdagA : psuDag h e ∈ psuAlg B := ((hP.1 _).mp hdagP).1
  have hdagprim : IsPrimIdemIn (psuAlg B) (psuDag h e) := (hP.1 _).1 hdagP
  by_cases hd : psuDag h e = e
  · rw [psuOrbitIdem, if_pos hd]
    exact ⟨heA, hd, hprim.2.1.eq⟩
  · rw [psuOrbitIdem, if_neg hd]
    have hne : e ≠ psuDag h e := fun h => hd h.symm
    have he_hd : e * psuDag h e = 0 := hP.2.1 e he (psuDag h e) hdagP hne
    have hd_e : psuDag h e * e = 0 := hP.2.1 (psuDag h e) hdagP e he (fun h => hne h.symm)
    refine ⟨Subalgebra.add_mem _ heA hdagA, ?_, ?_⟩
    · rw [psuDag_add h, psuDag_dag h, add_comm]
    · rw [add_mul, mul_add, mul_add, hprim.2.1.eq, he_hd, hd_e, hdagprim.2.1.eq]
      abel

private theorem psuC2a_orbit_self {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, psuOrbitIdem h e * e = e := by
  classical
  intro e he
  have hprim : IsPrimIdemIn (psuAlg B) e := (hP.1 e).1 he
  have hdagP : psuDag h e ∈ P := psuC2a_dag_perm S P hP e he
  have hdagprim : IsPrimIdemIn (psuAlg B) (psuDag h e) := (hP.1 _).1 hdagP
  by_cases hd : psuDag h e = e
  · rw [psuOrbitIdem, if_pos hd, hprim.2.1.eq]
  · rw [psuOrbitIdem, if_neg hd]
    have hne : e ≠ psuDag h e := fun h => hd h.symm
    have hd_e : psuDag h e * e = 0 := hP.2.1 (psuDag h e) hdagP e he (fun h => hne h.symm)
    rw [add_mul, hprim.2.1.eq, hd_e, add_zero]

private theorem psuC2a_orbit_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, psuOrbitIdem h (psuDag h e) = psuOrbitIdem h e := by
  classical
  intro e he
  have hdP : psuDag h e ∈ P := psuC2a_dag_perm S P hP e he
  by_cases hd : psuDag h e = e
  · rw [hd]
  · have hd' : psuDag h (psuDag h e) ≠ psuDag h e := by
      intro hh
      exact hd (((psuDag_dag h e).symm.trans hh).symm)
    have h1 : psuOrbitIdem h (psuDag h e) = psuDag h e + psuDag h (psuDag h e) := by
      rw [psuOrbitIdem, if_neg hd']
    have h2 : psuOrbitIdem h e = e + psuDag h e := by rw [psuOrbitIdem, if_neg hd]
    rw [h1, h2, psuDag_dag, add_comm]

private theorem psuC2a_orbit_mul_other {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, ∀ p ∈ P, p ≠ e → p ≠ psuDag h e → psuOrbitIdem h e * p = 0 := by
  classical
  intro e he p hp hpe hpde
  have hdP : psuDag h e ∈ P := psuC2a_dag_perm S P hP e he
  by_cases hd : psuDag h e = e
  · have hε : psuOrbitIdem h e = e := by rw [psuOrbitIdem, if_pos hd]
    rw [hε, hP.2.1 e he p hp (fun hh => hpe hh.symm)]
  · have hε : psuOrbitIdem h e = e + psuDag h e := by rw [psuOrbitIdem, if_neg hd]
    rw [hε, add_mul, hP.2.1 e he p hp (fun hh => hpe hh.symm),
      hP.2.1 (psuDag h e) hdP p hp (fun hh => hpde hh.symm), add_zero]

private theorem psuC2a_orbit_orth {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∀ e ∈ P, ∀ e' ∈ P, psuOrbitIdem h e ≠ psuOrbitIdem h e' →
      psuOrbitIdem h e * psuOrbitIdem h e' = 0 := by
  classical
  intro e he e' he' hne
  have hdP' : psuDag h e' ∈ P := psuC2a_dag_perm S P hP e' he'
  have hdag' : psuOrbitIdem h (psuDag h e') = psuOrbitIdem h e' :=
    psuC2a_orbit_dag S P hP e' he'
  by_cases hd' : psuDag h e' = e'
  · have hε' : psuOrbitIdem h e' = e' := by rw [psuOrbitIdem, if_pos hd']
    have hpe : e' ≠ e := fun hh => hne (by rw [hh])
    have hpde : e' ≠ psuDag h e := fun hh => hne (by rw [hh, psuC2a_orbit_dag S P hP e he])
    rw [hε', psuC2a_orbit_mul_other S P hP e he e' he' hpe hpde]
  · have hε' : psuOrbitIdem h e' = e' + psuDag h e' := by rw [psuOrbitIdem, if_neg hd']
    have h1 : psuOrbitIdem h e * e' = 0 :=
      psuC2a_orbit_mul_other S P hP e he e' he' (fun hh => hne (by rw [hh]))
        (fun hh => hne (by rw [hh, psuC2a_orbit_dag S P hP e he]))
    have h2 : psuOrbitIdem h e * psuDag h e' = 0 :=
      psuC2a_orbit_mul_other S P hP e he (psuDag h e') hdP'
        (fun hh => hne (by rw [← hh, psuC2a_orbit_dag S P hP e' he']))
        (fun hh => hne (by rw [← psuDag_dag h e', ← psuDag_dag h e, hh]))
    rw [hε', mul_add, h1, h2, add_zero]

private theorem psuC2a_orbit_sum {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P) :
    ∑ ε ∈ P.image (psuOrbitIdem h), ε = 1 := by
  classical
  set Q := P.image (psuOrbitIdem h) with hQ
  have hSe : ∀ e ∈ P, (∑ ε ∈ Q, ε) * e = e := by
    intro e he
    rw [Finset.sum_mul]
    have hterm : ∀ ε ∈ Q, ε * e = if ε = psuOrbitIdem h e then e else 0 := by
      intro ε hε
      by_cases hq : ε = psuOrbitIdem h e
      · rw [if_pos hq, hq, psuC2a_orbit_self S P hP e he]
      · rw [if_neg hq]
        obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp hε
        calc psuOrbitIdem h e₀ * e
            = psuOrbitIdem h e₀ * (psuOrbitIdem h e * e) := by
                rw [psuC2a_orbit_self S P hP e he]
          _ = (psuOrbitIdem h e₀ * psuOrbitIdem h e) * e := by rw [mul_assoc]
          _ = 0 := by
                rw [psuC2a_orbit_orth S P hP e₀ he₀ e he (fun hh => hq hh), zero_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Q (psuOrbitIdem h e) (fun _ => e),
      if_pos (Finset.mem_image.mpr ⟨e, he, rfl⟩)]
  calc (∑ ε ∈ Q, ε) = (∑ ε ∈ Q, ε) * 1 := (mul_one _).symm
    _ = (∑ ε ∈ Q, ε) * (∑ e ∈ P, e) := by rw [hP.2.2]
    _ = ∑ e ∈ P, (∑ ε ∈ Q, ε) * e := by rw [Finset.mul_sum]
    _ = ∑ e ∈ P, e := Finset.sum_congr rfl hSe
    _ = 1 := hP.2.2

private theorem psuC2a_scalar_unique {n : ℕ} {K : Type} [Field K] [NeZero n]
    (B x : GL (Fin n) K) (c c' : Kˣ)
    (h1 : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (c : K) • ((B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)))
    (h2 : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (c' : K) • ((B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K))) :
    c = c' := by
  have hzero : ((c : K) - (c' : K)) • ((B : Matrix (Fin n) (Fin n) K) *
      (x : Matrix (Fin n) (Fin n) K)) = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  have hne : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) ≠ 0 :=
    (Units.isUnit (B * x)).ne_zero
  have hc : (c : K) - (c' : K) = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hne
  exact Units.ext (sub_eq_zero.mp hc)

private noncomputable def psuC2a_lambdaVal {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (x : psuChat h B) : Kˣ :=
  Classical.choose x.property

private theorem psuC2a_lambdaVal_spec {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (x : psuChat h B) :
    (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) =
      ((psuC2a_lambdaVal x : Kˣ) : K) • ((B : Matrix (Fin n) (Fin n) K) *
        (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  Classical.choose_spec x.property

private noncomputable def psuC2a_lambda {f n : ℕ} {K : Type} [Field K] [NeZero n]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} : psuChat h B →* Kˣ where
  toFun := fun x => psuC2a_lambdaVal x
  map_one' := by
    apply psuC2a_scalar_unique B 1 (psuC2a_lambdaVal 1) 1
    · simpa using psuC2a_lambdaVal_spec (1 : psuChat h B)
    · simp
  map_mul' := by
    intro x y
    apply psuC2a_scalar_unique B (((x * y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K)
      (psuC2a_lambdaVal (x * y)) (psuC2a_lambdaVal x * psuC2a_lambdaVal y)
    · exact psuC2a_lambdaVal_spec (x * y)
    · have hx := psuC2a_lambdaVal_spec x
      have hy := psuC2a_lambdaVal_spec y
      calc ((((x * y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)
          = (((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) *
              ((((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) *
                (B : Matrix (Fin n) (Fin n) K)) := by
              simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
        _ = (((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) *
              (((psuC2a_lambdaVal y : Kˣ) : K) • ((B : Matrix (Fin n) (Fin n) K) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K))) := by rw [hy]
        _ = ((psuC2a_lambdaVal y : Kˣ) : K) •
              ((((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) *
                ((B : Matrix (Fin n) (Fin n) K) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K))) := by
              rw [Matrix.mul_smul]
        _ = ((psuC2a_lambdaVal y : Kˣ) : K) •
              (((((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) *
                (B : Matrix (Fin n) (Fin n) K)) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K)) := by
              rw [Matrix.mul_assoc]
        _ = ((psuC2a_lambdaVal y : Kˣ) : K) •
              ((((psuC2a_lambdaVal x : Kˣ) : K) • ((B : Matrix (Fin n) (Fin n) K) *
                (((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K))) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K)) := by rw [hx]
        _ = ((psuC2a_lambdaVal y : Kˣ) : K) •
              (((psuC2a_lambdaVal x : Kˣ) : K) •
                (((B : Matrix (Fin n) (Fin n) K) *
                (((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K)) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K))) := by
              rw [Matrix.smul_mul]
        _ = (((psuC2a_lambdaVal y : Kˣ) : K) * ((psuC2a_lambdaVal x : Kˣ) : K)) •
              (((B : Matrix (Fin n) (Fin n) K) *
                (((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K)) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K)) := by
              rw [smul_smul]
        _ = (((psuC2a_lambdaVal y : Kˣ) : K) * ((psuC2a_lambdaVal x : Kˣ) : K)) •
              ((B : Matrix (Fin n) (Fin n) K) *
                ((((x : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) *
                (((y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K))) := by
              rw [Matrix.mul_assoc]
        _ = ((psuC2a_lambdaVal x * psuC2a_lambdaVal y : Kˣ) : K) •
              ((B : Matrix (Fin n) (Fin n) K) *
                ((((x * y : psuChat h B) : AutPSU.XJ h n) : GL (Fin n) K) :
                  Matrix (Fin n) (Fin n) K)) := by
              rw [Units.val_mul, mul_comm]
              simp only [Subgroup.coe_mul, Units.val_mul]

private theorem psuC2a_lambda_apply {f n : ℕ} {K : Type} [Field K] [NeZero n]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (x : psuChat h B) :
    psuC2a_lambda x = psuC2a_lambdaVal x := rfl

private theorem psuC2a_lambda_ker {f n : ℕ} {K : Type} [Field K] [NeZero n]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (x : psuChat h B) :
    psuC2a_lambda x = 1 ↔
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) *
          (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro hx
    have hspec := psuC2a_lambdaVal_spec x
    rw [← psuC2a_lambda_apply x, hx] at hspec
    simpa using hspec
  · intro hx
    apply psuC2a_scalar_unique B (((x : AutPSU.XJ h n) : GL (Fin n) K))
      (psuC2a_lambda x) 1
    · rw [psuC2a_lambda_apply]; exact psuC2a_lambdaVal_spec x
    · rw [hx]; simp

private noncomputable def psuC2a_ext {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  ((x : Matrix (Fin n) (Fin n) K) - 1) * ε + 1

private lemma psuC2a_ring_ext_fix {A : Type} [Ring A]
    (x ε : A) (hε : ε * ε = ε) : ((x - 1) * ε + 1) * (1 - ε) = 1 - ε := by
  have h1 : (x - 1) * ε * (1 - ε) = 0 := by
    rw [mul_sub, mul_one, mul_assoc, hε, sub_self]
  rw [add_mul, h1, one_mul, zero_add]

private lemma psuC2a_ring_ext_mul {A : Type} [Ring A]
    (x y ε : A) (hε : ε * ε = ε) (hyε : y * ε = ε * y) :
    ((x - 1) * ε + 1) * ((y - 1) * ε + 1) = (x * y - 1) * ε + 1 := by
  have hcomm : ε * (y - 1) = (y - 1) * ε := by
    rw [mul_sub, sub_mul, hyε, mul_one, one_mul]
  have hcross : (x - 1) * ε * ((y - 1) * ε) = (x - 1) * (y - 1) * ε := by
    calc (x - 1) * ε * ((y - 1) * ε) = (x - 1) * (ε * (y - 1)) * ε := by noncomm_ring
      _ = (x - 1) * ((y - 1) * ε) * ε := by rw [hcomm]
      _ = (x - 1) * (y - 1) * (ε * ε) := by noncomm_ring
      _ = (x - 1) * (y - 1) * ε := by rw [hε]
  rw [add_mul, mul_add, mul_add, hcross]
  noncomm_ring

private lemma psuC2a_ring_ext_comm {A : Type} [Ring A]
    (x y ε ε' : A) (horth : ε * ε' = 0) (horth' : ε' * ε = 0)
    (hxε' : x * ε' = ε' * x) (hyε : y * ε = ε * y) :
    ((x - 1) * ε + 1) * ((y - 1) * ε' + 1) =
      ((y - 1) * ε' + 1) * ((x - 1) * ε + 1) := by
  have hcommε : ε * (y - 1) = (y - 1) * ε := by
    rw [mul_sub, sub_mul, hyε, mul_one, one_mul]
  have hcommε' : ε' * (x - 1) = (x - 1) * ε' := by
    rw [mul_sub, sub_mul, hxε', mul_one, one_mul]
  have hxy : (x - 1) * ε * ((y - 1) * ε') = 0 := by
    calc (x - 1) * ε * ((y - 1) * ε') = (x - 1) * (ε * (y - 1)) * ε' := by noncomm_ring
      _ = (x - 1) * ((y - 1) * ε) * ε' := by rw [hcommε]
      _ = (x - 1) * (y - 1) * (ε * ε') := by noncomm_ring
      _ = 0 := by rw [horth, mul_zero]
  have hyx : (y - 1) * ε' * ((x - 1) * ε) = 0 := by
    calc (y - 1) * ε' * ((x - 1) * ε) = (y - 1) * (ε' * (x - 1)) * ε := by noncomm_ring
      _ = (y - 1) * ((x - 1) * ε') * ε := by rw [hcommε']
      _ = (y - 1) * (x - 1) * (ε' * ε) := by noncomm_ring
      _ = 0 := by rw [horth', mul_zero]
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hxy, hyx]
  noncomm_ring

private theorem psuC2a_ext_fix {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K) (hε : ε * ε = ε) :
    psuC2a_ext x ε * (1 - ε) = 1 - ε := by
  unfold psuC2a_ext
  exact psuC2a_ring_ext_fix (x : Matrix (Fin n) (Fin n) K) ε hε

private theorem psuC2a_ext_one {n : ℕ} {K : Type} [Field K]
    (ε : Matrix (Fin n) (Fin n) K) :
    psuC2a_ext (1 : GL (Fin n) K) ε = 1 := by
  unfold psuC2a_ext
  rw [Units.val_one, sub_self, zero_mul, zero_add]

private theorem psuC2a_ext_mul {n : ℕ} {K : Type} [Field K]
    (x y : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K) (hε : ε * ε = ε)
    (hyε : (y : Matrix (Fin n) (Fin n) K) * ε = ε * (y : Matrix (Fin n) (Fin n) K)) :
    psuC2a_ext (x * y) ε = psuC2a_ext x ε * psuC2a_ext y ε := by
  unfold psuC2a_ext
  rw [Units.val_mul]
  exact (psuC2a_ring_ext_mul (x : Matrix (Fin n) (Fin n) K)
    (y : Matrix (Fin n) (Fin n) K) ε hε hyε).symm

private theorem psuC2a_ext_comm {n : ℕ} {K : Type} [Field K]
    (x y : GL (Fin n) K) (ε ε' : Matrix (Fin n) (Fin n) K)
    (horth : ε * ε' = 0) (horth' : ε' * ε = 0)
    (hxε' : (x : Matrix (Fin n) (Fin n) K) * ε' = ε' * (x : Matrix (Fin n) (Fin n) K))
    (hyε : (y : Matrix (Fin n) (Fin n) K) * ε = ε * (y : Matrix (Fin n) (Fin n) K)) :
    psuC2a_ext x ε * psuC2a_ext y ε' = psuC2a_ext y ε' * psuC2a_ext x ε := by
  unfold psuC2a_ext
  exact psuC2a_ring_ext_comm (x : Matrix (Fin n) (Fin n) K) (y : Matrix (Fin n) (Fin n) K)
    ε ε' horth horth' hxε' hyε

private theorem psuC2a_inv_comm {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K)
    (hxε : (x : Matrix (Fin n) (Fin n) K) * ε = ε * (x : Matrix (Fin n) (Fin n) K)) :
    ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε =
      ε * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hxx : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]; simp
  have hxx' : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]; simp
  calc ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε
      = ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε *
          (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hxx, mul_one]
    _ = ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((ε * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε) *
            ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [← hxε]
    _ = (((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ε *
            ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
    _ = ε * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hxx', one_mul]

private theorem psuC2a_ext_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K)
    (hε : psuDag h ε = ε)
    (hxinv : psuDag h (x : Matrix (Fin n) (Fin n) K) =
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hxε : (x : Matrix (Fin n) (Fin n) K) * ε = ε * (x : Matrix (Fin n) (Fin n) K)) :
    psuDag h (psuC2a_ext x ε) = psuC2a_ext x⁻¹ ε := by
  have hneg : psuDag h (-(1 : Matrix (Fin n) (Fin n) K)) =
      -(1 : Matrix (Fin n) (Fin n) K) := by
    rw [show -(1 : Matrix (Fin n) (Fin n) K) =
      (-1 : K) • (1 : Matrix (Fin n) (Fin n) K) by rw [neg_one_smul]]
    rw [psuDag_smul, psuDag_one, map_neg, map_one, neg_one_smul]
  have hx' : psuDag h ((x : Matrix (Fin n) (Fin n) K) - 1) =
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 := by
    rw [sub_eq_add_neg, psuDag_add, hneg, hxinv, sub_eq_add_neg]
  have hxinvε : ε * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε :=
    (psuC2a_inv_comm x ε hxε).symm
  unfold psuC2a_ext
  rw [psuDag_add, psuDag_mul, psuDag_one, hx', hε]
  rw [mul_sub, sub_mul, hxinvε, mul_one, one_mul]

private theorem psuC2a_ext_isometry {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K)
    (hε : psuDag h ε = ε) (hidem : ε * ε = ε)
    (hxinv : psuDag h (x : Matrix (Fin n) (Fin n) K) =
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hxε : (x : Matrix (Fin n) (Fin n) K) * ε = ε * (x : Matrix (Fin n) (Fin n) K)) :
    psuDag h (psuC2a_ext x ε) * psuC2a_ext x ε = 1 := by
  rw [psuC2a_ext_dag h x ε hε hxinv hxε, ← psuC2a_ext_mul x⁻¹ x ε hidem hxε]
  rw [inv_mul_cancel, psuC2a_ext_one]

private noncomputable def psuC2a_extGL {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K) (hε : ε * ε = ε)
    (hxε : (x : Matrix (Fin n) (Fin n) K) * ε = ε * (x : Matrix (Fin n) (Fin n) K)) :
    GL (Fin n) K where
  val := psuC2a_ext x ε
  inv := psuC2a_ext x⁻¹ ε
  val_inv := by
    rw [← psuC2a_ext_mul x x⁻¹ ε hε (psuC2a_inv_comm x ε hxε), mul_inv_cancel, psuC2a_ext_one]
  inv_val := by
    rw [← psuC2a_ext_mul x⁻¹ x ε hε hxε, inv_mul_cancel, psuC2a_ext_one]

private theorem psuC2a_extGL_coe {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K) (hε : ε * ε = ε)
    (hxε : (x : Matrix (Fin n) (Fin n) K) * ε = ε * (x : Matrix (Fin n) (Fin n) K)) :
    ((psuC2a_extGL x ε hε hxε : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      psuC2a_ext x ε := rfl

private lemma psuC2a_ring_sum_mul_zero_left {A : Type} [Ring A] (s : Finset A) (b : A)
    (h : ∀ ε ∈ s, ε * b = 0) : (∑ ε ∈ s, ε) * b = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero (fun ε hε => h ε hε)

private lemma psuC2a_ring_sum_mul_zero_right {A : Type} [Ring A] (s : Finset A) (b : A)
    (h : ∀ ε ∈ s, b * ε = 0) : b * (∑ ε ∈ s, ε) = 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun ε hε => h ε hε)

private lemma psuC2a_ring_sum_comm {A : Type} [Ring A] (s : Finset A) (x : A)
    (h : ∀ ε ∈ s, x * ε = ε * x) : x * (∑ ε ∈ s, ε) = (∑ ε ∈ s, ε) * x := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ε hε => h ε hε)

private lemma psuC2a_ring_sum_idem {A : Type} [Ring A] [DecidableEq A] (s : Finset A)
    (hidem : ∀ ε ∈ s, ε * ε = ε)
    (horth : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a * b = 0 ∧ b * a = 0) :
    (∑ ε ∈ s, ε) * (∑ ε ∈ s, ε) = ∑ ε ∈ s, ε := by
  induction s using Finset.induction with
  | empty => simp
  | insert ε s hεs ih =>
      rw [Finset.sum_insert hεs]
      have hidem_s : ∀ ε' ∈ s, ε' * ε' = ε' :=
        fun ε' hε' => hidem ε' (Finset.mem_insert_of_mem hε')
      have horth_s : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a * b = 0 ∧ b * a = 0 :=
        fun a ha b hb hne =>
          horth a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hne
      have ih' := ih hidem_s horth_s
      have hne : ∀ ε' ∈ s, ε' ≠ ε := by
        intro ε' hε' h
        exact hεs (h ▸ hε')
      have hεA : ε * (∑ ε' ∈ s, ε') = 0 :=
        psuC2a_ring_sum_mul_zero_right s ε (fun ε' hε' =>
          (horth ε (Finset.mem_insert_self ε s) ε' (Finset.mem_insert_of_mem hε')
            (fun h => hεs (h ▸ hε'))).1)
      have hAε : (∑ ε' ∈ s, ε') * ε = 0 :=
        psuC2a_ring_sum_mul_zero_left s ε (fun ε' hε' =>
          (horth ε (Finset.mem_insert_self ε s) ε' (Finset.mem_insert_of_mem hε')
            (fun h => hεs (h ▸ hε'))).2)
      rw [add_mul, mul_add, mul_add, hidem ε (Finset.mem_insert_self ε s), hεA, hAε, ih']
      abel

private lemma psuC2a_ring_ext_add {A : Type} [Ring A] (x a b : A)
    (hxa : x * a = a * x) (hab : a * b = 0)
    :
    (x - 1) * (a + b) + 1 = ((x - 1) * a + 1) * ((x - 1) * b + 1) := by
  have hcomm : a * (x - 1) = (x - 1) * a := by
    rw [mul_sub, sub_mul, hxa, mul_one, one_mul]
  have hcross : (x - 1) * a * ((x - 1) * b) = 0 := by
    calc (x - 1) * a * ((x - 1) * b) = (x - 1) * (a * (x - 1)) * b := by noncomm_ring
      _ = (x - 1) * ((x - 1) * a) * b := by rw [hcomm]
      _ = (x - 1) * (x - 1) * (a * b) := by noncomm_ring
      _ = 0 := by rw [hab, mul_zero]
  rw [mul_add, add_mul, mul_add, mul_add, hcross]
  noncomm_ring

private noncomputable def psuC2a_extSum {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (s : Finset (Matrix (Fin n) (Fin n) K)) :
    Matrix (Fin n) (Fin n) K :=
  ((x : Matrix (Fin n) (Fin n) K) - 1) * (∑ ε ∈ s, ε) + 1

private theorem psuC2a_extSum_empty {n : ℕ} {K : Type} [Field K] (x : GL (Fin n) K) :
    psuC2a_extSum x ∅ = 1 := by
  unfold psuC2a_extSum
  simp

private theorem psuC2a_extSum_insert {n : ℕ} {K : Type} [Field K] [DecidableEq K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K)
    (s : Finset (Matrix (Fin n) (Fin n) K)) (hεs : ε ∉ s)
    (hxa : (x : Matrix (Fin n) (Fin n) K) * (∑ ε' ∈ s, ε') =
      (∑ ε' ∈ s, ε') * (x : Matrix (Fin n) (Fin n) K))
    (hAε : (∑ ε' ∈ s, ε') * ε = 0)
    :
    psuC2a_extSum x (insert ε s) = psuC2a_extSum x s * psuC2a_ext x ε := by
  unfold psuC2a_extSum psuC2a_ext
  rw [Finset.sum_insert hεs, add_comm ε (∑ ε' ∈ s, ε')]
  exact psuC2a_ring_ext_add (x : Matrix (Fin n) (Fin n) K)
    (∑ ε' ∈ s, ε') ε hxa hAε

private theorem psuC2a_extSum_Q {n : ℕ} {K : Type} [Field K] (x : GL (Fin n) K)
    (Q : Finset (Matrix (Fin n) (Fin n) K)) (hQ : ∑ ε ∈ Q, ε = 1) :
    psuC2a_extSum x Q = (x : Matrix (Fin n) (Fin n) K) := by
  unfold psuC2a_extSum
  rw [hQ, mul_one, sub_add_cancel]

private def psuC2a_C {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (B : GL (Fin n) K) : Subgroup (AutPSU.XJ h n) :=
  (Subgroup.centralizer ({B} : Set (GL (Fin n) K))).comap (AutPSU.XJ h n).subtype

private theorem psuC2a_C_comm {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (x : psuC2a_C h B) :
    (((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) *
        (((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) := by
  have hx : (((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) ∈
      Subgroup.centralizer ({B} : Set (GL (Fin n) K)) := x.property
  rw [Subgroup.mem_centralizer_iff] at hx
  have hxg := hx B (by rw [Set.mem_singleton_iff])
  simpa only [Units.val_mul] using congrArg (fun u : GL (Fin n) K =>
    (u : Matrix (Fin n) (Fin n) K)) hxg.symm

private theorem psuC2a_C_le_chat {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} :
    psuC2a_C h B ≤ psuChat h B := by
  intro x hx
  rw [psuC2a_C, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hx
  have hx' := hx B (by rw [Set.mem_singleton_iff])
  refine ⟨1, ?_⟩
  have hg := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hx'.symm
  show (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) =
    1 • ((B : Matrix (Fin n) (Fin n) K) *
      (((x : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  rw [one_smul]
  exact hg

private theorem psuC2a_comm_of_centralizer {n : ℕ} {K : Type} [Field K]
    {B : GL (Fin n) K} (x : GL (Fin n) K)
    (hx : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)) :
    ∀ a ∈ psuAlg B, (x : Matrix (Fin n) (Fin n) K) * a = a * (x : Matrix (Fin n) (Fin n) K) := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun y _ => (x : Matrix (Fin n) (Fin n) K) * y =
    y * (x : Matrix (Fin n) (Fin n) K)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hx
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  · intro y z hy hz hpy hpz
    rw [mul_add, add_mul, hpy, hpz]
  · intro y z hy hz hpy hpz
    rw [← Matrix.mul_assoc, hpy, Matrix.mul_assoc, hpz, ← Matrix.mul_assoc]

private lemma psuC2a_J_mul_J (n : ℕ) (K : Type) [Field K] :
    psuJ n K * psuJ n K = (1 : Matrix (Fin n) (Fin n) K) := by
  simpa [psuJ, AutPSU.coe_gramJ] using
    (CFSG.LieType.Universal.Unitary.antidiag_mul_self (F := K) n)

private lemma psuC2a_J_inv (n : ℕ) (K : Type) [Field K] :
    (psuJ n K)⁻¹ = psuJ n K :=
  Matrix.inv_eq_right_inv (psuC2a_J_mul_J n K)

private theorem psuC2a_mem_XJ_iff {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (g : GL (Fin n) K) :
    g ∈ AutPSU.XJ h n ↔ psuDag h (g : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 ∧ (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [AutPSU.XJ, mem_gramSU]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [psuDag, formAdj, psuC2a_J_inv]
    calc psuJ n K * Matrix.transpose ((g : Matrix (Fin n) (Fin n) K).map h.bar) * psuJ n K *
          (g : Matrix (Fin n) (Fin n) K)
        = psuJ n K * (Matrix.transpose ((g : Matrix (Fin n) (Fin n) K).map h.bar) *
            psuJ n K * (g : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
      _ = psuJ n K * psuJ n K := by rw [h1]
      _ = 1 := psuC2a_J_mul_J n K
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h1' : psuJ n K * (Matrix.transpose ((g : Matrix (Fin n) (Fin n) K).map h.bar) *
        psuJ n K * (g : Matrix (Fin n) (Fin n) K)) = 1 := by
      simpa [psuDag, formAdj, psuC2a_J_inv, Matrix.mul_assoc] using h1
    have h2' := congrArg (fun M => psuJ n K * M) h1'
    rw [← Matrix.mul_assoc, psuC2a_J_mul_J n K, Matrix.one_mul, Matrix.mul_one] at h2'
    exact h2'

private theorem psuC2a_dag_eq_inv {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (g : GL (Fin n) K) (h1 : psuDag h (g : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1) :
    psuDag h (g : Matrix (Fin n) (Fin n) K) = ((g⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
  have hgg : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul]; simp
  calc psuDag h (g : Matrix (Fin n) (Fin n) K)
      = psuDag h (g : Matrix (Fin n) (Fin n) K) *
          ((g : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hgg, mul_one]
    _ = (psuDag h (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
    _ = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, one_mul]

private theorem psuC2a_C_comm_K {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} (x : psuC2a_C h B)
    (a : Matrix (Fin n) (Fin n) K) (ha : a ∈ psuAlg B) :
    ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * a =
      a * ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  psuC2a_comm_of_centralizer _ (psuC2a_C_comm x) a ha

private theorem psuC2a_ext_det_ne_zero {n : ℕ} {K : Type} [Field K]
    (x : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K) (hε : ε * ε = ε)
    (hxε : (x : Matrix (Fin n) (Fin n) K) * ε = ε * (x : Matrix (Fin n) (Fin n) K)) :
    (psuC2a_ext x ε).det ≠ 0 := by
  have h1 : IsUnit (psuC2a_ext x ε) := by
    simpa [psuC2a_extGL_coe] using Units.isUnit (psuC2a_extGL x ε hε hxε)
  exact ((Matrix.isUnit_iff_isUnit_det (psuC2a_ext x ε)).mp h1).ne_zero

private lemma psuC2a_ring_ext_comm_B {A : Type} [Ring A]
    (x b ε : A) (hxb : x * b = b * x) (hbε : b * ε = ε * b) :
    b * ((x - 1) * ε + 1) = ((x - 1) * ε + 1) * b := by
  have hb1 : b * (x - 1) = (x - 1) * b := by
    rw [mul_sub, sub_mul, hxb, mul_one, one_mul]
  calc b * ((x - 1) * ε + 1) = b * ((x - 1) * ε) + b * 1 := by rw [mul_add]
    _ = (b * (x - 1)) * ε + b := by noncomm_ring
    _ = ((x - 1) * b) * ε + b := by rw [hb1]
    _ = (x - 1) * (b * ε) + b := by noncomm_ring
    _ = (x - 1) * (ε * b) + b := by rw [hbε]
    _ = ((x - 1) * ε) * b + 1 * b := by noncomm_ring
    _ = ((x - 1) * ε + 1) * b := by rw [add_mul, one_mul]

private noncomputable def psuC2a_rep {f n : ℕ} {K : Type} [Field K] [DecidableEq K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    (ε : ↥(P.image (psuOrbitIdem h))) : Matrix (Fin n) (Fin n) K :=
  Classical.choose (Finset.mem_image.mp ε.property)

private theorem psuC2a_rep_mem {f n : ℕ} {K : Type} [Field K] [DecidableEq K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    (ε : ↥(P.image (psuOrbitIdem h))) : psuC2a_rep P ε ∈ P :=
  (Classical.choose_spec (Finset.mem_image.mp ε.property)).1

private theorem psuC2a_rep_orbit {f n : ℕ} {K : Type} [Field K] [DecidableEq K]
    {h : UnitaryFieldData 2 f K} (P : Finset (Matrix (Fin n) (Fin n) K))
    (ε : ↥(P.image (psuOrbitIdem h))) : psuOrbitIdem h (psuC2a_rep P ε) = ε.1 :=
  (Classical.choose_spec (Finset.mem_image.mp ε.property)).2

private theorem psuC2a_Q_idem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (ε : ↥(P.image (psuOrbitIdem h))) :
    ε.1 * ε.1 = ε.1 := by
  have h := psuC2a_orbit_mem S P hP (psuC2a_rep P ε) (psuC2a_rep_mem P ε)
  rw [← psuC2a_rep_orbit P ε]
  exact h.2.2

private theorem psuC2a_Q_mem_alg {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (ε : ↥(P.image (psuOrbitIdem h))) :
    ε.1 ∈ psuAlg B := by
  have h := psuC2a_orbit_mem S P hP (psuC2a_rep P ε) (psuC2a_rep_mem P ε)
  rw [← psuC2a_rep_orbit P ε]
  exact h.1

private theorem psuC2a_Q_comm {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (x : psuC2a_C h B)
    (ε : ↥(P.image (psuOrbitIdem h))) :
    ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.1 =
      ε.1 * ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) :=
  psuC2a_C_comm_K x ε.1 (psuC2a_Q_mem_alg S P hP ε)

private theorem psuC2a_Q_orth {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) (ε ε' : ↥(P.image (psuOrbitIdem h))) (hne : ε ≠ ε') :
    ε.1 * ε'.1 = 0 ∧ ε'.1 * ε.1 = 0 := by
  have hfne : psuOrbitIdem h (psuC2a_rep P ε) ≠ psuOrbitIdem h (psuC2a_rep P ε') := by
    rw [psuC2a_rep_orbit P ε, psuC2a_rep_orbit P ε']
    intro h
    exact hne (Subtype.ext h)
  have h1 := psuC2a_orbit_orth S P hP (psuC2a_rep P ε) (psuC2a_rep_mem P ε)
    (psuC2a_rep P ε') (psuC2a_rep_mem P ε') hfne
  have h2 := psuC2a_orbit_orth S P hP (psuC2a_rep P ε') (psuC2a_rep_mem P ε')
    (psuC2a_rep P ε) (psuC2a_rep_mem P ε) (fun h => hfne h.symm)
  rw [psuC2a_rep_orbit P ε, psuC2a_rep_orbit P ε'] at h1 h2
  exact ⟨h1, h2⟩

private theorem psuC2a_ext_mem_block {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (x : AutPSU.XJ h n)
    (hxB : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hdet : (psuC2a_ext (x : GL (Fin n) K) (psuOrbitIdem h e)).det = 1) :
    ∃ g ∈ psuBlock h B e,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        psuC2a_ext (x : GL (Fin n) K) (psuOrbitIdem h e) := by
  have hεidem : psuOrbitIdem h e * psuOrbitIdem h e = psuOrbitIdem h e :=
    (psuC2a_orbit_mem S P hP e he).2.2
  have hεdag : psuDag h (psuOrbitIdem h e) = psuOrbitIdem h e :=
    (psuC2a_orbit_mem S P hP e he).2.1
  have hεA : psuOrbitIdem h e ∈ psuAlg B := (psuC2a_orbit_mem S P hP e he).1
  have hxε : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * psuOrbitIdem h e =
      psuOrbitIdem h e * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    psuC2a_comm_of_centralizer (x : GL (Fin n) K) hxB (psuOrbitIdem h e) hεA
  have hxinv : psuDag h ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    psuC2a_dag_eq_inv h (x : GL (Fin n) K)
      ((psuC2a_mem_XJ_iff h (x : GL (Fin n) K)).mp x.property).1
  have hiso := psuC2a_ext_isometry h (x : GL (Fin n) K) (psuOrbitIdem h e)
    hεdag hεidem hxinv hxε
  have hmemXJ : psuC2a_extGL (x : GL (Fin n) K) (psuOrbitIdem h e) hεidem hxε ∈
      AutPSU.XJ h n := by
    refine (psuC2a_mem_XJ_iff h _).mpr ⟨?_, ?_⟩
    · simpa only [psuC2a_extGL_coe] using hiso
    · simpa only [psuC2a_extGL_coe] using hdet
  refine ⟨⟨psuC2a_extGL (x : GL (Fin n) K) (psuOrbitIdem h e) hεidem hxε, hmemXJ⟩, ?_, rfl⟩
  rw [psuBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Units.ext
    change (B : Matrix (Fin n) (Fin n) K) * psuC2a_ext (x : GL (Fin n) K)
        (psuOrbitIdem h e) =
      psuC2a_ext (x : GL (Fin n) K) (psuOrbitIdem h e) * (B : Matrix (Fin n) (Fin n) K)
    have hBmem : (B : Matrix (Fin n) (Fin n) K) ∈ psuAlg B :=
      Algebra.subset_adjoin ⟨B, rfl, rfl⟩
    have hBε : (B : Matrix (Fin n) (Fin n) K) * psuOrbitIdem h e =
        psuOrbitIdem h e * (B : Matrix (Fin n) (Fin n) K) :=
      (psuC2a_comm B (psuOrbitIdem h e) hεA (B : Matrix (Fin n) (Fin n) K) hBmem).symm
    exact psuC2a_ring_ext_comm_B ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (B : Matrix (Fin n) (Fin n) K) (psuOrbitIdem h e) hxB hBε
  · change (((psuC2a_extGL (x : GL (Fin n) K) (psuOrbitIdem h e) hεidem hxε :
      GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) * (1 - psuOrbitIdem h e) =
      1 - psuOrbitIdem h e
    rw [psuC2a_extGL_coe]
    exact psuC2a_ext_fix (x : GL (Fin n) K) (psuOrbitIdem h e) hεidem

private theorem psuC2a_extSum_mem_join {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (x : AutPSU.XJ h n)
    (hxB : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hdet : ∀ ε : ↥(P.image (psuOrbitIdem h)),
      (psuC2a_ext (x : GL (Fin n) K) ε.1).det = 1) :
    x ∈ ⨆ e ∈ P, psuBlock h B e := by
  classical
  set Q := P.image (psuOrbitIdem h) with hQ
  have hxε_all : ∀ e ∈ P, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      psuOrbitIdem h e = psuOrbitIdem h e * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    fun e he => psuC2a_comm_of_centralizer (x : GL (Fin n) K) hxB (psuOrbitIdem h e)
      (psuC2a_orbit_mem S P hP e he).1
  have hpoint : ∀ ε : ↥Q, ∃ g ∈ ⨆ e ∈ P, psuBlock h B e,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = psuC2a_ext (x : GL (Fin n) K) ε.1 := by
    intro ε
    obtain ⟨g, hg, hgmat⟩ := psuC2a_ext_mem_block S P hP (psuC2a_rep P ε)
      (psuC2a_rep_mem P ε) x hxB (by rw [psuC2a_rep_orbit P ε]; exact hdet ε)
    refine ⟨g, ?_, hgmat.trans ?_⟩
    · exact le_iSup (fun e => ⨆ (_ : e ∈ P), psuBlock h B e) (psuC2a_rep P ε)
        (le_iSup (fun _ : psuC2a_rep P ε ∈ P => psuBlock h B (psuC2a_rep P ε))
          (psuC2a_rep_mem P ε) hg)
    · rw [psuC2a_rep_orbit P ε]
  have hind : ∀ s : Finset (Matrix (Fin n) (Fin n) K), s ⊆ Q →
      ∃ g ∈ ⨆ e ∈ P, psuBlock h B e,
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = psuC2a_extSum (x : GL (Fin n) K) s := by
    intro s hs
    induction s using Finset.induction with
    | empty =>
        refine ⟨1, one_mem _, ?_⟩
        rw [psuC2a_extSum_empty]
        rfl
    | insert ε s hεs ih =>
        have hεQ : ε ∈ Q := hs (Finset.mem_insert_self ε s)
        have hsQ : s ⊆ Q := fun a ha => hs (Finset.mem_insert_of_mem ha)
        obtain ⟨gs, hgsJ, hgs⟩ := ih hsQ
        obtain ⟨gε, hgεJ, hgε⟩ := hpoint ⟨ε, hεQ⟩
        refine ⟨gs * gε, mul_mem hgsJ hgεJ, ?_⟩
        rw [Subgroup.coe_mul, Units.val_mul, hgs, hgε]
        have hne : ∀ a (ha : a ∈ s), (⟨ε, hεQ⟩ : ↥Q) ≠ ⟨a, hsQ ha⟩ := by
          intro a ha h
          have hεa : ε = a := Subtype.ext_iff.mp h
          rw [← hεa] at ha
          exact hεs ha
        have hxa : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (∑ ε' ∈ s, ε') =
            (∑ ε' ∈ s, ε') * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
          psuC2a_ring_sum_comm s ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
            (fun a ha => psuC2a_comm_of_centralizer (x : GL (Fin n) K) hxB a
              (psuC2a_Q_mem_alg S P hP ⟨a, hsQ ha⟩))
        have hεA : ε * (∑ ε' ∈ s, ε') = 0 :=
          psuC2a_ring_sum_mul_zero_right s ε (fun a ha =>
            (psuC2a_Q_orth S P hP ⟨ε, hεQ⟩ ⟨a, hsQ ha⟩ (hne a ha)).1)
        have hAε : (∑ ε' ∈ s, ε') * ε = 0 :=
          psuC2a_ring_sum_mul_zero_left s ε (fun a ha =>
            (psuC2a_Q_orth S P hP ⟨ε, hεQ⟩ ⟨a, hsQ ha⟩ (hne a ha)).2)
        have hAA : (∑ ε' ∈ s, ε') * (∑ ε' ∈ s, ε') = ∑ ε' ∈ s, ε' :=
          psuC2a_ring_sum_idem s (fun a ha => psuC2a_Q_idem S P hP ⟨a, hsQ ha⟩)
            (fun a ha b hb hneab => psuC2a_Q_orth S P hP ⟨a, hsQ ha⟩ ⟨b, hsQ hb⟩
              (fun h => hneab (Subtype.ext_iff.mp h)))
        rw [psuC2a_extSum_insert (x : GL (Fin n) K) ε s hεs hxa hAε
          ]
  obtain ⟨g, hgJ, hgx⟩ := hind Q (fun _ ha => ha)
  have hsum : psuC2a_extSum (x : GL (Fin n) K) Q = ((x : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) :=
    psuC2a_extSum_Q (x : GL (Fin n) K) Q (psuC2a_orbit_sum S P hP)
  have hgl : (x : GL (Fin n) K) = (g : GL (Fin n) K) := by
    apply Units.ext
    rw [hgx, hsum]
  have hxg : x = g := Subtype.ext hgl
  exact hxg ▸ hgJ

private theorem psuC2a_eq_ext_of_fix {n : ℕ} {K : Type} [Field K]
    (g : GL (Fin n) K) (ε : Matrix (Fin n) (Fin n) K)
    (h : (g : Matrix (Fin n) (Fin n) K) * (1 - ε) = 1 - ε) :
    (g : Matrix (Fin n) (Fin n) K) = psuC2a_ext g ε := by
  have h1 : (g : Matrix (Fin n) (Fin n) K) - (g : Matrix (Fin n) (Fin n) K) * ε = 1 - ε := by
    have hmul : (g : Matrix (Fin n) (Fin n) K) * (1 - ε) =
        (g : Matrix (Fin n) (Fin n) K) - (g : Matrix (Fin n) (Fin n) K) * ε := by
      rw [mul_sub, mul_one]
    rw [← hmul]
    exact h
  have hg : (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * ε + (1 - ε) := by
    calc (g : Matrix (Fin n) (Fin n) K)
        = ((g : Matrix (Fin n) (Fin n) K) - (g : Matrix (Fin n) (Fin n) K) * ε) +
            (g : Matrix (Fin n) (Fin n) K) * ε := (sub_add_cancel _ _).symm
      _ = (1 - ε) + (g : Matrix (Fin n) (Fin n) K) * ε := by rw [h1]
      _ = (g : Matrix (Fin n) (Fin n) K) * ε + (1 - ε) := by abel
  rw [hg]
  unfold psuC2a_ext
  noncomm_ring

private noncomputable def psuC2a_Phi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) :
    psuC2a_C h B →* (↥(P.image (psuOrbitIdem h)) → Kˣ) where
  toFun := fun x ε => Units.mk0 (psuC2a_ext
      ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K)) ε.1).det
    (psuC2a_ext_det_ne_zero ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K)) ε.1
      (psuC2a_Q_idem S P hP ε) (psuC2a_Q_comm S P hP x ε))
  map_one' := by
    funext ε
    apply Units.ext
    simp only [Pi.one_apply, Units.val_one, Units.val_mk0]
    have hone : ((((1 : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K)) =
        (1 : GL (Fin n) K) := rfl
    rw [hone, psuC2a_ext_one]
    simp
  map_mul' := by
    intro x y
    funext ε
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_one, Units.val_mk0]
    have hmul : ((((x * y : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K)) =
        ((((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K)) *
        ((((y : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
    rw [hmul, psuC2a_ext_mul _ _ ε.1 (psuC2a_Q_idem S P hP ε) (psuC2a_Q_comm S P hP y ε)]
    rw [Matrix.det_mul]

private theorem psuC2a_Phi_ker_le {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P) :
    (psuC2a_Phi S P hP).ker ≤ (⨆ e ∈ P, psuBlock h B e).subgroupOf (psuC2a_C h B) := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_subgroupOf]
  refine psuC2a_extSum_mem_join S P hP ((x : psuC2a_C h B) : AutPSU.XJ h n)
    (psuC2a_C_comm x) ?_
  intro ε
  have hfun := congrFun hx ε
  have h2 := congrArg (fun u : Kˣ => (u : K)) hfun
  change (psuC2a_ext (((x : psuC2a_C h B) : AutPSU.XJ h n) : GL (Fin n) K) ε.1).det = 1 at h2
  exact h2

private theorem psuC2a_blocks_le_C {f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) :
    (⨆ e ∈ P, psuBlock h B e) ≤ psuC2a_C h B := by
  apply iSup_le; intro e
  apply iSup_le; intro he
  intro x hx
  rw [psuC2a_C, Subgroup.mem_comap]
  rw [psuBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  exact hx.1

private theorem psuC2a_blocks_solvable {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P)
    (hsolv : ∀ e ∈ P, Group.IsSolvable ↥(psuBlock h B e)) :
    Group.IsSolvable ↥(⨆ e ∈ P, psuBlock h B e) := by
  classical
  have hjoin : (⨆ e ∈ P, psuBlock h B e) =
      ⨆ ε ∈ P.image (psuOrbitIdem h),
        glBlockCentralizer (AutPSU.XJ h n).subtype ({B} : Set (GL (Fin n) K)) ε := by
    apply le_antisymm
    · apply iSup_le; intro e
      apply iSup_le; intro he
      show glBlockCentralizer (AutPSU.XJ h n).subtype ({B} : Set (GL (Fin n) K))
          (psuOrbitIdem h e) ≤ _
      exact le_trans
        (le_iSup (fun _ : psuOrbitIdem h e ∈ P.image (psuOrbitIdem h) =>
          glBlockCentralizer (AutPSU.XJ h n).subtype ({B} : Set (GL (Fin n) K))
            (psuOrbitIdem h e)) (Finset.mem_image.mpr ⟨e, he, rfl⟩))
        (le_iSup (fun ε => ⨆ (_ : ε ∈ P.image (psuOrbitIdem h)),
          glBlockCentralizer (AutPSU.XJ h n).subtype ({B} : Set (GL (Fin n) K)) ε)
          (psuOrbitIdem h e))
    · apply iSup_le; intro ε
      apply iSup_le; intro hε
      obtain ⟨e, he, hfe⟩ := Finset.mem_image.mp hε
      rw [← hfe]
      exact le_trans (le_iSup (fun _ : e ∈ P => psuBlock h B e) he)
        (le_iSup (fun e => ⨆ (_ : e ∈ P), psuBlock h B e) e)
  rw [hjoin]
  refine psuC2a_commuting_join (P.image (psuOrbitIdem h))
    (fun ε => glBlockCentralizer (AutPSU.XJ h n).subtype ({B} : Set (GL (Fin n) K)) ε) ?_ ?_
  · intro ε hε
    obtain ⟨e, he, hfe⟩ := Finset.mem_image.mp hε
    rw [← hfe]
    exact hsolv e he
  · intro ε hε ε' hε' hne x hx y hy
    simp only [psuBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hx hy
    have hxB : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have h1 := hx.1
      rw [Subgroup.mem_centralizer_iff] at h1
      exact (congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
        (h1 B (by rw [Set.mem_singleton_iff]))).symm
    have hyB : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have h1 := hy.1
      rw [Subgroup.mem_centralizer_iff] at h1
      exact (congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
        (h1 B (by rw [Set.mem_singleton_iff]))).symm
    have hxeq : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        psuC2a_ext (x : GL (Fin n) K) ε := psuC2a_eq_ext_of_fix (x : GL (Fin n) K) ε hx.2
    have hyeq : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        psuC2a_ext (y : GL (Fin n) K) ε' := psuC2a_eq_ext_of_fix (y : GL (Fin n) K) ε' hy.2
    have horth := psuC2a_Q_orth S P hP (⟨ε, hε⟩ : ↥(P.image (psuOrbitIdem h)))
      (⟨ε', hε'⟩ : ↥(P.image (psuOrbitIdem h))) (by
      intro h; exact hne (Subtype.ext_iff.mp h))
    have hxε' : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε' =
        ε' * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      psuC2a_comm_of_centralizer (x : GL (Fin n) K) hxB ε'
        (psuC2a_Q_mem_alg S P hP (⟨ε', hε'⟩ : ↥(P.image (psuOrbitIdem h))))
    have hyε : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε =
        ε * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      psuC2a_comm_of_centralizer (y : GL (Fin n) K) hyB ε
        (psuC2a_Q_mem_alg S P hP (⟨ε, hε⟩ : ↥(P.image (psuOrbitIdem h))))
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hxeq, hyeq]
    exact psuC2a_ext_comm (x : GL (Fin n) K) (y : GL (Fin n) K) ε ε' horth.1 horth.2 hxε' hyε

private theorem psuC2a_centralizer_solvable {f n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] [DecidableEq K] {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K}
    (S : PSUGraphSetting h n X B) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (psuAlg B) P)
    (hsolv : ∀ e ∈ P, Group.IsSolvable ↥(psuBlock h B e)) :
    Group.IsSolvable ↥(psuC2a_C h B) := by
  haveI hJ : Group.IsSolvable ↥(⨆ e ∈ P, psuBlock h B e) :=
    psuC2a_blocks_solvable S P hP hsolv
  haveI hn : NeZero n := ⟨by have := S.four_le; omega⟩
  have hJC : (⨆ e ∈ P, psuBlock h B e) ≤ psuC2a_C h B := psuC2a_blocks_le_C P
  refine solvable_of_ker_le_range (Subgroup.inclusion hJC) (psuC2a_Phi S P hP) ?_
  rw [Subgroup.inclusion_range]
  exact psuC2a_Phi_ker_le S P hP

private theorem psuC2a_lambda_ker_eq {f n : ℕ} {K : Type} [Field K] [NeZero n]
    {h : UnitaryFieldData 2 f K} {B : GL (Fin n) K} :
    (psuC2a_lambda (h := h) (B := B)).ker =
      (psuC2a_C h B).subgroupOf (psuChat h B) := by
  ext x
  rw [MonoidHom.mem_ker, psuC2a_lambda_ker x]
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf, psuC2a_C, Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Units.ext
    exact hx.symm
  · intro hx
    rw [Subgroup.mem_subgroupOf, psuC2a_C, Subgroup.mem_comap] at hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have h := hx B (by rw [Set.mem_singleton_iff])
    exact (congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h).symm

theorem psuGraph_exists_nonsolvable_block {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (hns : ¬ Group.IsSolvable ↥(psuChat h B)) :
    ∃ e ∈ P, ¬ Group.IsSolvable ↥(psuBlock h B e) := by
  classical
  by_contra hall
  push Not at hall
  haveI hn : NeZero n := ⟨by have := S.four_le; omega⟩
  haveI hCsolv : Group.IsSolvable ↥(psuC2a_C h B) :=
    psuC2a_centralizer_solvable S P hP hall
  have hC := psuC2a_C_le_chat (h := h) (B := B)
  have hker : (psuC2a_lambda (h := h) (B := B)).ker ≤ (Subgroup.inclusion hC).range := by
    rw [psuC2a_lambda_ker_eq (h := h) (B := B), Subgroup.inclusion_range]
  exact hns (solvable_of_ker_le_range (Subgroup.inclusion hC) (psuC2a_lambda (h := h) (B := B))
    hker)

end CFSG.StandardType
