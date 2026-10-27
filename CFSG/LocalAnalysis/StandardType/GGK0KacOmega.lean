module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveAffineTags
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompTree
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] noncomputable def k0Kac :
    (T : GGKacType) → KacData (absTag T)
  | .E6 => kacE6
  | .E7 => kacE7
  | .E8 => kacE8
  | .F4 => kacF4


private theorem kacE6_extRoot_eq : kacE6.extRoot = fun x : Option (Fin 6) =>
    match x with
    | none => (-![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)
    | some j => Pi.single j 1 := by
  funext x
  cases x <;> rfl

private theorem kacE7_extRoot_eq : kacE7.extRoot = fun x : Option (Fin 7) =>
    match x with
    | none => (-![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ)
    | some j => Pi.single j 1 := by
  funext x
  cases x <;> rfl

private theorem kacE8_extRoot_eq : kacE8.extRoot = fun x : Option (Fin 8) =>
    match x with
    | none => (-![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ)
    | some j => Pi.single j 1 := by
  funext x
  cases x <;> rfl

private theorem kacF4_extRoot_eq : kacF4.extRoot = fun x : Option (Fin 4) =>
    match x with
    | none => (-![2, 3, 4, 2] : Fin 4 → ℤ)
    | some j => Pi.single j 1 := by
  funext x
  cases x <;> rfl

private theorem exists_weyl_omega_E6 (a : List ℕ) (ha : a ∈ k0E6Diag.omega) :
    ∃ v : WeylGroup Tag.E6, ∀ i, i < k0E6Diag.marks.length →
      v • kacE6.extRoot (idxNode i) = kacE6.extRoot (idxNode (a.getD i 0)) := by
  simp only [k0E6Diag, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · have hcheck : ∀ i : Fin 7, kacE6.extRoot (idxNode i.val) =
        kacE6.extRoot (idxNode ((k0pId 7).getD i.val 0)) := by
      rw [kacE6_extRoot_eq]
      decide +kernel
    refine ⟨1, fun i hi => ?_⟩
    rw [one_smul]
    simpa using hcheck ⟨i, hi⟩
  · have hcheck : ∀ i : Fin 7,
        ([0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5] : List ℕ).foldr
          (fun a w => reflect Tag.E6 (Fin.ofNat Tag.E6.rank a) w)
          (kacE6.extRoot (idxNode i.val)) =
        kacE6.extRoot (idxNode (([1, 6, 3, 5, 4, 2, 0]).getD i.val 0)) := by
      rw [kacE6_extRoot_eq]
      decide +kernel
    refine ⟨(([0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5] :
      List ℕ).map fun n => simple Tag.E6 (Fin.ofNat Tag.E6.rank n)).prod, fun i hi => ?_⟩
    rw [prod_map_simple_smul]
    simpa using hcheck ⟨i, hi⟩
  · have hcheck : ∀ i : Fin 7,
        ([5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0] : List ℕ).foldr
          (fun a w => reflect Tag.E6 (Fin.ofNat Tag.E6.rank a) w)
          (kacE6.extRoot (idxNode i.val)) =
        kacE6.extRoot (idxNode ((k0pMul [1, 6, 3, 5, 4, 2, 0]
          [1, 6, 3, 5, 4, 2, 0]).getD i.val 0)) := by
      rw [kacE6_extRoot_eq]
      decide +kernel
    refine ⟨(([5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0] :
      List ℕ).map fun n => simple Tag.E6 (Fin.ofNat Tag.E6.rank n)).prod, fun i hi => ?_⟩
    rw [prod_map_simple_smul]
    simpa using hcheck ⟨i, hi⟩

private theorem exists_weyl_omega_E7 (a : List ℕ) (ha : a ∈ k0E7Diag.omega) :
    ∃ v : WeylGroup Tag.E7, ∀ i, i < k0E7Diag.marks.length →
      v • kacE7.extRoot (idxNode i) = kacE7.extRoot (idxNode (a.getD i 0)) := by
  simp only [k0E7Diag, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl
  · have hcheck : ∀ i : Fin 8, kacE7.extRoot (idxNode i.val) =
        kacE7.extRoot (idxNode ((k0pId 8).getD i.val 0)) := by
      rw [kacE7_extRoot_eq]
      decide +kernel
    refine ⟨1, fun i hi => ?_⟩
    rw [one_smul]
    simpa using hcheck ⟨i, hi⟩
  · have hcheck : ∀ i : Fin 8,
        ([6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5,
          6] : List ℕ).foldr
          (fun a w => reflect Tag.E7 (Fin.ofNat Tag.E7.rank a) w)
          (kacE7.extRoot (idxNode i.val)) =
        kacE7.extRoot (idxNode ([7, 6, 2, 5, 4, 3, 1, 0].getD i.val 0)) := by
      rw [kacE7_extRoot_eq]
      decide +kernel
    refine ⟨(([6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5,
      6] : List ℕ).map fun n => simple Tag.E7 (Fin.ofNat Tag.E7.rank n)).prod, fun i hi => ?_⟩
    rw [prod_map_simple_smul]
    simpa using hcheck ⟨i, hi⟩

private theorem exists_weyl_omega_E8 (a : List ℕ) (ha : a ∈ k0E8Diag.omega) :
    ∃ v : WeylGroup Tag.E8, ∀ i, i < k0E8Diag.marks.length →
      v • kacE8.extRoot (idxNode i) = kacE8.extRoot (idxNode (a.getD i 0)) := by
  simp only [k0E8Diag, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl
  have hcheck : ∀ i : Fin 9, kacE8.extRoot (idxNode i.val) =
      kacE8.extRoot (idxNode ((k0pId 9).getD i.val 0)) := by
    rw [kacE8_extRoot_eq]
    decide +kernel
  refine ⟨1, fun i hi => ?_⟩
  rw [one_smul]
  simpa using hcheck ⟨i, hi⟩

private theorem exists_weyl_omega_F4 (a : List ℕ) (ha : a ∈ k0F4Diag.omega) :
    ∃ v : WeylGroup Tag.F4, ∀ i, i < k0F4Diag.marks.length →
      v • kacF4.extRoot (idxNode i) = kacF4.extRoot (idxNode (a.getD i 0)) := by
  simp only [k0F4Diag, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl
  have hcheck : ∀ i : Fin 5, kacF4.extRoot (idxNode i.val) =
      kacF4.extRoot (idxNode ((k0pId 5).getD i.val 0)) := by
    rw [kacF4_extRoot_eq]
    decide +kernel
  refine ⟨1, fun i hi => ?_⟩
  rw [one_smul]
  simpa using hcheck ⟨i, hi⟩


theorem k0Kac_facts
    (T : GGKacType) : (k0Kac T).Facts := by
  cases T
  · exact facts_E6
  · exact facts_E7
  · exact facts_E8
  · exact facts_F4

theorem k0Kac_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

theorem k0Kac_θ
    (T : GGKacType) (j : Fin (absTag T).rank) :
    (k0Kac T).θ j = ((k0DiagOf T).marks.getD (j.val + 1) 0 : ℤ) := by
  cases T <;> fin_cases j <;> rfl

private theorem extRoot_idxNode_zero {τ : Tag} (K : KacData τ) :
    K.extRoot (idxNode (0 : ℕ)) = -K.θ := by
  simp [idxNode, KacData.extRoot]

private theorem extRoot_idxNode_succ {τ : Tag} (K : KacData τ) (j : Fin τ.rank) :
    K.extRoot (idxNode (j.val + 1)) = Pi.single j 1 := by
  simp [idxNode, KacData.extRoot]

private theorem sum_theta_smul_single {τ : Tag} (θ : Fin τ.rank → ℤ) :
    (∑ j : Fin τ.rank, θ j • (Pi.single j 1 : Fin τ.rank → ℤ)) = θ := by
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

private theorem sum_marks_smul_extRoot {τ : Tag} (K : KacData τ) (m : ℕ → ℤ)
    (hm0 : m 0 = 1) (hmj : ∀ j : Fin τ.rank, m (j.val + 1) = K.θ j) :
    (∑ i : Fin (τ.rank + 1), m i.val • K.extRoot (idxNode i.val)) = 0 := by
  rw [Fin.sum_univ_succ]
  have hk : ∀ j : Fin τ.rank, K.extRoot (idxNode (j.val + 1)) = Pi.single j 1 :=
    fun j => extRoot_idxNode_succ K j
  simp only [Fin.val_zero, hm0, Fin.val_succ, hmj, extRoot_idxNode_zero]
  rw [one_smul, Finset.sum_congr rfl (fun j _ => by rw [hk j]), sum_theta_smul_single]
  exact neg_add_cancel K.θ

private theorem sigma_injective {τ : Tag} (K : KacData τ) {v : WeylGroup τ} {σ : ℕ → ℕ}
    (hα_inj : Function.Injective (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)))
    (h : ∀ i, i < τ.rank + 1 → v • K.extRoot (idxNode i) = K.extRoot (idxNode (σ i))) :
    ∀ i j, i < τ.rank + 1 → j < τ.rank + 1 → σ i = σ j → i = j := by
  intro i j hi hj hij
  have h2 : v • K.extRoot (idxNode i) = v • K.extRoot (idxNode j) := by
    rw [h i hi, h j hj, hij]
  have h3 : (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)) ⟨i, hi⟩ =
      (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)) ⟨j, hj⟩ := by
    simpa using h2
  exact congrArg Fin.val (hα_inj h3)

private theorem exists_perm_sum_marks
    {τ : Tag} (K : KacData τ) (m : ℕ → ℤ)
    (hm0 : m 0 = 1) (hmj : ∀ j : Fin τ.rank, m (j.val + 1) = K.θ j)
    {v : WeylGroup τ} {σ : ℕ → ℕ}
    (hα_inj : Function.Injective (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)))
    (hσ : ∀ i, i < τ.rank + 1 → σ i < τ.rank + 1)
    (h : ∀ i, i < τ.rank + 1 → v • K.extRoot (idxNode i) = K.extRoot (idxNode (σ i))) :
    ∃ e : Equiv.Perm (Fin (τ.rank + 1)),
      (e 0).val = σ 0 ∧
      (∑ x : Fin (τ.rank + 1), m (e.symm x).val • K.extRoot (idxNode x.val)) = 0 := by
  have hinj := sigma_injective K hα_inj h
  let f : Fin (τ.rank + 1) → Fin (τ.rank + 1) := fun i => ⟨σ i.val, hσ i.val i.isLt⟩
  have hf : Function.Injective f := fun i j hij => Fin.ext (hinj i.val j.val i.isLt j.isLt (by
    simpa [f] using congrArg Fin.val hij))
  let e : Equiv.Perm (Fin (τ.rank + 1)) :=
    Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hei : ∀ i, e i = f i := fun i => rfl
  let M : Fin (τ.rank + 1) → ℤ := fun i => m i.val
  let α : Fin (τ.rank + 1) → Fin τ.rank → ℤ := fun i => K.extRoot (idxNode i.val)
  have hrel : ∑ i : Fin (τ.rank + 1), M i • α i = 0 := by
    simpa [M, α] using sum_marks_smul_extRoot K m hm0 hmj
  have hvrel0 : ∑ i : Fin (τ.rank + 1), v • (M i • α i) = 0 := by
    have h0 : v • (∑ i : Fin (τ.rank + 1), M i • α i) = 0 := by
      rw [hrel, smul_zero]
    rw [Finset.smul_sum] at h0
    simpa using h0
  have hvrel : ∑ i : Fin (τ.rank + 1), M i • α (f i) = 0 := by
    calc ∑ i : Fin (τ.rank + 1), M i • α (f i)
        = ∑ i : Fin (τ.rank + 1), M i • (v • α i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show α (f i) = v • α i from by simpa [f, α] using (h i.val i.isLt).symm]
      _ = ∑ i : Fin (τ.rank + 1), v • (M i • α i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact smul_comm (M i) v (α i)
      _ = 0 := hvrel0
  have hrev : ∑ i : Fin (τ.rank + 1), M i • α (e i) = 0 := by
    simpa [hei] using hvrel
  refine ⟨e, by rw [hei 0]; rfl, ?_⟩
  have hdrel : ∑ x : Fin (τ.rank + 1), M (e.symm x) • α x = 0 := by
    rw [← Equiv.sum_comp e (fun x => M (e.symm x) • α x)]
    simpa [Equiv.symm_apply_apply] using hrev
  simpa [M, α] using hdrel

private theorem coord_of_sum_smul_extRoot {τ : Tag} (K : KacData τ)
    {d : Fin (τ.rank + 1) → ℤ}
    (hdrel : (∑ x : Fin (τ.rank + 1), d x • K.extRoot (idxNode x.val)) = 0) :
    ∀ k : Fin τ.rank, d k.succ = d 0 * K.θ k := by
  intro k
  have h1 := congrArg (fun w : Fin τ.rank → ℤ => w k) hdrel
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Fin.sum_univ_succ] at h1
  rw [Finset.sum_eq_single k] at h1
  · simp [extRoot_idxNode_zero, extRoot_idxNode_succ, eq_comm] at h1
    linarith
  · intro b _ hb
    simp [extRoot_idxNode_succ, hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem mark_sigma_d_eq {τ : Tag} (K : KacData τ) (m : ℕ → ℤ)
    (hm0 : m 0 = 1) (hmj : ∀ j : Fin τ.rank, m (j.val + 1) = K.θ j)
    {d : Fin (τ.rank + 1) → ℤ}
    (hcoord : ∀ k : Fin τ.rank, d k.succ = d 0 * K.θ k)
    (hsumd : (∑ x : Fin (τ.rank + 1), d x) = ∑ x : Fin (τ.rank + 1), m x.val) :
    d 0 = 1 ∧ ∀ x, d x = m x.val := by
  have hM : ∑ x : Fin (τ.rank + 1), m x.val = 1 + ∑ k : Fin τ.rank, K.θ k := by
    rw [Fin.sum_univ_succ]
    simp [hm0, hmj]
  have htotal_ne : (∑ x : Fin (τ.rank + 1), m x.val) ≠ 0 := by
    rw [hM]
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => K.θ_nonneg k)
    omega
  have hd0 : d 0 = 1 := by
    have h1 : ∑ x : Fin (τ.rank + 1), d x = d 0 * ∑ x : Fin (τ.rank + 1), m x.val := by
      rw [Fin.sum_univ_succ]
      rw [Finset.sum_congr rfl (fun k _ => hcoord k)]
      rw [← Finset.mul_sum, hM]
      ring
    rw [hsumd] at h1
    have h2 : (d 0 - 1) * (∑ x : Fin (τ.rank + 1), m x.val) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right htotal_ne)
  refine ⟨hd0, fun x => ?_⟩
  rcases Fin.eq_zero_or_eq_succ x with hx | ⟨k, rfl⟩
  · rw [hx, hd0]
    simpa using hm0.symm
  · rw [hcoord k, hd0, one_mul]
    simpa using (hmj k).symm

private theorem mark_sigma_zero {τ : Tag} (K : KacData τ) (m : ℕ → ℤ)
    (hα_inj : Function.Injective (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)))
    (hm0 : m 0 = 1) (hmj : ∀ j : Fin τ.rank, m (j.val + 1) = K.θ j)
    {v : WeylGroup τ} {σ : ℕ → ℕ}
    (hσ : ∀ i, i < τ.rank + 1 → σ i < τ.rank + 1)
    (h : ∀ i, i < τ.rank + 1 → v • K.extRoot (idxNode i) = K.extRoot (idxNode (σ i))) :
    m (σ 0) = 1 := by
  obtain ⟨e, he0, hdrel⟩ := exists_perm_sum_marks K m hm0 hmj hα_inj hσ h
  let d : Fin (τ.rank + 1) → ℤ := fun x => m (e.symm x).val
  have hdrel' : (∑ x : Fin (τ.rank + 1), d x • K.extRoot (idxNode x.val)) = 0 := by
    simpa [d] using hdrel
  have hcoord := coord_of_sum_smul_extRoot K hdrel'
  have hsumd : (∑ x : Fin (τ.rank + 1), d x) = ∑ x : Fin (τ.rank + 1), m x.val := by
    simpa [d] using Equiv.sum_comp e.symm (fun i => m i.val)
  obtain ⟨hd0, hdM⟩ := mark_sigma_d_eq K m hm0 hmj hcoord hsumd
  have h1 : d (e 0) = m (σ 0) := by
    rw [hdM (e 0)]
    simp [he0]
  have h2 : d (e 0) = 1 := by
    simp [d, Equiv.symm_apply_apply, hm0]
  rw [← h1, h2]

private theorem omega_of_weyl_step {τ : Tag} (K : KacData τ)
    {v vb : WeylGroup τ} {σ : ℕ → ℕ} {b bInv : ℕ → ℕ}
    (hα_inj : Function.Injective (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)))
    (hσ : ∀ i, i < τ.rank + 1 → σ i < τ.rank + 1)
    (h : ∀ i, i < τ.rank + 1 → v • K.extRoot (idxNode i) = K.extRoot (idxNode (σ i)))
    (hb_lt : ∀ i, i < τ.rank + 1 → b i < τ.rank + 1)
    (hb : ∀ i, i < τ.rank + 1 → vb • K.extRoot (idxNode i) = K.extRoot (idxNode (b i)))
    (hb0 : b 0 = σ 0)
    (hbinv : ∀ x, x < τ.rank + 1 → bInv x < τ.rank + 1 ∧ b (bInv x) = x) :
    ∀ i, i < τ.rank + 1 → σ i = b i := by
  intro i hi
  have hinj := sigma_injective K hα_inj h
  have hu : ∀ j : Fin τ.rank, 0 ≤ (vb⁻¹ * v) • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    intro j
    have hiN : j.val + 1 < τ.rank + 1 := by omega
    have hσN := hσ (j.val + 1) hiN
    have hklt : bInv (σ (j.val + 1)) < τ.rank + 1 := (hbinv (σ (j.val + 1)) hσN).1
    have hk0 : bInv (σ (j.val + 1)) ≠ 0 := by
      intro h0
      have hb1 := (hbinv (σ (j.val + 1)) hσN).2
      rw [h0] at hb1
      have heq : σ (j.val + 1) = σ 0 := by rw [← hb1, hb0]
      have := hinj (j.val + 1) 0 hiN (by omega) heq
      omega
    have h1 : (vb⁻¹ * v) • (Pi.single j 1) =
        K.extRoot (idxNode (bInv (σ (j.val + 1)))) := by
      rw [← extRoot_idxNode_succ K j, mul_smul, h (j.val + 1) hiN,
        show K.extRoot (idxNode (σ (j.val + 1))) =
          vb • K.extRoot (idxNode (bInv (σ (j.val + 1)))) from by
          rw [hb (bInv (σ (j.val + 1))) hklt, (hbinv (σ (j.val + 1)) hσN).2],
        inv_smul_smul]
    rw [h1]
    have hpos : 0 < bInv (σ (j.val + 1)) := Nat.pos_of_ne_zero hk0
    have hgc : bInv (σ (j.val + 1)) ≤ τ.rank := Nat.lt_succ_iff.mp hklt
    have hbound : bInv (σ (j.val + 1)) - 1 < τ.rank := by omega
    have hk' : bInv (σ (j.val + 1)) =
        (⟨bInv (σ (j.val + 1)) - 1, hbound⟩ : Fin τ.rank).val + 1 := by
      show bInv (σ (j.val + 1)) = (bInv (σ (j.val + 1)) - 1) + 1
      omega
    obtain ⟨k', hk'⟩ : ∃ k' : Fin τ.rank, bInv (σ (j.val + 1)) = k'.val + 1 :=
      ⟨⟨bInv (σ (j.val + 1)) - 1, hbound⟩, hk'⟩
    rw [hk', extRoot_idxNode_succ]
    simp
  have hu1 : vb⁻¹ * v = 1 := eq_one_of_forall_nonneg hu
  have hv_eq : v = vb := by
    calc v = vb * (vb⁻¹ * v) := (mul_inv_cancel_left vb v).symm
      _ = vb * 1 := by rw [hu1]
      _ = vb := mul_one vb
  have hαeq : K.extRoot (idxNode (σ i)) = K.extRoot (idxNode (b i)) := by
    rw [← h i hi, hv_eq, hb i hi]
  exact congrArg Fin.val (hα_inj (a₁ := ⟨σ i, hσ i hi⟩) (a₂ := ⟨b i, hb_lt i hi⟩)
    (by simpa using hαeq))

private theorem omega_of_weyl_of_realized
    {τ : Tag} (K : KacData τ) {v : WeylGroup τ} {σ : ℕ → ℕ} {a aInv : List ℕ}
    (hα_inj : Function.Injective (fun i : Fin (τ.rank + 1) => K.extRoot (idxNode i.val)))
    (hσ : ∀ i, i < τ.rank + 1 → σ i < τ.rank + 1)
    (h : ∀ i, i < τ.rank + 1 → v • K.extRoot (idxNode i) = K.extRoot (idxNode (σ i)))
    (hb : ∃ vb : WeylGroup τ, ∀ i, i < τ.rank + 1 →
      vb • K.extRoot (idxNode i) = K.extRoot (idxNode (a.getD i 0)))
    (hperm : ∀ i : Fin (τ.rank + 1), a.getD i.val 0 < τ.rank + 1)
    (hinv : ∀ x : Fin (τ.rank + 1),
      aInv.getD x.val 0 < τ.rank + 1 ∧ a.getD (aInv.getD x.val 0) 0 = x.val)
    (ha0 : a.getD 0 0 = σ 0) :
    ∀ i, i < τ.rank + 1 → σ i = a.getD i 0 := by
  obtain ⟨vb, hvb⟩ := hb
  refine omega_of_weyl_step (K := K) (v := v) (vb := vb) (σ := σ)
    (b := fun i => a.getD i 0) (bInv := fun i => aInv.getD i 0) hα_inj hσ h ?_ hvb ha0 ?_
  · intro i hi
    exact hperm ⟨i, hi⟩
  · intro x hx
    exact hinv ⟨x, hx⟩

set_option maxRecDepth 10000 in
private theorem omega_of_weyl_E6
    {v : WeylGroup Tag.E6} {σ : ℕ → ℕ}
    (hσ : ∀ i, i < 7 → σ i < 7)
    (h : ∀ i, i < 7 → v • kacE6.extRoot (idxNode i) = kacE6.extRoot (idxNode (σ i))) :
    ∃ a ∈ k0E6Diag.omega, ∀ i, i < 7 → σ i = a.getD i 0 := by
  have hα_inj : Function.Injective (fun i : Fin 7 => kacE6.extRoot (idxNode i.val)) := by
    rw [kacE6_extRoot_eq]
    decide +kernel
  have hm : ((k0E6Diag.marks.getD (σ 0) 0 : ℕ) : ℤ) = 1 := by
    refine mark_sigma_zero (K := kacE6) (m := fun i => ((k0E6Diag.marks.getD i 0 : ℕ) : ℤ))
      (v := v) (σ := σ) hα_inj (by decide) (fun j => (k0Kac_θ .E6 j).symm) ?_ ?_
    · intro i hi
      have h6 : Tag.E6.rank = 6 := rfl
      exact hσ i (by omega)
    · intro i hi
      have h6 : Tag.E6.rank = 6 := rfl
      exact h i (by omega)
  have hlt : σ 0 < 7 := hσ 0 (by decide)
  interval_cases h0 : σ 0
  · refine ⟨k0pId 7, by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacE6) (v := v) (σ := σ)
      (a := k0pId 7) (aInv := k0pId 7) hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_E6 (k0pId 7) (by decide)
      have h6 : Tag.E6.rank = 6 := rfl
      have hd : k0E6Diag.marks.length = 7 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl
  · refine ⟨[1, 6, 3, 5, 4, 2, 0], by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacE6) (v := v) (σ := σ)
      (a := [1, 6, 3, 5, 4, 2, 0]) (aInv := k0pInv [1, 6, 3, 5, 4, 2, 0])
      hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_E6 [1, 6, 3, 5, 4, 2, 0] (by decide)
      have h6 : Tag.E6.rank = 6 := rfl
      have hd : k0E6Diag.marks.length = 7 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl
  · norm_num [k0E6Diag] at hm
  · norm_num [k0E6Diag] at hm
  · norm_num [k0E6Diag] at hm
  · norm_num [k0E6Diag] at hm
  · refine ⟨k0pMul [1, 6, 3, 5, 4, 2, 0] [1, 6, 3, 5, 4, 2, 0], by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacE6) (v := v) (σ := σ)
      (a := k0pMul [1, 6, 3, 5, 4, 2, 0] [1, 6, 3, 5, 4, 2, 0])
      (aInv := k0pInv (k0pMul [1, 6, 3, 5, 4, 2, 0] [1, 6, 3, 5, 4, 2, 0]))
      hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_E6
        (k0pMul [1, 6, 3, 5, 4, 2, 0] [1, 6, 3, 5, 4, 2, 0]) (by decide)
      have h6 : Tag.E6.rank = 6 := rfl
      have hd : k0E6Diag.marks.length = 7 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl

set_option maxRecDepth 10000 in
private theorem omega_of_weyl_E7
    {v : WeylGroup Tag.E7} {σ : ℕ → ℕ}
    (hσ : ∀ i, i < 8 → σ i < 8)
    (h : ∀ i, i < 8 → v • kacE7.extRoot (idxNode i) = kacE7.extRoot (idxNode (σ i))) :
    ∃ a ∈ k0E7Diag.omega, ∀ i, i < 8 → σ i = a.getD i 0 := by
  have hα_inj : Function.Injective (fun i : Fin 8 => kacE7.extRoot (idxNode i.val)) := by
    rw [kacE7_extRoot_eq]
    decide +kernel
  have hm : ((k0E7Diag.marks.getD (σ 0) 0 : ℕ) : ℤ) = 1 := by
    refine mark_sigma_zero (K := kacE7) (m := fun i => ((k0E7Diag.marks.getD i 0 : ℕ) : ℤ))
      (v := v) (σ := σ) hα_inj (by decide) (fun j => (k0Kac_θ .E7 j).symm) ?_ ?_
    · intro i hi
      have h7 : Tag.E7.rank = 7 := rfl
      exact hσ i (by omega)
    · intro i hi
      have h7 : Tag.E7.rank = 7 := rfl
      exact h i (by omega)
  have hlt : σ 0 < 8 := hσ 0 (by decide)
  interval_cases h0 : σ 0
  · refine ⟨k0pId 8, by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacE7) (v := v) (σ := σ)
      (a := k0pId 8) (aInv := k0pId 8) hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_E7 (k0pId 8) (by decide)
      have h7 : Tag.E7.rank = 7 := rfl
      have hd : k0E7Diag.marks.length = 8 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl
  · norm_num [k0E7Diag] at hm
  · norm_num [k0E7Diag] at hm
  · norm_num [k0E7Diag] at hm
  · norm_num [k0E7Diag] at hm
  · norm_num [k0E7Diag] at hm
  · norm_num [k0E7Diag] at hm
  · refine ⟨[7, 6, 2, 5, 4, 3, 1, 0], by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacE7) (v := v) (σ := σ)
      (a := [7, 6, 2, 5, 4, 3, 1, 0]) (aInv := k0pInv [7, 6, 2, 5, 4, 3, 1, 0])
      hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_E7 [7, 6, 2, 5, 4, 3, 1, 0] (by decide)
      have h7 : Tag.E7.rank = 7 := rfl
      have hd : k0E7Diag.marks.length = 8 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl

set_option maxRecDepth 10000 in
private theorem omega_of_weyl_E8
    {v : WeylGroup Tag.E8} {σ : ℕ → ℕ}
    (hσ : ∀ i, i < 9 → σ i < 9)
    (h : ∀ i, i < 9 → v • kacE8.extRoot (idxNode i) = kacE8.extRoot (idxNode (σ i))) :
    ∃ a ∈ k0E8Diag.omega, ∀ i, i < 9 → σ i = a.getD i 0 := by
  have hα_inj : Function.Injective (fun i : Fin 9 => kacE8.extRoot (idxNode i.val)) := by
    rw [kacE8_extRoot_eq]
    decide +kernel
  have hm : ((k0E8Diag.marks.getD (σ 0) 0 : ℕ) : ℤ) = 1 := by
    refine mark_sigma_zero (K := kacE8) (m := fun i => ((k0E8Diag.marks.getD i 0 : ℕ) : ℤ))
      (v := v) (σ := σ) hα_inj (by decide) (fun j => (k0Kac_θ .E8 j).symm) ?_ ?_
    · intro i hi
      have h8 : Tag.E8.rank = 8 := rfl
      exact hσ i (by omega)
    · intro i hi
      have h8 : Tag.E8.rank = 8 := rfl
      exact h i (by omega)
  have hlt : σ 0 < 9 := hσ 0 (by decide)
  interval_cases h0 : σ 0
  · refine ⟨k0pId 9, by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacE8) (v := v) (σ := σ)
      (a := k0pId 9) (aInv := k0pId 9) hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_E8 (k0pId 9) (by decide)
      have h8 : Tag.E8.rank = 8 := rfl
      have hd : k0E8Diag.marks.length = 9 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm
  · norm_num [k0E8Diag] at hm

set_option maxRecDepth 10000 in
private theorem omega_of_weyl_F4
    {v : WeylGroup Tag.F4} {σ : ℕ → ℕ}
    (hσ : ∀ i, i < 5 → σ i < 5)
    (h : ∀ i, i < 5 → v • kacF4.extRoot (idxNode i) = kacF4.extRoot (idxNode (σ i))) :
    ∃ a ∈ k0F4Diag.omega, ∀ i, i < 5 → σ i = a.getD i 0 := by
  have hα_inj : Function.Injective (fun i : Fin 5 => kacF4.extRoot (idxNode i.val)) := by
    rw [kacF4_extRoot_eq]
    decide +kernel
  have hm : ((k0F4Diag.marks.getD (σ 0) 0 : ℕ) : ℤ) = 1 := by
    refine mark_sigma_zero (K := kacF4) (m := fun i => ((k0F4Diag.marks.getD i 0 : ℕ) : ℤ))
      (v := v) (σ := σ) hα_inj (by decide) (fun j => (k0Kac_θ .F4 j).symm) ?_ ?_
    · intro i hi
      have h4 : Tag.F4.rank = 4 := rfl
      exact hσ i (by omega)
    · intro i hi
      have h4 : Tag.F4.rank = 4 := rfl
      exact h i (by omega)
  have hlt : σ 0 < 5 := hσ 0 (by decide)
  interval_cases h0 : σ 0
  · refine ⟨k0pId 5, by decide, ?_⟩
    refine omega_of_weyl_of_realized (K := kacF4) (v := v) (σ := σ)
      (a := k0pId 5) (aInv := k0pId 5) hα_inj ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact hσ i hi
    · intro i hi; exact h i hi
    · obtain ⟨vb, hvb⟩ := exists_weyl_omega_F4 (k0pId 5) (by decide)
      have h4 : Tag.F4.rank = 4 := rfl
      have hd : k0F4Diag.marks.length = 5 := rfl
      exact ⟨vb, fun i hi => hvb i (by omega)⟩
    · decide +kernel
    · decide +kernel
    · rw [h0]; rfl
  · norm_num [k0F4Diag] at hm
  · norm_num [k0F4Diag] at hm
  · norm_num [k0F4Diag] at hm
  · norm_num [k0F4Diag] at hm

private theorem exists_weyl_tau0_E6 :
    ∃ v : WeylGroup Tag.E6, ∀ i, i < k0E6Diag.marks.length →
      v • kacE6.extRoot (idxNode i) =
        -(kacE6.extRoot (idxNode (k0E6Diag.tau0.getD i 0))) := by
  have hfold : ∀ v : Fin Tag.E6.rank → ℤ,
      excLongestElementE6 • v =
      excLongestWordE6.foldr (fun n w => reflect Tag.E6 (excNodeE6 n) w) v := by
    intro v
    rw [excLongestElementE6, prod_map_simple_smul]
  have hcheck : ∀ i : Fin 7,
      excLongestElementE6 • kacE6.extRoot (idxNode i.val) =
      -(kacE6.extRoot (idxNode (k0E6Diag.tau0.getD i.val 0))) := by
    simp_rw [kacE6_extRoot_eq, hfold]
    decide +kernel
  exact ⟨excLongestElementE6, fun i hi => hcheck ⟨i, hi⟩⟩

private theorem exists_weyl_tau0_E7 :
    ∃ v : WeylGroup Tag.E7, ∀ i, i < k0E7Diag.marks.length →
      v • kacE7.extRoot (idxNode i) =
        -(kacE7.extRoot (idxNode (k0E7Diag.tau0.getD i 0))) := by
  have hfold : ∀ v : Fin Tag.E7.rank → ℤ,
      (CFSG.LieType.SeitzGeneration.e7TwoWord.map fun j => simple Tag.E7 j).prod • v =
      CFSG.LieType.SeitzGeneration.e7TwoWord.foldr (fun j w => reflect Tag.E7 j w) v := by
    intro v
    simpa using prod_map_simple_smul Tag.E7 (fun j => j) CFSG.LieType.SeitzGeneration.e7TwoWord v
  have hcheck : ∀ i : Fin 8,
      (CFSG.LieType.SeitzGeneration.e7TwoWord.map fun j => simple Tag.E7 j).prod •
        kacE7.extRoot (idxNode i.val) =
      -(kacE7.extRoot (idxNode (k0E7Diag.tau0.getD i.val 0))) := by
    simp_rw [kacE7_extRoot_eq, hfold]
    decide +kernel
  exact ⟨_, fun i hi => hcheck ⟨i, hi⟩⟩

private theorem exists_weyl_tau0_E8 :
    ∃ v : WeylGroup Tag.E8, ∀ i, i < k0E8Diag.marks.length →
      v • kacE8.extRoot (idxNode i) =
        -(kacE8.extRoot (idxNode (k0E8Diag.tau0.getD i 0))) := by
  have hfold : ∀ v : Fin Tag.E8.rank → ℤ,
      (CFSG.LieType.SeitzGeneration.e8TwoWord.map fun j => simple Tag.E8 j).prod • v =
      CFSG.LieType.SeitzGeneration.e8TwoWord.foldr (fun j w => reflect Tag.E8 j w) v := by
    intro v
    simpa using prod_map_simple_smul Tag.E8 (fun j => j) CFSG.LieType.SeitzGeneration.e8TwoWord v
  have hcheck : ∀ i : Fin 9,
      (CFSG.LieType.SeitzGeneration.e8TwoWord.map fun j => simple Tag.E8 j).prod •
        kacE8.extRoot (idxNode i.val) =
      -(kacE8.extRoot (idxNode (k0E8Diag.tau0.getD i.val 0))) := by
    simp_rw [kacE8_extRoot_eq, hfold]
    decide +kernel
  exact ⟨_, fun i hi => hcheck ⟨i, hi⟩⟩

private theorem exists_weyl_tau0_F4 :
    ∃ v : WeylGroup Tag.F4, ∀ i, i < k0F4Diag.marks.length →
      v • kacF4.extRoot (idxNode i) =
        -(kacF4.extRoot (idxNode (k0F4Diag.tau0.getD i 0))) := by
  have hfold : ∀ v : Fin Tag.F4.rank → ℤ,
      (CFSG.LieType.SeitzGeneration.f4TwoWord.map fun j => simple Tag.F4 j).prod • v =
      CFSG.LieType.SeitzGeneration.f4TwoWord.foldr (fun j w => reflect Tag.F4 j w) v := by
    intro v
    simpa using prod_map_simple_smul Tag.F4 (fun j => j) CFSG.LieType.SeitzGeneration.f4TwoWord v
  have hcheck : ∀ i : Fin 5,
      (CFSG.LieType.SeitzGeneration.f4TwoWord.map fun j => simple Tag.F4 j).prod •
        kacF4.extRoot (idxNode i.val) =
      -(kacF4.extRoot (idxNode (k0F4Diag.tau0.getD i.val 0))) := by
    simp_rw [kacF4_extRoot_eq, hfold]
    decide +kernel
  exact ⟨_, fun i hi => hcheck ⟨i, hi⟩⟩

theorem k0Kac_hup
    (T : GGKacType) : ∀ γ : Fin (absTag T).rank → ℤ, IsRoot (absTag T) γ →
    (∀ j, 0 ≤ γ j) → γ ≠ (k0Kac T).θ → ∃ j, IsRoot (absTag T) (γ + Pi.single j 1) := by
  cases T
  · exact exists_isRoot_add_single_E6
  · exact exists_isRoot_add_single_E7
  · exact exists_isRoot_add_single_E8
  · exact exists_isRoot_add_single_F4

theorem k0Kac_hdown
    (T : GGKacType) : ∀ γ : Fin (absTag T).rank → ℤ, IsRoot (absTag T) γ →
    (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
    ∃ j, IsRoot (absTag T) (γ - Pi.single j 1) ∧
      ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin (absTag T).rank → ℤ) k := by
  cases T
  · exact exists_isRoot_sub_single_E6
  · exact exists_isRoot_sub_single_E7
  · exact exists_isRoot_sub_single_E8
  · exact exists_isRoot_sub_single_F4

theorem exists_weyl_omega
    (T : GGKacType) {a : List ℕ} (ha : a ∈ (k0DiagOf T).omega) :
    ∃ v : WeylGroup (absTag T), ∀ i, i < (k0DiagOf T).marks.length →
      v • (k0Kac T).extRoot (idxNode i) = (k0Kac T).extRoot (idxNode (a.getD i 0)) := by
  cases T
  · exact exists_weyl_omega_E6 a ha
  · exact exists_weyl_omega_E7 a ha
  · exact exists_weyl_omega_E8 a ha
  · exact exists_weyl_omega_F4 a ha

theorem exists_weyl_tau0
    (T : GGKacType) :
    ∃ v : WeylGroup (absTag T), ∀ i, i < (k0DiagOf T).marks.length →
      v • (k0Kac T).extRoot (idxNode i) =
        -(k0Kac T).extRoot (idxNode ((k0DiagOf T).tau0.getD i 0)) := by
  cases T
  · exact exists_weyl_tau0_E6
  · exact exists_weyl_tau0_E7
  · exact exists_weyl_tau0_E8
  · exact exists_weyl_tau0_F4

theorem exists_omega_of_weyl
    (T : GGKacType) {v : WeylGroup (absTag T)} {σ : ℕ → ℕ}
    (hσ : ∀ i, i < (k0DiagOf T).marks.length → σ i < (k0DiagOf T).marks.length)
    (h : ∀ i, i < (k0DiagOf T).marks.length →
      v • (k0Kac T).extRoot (idxNode i) = (k0Kac T).extRoot (idxNode (σ i))) :
    ∃ a ∈ (k0DiagOf T).omega, ∀ i, i < (k0DiagOf T).marks.length → σ i = a.getD i 0 := by
  cases T
  · refine omega_of_weyl_E6 (v := v) (σ := σ) ?_ ?_
    · intro i hi
      exact hσ i (show i < (k0DiagOf GGKacType.E6).marks.length from hi)
    · intro i hi
      exact h i (show i < (k0DiagOf GGKacType.E6).marks.length from hi)
  · refine omega_of_weyl_E7 (v := v) (σ := σ) ?_ ?_
    · intro i hi
      exact hσ i (show i < (k0DiagOf GGKacType.E7).marks.length from hi)
    · intro i hi
      exact h i (show i < (k0DiagOf GGKacType.E7).marks.length from hi)
  · refine omega_of_weyl_E8 (v := v) (σ := σ) ?_ ?_
    · intro i hi
      exact hσ i (show i < (k0DiagOf GGKacType.E8).marks.length from hi)
    · intro i hi
      exact h i (show i < (k0DiagOf GGKacType.E8).marks.length from hi)
  · refine omega_of_weyl_F4 (v := v) (σ := σ) ?_ ?_
    · intro i hi
      exact hσ i (show i < (k0DiagOf GGKacType.F4).marks.length from hi)
    · intro i hi
      exact h i (show i < (k0DiagOf GGKacType.F4).marks.length from hi)

end CFSG.StandardType.GGK0MarkedKacIface1587

end
