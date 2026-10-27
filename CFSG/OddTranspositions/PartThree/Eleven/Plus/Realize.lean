module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Perm
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import Certificates.Certificate1383005

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open Matrix
open CFSG.OddTranspositions.PartThree.PlusRealize

attribute [-instance] CFSG.RankThree.Native.fact_prime_five

@[expose] def fiveReflectionImage (n : ℕ) (ε π : Bool) :
    Set (fiveReflectionGroup n ε π ⧸ Subgroup.center (fiveReflectionGroup n ε π)) :=
  {x | ∃ h : fiveReflectionGroup n ε π,
    (h : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π ∧ x = QuotientGroup.mk h}

private theorem s11p5_sign (π : Bool) : signProp π :=
  sign_of_check π Certificates.certificate1383005

private theorem s11p5_cover (π : Bool) : coverProp π :=
  cover_of_check π Certificates.certificate1383005

private theorem s11p5_validA (π : Bool) (i : Fin 60) : f5ValidA (MA π i) = true :=
  validA_of_check π Certificates.certificate1383005 i

private theorem s11p5_inv (π : Bool) (i : Fin 60) :
    f5EqA (f5MulA (MA π i) (MA π i)) f5IdA = true :=
  inv_of_check π Certificates.certificate1383005 i

private theorem s11p5_table (π : Bool) (i j : Fin 60) :
    f5EqA (f5MulA (f5MulA (MA π i) (MA π j)) (MA π i)) (MA π (TA i j)) = true :=
  table_of_check π Certificates.certificate1383005 i j

private theorem s11p5_distinct (π : Bool) {i j : Fin 60} (hij : i ≠ j) :
    f5EqA (MA π i) (MA π j) = false :=
  distinct_of_check π Certificates.certificate1383005 hij

private lemma s11p5_ff3 (x y : Fin 4 → ZMod 5) :
    fiveForm 3 true x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - x 3 * y 3 := by
  simp [fiveForm, Fin.sum_univ_three]

private lemma s11p5_ff_smul_left (c : ZMod 5) (x y : Fin 4 → ZMod 5) :
    fiveForm 3 true (c • x) y = c * fiveForm 3 true x y := by
  simp only [s11p5_ff3, Pi.smul_apply, smul_eq_mul]; ring

private lemma s11p5_ff_smul_right (c : ZMod 5) (x y : Fin 4 → ZMod 5) :
    fiveForm 3 true x (c • y) = c * fiveForm 3 true x y := by
  simp only [s11p5_ff3, Pi.smul_apply, smul_eq_mul]; ring

private lemma s11p5_ff_smul_smul (c : ZMod 5) (v : Fin 4 → ZMod 5) :
    fiveForm 3 true (c • v) (c • v) = c ^ 2 * fiveForm 3 true v v := by
  rw [s11p5_ff_smul_left, s11p5_ff_smul_right]; ring

private lemma s11p5_fiveForm_single (v : Fin 4 → ZMod 5) (b : Fin 4) :
    fiveForm 3 true (Pi.single b 1) v = Jv v b := by
  fin_cases b <;> simp [Jv, s11p5_ff3] <;> ring

private lemma s11p5_sum_w (v x : Fin 4 → ZMod 5) :
    (∑ b : Fin 4, Jv v b * x b) = fiveForm 3 true x v := by
  rw [s11p5_ff3, Fin.sum_univ_four]
  simp [Jv, s11p5_ff3]
  ring

private lemma s11p5_sum_refl (v x : Fin 4 → ZMod 5) (a : Fin 4) :
    (∑ b : Fin 4, reflMat v a b * x b) =
      x a - 2 * (fiveForm 3 true v v)⁻¹ * v a * fiveForm 3 true x v := by
  have h1 : (∑ b : Fin 4, (if a = b then (1 : ZMod 5) else 0) * x b) = x a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm), zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  have h2 : (∑ b : Fin 4, (2 * (fiveForm 3 true v v)⁻¹ * v a * Jv v b) * x b) =
      2 * (fiveForm 3 true v v)⁻¹ * v a * fiveForm 3 true x v := by
    rw [show (∑ b : Fin 4, (2 * (fiveForm 3 true v v)⁻¹ * v a * Jv v b) * x b) =
        (2 * (fiveForm 3 true v v)⁻¹ * v a) * ∑ b : Fin 4, Jv v b * x b by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _; ring]
    rw [s11p5_sum_w]
  simp only [reflMat, sub_mul, Finset.sum_sub_distrib, h1, h2]

private lemma s11p5_reflMat_mulVec (v x : Fin 4 → ZMod 5) :
    reflMat v *ᵥ x =
      x - (2 * fiveForm 3 true x v * (fiveForm 3 true v v)⁻¹) • v := by
  ext a
  change (∑ b : Fin 4, reflMat v a b * x b) = _
  rw [s11p5_sum_refl]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma s11p5_coeff_refl (c : ZMod 5) (hc : c ≠ 0) (v : Fin 4 → ZMod 5) (a b : Fin 4) :
    2 * (c ^ 2 * fiveForm 3 true v v)⁻¹ * (c * v a) * (c * Jv v b) =
      2 * (fiveForm 3 true v v)⁻¹ * v a * Jv v b := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hq : fiveForm 3 true v v = 0
  · rw [hq]; simp
  · field_simp

private lemma s11p5_Jv_smul (c : ZMod 5) (v : Fin 4 → ZMod 5) : Jv (c • v) = c • Jv v := by
  ext b; fin_cases b <;> simp [Jv, Pi.smul_apply, smul_eq_mul]

private lemma s11p5_reflMat_smul (c : ZMod 5) (hc : c ≠ 0) (v : Fin 4 → ZMod 5) :
    reflMat (c • v) = reflMat v := by
  ext a b
  simp only [reflMat, s11p5_Jv_smul, Pi.smul_apply, smul_eq_mul, s11p5_ff_smul_smul]
  rw [s11p5_coeff_refl c hc v a b]

private theorem s11p5_isUnit (π : Bool) (i : Fin 60) :
    IsUnit (reflMat (vecD π i)) := by
  have h : reflMat (vecD π i) = f5Mat (MA π i) := by
    rw [vecD, MA, ← f5Mat_reflArr]
  rw [h]
  exact isUnit_f5Mat (s11p5_validA π i)

private noncomputable def s11p5_uGL (π : Bool) (i : Fin 60) : GL (Fin 4) (ZMod 5) :=
  (s11p5_isUnit π i).unit

private theorem s11p5_uGL_val (π : Bool) (i : Fin 60) :
    ((s11p5_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      reflMat (decode (vecA π i)) :=
  IsUnit.unit_spec _

private theorem s11p5_uGL_mem (π : Bool) (i : Fin 60) :
    s11p5_uGL π i ∈ fiveReflections 3 true π := by
  have hs : ∀ i : Fin 60, fiveForm 3 true (vecD π i) (vecD π i) ≠ 0 ∧
      (IsSquare (fiveForm 3 true (vecD π i) (vecD π i)) ↔ π = true) := s11p5_sign π
  refine ⟨vecD π i, (hs i).1, (hs i).2, fun x => ?_⟩
  show reflMat (decode (vecA π i)) *ᵥ x = _
  rw [s11p5_reflMat_mulVec]
  rfl

private theorem s11p5_TA_eq_plusRefl (i j : Fin 60) : TA i j = plusRefl i j := by
  apply Fin.ext
  rw [TA, Fin.ofNat_eq_cast, plusRefl_apply]
  exact Nat.mod_eq_of_lt (by
    have h := (plusRefl i j).isLt
    rwa [plusRefl_apply] at h)

private lemma s11p5_matrix_eq_of_action {g : Matrix (Fin 4) (Fin 4) (ZMod 5)}
    {v : Fin 4 → ZMod 5}
    (h : ∀ x, g *ᵥ x =
      x - (2 * fiveForm 3 true x v * (fiveForm 3 true v v)⁻¹) • v) :
    g = reflMat v := by
  ext a b
  have h1 := congrFun (h (Pi.single b 1)) a
  rw [Matrix.mulVec_single] at h1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.op_one, one_smul,
    Matrix.col_apply] at h1
  rw [s11p5_fiveForm_single] at h1
  have h2 : g a b =
      (if a = b then (1 : ZMod 5) else 0) - 2 * Jv v b * (fiveForm 3 true v v)⁻¹ * v a := by
    rw [h1, Pi.single_apply]
  rw [reflMat, h2]
  ring

private theorem s11p5_range_uGL (π : Bool) :
    fiveReflections 3 true π = Set.range (s11p5_uGL π) := by
  ext g
  constructor
  · rintro ⟨v, hv0, hvsq, hact⟩
    obtain ⟨i, c, hc, hcv⟩ := s11p5_cover π v hv0 hvsq
    refine ⟨i, ?_⟩
    apply Units.ext
    have hg : (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = reflMat v :=
      s11p5_matrix_eq_of_action hact
    rw [hg, hcv, s11p5_reflMat_smul c hc]
    exact (s11p5_uGL_val π i).symm
  · rintro ⟨i, rfl⟩
    exact s11p5_uGL_mem π i

private noncomputable def s11p5_R (π : Bool) : Subgroup (GL (Fin 4) (ZMod 5)) :=
  fiveReflectionGroup 3 true π

private noncomputable def s11p5_u (π : Bool) (i : Fin 60) : s11p5_R π :=
  ⟨s11p5_uGL π i, by
    rw [s11p5_R, fiveReflectionGroup, s11p5_range_uGL π]
    exact Subgroup.subset_closure (Set.mem_range_self i)⟩

private theorem s11p5_u_val (π : Bool) (i : Fin 60) :
    ((s11p5_u π i : s11p5_R π) : GL (Fin 4) (ZMod 5)) = s11p5_uGL π i := rfl

private theorem s11p5_u_mul_self (π : Bool) (i : Fin 60) :
    s11p5_u π i * s11p5_u π i = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((s11p5_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *
      ((s11p5_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = 1
  have h := f5Mat_eq_of_eqA (s11p5_inv π i)
  simp only [f5Mat_mulA, f5Mat_idA, MA, f5Mat_reflArr] at h
  simpa only [s11p5_uGL_val] using h

private theorem s11p5_u_inv (π : Bool) (i : Fin 60) :
    (s11p5_u π i)⁻¹ = s11p5_u π i := by
  have h := s11p5_u_mul_self π i
  calc (s11p5_u π i)⁻¹ = (s11p5_u π i)⁻¹ * 1 := by rw [mul_one]
    _ = (s11p5_u π i)⁻¹ * (s11p5_u π i * s11p5_u π i) := by rw [h]
    _ = s11p5_u π i := by group

private theorem s11p5_u_injective (π : Bool) : Function.Injective (s11p5_u π) := by
  intro i j hij
  have h : s11p5_uGL π i = s11p5_uGL π j := by
    have h' := congrArg (fun x : s11p5_R π => (x : GL (Fin 4) (ZMod 5))) hij
    rwa [s11p5_u_val π i, s11p5_u_val π j] at h'
  have hm : reflMat (vecD π i) = reflMat (vecD π j) := by
    show reflMat (decode (vecA π i)) = reflMat (decode (vecA π j))
    rw [← s11p5_uGL_val π i, ← s11p5_uGL_val π j, h]
  have hf : f5Mat (MA π i) = f5Mat (MA π j) := by
    show f5Mat (reflArr (vecA π i)) = f5Mat (reflArr (vecA π j))
    rw [f5Mat_reflArr, f5Mat_reflArr]
    exact hm
  by_contra hne
  have := s11p5_distinct π hne
  exact absurd (f5EqA_of_mat_eq hf) (by rw [this]; exact Bool.false_ne_true)

private theorem s11p5_u_quandle (π : Bool) (i j : Fin 60) :
    s11p5_u π i * s11p5_u π j * s11p5_u π i = s11p5_u π (TA i j) := by
  apply Subtype.ext
  apply Units.ext
  show ((s11p5_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *
      ((s11p5_uGL π j : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *
      ((s11p5_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
    ((s11p5_uGL π (TA i j) : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5))
  have h := f5Mat_eq_of_eqA (s11p5_table π i j)
  simp only [f5Mat_mulA, MA, f5Mat_reflArr] at h
  exact h

private theorem s11p5_uGL_inv (π : Bool) (i : Fin 60) :
    (s11p5_uGL π i)⁻¹ = s11p5_uGL π i := by
  have h := congrArg (fun x : s11p5_R π => (x : GL (Fin 4) (ZMod 5))) (s11p5_u_inv π i)
  simpa only [Subgroup.coe_inv, s11p5_u_val] using h

private theorem s11p5_uGL_quandle (π : Bool) (i j : Fin 60) :
    s11p5_uGL π i * s11p5_uGL π j * (s11p5_uGL π i)⁻¹ = s11p5_uGL π (TA i j) := by
  have h := congrArg (fun x : s11p5_R π => (x : GL (Fin 4) (ZMod 5))) (s11p5_u_quandle π i j)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, s11p5_u_val, s11p5_uGL_inv] using h

private theorem s11p5_conj_mem (π : Bool) (g : s11p5_R π) (j : Fin 60) :
    ∃ k, s11p5_u π k = g * s11p5_u π j * g⁻¹ := by
  let S : Set (GL (Fin 4) (ZMod 5)) := Set.range (s11p5_uGL π)
  have hN : ∀ g ∈ s11p5_R π, ∀ x : GL (Fin 4) (ZMod 5), x ∈ S ↔ g * x * g⁻¹ ∈ S := by
    intro g hg
    rw [s11p5_R, fiveReflectionGroup, s11p5_range_uGL π] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      intro y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨TA i j, (s11p5_uGL_quandle π i j).symm⟩
      · rintro ⟨j, hj⟩
        refine ⟨TA i j, ?_⟩
        have h2 : y = s11p5_uGL π (TA i j) := by
          calc y = (s11p5_uGL π i)⁻¹ *
                (s11p5_uGL π i * y * (s11p5_uGL π i)⁻¹) * s11p5_uGL π i := by group
            _ = (s11p5_uGL π i)⁻¹ * s11p5_uGL π j * s11p5_uGL π i := by rw [← hj]
            _ = s11p5_uGL π i * s11p5_uGL π j * s11p5_uGL π i := by rw [s11p5_uGL_inv]
            _ = s11p5_uGL π (TA i j) := by
              simpa only [s11p5_uGL_inv] using s11p5_uGL_quandle π i j
        exact h2.symm
    | one =>
      intro x
      simp
    | mul a b _ _ iha ihb =>
      intro x
      rw [show (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]
      exact (ihb x).trans (iha (b * x * b⁻¹))
    | inv a _ iha =>
      intro x
      have h := iha (a⁻¹ * x * a)
      rw [show a * (a⁻¹ * x * a) * a⁻¹ = x by group] at h
      exact h.symm
  have hmem := hN g g.2 (s11p5_uGL π j)
  obtain ⟨k, hk⟩ := hmem.mp ⟨j, rfl⟩
  exact ⟨k, Subtype.ext (by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, s11p5_u_val] using hk)⟩

private noncomputable def s11p5_smul (π : Bool) (g : s11p5_R π) (j : Fin 60) : Fin 60 :=
  Classical.choose (s11p5_conj_mem π g j)

private theorem s11p5_smul_spec (π : Bool) (g : s11p5_R π) (j : Fin 60) :
    s11p5_u π (s11p5_smul π g j) = g * s11p5_u π j * g⁻¹ :=
  Classical.choose_spec (s11p5_conj_mem π g j)

private noncomputable instance s11p5_mulAction (π : Bool) : MulAction (s11p5_R π) (Fin 60) where
  smul := s11p5_smul π
  one_smul j := by
    apply s11p5_u_injective π
    change s11p5_u π (s11p5_smul π 1 j) = s11p5_u π j
    rw [s11p5_smul_spec, one_mul, inv_one, mul_one]
  mul_smul g h j := by
    apply s11p5_u_injective π
    change s11p5_u π (s11p5_smul π (g * h) j) =
      s11p5_u π (s11p5_smul π g (s11p5_smul π h j))
    rw [s11p5_smul_spec, s11p5_smul_spec, s11p5_smul_spec]
    group

private noncomputable def s11p5_rho (π : Bool) : s11p5_R π →* Equiv.Perm (Fin 60) :=
  @MulAction.toPermHom (s11p5_R π) (Fin 60) _ (s11p5_mulAction π)

private theorem s11p5_rho_apply (π : Bool) (g : s11p5_R π) (j : Fin 60) :
    s11p5_rho π g j = s11p5_smul π g j := by
  rw [s11p5_rho, MulAction.toPermHom_apply, MulAction.toPerm]
  rfl

private theorem s11p5_rho_u (π : Bool) (i : Fin 60) :
    s11p5_rho π (s11p5_u π i) = plusRefl i := by
  ext j
  rw [s11p5_rho_apply]
  have h := s11p5_smul_spec π (s11p5_u π i) j
  rw [s11p5_u_inv π i] at h
  rw [s11p5_u_quandle] at h
  have h' := s11p5_u_injective π h
  rw [h', s11p5_TA_eq_plusRefl]

private theorem s11p5_closure_top (π : Bool) :
    Subgroup.closure (Set.range (s11p5_u π)) = ⊤ := by
  refine Subgroup.map_injective (f := (s11p5_R π).subtype) Subtype.coe_injective ?_
  rw [MonoidHom.map_closure]
  have himg : (s11p5_R π).subtype '' Set.range (s11p5_u π) = Set.range (s11p5_uGL π) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨s11p5_u π i, ⟨i, rfl⟩, rfl⟩
  rw [himg]
  have htop : (⊤ : Subgroup (s11p5_R π)).map (s11p5_R π).subtype = s11p5_R π := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [htop, s11p5_R, fiveReflectionGroup, s11p5_range_uGL π]

private theorem s11p5_ker_rho (π : Bool) :
    (s11p5_rho π).ker = Subgroup.center (s11p5_R π) := by
  have hker : (s11p5_rho π).ker = Subgroup.centralizer (Set.range (s11p5_u π)) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      obtain ⟨j, rfl⟩ := hx
      have h3 : s11p5_smul π g j = j := by
        have := congrArg (fun σ : Equiv.Perm (Fin 60) => σ j) h
        rwa [s11p5_rho_apply] at this
      have h2 : s11p5_u π j = g * s11p5_u π j * g⁻¹ := by
        have := s11p5_smul_spec π g j
        rwa [h3] at this
      calc s11p5_u π j * g = (g * s11p5_u π j * g⁻¹) * g := by
            conv_lhs => rw [h2]
        _ = g * s11p5_u π j := by group
    · intro h
      apply Equiv.ext
      intro j
      rw [s11p5_rho_apply]
      have h2 : s11p5_u π (s11p5_smul π g j) = s11p5_u π j := by
        rw [s11p5_smul_spec]
        rw [show g * s11p5_u π j * g⁻¹ = s11p5_u π j by
          rw [(h (s11p5_u π j) ⟨j, rfl⟩).symm]
          group]
      exact s11p5_u_injective π h2
  rw [hker, ← Subgroup.centralizer_closure (Set.range (s11p5_u π)), s11p5_closure_top π]
  exact Subgroup.centralizer_univ

private theorem s11p5_range_rho (π : Bool) :
    (s11p5_rho π).range = plusPerm := by
  rw [MonoidHom.range_eq_map, ← s11p5_closure_top π, MonoidHom.map_closure, plusPerm]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (s11p5_rho_u π i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨s11p5_u π i, ⟨i, rfl⟩, s11p5_rho_u π i⟩

theorem exists_plusRealize (π : Bool) :
    ∃ e : (fiveReflectionGroup 3 true π ⧸ Subgroup.center (fiveReflectionGroup 3 true π)) ≃*
      plusPerm, e '' fiveReflectionImage 3 true π = plusClass := by
  let e : (fiveReflectionGroup 3 true π ⧸
        Subgroup.center (fiveReflectionGroup 3 true π)) ≃* plusPerm :=
    (QuotientGroup.quotientMulEquivOfEq
        (show Subgroup.center (s11p5_R π) = (s11p5_rho π).ker from (s11p5_ker_rho π).symm)).trans
      ((QuotientGroup.quotientKerEquivRange (s11p5_rho π)).trans
        (MulEquiv.subgroupCongr (s11p5_range_rho π)))
  have he_mk : ∀ i : Fin 60,
      e (QuotientGroup.mk (s11p5_u π i)) = (⟨plusRefl i, plusRefl_mem i⟩ : plusPerm) := by
    intro i
    show (MulEquiv.subgroupCongr (s11p5_range_rho π))
        ((QuotientGroup.quotientKerEquivRange (s11p5_rho π))
          ((QuotientGroup.quotientMulEquivOfEq
            (show Subgroup.center (s11p5_R π) = (s11p5_rho π).ker
              from (s11p5_ker_rho π).symm)) (QuotientGroup.mk (s11p5_u π i)))) =
      (⟨plusRefl i, plusRefl_mem i⟩ : plusPerm)
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    apply Subtype.ext
    rw [MulEquiv.subgroupCongr_apply]
    exact s11p5_rho_u π i
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hy
    rw [s11p5_range_uGL π] at hh
    obtain ⟨i, hi⟩ := hh
    refine ⟨i, ?_⟩
    have hh' : h = s11p5_u π i := by
      apply Subtype.ext
      rw [← hi, s11p5_u_val]
    rw [hh', he_mk i]
  · rintro ⟨i, hi⟩
    refine ⟨QuotientGroup.mk (s11p5_u π i),
      ⟨s11p5_u π i, by rw [s11p5_range_uGL]; exact ⟨i, rfl⟩, rfl⟩, ?_⟩
    rw [he_mk i]
    exact Subtype.ext hi.symm

end CFSG.OddTranspositions.PartThree
