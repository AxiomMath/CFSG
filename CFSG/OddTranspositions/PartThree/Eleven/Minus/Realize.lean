module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Perm
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import Certificates.Certificate1383007
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.Realize

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open Matrix
open CFSG.OddTranspositions.PartThree.MinusRealize

attribute [-instance] CFSG.RankThree.Native.fact_prime_five

private theorem minus_sign (π : Bool) : signProp π :=
  sign_of_check π Certificates.certificate1383007

private theorem minus_cover (π : Bool) : coverProp π :=
  cover_of_check π Certificates.certificate1383007

private theorem minus_validA (π : Bool) (i : Fin 65) : f5ValidA (MA π i) = true :=
  validA_of_check π Certificates.certificate1383007 i

private theorem minus_inv (π : Bool) (i : Fin 65) :
    f5EqA (f5MulA (MA π i) (MA π i)) f5IdA = true :=
  inv_of_check π Certificates.certificate1383007 i

private theorem minus_table (π : Bool) (i j : Fin 65) :
    f5EqA (f5MulA (f5MulA (MA π i) (MA π j)) (MA π i)) (MA π (TA i j)) = true :=
  table_of_check π Certificates.certificate1383007 i j

private theorem minus_distinct (π : Bool) {i j : Fin 65} (hij : i ≠ j) :
    f5EqA (MA π i) (MA π j) = false :=
  distinct_of_check π Certificates.certificate1383007 hij

private lemma minus_ff3 (x y : Fin 4 → ZMod 5) :
    fiveForm 3 false x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - 2 * (x 3 * y 3) := by
  simp [fiveForm, Fin.sum_univ_three]

private lemma minus_ff_smul_left (c : ZMod 5) (x y : Fin 4 → ZMod 5) :
    fiveForm 3 false (c • x) y = c * fiveForm 3 false x y := by
  simp only [minus_ff3, Pi.smul_apply, smul_eq_mul]; ring

private lemma minus_ff_smul_right (c : ZMod 5) (x y : Fin 4 → ZMod 5) :
    fiveForm 3 false x (c • y) = c * fiveForm 3 false x y := by
  simp only [minus_ff3, Pi.smul_apply, smul_eq_mul]; ring

private lemma minus_ff_smul_smul (c : ZMod 5) (v : Fin 4 → ZMod 5) :
    fiveForm 3 false (c • v) (c • v) = c ^ 2 * fiveForm 3 false v v := by
  rw [minus_ff_smul_left, minus_ff_smul_right]; ring

private lemma minus_fiveForm_single (v : Fin 4 → ZMod 5) (b : Fin 4) :
    fiveForm 3 false (Pi.single b 1) v = Jv v b := by
  fin_cases b <;> simp [Jv, minus_ff3] <;> ring

private lemma minus_sum_w (v x : Fin 4 → ZMod 5) :
    (∑ b : Fin 4, Jv v b * x b) = fiveForm 3 false x v := by
  rw [minus_ff3, Fin.sum_univ_four]
  simp [Jv, minus_ff3]
  ring

private lemma minus_sum_refl (v x : Fin 4 → ZMod 5) (a : Fin 4) :
    (∑ b : Fin 4, reflMat v a b * x b) =
      x a - 2 * (fiveForm 3 false v v)⁻¹ * v a * fiveForm 3 false x v := by
  have h1 : (∑ b : Fin 4, (if a = b then (1 : ZMod 5) else 0) * x b) = x a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm), zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  have h2 : (∑ b : Fin 4, (2 * (fiveForm 3 false v v)⁻¹ * v a * Jv v b) * x b) =
      2 * (fiveForm 3 false v v)⁻¹ * v a * fiveForm 3 false x v := by
    rw [show (∑ b : Fin 4, (2 * (fiveForm 3 false v v)⁻¹ * v a * Jv v b) * x b) =
        (2 * (fiveForm 3 false v v)⁻¹ * v a) * ∑ b : Fin 4, Jv v b * x b by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _; ring]
    rw [minus_sum_w]
  simp only [reflMat, sub_mul, Finset.sum_sub_distrib, h1, h2]

private lemma minus_reflMat_mulVec (v x : Fin 4 → ZMod 5) :
    reflMat v *ᵥ x =
      x - (2 * fiveForm 3 false x v * (fiveForm 3 false v v)⁻¹) • v := by
  ext a
  change (∑ b : Fin 4, reflMat v a b * x b) = _
  rw [minus_sum_refl]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma minus_coeff_refl (c : ZMod 5) (hc : c ≠ 0) (v : Fin 4 → ZMod 5) (a b : Fin 4) :
    2 * (c ^ 2 * fiveForm 3 false v v)⁻¹ * (c * v a) * (c * Jv v b) =
      2 * (fiveForm 3 false v v)⁻¹ * v a * Jv v b := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hq : fiveForm 3 false v v = 0
  · rw [hq]; simp
  · field_simp

private lemma minus_Jv_smul (c : ZMod 5) (v : Fin 4 → ZMod 5) : Jv (c • v) = c • Jv v := by
  ext b; fin_cases b <;> simp [Jv, Pi.smul_apply, smul_eq_mul] <;> ring

private lemma minus_reflMat_smul (c : ZMod 5) (hc : c ≠ 0) (v : Fin 4 → ZMod 5) :
    reflMat (c • v) = reflMat v := by
  ext a b
  simp only [reflMat, minus_Jv_smul, Pi.smul_apply, smul_eq_mul, minus_ff_smul_smul]
  rw [minus_coeff_refl c hc v a b]

private theorem minus_isUnit (π : Bool) (i : Fin 65) :
    IsUnit (reflMat (vecD π i)) := by
  have h : reflMat (vecD π i) = f5Mat (MA π i) := by
    rw [vecD, MA, ← f5Mat_reflArr]
  rw [h]
  exact isUnit_f5Mat (minus_validA π i)

private noncomputable def minus_uGL (π : Bool) (i : Fin 65) : GL (Fin 4) (ZMod 5) :=
  (minus_isUnit π i).unit

private theorem minus_uGL_val (π : Bool) (i : Fin 65) :
    ((minus_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      reflMat (decode (vecA π i)) :=
  IsUnit.unit_spec _

private theorem minus_uGL_mem (π : Bool) (i : Fin 65) :
    minus_uGL π i ∈ fiveReflections 3 false π := by
  have hs : ∀ i : Fin 65, fiveForm 3 false (vecD π i) (vecD π i) ≠ 0 ∧
      (IsSquare (fiveForm 3 false (vecD π i) (vecD π i)) ↔ π = true) := minus_sign π
  refine ⟨vecD π i, (hs i).1, (hs i).2, fun x => ?_⟩
  show reflMat (decode (vecA π i)) *ᵥ x = _
  rw [minus_reflMat_mulVec]
  rfl

private theorem minus_TA_eq_minusRefl (i j : Fin 65) : TA i j = minusRefl i j := by
  apply Fin.ext
  rw [TA, Fin.ofNat_eq_cast, minusRefl_apply]
  exact Nat.mod_eq_of_lt (by
    have h := (minusRefl i j).isLt
    rwa [minusRefl_apply] at h)

private lemma minus_matrix_eq_of_action {g : Matrix (Fin 4) (Fin 4) (ZMod 5)}
    {v : Fin 4 → ZMod 5}
    (h : ∀ x, g *ᵥ x =
      x - (2 * fiveForm 3 false x v * (fiveForm 3 false v v)⁻¹) • v) :
    g = reflMat v := by
  ext a b
  have h1 := congrFun (h (Pi.single b 1)) a
  rw [Matrix.mulVec_single] at h1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.op_one, one_smul,
    Matrix.col_apply] at h1
  rw [minus_fiveForm_single] at h1
  have h2 : g a b =
      (if a = b then (1 : ZMod 5) else 0) - 2 * Jv v b * (fiveForm 3 false v v)⁻¹ * v a := by
    rw [h1, Pi.single_apply]
  rw [reflMat, h2]
  ring

private theorem minus_range_uGL (π : Bool) :
    fiveReflections 3 false π = Set.range (minus_uGL π) := by
  ext g
  constructor
  · rintro ⟨v, hv0, hvsq, hact⟩
    obtain ⟨i, c, hc, hcv⟩ := minus_cover π v hv0 hvsq
    refine ⟨i, ?_⟩
    apply Units.ext
    have hg : (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = reflMat v :=
      minus_matrix_eq_of_action hact
    rw [hg, hcv, minus_reflMat_smul c hc]
    exact (minus_uGL_val π i).symm
  · rintro ⟨i, rfl⟩
    exact minus_uGL_mem π i

private noncomputable def minus_R (π : Bool) : Subgroup (GL (Fin 4) (ZMod 5)) :=
  fiveReflectionGroup 3 false π

private noncomputable def minus_u (π : Bool) (i : Fin 65) : minus_R π :=
  ⟨minus_uGL π i, by
    rw [minus_R, fiveReflectionGroup, minus_range_uGL π]
    exact Subgroup.subset_closure (Set.mem_range_self i)⟩

private theorem minus_u_val (π : Bool) (i : Fin 65) :
    ((minus_u π i : minus_R π) : GL (Fin 4) (ZMod 5)) = minus_uGL π i := rfl

private theorem minus_u_mul_self (π : Bool) (i : Fin 65) :
    minus_u π i * minus_u π i = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((minus_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *
      ((minus_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = 1
  have h := f5Mat_eq_of_eqA (minus_inv π i)
  simp only [f5Mat_mulA, f5Mat_idA, MA, f5Mat_reflArr] at h
  simpa only [minus_uGL_val] using h

private theorem minus_u_inv (π : Bool) (i : Fin 65) :
    (minus_u π i)⁻¹ = minus_u π i := by
  have h := minus_u_mul_self π i
  calc (minus_u π i)⁻¹ = (minus_u π i)⁻¹ * 1 := by rw [mul_one]
    _ = (minus_u π i)⁻¹ * (minus_u π i * minus_u π i) := by rw [h]
    _ = minus_u π i := by group

private theorem minus_u_injective (π : Bool) : Function.Injective (minus_u π) := by
  intro i j hij
  have h : minus_uGL π i = minus_uGL π j := by
    have h' := congrArg (fun x : minus_R π => (x : GL (Fin 4) (ZMod 5))) hij
    rwa [minus_u_val π i, minus_u_val π j] at h'
  have hm : reflMat (vecD π i) = reflMat (vecD π j) := by
    show reflMat (decode (vecA π i)) = reflMat (decode (vecA π j))
    rw [← minus_uGL_val π i, ← minus_uGL_val π j, h]
  have hf : f5Mat (MA π i) = f5Mat (MA π j) := by
    show f5Mat (reflArr (vecA π i)) = f5Mat (reflArr (vecA π j))
    rw [f5Mat_reflArr, f5Mat_reflArr]
    exact hm
  by_contra hne
  have := minus_distinct π hne
  exact absurd (f5EqA_of_mat_eq hf) (by rw [this]; exact Bool.false_ne_true)

private theorem minus_u_quandle (π : Bool) (i j : Fin 65) :
    minus_u π i * minus_u π j * minus_u π i = minus_u π (TA i j) := by
  apply Subtype.ext
  apply Units.ext
  show ((minus_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *
      ((minus_uGL π j : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) *
      ((minus_uGL π i : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
    ((minus_uGL π (TA i j) : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5))
  have h := f5Mat_eq_of_eqA (minus_table π i j)
  simp only [f5Mat_mulA, MA, f5Mat_reflArr] at h
  exact h

private theorem minus_uGL_inv (π : Bool) (i : Fin 65) :
    (minus_uGL π i)⁻¹ = minus_uGL π i := by
  have h := congrArg (fun x : minus_R π => (x : GL (Fin 4) (ZMod 5))) (minus_u_inv π i)
  simpa only [Subgroup.coe_inv, minus_u_val] using h

private theorem minus_uGL_quandle (π : Bool) (i j : Fin 65) :
    minus_uGL π i * minus_uGL π j * (minus_uGL π i)⁻¹ = minus_uGL π (TA i j) := by
  have h := congrArg (fun x : minus_R π => (x : GL (Fin 4) (ZMod 5))) (minus_u_quandle π i j)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, minus_u_val, minus_uGL_inv] using h

private theorem minus_conj_mem (π : Bool) (g : minus_R π) (j : Fin 65) :
    ∃ k, minus_u π k = g * minus_u π j * g⁻¹ := by
  let S : Set (GL (Fin 4) (ZMod 5)) := Set.range (minus_uGL π)
  have hN : ∀ g ∈ minus_R π, ∀ x : GL (Fin 4) (ZMod 5), x ∈ S ↔ g * x * g⁻¹ ∈ S := by
    intro g hg
    rw [minus_R, fiveReflectionGroup, minus_range_uGL π] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      intro y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨TA i j, (minus_uGL_quandle π i j).symm⟩
      · rintro ⟨j, hj⟩
        refine ⟨TA i j, ?_⟩
        have h2 : y = minus_uGL π (TA i j) := by
          calc y = (minus_uGL π i)⁻¹ *
                (minus_uGL π i * y * (minus_uGL π i)⁻¹) * minus_uGL π i := by group
            _ = (minus_uGL π i)⁻¹ * minus_uGL π j * minus_uGL π i := by rw [← hj]
            _ = minus_uGL π i * minus_uGL π j * minus_uGL π i := by rw [minus_uGL_inv]
            _ = minus_uGL π (TA i j) := by
              simpa only [minus_uGL_inv] using minus_uGL_quandle π i j
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
  have hmem := hN g g.2 (minus_uGL π j)
  obtain ⟨k, hk⟩ := hmem.mp ⟨j, rfl⟩
  exact ⟨k, Subtype.ext (by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, minus_u_val] using hk)⟩

private noncomputable def minus_smul (π : Bool) (g : minus_R π) (j : Fin 65) : Fin 65 :=
  Classical.choose (minus_conj_mem π g j)

private theorem minus_smul_spec (π : Bool) (g : minus_R π) (j : Fin 65) :
    minus_u π (minus_smul π g j) = g * minus_u π j * g⁻¹ :=
  Classical.choose_spec (minus_conj_mem π g j)

private noncomputable instance minus_mulAction (π : Bool) : MulAction (minus_R π) (Fin 65) where
  smul := minus_smul π
  one_smul j := by
    apply minus_u_injective π
    change minus_u π (minus_smul π 1 j) = minus_u π j
    rw [minus_smul_spec, one_mul, inv_one, mul_one]
  mul_smul g h j := by
    apply minus_u_injective π
    change minus_u π (minus_smul π (g * h) j) =
      minus_u π (minus_smul π g (minus_smul π h j))
    rw [minus_smul_spec, minus_smul_spec, minus_smul_spec]
    group

private noncomputable def minus_rho (π : Bool) : minus_R π →* Equiv.Perm (Fin 65) :=
  @MulAction.toPermHom (minus_R π) (Fin 65) _ (minus_mulAction π)

private theorem minus_rho_apply (π : Bool) (g : minus_R π) (j : Fin 65) :
    minus_rho π g j = minus_smul π g j := by
  rw [minus_rho, MulAction.toPermHom_apply, MulAction.toPerm]
  rfl

private theorem minus_rho_u (π : Bool) (i : Fin 65) :
    minus_rho π (minus_u π i) = minusRefl i := by
  ext j
  rw [minus_rho_apply]
  have h := minus_smul_spec π (minus_u π i) j
  rw [minus_u_inv π i] at h
  rw [minus_u_quandle] at h
  have h' := minus_u_injective π h
  rw [h', minus_TA_eq_minusRefl]

private theorem minus_closure_top (π : Bool) :
    Subgroup.closure (Set.range (minus_u π)) = ⊤ := by
  refine Subgroup.map_injective (f := (minus_R π).subtype) Subtype.coe_injective ?_
  rw [MonoidHom.map_closure]
  have himg : (minus_R π).subtype '' Set.range (minus_u π) = Set.range (minus_uGL π) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨minus_u π i, ⟨i, rfl⟩, rfl⟩
  rw [himg]
  have htop : (⊤ : Subgroup (minus_R π)).map (minus_R π).subtype = minus_R π := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [htop, minus_R, fiveReflectionGroup, minus_range_uGL π]

private theorem minus_ker_rho (π : Bool) :
    (minus_rho π).ker = Subgroup.center (minus_R π) := by
  have hker : (minus_rho π).ker = Subgroup.centralizer (Set.range (minus_u π)) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      obtain ⟨j, rfl⟩ := hx
      have h3 : minus_smul π g j = j := by
        have := congrArg (fun σ : Equiv.Perm (Fin 65) => σ j) h
        rwa [minus_rho_apply] at this
      have h2 : minus_u π j = g * minus_u π j * g⁻¹ := by
        have := minus_smul_spec π g j
        rwa [h3] at this
      calc minus_u π j * g = (g * minus_u π j * g⁻¹) * g := by
            conv_lhs => rw [h2]
        _ = g * minus_u π j := by group
    · intro h
      apply Equiv.ext
      intro j
      rw [minus_rho_apply]
      have h2 : minus_u π (minus_smul π g j) = minus_u π j := by
        rw [minus_smul_spec]
        rw [show g * minus_u π j * g⁻¹ = minus_u π j by
          rw [(h (minus_u π j) ⟨j, rfl⟩).symm]
          group]
      exact minus_u_injective π h2
  rw [hker, ← Subgroup.centralizer_closure (Set.range (minus_u π)), minus_closure_top π]
  exact Subgroup.centralizer_univ

private theorem minus_range_rho (π : Bool) :
    (minus_rho π).range = minusPerm := by
  rw [MonoidHom.range_eq_map, ← minus_closure_top π, MonoidHom.map_closure, minusPerm]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (minus_rho_u π i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨minus_u π i, ⟨i, rfl⟩, minus_rho_u π i⟩

theorem exists_minusRealize (π : Bool) :
    ∃ e : (fiveReflectionGroup 3 false π ⧸ Subgroup.center (fiveReflectionGroup 3 false π)) ≃*
      minusPerm, e '' fiveReflectionImage 3 false π = minusClass := by
  let e : (fiveReflectionGroup 3 false π ⧸
        Subgroup.center (fiveReflectionGroup 3 false π)) ≃* minusPerm :=
    (QuotientGroup.quotientMulEquivOfEq
        (show Subgroup.center (minus_R π) = (minus_rho π).ker from (minus_ker_rho π).symm)).trans
      ((QuotientGroup.quotientKerEquivRange (minus_rho π)).trans
        (MulEquiv.subgroupCongr (minus_range_rho π)))
  have he_mk : ∀ i : Fin 65,
      e (QuotientGroup.mk (minus_u π i)) = (⟨minusRefl i, minusRefl_mem i⟩ : minusPerm) := by
    intro i
    show (MulEquiv.subgroupCongr (minus_range_rho π))
        ((QuotientGroup.quotientKerEquivRange (minus_rho π))
          ((QuotientGroup.quotientMulEquivOfEq
            (show Subgroup.center (minus_R π) = (minus_rho π).ker
              from (minus_ker_rho π).symm)) (QuotientGroup.mk (minus_u π i)))) =
      (⟨minusRefl i, minusRefl_mem i⟩ : minusPerm)
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    apply Subtype.ext
    rw [MulEquiv.subgroupCongr_apply]
    exact minus_rho_u π i
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hy
    rw [minus_range_uGL π] at hh
    obtain ⟨i, hi⟩ := hh
    refine ⟨i, ?_⟩
    have hh' : h = minus_u π i := by
      apply Subtype.ext
      rw [← hi, minus_u_val]
    rw [hh', he_mk i]
  · rintro ⟨i, hi⟩
    refine ⟨QuotientGroup.mk (minus_u π i),
      ⟨minus_u π i, by rw [minus_range_uGL]; exact ⟨i, rfl⟩, rfl⟩, ?_⟩
    rw [he_mk i]
    exact Subtype.ext hi.symm

end CFSG.OddTranspositions.PartThree
