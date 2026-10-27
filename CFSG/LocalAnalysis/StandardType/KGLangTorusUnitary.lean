module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpanH90
import CFSG.LocalAnalysis.StandardType.KGLangTorusInnerModel
import CFSG.LocalAnalysis.StandardType.KGLangTorusClassicalInner
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

private noncomputable def kgLangCUniAux_c {d n : ℕ} {𝕂 : Type} [Field 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 1 ≤ d) :
    LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))) :=
  (MulAut.congr (InndiagSU.projEquiv h hd)).symm.toMonoidHom.comp
    (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂))

private theorem kgLangCUniAux_congr_c {d n : ℕ} {𝕂 : Type} [Field 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 1 ≤ d)
    (A : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)) :
    MulAut.congr (InndiagSU.projEquiv h hd) (kgLangCUniAux_c h hd A) =
      LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) A := by
  rw [kgLangCUniAux_c, MonoidHom.comp_apply]
  exact MulEquiv.apply_symm_apply _ _

private theorem kgLangCUniAux_c_range {d n : ℕ} {𝕂 : Type} [Field 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 1 ≤ d) :
    (kgLangCUniAux_c h hd).range = RecipeFieldSU.recIU d h hd := by
  ext φ
  constructor
  · rintro ⟨A, rfl⟩
    rw [RecipeFieldSU.mem_recIU_iff]
    exact ⟨A, (kgLangCUniAux_congr_c h hd A).symm⟩
  · intro hφ
    rw [RecipeFieldSU.mem_recIU_iff] at hφ
    obtain ⟨A, hA⟩ := hφ
    refine ⟨A, ?_⟩
    apply (MulAut.congr (InndiagSU.projEquiv h hd)).injective
    rw [kgLangCUniAux_congr_c h hd A, hA]

private theorem kgLangCUniAux_ker_scalar {d n : ℕ} {𝕂 : Type} [Field 𝕂] [Finite 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 3 ≤ d) (hd1 : 1 ≤ d)
    {A : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)}
    (hA : kgLangCUniAux_c h hd1 A = 1) :
    ∃ c : 𝕂ˣ, h.norm (c : 𝕂) = 1 ∧
      (A : GL (Fin d) 𝕂) = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  have h1 : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
      ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) A = 1 := by
    rw [← kgLangCUniAux_congr_c h hd1 A, hA, map_one]
  obtain ⟨c, hc, hc'⟩ :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.eq_scalar_of_primeFormConjHom_eq_one
      (h := h) (C := (1 : GL (Fin d) 𝕂))
      (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) hd h1
  exact ⟨c, hc, hc'⟩

private theorem kgLangCUniAux_odd_ker {d n : ℕ} {𝕂 : Type} [Field 𝕂] [Finite 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hd1 : 1 ≤ d) : Odd (Nat.card (kgLangCUniAux_c h hd1).ker) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hdvd : 2 ∣ Nat.card (kgLangCUniAux_c h hd1).ker := even_iff_two_dvd.mp heven
  letI : Fintype (kgLangCUniAux_c h hd1).ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hdvd
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hxmem : kgLangCUniAux_c h hd1 (x : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)) = 1 := MonoidHom.mem_ker.mp x.2
  obtain ⟨c, hcnorm, hc⟩ := kgLangCUniAux_ker_scalar h hd hd1 hxmem
  have hc2 : c ^ 2 = 1 := by
    haveI : Nonempty (Fin d) := ⟨0, by omega⟩
    have h1 := congrArg (fun y : (kgLangCUniAux_c h hd1).ker => (y : GL (Fin d) 𝕂)) hx2
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    rw [hc] at h1
    have h3 : (Matrix.GeneralLinearGroup.scalar (Fin d) c) ^ 2 =
        Matrix.GeneralLinearGroup.scalar (Fin d) (c ^ 2) := by rw [map_pow]
    rw [h3] at h1
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin d) 𝕂 => (u : Matrix (Fin d) (Fin d) 𝕂)) h1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_one] at h4
    exact Matrix.scalar_inj.mp (by simpa using h4)
  have hcq : c ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h := hcnorm
    rw [LocalAnalysis.ComponentInitial.UnitaryFieldData.norm,
      LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply] at h
    rw [mul_comm, ← pow_succ] at h
    exact h
  have hcop : Nat.gcd 2 (2 ^ n + 1) = 1 := by
    have hodd : Odd (2 ^ n + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ]
      exact ⟨2 ^ k, by ring⟩
    exact hodd.coprime_two_left
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hc2, hcq⟩
    rwa [hcop, pow_one] at this
  have hx1 : x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hc, hc1, map_one]
    rfl
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  exact hxne hx1

private theorem kgLangCUniAux_fieldHom_injective {d n : ℕ} {𝕂 : Type} [Field 𝕂] [Finite 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) :
    Function.Injective (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
      (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d))) := by
  intro σ τ hστ
  have h2 : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h
      (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) hd hq
      (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
        (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) σ) = σ := by
    simpa using LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor_apply h
      (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) hd hq
      (1 : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)) σ
  have h3 : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h
      (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) hd hq
      (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
        (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) τ) = τ := by
    simpa using LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor_apply h
      (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) hd hq
      (1 : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)) τ
  have h1 := congrArg (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h
    (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) hd hq) hστ
  rwa [h2, h3] at h1

private theorem kgLangCUniAux_conj {d n : ℕ} {𝕂 : Type} [Field 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 1 ≤ d)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))}
    {σ : 𝕂 ≃+* 𝕂}
    (hf : MulAut.congr (InndiagSU.projEquiv h hd) f =
      LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
        (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) σ) :
    ∀ A : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂),
      f * kgLangCUniAux_c h hd A * f⁻¹ =
        kgLangCUniAux_c h hd
          (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h
            (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) σ A) := by
  intro A
  apply (MulAut.congr (InndiagSU.projEquiv h hd)).injective
  rw [map_mul, map_mul, map_inv, hf, kgLangCUniAux_congr_c h hd A,
    kgLangCUniAux_congr_c h hd
      (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h
        (LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)) σ A),
    LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormField_conj_eq]

private theorem kgLangCUniAux_prod_range_cyclic {M : Type*} [Monoid M] {p : ℕ} (hp : 0 < p)
    (S : Monoid.End M) (hS : S ^ p = 1) (f : ℕ → M) (hf : ∀ i, f (i+1) = S (f i))
    (hcomm : ∀ i, f i * f 0 = f 0 * f i) :
    ((List.range p).map (fun i => f (i+1))).prod = ((List.range p).map f).prod := by
  have hfp : f p = f 0 := by
    have h : ∀ i, f i = (S ^ i) (f 0) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [hf, ih, pow_succ']; rfl
    rw [h p, hS]
    rfl
  have hcomm0 : ∀ l : List ℕ, (∀ i ∈ l, f i * f 0 = f 0 * f i) →
      (l.map f).prod * f 0 = f 0 * (l.map f).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
        intro hl
        have hi : f i * f 0 = f 0 * f i := hl i List.mem_cons_self
        have hl' : ∀ j ∈ l, f j * f 0 = f 0 * f j :=
          fun j hj => hl j (List.mem_cons_of_mem i hj)
        simp only [List.map_cons, List.prod_cons]
        calc (f i * (l.map f).prod) * f 0
            = f i * ((l.map f).prod * f 0) := by rw [mul_assoc]
          _ = f i * (f 0 * (l.map f).prod) := by rw [ih hl']
          _ = (f i * f 0) * (l.map f).prod := by rw [mul_assoc]
          _ = (f 0 * f i) * (l.map f).prod := by rw [hi]
          _ = f 0 * (f i * (l.map f).prod) := by rw [mul_assoc]
  have hC : ((List.range (p - 1)).map (fun i => f (i+1))).prod * f 0 =
      f 0 * ((List.range (p - 1)).map (fun i => f (i+1))).prod := by
    have h := hcomm0 ((List.range (p - 1)).map (fun i => i+1)) (fun i _ => hcomm i)
    rwa [List.map_map] at h
  have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp).symm
  have hA : ((List.range p).map (fun i => f (i+1))).prod =
      ((List.range (p - 1)).map (fun i => f (i+1))).prod * f p := by
    conv_lhs => rw [hp1]
    rw [List.prod_range_succ, show p - 1 + 1 = p by omega]
  have hB : ((List.range p).map f).prod =
      f 0 * ((List.range (p - 1)).map (fun i => f (i+1))).prod := by
    conv_lhs => rw [hp1]
    rw [List.prod_range_succ']
  rw [hA, hB, hfp]
  exact hC

private theorem kgLangCUniAux_mapEquiv_pow_val {𝕂 : Type} [Field 𝕂] (σ : 𝕂 ≃+* 𝕂)
    (i : ℕ) (x : 𝕂ˣ) :
    ((((Units.mapEquiv σ.toMulEquiv) ^ i) x : 𝕂ˣ) : 𝕂) = (σ ^ i) (x : 𝕂) := by
  induction i with
  | zero => rw [pow_zero, pow_zero, MulAut.one_apply, RingAut.one_apply]
  | succ i ih =>
      rw [pow_succ']
      change (Units.mapEquiv σ.toMulEquiv) (((Units.mapEquiv σ.toMulEquiv) ^ i) x) =
        (σ ^ (i + 1)) (x : 𝕂)
      rw [Units.coe_mapEquiv, ih, pow_succ', RingAut.mul_apply]
      rfl

private theorem kgLangCUniAux_partNorm_eq_list_prod {𝕂 : Type} [Field 𝕂] (σ : 𝕂 ≃+* 𝕂)
    (ν : 𝕂ˣ) (k : ℕ) :
    TableBUF.partNorm σ (ν : 𝕂) k =
      (((List.range k).map (fun i =>
        ((((Units.mapEquiv σ.toMulEquiv) ^ i) ν : 𝕂ˣ) : 𝕂))).prod) := by
  rw [TableBUF.partNorm]
  conv_rhs =>
    rw [← List.prod_toFinset
        (f := fun i => ((((Units.mapEquiv σ.toMulEquiv) ^ i) ν : 𝕂ˣ) : 𝕂))
        (l := List.range k) List.nodup_range, List.toFinset_range]
  exact Finset.prod_congr rfl fun i _ => (kgLangCUniAux_mapEquiv_pow_val σ i ν).symm

private theorem kgLangCUniAux_scalar_norm {p : ℕ} (hp : p.Prime) {q : ℕ} (hq : Even q)
    (hq1 : 1 ≤ q) {𝕂 : Type} [Field 𝕂] [Finite 𝕂] (hK : Nat.card 𝕂 = q ^ 2)
    {σ : 𝕂 ≃+* 𝕂} (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1) :
    ∀ lam : 𝕂, lam ^ (q + 1) = 1 → σ lam = lam →
      ∃ ν : 𝕂, ν ^ (q + 1) = 1 ∧ TableBUF.partNorm σ ν p = lam := by
  intro lam hlam hσlam
  let β : MulAut 𝕂ˣ := Units.mapEquiv σ.toMulEquiv
  let M : Subgroup 𝕂ˣ :=
    { carrier := {u : 𝕂ˣ | u ^ (q + 1) = 1}
      mul_mem' := fun {u v} hu hv => by
        show (u * v) ^ (q + 1) = 1
        rw [mul_pow, hu, hv, one_mul]
      one_mem' := one_pow _
      inv_mem' := fun {u} hu => by
        show (u⁻¹) ^ (q + 1) = 1
        rw [inv_pow, hu, inv_one] }
  have hMab : ∀ a ∈ M, ∀ c ∈ M, a * c = c * a := fun a _ c _ => mul_comm a c
  have hmap1 : ∀ x : 𝕂ˣ, ((β x : 𝕂ˣ) : 𝕂) = σ (x : 𝕂) := by
    intro x
    rw [show (β x : 𝕂ˣ) = (β ^ 1) x from by rw [pow_one]]
    exact kgLangCUniAux_mapEquiv_pow_val σ 1 x
  have hβp : β ^ p = 1 := by
    ext x
    rw [MulAut.one_apply]
    rw [kgLangCUniAux_mapEquiv_pow_val σ p x, hσp, RingAut.one_apply]
  have hβM : ∀ t : 𝕂ˣ, β t ∈ M ↔ t ∈ M := by
    intro t
    change (β t) ^ (q + 1) = 1 ↔ t ^ (q + 1) = 1
    constructor
    · intro h
      apply Units.ext
      have h2 : ((β t : 𝕂ˣ) : 𝕂) ^ (q + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
      rw [hmap1 t] at h2
      have h4 : (t : 𝕂) ^ (q + 1) = 1 := by
        apply σ.injective
        rw [map_pow, h2, map_one]
      exact h4
    · intro h
      apply Units.ext
      have h2 : (t : 𝕂) ^ (q + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
      rw [Units.val_pow_eq_pow_val, hmap1 t, ← map_pow, h2, map_one, Units.val_one]
  have h90 : ∀ c ∈ M, ((List.range p).map fun i => (β ^ i) c).prod = 1 →
      ∃ s ∈ M, c = s⁻¹ * β s := by
    intro c hc hprod
    have hcK : (c : 𝕂) ^ (q + 1) = 1 := by
      have h := hc
      change c ^ (q + 1) = 1 at h
      have h2 := congrArg (fun u : 𝕂ˣ => (u : 𝕂)) h
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
    have hpart : TableBUF.partNorm σ (c : 𝕂) p = 1 := by
      rw [kgLangCUniAux_partNorm_eq_list_prod]
      have h1 : (List.range p).map (fun i => (((β ^ i) c : 𝕂ˣ) : 𝕂)) =
          ((List.range p).map (fun i => (β ^ i) c)).map (Units.coeHom 𝕂) := by
        rw [List.map_map]; rfl
      rw [h1, ← map_list_prod, hprod, map_one]
    obtain ⟨c₀, hc₀q, hc₀σ⟩ :=
      TableBUF.exists_hilbert90_unitary (q := q) hK hq hq1 hp hσp hσ1 hcK hpart
    have hc₀0 : c₀ ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at hc₀q
      exact zero_ne_one hc₀q
    refine ⟨Units.mk0 c₀ hc₀0, ?_, ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc₀q, Units.val_one]
    · apply Units.ext
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      change (c : 𝕂) = c₀⁻¹ * (Units.mapEquiv σ.toMulEquiv (Units.mk0 c₀ hc₀0) : 𝕂)
      rw [Units.coe_mapEquiv, Units.val_mk0]
      change (c : 𝕂) = c₀⁻¹ * σ c₀
      rw [hc₀σ, mul_comm (c : 𝕂) c₀, ← mul_assoc, inv_mul_cancel₀ hc₀0, one_mul]
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hlam
    exact zero_ne_one hlam
  let t : 𝕂ˣ := Units.mk0 lam hlam0
  have htM : t ∈ M := by
    change t ^ (q + 1) = 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hlam, Units.val_one]
  have hβt : β t = t := by
    apply Units.ext
    change (Units.mapEquiv σ.toMulEquiv t : 𝕂) = (t : 𝕂)
    rw [Units.coe_mapEquiv, Units.val_mk0]
    change σ lam = lam
    rw [hσlam]
  obtain ⟨s, hsM, hs⟩ := kgLangLT3_norms hMab hβp hβM h90 t htM hβt
  refine ⟨(s : 𝕂), ?_, ?_⟩
  · have h := hsM
    change s ^ (q + 1) = 1 at h
    have h2 := congrArg (fun u : 𝕂ˣ => (u : 𝕂)) h
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  · rw [kgLangCUniAux_partNorm_eq_list_prod]
    have h1 : (List.range p).map (fun i => (((β ^ i) s : 𝕂ˣ) : 𝕂)) =
        ((List.range p).map (fun i => (β ^ i) s)).map (Units.coeHom 𝕂) := by
      rw [List.map_map]; rfl
    rw [h1, ← map_list_prod, ← hs]
    exact Units.val_mk0 hlam0

private theorem kgLangCUniAux_scalar_mem {d n : ℕ} {𝕂 : Type} [Field 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 1 ≤ d) {μ : 𝕂ˣ}
    (hμ : h.norm (μ : 𝕂) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin d) μ ∈
      LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) := by
    rw [LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_one,
    LocalAnalysis.ComponentInitial.UnitaryHigher.scalar_barTranspose_mul_mul h
      (1 : Matrix (Fin d) (Fin d) 𝕂) (μ : 𝕂), hμ, one_smul]

private theorem kgLangCUniAux_conj_scalar {d n : ℕ} {𝕂 : Type} [Field 𝕂]
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂) (hd : 1 ≤ d) (μ : 𝕂ˣ)
    (hμ : Matrix.GeneralLinearGroup.scalar (Fin d) μ ∈
      LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)) :
    kgLangCUniAux_c h hd
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) μ, hμ⟩ = 1 := by
  apply (MulAut.congr (InndiagSU.projEquiv h hd)).injective
  rw [kgLangCUniAux_congr_c h hd ⟨Matrix.GeneralLinearGroup.scalar (Fin d) μ, hμ⟩, map_one]
  change LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjAut h
    ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)
    ⟨Matrix.GeneralLinearGroup.scalar (Fin d) μ, hμ⟩ = 1
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjAut_mk]
  congr 1
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.scalar (Fin d) μ * (g : GL (Fin d) 𝕂) *
      (Matrix.GeneralLinearGroup.scalar (Fin d) μ)⁻¹ = (g : GL (Fin d) 𝕂)
  simpa using InndiagSU.scalar_mul_conj μ (1 : GL (Fin d) 𝕂) (g : GL (Fin d) 𝕂)

private theorem kgLangCUniAux_prod_range_cyclic_aut {M : Type*} [Monoid M] {p : ℕ} (hp : 0 < p)
    (S : MulAut M) (hS : S ^ p = 1) (f : ℕ → M) (hf : ∀ i, f (i+1) = S (f i))
    (hcomm : ∀ i, f i * f 0 = f 0 * f i) :
    ((List.range p).map (fun i => f (i+1))).prod = ((List.range p).map f).prod := by
  let Send : Monoid.End M := S.toMonoidHom
  have hSp : Send ^ p = 1 := by
    ext w
    have h : ∀ k : ℕ, (Send ^ k) w = (S ^ k) w := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          rw [pow_succ', pow_succ']
          change Send ((Send ^ k) w) = S ((S ^ k) w)
          rw [ih]
          rfl
    rw [h p, hS]; rfl
  exact kgLangCUniAux_prod_range_cyclic hp Send hSp f hf hcomm

private theorem kgLangCUniAux_mem_units_image {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι]
    [Field 𝕂] (B : Subalgebra 𝕂 (Matrix ι ι 𝕂)) [Finite ↥B]
    (hcomm : ∀ a b : ↥B, a * b = b * a) (g : GL ι 𝕂) :
    g ∈ (⊤ : Subgroup (Units ↥B)).map (Units.map B.val.toMonoidHom) ↔
      (g : Matrix ι ι 𝕂) ∈ B := by
  letI : CommRing ↥B := { (inferInstance : Ring ↥B) with mul_comm := hcomm }
  constructor
  · intro hg
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hg
    exact (u : B).2
  · intro hg
    have hunit : IsUnit (⟨(g : Matrix ι ι 𝕂), hg⟩ : B) := by
      rw [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]
      intro y hy
      apply Subtype.ext
      have h := congrArg (fun z : B => (z : Matrix ι ι 𝕂)) hy
      simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h
      have hgunit : IsUnit (g : Matrix ι ι 𝕂) := ⟨g, rfl⟩
      have h' : (y : Matrix ι ι 𝕂) * (g : Matrix ι ι 𝕂) =
          (0 : Matrix ι ι 𝕂) * (g : Matrix ι ι 𝕂) := by
        rw [h, zero_mul]
      exact hgunit.mul_right_cancel h'
    exact Subgroup.mem_map.mpr ⟨hunit.unit, Subgroup.mem_top _, by
      apply Units.ext
      rw [Units.coe_map, IsUnit.unit_spec]
      rfl⟩

theorem kgLangC_torusInput_unitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d n : ℕ} (hd : 3 ≤ d)
    (hpd : ¬ p ∣ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (𝕂 : Type) [Field 𝕂] [Finite 𝕂]
    (h𝕂 : Nat.card 𝕂 = (2 ^ n) ^ 2)
    (J : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))))
    (hJ : (J : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))))) =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))))
    (hfp : orderOf f = p) :
    KGLangTorusInput p J (MulAut.conj f).toMonoidHom := by
  classical
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at h𝕂
    have h2 := Finite.one_lt_card (α := 𝕂)
    omega
  let h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂 := unitaryFieldData_of_card hn h𝕂
  haveI : CharP 𝕂 2 := h.charP
  have hd1 : 1 ≤ d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let hC : LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram (1 : GL (Fin d) 𝕂) :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := 𝕂) (n := d)
  let c := kgLangCUniAux_c h hd1
  have hJc : J = c.range := by
    rw [← SetLike.coe_set_eq, hJ, kgLangCUniAux_c_range h hd1, RecipeFieldSU.coe_recIU h h𝕂 hd1]
  obtain ⟨σ, hσ⟩ := RecipeFieldSU.congr_field_eq h hd1 hf
  have hσord : orderOf σ = p := by
    have h1 : orderOf (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h hC σ) = p := by
      rw [← hσ]
      exact (orderOf_injective ((MulAut.congr (InndiagSU.projEquiv h hd1)).toMonoidHom)
        (MulAut.congr (InndiagSU.projEquiv h hd1)).injective f).trans hfp
    rw [← orderOf_injective (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h hC)
      (kgLangCUniAux_fieldHom_injective h hd hq) σ]
    exact h1
  intro E hE hEfix
  have hEfix' : ∀ x ∈ E, f * x * f⁻¹ = x := by
    intro x hx
    have h := (hEfix x hx).2
    change MulAut.conj f x = x at h
    rwa [MulAut.conj_apply] at h
  have hEJ : E ≤ J := fun x hx => (hEfix x hx).1
  have hEcr : E ≤ c.range := by rw [← hJc]; exact hEJ
  let PU := LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
    ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)
  let P : Subgroup PU := E.comap c
  let Pgl : Subgroup (GL (Fin d) 𝕂) := P.map PU.subtype
  have hPmap : P.map c = E := Subgroup.map_comap_eq_self hEcr
  have hPab : ∀ a ∈ Pgl, ∀ b ∈ Pgl, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have hcomm : c a' * c b' = c b' * c a' := by
      letI : IsMulCommutative E := hE.1
      exact congrArg Subtype.val (mul_comm' (⟨c a', ha'⟩ : E) (⟨c b', hb'⟩ : E))
    have hker : c (a' * b' * (b' * a')⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    obtain ⟨lam, -, hlam⟩ := kgLangCUniAux_ker_scalar h hd hd1 hker
    have hap : c (a' ^ p) = 1 := by
      rw [map_pow, hE.2 (c a') ha']
    obtain ⟨μ, -, hμ⟩ := kgLangCUniAux_ker_scalar h hd hd1 hap
    have hxy : (a' : GL (Fin d) 𝕂) * b' = Matrix.GeneralLinearGroup.scalar (Fin d) lam * (b' * a') := by
      have h := hlam
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [← h]; group
    have hxp : (a' : GL (Fin d) 𝕂) ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) μ := by
      simpa only [Subgroup.coe_pow] using hμ
    exact kgLangC_pairing (c := lam) (μ := μ) hp hpd hxy hxp
  have hEp : IsPGroup p E := by
    apply IsPGroup.of_exponent_dvd_pow (n := 1)
    rw [pow_one]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 x x.2
  have hEodd : Odd (Nat.card E) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hPcard : Nat.card P = Nat.card c.ker * Nat.card E := by
    have h1 : Nat.card (c.comp P.subtype).ker * Nat.card (c.comp P.subtype).range = Nat.card P :=
      Subgroup.card_ker_mul_card_range (c.comp P.subtype)
    have h2 : (c.comp P.subtype).range = E := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
    have hc_ker_le_P : c.ker ≤ P := by
      intro x hx
      show c x ∈ E
      rw [MonoidHom.mem_ker.mp hx]
      exact E.one_mem
    have h3 : Nat.card (c.comp P.subtype).ker = Nat.card c.ker := by
      apply Nat.card_congr
      refine
        { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.mpr (by
            simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype] using
              MonoidHom.mem_ker.mp x.2)⟩
          invFun := fun y => ⟨⟨y.1, hc_ker_le_P y.2⟩,
            MonoidHom.mem_ker.mpr (by
              simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
              exact MonoidHom.mem_ker.mp y.2)⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun y => by ext; rfl }
    rw [h3, h2] at h1
    exact h1.symm
  have hPgl_card : Nat.card Pgl = Nat.card P :=
    Subgroup.card_map_of_injective (f := PU.subtype) (fun _ _ h => Subtype.ext h)
  have hPgl_odd : Odd (Nat.card Pgl) := by
    rw [hPgl_card, hPcard]
    exact (kgLangCUniAux_odd_ker h hn hd hd1).mul hEodd
  let B : Subalgebra 𝕂 (Matrix (Fin d) (Fin d) 𝕂) :=
    Algebra.adjoin 𝕂 ((fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (Pgl : Set _))
  let β : Matrix (Fin d) (Fin d) 𝕂 →+* Matrix (Fin d) (Fin d) 𝕂 :=
    (σ : 𝕂 →+* 𝕂).mapMatrix
  have hβP : ∀ g ∈ Pgl, β (g : Matrix (Fin d) (Fin d) 𝕂) ∈
      (fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) '' (Pgl : Set _) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨(LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC σ g' : PU), ?_, ?_⟩
    · have hmem : LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC σ g' ∈ P := by
        show c (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC σ g') ∈ E
        rw [← kgLangCUniAux_conj h hd1 hσ g', hEfix' (c g') hg']
        exact hg'
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    · change ((LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ g' : GL (Fin d) 𝕂) :
          Matrix (Fin d) (Fin d) 𝕂) =
        ((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂).map σ
      rw [LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
  have hβsc : ∀ r : 𝕂, β (Matrix.scalar (Fin d) r) = Matrix.scalar (Fin d) (σ r) := by
    intro r
    ext i j
    by_cases h : i = j
    · subst h; simp [β, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply]
    · simp [β, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, h]
  have hσp : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
  have hβpow : β ^ p = 1 := by
    ext M i j
    have hiter : ∀ (k : ℕ) (N : Matrix (Fin d) (Fin d) 𝕂) (a b : Fin d),
        ((β ^ k) N) a b = (σ ^ k) (N a b) := by
      intro k
      induction k with
      | zero => intro N a b; rw [pow_zero, pow_zero]; rfl
      | succ k ih =>
          intro N a b
          rw [pow_succ']
          change β ((β ^ k) N) a b = (σ ^ (k + 1)) (N a b)
          have h1 : β ((β ^ k) N) a b = σ (((β ^ k) N) a b) := rfl
          rw [h1, ih N a b, pow_succ']
          simp
    rw [hiter p M i j, hσp]
    rfl
  have hβp : ∀ a ∈ B, (⇑β)^[p] a = a := by
    intro a _
    rw [← RingHom.coe_pow, hβpow]
    rfl
  have hβB : ∀ x ∈ B, β x ∈ B := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => β x ∈ B) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact Algebra.subset_adjoin (hβP g hg)
    · intro r
      have hr : algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) r = Matrix.scalar (Fin d) r := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [hr, hβsc]
      have hr2 : Matrix.scalar (Fin d) (σ r) =
          algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) (σ r) := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [hr2]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y hx hy hx' hy'
      rw [map_add]; exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      rw [map_mul]; exact mul_mem hx' hy'
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x :=
    (kgLangC_span_comm_reduced Pgl hPab hPgl_odd).1
  haveI : CommRing ↥B :=
    { (inferInstance : Ring ↥B) with
      mul_comm := fun a b => Subtype.ext (hBcomm a a.2 b b.2) }
  haveI : Finite ↥B := inferInstance
  let τ : Matrix (Fin d) (Fin d) 𝕂 → Matrix (Fin d) (Fin d) 𝕂 := fun x => Matrix.transpose (x.map h.bar)
  have hτadd_gen : ∀ x y : Matrix (Fin d) (Fin d) 𝕂, τ (x + y) = τ x + τ y := by
    intro x y
    ext i j
    simp only [τ, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add]
  have hτmul_gen : ∀ x y : Matrix (Fin d) (Fin d) 𝕂, τ (x * y) = τ y * τ x := by
    intro x y
    show Matrix.transpose ((x * y).map h.bar) =
      Matrix.transpose (y.map h.bar) * Matrix.transpose (x.map h.bar)
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hτone_gen : τ 1 = 1 := by
    show Matrix.transpose ((1 : Matrix (Fin d) (Fin d) 𝕂).map h.bar) = 1
    rw [Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
  have hτsc : ∀ r : 𝕂, τ (Matrix.scalar (Fin d) r) = Matrix.scalar (Fin d) (h.bar r) := by
    intro r
    ext i j
    by_cases h : i = j
    · subst h; simp [τ, Matrix.map_apply, Matrix.transpose_apply, Matrix.scalar_apply]
    · simp [τ, Matrix.map_apply, Matrix.transpose_apply, Matrix.scalar_apply, h, Ne.symm h]
  have hττ_gen : ∀ x : Matrix (Fin d) (Fin d) 𝕂, τ (τ x) = x := by
    intro x
    ext i j
    simp only [τ, Matrix.transpose_apply, Matrix.map_apply]
    exact h.bar_bar (x i j)
  have hτB : ∀ a ∈ B, τ a ∈ B := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => τ a ∈ B) ?_ ?_ ?_ ?_ ha
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := hy
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      have hgunit : Matrix.transpose
          (((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂).map h.bar) *
          ((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) = 1 := by
        have h := (LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary
          (h := h) (C := ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂))).mp g'.2
        simpa using h
      have htau : τ ((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) =
          ((g'⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) := by
        show Matrix.transpose (((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂).map h.bar) =
          ((g'⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)
        calc Matrix.transpose (((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂).map h.bar)
            = Matrix.transpose (((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂).map h.bar) *
                ↑((g' : GL (Fin d) 𝕂) * (g' : GL (Fin d) 𝕂)⁻¹) := by
              rw [mul_inv_cancel, Units.val_one, mul_one]
          _ = (Matrix.transpose (((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂).map h.bar) *
                ↑(g' : GL (Fin d) 𝕂)) * ↑((g' : GL (Fin d) 𝕂)⁻¹) := by
              rw [Units.val_mul, mul_assoc]
          _ = 1 * ↑((g' : GL (Fin d) 𝕂)⁻¹) := by rw [hgunit]
          _ = ↑((g' : GL (Fin d) 𝕂)⁻¹) := by rw [one_mul]
      show τ ((g' : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) ∈ B
      rw [htau]
      exact Algebra.subset_adjoin
        ⟨(g'⁻¹ : GL (Fin d) 𝕂), Subgroup.mem_map.mpr ⟨g'⁻¹, P.inv_mem hg', rfl⟩, rfl⟩
    · intro r
      rw [show algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) r = Matrix.scalar (Fin d) r from by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply], hτsc]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y hx hy hx' hy'
      rw [hτadd_gen]; exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      rw [hτmul_gen]; exact mul_mem hy' hx'
  have hτadd : ∀ a ∈ B, ∀ b ∈ B, τ (a + b) = τ a + τ b := fun a _ b _ => hτadd_gen a b
  have hτmul : ∀ a ∈ B, ∀ b ∈ B, τ (a * b) = τ a * τ b := by
    intro a ha b hb
    rw [hτmul_gen]
    exact (hBcomm (τ a) (hτB a ha) (τ b) (hτB b hb)).symm
  have hτone : τ 1 = 1 := hτone_gen
  have hττ : ∀ a ∈ B, τ (τ a) = a := fun a _ => hττ_gen a
  have hτβ : ∀ a ∈ B, τ (β a) = β (τ a) := by
    intro a _
    ext i j
    show h.bar (σ (a j i)) = σ (h.bar (a j i))
    exact (LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ (a j i)).symm
  let V : Subgroup (GL (Fin d) 𝕂) :=
    (⊤ : Subgroup (Units ↥B)).map (Units.map B.val.toMonoidHom)
  have mem_V_iff : ∀ g : GL (Fin d) 𝕂, g ∈ V ↔ (g : Matrix (Fin d) (Fin d) 𝕂) ∈ B :=
    fun g => kgLangCUniAux_mem_units_image B
      (fun a b => Subtype.ext (hBcomm a a.2 b b.2)) g
  let U : Subgroup PU := V.comap PU.subtype
  have mem_U_iff : ∀ x : PU, x ∈ U ↔ ((x : GL (Fin d) 𝕂) :
      Matrix (Fin d) (Fin d) 𝕂) ∈ B :=
    fun x => mem_V_iff (x : GL (Fin d) 𝕂)
  have hPU : P ≤ U := by
    intro x hx
    rw [mem_U_iff]
    exact Algebra.subset_adjoin ⟨(x : GL (Fin d) 𝕂), Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
  let S : MulAut PU := LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC σ
  let coeU : PU →* Matrix (Fin d) (Fin d) 𝕂 :=
    (Units.coeHom (Matrix (Fin d) (Fin d) 𝕂)).comp PU.subtype
  have hβiter : ∀ (k : ℕ) (M : Matrix (Fin d) (Fin d) 𝕂),
      (⇑β)^[k] M = M.map ((σ ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) := by
    intro k
    induction k with
    | zero => intro M; simp
    | succ k ih =>
        intro M
        rw [Function.iterate_succ_apply', ih]
        change (M.map ((σ ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂)).map (σ : 𝕂 →+* 𝕂) =
          M.map ((σ ^ (k + 1) : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂)
        rw [Matrix.map_map]
        congr 1
        ext x
        rw [pow_succ']
        change σ ((σ ^ k) x) = (σ * σ ^ k) x
        rw [RingAut.mul_apply]
  have hβSiter : ∀ (i : ℕ) (w : PU),
      (⇑β)^[i] (coeU w) = coeU ((S ^ i) w) := by
    intro i w
    have hSi : (S ^ i) =
        LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC (σ ^ i) := by
      rw [show S = LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC σ from rfl]
      exact (map_pow (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC) σ i).symm
    change (⇑β)^[i] (((w : PU) : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) =
      ((((S ^ i) w : PU) : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)
    rw [hSi, LocalAnalysis.ComponentInitial.UnitaryHigher.coe_primeFormFieldU,
      LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
    exact hβiter i (((w : PU) : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)
  have hβS : ∀ w : PU, β (coeU w) = coeU (S w) := by
    intro w
    have h := hβSiter 1 w
    rwa [Function.iterate_one, pow_one] at h
  have hSp : S ^ p = 1 := by
    rw [show S = LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC σ from rfl,
      ← map_pow (LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldU h hC) σ p, hσp,
      map_one]
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    apply Units.ext
    show ((a : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
        ((b : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) =
      ((b : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
        ((a : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂)
    exact hBcomm _ ((mem_U_iff a).mp ha) _ ((mem_U_iff b).mp hb)
  have hβU : ∀ u ∈ U, S u ∈ U := by
    intro u hu
    rw [mem_U_iff]
    change coeU (S u) ∈ B
    rw [← hβS u]
    exact hβB _ ((mem_U_iff u).mp hu)
  let N : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))) := U.map c
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hUab a' ha' b' hb']
  have hNstab : ∀ x ∈ N, (MulAut.conj f).toMonoidHom x ∈ N := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    change f * c u * f⁻¹ ∈ N
    exact Subgroup.mem_map.mpr ⟨S u, hβU u hu, (kgLangCUniAux_conj h hd1 hσ u).symm⟩
  have hNleJ : N ≤ J := by
    rw [hJc]
    exact Subgroup.map_le_range c U
  have hEN : E ≤ N := by
    rw [← hPmap]
    exact Subgroup.map_mono hPU
  have hN90 : ∀ x ∈ N, ((List.range p).map fun i =>
      endPow (MulAut.conj f).toMonoidHom i x).prod = 1 →
      ∃ s ∈ N, x = s⁻¹ * (MulAut.conj f).toMonoidHom s := by
    intro x hx hnorm
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    let seq : ℕ → PU := fun i => (S ^ i) u
    have hseq : ∀ i, seq (i+1) = S (seq i) := fun i => by simp only [seq, pow_succ']; rfl
    have hiter : ∀ i, endPow (MulAut.conj f).toMonoidHom i (c u) = c (seq i) := by
      intro i
      induction i with
      | zero => rw [endPow_apply]; rfl
      | succ i ih =>
          rw [show endPow (MulAut.conj f).toMonoidHom (i+1) (c u) =
              (MulAut.conj f) (endPow (MulAut.conj f).toMonoidHom i (c u)) from by
            rw [endPow_apply, Function.iterate_succ_apply']; rfl, ih]
          change f * c (seq i) * f⁻¹ = c (seq (i+1))
          rw [kgLangCUniAux_conj h hd1 hσ (seq i)]
          congr 1
          show S (seq i) = seq (i+1)
          rw [hseq i]
    have hnorm_u : c (((List.range p).map seq).prod) = 1 := by
      rw [map_list_prod, List.map_map, ← hnorm]
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      exact (hiter i).symm
    obtain ⟨lam, hlamnorm, hlam⟩ := kgLangCUniAux_ker_scalar h hd hd1 hnorm_u
    have hlamq : (lam : 𝕂) ^ (2 ^ n + 1) = 1 := by
      have h := hlamnorm
      rw [LocalAnalysis.ComponentInitial.UnitaryFieldData.norm,
        LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply] at h
      rw [mul_comm, ← pow_succ] at h
      exact h
    have hσ1 : σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hσord
      exact hp.ne_one hσord.symm
    have hseqmem : ∀ i, seq i ∈ U := by
      intro i
      simp only [seq]
      induction i with
      | zero => simpa using hu
      | succ i ih => rw [pow_succ']; exact hβU _ ih
    have hcycle : ((List.range p).map (fun i => seq (i+1))).prod =
        ((List.range p).map seq).prod := by
      refine kgLangCUniAux_prod_range_cyclic_aut hp.pos S hSp seq ?_ ?_
      · intro i
        rw [hseq i]
      · intro i
        exact hUab _ (hseqmem i) _ (hseqmem 0)
    have hβfix : β (coeU (((List.range p).map seq).prod)) =
        coeU (((List.range p).map seq).prod) := by
      have hcoe : (List.map (fun i => coeU (seq i)) (List.range p)).prod =
          coeU (((List.range p).map seq).prod) := by
        rw [show (List.map (fun i => coeU (seq i)) (List.range p)) =
            List.map (⇑coeU) ((List.range p).map seq) from by rw [List.map_map]; rfl]
        exact (map_list_prod coeU ((List.range p).map seq)).symm
      calc β (coeU (((List.range p).map seq).prod))
          = β ((List.map (fun i => coeU (seq i)) (List.range p)).prod) := by rw [hcoe]
        _ = ((List.map (fun i => coeU (seq i)) (List.range p)).map β).prod := by
              rw [map_list_prod β]
        _ = ((List.range p).map (fun i => β (coeU (seq i)))).prod := by
              rw [List.map_map]; rfl
        _ = ((List.range p).map (fun i => coeU (S (seq i)))).prod := by
              apply congrArg List.prod
              apply List.map_congr_left
              intro i _
              exact hβS (seq i)
        _ = ((List.range p).map (fun i => coeU (seq (i+1)))).prod := by
              apply congrArg List.prod
              apply List.map_congr_left
              intro i _
              rw [hseq i]
        _ = coeU ((List.range p).map (fun i => seq (i+1))).prod := by
              rw [show (List.map (fun i => coeU (seq (i+1))) (List.range p)) =
                  List.map (⇑coeU) ((List.range p).map (fun i => seq (i+1))) from by
                rw [List.map_map]; rfl]
              exact (map_list_prod coeU ((List.range p).map (fun i => seq (i+1)))).symm
        _ = coeU ((List.range p).map seq).prod := by rw [hcycle]
    have hβfix' : β (Matrix.scalar (Fin d) (lam : 𝕂)) = Matrix.scalar (Fin d) (lam : 𝕂) := by
      have h := hβfix
      have hcoe' : coeU (((List.range p).map seq).prod) =
          ((Matrix.GeneralLinearGroup.scalar (Fin d) lam : GL (Fin d) 𝕂) :
            Matrix (Fin d) (Fin d) 𝕂) :=
        congrArg (fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) hlam
      rw [hcoe'] at h
      rwa [Matrix.GeneralLinearGroup.coe_scalar] at h
    have hσlam : σ lam = lam := by
      have h := hβfix'
      rw [hβsc] at h
      exact Matrix.scalar_inj.mp h
    obtain ⟨ν, hνq, hνpart⟩ := kgLangCUniAux_scalar_norm (q := 2 ^ n) hp
      ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow h𝕂 hσp hσ1 lam hlamq hσlam
    have hν0 : ν ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by positivity)] at hνq
      exact zero_ne_one hνq
    let νu : 𝕂ˣ := Units.mk0 ν hν0
    have hνpow : (νu : 𝕂) ^ (2 ^ n + 1) = 1 := by rw [Units.val_mk0]; exact hνq
    have hνinorm : h.norm ((νu⁻¹ : 𝕂ˣ) : 𝕂) = 1 := by
      rw [Units.val_inv_eq_inv_val, LocalAnalysis.ComponentInitial.UnitaryFieldData.norm,
        LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, mul_comm, ← pow_succ,
        inv_pow, hνpow, inv_one]
    have hscU : Matrix.GeneralLinearGroup.scalar (Fin d) (νu⁻¹) ∈ PU :=
      kgLangCUniAux_scalar_mem h hd1 hνinorm
    let u' : PU := ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (νu⁻¹) * (u : GL (Fin d) 𝕂),
      Subgroup.mul_mem _ hscU u.2⟩
    have hcoe_u' : coeU u' = Matrix.scalar (Fin d) ((νu⁻¹ : 𝕂ˣ) : 𝕂) * coeU u := by
      show ((Matrix.GeneralLinearGroup.scalar (Fin d) (νu⁻¹) * (u : GL (Fin d) 𝕂) :
        GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) =
        Matrix.scalar (Fin d) ((νu⁻¹ : 𝕂ˣ) : 𝕂) * coeU u
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      rfl
    have hu'U : u' ∈ U := by
      rw [mem_U_iff]
      show coeU u' ∈ B
      rw [hcoe_u']
      refine mul_mem ?_ ((mem_U_iff u).mp hu)
      rw [show Matrix.scalar (Fin d) ((νu⁻¹ : 𝕂ˣ) : 𝕂) =
          algebraMap 𝕂 (Matrix (Fin d) (Fin d) 𝕂) ((νu⁻¹ : 𝕂ˣ) : 𝕂) from by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]]
      exact Subalgebra.algebraMap_mem _ _
    have hnorm_u' : ((List.range p).map (fun i => (⇑β)^[i] (coeU u'))).prod = 1 := by
      have hterm : ∀ i : ℕ, (⇑β)^[i] (coeU u') =
          Matrix.scalar (Fin d) ((σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)) * (⇑β)^[i] (coeU u) := by
        intro i
        rw [hcoe_u']
        induction i with
        | zero => simp
        | succ i ih =>
            rw [Function.iterate_succ_apply', ih, map_mul, hβsc,
              ← Function.iterate_succ_apply' (⇑β) i (coeU u)]
            congr 1
            rw [pow_succ', RingAut.mul_apply]
      have hsplit : ∀ l : List ℕ,
          (l.map (fun i => Matrix.scalar (Fin d) ((σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)) *
            (⇑β)^[i] (coeU u))).prod =
          (l.map (fun i => Matrix.scalar (Fin d) ((σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)))).prod *
          (l.map (fun i => (⇑β)^[i] (coeU u))).prod := by
        intro l
        induction l with
        | nil => simp
        | cons i l ih =>
            simp only [List.map_cons, List.prod_cons, ih]
            have hcomm : Commute ((⇑β)^[i] (coeU u))
                ((l.map fun j => Matrix.scalar (Fin d) ((σ ^ j) ((νu⁻¹ : 𝕂ˣ) : 𝕂))).prod) := by
              apply Commute.list_prod_right
              intro x hx
              obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
              exact (Matrix.scalar_commute _ (fun r' => Commute.all _ _) _).symm
            exact hcomm.mul_mul_mul_comm _ _
      have hA : (List.map (fun i => (⇑β)^[i] (coeU u)) (List.range p)).prod =
          (List.map (fun i => coeU (seq i)) (List.range p)).prod := by
        congr 1
        apply List.map_congr_left
        intro i _
        exact hβSiter i u
      have hlam_matrix : (List.map (fun i => coeU (seq i)) (List.range p)).prod =
          Matrix.scalar (Fin d) (lam : 𝕂) := by
        have hcoe : (List.map (fun i => coeU (seq i)) (List.range p)).prod =
            coeU (((List.range p).map seq).prod) := by
          rw [show (List.map (fun i => coeU (seq i)) (List.range p)) =
              List.map (⇑coeU) ((List.range p).map seq) from by rw [List.map_map]; rfl]
          exact (map_list_prod coeU ((List.range p).map seq)).symm
        rw [hcoe]
        change coeU (((List.range p).map seq).prod) = Matrix.scalar (Fin d) (lam : 𝕂)
        rw [show coeU (((List.range p).map seq).prod) =
            ((Matrix.GeneralLinearGroup.scalar (Fin d) lam : GL (Fin d) 𝕂) :
              Matrix (Fin d) (Fin d) 𝕂) from
          congrArg (fun g : GL (Fin d) 𝕂 => (g : Matrix (Fin d) (Fin d) 𝕂)) hlam]
        rw [Matrix.GeneralLinearGroup.coe_scalar]
      have hscalar : (List.map (fun i => Matrix.scalar (Fin d) ((σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)))
          (List.range p)).prod = Matrix.scalar (Fin d)
          ((List.map (fun i => (σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)) (List.range p)).prod) := by
        rw [map_list_prod (Matrix.scalar (Fin d)) _, List.map_map]
        rfl
      have hlam_list : (List.map (fun i => (σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)) (List.range p)).prod =
          (lam : 𝕂)⁻¹ := by
        rw [← List.prod_toFinset (f := fun i => (σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂))
          (l := List.range p) List.nodup_range, List.toFinset_range]
        have h1 : (∏ i ∈ Finset.range p, (σ ^ i) ((νu⁻¹ : 𝕂ˣ) : 𝕂)) =
            (∏ i ∈ Finset.range p, (σ ^ i) ((νu : 𝕂ˣ) : 𝕂))⁻¹ := by
          rw [← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun i _ => map_inv₀ (σ ^ i) (νu : 𝕂)
        rw [h1, show (∏ i ∈ Finset.range p, (σ ^ i) ((νu : 𝕂ˣ) : 𝕂)) =
            TableBUF.partNorm σ (νu : 𝕂) p from rfl, Units.val_mk0, hνpart]
      rw [List.map_congr_left (fun i _ => hterm i), hsplit (List.range p), hscalar, hlam_list,
        hA, hlam_matrix]
      simp
    have hu'B : (((u' : PU) : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) ∈ B :=
      (mem_U_iff u').mp hu'U
    have hu'τ : (((u' : PU) : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
        τ (u' : GL (Fin d) 𝕂) = 1 := by
      have h' : τ (coeU u') * coeU u' = 1 := by
        have hmem := (LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary
          (h := h) (C := ((1 : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂))).mp u'.2
        change ((((((u' : PU) : GL (Fin d) 𝕂)) : Matrix (Fin d) (Fin d) 𝕂)).map h.bar).transpose *
            ((((u' : PU) : GL (Fin d) 𝕂)) : Matrix (Fin d) (Fin d) 𝕂) = 1
        simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one] using hmem
      have htau : τ (coeU u') = coeU (u'⁻¹) := by
        calc τ (coeU u')
            = τ (coeU u') * coeU (u' * u'⁻¹) := by rw [mul_inv_cancel, map_one coeU, mul_one]
          _ = (τ (coeU u') * coeU u') * coeU (u'⁻¹) := by
                rw [map_mul, mul_assoc]
          _ = 1 * coeU (u'⁻¹) := by rw [h']
          _ = coeU (u'⁻¹) := by rw [one_mul]
      change coeU u' * τ (coeU u') = 1
      rw [htau, show coeU u' * coeU (u'⁻¹) = coeU (u' * u'⁻¹) from by rw [map_mul],
        mul_inv_cancel, map_one coeU]
    obtain ⟨s, hsB, hsτ, hsu⟩ :=
      kgLangC_span_h90_unitary hp hσord Pgl hPab hPgl_odd B rfl β hβP hβsc hβp τ hτB hτadd
        hτmul hτone hττ hτβ (u' : GL (Fin d) 𝕂) hu'B hu'τ hnorm_u'
    have hsPU : s ∈ PU := by
      rw [LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary,
        Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
      have htau : τ ((s : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) =
          (((s⁻¹ : GL (Fin d) 𝕂)) : Matrix (Fin d) (Fin d) 𝕂) := by
        calc τ (s : Matrix (Fin d) (Fin d) 𝕂)
            = ((s⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
                ((s : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
                τ (s : Matrix (Fin d) (Fin d) 𝕂) := by
                rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
          _ = ((s⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
                (((s : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
                τ (s : Matrix (Fin d) (Fin d) 𝕂)) := by
                rw [mul_assoc]
          _ = ((s⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) * 1 := by rw [hsτ]
          _ = ((s⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) := by rw [mul_one]
      change τ ((s : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
          ((s : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) = 1
      rw [htau, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    let s₀ : PU := ⟨s, hsPU⟩
    have hs₀U : s₀ ∈ U := (mem_U_iff s₀).mpr hsB
    have hu'mat : coeU u' = coeU (s₀⁻¹ * S s₀) := by
      change (((u' : PU) : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) =
          coeU (s₀⁻¹ * S s₀)
      rw [hsu]
      change ((s⁻¹ : GL (Fin d) 𝕂) : Matrix (Fin d) (Fin d) 𝕂) *
          β (coeU s₀) = coeU (s₀⁻¹ * S s₀)
      rw [hβS s₀, map_mul]
      rfl
    have hu' : u' = s₀⁻¹ * S s₀ := by
      apply Subtype.ext
      apply Units.ext
      exact hu'mat
    have hcu' : c u' = c u := by
      have hu'eq : u' = ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (νu⁻¹), hscU⟩ * u :=
        Subtype.ext rfl
      rw [hu'eq, map_mul, kgLangCUniAux_conj_scalar h hd1 (νu⁻¹) hscU, one_mul]
    refine ⟨c s₀, Subgroup.mem_map.mpr ⟨s₀, hs₀U, rfl⟩, ?_⟩
    rw [← hcu', hu', map_mul, map_inv, ← kgLangCUniAux_conj h hd1 hσ s₀]
    rfl
  exact ⟨N, hNleJ, hNab, hNstab, hN90, hEN⟩

theorem kgLangTorusDatumCont_unitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d n : ℕ} (hd : 3 ≤ d)
    (hpd : ¬ p ∣ d) (hpn : p ∣ n) (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = (2 ^ n) ^ 2)
    (hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))))
    (hZ : ∀ [Finite (HopfCover (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))))]
      (θ : HopfCover (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))) ⧸
        Subgroup.center (HopfCover (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))) ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))),
      commutator (HopfCover (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))) = ⊤ →
      Nat.Coprime
        (Nat.card (Subgroup.center (HopfCover (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))))) p) :
    KGLangTorusDatumCont p (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))) := by
  classical
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at h𝕂
    have h2 := Finite.one_lt_card (α := 𝕂)
    omega
  let h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n 𝕂 := unitaryFieldData_of_card hn h𝕂
  haveI : CharP 𝕂 2 := h.charP
  have hd1 : 1 ≤ d := by omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn3 : 3 ≤ n := le_trans hp3 (Nat.le_of_dvd (by omega) hpn)
  have hnq : (d, 2 ^ n) ≠ (3, 2) := by
    intro hpair
    have h2 : 2 ^ n = 2 := congrArg Prod.snd hpair
    have hge : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    rw [h2] at hge
    norm_num at hge
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨h1, h2⟩
    exact hnq (by rw [h1, h2])
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU 𝕂 2 n h𝕂 d hd hnq
  have hna : ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)), a * b ≠ b * a := by
    haveI : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h𝕂 hd hnq
    have hperf : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))) :=
      Group.IsPerfect.ofSurjective
        (f := LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (QuotientGroup.mk'_surjective _)
    have := hs.toNontrivial
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative
      (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))) ⟨⟨h⟩⟩
  have hinn : ∀ r : LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)),
      MulAut.conj r ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)) := by
    intro r
    rw [← RecipeFieldSU.coe_recIU h h𝕂 hd1]
    exact RecipeFieldSU.conj_mem_recIU h hd1 r
  have hconj : GGRawFieldConj p (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))) :=
    RecipeFieldSpU.ggRawFieldConj_unitary (K := 𝕂) h h𝕂 hd hq hp hp2
  have hG1 : ∀ u ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)),
      GGL45IsPElt p u → ∃ r : LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)),
        u = MulAut.conj r := by
    intro u hu hpu
    obtain ⟨k, hk⟩ := hpu
    obtain ⟨r, hr⟩ := kgLangC_conjImage_pow_inner_unitary hd1 𝕂 h𝕂 u hu
    have hmem : u ∈ (MulAut.conj :
        LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))).range :=
      kgLangC_mem_of_pow_mem hp hpd
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))).range
        ⟨r, hr.symm⟩ hk
    obtain ⟨r', hr'⟩ := hmem
    exact ⟨r', hr'.symm⟩
  have hT : ∀ J' : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))),
      (J' : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))))) =
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
          (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)) →
      ∀ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))),
        orderOf f = p → KGLangTorusInput p J' (MulAut.conj f).toMonoidHom := by
    intro J' hJ' f hf hfo
    exact kgLangC_torusInput_unitary hp hp2 hd hpd hq 𝕂 h𝕂 J' hJ' hf hfo
  have hM : KGLangTorusMPart p (LargeEvenProj (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
        (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))) :=
    kgLangTorusMPart_of_inner hp hs hna hcyc hconj hinn hG1 hT (by
      intro hfin θ hcomm
      letI := hfin
      exact hZ θ hcomm)
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  letI := hfin
  have hcyc' := hcyc hs hna
  obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hcyc'
  have hα₀J : kgInducedAut θ α₀ ∉ J := by
    intro h
    exact hα₀I (hJI ▸ h)
  have hAS : ∀ α ∈ A, kgInducedAut θ α ∈ S := by
    intro α hα
    obtain ⟨u, huI, f, hfF, huf⟩ := hAI α hα
    apply hpS (kgInducedAut θ α)
    · rw [huf]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_union_left
          (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n))) : Set _)
          huI))
        (Subgroup.closure_mono (fun _ hx => Set.mem_union_right
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) 𝕂 (2 ^ n)))
            (LargeEvenGUSet (Fin d) 𝕂 (2 ^ n))) hx) hfF)
    · exact ⟨1, by rw [pow_one, ← map_pow, hA.2 α hα, map_one]⟩
  refine ⟨?_, hM θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I⟩
  intro α hα
  obtain ⟨k, hk⟩ := kgLangLT1_decomp hp θ hJS hN hcycS hA hAS hα₀ hα₀J α hα
  exact ⟨k, hJI ▸ hk⟩
end CFSG.StandardType
