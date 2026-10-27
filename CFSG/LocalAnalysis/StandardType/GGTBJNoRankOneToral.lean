module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_unitary det_permGL permGL_mul_diagHom_mul_inv diagHom_unitary
  exists_orderOf_eq_norm_one expHom expHom_apply expHom_single diagHom_expHom_mem_unitarySU)
open CFSG.SectionRank.OddCover (diagHom diagHom_injective det_diagHom coe_diagHom)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped BigOperators

private def l48nO_bv : Fin 4 → Fin 6 → ZMod 3 :=
  ![![0, 0, 0, 0, 1, 2], ![0, 0, 1, 1, 2, 2], ![0, 0, 1, 2, 0, 0], ![0, 1, 2, 2, 2, 2]]

private def l48nO_sig (i j : Fin 4) : Equiv.Perm (Fin 6) :=
  match i.val, j.val with
  | 0, _ => Equiv.swap 4 5
  | 2, _ => Equiv.swap 2 3
  | 3, _ => Equiv.swap 0 1
  | _, 0 => Equiv.swap 0 3 * Equiv.swap 0 1 * Equiv.swap 0 2
  | _, 2 => Equiv.swap 0 5 * Equiv.swap 0 1 * Equiv.swap 0 4
  | _, _ => Equiv.swap 2 5 * Equiv.swap 2 3 * Equiv.swap 2 4

private theorem l48nO_bv_inv (i j : Fin 4) :
    ∃ c : ZMod 3, ∀ r : Fin 6, l48nO_bv i ((l48nO_sig i j).symm r) = -l48nO_bv i r + c := by
  fin_cases i <;> fin_cases j <;> decide

private theorem l48nO_bv_fix (i j : Fin 4) (h : j ≠ i) :
    ∃ c : ZMod 3, ∀ r : Fin 6, l48nO_bv j ((l48nO_sig i j).symm r) = l48nO_bv j r + c := by
  fin_cases i <;> fin_cases j <;> (first | exact absurd rfl h | decide)

private theorem l48nO_bv_sum_zero (i : Fin 4) : ∑ r : Fin 6, l48nO_bv i r = 0 := by
  fin_cases i <;> decide

private theorem l48nO_bv_indep :
    ∀ n : Fin 4 → ZMod 3, (∀ r : Fin 6, ∑ i : Fin 4, n i * l48nO_bv i r = 0) → n = 0 := by
  decide

private theorem l48nO_zmod3_cube (x : Multiplicative (ZMod 3)) : x ^ 3 = 1 := by
  revert x
  decide

private theorem l48nO_zmod3_nsmul_three (x : ZMod 3) : (3 : ℕ) • x = 0 := by
  revert x
  decide

private theorem l48nO_zmod3_val_zero : ∀ x : ZMod 3, x.val = 0 → x = 0 := by
  decide

private theorem l48nO_bv_zero (i : Fin 4) : l48nO_bv i (0 : Fin 6) = 0 := by
  fin_cases i <;> decide

private def l48nO_pe (n : ℕ) :
    (Fin n → Multiplicative (ZMod 3)) ≃* Multiplicative (Fin n → ZMod 3) where
  toFun a := Multiplicative.ofAdd fun i => Multiplicative.toAdd (a i)
  invFun a i := Multiplicative.ofAdd (Multiplicative.toAdd a i)
  left_inv a := by
    funext i
    simp
  right_inv a := by
    funext i
    simp
  map_mul' a b := by
    show Multiplicative.ofAdd ((fun i => Multiplicative.toAdd (a i)) +
        (fun i => Multiplicative.toAdd (b i))) =
      Multiplicative.ofAdd (fun i => Multiplicative.toAdd (a i)) *
      Multiplicative.ofAdd (fun i => Multiplicative.toAdd (b i))
    rw [ofAdd_add]

private theorem l48nO_pe_apply (n : ℕ) (a : Fin n → Multiplicative (ZMod 3)) (i : Fin n) :
    l48nO_pe n a i = Multiplicative.ofAdd (Multiplicative.toAdd (a i)) := rfl

private theorem l48nO_ofAdd_apply {n : ℕ} (f : Fin n → ZMod 3) (i : Fin n) :
    (Multiplicative.ofAdd f : Multiplicative (Fin n → ZMod 3)) i = Multiplicative.ofAdd (f i) :=
  rfl

theorem ggRankOne_toral_four {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}
    (h3 : 3 ∣ 2 ^ m + 1) (hL : commutator L = ⊤)
    (hlab : GGHasLabel (⟨.twA, 5, m⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L)) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧
      ∀ e ∈ E, (∀ l ∈ L, e * l = l * e) → e = 1 := by
  classical
  dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeUnitary] at hlab
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eθ⟩⟩ := hlab
  letI := hKfield
  letI := hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      norm_num at h3
    · exact hm
  have hKd : UnitaryFieldData 2 m K :=
    ⟨Nat.prime_two, hm1, by rw [hKcard, ← pow_mul, mul_comm]⟩
  haveI hchar : CharP K 2 := hKd.charP
  obtain ⟨ω, hωorder, hωnorm⟩ := exists_orderOf_eq_norm_one hKd Nat.prime_three h3
  have hω3 : ω ^ 3 = 1 := by rw [← hωorder]; exact pow_orderOf_eq_one ω
  let H : Subgroup (GL (Fin 6) K) := LargeEvenSUGroup (Fin 6) K (2 ^ m)
  have hH : H = unitarySU 2 m K 6 := rfl
  let cubeH : Multiplicative (ZMod 3) →* Kˣ := TableBSymp.zmodPowHom hω3
  let cube : ZMod 3 → Kˣ := fun x => cubeH (Multiplicative.ofAdd x)
  have cube_add : ∀ x y : ZMod 3, cube (x + y) = cube x * cube y := by
    intro x y
    simp only [cube, cubeH, ofAdd_add, map_mul]
  have cube_zero : cube 0 = 1 := by simp [cube]
  have cube_neg : ∀ x : ZMod 3, cube (-x) = (cube x)⁻¹ := by
    intro x
    simp only [cube, cubeH, ofAdd_neg, map_inv]
  have cube_val : ∀ x : ZMod 3, (cube x : K) = (ω : K) ^ x.val := by
    intro x
    simp only [cube, cubeH, TableBSymp.zmodPowHom_apply, toAdd_ofAdd, Units.val_pow_eq_pow_val]
  have cube_nsmul : ∀ (n : ℕ) (x : ZMod 3), cube x ^ n = cube (n • x) := by
    intro n x
    induction n with
    | zero => simp [cube_zero]
    | succ n ih => rw [pow_succ, ih, ← cube_add, succ_nsmul]
  have cube_eq_one : ∀ x : ZMod 3, cube x = 1 → x = 0 := by
    intro x hx
    have h2 : cube x = ω ^ x.val := by
      simp only [cube, cubeH, TableBSymp.zmodPowHom_apply, toAdd_ofAdd]
    rw [h2] at hx
    have hdvd : orderOf ω ∣ x.val := orderOf_dvd_of_pow_eq_one hx
    rw [hωorder] at hdvd
    exact l48nO_zmod3_val_zero x (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt x))
  have prod_cube : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ZMod 3),
      s.prod (fun r => cube (f r)) = cube (s.sum f) := by
    intro ι _ s f
    induction s using Finset.induction_on with
    | empty => simp [cube_zero]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, cube_add]
  let c : Fin 4 → Fin 6 → Kˣ := fun i r => cube (l48nO_bv i r)
  have hc3 : ∀ i r, c i r ^ 3 = 1 := by
    intro i r
    show cube (l48nO_bv i r) ^ 3 = 1
    rw [cube_nsmul, l48nO_zmod3_nsmul_three, cube_zero]
  have hcprod : ∀ i : Fin 4, ∏ r : Fin 6, c i r = 1 := by
    intro i
    have h1 : (∏ r : Fin 6, c i r) = cube (∑ r : Fin 6, l48nO_bv i r) := by
      simp only [c]
      exact prod_cube Finset.univ (l48nO_bv i)
    rw [h1, l48nO_bv_sum_zero i, cube_zero]
  have hcnormK : ∀ i r, c i r ^ (2 ^ m + 1) = 1 := by
    intro i r
    show cube (l48nO_bv i r) ^ (2 ^ m + 1) = 1
    rw [cube_nsmul]
    have hzero : (2 ^ m + 1) • l48nO_bv i r = 0 := by
      obtain ⟨k, hk⟩ := h3
      rw [hk, mul_nsmul, l48nO_zmod3_nsmul_three, smul_zero]
    rw [hzero, cube_zero]
  have hmem : ∀ i : Fin 4, diagHom 6 (c i) ∈ H := by
    intro i
    rw [hH]
    have h := diagHom_expHom_mem_unitarySU hKd c hc3 hcprod hcnormK
      (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3)))
    rwa [expHom_single] at h
  have hperm_mem : ∀ σ : Equiv.Perm (Fin 6), permGL σ ∈ H := by
    intro σ
    rw [hH, mem_unitarySU_iff hKd]
    refine ⟨?_, permGL_unitary hKd σ⟩
    rw [det_permGL]
    have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hneg : (-1 : K) = 1 := by linear_combination -h2K
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]; simp
    · rw [h]; simp [hneg]
  let t : Fin 4 → ↥H := fun i => ⟨diagHom 6 (c i), hmem i⟩
  have ht3 : ∀ i : Fin 4, t i ^ 3 = 1 := by
    intro i
    apply Subtype.ext
    show (diagHom 6 (c i)) ^ 3 = 1
    rw [← map_pow]
    have h1 : c i ^ 3 = 1 := by
      funext r
      exact hc3 i r
    rw [h1, map_one]
  have htcomm : ∀ i j : Fin 4, Commute (t i) (t j) := by
    intro i j
    apply Subtype.ext
    show diagHom 6 (c i) * diagHom 6 (c j) = diagHom 6 (c j) * diagHom 6 (c i)
    rw [← map_mul, ← map_mul, mul_comm]
  let R := LargeEvenProj H
  have hmemH : ∀ a : Multiplicative (Fin 4 → ZMod 3), diagHom 6 (expHom c hc3 a) ∈ H := by
    intro a
    rw [hH]
    exact diagHom_expHom_mem_unitarySU hKd c hc3 hcprod hcnormK a
  let τDiag : Multiplicative (Fin 4 → ZMod 3) →* ↥H :=
    ((diagHom 6).comp (expHom c hc3)).codRestrict H hmemH
  let τDiag' : (Fin 4 → Multiplicative (ZMod 3)) →* ↥H :=
    τDiag.comp (l48nO_pe 4).toMonoidHom
  let τ : (Fin 4 → Multiplicative (ZMod 3)) →* R := (LargeEvenProjMk H).comp τDiag'
  have hτDiag' : ∀ a : (Fin 4 → Multiplicative (ZMod 3)),
      (τDiag' a : GL (Fin 6) K) = diagHom 6 (expHom c hc3 (l48nO_pe 4 a)) := by
    intro a
    have hτDiageq : τDiag' = τDiag.comp (l48nO_pe 4).toMonoidHom := rfl
    rw [hτDiageq, MonoidHom.comp_apply]
    rfl
  have htorusBasis : ∀ i : Fin 4, TableBSymp.torusBasis τ i = LargeEvenProjMk H (t i) := by
    intro i
    have hpe : l48nO_pe 4 (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3))) =
        Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) := by
      funext k
      rw [l48nO_pe_apply, l48nO_ofAdd_apply]
      by_cases hk : k = i
      · subst hk
        simp only [Pi.mulSingle_eq_same, toAdd_ofAdd, Pi.single_eq_same]
        rfl
      · simp only [Pi.mulSingle_eq_of_ne hk, toAdd_one, ofAdd_zero, Pi.single_eq_of_ne hk]
        rfl
    have hτeq : τ = (LargeEvenProjMk H).comp τDiag' := rfl
    have hτDiageq : τDiag' = τDiag.comp (l48nO_pe 4).toMonoidHom := rfl
    have hτDiageq2 : τDiag = ((diagHom 6).comp (expHom c hc3)).codRestrict H hmemH := rfl
    rw [TableBSymp.torusBasis, hτeq, MonoidHom.comp_apply, hτDiageq, MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    show diagHom 6 (expHom c hc3 ((l48nO_pe 4) (Pi.mulSingle i
      (Multiplicative.ofAdd (1 : ZMod 3))))) = diagHom 6 (c i)
    rw [hpe, expHom_single]
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hscal : τDiag' a ∈ (LargeEvenScalars (Fin 6) K).subgroupOf H := by
      have h1 : LargeEvenProjMk H (τDiag' a) = 1 := ha
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hscalGL : (τDiag' a : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K :=
      Subgroup.mem_subgroupOf.mp hscal
    rw [hτDiag' a] at hscalGL
    have hscal_exists : ∃ lam : Kˣ, (fun r : Fin 6 => expHom c hc3
        (l48nO_pe 4 a) r) = fun _ => lam := by
      rw [largeEvenScalars_def] at hscalGL
      obtain ⟨lam, hlam⟩ := hscalGL
      refine ⟨lam, ?_⟩
      funext r
      have hrr := congrArg (fun A : GL (Fin 6) K =>
        (A : Matrix (Fin 6) (Fin 6) K) r r) hlam
      apply Units.ext
      simpa [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom] using hrr.symm
    obtain ⟨lam, hlam⟩ := hscal_exists
    have hd : ∀ r : Fin 6, expHom c hc3 (l48nO_pe 4 a) r =
        cube (∑ i : Fin 4, (Multiplicative.toAdd (a i)).val • l48nO_bv i r) := by
      intro r
      rw [expHom_apply]
      simp only [l48nO_pe, toAdd_ofAdd, c, cube_nsmul]
      exact prod_cube Finset.univ
        (fun i : Fin 4 => (Multiplicative.toAdd (a i)).val • l48nO_bv i r)
    have hlam1 : lam = 1 := by
      have h0 := congrFun hlam 0
      rw [hd 0] at h0
      have hb0 : ∀ i : Fin 4, l48nO_bv i (0 : Fin 6) = 0 := l48nO_bv_zero
      simp only [hb0, nsmul_zero, Finset.sum_const_zero, cube_zero] at h0
      exact h0.symm
    have hvec : ∀ r : Fin 6, ∑ i : Fin 4,
        (Multiplicative.toAdd (a i)).val • l48nO_bv i r = 0 := by
      intro r
      have hr := congrFun hlam r
      rw [hd r, hlam1] at hr
      exact cube_eq_one _ hr
    have hvec' : ∀ r : Fin 6, ∑ i : Fin 4,
        Multiplicative.toAdd (a i) * l48nO_bv i r = 0 := by
      intro r
      have hr := hvec r
      simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using hr
    have ha0 : (fun i : Fin 4 => Multiplicative.toAdd (a i)) = 0 :=
      l48nO_bv_indep _ hvec'
    funext i
    have hi := congrFun ha0 i
    rw [Pi.zero_apply] at hi
    rw [← ofAdd_toAdd (a i), hi, ofAdd_zero]
    rfl
  have hfixi : ∀ i j : Fin 4, ∃ lam : Kˣ, ∀ r : Fin 6,
      c i ((l48nO_sig i j).symm r) = (c i r)⁻¹ * lam := by
    intro i j
    obtain ⟨cc, hcc⟩ := l48nO_bv_inv i j
    refine ⟨cube cc, fun r => ?_⟩
    simp only [c]
    rw [hcc r, cube_add, cube_neg]
  have hfixj : ∀ i j : Fin 4, j ≠ i → ∃ lam : Kˣ, ∀ r : Fin 6,
      c j ((l48nO_sig i j).symm r) = c j r * lam := by
    intro i j hij
    obtain ⟨cc, hcc⟩ := l48nO_bv_fix i j hij
    refine ⟨cube cc, fun r => ?_⟩
    simp only [c]
    rw [hcc r, cube_add]
  have hscalar_mem : ∀ lam : Kˣ, diagHom 6 (fun _ : Fin 6 => lam) ∈
      LargeEvenScalars (Fin 6) K := by
    intro lam
    rw [largeEvenScalars_def]
    refine ⟨lam, ?_⟩
    apply Units.ext
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom]
    · simp [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, h, Matrix.diagonal_apply_ne]
  let wσ : Fin 4 → Fin 4 → ↥H := fun i j => ⟨permGL (l48nO_sig i j), hperm_mem _⟩
  let w : Fin 4 → Fin 4 → R := fun i j => LargeEvenProjMk H (wσ i j)
  have hconj_inv : ∀ i j : Fin 4, w i j * TableBSymp.torusBasis τ i * (w i j)⁻¹ =
      (TableBSymp.torusBasis τ i)⁻¹ := by
    intro i j
    obtain ⟨lam, hlam⟩ := hfixi i j
    rw [htorusBasis i]
    dsimp only [w, wσ]
    rw [← map_inv, ← map_mul, ← map_mul]
    change (QuotientGroup.mk (⟨permGL (l48nO_sig i j), hperm_mem _⟩ * t i *
      ⟨permGL (l48nO_sig i j), hperm_mem _⟩⁻¹) : R) = QuotientGroup.mk ((t i)⁻¹)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have heq : (((⟨permGL (l48nO_sig i j), hperm_mem _⟩ * t i *
        ⟨permGL (l48nO_sig i j), hperm_mem _⟩⁻¹)⁻¹ * (t i)⁻¹ : ↥H) : GL (Fin 6) K) =
        diagHom 6 (fun _ : Fin 6 => lam⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      dsimp only [t]
      rw [permGL_mul_diagHom_mul_inv]
      rw [show (diagHom 6 (c i ∘ (l48nO_sig i j).symm))⁻¹ * (diagHom 6 (c i))⁻¹ =
          diagHom 6 (fun r : Fin 6 => (c i ((l48nO_sig i j).symm r))⁻¹ * (c i r)⁻¹) by
        rw [← map_inv, ← map_inv, ← map_mul]
        rfl]
      congr 1
      funext r
      rw [hlam r]
      group
    rw [heq]
    exact hscalar_mem lam⁻¹
  have hconj_fix : ∀ i j : Fin 4, j ≠ i → w i j * TableBSymp.torusBasis τ j * (w i j)⁻¹ =
      TableBSymp.torusBasis τ j := by
    intro i j hij
    obtain ⟨lam, hlam⟩ := hfixj i j hij
    rw [htorusBasis j]
    dsimp only [w, wσ]
    rw [← map_inv, ← map_mul, ← map_mul]
    change (QuotientGroup.mk (⟨permGL (l48nO_sig i j), hperm_mem _⟩ * t j *
      ⟨permGL (l48nO_sig i j), hperm_mem _⟩⁻¹) : R) = QuotientGroup.mk (t j)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have heq : (((⟨permGL (l48nO_sig i j), hperm_mem _⟩ * t j *
        ⟨permGL (l48nO_sig i j), hperm_mem _⟩⁻¹)⁻¹ * t j : ↥H) : GL (Fin 6) K) =
        diagHom 6 (fun _ : Fin 6 => lam⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      dsimp only [t]
      rw [permGL_mul_diagHom_mul_inv]
      rw [show (diagHom 6 (c j ∘ (l48nO_sig i j).symm))⁻¹ * diagHom 6 (c j) =
          diagHom 6 (fun r : Fin 6 => (c j ((l48nO_sig i j).symm r))⁻¹ * c j r) by
        rw [← map_inv, ← map_mul]
        rfl]
      congr 1
      funext r
      rw [hlam r]
      group
    rw [heq]
    exact hscalar_mem lam⁻¹
  have hψ : Function.Surjective (ggQuotHom eθ) := ggQuotHom_surjective eθ
  have hker : (ggQuotHom eθ).ker ≤ Subgroup.center ↥L := by
    rw [ker_ggQuotHom]
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ hker (by decide : Odd 3) τ
    (fun i j => ⟨w i j, hconj_inv i j, fun hij => hconj_fix i j hij⟩)
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : τ a = 1 := by
      rw [← hσ, MonoidHom.comp_apply, ha, map_one]
    exact hτinj (by rw [h1, map_one])
  let E' : Subgroup ↥L := σ.range
  have hE'card : Nat.card E' = 3 ^ 4 := by
    change Nat.card (σ.range) = 3 ^ 4
    rw [Nat.card_congr (MonoidHom.ofInjective hσinj).toEquiv.symm,
      Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hE'ab : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      apply Subtype.ext
      show (x : ↥L) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm u v]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow]
      have ha : u ^ 3 = 1 := by
        funext i
        exact l48nO_zmod3_cube (u i)
      rw [ha, map_one]
  have hE'center : E' ⊓ Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hx⟩
    have hx1 : ggQuotHom eθ (σ a) = 1 := by
      have hx' : σ a ∈ (ggQuotHom eθ).ker := by
        rw [ker_ggQuotHom]
        exact hx
      exact hx'
    have hτa : τ a = 1 := by
      rw [← hσ, MonoidHom.comp_apply, hx1]
    have : a = 1 := hτinj (by rw [hτa, map_one])
    rw [this, map_one]
    exact Subgroup.one_mem _
  refine ⟨E'.map L.subtype, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact y.2
  · exact TableB.isElemAbelian_map hE'ab L.subtype
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE'card]
  · rintro e ⟨x, hx, rfl⟩ he
    have hxcenter : x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact (he l l.2).symm
    have : x ∈ E' ⊓ Subgroup.center ↥L := ⟨hx, hxcenter⟩
    rw [hE'center, Subgroup.mem_bot] at this
    rw [this]
    rfl

end CFSG.StandardType

end
