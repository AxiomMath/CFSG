module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
import CFSG.GH74.GLS.LU.Local.L3InvUni
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L3Facts
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup Matrix CFSG.Open CFSG.RankThree.CentralCover CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.GH74.GLS.IVK
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen
open CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj
open CFSG.GH74.GLS.LU.Local.L3InvUni
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {q : ℕ}

omit [Finite F] in
private lemma odd_card_ker_statedSU {p f : ℕ} (h : UnitaryFieldData p f F) :
    Odd (Nat.card (statedProjMk (StatedSU 3 (p ^ f) F)).ker) := by
  have hker : Nat.card (statedProjMk (StatedSU 3 (p ^ f) F)).ker =
      Nat.gcd 3 (p ^ f + 1) := by
    have := (CFSG.LinearGroups.unitary_scalar_kernel h.prime h.card_eq_sq (n := 3)
      (by norm_num)).2.2
    rw [← this, statedProjMk, QuotientGroup.ker_mk']
  rw [hker]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)

omit [Finite F] in
private lemma orderOf_statedProjMk_of_orderOf_two {p f : ℕ} (h : UnitaryFieldData p f F)
    {a : StatedSU 3 (p ^ f) F} (ha : orderOf a = 2) :
    orderOf (statedProjMk (StatedSU 3 (p ^ f) F) a) = 2 := by
  have hpow : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hpow, map_one]
  · intro h1
    have hmem : a ∈ (statedProjMk (StatedSU 3 (p ^ f) F)).ker := h1
    have hdvd : orderOf a ∣ Nat.card (statedProjMk (StatedSU 3 (p ^ f) F)).ker :=
      Subgroup.orderOf_dvd_natCard _ hmem
    rw [ha] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_ker_statedSU h))
      (even_iff_two_dvd.mpr hdvd)

omit [Finite F] in
private def t1GL (F : Type) [Field F] : GL (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], !![-1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

private lemma t1GL_sq (F : Type) [Field F] : t1GL F ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t1GL, Matrix.mul_apply, Fin.sum_univ_three]

private lemma t1GL_ne_one (F : Type) [Field F] : t1GL F ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 2) h
  simp [t1GL] at this

omit [Finite F] in
private lemma t1GL_mem {p f : ℕ} (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) :
    t1GL F ∈ unitarySU p f F 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · simp [t1GL, Matrix.det_fin_three]
  · have hq0 : p ^ f ≠ 0 := by
      rintro h0
      rw [h0] at hq
      exact absurd hq (by decide)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t1GL, Matrix.mul_apply, Fin.sum_univ_three, h.bar_apply, hq.neg_one_pow,
        zero_pow hq0]

theorem psu3_orderOf_uniU₀ (hq : Odd q) (hF : Nat.card F = q ^ 2) : orderOf (uniU₀ F hq) = 2 := by
  obtain ⟨p, f, h, rfl, hp2⟩ := CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj.exists_unitaryFieldData hq hF
  let t : StatedSU 3 (p ^ f) F :=
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
  have ht : uniU₀ F hq = statedProjMk (StatedSU 3 (p ^ f) F) t := rfl
  rw [ht]
  refine orderOf_statedProjMk_of_orderOf_two h ?_
  have htmat : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 2 :=
    dgn_oddDiag₃ F
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_data h hp2
  have hdgn : dgn F 2 * dgn F 2 = 1 := by
    rw [dgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, sq, htmat, hdgn,
      OneMemClass.coe_one, Units.val_one]
  have hneg : (-1 : F) ≠ 1 := by
    intro hneg
    have htwo : (2 : F) = 0 := by
      have h := congrArg (fun x : F => x + 1) hneg
      norm_num at h ⊢
      exact h.symm
    exact h2 htwo
  have ht1 : t ≠ 1 := by
    intro h1
    have h11 := congrArg (fun g : StatedSU 3 (p ^ f) F =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h1
    simp [t, oddDiag₃] at h11
    exact hneg h11
  exact orderOf_eq_prime ht2 ht1

theorem psu3_conj (hq : Odd q) (hF : Nat.card F = q ^ 2) (t : StatedProj (StatedSU 3 q F))
    (ht : orderOf t = 2) : ∃ g : StatedProj (StatedSU 3 q F), g * uniU₀ F hq * g⁻¹ = t := by
  obtain ⟨p, f, h, rfl, hp2⟩ := CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj.exists_unitaryFieldData hq hF
  let t' : StatedSU 3 (p ^ f) F :=
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
  have hρt : uniU₀ F hq = statedProjMk (StatedSU 3 (p ^ f) F) t' := rfl
  let φ := unitaryPSUEquiv h (n := 3) (by norm_num)
  have hs : orderOf (φ.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.RankThree.Classical.isConj_unitaryProj_unitaryInvT h hp2 hs)
  have hbridge : (CFSG.RankThree.Classical.unitaryInvT h : StatedSU 3 (p ^ f) F) = t' := by
    apply Subtype.ext
    apply Units.ext
    rw [CFSG.RankThree.Classical.coe_unitaryInvT, negNegOneDiag_eq]
    rfl
  have hφπ : φ (unitaryProj h 3 (CFSG.RankThree.Classical.unitaryInvT h)) = uniU₀ F hq := by
    rw [unitaryPSUEquiv_unitaryProj h (by norm_num)]
    rw [hbridge, hρt]
    rfl
  refine ⟨φ c⁻¹, ?_⟩
  calc
    φ c⁻¹ * uniU₀ F hq * (φ c⁻¹)⁻¹
        = φ (c⁻¹ * unitaryProj h 3 (CFSG.RankThree.Classical.unitaryInvT h) * c) := by
          rw [← hφπ]
          simp
    _ = φ (φ.symm t) := by
      congr 1
      calc c⁻¹ * unitaryProj h 3 (CFSG.RankThree.Classical.unitaryInvT h) * c
          = c⁻¹ * (c * φ.symm t * c⁻¹) * c := by rw [hc]
        _ = φ.symm t := by group
    _ = t := φ.apply_symm_apply t

theorem psu3_quasi (hq : Odd q) (hq5 : 5 ≤ q) (hF : Nat.card F = q ^ 2) :
    CFSG.Open.IsQuasisimple ↥(derivedCent (uniU₀ F hq)) := by
  obtain ⟨p, f, h, rfl, hp2⟩ := CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj.exists_unitaryFieldData hq hF
  let t : StatedSU 3 (p ^ f) F :=
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
  let ρ := statedProjMk (StatedSU 3 (p ^ f) F)
  have hρt : uniU₀ F hq = ρ t := rfl
  have ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 2 := dgn_oddDiag₃ F
  have hq4 : 4 ≤ p ^ f := by omega
  let B := (coordBlock p f F 2).map ρ
  have hQ : CFSG.IsQuasisimple ↥B := isQuasisimple_block_map h 2 hq4
  have hperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hQ.1
  have hBC : B ≤ centralizer ({ρ t} : Set (StatedProj (StatedSU 3 (p ^ f) F))) :=
    block_map_le_centralizer 2 h t ht
  have hle : B ≤ derivedCent (ρ t) := by
    rw [derivedCent]
    calc B = ⁅B, B⁆ := hperf.symm
      _ ≤ ⁅centralizer ({ρ t} : Set (StatedProj (StatedSU 3 (p ^ f) F))),
          centralizer ({ρ t} : Set (StatedProj (StatedSU 3 (p ^ f) F)))⁆ :=
        Subgroup.commutator_mono hBC hBC
  have hder_le : derivedCent (ρ t) ≤ B := by
    unfold derivedCent
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨g, rfl⟩ := statedProjMk_surjective _ x
    obtain ⟨g', rfl⟩ := statedProjMk_surjective _ y
    have hgc : g ∈ centralizer ({t} : Set (StatedSU 3 (p ^ f) F)) :=
      mem_centralizer_of_mat_commute 2 t g ht (commute_of_mem_centralizer 2 t g ht hx)
    have hgc' : g' ∈ centralizer ({t} : Set (StatedSU 3 (p ^ f) F)) :=
      mem_centralizer_of_mat_commute 2 t g' ht (commute_of_mem_centralizer 2 t g' ht hy)
    exact ⟨⁅g, g'⁆, commutator_mem_coordBlock h hp2 2 t g g' ht hgc hgc',
      map_commutatorElement ρ g g'⟩
  have hder : derivedCent (ρ t) = B := le_antisymm hder_le hle
  rw [hρt, hder]
  exact ⟨Group.isPerfect_def.mp hQ.1, hQ.2.1⟩

theorem psu3_gen (hq : Odd q) (hq5 : 5 ≤ q) (hF : Nat.card F = q ^ 2)
    (t : StatedProj (StatedSU 3 q F)) (ht : orderOf t = 2) (hc : uniU₀ F hq * t = t * uniU₀ F hq)
    (hne : uniU₀ F hq ≠ t) : derivedCent (uniU₀ F hq) ⊔ derivedCent t = ⊤ := by
  obtain ⟨g, hg1, hg2⟩ := CFSG.GH74.GLS.IVK.Proofs2.uniConj F hq hF (uniU₀ F hq) t
    (psu3_orderOf_uniU₀ hq hF) ht hne hc
  let φ : StatedProj (StatedSU 3 q F) ≃* StatedProj (StatedSU 3 q F) := MulAut.conj g
  have hφ1 : φ (uniU₀ F hq) = uniU₀ F hq := by
    rw [MulAut.conj_apply]; exact hg1
  have hφ2 : φ t = uniU₀' F hq := by
    rw [MulAut.conj_apply]; exact hg2
  have h1 : (Ez (uniU₀ F hq)).map φ.toMonoidHom = Ez (uniU₀ F hq) := by
    rw [Ez_map φ (uniU₀ F hq), hφ1]
  have h2 : (Ez t).map φ.toMonoidHom = Ez (uniU₀' F hq) := by
    rw [Ez_map φ t, hφ2]
  have hgen := (uniGen F hq hF).1 (by omega : 3 < q)
  have hgen' : Subgroup.closure
      ((Ez (uniU₀ F hq) : Set (StatedProj (StatedSU 3 q F))) ∪
        (Ez t : Set (StatedProj (StatedSU 3 q F)))) = ⊤ :=
    closure_union_eq_top_of_map (K := StatedProj (StatedSU 3 q F))
      (X := StatedProj (StatedSU 3 q F)) φ (Ez (uniU₀ F hq)) (Ez t)
      (Ez (uniU₀ F hq)) (Ez (uniU₀' F hq)) h1 h2 hgen
  have hEz_le : ∀ z : StatedProj (StatedSU 3 q F), Ez z ≤ derivedCent z := by
    intro z
    let C := centralizer ({z} : Set (StatedProj (StatedSU 3 q F)))
    have hlayer : CFSG.layer ↥C ≤ ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ := by
      calc CFSG.layer ↥C = ⁅CFSG.layer ↥C, CFSG.layer ↥C⁆ :=
          CFSG.LocalCores.layer_perfect.symm
        _ ≤ ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ :=
          Subgroup.commutator_mono le_top le_top
    have hmap_le : (CFSG.layer ↥C).map C.subtype ≤ derivedCent z := by
      rw [derivedCent]
      calc (CFSG.layer ↥C).map C.subtype
          ≤ (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆).map C.subtype :=
            Subgroup.map_mono hlayer
        _ = ⁅C, C⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    intro x hx
    rw [Ez] at hx
    exact hmap_le hx
  have hgen_der : Subgroup.closure
      ((derivedCent (uniU₀ F hq) : Set (StatedProj (StatedSU 3 q F))) ∪
        (derivedCent t : Set (StatedProj (StatedSU 3 q F)))) = ⊤ := by
    rw [eq_top_iff, ← hgen']
    apply Subgroup.closure_mono
    exact Set.union_subset_union (hEz_le _) (hEz_le _)
  rwa [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq] at hgen_der

theorem psu3_four (hq : Odd q) (hF : Nat.card F = q ^ 2) :
    ∃ g : StatedProj (StatedSU 3 q F), orderOf (uniU₀ F hq * (g * uniU₀ F hq * g⁻¹)) = 4 := by
  obtain ⟨p, f, h, rfl, hp2⟩ := CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj.exists_unitaryFieldData hq hF
  let t : StatedSU 3 (p ^ f) F :=
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
  let ρ := statedProjMk (StatedSU 3 (p ^ f) F)
  have hρt : uniU₀ F hq = ρ t := rfl
  have ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dgn F 2 := dgn_oddDiag₃ F
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, sq, ht]
    have hdgn : dgn F 2 * dgn F 2 = 1 := by
      rw [dgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hdgn, OneMemClass.coe_one, Units.val_one]
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_data h hp2
  have hneg : (-1 : F) ≠ 1 := by
    intro h1
    have htwo : (2 : F) = 0 := by
      have h := congrArg (fun x : F => x + 1) h1
      norm_num at h ⊢
      exact h.symm
    exact h2 htwo
  have ht1 : t ≠ 1 := by
    intro h1
    have h11 := congrArg (fun g : StatedSU 3 (p ^ f) F =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h1
    simp [t, oddDiag₃] at h11
    exact hneg h11
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  let T1 : StatedSU 3 (p ^ f) F := ⟨t1GL F, t1GL_mem h hq⟩
  have hT1sq : T1 ^ 2 = 1 := by
    apply Subtype.ext
    exact t1GL_sq (F := F)
  have hT1ne : T1 ≠ 1 := by
    intro e
    exact t1GL_ne_one (F := F)
      (congrArg (fun x : StatedSU 3 (p ^ f) F => (x : GL (Fin 3) F)) e)
  have hT1ord : orderOf T1 = 2 := orderOf_eq_prime hT1sq hT1ne
  have hπT1ord : orderOf (ρ T1) = 2 :=
    orderOf_statedProjMk_of_orderOf_two h hT1ord
  obtain ⟨g, hg⟩ := psu3_conj hq hF (ρ T1) hπT1ord
  let u : StatedSU 3 (p ^ f) F := t * T1
  let s1 : StatedSU 3 (p ^ f) F :=
    ⟨oddDiag₁ F, Subgroup.subset_closure ⟨det_oddDiag₁ F, unitary_oddDiag₁ hq⟩⟩
  have hu2 : u ^ 2 = s1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, t, T1, s1, t1GL, oddDiag₃, oddDiag₁, sq, Matrix.mul_apply,
        Fin.sum_univ_three]
  have hs1sq : s1 ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s1, oddDiag₁, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hs1ne : s1 ≠ 1 := by
    intro e
    have h11 := congrArg (fun g : StatedSU 3 (p ^ f) F =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) e
    simp [s1, oddDiag₁] at h11
    exact hneg h11
  have hu4 : u ^ 4 = 1 := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by group
      _ = s1 ^ 2 := by rw [hu2]
      _ = 1 := hs1sq
  have hu2ord : orderOf (u ^ 2) = 2 := by
    rw [hu2]
    exact orderOf_eq_prime hs1sq hs1ne
  have h2ne : (ρ u) ^ 2 ≠ 1 := by
    intro h2u
    have hmem : u ^ 2 ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact h2u
    have hdvd : orderOf (u ^ 2) ∣ Nat.card ρ.ker :=
      Subgroup.orderOf_dvd_natCard ρ.ker hmem
    rw [hu2ord] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_ker_statedSU h))
      (even_iff_two_dvd.mpr hdvd)
  have h4 : (ρ u) ^ 4 = 1 := by
    rw [← map_pow, hu4, map_one]
  have hord : orderOf (ρ u) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2ne h4
    simpa using this
  have hprod : uniU₀ F hq * (g * uniU₀ F hq * g⁻¹) = ρ u := by
    rw [hg, hρt, ← map_mul]
  exact ⟨g, hprod.symm ▸ hord⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
