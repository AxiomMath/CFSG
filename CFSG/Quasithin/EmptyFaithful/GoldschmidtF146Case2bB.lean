module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bA
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
  CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

section Sp4

variable {K : Type} [Field K]

theorem comm_of_mul_eq {G : Type*} [Group G] {h t t' : G} (e : h * t = t' * h) :
    ⁅h, t⁆ = t' * t⁻¹ := by
  rw [commutatorElement_def, e]
  group

theorem exists_units_ne_one (hK : ∃ s : Finset K, s.card = 4) : ∃ u : Kˣ, (u : K) ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := hK
  by_contra h
  push Not at h
  have hsub : s ⊆ ({0, 1} : Finset K) := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have := h (Units.mk0 x hx0)
      simpa using Or.inr this
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
  omega

@[expose] noncomputable def diagSL (u : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

@[expose] def unitriSL (a : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨unitri a, det_unitri a⟩

theorem torusHom_eq_spLevi_one (u : Kˣ) :
    SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![u, u⁻¹] = spLevi 1 (diagSL u) := by
  have h1 : (spLevi (K := K) 1) = SymplecticTorusWeyl.leviSp.comp
      Matrix.SpecialLinearGroup.toGL := by simp [spLevi]
  rw [h1]
  show SymplecticTorusWeyl.leviSp (TauCeti.diagGL ![u, u⁻¹]) =
    SymplecticTorusWeyl.leviSp (Matrix.SpecialLinearGroup.toGL (diagSL u))
  congr 1
  apply Units.ext
  rw [TauCeti.diagGL_coe]
  show Matrix.diagonal (fun i => ((![u, u⁻¹] i : Kˣ) : K)) = (diagSL u : Matrix (Fin 2) (Fin 2) K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagSL, Matrix.diagonal]

theorem lam_eq_spLevi_one (a : K) : SymplecticFour.lam a = spLevi 1 (unitriSL a) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_lam]
  show _ = spMat (spLevi 1 (unitriSL a))
  rw [spMat_leviSp_one]
  have : (((unitriSL a)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      unitri (-a) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitriSL, unitri]
  rw [this]
  rfl

theorem torusHom_eq_spLevi_zero (u : Kˣ) :
    SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![1, u] = spLevi 0 (diagSL u) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [SymplecticTorusWeyl.coe_torusHom]
  have h0 : (spLevi (K := K) 0) = SymplecticTorusWeyl.lam 1 := by simp [spLevi]
  rw [h0, SymplecticTorusWeyl.coe_lam]
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [SymplecticTorusWeyl.pairMat, diagSL, Matrix.diagonal]

theorem tauS_zero_zero_eq_spLevi_zero (d : K) :
    tauS 0 0 d = spLevi 0 (Matrix.SpecialLinearGroup.transvection
      (i := (0 : Fin 2)) (j := 1) (by decide) d) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauS]
  have h0 : (spLevi (K := K) 0) = SymplecticTorusWeyl.lam 1 := by simp [spLevi]
  rw [h0, SymplecticTorusWeyl.coe_lam]
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [SymplecticTorusWeyl.pairMat, sym2, Matrix.SpecialLinearGroup.transvection,
      Matrix.transvection]

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem unipotent_le_of_gens {W : Subgroup (StatedSp 2 K)}
    (hb : ∀ b, tauS b 0 0 ∈ W) (hc : ∀ c, tauS 0 c 0 ∈ W) (hd : ∀ d, tauS 0 0 d ∈ W)
    (ha : ∀ a, SymplecticFour.lam a ∈ W) : unipotent 2 K ≤ W := by
  intro g hg
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.mp hg
  refine mul_mem ?_ (ha a)
  rw [tau_eq_tauS hC]
  have : tauS (C 0 0) (C 0 1) (C 1 1) =
      tauS (C 0 0) 0 0 * tauS 0 (C 0 1) 0 * tauS 0 0 (C 1 1) := by
    rw [tauS_mul_tauS, tauS_mul_tauS]
    simp
  rw [this]
  exact mul_mem (mul_mem (hb _) (hc _)) (hd _)

omit [Finite K] [CharP K 2] in
theorem unipotent_le_Q2 (j : Fin 2) {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K) : g ∈ Q2 K j :=
  borelSubgroup_le_Q2 j (unipotent_le_borelSubgroup hg)

omit [Finite K] in
theorem tauS_sq_mem {j : Fin 2} {a : K} (ha : SymplecticFour.lam a ∈ perfectCore (Q2 K j)) :
    tauS (a ^ 2) a 0 ∈ perfectCore (Q2 K j) := by
  have h := comm_mem_perfectCore_left (unipotent_le_Q2 j (tauS_mem_unipotent 0 0 (1 : K))) ha
  rwa [commutatorElement_lam_tauS, mul_one, mul_one] at h

omit [Finite K] [CharP K 2] in
theorem tauS_comm_mem {j : Fin 2} {h : StatedSp 2 K} (hh : h ∈ perfectCore (Q2 K j))
    {b c d b' c' d' B C D : K} (e : h * tauS b c d = tauS b' c' d' * h)
    (hB : B = b' - b) (hC : C = c' - c) (hD : D = d' - d) :
    tauS B C D ∈ perfectCore (Q2 K j) := by
  subst hB hC hD
  have h1 := comm_mem_perfectCore_left (unipotent_le_Q2 j (tauS_mem_unipotent b c d)) hh
  rwa [comm_of_mul_eq e, tauS_inv, tauS_mul_tauS, ← sub_eq_add_neg, ← sub_eq_add_neg,
    ← sub_eq_add_neg] at h1

omit [Finite K] in
theorem unipotent_le_perfectCore_Q2_one (hK : ∃ s : Finset K, s.card = 4) :
    unipotent 2 K ≤ perfectCore (Q2 K 1) := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hK
  have hu2 : (u : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (sq_ne_one_of_charTwo hu)
  have hv2 : ((u⁻¹ : Kˣ) : K) ^ 2 - 1 ≠ 0 := by
    refine sub_ne_zero.mpr (sq_ne_one_of_charTwo fun h => hu ?_)
    have := congrArg (fun x : K => x⁻¹) h
    simpa using this
  have hl : ∀ a, SymplecticFour.lam a ∈ perfectCore (Q2 K 1) := fun a => by
    rw [lam_eq_spLevi_one]
    exact spLevi_mem_perfectCore hK 1 _
  have ht : SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![u, u⁻¹] ∈ perfectCore (Q2 K 1) := by
    rw [torusHom_eq_spLevi_one]
    exact spLevi_mem_perfectCore hK 1 _
  have hb : ∀ b, tauS b 0 0 ∈ perfectCore (Q2 K 1) := fun b =>
    tauS_comm_mem ht (b := b / ((u : K) ^ 2 - 1)) (c := 0) (d := 0)
      (b' := (u : K) ^ 2 * (b / ((u : K) ^ 2 - 1))) (c' := 0) (d' := 0)
      (by rw [torusHom_mul_tauS]; simp) (by field_simp) (by simp) (by simp)
  have hd : ∀ d, tauS 0 0 d ∈ perfectCore (Q2 K 1) := fun d =>
    tauS_comm_mem ht (b := 0) (c := 0) (d := d / (((u⁻¹ : Kˣ) : K) ^ 2 - 1))
      (b' := 0) (c' := 0) (d' := ((u⁻¹ : Kˣ) : K) ^ 2 * (d / (((u⁻¹ : Kˣ) : K) ^ 2 - 1)))
      (by rw [torusHom_mul_tauS]; simp) (by simp) (by simp) (by field_simp)
  have hc : ∀ c, tauS 0 c 0 ∈ perfectCore (Q2 K 1) := fun a => by
    have h1 := tauS_sq_mem (hl a)
    have h2 : tauS 0 a 0 = tauS (a ^ 2) a 0 * (tauS (a ^ 2) 0 0)⁻¹ := by
      rw [tauS_inv, tauS_mul_tauS]
      simp
    rw [h2]
    exact mul_mem h1 (inv_mem (hb _))
  exact unipotent_le_of_gens hb hc hd hl

theorem unipotent_le_perfectCore_Q2_zero (hK : ∃ s : Finset K, s.card = 4) :
    unipotent 2 K ≤ perfectCore (Q2 K 0) := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hK
  have hu1 : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hv1 : ((u⁻¹ : Kˣ) : K) - 1 ≠ 0 := by
    refine sub_ne_zero.mpr fun h => hu ?_
    have := congrArg (fun x : K => x⁻¹) h
    simpa using this
  have hd : ∀ d, tauS 0 0 d ∈ perfectCore (Q2 K 0) := fun d => by
    rw [tauS_zero_zero_eq_spLevi_zero]
    exact spLevi_mem_perfectCore hK 0 _
  have ht : SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![1, u] ∈ perfectCore (Q2 K 0) := by
    rw [torusHom_eq_spLevi_zero]
    exact spLevi_mem_perfectCore hK 0 _
  have hc : ∀ c, tauS 0 c 0 ∈ perfectCore (Q2 K 0) := fun c =>
    tauS_comm_mem ht (b := 0) (c := c / ((u : K) - 1)) (d := 0)
      (b' := 0) (c' := (u : K) * (c / ((u : K) - 1))) (d' := 0)
      (by rw [torusHom_mul_tauS]; simp) (by simp) (by field_simp) (by simp)
  have hl : ∀ a, SymplecticFour.lam a ∈ perfectCore (Q2 K 0) := fun a => by
    have e : SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![1, u] * SymplecticFour.lam
        (a / (((u⁻¹ : Kˣ) : K) - 1)) = SymplecticFour.lam
        (((u⁻¹ : Kˣ) : K) * (a / (((u⁻¹ : Kˣ) : K) - 1))) *
          SymplecticTorusWeyl.torusHom (r := 2) (k := K) ![1, u] := by
      rw [torusHom_mul_lam]
      simp
    have h2 := comm_mem_perfectCore_left (unipotent_le_Q2 0 (lam_mem_unipotent
      (a / (((u⁻¹ : Kˣ) : K) - 1)))) ht
    rw [comm_of_mul_eq e, inv_lam, lam_mul] at h2
    convert h2 using 2
    field_simp
    ring
  have hb : ∀ b, tauS b 0 0 ∈ perfectCore (Q2 K 0) := fun b => by
    obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (CharP.ringChar_of_prime_eq_zero
      Nat.prime_two (CharP.cast_eq_zero K 2)) b
    have h1 := tauS_sq_mem (hl a)
    have h2 : tauS (a ^ 2) 0 0 = tauS (a ^ 2) a 0 * (tauS 0 a 0)⁻¹ := by
      rw [tauS_inv, tauS_mul_tauS]
      simp
    have h3 : tauS (a ^ 2) 0 0 ∈ perfectCore (Q2 K 0) := by
      rw [h2]
      exact mul_mem h1 (inv_mem (hc _))
    rw [ha, ← sq] at *
    exact h3
  exact unipotent_le_of_gens hb hc hd hl

theorem unipotent_le_perfectCore_Q2 (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    unipotent 2 K ≤ perfectCore (Q2 K j) := by
  fin_cases j
  · exact unipotent_le_perfectCore_Q2_zero hK
  · exact unipotent_le_perfectCore_Q2_one hK

end Sp4

end CFSG.Quasithin.F146Field.Case2b
