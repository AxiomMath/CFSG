module

public import CFSG.Quasithin.EmptyFaithful.E22PL2Psl
public import CFSG.Quasithin.EmptyFaithful.E22PL2PglA
public import CFSG.Quasithin.EmptyFaithful.E22PL2Pgl
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenCoatom

public section

namespace CFSG.Quasithin.E22L2

open CFSG.GorensteinWalter CFSG.Quasithin

theorem e22pl2sq_isOddPrimePower {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type}
    (hK : Nat.card K = p ^ 2) : IsOddPrimePower (Nat.card K) :=
  ⟨p, 2, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), by norm_num, hK⟩

theorem e22pl2sq_mod_eight {p : ℕ} (hpodd : Odd p) : p ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := hpodd
  have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  have h2 : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with h | h
    · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
    · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Odd.add_one h)) _
  obtain ⟨c, hc⟩ := h2
  omega

theorem psl2_centralizer_involution_isCoatom_sq {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {z : PSL2 K}
    (hz : orderOf z = 2) : IsCoatom (Subgroup.centralizer ({z} : Set (PSL2 K))) :=
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  CFSG.ComponentClassification.AutL2Facts.isCoatom_centralizer_involution (Fact.out : p.Prime)
    (by omega) hK (by have := e22pl2sq_mod_eight hpodd; omega) (by nlinarith) hz

theorem pgl2_centralizer_inner_involution_isCoatom_sq {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ 2)
    {z : PGL2 K} (hz : orderOf z = 2) (hzJ : z ∈ commutator (PGL2 K)) :
    IsCoatom (Subgroup.centralizer ({z} : Set (PGL2 K))) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hodd := e22pl2sq_isOddPrimePower hp5 hK
  have hcard : 3 < Nat.card K := by rw [hK]; nlinarith
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd hcard
  obtain ⟨w, rfl⟩ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range := hcomm ▸ hzJ
  have hφ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)
  have hw : orderOf w = 2 := by rw [← orderOf_injective _ hφ w]; exact hz
  have hN : (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := by
    rw [← hcomm]
    infer_instance
  exact e22pd_isCoatom_centralizer_of_index_two _ hφ hN (pgl2_psl2Range_index_eq_two K hodd) hw
    (fun x hx => CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hK hpodd two_pos hx hw)
    (psl2_centralizer_involution_isCoatom_sq hp5 hK hw)
    (CFSG.Walter.psl2_center_centralizer_involution K hK hpodd two_pos (by nlinarith) hw)

theorem nParam_psl2_sq_le_one
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) : E1.nParam (⊤ : Subgroup (PSL2 K)) ≤ 1 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨T, hT⟩ := E1.exists_isSylowIn_two (⊤ : Subgroup (PSL2 K))
  have h := (E1.nParam_le_iff (H := (⊤ : Subgroup (PSL2 K))) (n := 1) one_pos).mpr
    ((E1.inE_iff_inEFor hT).mpr (inEFor_psl2_of_coatom (e22pl2sq_isOddPrimePower hp5 hK)
      (Or.inl (by rw [hK]; exact e22pl2sq_mod_eight hpodd)) (by rw [hK]; nlinarith)
      (fun hz => psl2_centralizer_involution_isCoatom_sq hp5 hK hz) hT))
  simpa using h

theorem nParam_pgl2_sq_le_one
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) : E1.nParam (⊤ : Subgroup (PGL2 K)) ≤ 1 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have := e22pl2pgl_finite K
  obtain ⟨T, hT⟩ := E1.exists_isSylowIn_two (⊤ : Subgroup (PGL2 K))
  have h := (E1.nParam_le_iff (H := (⊤ : Subgroup (PGL2 K))) (n := 1) one_pos).mpr
    ((E1.inE_iff_inEFor hT).mpr (inEFor_pgl2_of_coatom_q (e22pl2sq_isOddPrimePower hp5 hK)
      (Or.inl (by rw [hK]; exact e22pl2sq_mod_eight hpodd)) (by rw [hK]; nlinarith) hT
      (fun hz hzJ => pgl2_centralizer_inner_involution_isCoatom_sq hp5 hK hz hzJ)))
  simpa using h

end CFSG.Quasithin.E22L2
