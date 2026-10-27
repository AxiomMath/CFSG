module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpFourWeight
public import CFSG.Quasithin.Background.SmithCurtisMain
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisInterp
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpRootSL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis

open TauCeti.GLSymplecticFin in
private def spFO_root (n : ℕ) (hn : 3 ≤ n) : RootSubgroupIndex n :=
  .difference ⟨1, by omega⟩ ⟨0, by omega⟩
    (by
      intro h
      have h' := congrArg Fin.val h
      simp at h')

open TauCeti.GLSymplecticFin in
private def spFO_exp (n c j : ℕ) (hn : 3 ≤ n) : Fin n → ℤ :=
  (c : ℤ) • Pi.single ⟨0, by omega⟩ (1 : ℤ) + (j : ℤ) • stdVec (spFO_root n hn)

private noncomputable def spFO_block (K : Type) [Field K] {n : ℕ} (hn : 3 ≤ n) :
    Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp n K :=
  CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock K
    (ne_succ' (k := (⟨0, by omega⟩ : Fin n)) (show (0 : ℕ) + 1 < n by omega))

private lemma spFO_not_dvd_of_pos_of_lt {K : Type} [Field K] [Finite K] {a : ℕ}
    (ha0 : 0 < a) (ha : a < Nat.card K - 1) :
    ¬ ((Nat.card K : ℤ) - 1) ∣ (a : ℤ) := by
  have hq : 2 ≤ Nat.card K := by
    have h := Finite.one_lt_card (α := K)
    omega
  have hcast : ((Nat.card K : ℤ) - 1) = ((Nat.card K - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (show 1 ≤ Nat.card K by omega)]
    norm_num
  rw [hcast, Int.natCast_dvd_natCast]
  intro hd
  have h0 := Nat.eq_zero_of_dvd_of_lt hd ha
  omega

open CFSG.LieType.Steinberg CFSG.SeitzReduction.LinearPilot in
private lemma spFO_chi_diag {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] {c : ℕ} (ι : K →+* k) (χ : StatedSp n K → k)
    (hχ : ∀ t : Fin n → Kˣ, χ (diagHom n K t) = ι (t ⟨0, by omega⟩ : K) ^ c) :
    ∀ u : Kˣ, χ (spFO_block K hn (diagUnit u)) = ι (u : K) ^ c := by
  have h01 : (0 : ℕ) + 1 < n := by omega
  intro u
  have hu : corootVec n K ⟨0, by omega⟩ u ⟨0, by omega⟩ = u := by simp [corootVec]
  rw [spFO_block, shortBlock_diagUnit_eq_corootSp h01, corootSp_apply,
    hχ (corootVec n K ⟨0, by omega⟩ u), hu]

open CFSG.LieType.Steinberg CFSG.SeitzReduction.LinearPilot
  CFSG.ClassicalInvolution.Models.SymplecticPairs in
private lemma spFO_hα {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    ∀ (e : Fin n → Kˣ) (t : K),
      diagHom n K e * spFO_block K hn (sl2Lower t) * (diagHom n K e)⁻¹ =
        spFO_block K hn (sl2Lower (((spFO_root n hn).character e : K) * t)) := by
  have h01 : (0 : ℕ) + 1 < n := by omega
  intro e t
  rw [spFO_block, shortBlock_sl2Lower (ne_succ' (k := (⟨0, by omega⟩ : Fin n)) h01),
    shortBlock_sl2Lower (ne_succ' (k := (⟨0, by omega⟩ : Fin n)) h01), diagHom_conj_elt,
    character_eq_prod (spFO_root n hn) e]
  rfl

private lemma spFO_hψ {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k]
    {c : ℕ} (ι : K →+* k) (χ : StatedSp n K → k)
    (hχ : ∀ t : Fin n → Kˣ, χ (diagHom n K t) = ι (t ⟨0, by omega⟩ : K) ^ c) :
    ∀ e : Fin n → Kˣ,
      ((spTorusChar ι ((c : ℤ) • Pi.single ⟨0, by omega⟩ (1 : ℤ)) e : kˣ) : k) =
        χ (diagHom n K e) := by
  intro e
  let e0 : Fin n → ℤ := (c : ℤ) • Pi.single ⟨0, by omega⟩ (1 : ℤ)
  change ((spTorusChar ι e0 e : kˣ) : k) = χ (diagHom n K e)
  rw [spTorusChar_apply, hχ e]
  have hprod : ∏ a, ι (e a : K) ^ e0 a = ι (e ⟨0, by omega⟩ : K) ^ c := by
    rw [Finset.prod_eq_single_of_mem (s := Finset.univ) ⟨0, by omega⟩ (Finset.mem_univ _)]
    · simp [e0, zpow_natCast]
    · intro b _ hb
      have hb1 : (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ℤ) : Fin n → ℤ) b = 0 :=
        Pi.single_eq_of_ne (i := (⟨0, by omega⟩ : Fin n)) hb 1
      have hb0 : e0 b = 0 := by simp [e0, hb1]
      rw [hb0, zpow_zero]
  rw [hprod]

open CFSG.LieType.Steinberg CFSG.SeitzReduction.LinearPilot
  CFSG.ClassicalInvolution.Models.SymplecticPairs TauCeti.GLSymplecticFin
  CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence in
private lemma spFO_weight_vector {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] [CharP k 2] (ι : K →+* k)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) {y₀ : V}
    {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ)
    (hμ : μ ⟨0, by omega⟩ = (spCurtisDatum n K).dScalar χ (⟨0, by omega⟩ : Fin n))
    {c j : ℕ} (hc : c < Nat.card K) (hj : 0 < j) (hjc : j < c)
    (hodd : Odd (c.choose j))
    (hχ : ∀ t : Fin n → Kˣ, χ (diagHom n K t) = ι (t ⟨0, by omega⟩ : K) ^ c) :
    ∃ v : V, v ≠ 0 ∧
      v ∈ weightSpace (ρ.comp (diagHom n K)) (spTorusChar ι (spFO_exp n c j hn)) := by
  let r : RootSubgroupIndex n := spFO_root n hn
  let ψ : (Fin n → Kˣ) →* kˣ :=
    spTorusChar ι ((c : ℤ) • Pi.single ⟨0, by omega⟩ (1 : ℤ))
  have hψ := spFO_hψ hn ι χ hχ
  have h01 : (0 : ℕ) + 1 < n := by omega
  obtain ⟨f, hf, hfy⟩ := (spCurtisDatum n K).exists_form hρ ht.1 ht.2.1
  have hchoose : (c.choose j : k) ≠ 0 := by
    intro hzero
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff k 2 _).mp hzero)
  obtain ⟨v, hv0, hve⟩ := exists_ne_zero_mem_weightSpace_of_choose
    (D := spCurtisDatum n K) ht hf hfy ι (spFO_block K hn)
    (fun t => shortBlock_sl2Upper_mem_U h01 t)
    (fun t => shortBlock_sl2Lower_mem_L h01 t)
    (fun u => by
      rw [spFO_block, shortBlock_diagUnit_eq_corootSp h01]
      exact corootSp_mem_H ⟨0, by omega⟩ u)
    ⟨1, (spCurtisDatum n K).H.one_mem, by
      rw [spFO_block, shortBlock_weyl_eq_n h01, mul_one]⟩
    hμ (by omega) hc (spFO_chi_diag hn ι χ hχ) (diagHom n K)
    (fun e => diagHom_mem_spCurtisDatum_H e) r.character (spFO_hα hn) ψ hψ (j := j) (by omega)
    hchoose
  refine ⟨v, hv0, ?_⟩
  have hw : spTorusChar ι ((c : ℤ) • Pi.single ⟨0, by omega⟩ (1 : ℤ)) *
      ((Units.map ι.toMonoidHom).comp r.character) ^ j =
      spTorusChar ι (spFO_exp n c j hn) := by
    rw [spTorusChar_mul_character_pow]
    simp [spFO_exp, spFO_root, r]
  rw [← hw]
  simpa [ψ] using hve

theorem four_le_finrank_of_odd_choose {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {k : Type} [Field k] [CharP k 2] (ι : K →+* k) {V : Type*} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {ρ : Representation k (StatedSp n K) V}
    (hρ : IsSimpleRep ρ) {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ)
    (hμ : μ ⟨0, by omega⟩ = (spCurtisDatum n K).dScalar χ (⟨0, by omega⟩ : Fin n))
    {c j : ℕ} (hc : c < Nat.card K) (hj : 0 < j) (hjc : j < c) (hodd : Odd (c.choose j))
    (hχ : ∀ t : Fin n → Kˣ, χ (diagHom n K t) = ι (t ⟨0, by omega⟩ : K) ^ c)
    {y : StatedSp n K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (ρ y - 1)) := by
  obtain ⟨v, hv0, hve⟩ := spFO_weight_vector (K := K) (n := n) (k := k) hn ι hρ ht hμ hc hj
    hjc hodd hχ
  have hn0 : 0 < n := by omega
  have h1n : 1 < n := by omega
  refine four_le_finrank_range_sub_one_of_weight (K := K) (n := n) (k := k) hn ι ρ
    (e := spFO_exp n c j hn) ?_ ?_ ?_ hv0 hve hy hy1
  · intro a ha
    have ha0 : a ≠ ⟨0, hn0⟩ := by
      rintro rfl
      simp at ha
    have ha1 : a ≠ ⟨1, h1n⟩ := by
      rintro rfl
      simp at ha
    have h0 : (Pi.single (⟨0, hn0⟩ : Fin n) (1 : ℤ) : Fin n → ℤ) a = 0 :=
      Pi.single_eq_of_ne ha0 1
    have h1 : (Pi.single (⟨1, h1n⟩ : Fin n) (1 : ℤ) : Fin n → ℤ) a = 0 :=
      Pi.single_eq_of_ne ha1 1
    simp [spFO_exp, spFO_root, stdVec, h0, h1]
  · have hval : spFO_exp n c j hn ⟨0, hn0⟩ = ((c - j : ℕ) : ℤ) := by
      have h2 : spFO_exp n c j hn ⟨0, hn0⟩ = (c : ℤ) - (j : ℤ) := by
        simp [spFO_exp, spFO_root, stdVec]
        omega
      rw [h2, Nat.cast_sub hjc.le]
    rw [hval]
    exact spFO_not_dvd_of_pos_of_lt (K := K) (a := c - j) (by omega) (by omega)
  · have hval : spFO_exp n c j hn ⟨1, h1n⟩ = (j : ℤ) := by
      simp [spFO_exp, spFO_root, stdVec]
    rw [hval]
    exact spFO_not_dvd_of_pos_of_lt (K := K) (a := j) (by omega) (by omega)

end CFSG.LocalAnalysis.WeakClosure81
