module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofTwist
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KLR
open CFSG.RankThree.PartOne.KEXC
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof


section Descent

variable {L : Type} [Field L] {F : MulAut (adjointGroup ReeTag.F4.tag L)}
  {n : ModGL ReeTag.F4.tag L}

theorem exists_twisted_conj_of_lang (hn : n ∈ adjointGroup ReeTag.F4.tag L)
    {s A x : ModGL ReeTag.F4.tag L} (hs : s ∈ twistedFixed F n) (hA : A ∈ twistedFixed F n)
    (hx : x ∈ adjointGroup ReeTag.F4.tag L) (hxs : x * s * x⁻¹ = A)
    (hlang : ∀ c ∈ adjointGroup ReeTag.F4.tag L, c * A = A * c →
      ∃ z ∈ adjointGroup ReeTag.F4.tag L, z * A = A * z ∧ z⁻¹ * twistMap F n z = c) :
    ∃ r ∈ twistedFixed F n, r * s * r⁻¹ = A := by
  have hFs : twistMap F n s = s := hs.2
  have hFA : twistMap F n A = A := hA.2
  have hFxG : twistMap F n x ∈ adjointGroup ReeTag.F4.tag L := twistMap_mem_adjoint hn hx
  have hFxs : twistMap F n x * s * (twistMap F n x)⁻¹ = A := by
    have h := congrArg (twistMap F n) hxs
    rw [twistMap_mul n (mul_mem hx hs.1) (inv_mem hx), twistMap_mul n hx hs.1,
      twistMap_inv n hx, hFs, hFA] at h
    exact h
  have hcG : x * (twistMap F n x)⁻¹ ∈ adjointGroup ReeTag.F4.tag L := mul_mem hx (inv_mem hFxG)
  have hcA : x * (twistMap F n x)⁻¹ * A = A * (x * (twistMap F n x)⁻¹) := by
    calc x * (twistMap F n x)⁻¹ * A =
        x * ((twistMap F n x)⁻¹ * A * twistMap F n x) * (twistMap F n x)⁻¹ := by group
      _ = x * s * x⁻¹ * (x * (twistMap F n x)⁻¹) := by rw [← hFxs]; group
      _ = A * (x * (twistMap F n x)⁻¹) := by rw [hxs]
  obtain ⟨z, hzG, hzA, hz⟩ := hlang _ hcG hcA
  have hFz : twistMap F n z = z * (x * (twistMap F n x)⁻¹) := by rw [← hz]; group
  refine ⟨z * x, ⟨mul_mem hzG hx, ?_⟩, ?_⟩
  · change twistMap F n (z * x) = z * x
    rw [twistMap_mul n hzG hx, hFz]
    group
  · calc z * x * s * (z * x)⁻¹ = z * (x * s * x⁻¹) * z⁻¹ := by group
      _ = A := by rw [hxs, hzA]; group

end Descent

section Torsion

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem three_dvd_mPhi2 (a : ℕ) : 3 ∣ mPhi2 a := by
  have := two_pow_odd_mod_three a
  rw [mPhi2]
  omega

theorem exists_expTuple_of_torsion (hF : IsReeFrob a F) {c : Fin ReeTag.F4.tag.rank → Lˣ}
    (hc3 : ∀ i, c i ^ 3 = 1)
    (hcR : rootDiagUnit ReeTag.F4.tag c ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)) :
    ∃ ξ₁ ξ₂ : Lˣ, ξ₁ ^ 3 = 1 ∧ ξ₂ ^ 3 = 1 ∧ c = expTuple ξ₁ ξ₂ (uPhi2 a) := by
  set ξ₁ : Lˣ := (c 1)⁻¹ * c 0 with hξ₁
  set ξ₂ : Lˣ := (c 0)⁻¹ with hξ₂
  have h1 : ξ₁ ^ 3 = 1 := by rw [hξ₁, mul_pow, inv_pow, hc3, hc3, inv_one, one_mul]
  have h2 : ξ₂ ^ 3 = 1 := by rw [hξ₂, inv_pow, hc3, inv_one]
  refine ⟨ξ₁, ξ₂, h1, h2, ?_⟩
  obtain ⟨Φ, -, hΦ, -, hΦF⟩ := (torusParam_phi2 hF).param
  have hm : 3 ∣ mPhi2 a := three_dvd_mPhi2 a
  have hmem : ∀ ξ : Lˣ, ξ ^ 3 = 1 → ξ ∈ rootsOfUnity (mPhi2 a) L := by
    intro ξ hξ
    rw [mem_rootsOfUnity]
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_mul, hξ, one_pow]
  set c' := expTuple ξ₁ ξ₂ (uPhi2 a) with hc'
  have hc'R : rootDiagUnit ReeTag.F4.tag c' ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) := by
    have h := hΦF (⟨ξ₁, hmem ξ₁ h1⟩, ⟨ξ₂, hmem ξ₂ h2⟩)
    rw [hΦ] at h
    exact h
  have e0' : c' 0 = c 0 := by
    simp [hc', expTuple, uPhi2, hξ₂]
  have e1' : c' 1 = c 1 := by
    simp only [hc', expTuple, uPhi2, hξ₁, hξ₂]
    simp
  have e0 : c' (0 : Fin 4) = c (0 : Fin 4) := e0'
  have e1 : c' (1 : Fin 4) = c (1 : Fin 4) := e1'
  obtain ⟨hc2, hc3'⟩ := coord_eq_of_mem_twistedFixed hF c hcR
  obtain ⟨hd2, hd3⟩ := coord_eq_of_mem_twistedFixed hF c' hc'R
  have e2 : c' (2 : Fin 4) = c (2 : Fin 4) := by rw [hd2, hc2, e0]
  have e3 : c' (3 : Fin 4) = c (3 : Fin 4) := by
    rw [e0, e1, e2, ← hc3'] at hd3
    exact mul_left_cancel hd3
  funext i
  fin_cases i
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm

end Torsion

section Transport

variable {L : Type} [Field L] {ζ : Lˣ}

theorem rootChar_smul_eq_of_simple {a b : Fin ReeTag.F4.tag.rank → Lˣ}
    {w : WeylGroup ReeTag.F4.tag}
    (h : ∀ i, rootChar a (w • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      rootChar b (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))
    (v : Fin ReeTag.F4.tag.rank → ℤ) : rootChar a (w • v) = rootChar b v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h i]

theorem exists_transport_expTuple (hζ : orderOf ζ = 3) (a : ℕ) {i j : ℕ} (hi : i < 3)
    (hj : j < 3) (hij : ¬ (i = 0 ∧ j = 0)) :
    ∃ v : WeylGroup ReeTag.F4.tag, ∀ l : Fin ReeTag.F4.tag.rank → ℤ,
      rootChar (expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)) (v • l) = rootChar (bStd ζ) l := by
  obtain ⟨v, hv⟩ := exists_transport (sOf_mem a) hi hj hij
  refine ⟨v, rootChar_smul_eq_of_simple fun k => ?_⟩
  have hb : rootChar (τ := ReeTag.F4.tag) (bStd ζ)
      (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) =
        ζ ^ ((Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) 1) := rootChar_bStd ζ _
  rw [rootChar_expTuple (ζ ^ i) (ζ ^ j) (uPhi2 a)
      (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)), hb, ← zpow_natCast,
    ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
  rw [zpow_eq_zpow_of_modEq (m := 3) (by rw [← hζ]; exact pow_orderOf_eq_one ζ)]
  refine Int.ModEq.symm (Int.modEq_iff_dvd.2 ?_)
  have hk : (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) 1 = if k = 1 then 1 else 0 := by
    by_cases h : k = 1
    · subst h
      simp
    · rw [Pi.single_eq_of_ne (Ne.symm h)]
      simp [h]
  rw [hk]
  have e0 := three_dvd_dot4_uPhi2_sub a 0 (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ))
  have e1 := three_dvd_dot4_uPhi2_sub a 1 (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ))
  have hd : ∀ t : Fin 2, (∑ l : Fin ReeTag.F4.tag.rank,
      uPhi2 a t l * (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l) =
        dot4 (uPhi2 a t) (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) := by
    intro t
    show (∑ l : Fin 4, uPhi2 a t l * (v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l) = _
    rw [Fin.sum_univ_four]
    rfl
  rw [hd 0, hd 1]
  have key := hv k
  obtain ⟨w, hw⟩ : ∃ w, w = v • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ) := ⟨_, rfl⟩
  rw [← hw] at key e0 e1 ⊢
  push_cast
  have hsum : (i : ℤ) * dot4 (uPhi2 a 0) w + (j : ℤ) * dot4 (uPhi2 a 1) w -
      (if k = 1 then 1 else 0) =
      ((i : ℤ) * dot4 (uBar (sOf a) 0) w + (j : ℤ) * dot4 (uBar (sOf a) 1) w -
        (if k = 1 then 1 else 0)) +
      (i : ℤ) * (dot4 (uPhi2 a 0) w - dot4 (uBar (sOf a) 0) w) +
      (j : ℤ) * (dot4 (uPhi2 a 1) w - dot4 (uBar (sOf a) 1) w) := by ring
  rw [hsum]
  exact dvd_add (dvd_add key (dvd_mul_of_dvd_right e0 _)) (dvd_mul_of_dvd_right e1 _)

end Transport

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
