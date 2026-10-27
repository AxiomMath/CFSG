module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2Group
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Outer
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411J1
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup
open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

open Polynomial in
private theorem card_galoisField_two (n : ℕ) :
    Nat.card (GaloisField 2 n) = 2 ^ (if n = 0 then 1 else n) := by
  split_ifs with hn
  · subst hn
    have hadj := SplittingField.adjoin_rootSet (X ^ 2 ^ 0 - X : (ZMod 2)[X])
    have hroot : (X ^ 2 ^ 0 - X : (ZMod 2)[X]).rootSet
        (SplittingField (X ^ 2 ^ 0 - X : (ZMod 2)[X])) = ∅ := by
      ext x
      simp
    rw [hroot, Algebra.adjoin_empty] at hadj
    have hrank : Module.finrank (ZMod 2) (SplittingField (X ^ 2 ^ 0 - X : (ZMod 2)[X])) = 1 :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hadj
    change Nat.card (SplittingField (X ^ 2 ^ 0 - X : (ZMod 2)[X])) = 2 ^ 1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hrank, Nat.card_zmod]
  · exact GaloisField.card 2 n hn

theorem noSmall1411_of_L2even (h : Hyp1411 X L S) {n : ℕ}
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) (hn2 : n ≠ 2) (hn4 : n ≠ 4) :
    NoSmall1411 X L S := by
  obtain ⟨e⟩ := hL
  intro I hIn hI hLI t htS htQ htt
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  set m := if n = 0 then 1 else n with hm
  have hcard := card_galoisField_two n
  have hm1 : 1 ≤ m := by rw [hm]; split_ifs <;> omega
  set ε : ↥(L.map π) ≃* SL(2, GaloisField 2 n) :=
    e.trans (slTwoEquivProjSL (GaloisField 2 n)).symm with hε
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  set α : MulAut SL(2, GaloisField 2 n) := ε.symm.trans (ψ.trans ε) with hα
  have hψ2 : ψ * ψ = 1 := by
    rw [hψ, ← map_mul, ← map_mul, htt, map_one, map_one]
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun x => ?_
    have := congrArg (fun f : MulAut ↥(L.map π) => ε (f (ε.symm x))) hψ2
    simpa [hα] using this
  have hinner : ∀ g : SL(2, GaloisField 2 n), α ≠ MulAut.conj g := by
    intro g hg
    obtain ⟨y, hyL, hy⟩ := not_inner_of_inf_eq_bot_of_hyp1411 h hSL htS htQ
      ((ε.symm g : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) (ε.symm g).2
    apply hy
    have h1 := congrArg (fun f : MulAut SL(2, GaloisField 2 n) => ε.symm (f (ε ⟨y, hyL⟩))) hg
    simp only [hα, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
      map_mul, map_inv] at h1
    have h2 := congrArg Subtype.val h1
    rw [hψ, MulAut.conjNormal_apply] at h2
    rw [h2]
    rfl
  obtain ⟨hev, x, hx⟩ := exists_dvd_orderOf_mul_inv_SL2_even_of_card hm1 hcard α hα2 hinner
  have hn0 : n ≠ 0 := by
    intro h0
    simp [hm, h0] at hev
  simp only [hm, hn0, ↓reduceIte] at hev hx
  have hn6 : 6 ≤ n := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hsimp : IsSimpleGroup ↥(L.map π) := by
    have := Sec21.isSimpleGroup_projSL_two (m := n) (by omega)
    exact e.isSimpleGroup
  have hbot := map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  have hord : orderOf (α x * x⁻¹) = orderOf (ψ (ε.symm x) * (ε.symm x)⁻¹) := by
    rw [← MulEquiv.orderOf_eq ε, map_mul, map_inv]
    simp [hα]
  obtain ⟨ℓ, -, hℓ⟩ := (ε.symm x).2
  have hu : t ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top t
  have hv : ℓ * t⁻¹ * ℓ⁻¹ ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have hvb : (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := by
    rw [relIndex_centralizer_conj hIn, inv_eq_of_mul_eq_one_right htt]
    exact hle
  obtain ⟨N, -, hpow, h105⟩ := exists_pow_mem_centralizer_odd_dvd_105 hI hu hv hle hvb
  have himg : π (t * (ℓ * t⁻¹ * ℓ⁻¹)) =
      ((ψ (ε.symm x) * (ε.symm x)⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ]
    simp only [map_mul, map_inv]
    group
  have h1 : (ψ (ε.symm x) * (ε.symm x)⁻¹) ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ (ε.symm x) * (ε.symm x)⁻¹) ^ (2 * N) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : 2 ^ (n / 2) + 1 ∣ 2 * N :=
    (hx.trans (hord ▸ dvd_refl _)).trans (orderOf_dvd_of_pow_eq_one h1)
  have hodd : Odd (2 ^ (n / 2) + 1) := by
    refine Even.add_one ?_
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hdvdN : 2 ^ (n / 2) + 1 ∣ N :=
    (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) hdvd)
  have h105' := h105 _ hodd hdvdN
  have hle105 : 2 ^ (n / 2) + 1 ≤ 105 := Nat.le_of_dvd (by norm_num) h105'
  have hk3 : 3 ≤ n / 2 := by omega
  have hk6 : n / 2 ≤ 6 := by
    by_contra hk
    push Not at hk
    have : 2 ^ 7 ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases hk : n / 2 <;> norm_num at h105'

theorem asc82Item1411_L2even (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {n : ℕ}
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) (hn2 : n ≠ 2) (hn4 : n ≠ 4) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  obtain ⟨e⟩ := hL
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X)
  have hcard := card_galoisField_two n
  have hm1 : 1 ≤ (if n = 0 then 1 else n) := by split_ifs <;> omega
  have hcyc : IsCyclic (Outer ↥(L.map π)) := by
    have h := (even_SL2_full_automorphism_semilinear_model (F := GaloisField 2 n) hm1
      hcard).2.2.1
    exact (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans (slTwoEquivProjSL (GaloisField 2 n)).symm)).isCyclic.2 h
  exact asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_isCyclic_outer h hSL hcyc)
    (noSmall1411_of_L2even h ⟨e⟩ hSL hn2 hn4)

end CFSG.RankThree.PartTwo.Sec20
