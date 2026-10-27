module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Determinant

import CFSG.Quasithin.EmptyFaithful.A38c15IrrMono
import CFSG.CharacterTheory.Burnside
import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

open Matrix

private theorem zmod3_pow_seven_eq_one {c : ZMod 3} (hc : c ^ 7 = 1) : c = 1 := by
  have h : ∀ c : ZMod 3, c ^ 7 = 1 → c = 1 := by decide
  exact h c hc

private theorem exists_card_eq_two_pow_mul_five_pow
    (G : Subgroup (GL (Fin 7) (ZMod 3)))
    (hG : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} G) :
    ∃ a b : ℕ, Nat.card G = 2 ^ a * 5 ^ b := by
  classical
  have hsupp : (Nat.card G).factorization.support ⊆ ({2, 5} : Finset ℕ) := by
    intro p hp
    have hfac : (Nat.card G).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hpprime : p.Prime := by
      by_contra hp'
      exact hfac ((Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hp'))
    have hpdvd : p ∣ Nat.card G := by
      by_contra hpd
      exact hfac ((Nat.factorization_eq_zero_iff _ _).mpr (Or.inr (Or.inl hpd)))
    have hmem : p = 2 ∨ p = 5 := by
      have h := hG ⟨p, hpprime⟩ hpdvd
      change p = 2 ∨ p = 5 at h
      exact h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hprod : Nat.card G = ∏ x ∈ ({2, 5} : Finset ℕ),
      x ^ (Nat.card G).factorization x := by
    have h := Nat.prod_factorization_pow_eq_self (Nat.card_pos (α := G)).ne'
    rw [Finsupp.prod_of_support_subset (Nat.card G).factorization hsupp
      (fun p e => p ^ e) (fun p _ => by simp)] at h
    exact h.symm
  refine ⟨(Nat.card G).factorization 2, (Nat.card G).factorization 5, ?_⟩
  simpa [Finset.prod_insert, Finset.prod_singleton] using hprod

theorem not_isIrreducibleMatrixRep_of_isPiSubgroup_two_five
    (G : Subgroup (GL (Fin 7) (ZMod 3)))
    (hdet : ∀ g ∈ G, Matrix.det (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1)
    (hG : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} G) :
    ¬ CFSG.RepresentationTheory.IsIrreducibleMatrixRep G.subtype := by
  classical
  intro hirr
  have hBloom := CFSG.RankThree.SubgroupLists.irreducible_prime_degree_reduction
    (K := ZMod 3) (n := 7) (by norm_num) hirr
  rcases hBloom with hcyc | hmono | hthird
  ·
    obtain ⟨H, hHG, -, -, -, hHdiv, hHnotdiv⟩ := hcyc
    have hHdiv' : Nat.card H ∣ 2186 := by
      simpa [Nat.card_zmod] using hHdiv
    have hHdiv2 : Nat.card H ∣ 2 * 1093 := by
      have h2186 : (2186 : ℕ) = 2 * 1093 := by norm_num
      rwa [h2186] at hHdiv'
    have hp1093 : Nat.Prime 1093 := by norm_num
    have h1093not : ¬ 1093 ∣ Nat.card H := by
      intro hdvd
      have hdvdG : 1093 ∣ Nat.card G :=
        hdvd.trans (Subgroup.card_dvd_of_le hHG)
      have hmem : (1093 : ℕ) = 2 ∨ (1093 : ℕ) = 5 := by
        have h := hG ⟨1093, hp1093⟩ hdvdG
        change (1093 : ℕ) = 2 ∨ (1093 : ℕ) = 5 at h
        exact h
      norm_num at hmem
    have hcop : Nat.Coprime (Nat.card H) 1093 :=
      ((hp1093.coprime_iff_not_dvd).mpr h1093not).symm
    have hHdvd2 : Nat.card H ∣ 2 := hcop.dvd_of_dvd_mul_right hHdiv2
    apply hHnotdiv
    simpa [Nat.card_zmod] using hHdvd2
  ·
    obtain ⟨L, hL, hrk, hperm, htrans⟩ := hmono
    have hinj : Function.Injective L :=
      CFSG.Quasithin.A38c15.monoLines_injective hL hrk
    let π : G →* Equiv.Perm (Fin 7) :=
      CFSG.Quasithin.A38c15.monoLineHom (G := G) hinj hperm
    have htrans' : ∀ i j : Fin 7, ∃ g : G, (π g) • i = j := by
      intro i j
      obtain ⟨g, hg, hgL⟩ := htrans i j
      refine ⟨⟨g, hg⟩, ?_⟩
      change π ⟨g, hg⟩ i = j
      apply hinj
      rw [← CFSG.Quasithin.A38c15.translate_monoLineHom hinj hperm ⟨g, hg⟩ i, hgL]
    have h7dvd : 7 ∣ Nat.card G := by
      have hstab : (MulAction.stabilizer π.range (0 : Fin 7)).index = 7 := by
        rw [MulAction.index_stabilizer]
        have horbit : MulAction.orbit π.range (0 : Fin 7) = Set.univ := by
          ext j
          constructor
          · intro _
            trivial
          · intro _
            obtain ⟨g, hg⟩ := htrans' 0 j
            exact ⟨⟨π g, ⟨g, rfl⟩⟩, hg⟩
        rw [horbit, Set.ncard_univ]
        simp [Nat.card_eq_fintype_card]
      have hcard : Nat.card π.range =
          Nat.card (MulAction.stabilizer π.range (0 : Fin 7)) * 7 := by
        have h := Subgroup.card_mul_index
          (MulAction.stabilizer π.range (0 : Fin 7))
        rw [hstab] at h
        exact h.symm
      have h7range : 7 ∣ Nat.card π.range := by
        refine ⟨Nat.card (MulAction.stabilizer π.range (0 : Fin 7)), ?_⟩
        rw [hcard, Nat.mul_comm]
      exact h7range.trans (Subgroup.card_range_dvd π)
    have h7mem : (7 : ℕ) = 2 ∨ (7 : ℕ) = 5 := by
      have h := hG ⟨7, by norm_num⟩ h7dvd
      change (7 : ℕ) = 2 ∨ (7 : ℕ) = 5 at h
      exact h
    norm_num at h7mem
  ·
    obtain ⟨a, b, hcard⟩ := exists_card_eq_two_pow_mul_five_pow G hG
    have hsol : Group.IsSolvable G :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (G := G) (p := 2) (q := 5) (a := a) (b := b)
        (by norm_num) (by norm_num) (by norm_num)
        (by simpa [Nat.card_eq_fintype_card] using hcard)
    have hG0 : G ≠ ⊥ := by
      intro hbot
      let v : Fin 7 → ZMod 3 := Pi.single (0 : Fin 7) (1 : ZMod 3)
      let W : Submodule (ZMod 3) (Fin 7 → ZMod 3) := Submodule.span (ZMod 3) {v}
      have hWinv : ∀ g : G, ∀ w ∈ W,
          ((G.subtype g : GL (Fin 7) (ZMod 3)) :
            Matrix (Fin 7) (Fin 7) (ZMod 3)) *ᵥ w ∈ W := by
        intro g w hw
        have hg1 : (g : GL (Fin 7) (ZMod 3)) = 1 := by
          have hmem : (g : GL (Fin 7) (ZMod 3)) ∈
              (⊥ : Subgroup (GL (Fin 7) (ZMod 3))) := by
            rw [← hbot]
            exact g.2
          simpa using hmem
        have hsub : G.subtype g = (1 : GL (Fin 7) (ZMod 3)) := by
          simpa using hg1
        rw [hsub]
        simpa using hw
      have hvec : v ≠ 0 := by
        intro h
        have h0 : (1 : ZMod 3) = 0 := by
          simpa [v] using congrFun h (0 : Fin 7)
        exact one_ne_zero h0
      have hWfr : Module.finrank (ZMod 3) W = 1 :=
        finrank_span_singleton hvec
      have hWbot : W ≠ ⊥ := by
        intro h
        have hmem : v ∈ (⊥ : Submodule (ZMod 3) (Fin 7 → ZMod 3)) := by
          rw [← h]
          exact Submodule.subset_span (by simp)
        rw [Submodule.mem_bot] at hmem
        exact hvec hmem
      have hWtop : W ≠ ⊤ := by
        intro h
        have htopfr : Module.finrank (ZMod 3)
            (⊤ : Submodule (ZMod 3) (Fin 7 → ZMod 3)) = 7 := by
          rw [finrank_top, Module.finrank_fin_fun]
        rw [h] at hWfr
        rw [htopfr] at hWfr
        omega
      rcases hirr W hWinv with h | h
      · exact hWbot h
      · exact hWtop h
    obtain ⟨A, hAG, hA0, hAcomm, hAnorm⟩ :=
      @CFSG.LinearGroups.exists_abelian_normalized_of_isSolvable
        (GL (Fin 7) (ZMod 3)) _ G hsol hG0
    obtain ⟨-, -, hab⟩ := hthird
    have hAle : A ≤ ⊥ := by
      intro x hx
      obtain ⟨c, hc⟩ := hab A hAG hAnorm hAcomm x hx
      have hxG : x ∈ G := hAG hx
      have hdetx : Matrix.det (x : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1 := hdet x hxG
      rw [hc] at hdetx
      have hc7 : c ^ 7 = 1 := by
        simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdetx
      have hc1 : c = 1 := zmod3_pow_seven_eq_one hc7
      rw [Subgroup.mem_bot]
      apply Units.ext
      rw [hc, hc1]
      simp [Matrix.scalar_apply]
    exact hA0 (le_antisymm hAle bot_le)

theorem exists_invariant_of_isPiSubgroup_two_five
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (hdim : Module.finrank (ZMod 3) V = 7) (H : Subgroup (V ≃ₗ[ZMod 3] V))
    (hdet : ∀ g ∈ H, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1)
    (hH : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} H) :
    ∃ W : Submodule (ZMod 3) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g ∈ H, ∀ w ∈ W, g w ∈ W := by
  classical
  let b := Module.finBasisOfFinrankEq (ZMod 3) V hdim
  let e : (V ≃ₗ[ZMod 3] V) ≃* GL (Fin 7) (ZMod 3) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  have he_coe : ∀ g : V ≃ₗ[ZMod 3] V,
      ((e g : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)) =
        LinearMap.toMatrix b b (g : V →ₗ[ZMod 3] V) := fun _ => rfl
  let G : Subgroup (GL (Fin 7) (ZMod 3)) := H.map e.toMonoidHom
  have hcardG : Nat.card G = Nat.card H :=
    Subgroup.card_map_of_injective e.injective
  have hdetG : ∀ g ∈ G,
      Matrix.det (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) = 1 := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hcoe : ((e.toMonoidHom h : GL (Fin 7) (ZMod 3)) :
        Matrix (Fin 7) (Fin 7) (ZMod 3)) =
        LinearMap.toMatrix b b (h : V →ₗ[ZMod 3] V) := by
      simpa using he_coe h
    rw [hcoe, LinearMap.det_toMatrix]
    exact hdet h hh
  have hGpi : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} G := by
    intro p hp
    rw [hcardG] at hp
    exact hH p hp
  have hnot := not_isIrreducibleMatrixRep_of_isPiSubgroup_two_five G hdetG hGpi
  unfold CFSG.RepresentationTheory.IsIrreducibleMatrixRep at hnot
  push Not at hnot
  obtain ⟨W', hW'inv, hW'bot, hW'top⟩ := hnot
  have hmap : (W'.comap b.equivFun.toLinearMap).map b.equivFun.toLinearMap = W' := by
    rw [Submodule.map_comap_eq_of_surjective b.equivFun.surjective]
  refine ⟨W'.comap b.equivFun.toLinearMap, ?_, ?_, ?_⟩
  · intro h
    apply hW'bot
    rw [← hmap, h, Submodule.map_bot]
  · intro h
    apply hW'top
    rw [← hmap, h, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.surjective
  · intro g hg w hw
    have hmem : e g ∈ G := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hinv := hW'inv ⟨e g, hmem⟩ (b.equivFun w) hw
    have hmat : ((G.subtype ⟨e g, hmem⟩ : GL (Fin 7) (ZMod 3)) :
        Matrix (Fin 7) (Fin 7) (ZMod 3)) =
        LinearMap.toMatrix b b (g : V →ₗ[ZMod 3] V) := by
      change ((e g : GL (Fin 7) (ZMod 3)) :
        Matrix (Fin 7) (Fin 7) (ZMod 3)) = LinearMap.toMatrix b b
          (g : V →ₗ[ZMod 3] V)
      exact he_coe g
    have hmatvec : LinearMap.toMatrix b b (g : V →ₗ[ZMod 3] V) *ᵥ b.equivFun w =
        b.equivFun (g w) := by
      rw [Module.Basis.equivFun_apply b w, LinearMap.toMatrix_mulVec_repr, Module.Basis.equivFun_apply]
      rfl
    rw [hmat] at hinv
    rw [hmatvec] at hinv
    exact hinv

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7
