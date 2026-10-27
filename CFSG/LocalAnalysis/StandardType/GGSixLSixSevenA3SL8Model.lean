module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ProofModels
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace CoordSL

section Companion

variable {K : Type} [Field K]

theorem rootMat_apply_of_card_two (hK : Nat.card K = 2) {g : K[X]} [Fact (Irreducible g)]
    (hdim : (rootPB g).dim = 2) (a b : Fin (rootPB g).dim) :
    rootMat g a b = if a.val = 0 ∧ b.val = 0 then 0 else 1 := by
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    obtain ⟨y, hy, hyu⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    have hy1 : y = 1 := (hyu 1 one_ne_zero).symm
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    · exact Or.inr ((hyu x hx).trans hy1)
  have h2 : (2 : K) = 0 := by
    have h11 : (1 : K) + 1 = 0 := by
      rcases h01 ((1 : K) + 1) with h | h
      · exact h
      · exfalso
        exact one_ne_zero ((add_left_cancel_iff (a := (1 : K))).mp (by simpa using h))
    rw [← one_add_one_eq_two]
    exact h11
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hgen : (rootPB g).gen = AdjoinRoot.root g := by
    rw [rootPB, AdjoinRoot.powerBasis_gen]
  have hgd : g.natDegree = 2 := by
    have h := AdjoinRoot.powerBasis_dim (f := g) (Fact.out : Irreducible g).ne_zero
    have h2' : (AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero).dim = 2 := hdim
    rw [h] at h2'
    exact h2'
  have hg0 : g ≠ 0 := (Fact.out : Irreducible g).ne_zero
  have hlc : g.leadingCoeff = 1 := by
    rcases h01 g.leadingCoeff with h | h
    · exfalso
      exact (Polynomial.leadingCoeff_ne_zero).mpr hg0 h
    · exact h
  have hmonic : g.Monic := hlc
  have hne1 : g.natDegree ≠ 1 := by rw [hgd]; norm_num
  have hnot0 : ¬ g.IsRoot 0 :=
    (Fact.out : Irreducible g).not_isRoot_of_natDegree_ne_one hne1
  have hnot1 : ¬ g.IsRoot 1 :=
    (Fact.out : Irreducible g).not_isRoot_of_natDegree_ne_one hne1
  have his : IsMonicOfDegree g 2 := ⟨hgd, hmonic⟩
  obtain ⟨c1, c0, hgeq⟩ := isMonicOfDegree_two_iff.mp his
  have heval0 : g.eval 0 = c0 := by rw [hgeq]; simp
  have heval1 : g.eval 1 = 1 + c1 + c0 := by rw [hgeq]; simp
  have hc0 : c0 = 1 := by
    rcases h01 c0 with h | h
    · exfalso; exact hnot0 (heval0.trans h)
    · exact h
  have hc1 : c1 = 1 := by
    rcases h01 c1 with h | h
    · exfalso
      exact hnot1 (by show g.eval 1 = 0; rw [heval1, h, hc0, add_zero]
                      exact CharTwo.add_self_eq_zero 1)
    · exact h
  have hgc0 : g.coeff 0 = 1 := by rw [hgeq]; simpa using hc0
  have hgc1 : g.coeff 1 = 1 := by rw [hgeq]; simpa using hc1
  have hminpoly : (rootPB g).minpolyGen = g := by
    rw [PowerBasis.minpolyGen_eq]
    rw [show rootPB g = AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero from rfl]
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hmonic]
  have hrootMat : rootMat g = Algebra.leftMulMatrix (rootPB g).basis (rootPB g).gen := by
    rw [rootMat, hgen]
  rw [hrootMat, PowerBasis.leftMulMatrix, hminpoly]
  simp only [Matrix.of_apply]
  have ha01 : a.val = 0 ∨ a.val = 1 := by omega
  have hb01 : b.val = 0 ∨ b.val = 1 := by omega
  rcases hb01 with hb | hb <;> rcases ha01 with ha | ha
  · have hb' : (b : ℕ) + 1 ≠ (rootPB g).dim := by omega
    have ha' : (a : ℕ) ≠ (b : ℕ) + 1 := by omega
    rw [if_neg hb', if_neg ha']
    simp [hb, ha]
  · have hb' : (b : ℕ) + 1 ≠ (rootPB g).dim := by omega
    have ha' : (a : ℕ) = (b : ℕ) + 1 := by omega
    rw [if_neg hb', if_pos ha']
    simp [hb, ha]
  · have hb' : (b : ℕ) + 1 = (rootPB g).dim := by omega
    rw [if_pos hb']
    simp [hb, ha, hgc0, hgc1, CharTwo.neg_eq]
  · have hb' : (b : ℕ) + 1 = (rootPB g).dim := by omega
    rw [if_pos hb']
    simp [hb, ha, hgc0, hgc1, CharTwo.neg_eq]

end Companion

section Model

variable {K : Type} [Field K] [CharP K 2]

lemma omMat_apply (c : ZMod 2 →+* K) (a : Fin 4) (x y : Fin 2) (b cc : Fin 4) :
    c (GGA3.omMat a.val (finProdFinEquiv (b, x)) (finProdFinEquiv (cc, y))) =
      if b = cc then (if b = a then (if x.val = 0 ∧ y.val = 0 then 0 else 1)
        else (if x = y then 1 else 0)) else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases cc <;> fin_cases x <;> fin_cases y <;>
    simp [GGA3.omMat, finProdFinEquiv, map_zero, map_one]

theorem exists_hom_eq_nsSL {n e s r : ℕ} (hn : n = 8) (he : e = 2) (hs : s = 4) (hr : r = 0)
    (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) K} (hC : C.det = 1)
    (hCa : ∀ a b : Fin e, C a b = if a.val = 0 ∧ b.val = 0 then 0 else 1)
    (σ : Fin 4 → Fin s) (hσ : Function.Injective σ) :
    ∃ Φ : Matrix.SpecialLinearGroup (Fin 8) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin n) K,
      ∀ (a : ℕ) (ha : a < 4), Φ (GGA3.omSL a ha) =
        SLNS.nsSL ε hC (fun i => if i = σ ⟨a, ha⟩ then 1 else 0) := by
  subst hn
  subst he
  subst hs
  subst hr
  have hσbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσ
  let σe : Fin 4 ≃ Fin 4 := Equiv.ofBijective σ hσbij
  let c : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let τ : Fin 8 ≃ Fin 8 :=
    ε.trans ((Equiv.sumEmpty (Fin 2 × Fin 4) (Fin 0)).trans
      (((Equiv.prodCongr (Equiv.refl (Fin 2)) σe.symm).trans
        ((Equiv.prodComm (Fin 2) (Fin 4)).trans finProdFinEquiv))))
  have hτ (x : Fin 2) (i : Fin 4) :
      τ (ε.symm (Sum.inl (x, i))) = finProdFinEquiv (σe.symm i, x) := by
    simp [τ, Equiv.trans_apply]
  refine ⟨(CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear τ.symm).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map c), ?_⟩
  intro a ha
  apply Matrix.SpecialLinearGroup.ext
  intro u v
  obtain ⟨w, rfl⟩ := ε.symm.surjective u
  obtain ⟨w', rfl⟩ := ε.symm.surjective v
  rcases w with ⟨x, i⟩ | j
  · rcases w' with ⟨y, i'⟩ | j'
    · obtain ⟨b, rfl⟩ := σe.surjective i
      obtain ⟨cc, rfl⟩ := σe.surjective i'
      have hL : (↑((CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear τ.symm).toMonoidHom.comp
            (Matrix.SpecialLinearGroup.map c) (GGA3.omSL a ha)) : Matrix (Fin 8) (Fin 8) K)
            (ε.symm (Sum.inl (x, σe b))) (ε.symm (Sum.inl (y, σe cc)))
          = c (GGA3.omMat a (finProdFinEquiv (b, x)) (finProdFinEquiv (cc, y))) := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [CFSG.SeitzReduction.LinearPilot.InvPlacement.coe_reindexSpecialLinear_apply]
        rw [show (↑(Matrix.SpecialLinearGroup.map c (GGA3.omSL a ha)) : Matrix (Fin 8) (Fin 8) K)
            = (GGA3.omMat a).map c from by
          rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]; rfl]
        rw [Matrix.map_apply, Equiv.symm_symm, hτ, hτ, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      have hR : (↑(SLNS.nsSL ε hC (fun i => if i = σ ⟨a, ha⟩ then 1 else 0)) :
            Matrix (Fin 8) (Fin 8) K)
            (ε.symm (Sum.inl (x, σe b))) (ε.symm (Sum.inl (y, σe cc)))
          = (if b = cc then (C ^ (if b = ⟨a, ha⟩ then 1 else 0)) x y else 0) := by
        show SLNS.nsMat ε C (fun i => if i = σ ⟨a, ha⟩ then 1 else 0)
            (ε.symm (Sum.inl (x, σe b))) (ε.symm (Sum.inl (y, σe cc))) = _
        simp only [SLNS.nsMat, Matrix.submatrix_apply, Equiv.apply_symm_apply]
        rw [SLNS.nsCore, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]
        simp only [Prod.snd, Prod.fst, Equiv.apply_eq_iff_eq, σe, Equiv.ofBijective_apply,
          hσ.eq_iff]
      rw [hL, hR, omMat_apply c ⟨a, ha⟩ x y b cc]
      by_cases hbc : b = cc
      · rw [if_pos hbc, if_pos hbc]
        by_cases hba : b = ⟨a, ha⟩
        · simp [hba, hCa]
        · simp [hba, Matrix.one_apply]
      · rw [if_neg hbc, if_neg hbc]
    · exact j'.elim0
  · exact j.elim0

end Model

end CoordSL

end CFSG.StandardType
