module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.LocalAnalysis.StandardType.GGRCWeylOfPerm
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan Matrix

open scoped MatrixGroups

private theorem nsFA_groupEquiv_of_eq {B : Type} {M M' : CoxeterMatrix B} (h : M = M') :
    ∃ φ : M.Group ≃* M'.Group, ∀ i, φ (M.simple i) = M'.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem nsWeylOfType_A_of_posSU {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hn : 2 ≤ n) (hpos : GGTableBPosSU p Bs X K f n ψ) :
    GGWeylOfType p (CoxeterMatrix.A (n - 1)) (ggAutomizer X Bs) := by
  obtain ⟨ε, hεrefl, -⟩ := hpos
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer X Bs)
  obtain ⟨φ, hφ⟩ := nsFA_groupEquiv_of_eq (coxeterMatrix_isFiniteType_A_eq m).symm
  let ee : (CoxeterMatrix.A m).Group ≃* Equiv.Perm (Fin (m + 1)) :=
    φ.trans (typeAWeylEquiv m).symm
  have hee : ∀ k : Fin m,
      ee ((CoxeterMatrix.A m).simple k) = Equiv.swap k.castSucc k.succ := by
    intro k
    change (typeAWeylEquiv m).symm (φ ((CoxeterMatrix.A m).simple k)) =
      Equiv.swap k.castSucc k.succ
    rw [hφ k, ← typeAWeylEquiv_swap m k, MulEquiv.symm_apply_apply]
  refine ⟨ee.trans ε, fun k => ?_⟩
  have hf : (ee.trans ε) ((CoxeterMatrix.A m).simple k) =
      ε (Equiv.swap k.castSucc k.succ) := by
    change ε (ee ((CoxeterMatrix.A m).simple k)) = ε (Equiv.swap k.castSucc k.succ)
    rw [hee k]
  rw [hf]
  exact hεrefl _ _ (ne_of_lt (Fin.castSucc_lt_succ (i := k)))

theorem nsBaseFrame_of_posSU {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {x : G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (hn : 4 ≤ n) (hpos : GGTableBPosSU p Bs X K f n ψ)
    (htor : Nat.card ↥Bs ≤ p ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (hx : orderOf x = p)
    (hFix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x) :
    ∃ (ιL : Type) (_ : Fintype ιL) (ML : CoxeterMatrix ιL),
      (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) ∧ GGWeylOfType p ML (ggAutomizer X Bs) ∧
        Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) ∧ 3 ≤ Fintype.card ιL := by
  have hW := nsWeylOfType_A_of_posSU (by omega) hpos
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
    have hle : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.zpowers x := by
      intro b hb
      have hfix : ∀ φ ∈ ggAutomizer X Bs, φ ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
        intro φ hφ
        obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
        refine Subtype.ext ?_
        rw [hg ⟨b, hb.1⟩]
        have hcomm : g * b = b * g := Subgroup.mem_centralizer_iff.mp hb.2 g hgX
        calc g * b * g⁻¹ = b * g * g⁻¹ := by rw [hcomm]
          _ = b := by group
      exact hFix ⟨b, hb.1⟩ hfix
    calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥(Subgroup.zpowers x) :=
          Subgroup.card_le_of_le hle
      _ = p := by rw [Nat.card_zpowers, hx]
  refine ⟨Fin m, inferInstance, CoxeterMatrix.A m,
    Or.inl (Or.inl ⟨m, Equiv.refl (Fin m), hm3, (ggCoxeterMatrix_reindex_refl _).symm⟩),
    hW, ?_, by rw [Fintype.card_fin]; exact hm3⟩
  rw [Fintype.card_fin, pow_succ]
  have htor' : Nat.card ↥Bs ≤ p ^ m * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := htor
  exact htor'.trans (Nat.mul_le_mul_left _ hC)

end CFSG.StandardType

end
