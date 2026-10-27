module

public import CFSG.Quasithin.Background.Harris.KFact2d.Lin2
public import CFSG.Quasithin.Background.Harris.KFact2d.ModelL3
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.SzOneV2d
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
  CFSG.Quasithin.A312U3
open scoped MatrixGroups Matrix

variable {p : ℕ} [Fact p.Prime]


variable {p : ℕ} [Fact p.Prime]

theorem ker_rhoL_scalar {B : GL (Fin 2) (ZMod p)} (h : rhoL p B = 1) :
    ∃ l : ZMod p, l ^ 3 = 1 ∧ (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) l := by
  have hk : leviHom p B ∈ (piL p).ker := h
  rw [ker_piL] at hk
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  refine ⟨r, by simpa using hr3, ?_⟩
  ext i j
  have := congrFun (congrFun hr (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [coe_leviHom, Matrix.scalar_apply] using this.symm


theorem exists_scL_of_scalar {A : GL (Fin 2) (ZMod p)} {a : ZMod p}
    (ha : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) a) :
    ∃ u : (ZMod p)ˣ, A = scL p u := by
  have hdet : ((A : Matrix (Fin 2) (Fin 2) (ZMod p))).det ≠ 0 := CFSG.Quasithin.A38c15.det_ne_zero_gl2 A
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hdet
    rw [ha]; simp
  exact ⟨Units.mk0 a ha0, Units.ext (by simpa [coe_scL] using ha)⟩

theorem f1At_special (hp4 : p % 4 = 3) {U : Subgroup (PSL3 p)} (hU : SpecialSylowL p U) :
    F1At (PSL3 p) U := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  obtain ⟨-, hUB, c, d, hQ, hc, hd⟩ := hU
  intro E hE hEU hUN t ht
  refine ⟨hEU ht, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  obtain ⟨_, ⟨A, rfl⟩, htA⟩ := hUB (hEU ht)
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hUB hu
  have htA' : t = rhoL p A := htA.symm
  subst htA'
  by_cases hs : ∃ a : ZMod p, (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.scalar (Fin 2) a
  · obtain ⟨a, ha⟩ := hs
    obtain ⟨v, rfl⟩ := exists_scL_of_scalar ha
    exact (rhoL_scL_comm v B).symm
  · exfalso
    have hA : ∀ a : ZMod p, (A : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ Matrix.scalar (Fin 2) a :=
      fun a h => hs ⟨a, h⟩
    have hsq : rhoL p A * rhoL p A = 1 := by
      have := hE.2 _ ht
      simpa [sq] using this
    obtain ⟨l, hl3, hAA'⟩ := ker_rhoL_scalar (B := A * A) (by rw [map_mul]; exact hsq)
    have hAA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) * A = Matrix.scalar (Fin 2) l := by
      simpa [Units.val_mul] using hAA'
    have hl : l ≠ 0 := by
      rintro rfl
      simp at hl3
    have hconj : ∀ g : SL(2, ZMod p), ofSL2 p g ∈ U →
        (Matrix.SpecialLinearGroup.toGL g * A * (Matrix.SpecialLinearGroup.toGL g)⁻¹ :
          GL (Fin 2) (ZMod p)) * A =
        A * (Matrix.SpecialLinearGroup.toGL g * A * (Matrix.SpecialLinearGroup.toGL g)⁻¹) := by
      intro g hg
      have hn := (Subgroup.mem_normalizer_iff.mp (hUN hg) (rhoL p A)).1 ht
      have hn' : rhoL p (Matrix.SpecialLinearGroup.toGL g * A *
          (Matrix.SpecialLinearGroup.toGL g)⁻¹) ∈ E := by
        simpa [map_mul, map_inv, ofSL2, rhoL] using hn
      have hcm := hE.1.is_comm.comm ⟨_, hn'⟩ ⟨_, ht⟩
      have hcm' := congrArg Subtype.val hcm
      exact commute_of_piL_commute (by simpa [rhoL] using hcm')
    have h2' := two_ne_zero_zmod hp2
    have hQ' := hQ.map (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod p) →* GL (Fin 2) (ZMod p))
      Matrix.SpecialLinearGroup.toGL_injective
    obtain ⟨hC, hD, hDC⟩ := quat_relations h2'
      (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact c.2) hQ'
    obtain ⟨x, -, hxx, hxA⟩ := exists_comm_sqm1 ⊤ trivial trivial hA hAA hl h2 hC hD hDC (hconj c hc) (hconj d hd)
    have hν : (l ^ 2) ^ 2 = l := by
      have : l ^ 4 = l * l ^ 3 := by ring
      calc (l ^ 2) ^ 2 = l ^ 4 := by ring
        _ = l := by rw [this, hl3, mul_one]
    have hns : ∀ y : ZMod p, y ^ 2 ≠ -1 := by
      intro y hy
      exact (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp ⟨y, by rw [← hy]; ring⟩ hp4
    exact false_of_sqm1_comm_linear hA (ν := l ^ 2) (by rw [hν]; exact hAA) h2 hns hxx hxA


theorem f1_psl {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hp4 : p % 4 = 3)
    (hK : IsPSL 3 p 1 ↥K) (hS : IsSylowTwoOf S K) :
    ∀ E : Subgroup X, IsElemAbelian 2 E → E ≤ S → S ≤ Subgroup.normalizer (E : Set X) →
      E ≤ E2P.zOf S := by
  obtain ⟨e, U₀, hU₀, hmap⟩ := exists_equiv_special (p := p) (by omega) hK hS
  have h := f1At_special hp4 hU₀
  rw [← hmap] at h
  exact f1_of_model hS.1 (F1At.of_map e _ h)

end CFSG.Quasithin.Background.Harris.KFact2d
