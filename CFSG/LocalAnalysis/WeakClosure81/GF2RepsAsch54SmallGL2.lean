module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallCF
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt41U

import CFSG.GH74.SectionalRankExtension
import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallG2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin
open CFSG.GH74.GLS.IVK (IsLnEps)
open CFSG.GH74.GLS.IVK.Proofs2 (GU2Stated)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {P : ∀ (X : Type) [Group X], Prop}

theorem not_isCompositionFactor_quotient_of_injective_GL2
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {X : Type} [Group X]
    (ρ : X →* GL (Fin 2) F) (hρ : Function.Injective ρ) (N : Subgroup X) [N.Normal]
    (L : Type) [Group L] (h : E1.IsCompositionFactor (X ⧸ N) L) : ¬ P L := by
  have : Finite X := Finite.of_injective ρ hρ
  have h2 : (2 : F) ≠ 0 := by
    let : Fintype F := Fintype.ofFinite F
    have hm : Fintype.card F % 2 = 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.odd_iff.mp hodd
    apply Ring.two_ne_zero
    intro hc
    have := FiniteField.even_card_of_char_two hc
    omega
  set d : X →* Fˣ := Matrix.GeneralLinearGroup.det.comp ρ
  set J : Subgroup (X ⧸ N) := d.ker.map (QuotientGroup.mk' N)
  have : J.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  refine not_isCompositionFactor_of_normal J ?_ ?_ L h
  · refine not_isCompositionFactor_of_sectionalTwoRankLE (fun L _ _ hL => (hP L hL).2) ?_
    have hSL : CFSG.GH74.SectionalTwoRankLE
        ↥(Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker 2 :=
      CFSG.GH74.SectionalTwoRankLE.of_mulEquiv Matrix.SpecialLinearGroup.toGLKerEquiv
        (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup F h2)
    have hker : CFSG.GH74.SectionalTwoRankLE ↥d.ker 2 :=
      CFSG.GH74.SectionalTwoRankLE.of_injective
        ((ρ.comp d.ker.subtype).codRestrict _ fun x => x.2)
        (fun x y hxy => Subtype.ext (hρ (congrArg Subtype.val hxy))) hSL
    exact CFSG.GH74.SectionalTwoRankLE.of_surjective ((QuotientGroup.mk' N).subgroupMap d.ker)
      ((QuotientGroup.mk' N).subgroupMap_surjective d.ker) hker
  · refine not_isCompositionFactor_of_isSolvable (fun L _ _ hL => (hP L hL).1)
      (isSolvable_of_comm fun a b => ?_)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    show (((x : X ⧸ N) * (y : X ⧸ N) : X ⧸ N) : (X ⧸ N) ⧸ J) =
      (((y : X ⧸ N) * (x : X ⧸ N) : X ⧸ N) : (X ⧸ N) ⧸ J)
    rw [QuotientGroup.eq]
    refine ⟨(x * y)⁻¹ * (y * x), ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
        mul_comm (d y) (d x), inv_mul_cancel]
    · simp only [map_mul, map_inv, QuotientGroup.mk'_apply]

theorem not_hasCompFactor_centralizer_of_isLnEps
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q} [E.Normal] (hq : Group.IsSolvable (Q ⧸ E))
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsLnEps 3 ↥E 1 (p ^ n) ∨ IsLnEps 3 ↥E (-1) (p ^ n)) {z : Q} (hzE : z ∈ E)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ¬ HasCompFactor (centralizer ({z} : Set Q)) P := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine not_hasCompFactor_of_subgroupOf (fun L _ _ hL => (hP L hL).1) hq _ ?_
  refine not_isCompositionFactor_of_mulEquiv (Asch80G2.subgroupOfCentralizerEquiv E hzE).symm ?_
  have hz := Asch80G2.orderOf_mk_eq_two hzE hz2 hz1
  rcases hE with hE | hE
  · obtain ⟨F, _, _, N, _, hF, -, ⟨e⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.ivk_4_1a_L3 ↥E p n hp hp2 hE _ hz
    exact not_isCompositionFactor_of_mulEquiv e.symm
      (not_isCompositionFactor_quotient_of_injective_GL2 hP (hF ▸ hpodd.pow) (MonoidHom.id _)
        Function.injective_id N)
  · obtain ⟨F, _, _, N, _, hF, -, ⟨e⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.ivk_4_1a_U3 ↥E p n hp hp2 hE _ hz
    exact not_isCompositionFactor_of_mulEquiv e.symm
      (not_isCompositionFactor_quotient_of_injective_GL2 hP (hF ▸ hpodd.pow.pow)
        (GU2Stated (p ^ n) F).subtype (GU2Stated (p ^ n) F).subtype_injective N)

end CFSG.LocalAnalysis.WeakClosure81

end
