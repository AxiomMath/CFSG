module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Uni
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCubicAction
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphismsCongr
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem label_eq_twA_of_isComponentOf_fixSubgroup (hRig : GGLabelRigidInput) {K : Type}
    [Field K] [Finite K] {d g : ℕ} (hK : Nat.card K = (2 ^ g) ^ 2) (hd : 3 ≤ d)
    (hdq : ¬(d = 3 ∧ 2 ^ g = 2))
    {s : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)))}
    (hsI : s ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ g)))
      (LargeEvenGUSet (Fin d) K (2 ^ g)))
    (hs3 : s ^ 3 = 1) {J₁ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)))}
    [Finite ↥J₁] (hJ₁ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s)) {n : ℕ} (hn : Odd n)
    {lab : LargeEvenLabel}
    (hlab : lab = ⟨.D, 4, n⟩ ∨ lab = ⟨.triD4, 0, n⟩ ∨ lab = ⟨.A, 2, 3 * n⟩ ∨
      lab = ⟨.twA, 2, 3 * n⟩)
    (hJ : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥J₁ (· = lab)) :
    lab = ⟨.twA, 2, 3 * n⟩ := by
  classical
  obtain ⟨τ, hτq, hτ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hK
  obtain ⟨A₀, hA₀, hgraph⟩ := hsI
  obtain ⟨A, hA, hAA⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_heldGU_of_GUSet hτq hK hτ A₀ hA₀
  have hdQ : (d, 2 ^ g) ≠ (3, 2) := fun h => hdq (Prod.mk.inj h)
  rcases CFSG.LocalAnalysis.GLTheoremA.CanonInn.component_psu_fixed
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds hτ hτq hK
      (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card hK) hd hdQ A hA
      Nat.prime_three (by norm_num) s (fun h h' hh => hgraph h h' (hh.trans (hAA _))) hs3 J₁
      hJ₁ with
    ⟨a, dd, E, _, _, τ', hτ', ha2, hτ'Q, hcardE, hφ⟩ | ⟨b, ee, E, _, _, hb2, hcardE, hφ⟩
  ·
    have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (g * dd) := fun x => by rw [pow_mul]; exact hτ'Q x
    have hcardm : Nat.card E = (2 ^ (g * dd)) ^ 2 := by rw [pow_mul]; exact hcardE
    rcases CFSG.LocalAnalysis.GLTheoremA.CanonInn.canonLabel_of_quot_heldSU hRig τ' hτ' ha2
        hτ'm hcardm hJ hφ with h | h <;>
      rcases hlab with rfl | rfl | rfl | rfl <;>
      simp [CFSG.LocalAnalysis.GLTheoremA.canonLabel] at h ⊢
  ·
    have hcardm : Nat.card E = 2 ^ (2 * (g * ee)) := by
      rw [hcardE, ← pow_mul, mul_left_comm]
    have h := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _
      lab b (2 * (g * ee)) E hb2 hcardm hJ hφ
    obtain ⟨m, rfl⟩ := hn
    rcases hlab with rfl | rfl | rfl | rfl <;>
      simp [CFSG.LocalAnalysis.GLTheoremA.canonLabel] at h
    omega

theorem centerQuotientHom_mem_innAutDerived_of_recipeUnitary {K : Type} [Field K] [Finite K]
    {d g : ℕ} (hg : 1 ≤ g) (hK : Nat.card K = (2 ^ g) ^ 2) (hd : 3 ≤ d) (hd6 : d ≤ 6)
    {s t : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)))}
    (hsI : s ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ g)))
      (LargeEvenGUSet (Fin d) K (2 ^ g)))
    (htI : t ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ g)))
      (LargeEvenGUSet (Fin d) K (2 ^ g)))
    (hs3 : s ^ 3 = 1) (ht3 : t ^ 3 = 1) (hst : s * t = t * s)
    {J₁ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)))}
    (hJ₁ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s)) {k : ℕ} (hk : Odd k)
    (hcard : Nat.card (↥J₁ ⧸ Subgroup.center ↥J₁) = CFSG.Open.ordTwistedA 2 (2 ^ k))
    (hstab : t ∈ CFSG.GroupActions.subgroupStabAut J₁) :
    centerQuotientHom ↥J₁ (CFSG.GroupActions.subgroupStabRestrict J₁ ⟨t, hstab⟩) ∈
      innAutDerived (↥J₁ ⧸ Subgroup.center ↥J₁) := by
  classical
  have h : UnitaryFieldData 2 g K := ⟨Nat.prime_two, hg, by rw [hK, ← pow_mul, mul_comm]⟩
  have hd1 : 1 ≤ d := by omega
  set e := InndiagSU.projEquiv h hd1 with he
  set E : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)) →* primeFormP h (idGram K d) :=
    e.toMonoidHom with hE
  obtain ⟨A, hA⟩ := InndiagSU.congr_mem_primeFormD h hd1 hK hsI
  obtain ⟨Y, hY⟩ := InndiagSU.congr_mem_primeFormD h hd1 hK htI
  have hfix : fixSubgroup (MulAut.congr e s) = (fixSubgroup s).map E := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (s (e.symm x)) = x ↔ s (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hKc : CFSG.Open.IsComponentOf (J₁.map E) (fixSubgroup (MulAut.congr e s)) := by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ₁
  let ε : ↥J₁ ≃* ↥(J₁.map E) := J₁.equivMapOfInjective E e.injective
  have hcardKc : Nat.card (↥(J₁.map E) ⧸ Subgroup.center ↥(J₁.map E)) =
      CFSG.Open.ordTwistedA 2 (2 ^ k) := by
    rw [← hcard]
    exact Nat.card_congr (QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).symm.toEquiv
  have hstabKc : MulAut.congr e t ∈ CFSG.GroupActions.subgroupStabAut (J₁.map E) := by
    change (J₁.map E).map (MulAut.congr e t).toMonoidHom = J₁.map E
    have hcomp : (MulAut.congr e t).toMonoidHom.comp E = E.comp t.toMonoidHom := by
      ext r
      simp [E, MulAut.congr_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, (hstab : J₁.map t.toMonoidHom = J₁)]
  have hres := centerQuotientHom_mem_innAutDerived_of_ordTwistedA h hd hd6 hA hY
    (by rw [← map_pow, hs3, map_one]) (by rw [← map_pow, ht3, map_one])
    (by show _ * _ = _ * _; rw [← map_mul, hst, map_mul]) hKc hk hcardKc hstabKc
  have hα : MulAut.congr ε (CFSG.GroupActions.subgroupStabRestrict J₁ ⟨t, hstab⟩) =
      CFSG.GroupActions.subgroupStabRestrict _ ⟨MulAut.congr e t, hstabKc⟩ := by
    ext k'
    obtain ⟨k, rfl⟩ := ε.surjective k'
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    show e (t k) = e (t (e.symm (e k)))
    rw [MulEquiv.symm_apply_apply]
  rw [← hα, ← centerQuotientHom_congr] at hres
  exact (mem_innAutDerived_congr _).1 hres

end CFSG.StandardType.SCFourCover

end
