module

public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Core
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Shift
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Frame
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Outer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4
import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Base

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover

private theorem map_pCoreOf_centralizer_eq
    {X : Type} [Group X] {K : Subgroup X} (ψ : X ≃* GJ)
    (hKA : Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)))
    (hxK : xJ ∈ K.map ψ.toMonoidHom)
    (hKz : K.map ψ.toMonoidHom ≤ centralizer ({zJ} : Set GJ)) :
    (CFSG.Open.pCoreOf 2 (centralizer (K : Set X))).map ψ.toMonoidHom = VJ := by
  rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2) ψ (centralizer (K : Set X)),
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.map_centralizer_mulEquiv ψ K,
    pCoreOf_centralizer hKA hxK hKz]

private theorem isSolvable_centralizer_eq
    {X : Type} [Group X] {K : Subgroup X} (ψ : X ≃* GJ)
    (hKA : Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)))
    (hxK : xJ ∈ K.map ψ.toMonoidHom)
    (hKz : K.map ψ.toMonoidHom ≤ centralizer ({zJ} : Set GJ)) :
    Group.IsSolvable ↥(centralizer (K : Set X)) := by
  haveI : Group.IsSolvable
      ↥(centralizer ((K.map ψ.toMonoidHom : Subgroup GJ) : Set GJ)) :=
    isSolvable_centralizer hKA hxK hKz
  exact Group.isSolvable_of_isSolvable_injective
    (f := (CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.centralizerMapEquiv ψ K).toMonoidHom)
    (CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.centralizerMapEquiv ψ K).injective

private theorem exists_conj_of_forall_apply_eq_map
    {X : Type} [Group X]
    {K : Subgroup X} (ψ : X ≃* GJ)
    (hKA : Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)))
    (hxK : xJ ∈ K.map ψ.toMonoidHom)
    (hKz : K.map ψ.toMonoidHom ≤ centralizer ({zJ} : Set GJ))
    (hCmap : (centralizer (K : Set X)).map ψ.toMonoidHom =
      centralizer ((K.map ψ.toMonoidHom : Subgroup GJ) : Set GJ))
    (α : MulAut X) (hα : ∀ k ∈ K, α k = k) :
    ∃ g ∈ centralizer (K : Set X), α = MulAut.conj g := by
  have hVK : VJ ≤ centralizer ((K.map ψ.toMonoidHom : Subgroup GJ) : Set GJ) :=
    VJ_le_centralizer hKA hxK hKz
  have hCV : centralizer ((K.map ψ.toMonoidHom : Subgroup GJ) : Set GJ) ⊓
      centralizer (VJ : Set GJ) = VJ :=
    centralizer_inf_centralizer_VJ hKA hxK hKz
  let α' : MulAut GJ := ψ.symm.trans (α.trans ψ)
  have hα' : ∀ y ∈ K.map ψ.toMonoidHom, α' y = y := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    show (ψ.symm.trans (α.trans ψ)) (ψ k) = ψ k
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply, hα k hk]
  obtain ⟨g', hg'C, hg'conj⟩ := eq_conj_of_forall_apply_eq hKA hxK hKz hVK hCV α' hα'
  have hgC : ψ.symm g' ∈ centralizer (K : Set X) := by
    rw [← Subgroup.mem_map_equiv (f := ψ) (K := centralizer (K : Set X)) (x := g'), hCmap]
    exact hg'C
  refine ⟨ψ.symm g', hgC, ?_⟩
  ext x
  apply ψ.injective
  rw [MulAut.conj_apply]
  have h := congrArg (fun e : MulAut GJ => e (ψ x)) hg'conj
  simp only [α', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  rw [show ψ (α x) = g' * ψ x * g'⁻¹ from h]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem eq_bot_or_eq_pCoreOf_of_map
    {X : Type} [Group X]
    {K E : Subgroup X} (ψ : X ≃* GJ) (hxK : xJ ∈ K.map ψ.toMonoidHom)
    (hzE : zJ ∈ E.map ψ.toMonoidHom)
    (hEmap : (CFSG.Open.pCoreOf 2 (centralizer (K : Set X))).map ψ.toMonoidHom = VJ) :
    ∀ U : Subgroup X, U ≤ centralizer (K : Set X) → IsPGroup 2 U →
      E ≤ normalizer (U : Set X) →
        U = ⊥ ∨ U = CFSG.Open.pCoreOf 2 (centralizer (K : Set X)) := by
  intro U hU hU2 hEU
  have hU'C : U.map ψ.toMonoidHom ≤
      centralizer ((K.map ψ.toMonoidHom : Subgroup GJ) : Set GJ) := by
    rw [← CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.map_centralizer_mulEquiv ψ K]
    exact Subgroup.map_mono hU
  have hzU' : zJ ∈ normalizer (U.map ψ.toMonoidHom : Subgroup GJ) := by
    rw [← Subgroup.map_equiv_normalizer_eq U ψ]
    obtain ⟨e, he, hψe⟩ := Subgroup.mem_map.mp hzE
    rw [← hψe]
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom (hEU he)
  rcases eq_bot_or_eq_VJ hxK hU'C (hU2.map ψ.toMonoidHom) hzU' with hbot | hVJ
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective U ψ.injective).mp hbot)
  · exact Or.inr (Subgroup.map_injective ψ.injective (hVJ.trans hEmap.symm))

private theorem nonempty_klein_pCoreOf_of_map
    {X : Type} [Group X] {K : Subgroup X} (ψ : X ≃* GJ)
    (hEmap : (CFSG.Open.pCoreOf 2 (centralizer (K : Set X))).map ψ.toMonoidHom = VJ) :
    Nonempty (CFSG.Open.pCoreOf 2 (centralizer (K : Set X)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.F6.GoldAmN.nonempty_mulEquiv_klein_subgroup (D := GJ) VJ
    card_V (fun v hv => by rw [pow_two]; exact mul_self_of_mem_kleinSub hv)
  exact ⟨(Subgroup.equivMapOfInjective (CFSG.Open.pCoreOf 2 (centralizer (K : Set X)))
    ψ.toMonoidHom ψ.injective).trans ((MulEquiv.subgroupCongr hEmap).trans e)⟩

private theorem nonempty_centralizer_pCoreOf_of_map
    {X : Type} [Group X] {K : Subgroup X} (ψ : X ≃* GJ)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hKp : Group.IsPerfect ↥K)
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hEmap : (CFSG.Open.pCoreOf 2 (centralizer (K : Set X))).map ψ.toMonoidHom = VJ) :
    Nonempty (Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer (K : Set X)) : Subgroup X) : Set X) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
  have hKne : K ≠ ⊥ := by
    intro hbot
    have h := card_eq_sixty_mul_card_pCoreOf hKA
    rw [hbot, Subgroup.card_bot] at h
    omega
  have hEcard : Nat.card (CFSG.Open.pCoreOf 2 (centralizer (K : Set X))) = 4 := by
    rw [← Subgroup.card_map_of_injective
      (K := CFSG.Open.pCoreOf 2 (centralizer (K : Set X))) (f := ψ.toMonoidHom) ψ.injective,
      hEmap, card_V]
  have hsq : ∀ x ∈ CFSG.Open.pCoreOf 2 (centralizer (K : Set X)), x ^ 2 = 1 := by
    intro x hx
    apply ψ.injective
    rw [map_pow, map_one, pow_two]
    have hxV : ψ x ∈ VJ := by
      rw [← hEmap]
      exact Subgroup.mem_map_of_mem ψ.toMonoidHom hx
    exact mul_self_of_mem_kleinSub hxV
  have hKle : K ≤ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer (K : Set X)) : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.mp
      (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (Subgroup.centralizer (K : Set X)))
  exact CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 X hX
    (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (K : Set X))) hEcard hsq
    ⟨K, hKne, hKp, hKle⟩

theorem ks166J2A5 :
    KFacts.KS166J2A5 := by
  intro X _ _ hX K hKp hKA E hEK _ hE9
  obtain ⟨ψ, hzE, hxK, hKz, hKA'⟩ := exists_frame2 hX hKp hKA hEK hE9
  have hCmap := CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.map_centralizer_mulEquiv ψ K
  have hEmap := map_pCoreOf_centralizer_eq ψ hKA' hxK hKz
  exact ⟨pCore_eq_bot hX hKp hKA hEK hE9,
    isSolvable_centralizer_eq ψ hKA' hxK hKz,
    exists_conj_of_forall_apply_eq_map ψ hKA' hxK hKz hCmap,
    eq_bot_or_eq_pCoreOf_of_map ψ hxK hzE hEmap,
    nonempty_klein_pCoreOf_of_map ψ hEmap,
    nonempty_centralizer_pCoreOf_of_map ψ hX hKp hKA hEmap⟩

end CFSG.RankThree.PartTwo.KFacts.KS166
