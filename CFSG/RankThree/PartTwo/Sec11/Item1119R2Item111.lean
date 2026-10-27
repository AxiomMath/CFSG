module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymInputs
import CFSG.RankThree.PartTwo.Sec11.Item116TheoremOCor
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec11.Item1119SymStruct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Main


theorem sym1119Item111_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) :
    Sym1119Item111 := by
  intro G _ _ A c L a R Y d x s r g hctx e heA hecd ⟨k, hk⟩ ⟨Ye, hYe, hKYe, hnf⟩
  have h := hctx.big.toSec11Data
  have hS := h.toSec11Std
  have hdL := h.inf_eq
  have hA := h.closure_eq
  have hAe := h.mem_partTwoF.1
  have hA3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hcA : c ∈ A := h.mem_A
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hle : (Subgroup.zpowers c).map (MulAut.conj k).toMonoidHom ≤ A := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    simpa [MulAut.conj_apply, hk] using heA
  obtain ⟨w, hwA, hw⟩ := item114_of h113 G A c L a R Y hS k hle
  have hemem : e ∈ Subgroup.zpowers (w * c * w⁻¹) := by
    have h1 : e ∈ (Subgroup.zpowers c).map (MulAut.conj k).toMonoidHom :=
      ⟨c, Subgroup.mem_zpowers c, by simpa [MulAut.conj_apply] using hk⟩
    rw [hw, MonoidHom.map_zpowers] at h1
    simpa [MulAut.conj_apply] using h1
  have he1 : e ≠ 1 := fun h1 => hecd (h1 ▸ Subgroup.one_mem _)
  have hcw3 : (w * c * w⁻¹) ^ 3 = 1 := by
    have := congrArg (MulAut.conj w) hc3
    simpa [map_pow, MulAut.conj_apply] using this
  have hzp : Subgroup.zpowers e = Subgroup.zpowers (w * c * w⁻¹) :=
    TheoremO.zpowers_eq_of_mem_of_ne_one hcw3 hemem he1
  set M := L.map (MulAut.conj w).toMonoidHom with hMdef
  have hM : M ∈ thetaComponentsAt 3 e := by
    rw [TheoremO.thetaComponentsAt_eq_of_zpowers_eq hzp]
    exact map_mem_thetaComponentsAt (MulAut.conj w) h.mem_thetaComponentsAt
  have hstdE := hS.change_a h45 hdL hA heA hecd hYe hKYe
  have hdYe : d ∈ Ye := hKYe (hstdE.d_mem_sec11K hdL)
  have hwd : w ∈ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    have hD : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
    have hD3 : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd3]
    exact ((h117 G A c L a R Y hS d hdL (Subgroup.zpowers d) hD hD3).mpr rfl) hwA
  have hdM : d ∈ M := by
    refine ⟨w⁻¹ * d * w, ?_, by show w * (w⁻¹ * d * w) * w⁻¹ = d; group⟩
    have h1 : w⁻¹ * d * w ∈ Subgroup.zpowers d := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwd) d).mp
        (Subgroup.mem_zpowers d)
      simpa using this
    rw [← hdL] at h1
    exact h1.2
  have hYeM : Ye = M := by
    by_contra hne
    have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hYe hM hne
    have hMlist : Sec9.IsList1016 (M ⧸ aschbacherSolvableCore 3 M) :=
      isList1016_of_mulEquiv (Sec13.thetaQuotEquiv (MulAut.conj w) L).symm hS.isList1016
    have hZM := center_eq_bot_of_isList1016 hMlist
    have hθM := Sec6.theta_eq_inf_of_mem_thetaComponentsAt hM
    have hdC : d ∈ Sec4.thetaQuotCentralizer M := by
      refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer hdM, fun l hl => ?_⟩
      rw [hθM]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact M.mul_mem (M.inv_mem hl) (M.mul_mem (M.mul_mem hdM hl) (M.inv_mem hdM))
      · have h1 : ⁅l⁻¹, d⁆ ∈ ⁅M, Ye⁆ := Subgroup.commutator_mem_commutator (M.inv_mem hl) hdYe
        rw [Subgroup.commutator_comm] at h1
        have h2 := hcomm h1
        have e1 : ⁅l⁻¹, d⁆ = l⁻¹ * (d * l * d⁻¹) := by rw [commutatorElement_def]; group
        rwa [e1] at h2
    have hdθ := mem_theta_of_mem_thetaQuotCentralizer hZM hdM hdC
    have hd3' : d ^ 3 = 1 := hA3 d hdA
    have hd1 := eq_one_of_mem_theta_of_pow_eq_one hdθ (k := 1)
      (Subtype.ext (by simpa using hd3'))
    have hd1' : d = 1 := congrArg Subtype.val hd1
    rw [hd1', orderOf_one] at hd3
    omega
  rw [hYeM] at hnf
  apply hnf
  have hc'A : w⁻¹ * c * w ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwA) c).mp hcA
    simpa using this
  have hc'cd : w⁻¹ * c * w ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hc'
    have hmap : (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj w).toMonoidHom ≤
        Subgroup.closure ({e, d} : Set G) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · have h1 : w * y * w⁻¹ ∈ Subgroup.zpowers e := by
          rw [hzp]
          exact Subgroup.mem_zpowers _
        exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) h1
      · have h1 : w * y * w⁻¹ ∈ Subgroup.zpowers y :=
          (Subgroup.mem_normalizer_iff.mp hwd y).mp (Subgroup.mem_zpowers y)
        exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) h1
    have hc_mem : c ∈ Subgroup.closure ({e, d} : Set G) := by
      have h1 : c = (MulAut.conj w).toMonoidHom (w⁻¹ * c * w) := by
        show c = w * (w⁻¹ * c * w) * w⁻¹
        group
      rw [h1]
      exact hmap ⟨_, hc', rfl⟩
    have hed : e * d = d * e := Item1117Proof.commute_of_mem_A h heA hdA
    exact hecd (Item1117Res5Proof.mem_closure_pair_of_mem hed (hA3 e heA) hc_mem
      (sym1119_indep h).2.1)
  obtain ⟨hc'N, hc'3, -⟩ := basic_facts_of_conj h45 hS hdL hA hc'A hc'cd
  have hout := not_isInnerAut_of_not_mem_closure h.toHyp91 hdL hA hc'A hc'cd hc'N
  have hfield := KFacts.inducesStdKind_field_of_isList1016 hS.isList1016 hc'3 ⟨hc'N, hout⟩
  have hmap := KFacts.InducesStdKind.map (MulAut.conj w).toMonoidHom L
    (KFacts.thetaQuotMap_iff_of_injective _ (MulAut.conj w).injective L) hfield
  have hcc : (MulAut.conj w).toMonoidHom (w⁻¹ * c * w) = c := by
    show w * (w⁻¹ * c * w) * w⁻¹ = c
    group
  rw [hcc] at hmap
  exact hmap

end Main

end CFSG.RankThree.PartTwo.Sec11
