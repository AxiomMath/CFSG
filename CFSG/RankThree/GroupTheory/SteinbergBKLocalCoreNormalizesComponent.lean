module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.RankThree.Coprime.SolvableFixedCommutator
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.GH74.AS16.TIBase
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.GroupTheory.LocalCores.PrimeSetCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG CFSG.LocalCores CFSG.RankThree.LocalRank

variable {G : Type*} [Group G]

open scoped Pointwise in
theorem exists_pSubgroup_normalizer_not_le_center [Finite G] {p : ℕ} [Fact p.Prime]
    {L W : Subgroup G} (hW : IsPGroup p W) (hWL : W ≤ normalizer (L : Set G))
    (hZW : (center L).map L.subtype ≤ W) (hpL : p ∣ Nat.card (L ⧸ center L)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ L ∧ P ≤ normalizer (W : Set G) ∧
      ¬ P ≤ (center L).map L.subtype := by
  classical
  let : MulDistribMulAction W L := Subgroup.conjMulDistribMulActionOfLeNormalizer W L hWL
  have hnd : ¬ p ∣ Nat.card (Sylow p L) := by
    intro h
    have h1 : Nat.card (Sylow p L) % p = 1 % p := card_sylow_modEq_one p L
    rw [Nat.mod_eq_zero_of_dvd h, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at h1
    exact zero_ne_one h1
  obtain ⟨Q, hQ⟩ := hW.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p L) hnd
  set U := (Q : Subgroup L).map L.subtype with hUdef
  have hUL : U ≤ L := map_subtype_le _
  have hUp : IsPGroup p U := Q.isPGroup'.map L.subtype
  have hWU : W ≤ normalizer (U : Set G) := by
    refine CFSG.GH74.AS16.le_normalizer_of_conj_mem fun w hw u hu => ?_
    obtain ⟨q, hq, rfl⟩ := hu
    have hfix : (⟨w, hw⟩ : W) • Q = Q := hQ ⟨w, hw⟩
    have hmem : (⟨w, hw⟩ : W) • q ∈ (Q : Subgroup L) := by
      rw [← hfix, Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
    exact ⟨_, hmem, rfl⟩
  have hZU : (center L).map L.subtype ≤ U := by
    have hZp : IsPGroup p (center L) := by
      have h := hW.to_le hZW
      exact h.of_equiv ((center L).equivMapOfInjective L.subtype L.subtype_injective).symm
    have := hZp.le_sylow_of_normal Q
    exact map_mono this
  have hUZ : ¬ U ≤ (center L).map L.subtype := by
    intro h
    have hQZ : (Q : Subgroup L) ≤ center L := by
      intro q hq
      obtain ⟨z, hz, hzq⟩ := h ⟨q, hq, rfl⟩
      rwa [← Subtype.ext hzq]
    have h1 : (center L).index ∣ (Q : Subgroup L).index := Subgroup.index_dvd_of_le hQZ
    exact Q.not_dvd_index (hpL.trans h1)
  refine ⟨U ⊓ normalizer (W : Set G), hUp.to_le inf_le_left, inf_le_left.trans hUL,
    inf_le_right, ?_⟩
  by_cases hUW : U ≤ W
  · rw [inf_eq_left.mpr (hUW.trans le_normalizer)]
    exact hUZ
  set T := U ⊔ W with hT
  have hTp : IsPGroup p T := IsPGroup.to_sup_of_normal_left' hUp hW hWU
  have hWT : W ≤ T := le_sup_right
  have hlt : W.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hUW
    intro u hu
    have : (⟨u, le_sup_left (a := U) hu⟩ : T) ∈ W.subgroupOf T := h ▸ mem_top _
    exact this
  obtain ⟨t, htN, htW⟩ := IsConcreteLE.exists_of_lt
    (CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition hTp hlt)
  have htNW : (t : G) ∈ normalizer (W : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have h1 := (mem_normalizer_iff.mp htN ⟨g, hWT hg⟩).mp hg
      exact h1
    · intro hg
      have hgT : g ∈ T := by
        have : g = (t : G)⁻¹ * (t * g * (t : G)⁻¹) * t := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem t.2) (hWT hg)) t.2
      exact (mem_normalizer_iff.mp htN ⟨g, hgT⟩).mpr hg
  have htUW : (t : G) ∈ (U : Set G) * W := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U W hWU]
    exact t.2
  obtain ⟨u, hu, w, hw, htuw⟩ := htUW
  have huN : u ∈ normalizer (W : Set G) := by
    have : u = t * w⁻¹ := by rw [← htuw]; group
    rw [this]
    exact mul_mem htNW (inv_mem (le_normalizer hw))
  have huW : u ∉ W := fun h => htW (by
    change (t : G) ∈ W
    rw [← htuw]
    exact mul_mem h hw)
  intro hle
  exact huW (hZW (hle ⟨hu, huN⟩))

theorem local_solvable_core_normalizes_prime_divisible_component [Finite G] {p : ℕ}
    (hp : p.Prime) {L : Subgroup G} (hL : IsComponent L) (hpL : p ∣ Nat.card (L ⧸ center L))
    (hZE : IsPGroup p (center (layer G))) {x : G} (hx : ∃ k : ℕ, orderOf x = p ^ k)
    (hxL : x ∈ normalizer (L : Set G)) :
    inSubgroup (aschbacherSolvableCore p) (centralizer {x}) ≤ normalizer (L : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set C := centralizer ({x} : Set G) with hC
  set S := inSubgroup (aschbacherSolvableCore p) C with hS
  obtain ⟨hθsolv, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := C) hp
  have hSC : S ≤ C := map_subtype_le _
  have hSsolv : Group.IsSolvable S :=
    Group.isSolvable_of_isSolvable_injective (f := ((aschbacherSolvableCore p C).equivMapOfInjective
      C.subtype C.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hSp : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, card_map_of_injective C.subtype_injective]
    exact hθp
  have hSn : (S.subgroupOf C).Normal := by
    rw [hS, inSubgroup, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]
    infer_instance
  set A := (center (layer G)).map (layer G).subtype with hA
  have : (layer G).Characteristic := layer_characteristic
  have hAn : A.Normal := ConjAct.normal_of_characteristic_of_normal
  have hAp : IsPGroup p A := hZE.map _
  obtain ⟨k, hk⟩ := hx
  have hX : IsPGroup p (zpowers x) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hCX : centralizer ((zpowers x : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hSA : ⁅S, A⁆ = ⊥ :=
    local_prime_complement_centralizes_normal_prime_group hp hAp hX (hCX ▸ hSC) (hCX ▸ hSn) hSp
  set W := A ⊔ zpowers x with hW
  have hWp : IsPGroup p W := IsPGroup.to_sup_of_normal_left hAp hX
  have hSW : S ≤ centralizer (W : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff]
      exact commutator_eq_bot_iff_le_centralizer.mp hSA
    · rw [← le_centralizer_iff, hCX]
      exact hSC
  have hAL : A ≤ centralizer (L : Set G) := by
    have hLE : L ≤ layer G := component_le_layer hL
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨l, hLE hl⟩)
  have hWL : W ≤ normalizer (L : Set G) :=
    sup_le (hAL.trans (centralizer_le_normalizer _)) (zpowers_le.mpr hxL)
  have hZW : (center L).map L.subtype ≤ W :=
    (center_component_le_center_layer hL).trans le_sup_left
  set V := centralizer (W : Set G) with hV
  have hxW : x ∈ W := mem_sup_right (mem_zpowers x)
  have hVC : V ≤ C := centralizer_le (Set.singleton_subset_iff.mpr hxW)
  have hCW : C ≤ normalizer (W : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_map_conj_eq, hW, Subgroup.map_sup]
    congr 1
    · rw [← mem_normalizer_iff_map_conj_eq, normalizer_eq_top_iff.mpr hAn]
      exact mem_top c
    · rw [MonoidHom.map_zpowers]
      congr 1
      rw [mem_centralizer_singleton_iff] at hc
      change c * x * c⁻¹ = x
      rw [hc, mul_inv_cancel_right]
  have hVn : (V.subgroupOf C).Normal :=
    ⟨fun v hv c => by
      rw [mem_subgroupOf] at hv ⊢
      exact (mem_normalizer_iff.mp
        (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup W (hCW c.2)) _).mp hv⟩
  have hθV : inSubgroup (aschbacherSolvableCore p) V = S := by
    rw [CFSG.RankThree.GroupTheory.inSubgroup_core_eq_inf_of_subgroupOf_isSubnormal hp hVC
      hVn.isSubnormal, inf_eq_right.mpr hSW]
  have hNWS : normalizer (W : Set G) ≤ normalizer (S : Set G) := by
    intro g hg
    have hgV : g ∈ normalizer (V : Set G) :=
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup W hg
    rw [← hθV]
    exact CFSG.GH74.AS16.le_normalizer_of_conj_mem (fun g hg y hy =>
      CFSG.RankThree.GroupTheory.conj_mem_inSubgroup_aschbacherSolvableCore hg hy) hgV
  obtain ⟨P, hPp, hPL, hPW, hPZ⟩ := exists_pSubgroup_normalizer_not_le_center hWp hWL hZW hpL
  have hPS : P ≤ normalizer (S : Set G) := hPW.trans hNWS
  let : MulDistribMulAction P S := Subgroup.conjMulDistribMulActionOfLeNormalizer P S hPS
  have hcop : Nat.Coprime (Nat.card S) (Nat.card P) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hPp
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hSp).symm
  obtain ⟨-, -, hfac, -⟩ :=
    CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization (A := P) (H := S)
      hSsolv hcop
  have hconjL : ∀ g : G, IsComponent (L.map (MulAut.conj g).toMonoidHom) := fun g =>
    isComponent_map_mulEquiv (MulAut.conj g) hL
  have hLK : ∀ g : G,
      L ≤ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro g
    rcases distinct_components_commute (hconjL g) hL with h | h
    · rw [h]
      exact le_normalizer
    · have : L ≤ centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
        exact h
      exact this.trans (centralizer_le_normalizer _)
  intro s hs
  obtain ⟨d, hd, c, hc, hdc⟩ := hfac ⟨s, hs⟩
  have hs' : s = (d : G) * c := congrArg Subtype.val hdc
  rw [hs']
  refine mul_mem ?_ ?_
  ·
    have hle : CFSG.LocalAnalysis.ComponentInitial.actionCommutator P (⊤ : Subgroup S) ≤
        (normalizer (L : Set G)).comap S.subtype := by
      refine (closure_le _).mpr ?_
      rintro _ ⟨t, -, y, rfl⟩
      change (t : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) ∈ normalizer (L : Set G)
      have h1 : (t : G)⁻¹ * y * t ∈ normalizer (L : Set G) := by
        have h := hLK t (hPL y.2)
        rw [← Subgroup.map_equiv_normalizer_eq] at h
        obtain ⟨z, hz, hzy⟩ := h
        rw [← hzy]
        simpa [mul_assoc] using hz
      have : (t : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) = ((t : G)⁻¹ * y * t) * (y : G)⁻¹ := by
        group
      rw [this]
      exact mul_mem h1 (inv_mem (le_normalizer (hPL y.2)))
    exact hle hd
  ·
    have hcP : ∀ y ∈ P, (c : G) * y * (c : G)⁻¹ = y := by
      intro y hy
      have h' : (y : G) * c * y⁻¹ = c := congrArg Subtype.val (hc ⟨y, hy⟩)
      calc (c : G) * y * (c : G)⁻¹ = ((y : G) * c * y⁻¹) * y * (c : G)⁻¹ := by rw [h']
        _ = y := by group
    rcases distinct_components_commute (hconjL c) hL with h | h
    · rw [mem_normalizer_iff_map_conj_eq]
      exact h
    · exfalso
      apply hPZ
      intro y hy
      have hyK : y ∈ L.map (MulAut.conj (c : G)).toMonoidHom := ⟨y, hPL hy, hcP y hy⟩
      have hyC : y ∈ centralizer (L : Set G) := commutator_eq_bot_iff_le_centralizer.mp h hyK
      refine ⟨⟨y, hPL hy⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp hyC l l.2)

end CFSG.RankThree.GroupTheory.SteinbergBK
