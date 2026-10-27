module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.KFacts.KS14Models131
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Proof163L4A7

section Alt

open CFSG.RankThree.PartTwo.KFacts.KP2 Equiv Equiv.Perm MulAction

theorem vOneF_mul_vTwoF_sq : (vOneF 1 * vTwoF 1) ^ 2 = swap 2 5 * swap 2 6 := by
  decide +kernel

theorem isThreeCycle_vOneF_mul_vTwoF_sq : ((vOneF 1 * vTwoF 1) ^ 2).IsThreeCycle := by
  rw [vOneF_mul_vTwoF_sq]
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem exists_apply_six : ∀ j : Fin 7, ∃ m : Fin 4, vOneF m 6 = j ∨ vTwoF m 6 = j := by
  decide +kernel

theorem alternatingGroup_le_vOne_sup_vTwo : alternatingGroup (Fin 7) ≤ vOne ⊔ vTwo := by
  set H := vOne ⊔ vTwo with hH
  have hT : ∀ j : Fin 7, ∃ h ∈ H, h 6 = j := by
    intro j
    obtain ⟨m, hm | hm⟩ := exists_apply_six j
    · exact ⟨vOneF m, Subgroup.mem_sup_left ⟨m, rfl⟩, hm⟩
    · exact ⟨vTwoF m, Subgroup.mem_sup_right ⟨m, rfl⟩, hm⟩
  have hpt : IsPretransitive H (Fin 7) := ⟨fun x y => by
    obtain ⟨h₁, hh₁, e₁⟩ := hT x
    obtain ⟨h₂, hh₂, e₂⟩ := hT y
    refine ⟨⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁)⟩, ?_⟩
    show (h₂ * h₁⁻¹) x = y
    rw [← e₁, ← e₂]
    simp⟩
  have h7 : Nat.Prime (Nat.card (Fin 7)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hpp : IsPreprimitive H (Fin 7) := IsPreprimitive.of_prime_card h7
  have hcH : (vOneF 1 * vTwoF 1) ^ 2 ∈ H :=
    pow_mem (mul_mem (Subgroup.mem_sup_left (show vOneF 1 ∈ vOne from ⟨1, rfl⟩))
      (Subgroup.mem_sup_right (show vTwoF 1 ∈ vTwo from ⟨1, rfl⟩))) 2
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hpp
    isThreeCycle_vOneF_mul_vTwoF_sq hcH

theorem eNine_le_centTwo : eNine ≤ centTwo := by
  rintro _ ⟨i, j, rfl⟩
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, eNineF_sign i j⟩
  rw [show cTwo = eNineF 0 1 by decide +kernel]
  exact eNineF_comm i j 0 1

theorem exists_gen_of_card_nine_alt7 (E : Subgroup (alternatingGroup (Fin 7)))
    (hE9 : Nat.card E = 9) :
    ∃ V₁ V₂ : Subgroup (alternatingGroup (Fin 7)), V₁ ⊔ V₂ = ⊤ ∧
      ¬ 3 ∣ Nat.card V₁ ∧ ¬ 3 ∣ Nat.card V₂ ∧
      E ≤ Subgroup.normalizer (V₁ : Set (alternatingGroup (Fin 7))) ∧
      E ≤ Subgroup.normalizer (V₂ : Set (alternatingGroup (Fin 7))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hE'9 : Nat.card (eNine.subgroupOf (alternatingGroup (Fin 7))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv,
      card_eNine]
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hE'p : IsPGroup 3 (eNine.subgroupOf (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (n := 2) (by rw [hE'9]; norm_num)
  have hEi : ¬ 3 ∣ E.index := by
    have h := E.index_mul_card
    rw [hE9, hcard] at h
    omega
  have hE'i : ¬ 3 ∣ (eNine.subgroupOf (alternatingGroup (Fin 7))).index := by
    have h := (eNine.subgroupOf (alternatingGroup (Fin 7))).index_mul_card
    rw [hE'9, hcard] at h
    omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hEp.toSylow hEi)
    (hE'p.toSylow hE'i)
  have hmem' : ∀ x : alternatingGroup (Fin 7), x ∈ E →
      g * x * g⁻¹ ∈ eNine.subgroupOf (alternatingGroup (Fin 7)) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ ((g • hEp.toSylow hEi : Sylow 3 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
        group
      rw [this, IsPGroup.toSylow_coe]
      exact hx
    rw [hg, IsPGroup.toSylow_coe] at hx'
    exact hx'
  let ψ : alternatingGroup (Fin 7) →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (MulAut.conj g).toMonoidHom
  have hψinj : Function.Injective ψ :=
    (alternatingGroup (Fin 7)).subtype_injective.comp (MulAut.conj g).injective
  have hrange : ψ.range = alternatingGroup (Fin 7) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1A : vOne ≤ alternatingGroup (Fin 7) := fun v hv => (vOne_le_centOne hv).2
  have h2A : vTwo ≤ alternatingGroup (Fin 7) := fun v hv => (vTwo_le_centTwo hv).2
  have hcard1 : Nat.card (vOne.comap ψ) = 4 := by
    rw [← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq, hrange,
      inf_eq_right.mpr h1A, card_vOne]
  have hcard2 : Nat.card (vTwo.comap ψ) = 4 := by
    rw [← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq, hrange,
      inf_eq_right.mpr h2A, card_vTwo]
  refine ⟨vOne.comap ψ, vTwo.comap ψ, ?_, by rw [hcard1]; norm_num, by rw [hcard2]; norm_num,
    fun x hx => ?_, fun x hx => ?_⟩
  ·
    refine top_le_iff.mp ?_
    rw [← Subgroup.map_le_map_iff_of_injective hψinj, Subgroup.map_sup, Subgroup.map_comap_eq,
      Subgroup.map_comap_eq, hrange, inf_eq_right.mpr h1A, inf_eq_right.mpr h2A,
      ← MonoidHom.range_eq_map, hrange]
    exact alternatingGroup_le_vOne_sup_vTwo
  · have hxE : ψ x ∈ eNine := Subgroup.mem_subgroupOf.mp (hmem' x hx)
    exact Subgroup.le_normalizer_comap ψ
      (mem_normalizer_of_le_of_normal_perm_seven vOne_le_centOne vOne_normal
        (eNine_le_centOne hxE))
  · have hxE : ψ x ∈ eNine := Subgroup.mem_subgroupOf.mp (hmem' x hx)
    exact Subgroup.le_normalizer_comap ψ
      (mem_normalizer_of_le_of_normal_perm_seven vTwo_le_centTwo vTwo_normal
        (eNine_le_centTwo hxE))

end Alt

section Lift

variable {G : Type} [Group G] [Finite G]

theorem mem_invariantPiSubgroups_of_inner {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (W : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (hW3 : ¬ 3 ∣ Nat.card W)
    (hWN : (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.normalizer (W : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    (W.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map L.subtype ∈
      invariantPiSubgroups L A (piCompl 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set K := W.comap π with hK
  set KG := K.map L.subtype with hKG
  have hKGL : KG ≤ L := Subgroup.map_subtype_le K
  have hcKG : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective L.subtype_injective
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hπk : π k ∈ W := k.2
    have hk3 : (k : ↥L) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one, Subgroup.coe_one]
    have hπ1 : π (k : ↥L) = 1 := by
      have ho1 : orderOf (⟨π k, hπk⟩ : W) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [← map_pow, hk3]))
      have ho2 : orderOf (⟨π k, hπk⟩ : W) ∣ Nat.card W := orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_three).mp ho1 with h1 | h1
      · have := orderOf_eq_one_iff.mp h1
        exact congrArg Subtype.val this
      · have h3W : 3 ∣ Nat.card W := by
          have h2 := ho2
          rwa [h1] at h2
        exact absurd h3W hW3
    have hkθ : (k : ↥L) ∈ θ := by
      rw [← QuotientGroup.eq_one_iff]
      exact hπ1
    have hk1 : (k : ↥L) = 1 := eq_one_of_mem_aschbacherSolvableCore hkθ hk3
    have : orderOf k = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hk1
    omega
  have hAKG : A ≤ Subgroup.normalizer (KG : Set G) := by
    rw [hAc]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer (hKGL hx))
    · intro b hb
      obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.mp hb
      have hbAb : π ⟨b, hbL⟩ ∈ (A.subgroupOf L).map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbA)
      have hbN : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.normalizer (K : Set ↥L) :=
        Subgroup.le_normalizer_comap π (show π ⟨b, hbL⟩ ∈ _ from hWN hbAb)
      exact Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hbN)
  exact ⟨hKGL, (isPiSubgroup_piCompl_iff Nat.prime_three KG).mpr (by rwa [hcKG]), hAKG⟩

theorem le_sSup_of_a7
    (h131 : Item131) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) :
    L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
  have hD := h.toSec13Data
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have hZ := Sec15.center_eq_bot_of_types hLc (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  have hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rintro ⟨p, e, hp, -, hiso⟩
    exact not_isoLThreePi_of_card_eq_2520 hcard p e hiso
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 KFacts.KS14.sporadicModels131 hD hZ hnL3
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  set Ab := (A.subgroupOf L).map π with hAb
  have hAb9 : Nat.card Ab = 9 := by
    rw [hAb, hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  set E := Ab.map φ.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by rw [hE, Subgroup.card_map_of_injective φ.injective, hAb9]
  obtain ⟨V₁, V₂, hV, hV₁3, hV₂3, hEV₁, hEV₂⟩ := exists_gen_of_card_nine_alt7 E hE9
  have hAbE : Ab = E.map φ.symm.toMonoidHom := by
    rw [hE, Subgroup.map_map]
    ext x
    simp
  have hN : ∀ V : Subgroup (alternatingGroup (Fin 7)),
      E ≤ Subgroup.normalizer (V : Set (alternatingGroup (Fin 7))) →
      Ab ≤ Subgroup.normalizer ((V.map φ.symm.toMonoidHom : Subgroup _) : Set _) := by
    intro V hEV
    rw [hAbE, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hEV
  have hc3 : ∀ V : Subgroup (alternatingGroup (Fin 7)), ¬ 3 ∣ Nat.card V →
      ¬ 3 ∣ Nat.card (V.map φ.symm.toMonoidHom) := fun V hV3 => by
    rwa [Subgroup.card_map_of_injective φ.symm.injective]
  set W₁ := V₁.map φ.symm.toMonoidHom with hW₁
  set W₂ := V₂.map φ.symm.toMonoidHom with hW₂
  have hW : W₁ ⊔ W₂ = ⊤ := by
    rw [hW₁, hW₂, ← Subgroup.map_sup, hV, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr φ.symm.surjective
  have hK₁ := mem_invariantPiSubgroups_of_inner h hAc W₁ (hc3 V₁ hV₁3) (hN V₁ hEV₁)
  have hK₂ := mem_invariantPiSubgroups_of_inner h hAc W₂ (hc3 V₂ hV₂3) (hN V₂ hEV₂)
  have htop : W₁.comap π ⊔ W₂.comap π = ⊤ := by
    have hker : π.ker ≤ W₁.comap π ⊔ W₂.comap π :=
      (Subgroup.ker_le_comap π W₁).trans le_sup_left
    rw [← sup_eq_left.mpr hker, ← Subgroup.comap_map_eq, Subgroup.map_sup,
      Subgroup.map_comap_eq_self_of_surjective hπs, Subgroup.map_comap_eq_self_of_surjective hπs,
      hW, Subgroup.comap_top]
  intro l hl
  have hl' : (⟨l, hl⟩ : ↥L) ∈ W₁.comap π ⊔ W₂.comap π := htop ▸ Subgroup.mem_top _
  have hlmap : l ∈ (W₁.comap π ⊔ W₂.comap π).map L.subtype :=
    ⟨⟨l, hl⟩, hl', rfl⟩
  rw [Subgroup.map_sup] at hlmap
  exact (sup_le (le_sSup hK₁) (le_sSup hK₂)) hlmap

theorem eq_delta_of_gen' {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h142 : Concl142 A (lB A)) (hgen : L ≤ sSup (invariantPiSubgroups L A (piCompl 3))) :
    L = delta A (lB A) L := by
  refine le_antisymm (hgen.trans (sSup_le fun Q hQ => ?_)) (delta_le L)
  obtain ⟨hQL, hQ3, hAQ⟩ := hQ
  exact le_delta (mem_scriptQ_of_concl142 h142 h.zpowers_mem_omegaA
    ⟨hQL.trans (h.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)), hQ3,
      hAQ⟩) hQL

theorem mem_scriptY4_of_a7
    (h131 : Item131) (h135 : Item135) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) (h142 : Concl142 A (lB A))
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) :
    L ∈ scriptY4 A (lB A) := by
  have hD := h.toSec13Data
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  exact ⟨⟨hLtop, hD.le_normalizer⟩, eq_oPrimeResidualOf_of_sec15R h,
    eq_delta_of_gen' h h142 (le_sSup_of_a7 h131 h φ), h135 G A c L hD h.hypS_or_hypT⟩

end Lift

end Proof163L4A7

open Proof163L4A7

theorem step163L4A7_of
    (h131 : Item131) (h142 : Concl142R) (h135 : Item135) :
    Step163L4A7 := by
  intro G _ _ A c L h ⟨φ⟩ _ _ _ _
  exact mem_scriptY4_of_a7 h131 h135 h (h142 G A c L h) φ

end CFSG.RankThree.PartTwo.Sec16
