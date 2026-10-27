module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutFinal

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Plain


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem centralizer_structure_J3Plain {X : Type} [Group X] [Finite X]
    (e : X ≃* NativeSporadic.J3) {a : X} (ha3 : a ^ 3 = 1) (ha : a ≠ 1)
    (h5 : 5 ∣ Nat.card (centralizer ({e a} : Set NativeSporadic.J3))) :
    ∃ I : Subgroup X, I ≤ centralizer ({a} : Set X) ∧ ⁅I, I⁆ = I ∧
      Nonempty (↥I ≃* alternatingGroup (Fin 6)) ∧
      (∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ I) ∧
      Nat.card (centralizer ({a} : Set X)) = 1080 ∧
      Nat.card ↥(zpowers a) = 3 ∧ Disjoint (zpowers a) I ∧
      (∀ d ∈ zpowers a, ∀ x ∈ centralizer ({a} : Set X), d * x = x * d) ∧
      zpowers a ⊔ I = centralizer ({a} : Set X) := by
  obtain ⟨I, hIC, hIperf, ⟨eI⟩, hImax⟩ := perfect_core_centralizer_J3Plain e ha3 ha h5
  have hC1080 : Nat.card (centralizer ({a} : Set X)) = 1080 :=
    card_centralizer_of_equiv_J3 e ha3 ha h5
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha
  have hD3 : Nat.card ↥(zpowers a) = 3 := by rw [Nat.card_zpowers, hoa]
  have haC : a ∈ centralizer ({a} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hDC : zpowers a ≤ centralizer ({a} : Set X) := Subgroup.zpowers_le.2 haC
  have hDcomm : ∀ d ∈ zpowers a, ∀ x ∈ centralizer ({a} : Set X), d * x = x * d := by
    intro d hd x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact ((show Commute x a from Subgroup.mem_centralizer_singleton_iff.1 hx).symm.zpow_left k).eq
  have hDI : Disjoint (zpowers a) I := by
    rw [Subgroup.disjoint_def]
    intro t htD htI
    have hcen : (⟨t, htI⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro i
      exact Subtype.ext (hDcomm t htD i (hIC i.2)).symm
    rw [center_eq_bot_of_equiv_alt6 I eI, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hI360 : Nat.card I = 360 := by
    rw [Nat.card_congr eI.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hlow : 1080 ≤ Nat.card ↥(zpowers a ⊔ I) := by
    have := card_mul_le_card_sup_of_disjoint (zpowers a) I hDI
    rw [hD3, hI360] at this
    exact this
  have hsup : zpowers a ⊔ I ≤ centralizer ({a} : Set X) := sup_le hDC hIC
  have hCeq : zpowers a ⊔ I = centralizer ({a} : Set X) := by
    refine Subgroup.eq_of_le_of_card_ge hsup ?_
    omega
  exact ⟨I, hIC, hIperf, ⟨eI⟩, hImax, hC1080, hD3, hDI, hDcomm, hCeq⟩

end Plain

section LocalFrame

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

theorem CoverOut.equivJ3_apply (h : CoverOut A E U c L) (hZ : Subgroup.center L = ⊥) (x : ↥L) :
    h.equivJ3 hZ x = h.quot.some (x : ↥L ⧸ center ↥L) := rfl

theorem CoverOut.centralizer_inf_eq (h : CoverOut A E U c L) {l : ↥L} {i : ℤ} {a : G}
    (hai : a = (l : G) * c ^ i) :
    Subgroup.centralizer ({a} : Set G) ⊓ L = (Subgroup.centralizer ({l} : Set ↥L)).map L.subtype := by
  have hci : ∀ y ∈ L, c ^ i * y = y * c ^ i := fun y hy =>
    ((show Commute c y from h.c_comm y hy).zpow_left i).eq
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨⟨x, hxL⟩, Subtype.ext ?_, rfl⟩
    have h1 : x * ((l : G) * c ^ i) = ((l : G) * c ^ i) * x := by rw [← hai]; exact hx
    have h2 : x * (l : G) * c ^ i = (l : G) * x * c ^ i := by
      calc x * (l : G) * c ^ i = x * ((l : G) * c ^ i) := by group
        _ = ((l : G) * c ^ i) * x := h1
        _ = (l : G) * (c ^ i * x) := by group
        _ = (l : G) * (x * c ^ i) := by rw [hci x hxL]
        _ = (l : G) * x * c ^ i := by group
    exact mul_right_cancel h2
  · rintro ⟨x', hx', rfl⟩
    refine ⟨?_, x'.2⟩
    have hx'' : (x' : G) * (l : G) = (l : G) * x' := congrArg Subtype.val hx'
    rw [hai]
    calc (x' : G) * ((l : G) * c ^ i) = ((x' : G) * (l : G)) * c ^ i := by group
      _ = ((l : G) * x') * c ^ i := by rw [hx'']
      _ = (l : G) * (x' * c ^ i) := by group
      _ = (l : G) * (c ^ i * x') := by rw [hci x' x'.2]
      _ = ((l : G) * c ^ i) * x' := by group

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.local_frame (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    ∃ (l : ↥L) (I' : Subgroup ↥L), (l : G) ∈ A ∧ (∃ i : ℤ, a = (l : G) * c ^ i) ∧ l ≠ 1 ∧
      l ^ 3 = 1 ∧ NonCentral 3 (l : ↥L ⧸ center ↥L) ∧
      I' ≤ Subgroup.centralizer ({l} : Set ↥L) ∧ ⁅I', I'⁆ = I' ∧
      Nonempty (↥I' ≃* alternatingGroup (Fin 6)) ∧ iCore L a = I'.map L.subtype ∧
      (∀ P' : Subgroup ↥L, P' ≤ Subgroup.centralizer ({l} : Set ↥L) → ⁅P', P'⁆ = P' → P' ≤ I') ∧
      Nat.card ↥(Subgroup.zpowers l) = 3 ∧ Disjoint (Subgroup.zpowers l) I' ∧
      (∀ d ∈ Subgroup.zpowers l, ∀ x ∈ Subgroup.centralizer ({l} : Set ↥L), d * x = x * d) ∧
      Subgroup.zpowers l ⊔ I' = Subgroup.centralizer ({l} : Set ↥L) ∧
      dGroup a c = Subgroup.zpowers (l : G) ⊔ Subgroup.zpowers c ∧
      dGroup a c ⊓ L = Subgroup.zpowers (l : G) := by
  have hZ := h.center_eq_bot h45
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3', hlnc, hDeq, hDL, -, -⟩ := h.dgroup_decomp h45 hfr
  have hl3 : l ^ 3 = 1 := Subtype.ext hl3'
  have hlq3 : (l : ↥L ⧸ center ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hl3]; rfl
  have hlq1 : (l : ↥L ⧸ center ↥L) ≠ 1 := fun h1 => by
    have := (QuotientGroup.eq_one_iff l).1 h1
    rw [hZ, Subgroup.mem_bot] at this
    exact hl1 this
  have h5q := five_dvd_centralizer_of_nonCentral h.quot.some hlq3 hlq1 hlnc
  have h5 : 5 ∣ Nat.card (centralizer ({h.equivJ3 hZ l} : Set NativeSporadic.J3)) := by
    rw [h.equivJ3_apply hZ]; exact h5q
  obtain ⟨I', hI'C, hI'perf, hφ, hI'max, -, hD3, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Plain (h.equivJ3 hZ) hl3 hl1 h5
  have hI : iCore L a = I'.map L.subtype := by
    unfold iCore
    rw [h.centralizer_inf_eq hai]
    exact CFSG.AGLEmbeddingD2.Wilson.Proving.perfCore_map_of_greatest L.subtype
      L.subtype_injective _ I' hI'C hI'perf hI'max
  exact ⟨l, I', hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hI'C, hI'perf, hφ, hI, hI'max, hD3, hDI, hDcomm,
    hCeq, hDeq, hDL⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.exists_component_ge_iCore (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5)
    (h : CoverOut A E U c L) {a : G} (hfr : Frame217 E c L a) :
    ∃ K' ∈ thetaComponentsAt 3 a, iCore L a ≤ K' := by
  have hEA : E ≤ A := h.pair.mem_E.2
  obtain ⟨l, I', hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hI'C, hI'perf0, ⟨φ⟩, hI, hI'max, -⟩ :=
    h.local_frame h45 hfr
  have hpair := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hcE : c ∈ E := hpair.1.1
  have hc1 : c ≠ 1 := hpair.2.1
  have ha1 : a ≠ 1 := fun h1 => hfr.not_mem (h1 ▸ Subgroup.one_mem _)
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({a} : Set G)) :=
    h.pair.toSec21Std.standing.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one h.pair.toSec21Std.standing.toTheoremFourHyp ha1)
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_thetaComponentsAt
  have hE27 := Late.isE27_of_mem_partTwoE h.pair.mem_E.1
  obtain ⟨hJperf0, -⟩ : Group.IsPerfect ↥(perfectResidual ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
      True := ⟨(perfect_residual_characterization
        (G := ↥(L ⊓ Subgroup.centralizer ({a} : Set G)))).2.2.1, trivial⟩
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) with hJ
  have hJperf : Group.IsPerfect ↥J :=
    Group.IsPerfect.ofSurjective
      (f := ((perfectResidual ↥(L ⊓ Subgroup.centralizer ({a} : Set G))).equivMapOfInjective _
        (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
  have hJC : J ≤ Subgroup.centralizer ({a} : Set G) ⊓ L := by
    rw [inf_comm]; exact Subgroup.map_subtype_le _
  have hJle : J ≤ iCore L a := le_sSup ⟨hJC, (isPerfect_iff_commutator_eq J).1 hJperf⟩
  have hIperf : ⁅I', I'⁆ = I' := perfect_of_equiv_alt6 I' φ
  have hIle : iCore L a ≤ J := by
    rw [hI]
    refine KFacts.le_inSubgroup_perfectResidual ?_ ?_
    · refine (isPerfect_iff_commutator_eq _).2 ?_
      rw [← Subgroup.map_commutator, hIperf]
    · have hIC : iCore L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := by
        rw [inf_comm]; exact sSup_le fun _ hK => hK.1
      rwa [hI] at hIC
  have hJI : J = iCore L a := le_antisymm hJle hIle
  have hJq : IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
    have e : ↥J ≃* alternatingGroup (Fin 6) :=
      (MulEquiv.subgroupCongr (hJI.trans hI)).trans
        (((I'.equivMapOfInjective L.subtype L.subtype_injective).symm).trans φ)
    have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have : IsSimpleGroup ↥J := @MulEquiv.isSimpleGroup _ _ _ _ hA6 e
    refine isQuasisimple_quot_theta_of_simple ?_
    by_contra hcomm
    push Not at hcomm
    letI : CommGroup ↥J := { (inferInstance : Group ↥J) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := ↥J)
    have hcard : Nat.card ↥J = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    rw [hcard] at hp
    exact absurd hp (by norm_num)
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hE27 hcE
    hfr.mem hc1 hLc hJq
  exact ⟨K', hK', hJI ▸ hJK'⟩

end LocalFrame

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
