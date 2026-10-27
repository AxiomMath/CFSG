module

public import CFSG.RankThree.PartTwo.Sec10.Sec10X
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
public import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Item463Inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ a ∈ A, a ∈ Subgroup.center G → a ≠ 1 → Odd (Nat.card (aschbacherSolvableCore 3 G)) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
      Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)),
        A⁆ : Subgroup G)) →
      ∃ L ∈ thetaComponents 3 G,
        (haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
          Nonempty (L ⧸ solvableRadical L ≃* alternatingGroup (Fin 7)) ∨
            Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M12) ∨
            Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.J2) ∨
            Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M22) ∨
            (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
              Sec4.IsoLThreePi (L ⧸ solvableRadical L) p e) ∨
            Nonempty (L ⧸ solvableRadical L ≃* projSL 2 (GaloisField 3 3))) ∧
        ∃ V ∈ invariantPiSubgroups L A (piOf 2), V ≠ ⊥

namespace Sec10XProof

section List

open CFSG.Blueprint

theorem isoLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi Y p f) : Sec4.IsoLThreePi X p f := by
  rcases h with ⟨h1, ⟨e'⟩⟩ | ⟨h1, ⟨e'⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h1, ⟨e.trans e'⟩⟩

theorem sec10XList {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hθ : aschbacherSolvableCore 3 Q = ⊥) {P : Type} [Group P]
    (eS : Q ⧸ Subgroup.center Q ≃* P)
    (hlist : Nonempty (P ≃* alternatingGroup (Fin 7)) ∨ Nonempty (P ≃* NativeSporadic.M12) ∨
      Nonempty (P ≃* NativeSporadic.J2) ∨ Nonempty (P ≃* NativeSporadic.M22) ∨
      (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧ Sec4.IsoLThreePi P p e) ∨
      Nonempty (P ≃* projSL 2 (GaloisField 3 3)))
    (hLF : Item1015Proof.ListFacts Q → False) :
    (Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ Nonempty (Q ≃* NativeSporadic.M12) ∨
        Nonempty (Q ≃* NativeSporadic.J2) ∨ Nonempty (Q ≃* NativeSporadic.M22) ∨
        ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
          (Sec4.IsoLThreePi Q p e ∨ Sec4.IsSLThreePiAt Q (p ^ e))) ∨
      Nonempty (Q ≃* projSL 2 (GaloisField 3 3)) := by
  have : Group.IsPerfect Q := hQ.1
  have hZ3 := isPGroup_center_of_theta_eq_bot hθ
  have hbot : Subgroup.center Q = ⊥ → Nonempty (Q ≃* P) := fun hZ =>
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eS⟩
  rcases hlist with he | he | he | he | ⟨p, f, hpf, hp3, hf1, hf2, hL⟩ | he
  · obtain ⟨e⟩ := he
    by_cases hZ : Subgroup.center Q = ⊥
    · obtain ⟨e'⟩ := hbot hZ
      exact Or.inl (Or.inl ⟨e'.trans e⟩)
    · exact (hLF (listFacts_of_quotient_list hQ (Or.inl ⟨eS.trans e⟩))).elim
  · obtain ⟨e⟩ := he
    by_cases hZ : Subgroup.center Q = ⊥
    · obtain ⟨e'⟩ := hbot hZ
      exact Or.inl (Or.inr (Or.inl ⟨e'.trans e⟩))
    · exact (hLF (listFacts_of_quotient_list hQ (Or.inr (Or.inl ⟨eS.trans e⟩)))).elim
  · obtain ⟨e⟩ := he
    by_cases hZ : Subgroup.center Q = ⊥
    · obtain ⟨e'⟩ := hbot hZ
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨e'.trans e⟩)))
    · exact (hLF (listFacts_of_quotient_list hQ (Or.inr (Or.inr (Or.inl ⟨eS.trans e⟩))))).elim
  · obtain ⟨e⟩ := he
    by_cases hZ : Subgroup.center Q = ⊥
    · obtain ⟨e'⟩ := hbot hZ
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨e'.trans e⟩))))
    · exact (hLF (listFacts_of_quotient_list hQ
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨eS.trans e⟩)))))).elim
  · by_cases hZ : Subgroup.center Q = ⊥
    · obtain ⟨e'⟩ := hbot hZ
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, f, hpf, hp3, hf1, hf2, Or.inl (isoLThreePi_of_mulEquiv e' hL)⟩))))
    · exact (hLF (listFacts_of_quotient_list hQ (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, f, hpf, hp3, hf1, hf2, isoLThreePi_of_mulEquiv eS hL⟩)))))).elim
  · obtain ⟨e⟩ := he
    have hZ := center_eq_bot_of_psl2_27 hZ3 ((eS.trans e).trans (Sec4.projSLEquivPSL _))
    obtain ⟨e'⟩ := hbot hZ
    exact Or.inr ⟨e'.trans e⟩

end List

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) :
    Subgroup.centralizer ((K.subgroupOf H : Subgroup H) : Set H) =
      (Subgroup.centralizer (K : Set G)).subgroupOf H := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy k hk
    exact congrArg Subtype.val (hy ⟨k, hKH hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
  · intro hy k hk
    exact Subtype.ext (hy k (Subgroup.mem_subgroupOf.mp hk))

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {K : Subgroup G} (H : Subgroup G)
    (hK : CFSG.Assembly.IsElemAbelian p K) : CFSG.Assembly.IsElemAbelian p (K.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hK H

omit [Finite G] in
theorem card_subgroupOf_of_le {K H : Subgroup G} (hKH : K ≤ H) :
    Nat.card (K.subgroupOf H) = Nat.card K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv

omit [Finite G] in
theorem mem_normalizer_map_subtype {H : Subgroup G} {V : Subgroup H} {x : H}
    (hx : x ∈ Subgroup.normalizer (V : Set H)) :
    (x : G) ∈ Subgroup.normalizer ((V.map H.subtype : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_map H.subtype ⟨x, hx, rfl⟩

end Transport

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem le_centralizer_of_mem (h : Sec10Std G A c L a R) {d : G} (hdA : d ∈ A) :
    A ≤ Subgroup.centralizer ({d} : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx hdA)

theorem odd_card_theta_centralizer (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) :
    Odd (Nat.card (aschbacherSolvableCore 3 (Subgroup.centralizer ({d} : Set G)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set Θ := inSubgroup (aschbacherSolvableCore 3) C with hΘ
  have hcardΘ : Nat.card Θ = Nat.card (aschbacherSolvableCore 3 C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  rw [← hcardΘ, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  set D := sec10D c R L with hD
  have hdD : d ∈ D := h.inf_le_D (h.d_mem_inf hdL)
  have hDC : D ≤ C := fun x hx => by
    have hxd := congrArg Subtype.val (h.isElemAbelian_D.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdD⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxd
  have hDN : D ≤ Subgroup.normalizer (Θ : Set G) := hDC.trans (Sec6.le_normalizer_theta C)
  have h3 : ¬ 3 ∣ Nat.card Θ := hcardΘ ▸ not_three_dvd_card_theta C
  obtain ⟨T, -, hT1, hT2, hDT⟩ := exists_pGroup_le_normalizer (p := 3) (q := 2)
    (Sec4.isPGroup_of_isElemAbelian h.isElemAbelian_D) h3 h2 hDN
  have hE : R ⊓ L ∈ partTwoE G :=
    ⟨h.isElemAbelian_inf, h.card_inf, T, hT1, hT2, h.inf_le_D.trans hDT⟩
  rw [h.partTwoE_eq h.card_eq] at hE
  have hDE := hE.2.1 D h.isElemAbelian_D h.inf_le_D
  have h81 : Nat.card D = 81 := h.card_D
  rw [hDE, h.card_inf] at h81
  norm_num at h81

theorem card_closure_a_d (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hd3 : orderOf d = 3) : Nat.card (Subgroup.closure ({a, d} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have ha3 : a ^ 3 = 1 := h.pow_three h.a_mem
  have hcl : Subgroup.closure ({a, d} : Set G) = Subgroup.zpowers d ⊔ Subgroup.zpowers a := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, sup_comm]
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) :
      Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (h.comm hdA h.a_mem) k).eq
  have had : a ∉ Subgroup.zpowers d := fun ha =>
    h.a_not_mem_L ((hdL ▸ ha : a ∈ A ⊓ L).2)
  rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
    (disjoint_zpowers_of_pow_three ha3 had), Nat.card_zpowers, Nat.card_zpowers, hd3,
    orderOf_eq_prime ha3 h.a_ne_one]

theorem exists_mem_thetaComponentsAt_of_fourGroup (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h463 : Item463Inv) (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    {U : Subgroup G} (hU : U ∈ fourGroupsMinus A)
    (hUθ : U ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G))) :
    ∃ X ∈ thetaComponentsAt 3 d,
      ((Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
          ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
            (Sec4.IsoLThreePi (X ⧸ aschbacherSolvableCore 3 X) p e ∨
              Sec4.IsSLThreePiAt (X ⧸ aschbacherSolvableCore 3 X) (p ^ e))) ∨
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField 3 3))) ∧
      ∃ U ∈ invariantPiSubgroups X (Subgroup.zpowers c) (piOf 2), U ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  have hdA := h.d_mem_A hdL
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hAC : A ≤ C := le_centralizer_of_mem h hdA
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsec4 : SectionFourHyp C := h.toTheoremFourHyp.sectionFourHyp
    (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hd1)
  set A' := A.subgroupOf C with hA'
  have hA'map : A'.map C.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'el : CFSG.Assembly.IsElemAbelian 3 A' :=
    isElemAbelian_subgroupOf C h.mem_partTwoF.1
  have hA'max : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'el, fun B hB hAB => ?_⟩
    have hBG := Sec4.isElemAbelian_map C.subtype hB
    have hAB' : A ≤ B.map C.subtype := hA'map ▸ Subgroup.map_mono hAB
    have heq := h.mem_partTwoF.2.1 _ hBG hAB'
    intro y hy
    have hy' : (y : G) ∈ B.map C.subtype := ⟨y, hy, rfl⟩
    rw [heq] at hy'
    exact Subgroup.mem_subgroupOf.mpr hy'
  have hA'card : Nat.card A' = 27 := (card_subgroupOf_of_le hAC).trans h.card_eq
  set d' : C := ⟨d, hdC⟩ with hd'
  have hd'A : d' ∈ A' := Subgroup.mem_subgroupOf.mpr hdA
  have hd'Z : d' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hd'1 : d' ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  set B := Subgroup.closure ({a, d} : Set G) with hB
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact h.a_mem
    · exact hdA
  have hBC : B ≤ C := hBA.trans hAC
  set B' := B.subgroupOf C with hB'
  have hB'A' : B' ≤ A' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hBA (Subgroup.mem_subgroupOf.mp hx))
  have hB'card : Nat.card B' = 9 :=
    (card_subgroupOf_of_le hBC).trans (card_closure_a_d h hdL hd3)
  have hCB : Subgroup.centralizer (B : Set G) ≤ C :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.subset_closure (by simp)))
  have hθmap : (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B' : Set C))).map
      C.subtype = inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) := by
    rw [hB', centralizer_subgroupOf hBC, Sec6.map_inSubgroup_theta_of_injective C.subtype
      C.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hCB]
  have heven : Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer (B' : Set C)), A'⁆ : Subgroup C)) := by
    have hmap : (⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B' : Set C)),
        A'⁆ : Subgroup C).map C.subtype =
        ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)), A⁆ := by
      rw [Subgroup.map_commutator, hθmap, hA'map]
    rw [← Subgroup.card_map_of_injective C.subtype_injective, hmap]
    have hUle : U ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer (B : Set G)), A⁆ := by
      rw [hU.2]
      exact Subgroup.commutator_mono hUθ le_rfl
    have h4 : 4 ∣ Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer (B : Set G)), A⁆ : Subgroup G) := by
      rw [← hU.1.2.2]
      exact Subgroup.card_dvd_of_le hUle
    exact even_iff_two_dvd.mpr ((show 2 ∣ 4 by norm_num).trans h4)
  obtain ⟨L', hL', hlist, V', hV', hV'1⟩ := h463 C hsec4 A' hA'max hA'card d' hd'A hd'Z hd'1
    (odd_card_theta_centralizer h hdL) B' hB'A' hB'card heven
  set X := L'.map C.subtype with hX
  have hXd : X ∈ thetaComponentsAt 3 d := ⟨L', hL', rfl⟩
  obtain ⟨hV'L', hV'2, hV'A⟩ := hV'
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (h.comm h.mem_A hdA)
  have hVinv : V'.map C.subtype ∈ invariantPiSubgroups X (Subgroup.zpowers c) (piOf 2) := by
    refine ⟨Subgroup.map_mono hV'L', fun r hr => hV'2 r ?_, ?_⟩
    · rwa [Subgroup.card_map_of_injective C.subtype_injective] at hr
    · rw [Subgroup.zpowers_le]
      exact mem_normalizer_map_subtype (x := ⟨c, hcC⟩)
        (hV'A (Subgroup.mem_subgroupOf.mpr h.mem_A))
  have hV1 : V'.map C.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
  refine ⟨X, hXd, ?_, _, hVinv, hV1⟩
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXd
  obtain ⟨hθs, -, hθp, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθQ := (solvable_prime_complement_core_quotient_centralizers Nat.prime_three
    (aschbacherSolvableCore 3 X) hθs hθp).2.2.1
  set eQ : X ⧸ aschbacherSolvableCore 3 X ≃* L' ⧸ aschbacherSolvableCore 3 L' :=
    Sec4.thetaQuotCongr (L'.equivMapOfInjective C.subtype C.subtype_injective).symm with heQ
  have hc : (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)).map
      (eQ : X ⧸ aschbacherSolvableCore 3 X →* L' ⧸ aschbacherSolvableCore 3 L') =
      Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') := Subgroup.map_center_eq eQ
  have : (solvableRadical L').Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨eR⟩ := nonempty_quotient_center_mulEquiv (Y := L') hL'.2.2
  exact sec10XList hQ hθQ ((QuotientGroup.congr _ _ eQ hc).trans eR) hlist fun hLF =>
    Item1015Proof.false_of_listFacts h45 h97 h hdL hXd hLF hVinv hV1

end Std

end Sec10XProof

section Main

theorem sec10X_of_item1012 (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h1012 : Item1012)
    (h463 : Item463Inv) : Sec10X := by
  intro G _ _ A c L a R h d hdL
  obtain ⟨a', h', U, hU, hUθ⟩ := h1012 G A c L a R h d hdL
  exact Sec10XProof.exists_mem_thetaComponentsAt_of_fourGroup h45 h97 h463 h' hdL hU hUθ

end Main

end CFSG.RankThree.PartTwo.Sec10
