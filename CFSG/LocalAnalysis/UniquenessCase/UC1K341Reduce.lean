module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S3Defs341

import CFSG.RankThree.Theta.SolvableLocalQuotientAlpha
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.Theta

@[expose] def Local422 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G →
    CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 →
    ∀ A : Subgroup G,
      Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
      (∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G)) →
      ∀ c : G, c ∈ A → ∀ hc : c ∈ Subgroup.center G, c ≠ 1 →
        (haveI : (Subgroup.zpowers c).Normal :=
            Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc);
          thetaAlpha 3 (A.map (QuotientGroup.mk' (Subgroup.zpowers c))) ≤
            aschbacherSolvableCore 3 (G ⧸ Subgroup.zpowers c)) ∨
        ∃ L ∈ thetaComponents 3 G, Nat.card (autThetaQuot A L) = 9 ∧
          thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥

theorem mem_hyperplanes_three_iff {G : Type} [Group G] [Finite G] {A E : Subgroup G}
    (hA : Nat.card A = 27) : E ∈ hyperplanes 3 A ↔ E ≤ A ∧ Nat.card E = 9 := by
  have key : ∀ hEA : E ≤ A, Nat.card E * E.relIndex A = 27 := by
    intro hEA
    have h := Subgroup.card_mul_index (E.subgroupOf A)
    have hc : Nat.card (E.subgroupOf A) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv
    rw [hc, hA] at h
    exact h
  constructor
  · rintro ⟨hEA, hrel⟩
    refine ⟨hEA, ?_⟩
    have := key hEA
    rw [hrel] at this
    omega
  · rintro ⟨hEA, hcard⟩
    refine ⟨hEA, ?_⟩
    have := key hEA
    rw [hcard] at this
    omega

theorem central_line_quotient_of_local
    (P : (G : Type) → [Group G] → [Finite G] → Prop)
    (Q : (G : Type) → [Group G] → [Finite G] → Subgroup G → Prop)
    (h : ∀ (G : Type) [Group G] [Finite G], P G → ∀ A : Subgroup G, Q G A →
      Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
      (∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G)) →
      ∀ c : G, c ∈ A → ∀ hc : c ∈ Subgroup.center G, c ≠ 1 →
        (haveI : (Subgroup.zpowers c).Normal :=
            Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc);
          thetaAlpha 3 (A.map (QuotientGroup.mk' (Subgroup.zpowers c))) ≤
            aschbacherSolvableCore 3 (G ⧸ Subgroup.zpowers c)) ∨
        ∃ L ∈ thetaComponents 3 G, Nat.card (autThetaQuot A L) = 9 ∧
          thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥)
    {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (hAe : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (hmax : Maximal (fun B : Subgroup G => CFSG.Open.IsElemAbelian 3 B) A)
    (hP : ∀ x ∈ A, x ≠ 1 → P ↥(Subgroup.centralizer ({x} : Set G)))
    (hQ : ∀ x ∈ A, x ≠ 1 → Q ↥(Subgroup.centralizer ({x} : Set G))
      (A.subgroupOf (Subgroup.centralizer ({x} : Set G))))
    (h1 : ∀ x ∈ A, x ≠ 1 → ∀ L ∈ thetaComponentsAt 3 x, A ≤ Subgroup.normalizer (L : Set G))
    (h2 : ∀ x ∈ A, x ≠ 1 → ∀ L ∈ thetaComponentsAt 3 x, Nat.card (autThetaQuot A L) = 9 →
      thetaAlpha 3 ((autThetaQuot A L).subgroupOf
        (autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)) = ⊥) :
    ∀ a ∈ A, a ≠ 1 →
      thetaAlpha 3 ((A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
          (QuotientGroup.mk' (centralLine a))) ≤
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G) ⧸ centralLine a) := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  intro a ha ha1
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx a ha)
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  have hmax' : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'e, fun B hB hAB => ?_⟩
    have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x, hx, rfl⟩ := x
        obtain ⟨_, y, hy, rfl⟩ := y
        apply Subtype.ext
        change (x : G) * y = y * x
        exact congrArg Subtype.val
          (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      · rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hB.2 x hx)
    have hAB' : A ≤ B.map C.subtype := fun x hx =>
      ⟨⟨x, hAC hx⟩, hAB (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hBA := hmax.2 hBe hAB'
    intro x hx
    have : (x : G) ∈ A := hBA ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr this
  set c' : C := ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr ha
  have hc'Z : c' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hc'1 : c' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hnorm' : ∀ L' ∈ thetaComponents 3 C, A' ≤ Subgroup.normalizer (L' : Set C) := by
    intro L' hL' x hx
    have hLc : L'.map C.subtype ∈ thetaComponentsAt 3 a := ⟨L', hL', rfl⟩
    exact (Sec13.coe_mem_normalizer_map_iff C).mp
      (h1 a ha ha1 _ hLc (Subgroup.mem_subgroupOf.mp hx))
  rcases h C (hP a ha ha1) A' (hQ a ha ha1) hmax' h27' hnorm' c' hc'A hc'Z hc'1 with
    h1' | ⟨L', hL', h9, hα⟩
  · exact h1'
  · exfalso
    set L := L'.map C.subtype with hLdef
    have hLc : L ∈ thetaComponentsAt 3 a := ⟨L', hL', rfl⟩
    have hAut : Nat.card (autThetaQuot A L) = 9 := by
      rw [← hA'map, hLdef, ← Sec13.map_autThetaQuot_sub C A' L',
        Subgroup.card_map_of_injective (MulAut.congr (Sec13.thetaQuotEquivSub C L')).injective,
        h9]
    have hαC : thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot C L)) ≠ ⊥ := by
      have hC' : (⊤ : Subgroup C).map C.subtype = C := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← (Sec13.thetaAlpha_subgroupOf_map_ne_bot_iff
        (MulAut.congr (Sec13.thetaQuotEquivSub C L'))
        (autThetaQuot A' L') (autThetaQuot ⊤ L'))] at hα
      rwa [Sec13.map_autThetaQuot_sub, Sec13.map_autThetaQuot_sub, hA'map, hC'] at hα
    exact hαC (h2 a ha ha1 L hLc hAut)

theorem concl_of_central_line_quotient {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (hAe : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (hquot : ∀ a ∈ A, a ≠ 1 →
      thetaAlpha 3 ((A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
          (QuotientGroup.mk' (centralLine a))) ≤
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G) ⧸ centralLine a)) :
    (∀ E ∈ hyperplanes 3 A,
      Group.IsSolvable ↥(thetaAlpha 3 E) ∧ Nat.Coprime 3 (Nat.card ↥(thetaAlpha 3 E))) ∧
    (∀ E ∈ hyperplanes 3 A, ∀ D ∈ hyperplanes 3 A, thetaAlpha 3 E = thetaAlpha 3 D) := by
  have H := CFSG.RankThree.Theta.part_two_solvable_local_quotient_alpha_criterion A hAe h27 hquot
  refine ⟨fun E hE => ?_, fun E hE D hD => ?_⟩
  · obtain ⟨hEA, hEc⟩ := (mem_hyperplanes_three_iff h27).mp hE
    exact H.1 E hEA hEc
  · obtain ⟨hEA, hEc⟩ := (mem_hyperplanes_three_iff h27).mp hE
    obtain ⟨hDA, hDc⟩ := (mem_hyperplanes_three_iff h27).mp hD
    exact H.2.1 E D hEA hEc hDA hDc

theorem k341_of_local422 (h : Local422) : K341 := by
  intro G _ _ A hAe h27 hmax hK hr h1 h2
  exact concl_of_central_line_quotient A hAe h27 (central_line_quotient_of_local
    (fun G _ _ => CFSG.IsKGroup G ∧ CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3)
    (fun _ _ _ _ => True)
    (fun G _ _ hP A _ => h G hP.1 hP.2 A) A hAe h27 hmax
    (fun x hx hx1 => ⟨CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple (hK x hx hx1), hr x hx hx1⟩)
    (fun _ _ _ => trivial) h1 h2)

theorem aschCore_le_normalizer_of_indep {X : Type} [Group X] [Finite X] (A : Subgroup X)
    (hAcard : Nat.card A = 27)
    (hind : ∀ E ∈ hyperplanes 3 A, ∀ D ∈ hyperplanes 3 A, thetaAlpha 3 E = thetaAlpha 3 D)
    {B : Subgroup X} (hB : B ∈ hyperplanes 3 A) :
    CFSG.Assembly.RankThreeEven.aschCore 2 3 A ≤ Subgroup.normalizer (thetaAlpha 3 B : Set X) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h27 : Nat.card A = 3 ^ 3 := by rw [hAcard]; norm_num
  obtain ⟨hBA, hBc⟩ := (mem_hyperplanes_three_iff hAcard).mp hB
  have hind' : ∀ B D : Subgroup X, B ≤ A → Nat.card B = 9 → D ≤ A → Nat.card D = 9 →
      thetaAlpha 3 B = thetaAlpha 3 D := fun B D hBA hB hDA hD =>
    hind B ((mem_hyperplanes_three_iff hAcard).mpr ⟨hBA, hB⟩) D
      ((mem_hyperplanes_three_iff hAcard).mpr ⟨hDA, hD⟩)
  refine sSup_le ?_
  have key : ∀ g : X, ∀ E : Subgroup X, E ≤ A → Nat.card E = 9 → conjugate E g ≤ A →
      g⁻¹ ∈ Subgroup.normalizer (thetaAlpha 3 B : Set X) := by
    intro g E hEA hE hEgA
    have hEg : Nat.card (conjugate E g) = 9 := by
      rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE]
    have h : conjugate (thetaAlpha 3 B) g = thetaAlpha 3 B :=
      calc conjugate (thetaAlpha 3 B) g = conjugate (thetaAlpha 3 E) g := by
            rw [hind' B E hBA hBc hEA hE]
        _ = thetaAlpha 3 (conjugate E g) := thetaAlpha_conjugate hp E g
        _ = thetaAlpha 3 B := hind' _ B hEgA hEg hBA hBc
    exact mem_normalizer_of_map_conj_eq_self h
  rintro _ ⟨U, hUA, hU2, -, rfl⟩ g hg
  have h9 : ∀ K : Subgroup X, Nat.card K = 3 ^ 2 → Nat.card K = 9 := fun K hK => by
    rw [hK]; norm_num
  rcases card_eq_or_eq_of_two_le_pRank hp h27 hUA hU2 with hUc | hUeq
  · have h := key g⁻¹ U hUA (h9 U hUc) ((conjugate_inv_le_of_mem_normalizer hg).trans hUA)
    rwa [inv_inv] at h
  · rw [hUeq] at hg
    have h := key g⁻¹ B hBA hBc
      ((Subgroup.map_mono hBA).trans (conjugate_inv_le_of_mem_normalizer hg))
    rwa [inv_inv] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
