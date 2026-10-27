module

public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.KFacts.KS12Covers
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank projSU)

section General

variable {G : Type} [Group G] [Finite G]

theorem centralizer_ne_top_of_theoremFourHyp (hG : TheoremFourHyp G) {c : G} (hc : c ≠ 1) :
    Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro hCt
  have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
    have hg : g ∈ Subgroup.centralizer ({c} : Set G) := hCt ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases hG.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hcZ
    exact hc hcZ
  · obtain ⟨a, b, hab⟩ := hG.nonabelian
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem localRank_quot_add_one_le_of_centralizes (L : Subgroup G) (N : Subgroup L) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {z : G} (hz : z ∈ Subgroup.centralizer (L : Set G))
    (hz3 : orderOf z = 3) (hzL : z ∉ L) (hpos : 0 < localRank 3 (L ⧸ N)) :
    localRank 3 (L ⧸ N) + 1 ≤ localRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, ⟨U, hU0, hU2, rfl⟩, hHk⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3 Nat.prime_three (L ⧸ N)
      hpos
  obtain ⟨E, hEH, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt
    (Subgroup.normalizer (U : Set (L ⧸ N)))
  obtain ⟨S, hSE, hS, hScard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN hE
  set D : Subgroup L := U.comap (QuotientGroup.mk' N) with hDdef
  have hSD : S ≤ Subgroup.normalizer (D : Set L) := by
    intro s hs
    have hsE : (QuotientGroup.mk' N) s ∈ Subgroup.normalizer (U : Set (L ⧸ N)) := hEH (hSE hs)
    rw [Subgroup.mem_normalizer_iff] at hsE ⊢
    intro d
    change (QuotientGroup.mk' N) d ∈ U ↔ (QuotientGroup.mk' N) (s * d * s⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hsE _
  have hDcard : Nat.card D = Nat.card N * Nat.card U :=
    QuotientGroup.card_preimage_mk N (U : Set (L ⧸ N))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hU0 ((Subgroup.card_eq_one).mp hm)
  set S' : Subgroup G := S.map L.subtype
  set D' : Subgroup G := D.map L.subtype
  have hD'card : Nat.card D' = Nat.card N * 2 ^ m := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hDcard, hm]
  have hcop : Nat.Coprime 3 (Nat.card D') := by
    rw [hD'card]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
      (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card D' := by
    rw [hD'card]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hS' : CFSG.Assembly.IsElemAbelian 3 S' := Sec4.Census.isElemAbelian_map_subtype hS
  have hS'L : S' ≤ L := Subgroup.map_subtype_le _
  have hD'L : D' ≤ L := Subgroup.map_subtype_le _
  have hzc : z ∈ Subgroup.centralizer (S' : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => Subgroup.mem_centralizer_iff.mp hz g (hS'L hg)
  have hdisj : S' ⊓ Subgroup.zpowers z = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hS'L).trans
      (Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hz3 hzL).le)
  obtain ⟨hWcard, hWc, hWe⟩ := card_sup_zpowers_of_disjoint hzc hS'.1 hS'.2 hz3 hdisj
  have hWD : S' ⊔ Subgroup.zpowers z ≤ Subgroup.normalizer (D' : Set G) := by
    refine sup_le ((Subgroup.map_mono hSD).trans (Subgroup.le_normalizer_map L.subtype)) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hc := Subgroup.mem_centralizer_iff.mp hz h (hD'L hh)
      rw [← hc, mul_inv_cancel_right]
      exact hh
    · intro hh
      have hhL : z * h * z⁻¹ ∈ L := hD'L hh
      have hc : (z * h * z⁻¹) * z = z * (z * h * z⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hz _ hhL
      have e : h = z * h * z⁻¹ := by
        calc h = z⁻¹ * ((z * h * z⁻¹) * z) := by group
          _ = z⁻¹ * (z * (z * h * z⁻¹)) := by rw [hc]
          _ = z * h * z⁻¹ := by group
      rw [e]
      exact hh
  have hk : Nat.card (S' ⊔ Subgroup.zpowers z : Subgroup G) =
      3 ^ (localRank 3 (L ⧸ N) + 1) := by
    rw [hWcard, Subgroup.card_map_of_injective L.subtype_injective, hScard, hEcard, pow_succ,
      hHk]
    rfl
  exact CFSG.RankThree.Classical2.le_localRank_of_normalizes Nat.prime_three hWD ⟨hWc, hWe⟩ hk
    hcop h2

theorem three_dvd_card_center_thetaQuot {L : Subgroup G} {c : G} (hcL : c ∈ L)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hc3 : orderOf c = 3) :
    3 ∣ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c' : L := ⟨c, hcL⟩ with hc'
  have hc'Z : c' ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc g.2))
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  have hZ : π c' ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨c', hc'Z, rfl⟩
  have hc'3 : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact hc3
  have hord : orderOf (π c') = 3 := by
    have hc'p : c' ^ 3 = 1 := by rw [← hc'3]; exact pow_orderOf_eq_one c'
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hc'p, map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      apply three_not_dvd_card_aschbacherSolvableCore (G := L)
      have h := orderOf_dvd_natCard (⟨c', h1⟩ : aschbacherSolvableCore 3 L)
      rwa [Subgroup.orderOf_mk, hc'3] at h
  have h := orderOf_dvd_natCard (⟨π c', hZ⟩ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))
  rwa [Subgroup.orderOf_mk, hord] at h

theorem card_inf_le_card_center_thetaQuot {L B : Subgroup G} (hB3 : IsPGroup 3 B)
    (hBL : B ≤ Subgroup.centralizer (L : Set G)) :
    Nat.card (B ⊓ L : Subgroup G) ≤
      Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  set S : Subgroup L := (B ⊓ L).subgroupOf L with hS
  have hScard : Nat.card S = Nat.card (B ⊓ L : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hS3 : IsPGroup 3 S := by
    have h1 : IsPGroup 3 (B ⊓ L : Subgroup G) := hB3.to_le inf_le_left
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hSZ : S ≤ Subgroup.center L := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro g
    have hxB : (x : G) ∈ B := (Subgroup.mem_subgroupOf.mp hx).1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hBL hxB) g g.2)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  have hmap : S.map π ≤ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
    (Subgroup.map_mono hSZ).trans (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _))
  have hinj : Set.InjOn π (S : Set L) := injOn_mk_of_isPGroup Nat.prime_three hS3
  have hcard : Nat.card (S.map π) = Nat.card S := by
    change Nat.card ((S.map π : Set (L ⧸ aschbacherSolvableCore 3 L))) = Nat.card (S : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  rw [← hScard, ← hcard]
  exact Subgroup.card_le_of_le hmap

end General

section Exclusion

variable {G : Type} [Group G] [Finite G]

theorem Sec12Std.orderOf_c {A L : Subgroup G} {c : G} (h : Sec12Std G A c L) : orderOf c = 3 :=
  orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one

theorem Sec12Std.le_centralizer {A L : Subgroup G} {c : G} (h : Sec12Std G A c L) :
    L ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨L', -, hL'⟩ := h.mem_thetaComponentsAt
  rw [← hL']
  exact Subgroup.map_subtype_le L'

theorem Sec12Std.exists_mem_B_not_mem {A L : Subgroup G} {c : G} (h : Sec12Std G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) < 9) :
    ∃ b ∈ A ⊓ Subgroup.centralizer (L : Set G), b ∉ L ∧ orderOf b = 3 := by
  have hB3 : IsPGroup 3 (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2.1)⟩
  by_contra hcon
  push Not at hcon
  have hBL : A ⊓ Subgroup.centralizer (L : Set G) ≤ L := by
    intro b hb
    by_contra hbL
    have hb1 : b ≠ 1 := fun hb1 => hbL (hb1 ▸ L.one_mem)
    exact hcon b hb hbL (orderOf_eq_prime (h.isE27.1.2 b hb.1) hb1)
  have hle := card_inf_le_card_center_thetaQuot hB3 inf_le_right (L := L)
  rw [inf_eq_left.mpr hBL, h.card_B] at hle
  omega

theorem false_of_lift_of_partTwoF_eq (hFE : partTwoF G = partTwoE G) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.centralizer (L : Set G)) (hb3 : orderOf b = 3) (hbL : b ∉ L)
    {E F T : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hEF : E ≤ F)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hE9 : Nat.card E = 9) (hF27 : Nat.card F = 27)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set _)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hN3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  obtain ⟨Fl, hFlF, hFl, hFlcard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN3 hF
  have hFl3 : IsPGroup 3 Fl := fun x => ⟨1, Subtype.ext (by simpa using hFl.2 x x.2)⟩
  have hinjF : Set.InjOn π (Fl : Set L) := injOn_mk_of_isPGroup Nat.prime_three hFl3
  have hFlmap : Fl.map π = F := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.mpr hFlF) ?_
    change Nat.card F ≤ Nat.card (↑(Fl.map π) : Set (L ⧸ N))
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinjF]
    change Nat.card F ≤ Nat.card Fl
    rw [hFlcard]
  set El : Subgroup L := Fl ⊓ E.comap π with hEl
  have hElFl : El ≤ Fl := inf_le_left
  have hElmap : El.map π = E := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr inf_le_right
    · intro y hy
      have hyF : y ∈ Fl.map π := hFlmap ▸ hEF hy
      obtain ⟨x, hx, rfl⟩ := hyF
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hElcard : Nat.card El = 9 := by
    rw [← hE9, ← hElmap]
    change Nat.card (El : Set L) = Nat.card (↑(El.map π) : Set (L ⧸ N))
    rw [Subgroup.coe_map, Nat.card_image_of_injOn (hinjF.mono hElFl)]
  have hEl : CFSG.Assembly.IsElemAbelian 3 El :=
    ⟨⟨⟨fun x y => Subtype.ext (congrArg (fun z : Fl => (z : L))
      (hFl.1.is_comm.comm ⟨x, hElFl x.2⟩ ⟨y, hElFl y.2⟩))⟩⟩, fun x hx => hFl.2 x (hElFl hx)⟩
  set D : Subgroup L := T.comap π with hDdef
  have hElD : El ≤ Subgroup.normalizer (D : Set L) := by
    intro s hs
    have hsE : π s ∈ Subgroup.normalizer (T : Set _) := hET hs.2
    rw [Subgroup.mem_normalizer_iff] at hsE ⊢
    intro d
    change π d ∈ T ↔ π (s * d * s⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hsE _
  have hDcard : Nat.card D = Nat.card N * Nat.card T :=
    QuotientGroup.card_preimage_mk N (T : Set (L ⧸ N))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hT ((Subgroup.card_eq_one).mp hm)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard, hm]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
      (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hm]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hEl3 : IsPGroup 3 El := hFl3.to_le hElFl
  obtain ⟨T₀, hElT₀, hT₀⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two El D hEl3 hElD hcop h2
  set U : Subgroup L := (T₀ : Subgroup D).map D.subtype with hU
  have hU2 : IsPGroup 2 U := T₀.isPGroup'.map D.subtype
  set El' : Subgroup G := El.map L.subtype
  set Fl' : Subgroup G := Fl.map L.subtype
  set U' : Subgroup G := U.map L.subtype
  have hEl'L : El' ≤ L := Subgroup.map_subtype_le _
  have hFl'L : Fl' ≤ L := Subgroup.map_subtype_le _
  have hU'L : U' ≤ L := Subgroup.map_subtype_le _
  have hEl' : CFSG.Assembly.IsElemAbelian 3 El' := Sec4.Census.isElemAbelian_map_subtype hEl
  have hFl' : CFSG.Assembly.IsElemAbelian 3 Fl' := Sec4.Census.isElemAbelian_map_subtype hFl
  have hbc : ∀ {K : Subgroup G}, K ≤ L → b ∈ Subgroup.centralizer (K : Set G) := fun hK =>
    Subgroup.mem_centralizer_iff.mpr fun g hg => Subgroup.mem_centralizer_iff.mp hb g (hK hg)
  have hdisj : ∀ {K : Subgroup G}, K ≤ L → K ⊓ Subgroup.zpowers b = ⊥ := fun hK =>
    eq_bot_iff.mpr ((inf_le_inf_right _ hK).trans
      (Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hb3 hbL).le)
  obtain ⟨hEcard', hEc', hEe'⟩ :=
    card_sup_zpowers_of_disjoint (hbc hEl'L) hEl'.1 hEl'.2 hb3 (hdisj hEl'L)
  obtain ⟨hFcard', hFc', hFe'⟩ :=
    card_sup_zpowers_of_disjoint (hbc hFl'L) hFl'.1 hFl'.2 hb3 (hdisj hFl'L)
  have hU'ne : U' ≠ ⊥ := fun h0 => hT₀ (by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact h0)
  have hU'2 : IsPGroup 2 U' := hU2.map L.subtype
  have hEmem : El' ⊔ Subgroup.zpowers b ∈ partTwoE G := by
    refine ⟨⟨hEc', hEe'⟩, ?_, U', hU'ne, hU'2, ?_⟩
    · rw [hEcard', Subgroup.card_map_of_injective L.subtype_injective, hElcard]
    · refine sup_le ?_ ?_
      · have h1 : El' ≤ (Subgroup.normalizer (U : Set L)).map L.subtype :=
          Subgroup.map_mono hElT₀
        exact h1.trans (Subgroup.le_normalizer_map L.subtype)
      · rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · intro hu
          have hc := Subgroup.mem_centralizer_iff.mp hb u (hU'L hu)
          rw [← hc, mul_inv_cancel_right]
          exact hu
        · intro hu
          have huL : b * u * b⁻¹ ∈ L := hU'L hu
          have hc : (b * u * b⁻¹) * b = b * (b * u * b⁻¹) :=
            Subgroup.mem_centralizer_iff.mp hb _ huL
          have e : u = b * u * b⁻¹ := by
            calc u = b⁻¹ * ((b * u * b⁻¹) * b) := by group
              _ = b⁻¹ * (b * (b * u * b⁻¹)) := by rw [hc]
              _ = b * u * b⁻¹ := by group
          rw [e]
          exact hu
  obtain ⟨M, hFM, hM⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B)
    (show CFSG.Assembly.IsElemAbelian 3 (Fl' ⊔ Subgroup.zpowers b) from ⟨hFc', hFe'⟩)
  have hEM : El' ⊔ Subgroup.zpowers b ≤ M :=
    (sup_le_sup_right (Subgroup.map_mono hElFl) _).trans hFM
  have hMF : M ∈ partTwoF G :=
    ⟨hM.1, fun B hB hMB => (hM.2 hB hMB).antisymm hMB, _, hEmem, hEM⟩
  rw [hFE] at hMF
  have h81 : Nat.card (Fl' ⊔ Subgroup.zpowers b : Subgroup G) = 81 := by
    rw [hFcard', Subgroup.card_map_of_injective L.subtype_injective, hFlcard, hF27]
  have hdvd := Subgroup.card_dvd_of_le hFM
  rw [h81, hMF.2.1] at hdvd
  norm_num at hdvd

end Exclusion

section Main

variable {G : Type} [Group G] [Finite G]

theorem card_center_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem Sec12Std.false_of_cover {A L : Subgroup G} {c : G} (h : Sec12Std G A c L)
    (hK : KFacts.KS12CoverExclusion)
    (hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hlist : Blueprint.ChevalleyExceptionalModel ((L ⧸ aschbacherSolvableCore 3 L) ⧸
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1 ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* projSU 4 3 1) ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* Blueprint.NativeSporadic.ON)) :
    False := by
  obtain ⟨b, hbB, hbL, hb3⟩ := h.exists_mem_B_not_mem (by rw [hZ]; norm_num)
  rcases hK _ hq hZ hlist with hrank | ⟨E, F, T, hEF, hF, hE9, hF27, hT, hT2, hET⟩
  · have h1 := localRank_quot_add_one_le_of_centralizes L (aschbacherSolvableCore 3 L)
      three_not_dvd_card_aschbacherSolvableCore hbB.2 hb3 hbL (by omega)
    have h3 := h.toTheoremFourHyp.localRank_three
    omega
  · exact false_of_lift_of_partTwoF_eq h.partTwoF_eq hbB.2 hb3 hbL hEF hF hE9 hF27 hT hT2 hET

theorem item122_of (h41 : Sec4.Item4_1) (h43 : Sec4.Item4_3)
    (hcov : Sec4.Census.CoverInputs46) (hK : KFacts.KS12CoverExclusion) : Item122 := by
  intro G _ _ A c L h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hCtop := centralizer_ne_top_of_theoremFourHyp h.toTheoremFourHyp h.ne_one
  have hS4 : SectionFourHyp C := h.toTheoremFourHyp.sectionFourHyp hCtop
  have hLc := h.le_centralizer
  have hc3 := h.orderOf_c
  obtain ⟨L', hL', hLL'⟩ := h.mem_thetaComponentsAt
  have hLL'' : L'.map C.subtype = L := hLL'
  subst hLL''
  set X' := L' ⧸ aschbacherSolvableCore 3 L' with hX'
  set X := (L'.map C.subtype) ⧸ aschbacherSolvableCore 3 (L'.map C.subtype) with hX
  have eX : X' ≃* X := Sec13.thetaQuotEquivSub C L'
  have hX'S : SectionFourHyp X' := Sec4.Census.sectionFourHyp_thetaQuotient h41 hS4 hL'
  have hX'q : IsQuasisimple X' := hL'.2.2
  have hXq : IsQuasisimple X := LocalCores.isQuasisimple_of_mulEquiv eX hX'q
  have hZ3 : IsPGroup 3 (Subgroup.center X) := Sec4.Census.isPGroup_center_thetaQuotient _
  have hZ3' : IsPGroup 3 (Subgroup.center X') := Sec4.Census.isPGroup_center_thetaQuotient L'
  have h3Z : 3 ∣ Nat.card (Subgroup.center X) := three_dvd_card_center_thetaQuot h.mem_L hLc hc3
  have hZeq : Nat.card (Subgroup.center X') = Nat.card (Subgroup.center X) :=
    card_center_eq_of_mulEquiv eX
  have h3Z' : 3 ∣ Nat.card (Subgroup.center X') := hZeq ▸ h3Z
  have hZne : Subgroup.center X' ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h3Z'
    norm_num at h3Z'
  have hloc : localRank 3 X ≤ 3 := by
    rw [← Census.localRank_eq_of_mulEquiv eX Nat.prime_three]
    exact Sec4.Census.SectionFourHyp.localRank_three_le hX'S
  set eZ : X' ⧸ Subgroup.center X' ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.congr _ _ eX (Subgroup.map_center_eq eX)
  have hZ3eq : Nat.card (Subgroup.center X') ∣ 3 → Nat.card (Subgroup.center X) = 3 := fun hd =>
    Nat.dvd_antisymm (hZeq ▸ hd) h3Z
  have hcover : ∀ {S : Type} [Group S], Nonempty (X' ⧸ Subgroup.center X' ≃* S) →
      Nonempty (X ⧸ Subgroup.center X ≃* S) := fun ⟨φ⟩ => ⟨eZ.symm.trans φ⟩
  rcases h43 X' hX'S hX'q h3Z' with
    ⟨p, e, _, he, hL3⟩ | hA6 | hA7 | hG2 | hU43 | hM22 | hJ3 | hMc | hON
  ·
    left
    have hq : p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
      rcases hL3 with ⟨hq, -⟩ | ⟨hq, -⟩
      · exact Or.inl hq
      · exact Or.inr hq
    have hbd := Sec4.Census.two_or_le_two_of_isoLThreePi
      (Sec4.Census.sectionFourHyp_quotient_center h41 hX'S hX'q) he hL3
    have hEps := hcov.slThree X' hX'q hZ3' hZne p e he hbd hL3
    exact Sec13.isSLThreePi_of_mulEquiv eX
      ⟨p ^ e, KFacts.isSLThreePiAt_of_isSLThreeEpsAt he hEps hq hZne⟩
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3' (Or.inl hA6))
    exact Or.inr (Or.inl ⟨h3, hcover hA6⟩)
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3' (Or.inr (Or.inl hA7)))
    exact Or.inr (Or.inr (Or.inl ⟨h3, hcover hA7⟩))
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3' (Or.inr (Or.inr (Or.inl hG2))))
    exact (h.false_of_cover hK hXq h3
      (Or.inl (SectionRank.chevalleyExceptionalModel_of_mulEquiv eZ.symm hG2))).elim
  ·
    have hd9 : Nat.card (Subgroup.center X) ∣ 9 := hZeq ▸ hcov.u43 X' hX'q hZ3' hU43
    have h39 : Nat.card (Subgroup.center X) = 3 ∨ Nat.card (Subgroup.center X) = 9 := by
      have hmem : Nat.card (Subgroup.center X) ∈ Nat.divisors 9 :=
        Nat.mem_divisors.mpr ⟨hd9, by norm_num⟩
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at hmem
      rcases Finset.mem_insert.mp hmem with h1 | hmem
      · rw [h1] at h3Z
        norm_num at h3Z
      rcases Finset.mem_insert.mp hmem with h3 | h9
      · exact Or.inl h3
      · exact Or.inr (Finset.mem_singleton.mp h9)
    rcases h39 with h3 | h9
    · exact (h.false_of_cover hK hXq h3 (Or.inr (Or.inl (hcover hU43)))).elim
    · have h4 := hcov.u43Rank X hXq h9 (hcover hU43)
      omega
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3' (Or.inr (Or.inr (Or.inr (Or.inl hM22)))))
    exact Or.inr (Or.inr (Or.inr ⟨h3, hcover hM22⟩))
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3'
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJ3))))))
    obtain ⟨φ⟩ := hJ3
    have hJ3' : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) :=
      ⟨eZ.symm.trans φ⟩
    exact (h.false_of_cover hK hXq h3 (Or.inr (Or.inr (Or.inl hJ3')))).elim
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3'
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMc)))))))
    obtain ⟨φ⟩ := hMc
    have hMc' : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) :=
      ⟨eZ.symm.trans φ⟩
    exact (h.false_of_cover hK hXq h3 (Or.inr (Or.inr (Or.inr (Or.inl hMc'))))).elim
  ·
    have h3 := hZ3eq (hcov.centerThree X' hX'q hZ3'
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hON)))))))
    obtain ⟨φ⟩ := hON
    have hON' : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON) :=
      ⟨eZ.symm.trans φ⟩
    exact (h.false_of_cover hK hXq h3 (Or.inr (Or.inr (Or.inr (Or.inr hON'))))).elim

end Main

section Center

theorem card_center_eq_three_of_isSLThreePi {X : Type} [Group X] (hX : Sec4.IsSLThreePi X) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
  · have hpf : Sec4.PiField true (ringChar K) n K := ⟨hp, n.2, hnc⟩
    have hq' : Sec4.ModThree true (ringChar K ^ (n : ℕ)) := by
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    rw [card_center_eq_of_mulEquiv e]
    exact KFacts.card_center_slPi hpf hq'
  · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, pow_zero] at hm
        rw [hm] at hq
        norm_num at hq
      · exact h0
    have hpf : Sec4.PiField false (ringChar K) m K := ⟨hp, hm1, by
      rw [hK, hm]
      rfl⟩
    have hq' : Sec4.ModThree false (ringChar K ^ m) := by
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
    rw [card_center_eq_of_mulEquiv e]
    have h := KFacts.card_center_slPi hpf hq'
    rw [← hm] at h
    exact h

theorem card_center_thetaQuot_eq_three_of_item122 (h122 : Item122) {G : Type} [Group G]
    [Finite G] {A L : Subgroup G} {c : G} (h : Sec12Std G A c L) :
    Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
  rcases h122 G A c L h with hSL | hA6 | hA7 | hM22
  · exact card_center_eq_three_of_isSLThreePi hSL
  · exact hA6.1
  · exact hA7.1
  · exact hM22.1

end Center

end CFSG.RankThree.PartTwo.Sec12
