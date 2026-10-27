module

public import CFSG.RankThree.PartTwo.Sec12.Hering129Defs
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_rep {L : Subgroup G} {b : G} (hb : b ∈ Sec4.thetaQuotCentralizer L)
    (hb3 : orderOf b = 3) (l : L) :
    ∃ x : L, b * (x : G) * b⁻¹ = x ∧ x⁻¹ * l ∈ aschbacherSolvableCore 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.zpowers b ≤ Sec4.thetaQuotCentralizer L := Subgroup.zpowers_le.mpr hb
  have hZN : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) :=
    hZ.trans (Sec6.thetaQuotCentralizer_le_normalizer L)
  let α : Subgroup.zpowers b →* MulAut L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion hZN)
  have hA : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3, pow_one])
  have hα : ∀ (a : Subgroup.zpowers b) (x : L), ((α a x : L) : G) = a * (x : G) * (a : G)⁻¹ :=
    fun a x => rfl
  have hNinv : ∀ (a : Subgroup.zpowers b), ∀ n ∈ aschbacherSolvableCore 3 L,
      α a n ∈ aschbacherSolvableCore 3 L := fun a n hn => by
    have h := Sec4.map_aschbacherSolvableCore (α a)
    rw [← h]
    exact ⟨n, hn, rfl⟩
  have htriv : ∀ (a : Subgroup.zpowers b) (g : L), g⁻¹ * α a g ∈ aschbacherSolvableCore 3 L :=
    fun a g => by
      have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp (hZ a.2)).2 g g.2
      obtain ⟨t, ht, hte⟩ := h1
      have : g⁻¹ * α a g = t := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hα]
        exact hte.symm
      rw [this]
      exact ht
  have hinv : ∀ (a : Subgroup.zpowers b) (x : L), l⁻¹ * x ∈ aschbacherSolvableCore 3 L →
      l⁻¹ * α a x ∈ aschbacherSolvableCore 3 L := fun a x hx => by
    have h4 : l⁻¹ * α a x = (l⁻¹ * α a l) * α a (l⁻¹ * x) := by
      rw [map_mul, map_inv]
      group
    rw [h4]
    exact Subgroup.mul_mem _ (htriv a l) (hNinv a _ hx)
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA α
    (aschbacherSolvableCore 3 L) three_not_dvd_card_aschbacherSolvableCore l).2 hinv
  refine ⟨c, ?_, ?_⟩
  · have h1 := congrArg Subtype.val (hfix ⟨b, Subgroup.mem_zpowers b⟩)
    exact h1
  · have := Subgroup.inv_mem _ hc
    simpa using this

noncomputable def centMap (L : Subgroup G) (b : G) :
    (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) →* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion inf_le_left)

theorem centMap_surjective {L : Subgroup G} {b : G} (hb : b ∈ Sec4.thetaQuotCentralizer L)
    (hb3 : orderOf b = 3) : Function.Surjective (centMap L b) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H l =>
    obtain ⟨x, hx, hxl⟩ := exists_fixed_rep hb hb3 l
    refine ⟨⟨(x : G), x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · have : b * (x : G) = x * b := by
        calc b * (x : G) = (b * x * b⁻¹) * b := by group
          _ = x * b := by rw [hx]
      exact this.symm
    · exact QuotientGroup.eq.mpr hxl

theorem not_three_dvd_card_ker_centMap (L : Subgroup G) (b : G) :
    ¬ 3 ∣ Nat.card (centMap L b).ker := by
  set K₀ : Subgroup L := (centMap L b).ker.map (Subgroup.inclusion inf_le_left) with hK₀
  have hK₀card : Nat.card K₀ = Nat.card (centMap L b).ker :=
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
  have hK₀le : K₀ ≤ aschbacherSolvableCore 3 L := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (MonoidHom.mem_ker.mp hx)
    rw [centMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  intro h3
  apply three_not_dvd_card_aschbacherSolvableCore (G := L)
  rw [← hK₀card] at h3
  exact h3.trans (Subgroup.card_dvd_of_le hK₀le)

theorem localRank_quot_add_one_le_of_thetaQuotCentralizer {L : Subgroup G} {b : G}
    (hb : b ∈ Sec4.thetaQuotCentralizer L) (hb3 : orderOf b = 3) (hbL : b ∉ L)
    (hpos : 0 < localRank 3 (L ⧸ aschbacherSolvableCore 3 L)) :
    localRank 3 (L ⧸ aschbacherSolvableCore 3 L) + 1 ≤ localRank 3 G := by
  set L₁ : Subgroup G := L ⊓ Subgroup.centralizer ({b} : Set G) with hL₁
  have hsurj := centMap_surjective hb hb3
  let φ := QuotientGroup.quotientKerEquivOfSurjective (centMap L b) hsurj
  have hrk : localRank 3 (L₁ ⧸ (centMap L b).ker) =
      localRank 3 (L ⧸ aschbacherSolvableCore 3 L) :=
    Census.localRank_eq_of_mulEquiv φ Nat.prime_three
  have hbc : b ∈ Subgroup.centralizer (L₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have h := localRank_quot_add_one_le_of_centralizes L₁ (centMap L b).ker
    (not_three_dvd_card_ker_centMap L b) hbc hb3 (fun h' => hbL h'.1) (by rw [hrk]; exact hpos)
  rw [hrk] at h
  exact h

theorem injOn_mk_of_isPGroup_of_not_dvd {N : Subgroup G} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {A : Subgroup G} (hA : IsPGroup 3 A) : Set.InjOn (QuotientGroup.mk' N) (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hdisj : Disjoint A N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN))
  intro x hx y hy hxy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
  have hmem : x⁻¹ * y ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem hx) hy, hxy⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact eq_of_inv_mul_eq_one hmem

theorem false_of_lift_of_partTwoF_eq' (hFE : partTwoF G = partTwoE G) {L : Subgroup G}
    (N : Subgroup L) [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) {b : G}
    (hb : b ∈ Subgroup.centralizer (L : Set G)) (hb3 : orderOf b = 3) (hbL : b ∉ L)
    {E F T : Subgroup (L ⧸ N)} (hEF : E ≤ F)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) (hE9 : Nat.card E = 9) (hF27 : Nat.card F = 27)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set _)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨Fl, hFlF, hFl, hFlcard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN3 hF
  have hFl3 : IsPGroup 3 Fl := fun x => ⟨1, Subtype.ext (by simpa using hFl.2 x x.2)⟩
  have hinjF : Set.InjOn π (Fl : Set L) := injOn_mk_of_isPGroup_of_not_dvd hN3 hFl3
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


theorem Sec12StdBar.exists_mem_B_not_mem {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) < 9) :
    ∃ b ∈ A ⊓ Sec4.thetaQuotCentralizer L, b ∉ L ∧ orderOf b = 3 := by
  have hB3 : IsPGroup 3 (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using h.isE27.1.2 x x.2.1)⟩
  by_contra hcon
  push Not at hcon
  have hBL : A ⊓ Sec4.thetaQuotCentralizer L ≤ L := by
    intro b hb
    by_contra hbL
    have hb1 : b ≠ 1 := fun hb1 => hbL (hb1 ▸ L.one_mem)
    exact hcon b hb hbL (orderOf_eq_prime (h.isE27.1.2 b hb.1) hb1)
  have hle := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
  rw [inf_eq_left.mpr hBL, h.card_B] at hle
  omega

theorem Sec12StdBar.false_of_cover {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hK : KFacts.KS12CoverExclusion)
    (hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hlist : Blueprint.ChevalleyExceptionalModel ((L ⧸ aschbacherSolvableCore 3 L) ⧸
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1 ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃*
          CFSG.Assembly.RankThreeEven.projSU 4 3 1) ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* Blueprint.NativeSporadic.ON)) :
    False := by
  obtain ⟨b, hbB, hbL, hb3⟩ := h.exists_mem_B_not_mem (by rw [hZ]; norm_num)
  rcases hK _ hq hZ hlist with hrank | ⟨E, F, T, hEF, hF, hE9, hF27, hT, hT2, hET⟩
  · have h1 := localRank_quot_add_one_le_of_thetaQuotCentralizer hbB.2 hb3 hbL (by omega)
    have h3 := h.toTheoremFourHyp.localRank_three
    omega
  · set L₁ : Subgroup G := L ⊓ Subgroup.centralizer ({b} : Set G) with hL₁
    have hsurj := centMap_surjective hbB.2 hb3
    let φ := QuotientGroup.quotientKerEquivOfSurjective (centMap L b) hsurj
    have hbc : b ∈ Subgroup.centralizer (L₁ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mp hy.2
    refine false_of_lift_of_partTwoF_eq' h.partTwoF_eq (centMap L b).ker
      (not_three_dvd_card_ker_centMap L b) hbc hb3 (fun h' => hbL h'.1)
      (E := E.map φ.symm.toMonoidHom) (F := F.map φ.symm.toMonoidHom)
      (T := T.map φ.symm.toMonoidHom) (Subgroup.map_mono hEF) ?_ ?_ ?_ ?_ ?_ ?_
    · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 φ.symm.toMonoidHom F hF
    · rw [Subgroup.card_map_of_injective φ.symm.injective, hE9]
    · rw [Subgroup.card_map_of_injective φ.symm.injective, hF27]
    · intro h0
      exact hT ((Subgroup.map_eq_bot_iff_of_injective T φ.symm.injective).mp h0)
    · exact hT2.map _
    · exact (Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _)

theorem item122Bar_of (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h43 : Sec4.Item4_3)
    (hcov : Sec4.Census.CoverInputs46) (hK : KFacts.KS12CoverExclusion) : Item122Bar := by
  intro G _ _ A c L h hAE
  unfold IsList122
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hCtop := centralizer_ne_top_of_theoremFourHyp h.toTheoremFourHyp h.ne_one
  have hS4 : SectionFourHyp C := h.toTheoremFourHyp.sectionFourHyp hCtop
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
  obtain ⟨L', hL', hLL'⟩ := h.mem_thetaComponentsAt
  have hLL'' : L'.map C.subtype = L := hLL'
  subst hLL''
  set X' := L' ⧸ aschbacherSolvableCore 3 L' with hX'
  set X := (L'.map C.subtype) ⧸ aschbacherSolvableCore 3 (L'.map C.subtype) with hX
  have eX : X' ≃* X := Sec13.thetaQuotEquivSub C L'
  have hX'S : SectionFourHyp X' := Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h1 hS4 hL'
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
      (Sec4.Item41Narrow.sectionFourHyp_quotient_center h1 h2 hX'S hX'q) he hL3
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


end CFSG.RankThree.PartTwo.Sec12
