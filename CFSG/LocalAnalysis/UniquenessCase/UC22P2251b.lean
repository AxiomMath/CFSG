module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wa
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yh
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
import CFSG.LocalAnalysis.UniquenessCase.UC22KHi8d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.Quasithin.EmptyFaithful.S146zXGIdent
import CFSG.Quasithin.H13.KG14726Alt
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.A5Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI)

@[expose] def LayerShape22 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ IsL2Ev X n) ∨ IsL3 X 1

@[expose] def BadShape22 (X : Type) [Group X] : Prop :=
  IsL2Ev X 2 ∨ IsL3 X 1

namespace LayerShape22

variable {X Y : Type} [Group X] [Group Y]

theorem of_mulEquiv (h : LayerShape22 X) (e : X ≃* Y) : LayerShape22 Y := by
  rcases h with ⟨n, hn, h⟩ | h
  · exact Or.inl ⟨n, hn, P22fin.isL2Ev_of_mulEquiv h e⟩
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)

variable [Finite X]

theorem isSimpleGroup (h : LayerShape22 X) : IsSimpleGroup X := by
  rcases h with ⟨n, hn, h⟩ | h
  · exact P22y.isSimpleGroup_of_isL2Ev h hn
  · exact PartTwo.isSimpleGroup_of_isL3 h

theorem center_eq_bot (h : LayerShape22 X) : center X = ⊥ := by
  rcases h with ⟨n, -, h⟩ | h
  · exact P22y.center_eq_bot_of_isL2Ev h
  · exact PartTwo.center_eq_bot_of_isL3 h

theorem isQuasisimple (h : LayerShape22 X) : CFSG.Open.IsQuasisimple X := by
  haveI := h.isSimpleGroup
  exact P22y.isQuasisimple_of_isSimpleGroup h.center_eq_bot

theorem three_dvd_card (h : LayerShape22 X) : 3 ∣ Nat.card X := by
  rcases h with ⟨n, -, h⟩ | h
  · exact P22y.three_dvd_card_of_isL2Ev h
  · rw [PartTwo.card_eq_of_isL3 h]
    norm_num

theorem isCyclic_of_isPGroup (h : LayerShape22 X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (P : Subgroup X)
    (hP : IsPGroup q P) : IsCyclic P := by
  rcases h with ⟨n, -, h⟩ | h
  · exact P22y.isCyclic_of_isPGroup_of_isL2Ev h hq hq2 P hP
  · haveI : Fact q.Prime := ⟨hq⟩
    rcases (Nat.dvd_prime hq).1 (PartTwo.card_pGroup_dvd_of_isL3 h hq hq2 hP) with h1 | h1
    · haveI := (Nat.card_eq_one_iff_unique.1 h1).1
      infer_instance
    · exact isCyclic_of_prime_card h1

theorem commutator_eq_self {Z : Type} [Group Z] {Y : Subgroup Z} [Finite Y] (h : LayerShape22 ↥Y) :
    ⁅Y, Y⁆ = Y := by
  rw [← Subgroup.map_subtype_commutator, h.isQuasisimple.1, ← MonoidHom.range_eq_map, range_subtype]

end LayerShape22

namespace BadShape22

variable {X Y : Type} [Group X] [Group Y]

theorem layerShape (h : BadShape22 X) : LayerShape22 X := by
  rcases h with h | h
  · exact Or.inl ⟨2, le_rfl, h⟩
  · exact Or.inr h

theorem of_mulEquiv (h : BadShape22 X) (e : X ≃* Y) : BadShape22 Y := by
  rcases h with h | h
  · exact Or.inl (P22fin.isL2Ev_of_mulEquiv h e)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e h)

theorem card [Finite X] (h : BadShape22 X) : Nat.card X = 60 ∨ Nat.card X = 168 := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | h
  · left
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF]
    norm_num
  · exact Or.inr (PartTwo.card_eq_of_isL3 h)

theorem nonempty_mulEquiv_alt_five_of_isL2Ev_two (h : IsL2Ev X 2) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_sl2 h
  haveI := Fintype.ofFinite F
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 2 2 two_ne_zero]
  obtain ⟨e₂⟩ := CFSG.Quasithin.S146zX.nonempty_mulEquiv_sl_two_four_of_alt_five
  exact ⟨e.trans ((P22s.slMapEquiv (FiniteField.ringEquivOfCardEq hcard)).trans e₂)⟩

theorem card_mulAut_dvd [Finite X] (h : BadShape22 X) :
    Nat.card (MulAut X) ∣ 120 ∨ Nat.card (MulAut X) ∣ 336 := by
  rcases h with h | h
  · obtain ⟨e⟩ := nonempty_mulEquiv_alt_five_of_isL2Ev_two h
    left
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      CFSG.Quasithin.H13.KG14726.card_mulAut_alternatingGroup (by norm_num) (by norm_num)]
    decide
  · exact Or.inr (PartTwo.card_mulAut_dvd_of_isL3 h)

theorem not_sq_dvd_card_mulAut [Finite X] (h : BadShape22 X) {p : ℕ} (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card (MulAut X) := by
  have key : ∀ d : ℕ, d = 120 ∨ d = 336 → ¬ p ^ 2 ∣ d := by
    rintro d hd hpd
    have hd0 : 0 < d := by rcases hd with rfl | rfl <;> norm_num
    have hle := Nat.le_of_dvd hd0 hpd
    have hp19 : p < 19 := by
      by_contra hc
      have : 361 ≤ p ^ 2 := by nlinarith
      rcases hd with rfl | rfl <;> omega
    interval_cases p <;> rcases hd with rfl | rfl <;> norm_num at hpd
  intro hdvd
  rcases h.card_mulAut_dvd with h1 | h1
  · exact key 120 (Or.inl rfl) (hdvd.trans h1)
  · exact key 336 (Or.inr rfl) (hdvd.trans h1)

end BadShape22

namespace P2251b

variable {X : Type} [Group X]

theorem isL2Ev_two_commutator_of_isS5 {Y : Subgroup X} (h : IsS5 ↥Y) : IsL2Ev ↥⁅Y, Y⁆ 2 := by
  obtain ⟨e⟩ := h
  obtain ⟨e₁⟩ := CFSG.EvenSporadicStandard.HNRecog.Harada.L27.commutator_equiv_a5_of_equiv_perm_five Y e
  obtain ⟨e₂⟩ := CFSG.Quasithin.S146zX.nonempty_mulEquiv_sl_two_four_of_alt_five
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_,
    ⟨e₁.trans (e₂.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)))⟩⟩
  exact GaloisField.card 2 2 two_ne_zero

theorem two_le_of_not_isL2Ev_one {Z : Type} [Group Z] {n : ℕ} (h : IsL2Ev Z n) (h1 : ¬ IsL2Ev Z 1) : 2 ≤ n := by
  have := P22y.one_le_of_isL2Ev h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl : n = 1 := by omega
    exact absurd h h1
  · exact hn

theorem layerShape_commutator [Finite X] {Y : Subgroup X} (h : FactorShape22 ↥Y) (h1 : ¬ IsL2Ev ↥Y 1) :
    LayerShape22 ↥⁅Y, Y⁆ := by
  rcases h with ⟨n, hn⟩ | h | h
  · have hl : LayerShape22 ↥Y := Or.inl ⟨n, two_le_of_not_isL2Ev_one hn h1, hn⟩
    rwa [hl.commutator_eq_self]
  · have hl : LayerShape22 ↥Y := Or.inr h
    rwa [hl.commutator_eq_self]
  · exact Or.inl ⟨2, le_rfl, isL2Ev_two_commutator_of_isS5 h⟩

theorem badShape_commutator [Finite X] {Y : Subgroup X} (h : FactorShape22 ↥Y)
    (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥Y n ∧ n ≠ 2) : BadShape22 ↥⁅Y, Y⁆ := by
  rcases h with ⟨n, hn⟩ | h | h
  · obtain rfl : n = 2 := by
      by_contra hne
      exact hbad ⟨n, hn, hne⟩
    have hl : LayerShape22 ↥Y := Or.inl ⟨2, le_rfl, hn⟩
    rw [hl.commutator_eq_self]
    exact Or.inl hn
  · have hl : LayerShape22 ↥Y := Or.inr h
    rw [hl.commutator_eq_self]
    exact Or.inr h
  · exact Or.inl (isL2Ev_two_commutator_of_isS5 h)

theorem not_isL2Ev_one_of_bad {Z : Type} [Group Z] (hbad : ¬ ∃ n : ℕ, IsL2Ev Z n ∧ n ≠ 2) : ¬ IsL2Ev Z 1 :=
  fun h => hbad ⟨1, h, by norm_num⟩

theorem card_of_bad {Z : Type} [Group Z] [Finite Z] (h : FactorShape22 Z)
    (hbad : ¬ ∃ n : ℕ, IsL2Ev Z n ∧ n ≠ 2) : Nat.card Z = 60 ∨ Nat.card Z = 120 ∨ Nat.card Z = 168 := by
  rcases h with ⟨n, hn⟩ | h | h
  · obtain rfl : n = 2 := by
      by_contra hne
      exact hbad ⟨n, hn, hne⟩
    rcases BadShape22.card (Or.inl hn) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inr (PartTwo.card_eq_of_isL3 h))
  · obtain ⟨e⟩ := h
    refine Or.inr (Or.inl ?_)
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl

theorem normal_commutator_subgroupOf (Y : Subgroup X) : (⁅Y, Y⁆.subgroupOf Y).Normal := by
  have h : ⁅Y, Y⁆.subgroupOf Y = commutator ↥Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (Subgroup.commutator_le_self Y)]
  rw [h]
  infer_instance

theorem ker_eq_bot_of_layerShape {Y : Type} [Group Y] [Finite X] (hX : commutator X = ⊤)
    (hO : CFSG.pCore 2 X = ⊥) (ψ : X →* Y) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center X)
    (hY : LayerShape22 Y) : ψ.ker = ⊥ := by
  haveI : Group.IsPerfect X := ⟨hX⟩
  haveI : Finite Y := Finite.of_surjective ψ hψ
  let e : X ⧸ ψ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  refine CFSG.RankThree.PartTwo.KFacts.KS14.eq_bot_of_isPerfect_of_isCyclic_sylow hker fun q hq hqZ Q => ?_
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ψ.ker) 2 hqZ
    have hzc : zpowers (z : X) ≤ center X := (zpowers_le (H := center X)).2 (hker z.2)
    have hN : (zpowers (z : X)).Normal := normal_of_le_center hzc
    have hzo : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
    have hP : IsPGroup 2 (zpowers (z : X)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
    have hle : zpowers (z : X) ≤ CFSG.pCore 2 X := le_sSup ⟨hN, hP⟩
    rw [hO, le_bot_iff, zpowers_eq_bot] at hle
    rw [hle, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  haveI := hY.isCyclic_of_isPGroup hq hq2 ((Q : Subgroup (X ⧸ ψ.ker)).map e.toMonoidHom) (Q.isPGroup'.map _)
  exact isCyclic_of_injective ((Q : Subgroup (X ⧸ ψ.ker)).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    ((Q : Subgroup (X ⧸ ψ.ker)).equivMapOfInjective e.toMonoidHom e.injective).injective

theorem lt_card_of_isL2Ev {Z : Type} [Group Z] {n : ℕ} (h : IsL2Ev Z n) (hn : 2 < n) : 168 < Nat.card Z := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF]
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  nlinarith

end P2251b

open P2251b

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251b_isComponentOf (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) (i : Fin m) (hi : ¬ IsL2Ev ↥(Nb i) 1) : IsComponentOf ⁅Nb i, Nb i⁆ ⊤ := by
  refine ⟨le_top, ?_, (layerShape_commutator (hNb.2 i) hi).isQuasisimple⟩
  exact CFSG.Open.IsSubnormal.of_mathlib (Subgroup.IsSubnormal.step _ _ (Subgroup.commutator_le_self _)
    (P22k8.isSubnormal_nb D hNb i) (normal_commutator_subgroupOf (Nb i)))

theorem uc22p2251b_exists_lift (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h119 : R119W D)
    (hU : ¬ IsTI D.U) {Lb : Subgroup (MBar D.M D.U)} (hLb : IsComponentOf Lb ⊤) (hsh : LayerShape22 ↥Lb) :
    ∃ K ∈ calC D.M, mbarImage D.M D.U K = Lb ∧ Nonempty (Bar2 K ≃* ↥Lb) := by
  obtain ⟨K, hK, hKb⟩ := uc22p22wa_lift D hx h61 h119 hU hLb
  refine ⟨K, hK, hKb, ?_⟩
  have hsh' : LayerShape22 ↥(mbarImage D.M D.U K) := by
    rw [hKb]
    exact hsh
  have hne : mbarImage D.M D.U K ≠ ⊥ := by
    haveI := hsh'.isSimpleGroup
    exact (nontrivial_iff_ne_bot _).1 inferInstance
  obtain ⟨ψ, hψs, hψk, -⟩ := uc22p22wa_onto D hK hne
  have hbot := ker_eq_bot_of_layerShape hK.2.2.1 CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot ψ hψs hψk hsh'
  exact ⟨(MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).1 hbot, hψs⟩).trans (MulEquiv.subgroupCongr hKb)⟩

theorem uc22p2251b_exists_lift_nb (D : Data G) {Ch : Choice2011 G} (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (c : Ctx22 D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (i : Fin m) (hi : ¬ IsL2Ev ↥(Nb i) 1) :
    ∃ K ∈ calC D.M, mbarImage D.M D.U K = ⁅Nb i, Nb i⁆ ∧ Nonempty (Bar2 K ≃* ↥⁅Nb i, Nb i⁆) ∧
      LayerShape22 (Bar2 K) := by
  have hsh := layerShape_commutator (hNb.2 i) hi
  obtain ⟨K, hK, hKb, ⟨e⟩⟩ :=
    uc22p2251b_exists_lift D hx h61 h119 c.hU (uc22p2251b_isComponentOf D hNb i hi) hsh
  exact ⟨K, hK, hKb, ⟨e⟩, hsh.of_mulEquiv e.symm⟩

theorem uc22p2251b_ne (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    {i j : Fin m} (hij : i ≠ j) (hi : ¬ IsL2Ev ↥(Nb i) 1) {K L : Subgroup G}
    (hK : mbarImage D.M D.U K = ⁅Nb i, Nb i⁆) (hL : mbarImage D.M D.U L = ⁅Nb j, Nb j⁆) : K ≠ L := by
  rintro rfl
  have hle : ⁅Nb i, Nb i⁆ ≤ Nb i ⊓ ⨆ k ∈ {k | k ≠ i}, Nb k := by
    refine le_inf (Subgroup.commutator_le_self _) ?_
    rw [← hK, hL]
    exact (Subgroup.commutator_le_self _).trans
      (le_iSup₂_of_le (f := fun k (_ : k ∈ {k | k ≠ i}) => Nb k) j (Ne.symm hij) le_rfl)
  rw [hNb.1.2.2 i, le_bot_iff] at hle
  haveI := (layerShape_commutator (hNb.2 i) hi).isSimpleGroup
  exact (nontrivial_iff_ne_bot _).1 inferInstance hle

theorem uc22p2251b_normal (D : Data G) {Ch : Choice2011 G} (h17 : S21_17 D Ch) (hH : H1930 D) (c : Ctx21 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hcard : Nat.card (Bar2 K) = 60 ∨ Nat.card (Bar2 K) = 168) :
    (K.subgroupOf D.M).Normal := by
  have h3 : 3 ∣ Nat.card (Bar2 K) := by
    rcases hcard with h | h <;> rw [h] <;> norm_num
  have hle : Nat.card (Bar2 K) ≤ 168 := by
    rcases hcard with h | h <;> omega
  rcases h17 hH c K hK with h1 | ⟨-, n, hn, hL2 | hSz⟩ | ⟨-, hJ1, -⟩
  · exact uc22p21j_normal_of_conjClosure_eq hK.1.le h1
  · have := lt_card_of_isL2Ev (P22fin.isL2Ev_of_isL2 hL2).1 hn
    omega
  · exact absurd h3 (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz)
  · have := (kJ1_holds (Bar2 K) hJ1).1
    omega

theorem uc22p2251b_exists_bad (D : Data G) {Ch : Choice2011 G} (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (h17 : S21_17 D Ch) (hH : H1930 D) (c : Ctx22 D Ch) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m}
    (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2) :
    ∃ K ∈ calC D.M, mbarImage D.M D.U K = ⁅Nb i, Nb i⁆ ∧ Nonempty (Bar2 K ≃* ↥⁅Nb i, Nb i⁆) ∧
      BadShape22 (Bar2 K) ∧ (K.subgroupOf D.M).Normal := by
  obtain ⟨K, hK, hKb, ⟨e⟩, -⟩ :=
    uc22p2251b_exists_lift_nb D hx h61 h119 c hNb i (not_isL2Ev_one_of_bad hbad)
  have hbs : BadShape22 (Bar2 K) := (badShape_commutator (hNb.2 i) hbad).of_mulEquiv e.symm
  exact ⟨K, hK, hKb, ⟨e⟩, hbs, uc22p2251b_normal D h17 hH c.toCtx21 hK hbs.card⟩

theorem uc22p2251b_isCyclic_of_isPGroup {K : Subgroup G} (hK : LayerShape22 (Bar2 K)) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup q P) : IsCyclic P := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup ↥K := P.subgroupOf K with hP'
  have hP'q : IsPGroup q P' := hP.comap_subtype
  have hdisj : Disjoint P' (CFSG.pCore 2 ↥K) :=
    IsPGroup.disjoint_of_ne q 2 hq2 _ _ hP'q CFSG.pCore_isPGroup
  let f : ↥P' →* Bar2 K := (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp P'.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : ↥K) ∈ P' ⊓ CFSG.pCore 2 ↥K := ⟨x.2, hxk⟩
    rw [disjoint_iff.1 hdisj, mem_bot] at hmem
    exact Subtype.ext hmem
  haveI := hK.isCyclic_of_isPGroup hq hq2 f.range (hP'q.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  haveI : IsCyclic ↥P' := isCyclic_of_injective f.rangeRestrict (by rwa [MonoidHom.rangeRestrict_injective_iff])
  exact isCyclic_of_injective (subgroupOfEquivOfLe hPK).symm.toMonoidHom (subgroupOfEquivOfLe hPK).symm.injective

theorem uc22p2251b_thin8 {K : Subgroup G} (hK : LayerShape22 (Bar2 K)) : F08.Thin8 K := by
  intro q hq hq2
  refine CFSG.SectionRank.pRank_le hq.one_lt fun E hEK hE => ?_
  haveI := uc22p2251b_isCyclic_of_isPGroup hK hq hq2 hEK (PartTwo.isPGroup_of_isElemAbelian hq hE)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have hgq : g ^ q = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 g g.2)
  rw [pow_one, ← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd hq.pos (orderOf_dvd_of_pow_eq_one hgq)

end CFSG.LocalAnalysis.UniquenessCase.UC22
