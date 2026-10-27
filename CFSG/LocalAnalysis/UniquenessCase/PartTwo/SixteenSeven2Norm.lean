module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FstarBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

noncomputable def lO3 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Subgroup G :=
  twoResidual (preBarSub D.M V₀ V hV (pCoreOf 3 (Mbar D.M V₀ V hV)))

theorem isPGroup_pCoreOf (p : ℕ) [Fact p.Prime] {X : Type} [Group X] [Finite X] (H : Subgroup X) :
    IsPGroup p ↥(pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

theorem mem_normalizer_pCoreOf (p : ℕ) [Fact p.Prime] {X : Type} [Group X] {H : Subgroup X} {x : X}
    (hx : x ∈ H) : x ∈ Subgroup.normalizer (pCoreOf p H : Set X) := by
  have key : ∀ {x : X}, x ∈ H → ∀ {y : X}, y ∈ pCoreOf p H → x * y * x⁻¹ ∈ pCoreOf p H := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹,
      (CFSG.pCore_normal (p := p) (G := ↥H)).conj_mem z hz ⟨x, hx⟩, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key hx hy, fun hy => ?_⟩
  have := key (H.inv_mem hx) hy
  simpa [mul_assoc] using this

theorem fstar_eq_self_of_isPGroup {X : Type} [Group X] [Finite X] {H : Subgroup X} {p : ℕ}
    [Fact p.Prime]
    (hH : IsPGroup p ↥H) : UC22.Fstar H = H := by
  have hnil : Group.IsNilpotent ↥H := hH.isNilpotent
  have h1 : CFSG.generalizedFitting ↥H = ⊤ := by
    rw [CFSG.WholeGroup.generalizedFitting_eq_fittingSubgroup_of_isSolvable]
    exact top_le_iff.1 (le_sSup ⟨inferInstance, inferInstance⟩)
  exact fstar_eq_of_generalizedFitting_eq le_rfl (by rw [Subgroup.subgroupOf_self]; exact h1)

theorem twoResidual_eq_self_of_isPGroup_three {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 3 ↥P) : twoResidual P = P := by
  refine le_antisymm (twoResidual_le _) fun x hx => ?_
  have h3 : Odd (orderOf x) := by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk; simpa using this)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    rw [hj]; exact Odd.pow (by decide)
  exact F6.mem_twoResidual_of_odd hx h3

theorem barSub_twoResidual (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {H : Subgroup G}
    (hH : H ≤ stabTil V₀ V) :
    barSub V₀ V hV (twoResidual H) = twoResidual (barSub V₀ V hV H) := by
  have h1 := CFSG.Quasithin.E1.map_twoResidual (stabTil V₀ V).subtype (H.subgroupOf (stabTil V₀ V))
  rw [Subgroup.map_subgroupOf_eq_of_le hH] at h1
  have h2 : (twoResidual H).subgroupOf (stabTil V₀ V) =
      twoResidual (H.subgroupOf (stabTil V₀ V)) := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have h3 := CFSG.Quasithin.E1.map_twoResidual (actTil V₀ V hV) (H.subgroupOf (stabTil V₀ V))
  unfold barSub
  rw [h2, h3]

theorem barSub_lO3 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) :
    barSub V₀ V hV (lO3 D V₀ V hV) = pCoreOf 3 (Mbar D.M V₀ V hV) := by
  have hle : preBarSub D.M V₀ V hV (pCoreOf 3 (Mbar D.M V₀ V hV)) ≤ stabTil V₀ V := fun g hg =>
    ((mem_preBarSub _ V₀ V hV _).1 hg).2.1
  have hpc : pCoreOf 3 (Mbar D.M V₀ V hV) ≤ Mbar D.M V₀ V hV := Subgroup.map_subtype_le _
  have hP : IsPGroup 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV)) := isPGroup_pCoreOf 3 _
  unfold lO3
  rw [barSub_twoResidual V₀ V hV hle, barSub_preBarSub, inf_eq_left.2 hpc]
  exact twoResidual_eq_self_of_isPGroup_three hP

theorem setting16_lO3 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) : Setting16 D V₀ V (lO3 D V₀ V hV) := by
  have hP := hS.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hle : lO3 D V₀ V hV ≤ D.M := (twoResidual_le _).trans inf_le_left
  refine ⟨hS.hyp16, ⟨hS.hyp151.hyp125, hle, twoResidual_twoResidual _, ?_, ?_⟩⟩
  · rw [barSub_lO3 D _ hS]
    exact fstar_eq_self_of_isPGroup (isPGroup_pCoreOf 3 _)
  · intro g hg hgn
    exfalso
    apply hgn
    refine (mem_preBarSub _ _ _ _ _).2 ⟨hg, hMst hg, ?_⟩
    rw [barSub_lO3 D _ hS]
    exact mem_normalizer_pCoreOf 3 (actTil_mem_barSub V₀ V _ hg (hMst hg))

theorem barSub_lO3_ne_bot (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) (hO : IsPOnePlusTwo 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV))) :
    barSub V₀ V hV (lO3 D V₀ V hV) ≠ ⊥ := by
  rw [barSub_lO3 D hV hS]
  intro h
  have h27 := hO.2.1
  rw [h, Subgroup.card_bot] at h27
  norm_num at h27

theorem case168_3_lO3 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) (h4 : Case168_4At D V₀ V hV L 3 2) (hsig : D.sig = {3})
    (hO : IsPOnePlusTwo 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV))) :
    Case168_3 D V₀ V hV (lO3 D V₀ V hV) := by
  refine ⟨?_, ?_, hsig⟩
  · show IsPOnePlusTwo 3 ↥(barSub V₀ V hV (lO3 D V₀ V hV))
    rw [barSub_lO3 D hV hS]
    exact hO
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hd : dParam 3 = 2 := by
      unfold dParam
      exact orderOf_eq_prime (by decide) (by decide)
    obtain ⟨ι, hι, Y, hfam⟩ := s16c1610_symSumFamily_of_symSumOfConj h4.2.1
    letI := hι
    have h1 := rk_iSup_biSup_eq_sum Y hfam.indep Finset.univ
    have h2 : (⨆ i ∈ (Finset.univ : Finset ι), Y i) = ⊤ := by simpa using hfam.sup
    rw [h2] at h1
    rw [h1]
    simp [hfam.rank, hd, Finset.card_univ, hfam.card]

theorem not_isQuasisimple_of_comm {X : Type*} [Group X] (h : CFSG.Open.IsQuasisimple X)
    (hc : ∀ a b : X, a * b = b * a) : False := by
  haveI := h.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
  induction x using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  apply hxy
  rw [QuotientGroup.eq, Subgroup.mem_center_iff]
  intro g
  exact hc _ _

theorem comm_of_le_elemAbelian {X : Type*} [Group X] {K L : Subgroup X} {p r : ℕ}
    (hL : IsElemAbelianOfRank p r ↥L) (hKL : K ≤ L) : ∀ a b : ↥K, a * b = b * a := by
  obtain ⟨e⟩ := hL
  intro a b
  have := e.injective (a₁ := ⟨a.1, hKL a.2⟩ * ⟨b.1, hKL b.2⟩)
    (a₂ := ⟨b.1, hKL b.2⟩ * ⟨a.1, hKL a.2⟩) (by rw [map_mul, map_mul, mul_comm])
  exact Subtype.ext (show a.1 * b.1 = b.1 * a.1 from congrArg Subtype.val this)

theorem commSub_map_le {W : Type} [CommGroup W] {A O L : Subgroup (MulAut W)} (hLO : L ≤ O)
    (hO : ∀ g ∈ A, ∀ x ∈ O, g * x * g⁻¹ ∈ O) {g : MulAut W} (hg : g ∈ A) :
    (commSub ⊤ L).map g.toMonoidHom ≤ commSub ⊤ O := by
  unfold commSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨c, ⟨x, hx, w, -, rfl⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨g * x * g⁻¹, hO g hg x (hLO hx), g w, Subgroup.mem_top _, ?_⟩
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem conc4_136_lO3 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h4 : Case168_4At D V₀ V hV L 3 2) (hsig : D.sig = {3})
    (hO : IsPOnePlusTwo 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV))) :
    Conc4_136 D V₀ V hV (lO3 D V₀ V hV) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, htM, ht2, ht1, htrk, hW⟩ := hconc
  set Mb := Mbar D.M V₀ V hV
  set Lb := lBar V₀ V hV L
  set O := pCoreOf 3 Mb
  have hab := h4.1
  have hcommL : ∀ K : Subgroup (MulAut (Vtil V₀ V hV)), K ≤ Lb →
      CFSG.Open.IsQuasisimple ↥K → False :=
    fun K hK hq => not_isQuasisimple_of_comm hq (comm_of_le_elemAbelian hab hK)
  have h133 : Conc4_133 Mb t Lb := by
    rcases hW.2.2 with h | ⟨K, hK, g, -, -, hLK, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
    · exact h
    · exact (hcommL K (hLK ▸ le_sup_left) hK.2.2).elim
    · exact (hcommL Lb le_rfl hcomp.2.2).elim
    · exact (hcommL Lb le_rfl hcomp.2.2).elim
  obtain ⟨p, hp, hLp, hcomm, -⟩ := h133
  have hLO : Lb ≤ O := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p ↥Lb := (isPGroup_pCoreOf p Mb).to_le hLp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
    have h9 : Nat.card ↥Lb = 3 ^ 2 := by
      obtain ⟨e⟩ := hab
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp [Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
    have h3 : 3 ∣ p ^ n := hn ▸ h9 ▸ dvd_pow_self 3 two_ne_zero
    have : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    subst this
    exact hLp
  have hOn : ∀ g ∈ Mb, ∀ x ∈ O, g * x * g⁻¹ ∈ O := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_pCoreOf 3 hg) x).1 hx
  have htop : commSub ⊤ O = ⊤ := by
    refine eq_top_iff.2 (hW.1.symm.trans_le (iSup₂_le fun X hX => ?_))
    obtain ⟨g, hg, rfl⟩ := hX
    exact commSub_map_le hLO hOn hg
  have hconj : conjSubs Mb (commSub ⊤ O) = {⊤} := by
    rw [htop]
    ext X
    simp only [conjSubs, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, -, rfl⟩
      exact Subgroup.map_top_of_surjective _ g.surjective
    · rintro rfl
      exact ⟨1, Mb.one_mem, (Subgroup.map_top_of_surjective _ (1 : MulAut _).surjective).symm⟩
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := (case168_3_lO3 D hV hS h4 hsig hO).2.1
  have hbar : lBar V₀ V hV (lO3 D V₀ V hV) = O := barSub_lO3 D hV hS
  refine ⟨t, htM, ht2, ht1, htrk, ?_⟩
  show Conc4_136W Mb t (lBar V₀ V hV (lO3 D V₀ V hV))
  rw [hbar]
  refine ⟨?_, fun g hg hgn => (hgn (mem_normalizer_pCoreOf 3 hg)).elim, Or.inl ?_⟩
  · rw [hconj]
    simp
  · refine ⟨3, Nat.prime_three, le_rfl, ?_, ?_, Or.inr (Or.inr (Or.inl ⟨hO, ?_⟩))⟩
    · exact fun h => hcomm (eq_bot_iff.2 (h ▸ Subgroup.commutator_mono hLO le_rfl))
    · rw [hconj]
      exact sSupIndep_singleton _
    · rw [htop]
      exact hrk

theorem rechoice_lO3 (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h4 : Case168_4At D V₀ V hV L 3 2) (hsig : D.sig = {3})
    (hO : IsPOnePlusTwo 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV))) :
    Setting16 D V₀ V (lO3 D V₀ V hV) ∧ barSub V₀ V hV (lO3 D V₀ V hV) ≠ ⊥ ∧
      Conc4_136 D V₀ V hV (lO3 D V₀ V hV) ∧ Case168_3 D V₀ V hV (lO3 D V₀ V hV) :=
  ⟨setting16_lO3 D hV hS, barSub_lO3_ne_bot D hV hS hO, conc4_136_lO3 D hV hS hne hconc h4 hsig hO,
    case168_3_lO3 D hV hS h4 hsig hO⟩

theorem not_elemAbelianOfRank_two_of_isPOnePlusTwo {X : Type*} [Group X]
    (h1 : IsPOnePlusTwo 3 X) : ¬ IsElemAbelianOfRank 3 2 X := by
  rintro ⟨e⟩
  have h27 : Nat.card X = 3 ^ 3 := h1.2.1
  have h9 : Nat.card X = 3 ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
  omega

theorem exists_counterex16_norm (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : Setting16 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h168 : Concl168 D V₀ V hV L)
    (hall : ∀ L' : Subgroup G, Setting16 D V₀ V L' → barSub V₀ V hV L' ≠ ⊥ →
      Conc4_136 D V₀ V hV L' → ¬ Concl167 D V₀ V hV L') :
    ∃ L' : Subgroup G, Counterex16 D V₀ V L' hV ∧ ChoiceNorm1613 D V₀ V hV L' := by
  by_cases hn : ChoiceNorm1613 D V₀ V hV L
  · exact ⟨L, ⟨hS, hne, hconc, hall L hS hne hconc, hall, h168, hn⟩, hn⟩
  · simp only [ChoiceNorm1613, not_imp, not_not] at hn
    obtain ⟨h4, hsig, hO⟩ := hn
    obtain ⟨hS', hne', hconc', h3⟩ := rechoice_lO3 D hV hS hne hconc h4 hsig hO
    have hN : ChoiceNorm1613 D V₀ V hV (lO3 D V₀ V hV) := by
      intro h4' _ _
      have hL : lBar V₀ V hV (lO3 D V₀ V hV) = pCoreOf 3 (Mbar D.M V₀ V hV) :=
        barSub_lO3 D hV hS
      have h1 : IsPOnePlusTwo 3 ↥(lBar V₀ V hV (lO3 D V₀ V hV)) := hL ▸ hO
      exact not_elemAbelianOfRank_two_of_isPOnePlusTwo h1 h4'.1
    exact ⟨lO3 D V₀ V hV, ⟨hS', hne', hconc', hall _ hS' hne' hconc', hall,
      Or.inr (Or.inr (Or.inl h3)), hN⟩, hN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
