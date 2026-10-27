module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivM12
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Stab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_cent_of_perfect_bar (D : Data G) {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hP : PairFacts D.M V₀ V)
    (hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V) (h4 : Nat.card V₀ ≤ 4) (x : IntMod V hV)
    (hx0 : x.val ∉ V₀) {P₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hP₀ : P₀ ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) (hperf : Group.IsPerfect P₀)
    (hpP₀ : p ∣ Nat.card P₀) (hpker : p ∣ Nat.card (F11.CTilde D.M V₀ V)) :
    ∃ X : Subgroup G, X ≤ D.M ⊓ centralizer ({x.val} : Set G) ∧ IsPGroup p X ∧ ¬ IsCyclic X := by
  classical
  haveI : Fact p.Prime := ⟨hpp⟩
  have h113 : ∃ n ≤ 2, (D.M ⊓ centralizer ({x.val} : Set G)).relIndex
      (F11.CElt D.M V₀ x.val) = 2 ^ n := by
    rcases hcase with rfl | h
    · exact ⟨0, by norm_num, by simpa using ElevenThree.relIndex_cElt_bot D.M x.val⟩
    · exact ElevenThree.relIndex_cElt_eq_pow_two h h4 x.val_mem hx0
  have hidx : ¬ p ∣ ((D.M ⊓ centralizer ({x.val} : Set G)).subgroupOf
      (F11.CElt D.M V₀ x.val)).index := by
    obtain ⟨n, -, hn⟩ := h113
    intro hd
    have hd' : p ∣ 2 ^ n := by
      rw [← hn]
      exact hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hd'))
  have hCs : F11.CElt D.M V₀ x.val ≤ stabTil V₀ V := fun c hc => ⟨hP.le_normalizer hc.1, hc.2.1⟩
  let f : ↥(F11.CElt D.M V₀ x.val) →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hCs)
  have hfmem : ∀ c : ↥(F11.CElt D.M V₀ x.val),
      f c ∈ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro c
    refine Subgroup.mem_inf.2 ⟨actTil_mem_barSub V₀ V hV c.2.1 (hCs c.2), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    show actTil V₀ V hV ⟨c, hCs c.2⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact c.2.2.2
  let g : ↥(F11.CElt D.M V₀ x.val) →* ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)) :=
    f.codRestrict _ hfmem
  have hg : Function.Surjective g := by
    rintro ⟨φ, hφ⟩
    obtain ⟨hφM, hφst⟩ := Subgroup.mem_inf.1 hφ
    obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφM
    have hfix : actTil V₀ V hV m (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
      MulAction.mem_stabilizer_iff.1 hφst
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
    exact ⟨⟨(m : G), hmM, stabTil_le_normalizer₀ V₀ V m.2, hfix⟩, Subtype.ext rfl⟩
  have hCT_le : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ x.val :=
    iInf_le_of_le x.val (iInf_le_of_le x.val_mem le_rfl)
  have hker_eq : g.ker =
      (F11.CTilde D.M V₀ V).subgroupOf (F11.CElt D.M V₀ x.val) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hP.le_normalizer]
    constructor
    · intro hc
      refine ⟨c.2.1, hCs c.2, ?_⟩
      change f c = 1
      exact congrArg Subtype.val hc
    · rintro ⟨-, h, h1⟩
      apply Subtype.ext
      change actTil V₀ V hV (Subgroup.inclusion hCs c) = 1
      rw [show actTil V₀ V hV (Subgroup.inclusion hCs c) =
          actTil V₀ V hV ⟨(c : G), h⟩ from
        congrArg (actTil V₀ V hV) (Subtype.ext rfl), h1]
  have hpker' : p ∣ Nat.card g.ker := by
    have hcard : Nat.card g.ker = Nat.card (F11.CTilde D.M V₀ V) := by
      rw [hker_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le).toEquiv
    rw [hcard]
    exact hpker
  haveI : Group.IsPerfect ↥P₀ := hperf
  have hperf' : Group.IsPerfect ↥(P₀.subgroupOf
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hP₀).symm.toMonoidHom) (MulEquiv.surjective _)
  have hcardP : Nat.card ↥(P₀.subgroupOf
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀).toEquiv
  have hpP₀' : p ∣ Nat.card ↥(P₀.subgroupOf
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x))) := hcardP.symm ▸ hpP₀
  obtain ⟨X₀, hX₀p, hX₀c⟩ :=
    exists_noncyclic_pGroup_of_perfect_section g hg hperf' hpP₀' hpker'
  obtain ⟨X₁, hX₁K, hX₁p, hX₁c⟩ :=
    SpLift.exists_noncyclic_pSubgroup_le (MonoidHom.id ↥(F11.CElt D.M V₀ x.val))
      Function.surjective_id hidx hX₀p hX₀c
  refine ⟨X₁.map (F11.CElt D.M V₀ x.val).subtype, ?_, hX₁p.map _, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hX₁K hc)
  · exact SpLift.not_isCyclic_map (F11.CElt D.M V₀ x.val).subtype
      (Subgroup.subtype_injective _) hX₁c

theorem pRank_le_pRank_mbar_of_not_dvd {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hP : PairFacts M V₀ V) {p : ℕ} (hpp : p.Prime)
    (hnd : ¬ p ∣ Nat.card (F11.CTilde M V₀ V)) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (Mbar M V₀ V hV) := by
  have hp1 : 1 < p := hpp.one_lt
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 M
  have hdisj : E ⊓ F11.CTilde M V₀ V = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (H := E) (K := F11.CTilde M V₀ V) ?_).eq_bot
    rw [hEcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).2 hnd)
  let f : ↥M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (le_stabTil hP.le_normalizer hP.le_normalizer₀))
  let fE : ↥E →* MulAut (Vtil V₀ V hV) := f.comp (Subgroup.inclusion hEM)
  have hcomm : ∀ a b : ↥E, a * b = b * a := by
    haveI : IsMulCommutative ↥E := hE.1
    exact fun a b => mul_comm' a b
  have hpow : ∀ a : ↥E, a ^ p = 1 := fun a =>
    Subtype.ext (by simpa using hE.2 (a : G) a.2)
  have hinj : Function.Injective fE := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h2 : (y : G) ∈ F11.CTilde M V₀ V := by
      rw [mem_cTilde_iff hV hP.le_normalizer]
      refine ⟨hEM y.2, le_stabTil hP.le_normalizer hP.le_normalizer₀ (hEM y.2), ?_⟩
      change fE y = 1
      exact hy
    have h3 : (y : G) ∈ E ⊓ F11.CTilde M V₀ V := ⟨y.2, h2⟩
    rw [hdisj] at h3
    exact Subtype.ext (Subgroup.mem_bot.1 h3)
  have hrange : fE.range ≤ Mbar M V₀ V hV := by
    rintro y ⟨x, rfl⟩
    exact actTil_mem_barSub V₀ V hV (hEM x.2)
      (le_stabTil hP.le_normalizer hP.le_normalizer₀ (hEM x.2))
  exact CFSG.SectionRank.le_pRank_of_injective hp1 hcomm hpow hEcard fE hinj hrange

theorem pRank_five_le_two_of_omegaModel {W : Type} [CommGroup W] [Finite W] (S : OmegaModel W)
    (hK : Nat.card S.K = 4) (H : Subgroup (MulAut W)) : CFSG.Open.pRank 5 H ≤ 2 := by
  have hcardW : Nat.card W = 256 := by
    rw [S.card_eq, hK]
    norm_num
  have hW2 : ∀ w : W, w * w = 1 := by
    intro w
    apply S.vec_injective
    rw [S.vec_mul, S.vec_one]
    exact CharTwo.add_self_eq_zero (S.vec w)
  have hElemTop : IsElemAbelian 2 (⊤ : Subgroup W) := by
    refine ⟨inferInstance, fun x _ => ?_⟩
    simpa [pow_two] using hW2 x
  have hcardTop : Nat.card (⊤ : Subgroup W) = 256 := by
    rw [Subgroup.card_top]
    exact hcardW
  let e : MulAut (↥(⊤ : Subgroup W)) ≃* MulAut W :=
    MulAut.congr (Subgroup.topEquiv : (⊤ : Subgroup W) ≃* W)
  refine CFSG.SectionRank.pRank_le (p := 5) (H := H) (k := 2) (by norm_num) ?_
  intro E _ hE
  have hAp : IsPGroup 5 (E.map e.symm.toMonoidHom) :=
    (hE.isPGroup).map e.symm.toMonoidHom
  have hAle : Nat.card (E.map e.symm.toMonoidHom) ≤ 25 :=
    CFSG.ComponentClassification.AS81.Sec2.card_le_twentyfive_of_isPGroup
      (G := W) (W := ⊤) hElemTop hcardTop hAp
  have hcard : Nat.card (E.map e.symm.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulEquiv.injective e.symm)
  rw [hcard] at hAle
  exact hAle.trans (by norm_num)

theorem eq_of_case1633 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {m p : ℕ}
    (hm : Case1633 D V₀ V hV L m) (hp : D.sig = {p}) : (m = 2 ∧ p = 5) ∨ (m = 3 ∧ p = 3) := by
  rcases hm with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · exact Or.inl ⟨rfl, (Set.singleton_eq_singleton_iff.1 (hc.2.2.symm.trans hp)).symm⟩
  · exact Or.inr ⟨rfl, (Set.singleton_eq_singleton_iff.1 (hc.2.2.symm.trans hp)).symm⟩

theorem dvd_card_cTilde_of_case1633 (D : Data G) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV)) (hSK : Nat.card S.K = 2 ^ m)
    {p : ℕ} (hp : D.sig = {p}) : p ∣ Nat.card (F11.CTilde D.M V₀ V) := by
  have hP : PairFacts D.M V₀ V := hS.setting.hyp16.hyp125.pairFacts
  rcases eq_of_case1633 hm hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_contra hnd
    have h1 := pRank_le_pRank_mbar_of_not_dvd hV hP (by norm_num) hnd
    have h2 := pRank_five_le_two_of_omegaModel S (by rw [hSK]; norm_num) (Mbar D.M V₀ V hV)
    have h3 := hext.three_le 5 (by rw [hp]; exact Set.mem_singleton 5)
    omega
  · rcases hm with ⟨hc, h⟩ | ⟨hc, -⟩
    · omega
    · exact (h5 V₀ V L hV hS.setting hS.ne_bot hS.conc hc.1).2

theorem r16_34_coord (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p})
    {x : IntMod V hV} (hx : S.Q (mkTil V₀ V hV x) ≠ 0) :
    1 < CFSG.Open.pRank p (D.M ⊓ centralizer ({x.val} : Set G)) ∧
      centralizer ({x.val} : Set G) ≤ D.M := by
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := hH125.pairFacts
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases hH125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4 : Nat.card V₀ ≤ 4 := by
    have hV₀2 : IsPGroup 2 V₀ := fun g =>
      ⟨1, Subtype.ext (by simpa using hP.elemAbelian₀.2 (g : G) g.2)⟩
    rw [card_eq_two_pow_mSub hV₀2]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS.setting.hyp16.small
      _ = 4 := by norm_num
  have hpsig : p ∈ D.sig := by
    rw [hp]
    exact Set.mem_singleton p
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpsig
  have hx1 : mkTil V₀ V hV x ≠ 1 := fun h => hx (h ▸ S.Q_one)
  have hx0 : x.val ∉ V₀ := fun h0 =>
    hx1 ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 h0)
  have hperf := S.isPerfect_ptCent_omega0 hx
  have hcard := S.card_ptCent_omega0 hx
  have hpP₀ : p ∣ Nat.card ↥(ptCent S.omega0 (mkTil V₀ V hV x)) := by
    rw [hcard, hSK]
    rcases eq_of_case1633 hm hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hP₀ : ptCent S.omega0 (mkTil V₀ V hV x) ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    refine inf_le_inf_right _ ?_
    calc S.omega0 ≤ S.omega := S.omega0_le_omega
      _ = lBar V₀ V hV L := hSω
      _ ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hS.setting.hyp151.le
  have hker := dvd_card_cTilde_of_case1633 D hext h5 hS hm S hSK hp
  obtain ⟨X, hXle, hXp, hXc⟩ := exists_noncyclic_cent_of_perfect_bar D hpp hp2 hV hP hcase h4 x
    hx0 hP₀ hperf hpP₀ hker
  refine ⟨?_, ?_⟩
  · have h2 := uc22p22u_two_le_pRank hpp hp2 hXp hXc
    have h3 := CFSG.SectionRank.pRank_mono hpp.one_lt hXle
    omega
  · have hx1' : x.val ≠ 1 := fun h => hx0 (h ▸ V₀.one_mem)
    have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x.val x.val_mem⟩
    exact centralizer_le_of_noncyclic D h61 hpsig (hXle.trans inf_le_left) hXp hXc hx1' hx2
      (hXle.trans inf_le_right)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
