module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbKit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F431Kit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_Mbar_le_normalizer {D : Data G} (hkitB : OmegaKitB) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    Mbar D.M V₀ V hV ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  intro x hx
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M x).1 hx
  by_contra hxnot
  have hmn : (m : G) ∉ nBar D.M V₀ V hV L := by
    intro hmem
    obtain ⟨-, h, hh⟩ := (mem_preBarSub D.M V₀ V hV
      (normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))).1 hmem
    rw [show (⟨(m : G), h⟩ : ↥(stabTil V₀ V)) = m from Subtype.ext rfl] at hh
    exact hxnot hh
  have hc1 : ⁅lBar V₀ V hV L, barSub V₀ V hV (conjSubgroup L (m : G))⁆ = ⊥ :=
    (hS.setting.hyp151.commute (m : G) hmM hmn).1
  have hle : barSub V₀ V hV (conjSubgroup L (m : G)) ≤
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc1
  have hbot : barSub V₀ V hV (conjSubgroup L (m : G)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact (hkitB (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).1 y
      (fun h hh => (Subgroup.mem_centralizer_iff.1 (hle hy) h hh).symm)
  have hmap : barSub V₀ V hV (conjSubgroup L (m : G)) =
      (lBar V₀ V hV L).map (MulAut.conj (actTil V₀ V hV m)⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup V₀ V hV m.2 L
  refine hS.ne_bot ?_
  have hmapbot : (lBar V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV m)⁻¹).toMonoidHom = ⊥ := hmap.symm.trans hbot
  exact (Subgroup.map_eq_bot_iff_of_injective (lBar V₀ V hV L)
    (MulEquiv.injective (MulAut.conj (actTil V₀ V hV m)⁻¹))).1 hmapbot

theorem s16c1_431_barSub_le_of_mem {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {i : ℕ} {A : Subgroup G} {g : G} (hy : Hyp1643 D V₀ V i A g) (hg : g ∈ D.M)
    (hS : Sect16 D V₀ V L hV) :
    barSub V₀ V hV A ≤ lBar V₀ V hV L := by
  have hA : A ≤ D.M := hy.2.1.1
  have hAg : A ≤ conjSubgroup V g := hy.2.2
  have hgN : g ∈ normalizer (V : Set G) := hS.setting.hyp151.hyp125.pairFacts.le_normalizer hg
  have hAV : A ≤ V := by
    intro a ha
    have h1 : g * a * g⁻¹ ∈ V := (mem_conjSubgroup_iff.1 (hAg ha))
    exact (Subgroup.mem_normalizer_iff.1 hgN a).2 h1
  have hbar : barSub V₀ V hV A = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨a, haA, rfl⟩ := (mem_barSub V₀ V hV A φ).1 hφ
    rw [Subgroup.mem_bot, actTil_eq_one_iff]
    intro v hv
    have hcomm : (a : G) * v = v * (a : G) :=
      congrArg Subtype.val (hV.1.is_comm.comm (⟨(a : G), hAV haA⟩ : V) ⟨v, hv⟩)
    have h1 : (a : G) * v * (a : G)⁻¹ * v⁻¹ = 1 := by rw [hcomm]; group
    rw [h1]
    exact V₀.one_mem
  rw [hbar]
  exact bot_le

theorem s16c1_431_outer {D : Data G} (hkitB : OmegaKitB) (hkitC : OmegaKitC) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {i : ℕ}
    {A : Subgroup G} {g : G} (hy : Hyp1643 D V₀ V i A g)
    {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q) (hQi : QuadInvariant Q (lBar V₀ V hV L))
    (hnot : ¬ barSub V₀ V hV A ≤ lBar V₀ V hV L) :
    ∃ (a : G) (ha : a ∈ stabTil V₀ V), a ∈ A ∧
      ∃ w : Vtil V₀ V hV, Q (actTil V₀ V hV ⟨a, ha⟩ w * w⁻¹) ≠ 0 := by
  obtain ⟨φ, hφA, hφL⟩ := Set.not_subset.1
    (show ¬ (barSub V₀ V hV A : Set (MulAut (Vtil V₀ V hV))) ⊆
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) from hnot)
  obtain ⟨m, hmA, hmφ⟩ := (mem_barSub V₀ V hV A φ).1 hφA
  have hMbar : actTil V₀ V hV m ∈ Mbar D.M V₀ V hV :=
    actTil_mem_barSub V₀ V hV (hy.2.1.1 hmA) m.2
  have hnorm : actTil V₀ V hV m ∈
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    s16c1_Mbar_le_normalizer hkitB hS hc hMbar
  have hout : OmegaOuterNons (lBar V₀ V hV L) :=
    (hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.2.1
  have hmnotL : actTil V₀ V hV m ∉ lBar V₀ V hV L := by
    rw [hmφ]
    exact hφL
  obtain ⟨w, hw⟩ := hout Q hQ hQi (actTil V₀ V hV m) hnorm hmnotL
  exact ⟨(m : G), m.2, hmA, w, hw⟩

private theorem s16c1_quadF2_one {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    (hQ : IsQuadF2 Q) : Q 1 = 0 := by
  have h := hQ.1 1 1 1
  simp only [polarQ, mul_one] at h
  generalize Q 1 = a at h ⊢
  revert a
  decide

theorem s16c1_431_not_le_conj {D : Data G} (h22 : R1622 D) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {i : ℕ} {A : Subgroup G} {g : G}
    (hy : Hyp1643 D V₀ V i A g) (hg : g ∉ D.M)
    {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q) (hQi : QuadInvariant Q (lBar V₀ V hV L))
    {a : G} (haS : a ∈ stabTil V₀ V) (haA : a ∈ A) {w : Vtil V₀ V hV}
    (hw : Q (actTil V₀ V hV ⟨a, haS⟩ w * w⁻¹) ≠ 0) :
    ¬ V ≤ conjSubgroup D.M g := by
  intro hVle
  obtain ⟨v, hv⟩ := mkTil_surjective V₀ V hV w
  have haN : a ∈ normalizer (V : Set G) := stabTil_le_normalizer V₀ V haS
  have hav : a * v.val * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 haN v.val).1 v.val_mem
  set v' : G := a * v.val * a⁻¹ * v.val⁻¹ with hv'def
  have hv'V : v' ∈ V := by
    rw [hv'def]
    exact V.mul_mem hav (V.inv_mem v.val_mem)
  have hv'2 : v' ^ 2 = 1 := hV.2 v' hv'V
  have hEq : mkTil V₀ V hV (IntMod.mk hV ⟨v', hv'V⟩) =
      actTil V₀ V hV ⟨a, haS⟩ w * w⁻¹ := by
    have h1 : actTil V₀ V hV ⟨a, haS⟩ w =
        mkTil V₀ V hV (actStab V₀ V hV ⟨a, haS⟩ v) := by
      rw [← hv]
      exact actTil_mk V₀ V hV ⟨a, haS⟩ v
    have h2 : w⁻¹ = mkTil V₀ V hV v⁻¹ := by
      rw [← hv]
      exact (map_inv (mkTil V₀ V hV) v).symm
    have h3 : (IntMod.mk hV ⟨v', hv'V⟩ : IntMod V hV) =
        actStab V₀ V hV ⟨a, haS⟩ v * v⁻¹ := by
      apply IntMod.val_injective
      simp only [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
      exact hv'def
    rw [h1, h2, ← map_mul, h3]
  have hw' : Q (mkTil V₀ V hV (IntMod.mk hV ⟨v', hv'V⟩)) ≠ 0 := by
    rw [hEq]
    exact hw
  have hv'ne : v' ≠ 1 := by
    intro h1
    apply hw'
    have hone : (IntMod.mk hV ⟨v', hv'V⟩ : IntMod V hV) = 1 := by
      apply IntMod.val_injective
      change v' = 1
      exact h1
    rw [hone, map_one]
    exact s16c1_quadF2_one hQ.1.1
  have h41' := (h41 V₀ V L hV hS hc).2 Q hQ hQi
  have hCv' : Subgroup.centralizer ({v'} : Set G) ≤ D.M := by
    have h := (h41'.2 (mkTil V₀ V hV (IntMod.mk hV ⟨v', hv'V⟩)) hw').2
      (IntMod.mk hV ⟨v', hv'V⟩) rfl
    change Subgroup.centralizer ({v'} : Set G) ≤ D.M at h
    exact h
  have haVg : a ∈ conjSubgroup V g := hy.2.2 haA
  have hvN : v.val ∈ normalizer (conjSubgroup V g : Set G) := by
    have hMgN : conjSubgroup D.M g ≤ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer V g]
      exact Subgroup.map_mono hS.setting.hyp151.hyp125.pairFacts.le_normalizer
    exact hMgN (hVle v.val_mem)
  have hv'Vg : v' ∈ conjSubgroup V g := by
    have hmem : v.val * a⁻¹ * v.val⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hvN a⁻¹).1 ((conjSubgroup V g).inv_mem haVg)
    have heq : v' = a * (v.val * a⁻¹ * v.val⁻¹) := by
      rw [hv'def]
      group
    rw [heq]
    exact (conjSubgroup V g).mul_mem haVg hmem
  have hgv'V : g * v' * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hv'Vg
  have hgv'ne : g * v' * g⁻¹ ≠ 1 := by
    intro h1
    have : v' = 1 := by
      have hc := congrArg (fun y => g⁻¹ * y * g) h1
      simpa [mul_assoc] using hc
    exact hv'ne this
  let U : Subgroup G := Subgroup.zpowers v'
  have hUV : U ≤ V := Subgroup.zpowers_le.mpr hv'V
  have hU2 : ∀ x ∈ U, x = 1 ∨ x = v' := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have horder : orderOf v' = 2 := orderOf_eq_prime hv'2 hv'ne
    have hmod : v' ^ (k % (2 : ℤ)) = v' ^ k := by
      simpa [horder] using zpow_mod_orderOf v' k
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [h0, zpow_zero] at hmod
      rw [← hk]
      exact hmod.symm
    · right
      rw [h1, zpow_one] at hmod
      rw [← hk]
      exact hmod.symm
  have hNU_le_cent : Subgroup.normalizer (U : Set G) ≤
      Subgroup.centralizer ({v'} : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : n * v' * n⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 hn v').1 (Subgroup.mem_zpowers v')
    rcases hU2 (n * v' * n⁻¹) hmem with h1 | h2
    · exfalso
      have : v' = 1 := by
        have hc := congrArg (fun y => n⁻¹ * y * n) h1
        simpa [mul_assoc] using hc
      exact hv'ne this
    · calc n * v' = (n * v' * n⁻¹) * n := by group
        _ = v' * n := by rw [h2]
  have hΓ : rankThreeGamma 1 2 U ≤ D.M := by
    refine CFSG.LocalAnalysis.WeakClosure81.rankThreeGamma_le_of_normalizer_le
      (M := D.M) (V₀ := U) (Z := U) ?_ le_rfl
    intro X hXU hXne
    have hv'X : v' ∈ X := by
      by_contra hnot
      exact hXne (le_bot_iff.1 fun x hx => by
        rcases hU2 x (hXU hx) with h1 | h2
        · simpa [h1]
        · exact absurd (h2 ▸ hx) hnot)
    have hXUeq : X = U := le_antisymm hXU (Subgroup.zpowers_le.mpr hv'X)
    rw [hXUeq]
    exact hNU_le_cent.trans hCv'
  have hg'inv : g⁻¹ ∉ D.M := fun hh => hg (by simpa using D.M.inv_mem hh)
  have hbot : conjSubgroup U g⁻¹ ⊓ V = ⊥ :=
    h22 V₀ V hS.setting.hyp16 g⁻¹ hg'inv U hUV hΓ
  have hmem : g * v' * g⁻¹ ∈ conjSubgroup U g⁻¹ ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, hgv'V⟩
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * v' * g⁻¹) * (g⁻¹)⁻¹ = v' := by group
    rw [e]
    exact Subgroup.mem_zpowers v'
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hgv'ne hmem

private theorem s16c1_relIndex_inf_preBarSub_eq_card_barSub {M X V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hXM : X ≤ M) (hX : X ≤ stabTil V₀ V) :
    (X ⊓ preBarSub M V₀ V hV ⊥).relIndex X = Nat.card (barSub V₀ V hV X) := by
  let ψ : ↥X →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hX)
  have hker : ψ.ker = (X ⊓ preBarSub M V₀ V hV ⊥).subgroupOf X := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨g.2, ?_⟩
      refine (mem_preBarSub M V₀ V hV ⊥).2 ⟨hXM g.2, hX g.2, ?_⟩
      rw [Subgroup.mem_bot]
      exact h
    · rintro ⟨-, hpre⟩
      obtain ⟨-, h', hh'⟩ := (mem_preBarSub M V₀ V hV ⊥).1 hpre
      have hh1 : actTil V₀ V hV (⟨(g : G), h'⟩ : ↥(stabTil V₀ V)) = 1 :=
        Subgroup.mem_bot.1 hh'
      show ψ g = 1
      change actTil V₀ V hV (Subgroup.inclusion hX g) = 1
      rw [show Subgroup.inclusion hX g = (⟨(g : G), h'⟩ : ↥(stabTil V₀ V))
        from Subtype.ext rfl, hh1]
  have hrange : ψ.range = barSub V₀ V hV X := by
    show ((actTil V₀ V hV).comp (Subgroup.inclusion hX)).range = barSub V₀ V hV X
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  rw [show (X ⊓ preBarSub M V₀ V hV ⊥).relIndex X =
      ((X ⊓ preBarSub M V₀ V hV ⊥).subgroupOf X).index from rfl, ← hker,
    Subgroup.index_ker, hrange]

theorem s16c1_431_rank {D : Data G} (h22 : R1622 D) (h42 : R16_42 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {i : ℕ}
    {A : Subgroup G} {g : G} (hy : Hyp1643 D V₀ V i A g) (hnot : ¬ V ≤ conjSubgroup D.M g) :
    16 ≤ Nat.card (barSub V₀ V hV A) := by
  by_contra h16
  have hlt : Nat.card (barSub V₀ V hV A) < 16 := not_le.1 h16
  have hAM : A ≤ D.M := hy.2.1.1
  have hAg : A ≤ conjSubgroup V g := hy.2.2
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hA_stab : A ≤ stabTil V₀ V := hAM.trans hMstab
  let X₀ : Subgroup G := A ⊓ preBarSub D.M V₀ V hV ⊥
  have hX₀A : X₀ ≤ A := inf_le_left
  have hX₀M : X₀ ≤ D.M := hX₀A.trans hAM
  have hX₀g : X₀ ≤ conjSubgroup V g := hX₀A.trans hAg
  have hmQA : E3.mQuot (conjSubgroup V g) A = i :=
    mQuot_eq_of_mem_gammaSet hy.2.1 hy.2.2
  have hX₀gam : X₀ ∈ E3.gammaSet V (i + E3.mQuot A X₀) D.M := by
    refine ⟨hX₀M, g, hX₀g, ?_⟩
    rw [E3.mQuot_add hX₀A hAg, hmQA]
    exact Nat.add_comm _ _
  have hcardpos : Nat.card (barSub V₀ V hV A) ≠ 0 := Nat.card_pos.ne'
  have hk_le : E3.mQuot A X₀ ≤ 3 := by
    have hrel := s16c1_relIndex_inf_preBarSub_eq_card_barSub (V₀ := V₀) (V := V)
      (hV := hV) hAM hA_stab
    have hpow : ¬ (2 ^ 4 ∣ Nat.card (barSub V₀ V hV A)) := by
      intro hdvd
      have h16' : 16 ≤ Nat.card (barSub V₀ V hV A) := by
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hcardpos) hdvd
        simpa using hle
      omega
    have h4 : ¬ 4 ≤ padicValNat 2 (Nat.card (barSub V₀ V hV A)) :=
      fun hle => hpow ((Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 4)
        (n := Nat.card (barSub V₀ V hV A)) (by norm_num) hcardpos).2 hle)
    rw [E3.mQuot, hrel]
    omega
  have hr : ((i + E3.mQuot A X₀ + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have h42' := h42 V₀ V L hV hS hc
    rcases hy.1 with hi0 | ⟨hV₀bot, hi1⟩
    · have hle : i + E3.mQuot A X₀ + mSub V₀ ≤ mSub V₀ + 3 := by omega
      have hlt' : ((mSub V₀ + 3 : ℕ) : ℕ∞) < ((mSub V₀ + 4 : ℕ) : ℕ∞) :=
        WithTop.coe_lt_coe.mpr (by omega)
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) (hlt'.trans_le h42'.1)
    · have hle : i + E3.mQuot A X₀ + mSub V₀ ≤ 4 := by
        rw [hi1, hV₀bot, mSub, rk_bot]
        omega
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) (h42'.2.2 hV₀bot)
  have h23 := sixteen_twentyThree_one D h22 hS.setting.hyp16 hX₀gam hX₀g hr
  apply hnot
  refine le_trans ?_ h23.2.2
  intro v hv
  refine Subgroup.mem_inf.2 ⟨hv, h23.2.1 v hv ?_⟩
  intro a ha
  obtain ⟨-, hpre⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨-, hstab, hact⟩ := (mem_preBarSub D.M V₀ V hV ⊥).1 hpre
  have hact1 : actTil V₀ V hV (⟨a, hstab⟩ : ↥(stabTil V₀ V)) = 1 := Subgroup.mem_bot.1 hact
  have hcomm : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ V₀ :=
    (actTil_eq_one_iff V₀ V hV ⟨a, hstab⟩).1 hact1 v hv
  rw [commutatorElement_def]
  have heq : v * a * v⁻¹ * a⁻¹ = ((a : G) * v * (a : G)⁻¹ * v⁻¹)⁻¹ := by group
  rw [heq]
  exact V₀.inv_mem hcomm

theorem s16c1_431_finish {D : Data G} (hkitB : OmegaKitB) (hkitC : OmegaKitC) (h22 : R1622 D)
    (h42 : R16_42 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {i : ℕ} {A : Subgroup G} {g : G} (hy : Hyp1643 D V₀ V i A g)
    (hnot : ¬ barSub V₀ V hV A ≤ lBar V₀ V hV L) (h16 : 16 ≤ Nat.card (barSub V₀ V hV A)) :
    V ≤ conjSubgroup D.M g := by
  have hAM : A ≤ D.M := hy.2.1.1
  have hAg : A ≤ conjSubgroup V g := hy.2.2
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hA_stab : A ≤ stabTil V₀ V := hAM.trans hMstab
  have hAElem : IsElemAbelian 2 A := (E3.isElemAbelian_conjSubgroup hV g).mono hAg
  have hAel : IsElemAbelian 2 (barSub V₀ V hV A) :=
    (hAElem.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
  have hAel2 : IsElemAbelian2 (barSub V₀ V hV A) := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · exact hAel.2 x hx
  have hbarNorm : barSub V₀ V hV A ≤
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hAM).trans (s16c1_Mbar_le_normalizer hkitB hS hc)
  have hkitC' := hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hrank : Nat.card (barSub V₀ V hV A) ≤ 16 :=
    hkitC'.2.2.2.1 (barSub V₀ V hV A) hbarNorm hAel2
  have hcard16 : Nat.card (barSub V₀ V hV A) = 16 := le_antisymm hrank h16
  obtain ⟨ā₁, hā₁, ā₂, hā₂, hcomm₁, hcomm₂, hfix⟩ :=
    hkitC'.2.2.2.2 (barSub V₀ V hV A) hbarNorm hAel2 hcard16 hnot
  obtain ⟨a₁, ha₁A, ha₁eq⟩ := (mem_barSub V₀ V hV A ā₁).1 hā₁
  obtain ⟨a₂, ha₂A, ha₂eq⟩ := (mem_barSub V₀ V hV A ā₂).1 hā₂
  have hcommVbot : commV (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) = ⊥ := by
    rw [commV, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨x, hx, v, rfl⟩
    rw [Subgroup.mem_bot] at hx
    simp [hx]
  have hāne : ∀ (ā : MulAut (Vtil V₀ V hV)),
      Nat.card (commV (Subgroup.zpowers ā)) = 2 → ā ≠ 1 := by
    intro ā hcomm h1
    have hcard : Nat.card (commV (Subgroup.zpowers ā)) = 1 := by
      rw [h1, Subgroup.zpowers_one_eq_bot, hcommVbot]
      simp
    omega
  have step : ∀ (ā : MulAut (Vtil V₀ V hV)) (a : ↥(stabTil V₀ V)),
      ā ∈ barSub V₀ V hV A → (a : G) ∈ A → actTil V₀ V hV a = ā → ā ≠ 1 →
      preTil V₀ V hV (fixV (Subgroup.zpowers ā)) ≤ conjSubgroup D.M g := by
    intro ā a hāA haA haeq hāne'
    let X₀ : Subgroup G := A ⊓ preBarSub D.M V₀ V hV ⊥
    let X : Subgroup G := A ⊓ preBarSub D.M V₀ V hV (Subgroup.zpowers ā)
    have hX₀A : X₀ ≤ A := inf_le_left
    have hXA : X ≤ A := inf_le_left
    have hXM : X ≤ D.M := hXA.trans hAM
    have hXg : X ≤ conjSubgroup V g := hXA.trans hAg
    have hX₀_le_X : X₀ ≤ X :=
      le_inf inf_le_left (inf_le_right.trans
        (le_inf inf_le_left (inf_le_right.trans (Subgroup.map_mono (Subgroup.comap_mono bot_le)))))
    have hmQA0 : E3.mQuot A X₀ = 4 := by
      rw [E3.mQuot, s16c1_relIndex_inf_preBarSub_eq_card_barSub (V₀ := V₀) (V := V)
        (hV := hV) hAM hA_stab, hcard16]
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
    have hXgam : X ∈ E3.gammaSet V (i + E3.mQuot A X) D.M := by
      refine ⟨hXM, g, hXg, ?_⟩
      rw [E3.mQuot_add hXA hAg, mQuot_eq_of_mem_gammaSet hy.2.1 hy.2.2]
      exact Nat.add_comm _ _
    have hk_le3 : E3.mQuot A X ≤ 3 := by
      have hle : E3.mQuot A X ≤ 4 := by
        rw [← hmQA0]
        exact E3.mQuot_mono hX₀_le_X
      by_contra hcon
      have h4 : E3.mQuot A X = 4 := by omega
      have hadd := E3.mQuot_add hX₀_le_X hXA
      rw [hmQA0, h4] at hadd
      have hzero : E3.mQuot X X₀ = 0 := by omega
      have hX2 : IsPGroup 2 X := (hAElem.mono hXA).isPGroup
      have hXeq : X₀ = X := (E3.mQuot_eq_zero_iff hX2 hX₀_le_X).1 hzero
      have hak : (a : G) ∈ X := by
        refine Subgroup.mem_inf.2 ⟨haA, ?_⟩
        refine (mem_preBarSub D.M V₀ V hV (Subgroup.zpowers ā)).2
          ⟨hAM haA, a.2, ?_⟩
        rw [haeq]
        exact Subgroup.mem_zpowers ā
      have hanot : (a : G) ∉ X₀ := by
        intro hmem
        obtain ⟨-, hpre⟩ := Subgroup.mem_inf.1 hmem
        obtain ⟨-, h', hh'⟩ := (mem_preBarSub D.M V₀ V hV ⊥).1 hpre
        have hh1 : actTil V₀ V hV (⟨(a : G), h'⟩ : ↥(stabTil V₀ V)) = 1 :=
          Subgroup.mem_bot.1 hh'
        have h1 : actTil V₀ V hV a = 1 := by
          rw [show a = (⟨(a : G), h'⟩ : ↥(stabTil V₀ V)) from Subtype.ext rfl]
          exact hh1
        exact hāne' (haeq ▸ h1)
      exact hanot (hXeq ▸ hak)
    have hr : ((i + E3.mQuot A X + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
      have h42' := h42 V₀ V L hV hS hc
      rcases hy.1 with hi0 | ⟨hV₀bot, hi1⟩
      · have hle : i + E3.mQuot A X + mSub V₀ ≤ mSub V₀ + 3 := by omega
        have hlt' : ((mSub V₀ + 3 : ℕ) : ℕ∞) < ((mSub V₀ + 4 : ℕ) : ℕ∞) :=
          WithTop.coe_lt_coe.mpr (by omega)
        exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) (hlt'.trans_le h42'.1)
      · have hle : i + E3.mQuot A X + mSub V₀ ≤ 4 := by
          rw [hi1, hV₀bot, mSub, rk_bot]
          omega
        exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) (h42'.2.2 hV₀bot)
    have h23 := sixteen_twentyThree_one D h22 hS.setting.hyp16 hXgam hXg hr
    intro v hv
    have hvV : v ∈ V := preTil_le V₀ V hV _ hv
    refine h23.2.2 (Subgroup.mem_inf.2 ⟨hvV, h23.2.1 v hvV ?_⟩)
    intro b hb
    obtain ⟨-, hpre_b⟩ := Subgroup.mem_inf.1 hb
    obtain ⟨-, hb_stab, hb_act⟩ :=
      (mem_preBarSub D.M V₀ V hV (Subgroup.zpowers ā)).1 hpre_b
    have hwfix : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈ fixV (Subgroup.zpowers ā) := by
      obtain ⟨x, hx, hxS⟩ := (mem_preTil V₀ V hV _).1 hv
      have hx' : (IntMod.mk hV ⟨v, hvV⟩ : IntMod V hV) = x := IntMod.val_injective hx.symm
      rwa [hx']
    have hact_w : actTil V₀ V hV (⟨(b : G), hb_stab⟩ : ↥(stabTil V₀ V))
        (mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) :=
      mem_fixV.1 hwfix _ hb_act
    have h1 : mkTil V₀ V hV
        (actStab V₀ V hV ⟨(b : G), hb_stab⟩ (IntMod.mk hV ⟨v, hvV⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) := by
      rw [← actTil_mk]
      exact hact_w
    have h2 : (b : G) * v * (b : G)⁻¹ * v⁻¹ ∈ V₀ := by
      have hh := (mkTil_eq_iff V₀ V hV
        (actStab V₀ V hV ⟨(b : G), hb_stab⟩ (IntMod.mk hV ⟨v, hvV⟩))
        (IntMod.mk hV ⟨v, hvV⟩)).1 h1
      rwa [actStab_apply_val] at hh
    rw [commutatorElement_def]
    have heq : v * b * v⁻¹ * b⁻¹ = ((b : G) * v * (b : G)⁻¹ * v⁻¹)⁻¹ := by group
    rw [heq]
    exact V₀.inv_mem h2
  have hP₁ : preTil V₀ V hV (fixV (Subgroup.zpowers ā₁)) ≤ conjSubgroup D.M g :=
    step ā₁ a₁ hā₁ ha₁A ha₁eq (hāne ā₁ hcomm₁)
  have hP₂ : preTil V₀ V hV (fixV (Subgroup.zpowers ā₂)) ≤ conjSubgroup D.M g :=
    step ā₂ a₂ hā₂ ha₂A ha₂eq (hāne ā₂ hcomm₂)
  have hV₀P₁ : V₀ ≤ preTil V₀ V hV (fixV (Subgroup.zpowers ā₁)) := by
    intro w hw
    have hwV : w ∈ V := hS.setting.hyp151.hyp125.pairFacts.le hw
    rw [mem_preTil_iff_of_mem V₀ V hV _ hwV]
    have h1 : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) = 1 := by
      rw [show mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) =
        ((IntMod.mk hV ⟨w, hwV⟩ : IntMod V hV) : Vtil V₀ V hV) from rfl,
        QuotientGroup.eq_one_iff, mem_modNull]
      exact hw
    rw [h1]
    exact (fixV (Subgroup.zpowers ā₁)).one_mem
  have hUV : preTil V₀ V hV (fixV (Subgroup.zpowers ā₁)) ⊔
      preTil V₀ V hV (fixV (Subgroup.zpowers ā₂)) ≤ V :=
    sup_le (preTil_le V₀ V hV _) (preTil_le V₀ V hV _)
  have hV₀P : V₀ ≤ preTil V₀ V hV (fixV (Subgroup.zpowers ā₁)) ⊔
      preTil V₀ V hV (fixV (Subgroup.zpowers ā₂)) := hV₀P₁.trans le_sup_left
  have himg : imgTil V₀ V hV (preTil V₀ V hV (fixV (Subgroup.zpowers ā₁)) ⊔
      preTil V₀ V hV (fixV (Subgroup.zpowers ā₂))) = ⊤ := by
    rw [s15_Core_imgTil_sup hV (preTil_le V₀ V hV _) (preTil_le V₀ V hV _),
      imgTil_preTil, imgTil_preTil, hfix]
  have heq : V = preTil V₀ V hV (fixV (Subgroup.zpowers ā₁)) ⊔
      preTil V₀ V hV (fixV (Subgroup.zpowers ā₂)) :=
    (s15_Two_eq_of_imgTil_eq_top hV hUV hV₀P himg).symm
  rw [heq]
  exact sup_le hP₁ hP₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
