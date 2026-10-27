module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F431Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Kit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1G44_quadF2_one {W : Type*} [CommGroup W] {Q : W → ZMod 2}
    (hQ : IsQuadF2 Q) : Q 1 = 0 := by
  have h := hQ.1 1 1 1
  simp only [polarQ, mul_one] at h
  generalize Q 1 = a at h ⊢
  revert a
  decide

theorem s16c1G44_relIndex_inf_preBarSub_eq_card_barSub {M X V₀ V : Subgroup G}
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

theorem s16c1G44_mQuot_inf_left (V U : Subgroup G) : E3.mQuot V (V ⊓ U) = E3.mQuot V U := by
  unfold E3.mQuot
  rw [inf_comm V U, Subgroup.inf_relIndex_right]

theorem s16c1G44_index_img {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {M' : Subgroup G}
    (hidx : E3.mQuot V M' ≤ 1) : (imgTil V₀ V hV (V ⊓ M')).index ∣ 2 := by
  have h1 : (imgTil V₀ V hV (V ⊓ M')).index ∣ (intSub V hV (V ⊓ M')).index :=
    Subgroup.index_map_dvd _ (mkTil_surjective V₀ V hV)
  have h2 : (intSub V hV (V ⊓ M')).index = M'.relIndex V := by
    show ((V ⊓ M').subgroupOf V).index = M'.relIndex V
    rw [← Subgroup.relIndex, inf_comm, Subgroup.inf_relIndex_right]
  have h3 : M'.relIndex V = 2 ^ E3.mQuot V M' := E3.relIndex_eq_two_pow hV.isPGroup M'
  rw [h2, h3] at h1
  exact h1.trans (by simpa using pow_dvd_pow 2 hidx)

theorem s16c1G44_fix_img {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {U : Subgroup G} {b : G}
    (hb : b ∈ stabTil V₀ V) (hbU : b ∈ centralizer (U : Set G)) :
    ∀ p ∈ imgTil V₀ V hV U, actTil V₀ V hV ⟨b, hb⟩ p = p := by
  intro p hp
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U p).1 hp
  rw [actTil_mk]
  congr 1
  apply IntMod.val_injective
  rw [actStab_apply_val]
  have h := Subgroup.mem_centralizer_iff.1 hbU x.val hxU
  rw [← h]
  group

theorem s16c1G44_isElemAbelian2_barSub {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {B : Subgroup G} {g : G} (hBg : B ≤ conjSubgroup V g) (hB : B ≤ stabTil V₀ V) :
    IsElemAbelian2 (barSub V₀ V hV B) := by
  have hBElem : IsElemAbelian 2 B := (E3.isElemAbelian_conjSubgroup hV g).mono hBg
  have hBel : IsElemAbelian 2 (barSub V₀ V hV B) :=
    (hBElem.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · exact hBel.2 x hx

theorem s16c1G44_good {D : Data G} (h22 : R1622 D) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {g : G} (hg : g ∉ D.M)
    {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q)
    (hQi : QuadInvariant Q (lBar V₀ V hV L))
    {a : G} (haS : a ∈ stabTil V₀ V) (haVg : a ∈ conjSubgroup V g)
    {u : IntMod V hV} (huM : u.val ∈ conjSubgroup D.M g) :
    Q (actTil V₀ V hV ⟨a, haS⟩ (mkTil V₀ V hV u) * (mkTil V₀ V hV u)⁻¹) = 0 := by
  by_contra hw
  have haN : a ∈ normalizer (V : Set G) := stabTil_le_normalizer V₀ V haS
  have hav : a * u.val * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 haN u.val).1 u.val_mem
  set v' : G := a * u.val * a⁻¹ * u.val⁻¹ with hv'def
  have hv'V : v' ∈ V := by
    rw [hv'def]
    exact V.mul_mem hav (V.inv_mem u.val_mem)
  have hv'2 : v' ^ 2 = 1 := hV.2 v' hv'V
  have hEq : mkTil V₀ V hV (IntMod.mk hV ⟨v', hv'V⟩) =
      actTil V₀ V hV ⟨a, haS⟩ (mkTil V₀ V hV u) * (mkTil V₀ V hV u)⁻¹ := by
    have h1 : actTil V₀ V hV ⟨a, haS⟩ (mkTil V₀ V hV u) =
        mkTil V₀ V hV (actStab V₀ V hV ⟨a, haS⟩ u) := actTil_mk V₀ V hV ⟨a, haS⟩ u
    have h2 : (mkTil V₀ V hV u)⁻¹ = mkTil V₀ V hV u⁻¹ := (map_inv (mkTil V₀ V hV) u).symm
    have h3 : (IntMod.mk hV ⟨v', hv'V⟩ : IntMod V hV) =
        actStab V₀ V hV ⟨a, haS⟩ u * u⁻¹ := by
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
    exact s16c1G44_quadF2_one hQ.1.1
  have h41' := (h41 V₀ V L hV hS hc).2 Q hQ hQi
  have hCv' : Subgroup.centralizer ({v'} : Set G) ≤ D.M := by
    have h := (h41'.2 (mkTil V₀ V hV (IntMod.mk hV ⟨v', hv'V⟩)) hw').2
      (IntMod.mk hV ⟨v', hv'V⟩) rfl
    change Subgroup.centralizer ({v'} : Set G) ≤ D.M at h
    exact h
  have hvN : u.val ∈ normalizer (conjSubgroup V g : Set G) := by
    have hMgN : conjSubgroup D.M g ≤ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer V g]
      exact Subgroup.map_mono hS.setting.hyp151.hyp125.pairFacts.le_normalizer
    exact hMgN huM
  have hv'Vg : v' ∈ conjSubgroup V g := by
    have hmem : u.val * a⁻¹ * u.val⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hvN a⁻¹).1 ((conjSubgroup V g).inv_mem haVg)
    have heq : v' = a * (u.val * a⁻¹ * u.val⁻¹) := by
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

theorem s16c1G44_rank {D : Data G} (h22 : R1622 D) (h42 : R16_42 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {g : G}
    (hidx : E3.mQuot (conjSubgroup V g) D.M ≤ 1)
    (hcard : Nat.card (barSub V₀ V hV (conjSubgroup V g ⊓ D.M)) ≤ 4) :
    V ≤ conjSubgroup D.M g := by
  let B : Subgroup G := conjSubgroup V g ⊓ D.M
  have hBM : B ≤ D.M := inf_le_right
  have hBg : B ≤ conjSubgroup V g := inf_le_left
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hBstab : B ≤ stabTil V₀ V := hBM.trans hMstab
  let X₀ : Subgroup G := B ⊓ preBarSub D.M V₀ V hV ⊥
  have hX₀B : X₀ ≤ B := inf_le_left
  have hX₀M : X₀ ≤ D.M := hX₀B.trans hBM
  have hX₀g : X₀ ≤ conjSubgroup V g := hX₀B.trans hBg
  have hX₀gam : X₀ ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) X₀) D.M :=
    ⟨hX₀M, g, hX₀g, rfl⟩
  have hcardpos : Nat.card (barSub V₀ V hV B) ≠ 0 := Nat.card_pos.ne'
  have hcard' : Nat.card (barSub V₀ V hV B) ≤ 4 := hcard
  have hk_le : E3.mQuot (conjSubgroup V g) X₀ ≤ 3 := by
    have hadd := E3.mQuot_add hX₀B hBg
    have h1 : E3.mQuot (conjSubgroup V g) B ≤ 1 := by
      rw [show B = conjSubgroup V g ⊓ D.M from rfl, s16c1G44_mQuot_inf_left]
      exact hidx
    have h2 : E3.mQuot B X₀ ≤ 2 := by
      have hrel := s16c1G44_relIndex_inf_preBarSub_eq_card_barSub (V₀ := V₀) (V := V)
        (hV := hV) hBM hBstab
      have hpow : ¬ (2 ^ 3 ∣ Nat.card (barSub V₀ V hV B)) := by
        intro hdvd
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hcardpos) hdvd
        omega
      have h3 : ¬ 3 ≤ padicValNat 2 (Nat.card (barSub V₀ V hV B)) :=
        fun hle => hpow ((Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 3)
          (n := Nat.card (barSub V₀ V hV B)) (by norm_num) hcardpos).2 hle)
      rw [E3.mQuot, hrel]
      omega
    omega
  have hr : ((E3.mQuot (conjSubgroup V g) X₀ + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    have h42' := h42 V₀ V L hV hS hc
    have hle : E3.mQuot (conjSubgroup V g) X₀ + mSub V₀ ≤ mSub V₀ + 3 := by omega
    have hlt' : ((mSub V₀ + 3 : ℕ) : ℕ∞) < ((mSub V₀ + 4 : ℕ) : ℕ∞) :=
      WithTop.coe_lt_coe.mpr (by omega)
    exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) (hlt'.trans_le h42'.1)
  have h23 := sixteen_twentyThree_one D h22 hS.setting.hyp16 hX₀gam hX₀g hr
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

theorem s16c1G44_oneFirst {D : Data G} (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D)
    (hkitB : OmegaKitB) (hkitD : OmegaKitD) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {g : G}
    (hg : InCalO 1 D.M V₀ V g) : OneFirst D.M V₀ V g := by
  have hpf := hS.setting.hyp151.hyp125.pairFacts
  have hgM : g ∉ D.M := by
    intro hgM
    refine hg.1.1 ?_
    rw [conjSubgroup_eq_iff_mem_normalizer.2 (hpf.le_normalizer hgM)]
    exact hpf.le_M
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hnVMg : ¬ V ≤ conjSubgroup D.M g := hg.2.1
  have hidx1 : E3.mQuot V (conjSubgroup D.M g) ≤ 1 := hg.1.2.1
  have hidx2 : E3.mQuot (conjSubgroup V g) D.M ≤ 1 := hg.2.2.1
  intro b hb
  obtain ⟨hb1, hbC⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hbVg, hbM⟩ := Subgroup.mem_inf.1 hb1
  have hbstab : b ∈ stabTil V₀ V := hMstab hbM
  refine (mem_cTilde_iff hV hpf.le_normalizer).2 ⟨hbM, hbstab, ?_⟩
  by_contra hne
  obtain ⟨Q, hQ, hQi⟩ := (h41 V₀ V L hV hS hc).1
  have hD := hkitD (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  let U : Subgroup G := V ⊓ conjSubgroup D.M g
  let B : Subgroup G := conjSubgroup V g ⊓ D.M
  have hBg : B ≤ conjSubgroup V g := inf_le_left
  have hBM : B ≤ D.M := inf_le_right
  have hBstab : B ≤ stabTil V₀ V := hBM.trans hMstab
  have hEnorm : barSub V₀ V hV B ≤
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hBM).trans (s16c1_Mbar_le_normalizer hkitB hS hc)
  have hEel : IsElemAbelian2 (barSub V₀ V hV B) := s16c1G44_isElemAbelian2_barSub hBg hBstab
  have htE : actTil V₀ V hV ⟨b, hbstab⟩ ∈ barSub V₀ V hV B :=
    actTil_mem_barSub V₀ V hV (Subgroup.mem_inf.2 ⟨hbVg, hbM⟩) hbstab
  have htfix : ∀ p ∈ imgTil V₀ V hV U, actTil V₀ V hV ⟨b, hbstab⟩ p = p :=
    s16c1G44_fix_img hbstab hbC
  have hPidx : (imgTil V₀ V hV U).index = 2 := by
    have hdvd : (imgTil V₀ V hV U).index ∣ 2 := s16c1G44_index_img hidx1
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exfalso
      apply hne
      have htop : imgTil V₀ V hV U = ⊤ := Subgroup.index_eq_one.1 h1
      refine MulEquiv.ext fun p => ?_
      rw [MulAut.one_apply]
      exact htfix p (htop ▸ Subgroup.mem_top p)
    · exact h2
  have hgood : ∀ e ∈ barSub V₀ V hV B, ∀ u ∈ imgTil V₀ V hV U, Q (e u * u⁻¹) = 0 := by
    intro e he u hu
    obtain ⟨a, haB, rfl⟩ := (mem_barSub V₀ V hV B e).1 he
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U u).1 hu
    exact s16c1G44_good h22 h41 hS hc hgM hQ hQi a.2 (Subgroup.mem_inf.1 haB).1
      (Subgroup.mem_inf.1 hxU).2
  have hcard : Nat.card (barSub V₀ V hV B) ≤ 4 :=
    hD Q hQ hQi _ hEnorm hEel _ hPidx _ htE hne htfix hgood
  exact hnVMg (s16c1G44_rank h22 h42 hS hc hidx2 hcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
