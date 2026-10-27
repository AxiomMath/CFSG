module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyVtil
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34NaturalModuleHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Final
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem n_eq_two_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V) : n = 2 := by
  have h1 := (h35.1 L n c.ctx).2
  have h2 := (h35.2 L n c.ctx c.v0).2.2.1
  omega

theorem cNatModSU3_two_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    CNatModSU3 (Vtil V₀ V c.ctx.hyp125.isElemAbelian)
      (barSub V₀ V c.ctx.hyp125.isElemAbelian L) 2 := by
  have hn : n = 2 := n_eq_two_of_ctx17_40 c h35
  subst hn
  exact cNatModSU3_of_ctx17_40 c h35 hx h61 h127 h1214

noncomputable def su3Vec {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (S : CNatModStructSU3 W X 2) (w : W) : Fin 3 → S.K :=
  Multiplicative.toAdd (S.e ⟨w, Subgroup.mem_top w⟩)

theorem ofAdd_su3Vec {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (S : CNatModStructSU3 W X 2) (w : W) :
    Multiplicative.ofAdd (su3Vec S w) = S.e ⟨w, Subgroup.mem_top w⟩ := by
  simp [su3Vec]

theorem su3Vec_eq_zero_iff {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    (S : CNatModStructSU3 W X 2) (w : W) : su3Vec S w = 0 ↔ w = 1 := by
  constructor
  · intro h
    have h1 : S.e ⟨w, Subgroup.mem_top w⟩ = 1 := by
      rw [← ofAdd_su3Vec S w, h, ofAdd_zero]
    have h2 : S.e ⟨w, Subgroup.mem_top w⟩ = S.e (1 : ↥(⊤ : Subgroup W)) := by
      rw [h1, map_one]
    exact Subtype.ext_iff.mp (S.e.injective h2)
  · rintro rfl
    simp [su3Vec]

theorem exists_orderOf_five_barSub_of_cnonsingular {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (S : CNatModStructSU3 W X 2)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_U34NonsingularStab)
    {w : W} (hw : w ≠ 1) (hns : CNonsingular W S w) :
    ∃ y ∈ X, orderOf y = 5 ∧ y w = w := by
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  letI : Fintype S.K := Fintype.ofFinite S.K
  haveI : CharP S.K 2 := charP_cardK S
  have hK16 : Nat.card S.K = 16 := by
    have h := S.cardK
    norm_num at h ⊢
    exact h
  have hw0 : su3Vec S w ≠ 0 := by
    intro h
    exact hw ((su3Vec_eq_zero_iff S w).mp h)
  have hwq : herm 2 (su3Vec S w) (su3Vec S w) ≠ 0 := by
    simpa [CNonsingular, su3Vec, herm, conjV, dotProduct, bar_apply] using hns
  obtain ⟨x, hx5, hxv⟩ := hS S.K hK16 (su3Vec S w) hw0 hwq
  obtain ⟨y, hyX, hyact⟩ := S.surj x x.property
  have hyfix : y w = w := by
    have h1 := hyact w (Subgroup.mem_top w) (Subgroup.mem_top (y w))
    rw [show Multiplicative.toAdd (S.e ⟨w, Subgroup.mem_top w⟩) = su3Vec S w from rfl,
      hxv] at h1
    have h2 : (⟨y w, Subgroup.mem_top (y w)⟩ : ↥(⊤ : Subgroup W)) =
        ⟨w, Subgroup.mem_top w⟩ :=
      S.e.injective (by rw [h1, ofAdd_su3Vec])
    exact congrArg Subtype.val h2
  have hy5 : orderOf y = 5 := by
    let e := su3NatEquiv S
    have hy' : MulAut.congr e y = matAut (x : GL (Fin 3) S.K) := by
      apply MulEquiv.ext
      intro z
      obtain ⟨w0, rfl⟩ := e.surjective z
      have h1 := hyact w0 (Subgroup.mem_top w0) (Subgroup.mem_top (y w0))
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [su3NatEquiv_apply S (y w0), h1, su3NatEquiv_apply S w0]
      rfl
    have hord' : orderOf (MulAut.congr e y) = 5 := by
      rw [hy', ← matHom_apply]
      rw [orderOf_injective (matHom : GL (Fin 3) S.K →* MulAut (StdMod (Fin 3) S.K))
        matHom_injective x]
      rw [Subgroup.orderOf_coe]
      exact hx5
    have hord : orderOf (MulAut.congr e y) = orderOf y :=
      orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective y
    omega
  exact ⟨y, hyX, hy5, hyfix⟩

theorem map_le_natNorm_of_cNatModSU3 {W : Type} [CommGroup W] [Finite W]
    {X Y : Subgroup (MulAut W)} (S : CNatModStructSU3 W X 2)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) :
    Y.map (MulAut.congr (su3NatEquiv S)).toMonoidHom ≤
      natNorm (StatedSU 3 4 S.K) := by
  let e := su3NatEquiv S
  have hX' : X.map (MulAut.congr e).toMonoidHom = natImage (StatedSU 3 4 S.K) :=
    natImageX_eq S
  have hY' : Y.map (MulAut.congr e).toMonoidHom ≤
      (Subgroup.normalizer (X : Set (MulAut W))).map (MulAut.congr e).toMonoidHom := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hYN hx, rfl⟩
  rwa [Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.congr e).toMonoidHom) X
    (MulAut.congr e).bijective, hX'] at hY'

private theorem two_le_pRank_of_two_five_zpowers_of_isPGroup {H : Subgroup G} {x y : G}
    (hH : IsPGroup 5 H) (hx : x ∈ H) (hy : y ∈ H)
    (hx5 : orderOf x = 5) (hy5 : orderOf y = 5)
    (hne : Subgroup.zpowers x ≠ Subgroup.zpowers y) :
    2 ≤ CFSG.Open.pRank 5 H := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra h
  exact hne (CFSG.LocalAnalysis.RankThreeUC.eq_of_card_eq_prime_of_pRank_le_one hH (by omega)
    (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy)
    (by rw [Nat.card_zpowers, hx5]) (by rw [Nat.card_zpowers, hy5]))

theorem inf_cTilde_le_pCoreOf_of_center_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hL : L ∈ calC D.M)
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hZ : Subgroup.center (Bar2 L) = ⊥) :
    L ⊓ F11.CTilde D.M V₀ V ≤ pCoreOf 2 L := by
  classical
  have hV := h.isElemAbelian
  have hLsub : L ≤ D.M := hL.1.le
  have hpair := h.pairFacts
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) := hpair.le_normalizer
  have hMnorm₀ : D.M ≤ Subgroup.normalizer (V₀ : Set G) := hpair.le_normalizer₀
  set K : Subgroup G := L ⊓ F11.CTilde D.M V₀ V with hKdef
  have hKL : K ≤ L := inf_le_left
  have hO2L : pCoreOf 2 L ≤ L := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hO2C : pCoreOf 2 L ≤ F11.CTilde D.M V₀ V := by
    refine (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hMnorm hMnorm₀
      (hO2L.trans hLsub)).1 ?_
    exact TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  have hO2K : pCoreOf 2 L ≤ K := le_inf hO2L hO2C
  have hCtN : D.M ≤ Subgroup.normalizer (F11.CTilde D.M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M V₀ V)).mp
      (CFSG.LocalAnalysis.WeakClosure81.cTilde_subgroupOf_normal hV hMnorm hMnorm₀)
  have hKnormal : (K.subgroupOf L).Normal := by
    have hLnorm : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
    have hCLnorm : L ≤ Subgroup.normalizer (F11.CTilde D.M V₀ V : Set G) :=
      hLsub.trans hCtN
    have hKnorm : L ≤ Subgroup.normalizer (K : Set G) :=
      (le_inf hLnorm hCLnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hKnorm
  let q : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Kq : Subgroup (Bar2 L) := (K.subgroupOf L).map q
  have hKq : Kq.Normal :=
    hKnormal.map q (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (Q := Bar2 L)
      (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hL.2.2) hKq
    with htop | hcen
  ·
    have hsup : K.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
      have h1 := Subgroup.comap_map_eq q (K.subgroupOf L)
      change Subgroup.comap q Kq = K.subgroupOf L ⊔ q.ker at h1
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hmap := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype,
      show (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L from rfl] at hmap
    have hmap' : K ⊔ pCoreOf 2 L = L := by
      rwa [inf_eq_left.mpr hKL] at hmap
    have hLK : L ≤ K := by
      rw [← hmap', sup_eq_left.mpr hO2K]
    have hLC : L ≤ F11.CTilde D.M V₀ V := hLK.trans inf_le_right
    exact absurd ((CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hMnorm hMnorm₀
      hLsub).2 hLC) hL1
  ·
    have hKqbot : Kq = ⊥ := by
      have h1 : Kq ≤ (⊥ : Subgroup (Bar2 L)) := by
        rwa [hZ] at hcen
      exact le_bot_iff.mp h1
    have hKle : K.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
      have h1 := hKqbot
      rw [show Kq = (K.subgroupOf L).map q from rfl, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk'] at h1
      exact h1
    intro x hx
    have hxL : x ∈ L := hx.1
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ K.subgroupOf L := by
      rwa [Subgroup.mem_subgroupOf]
    have hxpcore : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hKle hxsub
    exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hxpcore, rfl⟩

theorem centralizer_le_of_cnonsingular
    {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V)
    (h40 : R17_40At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_U34NonsingularStab)
    (S : CNatModStructSU3 (Vtil V₀ V c.ctx.hyp125.isElemAbelian)
      (barSub V₀ V c.ctx.hyp125.isElemAbelian L) 2)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hns : CNonsingular (Vtil V₀ V c.ctx.hyp125.isElemAbelian) S
      (mkTil V₀ V c.ctx.hyp125.isElemAbelian
        (CFSG.Quasithin.IntMod.mk c.ctx.hyp125.isElemAbelian ⟨v, hv⟩))) :
    Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  classical
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  let hV := c.ctx.hyp125.isElemAbelian
  have hpair := c.ctx.hyp125.pairFacts
  have hLsub : L ≤ D.M := c.ctx.mem_calC.1.le
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) := hpair.le_normalizer
  have hMnorm₀ : D.M ≤ Subgroup.normalizer (⊥ : Subgroup G) := hpair.le_normalizer₀
  let vtil : Vtil ⊥ V hV := mkTil ⊥ V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)
  have hvtil1 : vtil ≠ 1 := by
    intro h
    have hmem : (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩).val *
        (1 : CFSG.Quasithin.IntMod V hV).val⁻¹ ∈ (⊥ : Subgroup G) :=
      (mkTil_eq_iff ⊥ V hV _ _).mp h
    rw [Subgroup.mem_bot] at hmem
    have hone : CFSG.Quasithin.IntMod.val (1 : CFSG.Quasithin.IntMod V hV) = 1 :=
      CFSG.Quasithin.IntMod.val_one
    rw [hone, inv_one, mul_one] at hmem
    exact hv1 hmem
  obtain ⟨y, hyX, hy5, hyfix⟩ :=
    exists_orderOf_five_barSub_of_cnonsingular (W := Vtil ⊥ V hV)
      (X := barSub ⊥ V hV L) S hS hvtil1 hns
  obtain ⟨g, hgL, hgact⟩ := (mem_barSub ⊥ V hV L y).mp hyX
  have hgfix_til : actTil ⊥ V hV g vtil = vtil := by
    rw [hgact]; exact hyfix
  have hgfix : (g : G) * v * (g : G)⁻¹ = v := by
    have h1 : mkTil ⊥ V hV (actStab ⊥ V hV g
        (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)) =
        mkTil ⊥ V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩) := by
      rw [← actTil_mk ⊥ V hV g (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)]
      exact hgfix_til
    have h2 : (actStab ⊥ V hV g (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)).val *
        v⁻¹ ∈ (⊥ : Subgroup G) := (mkTil_eq_iff ⊥ V hV _ _).mp h1
    rw [Subgroup.mem_bot] at h2
    rw [actStab_apply_val] at h2
    exact mul_inv_eq_one.mp h2
  have hφg : orderOf (actTil ⊥ V hV g) = 5 := by rw [hgact]; exact hy5
  have hyne : y ≠ 1 := by
    intro h
    rw [h] at hy5
    simp at hy5
  have hg5act : actTil ⊥ V hV (g ^ 5) = 1 := by
    rw [map_pow, hgact]
    simpa [hy5] using pow_orderOf_eq_one y
  have hL1 : barSub ⊥ V hV L ≠ ⊥ := barSub_ne_bot_of_ctx17_40 c h35
  have hn : n = 2 := n_eq_two_of_ctx17_40 c h35
  have hZ : Subgroup.center (Bar2 L) = ⊥ := by
    have hshape : IsU3 (Bar2 L ⧸ Subgroup.center (Bar2 L)) 2 := by
      simpa [hn] using c.ctx.shape.2
    exact uc22s13xc_center_eq_bot_of_isU3_quot c.ctx.mem_calC.2.2 (by norm_num) hshape
  have hKleO2 : L ⊓ F11.CTilde D.M ⊥ V ≤ pCoreOf 2 L :=
    inf_cTilde_le_pCoreOf_of_center_eq_bot c.ctx.hyp125 c.ctx.mem_calC hL1 hZ
  have hpc : IsPGroup 2 (pCoreOf 2 L) := by
    rw [CFSG.Open.pCoreOf]
    exact CFSG.pCore_isPGroup.map L.subtype
  have h5notK : ¬ 5 ∣ Nat.card ↥(L ⊓ F11.CTilde D.M ⊥ V) := by
    intro h5
    have h5O2 : 5 ∣ Nat.card ↥(pCoreOf 2 L) :=
      h5.trans (Subgroup.card_dvd_of_le hKleO2)
    obtain ⟨t, ht⟩ := hpc.exists_card_eq
    rw [ht] at h5O2
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5O2
    norm_num at h52
  have hg5K : (g : G) ^ 5 ∈ L ⊓ F11.CTilde D.M ⊥ V := by
    refine Subgroup.mem_inf.mpr ⟨L.pow_mem hgL 5, ?_⟩
    have hst : (g : G) ^ 5 ∈ stabTil ⊥ V :=
      Subgroup.mem_inf.mpr
        ⟨hMnorm (hLsub (L.pow_mem hgL 5)), hMnorm₀ (hLsub (L.pow_mem hgL 5))⟩
    refine (mem_cTilde_iff hV hMnorm).mpr ⟨hLsub (L.pow_mem hgL 5), ⟨hst, ?_⟩⟩
    have h2 : (⟨(g : G) ^ 5, hst⟩ : ↥(stabTil ⊥ V)) = g ^ 5 := Subtype.ext rfl
    rw [h2]
    exact hg5act
  let k0 : ↥(L ⊓ F11.CTilde D.M ⊥ V) := ⟨(g : G) ^ 5, hg5K⟩
  let m := orderOf k0
  have hmcop : Nat.Coprime m 5 := by
    have hm_eq : m = orderOf ((g : G) ^ 5) := by
      change orderOf k0 = orderOf ((g : G) ^ 5)
      rw [← Subgroup.orderOf_coe k0]
    have hdvd : m ∣ Nat.card ↥(L ⊓ F11.CTilde D.M ⊥ V) := by
      rw [hm_eq]
      exact Subgroup.orderOf_dvd_natCard (L ⊓ F11.CTilde D.M ⊥ V) hg5K
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (fun h5 => h5notK (h5.trans hdvd))).symm
  have hkill : ((g : ↥(stabTil ⊥ V)) ^ 5) ^ m = 1 := by
    apply Subtype.ext
    change ((g : G) ^ 5) ^ m = 1
    have hord : orderOf ((k0 : G)) = m := by
      rw [Subgroup.orderOf_coe]
    rw [show (g : G) ^ 5 = (k0 : G) from rfl, ← hord]
    exact pow_orderOf_eq_one _
  obtain ⟨k, hkmap, hkord⟩ :=
    exists_pow_orderOf_eq_of_coprime_map (actTil ⊥ V hV) (r := 5) (m := m)
      Nat.prime_five hφg hkill hmcop
  let gz : ↥(stabTil ⊥ V) := g ^ k
  let z : G := (gz : ↥(stabTil ⊥ V))
  have hzL : z ∈ L := by
    change (gz : G) ∈ L
    rw [Subgroup.coe_pow]
    exact L.pow_mem hgL k
  have hzord : orderOf z = 5 := by
    change orderOf (gz : G) = 5
    rw [Subgroup.orderOf_coe]
    exact hkord
  have hzfix : z * v * z⁻¹ = v := by
    have h1 : actTil ⊥ V hV gz vtil = vtil := by
      rw [hkmap]
      exact hgfix_til
    have h2 : mkTil ⊥ V hV (actStab ⊥ V hV gz
        (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)) =
        mkTil ⊥ V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩) := by
      rw [← actTil_mk ⊥ V hV gz (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)]
      exact h1
    have h3 : (actStab ⊥ V hV gz (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)).val *
        v⁻¹ ∈ (⊥ : Subgroup G) := (mkTil_eq_iff ⊥ V hV _ _).mp h2
    rw [Subgroup.mem_bot] at h3
    rw [actStab_apply_val] at h3
    exact mul_inv_eq_one.mp h3
  have hzM : z ∈ D.M := hLsub hzL
  have hzC : z ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * v = (z * v * z⁻¹) * z := by group
      _ = v * z := by rw [hzfix]
  have hzH : z ∈ D.M ⊓ Subgroup.centralizer ({v} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hzM, hzC⟩
  have hpi : 5 ∈ piSet (F11.CTilde D.M ⊥ V) := by
    rw [UC22.cTilde_bot D.M V]
    exact seventeen_fortyone_one D ⊥ V h40 hSg Inputs1719.kU34Data_holds L n c
  set H : Subgroup G := D.M ⊓ Subgroup.centralizer ({v} : Set G) with hHdef
  have hzH' : z ∈ H := hzH
  let zH : ↥H := ⟨z, hzH'⟩
  have hzHord : orderOf zH = 5 := by
    have h : zH = ⟨z, hzH'⟩ := rfl
    rw [h]
    exact (Subgroup.orderOf_coe (⟨z, hzH'⟩ : ↥H)).symm.trans hzord
  have hzP : IsPGroup 5 (Subgroup.zpowers zH) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzHord]; norm_num)
  obtain ⟨Q, hQle⟩ := hzP.exists_le_sylow (p := 5) (G := ↥H)
  let S : Subgroup G := (Q : Subgroup ↥H).map H.subtype
  have hSH : S ≤ H := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    exact w.property
  have hzS : z ∈ S := by
    have hzQ : zH ∈ (Q : Subgroup ↥H) := hQle (Subgroup.mem_zpowers zH)
    exact Subgroup.mem_map.mpr ⟨zH, hzQ, rfl⟩
  have hSyl : CFSG.Quasithin.IsSylowIn 5 S H := by
    refine CFSG.Quasithin.isSylowIn_of_card_eq hSH ?_
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Q.card_eq_multiplicity
  have hCtilde_le_H : F11.CTilde D.M ⊥ V ≤ H := by
    refine le_inf (CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M ⊥ V) ?_
    intro a ha
    have hst : a ∈ stabTil ⊥ V :=
      le_stabTil hMnorm hMnorm₀ (CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M ⊥ V ha)
    have hact : actTil ⊥ V hV ⟨a, hst⟩ = 1 := by
      obtain ⟨-, h, h1⟩ := (mem_cTilde_iff hV hMnorm).mp ha
      simpa [show (⟨a, hst⟩ : ↥(stabTil ⊥ V)) = ⟨a, h⟩ from Subtype.ext rfl] using h1
    have hcent : a ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := (actTil_eq_one_iff ⊥ V hV ⟨a, hst⟩).mp hact w hw
      rw [Subgroup.mem_bot] at h2
      have h3 : a * w * a⁻¹ = w := mul_inv_eq_one.mp h2
      calc w * a = (a * w * a⁻¹) * a := by rw [h3]
        _ = a * w := by group
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)) hcent
  have hNnorm : ((F11.CTilde D.M ⊥ V).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCtilde_le_H]
    have hDN : D.M ≤ Subgroup.normalizer (F11.CTilde D.M ⊥ V : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M ⊥ V)).mp
        (CFSG.LocalAnalysis.WeakClosure81.cTilde_subgroupOf_normal hV hMnorm hMnorm₀)
    exact (inf_le_left : H ≤ D.M).trans hDN
  have hSylN : CFSG.Quasithin.IsSylowIn 5 (S ⊓ F11.CTilde D.M ⊥ V)
      (F11.CTilde D.M ⊥ V) := hSyl.inf_normal hCtilde_le_H hNnorm
  have hfac : 0 < (Nat.card ↥(F11.CTilde D.M ⊥ V)).factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_five (Nat.card_pos.ne') hpi.2
  have hcardS5 : 5 ∣ Nat.card ↥(S ⊓ F11.CTilde D.M ⊥ V) := by
    have hge : 5 ≤ Nat.card ↥(S ⊓ F11.CTilde D.M ⊥ V) := by
      rw [hSylN.card_eq]
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ (Nat.card ↥(F11.CTilde D.M ⊥ V)).factorization 5 :=
            Nat.pow_le_pow_right (by norm_num) hfac
    obtain ⟨t, ht⟩ := hSylN.isPGroup.exists_card_eq
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h
      · rw [h0, pow_zero] at ht
        omega
      · exact h
    have h5t : 5 ∣ 5 ^ t := dvd_pow_self 5 (by omega : t ≠ 0)
    rwa [ht]
  obtain ⟨z0, hz0ord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(S ⊓ F11.CTilde D.M ⊥ V)) 5 hcardS5
  have hz0ordG : orderOf (z0 : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hz0ord
  have hz0S : (z0 : G) ∈ S := (Subgroup.mem_inf.mp z0.property).1
  have hz0C : (z0 : G) ∈ F11.CTilde D.M ⊥ V := (Subgroup.mem_inf.mp z0.property).2
  have hz0le : Subgroup.zpowers (z0 : G) ≤ F11.CTilde D.M ⊥ V :=
    Subgroup.zpowers_le.mpr hz0C
  have hznotC : z ∉ F11.CTilde D.M ⊥ V := by
    intro hzC
    have hact : actTil ⊥ V hV gz = 1 := by
      obtain ⟨-, h, h1⟩ := (mem_cTilde_iff hV hMnorm).mp hzC
      have h2 : actTil ⊥ V hV (⟨z, h⟩ : ↥(stabTil ⊥ V)) = 1 := h1
      have h3 : (⟨z, h⟩ : ↥(stabTil ⊥ V)) = gz := Subtype.ext rfl
      rwa [h3] at h2
    have h4 : actTil ⊥ V hV gz = y := hkmap.trans hgact
    rw [h4] at hact
    exact hyne hact
  have hne : Subgroup.zpowers (z0 : G) ≠ Subgroup.zpowers z := by
    intro heq
    apply hznotC
    have hzmem : z ∈ Subgroup.zpowers (z0 : G) := by
      rw [heq]
      exact Subgroup.mem_zpowers z
    exact hz0le hzmem
  have hrankS : 2 ≤ CFSG.Open.pRank 5 S :=
    two_le_pRank_of_two_five_zpowers_of_isPGroup hSyl.isPGroup hz0S hzS
      hz0ordG hzord hne
  have hrankH : 2 ≤ CFSG.Open.pRank 5 H :=
    hrankS.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hSH)
  have hsig : D.sig = {5} := (h40 L n c).2.2
  have hpsig : 5 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 5
  exact centralizer_le_of_involution_of_two_le_pRank D h61 Nat.prime_five hpsig
    (hV.2 v hv) hv1 hrankH

theorem exists_cnonsingular_of_sixteen_lt_card {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} (S : CNatModStructSU3 W X 2)
    (hH : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_U34Hermitian)
    {U : Subgroup W} (hU : 16 < Nat.card U) :
    ∃ u ∈ U, u ≠ 1 ∧ CNonsingular W S u := by
  classical
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  letI : Fintype S.K := Fintype.ofFinite S.K
  haveI : CharP S.K 2 := charP_cardK S
  have hK16 : Nat.card S.K = 16 := by
    have h := S.cardK
    norm_num at h ⊢
    exact h
  let f : Additive W →+ (Fin 3 → S.K) :=
    { toFun := fun w => su3Vec S (Additive.toMul w)
      map_zero' := by
        change Multiplicative.toAdd
          (S.e (⟨Additive.toMul 0, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W))) = 0
        rw [show (⟨Additive.toMul (0 : Additive W), Subgroup.mem_top _⟩ :
            ↥(⊤ : Subgroup W)) = 1 from rfl, S.e.map_one]
        rfl
      map_add' := by
        intro a b
        change Multiplicative.toAdd
          (S.e (⟨Additive.toMul (a + b), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W))) =
          Multiplicative.toAdd
            (S.e (⟨Additive.toMul a, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W))) +
          Multiplicative.toAdd
            (S.e (⟨Additive.toMul b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)))
        rw [show (⟨Additive.toMul (a + b), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
            (⟨Additive.toMul a, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) *
              ⟨Additive.toMul b, Subgroup.mem_top _⟩ from rfl, S.e.map_mul]
        rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : S.e (⟨Additive.toMul a, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        S.e (⟨Additive.toMul b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) :=
      Multiplicative.toAdd.injective hab
    have h2 : Additive.toMul a = Additive.toMul b :=
      Subtype.ext_iff.mp (S.e.injective h1)
    exact Additive.toMul.injective h2
  let A : AddSubgroup (Fin 3 → S.K) :=
    AddSubgroup.map f (Subgroup.toAddSubgroup U)
  have hAcard : Nat.card A = Nat.card U := by
    rw [AddSubgroup.card_map_of_injective hf]
    exact Nat.card_congr
      { toFun := fun x => (⟨x.1, x.2⟩ : ↥U)
        invFun := fun x => (⟨x.1, x.2⟩ : ↥(Subgroup.toAddSubgroup U))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hA : ¬ ∀ a ∈ A, herm 2 a a = 0 := by
    intro hall
    have h := hH S.K hK16 A hall
    omega
  push Not at hA
  obtain ⟨a, haA, ha⟩ := hA
  obtain ⟨w, hwU, rfl⟩ := AddSubgroup.mem_map.mp haA
  refine ⟨Additive.toMul w, hwU, ?_, ?_⟩
  · intro h
    apply ha
    have hw0 : w = 0 := Additive.toMul.injective (by simpa using h)
    rw [hw0]
    change herm 2 (Multiplicative.toAdd (S.e (1 : ↥(⊤ : Subgroup W))))
      (Multiplicative.toAdd (S.e (1 : ↥(⊤ : Subgroup W)))) = 0
    rw [S.e.map_one]
    simp [herm, conjV, dotProduct]
  · simpa [CNonsingular, herm, conjV, dotProduct, bar_apply, su3Vec, f] using ha

theorem card_eq_two_pow_twelve_of_natModSU3 {W : Type} [Group W]
    {X : Subgroup (MulAut W)} (S : CNatModStructSU3 W X 2) :
    Nat.card W = 2 ^ 12 := by
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  letI : Fintype S.K := Fintype.ofFinite S.K
  have hK : Nat.card S.K = 16 := by
    have h := S.cardK
    norm_num at h ⊢
    exact h
  calc Nat.card W
      = Nat.card ↥(⊤ : Subgroup W) := (Subgroup.card_top).symm
    _ = Nat.card (Multiplicative (Fin 3 → S.K)) := Nat.card_congr S.e.toEquiv
    _ = Nat.card (Fin 3 → S.K) := rfl
    _ = Nat.card S.K ^ Nat.card (Fin 3) := Nat.card_fun
    _ = 2 ^ 12 := by rw [hK, Nat.card_fin]; norm_num

theorem seventeen_fortyone_three
    (D : Data G) (V₀ V : Subgroup G)
    (h40 : R17_40At D V₀ V) (h35 : R17_35At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    R17_41_3At D V₀ V := by
  have hH : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_U34Hermitian :=
    Inputs1719.k_U34Hermitian_holds
  have hS : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_U34NonsingularStab :=
    Inputs1719.k_U34NonsingularStab_holds
  intro L n c
  by_contra hlt
  rw [not_le] at hlt
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M := by
    by_contra h
    push Not at h
    rw [rMV_eq_top_of_forall D h] at hlt
    exact absurd hlt (by simp)
  obtain ⟨U, hUV, hCU, hrU⟩ := exists_mQuot_eq_rMV D hne
  obtain ⟨S⟩ := cNatModSU3_two_of_ctx17_40 c h35 hx h61 h127 h1214
  have hcardVtil : Nat.card (Vtil ⊥ V hV) = 2 ^ 12 :=
    card_eq_two_pow_twelve_of_natModSU3 S
  have hcardV : Nat.card V = 2 ^ 12 := by
    rw [card_Vtil_eq ⊥ V hV bot_le, Subgroup.card_bot, one_mul, hcardVtil]
  have hm8 : E3.mQuot V U < 8 := by
    have h : (E3.mQuot V U : ℕ∞) < (8 : ℕ∞) := by rw [hrU]; exact hlt
    exact WithTop.coe_lt_coe.mp h
  have hmul : 2 ^ E3.mQuot V U * Nat.card U = 2 ^ 12 := by
    rw [← E3.card_eq_two_pow_mul hV.isPGroup hUV, hcardV]
  have hmle : E3.mQuot V U ≤ 7 := by omega
  have hUeq : Nat.card U = 2 ^ (12 - E3.mQuot V U) := by
    have hcancel : Nat.card U * 2 ^ E3.mQuot V U =
        2 ^ (12 - E3.mQuot V U) * 2 ^ E3.mQuot V U := by
      calc Nat.card U * 2 ^ E3.mQuot V U = 2 ^ E3.mQuot V U * Nat.card U :=
            Nat.mul_comm _ _
        _ = 2 ^ 12 := hmul
        _ = 2 ^ ((12 - E3.mQuot V U) + E3.mQuot V U) := by
            rw [Nat.sub_add_cancel (by omega)]
        _ = 2 ^ (12 - E3.mQuot V U) * 2 ^ E3.mQuot V U :=
            pow_add 2 (12 - E3.mQuot V U) (E3.mQuot V U)
    exact Nat.mul_right_cancel (by positivity) hcancel
  have hU16 : 16 < Nat.card U := by
    rw [hUeq]
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ < 2 ^ (12 - E3.mQuot V U) :=
          Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  have hUbar : Nat.card ↥(imgTil ⊥ V hV U) = Nat.card U := s16c167_card_imgTil_bot hV hUV
  have h16 : 16 < Nat.card (imgTil ⊥ V hV U) := by rw [hUbar]; exact hU16
  obtain ⟨u, huU, hu1, huns⟩ :=
    exists_cnonsingular_of_sixteen_lt_card (W := Vtil ⊥ V hV)
      (X := barSub ⊥ V hV L) S hH h16
  obtain ⟨x, hxU, hxu⟩ := (mem_imgTil ⊥ V hV U u).1 huU
  let v : G := x.val
  have hv : v ∈ V := x.val_mem
  have hvU : v ∈ U := hxU
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    rw [← hxu]
    have hxval : (x : IntMod V hV).val = 1 := by
      change v = 1
      exact h
    have hx1 : x = 1 := CFSG.Quasithin.IntMod.val_injective (by simpa using hxval)
    rw [hx1, map_one]
  have hnsv : CNonsingular (Vtil ⊥ V hV) S
      (mkTil ⊥ V hV (CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩)) := by
    have hxeq : CFSG.Quasithin.IntMod.mk hV ⟨v, hv⟩ = x := rfl
    rw [hxeq, hxu]
    exact huns
  have hcent : Subgroup.centralizer (U : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvU)).trans
      (centralizer_le_of_cnonsingular c h35 h40 hSg h61 hS S hv hv1 hnsv)
  exact hCU hcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
