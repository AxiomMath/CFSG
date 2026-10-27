module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Quasithin.Background.D2Z2
public import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCycAb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import CFSG.GroupTheory.IrreducibleAbelianAction
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpArith

public section


namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem seventeen_two_four (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h2 : R17_2_2At D V₀ V hV) (h3 : R17_2_3At D V₀ V hV)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h115 : F11.R115 D) : R17_2_4At D V₀ V := by
  intro p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hDcard, hV0, hk, hm4⟩ :=
    h2 p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  subst hV0
  obtain ⟨hirr, hDbar⟩ := h3 p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  have hVe : IsElemAbelian 2 V := hV.isElemAbelian
  have hMnorm : D.M ≤ normalizer (V : Set G) := hV.pairFacts.le_normalizer
  have hMstab : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hMnorm (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  let W := Vtil (⊥ : Subgroup G) V hVe
  let Mb : Subgroup (MulAut W) := Mbar D.M ⊥ V hVe
  let Db : Subgroup (MulAut W) := barSub (⊥ : Subgroup G) V hVe Dsub
  have hDb_le : Db ≤ Mb := barSub_mono ⊥ V hVe hDM
  have hDb_card : Nat.card Db = p := hDbar
  have hDb_p : IsPGroup p Db := by
    have hDb_eq : Db = (Dsub.subgroupOf (stabTil (⊥ : Subgroup G) V)).map
        (actTil (⊥ : Subgroup G) V hVe) := rfl
    rw [hDb_eq]
    exact (hDp.comap_subtype (K := stabTil (⊥ : Subgroup G) V)).map _
  have hLle : Dsub ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le hDM (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hLnorm : D.M ≤ normalizer ((Dsub ⊔ pCoreOf 2 D.M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLle).1 hnormal
  have hnormSub : (Db.subgroupOf Mb).Normal := by
    have hbar := barSub_subgroupOf_mbar_normal (V₀ := ⊥) hVe hLle hLnorm
    rwa [barSub_sup_pCoreOf_eq_of_hyp125 hV hDM] at hbar
  have hMb_norm : Mb ≤ Subgroup.normalizer (Db : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDb_le).1 hnormSub
  have hnorm : ∀ y ∈ Mb, ∀ a ∈ Db, y * a * y⁻¹ ∈ Db := by
    intro y hy a ha
    exact (Subgroup.mem_normalizer_iff.mp (hMb_norm hy) a).mp ha
  have hWsq : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hVe
  have hDb_odd : Odd (Nat.card Db) := by
    rw [hDb_card]
    exact hp.odd_of_ne_two hp2
  have hfixStable : StableUnder Mb (CFSG.Quasithin.fixV Db) :=
    CFSG.LocalAnalysis.WeakClosure81.stableUnder_fixV hnorm
  have hcommStable : StableUnder Mb (CFSG.Quasithin.commV Db) := by
    rw [CFSG.Quasithin.commV_eq_commSub]
    exact CFSG.LocalAnalysis.WeakClosure81.stableUnder_commSub hnorm
      (fun y _ w _ => Subgroup.mem_top (y w))
  have hdecomp := CFSG.Quasithin.coprime_decomp (V := W) hDb_odd hWsq
    (W := ⊤) (fun g _ w _ => Subgroup.mem_top (g w))
  rw [top_inf_eq] at hdecomp
  have hsup : CFSG.Quasithin.commV Db ⊔ CFSG.Quasithin.fixV Db = ⊤ := by
    rw [CFSG.Quasithin.commV_eq_commSub]
    exact hdecomp.1
  have hdisj : CFSG.Quasithin.commV Db ⊓ CFSG.Quasithin.fixV Db = ⊥ := by
    rw [CFSG.Quasithin.commV_eq_commSub]
    exact hdecomp.2
  have hInd : IsIndivisible Mb := by
    simpa [Mb] using TwelveSeventeen.isIndivisible D hx h61 h127 h1214 hV
  have hcases := hInd (CFSG.Quasithin.fixV Db) (CFSG.Quasithin.commV Db)
    hfixStable hcommStable (by rw [sup_comm]; exact hsup)
  have hcomm_top : CFSG.Quasithin.commV Db = ⊤ := by
    rcases hcases with h | h
    · exfalso
      have hDb_bot : Db = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall Db).2 fun y hy => ?_
        ext w
        have hw : w ∈ CFSG.Quasithin.fixV Db := by rw [h]; exact Subgroup.mem_top w
        have hyw : y w = w := (CFSG.Quasithin.mem_fixV.mp hw) y hy
        exact hyw
      have h1 : Nat.card Db = 1 := by rw [hDb_bot]; simp
      rw [hDb_card] at h1
      exact hp.ne_one h1
    · exact h
  have hfix_bot : CFSG.Quasithin.fixV Db = ⊥ := by
    have h := hdisj
    rw [hcomm_top, top_inf_eq] at h
    exact h
  have hmParam : E3.mParam Mb = 4 := by
    simpa [mBar, Mb] using hm4
  by_cases hEven : Even (Nat.card Mb)
  · obtain ⟨t, htMb, ht2, htm⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Mb hEven
    have htcomm : rk (CFSG.Quasithin.commV (Subgroup.zpowers t)) = 4 := by
      rw [← CFSG.Quasithin.rkIdx_fixV_zpowers]
      rw [htm, hmParam]
    have htN : t ∈ Subgroup.normalizer (Db : Set (MulAut W)) := hMb_norm htMb
    have ht2' : t * t = 1 := by
      rw [← pow_two, ← ht2]
      exact pow_orderOf_eq_one t
    rcases CFSG.Quasithin.involution_on_cyclic hp2 hDb_p (isCyclic_of_prime_card hDb_card)
        (by rw [pow_two]; exact ht2')
        (fun y hy => (Subgroup.mem_normalizer_iff.mp htN y).mp hy) with hcent | hinv
    ·
      have hycomm : ∀ y ∈ Db, y * t = t * y := by
        intro y hy
        have h1 := hcent y hy
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      have hstabW : ∀ y ∈ Db, ∀ w ∈ CFSG.Quasithin.commV (Subgroup.zpowers t),
          y w ∈ CFSG.Quasithin.commV (Subgroup.zpowers t) := by
        intro y hy w hw
        rw [CFSG.Quasithin.commV_zpowers_eq_map] at hw ⊢
        obtain ⟨v, -, rfl⟩ := hw
        refine ⟨y v, Subgroup.mem_top _, ?_⟩
        rw [CFSG.Quasithin.commHom_apply, CFSG.Quasithin.commHom_apply, map_mul, map_inv]
        have h2 : t (y v) = y (t v) := by
          have := congrArg (fun f : MulAut W => f v) (hycomm y hy)
          simpa [MulAut.mul_apply] using this.symm
        rw [h2]
      have hdvd : orderOf (2 : ZMod p) ∣ rk (CFSG.Quasithin.commV (Subgroup.zpowers t)) :=
        CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hWsq hDb_p hstabW
          (by rw [hfix_bot, inf_bot_eq])
      rw [htcomm] at hdvd
      have hp15 : p ∣ 2 ^ 4 - 1 :=
        CFSG.GroupTheory.prime_dvd_two_pow_sub_one_of_orderOf_dvd hdvd
      have : p = 3 ∨ p = 5 := by
        have h1 : p ∣ 3 * 5 := by norm_num; exact hp15
        rcases (Nat.Prime.dvd_mul hp).1 h1 with h3' | h5'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3')
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5')
      omega
    ·
      letI : Module (ZMod 2) (Additive W) := CFSG.GroupTheory.elemModule 2 hWsq
      haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
      let ρ : Representation (ZMod 2) ↥Mb (Additive W) :=
        { toFun := fun y =>
            (MulEquiv.toAdditive (y : MulAut W)).toLinearEquiv (ZMod.map_smul (n := 2) _)
          map_one' := by ext x; rfl
          map_mul' := by intro a b; ext x; rfl }
      let X : Subgroup ↥Mb := Db.subgroupOf Mb
      let t' : ↥Mb := ⟨t, htMb⟩
      have hXcard : Nat.card ↥X = p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDb_le).toEquiv]
        exact hDb_card
      have ht'2 : orderOf t' = 2 := by
        rw [← Subgroup.orderOf_coe t']
        exact ht2
      have ht'2' : t' * t' = 1 := by
        rw [← pow_two, ← ht'2]
        exact pow_orderOf_eq_one t'
      have hinv' : ∀ x ∈ X, t' * x * t'⁻¹ = x⁻¹ := by
        intro x hx
        apply Subtype.ext
        have hx' : ((x : ↥Mb) : MulAut W) ∈ Db := hx
        exact hinv ((x : ↥Mb) : MulAut W) hx'
      have hX2 : ∀ x ∈ X, x ^ 2 = 1 → x = 1 := by
        intro x hx hx2
        have hdvd : orderOf x ∣ Nat.card ↥X := Subgroup.orderOf_dvd_natCard X hx
        rw [hXcard] at hdvd
        have hodd : Odd (orderOf x) := (hp.odd_of_ne_two hp2).of_dvd_nat hdvd
        have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
        rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
        · exact orderOf_eq_one_iff.1 h1
        · rw [h1] at hodd
          obtain ⟨k, hk⟩ := hodd
          omega
      have hfixSpace : fixedSpace ρ X = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro u hu
        rw [mem_fixedSpace_iff] at hu
        have hw : Additive.toMul u ∈ CFSG.Quasithin.fixV Db := by
          rw [CFSG.Quasithin.mem_fixV]
          intro y hy
          have hyX : (⟨y, hDb_le hy⟩ : ↥Mb) ∈ X := hy
          have h := hu (⟨y, hDb_le hy⟩ : ↥Mb) hyX
          exact Additive.ofMul.injective h
        rw [hfix_bot] at hw
        have h1 : Additive.toMul u = 1 := Subgroup.mem_bot.1 hw
        rw [show u = Additive.ofMul (Additive.toMul u) from rfl, h1]
        rfl
      haveI : Fintype ↥X := Fintype.ofFinite ↥X
      have hN : ∀ u ∈ (⊤ : Submodule (ZMod 2) (Additive W)), normOp ρ X u = 0 := by
        intro u _
        have h := mem_fixedSpace_normOp ρ X u
        rw [hfixSpace] at h
        simpa using h
      have hfin : Module.finrank (ZMod 2) (Additive W) = rk W := by
        have h1 : Nat.card (Additive W) = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W), Nat.card_zmod]
        have h2 : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.ofMul
        have h3 : Nat.card W = 2 ^ rk W :=
          card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hWsq)
        have h4 : 2 ^ Module.finrank (ZMod 2) (Additive W) = 2 ^ rk W := by
          rw [← h1, h2, h3]
        exact Nat.pow_right_injective (le_refl 2) h4
      have hker_fin : Module.finrank (ZMod 2)
          (LinearMap.ker ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) =
          rk (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
        have hcardker : Nat.card (LinearMap.ker
            ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) =
            Nat.card (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
          refine Nat.card_congr ?_
          refine
            { toFun := fun u => ⟨Additive.toMul u.1, ?_⟩
              invFun := fun w => ⟨Additive.ofMul w.1, ?_⟩
              left_inv := fun u => rfl
              right_inv := fun w => rfl }
          · have hu := u.2
            rw [LinearMap.mem_ker] at hu
            rw [mem_fixV_zpowers]
            have hu' : (ρ t' - 1) u.1 = 0 := hu
            rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hu'
            have h2 : ρ t' u.1 = Additive.ofMul (t (Additive.toMul u.1)) := rfl
            rw [h2] at hu'
            exact Additive.ofMul.injective hu'
          · rw [LinearMap.mem_ker]
            have hw : t w.1 = w.1 :=
              (mem_fixV_zpowers t w.1).1 w.2
            have h1 : ρ t' (Additive.ofMul w.1) = Additive.ofMul (t w.1) := rfl
            rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, h1, hw]
        haveI : Module.Finite (ZMod 2)
            ↥(LinearMap.ker ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) :=
          Module.Finite.of_finite
        have h1 : Nat.card (LinearMap.ker
            ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) =
            2 ^ Module.finrank (ZMod 2)
              (LinearMap.ker ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
            (V := ↥(LinearMap.ker ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1))),
            Nat.card_zmod]
        have h2 : Nat.card (CFSG.Quasithin.fixV (Subgroup.zpowers t)) =
            2 ^ rk (CFSG.Quasithin.fixV (Subgroup.zpowers t)) :=
          card_eq_two_pow hWsq _
        have h3 : 2 ^ Module.finrank (ZMod 2)
            (LinearMap.ker ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) =
            2 ^ rk (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
          rw [← h1, hcardker, h2]
        exact Nat.pow_right_injective (le_refl 2) h3
      have hmap : Module.finrank (ZMod 2)
          (Submodule.map ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1) ⊤) = 4 := by
        have hrange : Submodule.map ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1) ⊤ =
            LinearMap.range ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1) :=
          (LinearMap.range_eq_map _).symm
        rw [hrange]
        have h1 := LinearMap.finrank_range_add_finrank_ker
          ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)
        rw [hker_fin, hfin] at h1
        have h2 := rk_add_rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t))
        have h3 : Module.finrank (ZMod 2)
            (LinearMap.range ((ρ t' : Additive W →ₗ[ZMod 2] Additive W) - 1)) =
            rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by omega
        rw [h3, htm, hmParam]
      have hdim8 : Module.finrank (ZMod 2) (Additive W) = 8 := by
        have hdim := HyperplaneOrbitBounds.finrank_eq_two_mul ρ X t' ht'2' hinv' hX2
          (⊤ : Submodule (ZMod 2) (Additive W))
          (fun u _ => Submodule.mem_top (x := ρ t' u))
          (fun x _ u _ => Submodule.mem_top (x := ρ x u)) hN
        rw [hmap] at hdim
        simpa using hdim
      have hdvd_rk : orderOf (2 : ZMod p) ∣ rk W := by
        have h := CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hWsq hDb_p
          (W := ⊤) (fun y _ w _ => Subgroup.mem_top (y w))
          (by rw [hfix_bot, inf_bot_eq])
        simpa [rk_top] using h
      have hdvd : orderOf (2 : ZMod p) ∣ 8 := by
        rw [← hdim8, hfin]
        exact hdvd_rk
      have hp8 : p ∣ 2 ^ 8 - 1 :=
        CFSG.GroupTheory.prime_dvd_two_pow_sub_one_of_orderOf_dvd hdvd
      have hp3or5or17 : p = 3 ∨ p = 5 ∨ p = 17 := by
        have h : p ∣ 3 * 5 * 17 := by norm_num; exact hp8
        rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
        · rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h5
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3)
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5))
        · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2))
      rcases hp3or5or17 with rfl | rfl | rfl
      · omega
      · omega
      ·
        have hrkW : rk W = 8 := by
          rw [← hfin]
          exact hdim8
        have hirrDb : ∀ U : Subgroup W, (∀ y ∈ Db, ∀ u ∈ U, y u ∈ U) →
            U = ⊥ ∨ U = ⊤ := by
          intro U hU
          by_cases hUne : U = ⊥
          · exact Or.inl hUne
          · right
            have hUdvd : orderOf (2 : ZMod 17) ∣ rk U :=
              CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hWsq hDb_p
                (W := U) hU (by rw [hfix_bot, inf_bot_eq])
            rw [CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.orderOf_two_zmod_seventeen] at hUdvd
            have hrkUle : rk U ≤ 8 := by
              have h := rk_mono (le_top : U ≤ ⊤)
              simpa [rk_top, hrkW] using h
            have hrkU : rk U = 8 := by
              have hpos : 0 < rk U := by
                rw [Nat.pos_iff_ne_zero]
                intro h0
                have hUp : IsPGroup 2 ↥U :=
                  isPGroup_two_of_sq_eq_one
                    (fun w : ↥U => Subtype.ext (by simpa using hWsq (w : W)))
                exact hUne ((rk_eq_zero_iff_of_isPGroup (H := U) hUp).1 h0)
              omega
            apply Subgroup.eq_of_le_of_card_ge (le_top : U ≤ ⊤)
            rw [card_eq_two_pow hWsq U, card_eq_two_pow hWsq (⊤ : Subgroup W), rk_top,
              hrkU, hrkW]
        obtain ⟨q, hqsig⟩ := hx.sig_nonempty
        have hqp : q.Prime := (D.sig_prime q hqsig).1
        have hq2 : q ≠ 2 := (D.sig_prime q hqsig).2
        have hq1 : 1 < q := hqp.one_lt
        have hCtN : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal :=
          cTilde_bot_normal D.M V hMnorm
        haveI : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := hCtN
        have h115' := h115 (⊥ : Subgroup G) V (Hyp125.hyp11 h127 hV) (by simp) q hqsig
        obtain ⟨-, h115le, h115ge⟩ := h115'
        have hle : CFSG.Open.pRank q D.M - 1 ≤
            CFSG.Open.pRank q (⊤ : Subgroup (F11.MBar11 D.M ⊥ V)) := h115le
        have hMbarEq : CFSG.Open.pRank q (⊤ : Subgroup (F11.MBar11 D.M ⊥ V)) =
            CFSG.Open.pRank q (⊤ : Subgroup Mb) := by
          simpa [Mb] using s15_Three_pRank_MBar11 hVe hMstab q
        have hpRank : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Mb) := by
          rw [← hMbarEq]
          omega
        obtain ⟨E, -, hE_elem, hE_card⟩ :=
          CFSG.SectionRank.exists_pRank (G := Mb) hq1 (⊤ : Subgroup Mb)
        haveI : IsMulCommutative E := hE_elem.1
        let Db' : Subgroup Mb := Db.subgroupOf Mb
        have hDb'_card : Nat.card Db' = 17 := by
          dsimp [Db']
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDb_le).toEquiv, hDb_card]
        haveI : Db'.Normal := hnormSub
        haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
        haveI : IsCyclic Db' := isCyclic_of_prime_card hDb'_card
        have hAut_card : Nat.card (MulAut Db') = 16 := by
          have h := Nat.card_congr (IsCyclic.mulAutMulEquiv Db').toEquiv
          rw [h, hDb'_card, Nat.card_units, Nat.card_zmod]
        let φ : Mb →* MulAut Db' := MulAut.conjNormal
        have hcentral : ∀ e ∈ E, ∀ d ∈ Db', e * d * e⁻¹ = d := by
          intro e he d hd
          have hφ : φ e = 1 := by
            have h1 : orderOf (φ e) ∣ q := by
              exact dvd_trans (orderOf_map_dvd φ e)
                (orderOf_dvd_of_pow_eq_one (hE_elem.2 e he))
            have h4 : orderOf (φ e) ∣ 16 := by
              rw [← hAut_card]
              exact orderOf_dvd_natCard (φ e)
            have h5 : orderOf (φ e) = 1 := by
              have hcop : Nat.Coprime q 16 := by
                rw [show 16 = 2 ^ 4 by norm_num]
                exact Nat.Coprime.pow_right 4 (Nat.coprime_two_right.mpr (hqp.odd_of_ne_two hq2))
              have hg : orderOf (φ e) ∣ Nat.gcd q 16 := Nat.dvd_gcd h1 h4
              rw [hcop.gcd_eq_one] at hg
              exact Nat.dvd_one.mp hg
            exact orderOf_eq_one_iff.mp h5
          have hconj : ((MulAut.conjNormal e) ⟨d, hd⟩ : Db') = ⟨d, hd⟩ := by
            simpa [φ] using congrArg (fun f : MulAut Db' => f ⟨d, hd⟩) hφ
          have hconj' : e * d * e⁻¹ = d := by
            have := congrArg (fun x : Db' => (x : Mb)) hconj.symm
            simpa [MulAut.conjNormal_apply] using this.symm
          exact hconj'
        have hEDcomm : ∀ e ∈ E, ∀ d ∈ Db', e * d = d * e := by
          intro e he d hd
          have h := hcentral e he d hd
          rwa [mul_inv_eq_iff_eq_mul] at h
        let A : Subgroup Mb := E ⊔ Db'
        haveI : IsMulCommutative A := by
          dsimp [A]
          exact CFSG.OddStandard.SmallF3.HarrisU33.isMulCommutative_sup_of_commute
            hEDcomm hE_elem.1 (IsCyclic.isMulCommutative (α := Db'))
        have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
          intro a ha b hb
          exact congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb⟩)
        let ρE : Mb →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
          CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom ρ
        have hρE_inj : Function.Injective ρE := by
          intro y z h
          apply Subtype.ext
          ext w
          have h1 := congrArg (fun e : Additive W ≃ₗ[ZMod 2] Additive W =>
            e (Additive.ofMul w)) h
          rw [CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom_apply,
              CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom_apply]
            at h1
          exact Additive.ofMul.injective h1
        let O : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W) := A.map ρE
        have hOcomm : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := by
          intro a ha b hb
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
          rw [← map_mul, ← map_mul, hAcomm x hx y hy]
        have hOirr : ∀ U : Submodule (ZMod 2) (Additive W),
            (∀ g ∈ O, CFSG.LocalAnalysis.EvenBN.Tits.I21L.Stable g U) →
              U = ⊥ ∨ U = ⊤ := by
          intro U hU
          let Usub : Subgroup W :=
            { carrier := {w : W | Additive.ofMul w ∈ U}
              one_mem' := by
                change Additive.ofMul (1 : W) ∈ U
                simpa using U.zero_mem
              mul_mem' := fun {a b} ha hb => by
                change Additive.ofMul (a * b) ∈ U
                change Additive.ofMul a + Additive.ofMul b ∈ U
                exact U.add_mem ha hb
              inv_mem' := fun {a} ha => by
                change Additive.ofMul a⁻¹ ∈ U
                change -Additive.ofMul a ∈ U
                exact U.neg_mem ha }
          have hUsub_inv : ∀ d ∈ Db, ∀ w ∈ Usub, d w ∈ Usub := by
            intro d hd w hw
            have hdA : (⟨d, hDb_le hd⟩ : ↥Mb) ∈ A := by
              exact Subgroup.mem_sup_right (show (⟨d, hDb_le hd⟩ : ↥Mb) ∈ Db' from hd)
            have hρdO : ρE ⟨d, hDb_le hd⟩ ∈ O := Subgroup.mem_map_of_mem ρE hdA
            have h := hU (ρE ⟨d, hDb_le hd⟩) hρdO (Additive.ofMul w) hw
            have h' : (ρE ⟨d, hDb_le hd⟩) (Additive.ofMul w) = Additive.ofMul (d w) := by
              rw [CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom_apply]
              rfl
            rw [h'] at h
            exact h
          rcases hirrDb Usub hUsub_inv with hbot | htop
          · left
            rw [Submodule.eq_bot_iff]
            intro u hu
            have h1 : Additive.toMul u ∈ Usub := hu
            rw [hbot] at h1
            have h2 : Additive.toMul u = 1 := Subgroup.mem_bot.mp h1
            rw [show u = Additive.ofMul (Additive.toMul u) from rfl, h2]
            rfl
          · right
            rw [Submodule.eq_top_iff']
            intro u
            have h1 : Additive.toMul u ∈ Usub := by
              rw [htop]
              exact Subgroup.mem_top _
            change Additive.ofMul (Additive.toMul u) ∈ U at h1
            simpa using h1
        have hOcyc : IsCyclic O :=
          CFSG.LocalAnalysis.EvenBN.Tits.I21L.isCyclic_of_irreducible_abelian
            O hOcomm hOirr
        let eToO : E →* O :=
          { toFun := fun e => ⟨ρE (e : Mb), Subgroup.mem_map_of_mem ρE
              (Subgroup.mem_sup_left e.2)⟩
            map_one' := Subtype.ext (map_one ρE)
            map_mul' := fun a b => Subtype.ext (map_mul ρE (a : Mb) (b : Mb)) }
        have heToO_inj : Function.Injective eToO := by
          intro a b h
          apply Subtype.ext
          apply hρE_inj
          exact congrArg Subtype.val h
        haveI : IsCyclic O := hOcyc
        have hEcyc : IsCyclic E := isCyclic_of_injective eToO heToO_inj
        have hEnotcyc : ¬ IsCyclic E := by
          intro hcyc
          haveI : IsCyclic E := hcyc
          obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
          have hgord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
          have hgq : orderOf g ∣ q := by
            apply orderOf_dvd_of_pow_eq_one
            exact Subtype.ext (hE_elem.2 (g : E) g.2)
          rw [hgord, hE_card] at hgq
          have hdvd : q ^ 2 ∣ q := dvd_trans (pow_dvd_pow q hpRank) hgq
          have hle : q ^ 2 ≤ q := Nat.le_of_dvd (Nat.Prime.pos hqp) hdvd
          have : 2 ≤ 1 := (Nat.pow_le_pow_iff_right hq1).1 (by simpa using hle)
          omega
        exact (hEnotcyc hEcyc).elim
  ·
    have hrkW : rk W = 4 := by
      have h := hmParam
      unfold E3.mParam at h
      rw [if_neg hEven] at h
      exact h
    have hdvd : orderOf (2 : ZMod p) ∣ rk W := by
      have h := CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hWsq hDb_p
        (W := ⊤) (fun y _ w _ => Subgroup.mem_top (y w)) (by rw [hfix_bot, inf_bot_eq])
      simpa [rk_top] using h
    rw [hrkW] at hdvd
    have hp15 : p ∣ 2 ^ 4 - 1 :=
      CFSG.GroupTheory.prime_dvd_two_pow_sub_one_of_orderOf_dvd hdvd
    have : p = 3 ∨ p = 5 := by
      have h1 : p ∣ 3 * 5 := by norm_num; exact hp15
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h3' | h5'
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3')
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5')
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
