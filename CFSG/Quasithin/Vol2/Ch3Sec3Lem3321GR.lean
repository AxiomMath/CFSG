module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FS
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FB

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure RData (G : Type) [Group G] [Finite G] (T M L D R : Subgroup G) (α : ↥L →* SL4) :
    Prop where
  hyp : Hyp331 G T M L D
  TL : T ≤ Subgroup.normalizer (L : Set G)
  surj : Function.Surjective α
  ker : α.ker = CFSG.pCore 2 ↥L
  kerV : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G)
  mapU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4
  RT : R ≤ T
  TLR : T ⊓ L ≤ R
  QR : pCoreOf 2 (L ⊔ T) ≤ R
  conj : ∀ r ∈ R, ∃ y : ↥L, α y ∈ FLc.Ut 4 ∧ ∀ (x : ↥L) (hx : r * (x : G) * r⁻¹ ∈ L),
    α ⟨r * x * r⁻¹, hx⟩ = α y * α x * (α y)⁻¹

namespace RData

variable {T M L D R : Subgroup G} {α : ↥L →* SL4}

theorem RL (hR : RData G T M L D R α) : R ≤ Subgroup.normalizer (L : Set G) := hR.RT.trans hR.TL

theorem le_normalizer_liftPre (hR : RData G T M L D R α) (I : Set ℕ) :
    R ≤ Subgroup.normalizer (liftPre α (FLc.QI 4 I) : Set G) := by
  intro t ht
  obtain ⟨y, hyU, hy⟩ := hR.conj t ht
  have hyI : α y ∈ FLc.QI 4 I := FLc.Ut_le_QI 4 I hyU
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj t).injective).ge)
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  have hx : t * (l : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hR.RL ht) l).mp l.2
  refine ⟨⟨t * l * t⁻¹, hx⟩, ?_, rfl⟩
  show α ⟨t * l * t⁻¹, hx⟩ ∈ FLc.QI 4 I
  rw [hy l hx]
  exact (FLc.QI 4 I).mul_mem ((FLc.QI 4 I).mul_mem hyI hl) ((FLc.QI 4 I).inv_mem hyI)

theorem le_normalizer_Y (hR : RData G T M L D R α) (I : Set ℕ) :
    R ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 I) : Set G) := fun _ ht =>
  L3316.mem_normalizer_perfectCore (hR.le_normalizer_liftPre I ht)

theorem isPGroup (hR : RData G T M L D R α) : IsPGroup 2 R := hR.hyp.sylow.1.to_le hR.RT

theorem mem_Ut (hR : RData G T M L D R α) (l : ↥L) (hl : (l : G) ∈ R) : α l ∈ FLc.Ut 4 := by
  rw [← hR.mapU]
  exact ⟨l, Subgroup.mem_subgroupOf.2 ⟨hR.RT hl, l.2⟩, rfl⟩

theorem vPlus_le_pCoreOf (hR : RData G T M L D R α) : vPlus L T ≤ pCoreOf 2 (L ⊔ T) :=
  (Hyp331.vPlus_reduced hR.hyp.toSetup331).1.trans inf_le_left

theorem vPlus_le_R (hR : RData G T M L D R α) : vPlus L T ≤ R :=
  hR.vPlus_le_pCoreOf.trans hR.QR

theorem pCoreOf_L_le_R (hR : RData G T M L D R α) : pCoreOf 2 L ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans ?_ hR.QR
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hR.TL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem vPlus_le (hR : RData G T M L D R α) {Y : Subgroup G} (hYL : Y ≤ L) :
    vPlus L T ≤ pCoreOf 2 (Y ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR.vPlus_le_R.trans le_sup_right)
    (sup_le (hYL.trans (L3317.le_normalizer_vPlus hR.hyp))
      (hR.RT.trans (Hyp331.le_normalizer_vPlus L T)))
    (hR.isPGroup.to_le hR.vPlus_le_R)

theorem commV_le (hR : RData G T M L D R α) {Y : Subgroup G} (hYL : Y ≤ L)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) :
    ⁅vPlus L T, Y⁆ ≤ c134Q (Y ⊔ R) Y ⊓ pCoreOf 2 L := by
  refine le_inf (Subgroup.commutator_mono (hR.vPlus_le hYL) le_rfl) ?_
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := L3317.le_normalizer_vPlus hR.hyp
  have h1 : ⁅vPlus L T, Y⁆ ≤ vPlus L T :=
    Ch1Sec3.commutator_le_left_of_le_normalizer (hYL.trans hLV)
  have h2 : ⁅vPlus L T, Y⁆ ≤ Y :=
    Ch3Sec3.commutator_le_right_of_le_normalizer (hR.vPlus_le_R.trans hRY)
  have hab := (Hyp331.vPlus_reduced hR.hyp.toSetup331).2.1
  intro x hx
  have hxL : x ∈ L := hYL (h2 hx)
  have hxC : x ∈ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hab.1.is_comm.comm ⟨v, hv⟩ ⟨x, h1 hx⟩)
  have h3 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hR.ker]
    exact (hR.kerV ⟨x, hxL⟩).2 hxC
  exact (Lem3328.mem_pCore_iff _).1 h3

theorem exists_levi_one (hR : RData G T M L D R α) :
    ∃ ψ : ↥(liftCore α (FLc.QI 4 {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {1})) ∧
      ∀ y : ↥(liftCore α (FLc.QI 4 {1})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blkAt 1 3 (by norm_num)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  have hk2 : IsPGroup 2 ↥α.ker := by
    rw [hR.ker]
    exact CFSG.pCore_isPGroup
  obtain ⟨ψ, hψs, hψk, hψe⟩ := L3318.exists_levi (Nat.card_zmod 2) (by norm_num) hR.surj hk2
    (I := {1}) (a := 1) (m := 3) (by norm_num) le_rfl (Or.inr rfl) (Or.inl rfl) hno
  exact ⟨ψ, hψs, Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk, hψe⟩

theorem card_Q_ge_one (hR : RData G T M L D R α) :
    8 * Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ R) (liftCore α (FLc.QI 4 {1})) ⊓
      pCoreOf 2 L) ≤
      Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ R) (liftCore α (FLc.QI 4 {1}))) := by
  obtain ⟨ψ, -, hψk', hψe⟩ := hR.exists_levi_one
  have hRY := hR.le_normalizer_Y {1}
  have htr : ∀ {j c : Fin 4} (hj : 1 ≤ (j : ℕ)) (hc : 1 ≤ (c : ℕ)) (hcj : c ≠ j)
      (h0j : (0 : Fin 4) ≠ j), SpecialLinearGroup.transvection h0j (1 : ZMod 2) ∈
        (α.comp (Subgroup.inclusion (FData.Q_le_L hRY))).range := by
    intro j c hj hc hcj h0j
    have h0c : (0 : Fin 4) ≠ c := fun e => by rw [← e] at hc; simp at hc
    obtain ⟨x, hx, hxe⟩ := L3318.exists_mem_liftCore hR.surj
      (L3318.transvection_mem_perfectCore_one (K := ZMod 2) (n := 4) le_rfl rfl hc h0c)
    obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hR.surj
      (L3318.transvection_mem_perfectCore_levi_one (K := ZMod 2) (n := 4) le_rfl hc hj hcj)
    have hψx : ψ ⟨x, hx⟩ = 1 := by
      apply Subtype.ext
      rw [hψe, hxe, SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one]
      ext a b
      rw [blkAt_apply, Matrix.add_apply, Matrix.single_apply]
      have hne : ¬ ((0 : Fin 4) = ⟨1 + (a : ℕ), by omega⟩ ∧ c = ⟨1 + (b : ℕ), by omega⟩) := by
        rintro ⟨e, -⟩
        have := congrArg Fin.val e
        simp only [Fin.val_zero] at this
        omega
      rw [ite_eq_right hne, add_zero, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]
    have hxO := FData.mem_pCoreOf_of_levi hRY hψk' hx hψx
    obtain ⟨hq, hqL, hqe⟩ := FData.comm_mem_Q (α := α) (liftCore_le α _) hx hxO hy
    refine ⟨⟨⁅x, y⁆, hq⟩, ?_⟩
    show α ⟨⁅x, y⁆, _⟩ = _
    rw [hqe, hxe, hye, SpecialLinearGroup.commutatorElement_transvection h0c hcj h0j, mul_one]
  refine card_ge_of_inj hR.ker (FData.Q_le_L hRY) (fun c => ⟨radM1 c, det_radM1 c⟩)
    (fun c c' h => radM1_inj c c' (congrArg Subtype.val h)) fun c => ?_
  exact radM1_mem (htr (c := 2) (by decide) (by decide) (by decide) _)
    (htr (c := 1) (by decide) (by decide) (by decide) _)
    (htr (c := 1) (by decide) (by decide) (by decide) _) c

theorem isSylowTwoOf_one (hR : RData G T M L D R α) :
    IsSylowTwoOf R (liftCore α (FLc.QI 4 {1}) ⊔ R) := by
  set Y := liftCore α (FLc.QI 4 {1}) with hY
  set P := liftPre α (FLc.QI 4 {1}) with hP
  have hYP : Y ≤ P := by
    rw [hY, liftCore_eq]
    exact Subgroup.map_mono (perfectCore_le _)
  have hPL : P ≤ L := L3316.liftPre_le α _
  have hTLP : T ⊓ L ≤ P := by
    intro x hx
    refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
    show α ⟨x, hx.2⟩ ∈ FLc.QI 4 {1}
    exact FLc.Ut_le_QI 4 {1} (hR.mem_Ut ⟨x, hx.2⟩ (hR.TLR hx))
  have hS₀ : IsSylowTwoOf (T ⊓ L) L := L3317.isSylowTwoOf_inf hR.hyp hR.TL
  have hS₁ : IsSylowTwoOf (T ⊓ L) P := by
    refine ⟨hTLP, hS₀.2.1, fun h2 => hS₀.2.2 ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ L) P L hTLP hPL
    exact h2.trans ⟨P.relIndex L, h1.symm⟩
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) := fun p hp =>
    L3316.mem_normalizer_perfectCore (Subgroup.le_normalizer hp)
  have hS₂ : IsSylowTwoOf (T ⊓ L ⊓ Y) Y := A4.isSylowTwoOf_inf_normal hS₁ hYP hPY
  have hRY := hR.le_normalizer_Y {1}
  refine ⟨le_sup_right, hR.isPGroup, ?_⟩
  have h1 : (R ⊓ Y).relIndex Y = R.relIndex (R ⊔ Y) := B6.relIndex_inf_eq_relIndex_sup hRY
  have h2 : T ⊓ L ⊓ Y ≤ R ⊓ Y := inf_le_inf_right Y hR.TLR
  have h3 : (R ⊓ Y).relIndex Y ∣ (T ⊓ L ⊓ Y).relIndex Y :=
    Subgroup.relIndex_dvd_of_le_left Y h2
  intro h2d
  apply hS₂.2.2
  have h4 : 2 ∣ (R ⊓ Y).relIndex Y := by
    rw [h1, sup_comm]
    exact h2d
  exact h4.trans h3

theorem vPlus_ne_bot (hR : RData G T M L D R α) : vPlus L T ≠ ⊥ := by
  intro h1
  apply Setup.omegaOneCenterOf_ne_bot hR.hyp.sylow.1 hR.hyp.toSetup331.T_ne_bot
  rw [eq_bot_iff, ← h1]
  exact le_conjClosure _ _

theorem isLocal_one (hR : RData G T M L D R α) :
    quasithinIsLocal R (liftCore α (FLc.QI 4 {1})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
  have : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    sl_isSimple_of_card_two (Nat.card_zmod 2) le_rfl
  have hY1 : liftCore α (FLc.QI 4 {1}) ≠ ⊥ := by
    rintro h1
    obtain ⟨a, b, hab⟩ := exists_pair_ne (SpecialLinearGroup (Fin 3) (ZMod 2))
    obtain ⟨x, rfl⟩ := hψs a
    obtain ⟨y, rfl⟩ := hψs b
    apply hab
    have hx : (x : G) ∈ (⊥ : Subgroup G) := by rw [← h1]; exact x.2
    have hy : (y : G) ∈ (⊥ : Subgroup G) := by rw [← h1]; exact y.2
    have : x = y := Subtype.ext ((Subgroup.mem_bot.1 hx).trans (Subgroup.mem_bot.1 hy).symm)
    rw [this]
  have hk : IsPGroup 2 ψ.ker := by
    rw [hψk]
    exact CFSG.pCore_isPGroup
  refine ⟨hR.isPGroup, Sec1216Lv.mem_cComp_of_hom (L3316.liftCore_perfect α _) hY1
    (hR.le_normalizer_Y {1}) ψ hψs hk, hR.isSylowTwoOf_one.2.2, fun hbot => hR.vPlus_ne_bot ?_⟩
  rw [eq_bot_iff, ← hbot]
  exact hR.vPlus_le (liftCore_le α _)

theorem charTwo (hR : RData G T M L D R α) {Y : Subgroup G} (hYL : Y ≤ L) :
    CharTwo (Y ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLT : CharTwo (L ⊔ T) := charTwo_of_inH' hR.hyp.qtke hR.hyp.sylow
    ⟨le_sup_right, hR.hyp.toSetup331.pCoreOf_ne_bot⟩
  have hYR : Y ⊔ R ≤ L ⊔ T := sup_le_sup hYL hR.RT
  have hQ : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (Y ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hR.QR.trans le_sup_right)
      (hYR.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro x ⟨hx, hxC⟩
  have hxC' : x ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    Subgroup.centralizer_le (fun y hy => hQ hy) hxC
  exact hQ (hLT ⟨hYR hx, hxC'⟩)

theorem isMSPair_or_one (hR : RData G T M L D R α) :
    IsMSPair (liftCore α (FLc.QI 4 {1}) ⊔ R) R ∨ ∃ C : Subgroup G, C ≤ R ∧ C ≠ ⊥ ∧
      (C.subgroupOf R).Characteristic ∧
        liftCore α (FLc.QI 4 {1}) ⊔ R ≤ Subgroup.normalizer (C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
  obtain ⟨hR2, hcomp, hidx, hO⟩ := hR.isLocal_one
  have hα₂ := isModO2Surj_comp hψs hψk
  by_cases hMS3 : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      ¬ liftCore α (FLc.QI 4 {1}) ⊔ R ≤ Subgroup.normalizer (C : Set G)
  · left
    refine ⟨⟨sqtkGroup_of_pCoreOf_ne_bot hR.hyp.qtke hR.hyp.simple hR.hyp.nonabelian hO,
      hR.charTwo (liftCore_le α _), liftCore α (FLc.QI 4 {1}), hcomp,
      Subgroup.coe_mul_of_right_le_normalizer_left _ R (hR.le_normalizer_Y {1}),
      CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 _ hα₂.1 hα₂.2⟩,
      Or.inl ⟨R, ?_, hidx, ?_⟩, hMS3⟩
    · refine lt_of_le_of_ne le_sup_right fun hRe => ?_
      have hYR : liftCore α (FLc.QI 4 {1}) ≤ R := hRe ▸ le_sup_left
      have hsol : Group.IsSolvable ↥R := by
        have := hR2.isNilpotent
        infer_instance
      exact not_isSolvable_of_mem_cComp hcomp
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYR)
          (Subgroup.inclusion_injective hYR))
    · exact (F6.pCoreOf_eq_self_of_isPGroup hR2).symm
  · right
    push Not at hMS3
    exact hMS3

theorem not_case12_one (hR : RData G T M L D R α)
    (hV : 16 ≤ Nat.card ↥⁅vPlus L T, liftCore α (FLc.QI 4 {1})⁆) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hc : IsC134Case j (liftCore α (FLc.QI 4 {1}) ⊔ R) R (liftCore α (FLc.QI 4 {1}))) :
    False := by
  obtain ⟨ψ, hψs, hψk, -⟩ := hR.exists_levi_one
  have hα₂ := isModO2Surj_comp hψs hψk
  have h1 := Subgroup.card_le_of_le (hR.commV_le (liftCore_le α _) (hR.le_normalizer_Y {1}))
  have hQ8 := hR.card_Q_ge_one
  have hQ : Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ R) (liftCore α (FLc.QI 4 {1}))) ≤
      64 := by
    rcases hj with rfl | rfl
    · rw [card_Q_of_case1 hα₂ hc]
      norm_num
    · rw [card_Q_of_case2 hα₂ hc]
  omega

theorem not_case3_one (hR : RData G T M L D R α)
    (h3 : IsC134Case3 (liftCore α (FLc.QI 4 {1}) ⊔ R) R (liftCore α (FLc.QI 4 {1})))
    (hc : ∃ c ∈ ⁅vPlus L T, liftCore α (FLc.QI 4 {1})⁆, c ≠ 1 ∧
      c ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G)) : False := by
  obtain ⟨c, hcV, hc1, hcC⟩ := hc
  have h1 : c ∈ c134Q (liftCore α (FLc.QI 4 {1}) ⊔ R) (liftCore α (FLc.QI 4 {1})) ⊓
      Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G) :=
    ⟨(hR.commV_le (liftCore_le α _) (hR.le_normalizer_Y {1}) hcV).1, hcC⟩
  rw [MSY.inf_centralizer_eq_bot_of_case3 h3, Subgroup.mem_bot] at h1
  exact hc1 h1

theorem not_case5_one (hR : RData G T M L D R α)
    (h5 : IsC134Case5 (liftCore α (FLc.QI 4 {1}) ⊔ R) R (liftCore α (FLc.QI 4 {1}))) : False := by
  obtain ⟨ψ, hψs, hψk, hψe⟩ := hR.exists_levi_one
  exact not_case5_of hR.isSylowTwoOf_one (hR.le_normalizer_Y {1}) hψs hψk
    (fun y hy => FData.blkAt_mem_ut _ (hR.mem_Ut ⟨y, liftCore_le α _ y.2⟩ hy) (hψe y)) h5

end RData

end CFSG.Quasithin.H13.L3321
