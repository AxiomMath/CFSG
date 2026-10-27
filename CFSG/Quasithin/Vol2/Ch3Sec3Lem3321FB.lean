module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FA
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318G

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open scoped commutatorElement

@[expose] def radM1 (c : Fin 3 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, c 0, c 1, c 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def radM3 (c : Fin 3 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, c 0; 0, 1, 0, c 1; 0, 0, 1, c 2; 0, 0, 0, 1]

theorem det_radM1 : ∀ c, (radM1 c).det = 1 := by decide +kernel

theorem det_radM3 : ∀ c, (radM3 c).det = 1 := by decide +kernel

theorem radM1_inj : ∀ c c', radM1 c = radM1 c' → c = c' := by decide +kernel

theorem radM3_inj : ∀ c c', radM3 c = radM3 c' → c = c' := by decide +kernel

theorem radM1_eq : ∀ c : Fin 3 → ZMod 2, radM1 c =
    (if c 0 = 1 then 1 + single 0 1 1 else 1) * (if c 1 = 1 then 1 + single 0 2 1 else 1) *
      (if c 2 = 1 then 1 + single 0 3 1 else 1) := by decide +kernel

theorem radM3_eq : ∀ c : Fin 3 → ZMod 2, radM3 c =
    (if c 0 = 1 then 1 + single 0 3 1 else 1) * (if c 1 = 1 then 1 + single 1 3 1 else 1) *
      (if c 2 = 1 then 1 + single 2 3 1 else 1) := by decide +kernel

theorem radM1_mem {E : Subgroup SL4}
    (h1 : SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 1) (by decide) 1 ∈ E)
    (h2 : SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 2) (by decide) 1 ∈ E)
    (h3 : SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 3) (by decide) 1 ∈ E)
    (c : Fin 3 → ZMod 2) : (⟨radM1 c, det_radM1 c⟩ : SL4) ∈ E := by
  have key : ∀ (b : Fin 3 → ZMod 2) (k : Fin 3) (j : Fin 4) (hj : (0 : Fin 4) ≠ j),
      SpecialLinearGroup.transvection hj 1 ∈ E →
      ∃ g ∈ E, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = if b k = 1 then 1 + single 0 j 1 else 1 := by
    intro b k j hj hmem
    by_cases hb : b k = 1
    · exact ⟨_, hmem, by rw [ite_eq_left_iff.2 (fun h => absurd hb h),
        SpecialLinearGroup.transvection_coe]⟩
    · exact ⟨1, E.one_mem, by rw [ite_eq_right hb]; rfl⟩
  obtain ⟨g₁, hg₁, e₁⟩ := key c 0 1 (by decide) h1
  obtain ⟨g₂, hg₂, e₂⟩ := key c 1 2 (by decide) h2
  obtain ⟨g₃, hg₃, e₃⟩ := key c 2 3 (by decide) h3
  have : (⟨radM1 c, det_radM1 c⟩ : SL4) = g₁ * g₂ * g₃ := by
    apply Subtype.ext
    show radM1 c = (g₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (g₂ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      (g₃ : Matrix (Fin 4) (Fin 4) (ZMod 2))
    rw [e₁, e₂, e₃]
    exact radM1_eq c
  rw [this]
  exact E.mul_mem (E.mul_mem hg₁ hg₂) hg₃

theorem radM3_mem {E : Subgroup SL4}
    (h1 : SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 3) (by decide) 1 ∈ E)
    (h2 : SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := 3) (by decide) 1 ∈ E)
    (h3 : SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 3) (by decide) 1 ∈ E)
    (c : Fin 3 → ZMod 2) : (⟨radM3 c, det_radM3 c⟩ : SL4) ∈ E := by
  have key : ∀ (b : Fin 3 → ZMod 2) (k : Fin 3) (i : Fin 4) (hi : i ≠ (3 : Fin 4)),
      SpecialLinearGroup.transvection hi 1 ∈ E →
      ∃ g ∈ E, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = if b k = 1 then 1 + single i 3 1 else 1 := by
    intro b k i hi hmem
    by_cases hb : b k = 1
    · exact ⟨_, hmem, by rw [ite_eq_left_iff.2 (fun h => absurd hb h),
        SpecialLinearGroup.transvection_coe]⟩
    · exact ⟨1, E.one_mem, by rw [ite_eq_right hb]; rfl⟩
  obtain ⟨g₁, hg₁, e₁⟩ := key c 0 0 (by decide) h1
  obtain ⟨g₂, hg₂, e₂⟩ := key c 1 1 (by decide) h2
  obtain ⟨g₃, hg₃, e₃⟩ := key c 2 2 (by decide) h3
  have : (⟨radM3 c, det_radM3 c⟩ : SL4) = g₁ * g₂ * g₃ := by
    apply Subtype.ext
    show radM3 c = (g₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (g₂ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      (g₃ : Matrix (Fin 4) (Fin 4) (ZMod 2))
    rw [e₁, e₂, e₃]
    exact radM3_eq c
  rw [this]
  exact E.mul_mem (E.mul_mem hg₁ hg₂) hg₃

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_mul {L Q : Subgroup G} {α : ↥L →* SL4} (hker : α.ker = CFSG.pCore 2 ↥L)
    (hQL : Q ≤ L) :
    Nat.card ↥Q = Nat.card ↥(Q ⊓ pCoreOf 2 L) *
      Nat.card ↥(α.comp (Subgroup.inclusion hQL)).range := by
  set f := α.comp (Subgroup.inclusion hQL) with hf
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have hk : f.ker = (pCoreOf 2 L).subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      hker, Lem3328.mem_pCore_iff]
    rfl
  have h2 : Nat.card ↥f.ker = Nat.card ↥(Q ⊓ pCoreOf 2 L) := by
    rw [hk, ← Subgroup.card_map_of_injective Q.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h1, h2, mul_comm]

omit [Finite G] in
theorem card_ge_of_inj {L Q : Subgroup G} {α : ↥L →* SL4} (hker : α.ker = CFSG.pCore 2 ↥L)
    (hQL : Q ≤ L) (r : (Fin 3 → ZMod 2) → SL4) (hr : Function.Injective r)
    (hmem : ∀ c, r c ∈ (α.comp (Subgroup.inclusion hQL)).range) :
    8 * Nat.card ↥(Q ⊓ pCoreOf 2 L) ≤ Nat.card ↥Q := by
  rw [card_eq_mul hker hQL, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  have h8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [← h8]
  exact Nat.card_le_card_of_injective (fun c => ⟨r c, hmem c⟩)
    fun c c' h => hr (congrArg Subtype.val h)

omit [Finite G] in
theorem card_field_eq_two {Y : Subgroup G}
    {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj Y α₂) {n : ℕ} {F : Type}
    [Field F] [Fintype F] (hFc : Fintype.card F = 2 ^ n) {α : ↥Y →* ↥(StatedSL 3 F)}
    (hα : IsModO2Surj Y α) : Fintype.card F = 2 :=
  Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)

omit [Finite G] in
theorem card_Q_of_case1 {T Y : Subgroup G} {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj Y α₂) (h1 : IsC134Case1 (Y ⊔ T) T Y) :
    Nat.card ↥(c134Q (Y ⊔ T) Y) = 8 := by
  obtain ⟨-, nF, F, _, _, hFc, -, α', hα's, hα'k, β, hβs, hβk, -⟩ := h1
  have hF := card_field_eq_two hα₂ hFc ⟨hα's, hα'k⟩
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card, hF]
  simp

omit [Finite G] in
theorem card_Q_of_case2 {T Y : Subgroup G} {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj Y α₂) (h2 : IsC134Case2 (Y ⊔ T) T Y) :
    Nat.card ↥(c134Q (Y ⊔ T) Y) = 64 := by
  obtain ⟨⟨nF, F, _, _, α', hFc, hα', -, -, β, hβs, hβk, -⟩, -⟩ := h2
  have hF := card_field_eq_two hα₂ hFc hα'
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
  simp

omit [Finite G] in
theorem card_Q_of_case3 {T Y : Subgroup G} {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj Y α₂) (h3 : IsC134Case3 (Y ⊔ T) T Y) :
    Nat.card ↥(c134Q (Y ⊔ T) Y) = 512 := by
  obtain ⟨⟨nF, F, _, _, α', hFc, hα', ⟨-, -, βZ, hβZs, hβZk, -⟩, ⟨-, hZQ, βQ, hβQs, hβQk, -⟩⟩,
    -⟩ := h3
  have hF := card_field_eq_two hα₂ hFc hα'
  have hβZi : Function.Injective βZ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβZk, Subgroup.bot_subgroupOf]
  have hZ8 : Nat.card ↥(centerOf (c134Q (Y ⊔ T) Y)) = 8 := by
    rw [Nat.card_congr (Equiv.ofBijective βZ ⟨hβZi, hβZs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup βQ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective βQ hβQs).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fun,
    Nat.card_eq_fintype_card (α := F), hF, hβQk,
    ← Subgroup.card_map_of_injective (c134Q (Y ⊔ T) Y).subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZQ, hZ8] at h1
  rw [h1]
  norm_num

namespace FData

variable {T M L D : Subgroup G} {α : ↥L →* SL4}

omit [Finite G] in
theorem Q_le_Y {Y : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    c134Q (Y ⊔ T) Y ≤ Y :=
  Ch3Sec3.commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer hTY))

omit [Finite G] in
theorem pCoreOf_le_pCoreOf {Y : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    pCoreOf 2 Y ≤ pCoreOf 2 (Y ⊔ T) :=
  CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTY))

theorem pCoreOf_L_le (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L) :
    pCoreOf 2 L ≤ pCoreOf 2 (Y ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hD.pCoreOf_le.trans le_sup_right)
    (sup_le (hYL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)) ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact hD.TL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

theorem vPlus_le (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L) :
    vPlus L T ≤ pCoreOf 2 (Y ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := ((Hyp331.vPlus_reduced hD.hyp.toSetup331).1.trans inf_le_left)
  have hPT : pCoreOf 2 (L ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf hD.hyp.toSetup331.isSylowTwoOf
  exact hV.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans le_sup_right)
    ((sup_le_sup_right hYL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))

theorem commV_le (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    ⁅vPlus L T, Y⁆ ≤ c134Q (Y ⊔ T) Y ⊓ pCoreOf 2 L := by
  refine le_inf (Subgroup.commutator_mono (hD.vPlus_le hYL) le_rfl) ?_
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    le_sup_left.trans (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.2.2.1
  have hVT : vPlus L T ≤ T :=
    (((Hyp331.vPlus_reduced hD.hyp.toSetup331).1.trans inf_le_left)).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hD.hyp.toSetup331.isSylowTwoOf)
  have h1 : ⁅vPlus L T, Y⁆ ≤ vPlus L T :=
    Ch1Sec3.commutator_le_left_of_le_normalizer (hYL.trans hLV)
  have h2 : ⁅vPlus L T, Y⁆ ≤ Y :=
    Ch3Sec3.commutator_le_right_of_le_normalizer (hVT.trans hTY)
  have hab := (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.1
  intro x hx
  have hxL : x ∈ L := hYL (h2 hx)
  have hxC : x ∈ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hab.1.is_comm.comm ⟨v, hv⟩ ⟨x, h1 hx⟩)
  have h3 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hD.ker]
    exact (hD.kerV ⟨x, hxL⟩).2 hxC
  exact (Lem3328.mem_pCore_iff _).1 h3

theorem comm_pCoreOf_le (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L) :
    ⁅pCoreOf 2 L, Y⁆ ≤ c134Q (Y ⊔ T) Y ⊓ pCoreOf 2 L :=
  le_inf (Subgroup.commutator_mono (hD.pCoreOf_L_le hYL) le_rfl)
    (Ch1Sec3.commutator_le_left_of_le_normalizer
      (hYL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)))

omit [Finite G] in
theorem mem_pCoreOf_of_levi {Y : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψk : ψ.ker = CFSG.pCore 2 ↥Y)
    {x : G} (hx : x ∈ Y) (h1 : ψ ⟨x, hx⟩ = 1) : x ∈ pCoreOf 2 (Y ⊔ T) := by
  have h2 : (⟨x, hx⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
    rw [← hψk]
    exact h1
  exact pCoreOf_le_pCoreOf hTY ((Lem3328.mem_pCore_iff _).1 h2)

omit [Finite G] in
theorem comm_mem_Q {Y : Subgroup G} (hYL : Y ≤ L) {x y : G} (hxY : x ∈ Y)
    (hx : x ∈ pCoreOf 2 (Y ⊔ T)) (hy : y ∈ Y) :
    ⁅x, y⁆ ∈ c134Q (Y ⊔ T) Y ∧ ∃ hq : ⁅x, y⁆ ∈ L,
      α ⟨⁅x, y⁆, hq⟩ = ⁅α ⟨x, hYL hxY⟩, α ⟨y, hYL hy⟩⁆ := by
  refine ⟨Subgroup.commutator_mem_commutator hx hy, ?_⟩
  have hq : ⁅x, y⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem (hYL hxY) (hYL hy)) (L.inv_mem (hYL hxY)))
      (L.inv_mem (hYL hy))
  refine ⟨hq, ?_⟩
  have : (⟨⁅x, y⁆, hq⟩ : ↥L) = ⁅(⟨x, hYL hxY⟩ : ↥L), ⟨y, hYL hy⟩⁆ := rfl
  rw [this, map_commutatorElement]

omit [Finite G] in
theorem Q_le_L {I : Set ℕ} (hTY : T ≤ Subgroup.normalizer (liftCore α (FLc.QI 4 I) : Set G)) :
    c134Q (liftCore α (FLc.QI 4 I) ⊔ T) (liftCore α (FLc.QI 4 I)) ≤ L :=
  (Q_le_Y hTY).trans (liftCore_le α _)

theorem transvection_mem_one (hD : FData G T M L D α)
    {ψ : ↥(liftCore α (FLc.QI 4 {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψk : ψ.ker = CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {1})))
    (hψe : ∀ y : ↥(liftCore α (FLc.QI 4 {1})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blkAt 1 3 (by norm_num)
          ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {j c : Fin 4} (hj : 1 ≤ (j : ℕ)) (hc : 1 ≤ (c : ℕ)) (hcj : c ≠ j) (h0j : (0 : Fin 4) ≠ j) :
    SpecialLinearGroup.transvection h0j (1 : ZMod 2) ∈
      (α.comp (Subgroup.inclusion (Q_le_L (hD.le_normalizer_Y {1})))).range := by
  have h0c : (0 : Fin 4) ≠ c := fun e => by rw [← e] at hc; simp at hc
  obtain ⟨x, hx, hxe⟩ := L3318.exists_mem_liftCore hD.surj
    (L3318.transvection_mem_perfectCore_one (K := ZMod 2) (n := 4) le_rfl rfl hc h0c)
  obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hD.surj
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
  have hxO := mem_pCoreOf_of_levi (hD.le_normalizer_Y {1}) hψk hx hψx
  obtain ⟨hq, hqL, hqe⟩ := comm_mem_Q (α := α) (liftCore_le α _) hx hxO hy
  refine ⟨⟨⁅x, y⁆, hq⟩, ?_⟩
  show α ⟨⁅x, y⁆, _⟩ = _
  rw [hqe, hxe, hye, SpecialLinearGroup.commutatorElement_transvection h0c hcj h0j, mul_one]

theorem transvection_mem_three (hD : FData G T M L D α)
    {ψ : ↥(liftCore α (FLc.QI 4 {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψk : ψ.ker = CFSG.pCore 2 ↥(liftCore α (FLc.QI 4 {3})))
    (hψe : ∀ y : ↥(liftCore α (FLc.QI 4 {3})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blkAt 0 3 (by norm_num)
          ((α ⟨y, liftCore_le α _ y.2⟩ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {i c : Fin 4} (hi : (i : ℕ) < 3) (hc : (c : ℕ) < 3) (hic : i ≠ c) (hi3 : i ≠ (3 : Fin 4)) :
    SpecialLinearGroup.transvection hi3 (1 : ZMod 2) ∈
      (α.comp (Subgroup.inclusion (Q_le_L (hD.le_normalizer_Y {3})))).range := by
  have hc3 : c ≠ (3 : Fin 4) := fun e => by rw [e] at hc; simp at hc
  have hno : ∀ c' ∈ ({3} : Set ℕ), ¬ (0 < c' ∧ c' < 0 + 3) := by
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    omega
  have hyP : SpecialLinearGroup.transvection hic (1 : ZMod 2) ∈
      perfectCore (flagStabilizer 4 (ZMod 2) {3}) := by
    rw [L3318.transvection_eq_liftT (by norm_num) hi hc hic]
    exact Ln2.liftT_mem_perfectCore (by norm_num) le_rfl hno _
  obtain ⟨y, hy, hye⟩ := L3318.exists_mem_liftCore hD.surj hyP
  obtain ⟨x, hx, hxe⟩ := L3318.exists_mem_liftCore hD.surj
    (L3318.transvection_mem_perfectCore_three (K := ZMod 2) (n := 4) hc (by norm_num) hc3)
  have hψx : ψ ⟨x, hx⟩ = 1 := by
    apply Subtype.ext
    rw [hψe, hxe, SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one]
    ext a b
    rw [blkAt_apply, Matrix.add_apply, Matrix.single_apply]
    have hne : ¬ (c = ⟨0 + (a : ℕ), by omega⟩ ∧ (3 : Fin 4) = ⟨0 + (b : ℕ), by omega⟩) := by
      rintro ⟨-, e⟩
      have := congrArg Fin.val e
      change 3 = 0 + (b : ℕ) at this
      have := b.isLt
      omega
    rw [ite_eq_right hne, add_zero, Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.mk.injEq, Nat.zero_add, Fin.val_inj]
  have hxO := mem_pCoreOf_of_levi (hD.le_normalizer_Y {3}) hψk hx hψx
  obtain ⟨hq, hqL, hqe⟩ := comm_mem_Q (α := α) (liftCore_le α _) hx hxO hy
  have hq' : ⁅y, x⁆ ∈ c134Q (liftCore α (FLc.QI 4 {3}) ⊔ T) (liftCore α (FLc.QI 4 {3})) := by
    have : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := by rw [commutatorElement_inv]
    rw [this]
    exact Subgroup.inv_mem _ hq
  refine ⟨⟨⁅y, x⁆, hq'⟩, ?_⟩
  have hyx : (⟨⁅y, x⁆, (Q_le_L (hD.le_normalizer_Y {3})) hq'⟩ : ↥L) =
      ⁅(⟨y, liftCore_le α _ hy⟩ : ↥L), ⟨x, liftCore_le α _ hx⟩⁆ := rfl
  show α ⟨⁅y, x⁆, _⟩ = _
  rw [hyx, map_commutatorElement, hye, hxe,
    SpecialLinearGroup.commutatorElement_transvection hic hc3 hi3, mul_one]

theorem card_Q_ge_one (hD : FData G T M L D α) :
    8 * Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ T) (liftCore α (FLc.QI 4 {1})) ⊓
      pCoreOf 2 L) ≤
      Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {1}) ⊔ T) (liftCore α (FLc.QI 4 {1}))) := by
  obtain ⟨ψ, -, hψk, hψe⟩ := hD.exists_levi_one
  refine card_ge_of_inj hD.ker (Q_le_L (hD.le_normalizer_Y {1})) (fun c => ⟨radM1 c, det_radM1 c⟩)
    (fun c c' h => radM1_inj c c' (congrArg Subtype.val h)) fun c => ?_
  exact radM1_mem (hD.transvection_mem_one hψk hψe (c := 2) (by decide) (by decide) (by decide) _)
    (hD.transvection_mem_one hψk hψe (c := 1) (by decide) (by decide) (by decide) _)
    (hD.transvection_mem_one hψk hψe (c := 1) (by decide) (by decide) (by decide) _) c

theorem card_Q_ge_three (hD : FData G T M L D α) :
    8 * Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {3}) ⊔ T) (liftCore α (FLc.QI 4 {3})) ⊓
      pCoreOf 2 L) ≤
      Nat.card ↥(c134Q (liftCore α (FLc.QI 4 {3}) ⊔ T) (liftCore α (FLc.QI 4 {3}))) := by
  obtain ⟨ψ, -, hψk, hψe⟩ := hD.exists_levi_three
  refine card_ge_of_inj hD.ker (Q_le_L (hD.le_normalizer_Y {3})) (fun c => ⟨radM3 c, det_radM3 c⟩)
    (fun c c' h => radM3_inj c c' (congrArg Subtype.val h)) fun c => ?_
  exact radM3_mem (hD.transvection_mem_three hψk hψe (c := 1) (by decide) (by decide) (by decide) _)
    (hD.transvection_mem_three hψk hψe (c := 0) (by decide) (by decide) (by decide) _)
    (hD.transvection_mem_three hψk hψe (c := 0) (by decide) (by decide) (by decide) _) c

theorem not_case12 (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj Y α₂)
    (hQ8 : 8 * Nat.card ↥(c134Q (Y ⊔ T) Y ⊓ pCoreOf 2 L) ≤ Nat.card ↥(c134Q (Y ⊔ T) Y))
    (hV : 16 ≤ Nat.card ↥⁅vPlus L T, Y⁆) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hc : IsC134Case j (Y ⊔ T) T Y) : False := by
  have h1 := Subgroup.card_le_of_le (hD.commV_le hYL hTY)
  have hQ : Nat.card ↥(c134Q (Y ⊔ T) Y) ≤ 64 := by
    rcases hj with rfl | rfl
    · rw [card_Q_of_case1 hα₂ hc]
      norm_num
    · rw [card_Q_of_case2 hα₂ hc]
  omega

theorem comm_le_of_case3 (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) {α₂ : ↥Y →* ↥(StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj Y α₂)
    (hQ8 : 8 * Nat.card ↥(c134Q (Y ⊔ T) Y ⊓ pCoreOf 2 L) ≤ Nat.card ↥(c134Q (Y ⊔ T) Y))
    (hV : 64 ≤ Nat.card ↥⁅vPlus L T, Y⁆) (h3 : IsC134Case3 (Y ⊔ T) T Y) :
    ⁅pCoreOf 2 L, Y⁆ ≤ ⁅vPlus L T, Y⁆ := by
  rw [card_Q_of_case3 hα₂ h3] at hQ8
  have heq : ⁅vPlus L T, Y⁆ = c134Q (Y ⊔ T) Y ⊓ pCoreOf 2 L :=
    Subgroup.eq_of_le_of_card_ge (hD.commV_le hYL hTY) (by omega)
  rw [heq]
  exact hD.comm_pCoreOf_le hYL

theorem not_case3 (hD : FData G T M L D α) {Y : Subgroup G} (hYL : Y ≤ L)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (h3 : IsC134Case3 (Y ⊔ T) T Y)
    (hc : ∃ c ∈ ⁅vPlus L T, Y⁆, c ≠ 1 ∧ c ∈ Subgroup.centralizer (Y : Set G)) : False := by
  obtain ⟨c, hcV, hc1, hcC⟩ := hc
  have h1 : c ∈ c134Q (Y ⊔ T) Y ⊓ Subgroup.centralizer (Y : Set G) :=
    ⟨(hD.commV_le hYL hTY hcV).1, hcC⟩
  rw [MSY.inf_centralizer_eq_bot_of_case3 h3, Subgroup.mem_bot] at h1
  exact hc1 h1

theorem not_case5_one (hD : FData G T M L D α)
    (h5 : IsC134Case5 (liftCore α (FLc.QI 4 {1}) ⊔ T) T (liftCore α (FLc.QI 4 {1}))) : False := by
  obtain ⟨ψ, hψs, hψk, hψe⟩ := hD.exists_levi_one
  exact not_case5_of (isSylowTwoOf_of_quasithinIsSylowTwo hD.hyp.sylow le_sup_right)
    (hD.le_normalizer_Y {1}) hψs hψk
    (fun y hy => blkAt_mem_ut _ (hD.mem_Ut _ hy) (hψe y)) h5

theorem not_case5_three (hD : FData G T M L D α)
    (h5 : IsC134Case5 (liftCore α (FLc.QI 4 {3}) ⊔ T) T (liftCore α (FLc.QI 4 {3}))) : False := by
  obtain ⟨ψ, hψs, hψk, hψe⟩ := hD.exists_levi_three
  exact not_case5_of (isSylowTwoOf_of_quasithinIsSylowTwo hD.hyp.sylow le_sup_right)
    (hD.le_normalizer_Y {3}) hψs hψk
    (fun y hy => blkAt_mem_ut _ (hD.mem_Ut _ hy) (hψe y)) h5

end FData

end CFSG.Quasithin.H13.L3321
