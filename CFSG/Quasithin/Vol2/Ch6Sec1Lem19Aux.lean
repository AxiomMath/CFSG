module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem17Nat
public import CFSG.Quasithin.Vol2.Ch6Sec1Prop15

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem conjSub_centralizer' (g : G) (X : Subgroup G) :
    conjSub g (Subgroup.centralizer (X : Set G)) =
      Subgroup.centralizer (conjSub g X : Set G) :=
  (centralizer_map_conj X g).symm

omit [Finite G] in
theorem conjSub_eq_of_mem_normalizer' {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : conjSub g X = X :=
  map_conj_eq_of_mem_normalizer hg

omit [Finite G] in
theorem conjSub_commutator' (g : G) (A B : Subgroup G) :
    conjSub g ⁅A, B⁆ = ⁅conjSub g A, conjSub g B⁆ :=
  Subgroup.map_commutator A B _

omit [Finite G] in
theorem conjSub_zpowers (g b : G) :
    conjSub g (Subgroup.zpowers b) = Subgroup.zpowers (g * b * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
theorem card_conjSub' (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [Finite G] in
theorem relIndex_le_two_of_forall {K F : Subgroup G}
    (h : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ ∉ K → f₂ ∉ K → f₁⁻¹ * f₂ ∈ K) : K.relIndex F ≤ 2 := by
  classical
  let φ : ↥F ⧸ K.subgroupOf F → Bool :=
    Quotient.lift (fun f : ↥F => decide ((f : G) ∈ K)) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ K.subgroupOf F := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab'
      simp only [decide_eq_decide]
      constructor
      · intro ha
        have := K.mul_mem ha hab'
        simpa using this
      · intro hb
        have := K.mul_mem hb (K.inv_mem hab')
        simpa [mul_assoc] using this)
  have hinj : Function.Injective φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hxy' : decide ((a : G) ∈ K) = decide ((b : G) ∈ K) := hxy
        by_cases ha : (a : G) ∈ K
        · have hb : (b : G) ∈ K := by simpa [ha] using hxy'
          exact K.mul_mem (K.inv_mem ha) hb
        · have hb : (b : G) ∉ K := by simpa [ha] using hxy'
          exact h a a.2 b b.2 ha hb
  show Nat.card (↥F ⧸ K.subgroupOf F) ≤ 2
  calc Nat.card (↥F ⧸ K.subgroupOf F) ≤ Nat.card Bool := Nat.card_le_card_of_injective φ hinj
    _ = 2 := by simp

theorem mQuot_le_one_of_relIndex_le_two {X Y : Subgroup G} (hX : IsPGroup 2 X)
    (h : Y.relIndex X ≤ 2) : mQuot X Y ≤ 1 := by
  have e := relIndex_eq_two_pow hX Y
  by_contra hcon
  push Not at hcon
  have : 2 ^ 2 ≤ 2 ^ mQuot X Y := Nat.pow_le_pow_right (by norm_num) hcon
  omega

namespace Hyp611Nat

theorem le_centralizer_ZS_of_conjSub_le (h6112 : Stmt6_1_12) (h : Hyp611Nat G T M L V n)
    {H : Subgroup G} (hTH : IsSylowTwoOf T H)
    (hHZ : H ≤ Subgroup.normalizer (ch6ZS T L V : Set G)) {x : G} (hxH : conjSub x V ≤ H) :
    conjSub x V ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (conjSub x V) :=
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).map _
  obtain ⟨y, hyH, hle⟩ := F7.isSylowTwoOf_exists_conj_le hTH hxH hV2
  have hW : conjSubgroup V (x⁻¹ * y) ≤ T := by
    intro w hw
    rw [mem_conjSubgroup_iff] at hw
    have hv : y * w * y⁻¹ ∈ conjSub x V :=
      mem_conjSub.mpr (by simpa [mul_assoc] using hw)
    have := mem_conjSub.mp (hle hv)
    simpa [mul_assoc] using this
  have hWS : conjSubgroup V (x⁻¹ * y) ≤ ch6S T L V :=
    (le_wClos (mem_gammaSet_iff.mpr ⟨hW, x⁻¹ * y, le_rfl, mQuot_self _⟩)).trans
      (h6112 G T M L V n h).2.2
  intro v hv
  have hw : y⁻¹ * v * y ∈ conjSubgroup V (x⁻¹ * y) := by
    rw [mem_conjSubgroup_iff]
    have := mem_conjSub.mp hv
    simpa [mul_assoc] using this
  have hwc := (hWS hw).2
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hyN : y⁻¹ ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.inv_mem _ (hHZ hyH)
  have hz' : y⁻¹ * z * y⁻¹⁻¹ ∈ ch6ZS T L V := (Subgroup.mem_normalizer_iff.mp hyN z).mp hz
  rw [inv_inv] at hz'
  have hc := Subgroup.mem_centralizer_iff.mp hwc _ hz'
  calc z * v = y * ((y⁻¹ * z * y) * (y⁻¹ * v * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * v * y) * (y⁻¹ * z * y)) * y⁻¹ := by rw [hc]
    _ = v * z := by group

theorem isSylowIn_S_inf (h : Hyp611Nat G T M L V n) :
    IsSylowIn 2 (ch6S T L V)
      (Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) :=
  E6.isSylowIn_of_le h.isSylowIn_S
    (le_inf (inf_le_left.trans h.toHyp611.T_le_normalizer) inf_le_right) inf_le_right

theorem exists_conj_S (h : Hyp611Nat G T M L V n) {P : Subgroup G}
    (hP : P ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hP2 : IsPGroup 2 P) :
    ∃ y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G),
      conjSub y⁻¹ P ≤ ch6S T L V := by
  obtain ⟨y, hy, hle⟩ := F7.isSylowTwoOf_exists_conj_le h.isSylowIn_S_inf hP hP2
  refine ⟨y, hy, fun p hp => ?_⟩
  have hp' := mem_conjSub.mp hp
  rw [inv_inv] at hp'
  have := mem_conjSub.mp (hle (show y * p * y⁻¹ ∈ P from by simpa [mul_assoc] using hp'))
  simpa [mul_assoc] using this

omit [Finite G] in
theorem conj_mem_centralizer_iff {y b : G} (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    y * b * y⁻¹ ∈ Subgroup.centralizer (V : Set G) ↔ b ∈ Subgroup.centralizer (V : Set G) := by
  have hN : y ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    F7.normalizer_le_normalizer_centralizer V hy
  exact ((Subgroup.mem_normalizer_iff.mp hN) b).symm

theorem commutator_of_two (h : Hyp611Nat G T M L V n) {b : G}
    (hb : b ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hb2 : ∃ k : ℕ, b ^ 2 ^ k = 1) (hbV : b ∉ Subgroup.centralizer (V : Set G)) :
    ⁅V, Subgroup.zpowers b⁆ = ch6ZS T L V ∧
      ∀ Y : Subgroup G, ch6ZS T L V ≤ Y → Y ≤ V →
        Nat.card ↥⁅Y, Subgroup.zpowers b⁆ * Nat.card (ch6ZS T L V) = Nat.card Y := by
  have hP2 : IsPGroup 2 (Subgroup.zpowers b) := by
    obtain ⟨k, hk⟩ := hb2
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨y, hy, hle⟩ := h.exists_conj_S (Subgroup.zpowers_le.mpr hb) hP2
  set b' := y⁻¹ * b * y⁻¹⁻¹ with hb'
  have hb'S : b' ∈ ch6S T L V := hle (mul_mem_conjSub (Subgroup.mem_zpowers b))
  have hb'V : b' ∉ Subgroup.centralizer (V : Set G) := fun hc =>
    hbV ((conj_mem_centralizer_iff (Subgroup.inv_mem _ hy.1)).mp hc)
  have hVy : conjSub y V = V := conjSub_eq_of_mem_normalizer' hy.1
  have hZy : conjSub y (ch6ZS T L V) = ch6ZS T L V :=
    conjSub_eq_of_mem_normalizer' (Subgroup.centralizer_le_normalizer _ hy.2)
  have hbb : conjSub y (Subgroup.zpowers b') = Subgroup.zpowers b := by
    rw [conjSub_zpowers, hb']
    congr 1
    group
  refine ⟨?_, fun Y hZY hYV => ?_⟩
  · have := congrArg (conjSub y) (h.commutator_zpowers_eq hb'S hb'V)
    rwa [conjSub_commutator', hVy, hbb, hZy] at this
  · set Y' := conjSub y⁻¹ Y with hY'
    have hZY' : ch6ZS T L V ≤ Y' := by
      have := conjSub_mono y⁻¹ hZY
      rwa [show conjSub y⁻¹ (ch6ZS T L V) = ch6ZS T L V from by
        rw [← hZy, conjSub_conjSub_inv, hZy]] at this
    have hY'V : Y' ≤ V := by
      have := conjSub_mono y⁻¹ hYV
      rwa [show conjSub y⁻¹ V = V from by rw [← hVy, conjSub_conjSub_inv, hVy]] at this
    have h1 := h.card_commutator_mul hb'S hb'V hZY' hY'V
    have hYY : conjSub y Y' = Y := by rw [hY', ← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [← card_conjSub' y ⁅Y', Subgroup.zpowers b'⁆, conjSub_commutator', hYY, hbb,
      ← card_conjSub' y Y', hYY] at h1
    exact h1

theorem conj_eq_of_not_le_commutator (h : Hyp611Nat G T M L V n) {Y F : Subgroup G}
    (hZY : ch6ZS T L V ≤ Y) (hY2 : Y.relIndex V = 2)
    (hF : F ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hF2 : IsPGroup 2 F) (hnot : ¬ ch6ZS T L V ≤ ⁅Y, F⁆) {f₁ f₂ : G} (hf₁ : f₁ ∈ F)
    (hf₂ : f₂ ∈ F) (hf₁V : f₁ ∉ Subgroup.centralizer (V : Set G))
    (hf₂V : f₂ ∉ Subgroup.centralizer (V : Set G)) :
    ∀ v ∈ V, f₁ * v * f₁⁻¹ = f₂ * v * f₂⁻¹ := by
  obtain ⟨y, hy, hle⟩ := h.exists_conj_S hF hF2
  have hVy : conjSub y V = V := conjSub_eq_of_mem_normalizer' hy.1
  have hZy : conjSub y (ch6ZS T L V) = ch6ZS T L V :=
    conjSub_eq_of_mem_normalizer' (Subgroup.centralizer_le_normalizer _ hy.2)
  have hVy' : conjSub y⁻¹ V = V := by rw [← hVy, conjSub_conjSub_inv, hVy]
  have hZy' : conjSub y⁻¹ (ch6ZS T L V) = ch6ZS T L V := by
    rw [← hZy, conjSub_conjSub_inv, hZy]
  set F' := conjSub y⁻¹ F with hF'
  set Y' := conjSub y⁻¹ Y with hY'
  have hZY' : ch6ZS T L V ≤ Y' := by
    have := conjSub_mono y⁻¹ hZY
    rwa [hZy'] at this
  have hY'2 : Y'.relIndex V = 2 := by
    rw [← hVy', hY', ← hY2]
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective
  have hnot' : ¬ ch6ZS T L V ≤ ⁅Y', F'⁆ := by
    intro hle'
    apply hnot
    have := conjSub_mono y hle'
    rwa [hZy, conjSub_commutator', hY', hF', ← conjSub_mul, ← conjSub_mul, mul_inv_cancel,
      conjSub_one, conjSub_one] at this
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hne⟩ := hcon
  set g₁ : Subgroup.normalizer (V : Set G) :=
    ⟨y⁻¹ * f₁ * y⁻¹⁻¹, h.toHyp611.T_le_normalizer (hle (mul_mem_conjSub hf₁)).1⟩ with hg₁
  set g₂ : Subgroup.normalizer (V : Set G) :=
    ⟨y⁻¹ * f₂ * y⁻¹⁻¹, h.toHyp611.T_le_normalizer (hle (mul_mem_conjSub hf₂)).1⟩ with hg₂
  have hconj1 : ∀ g : Subgroup.normalizer (V : Set G),
      conjAct V g = 1 → (g : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun a : MulAut ↥V => ((a ⟨x, hx⟩ : ↥V) : G)) hg
    simp only [MulAut.one_apply, conjAct_apply_coe] at this
    calc x * (g : G) = ((g : G) * x * (g : G)⁻¹) * g := by rw [this]
      _ = g * x := by group
  have hyN : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hy.1
  have ha₁ : conjAct V g₁ ≠ 1 := fun h1 => hf₁V
    ((conj_mem_centralizer_iff hyN).mp (hconj1 g₁ h1))
  have ha₂ : conjAct V g₂ ≠ 1 := fun h1 => hf₂V
    ((conj_mem_centralizer_iff hyN).mp (hconj1 g₂ h1))
  have ha₁₂ : conjAct V g₁ ≠ conjAct V g₂ := by
    intro heq
    apply hne
    set w := y⁻¹ * v * y with hw
    have hwV : w ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hyN v).mp hv
      simpa [hw, mul_assoc] using this
    have := congrArg (fun a : MulAut ↥V => ((a ⟨w, hwV⟩ : ↥V) : G)) heq
    simp only [conjAct_apply_coe, hg₁, hg₂] at this
    calc f₁ * v * f₁⁻¹ = y * ((y⁻¹ * f₁ * y⁻¹⁻¹) * w * (y⁻¹ * f₁ * y⁻¹⁻¹)⁻¹) * y⁻¹ := by
          rw [hw]; group
      _ = y * ((y⁻¹ * f₂ * y⁻¹⁻¹) * w * (y⁻¹ * f₂ * y⁻¹⁻¹)⁻¹) * y⁻¹ := by rw [this]
      _ = f₂ * v * f₂⁻¹ := by rw [hw]; group
  exact hnot' (h.ZS_le_commutator_of_ne (g₁ := g₁) (g₂ := g₂) hZY' hY'2 hle (mul_mem_conjSub hf₁)
    (mul_mem_conjSub hf₂) ha₁ ha₂ ha₁₂)

theorem commutator_eq_conjSub (h : Hyp611Nat G T M L V n) (y : G) {B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (conjSub y V : Set G) ⊓
      Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G))
    (hB2 : IsPGroup 2 B) (hne : ⁅conjSub y V, B⁆ ≠ ⊥) :
    ⁅conjSub y V, B⁆ = conjSub y (ch6ZS T L V) := by
  set B' := conjSub y⁻¹ B with hB'
  have hB'B : conjSub y B' = B := by rw [hB', ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hB'le : B' ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have := conjSub_mono y⁻¹ hB
    rwa [conjSub_inf, conjSub_normalizer, ← conjSub_centralizer', conjSub_conjSub_inv,
      conjSub_conjSub_inv] at this
  have hB'2 : IsPGroup 2 B' := hB2.map _
  have hkey : ⁅V, B'⁆ = ch6ZS T L V := by
    have hne' : ⁅V, B'⁆ ≠ ⊥ := by
      intro h0
      apply hne
      rw [← hB'B, ← conjSub_commutator', h0]
      exact Subgroup.map_bot _
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro v hv b hb
      by_cases hbV : b ∈ Subgroup.centralizer (V : Set G)
      · have : ⁅v, b⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact Subgroup.mem_centralizer_iff.mp hbV v hv
        rw [this]
        exact (ch6ZS T L V).one_mem
      · obtain ⟨k, hk⟩ := hB'2 ⟨b, hb⟩
        have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [← (h.commutator_of_two (hB'le hb) ⟨k, hbk⟩ hbV).1]
        exact Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers b)
    · by_contra hcon
      apply hne'
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      by_contra hbv
      apply hcon
      have hbV : b ∉ Subgroup.centralizer (V : Set G) := fun hc =>
        hbv (Subgroup.mem_centralizer_iff.mp hc v hv).symm
      obtain ⟨k, hk⟩ := hB'2 ⟨b, hb⟩
      have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← (h.commutator_of_two (hB'le hb) ⟨k, hbk⟩ hbV).1]
      exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hb)
  rw [← hB'B, ← conjSub_commutator', hkey]

theorem le_centralizer_conjSub_ZS (h6112 : Stmt6_1_12) (h : Hyp611Nat G T M L V n)
    {H : Subgroup G} (hTH : IsSylowTwoOf T H)
    (hHZ : H ≤ Subgroup.normalizer (ch6ZS T L V : Set G)) (g : G) {x : G}
    (hx : conjSub x V ≤ conjSub g H) :
    conjSub x V ≤ Subgroup.centralizer (conjSub g (ch6ZS T L V) : Set G) := by
  have h1 : conjSub (g⁻¹ * x) V ≤ H := by
    rw [conjSub_mul]
    have := conjSub_mono g⁻¹ hx
    rwa [conjSub_conjSub_inv] at this
  have h2 := h.le_centralizer_ZS_of_conjSub_le h6112 hTH hHZ h1
  have h3 := conjSub_mono g h2
  rwa [conjSub_centralizer', ← conjSub_mul, mul_inv_cancel_left] at h3

theorem le_centralizer_conjSub_of_le (h6110 : Stmt6_1_10) (h : Hyp611Nat G T M L V n)
    {x y : G} {B : Subgroup G} (hBV : B ≤ conjSub x V)
    (hBN : B ≤ Subgroup.normalizer (conjSub y V : Set G)) (hm : mQuot (conjSub x V) B ≤ 1)
    (hE : conjSub y V ≤ Subgroup.centralizer (B : Set G)) :
    conjSub y V ≤ Subgroup.centralizer (conjSub x V : Set G) := by
  have hV := h.toHyp611.isElemAbelian
  have hEe : conjSub y V = conjSubgroup V y⁻¹ := by
    unfold conjSubgroup conjSub
    rw [inv_inv]
  have hEel : IsElemAbelian 2 (conjSub y V) := hEe ▸ isElemAbelian_conjSubgroup hV y⁻¹
  have hV' : conjSub x V = conjSubgroup (conjSub y V) (y * x⁻¹) := by
    rw [hEe, conjSubgroup_conjSubgroup]
    unfold conjSubgroup conjSub
    congr 1
    group
  have hs : sParam hEel = n := by
    have h1 : sParam (isElemAbelian_conjSubgroup hV y⁻¹) = sParam hV :=
      sParam_conj hV y⁻¹ _
    have h2 := ((h6110 G T M L V n h).2.1 hV).1
    have h3 : sParam hEel = sParam (isElemAbelian_conjSubgroup hV y⁻¹) := by
      congr 1
    rw [h3, h1, h2]
  have h7 := e3_7 hEel (g := y * x⁻¹) (B := B) (le_inf (hV' ▸ hBV) hBN)
    (by rw [hs, ← hV']; have := h.two_le; omega)
  intro e he
  have : e ∈ conjSub y V ⊓ Subgroup.centralizer (B : Set G) := ⟨he, hE he⟩
  rw [h7, ← hV'] at this
  exact this.2

theorem centralizer_le_normalizer_of_mQuot_lt (h6110 : Stmt6_1_10) (h : Hyp611Nat G T M L V n)
    (y : G) {U : Subgroup G} (hU : U ≤ conjSub y V) (hm : mQuot (conjSub y V) U < n) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (conjSub y V : Set G) := by
  have hEe : conjSub y V = conjSubgroup V y⁻¹ := by
    unfold conjSubgroup conjSub
    rw [inv_inv]
  have hr : (n : ℕ∞) ≤ rParam (conjSub y V) := by
    rw [hEe, rParam_conj]
    exact (h6110 G T M L V n h).1
  by_contra hcon
  have hle : rParam (conjSub y V) ≤ mQuot (conjSub y V) U := by
    unfold rParam
    exact iInf₂_le U ⟨hU, hcon⟩
  have : (n : ℕ∞) ≤ mQuot (conjSub y V) U := hr.trans hle
  have : n ≤ mQuot (conjSub y V) U := by exact_mod_cast this
  omega

theorem n_le_two_of_config (h6110 : Stmt6_1_10) (h : Hyp611Nat G T M L V n)
    {U : Subgroup G} {y : G} (hVU : V ≤ U)
    (hB : (U ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex U = 2)
    (hF : (conjSub y V ⊓ Subgroup.normalizer (V : Set G)).relIndex (conjSub y V) = 2)
    (hEB : ⁅conjSub y V, U ⊓ Subgroup.normalizer (conjSub y V : Set G)⁆ =
      conjSub y (ch6ZS T L V))
    (hVF : ⁅V, conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = ch6ZS T L V)
    (hZ : conjSub y (ch6ZS T L V) ≠ ch6ZS T L V)
    (hEZ : conjSub y V ≤ Subgroup.centralizer (ch6ZS T L V : Set G)) : n ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := conjSub y V with hE
  set B := U ⊓ Subgroup.normalizer (E : Set G) with hBdef
  set F := E ⊓ Subgroup.normalizer (V : Set G) with hFdef
  set VB := V ⊓ B with hVB
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  have hE2 : IsPGroup 2 E := hV2.map _
  have hZV := h.ZS_le
  have hZVB : ch6ZS T L V ≤ VB := by
    refine le_inf hZV (le_inf (hZV.trans hVU) ?_)
    exact (Subgroup.le_centralizer_iff.mp hEZ).trans (Subgroup.centralizer_le_normalizer _)
  have hVBV : VB ≤ V := inf_le_left
  have hFN : F ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hEZ)
  have hF2 : IsPGroup 2 F := hE2.to_le inf_le_left
  have hcomm1 : ⁅VB, F⁆ ≤ ch6ZS T L V := hVF ▸ Subgroup.commutator_mono hVBV le_rfl
  have hcomm2 : ⁅VB, F⁆ ≤ conjSub y (ch6ZS T L V) := by
    rw [← hEB, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono inf_le_left (inf_le_right)
  have hnot : ¬ ch6ZS T L V ≤ ⁅VB, F⁆ := by
    intro hle
    apply hZ
    have h1 : ch6ZS T L V ≤ conjSub y (ch6ZS T L V) := hle.trans hcomm2
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_conjSub'])).symm
  obtain ⟨f, hfF, hfV⟩ : ∃ f ∈ F, f ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    apply h.ZS_ne_bot
    rw [← hVF]
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x hx => hcon x hx
  obtain ⟨k, hk⟩ := hF2 ⟨f, hfF⟩
  have hfk : f ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hf := h.commutator_of_two (hFN hfF) ⟨k, hfk⟩ hfV
  have hVB2 : VB.relIndex V = 2 := by
    have hle2 : VB.relIndex V ≤ 2 := by
      rw [hVB, Subgroup.inf_relIndex_left]
      rw [← hB]
      exact Subgroup.relIndex_le_of_le_right hVU (by rw [hB]; norm_num)
    have hne1 : VB.relIndex V ≠ 1 := by
      intro h1
      have hVVB : V ≤ VB := Subgroup.relIndex_eq_one.mp h1
      apply hnot
      rw [← hf.1]
      exact Subgroup.commutator_mono hVVB (Subgroup.zpowers_le.mpr hfF)
    have h0 := relIndex_ne_zero' V VB
    omega
  have hFalike : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ ∉ Subgroup.centralizer (V : Set G) →
      f₂ ∉ Subgroup.centralizer (V : Set G) → ∀ v ∈ V, f₁ * v * f₁⁻¹ = f₂ * v * f₂⁻¹ :=
    fun f₁ hf₁ f₂ hf₂ h₁ h₂ => h.conj_eq_of_not_le_commutator hZVB hVB2 hFN hF2 hnot hf₁ hf₂ h₁ h₂
  have hFC : (F ⊓ Subgroup.centralizer (V : Set G)).relIndex F ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    refine relIndex_le_two_of_forall fun f₁ hf₁ f₂ hf₂ h₁ h₂ => ?_
    have e := hFalike f₁ hf₁ f₂ hf₂ h₁ h₂
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := e v hv
    calc v * (f₁⁻¹ * f₂) = f₁⁻¹ * (f₁ * v * f₁⁻¹) * f₂ := by group
      _ = f₁⁻¹ * (f₂ * v * f₂⁻¹) * f₂ := by rw [this]
      _ = f₁⁻¹ * f₂ * v := by group
  have hCF : E ⊓ Subgroup.centralizer (V : Set G) ≤ F :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hEC : E ⊓ Subgroup.centralizer (V : Set G) = F ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hFdef, inf_assoc, inf_comm (Subgroup.normalizer (V : Set G)), ← inf_assoc,
      inf_eq_left.mpr (hCF.trans inf_le_right)]
  have hm : mQuot E (E ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 := by
    rw [mQuot_add hCF inf_le_left, hEC]
    have h1 : mQuot F (F ⊓ Subgroup.centralizer (V : Set G)) ≤ 1 :=
      mQuot_le_one_of_relIndex_le_two hF2 hFC
    have h2 : mQuot E F ≤ 1 := mQuot_le_one_of_relIndex_le_two hE2 (by rw [hF])
    omega
  by_contra hn
  push Not at hn
  have hCN := h.centralizer_le_normalizer_of_mQuot_lt h6110 y
    (U := E ⊓ Subgroup.centralizer (V : Set G)) inf_le_left (hm.trans_lt hn)
  have hVN : V ≤ Subgroup.normalizer (E : Set G) := by
    refine le_trans ?_ hCN
    exact Subgroup.le_centralizer_iff.mp inf_le_right
  have hVVB : V ≤ VB := le_inf le_rfl (le_inf hVU hVN)
  have := Subgroup.relIndex_eq_one.mpr hVVB
  omega

end Hyp611Nat

end CFSG.Quasithin.H13
