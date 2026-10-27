module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316F
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316G
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316I

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped Pointwise

namespace L3316

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inducedAut {L : Subgroup G} {Y : Type} [Group Y] {α : ↥L →* Y}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) :
    ∃ φ : MulAut Y, ∀ l : ↥L,
      φ (α l) = α ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht l).mp l.2⟩ := by
  have hmap : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  let ct : ↥L ≃* ↥L := ((MulAut.conj t).subgroupMap L).trans (MulEquiv.subgroupCongr hmap)
  have hcte : (α.ker).map (ct : ↥L →* ↥L) = α.ker := by
    rw [hker, Subgroup.map_equiv_eq_comap_symm]
    exact (CFSG.pCore_characteristic (p := 2) (G := ↥L)).fixed ct.symm
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    ((QuotientGroup.congr α.ker α.ker ct hcte).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)), fun l => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective α hα).symm (α l) =
      (l : ↥L ⧸ α.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
  rfl

theorem exists_central {L : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    ∃ x : ↥L, orderOf x = 3 ∧ α x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
      α x ≠ 1 := by
  classical
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ x : F, x ≠ 0 → x = 1 := fun x hx => by
      by_contra h
      exact hcon ⟨x, hx, h⟩
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon' x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hF] at this
    have h2 := Finset.card_insert_le (0 : F) {1}
    rw [Finset.card_singleton] at h2
    omega
  have hω3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [hF] at this
  let z₀ : Matrix.SpecialLinearGroup (Fin 3) F :=
    ⟨Matrix.scalar (Fin 3) ω, by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp
      linear_combination hω3⟩
  have hz₀ : z₀ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨ω, by simpa using hω3, rfl⟩
  have hz₀3 : orderOf z₀ = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (Matrix.scalar (Fin 3) ω) ^ 3 = 1
      rw [← map_pow, hω3, map_one]
    · intro h1
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
        (A : Matrix (Fin 3) (Fin 3) F) 0 0) h1
      simp [z₀] at this
      exact hω1 this
  obtain ⟨l₀, hl₀⟩ := hα z₀
  set N := orderOf l₀ with hN
  have hN0 : N ≠ 0 := (orderOf_pos l₀).ne'
  have h3N : 3 ∣ N := by
    have := orderOf_map_dvd α l₀
    rwa [hl₀, hz₀3] at this
  have hd0 : N / 3 ≠ 0 := by
    obtain ⟨c, hc⟩ := h3N
    omega
  refine ⟨l₀ ^ (N / 3), ?_, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hd0 (Nat.div_dvd_of_dvd h3N), Nat.div_div_self h3N hN0]
  · rw [map_pow, hl₀]
    exact Subgroup.pow_mem _ hz₀ _
  · intro h1
    have hx : l₀ ^ (N / 3) ∈ α.ker := h1
    rw [hker] at hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hx⟩
    have h2 : orderOf (l₀ ^ (N / 3)) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [orderOf_pow_of_dvd hd0 (Nat.div_dvd_of_dvd h3N), Nat.div_div_self h3N hN0] at h2
    have := Nat.prime_three.dvd_of_dvd_pow h2
    norm_num at this

theorem inf_pCoreOf_le' {K H : Subgroup G} (hKH : K ≤ H) : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  exact (le_inf Subgroup.le_normalizer
    (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem mem_normalizer_of_map_le {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem mem_pCoreOf_of_ker {L : Subgroup G} {Y : Type} [Group Y] {α : ↥L →* Y}
    (hker : α.ker = CFSG.pCore 2 ↥L) {l : ↥L} (hl : α l = 1) : (l : G) ∈ pCoreOf 2 L := by
  have h1 : l ∈ α.ker := hl
  rw [hker] at h1
  rw [pCoreOf]
  exact ⟨l, h1, rfl⟩

theorem sl3_endgame
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h14 : Stmt3_3_14) (hJ1 : FactJ1Norm3312) {F : Type} [Field F] [Fintype F]
    (hF : Nat.card F = 4) {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) (j : Fin 2)
    (hTP : T ≤ Subgroup.normalizer (liftPre α (Q3 F j) : Set G))
    (hY : liftCore α (Q3 F j) ∈ lFamilyOf L T) (hinn : InducesInnerOn T (liftCore α (Q3 F j)))
    (hO : pCoreOf 2 (liftCore α (Q3 F j) ⊔ T ⊔ D) ≠ ⊥) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (liftCore α (Q3 F j) ⊔ T ⊔ D)) (hYK : liftCore α (Q3 F j) ≤ Kc)
    (hHK : liftCore α (Q3 F j) ⊔ T ⊔ D ≤ Subgroup.normalizer (Kc : Set G))
    (hc : A312C15 (modO2Image (liftCore α (Q3 F j) ⊔ T ⊔ D) (liftCore α (Q3 F j)))
      (modO2Image (liftCore α (Q3 F j) ⊔ T ⊔ D) Kc)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := liftCore α (Q3 F j) with hYdef
  set H₁ := Y ⊔ T ⊔ D with hH₁
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hF' : Fintype.card F = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hF4 : ∃ s : Finset F, s.card = 4 := ⟨Finset.univ, by rw [Finset.card_univ, hF']⟩
  have hF4' : 4 ≤ Nat.card F := hF.ge
  have : CharP F 2 := SzN15.charP_two_of_card (m := 2) (by rw [hF]; norm_num)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    mem_normalizer_perfectCore (hTP ht)
  have hYL : Y ≤ L := liftCore_le α (Q3 F j)
  have hYH : Y ≤ H₁ := le_sup_left.trans le_sup_left
  have hTH : T ≤ H₁ := le_sup_right.trans le_sup_left
  have hDH : D ≤ H₁ := le_sup_right
  have hαY : ∀ y : ↥L, (y : G) ∈ Y → α y ∈ perfectCore (Q3 F j) := by
    intro y hy
    rw [hYdef, liftCore_eq] at hy
    obtain ⟨l, hl, hly⟩ := hy
    have : l = y := Subtype.ext hly
    rw [← this, ← map_perfectCore_comap hα]
    exact ⟨l, hl, rfl⟩
  have hαYs : ∀ z ∈ perfectCore (Q3 F j), ∃ y : ↥L, (y : G) ∈ Y ∧ α y = z := by
    intro z hz
    rw [← map_perfectCore_comap hα] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    refine ⟨l, ?_, rfl⟩
    rw [hYdef, liftCore_eq]
    exact ⟨l, hl, rfl⟩
  let αY : ↥Y →* ↥(perfectCore (Q3 F j)) :=
    (α.comp (Subgroup.inclusion hYL)).codRestrict _ (fun y => hαY _ y.2)
  have hαYv : ∀ y : ↥Y, ((αY y : ↥(perfectCore (Q3 F j))) : Matrix.SpecialLinearGroup (Fin 3) F) =
      α ⟨y, hYL y.2⟩ := fun y => rfl
  have hαYsurj : Function.Surjective αY := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hyY, rfl⟩ := hαYs z hz
    exact ⟨⟨y, hyY⟩, rfl⟩
  let g : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) F := (blk3 j).comp αY
  have hgs : Function.Surjective g := (blk3_surjective hF4 j).comp hαYsurj
  have hgO : ∀ o : ↥Y, (o : G) ∈ pCoreOf 2 Y → g o = 1 := by
    have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup hF4'
    have hW : (CFSG.pCore 2 ↥Y).map g = ⊥ := by
      have : ((CFSG.pCore 2 ↥Y).map g).Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map g hgs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Y).map g) with h1 | h1
      · exact h1
      · exfalso
        have hp : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) F) := by
          have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map g
          rw [h1] at h2
          exact h2.of_equiv Subgroup.topEquiv
        have := hp.isNilpotent
        exact CFSG.Quasithin.SL2Sylow.not_isSolvable_sl2 hF4' inferInstance
    intro o ho
    rw [pCoreOf] at ho
    obtain ⟨o', ho', hoo⟩ := ho
    have : o' = o := Subtype.ext hoo
    subst this
    have h1 : g o' ∈ (CFSG.pCore 2 ↥Y).map g := ⟨o', ho', rfl⟩
    rw [hW] at h1
    exact h1
  have hcent : ∀ (t : G) (ht : t ∈ T) (l : ↥L),
      α l ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) →
      α ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp l.2⟩ = α l := by
    intro t ht l hl
    obtain ⟨φ, hφ⟩ := exists_inducedAut hα hker (hTL ht)
    have hQle : (Q3 F j).map φ.toMonoidHom ≤ Q3 F j := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨l', rfl⟩ := hα q
      show φ (α l') ∈ Q3 F j
      rw [hφ]
      have h1 : (l' : G) ∈ liftPre α (Q3 F j) := ⟨l', hq, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTP ht) _).mp h1
      obtain ⟨l'', hl'', hl''e⟩ := h2
      have : l'' = ⟨t * l' * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l').mp l'.2⟩ :=
        Subtype.ext hl''e
      rw [← this]
      exact hl''
    have hQ : (Q3 F j).map φ.toMonoidHom = Q3 F j := by
      refine Subgroup.eq_of_le_of_card_ge hQle ?_
      rw [Subgroup.card_map_of_injective φ.injective]
    obtain ⟨y₀, hy₀, hy₀c⟩ := hinn t ht
    suffices hlevi : ∀ (x : ↥(perfectCore (Q3 F j))) (hx : φ x ∈ perfectCore (Q3 F j)),
        blk3 j ⟨φ x, hx⟩ = g ⟨y₀, hy₀⟩ * blk3 j x * (g ⟨y₀, hy₀⟩)⁻¹ by
      rw [← hφ]
      exact SL3Aut.center_fixed hF4 φ j hQ (g ⟨y₀, hy₀⟩) hlevi (α l) hl
    intro x hx
    obtain ⟨xl, hxY, hxe⟩ := hαYs x x.2
    have htx : t * (xl : G) * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY ht) _).mp hxY
    have hyx : y₀ * (xl : G) * y₀⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy₀ hxY) (Y.inv_mem hy₀)
    have h1 := hgO (⟨t * xl * t⁻¹, htx⟩ * (⟨y₀ * xl * y₀⁻¹, hyx⟩)⁻¹) (hy₀c xl hxY)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : (⟨φ x, hx⟩ : ↥(perfectCore (Q3 F j))) = αY ⟨t * xl * t⁻¹, htx⟩ := by
      apply Subtype.ext
      rw [hαYv]
      show φ (x : Matrix.SpecialLinearGroup (Fin 3) F) = _
      rw [← hxe, hφ]
    have h3 : x = αY ⟨xl, hxY⟩ := Subtype.ext (by rw [hαYv]; exact hxe.symm)
    have h4 : (⟨y₀ * xl * y₀⁻¹, hyx⟩ : ↥Y) = ⟨y₀, hy₀⟩ * ⟨xl, hxY⟩ * (⟨y₀, hy₀⟩)⁻¹ := rfl
    rw [h2, h3]
    show g ⟨t * xl * t⁻¹, htx⟩ = _
    rw [h1, h4, map_mul, map_mul, map_inv]
    rfl
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hPT : pCoreOf 2 L ≤ T := (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left
  obtain ⟨x₀, hx₀3, hx₀c, hx₀1⟩ := exists_central hF' hα hker
  set x : G := (x₀ : G) with hxdef
  have hx3 : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe, hx₀3]
  have hcT : ∀ l : ↥L, α l ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) →
      ∀ t ∈ T, (l : G) * t * (l : G)⁻¹ ∈ T := by
    intro l hl t ht
    have h1 := hcent t ht l hl
    have h2 : α (⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp l.2⟩ * l⁻¹) = 1 := by
      rw [map_mul, h1, map_inv, mul_inv_cancel]
    have h3 := hPT (mem_pCoreOf_of_ker hker h2)
    have h4 := T.mul_mem (T.inv_mem h3) ht
    convert h4 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      exact hcT x₀ hx₀c s hs
    · intro hs
      have := hcT x₀⁻¹ (by rw [map_inv]; exact inv_mem hx₀c) _ hs
      simpa [hxdef, mul_assoc] using this
  set X := Subgroup.zpowers x with hXdef
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])
  have hXT : X ≤ Subgroup.normalizer (T : Set G) := (Subgroup.zpowers_le).mpr hxT
  have hxL : x ∈ L := x₀.2
  have hXL : X ≤ L := (Subgroup.zpowers_le).mpr hxL
  have hcx : ∀ x' ∈ X, ∃ l : ↥L, (l : G) = x' ∧
      α l ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    intro x' hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    exact ⟨x₀ ^ k, by simp [hxdef], by rw [map_zpow]; exact Subgroup.zpow_mem _ hx₀c k⟩
  have hxH : x ∈ H₁ := by
    have : x ∈ T ⊔ D := by rw [← h.ND]; exact hxT
    exact (sup_le hTH hDH) this
  have hXH : X ≤ H₁ := (Subgroup.zpowers_le).mpr hxH
  have hzc : ∀ l : ↥L, α x₀ * α l = α l * α x₀ := fun l =>
    (Subgroup.mem_center_iff.mp hx₀c (α l)).symm
  have hxP : x ∈ Subgroup.normalizer (liftPre α (Q3 F j) : Set G) := by
    apply mem_normalizer_of_map_le
    rintro _ ⟨p, ⟨lp, hlp, rfl⟩, rfl⟩
    refine ⟨x₀ * lp * x₀⁻¹, ?_, rfl⟩
    show α (x₀ * lp * x₀⁻¹) ∈ Q3 F j
    rw [map_mul, map_mul, map_inv, hzc, mul_inv_cancel_right]
    exact hlp
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_perfectCore hxP
  have hxy : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 Y := by
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hxY y).mp hy) (Y.inv_mem hy)
    have hyL := hYL hy
    have h2 := mem_pCoreOf_of_ker hker (l := x₀ * ⟨y, hyL⟩ * x₀⁻¹ * (⟨y, hyL⟩ : ↥L)⁻¹) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzc, mul_inv_cancel_right, mul_inv_cancel])
    exact inf_pCoreOf_le' hYL ⟨h1, by simpa [hxdef] using h2⟩
  obtain ⟨⟨eY⟩, ⟨eK⟩⟩ := hc
  have hKH : Kc ≤ H₁ := le_of_mem_cComp hKc
  have hKn : (modO2Image H₁ Kc).Normal := L3312.modO2Image_normal hKH hHK
  let πY : ↥Y →* ↥(modO2Image H₁ Y) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H₁)).comp (Subgroup.inclusion hYH)).codRestrict _
      (fun y => ⟨⟨y, hYH y.2⟩, y.2, rfl⟩)
  have hπY : Function.Surjective πY := by
    rintro ⟨_, ⟨⟨y, hyH⟩, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hOYH : ∀ o ∈ pCoreOf 2 Y, ∀ hoH : o ∈ H₁, (⟨o, hoH⟩ : ↥H₁) ∈ CFSG.pCore 2 ↥H₁ := by
    intro o ho hoH
    set f : ↥Y →* alternatingGroup (Fin 5) := eY.toMonoidHom.comp πY with hfdef
    have hfs : Function.Surjective f := eY.surjective.comp hπY
    have hW : (CFSG.pCore 2 ↥Y).map f = ⊥ := by
      have : ((CFSG.pCore 2 ↥Y).map f).Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map f hfs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Y).map f) with h1 | h1
      · exact h1
      · exfalso
        have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map f
        rw [h1] at h2
        obtain ⟨k, hk⟩ := (h2.of_equiv Subgroup.topEquiv).exists_card_eq
        rw [card_alt 5 (by norm_num)] at hk
        have h3 : 3 ∣ 2 ^ k := by rw [← hk]; decide
        have := Nat.prime_three.dvd_of_dvd_pow h3
        norm_num at this
    rw [pCoreOf] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    have h1 : f o' ∈ (CFSG.pCore 2 ↥Y).map f := ⟨o', ho', rfl⟩
    rw [hW, Subgroup.mem_bot] at h1
    have h2 : πY o' = 1 := eY.injective (by rw [map_one]; exact h1)
    have h3 : (QuotientGroup.mk (⟨o', hoH⟩ : ↥H₁) : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = 1 :=
      congrArg Subtype.val h2
    exact (QuotientGroup.eq_one_iff _).mp h3
  let ψ : (↥H₁ ⧸ CFSG.pCore 2 ↥H₁) →* MulAut ↥(modO2Image H₁ Kc) := MulAut.conjNormal
  have hInn : (MulAut.conj : ↥(modO2Image H₁ Kc) →* MulAut ↥(modO2Image H₁ Kc)).range ≤
      ψ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, MulAut.conjNormal_val⟩
  have H3 : L3312.Hyp3312 G T M L D Y := ⟨h, hY, hO⟩
  have hS := L3312.isSylowTwoOf_map_range ψ H3.isSylowTwoOf_modO2Image_T
  have hYK' : modO2Image H₁ Y ≤ modO2Image H₁ Kc := Subgroup.map_mono fun y hy => hYK hy
  have hSB : (modO2Image H₁ T).map ψ ≤ MulAction.stabilizer (MulAut ↥(modO2Image H₁ Kc))
      ((modO2Image H₁ Y).subgroupOf (modO2Image H₁ Kc)) := by
    rintro _ ⟨tb, htb, rfl⟩
    obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb
    refine (L3312.conjNormal_mem_stabilizer_iff hYK' _).mpr ?_
    exact L3312.mk_mem_normalizer_modO2Image htX (hTY ht)
  have hB5 : IsAlt 5 ↥((modO2Image H₁ Y).subgroupOf (modO2Image H₁ Kc)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hYK').trans eY⟩
  have hJ := (hJ1 _ ⟨eK⟩ ψ.range _ _ hInn hS hB5 hSB).2
  set xb : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁ := QuotientGroup.mk ⟨x, hxH⟩ with hxbdef
  have hψx : ψ xb = 1 := by
    refine hJ (ψ xb) ⟨xb, rfl⟩ ?_ ?_
    · have hxb3 : orderOf xb ∣ 3 := by
        have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥H₁)) (⟨x, hxH⟩ : ↥H₁)
        rw [Subgroup.orderOf_mk, hx3] at this
        exact this
      have h1 : orderOf (ψ xb) ∣ 3 := (orderOf_map_dvd ψ xb).trans hxb3
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h <;> rw [h] <;> decide
    · rintro ⟨b, hbK⟩ hb
      obtain ⟨⟨y, hyH⟩, hy, hyb⟩ := hb
      have hyb' : (QuotientGroup.mk ⟨y, hyH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = b := hyb
      apply Subtype.ext
      show xb * b * xb⁻¹ = b
      rw [← hyb']
      have hc := hOYH _ (hxy y hy)
        (H₁.mul_mem (H₁.mul_mem (H₁.mul_mem hxH hyH) (H₁.inv_mem hxH)) (H₁.inv_mem hyH))
      have h2 : (QuotientGroup.mk (⟨x, hxH⟩ * ⟨y, hyH⟩ * (⟨x, hxH⟩ : ↥H₁)⁻¹ *
          (⟨y, hyH⟩ : ↥H₁)⁻¹) : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, mul_inv_eq_one] at h2
      exact h2
  have hxK : ∀ k ∈ Kc, ∀ hkH : k ∈ H₁,
      xb * QuotientGroup.mk ⟨k, hkH⟩ = QuotientGroup.mk ⟨k, hkH⟩ * xb := by
    intro k hk hkH
    have h1 := congrArg (fun φ : MulAut ↥(modO2Image H₁ Kc) =>
      ((φ ⟨QuotientGroup.mk ⟨k, hkH⟩, ⟨⟨k, hkH⟩, hk, rfl⟩⟩ : ↥(modO2Image H₁ Kc)) :
        ↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) hψx
    simp only [MulAut.one_apply] at h1
    change xb * QuotientGroup.mk ⟨k, hkH⟩ * xb⁻¹ = QuotientGroup.mk ⟨k, hkH⟩ at h1
    calc xb * QuotientGroup.mk ⟨k, hkH⟩ =
          (xb * QuotientGroup.mk ⟨k, hkH⟩ * xb⁻¹) * xb := by group
      _ = QuotientGroup.mk ⟨k, hkH⟩ * xb := by rw [h1]
  set Cb := Subgroup.centralizer ((modO2Image H₁ Kc : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) :
    Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) with hCb
  have hxC : xb ∈ Cb := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨k, hkH⟩, hk, rfl⟩
    exact (hxK k hk hkH).symm
  have hCn : Cb.Normal := Subgroup.normal_centralizer
  set Wb := modO2Image H₁ T ⊓ Cb with hWb
  have hCbN : ∀ g, g ∈ Subgroup.normalizer (Cb : Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCn]
    exact Subgroup.mem_top g
  set Nmap : Subgroup G := ((Subgroup.normalizer (Wb : Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H₁))).map H₁.subtype with hNmap
  have hYN : Y ≤ Nmap := by
    intro y hy
    refine ⟨⟨y, hYH hy⟩, ?_, rfl⟩
    show (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) ∈
      Subgroup.normalizer (Wb : Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))
    have hyK : (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) ∈ modO2Image H₁ Kc :=
      ⟨⟨y, hYH hy⟩, hYK hy, rfl⟩
    apply mem_normalizer_of_map_le
    rintro _ ⟨w, hw, rfl⟩
    have hc : (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * w =
        w * QuotientGroup.mk ⟨y, hYH hy⟩ := Subgroup.mem_centralizer_iff.mp hw.2 _ hyK
    show (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * w *
      (QuotientGroup.mk ⟨y, hYH hy⟩)⁻¹ ∈ Wb
    rw [hc, mul_inv_cancel_right]
    exact hw
  have hTDN : ∀ g ∈ T ⊔ D, g ∈ Nmap := by
    have key : ∀ g, ∀ hg : g ∈ H₁, g ∈ Subgroup.normalizer (T : Set G) →
        g ∈ Nmap := by
      intro g hg hgT
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      exact L3316.mem_normalizer_inf (L3312.mk_mem_normalizer_modO2Image hg hgT) (hCbN _)
    intro g hg
    have hgH : g ∈ H₁ := (sup_le hTH hDH) hg
    have hgN : g ∈ Subgroup.normalizer (T : Set G) := by rw [h.ND]; exact hg
    exact key g hgH hgN
  have hHN : H₁ ≤ Nmap := sup_le (sup_le hYN (fun t ht => hTDN t (Subgroup.mem_sup_left ht)))
    (fun d hd => hTDN d (Subgroup.mem_sup_right hd))
  have hWn : Wb.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro hb _
    obtain ⟨hh, rfl⟩ := QuotientGroup.mk_surjective hb
    obtain ⟨hh', hh'N, hh'e⟩ := hHN hh.2
    have : hh' = hh := Subtype.ext hh'e
    rw [← this]
    exact hh'N
  have hW2 : IsPGroup 2 ↥Wb := by
    have hT2 : IsPGroup 2 ↥(modO2Image H₁ T) :=
      (h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
    exact hT2.to_le inf_le_left
  have hWbot : Wb = ⊥ := by
    have h1 : Wb ≤ CFSG.pCore 2 (↥H₁ ⧸ CFSG.pCore 2 ↥H₁) := le_sSup ⟨hWn, hW2⟩
    rwa [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff] at h1
  have hxTc : ∀ t ∈ T, ∀ htH : t ∈ H₁,
      (QuotientGroup.mk ⟨t, htH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * xb =
        xb * QuotientGroup.mk ⟨t, htH⟩ := by
    intro t ht htH
    set tb : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁ := QuotientGroup.mk ⟨t, htH⟩
    have hcT' : tb * xb * tb⁻¹ * xb⁻¹ ∈ modO2Image H₁ T := by
      have hm : t * x * t⁻¹ * x⁻¹ ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp hxT t⁻¹).mp (T.inv_mem ht)
        have h2 := T.mul_mem ht this
        simpa [mul_assoc] using h2
      refine ⟨⟨t * x * t⁻¹ * x⁻¹, H₁.mul_mem (H₁.mul_mem (H₁.mul_mem htH hxH) (H₁.inv_mem htH))
        (H₁.inv_mem hxH)⟩, hm, ?_⟩
      rfl
    have hcC : tb * xb * tb⁻¹ * xb⁻¹ ∈ Cb :=
      Cb.mul_mem (hCn.conj_mem _ hxC tb) (Cb.inv_mem hxC)
    have h1 : tb * xb * tb⁻¹ * xb⁻¹ ∈ Wb := ⟨hcT', hcC⟩
    rw [hWbot, Subgroup.mem_bot] at h1
    have h2 : tb * xb * tb⁻¹ = xb := mul_inv_eq_one.mp h1
    calc tb * xb = (tb * xb * tb⁻¹) * tb := by group
      _ = xb * tb := by rw [h2]
  set PL := pCoreOf 2 L with hPLdef
  set R₁ := pCoreOf 2 H₁ with hR₁def
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hTsH : IsSylowTwoOf T H₁ :=
    ⟨hTH, hT2, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hR₁T : R₁ ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsH
  have hPL2 : IsPGroup 2 ↥PL := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hR₁2 : IsPGroup 2 ↥R₁ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁
  have hLPL : L ≤ Subgroup.normalizer (PL : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hHR : H₁ ≤ Subgroup.normalizer (R₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁
  have hLTPL : L ⊔ T ≤ Subgroup.normalizer (PL : Set G) :=
    sup_le hLPL (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hcL : ∀ g ∈ L, ∀ x' ∈ X, g * x' * g⁻¹ * x'⁻¹ ∈ PL := by
    intro g hg x' hx'
    obtain ⟨l, rfl, hl⟩ := hcx x' hx'
    have h1 : α (⟨g, hg⟩ * l * (⟨g, hg⟩ : ↥L)⁻¹ * l⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        (Subgroup.mem_center_iff.mp hl (α ⟨g, hg⟩)), mul_inv_cancel_right, mul_inv_cancel]
    simpa using mem_pCoreOf_of_ker hker h1
  have hcT' : ∀ t ∈ T, ∀ x' ∈ X, t * x' * t⁻¹ * x'⁻¹ ∈ PL := by
    intro t ht x' hx'
    obtain ⟨l, rfl, hl⟩ := hcx x' hx'
    have h1 := hcent t ht l hl
    have h2 : α (⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp l.2⟩ * l⁻¹) = 1 := by
      rw [map_mul, h1, map_inv, mul_inv_cancel]
    simpa using mem_pCoreOf_of_ker hker h2
  have hTXL : ⁅T, X⁆ ≤ PL := by
    rw [Subgroup.commutator_le]
    intro t ht x' hx'
    rw [commutatorElement_def]
    exact hcT' t ht x' hx'
  have hpow : ∀ g ∈ H₁, ∀ hgH : g ∈ H₁,
      (QuotientGroup.mk ⟨g, hgH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * xb = xb * QuotientGroup.mk ⟨g, hgH⟩ →
      ∀ x' ∈ X, g * x' * g⁻¹ * x'⁻¹ ∈ R₁ := by
    intro g _ hgH hgx x' hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    have hxk : x ^ k ∈ H₁ := H₁.zpow_mem hxH k
    have hc : Commute (QuotientGroup.mk ⟨g, hgH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) (xb ^ k) :=
      (Commute.zpow_right hgx k)
    have hmem : (⟨g, hgH⟩ * ⟨x, hxH⟩ ^ k * (⟨g, hgH⟩ : ↥H₁)⁻¹ * ((⟨x, hxH⟩ : ↥H₁) ^ k)⁻¹ :
        ↥H₁) ∈ CFSG.pCore 2 ↥H₁ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_zpow,
        hc.eq, mul_inv_cancel_right, mul_inv_cancel]
    rw [hR₁def, pCoreOf]
    exact ⟨_, hmem, by simp⟩
  have hTXR : ⁅T, X⁆ ≤ R₁ := by
    rw [Subgroup.commutator_le]
    intro t ht x' hx'
    rw [commutatorElement_def]
    exact hpow t (hTH ht) (hTH ht) (hxTc t ht (hTH ht)) x' hx'
  have hQL : ⁅PL, X⁆ = ⁅T, X⁆ := commutator_eq_of_le hT2 hX3 hXT hPT hTXL
  have hQR : ⁅R₁, X⁆ = ⁅T, X⁆ := commutator_eq_of_le hT2 hX3 hXT hR₁T hTXR
  have hnormPX : ∀ P : Subgroup G, ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) →
      g * x * g⁻¹ * x⁻¹ ∈ P → g ∈ Subgroup.normalizer ((P ⊔ X : Subgroup G) : Set G) := by
    intro P g hgP hgx
    apply mem_normalizer_of_map_le
    have hPg : P.map (MulAut.conj g).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgP
    rw [Subgroup.map_sup, hPg, hXdef, MonoidHom.map_zpowers]
    refine sup_le le_sup_left ((Subgroup.zpowers_le).mpr ?_)
    have h1 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    show g * x * g⁻¹ ∈ P ⊔ X
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgx)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer ((⁅T, X⁆ : Subgroup G) : Set G) := by
    have hLTN : L ⊔ T ≤ Subgroup.normalizer ((PL ⊔ X : Subgroup G) : Set G) :=
      sup_le (fun l hl => hnormPX PL l (hLPL hl) (hcL l hl x (Subgroup.mem_zpowers x)))
        (fun t ht => hnormPX PL t (hLTPL (Subgroup.mem_sup_right ht))
          (hcT' t ht x (Subgroup.mem_zpowers x)))
    intro g hg
    rw [← hQL]
    exact mem_normalizer_commutator hPL2 hX3 (hXL.trans hLPL) (hLTPL hg) (hLTN hg)
  have hKQ : Kc ≤ Subgroup.normalizer ((⁅T, X⁆ : Subgroup G) : Set G) := by
    intro k hk
    have hkH := hKH hk
    have hkx : k * x * k⁻¹ * x⁻¹ ∈ R₁ :=
      hpow k hkH hkH (hxK k hk hkH).symm x (Subgroup.mem_zpowers x)
    rw [← hQR]
    exact mem_normalizer_commutator hR₁2 hX3 (hXH.trans hHR) (hHR hkH)
      (hnormPX R₁ k (hHR hkH) hkx)
  have hQ2 : IsPGroup 2 ↥(⁅T, X⁆ : Subgroup G) := by
    refine hT2.to_le ?_
    rw [Subgroup.commutator_le]
    intro t ht x' hx'
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.mp (hXT hx') t⁻¹).mp (T.inv_mem ht)
    have h2 := T.mul_mem ht this
    simpa [mul_assoc] using h2
  have hQ1 : (⁅T, X⁆ : Subgroup G) ≠ ⊥ := by
    intro hQ
    have hcen := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQ
    have hxC' : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
      refine ⟨Subgroup.mem_sup_left hxL, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hrT : r ∈ T := (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf) hr
      exact (Subgroup.mem_centralizer_iff.mp (hcen hrT) x (Subgroup.mem_zpowers x)).symm
    have hx2 := h.toSetup331.charTwo hxC'
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨x, hx2⟩
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hx3] at h1
    have := Nat.prime_three.dvd_of_dvd_pow h1
    norm_num at this
  have hNQ := h.toSetup331.normalizer_le h38 h39 hQ1 hQ2 hLTQ
  have hKL : Kc ≤ Subgroup.normalizer (L : Set G) := (hKQ.trans hNQ).trans hMN
  have hJs : IsSimpleGroup ↥(modO2Image H₁ Kc) := by
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
      CFSG.Sporadic.J1.isSimpleGroup_J1
    have hnt : Nontrivial ↥(modO2Image H₁ Kc) := by
      rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr eK.toEquiv]
      rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560 from
        CFSG.Sporadic.J1.card_J1]
      norm_num
    exact IsSimpleGroup.isSimpleGroup_of_surjective eK.symm.toMonoidHom eK.symm.surjective
  let πK : ↥Kc →* ↥(modO2Image H₁ Kc) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H₁)).comp (Subgroup.inclusion hKH)).codRestrict _
      (fun k => ⟨⟨k, hKH k.2⟩, k.2, rfl⟩)
  have hπK : Function.Surjective πK := by
    rintro ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hKLn : ((Kc ⊓ L).subgroupOf Kc).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
      L3316.mem_normalizer_inf (Subgroup.le_normalizer hk) (hKL hk)
  have hNm : ((Kc ⊓ L).subgroupOf Kc).map πK = ⊤ := by
    have : (((Kc ⊓ L).subgroupOf Kc).map πK).Normal := hKLn.map πK hπK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Kc ⊓ L).subgroupOf Kc).map πK) with h1 | h1
    · exfalso
      obtain ⟨b, hb⟩ : ∃ b : ↥(modO2Image H₁ Y), b ≠ 1 := by
        have : Nontrivial ↥(modO2Image H₁ Y) := by
          rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr eY.toEquiv,
            card_alt 5 (by norm_num)]
          decide
        exact exists_ne 1
      obtain ⟨⟨y, hy⟩, rfl⟩ := hπY b
      have h2 : πK ⟨y, hYK hy⟩ ∈ ((Kc ⊓ L).subgroupOf Kc).map πK :=
        ⟨⟨y, hYK hy⟩, ⟨hYK hy, hYL hy⟩, rfl⟩
      rw [h1, Subgroup.mem_bot] at h2
      apply hb
      have h3 : ((πY ⟨y, hy⟩ : ↥(modO2Image H₁ Y)) : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = 1 :=
        congrArg Subtype.val h2
      exact Subtype.ext h3
    · exact h1
  have hdvd : 175560 ∣ Nat.card ↥L := by
    have h1 := Subgroup.card_map_dvd ((Kc ⊓ L).subgroupOf Kc) πK
    rw [hNm, Subgroup.card_top, Nat.card_congr eK.toEquiv,
      show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560 from
        CFSG.Sporadic.J1.card_J1] at h1
    have h2 : Nat.card ↥((Kc ⊓ L).subgroupOf Kc) = Nat.card ↥(Kc ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2] at h1
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hcardL : Nat.card ↥L = Nat.card ↥α.ker * 60480 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      Matrix.card_SL_field, hF'] at h1
    rw [h1]
    norm_num [Fin.prod_univ_three]
    ring
  obtain ⟨a, ha⟩ : ∃ a, Nat.card ↥α.ker = 2 ^ a := by
    rw [hker]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hcardL, ha] at hdvd
  have h19 : 19 ∣ 2 ^ a * 60480 := (by norm_num : 19 ∣ 175560).trans hdvd
  have hcop : Nat.Coprime 19 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h19
  norm_num at this

theorem step3_3_16SL3_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h10 : Stmt3_3_10)
    (h14 : Stmt3_3_14) (h15 : Step3_3_15RB) (hJ1 : FactJ1Norm3312) : Step3_3_16SL3 := by
  intro G _ _ T M L D h n K _ _ hn hK ⟨e⟩ ⟨F, _, _, α, hF, hα⟩
  obtain ⟨α₂, j, Kc, hα₂, hker, hF4, hTP, hY, hinn, hO, hKc, hYK, hHK, hc⟩ :=
    sl3_config h h38 h39 h51 h10 h14 h15 hn hK e hF hα
  exact sl3_endgame h h38 h39 h14 hJ1 hF4 hα₂ hker j hTP hY hinn hO hKc hYK hHK hc

end L3316

end CFSG.Quasithin.H13
