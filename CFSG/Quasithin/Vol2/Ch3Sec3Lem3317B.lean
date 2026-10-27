module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317A
public import CFSG.Goldschmidt.Steps.Sec87d

public section

namespace CFSG.Quasithin.H13.L3317

open CFSG.Open (pCoreOf)
open CFSG.Quasithin CFSG.SectionRank.Ccomm

section Abstract

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem commHom_sq_apply (hW2 : ∀ w : W, w * w = 1) (c : MulAut W) (w : W) :
    commHom (c ^ 2) w = commHom c (commHom c w) := by
  have h1 : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hW2 x)
  simp only [commHom_apply, map_mul, map_inv, sq, MulAut.mul_apply, mul_inv_rev, inv_inv]
  calc c (c w) * w⁻¹ = c (c w) * ((c w)⁻¹ * (c w)⁻¹) * w := by
        rw [h1 (c w), hW2 (c w), mul_one, h1 w]
    _ = _ := by ac_rfl

omit [Finite W] in
theorem commHom_four_apply (hW2 : ∀ w : W, w * w = 1) (c : MulAut W) (w : W) :
    commHom (c ^ 4) w = commHom c (commHom c (commHom c (commHom c w))) := by
  rw [show c ^ 4 = (c ^ 2) ^ 2 by rw [← pow_mul], commHom_sq_apply hW2 (c ^ 2),
    commHom_sq_apply hW2 c, commHom_sq_apply hW2 c]

omit [Finite W] in
theorem range_inf_ker_ne_bot (hW2 : ∀ w : W, w * w = 1) {c : MulAut W} (hc1 : c ≠ 1)
    (hc4 : c ^ 4 = 1) : (commHom c).range ⊓ (commHom c).ker ≠ ⊥ := by
  intro hbot
  have hinj : ∀ x ∈ (commHom c).range, commHom c x = 1 → x = 1 := by
    intro x hx h1
    have hx' : x ∈ (commHom c).range ⊓ (commHom c).ker := ⟨hx, h1⟩
    rw [hbot] at hx'
    exact hx'
  obtain ⟨w, hw⟩ : ∃ w, commHom c w ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hc1
    ext w
    have := hall w
    rw [commHom_apply, mul_inv_eq_one] at this
    exact this
  have h2 : commHom c (commHom c w) ≠ 1 := fun h => hw (hinj _ ⟨w, rfl⟩ h)
  have h3 : commHom c (commHom c (commHom c w)) ≠ 1 := fun h => h2 (hinj _ ⟨_, rfl⟩ h)
  have h4 : commHom c (commHom c (commHom c (commHom c w))) ≠ 1 := fun h =>
    h3 (hinj _ ⟨_, rfl⟩ h)
  apply h4
  rw [← commHom_four_apply hW2, hc4, commHom_apply, MulAut.one_apply, mul_inv_cancel]

theorem card_eq_two_pow_rk_of_le (hW2 : ∀ w : W, w * w = 1) (X : Subgroup W) :
    Nat.card X = 2 ^ rk X :=
  card_eq_two_pow_rk fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, sq, OneMemClass.coe_one]
    exact hW2 _)

theorem one_le_rk_of_ne_bot (hW2 : ∀ w : W, w * w = 1) {X : Subgroup W} (hX : X ≠ ⊥) :
    1 ≤ rk X := by
  by_contra h0
  push Not at h0
  have h1 : Nat.card X = 1 := by
    rw [card_eq_two_pow_rk_of_le hW2 X, show rk X = 0 by omega, pow_zero]
  exact hX (Subgroup.eq_bot_of_card_eq X h1)

theorem card_fixV_le_two (hW2 : ∀ w : W, w * w = 1)
    (hW : Nat.card W = 2 ^ 4) {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {c : MulAut W}
    (hcΓ : c ∈ Γ) (hc2 : c ^ 2 ≠ 1) (hc4 : c ^ 4 = 1) :
    Nat.card (fixV (Subgroup.zpowers c)) ≤ 2 := by
  have hrkW : rk W = 4 := by
    rw [rk, hW]
    exact padicValNat.prime_pow 4
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, one_pow])
  set φ := commHom c with hφ
  have hR : commV (Subgroup.zpowers c) = φ.range := by
    rw [commV_zpowers_eq_map, MonoidHom.range_eq_map]
  have hR2 : commV (Subgroup.zpowers (c ^ 2)) = φ.range.map φ := by
    rw [commV_zpowers_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    congr 1
    ext w
    exact commHom_sq_apply hW2 c w
  have hA := rk_commV_add_rk_fixV c
  have hB := rk_commV_add_rk_fixV (c ^ 2)
  have hC := rk_map_add_rk_inf_ker φ φ.range
  have hD : 1 ≤ rk ↥(φ.range ⊓ φ.ker) :=
    one_le_rk_of_ne_bot hW2 (range_inf_ker_ne_bot hW2 hc1 hc4)
  have hinv : c ^ 2 * c ^ 2 = 1 := by rw [← pow_add, hc4]
  have hfix2 := CFSG.Quasithin.H13.A7.card_fixV_le_four_of_inv hW2 hW hΓ
    (Γ.pow_mem hcΓ 2) hinv hc2
  rw [card_eq_two_pow_rk_of_le hW2] at hfix2
  have hk2 : rk (fixV (Subgroup.zpowers (c ^ 2))) ≤ 2 := by
    by_contra hk
    push Not at hk
    have : 2 ^ 3 ≤ 2 ^ rk (fixV (Subgroup.zpowers (c ^ 2))) :=
      Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [hR] at hA
  rw [hR2] at hB
  have hk1 : rk (fixV (Subgroup.zpowers c)) ≤ 1 := by omega
  rw [card_eq_two_pow_rk_of_le hW2]
  calc 2 ^ rk (fixV (Subgroup.zpowers c)) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

end Abstract

section GL3

theorem nonempty_GL3_equiv_PSL3 :
    Nonempty (GL (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1)) := by
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [ZMod.card, Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
  let φ : ZMod 2 ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e₃.symm.trans (e₂.symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3)))⟩

theorem card_hopfMultiplier_GL3 :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (GL (Fin 3) (ZMod 2))) = 2 := by
  obtain ⟨e⟩ := nonempty_GL3_equiv_PSL3
  rw [card_hopfMultiplier_congr e, card_hopfMultiplier_psl32]

theorem isPSL_three_two_of_GL3 {X : Type} [Group X] (e : X ≃* GL (Fin 3) (ZMod 2)) :
    IsPSL 3 2 1 X :=
  CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two
    (e.trans (MulEquiv.ofBijective _
      CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two).symm)

variable {W : Type*} [CommGroup W] [Finite W]

theorem nonempty_fourStab_equiv_GL3 (hW2 : ∀ w : W, w * w = 1)
    (hW : Nat.card W = 2 ^ 4) {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W}
    (hz : z ≠ 1) : Nonempty (CFSG.Quasithin.H13.A7.fourStab Γ z ≃* GL (Fin 3) (ZMod 2)) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 z) hz
  have hQ : Nat.card (W ⧸ Subgroup.zpowers z) = 2 ^ 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
    rw [hW, Nat.card_zpowers, hz2] at this
    norm_num at this ⊢
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (W := W ⧸ Subgroup.zpowers z) (p := 2)
    (fun a b => mul_comm a b) (fun a => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
      rw [← QuotientGroup.mk_pow, sq, hW2, QuotientGroup.mk_one]) hQ
  have hcardA : Nat.card (MulAut (W ⧸ Subgroup.zpowers z)) = 168 := by
    rw [card_mulAut_eq_card_GL e, Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
    norm_num
  have hbij : Function.Bijective (CFSG.Quasithin.H13.A7.fourStabQuot Γ z) :=
    (CFSG.Quasithin.H13.A7.fourStabQuot_injective hW2 hW hΓ).bijective_of_nat_card_le
      (by rw [hcardA, CFSG.Quasithin.H13.A7.card_fourStab hW hΓ hz])
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (elemAutEquivGL e)⟩

end GL3

theorem exists_sq_ne_one_of_card_eight {X : Subgroup (alternatingGroup (Fin 7))}
    (hX : Nat.card X = 8) : ∃ σ ∈ X, σ ^ 2 ≠ 1 ∧ σ ^ 4 = 1 := by
  have hx : ∃ x ∈ X, x ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsq : ∀ x ∈ X, x * x = 1 := fun x hx => by rw [← sq]; exact hall x hx
    have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
      intro x hx y hy
      have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
      have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
      have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hsq _ (X.mul_mem hx hy))
      rw [← hxy, _root_.mul_inv_rev, hx', hy']
    have hel : CFSG.Open.IsElemAbelian 2 X :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => hall x hx⟩
    have hk : Nat.card X = 2 ^ 3 := by rw [hX]; norm_num
    have h3 := (CFSG.SectionRank.le_pRank (by norm_num) le_top hel hk).trans
      CFSG.GH74.SmallRanks.twoRank_alternatingGroup_seven_le_two
    omega
  obtain ⟨x, hxX, hx2⟩ := hx
  have hx8 : x ^ 8 = 1 := by
    have := pow_card_eq_one' (G := X) (x := ⟨x, hxX⟩)
    rw [hX] at this
    exact congrArg Subtype.val this
  by_cases hx4 : x ^ 4 = 1
  · exact ⟨x, hxX, hx2, hx4⟩
  · refine ⟨x ^ 2, X.pow_mem hxX 2, ?_, ?_⟩
    · rwa [← pow_mul]
    · rw [← pow_mul]
      exact hx8


section Setting

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem isMulCommutative_commV (h : Hyp331 G T M L D) : IsMulCommutative ↥⁅vPlus L T, L⁆ := by
  obtain ⟨-, hV, -⟩ := Hyp331.vPlus_reduced h.toSetup331
  have hWV := commV_le_vPlus h
  have hc : ∀ x ∈ vPlus L T, ∀ y ∈ vPlus L T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact hc a (hWV a.2) b (hWV b.2)

theorem mul_self_commV (h : Hyp331 G T M L D) (w : ↥⁅vPlus L T, L⁆) : w * w = 1 := by
  obtain ⟨-, hV, -⟩ := Hyp331.vPlus_reduced h.toSetup331
  apply Subtype.ext
  have := hV.2 w (commV_le_vPlus h w.2)
  rw [sq] at this
  exact this

theorem commV_le_T (h : Hyp331 G T M L D) : ⁅vPlus L T, L⁆ ≤ T :=
  (commV_le_vPlus h).trans ((Hyp331.vPlus_reduced h.toSetup331).1.trans
    (inf_le_left.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right))))

theorem card_autOn_commV (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L) :
    Nat.card ↥(autOn L ⁅vPlus L T, L⁆) = 2520 := by
  rw [Nat.card_congr (autOnEquiv (le_normalizer_vPlus h) (le_normalizer_commV h)
    (inf_centralizer_commV h hML)).toEquiv, Nat.card_congr e.toEquiv,
    CFSG.Quasithin.H.A7.card_A7]

theorem actL_commV_eq_one_iff (h : Hyp331 G T M L D) (hML : mPlus L T = L) (l : ↥L) :
    actL L ⁅vPlus L T, L⁆ (le_normalizer_commV h) l = 1 ↔
      actL L (vPlus L T) (le_normalizer_vPlus h) l = 1 := by
  rw [actL_eq_one_iff, actL_eq_one_iff]
  have hC := Subgroup.ext_iff.1 (inf_centralizer_commV h hML) l
  exact ⟨fun hl => (hC.1 ⟨l.2, hl⟩).2, fun hl => (hC.2 ⟨l.2, hl⟩).2⟩

theorem two_pow_eq_eight {k m : ℕ} (h : 2 ^ k * m = 2520) (hm : ¬ 2 ∣ m) : 2 ^ k = 8 := by
  have hk : k ≤ 3 := by
    by_contra hk
    push Not at hk
    have h16 : (16 : ℕ) ∣ 2520 := by
      have h1 : (16 : ℕ) ∣ 2 ^ k := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
        exact Nat.pow_dvd_pow 2 hk
      exact h1.trans (Dvd.intro m h)
    norm_num at h16
  interval_cases k
  · norm_num at h
    omega
  · norm_num at h
    omega
  · norm_num at h
    omega
  · norm_num

theorem isSylowTwoOf_inf (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsSylowTwoOf (T ⊓ L) L := by
  refine ⟨inf_le_right, h.sylow.1.to_le inf_le_left, ?_⟩
  have h1 := B6.relIndex_inf_eq_relIndex_sup hTL
  have h2 := (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow (le_sup_left : T ≤ T ⊔ L)).2.2
  show ¬ 2 ∣ (T ⊓ L).relIndex L
  rw [h1]
  exact h2

theorem exists_mem_T_order_four (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ t : ↥L, (t : G) ∈ T ∧ (actL L ⁅vPlus L T, L⁆ (le_normalizer_commV h) t) ^ 2 ≠ 1 ∧
      (actL L ⁅vPlus L T, L⁆ (le_normalizer_commV h) t) ^ 4 = 1 := by
  have hLV := le_normalizer_vPlus h
  set φ := actA7 hLV e with hφ
  have hTLs := isSylowTwoOf_inf h hTL
  set X := ((T ⊓ L).subgroupOf L).map φ with hX
  have hX8 : Nat.card X = 8 := by
    have hP : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
      hTLs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (hP.map φ)
    have hmul := X.card_mul_index
    rw [hk, CFSG.Quasithin.H.A7.card_A7] at hmul
    have hidx : ¬ 2 ∣ X.index := fun h2 =>
      hTLs.2.2 (h2.trans (Subgroup.index_map_dvd _ (actA7_surjective hLV e)))
    rw [hk]
    exact two_pow_eq_eight hmul hidx
  obtain ⟨σ, hσX, hσ2, hσ4⟩ := exists_sq_ne_one_of_card_eight hX8
  obtain ⟨t, htT, rfl⟩ := hσX
  refine ⟨t, (Subgroup.mem_subgroupOf.1 htT).1, ?_, ?_⟩
  · intro h2
    apply hσ2
    have h2' : actL L (vPlus L T) hLV (t ^ 2) = 1 := by
      rw [← actL_commV_eq_one_iff h hML, map_pow]
      exact h2
    rw [← map_pow]
    simp only [hφ, actA7, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      h2', map_one]
  · have h4 : φ (t ^ 4) = 1 := by rw [map_pow]; exact hσ4
    have h4' : actL L (vPlus L T) hLV (t ^ 4) = 1 := by
      simpa only [hφ, actA7, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.map_eq_one_iff] using h4
    rw [← map_pow, actL_commV_eq_one_iff h hML]
    exact h4'

omit [Finite G] in
theorem omegaOneCenter_le (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hx => (Subgroup.mem_inf.1 hx.1).1

theorem exists_Z_inf_commV (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hc4 : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4) :
    ∃ z₀ ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆, z₀ ≠ 1 ∧
      ∀ z ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆, z = 1 ∨ z = z₀ := by
  have := isMulCommutative_commV h
  have hLW := le_normalizer_commV h
  set W := ⁅vPlus L T, L⁆ with hW
  obtain ⟨t, htT, ht2, ht4⟩ := exists_mem_T_order_four h e hML hTL
  set c := actL L W hLW t with hc
  have hc2 : (c : MulAut ↥W) ^ 2 ≠ 1 := fun h2 => ht2 (Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact h2))
  have hc4' : (c : MulAut ↥W) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, ht4]
    rfl
  have hfix := card_fixV_le_two (mul_self_commV h) hc4 (card_autOn_commV h e hML) c.2 hc2 hc4'
  have hfixZ : ∀ (z : G) (hz : z ∈ quasithinOmegaOneCenter T ⊓ W),
      (⟨z, (Subgroup.mem_inf.1 hz).2⟩ : ↥W) ∈ fixV (Subgroup.zpowers (c : MulAut ↥W)) := by
    intro z hz
    rw [mem_fixV_zpowers_iff]
    apply Subtype.ext
    rw [hc, actL]
    show (t : G) * z * (t : G)⁻¹ = z
    have := Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T htT) z
      (Subgroup.mem_inf.1 hz).1
    rw [← this, mul_inv_cancel_right]
  have hW1 : W ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hc4
    norm_num at hc4
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (CFSG.Goldschmidt.Sec8.inf_center_ne_bot' h.sylow.1 (commV_le_T h)
      (T_le_normalizer_commV hTL) hW1)
  have hz₀1' : z₀ ≠ 1 := fun h1 => hz₀1 (Subtype.ext h1)
  obtain ⟨hz₀W, hz₀C⟩ := Subgroup.mem_inf.1 hz₀
  have hz₀Z : z₀ ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨hz₀C, ?_⟩
    rw [sq]
    exact congrArg Subtype.val (mul_self_commV h ⟨z₀, hz₀W⟩)
  refine ⟨z₀, Subgroup.mem_inf.2 ⟨hz₀Z, hz₀W⟩, hz₀1', fun z hz => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hz1, hzz₀⟩ := hne
  classical
  set F := fixV (Subgroup.zpowers (c : MulAut ↥W)) with hF
  set w₀ : ↥F := ⟨_, hfixZ z₀ (Subgroup.mem_inf.2 ⟨hz₀Z, hz₀W⟩)⟩ with hw₀
  set w : ↥F := ⟨_, hfixZ z hz⟩ with hw
  have hw₀1 : w₀ ≠ 1 := fun h1 => hz₀1' (congrArg (fun x : ↥F => ((x : ↥W) : G)) h1)
  have hw1 : w ≠ 1 := fun h1 => hz1 (congrArg (fun x : ↥F => ((x : ↥W) : G)) h1)
  have hww₀ : w₀ ≠ w := fun h1 => hzz₀ (congrArg (fun x : ↥F => ((x : ↥W) : G)) h1).symm
  let := Fintype.ofFinite ↥F
  have hcard : ({1, w₀, w} : Finset ↥F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hww₀]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hw₀1.symm, hw1.symm⟩
  have h3 := Finset.card_le_univ ({1, w₀, w} : Finset ↥F)
  rw [hcard, ← Nat.card_eq_fintype_card] at h3
  have := h3.trans hfix
  norm_num at this

theorem inf_centralizer_Z_eq (h : Hyp331 G T M L D) (hML : mPlus L T = L) {z₀ : G}
    (hz₀ : z₀ ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆)
    (huniq : ∀ z ∈ quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆, z = 1 ∨ z = z₀) :
    L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
      L ⊓ Subgroup.centralizer ({z₀} : Set G) := by
  have h9 := stmt3_3_9_of G T M L D h
  rw [hML] at h9
  rw [h9]
  congr 1
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact hx z₀ hz₀
  · intro hx y hy
    rcases huniq y hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hx y rfl

abbrev mOne (L T : Subgroup G) : Subgroup G :=
  perfectCore (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))

omit [Finite G] in
theorem mOne_le (L T : Subgroup G) : mOne L T ≤ L :=
  (perfectCore_le _).trans inf_le_left

theorem mOne_perfect (L T : Subgroup G) : ⁅mOne L T, mOne L T⁆ = mOne L T :=
  perfectCore_perfect _

omit [Finite G] in
theorem mOne_le_centralizer (L T : Subgroup G) :
    mOne L T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  (perfectCore_le _).trans inf_le_right

theorem T_le_normalizer_mOne (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer (mOne L T : Set G) := fun _ ht =>
  L3316.mem_normalizer_perfectCore (CFSG.Quasithin.A4.mem_normalizer_inf (hTL ht)
    (Subgroup.le_normalizer (L246C127.le_centralizer_omegaOneCenter T ht)))

theorem pCoreOf_mOne_ne_bot (h : Hyp331 G T M L D) {z₀ : G}
    (hz₀ : z₀ ∈ quasithinOmegaOneCenter T) (hz₀1 : z₀ ≠ 1) :
    pCoreOf 2 (mOne L T ⊔ T ⊔ D) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZT := omegaOneCenter_le T
  have hNZ := normalizer_le_normalizer_quasithinOmegaOneCenter T
  have hle : quasithinOmegaOneCenter T ≤ pCoreOf 2 (mOne L T ⊔ T ⊔ D) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hZT.trans (le_sup_right.trans le_sup_left)) ?_ (h.sylow.1.to_le hZT)
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (mOne_le_centralizer L T).trans (Subgroup.centralizer_le_normalizer _)
    · exact Subgroup.le_normalizer.trans hNZ
    · exact h.DN.trans hNZ
  intro hb
  rw [hb, le_bot_iff] at hle
  exact hz₀1 (by rw [← Subgroup.mem_bot, ← hle]; exact hz₀)

theorem mOne_facts
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hc4 : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4) :
    mOne L T ∈ lFamilyOf L T ∧ L3312.Type3312R (↥(mOne L T) ⧸ CFSG.pCore 2 ↥(mOne L T)) ∧
      ¬ IsPSL 2 2 2 (↥(mOne L T) ⧸ CFSG.pCore 2 ↥(mOne L T)) ∧
      pCoreOf 2 (mOne L T ⊔ T ⊔ D) ≠ ⊥ ∧
      Nat.card ↥(autOn (mOne L T) ⁅vPlus L T, L⁆) = 168 := by
  have := isMulCommutative_commV h
  have hLW := le_normalizer_commV h
  set W := ⁅vPlus L T, L⁆ with hW
  obtain ⟨z₀, hz₀, hz₀1, huniq⟩ := exists_Z_inf_commV h e hML hTL hc4
  obtain ⟨hz₀Z, hz₀W⟩ := Subgroup.mem_inf.1 hz₀
  have hΓ := card_autOn_commV h e hML
  have hW2 := mul_self_commV h
  have hz₀1' : (⟨z₀, hz₀W⟩ : ↥W) ≠ 1 := fun h1 => hz₀1 (congrArg Subtype.val h1)
  have hCZ := inf_centralizer_Z_eq h hML hz₀ huniq
  have hXW : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (W : Set G) := inf_le_left.trans hLW
  have hM₁W : mOne L T ≤ Subgroup.normalizer (W : Set G) := (perfectCore_le _).trans hXW
  have haut : autOn (mOne L T) W = A7.fourStab (autOn L W) ⟨z₀, hz₀W⟩ := by
    show autOn (perfectCore (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) W = _
    rw [A7.autOn_perfectCore_eq hXW, hCZ, A7.autOn_inf_centralizer_eq hLW hz₀W,
      perfectCore_eq_self_of_perfect (A7.commutator_fourStab hW2 hc4 hΓ hz₀1')]
  obtain ⟨eGL⟩ := nonempty_fourStab_equiv_GL3 hW2 hc4 hΓ hz₀1'
  have h2S : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      ↥(A7.fourStab (autOn L W) ⟨z₀, hz₀W⟩)) = 2 := by
    rw [card_hopfMultiplier_congr eGL, card_hopfMultiplier_GL3]
  have := A7.isSimpleGroup_fourStab hW2 hc4 hΓ hz₀1'
  have hnc := A7.fourStab_noncomm hW2 hc4 hΓ hz₀1'
  set f : ↥(mOne L T) →* ↥(A7.fourStab (autOn L W) ⟨z₀, hz₀W⟩) :=
    (MulEquiv.subgroupCongr haut).toMonoidHom.comp (actL (mOne L T) W hM₁W) with hf
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr haut).surjective.comp (actL_surjective hM₁W)
  have hfk : ∀ y : ↥(mOne L T), f y = 1 ↔ (y : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    intro y
    have hyL : (y : G) ∈ L := mOne_le L T y.2
    have hC := Subgroup.ext_iff.1 (inf_centralizer_commV h hML) y
    simp only [hf, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.map_eq_one_iff, actL_eq_one_iff]
    exact ⟨fun hy => (hC.1 ⟨hyL, hy⟩).2, fun hy => (hC.2 ⟨hyL, hy⟩).2⟩
  obtain ⟨hmem, ⟨eQ⟩⟩ := mem_lFamilyOf_of_hopf h e (mOne_le L T) (mOne_perfect L T)
    (T_le_normalizer_mOne hTL) hnc h2S f hfs hfk
  have hcQ : Nat.card (↥(mOne L T) ⧸ CFSG.pCore 2 ↥(mOne L T)) = 168 := by
    rw [Nat.card_congr eQ.toEquiv, A7.card_fourStab hc4 hΓ hz₀1']
  refine ⟨hmem, Or.inr (Or.inl (isPSL_three_two_of_GL3 (eQ.trans eGL))), fun hP => ?_,
    pCoreOf_mOne_ne_bot h hz₀Z hz₀1, ?_⟩
  · have := GoldS146R.card_isPSL_two_two hP
    rw [hcQ] at this
    norm_num at this
  · rw [haut]
    exact A7.card_fourStab hc4 hΓ hz₀1'

end Setting

end CFSG.Quasithin.H13.L3317
