module

public import CFSG.Quasithin.Background.HA7Rec
public import CFSG.Quasithin.Background.HA7Mod
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.SectionRank.Ccomm Subgroup
open scoped Matrix commutatorElement

theorem isSimpleGroup_GL_three_two_four : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

theorem isPGroup_zpowers_four {H : Type*} [Group H] {p : ℕ} {g : H} (hg : g ^ p = 1) :
    IsPGroup p (zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

section Abstract

variable {W : Type*} [CommGroup W] [Finite W]

theorem fixV_zpowers_eq_bot_five_four (hW : Nat.card W = 2 ^ 4) {g : MulAut W} (h5 : g ^ 5 = 1)
    (h1 : g ≠ 1) : fixV (zpowers g) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := card_modEq_card_fixV (isPGroup_zpowers_four h5)
  have hdvd : Nat.card (fixV (zpowers g)) ∣ 2 ^ 4 := hW ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne : k ≠ 4 := by
    rintro rfl
    exact h1 (eq_one_of_fixV_eq_top (Subgroup.eq_top_of_card_eq _ (hk'.trans hW.symm)))
  rw [hW, hk'] at hmod
  rw [← Subgroup.card_eq_one, hk']
  interval_cases k
  · rfl
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact absurd rfl hne

theorem card_fixV_zpowers_seven_four (hW : Nat.card W = 2 ^ 4) {g : MulAut W} (h7 : g ^ 7 = 1)
    (h1 : g ≠ 1) : Nat.card (fixV (zpowers g)) = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := card_modEq_card_fixV (isPGroup_zpowers_four h7)
  have hdvd : Nat.card (fixV (zpowers g)) ∣ 2 ^ 4 := hW ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne : k ≠ 4 := by
    rintro rfl
    exact h1 (eq_one_of_fixV_eq_top (Subgroup.eq_top_of_card_eq _ (hk'.trans hW.symm)))
  rw [hW, hk'] at hmod
  rw [hk']
  interval_cases k
  · exact absurd hmod (by decide)
  · rfl
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact absurd rfl hne

theorem card_set_modEq_card_fixed_four {p : ℕ} [Fact p.Prime] {Y : Subgroup (MulAut W)}
    (hY : IsPGroup p Y) (S : Set W) (hS : ∀ g ∈ Y, ∀ w ∈ S, g w ∈ S) :
    Nat.card S ≡ Nat.card {w : W // w ∈ S ∧ w ∈ fixV Y} [MOD p] := by
  classical
  let s : SubMulAction Y W :=
    { carrier := S
      smul_mem' := fun g v hv => hS g g.2 v hv }
  have h1 := hY.card_modEq_card_fixedPoints s
  have e1 : Nat.card s = Nat.card S := rfl
  have e2 : Nat.card (MulAction.fixedPoints Y s) =
      Nat.card {w : W // w ∈ S ∧ w ∈ fixV Y} := by
    refine Nat.card_congr
      { toFun := fun ω => ⟨(ω.1 : W), ω.1.2, fun g hg => congrArg Subtype.val (ω.2 ⟨g, hg⟩)⟩
        invFun := fun u => ⟨⟨(u : W), u.2.1⟩, fun g => Subtype.ext (u.2.2 g g.2)⟩
        left_inv := fun ω => rfl
        right_inv := fun u => rfl }
  rw [e1, e2] at h1
  exact h1

theorem exists_apply_eq_four (hW : Nat.card W = 2 ^ 4) {Γ : Subgroup (MulAut W)}
    (hΓ : Nat.card Γ = 2520) {v w : W} (hv : v ≠ 1) (hw : w ≠ 1) : ∃ γ ∈ Γ, γ v = w := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 5 (by rw [hΓ]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 7 (by rw [hΓ]; norm_num)
  have ha' : orderOf (a : MulAut W) = 5 := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : MulAut W) = 7 := by rw [Subgroup.orderOf_coe]; exact hb
  have hF5 : fixV (zpowers (a : MulAut W)) = ⊥ :=
    fixV_zpowers_eq_bot_five_four hW (ha' ▸ pow_orderOf_eq_one _) fun h => by
      rw [h, orderOf_one] at ha'
      norm_num at ha'
  have hF7 : Nat.card (fixV (zpowers (b : MulAut W))) = 2 :=
    card_fixV_zpowers_seven_four hW (hb' ▸ pow_orderOf_eq_one _) fun h => by
      rw [h, orderOf_one] at hb'
      norm_num at hb'
  obtain ⟨⟨f, hf⟩, hf1, huniq⟩ := (Nat.card_eq_two_iff' (1 : fixV (zpowers (b : MulAut W)))).1 hF7
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have huniq' : ∀ u ∈ fixV (zpowers (b : MulAut W)), u ≠ 1 → u = f := fun u hu hu1 =>
    congrArg Subtype.val (huniq ⟨u, hu⟩ fun h => hu1 (congrArg Subtype.val h))
  set O : Set W := {u | ∃ γ ∈ Γ, γ f = u} with hO
  have hOinv : ∀ g ∈ Γ, ∀ u ∈ O, g u ∈ O := by
    rintro g hg _ ⟨γ, hγ, rfl⟩
    exact ⟨g * γ, Γ.mul_mem hg hγ, rfl⟩
  have hO1 : ∀ u ∈ O, u ≠ 1 := by
    rintro _ ⟨γ, -, rfl⟩ h
    exact hf1' ((map_eq_one_iff γ γ.injective).1 h)
  have hfO : f ∈ O := ⟨1, Γ.one_mem, rfl⟩
  have hY5 : zpowers (a : MulAut W) ≤ Γ := zpowers_le.2 a.2
  have hY7 : zpowers (b : MulAut W) ≤ Γ := zpowers_le.2 b.2
  have hc5 := card_set_modEq_card_fixed_four (isPGroup_zpowers_four (p := 5)
    (ha' ▸ pow_orderOf_eq_one _)) O fun g hg => hOinv g (hY5 hg)
  have hc7 := card_set_modEq_card_fixed_four (isPGroup_zpowers_four (p := 7)
    (hb' ▸ pow_orderOf_eq_one _)) O fun g hg => hOinv g (hY7 hg)
  have hfix5 : Nat.card {u : W // u ∈ O ∧ u ∈ fixV (zpowers (a : MulAut W))} = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨u, huO, hu⟩
    rw [hF5, mem_bot] at hu
    exact hO1 u huO hu
  have hfix7 : Nat.card {u : W // u ∈ O ∧ u ∈ fixV (zpowers (b : MulAut W))} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨f, hfO, hf⟩⟩⟩
    rw [huniq' _ x.2.2 (hO1 _ x.2.1), huniq' _ y.2.2 (hO1 _ y.2.1)]
  rw [hfix5] at hc5
  rw [hfix7] at hc7
  have hle : O ⊆ ({1}ᶜ : Set W) := fun u hu => hO1 u hu
  have hcompl : ({1}ᶜ : Set W).ncard = 15 := by
    rw [Set.ncard_compl, Set.ncard_singleton, hW]
    norm_num
  have hOle : O.ncard ≤ 15 := hcompl ▸ Set.ncard_le_ncard hle
  have hO15 : O.ncard = 15 := by
    rw [Nat.card_coe_set_eq] at hc5 hc7
    unfold Nat.ModEq at hc5 hc7
    omega
  have hOeq : O = {1}ᶜ := Set.eq_of_subset_of_ncard_le hle (by rw [hcompl, hO15])
  have hvO : v ∈ O := hOeq ▸ hv
  have hwO : w ∈ O := hOeq ▸ hw
  obtain ⟨γ₁, hγ₁, rfl⟩ := hvO
  obtain ⟨γ₂, hγ₂, rfl⟩ := hwO
  refine ⟨γ₂ * γ₁⁻¹, Γ.mul_mem hγ₂ (Γ.inv_mem hγ₁), ?_⟩
  change γ₂ (γ₁.symm (γ₁ f)) = γ₂ f
  rw [MulEquiv.symm_apply_apply]

theorem exists_coord_four (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) :
    ∃ (e : W ≃* Multiplicative (Fin 4 → ZMod 2))
      (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)),
      Γ.map (elemAutEquivGL e).toMonoidHom = CFSG.Quasithin.H.A7.Γ α := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (W := W) (p := 2)
    (fun a b => mul_comm a b) (fun a => by rw [sq]; exact hW2 a) hW
  have hcard : Nat.card (Γ.map (elemAutEquivGL e).toMonoidHom) = 2520 := by
    rw [Subgroup.card_map_of_injective (elemAutEquivGL e).injective, hΓ]
  have h8 : (Γ.map (elemAutEquivGL e).toMonoidHom).index = 8 := by
    have := (Γ.map (elemAutEquivGL e).toMonoidHom).index_mul_card
    rw [CFSG.Quasithin.H.A7.card_GL_four, hcard] at this
    omega
  obtain ⟨α, hα⟩ := CFSG.Quasithin.H.A7.exists_alpha_of_index h8
  refine ⟨e, α, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
  · rintro _ ⟨σ, rfl⟩
    exact hα σ
  · rw [hcard, CFSG.Quasithin.H.A7.card_Γ]

omit [Finite W] in
theorem card_fixV_eq_card_fix_mat {n : ℕ} (e : W ≃* Multiplicative (Fin n → ZMod 2))
    (t : MulAut W) : Nat.card (fixV (zpowers t)) = Fintype.card {v : Fin n → ZMod 2 //
      ((elemAutEquivGL e t : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v =
        v} := by
  classical
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd (e w.1), by
        rw [elemAutEquivGL_mulVec, mem_fixV_zpowers_iff.1 w.2]⟩
      invFun := fun v => ⟨e.symm (Multiplicative.ofAdd v.1), mem_fixV_zpowers_iff.2 (by
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [← elemAutEquivGL_mulVec, MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact v.2)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun v => by ext; simp }

theorem card_fixV_le_four_of_inv
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {t : MulAut W} (htΓ : t ∈ Γ)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : Nat.card (fixV (zpowers t)) ≤ 4 := by
  obtain ⟨e, α, hΓα⟩ := exists_coord_four hW2 hW hΓ
  have hmem : elemAutEquivGL e t ∈ CFSG.Quasithin.H.A7.Γ α := by
    rw [← hΓα, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact htΓ
  have hγ2 : (⟨elemAutEquivGL e t, hmem⟩ : CFSG.Quasithin.H.A7.Γ α) * ⟨elemAutEquivGL e t, hmem⟩ =
      1 := Subtype.ext (by
    change elemAutEquivGL e t * elemAutEquivGL e t = 1
    rw [← map_mul, ht2, map_one])
  have hγ1 : (⟨elemAutEquivGL e t, hmem⟩ : CFSG.Quasithin.H.A7.Γ α) ≠ 1 := fun h =>
    ht1 ((elemAutEquivGL e).injective (by rw [map_one]; exact congrArg Subtype.val h))
  rw [card_fixV_eq_card_fix_mat e]
  convert CFSG.Quasithin.H.A7.card_fix_le_four α hγ2 hγ1 using 2

theorem mem_of_mem_normalizer_four (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {x : MulAut W}
    (hx : x ∈ normalizer (Γ : Set (MulAut W))) : x ∈ Γ := by
  obtain ⟨e, α, hΓα⟩ := exists_coord_four hW2 hW hΓ
  have hmemρ : ∀ y : MulAut W,
      elemAutEquivGL e y ∈ Γ.map (elemAutEquivGL e).toMonoidHom ↔ y ∈ Γ := fun y => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hρx : elemAutEquivGL e x ∈
      normalizer (CFSG.Quasithin.H.A7.Γ α : Set (GL (Fin 4) (ZMod 2))) := by
    rw [mem_normalizer_iff]
    intro g
    obtain ⟨h, rfl⟩ := (elemAutEquivGL e).surjective g
    rw [← hΓα, ← map_inv, ← map_mul, ← map_mul, hmemρ, hmemρ]
    exact mem_normalizer_iff.1 hx h
  rw [CFSG.Quasithin.H.A7.normalizer_eq α, ← hΓα, hmemρ] at hρx
  exact hρx

omit [Finite W] in
abbrev fourStab (Γ : Subgroup (MulAut W)) (z : W) : Subgroup (MulAut W) :=
  Γ ⊓ MulAction.stabilizer (MulAut W) z

theorem card_fourStab (hW : Nat.card W = 2 ^ 4) {Γ : Subgroup (MulAut W)}
    (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) : Nat.card (fourStab Γ z) = 168 := by
  classical
  have horb : MulAction.orbit Γ z = ({1}ᶜ : Set W) := by
    ext u
    constructor
    · rintro ⟨γ, rfl⟩ h
      exact hz ((map_eq_one_iff (γ : MulAut W) (γ : MulAut W).injective).1 h)
    · intro hu
      obtain ⟨γ, hγ, rfl⟩ := exists_apply_eq_four hW hΓ hz hu
      exact ⟨⟨γ, hγ⟩, rfl⟩
  have hidx := MulAction.index_stabilizer Γ z
  rw [horb, Set.ncard_compl, Set.ncard_singleton, hW] at hidx
  norm_num at hidx
  have h1 := (MulAction.stabilizer Γ z).index_mul_card
  rw [hidx, hΓ] at h1
  have e : MulAction.stabilizer Γ z ≃ fourStab Γ z :=
    { toFun := fun g => ⟨(g : Γ), (g : Γ).2, g.2⟩
      invFun := fun g => ⟨⟨g, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e]
  omega

omit [Finite W] in
@[expose] noncomputable def fourStabQuot (Γ : Subgroup (MulAut W)) (z : W) :
    fourStab Γ z →* MulAut (W ⧸ zpowers z) where
  toFun γ := QuotientGroup.congr (zpowers z) (zpowers z) (γ : MulAut W) (by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers γ.2.2)
  map_one' := by
    ext x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' a b := by
    ext x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

omit [Finite W] in
theorem fourStabQuot_mk {Γ : Subgroup (MulAut W)} {z : W} (γ : fourStab Γ z) (w : W) :
    fourStabQuot Γ z γ (QuotientGroup.mk w) = QuotientGroup.mk ((γ : MulAut W) w) := rfl

theorem fourStabQuot_injective
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} :
    Function.Injective (fourStabQuot Γ z) := by
  have hW16 : Nat.card W = 16 := by rw [hW]; norm_num
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hgz : (γ : MulAut W) z = z := γ.2.2
  have hd : ∀ w : W, commHom (γ : MulAut W) w ∈ zpowers z := by
    intro w
    have h1 : (QuotientGroup.mk ((γ : MulAut W) w) : W ⧸ zpowers z) = QuotientGroup.mk w := by
      rw [← fourStabQuot_mk, hγ, MulAut.one_apply]
    rw [QuotientGroup.eq] at h1
    have h2 := (zpowers z).inv_mem h1
    rw [mul_inv_rev, inv_inv] at h2
    rw [commHom_apply, mul_comm]
    exact h2
  have hfixz : ∀ d ∈ zpowers z, (γ : MulAut W) d = d := by
    intro d hd
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
    rw [map_zpow, hgz]
  have hg2 : (γ : MulAut W) * γ = 1 := by
    ext w
    rw [MulAut.mul_apply, MulAut.one_apply]
    have hgw : (γ : MulAut W) w = commHom (γ : MulAut W) w * w := by
      rw [commHom_apply, inv_mul_cancel_right]
    calc (γ : MulAut W) ((γ : MulAut W) w)
        = (γ : MulAut W) (commHom (γ : MulAut W) w * w) := by rw [← hgw]
      _ = commHom (γ : MulAut W) w * (commHom (γ : MulAut W) w * w) := by
          rw [map_mul, hfixz _ (hd w), ← hgw]
      _ = w := by rw [← mul_assoc, hW2, one_mul]
  have hcard : 8 ≤ Nat.card (fixV (zpowers (γ : MulAut W))) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commHom (γ : MulAut W)).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, ker_commHom, hW16] at h1
    have h2 : Nat.card (commHom (γ : MulAut W)).range ≤ Nat.card (zpowers z) :=
      Subgroup.card_le_of_le (by rintro _ ⟨w, rfl⟩; exact hd w)
    have h3 : Nat.card (zpowers z) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hW2 z))
    have h4 := Nat.mul_le_mul_right (Nat.card (fixV (zpowers (γ : MulAut W)))) (h2.trans h3)
    have h5 := h1.le.trans h4
    omega
  by_contra hne
  have hg1 : (γ : MulAut W) ≠ 1 := fun h => hne (Subtype.ext h)
  have := card_fixV_le_four_of_inv hW2 hW hΓ γ.2.1 hg2 hg1
  omega

theorem isSimpleGroup_fourStab
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) :
    IsSimpleGroup (fourStab Γ z) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 z) hz
  have hQ : Nat.card (W ⧸ zpowers z) = 2 ^ 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers z)
    rw [hW, Nat.card_zpowers, hz2] at this
    norm_num at this ⊢
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary (W := W ⧸ zpowers z) (p := 2)
    (fun a b => mul_comm a b) (fun a => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
      rw [← QuotientGroup.mk_pow, sq, hW2, QuotientGroup.mk_one]) hQ
  have hcardA : Nat.card (MulAut (W ⧸ zpowers z)) = 168 := by
    rw [card_mulAut_eq_card_GL e, Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
    norm_num
  have hbij : Function.Bijective (fourStabQuot Γ z) :=
    (fourStabQuot_injective hW2 hW hΓ).bijective_of_nat_card_le
      (by rw [hcardA, card_fourStab hW hΓ hz])
  have := isSimpleGroup_GL_three_two_four
  exact ((MulEquiv.ofBijective _ hbij).trans (elemAutEquivGL e)).isSimpleGroup

theorem fourStab_noncomm
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) :
    ∃ a b : fourStab Γ z, a * b ≠ b * a := by
  have := isSimpleGroup_fourStab hW2 hW hΓ hz
  have hS := card_fourStab hW hΓ hz
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fourStab Γ z) 7 (by rw [hS]; norm_num)
  have hN : (zpowers x).Normal := ⟨fun n hn g => by rw [h g n, mul_inv_cancel_right]; exact hn⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (zpowers x) with h1 | h1
  · have hx1 : x = 1 := by rw [← mem_bot, ← h1]; exact mem_zpowers x
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · have h2 := Nat.card_zpowers x
    rw [h1, card_top, hS, hx] at h2
    norm_num at h2

theorem commutator_fourStab
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) :
    ⁅fourStab Γ z, fourStab Γ z⁆ = fourStab Γ z := by
  have := isSimpleGroup_fourStab hW2 hW hΓ hz
  obtain ⟨x, y, hxy⟩ := fourStab_noncomm hW2 hW hΓ hz
  have hcomm : commutator ↥(fourStab Γ z) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(fourStab Γ z)) with h | h
    · exfalso
      apply hxy
      have hmem : ⁅x, y⁆ ∈ commutator ↥(fourStab Γ z) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hcomm)

theorem oTwoUpper_fourStab
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) :
    oTwoUpper (fourStab Γ z) = fourStab Γ z := by
  have := isSimpleGroup_fourStab hW2 hW hΓ hz
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN : ((oTwoUpper (fourStab Γ z)).subgroupOf (fourStab Γ z)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).2 (le_normalizer_oTwoUpper _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fourStab Γ z) 7
    (by rw [card_fourStab hW hΓ hz]; norm_num)
  have hxO : (x : MulAut W) ∈ oTwoUpper (fourStab Γ z) :=
    mem_oTwoUpper_of_odd x.2 (by rw [Subgroup.orderOf_coe, hx]; decide)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((oTwoUpper (fourStab Γ z)).subgroupOf (fourStab Γ z))
    with h | h
  · exfalso
    have hx' : x ∈ (oTwoUpper (fourStab Γ z)).subgroupOf (fourStab Γ z) := hxO
    rw [h, mem_bot] at hx'
    rw [hx', orderOf_one] at hx
    norm_num at hx
  · refine le_antisymm (oTwoUpper_le _) fun y hy => ?_
    have hy' : (⟨y, hy⟩ : fourStab Γ z) ∈ (oTwoUpper (fourStab Γ z)).subgroupOf (fourStab Γ z) :=
      h ▸ mem_top _
    exact hy'

theorem pCoreOf_fourStab
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) :
    pCoreOf 2 (fourStab Γ z) = ⊥ := by
  have := isSimpleGroup_fourStab hW2 hW hΓ hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : pCoreOf 2 (fourStab Γ z) ≤ fourStab Γ z := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hN : ((pCoreOf 2 (fourStab Γ z)).subgroupOf (fourStab Γ z)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPS).2 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((pCoreOf 2 (fourStab Γ z)).subgroupOf (fourStab Γ z))
    with h | h
  · rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hPS hy⟩ : fourStab Γ z) ∈ (pCoreOf 2 (fourStab Γ z)).subgroupOf
        (fourStab Γ z) := hy
    rw [h, mem_bot] at hy'
    exact (mem_bot).2 (congrArg Subtype.val hy')
  · exfalso
    have hSP : fourStab Γ z ≤ pCoreOf 2 (fourStab Γ z) := fun y hy => by
      have hy' : (⟨y, hy⟩ : fourStab Γ z) ∈ (pCoreOf 2 (fourStab Γ z)).subgroupOf
          (fourStab Γ z) := h ▸ mem_top _
      exact hy'
    have hS2 : IsPGroup 2 (fourStab Γ z) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hSP
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS2
    rw [card_fourStab hW hΓ hz] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

omit [Finite W] in
theorem range_commHom_le_commV {X : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ X) :
    (commHom g).range ≤ commV X := by
  rintro _ ⟨w, rfl⟩
  exact subset_closure ⟨g, hg, w, rfl⟩

omit [Finite W] in
theorem commHom_eq_one_of_fixed_seven (hW2 : ∀ w : W, w * w = 1) {g : MulAut W}
    (hg : g ^ 7 = 1) (w : W) (hfix : g (commHom g w) = commHom g w) : commHom g w = 1 := by
  have hgw : g w = commHom g w * w := by rw [commHom_apply, inv_mul_cancel_right]
  have key : ∀ k : ℕ, (g ^ k) w = commHom g w ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, hgw, pow_succ, mul_assoc]
  have h7 := key 7
  rw [hg, MulAut.one_apply] at h7
  have hy7 : commHom g w ^ 7 = 1 := by
    have := congrArg (· * w⁻¹) h7
    simp only [mul_inv_cancel, mul_inv_cancel_right] at this
    exact this.symm
  have hy2 : commHom g w ^ 2 = 1 := by rw [sq]; exact hW2 _
  calc commHom g w = commHom g w ^ 7 := by
        rw [show 7 = 2 * 3 + 1 from rfl, pow_succ, pow_mul, hy2, one_pow, one_mul]
    _ = 1 := hy7

omit [Finite W] in
theorem commHom_mem_fixV_of_inv (hW2 : ∀ w : W, w * w = 1) {t : MulAut W} (ht : t * t = 1)
    (w : W) : commHom t w ∈ fixV (zpowers t) := by
  have h1 : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hW2 x)
  rw [mem_fixV_zpowers_iff, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, ht,
    MulAut.one_apply, h1 ((t : MulAut W) w), h1 w, mul_comm]

theorem commV_fourStab_eq_top
    (hW2 : ∀ w : W, w * w = 1) (hW : Nat.card W = 2 ^ 4)
    {Γ : Subgroup (MulAut W)} (hΓ : Nat.card Γ = 2520) {z : W} (hz : z ≠ 1) :
    commV (fourStab Γ z) = ⊤ := by
  have hS := card_fourStab hW hΓ hz
  have hW16 : Nat.card W = 16 := by rw [hW]; norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := fourStab Γ z) 7 (by rw [hS]; norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fourStab Γ z) 2 (by rw [hS]; norm_num)
  have ha' : orderOf (a : MulAut W) = 7 := by rw [Subgroup.orderOf_coe]; exact ha
  have ht' : orderOf (t : MulAut W) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hg7 : (a : MulAut W) ^ 7 = 1 := ha' ▸ pow_orderOf_eq_one _
  have hg1 : (a : MulAut W) ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha'
    norm_num at ha'
  have ht2 : (t : MulAut W) * t = 1 := by rw [← sq, ← ht']; exact pow_orderOf_eq_one _
  have ht1 : (t : MulAut W) ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht'
    norm_num at ht'
  have hF := card_fixV_zpowers_seven_four hW hg7 hg1
  have hδ : Nat.card (commHom (a : MulAut W)).range = 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commHom (a : MulAut W)).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, ker_commHom, hF, hW16]
      at h1
    omega
  have hzδ : z ∉ (commHom (a : MulAut W)).range := by
    rintro ⟨w, hw⟩
    have hfix : (a : MulAut W) (commHom (a : MulAut W) w) = commHom (a : MulAut W) w := by
      rw [hw]
      exact a.2.2
    exact hz (hw ▸ commHom_eq_one_of_fixed_seven hW2 hg7 w hfix)
  have hzt : z ∈ (commHom (t : MulAut W)).range := by
    have hle : (commHom (t : MulAut W)).range ≤ fixV (zpowers (t : MulAut W)) := by
      rintro _ ⟨w, rfl⟩
      exact commHom_mem_fixV_of_inv hW2 ht2 w
    have h4 := card_fixV_le_four_of_inv hW2 hW hΓ t.2.1 ht2 ht1
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commHom (t : MulAut W)).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, ker_commHom, hW16] at h1
    have h5 := h1.le.trans (Nat.mul_le_mul_left (Nat.card (commHom (t : MulAut W)).range) h4)
    have heq : (commHom (t : MulAut W)).range = fixV (zpowers (t : MulAut W)) :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq, mem_fixV_zpowers_iff]
    exact t.2.2
  have hδC := range_commHom_le_commV (X := fourStab Γ z) a.2
  have hzC : z ∈ commV (fourStab Γ z) := range_commHom_le_commV (X := fourStab Γ z) t.2 hzt
  have hdvd : Nat.card (commV (fourStab Γ z)) ∣ 2 ^ 4 := hW ▸ Subgroup.card_subgroup_dvd_card _
  have h8 : 8 ∣ Nat.card (commV (fourStab Γ z)) := hδ ▸ Subgroup.card_dvd_of_le hδC
  have hne : Nat.card (commV (fourStab Γ z)) ≠ 8 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hδC (by rw [h, hδ])
    exact hzδ (this ▸ hzC)
  apply Subgroup.eq_top_of_card_eq
  rw [hW]
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk'] at h8 hne ⊢
  interval_cases k
  · exact absurd h8 (by decide)
  · exact absurd h8 (by decide)
  · exact absurd h8 (by decide)
  · exact absurd (by norm_num) hne
  · rfl

end Abstract

end CFSG.Quasithin.H13.A7
