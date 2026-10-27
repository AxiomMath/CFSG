module

public import CFSG.Quasithin.H13.L32NSet14Idx

public section

namespace CFSG.Quasithin.H13.U3P33

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

abbrev nX (W W₁ : Subgroup G) : Subgroup G :=
  normalizer (W : Set G) ⊓ normalizer (W₁ : Set G)

theorem exists_rep [Finite G] {W W₁ : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) :
    ∃ ψ : ↥(nX W W₁) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub W W₁ := by
  classical
  obtain ⟨hcomm, hsq⟩ := hW
  let _ := zmodModuleOf (V := W) hsq
  have : Module.Finite (ZMod 2) (Additive ↥W) := Module.Finite.of_finite
  set W₁' := subOf (V := W) W₁ with hW₁'
  have : Finite (Additive ↥W ⧸ W₁') :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective W₁')
  have hdimV : Module.finrank (ZMod 2) (Additive ↥W) = 3 := by
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥W)
    rw [Nat.card_zmod] at h2
    have h3 : Nat.card (Additive ↥W) = 2 ^ 3 := hc
    rw [h3] at h2
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hdimW : Module.finrank (ZMod 2) W₁' = 1 := finrank_subOf h1 (by rw [hc1]; rfl)
  have hdimQ : Module.finrank (ZMod 2) (Additive ↥W ⧸ W₁') = 2 := by
    have := Submodule.finrank_quotient_add_finrank W₁'
    omega
  obtain ⟨eQ⟩ := nonempty_linearEquiv_mulEquiv_sl hdimQ
  have hXV : nX W W₁ ≤ normalizer (W : Set G) := inf_le_left
  let σ : ↥(nX W W₁) →* (Additive ↥W ≃ₗ[ZMod 2] Additive ↥W) :=
    linHom.comp ((conjAct W).comp (Subgroup.inclusion hXV))
  have hσ : ∀ (x : ↥(nX W W₁)) (v : Additive ↥W), ((Additive.toMul (σ x v) : ↥W) : G) =
      (x : G) * ((Additive.toMul v : ↥W) : G) * (x : G)⁻¹ := fun x v => rfl
  have hσle : ∀ x : ↥(nX W W₁), W₁'.map (σ x : Additive ↥W →ₗ[ZMod 2] Additive ↥W) ≤ W₁' := by
    rintro x _ ⟨w, hw, rfl⟩
    have hw' : ((w.toMul : ↥W) : G) ∈ W₁ := mem_subOf.1 hw
    show (σ x : Additive ↥W →ₗ[ZMod 2] Additive ↥W) w ∈ subOf (V := W) W₁
    rw [mem_subOf, show ((σ x : Additive ↥W →ₗ[ZMod 2] Additive ↥W) w) = σ x w from rfl, hσ]
    exact (Subgroup.mem_normalizer_iff.1 x.2.2 _).1 hw'
  have hσW : ∀ x : ↥(nX W W₁), W₁'.map (σ x : Additive ↥W →ₗ[ZMod 2] Additive ↥W) = W₁' := by
    intro x
    refine le_antisymm (hσle x) fun w hw => ?_
    refine ⟨σ x⁻¹ w, hσle x⁻¹ ⟨w, hw, rfl⟩, ?_⟩
    show σ x (σ x⁻¹ w) = w
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  let ρX : ↥(nX W W₁) →* ((Additive ↥W ⧸ W₁') ≃ₗ[ZMod 2] (Additive ↥W ⧸ W₁')) :=
    { toFun := fun x => Submodule.Quotient.equiv W₁' W₁' (σ x) (hσW x)
      map_one' := by
        apply LinearEquiv.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁' q
        simp [map_one]
      map_mul' := fun x y => by
        apply LinearEquiv.ext
        intro q
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁' q
        simp [map_mul] }
  have hρX : ∀ (x : ↥(nX W W₁)) (v : Additive ↥W),
      ρX x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (σ x v) := fun x v => rfl
  refine ⟨eQ.toMonoidHom.comp ρX, fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  constructor
  · intro hx
    refine ⟨x.2.1, x.2.2, fun v hv => ?_⟩
    have h2 := LinearEquiv.congr_fun hx (Submodule.Quotient.mk (Additive.ofMul (⟨v, hv⟩ : ↥W)))
    rw [hρX, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq, hW₁', mem_subOf] at h2
    have e1 : ((Additive.toMul (σ x (Additive.ofMul ⟨v, hv⟩) - Additive.ofMul ⟨v, hv⟩) :
        ↥W) : G) = (x : G) * v * (x : G)⁻¹ * v⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, hσ, div_eq_mul_inv]
      rfl
    rw [← e1]
    exact h2
  · intro hx
    apply LinearEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W₁' q
    rw [hρX, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq, hW₁', mem_subOf]
    have e1 : ((Additive.toMul (σ x v - v) : ↥W) : G) =
        (x : G) * ((Additive.toMul v : ↥W) : G) * (x : G)⁻¹ *
          ((Additive.toMul v : ↥W) : G)⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, hσ, div_eq_mul_inv]
    rw [e1]
    exact hx.2.2 _ (Additive.toMul v).2

theorem sq_mem_centralizer [Finite G] {W W₁ : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) {g : G} (hg : g ∈ L32NSet14.trivSub W W₁) :
    g ^ 2 ∈ centralizer (W : Set G) := by
  obtain ⟨-, hg1, hg⟩ := hg
  rw [mem_centralizer_iff]
  intro v hv
  set d := g * v * g⁻¹ * v⁻¹ with hddef
  have hd : d ∈ W₁ := hg v hv
  have hgd : g * d = d * g :=
    mem_centralizer_iff.mp (le_centralizer_normalizer_of_card_eq_two hc1 hd) g hg1
  have hdd : d * d = 1 := by
    rw [← pow_two]
    exact hW.2 d (h1 hd)
  have e2 : g * v * g⁻¹ = d * v := by rw [hddef]; group
  have e3 : g * d * g⁻¹ = d := by rw [hgd]; group
  have e4 : g ^ 2 * v * (g ^ 2)⁻¹ = v := by
    calc g ^ 2 * v * (g ^ 2)⁻¹ = (g * d * g⁻¹) * (g * v * g⁻¹) := by rw [hddef, pow_two]; group
      _ = d * (d * v) := by rw [e3, e2]
      _ = v := by rw [← mul_assoc, hdd, one_mul]
  calc v * g ^ 2 = (g ^ 2 * v * (g ^ 2)⁻¹) * g ^ 2 := by rw [e4]
    _ = g ^ 2 * v := by group

theorem le_pCoreOf [Finite G] {W W₁ H : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hHX : H ≤ nX W W₁)
    (hC : IsPGroup 2 ↥(H ⊓ centralizer (W : Set G))) :
    H ⊓ L32NSet14.trivSub W W₁ ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun h hh => ?_) ?_
  · refine Subgroup.mem_normalizer_fintype fun g hg => ⟨H.mul_mem (H.mul_mem hh hg.1)
      (H.inv_mem hh), ?_⟩
    exact L32NSet14.conj_mem_trivSub (hHX hh).1 (hHX hh).2 hg.2
  · rintro ⟨g, hg⟩
    have hmem : g ^ 2 ∈ H ⊓ centralizer (W : Set G) :=
      ⟨H.pow_mem hg.1 2, sq_mem_centralizer hW hc1 h1 hg.2⟩
    obtain ⟨k, hk⟩ := hC ⟨_, hmem⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
    rw [pow_succ', pow_mul]
    exact h2

theorem cube_eq_one {W W₁ Y : Subgroup G} (hY : Y ≤ nX W W₁)
    (ψ : ↥(nX W W₁) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) {g : G}
    (hg : g ∈ oTwoRes Y) (hgX : g ∈ nX W W₁) : ψ ⟨g, hgX⟩ ^ 3 = 1 := by
  have hLX : oTwoRes Y ≤ nX W W₁ := (oTwoRes_le Y).trans hY
  have key : ψ ⟨g, hLX hg⟩ ^ 3 = 1 := by
    refine Subgroup.closure_induction
      (k := {x | x ∈ Y ∧ ∃ m : ℕ, Odd m ∧ x ^ m = 1})
      (p := fun g hg => ψ ⟨g, hLX hg⟩ ^ 3 = 1) ?_ ?_ ?_ ?_ hg
    · intro g hg'
      obtain ⟨-, m, hm, hgm⟩ := id hg'
      refine L32NSet14.sl2_cube_of_odd hm ?_
      rw [← map_pow]
      have : (⟨g, hLX (subset_closure hg')⟩ : ↥(nX W W₁)) ^ m = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hgm)
      rw [this, map_one]
    · show ψ 1 ^ 3 = 1
      rw [map_one, one_pow]
    · intro g g' hg hg' ih ih'
      show ψ (⟨g, hLX hg⟩ * ⟨g', hLX hg'⟩) ^ 3 = 1
      rw [map_mul]
      exact L32NSet14.sl2_cube_mul _ _ ih ih'
    · intro g hg ih
      show ψ (⟨g, hLX hg⟩)⁻¹ ^ 3 = 1
      rw [map_inv, inv_pow, ih, inv_one]
  exact key

theorem pCoreOf_le_trivSub [Finite G] {W W₁ Y : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hY : Y ≤ nX W W₁) :
    pCoreOf 2 (oTwoRes Y) ≤ L32NSet14.trivSub W W₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := exists_rep hW hc hc1 h1
  have hLX : oTwoRes Y ≤ nX W W₁ := (oTwoRes_le Y).trans hY
  intro q hq
  have hqL : q ∈ oTwoRes Y := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoRes Y)) ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow] at this
  have h3 := cube_eq_one hY ψ hqL (hLX hqL)
  have h2 : ψ ⟨q, hLX hqL⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨q, hLX hqL⟩ : ↥(nX W W₁)) ^ 2 ^ k = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hk')
    rw [this, map_one]
  have ho : orderOf (ψ ⟨q, hLX hqL⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
      (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  exact (hψ _).mp (orderOf_eq_one_iff.mp ho)

theorem commutator_mem_pCoreOf [Finite G] {W W₁ Y : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hY : Y ≤ nX W W₁)
    (hC : IsPGroup 2 ↥(oTwoRes Y ⊓ centralizer (W : Set G))) {a b : G} (ha : a ∈ oTwoRes Y)
    (hb : b ∈ oTwoRes Y) : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (oTwoRes Y) := by
  obtain ⟨ψ, hψ⟩ := exists_rep hW hc hc1 h1
  have hLX : oTwoRes Y ≤ nX W W₁ := (oTwoRes_le Y).trans hY
  have hk : a * b * a⁻¹ * b⁻¹ ∈ oTwoRes Y :=
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine le_pCoreOf hW hc1 h1 hLX hC ⟨hk, (hψ ⟨_, hLX hk⟩).mp ?_⟩
  have e : (⟨a * b * a⁻¹ * b⁻¹, hLX hk⟩ : ↥(nX W W₁)) = ⟨a, hLX ha⟩ * ⟨b, hLX hb⟩ *
      (⟨a, hLX ha⟩ : ↥(nX W W₁))⁻¹ * (⟨b, hLX hb⟩ : ↥(nX W W₁))⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
    L32NSet14.sl2_cube_comm _ _ (cube_eq_one hY ψ ha (hLX ha)) (cube_eq_one hY ψ hb (hLX hb))]
  group

theorem relIndex_eq_three [Finite G] {W W₁ Y : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hY : Y ≤ nX W W₁)
    (hC : IsPGroup 2 ↥(oTwoRes Y ⊓ centralizer (W : Set G))) {c : G} (hcY : c ∈ oTwoRes Y)
    (hcn : c ∉ L32NSet14.trivSub W W₁) :
    (pCoreOf 2 (oTwoRes Y)).relIndex (oTwoRes Y) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ, hψ⟩ := exists_rep hW hc hc1 h1
  have hLX : oTwoRes Y ≤ nX W W₁ := (oTwoRes_le Y).trans hY
  set φ : ↥(oTwoRes Y) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ψ.comp (Subgroup.inclusion hLX) with hφ
  have hφ_apply : ∀ y : ↥(oTwoRes Y), φ y = ψ ⟨y, hLX y.2⟩ := fun y => rfl
  have hker : φ.ker = (pCoreOf 2 (oTwoRes Y)).subgroupOf (oTwoRes Y) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ_apply, hψ]
    constructor
    · intro h
      exact le_pCoreOf hW hc1 h1 hLX hC ⟨y.2, h⟩
    · intro h
      exact pCoreOf_le_trivSub hW hc hc1 h1 hY h
  have hrange : Nat.card φ.range = 3 := by
    have hp3 : IsPGroup 3 φ.range := by
      rintro ⟨s, hs⟩
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hs
      exact ⟨1, Subtype.ext (by
        show φ y ^ 3 ^ 1 = 1
        rw [pow_one, hφ_apply]
        exact cube_eq_one hY ψ y.2 _)⟩
    obtain ⟨k, hk⟩ := hp3.exists_card_eq
    have hdvd : Nat.card φ.range ∣ 6 :=
      L32NSet14.card_sl2 ▸ Subgroup.card_subgroup_dvd_card φ.range
    have hφc : φ ⟨c, hcY⟩ ≠ 1 := by
      rw [hφ_apply, Ne, hψ]
      exact hcn
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      have : φ ⟨c, hcY⟩ ∈ φ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rw [hk, Subgroup.mem_bot] at this
      exact hφc this
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      rw [hk] at hdvd
      exact absurd ((Nat.pow_dvd_pow 3 h).trans hdvd) (by decide)
    obtain rfl : k = 1 := by omega
    rw [hk, pow_one]
  rw [show (pCoreOf 2 (oTwoRes Y)).relIndex (oTwoRes Y) =
      ((pCoreOf 2 (oTwoRes Y)).subgroupOf (oTwoRes Y)).index from rfl,
    ← hker, Subgroup.index_ker, hrange]

theorem pCoreOf_sup_le_trivSub [Finite G] {W W₁ Y T : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hY : Y ≤ nX W W₁)
    (hT : T ≤ nX W W₁) {c : G} (hcY : c ∈ oTwoRes Y) (hcn : c ∉ L32NSet14.trivSub W W₁) :
    pCoreOf 2 (oTwoRes Y ⊔ T) ≤ L32NSet14.trivSub W W₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := exists_rep hW hc hc1 h1
  have hLX : oTwoRes Y ≤ nX W W₁ := (oTwoRes_le Y).trans hY
  have hHX : oTwoRes Y ⊔ T ≤ nX W W₁ := sup_le hLX hT
  have hψc : ψ ⟨c, hLX hcY⟩ ≠ 1 := by
    rw [Ne, hψ]
    exact hcn
  have h2el : ∀ q (hq : q ∈ pCoreOf 2 (oTwoRes Y ⊔ T)),
      ψ ⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ ^ 2 = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (oTwoRes Y ⊔ T)) ⟨q, hq⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ : ↥(nX W W₁)) ^ 2 ^ k = 1 :=
      Subtype.ext (by
        have := congrArg Subtype.val hk
        rw [Subgroup.coe_pow] at this ⊢
        exact this)
    rw [this, map_one]
  intro q hq
  have hq' : c * q * c⁻¹ ∈ pCoreOf 2 (oTwoRes Y ⊔ T) :=
    (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (mem_sup_left hcY)) q).mp hq
  have hqq := h2el _ (mul_mem hq hq')
  have e : (⟨q * (c * q * c⁻¹), hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _
      (mul_mem hq hq'))⟩ : ↥(nX W W₁)) = ⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ *
        (⟨c, hLX hcY⟩ * ⟨q, hHX (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq)⟩ *
          (⟨c, hLX hcY⟩ : ↥(nX W W₁))⁻¹) := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv] at hqq
  exact (hψ _).mp (L32NSet14.sl2_eq_one_of_conj _ _ (cube_eq_one hY ψ hcY (hLX hcY)) hψc
    (h2el q hq) hqq)

theorem relIndex_le_two [Finite G] {W W₁ Y T : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hY : Y ≤ nX W W₁)
    (hT : T ≤ nX W W₁) (hT2 : IsPGroup 2 T)
    (hC : IsPGroup 2 ↥((oTwoRes Y ⊔ T) ⊓ centralizer (W : Set G))) :
    (pCoreOf 2 (oTwoRes Y ⊔ T)).relIndex T ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := exists_rep hW hc hc1 h1
  have hHX : oTwoRes Y ⊔ T ≤ nX W W₁ := sup_le ((oTwoRes_le Y).trans hY) hT
  set φ : ↥T →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    ψ.comp (Subgroup.inclusion hT) with hφ
  have hφ_apply : ∀ t : ↥T, φ t = ψ ⟨t, hT t.2⟩ := fun t => rfl
  have hker : φ.ker ≤ (pCoreOf 2 (oTwoRes Y ⊔ T)).subgroupOf T := by
    intro t ht
    rw [MonoidHom.mem_ker, hφ_apply, hψ] at ht
    exact Subgroup.mem_subgroupOf.mpr
      (le_pCoreOf hW hc1 h1 hHX hC ⟨Subgroup.mem_sup_right t.2, ht⟩)
  have hrange : Nat.card φ.range ≤ 2 := by
    have hp2 : IsPGroup 2 φ.range := by
      rintro ⟨s, hs⟩
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hs
      obtain ⟨k, hk⟩ := hT2 t
      exact ⟨k, Subtype.ext (by
        show φ t ^ 2 ^ k = 1
        rw [← map_pow, hk, map_one])⟩
    obtain ⟨j, hj⟩ := hp2.exists_card_eq
    have hdvd : Nat.card φ.range ∣ 6 :=
      L32NSet14.card_sl2 ▸ Subgroup.card_subgroup_dvd_card φ.range
    rw [hj] at hdvd ⊢
    have hj2 : j < 2 := by
      by_contra h
      push Not at h
      exact absurd ((Nat.pow_dvd_pow 2 h).trans hdvd) (by decide)
    interval_cases j <;> norm_num
  calc (pCoreOf 2 (oTwoRes Y ⊔ T)).relIndex T =
      ((pCoreOf 2 (oTwoRes Y ⊔ T)).subgroupOf T).index := rfl
    _ ≤ φ.ker.index := Subgroup.index_antitone hker
    _ = Nat.card φ.range := Subgroup.index_ker φ
    _ ≤ 2 := hrange

theorem relIndex_eq_two [Finite G] {W W₁ Y T : Subgroup G} (hW : IsElemAbelian 2 W)
    (hc : Nat.card W = 8) (hc1 : Nat.card W₁ = 2) (h1 : W₁ ≤ W) (hY : Y ≤ nX W W₁)
    (hT : T ≤ nX W W₁) (hT2 : IsPGroup 2 T)
    (hC : IsPGroup 2 ↥((oTwoRes Y ⊔ T) ⊓ centralizer (W : Set G))) {c t : G}
    (hcY : c ∈ oTwoRes Y) (hcn : c ∉ L32NSet14.trivSub W W₁) (ht : t ∈ T)
    (htn : t ∉ L32NSet14.trivSub W W₁) :
    (pCoreOf 2 (oTwoRes Y ⊔ T)).relIndex T = 2 := by
  have h2 := relIndex_le_two hW hc hc1 h1 hY hT hT2 hC
  have h1' : (pCoreOf 2 (oTwoRes Y ⊔ T)).relIndex T ≠ 1 := fun h =>
    htn (pCoreOf_sup_le_trivSub hW hc hc1 h1 hY hT hcY hcn (Subgroup.relIndex_eq_one.mp h ht))
  have h0 : (pCoreOf 2 (oTwoRes Y ⊔ T)).relIndex T ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

end CFSG.Quasithin.H13.U3P33
