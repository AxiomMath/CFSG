module

public import CFSG.Foundations.HigherElementaryThompson
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
import CFSG.Quasithin.SteinbergBKNearMaximalElementaryRank
import CFSG.RankThree.GroupTheory.SteinbergBKTwoStageAutomorphismKernel
import CFSG.Quasithin.SteinbergCDSolvableFFThreeFitting
import CFSG.GroupTheory.SteinbergBKChiefFactorModule
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Base

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG
open scoped commutatorElement

variable {H : Type*} [Group H]

theorem mem_omegaOneCenter_iff {J : Subgroup H} {z : H} :
    z ∈ omegaOneCenter J ↔ z ∈ J ∧ (∀ w ∈ J, w * z = z * w) ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    exact ⟨y.2, fun w hw => congrArg Subtype.val (mem_center_iff.1 hy ⟨w, hw⟩), hz⟩
  · rintro ⟨hz, hc, hz2⟩
    exact ⟨⟨⟨z, hz⟩, mem_center_iff.2 fun w => Subtype.ext (hc w w.2), rfl⟩, hz2⟩

theorem isElementaryAbelian_omegaOneCenter (J : Subgroup H) :
    IsElementaryAbelian 2 (omegaOneCenter J) :=
  Quasithin.BlueprintB2.isElementaryAbelian_iff.2
    ⟨fun _ ha b hb => ((mem_omegaOneCenter_iff.1 ha).2.1 b (mem_omegaOneCenter_iff.1 hb).1).symm,
      fun _ ha => (mem_omegaOneCenter_iff.1 ha).2.2⟩

theorem omegaOneCenter_normal {J : Subgroup H} (hJ : J.Normal) : (omegaOneCenter J).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨hzJ, hzc, hz2⟩ := mem_omegaOneCenter_iff.1 hz
  refine mem_omegaOneCenter_iff.2 ⟨hJ.conj_mem z hzJ g, fun w hw => ?_, ?_⟩
  · have hw' : g⁻¹ * w * g ∈ J := by
      have := hJ.conj_mem w hw g⁻¹
      rwa [inv_inv] at this
    have h := hzc _ hw'
    calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * w := by group
  · rw [conj_pow, hz2, mul_one, mul_inv_cancel]

theorem pCore_range_eq_bot_of_irreducible {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[ZMod 2] V)) {d : ℕ}
    (hV : Nat.card V = 2 ^ d) (hd : 1 ≤ d)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    pCore 2 ρ.range = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCore 2 ρ.range with hPdef
  let W : Submodule (ZMod 2) V :=
    { carrier := {v | ∀ g ∈ P, ((g : ρ.range) : V ≃ₗ[ZMod 2] V) v = v}
      add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => map_zero _
      smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg] }
  have hWinv : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W := by
    intro g' w hw g hg
    have hconj : (⟨ρ g', g', rfl⟩ : ρ.range)⁻¹ * g * ⟨ρ g', g', rfl⟩ ∈ P := by
      have := (pCore_normal (p := 2) (G := ρ.range)).conj_mem g hg (⟨ρ g', g', rfl⟩ : ρ.range)⁻¹
      simpa using this
    have h := hw _ hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply] at h
    have h' := congrArg (ρ g') h
    rw [← LinearEquiv.mul_apply, mul_inv_cancel] at h'
    exact h'
  have hWne : W ≠ ⊥ := by
    have hmod := IsPGroup.card_modEq_card_fixedPoints (pCore_isPGroup (p := 2) (G := ρ.range)) V
    rw [hV] at hmod
    have h0 : (0 : V) ∈ MulAction.fixedPoints P V := fun g => smul_zero _
    have hpos : 0 < Nat.card (MulAction.fixedPoints P V) :=
      Nat.card_pos_iff.2 ⟨⟨_, h0⟩, inferInstance⟩
    have heven : 2 ∣ Nat.card (MulAction.fixedPoints P V) := by
      have h1 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
      exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h1)))
    have h2 : 1 < Nat.card (MulAction.fixedPoints P V) := by
      obtain ⟨k, hk⟩ := heven
      omega
    have := Finite.one_lt_card_iff_nontrivial.1 h2
    obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (⟨0, h0⟩ : ↥(MulAction.fixedPoints P V))
    intro hbot
    have hvW : v ∈ W := fun g hg => hv ⟨g, hg⟩
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 (Subtype.ext hvW)
  rcases hirr W hWinv with h | h
  · exact absurd h hWne
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ W := h ▸ Submodule.mem_top
  exact hv g hg

theorem commutator_le_of_chief_factor [Finite H] [Group.IsSolvable H] (h3 : ¬ 3 ∣ Nat.card H)
    {S A X Y : Subgroup H} (hS2 : IsPGroup 2 S) (hgen : normalClosure (A : Set H) ⊔ S = ⊤)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) [X.Normal] [Y.Normal] (hYX : Y < X)
    (hchief : ∀ Z : Subgroup H, Z.Normal → ¬ (Y < Z ∧ Z < X)) (hX2 : IsPGroup 2 X)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, ∀ x' ∈ X, (a * x * a⁻¹)⁻¹ * x ∉ Y → (a * x' * a⁻¹)⁻¹ * x' ∉ Y →
      (a * (x * x'⁻¹) * a⁻¹)⁻¹ * (x * x'⁻¹) ∈ Y) :
    ⁅(⊤ : Subgroup H), X⁆ ≤ Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, d, hp, hd, -, hcard, hc, hpp, hrest⟩ :=
    GroupTheory.SteinbergBK.solvable_chief_factor_module inferInstance hYX hchief
  have hp2 : p = 2 := by
    have h2 : IsPGroup 2 (GroupTheory.SteinbergBK.chiefQuot X Y) := hX2.map (QuotientGroup.mk' Y)
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hcard] at hn
    have hdvd : p ∣ 2 ^ n := hn ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow hdvd)
  subst hp2
  let _ : CommGroup (GroupTheory.SteinbergBK.chiefQuot X Y) :=
    GroupTheory.SteinbergBK.commGroupOfComm hc
  let _ : Module (ZMod 2) (Additive (GroupTheory.SteinbergBK.chiefQuot X Y)) :=
    GroupTheory.SteinbergBK.elemModule 2 hc hpp
  obtain ⟨ρ, hρ, hirr, htriv⟩ := hrest
  have hO2 : pCore 2 ρ.range = ⊥ := pCore_range_eq_bot_of_irreducible ρ hcard hd hirr
  have hsolv : Group.IsSolvable ρ.range := Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have h3' : ¬ 3 ∣ Nat.card ρ.range := by
    intro h
    apply h3
    refine h.trans ?_
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hFF := (Quasithin.SteinbergCD.solvable_two_core_free_FF_action_three_in_fitting
    (k := ZMod 2) (H := ρ.range) hO2).2.2 h3'
  have hsurjX : ∀ v : Additive (GroupTheory.SteinbergBK.chiefQuot X Y), ∃ (x : H) (hx : x ∈ X),
      v = Additive.ofMul ⟨QuotientGroup.mk' Y x, mem_map_of_mem _ hx⟩ := by
    intro v
    obtain ⟨⟨q, hq⟩, rfl⟩ : ∃ w, Additive.ofMul w = v := ⟨Additive.toMul v, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨x, hx, rfl⟩
  have hfix : ∀ (a x : H) (hx : x ∈ X),
      ρ a (Additive.ofMul ⟨QuotientGroup.mk' Y x, mem_map_of_mem _ hx⟩) =
        Additive.ofMul ⟨QuotientGroup.mk' Y x, mem_map_of_mem _ hx⟩ ↔
        (a * x * a⁻¹)⁻¹ * x ∈ Y := by
    intro a x hx
    rw [hρ a x hx, Additive.ofMul.apply_eq_iff_eq, Subtype.mk.injEq, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hAtriv : ∀ a ∈ A, ρ a = 1 := by
    intro a ha
    by_contra hne
    have hsq : ρ a ^ 2 = 1 := by rw [← map_pow, hA2 a ha, map_one]
    have hord : orderOf (ρ a) = 2 := orderOf_eq_prime hsq hne
    have hA'le : zpowers (ρ a) ≤ ρ.range := zpowers_le.2 ⟨a, rfl⟩
    have hA'ea : IsElementaryAbelian 2 (zpowers (ρ a)) := by
      refine Quasithin.BlueprintB2.isElementaryAbelian_iff.2 ⟨fun b hb c hc => ?_, fun b hb => ?_⟩
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
        rw [← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]
    have hA'ne : zpowers (ρ a) ≠ ⊥ := fun h => hne (by
      have : ρ a ∈ zpowers (ρ a) := mem_zpowers _
      rwa [h, mem_bot] at this)
    have hw := hFF _ hA'le hA'ea hA'ne
    set F := QuasithinUnique.Setup.Offender.fixSub (MonoidHom.id _) (zpowers (ρ a)) with hFdef
    have hmemF : ∀ v, v ∈ F ↔ ρ a v = v := by
      intro v
      rw [QuasithinUnique.Setup.Offender.mem_fixSub]
      refine ⟨fun h => h _ (mem_zpowers _), fun h b hb => ?_⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
      clear hb
      have hinv : (ρ a)⁻¹ v = v := by
        conv_lhs => rw [← h]
        rw [← LinearEquiv.mul_apply, inv_mul_cancel]
        rfl
      show (ρ a ^ n) v = v
      induction n using Int.induction_on with
      | zero => rfl
      | succ n ih =>
        rw [zpow_add_one, LinearEquiv.mul_apply, h]
        exact ih
      | pred n ih =>
        rw [zpow_sub_one, LinearEquiv.mul_apply, hinv]
        exact ih
    have hle2 : Nat.card (Additive (GroupTheory.SteinbergBK.chiefQuot X Y)) ≤ 2 * Nat.card F := by
      by_cases hallF : ∀ v, v ∈ F
      · have hF : Nat.card F = Nat.card (Additive (GroupTheory.SteinbergBK.chiefQuot X Y)) :=
          Nat.card_congr ((Equiv.subtypeEquivRight fun v => ⟨fun _ => trivial,
            fun _ => hallF v⟩).trans (Equiv.Set.univ _))
        omega
      obtain ⟨v₀, hv₀⟩ := not_forall.1 hallF
      obtain ⟨x₀, hx₀, rfl⟩ := hsurjX v₀
      have hoff : ∀ (x : H) (hx : x ∈ X),
          Additive.ofMul (⟨QuotientGroup.mk' Y x, mem_map_of_mem _ hx⟩ :
            GroupTheory.SteinbergBK.chiefQuot X Y) ∉ F →
          Additive.ofMul (⟨QuotientGroup.mk' Y (x * x₀⁻¹),
            mem_map_of_mem _ (X.mul_mem hx (X.inv_mem hx₀))⟩ :
              GroupTheory.SteinbergBK.chiefQuot X Y) ∈ F := by
        intro x hx hxF
        rw [hmemF, hfix a x hx] at hxF
        rw [hmemF, hfix a x₀ hx₀] at hv₀
        rw [hmemF, hfix a _ (X.mul_mem hx (X.inv_mem hx₀))]
        exact hAX a ha x hx x₀ hx₀ hxF hv₀
      let g : Additive (GroupTheory.SteinbergBK.chiefQuot X Y) → Bool × F := fun v =>
        if hv : v ∈ F then (false, ⟨v, hv⟩) else
          (true, ⟨Additive.ofMul (Additive.toMul v *
            (⟨QuotientGroup.mk' Y x₀, mem_map_of_mem _ hx₀⟩ :
              GroupTheory.SteinbergBK.chiefQuot X Y)⁻¹), by
            obtain ⟨x, hx, rfl⟩ := hsurjX v
            have h := hoff x hx hv
            convert h using 2
            apply Subtype.ext
            simp⟩)
      have hginj : Function.Injective g := by
        intro v w hvw
        by_cases hv : v ∈ F <;> by_cases hw' : w ∈ F <;> simp only [g, hv, hw', dite_true,
          dite_false, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and,
          true_and, Subtype.mk.injEq] at hvw
        · exact hvw
        · have h := Additive.ofMul.injective hvw
          exact Additive.toMul.injective (mul_right_cancel h)
      calc Nat.card (Additive (GroupTheory.SteinbergBK.chiefQuot X Y)) ≤ Nat.card (Bool × F) :=
            Nat.card_le_card_of_injective g hginj
        _ = 2 * Nat.card F := by rw [Nat.card_prod]; simp
    have hweight : QuasithinUnique.Setup.Offender.weight (MonoidHom.id _) (zpowers (ρ a)) =
        2 * Nat.card F := by
      rw [QuasithinUnique.Setup.Offender.weight, Nat.card_zpowers, hord]
    rw [hweight] at hw
    omega
  have hNk : normalClosure (A : Set H) ≤ ρ.ker :=
    Subgroup.normalClosure_le_normal fun a ha => MonoidHom.mem_ker.2 (hAtriv a ha)
  have hΓ2 : IsPGroup 2 ρ.range := by
    have hrange : ρ.range = S.map ρ := by
      rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 hNk,
        bot_sup_eq]
    rw [hrange]
    exact hS2.map ρ
  have hall : ∀ g : H, ρ g = 1 := by
    intro g
    have htop : (⊤ : Subgroup ρ.range) ≤ pCore 2 ρ.range :=
      le_sSup ⟨inferInstance, hΓ2.of_equiv Subgroup.topEquiv.symm⟩
    rw [hO2] at htop
    have h := htop (mem_top ⟨ρ g, g, rfl⟩)
    rw [mem_bot] at h
    exact congrArg Subtype.val h
  exact (htriv ⊤).1 fun g _ => hall g

theorem odd_centralizes_of_normal_le [Finite H] [Group.IsSolvable H] (h3 : ¬ 3 ∣ Nat.card H)
    {S A E : Subgroup H} (hS2 : IsPGroup 2 S) (hgen : normalClosure (A : Set H) ⊔ S = ⊤)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hE2 : IsPGroup 2 E)
    (hAE : ∀ a ∈ A, ∀ e ∈ E, ∀ e' ∈ E, a * e * a⁻¹ ≠ e → a * e' * a⁻¹ ≠ e' →
      a * (e * e'⁻¹) * a⁻¹ = e * e'⁻¹) :
    ∀ X : Subgroup H, X.Normal → X ≤ E → ∀ h : H, Odd (orderOf h) → ∀ x ∈ X, h * x = x * h := by
  classical
  intro X
  induction hn : Nat.card X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  intro hXn hXE h hodd
  by_cases hX1 : X = ⊥
  · intro x hx
    rw [hX1, mem_bot] at hx
    rw [hx, mul_one, one_mul]
  obtain ⟨Y, ⟨hYn, hYX⟩, hYmax⟩ := QuasithinUnique.C5.exists_max_card
    (fun Y : Subgroup H => Y.Normal ∧ Y < X) ⟨normal_bot, bot_lt_iff_ne_bot.2 hX1⟩
  have hchief : ∀ Z : Subgroup H, Z.Normal → ¬ (Y < Z ∧ Z < X) := by
    rintro Z hZn ⟨hYZ, hZX⟩
    have h1 := hYmax Z ⟨hZn, hZX⟩
    have h2 := Subgroup.card_lt_of_lt hYZ
    omega
  have hY : ∀ y ∈ Y, h * y = y * h :=
    ih (Nat.card Y) (hn ▸ Subgroup.card_lt_of_lt hYX) Y rfl hYn (hYX.le.trans hXE) h hodd
  have hX2 : IsPGroup 2 X := hE2.to_le hXE
  have hcomm := commutator_le_of_chief_factor h3 hS2 hgen hA2 hYX hchief hX2
    fun a ha x hx x' hx' hxY hx'Y => by
      have h1 : a * x * a⁻¹ ≠ x := fun e => hxY (by rw [e, inv_mul_cancel]; exact one_mem Y)
      have h2 : a * x' * a⁻¹ ≠ x' := fun e => hx'Y (by rw [e, inv_mul_cancel]; exact one_mem Y)
      rw [hAE a ha x (hXE hx) x' (hXE hx') h1 h2, inv_mul_cancel]
      exact one_mem Y
  refine QuasithinUnique.Setup.Wreath.centralizes_of_odd_trivial_factors hX2 hYX.le
    (fun x _ => by rw [normalizer_eq_top_iff.2 hYn]; exact mem_top x)
    (by rw [normalizer_eq_top_iff.2 hXn]; exact mem_top h) hodd hY fun x hx => ?_
  have hc := hcomm (commutator_mem_commutator (mem_top h) (X.inv_mem hx))
  have e : x⁻¹ * (h * x * h⁻¹) = (⁅h, x⁻¹⁆)⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact Y.inv_mem hc

theorem isElementaryAbelian_sup_of_commute {A B : Subgroup H} (hA : IsElementaryAbelian 2 A)
    (hB : IsElementaryAbelian 2 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElementaryAbelian 2 (A ⊔ B : Subgroup H) := by
  obtain ⟨hAc, hA2⟩ := Quasithin.BlueprintB2.isElementaryAbelian_iff.1 hA
  obtain ⟨hBc, hB2⟩ := Quasithin.BlueprintB2.isElementaryAbelian_iff.1 hB
  refine Quasithin.BlueprintB2.isElementaryAbelian_iff.2 ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := QuasithinUnique.C5.mem_sup_of_commute hc hx
    obtain ⟨a', ha', b', hb', rfl⟩ := QuasithinUnique.C5.mem_sup_of_commute hc hy
    have h1 : Commute a a' := hAc a ha a' ha'
    have h2 : Commute b b' := hBc b hb b' hb'
    have h3 : Commute a b' := hc a ha b' hb'
    have h4 : Commute b a' := (hc a' ha' b hb).symm
    exact (h1.mul_right h3).mul_left (h4.mul_right h2)
  · obtain ⟨a, ha, b, hb, rfl⟩ := QuasithinUnique.C5.mem_sup_of_commute hc hx
    rw [(show Commute a b from hc a ha b hb).mul_pow, hA2 a ha, hB2 b hb, one_mul]

theorem pRank_sylow_eq [Finite H] (S : Sylow 2 H) : pRank 2 (S : Subgroup H) = pRank 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · have h := Quasithin.SteinbergBK.pRank_le_pRank_of_subgroup (S : Subgroup H)
    exact h
  · obtain ⟨A₀, hA₀, hA₀c⟩ := Quasithin.BlueprintB2.exists_card_eq_pow_pRank H 2
    obtain ⟨S', hS'⟩ := (IsElementaryAbelian.isPGroup 2 A₀).exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H S' S
    have hA₁ : A₀.map (MulAut.conj g).toMonoidHom ≤ ((g • S' : Sylow 2 H) : Subgroup H) := by
      rintro _ ⟨a, ha, rfl⟩
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have e : (MulAut.conj g)⁻¹ • (MulAut.conj g).toMonoidHom a = a := by
        rw [MulAut.smul_def, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
      rw [e]
      exact hS' ha
    have hea := Quasithin.BlueprintB2.isElementaryAbelian_subgroupOf
      (Y := ((g • S' : Sylow 2 H) : Subgroup H))
      (Quasithin.BlueprintB2.isElementaryAbelian_map hA₀ (MulAut.conj g).toMonoidHom)
    have h := Quasithin.BlueprintB2.card_le_pow_pRank hea
    rw [Quasithin.BlueprintB2.card_subgroupOf_eq hA₁,
      card_map_of_injective (MulAut.conj g).injective, hA₀c] at h
    exact (Nat.pow_le_pow_iff_right one_lt_two).1 h

theorem three_free_solvable_rank_one_step_normalizes_near_maximal_Thompson_center [Finite H]
    [Group.IsSolvable H] (hchar : IsCharacteristicP 2 H) (h3 : ¬ 3 ∣ Nat.card H)
    (S : Sylow 2 H) (hm : 2 ≤ pRank 2 (S : Subgroup H)) (A : Subgroup H)
    (hA : IsElementaryAbelian 2 A) (hAm : Nat.card A = 2 ^ pRank 2 (S : Subgroup H))
    (hAQ : (A ⊓ pCore 2 H).relIndex A = 2) (hgen : normalClosure (A : Set H) ⊔ S = ⊤) :
    let m := pRank 2 (S : Subgroup H)
    let Q := pCore 2 H
    let W := sSup {B : Subgroup H | B ≤ Q ∧ IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ (m - 1)}
    let E := omegaOneCenter W
    let D := (higherElemThompsonOmega (S : Subgroup H) 1).map (S : Subgroup H).subtype
    W.Normal ∧ D ≠ ⊥ ∧ D ≤ E ∧ E ≤ Q ∧ IsElementaryAbelian 2 E ∧
      (∀ h : H, ∃ k : ℕ, h ^ 2 ^ k ∈ centralizer (E : Set H)) ∧
      centralizer (E : Set H) ⊔ S = ⊤ ∧ D.Normal ∧ normalizer (D : Set H) = ⊤ := by
  intro m Q W E D
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (S : Subgroup H) := S.isPGroup'
  have hQ2 : IsPGroup 2 Q := pCore_isPGroup
  have hQn : Q.Normal := pCore_normal
  have hQS : Q ≤ S := hQ2.le_sylow_of_normal S
  obtain ⟨hAc, hA2⟩ := Quasithin.BlueprintB2.isElementaryAbelian_iff.1 hA
  have hAQcard : Nat.card ↥(A ⊓ Q) = 2 ^ (m - 1) := by
    have h := relIndex_mul_card (A ⊓ Q) A
    rw [hAQ, inf_eq_left.2 inf_le_left, hAm] at h
    have h' : 2 * Nat.card ↥(A ⊓ Q) = 2 * 2 ^ (m - 1) := by
      rw [h, ← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left two_pos h'
  have hAQF : A ⊓ Q ∈ {B : Subgroup H | B ≤ Q ∧ IsElementaryAbelian 2 B ∧
      Nat.card B = 2 ^ (m - 1)} :=
    ⟨inf_le_right, Quasithin.BlueprintB2.isElementaryAbelian_of_le inf_le_left hA, hAQcard⟩
  have hAQW : A ⊓ Q ≤ W := le_sSup hAQF
  have hWQ : W ≤ Q := sSup_le fun B hB => hB.1
  have hWn : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    have hle : W ≤ W.comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun B hB => ?_
      rw [← map_le_iff_le_comap]
      refine le_sSup ⟨?_, Quasithin.BlueprintB2.isElementaryAbelian_map hB.2.1 _, ?_⟩
      · rintro _ ⟨b, hb, rfl⟩
        exact hQn.conj_mem b (hB.1 hb) g
      · rw [card_map_of_injective (MulAut.conj g).injective, hB.2.2]
    exact hle hw
  have hEW : E ≤ W := fun z hz => (mem_omegaOneCenter_iff.1 hz).1
  have hEQ : E ≤ Q := hEW.trans hWQ
  have hEn : E.Normal := omegaOneCenter_normal hWn
  have hEea : IsElementaryAbelian 2 E := isElementaryAbelian_omegaOneCenter W
  have hinvE : ∀ x ∈ Q, x ^ 2 = 1 → (∀ w ∈ W, w * x = x * w) → x ∈ E := by
    intro x hxQ hx2 hxW
    refine mem_omegaOneCenter_iff.2 ⟨?_, hxW, hx2⟩
    by_cases hxB : x ∈ A ⊓ Q
    · exact hAQW hxB
    have hdvd : 2 ^ (m - 2) ∣ Nat.card ↥(A ⊓ Q) := by
      rw [hAQcard]
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    have hPAQ : B'.map (A ⊓ Q).subtype ≤ A ⊓ Q := map_subtype_le _
    have hPea : IsElementaryAbelian 2 (B'.map (A ⊓ Q).subtype) :=
      Quasithin.BlueprintB2.isElementaryAbelian_of_le hPAQ
        (Quasithin.BlueprintB2.isElementaryAbelian_of_le inf_le_left hA)
    have hPcard : Nat.card (B'.map (A ⊓ Q).subtype) = 2 ^ (m - 2) := by
      rw [card_map_of_injective (A ⊓ Q).subtype_injective, hB']
    have hx1 : x ≠ 1 := fun h => hxB (h ▸ one_mem _)
    have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hZ : ∀ z ∈ zpowers x, z = 1 ∨ z = x := by
      intro z hz
      rw [mem_zpowers_iff_mem_range_orderOf, hord] at hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_range] at hn
      interval_cases n
      · exact Or.inl (pow_zero x)
      · exact Or.inr (pow_one x)
    have hZea : IsElementaryAbelian 2 (zpowers x) := by
      refine Quasithin.BlueprintB2.isElementaryAbelian_iff.2 ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · rcases hZ a ha with rfl | rfl <;> rcases hZ b hb with rfl | rfl <;> simp
      · rcases hZ a ha with rfl | rfl
        · exact one_pow 2
        · exact hx2
    have hcomm : ∀ p ∈ B'.map (A ⊓ Q).subtype, ∀ z ∈ zpowers x, p * z = z * p := by
      intro p hp z hz
      have hpx : p * x = x * p := hxW p (hAQW (hPAQ hp))
      rcases hZ z hz with rfl | rfl
      · rw [mul_one, one_mul]
      · exact hpx
    have hPZ : B'.map (A ⊓ Q).subtype ⊓ zpowers x = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rcases hZ z hz.2 with rfl | rfl
      · exact one_mem _
      · exact absurd (hPAQ hz.1) hxB
    have hVcard : Nat.card ↥(B'.map (A ⊓ Q).subtype ⊔ zpowers x) = 2 ^ (m - 1) := by
      have h := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
        (QuasithinUnique.C5.le_normalizer_of_commute hcomm)
      rw [hPZ, card_bot, mul_one, hPcard, Nat.card_zpowers, hord, ← pow_succ] at h
      rw [h]
      congr 1
      omega
    have hVF : B'.map (A ⊓ Q).subtype ⊔ zpowers x ∈ {B : Subgroup H | B ≤ Q ∧
        IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ (m - 1)} :=
      ⟨sup_le (hPAQ.trans inf_le_right) (zpowers_le.2 hxQ),
        isElementaryAbelian_sup_of_commute hPea hZea hcomm, hVcard⟩
    exact le_sSup hVF (mem_sup_right (mem_zpowers x))
  obtain ⟨hHTchar, hHTint, -⟩ :=
    Quasithin.SteinbergBK.higher_elementary_thompson_intersections_and_central_involutions hS2
  obtain ⟨-, -, -, hJ1, -, -, -, hE1ne⟩ := hHTint 1 1 le_rfl (by omega)
  have hDne : D ≠ ⊥ := by
    intro h
    apply hE1ne
    rwa [map_eq_bot_iff_of_injective _ (S : Subgroup H).subtype_injective] at h
  have hWJ : W ≤ (higherElemThompson (S : Subgroup H) 1).map (S : Subgroup H).subtype := by
    refine sSup_le fun B hB => ?_
    have hBS : B ≤ S := hB.1.trans hQS
    have hB' := Quasithin.BlueprintB2.isElementaryAbelian_subgroupOf (Y := (S : Subgroup H))
      hB.2.1
    have hBrank : pRank 2 (B.subgroupOf S) = m - 1 :=
      pRank_eq_of_card_eq_pow one_lt_two
        (by rw [Quasithin.BlueprintB2.card_subgroupOf_eq hBS, hB.2.2])
    have h := hJ1 _ hB' (by rw [hBrank])
    calc B = (B.subgroupOf S).map (S : Subgroup H).subtype := by
          rw [subgroupOf_map_subtype, inf_eq_left.2 hBS]
      _ ≤ _ := map_mono h
  have hDmem : ∀ d ∈ D, d ^ 2 = 1 ∧ ∀ w ∈ W, w * d = d * w := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨-, hdc, hd2⟩ := mem_omegaOneCenter_iff.1 hd
    refine ⟨by rw [← map_pow, hd2, map_one], fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hWJ hw
    exact congrArg Subtype.val (hdc y hy)
  have hSD : ∀ s ∈ (S : Subgroup H), ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    rintro s hs _ ⟨d, hd, rfl⟩
    have h := (hHTchar 1).2.fixed (MulAut.conj (⟨s, hs⟩ : (S : Subgroup H)))
    have hd' : d ∈ (higherElemThompsonOmega (S : Subgroup H) 1).comap
        (MulAut.conj (⟨s, hs⟩ : (S : Subgroup H))).toMonoidHom := h.symm ▸ hd
    exact ⟨_, hd', by simp⟩
  have hQD : ∀ d ∈ D, ∀ x ∈ Q, ⁅x, d⁆ ∈ W := by
    intro d hd x hx
    have hdS : d ∈ (S : Subgroup H) := map_subtype_le _ hd
    have h1 : ⁅x, d⁆ ∈ Q := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine Q.mul_mem hx ?_
      rw [← mul_assoc]
      exact hQn.conj_mem _ (Q.inv_mem hx) d
    have h2 : ⁅x, d⁆ ∈ D := by
      rw [commutatorElement_def]
      exact D.mul_mem (hSD x (hQS hx) d hd) (D.inv_mem hd)
    exact hEW (hinvE _ h1 (hDmem _ h2).1 (hDmem _ h2).2)
  have hDQ : D ≤ Q := fun d hd =>
    (RankThree.GroupTheory.SteinbergBK.two_stage_pointwise_automorphism_kernel_is_a_prime_group.{0}
      2).2 H hchar W hWQ d (mem_centralizer_iff.2 (hDmem d hd).2) fun x hx => hQD d hd x hx
  have hDE : D ≤ E := fun d hd => hinvE d (hDQ hd) (hDmem d hd).1 (hDmem d hd).2
  have hpr : pRank 2 H = m := (pRank_sylow_eq S).symm
  have hAfam : A ∈ higherElemThompsonFamily H 0 := by
    rw [mem_higherElemThompsonFamily_iff, hpr, Nat.sub_zero]
    exact ⟨hA, hAm⟩
  obtain ⟨d₀, e₀, hd₀, he₀, hde, -, -⟩ :=
    Quasithin.SteinbergBK.near_maximal_elementary_whole_module_rank_inequality E hAfam
  have hAQC : A ⊓ Q ≤ A ⊓ centralizer (E : Set H) := fun y hy =>
    ⟨hy.1, mem_centralizer_iff.2 fun e he => ((mem_omegaOneCenter_iff.1 he).2.1 y (hAQW hy)).symm⟩
  have he₀1 : 2 ^ e₀ ≤ 2 := by
    rw [← he₀, ← hAQ]
    exact relIndex_le_of_le_left hAQC (by rw [hAQ]; norm_num)
  have hEA2 : (E ⊓ centralizer (A : Set H)).relIndex E ≤ 2 := by
    rw [hd₀]
    have he1 : e₀ ≤ 1 := by
      by_contra h
      have : 2 ^ 2 ≤ 2 ^ e₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 2 ^ d₀ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
  have hAE : ∀ a ∈ A, ∀ e ∈ E, ∀ e' ∈ E, a * e * a⁻¹ ≠ e → a * e' * a⁻¹ ≠ e' →
      a * (e * e'⁻¹) * a⁻¹ = e * e'⁻¹ := by
    intro a ha e he e' he' hea hea'
    have hfix : ∀ y : H, y ∈ centralizer ({a} : Set H) ↔ a * y * a⁻¹ = y := by
      intro y
      rw [mem_centralizer_singleton_iff]
      constructor
      · intro h
        rw [← h]
        group
      · intro h
        calc y * a = a * y * a⁻¹ * a := by rw [h]
          _ = a * y := by group
    set K := (E ⊓ centralizer ({a} : Set H)).subgroupOf E with hK
    have hKidx : K.index ≤ 2 := by
      refine le_trans ?_ hEA2
      refine relIndex_le_of_le_left (inf_le_inf_left _ (centralizer_le ?_)) ?_
      · rintro _ rfl
        exact ha
      · have : (E ⊓ centralizer (A : Set H)).relIndex E ≠ 0 := by
          rw [hd₀]
          positivity
        exact this
    have heK : (⟨e, he⟩ : E) ∉ K := fun h => hea ((hfix e).1 (mem_subgroupOf.1 h).2)
    have he'K : (⟨e', he'⟩ : E) ∉ K := fun h => hea' ((hfix e').1 (mem_subgroupOf.1 h).2)
    have hK2 : K.index = 2 := by
      have hK1 : K.index ≠ 1 := fun h => heK (index_eq_one.1 h ▸ mem_top _)
      have hK0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hprod : (⟨e, he⟩ : E) * (⟨e', he'⟩ : E)⁻¹ ∈ K := by
      rw [mul_mem_iff_of_index_two hK2, inv_mem_iff]
      exact iff_of_false heK he'K
    exact (hfix _).1 (mem_subgroupOf.1 hprod).2
  have hodd := odd_centralizes_of_normal_le h3 hS2 hgen hA2 (hQ2.to_le hEQ) hAE E hEn le_rfl
  have himage : ∀ h : H, ∃ k : ℕ, h ^ 2 ^ k ∈ centralizer (E : Set H) := by
    intro h
    obtain ⟨a, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    refine ⟨a, mem_centralizer_iff.2 fun e he => (hodd _ ?_ e he).symm⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hb
  have hCS : centralizer (E : Set H) ⊔ S = ⊤ := by
    have hQC2 : IsPGroup 2 (H ⧸ centralizer (E : Set H)) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := himage h
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
    have hsurj : Function.Surjective (QuotientGroup.mk' (centralizer (E : Set H))) :=
      QuotientGroup.mk'_surjective _
    have hmap : (S : Subgroup H).map (QuotientGroup.mk' (centralizer (E : Set H))) = ⊤ := by
      rw [← Sylow.coe_mapSurjective hsurj S]
      exact ((S.mapSurjective hsurj).is_maximal' (hQC2.to_subgroup ⊤) le_top).symm
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' (centralizer (E : Set H)))) hmap
    rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at h
    rw [sup_comm]
    exact h
  have hDnorm : normalizer (D : Set H) = ⊤ := by
    rw [eq_top_iff, ← hCS]
    refine sup_le (QuasithinUnique.C5.le_normalizer_of_commute fun c hc d hd =>
      (mem_centralizer_iff.1 hc d (hDE hd)).symm) fun s hs => ?_
    rw [mem_normalizer_iff]
    intro d
    refine ⟨hSD s hs d, fun h => ?_⟩
    simpa [mul_assoc] using hSD s⁻¹ (inv_mem hs) _ h
  exact ⟨hWn, hDne, hDE, hEQ, hEea, himage, hCS, normalizer_eq_top_iff.1 hDnorm, hDnorm⟩

end CFSG.Quasithin.H13.QRC
