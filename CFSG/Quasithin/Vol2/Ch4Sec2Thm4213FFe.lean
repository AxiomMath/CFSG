module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFw

public section

namespace CFSG.Quasithin.H13.Ch4.FFe

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem four_le_card_fixV {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {E : Subgroup (MulAut V)} (hE2 : ∀ e ∈ E, e ^ 2 = 1) {τ : MulAut V} (hτ3 : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (hτE : ∀ e ∈ E, e * τ = τ * e) : 4 ≤ Nat.card (fixV E) := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => by
    rw [inv_eq_iff_mul_eq_one, ← sq, hV]
  let δ : V →* V :=
    { toFun := fun v => τ v * v⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  set W := δ.range with hW
  have hδ : ∀ v, δ v = τ v * v⁻¹ := fun _ => rfl
  have hτ3' : ∀ v, τ (τ (τ v)) = v := fun v => by
    have := congrArg (fun g : MulAut V => g v) hτ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have key : ∀ a b c : V, a * b⁻¹ * (c * a⁻¹) * (b * c⁻¹) = 1 := by
    intro a b c
    calc a * b⁻¹ * (c * a⁻¹) * (b * c⁻¹) = (a * a⁻¹) * ((b⁻¹ * b) * (c * c⁻¹)) := by ac_rfl
      _ = 1 := by simp
  have htele : ∀ w ∈ W, w * τ w * τ (τ w) = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [hδ, map_mul, map_mul, map_inv, map_inv, hτ3' v]
    exact key _ _ _
  have hfree : ∀ w ∈ W, τ w = w → w = 1 := by
    intro w hw hτw
    have h := htele w hw
    rw [hτw, hτw] at h
    have h2 : w * w = 1 := by rw [← sq, hV]
    rw [h2, one_mul] at h
    exact h
  obtain ⟨v₀, hv₀⟩ : ∃ v, τ v ≠ v := by
    by_contra h
    push Not at h
    exact hτ1 (MulEquiv.ext h)
  have hW1 : δ v₀ ≠ 1 := by
    intro h
    apply hv₀
    rw [hδ, mul_inv_eq_one] at h
    exact h
  have hEW : ∀ e ∈ E, ∀ w ∈ W, e w ∈ W := by
    rintro e he _ ⟨v, rfl⟩
    refine ⟨e v, ?_⟩
    rw [hδ, hδ, map_mul, map_inv]
    have := congrArg (fun g : MulAut V => g v) (hτE e he)
    simp only [MulAut.mul_apply] at this
    rw [this]
  let _ : MulAction ↥E ↥W :=
    { smul := fun e w => ⟨(e : MulAut V) w, hEW e e.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun e f w => Subtype.ext rfl }
  have hE2' : IsPGroup 2 ↥E := fun e => ⟨1, Subtype.ext (by simpa using hE2 e e.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2W : 2 ∣ Nat.card ↥W := by
    have hord : orderOf (⟨δ v₀, ⟨v₀, rfl⟩⟩ : ↥W) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (hV _)
      · intro h
        exact hW1 (congrArg Subtype.val h)
    rw [← hord]
    exact orderOf_dvd_natCard _
  have h1fix : (1 : ↥W) ∈ MulAction.fixedPoints ↥E ↥W := fun e =>
    Subtype.ext (map_one (e : MulAut V))
  obtain ⟨x, hxfix, hx1⟩ := hE2'.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥W h2W h1fix
  have hxE : ∀ e ∈ E, e x = x := fun e he => congrArg Subtype.val (hxfix ⟨e, he⟩)
  have hx1' : (x : V) ≠ 1 := fun h => hx1 (Subtype.ext h.symm)
  have hτx : τ x ≠ (x : V) := fun h => hx1' (hfree x x.2 h)
  have hmem : ∀ y : V, (∀ e ∈ E, e y = y) → y ∈ fixV E := fun y hy => mem_fixV.mpr hy
  have hτxE : ∀ e ∈ E, e (τ x) = τ x := by
    intro e he
    have := congrArg (fun g : MulAut V => g x) (hτE e he)
    simp only [MulAut.mul_apply] at this
    rw [this, hxE e he]
  let f : Fin 4 → ↥(fixV E) := ![1, ⟨x, hmem _ hxE⟩, ⟨τ x, hmem _ hτxE⟩,
    ⟨x * τ x, (fixV E).mul_mem (hmem _ hxE) (hmem _ hτxE)⟩]
  have hτx1 : τ (x : V) ≠ 1 := fun h => hx1' ((map_eq_one_iff τ τ.injective).mp h)
  have hprod1 : (x : V) * τ x ≠ 1 := by
    intro h
    apply hτx
    rw [mul_eq_one_iff_eq_inv, hinv] at h
    exact h.symm
  have hf : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    have hx1'' : (1 : V) ≠ x := fun h => hx1' h.symm
    fin_cases i <;> fin_cases j <;> simp [f] at hv ⊢ <;> first
      | exact hx1 hv | exact hx1 hv.symm | exact hx1'' hv | exact hx1' hv
      | exact hx1' hv.symm | exact hτx1 hv | exact hτx1 hv.symm
      | exact hprod1 hv | exact hprod1 hv.symm | exact hτx hv | exact hτx hv.symm
  have h4 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h4

theorem card_le_index_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {U Z V : Subgroup G}
    (hVU : V ≤ U) (hVZ : V ⊓ Z = ⊥) : Nat.card ↥V ≤ (Z.subgroupOf U).index := by
  let q : ↥V → ↥U ⧸ Z.subgroupOf U := fun v => QuotientGroup.mk (Subgroup.inclusion hVU v)
  have hq : Function.Injective q := by
    intro v w hvw
    have h1 := QuotientGroup.eq.mp hvw
    rw [Subgroup.mem_subgroupOf] at h1
    have hvc : (v : G)⁻¹ * w ∈ V ⊓ Z := ⟨V.mul_mem (V.inv_mem v.2) w.2, by simpa using h1⟩
    rw [hVZ, Subgroup.mem_bot, inv_mul_eq_one] at hvc
    exact Subtype.ext hvc
  exact Nat.card_le_card_of_injective q hq

theorem swap_mul_swap_mem {a b c d : Fin 7} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  decide

@[expose] def a7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, swap_mul_swap_mem (by decide) (by decide)⟩

@[expose] def b7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, swap_mul_swap_mem (by decide) (by decide)⟩

@[expose] def t7 : ↥(alternatingGroup (Fin 7)) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 5 6, swap_mul_swap_mem (by decide) (by decide)⟩

@[expose] def k7 : Multiplicative (Fin 2 → ZMod 2) →* ↥(alternatingGroup (Fin 7)) where
  toFun v := a7 ^ (Multiplicative.toAdd v 0).val * b7 ^ (Multiplicative.toAdd v 1).val
  map_one' := by decide
  map_mul' := by decide +kernel

theorem k7_injective : Function.Injective k7 := by
  rw [injective_iff_map_eq_one]
  decide +kernel

theorem t7_comm : ∀ v, k7 v * t7 = t7 * k7 v := by decide +kernel

theorem t7_pow_three : t7 ^ 3 = 1 := by decide

theorem t7_ne_one : t7 ≠ 1 := by decide

end CFSG.Quasithin.H13.Ch4.FFe

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem pCoreOf_LH_le : pCoreOf 2 (perfectCore (L ⊓ H)) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLH
  have hLHL : LH ≤ L := (perfectCore_le _).trans inf_le_left
  have hOL : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hN2 : IsPGroup 2 ↥(pCoreOf 2 LH ⊔ pCoreOf 2 L) :=
    (pCoreOf_isPGroup 2 LH).to_sup_of_normal_right' (pCoreOf_isPGroup 2 L)
      (((pCoreOf_le 2 LH).trans hLHL).trans hOL)
  have hNL : pCoreOf 2 LH ⊔ pCoreOf 2 L ≤ L :=
    _root_.sup_le ((pCoreOf_le 2 LH).trans hLHL) (pCoreOf_le 2 L)
  have hLN : L ≤ Subgroup.normalizer ((pCoreOf 2 LH ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
    refine c.L_le.trans (_root_.sup_le ?_ ?_)
    · exact le_normalizer_sup_of_le (le_normalizer_pCoreOf 2 LH) (hLHL.trans hOL)
    · exact (le_sup_right : pCoreOf 2 L ≤ pCoreOf 2 LH ⊔ pCoreOf 2 L).trans
        Subgroup.le_normalizer
  exact le_sup_left.trans (le_pCoreOf_of_le_normalizer 2 hNL hLN hN2)

open scoped IsMulCommutative in
theorem ff_of_case4
    (hCV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hblk : CFSG.Quasithin.IsExcA7Block (perfectCore (L ⊓ H))) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  have hV := c.isMulCommutative_V
  set LH := perfectCore (L ⊓ H) with hLHdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  obtain ⟨-, ⟨α, hα, hker⟩, hidx⟩ := hblk
  have hLHV : LH ≤ Subgroup.normalizer (V : Set G) := c.LH_le_normalizer_V
  set ρ := Setup.rho V LH hLHV with hρ
  have hO2 : pCoreOf 2 LH ≤ Subgroup.centralizer (V : Set G) :=
    c.pCoreOf_le_centralizer_V (c.pCoreOf_LH_le.trans c.pCoreOf_L_le)
  have hkerρ : α.ker ≤ ρ.ker := by
    intro ℓ hℓ
    rw [hker] at hℓ
    rw [MonoidHom.mem_ker, Setup.rho_eq_one_iff]
    exact T4213N.pCore_le_subgroupOf hO2 hℓ
  set e := QuotientGroup.quotientKerEquivOfSurjective α hα with he
  set π : ↥(alternatingGroup (Fin 7)) →* MulAut ↥V :=
    (QuotientGroup.lift α.ker ρ hkerρ).comp e.symm.toMonoidHom with hπ
  have hπα : ∀ ℓ : ↥LH, π (α ℓ) = ρ ℓ := by
    intro ℓ
    have h1 : e.symm (α ℓ) = (ℓ : ↥LH ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases hs.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      have hLc : LH ≤ Subgroup.centralizer (V : Set G) := by
        intro ℓ hℓ
        have h1 : π (α ⟨ℓ, hℓ⟩) = 1 := by
          rw [← MonoidHom.mem_ker, h]
          exact Subgroup.mem_top _
        rw [hπα, Setup.rho_eq_one_iff] at h1
        exact h1
      apply c.hypC28.V_ne
      have h1 := c.hypC28.V_comm
      rw [conjClosure_eq_self c.LH_normal] at h1
      rw [← h1, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp hLc
  set E := (π.comp FFe.k7).range with hE
  have hEinj : Function.Injective (π.comp FFe.k7) := hπinj.comp FFe.k7_injective
  have hcE : Nat.card E = 4 := by
    rw [hE, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hEinj, Subgroup.card_top]
    show Nat.card (Fin 2 → ZMod 2) = 4
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    rfl
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
        Nat.cast_ofNat]
      exact (show ∀ x : ZMod 2, 2 * x = 0 by decide) _
    rw [this, map_one]
  have hτE : ∀ x ∈ E, x * π FFe.t7 = π FFe.t7 * x := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, FFe.t7_comm]
  have hτ3 : π FFe.t7 ^ 3 = 1 := by rw [← map_pow, FFe.t7_pow_three, map_one]
  have hτ1 : π FFe.t7 ≠ 1 := fun h => FFe.t7_ne_one (hπinj (h.trans (map_one π).symm))
  have hVsq : ∀ v : ↥V, v ^ 2 = 1 := fun v =>
    Subtype.ext (c.hypC28.V_elem.2 _ v.2)
  have hfix := FFe.four_le_card_fixV hVsq hE2 hτ3 hτ1 hτE
  have hVZ : V ⊓ Subgroup.centralizer (LH : Set G) = ⊥ := by
    rw [← c.inf_centralizer_eq]
    exact hCV
  have hcardV : Nat.card ↥V ≤ 16 := by
    have hVZ' : V ⊓ blockZ LH = ⊥ :=
      le_bot_iff.mp (hVZ ▸ inf_le_inf_left V (inf_le_right : blockZ LH ≤ _))
    have h1 := FFe.card_le_index_of_inf_eq_bot c.V_le_blockU hVZ'
    rw [hidx] at h1
    simpa using h1
  have hFF : IsFFModule (autOn LH V) := by
    refine ⟨E, ?_, ?_, ⟨?_, hE2⟩, ?_⟩
    · rintro _ ⟨v, rfl⟩
      obtain ⟨ℓ, hℓ⟩ := hα (FFe.k7 v)
      rw [← Setup.range_rho hLHV]
      exact ⟨ℓ, by rw [MonoidHom.comp_apply, ← hℓ, hπα]⟩
    · intro hbot
      have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
      omega
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [hcE]
      omega
  refine ⟨hV, B1Red.isFFModule_mono ?_ hFF⟩
  exact T4213N.autOn_le_of_acts c.sup_le_normalizer_V fun a ha =>
    ⟨a, (((perfectCore_le _).trans inf_le_left).trans le_sup_left) ha, fun _ _ => rfl⟩

end Conf4212

end CFSG.Quasithin.H13.Ch4
