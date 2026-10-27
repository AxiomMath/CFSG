module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

variable {T : Type*} [Group T]

@[expose] def conjActOn (V : Subgroup T) [V.Normal] (A : Subgroup T) : A →* MulAut V :=
  MulAut.conjNormal.comp A.subtype

theorem conjActOn_apply (V : Subgroup T) [V.Normal] (A : Subgroup T) (a : A) (v : V) :
    ((conjActOn V A a v : V) : T) = a * v * (a : T)⁻¹ :=
  rfl

theorem isElementaryAbelian_of_le {p : ℕ} {X A : Subgroup T} (hXA : X ≤ A)
    (hA : CFSG.IsElementaryAbelian p A) : CFSG.IsElementaryAbelian p X :=
  CFSG.IsElementaryAbelian.of_le hA hXA

theorem commute_of_isElementaryAbelian {p : ℕ} {A : Subgroup T}
    (hA : CFSG.IsElementaryAbelian p A) {x y : T} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

variable [Finite T]

theorem card_mul_card_centralizer_le {p : ℕ} {V A X : Subgroup T}
    (hV : CFSG.IsElementaryAbelian p V) (hA : CFSG.IsElementaryAbelian p A)
    (hmax : ∀ E : Subgroup T, CFSG.IsElementaryAbelian p E → Nat.card E ≤ Nat.card A)
    (hXA : X ≤ A) :
    Nat.card X * Nat.card (V ⊓ centralizer (X : Set T) : Subgroup T) ≤
      Nat.card A * Nat.card (A ⊓ V : Subgroup T) := by
  set Y := V ⊓ centralizer (X : Set T) with hY
  have hXe : CFSG.IsElementaryAbelian p X := isElementaryAbelian_of_le hXA hA
  have hYe : CFSG.IsElementaryAbelian p Y := isElementaryAbelian_of_le inf_le_left hV
  have hYX : Y ≤ centralizer (X : Set T) := inf_le_right
  have hEe : CFSG.IsElementaryAbelian p (X ⊔ Y : Subgroup T) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hYX
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 (hYX hy)) x hx
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X Y hcomm
  have hinf : X ⊓ Y ≤ A ⊓ V := fun z hz => ⟨hXA hz.1, hz.2.1⟩
  calc Nat.card X * Nat.card Y = Nat.card (X ⊔ Y : Subgroup T) * Nat.card (X ⊓ Y : Subgroup T) :=
        hprod.symm
    _ ≤ Nat.card A * Nat.card (A ⊓ V : Subgroup T) :=
        Nat.mul_le_mul (hmax _ hEe) (card_le_of_le hinf)

theorem inf_centralizer_eq_inf {p : ℕ} {V A : Subgroup T} (hV : CFSG.IsElementaryAbelian p V)
    (hA : CFSG.IsElementaryAbelian p A)
    (hmax : ∀ E : Subgroup T, CFSG.IsElementaryAbelian p E → Nat.card E ≤ Nat.card A) :
    V ⊓ centralizer (A : Set T) = A ⊓ V := by
  have hYe : CFSG.IsElementaryAbelian p (V ⊓ centralizer (A : Set T) : Subgroup T) :=
    isElementaryAbelian_of_le inf_le_left hV
  have hEe : CFSG.IsElementaryAbelian p (A ⊔ V ⊓ centralizer (A : Set T) : Subgroup T) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hEA : A ⊔ V ⊓ centralizer (A : Set T) = A :=
    (eq_of_le_of_card_ge le_sup_left (hmax _ hEe)).symm
  have h1 : V ⊓ centralizer (A : Set T) ≤ A :=
    (le_sup_right : V ⊓ centralizer (A : Set T) ≤ A ⊔ V ⊓ centralizer (A : Set T)).trans hEA.le
  have h2 : A ⊓ V ≤ centralizer (A : Set T) := fun x hx => mem_centralizer_iff.2 fun y hy =>
    commute_of_isElementaryAbelian hA hy hx.1
  exact le_antisymm (le_inf h1 inf_le_left) (le_inf inf_le_right h2)

@[expose] def fixedEquiv (V : Subgroup T) [V.Normal] (A : Subgroup T) (D : Subgroup (MulAut V))
    (hD : D ≤ (conjActOn V A).range) :
    {v : V // ∀ d ∈ D, d v = v} ≃
      ↥(V ⊓ centralizer (((D.comap (conjActOn V A)).map A.subtype : Subgroup T) : Set T)) where
  toFun v := ⟨v.1, v.1.2, mem_centralizer_iff.2 fun x hx => by
    obtain ⟨a, ha, rfl⟩ := hx
    have h := congrArg Subtype.val (v.2 _ ha)
    rw [conjActOn_apply] at h
    change (a : T) * v.1 = v.1 * a
    calc (a : T) * v.1 = (a * v.1 * (a : T)⁻¹) * a := by group
      _ = v.1 * a := by rw [h]⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, fun d hd => by
    obtain ⟨a, rfl⟩ := hD hd
    apply Subtype.ext
    rw [conjActOn_apply]
    have h := (mem_centralizer_iff.1 w.2.2) a ⟨a, hd, rfl⟩
    calc (a : T) * w.1 * (a : T)⁻¹ = (w.1 * a) * (a : T)⁻¹ := by rw [h]
      _ = w.1 := by group⟩
  left_inv v := rfl
  right_inv w := rfl

theorem maximal_elementary_subgroup_original_best_weight {p : ℕ} (V : Subgroup T) [V.Normal]
    (hV : CFSG.IsElementaryAbelian p V) (A : Subgroup T) (hA : CFSG.IsElementaryAbelian p A)
    (hmax : ∀ E : Subgroup T, CFSG.IsElementaryAbelian p E → Nat.card E ≤ Nat.card A) :
    (conjActOn V A).ker.map A.subtype = A ⊓ centralizer (V : Set T) ∧
    V ⊓ centralizer (A : Set T) = A ⊓ V ∧
    (∀ D : Subgroup (MulAut V), D ≤ (conjActOn V A).range →
      Nat.card D * Nat.card ↥(V ⊓ centralizer
        (((D.comap (conjActOn V A)).map A.subtype : Subgroup T) : Set T)) ≤
        Nat.card (conjActOn V A).range * Nat.card ↥(V ⊓ centralizer (A : Set T))) ∧
    (∀ D : Subgroup (MulAut V), D ≤ (conjActOn V A).range →
      Nat.card D * Nat.card {v : V // ∀ d ∈ D, d v = v} ≤
        Nat.card (conjActOn V A).range *
          Nat.card {v : V // ∀ d ∈ (conjActOn V A).range, d v = v}) ∧
    Nat.card V ≤ Nat.card (conjActOn V A).range *
      Nat.card {v : V // ∀ d ∈ (conjActOn V A).range, d v = v} ∧
    CFSG.IsElementaryAbelian p (conjActOn V A).range ∧
    ((conjActOn V A).range ≠ ⊥ ↔ ⁅V, A⁆ ≠ ⊥) := by
  classical
  set φ := conjActOn V A with hφ
  have hCA := inf_centralizer_eq_inf hV hA hmax
  have hker : φ.ker.map A.subtype = A ⊓ centralizer (V : Set T) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, mem_centralizer_iff.2 fun v hv => ?_⟩
      have h' := congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.1 ha) ⟨v, hv⟩)
      rw [conjActOn_apply, MulAut.one_apply] at h'
      have h : (a : T) * v * (a : T)⁻¹ = v := h'
      change v * a = a * v
      calc v * (a : T) = ((a : T) * v * (a : T)⁻¹) * a := by rw [h]
        _ = a * v := by group
    · rintro ⟨hxA, hxC⟩
      refine ⟨⟨x, hxA⟩, MonoidHom.mem_ker.2 (MulEquiv.ext fun v => Subtype.ext ?_), rfl⟩
      have h : (v : T) * x = x * v := (mem_centralizer_iff.1 hxC) v v.2
      rw [conjActOn_apply, MulAut.one_apply]
      change x * (v : T) * x⁻¹ = v
      rw [← h]
      group
  have hcardpre : ∀ D : Subgroup (MulAut V), D ≤ φ.range →
      Nat.card (D.comap φ) = Nat.card D * Nat.card φ.ker := by
    intro D hD
    set ψ : D.comap φ →* D := (φ.comp (D.comap φ).subtype).codRestrict D fun x => x.2
    have hψ : Function.Surjective ψ := by
      intro d
      obtain ⟨a, ha⟩ := hD d.2
      exact ⟨⟨a, show φ a ∈ D by rw [ha]; exact d.2⟩, Subtype.ext ha⟩
    have hψker : Nat.card ψ.ker = Nat.card φ.ker := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, ?_⟩
          invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
      · have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        exact MonoidHom.mem_ker.2 this
      · change φ y.1 ∈ D
        rw [MonoidHom.mem_ker.1 y.2]
        exact D.one_mem
      · exact MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 y.2))
    rw [← card_mul_index ψ.ker, index_ker, MonoidHom.range_eq_top.2 hψ, card_top,
      hψker, mul_comm]
  have hcardA : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [← card_mul_index φ.ker, index_ker, mul_comm]
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hbest : ∀ D : Subgroup (MulAut V), D ≤ φ.range →
      Nat.card D * Nat.card ↥(V ⊓ centralizer
        (((D.comap φ).map A.subtype : Subgroup T) : Set T)) ≤
        Nat.card φ.range * Nat.card ↥(V ⊓ centralizer (A : Set T)) := by
    intro D hD
    have hXA : (D.comap φ).map A.subtype ≤ A := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have h1 := card_mul_card_centralizer_le hV hA hmax hXA
    rw [card_map_of_injective A.subtype_injective, hcardpre D hD, hcardA, ← hCA] at h1
    refine Nat.le_of_mul_le_mul_right ?_ hkpos
    calc Nat.card D * Nat.card ↥(V ⊓ centralizer
          (((D.comap φ).map A.subtype : Subgroup T) : Set T)) * Nat.card φ.ker =
        Nat.card D * Nat.card φ.ker * Nat.card ↥(V ⊓ centralizer
          (((D.comap φ).map A.subtype : Subgroup T) : Set T)) := by ring
      _ ≤ Nat.card φ.range * Nat.card φ.ker * Nat.card ↥(V ⊓ centralizer (A : Set T)) := h1
      _ = _ := by ring
  have hpreB : ((φ.range.comap φ).map A.subtype : Subgroup T) = A := by
    have h1 : φ.range.comap φ = ⊤ := eq_top_iff.2 fun a _ => ⟨a, rfl⟩
    rw [h1, ← MonoidHom.range_eq_map, range_subtype]
  have hfixB : Nat.card {v : V // ∀ d ∈ φ.range, d v = v} =
      Nat.card ↥(V ⊓ centralizer (A : Set T)) := by
    rw [Nat.card_congr (fixedEquiv V A φ.range le_rfl), hpreB]
  have hfix : ∀ D : Subgroup (MulAut V), D ≤ φ.range →
      Nat.card D * Nat.card {v : V // ∀ d ∈ D, d v = v} ≤
        Nat.card φ.range * Nat.card {v : V // ∀ d ∈ φ.range, d v = v} := by
    intro D hD
    rw [Nat.card_congr (fixedEquiv V A D hD), hfixB]
    exact hbest D hD
  have hV1 : Nat.card V ≤ Nat.card φ.range * Nat.card {v : V // ∀ d ∈ φ.range, d v = v} := by
    have h1 := hfix ⊥ bot_le
    have h2 : Nat.card {v : V // ∀ d ∈ (⊥ : Subgroup (MulAut V)), d v = v} = Nat.card V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun v d hd => by
        rw [mem_bot.1 hd, MulAut.one_apply])
    rwa [card_bot, one_mul, h2] at h1
  have : CFSG.IsElementaryAbelian p A := hA
  have hBe : CFSG.IsElementaryAbelian p φ.range :=
    { toIsMulCommutative := ⟨⟨fun x y => by
        obtain ⟨a, ha⟩ := x.2
        obtain ⟨b, hb⟩ := y.2
        apply Subtype.ext
        change (x : MulAut V) * y = y * x
        rw [← ha, ← hb, ← map_mul, ← map_mul, hA.is_comm.comm a b]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨a, ha⟩ := x.2
        apply Subtype.ext
        have hap : a ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (CFSG.IsElementaryAbelian.exponent_dvd_p p A) a
        rw [coe_pow, ← ha, ← map_pow, hap, map_one, coe_one] }
  have htriv : φ.range = ⊥ ↔ ⁅V, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    constructor
    · intro h a ha
      have h1 : φ ⟨a, ha⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [h, mem_bot] at h1
      have h2 : a ∈ φ.ker.map A.subtype := ⟨⟨a, ha⟩, MonoidHom.mem_ker.2 h1, rfl⟩
      rw [hker] at h2
      exact h2.2
    · intro h
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      have h1 : (a : T) ∈ φ.ker.map A.subtype := by
        rw [hker]
        exact ⟨a.2, h a.2⟩
      obtain ⟨a', ha', ha'a⟩ := h1
      have : a' = a := Subtype.ext ha'a
      rw [← this]
      exact mem_bot.2 (MonoidHom.mem_ker.1 ha')
  exact ⟨hker, hCA, hbest, hfix, hV1, hBe, not_congr htriv⟩

end CFSG.Quasithin.SteinbergBT
