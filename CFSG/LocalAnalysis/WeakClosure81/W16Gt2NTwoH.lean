module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoC
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoHAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_inner_eq_bot_of_rank {Y : Type} [Group Y] [Finite Y]
    (hZ : Subgroup.center Y = ⊥) {n : ℕ} (Vb : Subgroup Y) (hVb : IsElemAbelian 2 Vb)
    (hcard : Nat.card Vb = 2 ^ n)
    (hrank : ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ n)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 2 A)
    (hcomm : ∀ y : Y, MulAut.conj y ∈ A → ∀ v ∈ Vb, y * v = v * y)
    (hinter : ∀ y ∈ Vb, MulAut.conj y ∈ A → y = 1) :
    A ⊓ (MulAut.conj : Y →* MulAut Y).range = ⊥ := by
  classical
  let E₀ : Subgroup Y := A.comap (MulAut.conj : Y →* MulAut Y)
  have hconj_inj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyc : y ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 : MulAut.conj y z = z := by rw [hy]; rfl
      rw [MulAut.conj_apply] at h1
      calc z * y = (y * z * y⁻¹) * y := by rw [h1]
        _ = y * z := by group
    rw [hZ] at hyc
    exact Subgroup.mem_bot.1 hyc
  have hE₀ : IsElemAbelian 2 E₀ := by
    haveI : IsMulCommutative ↥A := hA.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      exact hconj_inj (by
        change MulAut.conj ((x : Y) * (y : Y)) = MulAut.conj ((y : Y) * (x : Y))
        rw [map_mul, map_mul]
        exact congrArg Subtype.val (mul_comm' (⟨MulAut.conj (x : Y),
          Subgroup.mem_comap.1 x.2⟩ : ↥A)
          ⟨MulAut.conj (y : Y), Subgroup.mem_comap.1 y.2⟩))
    · exact hconj_inj (by
        rw [map_pow, map_one]
        exact hA.2 (MulAut.conj x) (Subgroup.mem_comap.1 hx))
  have hE₀sq : ∀ a : ↥E₀, a ^ 2 = 1 := fun a => Subtype.ext (hE₀.2 (a : Y) a.2)
  have hVbsq : ∀ a : ↥Vb, a ^ 2 = 1 := fun a => Subtype.ext (hVb.2 (a : Y) a.2)
  have hE₀Vb : ∀ e ∈ E₀, ∀ v ∈ Vb, e * v = v * e := fun e he v hv =>
    hcomm e (Subgroup.mem_comap.1 he) v hv
  have hE₀bot : E₀ ⊓ Vb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE₀, hxVb⟩
    exact Subgroup.mem_bot.2 (hinter x hxVb (Subgroup.mem_comap.1 hxE₀))
  haveI : IsMulCommutative ↥E₀ := hE₀.1
  haveI : IsMulCommutative ↥Vb := hVb.1
  let φ : ↥E₀ × ↥Vb →* Y :=
    E₀.subtype.noncommCoprod Vb.subtype
      (fun e v => (commute_iff_eq _ _).mpr (hE₀Vb e e.2 v v.2))
  have hφ_apply : ∀ e v, φ (e, v) = (e : Y) * (v : Y) := by
    intro e v
    rw [MonoidHom.noncommCoprod_apply]
    rfl
  have hφ_inj : Function.Injective φ := by
    rintro ⟨e₁, v₁⟩ ⟨e₂, v₂⟩ heq
    have he : (e₁ : Y) * (v₁ : Y) = (e₂ : Y) * (v₂ : Y) := by
      simpa only [hφ_apply] using heq
    have hmem : (e₂ : Y)⁻¹ * (e₁ : Y) = (v₂ : Y) * (v₁ : Y)⁻¹ := by
      calc (e₂ : Y)⁻¹ * (e₁ : Y)
          = (e₂ : Y)⁻¹ * ((e₁ : Y) * (v₁ : Y)) * (v₁ : Y)⁻¹ := by group
        _ = (e₂ : Y)⁻¹ * ((e₂ : Y) * (v₂ : Y)) * (v₁ : Y)⁻¹ := by rw [he]
        _ = (v₂ : Y) * (v₁ : Y)⁻¹ := by group
    have h1 : (e₂ : Y)⁻¹ * (e₁ : Y) ∈ E₀ ⊓ Vb :=
      ⟨E₀.mul_mem (E₀.inv_mem e₂.2) e₁.2, by
        rw [hmem]
        exact Vb.mul_mem v₂.2 (Vb.inv_mem v₁.2)⟩
    rw [hE₀bot] at h1
    have h2 : (e₂ : Y)⁻¹ * (e₁ : Y) = 1 := Subgroup.mem_bot.1 h1
    have h3 : (e₁ : Y) = (e₂ : Y) := by
      have := congrArg (fun z => (e₂ : Y) * z) h2
      simpa [mul_assoc] using this
    have hv : (v₁ : Y) = (v₂ : Y) := by
      have h4 := he
      rw [h3] at h4
      exact mul_left_cancel h4
    exact Prod.ext (Subtype.ext h3) (Subtype.ext hv)
  have htop : IsElemAbelian 2 (⊤ : Subgroup (↥E₀ × ↥Vb)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · apply Subtype.ext
      exact mul_comm' (a : ↥E₀ × ↥Vb) (b : ↥E₀ × ↥Vb)
    · exact Prod.ext (hE₀sq (x : ↥E₀ × ↥Vb).1) (hVbsq (x : ↥E₀ × ↥Vb).2)
  have hE_ea : IsElemAbelian 2 φ.range := by
    simpa [Subgroup.map_top] using htop.map φ
  have hcardφ : Nat.card φ.range = Nat.card ↥E₀ * Nat.card Vb := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofInjective φ hφ_inj)).symm
  have hle : Nat.card ↥E₀ * 2 ^ n ≤ 2 ^ n := by
    have h := hrank φ.range hE_ea
    rwa [hcardφ, hcard] at h
  have hE₀card : Nat.card ↥E₀ = 1 := by
    have hle1 : Nat.card ↥E₀ ≤ 1 := by
      have h2 : Nat.card ↥E₀ * 2 ^ n ≤ 1 * 2 ^ n := by
        simpa only [one_mul] using hle
      exact Nat.le_of_mul_le_mul_right h2 (pow_pos (by norm_num) n)
    have hpos : 0 < Nat.card ↥E₀ := Nat.card_pos
    omega
  have hE₀bot' : E₀ = ⊥ := Subgroup.eq_bot_of_card_eq (H := E₀) hE₀card
  rw [Subgroup.eq_bot_iff_forall]
  intro α hα
  obtain ⟨hαA, hαrange⟩ := Subgroup.mem_inf.1 hα
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hαrange
  have hyE₀ : y ∈ E₀ := Subgroup.mem_comap.2 (by rw [hy]; exact hαA)
  have hybot : y = 1 := by rw [hE₀bot'] at hyE₀; exact Subgroup.mem_bot.1 hyE₀
  rw [← hy, hybot, map_one]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem exists_barAct (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∃ β : ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)),
      ∀ (b : ↥B) (x x' : ↥(hatK Mo V)),
        (x' : LGL 2 Mo.W) = Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩ * x *
            (Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩)⁻¹ →
          β b (hatBar Mo V x) = hatBar Mo V x' :=
  w16gt2NTwoH_exists_barAct c Mo

section Certified


theorem two_pow_le_card_B (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    2 ^ E3.mQuot V (U ⊔ V₀) ≤ Nat.card B := by
  have hnle := (c.hatL_shape h1 h5 h15 hS Mo c.g_mem c.g_not).2
  obtain ⟨m, -, hBm⟩ := c.B_conj
  have hcardB : Nat.card B = Nat.card V₀ := by
    rw [hBm, E3.card_conjSubgroup, E3.card_conjSubgroup]
  have hV₀ea : IsElemAbelian 2 V₀ := c.cex.hyp.h6.elemAbelian.mono c.cex.hyp.h6.le
  have hcardV₀ : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV₀ea.isPGroup
  rw [hcardB, hcardV₀]
  exact Nat.pow_le_pow_right (by norm_num) hnle

theorem barAct_properties (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (β : ↥B →* MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V)))
    (hβ : ∀ (b : ↥B) (x x' : ↥(hatK Mo V)),
      (x' : LGL 2 Mo.W) = Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩ * x *
          (Mo.ρ ⟨(b : G), c.mem.1 (c.B_le b.2)⟩)⁻¹ →
        β b (hatBar Mo V x) = hatBar Mo V x') :
    Function.Injective β ∧ IsElemAbelian 2 β.range ∧
      (∀ y : hatX Mo V ⧸ Subgroup.center (hatX Mo V), MulAut.conj y ∈ β.range →
        ∀ v ∈ hatBarSub Mo V V, y * v = v * y) ∧
      ∀ y ∈ hatBarSub Mo V V, MulAut.conj y ∈ β.range → y = 1 :=
  w16gt2NTwoH_barAct_properties hn h1 h5 h15 hS c Mo β hβ

theorem false_of_rank (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hrank : ∀ E : Subgroup (hatX Mo V ⧸ Subgroup.center (hatX Mo V)), IsElemAbelian 2 E →
      Nat.card E ≤ 2 ^ E3.mQuot V (U ⊔ V₀))
    (hout : ∀ E : Subgroup (MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V))),
      IsElemAbelian 2 E →
        E ⊓ (MulAut.conj : (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) →*
          MulAut (hatX Mo V ⧸ Subgroup.center (hatX Mo V))).range = ⊥ → Nat.card E ≤ 2) :
    False := by
  obtain ⟨β, hβ⟩ := c.exists_barAct Mo
  obtain ⟨hinj, helem, hcomm, hinter⟩ := c.barAct_properties hn h1 h5 h15 hS Mo β hβ
  haveI : Group.IsPerfect ↥(hatK Mo V) := c.isPerfect_hatK hn h1 h5 h15 hS Mo
  haveI : Group.IsPerfect (hatX Mo V) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK Mo V)))
  have hZ : Subgroup.center (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (hatX Mo V)
  have hA := inf_inner_eq_bot_of_rank hZ (hatBarSub Mo V V) (c.isElemAbelian_hatBarSub Mo)
    (c.card_hatBarSub_V hn h1 h5 h15 hS Mo) hrank β.range helem hcomm hinter
  have hle := hout β.range helem hA
  have hcardR : Nat.card β.range = Nat.card B :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hB := c.two_pow_le_card_B h1 h5 h15 hS Mo
  have : 2 ^ 2 ≤ 2 ^ E3.mQuot V (U ⊔ V₀) := Nat.pow_le_pow_right (by norm_num) hn
  omega

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
