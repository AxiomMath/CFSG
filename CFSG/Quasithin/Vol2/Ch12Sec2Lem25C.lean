module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25Coh
public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem mem_centralizer_sup {H K : Subgroup G} {c : G}
    (hH : c ∈ Subgroup.centralizer (H : Set G)) (hK : c ∈ Subgroup.centralizer (K : Set G)) :
    c ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have h1 : H ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp ((Subgroup.zpowers_le).mpr hH)
  have h2 : K ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp ((Subgroup.zpowers_le).mpr hK)
  exact (Subgroup.le_centralizer_iff.mpr (sup_le h1 h2)) (Subgroup.mem_zpowers c)

theorem actionOn_conj_eq_or_eq_inv {U W : Subgroup G} {h x : G} {p : ℕ} (hp : p.Prime)
    (hord : orderOf h = p) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hW2 : ∀ w ∈ W, w * w = 1) (hhU : h ∈ Subgroup.normalizer (U : Set G))
    (hUP : U ⊓ Subgroup.centralizer (Subgroup.zpowers h : Set G) = ⊥) (hU1 : U ≠ ⊥)
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hxW : x ∈ Subgroup.centralizer (W : Set G))
    (hxc : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ W) (hxh : x * h * x⁻¹ ∈ U ⊔ Subgroup.zpowers h) :
    A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨x, hxU⟩ *
        A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨h, hhU⟩ *
        (A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨x, hxU⟩)⁻¹ =
        A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨h, hhU⟩ ∨
      A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨x, hxU⟩ *
        A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨h, hhU⟩ *
        (A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨x, hxU⟩)⁻¹ =
        (A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨h, hhU⟩)⁻¹ := by
  set φ := A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl with hφ
  have hX2 : φ ⟨x, hxU⟩ * φ ⟨x, hxU⟩ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have hc := hxc y y.2
    set c := x * (y : G) * x⁻¹ * (y : G)⁻¹ with hcdef
    have h1 : x * (y : G) * x⁻¹ = c * y := by rw [hcdef]; group
    have h2 : x * c * x⁻¹ = c := by
      rw [← Subgroup.mem_centralizer_iff.mp hxW _ hc, mul_inv_cancel_right]
    show x * (x * (y : G) * x⁻¹) * x⁻¹ = y
    calc x * (x * (y : G) * x⁻¹) * x⁻¹ = x * (c * y) * x⁻¹ := by rw [h1]
      _ = (x * c * x⁻¹) * (x * (y : G) * x⁻¹) := by group
      _ = c * (c * y) := by rw [h2, h1]
      _ = y := by rw [← mul_assoc, hW2 c hc, one_mul]
  obtain ⟨u, hu, k, hk, huk⟩ :=
    Lem24.exists_mul_of_mem_sup_normal ((Subgroup.zpowers_le).mpr hhU) hxh
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hφu : φ ⟨u, Subgroup.le_normalizer hu⟩ = 1 :=
    (A4.actionOn_eq_one_iff _ _).mpr
      (Subgroup.mem_centralizer_iff.mpr fun y hy => hUab y hy u hu)
  have hconj : φ ⟨x, hxU⟩ * φ ⟨h, hhU⟩ * (φ ⟨x, hxU⟩)⁻¹ = φ ⟨h, hhU⟩ ^ m := by
    have h1 : (⟨x, hxU⟩ : ↥(Subgroup.normalizer (U : Set G))) * ⟨h, hhU⟩ * ⟨x, hxU⟩⁻¹ =
        ⟨u, Subgroup.le_normalizer hu⟩ * ⟨h, hhU⟩ ^ m :=
      Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          SubgroupClass.coe_zpow]
        exact huk.symm)
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul, hφu, one_mul, map_zpow]
  have hsq : φ ⟨h, hhU⟩ = φ ⟨h, hhU⟩ ^ (m * m) := by
    calc φ ⟨h, hhU⟩ = (φ ⟨x, hxU⟩ * φ ⟨x, hxU⟩) * φ ⟨h, hhU⟩ * (φ ⟨x, hxU⟩ * φ ⟨x, hxU⟩)⁻¹ := by
          rw [hX2, one_mul, inv_one, mul_one]
      _ = φ ⟨x, hxU⟩ * (φ ⟨x, hxU⟩ * φ ⟨h, hhU⟩ * (φ ⟨x, hxU⟩)⁻¹) * (φ ⟨x, hxU⟩)⁻¹ := by group
      _ = φ ⟨x, hxU⟩ * φ ⟨h, hhU⟩ ^ m * (φ ⟨x, hxU⟩)⁻¹ := by rw [hconj]
      _ = (φ ⟨x, hxU⟩ * φ ⟨h, hhU⟩ * (φ ⟨x, hxU⟩)⁻¹) ^ m := conj_zpow.symm
      _ = φ ⟨h, hhU⟩ ^ (m * m) := by rw [hconj, ← zpow_mul]
  have hne : φ ⟨h, hhU⟩ ≠ 1 := by
    intro h1
    rw [A4.actionOn_eq_one_iff] at h1
    apply hU1
    rw [eq_bot_iff, ← hUP]
    intro y hy
    refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute h y := (Subgroup.mem_centralizer_iff.mp h1 y hy).symm
    exact (hc.zpow_left j).eq
  have hordφ : orderOf (φ ⟨h, hhU⟩) = p := by
    have hd : orderOf (φ ⟨h, hhU⟩) ∣ p := by
      rw [← hord]
      have : orderOf (⟨h, hhU⟩ : ↥(Subgroup.normalizer (U : Set G))) = orderOf h :=
        (Subgroup.orderOf_coe _).symm
      rw [← this]
      exact orderOf_map_dvd φ _
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  have hdvd : (p : ℤ) ∣ (m - 1) * (m + 1) := by
    rw [← hordφ]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [show (m - 1) * (m + 1) = m * m - 1 by ring, zpow_sub_one, ← hsq, mul_inv_cancel]
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h1 | h1
  · left
    rw [hconj]
    have h2 : φ ⟨h, hhU⟩ ^ (m - 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hordφ]; exact h1)
    rwa [zpow_sub_one, mul_inv_eq_one] at h2
  · right
    rw [hconj]
    have h2 : φ ⟨h, hhU⟩ ^ (m + 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hordφ]; exact h1)
    rwa [zpow_add_one, mul_eq_one_iff_eq_inv] at h2

theorem mem_centralizer_of_actionOn_comm {U W A : Subgroup G} {h x : G} (hUd : U = W ⊔ A)
    (hWU : W ≤ U) (hAW : ∀ a ∈ A, h * a * h⁻¹ ∈ W) (hhU : h ∈ Subgroup.normalizer (U : Set G))
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hxW : x ∈ Subgroup.centralizer (W : Set G))
    (hc : A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨x, hxU⟩ *
        A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨h, hhU⟩ *
        (A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨x, hxU⟩)⁻¹ =
      A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl ⟨h, hhU⟩) :
    x ∈ Subgroup.centralizer (U : Set G) := by
  set φ := A4.actionOn U (Subgroup.normalizer (U : Set G)) le_rfl with hφ
  have hcomm : Commute (φ ⟨x, hxU⟩) (φ ⟨h, hhU⟩) := mul_inv_eq_iff_eq_mul.mp hc
  have hc' : φ ⟨x, hxU⟩ * φ (⟨h, hhU⟩⁻¹) = φ (⟨h, hhU⟩⁻¹) * φ ⟨x, hxU⟩ := by
    rw [map_inv]
    exact hcomm.inv_right.eq
  rw [hUd]
  refine mem_centralizer_sup hxW (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
  have hw := hAW a ha
  have e := congrArg (fun σ : MulAut ↥U => ((σ ⟨h * a * h⁻¹, hWU hw⟩ : ↥U) : G)) hc'
  simp only [hφ, MulAut.mul_apply, A4.actionOn_apply_coe, Subgroup.coe_inv, inv_inv] at e
  have hxw : x * (h * a * h⁻¹) * x⁻¹ = h * a * h⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hxW _ hw, mul_inv_cancel_right]
  rw [hxw, show h⁻¹ * (h * a * h⁻¹) * h = a by group] at e
  calc a * x = x * a * x⁻¹ * x := by rw [e]
    _ = x * a := by group

theorem conj_mul_eq_of_conj_eq_inv {M : Type*} [Group M] {a b c : M} (ha : a * c * a⁻¹ = c⁻¹)
    (hb : b * c * b⁻¹ = c⁻¹) : a * b * c * (a * b)⁻¹ = c := by
  calc a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
    _ = a * c⁻¹ * a⁻¹ := by rw [hb]
    _ = (a * c * a⁻¹)⁻¹ := by group
    _ = c := by rw [ha, inv_inv]

variable [Finite G]

theorem exists_mul_mem_centralizer_of_cocycle_axis {L V : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ v : ↥V, v * v = 1) {n : ℕ}
    (hn : 3 ≤ n) (hVn : Nat.card ↥V = 2 ^ n) (htop : autOn L V = ⊤) {q : G}
    (hqL : ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ V)
    (hqC : ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) → q * l * q⁻¹ * l⁻¹ = 1)
    {W : Subgroup ↥V} (hW : W.index = 2)
    (hax : ∀ (l : G) (hl : l ∈ L), A4.actionOn V L hLV ⟨l, hl⟩ ∈ transvAxis W →
      q * l * q⁻¹ * l⁻¹ = 1) :
    ∃ v ∈ V, v * q ∈ Subgroup.centralizer (L : Set G) := by
  classical
  let _ := MulAutTwo.zmod2Module hV2
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive ↥V) = n :=
    Nat.pow_right_injective le_rfl (MulAutTwo.card_eq_pow_finrank.symm.trans hVn)
  set ρ : ↥L →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    MulAutTwo.linEquiv.toMonoidHom.comp (A4.actionOn V L hLV) with hρ
  have hρ1 : ∀ (l : ↥L) (v : ↥V), ρ l (Additive.ofMul v) =
      Additive.ofMul (A4.actionOn V L hLV l v) := fun _ _ => rfl
  have hρt : ∀ (f : Module.Dual (ZMod 2) (Additive ↥V)) (d : Additive ↥V) (h : f d = 0),
      ∃ l, ρ l = LinearEquiv.transvection h := by
    intro f d h
    set σ : MulAut ↥V := MulAutTwo.linEquiv.symm (LinearEquiv.transvection h)
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
    refine ⟨l, ?_⟩
    show MulAutTwo.linEquiv (A4.actionOn V L hLV l) = _
    rw [hl]
    exact MulEquiv.apply_symm_apply _ _
  set δ : ↥L → Additive ↥V := fun l => Additive.ofMul ⟨q * l * q⁻¹ * (l : G)⁻¹, hqL l l.2⟩
    with hδdef
  have hδ : ∀ g h, δ (g * h) = δ g + ρ g (δ h) := by
    intro g h
    rw [hδdef, hρ1]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_add, toMul_ofMul, Subgroup.coe_mul, A4.actionOn_apply_coe]
    group
  have hker : ∀ g, ρ g = 1 → δ g = 0 := by
    intro g hg
    have h1 : A4.actionOn V L hLV g = 1 := MulAutTwo.linEquiv.injective (by
      rw [map_one]
      exact hg)
    rw [A4.actionOn_eq_one_iff] at h1
    rw [hδdef]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, toMul_zero, OneMemClass.coe_one]
    exact hqC g g.2 h1
  set f₀ := MulAutTwo.axisForm W hW with hf₀def
  have hf₀ : f₀ ≠ 0 := by
    intro h0
    have hWt : W = ⊤ := eq_top_iff.mpr fun x _ => by
      have := (MulAutTwo.axisForm_eq_zero W hW (Additive.ofMul x)).mp (by rw [← hf₀def, h0]; rfl)
      simpa using this
    rw [hWt, Subgroup.index_top] at hW
    exact absurd hW (by norm_num)
  have h₀ : ∀ (d : Additive ↥V) (h : f₀ d = 0) g, ρ g = LinearEquiv.transvection h →
      δ g = 0 := by
    intro d h g hg
    have hdW : Additive.toMul d ∈ W := (MulAutTwo.axisForm_eq_zero W hW d).mp h
    have hσ : A4.actionOn V L hLV g = MulAutTwo.linEquiv.symm (LinearEquiv.transvection h) := by
      rw [← hg]
      exact (MulEquiv.symm_apply_apply _ _).symm
    have hmem : A4.actionOn V L hLV g ∈ transvAxis W := by
      rw [hσ]
      refine ⟨fun a ha => ?_, fun x => ?_⟩
      · show Additive.toMul (LinearEquiv.transvection h (Additive.ofMul a)) = a
        rw [GroupTheory.GLnTwoSplitting.transvection_apply,
          (MulAutTwo.axisForm_eq_zero W hW _).mpr (by simpa using ha), zero_smul, add_zero,
          toMul_ofMul]
      · show Additive.toMul (LinearEquiv.transvection h (Additive.ofMul x)) * x⁻¹ ∈ W
        rw [GroupTheory.GLnTwoSplitting.transvection_apply, toMul_add, toMul_ofMul, mul_comm x,
          mul_assoc, mul_inv_cancel, mul_one]
        rcases GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one (f₀ (Additive.ofMul x))
          with h1 | h1
        · rw [h1, zero_smul, toMul_zero]
          exact W.one_mem
        · rw [h1, one_smul]
          exact hdW
    rw [hδdef]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul, toMul_zero, OneMemClass.coe_one]
    exact hax g g.2 hmem
  obtain ⟨w, hw⟩ := exists_eq_of_isCocycle_of_axis (hfin ▸ hn) ρ hρt δ hδ hker hf₀ h₀
  set v : ↥V := Additive.toMul w with hv
  have hwv : w = Additive.ofMul v := rfl
  refine ⟨v, v.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have e := hw ⟨l, hl⟩
  rw [hwv, hρ1, hδdef] at e
  have e' := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) e
  simp only [toMul_add, toMul_ofMul, Subgroup.coe_mul, A4.actionOn_apply_coe] at e'
  have hlv : l * (v : G) * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp v.2
  have hcomm : l * (v : G) * l⁻¹ * v = v * (l * (v : G) * l⁻¹) := by
    have := congrArg Subtype.val (mul_comm (⟨l * (v : G) * l⁻¹, hlv⟩ : ↥V) v)
    simpa using this
  have hvv : (v : G) * v = 1 := congrArg Subtype.val (hV2 v)
  have hav : (v : G) * (l * (v : G) * l⁻¹) * v = l * (v : G) * l⁻¹ := by
    calc (v : G) * (l * (v : G) * l⁻¹) * v = (l * (v : G) * l⁻¹) * ((v : G) * v) := by
          rw [← hcomm]; group
      _ = l * (v : G) * l⁻¹ := by rw [hvv, mul_one]
  calc l * ((v : G) * q) = (v : G) * (l * (v : G) * l⁻¹) * v * l * q := by rw [hav]; group
    _ = (v : G) * ((l * (v : G) * l⁻¹ * v) * l * q) := by group
    _ = (v : G) * ((q * l * q⁻¹ * l⁻¹) * l * q) := by rw [e']
    _ = (v : G) * q * l := by group

end Lem25

end CFSG.Quasithin.H13
