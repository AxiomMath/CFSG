module

public import Mathlib.GroupTheory.Index
import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

structure KData (B Bg T Tg K : Subgroup G) : Prop where
  K_comm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a
  K_sq : ∀ a ∈ K, a * a = 1
  B_le : B ≤ T ⊓ K
  Bg_le : Bg ≤ Tg ⊓ K
  T_K : ∀ t ∈ T, ∀ k ∈ K, ⁅t, k⁆ ∈ T ⊓ K
  Tg_K : ∀ t ∈ Tg, ∀ k ∈ K, ⁅t, k⁆ ∈ Tg ⊓ K
  T_T0 : ∀ t ∈ T, ∀ x ∈ T ⊓ K, ⁅t, x⁆ ∈ B
  T_B : ∀ t ∈ T, ∀ b ∈ B, t * b = b * t
  T_Bg : ∀ t ∈ T, ∀ b ∈ Bg, ⁅t, b⁆ ∈ B
  Tg_B : ∀ t ∈ Tg, ∀ b ∈ B, ⁅t, b⁆ ∈ Bg
  T_sq : ∀ t ∈ T, t * t ∈ B

namespace KData

variable {B Bg T Tg K : Subgroup G} (D : KData B Bg T Tg K)
include D

theorem alt {t : G} (ht : t ∈ T) {y : G} (hy : y ∈ K) : ⁅t, ⁅t, y⁆⁆ = 1 := by
  have hu : t * y * t⁻¹ ∈ K := by
    have h1 := (D.T_K t ht y hy).2
    have : t * y * t⁻¹ = ⁅t, y⁆ * y := by simp [commutatorElement_def, mul_assoc]
    rw [this]; exact K.mul_mem h1 hy
  have hz : ⁅t, y⁆ ∈ K := (D.T_K t ht y hy).2
  have ht2 : t * t ∈ K := (D.B_le (D.T_sq t ht)).2
  have hc : t * t * y = y * (t * t) := D.K_comm _ ht2 _ hy
  have h1 : t * ⁅t, y⁆ * t⁻¹ = y * (t * y * t⁻¹)⁻¹ := by
    calc t * ⁅t, y⁆ * t⁻¹ = (t * t * y) * (t⁻¹ * t⁻¹) * (t * y⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = (y * (t * t)) * (t⁻¹ * t⁻¹) * (t * y⁻¹ * t⁻¹) := by rw [hc]
      _ = y * (t * y * t⁻¹)⁻¹ := by group
  have hsq := D.K_sq (y * (t * y * t⁻¹)⁻¹) (K.mul_mem hy (K.inv_mem hu))
  calc ⁅t, ⁅t, y⁆⁆ = (t * ⁅t, y⁆ * t⁻¹) * ⁅t, y⁆⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = (y * (t * y * t⁻¹)⁻¹) * (y * (t * y * t⁻¹)⁻¹) := by
        rw [h1]; simp only [commutatorElement_def]; group
    _ = 1 := hsq

omit D in
theorem rearr {C : Type*} [CommGroup C] (f d c g e x : C) (hc : c * c = 1) :
    f * d * c * (g * e) * (c * x) = x * e * d * g * f := by
  calc f * d * c * (g * e) * (c * x) = (c * c) * (f * d * g * e * x) := by ac_rfl
    _ = x * e * d * g * f := by rw [hc, one_mul]; ac_rfl

theorem weyl {t t' : G} (ht : t ∈ T) (ht' : t' ∈ Tg)
    (hw : ∀ x ∈ T ⊓ K, (t * t' * t) * x * (t * t' * t)⁻¹ ∈ Tg ⊓ K) :
    ∀ x ∈ T ⊓ K, ∃ b ∈ B, x * ⁅t, ⁅t', x⁆⁆ * b ∈ T ⊓ Tg := by
  intro x hx
  set c₁ : G := ⁅t, x⁆ with hc₁def
  set e₁ : G := ⁅t', x⁆ with he₁def
  set d₁ : G := ⁅t', c₁⁆ with hd₁def
  set g₁ : G := ⁅t, e₁⁆ with hg₁def
  set f₁ : G := ⁅t, d₁⁆ with hf₁def
  have hc₁B : c₁ ∈ B := D.T_T0 t ht x hx
  have hc₁K : c₁ ∈ K := (D.B_le hc₁B).2
  have hxK : x ∈ K := hx.2
  have he₁ : e₁ ∈ Tg ⊓ K := D.Tg_K t' ht' x hxK
  have hd₁ : d₁ ∈ Bg := D.Tg_B t' ht' c₁ hc₁B
  have hg₁ : g₁ ∈ T ⊓ K := D.T_K t ht e₁ he₁.2
  have hf₁ : f₁ ∈ B := D.T_Bg t ht d₁ hd₁
  have hcomm : t * c₁ = c₁ * t := D.T_B t ht c₁ hc₁B
  have h1 : t * x * t⁻¹ = c₁ * x := by rw [hc₁def]; simp [commutatorElement_def]
  have h2 : t' * (c₁ * x) * t'⁻¹ = (d₁ * c₁) * (e₁ * x) := by
    rw [hd₁def, he₁def]; simp only [commutatorElement_def]; group
  have h3 : t * ((d₁ * c₁) * (e₁ * x)) * t⁻¹ = (f₁ * d₁) * c₁ * (g₁ * e₁) * (c₁ * x) := by
    have hcc : t * c₁ * t⁻¹ = c₁ := by rw [hcomm]; group
    calc t * ((d₁ * c₁) * (e₁ * x)) * t⁻¹
        = (t * d₁ * t⁻¹) * (t * c₁ * t⁻¹) * ((t * e₁ * t⁻¹) * (t * x * t⁻¹)) := by group
      _ = (f₁ * d₁) * c₁ * (g₁ * e₁) * (c₁ * x) := by
        rw [hcc, h1]
        have e1 : t * d₁ * t⁻¹ = f₁ * d₁ := by rw [hf₁def]; simp [commutatorElement_def]
        have e2 : t * e₁ * t⁻¹ = g₁ * e₁ := by rw [hg₁def]; simp [commutatorElement_def]
        rw [e1, e2]; simp only [mul_assoc]
  have hconj : (t * t' * t) * x * (t * t' * t)⁻¹ = (f₁ * d₁) * c₁ * (g₁ * e₁) * (c₁ * x) := by
    rw [← h3, ← h2, ← h1]; group
  haveI : IsMulCommutative ↥K := ⟨⟨fun a b => Subtype.ext (D.K_comm a a.2 b b.2)⟩⟩
  letI : CommGroup ↥K := IsMulCommutative.instCommGroup
  have hcc1 : (⟨c₁, hc₁K⟩ : ↥K) * ⟨c₁, hc₁K⟩ = 1 := Subtype.ext (D.K_sq c₁ hc₁K)
  have hre := rearr (⟨f₁, (D.B_le hf₁).2⟩ : ↥K) ⟨d₁, (D.Bg_le hd₁).2⟩ ⟨c₁, hc₁K⟩ ⟨g₁, hg₁.2⟩
    ⟨e₁, he₁.2⟩ ⟨x, hxK⟩ hcc1
  have hre' : (f₁ * d₁) * c₁ * (g₁ * e₁) * (c₁ * x) = x * e₁ * d₁ * g₁ * f₁ :=
    congrArg Subtype.val hre
  have hY := hw x hx
  rw [hconj, hre'] at hY
  refine ⟨f₁, hf₁, ?_⟩
  have hed : e₁ * d₁ ∈ Tg ⊓ K := (Tg ⊓ K).mul_mem he₁ (D.Bg_le hd₁)
  have hsub : (⟨x, hxK⟩ : ↥K) * ⟨g₁, hg₁.2⟩ * ⟨f₁, (D.B_le hf₁).2⟩ =
      (⟨x, hxK⟩ * ⟨e₁, he₁.2⟩ * ⟨d₁, (D.Bg_le hd₁).2⟩ * ⟨g₁, hg₁.2⟩ * ⟨f₁, (D.B_le hf₁).2⟩) *
        (⟨e₁, he₁.2⟩ * ⟨d₁, (D.Bg_le hd₁).2⟩)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; ac_rfl
  have hxgf : x * g₁ * f₁ = (x * e₁ * d₁ * g₁ * f₁) * (e₁ * d₁)⁻¹ := congrArg Subtype.val hsub
  have hTg : x * g₁ * f₁ ∈ Tg ⊓ K := by
    rw [hxgf]; exact (Tg ⊓ K).mul_mem hY ((Tg ⊓ K).inv_mem hed)
  have hT : x * g₁ * f₁ ∈ T ⊓ K := (T ⊓ K).mul_mem ((T ⊓ K).mul_mem hx hg₁) (D.B_le hf₁)
  exact ⟨hT.1, hTg.1⟩

theorem key1 {t t' : G} (ht : t ∈ T) (ht' : t' ∈ Tg)
    (hw : ∀ x ∈ T ⊓ K, (t * t' * t) * x * (t * t' * t)⁻¹ ∈ Tg ⊓ K) :
    ∀ x ∈ T ⊓ K, ∃ a ∈ T ⊓ Tg, ⁅t, x * a⁻¹⁆ = 1 := by
  intro x hx
  obtain ⟨b, hb, ha⟩ := D.weyl ht ht' hw x hx
  refine ⟨x * ⁅t, ⁅t', x⁆⁆ * b, ha, ?_⟩
  have hyK : ⁅t', x⁆ ∈ K := (D.Tg_K t' ht' x hx.2).2
  have hzK : ⁅t, ⁅t', x⁆⁆ ∈ K := (D.T_K t ht _ hyK).2
  have hbK : b ∈ K := (D.B_le hb).2
  have hxK : x ∈ K := hx.2
  have halt : ⁅t, ⁅t, ⁅t', x⁆⁆⁆ = 1 := D.alt ht hyK
  set z := ⁅t, ⁅t', x⁆⁆ with hz
  have h1 : t * z * t⁻¹ = z := by
    have : ⁅t, z⁆ = 1 := halt
    rw [commutatorElement_def] at this
    calc t * z * t⁻¹ = (t * z * t⁻¹ * z⁻¹) * z := by group
      _ = z := by rw [this, one_mul]
  have h2 : t * b * t⁻¹ = b := by rw [D.T_B t ht b hb]; group
  have hzb : t * (z * b) * t⁻¹ = z * b := by
    calc t * (z * b) * t⁻¹ = (t * z * t⁻¹) * (t * b * t⁻¹) := by group
      _ = z * b := by rw [h1, h2]
  have e1 : x * (x * z * b)⁻¹ = (z * b)⁻¹ := by
    have hc : x * (b⁻¹ * z⁻¹) = (b⁻¹ * z⁻¹) * x :=
      D.K_comm x hxK _ (K.mul_mem (K.inv_mem hbK) (K.inv_mem hzK))
    calc x * (x * z * b)⁻¹ = x * (b⁻¹ * z⁻¹) * x⁻¹ := by group
      _ = ((b⁻¹ * z⁻¹) * x) * x⁻¹ := by rw [hc]
      _ = (z * b)⁻¹ := by group
  rw [e1, commutatorElement_def]
  calc t * (z * b)⁻¹ * t⁻¹ * ((z * b)⁻¹)⁻¹ = (t * (z * b) * t⁻¹)⁻¹ * (z * b) := by group
    _ = 1 := by rw [hzb]; group

theorem comm_mul {t : G} (ht : t ∈ T) {y y' : G} (hy : y ∈ K) (hy' : y' ∈ K) :
    ⁅t, y * y'⁆ = ⁅t, y⁆ * ⁅t, y'⁆ := by
  have hc : y * ⁅t, y'⁆ = ⁅t, y'⁆ * y := D.K_comm y hy _ (D.T_K t ht y' hy').2
  calc ⁅t, y * y'⁆ = (t * y * t⁻¹) * (t * y' * t⁻¹) * y'⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (⁅t, y⁆ * y) * (⁅t, y'⁆ * y') * y'⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅t, y⁆ * (y * ⁅t, y'⁆) * y⁻¹ := by group
    _ = ⁅t, y⁆ * ⁅t, y'⁆ := by rw [hc]; group

omit D in
theorem relIndex_eq_of_le {H K : Subgroup G} [Finite G] (hHK : H ≤ K)
    (h : H.index = K.index) : H = K := by
  have h1 := Subgroup.relIndex_mul_index hHK
  have h2 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : H.relIndex K = 1 := by
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h2) (by rw [h1, one_mul])
  exact le_antisymm hHK (Subgroup.relIndex_eq_one.mp h3)

theorem inj_mod [Finite G] {t t' : G} (ht : t ∈ T) (ht' : t' ∈ Tg)
    (hw : ∀ x ∈ T ⊓ K, (t * t' * t) * x * (t * t' * t)⁻¹ ∈ Tg ⊓ K)
    (hcard : (Bg ⊔ (T ⊓ Tg)).relIndex (Tg ⊓ K) = (B ⊔ (T ⊓ Tg)).relIndex (T ⊓ K))
    (hS : B ⊔ (T ⊓ Tg) ≤ T ⊓ K) :
    ∀ y ∈ Tg ⊓ K, ⁅t, y⁆ ∈ B ⊔ (T ⊓ Tg) → y ∈ Bg ⊔ (T ⊓ Tg) := by
  classical
  set S := B ⊔ (T ⊓ Tg) with hSdef
  set S' := Bg ⊔ (T ⊓ Tg) with hS'def
  set T₀ := T ⊓ K with hT₀
  set T₀' := Tg ⊓ K with hT₀'
  haveI : IsMulCommutative ↥T₀ := ⟨⟨fun a b => Subtype.ext (D.K_comm a (a.2).2 b (b.2).2)⟩⟩
  haveI : (S.subgroupOf T₀).Normal := Subgroup.normal_of_comm _
  have hmemT₀ : ∀ y ∈ T₀', ⁅t, y⁆ ∈ T₀ := fun y hy => D.T_K t ht y hy.2
  let Dh : ↥T₀' →* ↥T₀ :=
    { toFun := fun y => ⟨⁅t, y⁆, hmemT₀ y y.2⟩
      map_one' := by apply Subtype.ext; simp [commutatorElement_def]
      map_mul' := fun y y' => by
        apply Subtype.ext
        exact D.comm_mul ht y.2.2 y'.2.2 }
  let φ : ↥T₀' →* ↥T₀ ⧸ S.subgroupOf T₀ := (QuotientGroup.mk' (S.subgroupOf T₀)).comp Dh
  have hφ : ∀ y : ↥T₀', φ y = 1 ↔ ⁅t, (y : G)⁆ ∈ S := fun y => by
    show QuotientGroup.mk' (S.subgroupOf T₀) (Dh y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, hb, ha⟩ := D.weyl ht ht' hw ((x : G)⁻¹) (T₀.inv_mem x.2)
      set y : G := ⁅t', (x : G)⁻¹⁆ with hy
      have hyT₀' : y ∈ T₀' := D.Tg_K t' ht' _ ((T₀.inv_mem x.2).2)
      refine ⟨⟨y, hyT₀'⟩, ?_⟩
      show QuotientGroup.mk' (S.subgroupOf T₀) (Dh ⟨y, hyT₀'⟩) = QuotientGroup.mk' _ x
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hS1 : (x : G)⁻¹ * ⁅t, y⁆ ∈ S := by
        have e : (x : G)⁻¹ * ⁅t, y⁆ = ((x : G)⁻¹ * ⁅t, y⁆ * b) * b⁻¹ := by group
        rw [e]
        exact S.mul_mem ((le_sup_right : T ⊓ Tg ≤ S) ha) (S.inv_mem (Subgroup.mem_sup_left hb))
      have e2 : (⁅t, y⁆)⁻¹ * (x : G) = ((x : G)⁻¹ * ⁅t, y⁆)⁻¹ := by group
      show (⁅t, y⁆)⁻¹ * (x : G) ∈ S
      rw [e2]
      exact S.inv_mem hS1
  have hAK : T ⊓ Tg ≤ K := fun a ha => (hS ((le_sup_right : T ⊓ Tg ≤ S) ha)).2
  have hker : S'.subgroupOf T₀' ≤ φ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, hφ]
    have hyS' : (y : G) ∈ S' := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨b', hb', a, ha, hba⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun u hu v hv => D.K_comm u (hAK hu) v (D.Bg_le hv).2) hyS'
    rw [hba, D.comm_mul ht (D.Bg_le hb').2 (hAK ha)]
    exact S.mul_mem ((le_sup_left : B ≤ S) (D.T_Bg t ht b' hb'))
      ((le_sup_left : B ≤ S) (D.T_T0 t ht a ⟨ha.1, hAK ha⟩))
  have hidx : (S'.subgroupOf T₀').index = φ.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact hcard
  have hker_eq : S'.subgroupOf T₀' = φ.ker := relIndex_eq_of_le hker hidx
  intro y hy hyS
  have : (⟨y, hy⟩ : ↥T₀') ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ]; exact hyS
  rw [← hker_eq] at this
  exact Subgroup.mem_subgroupOf.mp this

theorem comm_mul_left {p κ y : G} (hκ : κ ∈ K) (hy : y ∈ K) : ⁅p * κ, y⁆ = ⁅p, y⁆ := by
  have hc : κ * y = y * κ := D.K_comm κ hκ y hy
  calc ⁅p * κ, y⁆ = p * (κ * y) * κ⁻¹ * p⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = p * (y * κ) * κ⁻¹ * p⁻¹ * y⁻¹ := by rw [hc]
    _ = ⁅p, y⁆ := by simp only [commutatorElement_def]; group

theorem card_le_relIndex [Finite G] {F : Type} [AddCommGroup F] [Finite F]
    (hF2 : ∀ s : F, s + s = 0) (u : F → G) (hu : ∀ s, u s ∈ T)
    (hadd : ∀ s s', ∃ κ ∈ T ⊓ K, u (s + s') = u s * u s' * κ)
    (hinj : ∀ s ≠ 0, ∀ y ∈ Tg ⊓ K, ⁅u s, y⁆ ∈ B ⊔ (T ⊓ Tg) → y ∈ Bg ⊔ (T ⊓ Tg))
    (hS : B ⊔ (T ⊓ Tg) ≤ T ⊓ K) {y₀ : G} (hy₀ : y₀ ∈ Tg ⊓ K)
    (hy₀S : y₀ ∉ Bg ⊔ (T ⊓ Tg)) :
    Nat.card F ≤ (B ⊔ (T ⊓ Tg)).relIndex (T ⊓ K) := by
  classical
  set S := B ⊔ (T ⊓ Tg) with hSdef
  set T₀ := T ⊓ K with hT₀
  haveI : IsMulCommutative ↥T₀ := ⟨⟨fun a b => Subtype.ext (D.K_comm a (a.2).2 b (b.2).2)⟩⟩
  haveI : (S.subgroupOf T₀).Normal := Subgroup.normal_of_comm _
  have hmem : ∀ s, ⁅u s, y₀⁆ ∈ T₀ := fun s => D.T_K (u s) (hu s) y₀ hy₀.2
  let Φ : F → ↥T₀ ⧸ S.subgroupOf T₀ := fun s => QuotientGroup.mk ⟨⁅u s, y₀⁆, hmem s⟩
  have hΦ : Function.Injective Φ := by
    intro s s' h
    have h1 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h1
    set a : G := ⁅u s, y₀⁆ with ha
    set a' : G := ⁅u s', y₀⁆ with ha'
    have haK : a ∈ K := (hmem s).2
    have ha'K : a' ∈ K := (hmem s').2
    have haa : a * a = 1 := D.K_sq a haK
    have h2 : a * a' ∈ S := by
      have : a * a' = a⁻¹ * a' := by
        have : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
        rw [this]
      rw [this]
      exact h1
    by_contra hne
    have hs0 : s + s' ≠ 0 := fun h0 => hne (by
      have := add_eq_zero_iff_eq_neg.mp h0
      rw [this, neg_eq_iff_add_eq_zero.mpr (hF2 s')]) 
    obtain ⟨κ, hκ, hu'⟩ := hadd s s'
    have h3 : ⁅u (s + s'), y₀⁆ = ⁅u s * u s', y₀⁆ := by rw [hu']; exact D.comm_mul_left hκ.2 hy₀.2
    have h4 : ⁅u s * u s', y₀⁆ = ⁅u s, a'⁆ * a' * a := by
      simp only [ha, ha', commutatorElement_def]; group
    have h5 : ⁅u s, a'⁆ ∈ B := D.T_T0 (u s) (hu s) a' (hmem s')
    have h6 : a' * a = a * a' := D.K_comm a' ha'K a haK
    have h7 : ⁅u (s + s'), y₀⁆ ∈ S := by
      rw [h3, h4, mul_assoc, h6]
      exact S.mul_mem ((le_sup_left : B ≤ S) h5) h2
    exact hy₀S (hinj (s + s') hs0 y₀ hy₀ h7)
  have := Nat.card_le_card_of_injective Φ hΦ
  exact this

theorem T0_le_sup [Finite G] {F : Type} [AddCommGroup F] [Finite F] (hF2 : ∀ s : F, s + s = 0)
    (u v : F → G) (hu : ∀ s, u s ∈ T) (hv : ∀ s, v s ∈ Tg)
    (hadd : ∀ s s', ∃ κ ∈ T ⊓ K, u (s + s') = u s * u s' * κ)
    (hgen : ∀ t ∈ T, ∃ s, ∃ κ ∈ T ⊓ K, t = u s * κ)
    (hw : ∀ s ≠ 0, ∀ x ∈ T ⊓ K, (u s * v s * u s) * x * (u s * v s * u s)⁻¹ ∈ Tg ⊓ K)
    (hS : B ⊔ (T ⊓ Tg) ≤ T ⊓ K)
    (hcard : (Bg ⊔ (T ⊓ Tg)).relIndex (Tg ⊓ K) = (B ⊔ (T ⊓ Tg)).relIndex (T ⊓ K))
    (hm : B.relIndex (T ⊓ K) ≤ Nat.card F)
    (hZ : ∀ x ∈ T, (∀ t ∈ T, x * t = t * x) → x ∈ B) (hBTg : B ⊓ Tg = ⊥)
    (hBlt : B < T ⊓ K) : T ⊓ K ≤ B ⊔ (T ⊓ Tg) := by
  classical
  by_contra hne
  set S := B ⊔ (T ⊓ Tg) with hSdef
  set S' := Bg ⊔ (T ⊓ Tg) with hS'def
  have hr1 : S.relIndex (T ⊓ K) ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
  have hT₀'S' : ¬ (Tg ⊓ K) ≤ S' := fun h => hr1 (by
    rw [← hcard]; exact Subgroup.relIndex_eq_one.mpr h)
  obtain ⟨y₀, hy₀, hy₀S'⟩ := SetLike.not_le_iff_exists.mp hT₀'S'
  have hinj : ∀ s ≠ 0, ∀ y ∈ Tg ⊓ K, ⁅u s, y⁆ ∈ S → y ∈ S' := fun s hs =>
    D.inj_mod (hu s) (hv s) (hw s hs) hcard hS
  have hcount := D.card_le_relIndex hF2 u hu hadd hinj hS hy₀ hy₀S'
  have hBS : B ≤ S := le_sup_left
  have hmul := Subgroup.relIndex_mul_relIndex B S (T ⊓ K) hBS hS
  have hpos : 0 < S.relIndex (T ⊓ K) := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hr_le : S.relIndex (T ⊓ K) ≤ B.relIndex (T ⊓ K) := by
    rw [← hmul]; exact Nat.le_mul_of_pos_left _ (by
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  have hcount' : Nat.card F ≤ S.relIndex (T ⊓ K) := hcount
  have hr_eq : S.relIndex (T ⊓ K) = B.relIndex (T ⊓ K) := le_antisymm hr_le (hm.trans hcount')
  have hBS1 : B.relIndex S = 1 := by
    rw [← hr_eq] at hmul
    have : B.relIndex S * S.relIndex (T ⊓ K) = 1 * S.relIndex (T ⊓ K) := by rw [hmul, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hSB : S ≤ B := Subgroup.relIndex_eq_one.mp hBS1
  have hA1 : T ⊓ Tg = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : a ∈ B ⊓ Tg := ⟨hSB ((le_sup_right : T ⊓ Tg ≤ S) ha), ha.2⟩
    rw [hBTg, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr h1
  have hx : ∀ x ∈ T ⊓ K, x ∈ B := by
    intro x hx
    refine hZ x hx.1 fun t ht => ?_
    obtain ⟨s, κ, hκ, rfl⟩ := hgen t ht
    have hxκ : x * κ = κ * x := D.K_comm x hx.2 κ hκ.2
    by_cases hs : s = 0
    · subst hs
      obtain ⟨κ₀, hκ₀, h00⟩ := hadd 0 0
      rw [add_zero] at h00
      have hu0 : u 0 = κ₀⁻¹ := by
        have : u 0 * (u 0 * κ₀) = u 0 * 1 := by rw [← mul_assoc, ← h00, mul_one]
        have h1 := mul_left_cancel this
        exact eq_inv_of_mul_eq_one_left h1
      have hu0K : u 0 ∈ T ⊓ K := by rw [hu0]; exact (T ⊓ K).inv_mem hκ₀
      calc x * (u 0 * κ) = (x * u 0) * κ := by rw [mul_assoc]
        _ = (u 0 * x) * κ := by rw [D.K_comm x hx.2 (u 0) hu0K.2]
        _ = u 0 * (x * κ) := by rw [mul_assoc]
        _ = u 0 * (κ * x) := by rw [hxκ]
        _ = (u 0 * κ) * x := by rw [mul_assoc]
    · obtain ⟨a, ha, h1⟩ := D.key1 (hu s) (hv s) (hw s hs) x hx
      rw [hA1, Subgroup.mem_bot] at ha
      subst ha
      have h2 : u s * x = x * u s := by
        rw [inv_one, mul_one] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      calc x * (u s * κ) = (x * u s) * κ := by rw [mul_assoc]
        _ = (u s * x) * κ := by rw [h2]
        _ = u s * (x * κ) := by rw [mul_assoc]
        _ = u s * (κ * x) := by rw [hxκ]
        _ = (u s * κ) * x := by rw [mul_assoc]
  exact absurd (fun x hx' => hx x hx') (not_le_of_gt hBlt)

end KData

end CFSG.RankThree.GF2n.Tim78
