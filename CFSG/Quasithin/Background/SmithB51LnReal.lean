module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B5IrrA
public import CFSG.Quasithin.Background.SmithB51LnModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Assembly.LowTwoRank Matrix Module
open scoped Matrix

variable {V : Type} [CommGroup V] {n : ℕ}

theorem realizesVia_of_coord {D : FFModel} (hs : D.sec = ⊤) (hk : D.ker = ⊥)
    (hact : ∀ γ, D.act γ 1 = 1) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (hπ : Function.Surjective π) (hZU : Z ≤ U) (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U)
    (hHZ : ∀ h : ↥H, ∀ z ∈ Z, (h : MulAut V) z ∈ Z) (β : ↥U →* D.Amb)
    (hβs : Function.Surjective β) (hβk : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z)
    (hβe : ∀ (γ : D.Gam) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = D.act γ (β u)) :
    D.RealizesVia H U Z π := by
  have hall : ∀ m : D.Amb, m ∈ D.sec := fun m => by rw [hs]; trivial
  let κ : D.Amb →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.mk' _).comp ((MonoidHom.id D.Amb).codRestrict D.sec hall)
  have hκ : ∀ m : D.Amb, κ m = QuotientGroup.mk ⟨m, hall m⟩ := fun _ => rfl
  have hκinj : ∀ a b : D.Amb, κ a = κ b → a = b := by
    intro a b hab
    rw [hκ, hκ, QuotientGroup.eq, Subgroup.mem_subgroupOf, hk, Subgroup.mem_bot] at hab
    have : a⁻¹ * b = 1 := hab
    exact (inv_mul_eq_one.1 this)
  refine ⟨hπ, hZU, by rw [hk]; exact bot_le, hHU, hHZ, fun γ m _ => hall _, fun γ m hm => ?_,
    κ.comp β, ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · rw [hk, Subgroup.mem_bot] at hm ⊢
    rw [hm, hact]
  · intro q
    obtain ⟨⟨m, -⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := hβs m
    exact ⟨u, by rw [MonoidHom.comp_apply, hu]; rfl⟩
  · rw [← hβk u, MonoidHom.comp_apply]
    constructor
    · intro h1
      exact hκinj _ _ (h1.trans (map_one κ).symm)
    · intro h1
      rw [h1, map_one]
  · rw [MonoidHom.comp_apply, hβe γ u hu]
    have h1 : β u = (m : D.Amb) := by
      apply hκinj
      rw [← MonoidHom.comp_apply, hum, hκ]
    rw [h1, hκ]

@[expose] def RealM (L : Subgroup (MulAut V)) (W Y : Subgroup V)
    (π : ↥(StatedSL n (ZMod 2)) →* ↥L)
    (M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  Function.Surjective π ∧ Y ≤ W ∧ (∀ l : ↥L, ∀ w ∈ W, (l : MulAut V) w ∈ W) ∧
    (∀ l : ↥L, ∀ y ∈ Y, (l : MulAut V) y ∈ Y) ∧
    ∃ β : ↥W →* Multiplicative (Fin n → ZMod 2), Function.Surjective β ∧
      (∀ w : ↥W, β w = 1 ↔ (w : V) ∈ Y) ∧
      ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) (w : V) ∈ W),
        Multiplicative.toAdd (β ⟨((π γ : ↥L) : MulAut V) (w : V), hw⟩) =
          M γ *ᵥ Multiplicative.toAdd (β w)

variable {L : Subgroup (MulAut V)} {W Y : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
  {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}

theorem realM_mat_iff :
    RealM L W Y π mat ↔ (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L W Y π := by
  constructor
  · rintro ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩
    refine realizesVia_of_coord (D := FFModel.nat (StatedSL n (ZMod 2))) rfl rfl
      (fun γ => ?_) hπ hYW hLW hLY β hβs hβk (fun γ u hu => ?_)
    · show Multiplicative.ofAdd (mat γ *ᵥ Multiplicative.toAdd (1 : Multiplicative _)) = 1
      rw [toAdd_one, mulVec_zero]
      rfl
    · have := hβe γ u hu
      apply Multiplicative.toAdd.injective
      exact this
  · intro h
    obtain ⟨β, hβs, hβk, hβe⟩ :=
      FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL n (ZMod 2))) rfl rfl h
    obtain ⟨hπ, hYW, -, hLW, hLY, -, -, -⟩ := h
    exact ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, fun γ w hw =>
      congrArg Multiplicative.toAdd (hβe γ w hw)⟩

theorem realM_dmat_iff :
    RealM L W Y π dmat ↔ (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia L W Y π := by
  constructor
  · rintro ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩
    refine realizesVia_of_coord (D := FFModel.dualNat (StatedSL n (ZMod 2))) rfl rfl
      (fun γ => ?_) hπ hYW hLW hLY β hβs hβk (fun γ u hu => ?_)
    · show Multiplicative.ofAdd (dmat γ *ᵥ Multiplicative.toAdd (1 : Multiplicative _)) = 1
      rw [toAdd_one, mulVec_zero]
      rfl
    · have := hβe γ u hu
      apply Multiplicative.toAdd.injective
      exact this
  · intro h
    obtain ⟨β, hβs, hβk, hβe⟩ :=
      FFModel.RealizesVia.coord (D := FFModel.dualNat (StatedSL n (ZMod 2))) rfl rfl h
    obtain ⟨hπ, hYW, -, hLW, hLY, -, -, -⟩ := h
    exact ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, fun γ w hw =>
      congrArg Multiplicative.toAdd (hβe γ w hw)⟩

@[expose] def fixM (M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2))
    (B : Subgroup ↥(StatedSL n (ZMod 2))) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | ∀ g ∈ B, M g *ᵥ x = x}
  add_mem' := fun ha hb g hg => by rw [mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => mulVec_zero _
  smul_mem' := fun c x hx g hg => by rw [mulVec_smul, hx g hg]

theorem fixM_mat (B : Subgroup ↥(StatedSL n (ZMod 2))) : fixM mat B = fixN B := rfl

theorem fixM_dmat (B : Subgroup ↥(StatedSL n (ZMod 2))) : fixM dmat B = fixD B := rfl

theorem mk_mem_fixV_autSec_iff {B : Subgroup (MulAut V)} (hBW : B ≤ stabSub W)
    (hBY : B ≤ stabSub Y) (w : ↥W) :
    (QuotientGroup.mk w : Sec W Y) ∈ fixV (autSec B W Y) ↔ ∀ b ∈ B, b (w : V) * (w : V)⁻¹ ∈ Y := by
  rw [autSec, mk_mem_fixV_autQuot]
  constructor
  · intro h b hb
    have hg : resHom W ⟨b, hBW hb⟩ ∈ autSub B W := mem_autSub.2 ⟨⟨b, hBW hb⟩, hb, rfl⟩
    have := h _ hg (autSub_le_stabSub_subgroupOf hBY hg)
    rw [Subgroup.mem_subgroupOf] at this
    simpa [resHom_apply] using this
  · intro h g hg _
    obtain ⟨b, hb, rfl⟩ := mem_autSub.1 hg
    rw [Subgroup.mem_subgroupOf]
    simpa [resHom_apply] using h b hb

theorem RealM.hLW (h : RealM L W Y π M) : L ≤ stabSub W := fun l hl =>
  mem_stabSub_of_inv (h.2.2.1 ⟨l, hl⟩) (h.2.2.1 ⟨l⁻¹, L.inv_mem hl⟩)

theorem RealM.hLY (h : RealM L W Y π M) : L ≤ stabSub Y := fun l hl =>
  mem_stabSub_of_inv (h.2.2.2.1 ⟨l, hl⟩) (h.2.2.2.1 ⟨l⁻¹, L.inv_mem hl⟩)

@[expose] def pre (π : ↥(StatedSL n (ZMod 2)) →* ↥L) (B : Subgroup (MulAut V)) :
    Subgroup ↥(StatedSL n (ZMod 2)) :=
  (B.subgroupOf L).comap π

theorem mem_pre {B : Subgroup (MulAut V)} {γ : ↥(StatedSL n (ZMod 2))} :
    γ ∈ pre π B ↔ ((π γ : ↥L) : MulAut V) ∈ B := Iff.rfl

theorem RealM.fixed_iff (h : RealM L W Y π M) {β : ↥W →* Multiplicative (Fin n → ZMod 2)}
    (hβk : ∀ w : ↥W, β w = 1 ↔ (w : V) ∈ Y)
    (hβe : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : ↥W) (hw : ((π γ : ↥L) : MulAut V) (w : V) ∈ W),
      Multiplicative.toAdd (β ⟨((π γ : ↥L) : MulAut V) (w : V), hw⟩) =
        M γ *ᵥ Multiplicative.toAdd (β w))
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) (w : ↥W) :
    (∀ b ∈ B, b (w : V) * (w : V)⁻¹ ∈ Y) ↔ Multiplicative.toAdd (β w) ∈ fixM M (pre π B) := by
  constructor
  · intro hw γ hγ
    have hmem := hw _ hγ
    have hW' : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := h.2.2.1 (π γ) w w.2
    have h1 : β (⟨((π γ : ↥L) : MulAut V) (w : V), hW'⟩ * w⁻¹) = 1 := (hβk _).2 hmem
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [← hβe γ w hW', h1]
  · intro hw b hb
    obtain ⟨γ, hγ⟩ := h.1 ⟨b, hBL hb⟩
    have hγB : γ ∈ pre π B := by rw [mem_pre, hγ]; exact hb
    have hW' : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := h.2.2.1 (π γ) w w.2
    have h1 := hβe γ w hW'
    rw [hw γ hγB] at h1
    have h2 : β ⟨((π γ : ↥L) : MulAut V) (w : V), hW'⟩ = β w := Multiplicative.toAdd.injective h1
    have h3 : β (⟨((π γ : ↥L) : MulAut V) (w : V), hW'⟩ * w⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 : ((π γ : ↥L) : MulAut V) (w : V) * (w : V)⁻¹ ∈ Y := (hβk _).1 h3
    rw [hγ] at h4
    exact h4

theorem RealM.card_fixV_autSec [Finite V] (h : RealM L W Y π M) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) :
    Nat.card (fixV (autSec B W Y)) = 2 ^ finrank (ZMod 2) (fixM M (pre π B)) := by
  classical
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  have hker : β.ker = Y.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  let e : Sec W Y ≃* Multiplicative (Fin n → ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβs)
  have he : ∀ w : ↥W, e (QuotientGroup.mk w) = β w := fun w => rfl
  have hBW : B ≤ stabSub W := hBL.trans (RealM.hLW ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩)
  have hBY : B ≤ stabSub Y := hBL.trans (RealM.hLY ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩)
  have hmem : ∀ s : Sec W Y, s ∈ fixV (autSec B W Y) ↔
      Multiplicative.toAdd (e s) ∈ fixM M (pre π B) := by
    intro s
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    rw [mk_mem_fixV_autSec_iff hBW hBY, he]
    exact RealM.fixed_iff ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ hβk hβe hBL w
  let f : ↥(fixV (autSec B W Y)) ≃ ↥(fixM M (pre π B)) :=
    { toFun := fun s => ⟨Multiplicative.toAdd (e s), (hmem s).1 s.2⟩
      invFun := fun x => ⟨e.symm (Multiplicative.ofAdd x), (hmem _).2 (by simp)⟩
      left_inv := fun s => by ext; simp
      right_inv := fun x => by ext; simp }
  rw [Nat.card_congr f, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem RealM.card_sec (h : RealM L W Y π M) : Nat.card (Sec W Y) = 2 ^ n := by
  obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = Y.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  let e : Sec W Y ≃* Multiplicative (Fin n → ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβs)
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (Fin n → ZMod 2) = 2 ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem RealM.rkIdx_fixV_autSec [Finite V] (h : RealM L W Y π M) {B : Subgroup (MulAut V)}
    (hBL : B ≤ L) :
    rkIdx (fixV (autSec B W Y)) = n - finrank (ZMod 2) (fixM M (pre π B)) := by
  have h1 := rk_add_rkIdx (fixV (autSec B W Y))
  have h2 : rk (fixV (autSec B W Y)) = finrank (ZMod 2) (fixM M (pre π B)) := by
    unfold rk
    rw [h.card_fixV_autSec hBL, padicValNat.prime_pow]
  have h3 : rk (Sec W Y) = n := by
    unfold rk
    rw [h.card_sec, padicValNat.prime_pow]
  omega

theorem RealM.commN_le_fixN (h : RealM L W Y π mat) {B : Subgroup (MulAut V)}
    (hq : IsQuadratic B) : commN (pre π B) ≤ fixN (pre π B) := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  rw [commN, Submodule.span_le]
  rintro _ ⟨γ, hγ, x, rfl⟩
  obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd x)
  have hW' : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := hLW (π γ) w w.2
  have hc : ((π γ : ↥L) : MulAut V) (w : V) * (w : V)⁻¹ ∈ fixV B :=
    hq (Subgroup.subset_closure ⟨_, hγ, w, rfl⟩)
  set c : ↥W := ⟨((π γ : ↥L) : MulAut V) (w : V), hW'⟩ * w⁻¹ with hcdef
  have hcx : Multiplicative.toAdd (β c) = mat γ *ᵥ x - x := by
    rw [hcdef, map_mul, map_inv, toAdd_mul, toAdd_inv, hβe γ w hW', hw, toAdd_ofAdd,
      sub_eq_add_neg]
  intro δ hδ
  have hcW' : ((π δ : ↥L) : MulAut V) (c : V) ∈ W := hLW (π δ) c c.2
  have h1 := hβe δ c hcW'
  have h2 : (⟨((π δ : ↥L) : MulAut V) (c : V), hcW'⟩ : ↥W) = c :=
    Subtype.ext (hc _ hδ)
  rw [h2, hcx] at h1
  exact h1.symm

theorem RealM.eq_or_eq_aux {β : ↥W →* Multiplicative (Fin n → ZMod 2)}
    (hβk : ∀ w : ↥W, β w = 1 ↔ (w : V) ∈ Y) {X : Subgroup V}
    (hYX : Y ≤ X) (hXW : X ≤ W)
    (hX : ((X.subgroupOf W).map β) = ⊥ ∨ ((X.subgroupOf W).map β) = ⊤) : X = Y ∨ X = W := by
  rcases hX with h0 | h1
  · left
    refine le_antisymm (fun x hx => ?_) hYX
    have : β ⟨x, hXW hx⟩ ∈ (X.subgroupOf W).map β := ⟨⟨x, hXW hx⟩, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact (hβk _).1 this
  · right
    refine le_antisymm hXW (fun w hw => ?_)
    have : β ⟨w, hw⟩ ∈ (X.subgroupOf W).map β := by rw [h1]; trivial
    obtain ⟨x, hx, hxw⟩ := this
    have h2 : β (⟨w, hw⟩ * x⁻¹) = 1 := by rw [map_mul, map_inv, hxw, mul_inv_cancel]
    have h3 := (hβk _).1 h2
    have h4 : (w : V) * ((x : ↥W) : V)⁻¹ ∈ X := hYX h3
    have h5 : ((x : ↥W) : V) ∈ X := hx
    have := X.mul_mem h4 h5
    simpa using this

theorem RealM.eq_or_eq (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat) {X : Subgroup V}
    (hX : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X) (hYX : Y ≤ X) (hXW : X ≤ W) : X = Y ∨ X = W := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  apply RealM.eq_or_eq_aux hβk hYX hXW
  set Xb := (X.subgroupOf W).map β with hXb
  set Xa : AddSubgroup (Fin n → ZMod 2) := Subgroup.toAddSubgroup' Xb with hXa
  have hXa : ∀ y, y ∈ Xa ↔ Multiplicative.ofAdd y ∈ Xb := fun y => Iff.rfl
  have hinvA : ∀ γ : ↥(StatedSL n (ZMod 2)), ∀ y ∈ Xa, M γ *ᵥ y ∈ Xa := by
    intro γ y hy
    rw [hXa] at hy ⊢
    obtain ⟨u, hu, huy⟩ := hy
    have hW' : ((π γ : ↥L) : MulAut V) (u : V) ∈ W := hLW (π γ) u u.2
    refine ⟨⟨_, hW'⟩, hX _ (π γ).2 _ hu, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβe γ u hW', huy, toAdd_ofAdd, toAdd_ofAdd]
  have hcase : Xa = ⊥ ∨ Xa = ⊤ := by
    rcases hM with rfl | rfl
    · exact eq_bot_or_eq_top hinvA
    · exact eq_bot_or_eq_top_dual hinvA
  rcases hcase with h0 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have : Multiplicative.toAdd x ∈ Xa := hx
    rw [h0, AddSubgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact this
  · right
    rw [eq_top_iff]
    intro x _
    have : Multiplicative.toAdd x ∈ Xa := by rw [h1]; trivial
    exact this

theorem RealM.injective (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat) :
    Function.Injective π := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hfix : ∀ x, M γ *ᵥ x = x := by
    intro x
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd x)
    have hW' : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := hLW (π γ) w w.2
    have h1 := hβe γ w hW'
    have h2 : (⟨((π γ : ↥L) : MulAut V) (w : V), hW'⟩ : ↥W) = w := by
      apply Subtype.ext
      show ((π γ : ↥L) : MulAut V) (w : V) = (w : V)
      rw [hγ]
      rfl
    rw [h2, hw, toAdd_ofAdd] at h1
    exact h1.symm
  rcases hM with rfl | rfl
  · exact eq_of_mulVec_eq fun x => by rw [hfix, mat_one, one_mulVec]
  · have h1 : ∀ x, mat γ⁻¹ *ᵥ x = x := by
      intro x
      have h2 := congrArg (fun y => (mat γ⁻¹)ᵀᵀ *ᵥ y) (hfix 0)
      have h3 : dmat γ = 1 := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro y
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix, one_mulVec]
      have h4 : mat γ⁻¹ = 1 := by
        have := congrArg Matrix.transpose h3
        rwa [dmat, transpose_transpose, transpose_one] at this
      rw [h4, one_mulVec]
    have h5 : γ⁻¹ = 1 := eq_of_mulVec_eq fun x => by rw [h1, mat_one, one_mulVec]
    exact inv_eq_one.1 h5

theorem exists_ne_one (hn : 2 ≤ n) (hM : M = mat ∨ M = dmat) :
    ∃ γ : ↥(StatedSL n (ZMod 2)), ∃ x, M γ *ᵥ x ≠ x := by
  have hx : (Pi.single ⟨0, by omega⟩ 1 : Fin n → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have hy : (Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 : Fin n → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have hxy : (Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 : Fin n → ZMod 2) ≠
      Pi.single ⟨0, by omega⟩ 1 := by
    intro h
    have := congrFun h ⟨1, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := exists_mulVec_eq hx hy
  rcases hM with rfl | rfl
  · exact ⟨g, _, by rw [hg]; exact hxy⟩
  · obtain ⟨g', hg'⟩ := exists_dmat_eq (g : GL (Fin n) (ZMod 2))
    refine ⟨g', Pi.single ⟨0, by omega⟩ 1, ?_⟩
    rw [hg']
    show mat g *ᵥ _ ≠ _
    rw [hg]
    exact hxy

theorem RealM.mem_of_fixed (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat) (hn : 2 ≤ n)
    {w : V} (hw : w ∈ W) (hfix : ∀ l ∈ L, l w * w⁻¹ ∈ Y) : w ∈ Y := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  have hfx := (RealM.fixed_iff ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ hβk hβe le_rfl ⟨w, hw⟩).1 hfix
  have hinv : ∀ γ : ↥(StatedSL n (ZMod 2)), ∀ y ∈ (fixM M (pre π L)).toAddSubgroup,
      M γ *ᵥ y ∈ (fixM M (pre π L)).toAddSubgroup := by
    intro γ y hy δ hδ
    have hy' : M δ *ᵥ y = y := hy δ hδ
    have hγ : γ ∈ pre π L := (π γ).2
    have hy'' : M γ *ᵥ y = y := hy γ hγ
    rw [hy'', hy']
  have hne : (fixM M (pre π L)).toAddSubgroup ≠ ⊤ := by
    intro htop
    obtain ⟨γ, x, hx⟩ := exists_ne_one hn hM
    have hxm : x ∈ (fixM M (pre π L)).toAddSubgroup := by rw [htop]; trivial
    exact hx (hxm γ (π γ).2)
  have hcase : (fixM M (pre π L)).toAddSubgroup = ⊥ := by
    rcases hM with rfl | rfl
    · exact (eq_bot_or_eq_top hinv).resolve_right hne
    · exact (eq_bot_or_eq_top_dual hinv).resolve_right hne
  have h0 : Multiplicative.toAdd (β ⟨w, hw⟩) ∈ (fixM M (pre π L)).toAddSubgroup := hfx
  rw [hcase, AddSubgroup.mem_bot] at h0
  exact (hβk _).1 h0

end CFSG.Quasithin.B5.Ln
