module

public import CFSG.Quasithin.MS93.S46FFSD

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin

section Aux

variable {V : Type} [CommGroup V]

theorem fix_of_two_step {X : Type*} [Group X] (σ : X →* MulAut V) {L : Subgroup X}
    (hL : ⁅L, L⁆ = L) {U₁ U₂ : Subgroup V} (h1 : ∀ l ∈ L, ∀ u ∈ U₁, σ l u = u)
    (h2 : ∀ l ∈ L, ∀ v ∈ U₂, σ l v * v⁻¹ ∈ U₁) : ∀ l ∈ L, ∀ v ∈ U₂, σ l v = v := by
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  let d : ↥L → (↥U₂ →* ↥U₁) := fun l =>
    { toFun := fun v => ⟨σ l v * (v : V)⁻¹, h2 l l.2 v v.2⟩
      map_one' := by ext; simp
      map_mul' := fun v w => by
        ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hd : ∀ l v, ((d l v : ↥U₁) : V) = σ l v * (v : V)⁻¹ := fun _ _ => rfl
  let D : ↥L →* (↥U₂ →* ↥U₁) := MonoidHom.mk' d fun l l' => by
    ext v
    rw [MonoidHom.mul_apply, Subgroup.coe_mul, hd, hd, hd]
    have hu : σ l' v * (v : V)⁻¹ ∈ U₁ := h2 l' l'.2 v v.2
    have hfix : σ l (σ l' v * (v : V)⁻¹) = σ l' v * (v : V)⁻¹ := h1 l l.2 _ hu
    calc σ ((l * l' : ↥L) : X) v * (v : V)⁻¹
        = σ l (σ l' v * (v : V)⁻¹ * v) * (v : V)⁻¹ := by
          rw [inv_mul_cancel_right, Subgroup.coe_mul, map_mul, MulAut.mul_apply]
      _ = σ l (σ l' v * (v : V)⁻¹) * (σ l v * (v : V)⁻¹) := by rw [map_mul, mul_assoc]
      _ = (σ l v * (v : V)⁻¹) * (σ l' v * (v : V)⁻¹) := by rw [hfix, mul_comm]
  have : IsMulCommutative (↥U₂ →* ↥U₁) := ⟨⟨mul_comm⟩⟩
  have hker : D.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker D
  intro l hl v hv
  have h3 : D ⟨l, hl⟩ = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top _)
  have h4 := congrArg Subtype.val (DFunLike.congr_fun h3 ⟨v, hv⟩)
  exact mul_inv_eq_one.mp h4

theorem exists_lift {X Γ H : Type*} [Group X] [Group Γ] [Group H] (π : X →* Γ)
    (hπ : Function.Surjective π) (τ : X →* H) (hτ : ∀ x, π x = 1 → τ x = 1) :
    ∃ ρ : Γ →* H, ∀ x, ρ (π x) = τ x := by
  refine ⟨(QuotientGroup.lift π.ker τ fun x hx =>
    MonoidHom.mem_ker.mpr (hτ x (MonoidHom.mem_ker.mp hx))).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom, fun x => ?_⟩
  have : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) = (x : X ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]

end Aux

section Units

variable {V : Type} [CommGroup V]

noncomputable def zmodTwoUnits : Multiplicative (ZMod 2) →* ℂˣ :=
  MonoidHom.mk' (fun x => (-1 : ℂˣ) ^ (Multiplicative.toAdd x).val) fun x y => by
    have h2 : (-1 : ℂˣ) ^ 2 = 1 := neg_one_sq
    show (-1 : ℂˣ) ^ (Multiplicative.toAdd (x * y)).val =
      (-1) ^ (Multiplicative.toAdd x).val * (-1) ^ (Multiplicative.toAdd y).val
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add]

theorem zmodTwoUnits_injective : Function.Injective zmodTwoUnits := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (-1 : ℂˣ) ^ (Multiplicative.toAdd x).val = 1 := hx
  have hlt := ZMod.val_lt (Multiplicative.toAdd x)
  rcases (by omega : (Multiplicative.toAdd x).val = 0 ∨ (Multiplicative.toAdd x).val = 1)
    with h | h
  · exact toAdd_eq_zero.mp ((ZMod.val_eq_zero _).mp h)
  · exfalso
    rw [h, pow_one] at h1
    have := congrArg Units.val h1
    norm_num at this

noncomputable def compForm {M : Type*} [CommGroup M] (ι : M →* ℂˣ) (ω : V →* V →* M) :
    V →* V →* ℂˣ where
  toFun v := ι.comp (ω v)
  map_one' := by
    refine MonoidHom.ext fun w => ?_
    show ι (ω 1 w) = 1
    rw [map_one, MonoidHom.one_apply, map_one]
  map_mul' v v' := by
    refine MonoidHom.ext fun w => ?_
    show ι (ω (v * v') w) = ι (ω v w) * ι (ω v' w)
    rw [map_mul, MonoidHom.mul_apply, map_mul]

theorem compForm_eq_one_iff {M : Type*} [CommGroup M] {ι : M →* ℂˣ}
    (hι : Function.Injective ι) (ω : V →* V →* M) (v w : V) :
    compForm ι ω v w = 1 ↔ ω v w = 1 :=
  map_eq_one_iff ι hι

theorem perpIn_compForm {M : Type*} [CommGroup M] {ι : M →* ℂˣ} (hι : Function.Injective ι)
    (ω : V →* V →* M) (X U : Subgroup V) : perpIn (compForm ι ω) X U = perpIn ω X U := by
  ext x
  show (x ∈ X ∧ ∀ u ∈ U, compForm ι ω x u = 1) ↔ (x ∈ X ∧ ∀ u ∈ U, ω x u = 1)
  exact and_congr Iff.rfl (forall₂_congr fun u _ => compForm_eq_one_iff hι ω x u)

theorem card_mul_card_perpIn [Finite V] (f : V →* V →* ℂˣ)
    (hskew : ∀ v w, f v w = 1 → f w v = 1) (hnd : ∀ v, (∀ w, f v w = 1) → v = 1)
    (U : Subgroup V) : Nat.card U * Nat.card (perpIn f ⊤ U) = Nat.card V := by
  apply le_antisymm
  · have h := card_mul_le_of_pairing f (P₀ := perpIn f ⊤ U) (P := ⊤) (Q₀ := ⊥) (Q := U)
      le_top bot_le (fun p hp q hq => hp.2 q hq)
      (fun q hq h => (Subgroup.mem_bot).mpr (hnd q fun w => hskew _ _ (h w trivial)))
    rwa [Subgroup.card_top, Subgroup.card_bot, mul_one] at h
  · have h := card_mul_le_of_pairing f (P₀ := ⊥) (P := U) (Q₀ := perpIn f ⊤ U) (Q := ⊤)
      bot_le le_top (fun p hp q _ => by rw [Subgroup.mem_bot.mp hp, map_one,
        MonoidHom.one_apply])
      (fun q _ h => ⟨trivial, fun u hu => hskew _ _ (h u hu)⟩)
    rwa [Subgroup.card_top, Subgroup.card_bot, mul_one] at h

end Units

section NB

variable {F : Type} [Field F] [Fintype F] {n : ℕ}

theorem card_lt_of_nontrivial (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    (ρ : SL3 F →* MulAut W) (hnt : ∃ g w, ρ g w ≠ w) {B : Subgroup (SL3 F)} (hB : B ≠ ⊥)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    Nat.card B < (fixV (B.map ρ)).index * Nat.card (commV (B.map ρ)) := by
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have : Group.IsPerfect (SL3 F) := isPerfect_SL3
  by_contra hcon
  push Not at hcon
  have hinjB : B ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hb, hbk⟩
    have hc := ker_le_center ρ hnt hbk
    exact eq_one_of_pow_three (pow_three_eq_one_of_mem_center hc) (e := 1)
      (by simpa using hB2 b hb)
  have hcardB : Nat.card (B.map ρ) = Nat.card B := by
    have h := B1More.card_map_mul_card_inf_ker B ρ
    rwa [hinjB, Subgroup.card_bot, mul_one] at h
  have hB'K : B.map ρ ≤ ρ.range := Subgroup.map_le_range ρ B
  have hB'e : IsElemAbelian2 (B.map ρ) := by
    constructor
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hBc b hb b' hb']
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hB2 b hb, map_one]
  have hB'1 : B.map ρ ≠ ⊥ := by
    intro h
    apply hB
    have h1 : Nat.card B = 1 := by rw [← hcardB, h, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq B h1
  set X := commV ρ.range with hXdef
  have hXinv : ∀ g, ∀ x ∈ X, ρ g x ∈ X := fun g x hx => commV_inv ρ g hx
  have hXne : X ≠ ⊥ := by
    obtain ⟨g₀, w₀, hw₀⟩ := hnt
    intro h
    have : ρ g₀ w₀ * w₀⁻¹ ∈ X := Subgroup.subset_closure ⟨ρ g₀, mem_range_apply ρ g₀, w₀, rfl⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact hw₀ this
  obtain ⟨M₀, hM₀inv, -, hM₀X, hM₀ne, hM₀max⟩ := exists_maximal_inv ρ (R := ⊥)
    (fun g u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]) bot_le hXne.symm
  obtain ⟨g₁, x₁, hx₁, hg₁⟩ : ∃ g, ∃ x ∈ X, ρ g x * x⁻¹ ∉ M₀ := by
    by_contra h
    push Not at h
    exact hM₀ne (le_antisymm hM₀X (commV_le_of_isPerfect ρ h))
  have hntS := sec_nt ρ hXinv hM₀inv hx₁ hg₁
  have hirrS := sec_irr ρ hXinv hM₀inv hM₀X hM₀max
  have hfaith := inf_centSec_eq_bot ρ hXinv hM₀inv hntS hB'K hB'e.2
  have hcard : Nat.card W ≤ Nat.card (B.map ρ) * Nat.card (fixV (B.map ρ)) := by
    have h1 := (fixV (B.map ρ)).index_mul_card
    have hk : 1 ≤ Nat.card (commV (B.map ρ)) := Nat.card_pos
    calc Nat.card W = (fixV (B.map ρ)).index * Nat.card (fixV (B.map ρ)) := h1.symm
      _ ≤ (fixV (B.map ρ)).index * Nat.card (commV (B.map ρ)) * Nat.card (fixV (B.map ρ)) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hk)
      _ ≤ Nat.card B * Nat.card (fixV (B.map ρ)) := Nat.mul_le_mul_right _ hcon
      _ = Nat.card (B.map ρ) * Nat.card (fixV (B.map ρ)) := by rw [hcardB]
  have hffS := sec_ff ρ hXinv hM₀inv hM₀X hB'K hB'1 hB'e hcard hfaith
  obtain ⟨F', iF', fF', hFF', σ, θ, hθ⟩ := exists_natCoord (secRho ρ hXinv hM₀inv) h14 hSQ hsq
    hF' (sec_sq hW2) hirrS hntS hffS
  have : CharP F' 2 := FFC.charP_two_of_card_pow (hFF'.trans hF')
  have hBX : B.map ρ ≤ stabSub X := hB'K.trans (range_le_stabSub ρ hXinv)
  have hBM : B.map ρ ≤ stabSub M₀ := hB'K.trans (range_le_stabSub ρ hM₀inv)
  have hcBb : Nat.card (autSec (B.map ρ) X M₀) = Nat.card (B.map ρ) := by
    have := card_autSec_mul hBX hBM
    rwa [hfaith, Subgroup.card_bot, mul_one] at this
  have hBbK : autSec (B.map ρ) X M₀ ≤ (secRho ρ hXinv hM₀inv).range := by
    rw [range_secRho]
    exact autSec_mono hB'K X M₀
  have hBb1 : autSec (B.map ρ) X M₀ ≠ ⊥ := by
    intro h
    apply hB'1
    have h1 : Nat.card (B.map ρ) = 1 := by rw [← hcBb, h, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hlt := card_lt_of_coord hθ hBbK hBb1 (isElemAbelian2_autSec ρ hXinv hM₀inv hB'K hB'e)
  have hidx : (fixV (autSec (B.map ρ) X M₀)).index ≤ (fixV (B.map ρ)).index := by
    have h1 := (fixV (autSec (B.map ρ) X M₀)).index_mul_card
    have h2 := B5.card_fixV_autSec_mul hM₀X hBX hBM
    have h3 := card_sec_mul hM₀X
    have h4 := card_sup_mul_card_inf X (fixV (B.map ρ))
    have h5 : Nat.card ↥(X ⊔ fixV (B.map ρ)) ≤ Nat.card W := Subgroup.card_le_card_group _
    have h6 : Nat.card ↥(X ⊓ fixV (B.map ρ)) ≤ Nat.card (B5.fixSec (B.map ρ) X M₀) :=
      Subgroup.card_le_of_le fun x hx => ⟨hx.1, fun b hb => by
        rw [hx.2 b hb, mul_inv_cancel]
        exact M₀.one_mem⟩
    have h7 := (fixV (B.map ρ)).index_mul_card
    have hfs : 0 < Nat.card (B5.fixSec (B.map ρ) X M₀) := Nat.card_pos
    have hc : 0 < Nat.card (fixV (B.map ρ)) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hfs
    have hx : (fixV (autSec (B.map ρ) X M₀)).index * Nat.card (B5.fixSec (B.map ρ) X M₀) =
        Nat.card X := by rw [← h2, ← mul_assoc, h1, h3]
    rw [hx]
    refine Nat.le_of_mul_le_mul_right ?_ hc
    calc Nat.card X * Nat.card (fixV (B.map ρ))
        = Nat.card ↥(X ⊔ fixV (B.map ρ)) * Nat.card ↥(X ⊓ fixV (B.map ρ)) := h4.symm
      _ ≤ Nat.card W * Nat.card (B5.fixSec (B.map ρ) X M₀) := Nat.mul_le_mul h5 h6
      _ = (fixV (B.map ρ)).index * Nat.card (B5.fixSec (B.map ρ) X M₀) *
            Nat.card (fixV (B.map ρ)) := by rw [← h7]; ring
  have hcomm : Nat.card (commV (autSec (B.map ρ) X M₀)) ≤ Nat.card (commV (B.map ρ)) := by
    have h1 := card_secPre hM₀X (commV (autSec (B.map ρ) X M₀))
    have h2 : secPre X M₀ (commV (autSec (B.map ρ) X M₀)) ≤ commV (B.map ρ) ⊔ M₀ :=
      secPre_commV_le le_sup_right fun b hb w _ =>
        Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, hb, w, rfl⟩)
    have h3 := card_sup_mul_card_inf (commV (B.map ρ)) M₀
    have h4 : 0 < Nat.card ↥(commV (B.map ρ) ⊓ M₀) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card M₀)
    rw [h1]
    calc Nat.card (secPre X M₀ (commV (autSec (B.map ρ) X M₀)))
        ≤ Nat.card ↥(commV (B.map ρ) ⊔ M₀) := Subgroup.card_le_of_le h2
      _ ≤ Nat.card ↥(commV (B.map ρ) ⊔ M₀) * Nat.card ↥(commV (B.map ρ) ⊓ M₀) :=
          Nat.le_mul_of_pos_right _ h4
      _ = Nat.card (commV (B.map ρ)) * Nat.card M₀ := h3
  have : Nat.card B < (fixV (B.map ρ)).index * Nat.card (commV (B.map ρ)) :=
    calc Nat.card B = Nat.card (autSec (B.map ρ) X M₀) := by rw [hcBb, hcardB]
      _ < (fixV (autSec (B.map ρ) X M₀)).index * Nat.card (commV (autSec (B.map ρ) X M₀)) :=
          hlt
      _ ≤ (fixV (B.map ρ)).index * Nat.card (commV (B.map ρ)) := Nat.mul_le_mul hidx hcomm
  omega

end NB

section Ext

variable {F : Type} [Field F] [Fintype F] {n : ℕ} {X : Type} [Group X]

theorem sd_ext_aux (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) (π : X →* SL3 F) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 → ∃ e : ℕ, x ^ 2 ^ e = 1) (A : Subgroup X)
    (hA2 : ∀ a ∈ A, π a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, π a * π b = π b * π a)
    (hA1 : ∃ a ∈ A, π a ≠ 1) (L : Subgroup X) (hL : ⁅L, L⁆ = L) {M : Type} [CommGroup M]
    {ι : M →* ℂˣ} (hι : Function.Injective ι) (N : ℕ) :
    ∀ (S : Type) [CommGroup S] [Finite S], Nat.card S = N → (∀ s : S, s ^ 2 = 1) →
      ∀ (σ : X →* MulAut S) (ω : S →* S →* M), (∀ s, ω s s = 1) →
      (∀ x s t, ω (σ x s) (σ x t) = ω s t) → (∀ s, (∀ t, ω s t = 1) → s = 1) →
      Nat.card S ≤ Nat.card ↥(A.map π) * Nat.card ↥(fixV (A.map σ)) →
      ∀ l ∈ L, ∀ s, σ l s = s := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro S _ _ hSN hS2 σ ω halt hinv hnd hff
  set B : Subgroup (SL3 F) := A.map π with hBdef
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA2 a ha
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact hAc a ha a' ha'
  have hB1 : B ≠ ⊥ := by
    obtain ⟨a, ha, ha1⟩ := hA1
    intro h
    have : π a ∈ B := ⟨a, ha, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact ha1 this
  have hωskew : ∀ s t, ω s t = 1 → ω t s = 1 := fun s t h => by
    have := mul_eq_one_of_alt ω halt s t
    rwa [h, one_mul] at this
  have hfskew : ∀ s t, compForm ι ω s t = 1 → compForm ι ω t s = 1 := fun s t h => by
    rw [compForm_eq_one_iff hι] at h ⊢
    exact hωskew s t h
  have hfnd : ∀ s, (∀ t, compForm ι ω s t = 1) → s = 1 := fun s h =>
    hnd s fun t => (compForm_eq_one_iff hι ω s t).mp (h t)
  have hcardperp : ∀ U : Subgroup S, Nat.card U * Nat.card (perpIn ω ⊤ U) = Nat.card S :=
    fun U => by
      rw [← perpIn_compForm hι]
      exact card_mul_card_perpIn _ hfskew hfnd U
  have hR : perpIn ω ⊤ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact hnd s fun t => hs.2 t trivial
  have hpp : ∀ U : Subgroup S, perpIn ω ⊤ (perpIn ω ⊤ U) = U := fun U => by
    have := perpIn_perpIn (compForm ι ω) hfskew (X := ⊤) (U := U)
      (by rw [perpIn_compForm hι, hR]; exact bot_le) le_top
    rwa [perpIn_compForm hι, perpIn_compForm hι] at this
  have hperpinv : ∀ {U : Subgroup S}, (∀ x, ∀ u ∈ U, σ x u ∈ U) →
      ∀ x, ∀ s ∈ perpIn ω ⊤ U, σ x s ∈ perpIn ω ⊤ U :=
    fun hU => perpIn_inv σ ω hinv (fun _ _ _ => trivial) hU
  have hbot : ∀ x, ∀ u ∈ (⊥ : Subgroup S), σ x u ∈ (⊥ : Subgroup S) := fun _ _ h => by
    rw [Subgroup.mem_bot] at h ⊢
    rw [h, map_one]
  have hsecIH : ∀ {W U : Subgroup S} (hW : ∀ x, ∀ w ∈ W, σ x w ∈ W)
      (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U), U ≤ W → (∀ u ∈ U, ∀ w ∈ W, ω u w = 1) →
      (∀ w ∈ W, (∀ w' ∈ W, ω w w' = 1) → w ∈ U) → Nat.card (Sec W U) < N →
      ∀ l ∈ L, ∀ w ∈ W, σ l w * w⁻¹ ∈ U := by
    intro W U hW hU hUW h1 hrad hlt
    have h2 : ∀ w ∈ W, ∀ u ∈ U, ω w u = 1 := fun w hw u hu => hωskew _ _ (h1 u hu w hw)
    have key := IH _ hlt (Sec W U) rfl (sec_sq hS2) (secRho σ hW hU) (secForm ω h1 h2)
      (fun s => by
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
        rw [secForm_mk]
        exact halt w)
      (fun x s t => secForm_inv σ hW hU ω h1 h2 hinv x s t)
      (fun s hs => by
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hrad w w.2 fun w' hw' => by
          have := hs (QuotientGroup.mk ⟨w', hw'⟩)
          rwa [secForm_mk] at this)
      (sec_card_le σ hW hU hUW A hff)
    intro l hl w hw
    have := key l hl (QuotientGroup.mk ⟨w, hw⟩)
    rw [secRho_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  by_cases hQ : ∀ x, π x = 1 → σ x = 1
  ·
    obtain ⟨ρ, hρ⟩ := exists_lift π hπ σ hQ
    have hρinv : ∀ g s t, ω (ρ g s) (ρ g t) = ω s t := by
      intro g s t
      obtain ⟨x, rfl⟩ := hπ g
      rw [hρ]
      exact hinv x s t
    by_cases hρt : ∃ g s, ρ g s ≠ s
    · have hbotB : B ⊓ ρ.ker = ⊥ := by
        rw [eq_bot_iff]
        rintro b ⟨hb, hbk⟩
        have hc := ker_le_center ρ hρt hbk
        exact eq_one_of_pow_three (pow_three_eq_one_of_mem_center hc) (e := 1)
          (by simpa using hB2 b hb)
      have hAσ : A.map σ = B.map ρ := by
        rw [hBdef, Subgroup.map_map]
        congr 1
        exact (MonoidHom.ext fun x => hρ x).symm
      have hcard : Nat.card (B.map ρ) = Nat.card B := by
        have h := B1More.card_map_mul_card_inf_ker B ρ
        rwa [hbotB, Subgroup.card_bot, mul_one] at h
      have hffρ : IsFFModule ρ.range := by
        refine ⟨B.map ρ, Subgroup.map_le_range ρ B, ?_, ⟨?_, ?_⟩, ?_⟩
        · intro h
          apply hB1
          have h1 : Nat.card B = 1 := by rw [← hcard, h, Subgroup.card_bot]
          exact Subgroup.eq_bot_of_card_eq B h1
        · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
          rw [← map_mul, ← map_mul, hBc b hb b' hb']
        · rintro _ ⟨b, hb, rfl⟩
          rw [← map_pow, hB2 b hb, map_one]
        · rw [hcard, ← hAσ]
          exact hff
      have := sd_trivial h14 hSQ hsq hF hS2 ρ ω halt hρinv hnd hffρ
      intro l _ s
      rw [← hρ]
      exact this _ s
    · push Not at hρt
      intro l _ s
      rw [← hρ]
      exact hρt _ s
  push Not at hQ
  obtain ⟨x₀, hx₀, hσx₀⟩ := hQ
  set C : Subgroup S := fixV (π.ker.map σ) with hCdef
  have hCinv : ∀ x, ∀ c ∈ C, σ x c ∈ C := by
    intro x c hc
    rintro _ ⟨q, hq, rfl⟩
    have hq1 : π q = 1 := hq
    have hq' : x⁻¹ * q * x ∈ π.ker := by
      show π (x⁻¹ * q * x) = 1
      rw [map_mul, map_mul, hq1, mul_one, map_inv, inv_mul_cancel]
    have h1 := hc (σ (x⁻¹ * q * x)) ⟨_, hq', rfl⟩
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv] at h1
    have h2 := congrArg (σ x) h1
    rwa [MulAut.apply_inv_self] at h2
  have hQ2 : IsPGroup 2 ↥(π.ker.map σ) := by
    rintro ⟨_, q, hq, rfl⟩
    obtain ⟨e, he⟩ := hker q hq
    exact ⟨e, Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, he, map_one]; rfl)⟩
  have hSnt : (⊤ : Subgroup S) ≠ ⊥ := by
    intro h
    apply hσx₀
    refine MulEquiv.ext fun s => ?_
    have : s ∈ (⊤ : Subgroup S) := trivial
    rw [h, Subgroup.mem_bot] at this
    rw [this, map_one]
    rfl
  have hC1 : C ≠ ⊥ := by
    obtain ⟨m, -, hm1, hmfix⟩ := B1.exists_fixed_ne_one hS2 hQ2 (M := ⊤)
      (fun _ _ _ _ => trivial) hSnt
    intro h
    have : m ∈ C := fun b hb => hmfix b hb
    rw [h, Subgroup.mem_bot] at this
    exact hm1 this
  have hCtop : C ≠ ⊤ := by
    intro h
    apply hσx₀
    refine MulEquiv.ext fun s => ?_
    have : s ∈ C := by rw [h]; trivial
    exact this _ ⟨x₀, hx₀, rfl⟩
  have hCinvp := hperpinv hCinv
  by_cases hW₁ : C ⊓ perpIn ω ⊤ C = ⊥
  ·
    have hsup : C ⊔ perpIn ω ⊤ C = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have h1 := card_sup_mul_card_inf C (perpIn ω ⊤ C)
      rwa [hW₁, Subgroup.card_bot, mul_one, hcardperp C] at h1
    have hCpt : perpIn ω ⊤ C ≠ ⊤ := by
      intro h
      apply hC1
      rw [← hpp C, h, hR]
    have hcardC : Nat.card C < N := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hCtop)
      rwa [Subgroup.card_top, hSN] at this
    have hcardCp : Nat.card (perpIn ω ⊤ C) < N := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hCpt)
      rwa [Subgroup.card_top, hSN] at this
    have hLC := hsecIH hCinv hbot bot_le
      (fun u hu w _ => by rw [Subgroup.mem_bot.mp hu, map_one, MonoidHom.one_apply])
      (fun w hw h => by
        rw [← hW₁]
        exact ⟨hw, trivial, fun c hc => h c hc⟩)
      (by rw [card_sec_bot]; exact hcardC)
    have hLCp := hsecIH hCinvp hbot bot_le
      (fun u hu w _ => by rw [Subgroup.mem_bot.mp hu, map_one, MonoidHom.one_apply])
      (fun w hw h => by
        rw [← hW₁]
        refine ⟨?_, hw⟩
        rw [← hpp C]
        exact ⟨trivial, h⟩)
      (by rw [card_sec_bot]; exact hcardCp)
    intro l hl s
    have hs : s ∈ C ⊔ perpIn ω ⊤ C := by rw [hsup]; trivial
    obtain ⟨c, hc, c', hc', rfl⟩ := Subgroup.mem_sup.mp hs
    have e1 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hLC l hl c hc))
    have e2 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hLCp l hl c' hc'))
    rw [map_mul, e1, e2]
  set W₁ := C ⊓ perpIn ω ⊤ C with hW₁def
  have hW₁inv : ∀ x, ∀ w ∈ W₁, σ x w ∈ W₁ := fun x w hw => ⟨hCinv x w hw.1, hCinvp x w hw.2⟩
  have hiso : ∀ w ∈ W₁, ∀ w' ∈ W₁, ω w w' = 1 := fun w hw w' hw' => hw.2.2 w' hw'.1
  have hWpinv := hperpinv hW₁inv
  have hW₁Wp : W₁ ≤ perpIn ω ⊤ W₁ := fun w hw => ⟨trivial, fun w' hw' => hiso w hw w' hw'⟩
  have hfixW₁ : ∀ x, ∀ w ∈ W₁, σ x w = w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, w₁, hw₁, hne⟩ := hcon
    have hQ₁ : ∀ x, π x = 1 → secRho σ hW₁inv hbot x = 1 := by
      intro x hx
      refine MulEquiv.ext fun s => ?_
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
      rw [secRho_mk, MulAut.one_apply]
      congr 1
      exact Subtype.ext (w.2.1 (σ x) ⟨x, hx, rfl⟩)
    obtain ⟨ρ₁, hρ₁⟩ := exists_lift π hπ _ hQ₁
    have hρ₁nt : ∃ g s, ρ₁ g s ≠ s := by
      refine ⟨π x₁, QuotientGroup.mk ⟨w₁, hw₁⟩, ?_⟩
      rw [hρ₁, secRho_mk]
      intro h
      rw [mk_eq_mk_iff, Subgroup.mem_subgroupOf] at h
      apply hne
      simpa [mul_inv_eq_one] using h
    have hNB := card_lt_of_nontrivial h14 hSQ hsq hF (sec_sq hS2) ρ₁ hρ₁nt hB1 hB2 hBc
    have hBρ : B.map ρ₁ = autSec (A.map σ) W₁ ⊥ := by
      rw [hBdef, Subgroup.map_map, ← map_secRho σ hW₁inv hbot]
      congr 1
      exact MonoidHom.ext fun x => hρ₁ x
    rw [hBρ] at hNB
    set CA := fixV (A.map σ) with hCA
    set D := G6.commOn (A.map σ) W₁ with hD
    have hAσinv : ∀ a ∈ A.map σ, ∀ w ∈ W₁, a w ∈ W₁ := by
      rintro _ ⟨x, -, rfl⟩ w hw
      exact hW₁inv x w hw
    have hAσW : A.map σ ≤ stabSub W₁ :=
      (Subgroup.map_le_range σ A).trans (range_le_stabSub σ hW₁inv)
    have hAσb : A.map σ ≤ stabSub (⊥ : Subgroup S) :=
      (Subgroup.map_le_range σ A).trans (range_le_stabSub σ hbot)
    have hk : Nat.card (commV (autSec (A.map σ) W₁ ⊥)) ≤ Nat.card D := by
      have h1 := card_secPre (bot_le : (⊥ : Subgroup S) ≤ W₁) (commV (autSec (A.map σ) W₁ ⊥))
      have h2 : secPre W₁ ⊥ (commV (autSec (A.map σ) W₁ ⊥)) ≤ D :=
        secPre_commV_le bot_le fun a ha w hw => G6.mem_commOn_of_mem ha hw
      rw [Subgroup.card_bot, mul_one] at h1
      rw [h1]
      exact Subgroup.card_le_of_le h2
    have hidx : (fixV (autSec (A.map σ) W₁ ⊥)).index * Nat.card ↥(W₁ ⊓ CA) = Nat.card W₁ := by
      have h1 := (fixV (autSec (A.map σ) W₁ ⊥)).index_mul_card
      have h2 := B5.card_fixV_autSec_mul bot_le hAσW hAσb
      have h3 : B5.fixSec (A.map σ) W₁ ⊥ = W₁ ⊓ CA := by
        ext w
        rw [B5.mem_fixSec, Subgroup.mem_inf]
        refine and_congr Iff.rfl ⟨fun h b hb => ?_, fun h b hb => ?_⟩
        · exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp (h b hb))
        · rw [h b hb, mul_inv_cancel]
          exact Subgroup.one_mem _
      rw [Subgroup.card_bot, mul_one, h3] at h2
      rw [← h2, h1, card_sec_bot]
    have hDW₁ : D ≤ W₁ := G6.commOn_le_iff.mpr fun a ha w hw =>
      W₁.mul_mem (hAσinv a ha w hw) (W₁.inv_mem hw)
    have hDc : ∀ c ∈ CA, ∀ d ∈ D, ω c d = 1 := by
      intro c hc d hd
      have hle : D ≤ (ω c).ker := G6.commOn_le_iff.mpr fun a ha u _ => by
        obtain ⟨x, hxA, rfl⟩ := ha
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have h1 := hinv x c u
        rw [hc (σ x) ⟨x, hxA, rfl⟩] at h1
        rw [h1, mul_inv_cancel]
      exact hle hd
    have hle : W₁ ⊔ CA ≤ perpIn ω ⊤ D := sup_le
      (fun w hw => ⟨trivial, fun d hd => hiso w hw d (hDW₁ hd)⟩)
      (fun c hc => ⟨trivial, fun d hd => hDc c hc d hd⟩)
    have h5 := card_sup_mul_card_inf W₁ CA
    have h6 := hcardperp D
    set idx := (fixV (autSec (A.map σ) W₁ ⊥)).index
    set k := Nat.card (commV (autSec (A.map σ) W₁ ⊥))
    have hi : 0 < Nat.card ↥(W₁ ⊓ CA) := Nat.card_pos
    have hc : 0 < Nat.card CA := Nat.card_pos
    have hstep : idx * Nat.card CA ≤ Nat.card (perpIn ω ⊤ D) := by
      refine Nat.le_of_mul_le_mul_right ?_ hi
      calc idx * Nat.card CA * Nat.card ↥(W₁ ⊓ CA)
          = idx * Nat.card ↥(W₁ ⊓ CA) * Nat.card CA := by ring
        _ = Nat.card W₁ * Nat.card CA := by rw [hidx]
        _ = Nat.card ↥(W₁ ⊔ CA) * Nat.card ↥(W₁ ⊓ CA) := h5.symm
        _ ≤ Nat.card (perpIn ω ⊤ D) * Nat.card ↥(W₁ ⊓ CA) :=
            Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)
    have hfin : idx * k ≤ Nat.card B := by
      refine Nat.le_of_mul_le_mul_right ?_ hc
      calc idx * k * Nat.card CA ≤ idx * Nat.card D * Nat.card CA :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
        _ = Nat.card D * (idx * Nat.card CA) := by ring
        _ ≤ Nat.card D * Nat.card (perpIn ω ⊤ D) := Nat.mul_le_mul_left _ hstep
        _ = Nat.card S := h6
        _ ≤ Nat.card B * Nat.card CA := hff
    omega
  have hradWp : ∀ w ∈ perpIn ω ⊤ W₁, (∀ w' ∈ perpIn ω ⊤ W₁, ω w w' = 1) → w ∈ W₁ :=
    fun w _ h => by
      rw [← hpp W₁]
      exact ⟨trivial, h⟩
  have hcardSec : Nat.card (Sec (perpIn ω ⊤ W₁) W₁) < N := by
    have h1 := card_sec_mul hW₁Wp
    have h2 := hcardperp W₁
    have h3 : 1 < Nat.card W₁ := (Subgroup.one_lt_card_iff_ne_bot W₁).mpr hW₁
    have h4 : 0 < Nat.card (Sec (perpIn ω ⊤ W₁) W₁) := Nat.card_pos
    rw [← hSN, ← h2, ← h1]
    nlinarith
  have hLWp := hsecIH hWpinv hW₁inv hW₁Wp (fun u hu w hw => hωskew _ _ (hw.2 u hu)) hradWp
    hcardSec
  have hLfixWp := fix_of_two_step σ hL (fun l _ u hu => hfixW₁ l u hu) hLWp
  have hLS : ∀ l ∈ L, ∀ s ∈ (⊤ : Subgroup S), σ l s * s⁻¹ ∈ perpIn ω ⊤ W₁ := by
    intro l _ s _
    refine ⟨trivial, fun w hw => ?_⟩
    rw [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply]
    have := hinv l s w
    rw [hfixW₁ l w hw] at this
    rw [this, mul_inv_cancel]
  intro l hl s
  exact fix_of_two_step σ hL hLfixWp hLS l hl s trivial

end Ext

end CFSG.Quasithin.MS93.S46
