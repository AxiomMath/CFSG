module

public import CFSG.Quasithin.Background.B69Red

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

theorem a_stab_irr (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)} (hA : IsFFStarMin X A)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {I : Subgroup V}
    (hI : I ∈ IrrPlus L (⊤ : Subgroup V)) : ∀ b ∈ A, ∀ w ∈ I, b w ∈ I := by
  intro b hb w hw
  have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  have hE : oTwoUpper L = L := B1Red.oTwoUpper_eq_of_perfect hperf
  have hCF : AllTwoChiefFactorsCentral L := B1Red.allTwoChiefFactorsCentral_of_quasisimple hL
  have h1 := B1_5_3 hV hA hE hLA hCF b hb I hI
  have h2 : b w ∈ I.map b.toMonoidHom := Subgroup.mem_map_of_mem _ hw
  rwa [h1] at h2

omit [Finite V] in
theorem inf_le_fixV_of_ne {L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
    (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V)) (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V))
    (hne : W₁ ≠ W₂) : W₁ ⊓ W₂ ≤ fixV L := by
  rcases irrPlus_sup_inf h₁ h₂ with h | h
  · exact absurd h hne
  · intro x hx
    have hmem : x ∈ (W₁ ⊔ fixV L) ⊓ (W₂ ⊔ fixV L) :=
      ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩
    rw [h] at hmem
    exact hmem

omit [Finite V] in
theorem commSub_ne_bot_of_irr {A L : Subgroup (MulAut V)} (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) : commSub W A ≠ ⊥ := by
  intro hbot
  rw [commSub_eq_bot_iff] at hbot
  obtain ⟨hinv, -, hlt, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLc : L ≤ centSub W := by
    rw [← hLA]
    refine Subgroup.commutator_le.2 fun l hl a ha => ?_
    intro w hw
    have h1 : a⁻¹ w = w := hbot hw a⁻¹ (A.inv_mem ha)
    have h2 : l⁻¹ w ∈ W := hinv l⁻¹ (L.inv_mem hl) w hw
    have h4 : a (l⁻¹ w) = l⁻¹ w := hbot h2 a ha
    show (l * a * l⁻¹ * a⁻¹) w = w
    simp only [MulAut.mul_apply]
    rw [h1, h4]
    simp
  have hWle : W ≤ fixV L := fun w hw l hl => hLc hl w hw
  have : W ⊓ fixV L = W := inf_eq_left.2 hWle
  rw [this] at hlt
  exact lt_irrefl _ hlt

omit [Finite V] in
theorem conj_mem_centSec {W U : Subgroup V} {h g : MulAut V} (hhW : h ∈ stabSub W)
    (hhU : h ∈ stabSub U) (hg : g ∈ centSec W U) : h * g * h⁻¹ ∈ centSec W U :=
  CFSG.Quasithin.StabLat.conj_mem_centSec hhW hhU hg

omit [Finite V] in
theorem sec_triv_imp_triv {A L : Subgroup (MulAut V)} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hWA : ∀ b ∈ A, ∀ w ∈ W, b w ∈ W) {a : MulAut V}
    (ha : a ∈ A) (hsec : ∀ w ∈ W, a w * w⁻¹ ∈ fixV L) : ∀ w ∈ W, a w = w := by
  obtain ⟨hinv, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant hinv
  have hLU : L ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant (isInv_fixV L)
  have haW : a ∈ stabSub W := B1.le_stabSub_of_invariant hWA ha
  have haTr : a ∈ centSec W (fixV L) := ⟨haW, hsec⟩
  have ha'Tr : a⁻¹ ∈ centSec W (fixV L) := (centSec W (fixV L)).inv_mem haTr
  have hc : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ L ⊓ centSec W (fixV L) := by
    intro l hl
    refine ⟨L.mul_mem (hAn a ha l hl) (L.inv_mem hl), ?_⟩
    have h1 : l * a⁻¹ * l⁻¹ ∈ centSec W (fixV L) :=
      conj_mem_centSec (hLW hl) (hLU hl) ha'Tr
    have h2 := (centSec W (fixV L)).mul_mem haTr h1
    simpa [mul_assoc] using h2
  set L₁ : Subgroup ↥L := (centSec W (fixV L)).subgroupOf L with hL₁
  have : L₁.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hL₁, Subgroup.mem_subgroupOf] at hx ⊢
    have := conj_mem_centSec (h := (g : MulAut V)) (hLW g.2) (hLU g.2) hx
    simpa using this
  have hL₁ne : L₁ ≠ ⊤ := by
    intro htop
    have hLTr : ∀ x ∈ L, x ∈ centSec W (fixV L) := fun x hx => by
      have : (⟨x, hx⟩ : ↥L) ∈ L₁ := by rw [htop]; trivial
      exact this
    have hle : commSub W L ≤ W ⊓ fixV L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact ⟨W.mul_mem (hinv x hx w hw) (W.inv_mem hw), (hLTr x hx).2 w hw⟩
    rw [hcomm] at hle
    have : W ⊓ fixV L = W := le_antisymm inf_le_left hle
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hcent : L₁ ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL L₁ hL₁ne
  have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  let φ : ↥L →* ↥L :=
    { toFun := fun l => ⟨a * l * a⁻¹, hAn a ha l l.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [mul_assoc] }
  have hφ : ∀ l : ↥L, l⁻¹ * φ l ∈ Subgroup.center ↥L := by
    rintro ⟨x, hx⟩
    have hmem : (⟨a * x * a⁻¹ * x⁻¹, (hc x hx).1⟩ : ↥L) ∈ L₁ := (hc x hx).2
    have hz := hcent hmem
    have : (⟨x, hx⟩ : ↥L)⁻¹ * φ ⟨x, hx⟩ = ⟨a * x * a⁻¹ * x⁻¹, (hc x hx).1⟩ := by
      have hz' := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
      apply Subtype.ext
      have h5 : x * (a * x * a⁻¹ * x⁻¹) = a * x * a⁻¹ * x⁻¹ * x := congrArg Subtype.val hz'
      show x⁻¹ * (a * x * a⁻¹) = a * x * a⁻¹ * x⁻¹
      calc x⁻¹ * (a * x * a⁻¹) = x⁻¹ * ((a * x * a⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (a * x * a⁻¹ * x⁻¹)) := by rw [h5]
        _ = a * x * a⁻¹ * x⁻¹ := by group
    rw [this]
    exact hz
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hφ
  have hal : ∀ l ∈ L, a * l = l * a := by
    intro l hl
    have h6 : a * l * a⁻¹ = l :=
      congrArg (fun f : ↥L →* ↥L => ((f ⟨l, hl⟩ : ↥L) : MulAut V)) hid
    calc a * l = (a * l * a⁻¹) * a := by group
      _ = l * a := by rw [h6]
  set F : Subgroup V := MonoidHom.eqLocus a.toMonoidHom (MonoidHom.id V) with hF
  have hmemF : ∀ v, v ∈ F ↔ a v = v := fun v => Iff.rfl
  have hgens : commSub W L ≤ F := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    rw [SetLike.mem_coe, hmemF]
    have hd := hsec w hw
    have h1 : a (l w) = l (a w) := congrArg (fun g : MulAut V => g w) (hal l hl)
    have h2 : a w = (a w * w⁻¹) * w := by simp
    have h3 : l (a w) = (a w * w⁻¹) * l w := by
      conv_lhs => rw [h2]
      rw [map_mul, hd l hl]
    rw [map_mul, map_inv, h1, h3]
    have key : ∀ x y z : V, x * y⁻¹ * z * x⁻¹ = z * y⁻¹ := fun x y z => by
      rw [mul_inv_eq_iff_eq_mul]
      ac_rfl
    exact key _ _ _
  intro w hw
  have : w ∈ commSub W L := by rw [hcomm]; exact hw
  exact hgens this

section Prod

variable {W₁ W₂ : Subgroup V}

noncomputable def sumHom (W₁ W₂ : Subgroup V) : ↥W₁ × ↥W₂ →* ↥(W₁ ⊔ W₂) :=
  (Subgroup.inclusion (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).coprod
    (Subgroup.inclusion (le_sup_right : W₂ ≤ W₁ ⊔ W₂))

omit [Finite V] in
theorem coe_sumHom (p : ↥W₁ × ↥W₂) :
    ((sumHom W₁ W₂ p : ↥(W₁ ⊔ W₂)) : V) = (p.1 : V) * p.2 := by
  simp [sumHom]

omit [Finite V] in
theorem sumHom_surjective (W₁ W₂ : Subgroup V) : Function.Surjective (sumHom W₁ W₂) := by
  intro y
  obtain ⟨x, hx, z, hz, hxz⟩ := Subgroup.mem_sup.1 y.2
  exact ⟨(⟨x, hx⟩, ⟨z, hz⟩), Subtype.ext (by rw [coe_sumHom]; exact hxz)⟩

omit [Finite V] in
theorem ker_sumHom_le {U : Subgroup V} (hind : W₁ ⊓ W₂ ≤ U) {p : ↥W₁ × ↥W₂}
    (hp : p ∈ (sumHom W₁ W₂).ker) : (p.1 : V) ∈ U ∧ (p.2 : V) ∈ U := by
  have h1 : (p.1 : V) * p.2 = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hp)
    simpa [coe_sumHom] using this
  have hp1 : (p.1 : V) = (p.2 : V)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmem1 : (p.1 : V) ∈ W₁ ⊓ W₂ := ⟨p.1.2, by rw [hp1]; exact W₂.inv_mem p.2.2⟩
  have hmem2 : (p.2 : V) ∈ W₁ ⊓ W₂ :=
    ⟨by have := W₁.inv_mem p.1.2; rwa [hp1, inv_inv] at this, p.2.2⟩
  exact ⟨hind hmem1, hind hmem2⟩

noncomputable def prodHom (U : Subgroup V) (hind : W₁ ⊓ W₂ ≤ U) :
    ↥(W₁ ⊔ W₂) →* Sec W₁ U × Sec W₂ U :=
  (sumHom W₁ W₂).liftOfSurjective (sumHom_surjective W₁ W₂)
    ⟨(QuotientGroup.mk' (U.subgroupOf W₁)).prodMap (QuotientGroup.mk' (U.subgroupOf W₂)), by
      intro p hp
      obtain ⟨h1, h2⟩ := ker_sumHom_le hind hp
      rw [MonoidHom.mem_ker]
      refine Prod.ext ?_ ?_
      · exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1)
      · exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h2)⟩

omit [Finite V] in
theorem prodHom_sumHom (U : Subgroup V) (hind : W₁ ⊓ W₂ ≤ U) (p : ↥W₁ × ↥W₂) :
    prodHom U hind (sumHom W₁ W₂ p) = (QuotientGroup.mk p.1, QuotientGroup.mk p.2) := by
  simp [prodHom]
  rfl

omit [Finite V] in
theorem prodHom_surjective (U : Subgroup V) (hind : W₁ ⊓ W₂ ≤ U) :
    Function.Surjective (prodHom U hind) := by
  rintro ⟨s₁, s₂⟩
  obtain ⟨w₁, rfl⟩ := QuotientGroup.mk_surjective s₁
  obtain ⟨w₂, rfl⟩ := QuotientGroup.mk_surjective s₂
  exact ⟨sumHom W₁ W₂ (w₁, w₂), prodHom_sumHom U hind (w₁, w₂)⟩

end Prod

section Count

variable {W₁ W₂ : Subgroup V}

omit [Finite V] in
theorem diff_mem_inf {a : MulAut V} (ha₁ : ∀ w ∈ W₁, a w ∈ W₁) (ha₂ : ∀ w ∈ W₂, a w ∈ W₂)
    {w₁ w₂ : V} (hw₁ : w₁ ∈ W₁) (hw₂ : w₂ ∈ W₂) (h : a (w₁ * w₂) = w₁ * w₂) :
    a w₁ * w₁⁻¹ ∈ W₁ ⊓ W₂ ∧ a w₂ * w₂⁻¹ ∈ W₁ ⊓ W₂ := by
  have hx : a w₁ * w₁⁻¹ ∈ W₁ := W₁.mul_mem (ha₁ w₁ hw₁) (W₁.inv_mem hw₁)
  have hy : a w₂ * w₂⁻¹ ∈ W₂ := W₂.mul_mem (ha₂ w₂ hw₂) (W₂.inv_mem hw₂)
  have hxy : (a w₁ * w₁⁻¹) * (a w₂ * w₂⁻¹) = 1 := by
    have e : (a w₁ * w₁⁻¹) * (a w₂ * w₂⁻¹) = a (w₁ * w₂) * (w₁ * w₂)⁻¹ := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [e, h, mul_inv_cancel]
  have hx' : a w₁ * w₁⁻¹ = (a w₂ * w₂⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hxy
  have hy' : a w₂ * w₂⁻¹ = (a w₁ * w₁⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hxy
  exact ⟨⟨hx, by rw [hx']; exact W₂.inv_mem hy⟩, ⟨by rw [hy']; exact W₁.inv_mem hx, hy⟩⟩

omit [Finite V] in
theorem prodHom_mem_fix (U : Subgroup V) (hind : W₁ ⊓ W₂ ≤ U) {A : Subgroup (MulAut V)}
    (hA₁ : ∀ a ∈ A, ∀ w ∈ W₁, a w ∈ W₁) (hA₂ : ∀ a ∈ A, ∀ w ∈ W₂, a w ∈ W₂)
    {y : ↥(W₁ ⊔ W₂)} (hy : y ∈ fixV (autSub A (W₁ ⊔ W₂))) :
    prodHom U hind y ∈ (fixV (autSec A W₁ U)).prod (fixV (autSec A W₂ U)) := by
  obtain ⟨⟨w₁, w₂⟩, rfl⟩ := sumHom_surjective W₁ W₂ y
  rw [prodHom_sumHom, Subgroup.mem_prod]
  have hAY : ∀ a ∈ A, ∀ y ∈ W₁ ⊔ W₂, a y ∈ W₁ ⊔ W₂ := isInv_sup hA₁ hA₂
  have hfix : ∀ a ∈ A, a ((w₁ : V) * w₂) = (w₁ : V) * w₂ := by
    intro a ha
    have h1 := mem_fixV_autSub.1 hy a ha (B1.le_stabSub_of_invariant hAY ha)
    rwa [coe_sumHom] at h1
  refine ⟨?_, ?_⟩
  · refine mk_mem_fixV_autQuot.2 fun g hg _ => ?_
    obtain ⟨b, hb, rfl⟩ := mem_autSub.1 hg
    rw [Subgroup.mem_subgroupOf]
    exact hind (diff_mem_inf (fun w hw => hA₁ _ hb w hw) (fun w hw => hA₂ _ hb w hw) w₁.2 w₂.2
      (hfix _ hb)).1
  · refine mk_mem_fixV_autQuot.2 fun g hg _ => ?_
    obtain ⟨b, hb, rfl⟩ := mem_autSub.1 hg
    rw [Subgroup.mem_subgroupOf]
    exact hind (diff_mem_inf (fun w hw => hA₁ _ hb w hw) (fun w hw => hA₂ _ hb w hw) w₁.2 w₂.2
      (hfix _ hb)).2

theorem card_fixY_le (U : Subgroup V) (hind : W₁ ⊓ W₂ ≤ U) {A : Subgroup (MulAut V)}
    (hA₁ : ∀ a ∈ A, ∀ w ∈ W₁, a w ∈ W₁) (hA₂ : ∀ a ∈ A, ∀ w ∈ W₂, a w ∈ W₂) :
    Nat.card ↥(fixV (autSub A (W₁ ⊔ W₂))) ≤
      Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) *
        Nat.card ↥(prodHom U hind).ker := by
  have h1 := B1More.card_map_mul_card_inf_ker (fixV (autSub A (W₁ ⊔ W₂))) (prodHom U hind)
  have h2 : (fixV (autSub A (W₁ ⊔ W₂))).map (prodHom U hind) ≤
      (fixV (autSec A W₁ U)).prod (fixV (autSec A W₂ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact prodHom_mem_fix U hind hA₁ hA₂ hy
  have h3 := Subgroup.card_le_of_le h2
  have h4 : Nat.card ↥((fixV (autSec A W₁ U)).prod (fixV (autSec A W₂ U))) =
      Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have h5 : Nat.card ↥(fixV (autSub A (W₁ ⊔ W₂)) ⊓ (prodHom U hind).ker) ≤
      Nat.card ↥(prodHom U hind).ker := Subgroup.card_le_of_le inf_le_right
  rw [← h1]
  exact Nat.mul_le_mul (h3.trans h4.le) h5

omit [Finite V] in
theorem card_Y_eq (U : Subgroup V) (hind : W₁ ⊓ W₂ ≤ U) :
    Nat.card ↥(W₁ ⊔ W₂) =
      Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) * Nat.card ↥(prodHom U hind).ker := by
  have h1 := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥(W₁ ⊔ W₂)) (prodHom U hind)
  have h2 : (⊤ : Subgroup ↥(W₁ ⊔ W₂)).map (prodHom U hind) = ⊤ :=
    Subgroup.map_top_of_surjective _ (prodHom_surjective U hind)
  rw [h2, top_inf_eq, Subgroup.card_top, Subgroup.card_top, Nat.card_prod] at h1
  exact h1.symm

end Count

theorem arith_ul {a k k' aY cY c₁ c₂ s₁ s₂ d y : ℕ} (hk : 0 < k) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hd : 0 < d) (ha : 0 < a) (H1 : y < aY * cY) (H2 : k ≤ k') (H3 : aY * k' = a)
    (H4 : cY ≤ c₁ * c₂ * d) (H5 : y = s₁ * s₂ * d) (H6 : 2 * a * c₁ * c₂ ≤ s₁ * s₂ * k) :
    False := by
  have h1 : y * k < a * (c₁ * c₂ * d) := by
    calc y * k < aY * cY * k := Nat.mul_lt_mul_of_pos_right H1 hk
      _ ≤ aY * cY * k' := Nat.mul_le_mul_left _ H2
      _ = a * cY := by rw [← H3]; ring
      _ ≤ a * (c₁ * c₂ * d) := Nat.mul_le_mul_left _ H4
  have h2 : 2 * (a * (c₁ * c₂ * d)) ≤ y * k := by
    calc 2 * (a * (c₁ * c₂ * d)) = (2 * a * c₁ * c₂) * d := by ring
      _ ≤ (s₁ * s₂ * k) * d := Nat.mul_le_mul_right _ H6
      _ = y * k := by rw [H5]; ring
  have hpos : 0 < a * (c₁ * c₂ * d) := by positivity
  linarith

theorem false_of_two_sections (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hs : rAV A < 1) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {W₁ W₂ : Subgroup V} (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V)) (hne : W₁ ≠ W₂)
    (hGT : 2 * Nat.card A * Nat.card ↥(fixV (autSec A W₁ (fixV L))) *
        Nat.card ↥(fixV (autSec A W₂ (fixV L))) ≤
      Nat.card (Sec W₁ (fixV L)) * Nat.card (Sec W₂ (fixV L)) *
        Nat.card ↥(A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L))) : False := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA h₁
  have hA₂ := a_stab_irr hV hA hL hLA h₂
  have hind := inf_le_fixV_of_ne h₁ h₂ hne
  have hAY : ∀ a ∈ A, ∀ y ∈ W₁ ⊔ W₂, a y ∈ W₁ ⊔ W₂ := isInv_sup hA₁ hA₂
  have hAst : A ≤ stabSub (W₁ ⊔ W₂) := B1.le_stabSub_of_invariant hAY
  have hnt : commSub (W₁ ⊔ W₂) A ≠ ⊥ := fun h =>
    commSub_ne_bot_of_irr hLA h₁ (eq_bot_iff.2 (h ▸ commSub_mono le_sup_left le_rfl))
  obtain ⟨hmin, -⟩ := B1_5_2 hV hA hAY hnt
  have hr : rAV (autSub A (W₁ ⊔ W₂)) < 1 := rAV_autSub_lt_one hV hA hAY hnt hs
  have hY1 : Nat.card ↥(W₁ ⊔ W₂) <
      Nat.card ↥(autSub A (W₁ ⊔ W₂)) * Nat.card ↥(fixV (autSub A (W₁ ⊔ W₂))) :=
    (rAV_lt_one_iff (B1.sq_eq_one_sub hV (W₁ ⊔ W₂)) hmin.1.isA2).1 hr
  have hK0 : A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L) ≤ A ⊓ centSub (W₁ ⊔ W₂) := by
    intro a ha
    obtain ⟨⟨haA, ha1⟩, ha2⟩ := ha
    refine ⟨haA, ?_⟩
    have e1 := sec_triv_imp_triv hL hAn h₁ hA₁ haA ha1.2
    have e2 := sec_triv_imp_triv hL hAn h₂ hA₂ haA ha2.2
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul, e1 x hx, e2 z hz]
  have hk' := Subgroup.card_le_of_le hK0
  have hA3 := card_autSub_mul hAst
  exact arith_ul Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos hY1 hk' hA3
    (card_fixY_le (fixV L) hind hA₁ hA₂) (card_Y_eq (fixV L) hind) hGT

end B69

end CFSG.Quasithin
