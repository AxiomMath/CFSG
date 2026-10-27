module

public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def centQuot (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, g v * v⁻¹ ∈ U}
  one_mem' := fun v => by simp
  mul_mem' := by
    intro a b ha hb v
    have h1 := U.mul_mem (ha (b v)) (hb v)
    have h2 : (a * b) v * v⁻¹ = a (b v) * (b v)⁻¹ * (b v * v⁻¹) := by
      change a (b v) * v⁻¹ = _
      simp [mul_comm, mul_left_comm]
    rw [h2]
    exact h1
  inv_mem' := by
    intro a ha v
    have h1 := U.inv_mem (ha (a⁻¹ v))
    have h2 : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
      have : a (a⁻¹ v) = v := by simp
      rw [this]
      simp
    change a⁻¹ v * v⁻¹ ∈ U
    rw [h2]
    exact h1

theorem mem_centQuot {U : Subgroup V} {g : MulAut V} :
    g ∈ centQuot U ↔ ∀ v : V, g v * v⁻¹ ∈ U := Iff.rfl

theorem centQuot_le_stabSub (U : Subgroup V) : centQuot U ≤ stabSub U := by
  intro g hg u
  constructor
  · intro h
    have h1 := hg u
    have : u = g u * (g u * u⁻¹)⁻¹ := by simp
    rw [this]
    exact U.mul_mem h (U.inv_mem h1)
  · intro h
    have h1 := hg u
    have : g u = (g u * u⁻¹) * u := by simp
    rw [this]
    exact U.mul_mem h1 h

theorem centSub_le_centQuot_of_le {U W : Subgroup V} (h : W ≤ U) : centQuot W ≤ centQuot U :=
  fun _ hg v => h (hg v)

theorem map_eq_of_mem_stabSub {U : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub U) :
    U.map (g : V ≃* V).toMonoidHom = U := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hg y).2 hy
  · intro hx
    refine ⟨g⁻¹ x, ?_, by simp⟩
    have h1 := (hg (g⁻¹ x)).1
    have h2 : g (g⁻¹ x) = x := by simp
    rw [h2] at h1
    exact h1 hx

@[expose] def quotAut (U : Subgroup V) (g : stabSub U) : MulAut (V ⧸ U) :=
  QuotientGroup.congr U U (g.1 : V ≃* V) (map_eq_of_mem_stabSub g.2)

theorem quotAut_mk (U : Subgroup V) (g : stabSub U) (v : V) :
    quotAut U g (QuotientGroup.mk v) = QuotientGroup.mk (g.1 v) := rfl

@[expose] def quotHom (U : Subgroup V) : stabSub U →* MulAut (V ⧸ U) where
  toFun := quotAut U
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  map_mul' a b := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => rfl

theorem quotHom_mk (U : Subgroup V) (g : stabSub U) (v : V) :
    quotHom U g (QuotientGroup.mk v) = QuotientGroup.mk (g.1 v) := rfl

theorem mk_eq_mk_iff {U : Subgroup V} (a b : V) :
    (QuotientGroup.mk a : V ⧸ U) = QuotientGroup.mk b ↔ a * b⁻¹ ∈ U := by
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]

theorem ker_quotHom (U : Subgroup V) :
    (quotHom U).ker = (centQuot U).subgroupOf (stabSub U) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centQuot]
  constructor
  · intro h v
    have := congrArg (fun φ : MulAut (V ⧸ U) => φ (QuotientGroup.mk v)) h
    simp only [quotHom_mk, MulAut.one_apply] at this
    exact (mk_eq_mk_iff _ _).1 this
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => exact (mk_eq_mk_iff _ _).2 (h v)

@[expose] def autQuot (X : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup (MulAut (V ⧸ U)) :=
  (X.subgroupOf (stabSub U)).map (quotHom U)

theorem mem_autQuot {X : Subgroup (MulAut V)} {U : Subgroup V} {φ : MulAut (V ⧸ U)} :
    φ ∈ autQuot X U ↔ ∃ g : stabSub U, (g : MulAut V) ∈ X ∧ quotHom U g = φ := by
  simp [autQuot, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem autQuot_mono {X X' : Subgroup (MulAut V)} (h : X ≤ X') (U : Subgroup V) :
    autQuot X U ≤ autQuot X' U :=
  Subgroup.map_mono fun _ hg => h hg

namespace B1More

theorem card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H] (K : Subgroup G)
    (f : G →* H) : Nat.card ↥(K.map f) * Nat.card ↥(K ⊓ f.ker) = Nat.card K := by
  have h1 : f.ker.relIndex K = Nat.card (K.map f) := Subgroup.relIndex_ker K f
  have h2 := Subgroup.relIndex_mul_card f.ker K
  rw [h1, inf_comm] at h2
  exact h2

end B1More

theorem card_autQuot_mul {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    Nat.card (autQuot A U) * Nat.card ↥(A ⊓ centQuot U) = Nat.card A := by
  have h2 := B1More.card_map_mul_card_inf_ker (A.subgroupOf (stabSub U)) (quotHom U)
  have h3 : A.subgroupOf (stabSub U) ⊓ (quotHom U).ker =
      (A ⊓ centQuot U).subgroupOf (stabSub U) := by
    ext g
    simp [ker_quotHom, Subgroup.mem_subgroupOf]
  have h4 : Nat.card (A.subgroupOf (stabSub U)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have h5 : Nat.card ↥((A ⊓ centQuot U).subgroupOf (stabSub U)) = Nat.card ↥(A ⊓ centQuot U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA)).toEquiv
  rw [h3, h5, h4] at h2
  exact h2

theorem mk_mem_fixV_autQuot {X : Subgroup (MulAut V)} {U : Subgroup V} {v : V} :
    (QuotientGroup.mk v : V ⧸ U) ∈ fixV (autQuot X U) ↔
      ∀ g ∈ X, g ∈ stabSub U → g v * v⁻¹ ∈ U := by
  constructor
  · intro h g hg hgs
    have := h (quotHom U ⟨g, hgs⟩) (mem_autQuot.mpr ⟨⟨g, hgs⟩, hg, rfl⟩)
    exact (mk_eq_mk_iff _ _).1 this
  · intro h φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    exact (mk_eq_mk_iff _ _).2 (h g hg g.2)

theorem card_fixV_le_autQuot [Finite V] {A : Subgroup (MulAut V)} {U : Subgroup V} :
    Nat.card (fixV A) ≤ Nat.card (fixV (autQuot A U)) * Nat.card ↥(U ⊓ fixV A) := by
  have h1 := B1More.card_map_mul_card_inf_ker (fixV A) (QuotientGroup.mk' U)
  have h2 : (fixV A).map (QuotientGroup.mk' U) ≤ fixV (autQuot A U) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mk_mem_fixV_autQuot.2 fun g hg _ => by rw [hv g hg]; simp
  have h3 : fixV A ⊓ (QuotientGroup.mk' U).ker = U ⊓ fixV A := by
    rw [QuotientGroup.ker_mk', inf_comm]
  rw [h3] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le h2)

abbrev Sec (W U : Subgroup V) : Type _ := ↥W ⧸ U.subgroupOf W

@[expose] def autSec (X : Subgroup (MulAut V)) (W U : Subgroup V) :
    Subgroup (MulAut (Sec W U)) :=
  autQuot (autSub X W) (U.subgroupOf W)

@[expose] def centSec (W U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | g ∈ stabSub W ∧ ∀ w ∈ W, g w * w⁻¹ ∈ U}
  one_mem' := ⟨(stabSub W).one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(stabSub W).mul_mem ha1 hb1, fun w hw => ?_⟩
    have hbw : b w ∈ W := (hb1 w).2 hw
    have h1 := U.mul_mem (ha2 (b w) hbw) (hb2 w hw)
    have h2 : (a * b) w * w⁻¹ = a (b w) * (b w)⁻¹ * (b w * w⁻¹) := by
      change a (b w) * w⁻¹ = _
      simp [mul_comm, mul_left_comm]
    rw [h2]
    exact h1
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(stabSub W).inv_mem ha1, fun w hw => ?_⟩
    have hw' : a⁻¹ w ∈ W := ((stabSub W).inv_mem ha1 w).2 hw
    have h1 := U.inv_mem (ha2 (a⁻¹ w) hw')
    have h2 : a⁻¹ w * w⁻¹ = (a (a⁻¹ w) * (a⁻¹ w)⁻¹)⁻¹ := by
      have : a (a⁻¹ w) = w := by simp
      rw [this]
      simp
    change a⁻¹ w * w⁻¹ ∈ U
    rw [h2]
    exact h1

theorem mem_centSec {W U : Subgroup V} {g : MulAut V} :
    g ∈ centSec W U ↔ g ∈ stabSub W ∧ ∀ w ∈ W, g w * w⁻¹ ∈ U := Iff.rfl

theorem centSub_le_centSec (W U : Subgroup V) : centSub W ≤ centSec W U := by
  intro g hg
  exact ⟨centSub_le_stabSub W hg, fun w hw => by rw [hg w hw]; simp⟩

theorem centSec_le_stabSub (W U : Subgroup V) : centSec W U ≤ stabSub W := fun _ h => h.1


theorem autSub_le_stabSub_subgroupOf {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAU : A ≤ stabSub U) : autSub A W ≤ stabSub (U.subgroupOf W) := by
  intro φ hφ x
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  have h := hAU hg
  have h2 : ((resHom W g x : W) : V) = g.1 (x : V) := rfl
  show (resHom W g x : W) ∈ U.subgroupOf W ↔ x ∈ U.subgroupOf W
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, h2]
  exact h (x : V)

theorem autSec_mono {X X' : Subgroup (MulAut V)} (h : X ≤ X') (W U : Subgroup V) :
    autSec X W U ≤ autSec X' W U :=
  autQuot_mono (autSub_mono h W) _

theorem card_autSec_mul {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) :
    Nat.card (autSec A W U) * Nat.card ↥(A ⊓ centSec W U) = Nat.card A := by
  have h1 : Nat.card (autSec A W U) * Nat.card ↥(autSub A W ⊓ centQuot (U.subgroupOf W)) =
      Nat.card (autSub A W) := card_autQuot_mul (autSub_le_stabSub_subgroupOf hAU)
  have h2 := card_autSub_mul hAW
  have h3 := B1More.card_map_mul_card_inf_ker ((A ⊓ centSec W U).subgroupOf (stabSub W))
    (resHom W)
  have hK : ((A ⊓ centSec W U).subgroupOf (stabSub W)).map (resHom W) =
      autSub A W ⊓ centQuot (U.subgroupOf W) := by
    ext φ
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : (g : MulAut V) ∈ A ⊓ centSec W U := hg
      rw [Subgroup.mem_inf] at hg'
      refine ⟨mem_autSub.mpr ⟨g, hg'.1, rfl⟩, fun x => ?_⟩
      rw [Subgroup.mem_subgroupOf]
      exact hg'.2.2 (x : V) x.2
    · rintro ⟨hφ, hq⟩
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      refine ⟨g, ?_, rfl⟩
      show (g : MulAut V) ∈ A ⊓ centSec W U
      refine ⟨hg, g.2, fun w hw => ?_⟩
      have := hq ⟨w, hw⟩
      rw [Subgroup.mem_subgroupOf] at this
      exact this
  have hKer : ((A ⊓ centSec W U).subgroupOf (stabSub W)) ⊓ (resHom W).ker =
      (A ⊓ centSub W).subgroupOf (stabSub W) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, ker_resHom]
    constructor
    · rintro ⟨⟨hA, _⟩, hc⟩
      exact ⟨hA, hc⟩
    · rintro ⟨hA, hc⟩
      exact ⟨⟨hA, centSub_le_centSec W U hc⟩, hc⟩
  have hc1 : Nat.card ↥((A ⊓ centSec W U).subgroupOf (stabSub W)) =
      Nat.card ↥(A ⊓ centSec W U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right.trans (centSec_le_stabSub W U))).toEquiv
  have hc2 : Nat.card ↥((A ⊓ centSub W).subgroupOf (stabSub W)) = Nat.card ↥(A ⊓ centSub W) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right.trans (centSub_le_stabSub W))).toEquiv
  rw [hK, hKer, hc1, hc2] at h3
  calc Nat.card (autSec A W U) * Nat.card ↥(A ⊓ centSec W U)
      = Nat.card (autSec A W U) *
          (Nat.card ↥(autSub A W ⊓ centQuot (U.subgroupOf W)) * Nat.card ↥(A ⊓ centSub W)) := by
        rw [h3]
    _ = (Nat.card (autSec A W U) * Nat.card ↥(autSub A W ⊓ centQuot (U.subgroupOf W))) *
          Nat.card ↥(A ⊓ centSub W) := by ring
    _ = Nat.card (autSub A W) * Nat.card ↥(A ⊓ centSub W) := by rw [h1]
    _ = Nat.card A := h2


theorem card_inf_fixV_le_autSec [Finite V] {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    Nat.card ↥(W ⊓ fixV A) ≤ Nat.card (fixV (autSec A W U)) * Nat.card ↥(U ⊓ fixV A) := by
  have h1 := card_fixV_le_autQuot (A := autSub A W) (U := U.subgroupOf W)
  have h2 : Nat.card (fixV (autSub A W)) = Nat.card ↥(W ⊓ fixV A) := by
    rw [← map_subtype_fixV_autSub hAW, Subgroup.card_map_of_injective W.subtype_injective]
  have h3 : Nat.card ↥(U.subgroupOf W ⊓ fixV (autSub A W)) = Nat.card ↥(U ⊓ fixV A) := by
    have h4 : (U.subgroupOf W ⊓ fixV (autSub A W)).map W.subtype = U ⊓ fixV A := by
      rw [Subgroup.map_inf _ _ _ W.subtype_injective, map_subtype_fixV_autSub hAW,
        Subgroup.map_subgroupOf_eq_of_le hUW, ← inf_assoc, inf_eq_left.2 hUW]
    rw [← h4, Subgroup.card_map_of_injective W.subtype_injective]
  rw [h2, h3] at h1
  exact h1

theorem card_sec_mul [Finite V] {W U : Subgroup V} (hUW : U ≤ W) :
    Nat.card (Sec W U) * Nat.card U = Nat.card W := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf W)
  have h2 : Nat.card ↥(U.subgroupOf W) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem card_mul_card_fixV_le [Finite V] (A : Subgroup (MulAut V)) (W : Subgroup V) :
    Nat.card ↥(W ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) = Nat.card W * Nat.card (fixV A) :=
  card_sup_mul_card_inf W (fixV A)

theorem arith_section {sS u w v a cV cW cU cS : ℕ} (hsu : sS * u = w) (hcw : cW ≤ cS * cU)
    (hcu : cU ≤ u) (hn : w * cV ≤ v * cW) (hv : v ≤ a * cV) (hcV : 0 < cV) (hu : 0 < u) :
    w ≤ a * cW ∧ sS * u ≤ a * cS * cU ∧ sS ≤ a * cS := by
  have hA : w ≤ a * cW := by
    have h1 : w * cV ≤ (a * cW) * cV := by
      calc w * cV ≤ v * cW := hn
        _ ≤ (a * cV) * cW := Nat.mul_le_mul_right _ hv
        _ = (a * cW) * cV := by ring
    exact Nat.le_of_mul_le_mul_right h1 hcV
  have hB : sS * u ≤ a * cS * cU := by
    rw [hsu]
    calc w ≤ a * cW := hA
      _ ≤ a * (cS * cU) := Nat.mul_le_mul_left _ hcw
      _ = a * cS * cU := by ring
  have hC : sS ≤ a * cS := by
    have h1 : sS * u ≤ (a * cS) * u := by
      calc sS * u ≤ a * cS * cU := hB
        _ ≤ (a * cS) * u := Nat.mul_le_mul_left _ hcu
    exact Nat.le_of_mul_le_mul_right h1 hu
  exact ⟨hA, hB, hC⟩

theorem section_numerics [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {W U : Subgroup V} (hUW : U ≤ W) (hAW : A ≤ stabSub W) :
    Nat.card W ≤ Nat.card A * Nat.card ↥(W ⊓ fixV A) ∧
      Nat.card (Sec W U) * Nat.card U ≤
        Nat.card A * Nat.card (fixV (autSec A W U)) * Nat.card ↥(U ⊓ fixV A) ∧
      Nat.card (Sec W U) ≤ Nat.card A * Nat.card (fixV (autSec A W U)) := by
  have hv : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [B1.card_bot_mul_card_fixV] at this
  have hn : Nat.card W * Nat.card (fixV A) ≤ Nat.card V * Nat.card ↥(W ⊓ fixV A) := by
    rw [← card_mul_card_fixV_le A W]
    exact Nat.mul_le_mul_right _ (by
      simpa using Subgroup.card_le_of_le (le_top : (W ⊔ fixV A) ≤ ⊤))
  have hcu : Nat.card ↥(U ⊓ fixV A) ≤ Nat.card U := Subgroup.card_le_of_le inf_le_left
  exact arith_section (card_sec_mul hUW) (card_inf_fixV_le_autSec hUW hAW) hcu hn hv
    Nat.card_pos Nat.card_pos

theorem section_equality [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {W U : Subgroup V} (hUW : U ≤ W) (hAW : A ≤ stabSub W)
    (h : Nat.card (Sec W U) = Nat.card A * Nat.card (fixV (autSec A W U))) :
    U ≤ fixV A ∧ W ⊔ fixV A = ⊤ := by
  obtain ⟨hw, hb, -⟩ := section_numerics hA hUW hAW
  have hcw := card_inf_fixV_le_autSec (A := A) hUW hAW
  have hsu := card_sec_mul hUW
  have hcu : Nat.card ↥(U ⊓ fixV A) ≤ Nat.card U := Subgroup.card_le_of_le inf_le_left
  have hsS : 0 < Nat.card (Sec W U) := Nat.card_pos
  have hu : 0 < Nat.card U := Nat.card_pos
  have hapos : 0 < Nat.card A := Nat.card_pos
  have hcS : 0 < Nat.card (fixV (autSec A W U)) := Nat.card_pos
  have hUeq : Nat.card ↥(U ⊓ fixV A) = Nat.card U := by
    rw [h] at hb
    have h1 : (Nat.card A * Nat.card (fixV (autSec A W U))) * Nat.card U ≤
        (Nat.card A * Nat.card (fixV (autSec A W U))) * Nat.card ↥(U ⊓ fixV A) := by
      simpa [mul_assoc] using hb
    have := Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hapos hcS)
    exact le_antisymm hcu this
  have hUfix : U ≤ fixV A := by
    have : U ⊓ fixV A = U :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (hUeq ▸ le_rfl)
    exact inf_eq_left.1 this
  refine ⟨hUfix, ?_⟩
  have hWeq : Nat.card W = Nat.card A * Nat.card ↥(W ⊓ fixV A) := by
    refine le_antisymm hw ?_
    calc Nat.card A * Nat.card ↥(W ⊓ fixV A)
        ≤ Nat.card A * (Nat.card (fixV (autSec A W U)) * Nat.card ↥(U ⊓ fixV A)) :=
          Nat.mul_le_mul_left _ hcw
      _ = Nat.card (Sec W U) * Nat.card U := by rw [h, hUeq]; ring
      _ = Nat.card W := hsu
  have hv : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [B1.card_bot_mul_card_fixV] at this
  have hsup := card_mul_card_fixV_le A W
  have hWpos : 0 < Nat.card ↥(W ⊓ fixV A) := Nat.card_pos
  have hcsup : Nat.card ↥(W ⊔ fixV A) = Nat.card V := by
    refine le_antisymm (by simpa using Subgroup.card_le_of_le (le_top : (W ⊔ fixV A) ≤ ⊤)) ?_
    have h1 : Nat.card ↥(W ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) =
        Nat.card A * Nat.card (fixV A) * Nat.card ↥(W ⊓ fixV A) := by
      rw [hsup, hWeq]; ring
    have h2 := Nat.eq_of_mul_eq_mul_right hWpos h1
    rw [h2]
    exact hv
  exact Subgroup.eq_top_of_card_eq _ (by simpa using hcsup)

end CFSG.Quasithin
