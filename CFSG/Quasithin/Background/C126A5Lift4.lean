module

public import CFSG.Quasithin.Background.C126A5Comm
public import CFSG.Quasithin.Background.C126A5Lift2
public import CFSG.Quasithin.Background.C126A5Module

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

@[expose] def cq (A Q W : Subgroup G) (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W) : Subgroup G where
  carrier := {k | k ∈ A ∧ ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W}
  one_mem' := ⟨A.one_mem, fun q _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, fun q hq => by
    have h1 := hAW a ha.1 _ (hb.2 q hq)
    have h2 := ha.2 q hq
    have : a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
    rw [this]; exact W.mul_mem h1 h2⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, fun q hq => by
    have h2 := ha.2 q hq
    have h3 : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h3]; exact hAW a⁻¹ (A.inv_mem ha.1) _ (W.inv_mem h2)⟩

theorem conj_mem_cq {A Q W : Subgroup G} {hAW : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W}
    (hAQ : ∀ a ∈ A, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) {a z : G} (ha : a ∈ A)
    (hz : z ∈ cq A Q W hAW) : a * z * a⁻¹ ∈ cq A Q W hAW := by
  refine ⟨A.mul_mem (A.mul_mem ha hz.1) (A.inv_mem ha), fun q hq => ?_⟩
  have h1 := hz.2 (a⁻¹ * q * a) (by simpa using hAQ a⁻¹ (A.inv_mem ha) q hq)
  have := hAW a ha _ h1
  have e : a * z * a⁻¹ * q * (a * z * a⁻¹)⁻¹ * q⁻¹ =
      a * (z * (a⁻¹ * q * a) * z⁻¹ * (a⁻¹ * q * a)⁻¹) * a⁻¹ := by group
  rw [e]; exact this

@[expose] def valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

variable (d) in
@[expose] def Vc : Subgroup G := (commV d.L).map (valHom hV)

theorem mem_Vc {u : G} : u ∈ Vc d ↔ ∃ w ∈ commV d.L, w.val = u := by
  unfold Vc; simp [valHom, Subgroup.mem_map]; rfl

theorem Vc_le_V : Vc d ≤ V := by
  rintro u hu
  obtain ⟨w, -, rfl⟩ := mem_Vc.1 hu
  exact w.val_mem

theorem Vc_conj {a u : G} (ha : a ∈ A₁ s d) (hu : u ∈ Vc d) : a * u * a⁻¹ ∈ Vc d := by
  obtain ⟨w, hw, rfl⟩ := mem_Vc.1 hu
  obtain ⟨haH, haL⟩ := mem_A₁.1 ha
  refine mem_Vc.2 ⟨cv hV a w, act_mem_commV haL hw, cv_val hV (s.H_le_N haH) w⟩

theorem Vc_hAW : ∀ a ∈ A₁ s d, ∀ w ∈ Vc d, a * w * a⁻¹ ∈ Vc d := fun _ ha _ hw =>
  Vc_conj ha hw

variable (s d) in
@[expose] def cqK : Subgroup G := cq (A₁ s d) (pCoreOf 2 H) (Vc d) (Vc_hAW (s := s) (d := d))

theorem mem_cqK {k : G} : k ∈ cqK s d ↔ k ∈ A₁ s d ∧ ∀ q ∈ pCoreOf 2 H, k * q * k⁻¹ * q⁻¹ ∈ Vc d :=
  Iff.rfl

theorem A₁_normalizes_Q : ∀ a ∈ A₁ s d, ∀ q ∈ pCoreOf 2 H, a * q * a⁻¹ ∈ pCoreOf 2 H :=
  fun _ ha q hq => (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (A₁_le_H ha)) q).1 hq

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem four_comm_V : 4 ≤ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹}.ncard := by
  have h := four_commutators d.θ d.β d.hβ d.π (h := (⟨cv hV x, hx.mem_L⟩ : ↥d.L))
    (by rw [← d.th_of_mem hx.mem_L]; exact hx.th_eq)
  set R := Set.range fun w : ↥(commV d.L) =>
    (((⟨cv hV x, hx.mem_L⟩ : ↥d.L) : MulAut (IntMod V hV)) (w : IntMod V hV)) *
      (w : IntMod V hV)⁻¹ with hR
  have hsub : IntMod.val '' R ⊆ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹} := by
    rintro _ ⟨r, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w : IntMod V hV).val, (w : IntMod V hV).val_mem, ?_⟩
    rw [IntMod.val_mul, IntMod.val_inv]
    simp only
    rw [cv_val hV (s.H_le_N (s.Y_le hx.mem))]
  calc 4 ≤ R.ncard := h
    _ = (IntMod.val '' R).ncard := (Set.ncard_image_of_injective R IntMod.val_injective).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem comm_mem_V (q : G) (hq : q ∈ pCoreOf 2 H) :
    ∃ v ∈ V, x * q * x⁻¹ * q⁻¹ = x * v * x⁻¹ * v⁻¹ := by
  refine exists_comm_V hY hA3 hx.mem hx.ord ?_ ?_ ?_ ?_ ?_ hx.four_comm_V q hq
  · intro q hq y hy
    exact (Subgroup.mem_normalizer_iff.1 (s.Q_norm hq) y).1 hy
  · intro y hy q hq
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (s.Y_le hy)) q).1 hq
  · intro q hq
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨q, hq⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · intro c hcY hcQ
    have hn : Y ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 H : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (s.Y_le hy)⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨hcY, hcQ⟩
  · exact (MinParabolic.le_pCoreOf_of_isTwoReduced s.red)

theorem x_mem_cq : x ∈ cqK s d := by
  refine ⟨hx.x_mem_A₁, fun q hq => ?_⟩
  obtain ⟨v, hv, hqv⟩ := hx.comm_mem_V hY hA3 q hq
  rw [hqv]
  refine mem_Vc.2 ⟨cv hV x (IntMod.mk hV ⟨v, hv⟩) * (IntMod.mk hV ⟨v, hv⟩)⁻¹,
    mem_commV_gen hx.mem_L _, ?_⟩
  rw [IntMod.val_mul, IntMod.val_inv, cv_val hV (s.H_le_N (s.Y_le hx.mem))]
  rfl

theorem Khat_le_cq : Khat s d x ≤ cqK s d := by
  unfold Khat
  refine conjClosure_le fun a ha z hz => ?_
  have hxz : Subgroup.zpowers x ≤ cqK s d := by
    rw [Subgroup.zpowers_le]; exact hx.x_mem_cq hY hA3
  exact conj_mem_cq (A₁_normalizes_Q (s := s) (d := d)) ha (hxz hz)

end XData

end Lift

end CFSG.Quasithin.C126.A5
