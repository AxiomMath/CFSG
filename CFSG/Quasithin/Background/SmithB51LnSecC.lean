module

public import CFSG.Quasithin.Background.SmithB51LnReal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

section Quot

variable {V : Type} [CommGroup V] {n : ℕ} {L : Subgroup (MulAut V)} {W Y Z : Subgroup V}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥L} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}

@[expose] def secImg (W Z Y : Subgroup V) : Subgroup (Sec W Z) :=
  (Y.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))

theorem mk_mem_secImg (hZY : Z ≤ Y) (w : ↥W) :
    (QuotientGroup.mk w : Sec W Z) ∈ secImg W Z Y ↔ (w : V) ∈ Y := by
  constructor
  · rintro ⟨y, hy, hyw⟩
    have hy : (y : V) ∈ Y := hy
    have h1 : y⁻¹ * w ∈ Z.subgroupOf W := QuotientGroup.eq.1 hyw
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 := Y.mul_mem hy (hZY h1)
    simpa using h2
  · intro hw
    exact ⟨w, hw, rfl⟩

@[expose] noncomputable def secHomL (L : Subgroup (MulAut V)) (hLW : L ≤ stabSub W)
    (hLZ : L ≤ stabSub Z) : ↥L →* ↥(autSec L W Z) :=
  (B5.secHom L hLW hLZ).codRestrict _ fun g => by
    rw [← B5.range_secHom L hLW hLZ]
    exact ⟨g, rfl⟩

theorem secHomL_surjective (hLW : L ≤ stabSub W) (hLZ : L ≤ stabSub Z) :
    Function.Surjective (secHomL L hLW hLZ) := by
  intro y
  have hy : (y : MulAut (Sec W Z)) ∈ (B5.secHom L hLW hLZ).range := by
    rw [B5.range_secHom L hLW hLZ]; exact y.2
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

theorem RealM.toSec (h : RealM L W Y π M) (hZY : Z ≤ Y) (hLZ : L ≤ stabSub Z) :
    RealM (autSec L W Z) ⊤ (secImg W Z Y) ((secHomL L h.hLW hLZ).comp π) M := by
  have hLW := h.hLW
  obtain ⟨hπ, hYW, hLW', hLY', β, hβs, hβk, hβe⟩ := h
  have hker : ∀ z ∈ Z.subgroupOf W, z ∈ β.ker := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [MonoidHom.mem_ker, hβk]
    exact hZY hz
  let lift : Sec W Z →* Multiplicative (Fin n → ZMod 2) := QuotientGroup.lift _ β hker
  have hlift : ∀ w : ↥W, lift (QuotientGroup.mk w) = β w := fun _ => rfl
  refine ⟨(secHomL_surjective hLW hLZ).comp hπ, le_top, fun _ _ _ => trivial, ?_,
    lift.comp (⊤ : Subgroup (Sec W Z)).subtype, ?_, ?_, ?_⟩
  · intro l s hs
    obtain ⟨y, hy, rfl⟩ := hs
    obtain ⟨g, hg⟩ := secHomL_surjective hLW hLZ l
    rw [← hg]
    show B5.secHom L hLW hLZ g (QuotientGroup.mk y) ∈ _
    rw [B5.secHom_mk]
    refine ⟨_, ?_, rfl⟩
    have hy : (y : V) ∈ Y := hy
    exact hLY' g _ hy
  · intro x
    obtain ⟨w, hw⟩ := hβs x
    exact ⟨⟨QuotientGroup.mk w, trivial⟩, hw⟩
  · rintro ⟨s, -⟩
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    show lift (QuotientGroup.mk w) = 1 ↔ _
    rw [hlift, hβk, mk_mem_secImg hZY]
  · rintro γ ⟨s, -⟩ -
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    have hW' : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := hLW' (π γ) w w.2
    show Multiplicative.toAdd (lift (B5.secHom L hLW hLZ (π γ) (QuotientGroup.mk w))) =
      M γ *ᵥ Multiplicative.toAdd (lift (QuotientGroup.mk w))
    rw [B5.secHom_mk, hlift, hlift]
    exact hβe γ w hW'

theorem commV_autSec_eq_top (hLW : L ≤ stabSub W) (hLY : L ≤ stabSub Y)
    (hcomm : commSub W L ⊔ Y = W) : commV (autSec L W Y) = ⊤ := by
  set φ : ↥W →* Sec W Y := QuotientGroup.mk' (Y.subgroupOf W) with hφ
  set T : Subgroup V := ((commV (autSec L W Y)).comap φ).map W.subtype with hT
  have hle : commSub W L ≤ T := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    have hxw : x w ∈ W := (hLW hx w).2 hw
    refine ⟨⟨x w, hxw⟩ * ⟨w, hw⟩⁻¹, ?_, rfl⟩
    show φ (⟨x w, hxw⟩ * ⟨w, hw⟩⁻¹) ∈ commV (autSec L W Y)
    rw [map_mul, map_inv]
    have hxs : B5.secHom L hLW hLY ⟨x, hx⟩ ∈ autSec L W Y := by
      rw [← B5.range_secHom L hLW hLY]; exact ⟨_, rfl⟩
    have : (B5.secHom L hLW hLY ⟨x, hx⟩) (QuotientGroup.mk ⟨w, hw⟩) *
        (QuotientGroup.mk ⟨w, hw⟩ : Sec W Y)⁻¹ ∈ commV (autSec L W Y) :=
      Subgroup.subset_closure ⟨_, hxs, QuotientGroup.mk ⟨w, hw⟩, rfl⟩
    rw [B5.secHom_mk] at this
    exact this
  rw [eq_top_iff]
  intro s _
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  have hw : (w : V) ∈ commSub W L ⊔ Y := by rw [hcomm]; exact w.2
  obtain ⟨a, ha, y, hy, hay⟩ := Subgroup.mem_sup.1 hw
  obtain ⟨a', ha', rfl⟩ := hle ha
  have ha' : φ a' ∈ commV (autSec L W Y) := ha'
  simp only [Subgroup.coe_subtype] at hay
  have hyW : y ∈ W := by
    have : y = (a' : V)⁻¹ * w := by rw [← hay]; group
    rw [this]
    exact W.mul_mem (W.inv_mem a'.2) w.2
  have hmk : (QuotientGroup.mk w : Sec W Y) = φ a' := by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    show ((w : V))⁻¹ * (a' : V) ∈ Y
    have : ((w : V))⁻¹ * (a' : V) = y⁻¹ := by rw [← hay]; group
    rw [this]
    exact Y.inv_mem hy
  rw [hmk]
  exact ha'

theorem RealM.ne_bot (h : RealM L W ⊥ π M) (hn : 1 ≤ n) : W ≠ ⊥ := by
  intro hW
  have h1 := h.card_sec
  subst hW
  have h2 : Nat.card (Sec (⊥ : Subgroup V) ⊥) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 a.2)
    have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 b.2)
    rw [ha, hb]
  rw [h2] at h1
  have : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem RealM.commSub_sup [Finite V] (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat)
    (hn : 2 ≤ n) : commSub W L ⊔ Y = W := by
  have hinv : ∀ l ∈ L, ∀ x ∈ commSub W L ⊔ Y, l x ∈ commSub W L ⊔ Y :=
    CFSG.Quasithin.isInv_sup (commSub_inv_H L W) (fun l hl y hy => h.2.2.2.1 ⟨l, hl⟩ y hy)
  have hle : commSub W L ⊔ Y ≤ W :=
    sup_le (commSub_le_of_invariant fun l hl w hw => h.2.2.1 ⟨l, hl⟩ w hw) h.2.1
  rcases h.eq_or_eq hM hinv le_sup_right hle with h1 | h1
  · exfalso
    have hWY : W ≤ Y := by
      intro w hw
      refine h.mem_of_fixed hM hn hw fun l hl => ?_
      rw [← h1]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩)
    have hc := h.card_sec
    have h2 : Nat.card (Sec W Y) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hWY (W.mul_mem (W.inv_mem a.2) b.2)
    rw [h2] at hc
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · exact h1

end Quot

end CFSG.Quasithin.B5.Ln
