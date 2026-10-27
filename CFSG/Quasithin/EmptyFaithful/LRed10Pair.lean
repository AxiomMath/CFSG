module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace LRed10

section Basic

variable {W : Type*} [CommGroup W]

theorem mem_commV_of_mem {L : Subgroup (MulAut W)} {x : MulAut W} (hx : x ∈ L) {u : W}
    (hu : u ∈ commV L) : x u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hu

theorem mem_commV_of_commute {L : Subgroup (MulAut W)} {φ : MulAut W}
    (hφ : ∀ x ∈ L, φ * x = x * φ) {u : W} (hu : u ∈ commV L) : φ u ∈ commV L :=
  CFSG.Quasithin.apply_mem_commV_of_forall_commute hφ hu

theorem commV_bot : commV (⊥ : Subgroup (MulAut W)) = ⊥ :=
  CFSG.Quasithin.FixVLat.commV_bot

theorem fixV_bot' : fixV (⊥ : Subgroup (MulAut W)) = ⊤ :=
  CFSG.Quasithin.B1.fixV_bot

structure BlkProp (L P : Subgroup (MulAut W)) : Prop where
  le : P ≤ L
  ineq : ∀ B : Subgroup (MulAut W), B ≤ P →
    rk ↥B + rk ↥(fixV B ⊓ commV L) ≤ rk ↥(commV L)
  rank : rk ↥(commV L) ≤ 2 * rk ↥(fixV P ⊓ commV L)

theorem BlkProp.bot : BlkProp (⊥ : Subgroup (MulAut W)) ⊥ := by
  have h : fixV (⊥ : Subgroup (MulAut W)) ⊓ commV ⊥ = ⊥ := by
    rw [commV_bot, inf_bot_eq]
  refine ⟨le_rfl, fun B hB => ?_, ?_⟩
  · rw [le_bot_iff.1 hB, h, commV_bot]
    simp [rk_bot]
  · rw [h, commV_bot]
    simp [rk_bot]

structure Pair2 (L₁ L₂ P₁ P₂ Kst : Subgroup (MulAut W)) : Prop where
  blk₁ : BlkProp L₁ P₁
  blk₂ : BlkProp L₂ P₂
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  ind : L₁ ⊓ L₂ = ⊥
  sup : fixV Kst ⊔ commV L₁ ⊔ commV L₂ = ⊤
  ind₁ : commV L₁ ⊓ (fixV Kst ⊔ commV L₂) ≤ fixV Kst
  ind₂ : commV L₂ ⊓ (fixV Kst ⊔ commV L₁) ≤ fixV Kst
  v₁ : fixV Kst ⊓ commV L₁ = ⊥
  v₂ : fixV Kst ⊓ commV L₂ = ⊥
  kinv : ∀ φ ∈ P₁ ⊔ P₂, ∀ w ∈ fixV Kst, φ w ∈ fixV Kst

variable {L₁ L₂ P₁ P₂ Kst : Subgroup (MulAut W)}

theorem Pair2.comm' (h : Pair2 L₁ L₂ P₁ P₂ Kst) : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a :=
  fun a ha b hb => h.comm a (h.blk₁.le ha) b (h.blk₂.le hb)

theorem Pair2.comm'' (h : Pair2 L₁ L₂ P₁ P₂ Kst) : ∀ b ∈ P₂, ∀ a ∈ P₁, b * a = a * b :=
  fun b hb a ha => (h.comm' a ha b hb).symm

theorem Pair2.inf_P (h : Pair2 L₁ L₂ P₁ P₂ Kst) : P₁ ⊓ P₂ = ⊥ := by
  refine eq_bot_iff.2 ?_
  rw [← h.ind]
  exact inf_le_inf h.blk₁.le h.blk₂.le

theorem Pair2.inf_U (h : Pair2 L₁ L₂ P₁ P₂ Kst) : commV L₁ ⊓ commV L₂ = ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  have h1 : u ∈ commV L₁ ⊓ (fixV Kst ⊔ commV L₂) := ⟨hu.1, Subgroup.mem_sup_right hu.2⟩
  have h2 : u ∈ fixV Kst ⊓ commV L₁ := ⟨h.ind₁ h1, hu.1⟩
  rw [h.v₁] at h2
  exact h2

theorem Pair2.inf_X (h : Pair2 L₁ L₂ P₁ P₂ Kst) : (fixV Kst ⊔ commV L₁) ⊓ commV L₂ = ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  have h1 : u ∈ fixV Kst := h.ind₂ ⟨hu.2, hu.1⟩
  have h2 : u ∈ fixV Kst ⊓ commV L₂ := ⟨h1, hu.2⟩
  rwa [h.v₂] at h2

theorem Pair2.triv₁ (h : Pair2 L₁ L₂ P₁ P₂ Kst) {φ : MulAut W} (hφ : φ ∈ L₂) {u : W}
    (hu : u ∈ commV L₁) : φ u = u := by
  have h1 : φ u ∈ commV L₁ := mem_commV_of_commute
    (fun x hx => (h.comm x hx φ hφ).symm) hu
  have h2 : φ u * u⁻¹ ∈ commV L₂ := Subgroup.subset_closure ⟨φ, hφ, u, rfl⟩
  have h3 : φ u * u⁻¹ ∈ commV L₁ := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hu)
  have h4 : φ u * u⁻¹ ∈ commV L₁ ⊓ commV L₂ := ⟨h3, h2⟩
  rw [h.inf_U, Subgroup.mem_bot] at h4
  exact mul_inv_eq_one.1 h4

theorem Pair2.triv₂ (h : Pair2 L₁ L₂ P₁ P₂ Kst) {φ : MulAut W} (hφ : φ ∈ L₁) {u : W}
    (hu : u ∈ commV L₂) : φ u = u := by
  have h1 : φ u ∈ commV L₂ := mem_commV_of_commute
    (fun x hx => h.comm φ hφ x hx) hu
  have h2 : φ u * u⁻¹ ∈ commV L₁ := Subgroup.subset_closure ⟨φ, hφ, u, rfl⟩
  have h3 : φ u * u⁻¹ ∈ commV L₂ := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hu)
  have h4 : φ u * u⁻¹ ∈ commV L₁ ⊓ commV L₂ := ⟨h2, h3⟩
  rw [h.inf_U, Subgroup.mem_bot] at h4
  exact mul_inv_eq_one.1 h4

theorem Pair2.exists_mul (h : Pair2 L₁ L₂ P₁ P₂ Kst) {φ : MulAut W} (hφ : φ ∈ P₁ ⊔ P₂) :
    ∃ a ∈ P₁, ∃ b ∈ P₂, φ = a * b := by
  let S : Subgroup (MulAut W) :=
    { carrier := {g | ∃ a ∈ P₁, ∃ b ∈ P₂, g = a * b}
      one_mem' := ⟨1, P₁.one_mem, 1, P₂.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', P₁.mul_mem ha ha', b * b', P₂.mul_mem hb hb', ?_⟩
        have := h.comm' a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, P₁.inv_mem ha, b⁻¹, P₂.inv_mem hb, ?_⟩
        have := h.comm' a⁻¹ (P₁.inv_mem ha) b⁻¹ (P₂.inv_mem hb)
        rw [mul_inv_rev, ← this] }
  have hle : P₁ ⊔ P₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, P₂.one_mem, by simp⟩)
    (fun b hb => ⟨1, P₁.one_mem, b, hb, by simp⟩)
  exact hle hφ

theorem Pair2.stab₁ (h : Pair2 L₁ L₂ P₁ P₂ Kst) {φ : MulAut W} (hφ : φ ∈ P₁ ⊔ P₂) {u : W}
    (hu : u ∈ commV L₁) : φ u ∈ commV L₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hφ
  rw [MulAut.mul_apply, h.triv₁ (h.blk₂.le hb) hu]
  exact mem_commV_of_mem (h.blk₁.le ha) hu

theorem Pair2.stab₂ (h : Pair2 L₁ L₂ P₁ P₂ Kst) {φ : MulAut W} (hφ : φ ∈ P₁ ⊔ P₂) {u : W}
    (hu : u ∈ commV L₂) : φ u ∈ commV L₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hφ
  rw [MulAut.mul_apply, h.triv₂ (h.blk₁.le ha) (mem_commV_of_mem (h.blk₂.le hb) hu)]
  exact mem_commV_of_mem (h.blk₂.le hb) hu

theorem Pair2.stab_X (h : Pair2 L₁ L₂ P₁ P₂ Kst) {φ : MulAut W} (hφ : φ ∈ P₁ ⊔ P₂) {x : W}
    (hx : x ∈ fixV Kst ⊔ commV L₁) : φ x ∈ fixV Kst ⊔ commV L₁ := by
  obtain ⟨v, hv, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [map_mul]
  exact Subgroup.mul_mem_sup (h.kinv φ hφ v hv) (h.stab₁ hφ hu)

theorem fixV_compat {X Y : Subgroup W} (hXY : X ⊓ Y = ⊥) {B : Subgroup (MulAut W)}
    (hX : ∀ φ ∈ B, ∀ x ∈ X, φ x ∈ X) (hY : ∀ φ ∈ B, ∀ y ∈ Y, φ y ∈ Y) {x y : W} (hx : x ∈ X)
    (hy : y ∈ Y) (h : x * y ∈ fixV B) : x ∈ fixV B ∧ y ∈ fixV B := by
  have key : ∀ φ ∈ B, φ x = x ∧ φ y = y := by
    intro φ hφ
    have h1 : φ x * φ y = x * y := by rw [← map_mul]; exact h φ hφ
    have h2 : x⁻¹ * φ x = y * (φ y)⁻¹ := by
      calc x⁻¹ * φ x = x⁻¹ * (φ x * φ y) * (φ y)⁻¹ := by group
        _ = x⁻¹ * (x * y) * (φ y)⁻¹ := by rw [h1]
        _ = y * (φ y)⁻¹ := by group
    have hxm : x⁻¹ * φ x ∈ X := X.mul_mem (X.inv_mem hx) (hX φ hφ x hx)
    have hym : y * (φ y)⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem (hY φ hφ y hy))
    have h3 : x⁻¹ * φ x ∈ X ⊓ Y := ⟨hxm, h2 ▸ hym⟩
    rw [hXY, Subgroup.mem_bot] at h3
    have h4 : φ x = x := (inv_mul_eq_one.1 h3).symm
    refine ⟨h4, ?_⟩
    rw [h4] at h1
    exact mul_left_cancel h1
  exact ⟨fun φ hφ => (key φ hφ).1, fun φ hφ => (key φ hφ).2⟩

@[expose] def projSub (P Q B : Subgroup (MulAut W)) (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) :
    Subgroup (MulAut W) where
  carrier := {a | a ∈ P ∧ ∃ b ∈ Q, a * b ∈ B}
  one_mem' := ⟨P.one_mem, 1, Q.one_mem, by simp⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨P.mul_mem ha ha', b * b', Q.mul_mem hb hb', ?_⟩
    have e : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [e]
    exact B.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨P.inv_mem ha, b⁻¹, Q.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
        _ = (a * b)⁻¹ := by rw [hc a ha b hb]
    rw [e]
    exact B.inv_mem hab

theorem projSub_le {P Q B : Subgroup (MulAut W)} {hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a} :
    projSub P Q B hc ≤ P := fun _ ha => ha.1

theorem Pair2.fixV_inf_comm₁ (h : Pair2 L₁ L₂ P₁ P₂ Kst) {B : Subgroup (MulAut W)}
    (hB : B ≤ P₁ ⊔ P₂) :
    fixV B ⊓ commV L₁ = fixV (projSub P₁ P₂ B h.comm') ⊓ commV L₁ := by
  ext u
  constructor
  · rintro ⟨hu, hu₁⟩
    refine ⟨fun a ⟨_, b, hb, hab⟩ => ?_, hu₁⟩
    have h1 : (a * b) u = u := hu _ hab
    rw [MulAut.mul_apply, h.triv₁ (h.blk₂.le hb) hu₁] at h1
    exact h1
  · rintro ⟨hu, hu₁⟩
    refine ⟨fun x hx => ?_, hu₁⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (hB hx)
    have h1 : a u = u := hu a ⟨ha, b, hb, hx⟩
    rw [MulAut.mul_apply, h.triv₁ (h.blk₂.le hb) hu₁, h1]

theorem Pair2.fixV_inf_comm₂ (h : Pair2 L₁ L₂ P₁ P₂ Kst) {B : Subgroup (MulAut W)}
    (hB : B ≤ P₁ ⊔ P₂) :
    fixV B ⊓ commV L₂ = fixV (projSub P₂ P₁ B h.comm'') ⊓ commV L₂ := by
  ext u
  constructor
  · rintro ⟨hu, hu₂⟩
    refine ⟨fun b ⟨_, a, ha, hba⟩ => ?_, hu₂⟩
    have h1 : (b * a) u = u := hu _ hba
    rw [MulAut.mul_apply, h.triv₂ (h.blk₁.le ha) hu₂] at h1
    exact h1
  · rintro ⟨hu, hu₂⟩
    refine ⟨fun x hx => ?_, hu₂⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (hB hx)
    have h1 : b u = u := hu b ⟨hb, a, ha, by rw [h.comm'' b hb a ha]; exact hx⟩
    rw [MulAut.mul_apply, h1, h.triv₂ (h.blk₁.le ha) hu₂]

theorem Pair2.le_sup_projSub (h : Pair2 L₁ L₂ P₁ P₂ Kst) {B : Subgroup (MulAut W)}
    (hB : B ≤ P₁ ⊔ P₂) :
    B ≤ projSub P₁ P₂ B h.comm' ⊔ projSub P₂ P₁ B h.comm'' := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (hB hx)
  exact Subgroup.mul_mem_sup ⟨ha, b, hb, hx⟩
    ⟨hb, a, ha, by rw [h.comm'' b hb a ha]; exact hx⟩

end Basic

section Count

variable {W : Type*} [CommGroup W] [Finite W] {L₁ L₂ P₁ P₂ Kst : Subgroup (MulAut W)}

theorem rk_fixV_inf_sup {X Y : Subgroup W} (hXY : X ⊓ Y = ⊥) {B : Subgroup (MulAut W)}
    (hX : ∀ φ ∈ B, ∀ x ∈ X, φ x ∈ X) (hY : ∀ φ ∈ B, ∀ y ∈ Y, φ y ∈ Y) :
    rk ↥(fixV B ⊓ (X ⊔ Y)) = rk ↥(fixV B ⊓ X) + rk ↥(fixV B ⊓ Y) := by
  have hsup : fixV B ⊓ (X ⊔ Y) = (fixV B ⊓ X) ⊔ (fixV B ⊓ Y) := by
    refine le_antisymm (fun c hc => ?_)
      (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hc.2
    obtain ⟨h1, h2⟩ := fixV_compat hXY hX hY hx hy hc.1
    exact Subgroup.mul_mem_sup ⟨h1, hx⟩ ⟨h2, hy⟩
  have hinf : (fixV B ⊓ X) ⊓ (fixV B ⊓ Y) = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    have : c ∈ X ⊓ Y := ⟨hc.1.2, hc.2.2⟩
    rwa [hXY] at this
  have := rk_sup_add_rk_inf (fixV B ⊓ X) (fixV B ⊓ Y)
  rw [hinf, rk_bot, ← hsup] at this
  omega

theorem Pair2.rk_fixV (h : Pair2 L₁ L₂ P₁ P₂ Kst) {B : Subgroup (MulAut W)} (hB : B ≤ P₁ ⊔ P₂) :
    rk ↥(fixV B) = rk ↥(fixV B ⊓ fixV Kst) + rk ↥(fixV B ⊓ commV L₁) +
      rk ↥(fixV B ⊓ commV L₂) := by
  have e1 : fixV B ⊓ ((fixV Kst ⊔ commV L₁) ⊔ commV L₂) = fixV B := by
    rw [show (fixV Kst ⊔ commV L₁) ⊔ commV L₂ = ⊤ from h.sup, inf_top_eq]
  have r1 := rk_fixV_inf_sup (B := B) h.inf_X (fun φ hφ x hx => h.stab_X (hB hφ) hx)
    (fun φ hφ y hy => h.stab₂ (hB hφ) hy)
  have r2 := rk_fixV_inf_sup (B := B) (X := fixV Kst) (Y := commV L₁) h.v₁
    (fun φ hφ x hx => h.kinv φ (hB hφ) x hx) (fun φ hφ y hy => h.stab₁ (hB hφ) hy)
  rw [e1] at r1
  omega

theorem Pair2.rk_total (h : Pair2 L₁ L₂ P₁ P₂ Kst) :
    rk W = rk ↥(fixV Kst) + rk ↥(commV L₁) + rk ↥(commV L₂) := by
  have := h.rk_fixV (B := ⊥) bot_le
  rw [fixV_bot', top_inf_eq, top_inf_eq, top_inf_eq, rk_top] at this
  exact this

theorem Pair2.rk_le_projSub (h : Pair2 L₁ L₂ P₁ P₂ Kst) {B : Subgroup (MulAut W)}
    (hB : B ≤ P₁ ⊔ P₂) :
    rk ↥B ≤ rk ↥(projSub P₁ P₂ B h.comm') + rk ↥(projSub P₂ P₁ B h.comm'') := by
  have h1 := B2F.rk_sup_add_rk_inf_of_commute (A := projSub P₁ P₂ B h.comm')
    (B := projSub P₂ P₁ B h.comm'') (fun a ha b hb => h.comm' a ha.1 b hb.1)
  have h2 : projSub P₁ P₂ B h.comm' ⊓ projSub P₂ P₁ B h.comm'' = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ P₁ ⊓ P₂ := ⟨hx.1.1, hx.2.1⟩
    rwa [h.inf_P] at this
  have h3 := rk_mono (h.le_sup_projSub hB)
  rw [h2, rk_bot] at h1
  omega

theorem Pair2.rk_B_le (h : Pair2 L₁ L₂ P₁ P₂ Kst) {B : Subgroup (MulAut W)} (hB : B ≤ P₁ ⊔ P₂) :
    rk ↥B + rk ↥(fixV Kst) ≤ rkIdx (fixV B) + rk ↥(fixV B ⊓ fixV Kst) := by
  have r1 := h.rk_fixV hB
  have r2 := h.rk_total
  have r3 := rk_add_rkIdx (fixV B)
  have r4 := h.rk_le_projSub hB
  have r5 := h.blk₁.ineq (projSub P₁ P₂ B h.comm') projSub_le
  have r6 := h.blk₂.ineq (projSub P₂ P₁ B h.comm'') projSub_le
  rw [← h.fixV_inf_comm₁ hB] at r5
  rw [← h.fixV_inf_comm₂ hB] at r6
  omega

theorem Pair2.two_mul_rkIdx_le (h : Pair2 L₁ L₂ P₁ P₂ Kst) (hfix : fixV Kst ≤ fixV (P₁ ⊔ P₂)) :
    2 * rkIdx (fixV (P₁ ⊔ P₂)) ≤ rkIdx (fixV Kst) := by
  have r1 := h.rk_fixV (B := P₁ ⊔ P₂) le_rfl
  have r2 := h.rk_total
  have r3 := rk_add_rkIdx (fixV (P₁ ⊔ P₂))
  have r4 := rk_add_rkIdx (fixV Kst)
  have e1 : fixV (P₁ ⊔ P₂) ⊓ fixV Kst = fixV Kst := inf_eq_right.2 hfix
  have e2 : fixV (P₁ ⊔ P₂) ⊓ commV L₁ = fixV P₁ ⊓ commV L₁ := by
    ext u
    constructor
    · rintro ⟨hu, hu₁⟩
      exact ⟨fun a ha => hu a (Subgroup.mem_sup_left ha), hu₁⟩
    · rintro ⟨hu, hu₁⟩
      refine ⟨fun x hx => ?_, hu₁⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
      rw [MulAut.mul_apply, h.triv₁ (h.blk₂.le hb) hu₁, hu a ha]
  have e3 : fixV (P₁ ⊔ P₂) ⊓ commV L₂ = fixV P₂ ⊓ commV L₂ := by
    ext u
    constructor
    · rintro ⟨hu, hu₂⟩
      exact ⟨fun b hb => hu b (Subgroup.mem_sup_right hb), hu₂⟩
    · rintro ⟨hu, hu₂⟩
      refine ⟨fun x hx => ?_, hu₂⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
      rw [MulAut.mul_apply, hu b hb, h.triv₂ (h.blk₁.le ha) hu₂]
  rw [e1, e2, e3] at r1
  have r5 := h.blk₁.rank
  have r6 := h.blk₂.rank
  omega

end Count

end LRed10

end CFSG.Quasithin
