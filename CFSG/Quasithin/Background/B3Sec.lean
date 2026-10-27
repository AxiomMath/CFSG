module

public import CFSG.Quasithin.Background.Module
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.B3

variable {G : Type*} [Group G] {K : Type*} [CommGroup K]

@[expose] def IsInv (ρ : G →* MulAut K) (W : Subgroup K) : Prop := ∀ g : G, ∀ w ∈ W, ρ g w ∈ W

abbrev Sec (W N : Subgroup K) : Type _ := ↥W ⧸ N.subgroupOf W

@[expose] def restrictEquiv (ρ : G →* MulAut K) (W : Subgroup K) (hW : IsInv ρ W) (g : G) : ↥W ≃* ↥W where
  toFun w := ⟨ρ g w, hW g w w.2⟩
  invFun w := ⟨ρ g⁻¹ w, hW g⁻¹ w w.2⟩
  left_inv w := by
    apply Subtype.ext
    show ρ g⁻¹ (ρ g w) = w
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv w := by
    apply Subtype.ext
    show ρ g (ρ g⁻¹ w) = w
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_mul' a b := by
    apply Subtype.ext
    show ρ g (a * b : K) = ρ g a * ρ g b
    exact map_mul _ _ _

theorem restrictEquiv_apply (ρ : G →* MulAut K) (W : Subgroup K) (hW : IsInv ρ W) (g : G)
    (w : ↥W) : ((restrictEquiv ρ W hW g w : ↥W) : K) = ρ g w := rfl

theorem map_restrictEquiv (ρ : G →* MulAut K) {W N : Subgroup K} (hW : IsInv ρ W)
    (hN : IsInv ρ N) (g : G) :
    (N.subgroupOf W).map (restrictEquiv ρ W hW g).toMonoidHom = N.subgroupOf W := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hN g x hx
  · intro hy
    refine ⟨(restrictEquiv ρ W hW g).symm y, ?_, (restrictEquiv ρ W hW g).apply_symm_apply y⟩
    exact hN g⁻¹ y hy

@[expose] noncomputable def secAct (ρ : G →* MulAut K) {W N : Subgroup K} (hW : IsInv ρ W)
    (hN : IsInv ρ N) : G →* MulAut (Sec W N) where
  toFun g := QuotientGroup.congr (N.subgroupOf W) (N.subgroupOf W) (restrictEquiv ρ W hW g)
    (map_restrictEquiv ρ hW hN g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      apply congrArg (QuotientGroup.mk (s := N.subgroupOf W))
      apply Subtype.ext
      show ρ 1 (x : K) = x
      rw [map_one]
      rfl
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      apply congrArg (QuotientGroup.mk (s := N.subgroupOf W))
      apply Subtype.ext
      show ρ (g * h) (x : K) = ρ g (ρ h x)
      rw [map_mul]
      rfl


theorem card_map_mk_mul_card {L : Type*} [CommGroup L] (S N : Subgroup L) (h : N ≤ S) :
    Nat.card (S.map (QuotientGroup.mk' N)) * Nat.card N = Nat.card S := by
  have h1 := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' N).domRestrict S)
  rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', MonoidHom.domRestrict_range] at h1
  have h2 : Nat.card ↥(N.subgroupOf S) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2, mul_comm] at h1
  exact h1

def secFix (ρ : G →* MulAut K) (W N : Subgroup K) (B : Subgroup G) : Subgroup ↥W where
  carrier := {w | ∀ b ∈ B, ρ b (w : K) * (w : K)⁻¹ ∈ N}
  one_mem' := by
    intro b _
    simp only [OneMemClass.coe_one, map_one, inv_one, mul_one]
    exact N.one_mem
  mul_mem' := by
    intro a a' ha ha' b hb
    have h := N.mul_mem (ha b hb) (ha' b hb)
    have e : ρ b ((a * a' : ↥W) : K) * ((a * a' : ↥W) : K)⁻¹ =
        (ρ b (a : K) * (a : K)⁻¹) * (ρ b (a' : K) * (a' : K)⁻¹) := by
      simp only [Subgroup.coe_mul, map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    rw [e]
    exact h
  inv_mem' := by
    intro a ha b hb
    have h := N.inv_mem (ha b hb)
    have e : ρ b ((a⁻¹ : ↥W) : K) * ((a⁻¹ : ↥W) : K)⁻¹ =
        (ρ b (a : K) * (a : K)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv, map_inv, inv_inv, mul_inv_rev]
      exact mul_comm _ _
    rw [e]
    exact h

theorem mem_secFix {ρ : G →* MulAut K} {W N : Subgroup K} {B : Subgroup G} {w : ↥W} :
    w ∈ secFix ρ W N B ↔ ∀ b ∈ B, ρ b (w : K) * (w : K)⁻¹ ∈ N := Iff.rfl

theorem le_secFix (ρ : G →* MulAut K) {W N : Subgroup K} (hN : IsInv ρ N) (B : Subgroup G) :
    N.subgroupOf W ≤ secFix ρ W N B := by
  intro w hw b _
  have hw' : (w : K) ∈ N := hw
  exact N.mul_mem (hN b w hw') (N.inv_mem hw')

theorem fixV_sec_eq (ρ : G →* MulAut K) {W N : Subgroup K} (hW : IsInv ρ W) (hN : IsInv ρ N)
    (B : Subgroup G) :
    fixV (B.map (secAct ρ hW hN)) = (secFix ρ W N B).map (QuotientGroup.mk' (N.subgroupOf W)) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H w =>
    have key : (QuotientGroup.mk w : Sec W N) ∈ fixV (B.map (secAct ρ hW hN)) ↔
        w ∈ secFix ρ W N B := by
      constructor
      · intro h b hb
        have h1 := h (secAct ρ hW hN b) (Subgroup.mem_map_of_mem _ hb)
        have h2 : (QuotientGroup.mk (restrictEquiv ρ W hW b w) : Sec W N) = QuotientGroup.mk w := h1
        rw [QuotientGroup.eq] at h2
        have h3 := N.inv_mem (show (((restrictEquiv ρ W hW b w)⁻¹ * w : ↥W) : K) ∈ N from h2)
        simpa [restrictEquiv_apply, mul_comm] using h3
      · intro h x hx
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
        show (QuotientGroup.mk (restrictEquiv ρ W hW b w) : Sec W N) = QuotientGroup.mk w
        rw [QuotientGroup.eq]
        have h3 := N.inv_mem (h b hb)
        show (((restrictEquiv ρ W hW b w)⁻¹ * w : ↥W) : K) ∈ N
        simpa [restrictEquiv_apply, mul_comm] using h3
    rw [key]
    constructor
    · intro h
      exact ⟨w, h, rfl⟩
    · rintro ⟨w', hw', hw'eq⟩
      have h1 : w'⁻¹ * w ∈ N.subgroupOf W := by
        have := QuotientGroup.eq.1 hw'eq
        simpa using this
      have h2 : w'⁻¹ * w ∈ secFix ρ W N B := le_secFix ρ hN B h1
      have h3 : w = w' * (w'⁻¹ * w) := by simp
      rw [h3]
      exact (secFix ρ W N B).mul_mem hw' h2

theorem card_fixV_sec (ρ : G →* MulAut K) {W N : Subgroup K} (hW : IsInv ρ W) (hN : IsInv ρ N)
    (B : Subgroup G) :
    Nat.card (fixV (B.map (secAct ρ hW hN))) * Nat.card ↥(N ⊓ W) =
      Nat.card {w : K // w ∈ W ∧ ∀ b ∈ B, ρ b w * w⁻¹ ∈ N} := by
  rw [fixV_sec_eq ρ hW hN B]
  have h1 := card_map_mk_mul_card (secFix ρ W N B) (N.subgroupOf W) (le_secFix ρ hN B)
  have h2 : Nat.card ↥(N.subgroupOf W) = Nat.card ↥(N ⊓ W) := by
    rw [← Subgroup.inf_subgroupOf_right N W]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ W ≤ W)).toEquiv
  rw [h2] at h1
  rw [h1]
  refine Nat.card_congr ?_
  exact
    { toFun := fun s => ⟨(s.1 : K), s.1.2, s.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
      left_inv := fun s => rfl
      right_inv := fun w => rfl }

end CFSG.Quasithin.B3
