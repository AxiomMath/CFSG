module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Defs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Lift

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup

section Transfer

variable {X Y : Type*} [Group X] [Group Y]

theorem model3_transfer_comm_of_map_comm (γ : X →* Y) {W : Subgroup X} (hW : W ⊓ γ.ker = ⊥)
    {a b : X} (ha : a ∈ W) (hb : b ∈ W) (hab : γ a * γ b = γ b * γ a) : a * b = b * a := by
  have hmem : (b * a)⁻¹ * (a * b) ∈ W ⊓ γ.ker := by
    refine ⟨W.mul_mem (W.inv_mem (W.mul_mem hb ha)) (W.mul_mem ha hb), MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, map_mul, map_mul, hab, inv_mul_cancel]
  rw [hW, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem model3_transfer_injOn (γ : X →* Y) {W : Subgroup X} (hW : W ⊓ γ.ker = ⊥)
    {K : Subgroup X} (hKW : K ≤ W) : Set.InjOn γ (K : Set X) := by
  intro a ha b hb hab
  have hmem : a⁻¹ * b ∈ W ⊓ γ.ker := by
    refine ⟨W.mul_mem (W.inv_mem (hKW ha)) (hKW hb), MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  rw [hW, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem

theorem model3_center_map_eq (γ : X →* Y) {W : Subgroup X} (hW : W ⊓ γ.ker = ⊥) :
    (center ↥(W.map γ)).map (W.map γ).subtype = ((center ↥W).map W.subtype).map γ := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, hwW, hwz⟩ := Subgroup.mem_map.mp z.2
    have hwc : (⟨w, hwW⟩ : ↥W) ∈ center ↥W := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hcomm := (Subgroup.mem_center_iff.mp hz) ⟨γ g, Subgroup.mem_map_of_mem γ g.2⟩
      have hcomm' : γ g * (z : Y) = (z : Y) * γ g := congrArg Subtype.val hcomm
      rw [← hwz] at hcomm'
      exact model3_transfer_comm_of_map_comm γ hW g.2 hwW hcomm'
    exact Subgroup.mem_map.mpr ⟨(w : X), Subgroup.mem_map.mpr ⟨⟨w, hwW⟩, hwc, rfl⟩, hwz⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨γ w, Subgroup.mem_map_of_mem γ w.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp g.2
    have hcomm : u * (w : X) = (w : X) * u :=
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hw) ⟨u, hu⟩)
    apply Subtype.ext
    show (g : Y) * γ w = γ w * (g : Y)
    rw [← hug, ← map_mul, ← map_mul, hcomm]

theorem model3_card_center_map (γ : X →* Y) {W : Subgroup X} (hW : W ⊓ γ.ker = ⊥) :
    Nat.card ↥(center ↥(W.map γ)) = Nat.card ↥(center ↥W) := by
  have hKW : (center ↥W).map W.subtype ≤ W := Subgroup.map_subtype_le _
  have hinj := model3_transfer_injOn γ hW hKW
  have himg : Nat.card ↥(((center ↥W).map W.subtype).map γ) =
      Nat.card ↥((center ↥W).map W.subtype) := by
    have h := Nat.card_image_of_injOn hinj
    rw [← Subgroup.coe_map] at h
    exact h
  rw [← Subgroup.card_subtype (W.map γ) (center ↥(W.map γ)), model3_center_map_eq γ hW, himg,
    Subgroup.card_subtype W (center ↥W)]

theorem model3_lift_involution (γ : X →* Y) (hodd : Odd (Nat.card γ.ker)) {x : Y}
    (hx : x ∈ γ.range) (hx2 : x * x = 1) : ∃ x' : X, x' * x' = 1 ∧ γ x' = x := by
  obtain ⟨x₀, rfl⟩ := MonoidHom.mem_range.mp hx
  have hk : x₀ * x₀ ∈ γ.ker := MonoidHom.mem_ker.mpr (by rw [map_mul]; exact hx2)
  have hpow : (x₀ * x₀) ^ Nat.card γ.ker = 1 := by
    have h1 : (⟨x₀ * x₀, hk⟩ : γ.ker) ^ Nat.card γ.ker = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  refine ⟨x₀ ^ Nat.card γ.ker, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, pow_mul, sq]
    exact hpow
  · rw [map_pow]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, sq, hx2, one_pow, one_mul]

theorem model3A_map (γ : X →* Y) {W : Subgroup X} (hW : W ⊓ γ.ker = ⊥) {q : ℕ}
    (h : Model3A X W q) : Model3A Y (W.map γ) q := by
  unfold Model3A at h ⊢
  refine ⟨(model3_card_center_map γ hW).trans h.1, ?_⟩
  intro z hz
  have hz' : (z : Y) ∈ ((center ↥W).map W.subtype).map γ := by
    rw [← model3_center_map_eq γ hW]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  obtain ⟨u, hu, hzu⟩ := Subgroup.mem_map.mp hz'
  obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp hu
  have hsq : W.subtype w * W.subtype w = 1 := by
    rw [← map_mul, h.2 w hw, map_one]
  apply Subtype.ext
  show (z : Y) * (z : Y) = 1
  rw [← hzu, ← hwu, ← map_mul, hsq, map_one]

theorem model3B_map (γ : X →* Y) (hγ : Function.Surjective γ) (hodd : Odd (Nat.card γ.ker))
    {W : Subgroup X} (hW : W ⊓ γ.ker = ⊥) (h : Model3B X W) : Model3B Y (W.map γ) := by
  unfold Model3B at h ⊢
  intro x hx
  have hxr : x ∈ γ.range := MonoidHom.mem_range.mpr (hγ x)
  obtain ⟨x', hx'2, hx'⟩ := model3_lift_involution γ hodd hxr hx
  obtain ⟨y', hy'⟩ := h x' hx'2
  refine ⟨γ y', ?_⟩
  rw [model3_center_map_eq γ hW]
  refine Subgroup.mem_map.mpr ⟨y'⁻¹ * x' * y', hy', ?_⟩
  rw [map_mul, map_mul, map_inv, hx']

theorem model3_map_conj_map (γ : X →* Y) (g : X) (K : Subgroup X) :
    (K.map (MulAut.conj g⁻¹).toMonoidHom).map γ =
      (K.map γ).map (MulAut.conj (γ g)⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem model3_sup_conj_map (γ : X →* Y) (g : X) (K : Subgroup X) :
    (K ⊔ K.map (MulAut.conj g⁻¹).toMonoidHom).map γ =
      K.map γ ⊔ (K.map γ).map (MulAut.conj (γ g)⁻¹).toMonoidHom := by
  rw [Subgroup.map_sup, model3_map_conj_map γ g K]

theorem model3_isPGroup_map (γ : X →* Y) {S : Subgroup X} (hP : IsPGroup 2 ↥S) :
    IsPGroup 2 ↥(S.map γ) :=
  hP.map γ

theorem model3C_map (γ : X →* Y) (hγ : Function.Surjective γ) {W : Subgroup X}
    (hW : W ⊓ γ.ker = ⊥) (h : Model3C X W) : Model3C Y (W.map γ) := by
  unfold Model3C at h ⊢
  intro τ hτ
  obtain ⟨τ', rfl⟩ := hγ τ
  have hnot : ¬ IsPGroup 2 ↥((center ↥W).map W.subtype ⊔
      ((center ↥W).map W.subtype).map (MulAut.conj τ'⁻¹).toMonoidHom) := by
    intro hP
    apply hτ
    rw [model3_center_map_eq γ hW, ← model3_sup_conj_map γ τ']
    exact model3_isPGroup_map γ hP
  rw [← model3_sup_conj_map γ τ' W, h τ' hnot, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hγ]

theorem model3_of_cover [Finite X] (γ : X →* Y) (hγ : Function.Surjective γ)
    (hodd : Odd (Nat.card γ.ker)) {q : ℕ} (hX : Model3Tilde X q) {V : Subgroup Y}
    (hV : ∃ R : Sylow 2 Y, (R : Subgroup Y) = V) : Model3Concl Y V q := by
  obtain ⟨W, hWV, hW⟩ := model3_exists_sylow_lift γ hγ hodd hV
  subst hWV
  exact ⟨model3A_map γ hW (hX.a W), model3B_map γ hγ hodd hW (hX.b W),
    model3C_map γ hγ hW (hX.c W)⟩

end Transfer

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
