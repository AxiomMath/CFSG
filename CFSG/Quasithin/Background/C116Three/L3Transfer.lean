module

public import CFSG.Quasithin.Background.C116Three.L3Defs
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

theorem l3t_relIndex_ne_zero (M W : Subgroup V) : M.relIndex W ≠ 0 := by
  intro h0
  have h := Subgroup.relIndex_mul_card (H := M) (K := W)
  rw [h0, zero_mul] at h
  have hpos : 0 < Nat.card ↥W := Nat.card_pos
  omega

theorem l3t_relIndex_mul_card {M W : Subgroup V} (hMW : M ≤ W) :
    M.relIndex W * Nat.card ↥M = Nat.card ↥W := by
  have h := Subgroup.relIndex_mul_card (H := M) (K := W)
  rwa [inf_eq_left.mpr hMW] at h

theorem l3t_card_le_mul {X M W Y : Subgroup V} (hXW : X ≤ W) (hY : X ⊓ M = Y) :
    Nat.card ↥X ≤ M.relIndex W * Nat.card ↥Y := by
  subst hY
  have h1 : M.relIndex X * Nat.card ↥(X ⊓ M) = Nat.card ↥X := by
    rw [inf_comm]
    exact Subgroup.relIndex_mul_card (H := M) (K := X)
  have h2 : M.relIndex X ≤ M.relIndex W :=
    Subgroup.relIndex_le_of_le_right hXW (l3t_relIndex_ne_zero M W)
  calc Nat.card ↥X = M.relIndex X * Nat.card ↥(X ⊓ M) := h1.symm
    _ ≤ M.relIndex W * Nat.card ↥(X ⊓ M) := Nat.mul_le_mul h2 le_rfl

theorem l3t_fixMod_inf {M W : Subgroup V} (hMW : M ≤ W) (B : Subgroup (MulAut V))
    (C : Subgroup V) : R3c23.fixMod B W C ⊓ M = R3c23.fixMod B M C := by
  ext w
  simp only [Subgroup.mem_inf, R3c23.mem_fixMod]
  exact ⟨fun hw => ⟨hw.2, hw.1.2⟩, fun hw => ⟨⟨hMW hw.1, hw.2⟩, hw.1⟩⟩

theorem bounds_mono {G : Subgroup (MulAut V)} {M W C : Subgroup V} (hMW : M ≤ W)
    (h : Bounds G M C) : Bounds G W C := by
  intro B hBG hBel
  obtain ⟨h1, h2⟩ := h B hBG hBel
  have hZ : Nat.card ↥(fixV B ⊓ W) ≤ M.relIndex W * Nat.card ↥(fixV B ⊓ M) :=
    l3t_card_le_mul inf_le_right (by rw [inf_assoc, inf_eq_right.mpr hMW])
  have hY : Nat.card ↥(R3c23.fixMod B W C) ≤
      M.relIndex W * Nat.card ↥(R3c23.fixMod B M C) :=
    l3t_card_le_mul (fun w hw => (R3c23.mem_fixMod.1 hw).1) (l3t_fixMod_inf hMW B C)
  have hW := l3t_relIndex_mul_card hMW
  constructor
  · calc Nat.card B * Nat.card ↥(fixV B ⊓ W)
        ≤ Nat.card B * (M.relIndex W * Nat.card ↥(fixV B ⊓ M)) := Nat.mul_le_mul le_rfl hZ
      _ = M.relIndex W * (Nat.card B * Nat.card ↥(fixV B ⊓ M)) := by ring
      _ ≤ M.relIndex W * Nat.card ↥M := Nat.mul_le_mul le_rfl h1
      _ = Nat.card ↥W := hW
  · calc Nat.card B ^ 2 * Nat.card ↥(fixV B ⊓ W) * Nat.card ↥(R3c23.fixMod B W C)
        ≤ Nat.card B ^ 2 * (M.relIndex W * Nat.card ↥(fixV B ⊓ M)) *
            (M.relIndex W * Nat.card ↥(R3c23.fixMod B M C)) :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl hZ) hY
      _ = M.relIndex W ^ 2 * (Nat.card B ^ 2 * Nat.card ↥(fixV B ⊓ M) *
            Nat.card ↥(R3c23.fixMod B M C)) := by ring
      _ ≤ M.relIndex W ^ 2 * Nat.card ↥M ^ 2 := Nat.mul_le_mul le_rfl h2
      _ = Nat.card ↥W ^ 2 := by rw [← hW]; ring

theorem tight_of_tight {G : Subgroup (MulAut V)} {M W C : Subgroup V} (hMW : M ≤ W)
    (h : Bounds G M C) {B : Subgroup (MulAut V)} (hBG : B ≤ G) (hBel : IsElemAbelian2 B)
    (ht : Nat.card B * Nat.card ↥(fixV B ⊓ W) = Nat.card W) :
    Nat.card B * Nat.card ↥(fixV B ⊓ M) = Nat.card M := by
  obtain ⟨h1, -⟩ := h B hBG hBel
  have hZ : Nat.card ↥(fixV B ⊓ W) ≤ M.relIndex W * Nat.card ↥(fixV B ⊓ M) :=
    l3t_card_le_mul inf_le_right (by rw [inf_assoc, inf_eq_right.mpr hMW])
  have hW := l3t_relIndex_mul_card hMW
  have hpos : 0 < M.relIndex W := Nat.pos_of_ne_zero (l3t_relIndex_ne_zero M W)
  have key : M.relIndex W * Nat.card ↥M ≤
      M.relIndex W * (Nat.card B * Nat.card ↥(fixV B ⊓ M)) := by
    calc M.relIndex W * Nat.card ↥M = Nat.card ↥W := hW
      _ = Nat.card B * Nat.card ↥(fixV B ⊓ W) := ht.symm
      _ ≤ Nat.card B * (M.relIndex W * Nat.card ↥(fixV B ⊓ M)) := Nat.mul_le_mul le_rfl hZ
      _ = M.relIndex W * (Nat.card B * Nat.card ↥(fixV B ⊓ M)) := by ring
  exact le_antisymm h1 (le_of_mul_le_mul_left key hpos)

theorem l3t_fixMod_conj (τ : MulAut V) (A : Subgroup (MulAut V)) (M C : Subgroup V) :
    R3c23.fixMod (B1.conjAut τ A) (M.map τ.toMonoidHom) (C.map τ.toMonoidHom) =
      (R3c23.fixMod A M C).map τ.toMonoidHom := by
  have hτ : Function.Injective τ.toMonoidHom := τ.injective
  ext w
  constructor
  · intro hw
    obtain ⟨hwM, hwC⟩ := R3c23.mem_fixMod.1 hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hwM
    refine Subgroup.mem_map.2 ⟨m, R3c23.mem_fixMod.2 ⟨hm, fun a ha => ?_⟩, rfl⟩
    have hb : τ * a * τ⁻¹ ∈ B1.conjAut τ A :=
      B1.mem_conjAut.2 (by simpa [mul_assoc] using ha)
    obtain ⟨c, hc, hc'⟩ := Subgroup.mem_map.1 (hwC _ hb)
    have key : τ.toMonoidHom (a m * m⁻¹) =
        (τ * a * τ⁻¹) (τ.toMonoidHom m) * (τ.toMonoidHom m)⁻¹ := by
      simp [MulAut.mul_apply, MulAut.inv_apply_self]
    have hc2 : c = a m * m⁻¹ := hτ (hc'.trans key.symm)
    rw [← hc2]
    exact hc
  · intro hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hw
    refine R3c23.mem_fixMod.2
      ⟨Subgroup.mem_map.2 ⟨m, (R3c23.mem_fixMod.1 hm).1, rfl⟩, fun b hb => ?_⟩
    have ha : τ⁻¹ * b * τ ∈ A := B1.mem_conjAut.1 hb
    have hm' : (τ⁻¹ * b * τ) m * m⁻¹ ∈ C := (R3c23.mem_fixMod.1 hm).2 _ ha
    have key : b (τ.toMonoidHom m) * (τ.toMonoidHom m)⁻¹ =
        τ.toMonoidHom ((τ⁻¹ * b * τ) m * m⁻¹) := by
      simp [MulAut.mul_apply, MulAut.apply_inv_self]
    rw [key]
    exact Subgroup.mem_map.2 ⟨_, hm', rfl⟩

theorem bounds_map (τ : MulAut V) {G : Subgroup (MulAut V)} {M C : Subgroup V}
    (h : Bounds G M C) :
    Bounds (G.map (MulAut.conj τ).toMonoidHom) (M.map τ.toMonoidHom) (C.map τ.toMonoidHom) := by
  intro B hBG hBel
  obtain ⟨A, rfl⟩ : ∃ A, B = B1.conjAut τ A :=
    ⟨B1.conjAut τ⁻¹ B, (B1.conjAut_conjAut_inv τ B).symm⟩
  have hAG : A ≤ G := by
    intro x hx
    have hx' : τ * x * τ⁻¹ ∈ B1.conjAut τ A :=
      B1.mem_conjAut.2 (by simpa [mul_assoc] using hx)
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 (hBG hx')
    have h3 : τ * g * τ⁻¹ = τ * x * τ⁻¹ := by
      rw [← MulAut.conj_apply]
      exact hgx
    rw [← mul_left_cancel (mul_right_cancel h3)]
    exact hg
  have hAel : IsElemAbelian2 A := by
    have h2 := B1.isElemAbelian2_conjAut (g := τ⁻¹) hBel
    rwa [B1.conjAut_inv_conjAut] at h2
  obtain ⟨h1, h2⟩ := h A hAG hAel
  have hτ : Function.Injective τ.toMonoidHom := τ.injective
  have hfix : fixV (B1.conjAut τ A) ⊓ M.map τ.toMonoidHom =
      (fixV A ⊓ M).map τ.toMonoidHom := by
    rw [B1.fixV_conjAut, Subgroup.map_inf_eq _ _ _ hτ]
  simp only [B1.card_conjAut, hfix, l3t_fixMod_conj, Subgroup.card_map_of_injective hτ]
  exact ⟨h1, h2⟩

end CFSG.Quasithin.C116Three
