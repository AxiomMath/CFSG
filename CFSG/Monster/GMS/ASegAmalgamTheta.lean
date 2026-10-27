module

public import CFSG.Monster.GMS.ASegAmalgamKey
public import CFSG.Monster.GMS.ASegAmalgamFun

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly CFSG.Monster.GMS.S4Family

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Cent

variable {G : Type*} [Group G] {a y z : G}

theorem Comm3.y_mem_cent_a (h : Comm3 a y z) : y ∈ C[a] :=
  Subgroup.mem_centralizer_singleton_iff.2 h.ya

theorem Comm3.z_mem_cent_a (h : Comm3 a y z) : z ∈ C[a] :=
  Subgroup.mem_centralizer_singleton_iff.2 h.za

theorem Comm3.a_mem_cent_z (h : Comm3 a y z) : a ∈ C[z] :=
  Subgroup.mem_centralizer_singleton_iff.2 h.az

theorem Comm3.y_mem_cent_z (h : Comm3 a y z) : y ∈ C[z] :=
  Subgroup.mem_centralizer_singleton_iff.2 h.yz

end Cent

section Data

variable {G G' : Type*} [Group G] [Group G']

structure AmalgamData (a y z : G) (a' y' z' : G') (A Z : G → G') : Prop where
  alphaZeta : AlphaZeta a y z a' y' z' A Z
  comm3 : Comm3 a y z
  comm3' : Comm3 a' y' z'
  dec : ∀ g ∈ Xt0 a y, ∃ k ∈ C[a] ⊓ C[y], ∃ w ∈ Xt0 a y ⊓ C[z], g = k * w
  dec' : ∀ g ∈ Xt0 a' y', ∃ k ∈ C[a'] ⊓ C[y'], ∃ w ∈ Xt0 a' y' ⊓ C[z'], g = k * w
  key : ∀ w ∈ Xt0 a y ⊓ C[z], ∀ k ∈ C[a] ⊓ C[y], A (w * k * w⁻¹) = Z w * A k * (Z w)⁻¹

end Data

section Theta

variable {G G' : Type} [Group G] [Group G'] {a y z : G} {a' y' z' : G'} {A Z : G → G'}

open Classical in
@[expose] noncomputable def asegTheta (A Z : G → G') (a y z : G) (g : G) : G' :=
  if h : ∃ k ∈ C[a] ⊓ C[y], ∃ w ∈ Xt0 a y ⊓ C[z], g = k * w then
    A h.choose * Z h.choose_spec.2.choose
  else 1

theorem AlphaZeta.A_mul_Z_eq (P : AlphaZeta a y z a' y' z' A Z) {k k' w w' : G}
    (hk : k ∈ C[a] ⊓ C[y]) (hk' : k' ∈ C[a] ⊓ C[y]) (hw : w ∈ Xt0 a y ⊓ C[z])
    (hw' : w' ∈ Xt0 a y ⊓ C[z]) (he : k * w = k' * w') : A k * Z w = A k' * Z w' := by
  have hu : k'⁻¹ * k = w' * w⁻¹ := by
    calc k'⁻¹ * k = k'⁻¹ * (k * w) * w⁻¹ := by group
      _ = k'⁻¹ * (k' * w') * w⁻¹ := by rw [he]
      _ = w' * w⁻¹ := by group
  have huA : k'⁻¹ * k ∈ C[a] := (C[a]).mul_mem ((C[a]).inv_mem hk'.1) hk.1
  have huZ : k'⁻¹ * k ∈ C[z] := by
    rw [hu]
    exact (C[z]).mul_mem hw'.2 ((C[z]).inv_mem hw.2)
  have h1 : Z (k'⁻¹ * k) = A (k'⁻¹ * k) := P.Z_eq_A _ ⟨huA, huZ⟩
  have h2 : Z (k'⁻¹ * k) = Z w' * (Z w)⁻¹ := by
    rw [hu, P.hZ.map_mul w' hw'.2 w⁻¹ ((C[z]).inv_mem hw.2), iso_map_inv P.hZ hw.2]
  have h3 : A (k'⁻¹ * k) = (A k')⁻¹ * A k := by
    rw [P.hA.map_mul k'⁻¹ ((C[a]).inv_mem hk'.1) k hk.1, iso_map_inv P.hA hk'.1]
  rw [h2, h3] at h1
  calc A k * Z w = A k' * ((A k')⁻¹ * A k) * Z w := by group
    _ = A k' * (Z w' * (Z w)⁻¹) * Z w := by rw [h1]
    _ = A k' * Z w' := by group

namespace AmalgamData

variable (Q : AmalgamData a y z a' y' z' A Z)
include Q

theorem theta_mul {k w : G} (hk : k ∈ C[a] ⊓ C[y]) (hw : w ∈ Xt0 a y ⊓ C[z]) :
    asegTheta A Z a y z (k * w) = A k * Z w := by
  have h : ∃ k' ∈ C[a] ⊓ C[y], ∃ w' ∈ Xt0 a y ⊓ C[z], k * w = k' * w' := ⟨k, hk, w, hw, rfl⟩
  rw [asegTheta, dite_eq_left h]
  exact Q.alphaZeta.A_mul_Z_eq h.choose_spec.1 hk h.choose_spec.2.choose_spec.1 hw
    h.choose_spec.2.choose_spec.2.symm

theorem isIsoOn_K : IsIsoOn A (C[a] ⊓ C[y]) (C[a'] ⊓ C[y']) := by
  have := isIsoOn_inf_centralizer Q.alphaZeta.hA Q.comm3.y_mem_cent_a
  rwa [Q.alphaZeta.A_y] at this

theorem Z_mem_W [Finite G] [Finite G'] {w : G} (hw : w ∈ Xt0 a y ⊓ C[z]) :
    Z w ∈ Xt0 a' y' ⊓ C[z'] := by
  refine ⟨?_, Q.alphaZeta.hZ.map_mem w hw.2⟩
  have := (mem_Xt0_iff_of_isIsoOn Q.alphaZeta.hZ Q.comm3.a_mem_cent_z Q.comm3.y_mem_cent_z
    hw.2).2 hw.1
  rwa [Q.alphaZeta.Z_a, Q.alphaZeta.Z_y] at this

theorem mem_Xt0_of_Z [Finite G] [Finite G'] {w : G} (hw : w ∈ C[z]) (h : Z w ∈ Xt0 a' y') :
    w ∈ Xt0 a y := by
  have := mem_Xt0_iff_of_isIsoOn Q.alphaZeta.hZ Q.comm3.a_mem_cent_z Q.comm3.y_mem_cent_z hw
  rw [Q.alphaZeta.Z_a, Q.alphaZeta.Z_y] at this
  exact this.1 h

theorem theta_mem [Finite G] [Finite G'] {g : G} (hg : g ∈ Xt0 a y) :
    asegTheta A Z a y z g ∈ Xt0 a' y' := by
  obtain ⟨k, hk, w, hw, rfl⟩ := Q.dec g hg
  rw [Q.theta_mul hk hw]
  exact (Xt0 a' y').mul_mem (K_le_Xt0 a' y' (Q.isIsoOn_K.map_mem k hk)) (Q.Z_mem_W hw).1

theorem theta_map_mul {g₁ g₂ : G} (h₁ : g₁ ∈ Xt0 a y) (h₂ : g₂ ∈ Xt0 a y) :
    asegTheta A Z a y z (g₁ * g₂) = asegTheta A Z a y z g₁ * asegTheta A Z a y z g₂ := by
  obtain ⟨k₁, hk₁, w₁, hw₁, rfl⟩ := Q.dec g₁ h₁
  obtain ⟨k₂, hk₂, w₂, hw₂, rfl⟩ := Q.dec g₂ h₂
  have hk₂' : w₁ * k₂ * w₁⁻¹ ∈ C[a] ⊓ C[y] := (Xt0.mem_K_iff hw₁.1 k₂).1 hk₂
  have e : k₁ * w₁ * (k₂ * w₂) = (k₁ * (w₁ * k₂ * w₁⁻¹)) * (w₁ * w₂) := by group
  rw [e, Q.theta_mul ((C[a] ⊓ C[y]).mul_mem hk₁ hk₂') ((Xt0 a y ⊓ C[z]).mul_mem hw₁ hw₂),
    Q.theta_mul hk₁ hw₁, Q.theta_mul hk₂ hw₂, Q.alphaZeta.hA.map_mul k₁ hk₁.1 _ hk₂'.1,
    Q.key w₁ hw₁ k₂ hk₂, Q.alphaZeta.hZ.map_mul w₁ hw₁.2 w₂ hw₂.2]
  group

theorem theta_injOn {g₁ g₂ : G} (h₁ : g₁ ∈ Xt0 a y) (h₂ : g₂ ∈ Xt0 a y)
    (he : asegTheta A Z a y z g₁ = asegTheta A Z a y z g₂) : g₁ = g₂ := by
  obtain ⟨k₁, hk₁, w₁, hw₁, rfl⟩ := Q.dec g₁ h₁
  obtain ⟨k₂, hk₂, w₂, hw₂, rfl⟩ := Q.dec g₂ h₂
  rw [Q.theta_mul hk₁ hw₁, Q.theta_mul hk₂ hw₂] at he
  have hA := Q.alphaZeta.hA
  have hZ := Q.alphaZeta.hZ
  have huA : k₂⁻¹ * k₁ ∈ C[a] := (C[a]).mul_mem ((C[a]).inv_mem hk₂.1) hk₁.1
  have hwu : w₂ * w₁⁻¹ ∈ C[z] := (C[z]).mul_mem hw₂.2 ((C[z]).inv_mem hw₁.2)
  have e1 : A (k₂⁻¹ * k₁) = Z (w₂ * w₁⁻¹) := by
    rw [hA.map_mul k₂⁻¹ ((C[a]).inv_mem hk₂.1) k₁ hk₁.1, iso_map_inv hA hk₂.1,
      hZ.map_mul w₂ hw₂.2 w₁⁻¹ ((C[z]).inv_mem hw₁.2), iso_map_inv hZ hw₁.2]
    calc (A k₂)⁻¹ * A k₁ = (A k₂)⁻¹ * (A k₁ * Z w₁) * (Z w₁)⁻¹ := by group
      _ = (A k₂)⁻¹ * (A k₂ * Z w₂) * (Z w₁)⁻¹ := by rw [he]
      _ = Z w₂ * (Z w₁)⁻¹ := by group
  have hz1 : A (k₂⁻¹ * k₁) ∈ C[A z] := by
    rw [e1, Q.alphaZeta.A_z]
    exact hZ.map_mem _ hwu
  have hz2 : k₂⁻¹ * k₁ ∈ C[z] :=
    (iso_mem_centralizer_iff hA huA Q.comm3.z_mem_cent_a).1 hz1
  have e2 : k₂⁻¹ * k₁ = w₂ * w₁⁻¹ :=
    hZ.injOn hz2 hwu ((Q.alphaZeta.Z_eq_A _ ⟨huA, hz2⟩).trans e1)
  calc k₁ * w₁ = k₂ * (k₂⁻¹ * k₁) * w₁ := by group
    _ = k₂ * (w₂ * w₁⁻¹) * w₁ := by rw [e2]
    _ = k₂ * w₂ := by group

theorem theta_surjOn [Finite G] [Finite G'] {x : G'} (hx : x ∈ Xt0 a' y') :
    ∃ g ∈ Xt0 a y, asegTheta A Z a y z g = x := by
  obtain ⟨k', hk', w', hw', rfl⟩ := Q.dec' x hx
  obtain ⟨k, hk, rfl⟩ := Q.alphaZeta.hA.surjOn k' hk'.1
  obtain ⟨w, hw, rfl⟩ := Q.alphaZeta.hZ.surjOn w' hw'.2
  have hkK : k ∈ C[a] ⊓ C[y] := by
    refine ⟨hk, ?_⟩
    have := (iso_mem_centralizer_iff Q.alphaZeta.hA hk Q.comm3.y_mem_cent_a).1
    rw [Q.alphaZeta.A_y] at this
    exact this hk'.2
  have hwW : w ∈ Xt0 a y ⊓ C[z] := ⟨Q.mem_Xt0_of_Z hw hw'.1, hw⟩
  exact ⟨k * w, (Xt0 a y).mul_mem (K_le_Xt0 a y hkK) hwW.1, Q.theta_mul hkK hwW⟩

theorem isIsoOn_theta [Finite G] [Finite G'] :
    IsIsoOn (asegTheta A Z a y z) (Xt0 a y) (Xt0 a' y') where
  map_mem _ hg := Q.theta_mem hg
  map_mul _ hx _ hy := Q.theta_map_mul hx hy
  injOn _ hx _ hy h := Q.theta_injOn hx hy h
  surjOn _ hx := Q.theta_surjOn hx

end AmalgamData

end Theta

end CFSG.Monster.GMS
