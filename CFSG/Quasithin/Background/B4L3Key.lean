module

public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem vec_add_self (x : L3.Vec) : x + x = 0 := by
  funext i
  have : ∀ z : ZMod 2, z + z = 0 := by decide
  exact this _

theorem vec_neg_eq (x : L3.Vec) : -x = x := by
  funext i
  have : ∀ z : ZMod 2, -z = z := by decide
  exact this _

@[expose] def SubOf (S : Finset L3.Vec) (h0 : (0 : L3.Vec) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) : Subgroup (Multiplicative L3.Vec) where
  carrier := {x | Multiplicative.toAdd x ∈ S}
  one_mem' := h0
  mul_mem' := fun {x y} hx hy => hadd _ hx _ hy
  inv_mem' := fun {x} hx => by
    show Multiplicative.toAdd x⁻¹ ∈ S
    rw [toAdd_inv, vec_neg_eq]
    exact hx

theorem mem_SubOf {S : Finset L3.Vec} {h0 : (0 : L3.Vec) ∈ S}
    {hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S} {x : Multiplicative L3.Vec} :
    x ∈ SubOf S h0 hadd ↔ Multiplicative.toAdd x ∈ S := Iff.rfl

theorem card_SubOf (S : Finset L3.Vec) (h0 : (0 : L3.Vec) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) : Nat.card (SubOf S h0 hadd) = S.card := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ⟨fun x => ⟨Multiplicative.toAdd x.1, x.2⟩,
    fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩, fun x => rfl, fun v => rfl⟩

theorem pair_zero_mem (c : L3.Vec) : (0 : L3.Vec) ∈ ({0, c} : Finset L3.Vec) := by simp

theorem pair_add_mem (c : L3.Vec) : ∀ x ∈ ({0, c} : Finset L3.Vec), ∀ y ∈ ({0, c} : Finset L3.Vec),
    x + y ∈ ({0, c} : Finset L3.Vec) := by
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; exact vec_add_self _

@[expose] def Zc (c : L3.Vec) : Subgroup (Multiplicative L3.Vec) :=
  SubOf {0, c} (pair_zero_mem c) (pair_add_mem c)

theorem card_Zc {c : L3.Vec} (hc : c ≠ 0) : Nat.card (Zc c) = 2 := by
  unfold Zc
  rw [card_SubOf]
  exact Finset.card_pair (Ne.symm hc)

namespace L3Data

variable {G : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data G U Z)

@[expose] def pre (S : Subgroup (Multiplicative L3.Vec)) : Subgroup V :=
  (S.comap D.β).map U.subtype

theorem mem_pre {S : Subgroup (Multiplicative L3.Vec)} {x : V} :
    x ∈ D.pre S ↔ ∃ hx : x ∈ U, D.β ⟨x, hx⟩ ∈ S := by
  unfold pre
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pre_le (S : Subgroup (Multiplicative L3.Vec)) : D.pre S ≤ U := fun _ hx =>
  (D.mem_pre.1 hx).1

theorem Z_le_pre (S : Subgroup (Multiplicative L3.Vec)) : Z ≤ D.pre S := by
  intro z hz
  rw [D.mem_pre]
  refine ⟨D.Z_le hz, ?_⟩
  rw [(D.ker_β ⟨z, D.Z_le hz⟩).2 hz]
  exact S.one_mem

include D in
theorem card_pre (S : Subgroup (Multiplicative L3.Vec)) :
    Nat.card (D.pre S) = Nat.card Z * Nat.card S := by
  unfold pre
  rw [Subgroup.card_map_of_injective U.subtype_injective]
  have h := B1More.card_map_mul_card_inf_ker (S.comap D.β) D.β
  have h1 : (S.comap D.β).map D.β = S := Subgroup.map_comap_eq_self_of_surjective D.β_surj S
  have h2 : S.comap D.β ⊓ D.β.ker = D.β.ker := by
    rw [inf_eq_right]
    intro u hu
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hu]
    exact S.one_mem
  rw [h1, h2, D.card_ker_β] at h
  rw [← h]
  ring

include D in
theorem pre_injective {S S' : Subgroup (Multiplicative L3.Vec)} (h : D.pre S = D.pre S') :
    S = S' := by
  ext x
  obtain ⟨u, rfl⟩ := D.β_surj x
  have h1 : (u : V) ∈ D.pre S ↔ (u : V) ∈ D.pre S' := by rw [h]
  rw [D.mem_pre, D.mem_pre] at h1
  simpa using h1

theorem β_comm (δ : L3.Γ) (u : ↥U) (hmem : D.rho δ (u : V) ∈ U)
    (hx : D.rho δ (u : V) * (u : V)⁻¹ ∈ U) :
    D.β ⟨D.rho δ (u : V) * (u : V)⁻¹, hx⟩ = Multiplicative.ofAdd
      (L3.act δ (Multiplicative.toAdd (D.β u)) - Multiplicative.toAdd (D.β u)) := by
  have h1 : (⟨D.rho δ (u : V) * (u : V)⁻¹, hx⟩ : ↥U) = ⟨D.rho δ (u : V), hmem⟩ * u⁻¹ := rfl
  rw [h1, map_mul, map_inv, D.β_rho δ (u : V) u.2 hmem]
  rw [ofAdd_sub, div_eq_mul_inv]
  rfl

end L3Data

end CFSG.Quasithin
