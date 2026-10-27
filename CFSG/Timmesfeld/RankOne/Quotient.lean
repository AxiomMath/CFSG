module

public import CFSG.Timmesfeld.RankOne.Points

public section

namespace CFSG.Timmesfeld

open RankOne

variable {X Y : Type*} [Group X] [Group Y]

namespace RankOne

theorem map_map_conj (f : X →* Y) (H : Subgroup X) (g : X) :
    (H.map (MulAut.conj g).toMonoidHom).map f =
      (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end RankOne

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem eq_one_of_mem_ker {f : X →* Y} (hker : f.ker ≤ Subgroup.normalizer (B : Set X))
    {a : X} (ha : a ∈ A) (hfa : f a = 1) : a = 1 :=
  h.eq_one_of_map_conj_eq ha (map_conj_eq_self_iff.2 (hker hfa))

theorem card_map_eq {f : X →* Y} (hker : f.ker ≤ Subgroup.normalizer (B : Set X)) :
    Nat.card (A.map f) = Nat.card A := by
  refine (Nat.card_congr (Equiv.ofBijective (fun a : A => (⟨f a, a, a.2, rfl⟩ : A.map f))
    ⟨fun a a' haa => ?_, ?_⟩)).symm
  · have h1 : f ((a : X)⁻¹ * a') = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact congrArg Subtype.val haa
    have := h.eq_one_of_mem_ker hker (A.mul_mem (A.inv_mem a.2) a'.2) h1
    rw [inv_mul_eq_one] at this
    exact Subtype.ext this
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem map_ne_map {f : X →* Y} (hker : f.ker ≤ Subgroup.normalizer (B : Set X)) :
    A.map f ≠ B.map f := by
  intro heq
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  have hfa : f a ∈ B.map f := heq ▸ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hfb⟩ := hfa
  have hk : b⁻¹ * a ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, inv_mul_cancel]
  have hbN : b ∈ Subgroup.normalizer (B : Set X) :=
    map_conj_eq_self_iff.1 (map_conj_of_mem hb)
  have haN : a ∈ Subgroup.normalizer (B : Set X) := by
    have := Subgroup.mul_mem _ hbN (hker hk)
    rwa [mul_inv_cancel_left] at this
  exact ha1 (h.eq_one_of_map_conj_eq ha (map_conj_eq_self_iff.2 haN))

theorem map {f : X →* Y} (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X)) :
    IsElemAbRankOne (A.map f) (B.map f) := by
  have hkA : f.ker ≤ Subgroup.normalizer (A : Set X) := hker.trans inf_le_left
  have hkB : f.ker ≤ Subgroup.normalizer (B : Set X) := hker.trans inf_le_right
  refine
    { gen := by rw [← Subgroup.map_sup, h.gen, Subgroup.map_top_of_surjective f hf]
      ne := h.map_ne_map hkB
      comm := ?_
      sq := ?_
      moufang := ?_
      moufang' := ?_ }
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    exact (h.comm a ha a' ha').map f
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, h.sq a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ ha1
    have ha1' : a ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
    obtain ⟨b, hb, hb1, hab⟩ := h.moufang a ha ha1'
    refine ⟨f b, ⟨b, hb, rfl⟩, fun h1 => hb1 (h.symm.eq_one_of_mem_ker hkA hb h1), ?_⟩
    rw [← map_map_conj, ← map_map_conj, hab]
  · rintro _ ⟨b, hb, rfl⟩ hb1
    have hb1' : b ≠ 1 := fun h1 => hb1 (by rw [h1, map_one])
    obtain ⟨a, ha, ha1, hab⟩ := h.moufang' b hb hb1'
    refine ⟨f a, ⟨a, ha, rfl⟩, fun h1 => ha1 (h.eq_one_of_mem_ker hkB ha h1), ?_⟩
    rw [← map_map_conj, ← map_map_conj, hab]

theorem map_conj_eq_of_map_eq {f : X →* Y}
    (hker : f.ker ≤ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X))
    {x y : X} (heq : (A.map (MulAut.conj x).toMonoidHom).map f =
      (A.map (MulAut.conj y).toMonoidHom).map f) :
    A.map (MulAut.conj x).toMonoidHom = A.map (MulAut.conj y).toMonoidHom := by
  by_contra hne
  have hne' : A.map (MulAut.conj (x⁻¹ * y)).toMonoidHom ≠ A := by
    intro h1
    apply hne
    rw [map_conj_mul, map_conj_eq_iff, inv_inv] at h1
    exact h1.symm
  have heq' : A.map f = (A.map (MulAut.conj (x⁻¹ * y)).toMonoidHom).map f := by
    have := congrArg (fun H => H.map (MulAut.conj (f x⁻¹)).toMonoidHom) heq
    rwa [← map_map_conj, ← map_map_conj, ← map_conj_mul, ← map_conj_mul, inv_mul_cancel,
      map_conj_one] at this
  obtain ⟨a, ha, haeq⟩ := h.exists_eq_of_map_conj_ne hne'
  rw [haeq, map_map_conj] at heq'
  have h2 := map_conj_eq_iff.1 heq'.symm
  rw [map_conj_of_mem (Subgroup.inv_mem _ (Subgroup.mem_map_of_mem f ha))] at h2
  exact h.map_ne_map (hker.trans inf_le_right) h2.symm

end IsElemAbRankOne

namespace IsElemAbRankOne

variable {X : Type*} [Group X] {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

@[expose] def pointKernel (A : Subgroup X) : Subgroup X :=
  (MulAction.toPermHom X (Point A)).ker

omit h in
theorem mem_pointKernel {A : Subgroup X} {k : X} :
    k ∈ pointKernel A ↔ ∀ C : Point A, k • C = C := by
  simp [pointKernel, MonoidHom.mem_ker, Equiv.Perm.ext_iff]

omit h in
instance (A : Subgroup X) : (pointKernel A).Normal := by
  unfold pointKernel
  infer_instance

theorem pointKernel_le :
    pointKernel A ≤ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) := by
  intro k hk
  rw [mem_pointKernel] at hk
  refine ⟨?_, ?_⟩
  · rw [← Point.stabilizer_base]
    exact hk _
  · rw [← h.stabilizer_pt_one]
    exact hk _

theorem faithfulSMul_quotient :
    FaithfulSMul (X ⧸ pointKernel A) (Point (A.map (QuotientGroup.mk' (pointKernel A)))) := by
  set f := QuotientGroup.mk' (pointKernel A)
  have hker : f.ker ≤ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) := by
    rw [QuotientGroup.ker_mk']
    exact h.pointKernel_le
  refine ⟨fun {y₁ y₂} hy => ?_⟩
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk'_surjective (pointKernel A) y₁
  obtain ⟨x₂, rfl⟩ := QuotientGroup.mk'_surjective (pointKernel A) y₂
  have hz : x₂⁻¹ * x₁ ∈ pointKernel A := by
    rw [mem_pointKernel]
    intro C
    obtain ⟨x, rfl⟩ := Point.exists_smul_base C
    have hv := congrArg Point.val
      (hy ⟨(A.map (MulAut.conj x).toMonoidHom).map f, ⟨f x, map_map_conj f A x⟩⟩)
    simp only [Point.val_smul] at hv
    rw [← map_map_conj, ← map_map_conj, ← map_conj_mul, ← map_conj_mul] at hv
    have h1 := h.map_conj_eq_of_map_eq hker hv
    apply Point.ext
    rw [Point.val_smul, Point.val_smul_base, ← map_conj_mul, mul_assoc, map_conj_mul, h1,
      ← map_conj_mul, inv_mul_cancel_left]
  have h1 : f (x₂⁻¹ * x₁) = 1 := (QuotientGroup.eq_one_iff _).2 hz
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

end IsElemAbRankOne

end CFSG.Timmesfeld
