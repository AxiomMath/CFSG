module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem transvection_mem_slOn {N : ℕ} {S : Set (Fin N)} {a b : Fin N} (hab : a ≠ b) (c : F2)
    (ha : a ∈ S) (hb : b ∈ S) : SpecialLinearGroup.transvection hab c ∈ slOn N S :=
  Subgroup.subset_closure ⟨a, b, hab, c, ha, hb, rfl⟩

theorem weylRep_eq_slPerm (n : ℕ) (k : Fin n) :
    weylRep n F2 k = slPerm gf2_two (Equiv.swap k.castSucc k.succ) :=
  (slPerm_swap_castSucc_succ gf2_two k).symm

theorem slOn_mono {N : ℕ} {S S' : Set (Fin N)} (h : S ⊆ S') : slOn N S ≤ slOn N S' :=
  Subgroup.closure_mono fun _ ⟨a, b, hab, c, ha, hb, ht⟩ => ⟨a, b, hab, c, h ha, h hb, ht⟩

theorem slOn_univ (N : ℕ) : slOn N Set.univ = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin N) (K := F2)]
  rw [Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def]
  exact transvection_mem_slOn t.hij t.c (Set.mem_univ _) (Set.mem_univ _)

private theorem mem_of_transvection_mul {G : Type*} [Group G] {H : Subgroup G} {A B C : G}
    (key : A * B = B * A * C) (hA : A ∈ H) (hB : B ∈ H) : C ∈ H := by
  have hC : C = (B * A)⁻¹ * (A * B) := by rw [key]; group
  rw [hC]
  exact H.mul_mem (H.inv_mem (H.mul_mem hB hA)) (H.mul_mem hA hB)

theorem slOn_sup_of_inter {N : ℕ} {S₁ S₂ : Set (Fin N)} (h : (S₁ ∩ S₂).Nonempty) :
    slOn N S₁ ⊔ slOn N S₂ = slOn N (S₁ ∪ S₂) := by
  refine le_antisymm
    (sup_le (slOn_mono Set.subset_union_left) (slOn_mono Set.subset_union_right)) ?_
  obtain ⟨d, hd⟩ := h
  rw [slOn, Subgroup.closure_le]
  rintro t ⟨a, b, hab, c, ha, hb, rfl⟩
  have ha' : a ∈ S₁ ∨ a ∈ S₂ := by simpa only [Set.mem_union] using ha
  have hb' : b ∈ S₁ ∨ b ∈ S₂ := by simpa only [Set.mem_union] using hb
  by_cases ha1 : a ∈ S₁
  · by_cases hb1 : b ∈ S₁
    · exact Subgroup.mem_sup_left (transvection_mem_slOn hab c ha1 hb1)
    · have hb2 : b ∈ S₂ := hb'.resolve_left hb1
      by_cases ha2 : a ∈ S₂
      · exact Subgroup.mem_sup_right (transvection_mem_slOn hab c ha2 hb2)
      · have had : a ≠ d := by rintro rfl; exact ha2 hd.2
        have hdb : d ≠ b := by rintro rfl; exact hb1 hd.1
        have hA : SpecialLinearGroup.transvection had c ∈ slOn N S₁ ⊔ slOn N S₂ :=
          Subgroup.mem_sup_left (transvection_mem_slOn had c ha1 hd.1)
        have hB : SpecialLinearGroup.transvection hdb 1 ∈ slOn N S₁ ⊔ slOn N S₂ :=
          Subgroup.mem_sup_right (transvection_mem_slOn hdb 1 hd.2 hb2)
        have key :=
          SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul had hdb hab c (1 : F2)
        rw [mul_one] at key
        exact mem_of_transvection_mul key hA hB
  · have ha2 : a ∈ S₂ := ha'.resolve_left ha1
    by_cases hb2 : b ∈ S₂
    · exact Subgroup.mem_sup_right (transvection_mem_slOn hab c ha2 hb2)
    · have hb1 : b ∈ S₁ := hb'.resolve_right hb2
      have had : a ≠ d := by rintro rfl; exact ha1 hd.1
      have hdb : d ≠ b := by rintro rfl; exact hb2 hd.2
      have hA : SpecialLinearGroup.transvection had c ∈ slOn N S₁ ⊔ slOn N S₂ :=
        Subgroup.mem_sup_right (transvection_mem_slOn had c ha2 hd.2)
      have hB : SpecialLinearGroup.transvection hdb 1 ∈ slOn N S₁ ⊔ slOn N S₂ :=
        Subgroup.mem_sup_left (transvection_mem_slOn hdb 1 hd.1 hb1)
      have key :=
        SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul had hdb hab c (1 : F2)
      rw [mul_one] at key
      exact mem_of_transvection_mul key hA hB

private theorem conj_slPerm_transvection {N : ℕ} (π : Equiv.Perm (Fin N)) {a b : Fin N}
    (hab : a ≠ b) (c : F2) :
    (MulAut.conj (slPerm gf2_two π)).toMonoidHom (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection (π.injective.ne hab) c := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_transvection_of_coe_eq_signedPerm (coe_slPerm gf2_two π) (fun s => by simp) hab c]
  simp

theorem slOn_map_conj_slPerm {N : ℕ} (π : Equiv.Perm (Fin N)) (S : Set (Fin N)) :
    (slOn N S).map (MulAut.conj (slPerm gf2_two π)).toMonoidHom = slOn N (π '' S) := by
  rw [slOn, MonoidHom.map_closure, slOn]
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro _ ⟨t, ht, rfl⟩
    rcases ht with ⟨a, b, hab, c, ha, hb, rfl⟩
    rw [conj_slPerm_transvection π hab c]
    exact ⟨π a, π b, π.injective.ne hab, c, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩
  · rw [Subgroup.closure_le]
    rintro t ⟨a', b', ha'b', c, ha', hb', rfl⟩
    rcases ha' with ⟨a, ha, rfl⟩
    rcases hb' with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => ha'b' (by rw [h])
    refine Subgroup.subset_closure ⟨SpecialLinearGroup.transvection hab c, ?_, ?_⟩
    · exact ⟨a, b, hab, c, ha, hb, rfl⟩
    · rw [conj_slPerm_transvection π hab c]

theorem commute_slPerm_slOn {N : ℕ} {π : Equiv.Perm (Fin N)} {S : Set (Fin N)}
    (h : ∀ i ∈ S, π i = i) {g : SpecialLinearGroup (Fin N) F2} (hg : g ∈ slOn N S) :
    slPerm gf2_two π * g = g * slPerm gf2_two π := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
      rcases hs with ⟨a, b, hab, c, ha, hb, rfl⟩
      rw [← mul_inv_eq_iff_eq_mul]
      exact slPerm_conj_transvection_of_fixed gf2_two (h a ha) (h b hb) hab c
  | one => rw [mul_one, one_mul]
  | mul x y _ _ ihx ihy =>
      calc slPerm gf2_two π * (x * y) = (slPerm gf2_two π * x) * y := by rw [mul_assoc]
        _ = (x * slPerm gf2_two π) * y := by rw [ihx]
        _ = x * (slPerm gf2_two π * y) := by rw [mul_assoc]
        _ = x * (y * slPerm gf2_two π) := by rw [ihy]
        _ = (x * y) * slPerm gf2_two π := by rw [mul_assoc]
  | inv x _ ihx =>
      rw [mul_inv_eq_iff_eq_mul]
      calc slPerm gf2_two π = x⁻¹ * (x * slPerm gf2_two π) := by group
        _ = x⁻¹ * (slPerm gf2_two π * x) := by rw [ihx]
        _ = (x⁻¹ * slPerm gf2_two π) * x := by rw [mul_assoc]

end CFSG.StandardType.GGHalf

end
