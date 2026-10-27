module

public import CFSG.Quasithin.Background.F7TwoInvNonempty

public section

namespace CFSG.Quasithin.F7Two

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ} {a : Γ}

theorem invGen_of_commute [Finite Γ] (hsimple : IsSimpleGroup ↥L)
    (hnonab : ∃ x y : ↥L, x * y ≠ y * x) (ha2 : a * a = 1)
    (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) (hac : ∃ x ∈ L, a * x ≠ x * a)
    (hcomm : ∀ x ∈ L, IsPGroup 2 ↥(Subgroup.zpowers (a * x * a⁻¹ * x⁻¹)) →
      (a * x * a⁻¹ * x⁻¹) ^ 2 = 1) : InvGen L a := by
  have hne := invXi_nonempty hsimple hnonab ha2 haL hac
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  set K : Subgroup Γ := Subgroup.closure (invXi L a) with hK
  have hKL : K ≤ L := closure_invXi_le
  refine le_antisymm hKL ?_
  by_contra hLK
  obtain ⟨g, hgL, hgK⟩ := IsConcreteLE.not_le_iff_exists.mp hLK
  have hcommute : ∀ k ∈ K, ∀ l ∈ L, l ∉ K →
      (k * a * k⁻¹) * (l * a * l⁻¹) = (l * a * l⁻¹) * (k * a * k⁻¹) := by
    intro k hk l hl hlK
    have hmL : k⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hKL hk)) hl
    have hmK : k⁻¹ * l ∉ K := fun h => hlK (by simpa using K.mul_mem hk h)
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers (a * (k⁻¹ * l) * a⁻¹ * (k⁻¹ * l)⁻¹)) := by
      by_contra hn
      exact hmK (Subgroup.subset_closure ⟨hmL, hn⟩)
    have hsq := hcomm _ hmL h2
    have hbb : (k⁻¹ * l * a * (k⁻¹ * l)⁻¹) * (k⁻¹ * l * a * (k⁻¹ * l)⁻¹) = 1 := by
      calc _ = (k⁻¹ * l) * (a * a) * (k⁻¹ * l)⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have hexp : a * (k⁻¹ * l) * a⁻¹ * (k⁻¹ * l)⁻¹ = a * (k⁻¹ * l * a * (k⁻¹ * l)⁻¹) := by
      rw [hai]
      group
    rw [hexp, pow_two] at hsq
    set b : Γ := k⁻¹ * l * a * (k⁻¹ * l)⁻¹ with hb
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have h3 : a * b * a = b := by
      have := mul_eq_one_iff_eq_inv.mp (show a * b * a * b = 1 by simpa [mul_assoc] using hsq)
      rwa [hbi] at this
    have h4 : a * b = b * a := by
      calc a * b = a * b * a * a := by rw [mul_assoc (a * b), ha2, mul_one]
        _ = b * a := by rw [h3]
    calc (k * a * k⁻¹) * (l * a * l⁻¹) = k * (a * b) * k⁻¹ := by rw [hb]; group
      _ = k * (b * a) * k⁻¹ := by rw [h4]
      _ = (l * a * l⁻¹) * (k * a * k⁻¹) := by rw [hb]; group
  set D₁ : Set Γ := {z | ∃ k ∈ K, z = k * a * k⁻¹} with hD₁
  set D : Set Γ := {z | ∃ l ∈ L, z = l * a * l⁻¹} with hD
  set N₁ : Subgroup Γ := Subgroup.closure D₁ with hN₁
  set M : Subgroup Γ := Subgroup.closure D with hM
  have haD₁ : a ∈ D₁ := ⟨1, K.one_mem, by simp⟩
  have hcent : ∀ l ∈ L, l ∉ K → ∀ h ∈ N₁, h * (l * a * l⁻¹) = (l * a * l⁻¹) * h := by
    intro l hl hlK
    have hle : N₁ ≤ Subgroup.centralizer {l * a * l⁻¹} := by
      rw [hN₁, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommute k hk l hl hlK)
    exact fun h hh => Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hMN : M ≤ Subgroup.normalizer (N₁ : Set Γ) := by
    rw [hM, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    by_cases hlK : l ∈ K
    · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨l, hlK, rfl⟩)
    · refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      exact fun h hh => hcent l hl hlK h hh
  have hLM : L ≤ M := by
    have hMnorm : ∀ l ∈ L, ∀ x ∈ M ⊓ L, l * x * l⁻¹ ∈ M ⊓ L := by
      intro l hl x hx
      refine ⟨?_, L.mul_mem (L.mul_mem hl hx.2) (L.inv_mem hl)⟩
      refine conj_mem_closure_of_forall (S := D) ?_ hx.1
      rintro _ ⟨l', hl', rfl⟩
      exact Subgroup.subset_closure ⟨l * l', L.mul_mem hl hl', by group⟩
    rcases eq_bot_or_eq_of_normalized hsimple inf_le_right hMnorm with hX | hX
    · exfalso
      obtain ⟨x₀, hx₀L, hx₀⟩ := hac
      refine hx₀ ?_
      have hc : a * x₀ * a⁻¹ * x₀⁻¹ ∈ M ⊓ L := by
        refine ⟨?_, comm_mem_of_mem haL hx₀L⟩
        have e : a * x₀ * a⁻¹ * x₀⁻¹ = a * (x₀ * a * x₀⁻¹)⁻¹ := by group
        rw [e]
        exact M.mul_mem (Subgroup.subset_closure ⟨1, L.one_mem, by simp⟩)
          (M.inv_mem (Subgroup.subset_closure ⟨x₀, hx₀L, rfl⟩))
      rw [hX, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
      exact hc
    · exact inf_eq_right.mp hX
  have hLN : L ≤ N₁ := by
    have hYnorm : ∀ l ∈ L, ∀ y ∈ N₁ ⊓ L, l * y * l⁻¹ ∈ N₁ ⊓ L := by
      intro l hl y hy
      refine ⟨?_, L.mul_mem (L.mul_mem hl hy.2) (L.inv_mem hl)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMN (hLM hl)) y).mp hy.1
    rcases eq_bot_or_eq_of_normalized hsimple inf_le_right hYnorm with hY | hY
    · exfalso
      obtain ⟨x, hx⟩ := hne
      have hxK : x ∈ K := Subgroup.subset_closure hx
      have hxL : x ∈ L := hKL hxK
      have hy : (x * a * x⁻¹) * a ∈ N₁ ⊓ L := by
        refine ⟨N₁.mul_mem (Subgroup.subset_closure ⟨x, hxK, rfl⟩)
          (Subgroup.subset_closure haD₁), ?_⟩
        have e : x * a * x⁻¹ * a = x * (a * x⁻¹ * a⁻¹) := by rw [hai]; group
        rw [e]
        exact L.mul_mem hxL (haL _ (L.inv_mem hxL))
      rw [hY, Subgroup.mem_bot] at hy
      have h1 : x * a * x⁻¹ = a := by
        have := mul_eq_one_iff_eq_inv.mp hy
        rwa [hai] at this
      exact not_mem_invXi_of_commute (mul_inv_eq_iff_eq_mul.mp h1).symm hx
    · exact inf_eq_right.mp hY
  obtain ⟨x, hxL, hx⟩ := hac
  refine hx ?_
  have h1 := hcent g hgL hgK (g * x * g⁻¹) (hLN (L.mul_mem (L.mul_mem hgL hxL) (L.inv_mem hgL)))
  have h2 : g * (x * a) * g⁻¹ = g * (a * x) * g⁻¹ := by
    calc g * (x * a) * g⁻¹ = g * x * g⁻¹ * (g * a * g⁻¹) := by group
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := h1
      _ = g * (a * x) * g⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem invGen_of_two_adjacent_commute [Finite Γ] (hsimple : IsSimpleGroup ↥L)
    (hnonab : ∃ x y : ↥L, x * y ≠ y * x) (ha2 : a * a = 1)
    (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) (hac : ∃ x ∈ L, a * x ≠ x * a)
    (hdih : ∀ x ∈ L, IsPGroup 2 ↥(Subgroup.closure ({a, x * a * x⁻¹} : Set Γ)) →
      a * (x * a * x⁻¹) = (x * a * x⁻¹) * a) : InvGen L a := by
  refine invGen_of_commute hsimple hnonab ha2 haL hac fun x hx h2 => ?_
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨n, hn⟩ := isPGroup_two_zpowers_iff.mp h2
  have hts : a * x * a⁻¹ * x⁻¹ = a * (x * a * x⁻¹) := by rw [hai]; group
  set b : Γ := x * a * x⁻¹ with hb
  have hbb : b * b = 1 := by
    calc b * b = x * (a * a) * x⁻¹ := by rw [hb]; group
      _ = 1 := by rw [ha2]; group
  rw [hts] at hn ⊢
  have hcl : a * b = b * a :=
    hdih x hx (isPGroup_closure_pair_of_involutions ha2 hbb hn)
  calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
    _ = a * (a * b) * b := by rw [← hcl]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha2, hbb, one_mul]

theorem invGen_of_abelian_two_subgroups [Finite Γ] (hsimple : IsSimpleGroup ↥L)
    (hnonab : ∃ x y : ↥L, x * y ≠ y * x) (ha2 : a * a = 1)
    (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) (hac : ∃ x ∈ L, a * x ≠ x * a)
    (hab : ∀ P : Subgroup Γ, P ≤ L ⊔ Subgroup.zpowers a → IsPGroup 2 ↥P →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : InvGen L a := by
  refine invGen_of_two_adjacent_commute hsimple hnonab ha2 haL hac fun x hx h2 => ?_
  have haH : a ∈ L ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hxH : x ∈ L ⊔ Subgroup.zpowers a := Subgroup.mem_sup_left hx
  have hle : Subgroup.closure ({a, x * a * x⁻¹} : Set Γ) ≤ L ⊔ Subgroup.zpowers a := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact haH
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxH haH) (Subgroup.inv_mem _ hxH)
  exact hab _ hle h2 a (Subgroup.subset_closure (Set.mem_insert _ _)) _
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem invGen_of_abelian_two_subgroups_of_mem [Finite Γ] (hsimple : IsSimpleGroup ↥L)
    (hnonab : ∃ x y : ↥L, x * y ≠ y * x) (ha2 : a * a = 1) (haL₀ : a ∈ L)
    (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) (hac : ∃ x ∈ L, a * x ≠ x * a)
    (hab : ∀ P : Subgroup Γ, P ≤ L → IsPGroup 2 ↥P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    InvGen L a :=
  invGen_of_abelian_two_subgroups hsimple hnonab ha2 haL hac fun P hP h2 =>
    hab P (hP.trans (sup_le le_rfl (Subgroup.zpowers_le.mpr haL₀))) h2

end CFSG.Quasithin.F7Two
