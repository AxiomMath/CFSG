module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG

section Restriction

variable {E : Type*} [Group E]

@[expose] def autStab (S : Subgroup E) : Subgroup (MulAut E) where
  carrier := {α | ∀ x, x ∈ S ↔ α x ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {_ β} hα hβ x => (hβ x).trans (hα (β x))
  inv_mem' := fun {α} hα x => by
    have h := hα (α⁻¹ x)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

theorem mem_autStab {S : Subgroup E} {α : MulAut E} :
    α ∈ autStab S ↔ ∀ x, x ∈ S ↔ α x ∈ S :=
  Iff.rfl

@[expose] noncomputable def restrictHom (S : Subgroup E) : autStab S →* MulAut S where
  toFun α :=
    { toFun := fun x => ⟨(α : MulAut E) x, ((mem_autStab.1 α.2) x).1 x.2⟩
      invFun := fun x => ⟨(α : MulAut E)⁻¹ x, ((mem_autStab.1 (inv_mem α.2)) x).1 x.2⟩
      left_inv := fun _ => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun _ => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem coe_restrictHom_apply (S : Subgroup E) (α : autStab S) (x : S) :
    ((restrictHom S α x : S) : E) = (α : MulAut E) x :=
  rfl

end Restriction

section Pair

variable {E : Type*} [Group E] {S₁ S₂ : Subgroup E}

theorem normal_of_commute_of_sup_eq_top (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hsup : S₁ ⊔ S₂ = ⊤) : S₁.Normal := by
  have h2 : S₂ ≤ normalizer (S₁ : Set E) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hcomm h hh g hg, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h' : g * h * g⁻¹ * g = g * (g * h * g⁻¹) := hcomm _ hh g hg
      have h'' : g * h = g * (g * h * g⁻¹) := by rw [← h']; group
      rw [mul_left_cancel h'']
      exact hh
  have htop : normalizer (S₁ : Set E) = ⊤ :=
    top_le_iff.1 (hsup ▸ sup_le le_normalizer h2)
  exact normalizer_eq_top_iff.1 htop

theorem exists_mul_eq_of_commute_of_sup_eq_top (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hsup : S₁ ⊔ S₂ = ⊤) (x : E) : ∃ a ∈ S₁, ∃ b ∈ S₂, a * b = x := by
  have := normal_of_commute_of_sup_eq_top hcomm hsup
  have hx : x ∈ ((S₁ ⊔ S₂ : Subgroup E) : Set E) := by rw [hsup]; exact mem_top x
  rw [normal_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

theorem center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ center S := h ▸ mem_top b
    exact hab (mem_center_iff.1 hb a)

theorem center_eq_bot_of_pair (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hsup : S₁ ⊔ S₂ = ⊤) [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hnab₁ : ∃ a b : S₁, a * b ≠ b * a) (hnab₂ : ∃ a b : S₂, a * b ≠ b * a) :
    center E = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_commute_of_sup_eq_top hcomm hsup z
  have ha1 : (⟨a, ha⟩ : S₁) ∈ center S₁ := by
    rw [mem_center_iff]
    intro s
    apply Subtype.ext
    have h1 := mem_center_iff.1 hz s
    have h2 := hcomm s s.2 b hb
    change (s : E) * a = a * s
    have : (s : E) * a * b = a * s * b := by
      calc (s : E) * a * b = s * (a * b) := mul_assoc _ _ _
        _ = a * b * s := h1
        _ = a * (b * s) := mul_assoc _ _ _
        _ = a * (s * b) := by rw [h2]
        _ = a * s * b := (mul_assoc _ _ _).symm
    exact mul_right_cancel this
  have hb1 : (⟨b, hb⟩ : S₂) ∈ center S₂ := by
    rw [mem_center_iff]
    intro s
    apply Subtype.ext
    have h1 := mem_center_iff.1 hz s
    have h2 := hcomm a ha s s.2
    change (s : E) * b = b * s
    have : a * (s * b) = a * (b * s) := by
      calc a * (s * b) = s * a * b := by rw [← mul_assoc, h2]
        _ = s * (a * b) := mul_assoc _ _ _
        _ = a * b * s := h1
        _ = a * (b * s) := mul_assoc _ _ _
    exact mul_left_cancel this
  rw [center_eq_bot_of_isSimpleGroup hnab₁, mem_bot] at ha1
  rw [center_eq_bot_of_isSimpleGroup hnab₂, mem_bot] at hb1
  have ha' : a = 1 := congrArg Subtype.val ha1
  have hb' : b = 1 := congrArg Subtype.val hb1
  rw [ha', hb', mul_one]
  exact one_mem _

theorem le_of_inf_ne_bot {N S : Subgroup E} [N.Normal] [S.Normal] [IsSimpleGroup S]
    (h : N ⊓ S ≠ ⊥) : S ≤ N := by
  have hNS : (N ⊓ S).Normal := inferInstance
  have hn : ((N ⊓ S).subgroupOf S).Normal := hNS.subgroupOf S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ S).subgroupOf S) with h0 | h0
  · exfalso
    apply h
    rw [subgroupOf_eq_bot] at h0
    exact disjoint_iff.1 (h0.mono_right le_rfl) ▸ (inf_eq_left.2 inf_le_right).symm
  · rw [subgroupOf_eq_top] at h0
    exact h0.trans inf_le_left

theorem le_or_le_of_normal (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hsup : S₁ ⊔ S₂ = ⊤) [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hnab₁ : ∃ a b : S₁, a * b ≠ b * a) (hnab₂ : ∃ a b : S₂, a * b ≠ b * a)
    {N : Subgroup E} [N.Normal] (hN : N ≠ ⊥) : S₁ ≤ N ∨ S₂ ≤ N := by
  have hcomm' : ∀ x ∈ S₂, ∀ y ∈ S₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hsup' : S₂ ⊔ S₁ = ⊤ := by rw [sup_comm, hsup]
  have := normal_of_commute_of_sup_eq_top hcomm hsup
  have := normal_of_commute_of_sup_eq_top hcomm' hsup'
  by_contra hcon
  rw [not_or] at hcon
  have h1 : N ⊓ S₁ = ⊥ := by
    by_contra h
    exact hcon.1 (le_of_inf_ne_bot h)
  have h2 : N ⊓ S₂ = ⊥ := by
    by_contra h
    exact hcon.2 (le_of_inf_ne_bot h)
  have hc : ∀ n ∈ N, ∀ (S : Subgroup E), S.Normal → N ⊓ S = ⊥ → ∀ s ∈ S, n * s = s * n := by
    intro n hn S hS hNS s hs
    have hmem : n * s * n⁻¹ * s⁻¹ ∈ N ⊓ S := by
      refine ⟨?_, ?_⟩
      · rw [mul_assoc, mul_assoc]
        refine N.mul_mem hn ?_
        rw [← mul_assoc]
        exact Normal.conj_mem inferInstance _ (N.inv_mem hn) s
      · exact S.mul_mem (hS.conj_mem s hs n) (S.inv_mem hs)
    rw [hNS, mem_bot] at hmem
    have := mul_inv_eq_one.1 hmem
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  apply hN
  rw [eq_bot_iff, ← center_eq_bot_of_pair hcomm hsup hnab₁ hnab₂]
  intro n hn
  rw [mem_center_iff]
  intro g
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_commute_of_sup_eq_top hcomm hsup g
  rw [mul_assoc, ← hc n hn S₂ inferInstance h2 b hb, ← mul_assoc,
    ← hc n hn S₁ inferInstance h1 a ha, mul_assoc]

variable [Finite E]

end Pair

end CFSG.Quasithin.H13.QRC
