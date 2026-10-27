module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def InH (X H : Subgroup G) : Prop := X ≤ H ∧ pCoreOf 2 H ≠ ⊥

@[expose] def InM (X M : Subgroup G) : Prop := quasithinIsMaxTwoLocal M ∧ X ≤ M

@[expose] def IsUniqueM (X M : Subgroup G) : Prop := InM X M ∧ ∀ M', InM X M' → M' = M

@[expose] def conjClosure (Z H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x}

@[expose] def VZ (T H : Subgroup G) : Subgroup G := conjClosure (quasithinOmegaOneCenter T) H

@[expose] def OrdLE (T H₁ H₂ : Subgroup G) : Prop :=
  ∀ h ∈ H₁, ∃ a ∈ H₁ ⊓ H₂, ∃ c ∈ H₁ ⊓ Subgroup.centralizer (VZ T H₁ : Set G), h = a * c

@[expose] def IsHv (T H : Subgroup G) : Prop := H = Subgroup.normalizer (VZ T H : Set G)

theorem mem_conjClosure {Z H : Subgroup G} {h z : G} (hh : h ∈ H) (hz : z ∈ Z) :
    h * z * h⁻¹ ∈ conjClosure Z H :=
  Subgroup.subset_closure ⟨h, hh, z, hz, rfl⟩

theorem le_conjClosure (Z H : Subgroup G) : Z ≤ conjClosure Z H := fun z hz => by
  simpa using mem_conjClosure (H.one_mem) hz

theorem conjClosure_le {Z H K : Subgroup G}
    (h : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ K) : conjClosure Z H ≤ K := by
  rw [conjClosure, Subgroup.closure_le]
  rintro x ⟨h', hh', z, hz, rfl⟩
  exact h h' hh' z hz

theorem conjClosure_mono {Z₁ Z₂ H₁ H₂ : Subgroup G} (hZ : Z₁ ≤ Z₂) (hH : H₁ ≤ H₂) :
    conjClosure Z₁ H₁ ≤ conjClosure Z₂ H₂ :=
  conjClosure_le fun _ hh _ hz => mem_conjClosure (hH hh) (hZ hz)

theorem le_normalizer_conjClosure (Z H : Subgroup G) :
    H ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ k ∈ H, ∀ x ∈ conjClosure Z H, k * x * k⁻¹ ∈ conjClosure Z H := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      simpa [mul_assoc] using mem_conjClosure (H.mul_mem hk hh) hz
    | one => simp
    | mul x y _ _ ihx ihy =>
      simpa [mul_assoc] using (conjClosure Z H).mul_mem ihx ihy
    | inv x _ ih =>
      simpa [mul_assoc] using (conjClosure Z H).inv_mem ih
  intro x
  constructor
  · exact key g hg x
  · intro hx
    simpa [mul_assoc] using key g⁻¹ (H.inv_mem hg) _ hx

theorem conj_of_ordLE {T H₁ H₂ : Subgroup G} (hle : OrdLE T H₁ H₂) {h z : G} (hh : h ∈ H₁)
    (hz : z ∈ VZ T H₁) : ∃ a ∈ H₁ ⊓ H₂, h * z * h⁻¹ = a * z * a⁻¹ := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hle h hh
  refine ⟨a, ha, ?_⟩
  have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc.2 z hz).symm
  calc a * c * z * (a * c)⁻¹ = a * (c * z) * c⁻¹ * a⁻¹ := by group
    _ = a * z * a⁻¹ := by rw [hcz]; group

theorem VZ_le_of_ordLE {T H₁ H₂ : Subgroup G} (hle : OrdLE T H₁ H₂) :
    VZ T H₁ ≤ VZ T H₂ := by
  refine conjClosure_le fun h hh z hz => ?_
  obtain ⟨a, ha, heq⟩ :=
    conj_of_ordLE hle hh (le_conjClosure (quasithinOmegaOneCenter T) H₁ hz)
  rw [heq]
  exact mem_conjClosure ha.2 hz

theorem centralizer_VZ_le_of_ordLE {T H₁ H₂ : Subgroup G} (hle : OrdLE T H₁ H₂) :
    H₂ ⊓ Subgroup.centralizer (VZ T H₂ : Set G) ≤
      H₂ ⊓ Subgroup.centralizer (VZ T H₁ : Set G) :=
  inf_le_inf_left _ (Subgroup.centralizer_le (VZ_le_of_ordLE hle))

theorem centralizer_VZ_le_of_ordLE_of_isHv {T H₁ H₂ : Subgroup G} (hle : OrdLE T H₁ H₂)
    (hv : IsHv T H₁) :
    H₂ ⊓ Subgroup.centralizer (VZ T H₂ : Set G) ≤
      H₁ ⊓ Subgroup.centralizer (VZ T H₁ : Set G) := by
  intro g hg
  have hc : g ∈ Subgroup.centralizer (VZ T H₁ : Set G) :=
    Subgroup.centralizer_le (VZ_le_of_ordLE hle) hg.2
  refine ⟨?_, hc⟩
  rw [hv]
  exact Subgroup.centralizer_le_normalizer _ hc

theorem ordLE_refl (T H : Subgroup G) : OrdLE T H H := fun h hh =>
  ⟨h, ⟨hh, hh⟩, 1, ⟨H.one_mem, Subgroup.one_mem _⟩, (mul_one h).symm⟩

theorem ordLE_of_le {T H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : OrdLE T H₁ H₂ := fun x hx =>
  ⟨x, ⟨hx, h hx⟩, 1, ⟨H₁.one_mem, Subgroup.one_mem _⟩, (mul_one x).symm⟩

theorem eq_of_VZ_eq {T H₁ H₂ : Subgroup G} (hv₁ : IsHv T H₁) (hv₂ : IsHv T H₂)
    (h : VZ T H₁ = VZ T H₂) : H₁ = H₂ := by
  rw [hv₁, hv₂, h]

theorem eq_of_ordLE_antisymm {T H₁ H₂ : Subgroup G} (hv₁ : IsHv T H₁) (hv₂ : IsHv T H₂)
    (h₁₂ : OrdLE T H₁ H₂) (h₂₁ : OrdLE T H₂ H₁) : H₁ = H₂ :=
  eq_of_VZ_eq hv₁ hv₂ (le_antisymm (VZ_le_of_ordLE h₁₂) (VZ_le_of_ordLE h₂₁))

theorem isHv_eq_tfae {T H₁ H₂ : Subgroup G} (hv₁ : IsHv T H₁) (hv₂ : IsHv T H₂) :
    List.TFAE [H₁ = H₂, VZ T H₁ = VZ T H₂, OrdLE T H₁ H₂ ∧ OrdLE T H₂ H₁] := by
  tfae_have 1 → 2 := fun h => by rw [h]
  tfae_have 2 → 1 := eq_of_VZ_eq hv₁ hv₂
  tfae_have 1 → 3 := fun h => by subst h; exact ⟨ordLE_refl T H₁, ordLE_refl T H₁⟩
  tfae_have 3 → 1 := fun h => eq_of_ordLE_antisymm hv₁ hv₂ h.1 h.2
  tfae_finish

theorem ordLE_trans {T H₁ H₂ H₃ : Subgroup G} (hv₁ : IsHv T H₁) (h₁₂ : OrdLE T H₁ H₂)
    (h₂₃ : OrdLE T H₂ H₃) : OrdLE T H₁ H₃ := by
  intro h hh
  obtain ⟨a, ha, c, hc, rfl⟩ := h₁₂ h hh
  obtain ⟨b, hb, d, hd, rfl⟩ := h₂₃ a ha.2
  have hd₁ : d ∈ H₁ ⊓ Subgroup.centralizer (VZ T H₁ : Set G) :=
    centralizer_VZ_le_of_ordLE_of_isHv h₁₂ hv₁ hd
  have hb₁ : b ∈ H₁ := by
    have : b = b * d * d⁻¹ := by group
    rw [this]
    exact H₁.mul_mem ha.1 (H₁.inv_mem hd₁.1)
  exact ⟨b, ⟨hb₁, hb.2⟩, d * c, (H₁ ⊓ _).mul_mem hd₁ hc, by group⟩

theorem le_of_ordLE_of_normal {T H M V : Subgroup G} (hM : quasithinIsMaxTwoLocal M)
    (hle : OrdLE T H M) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hVM : M ≤ Subgroup.normalizer (V : Set G))
    (hgen : V = conjClosure (V ⊓ quasithinOmegaOneCenter T) (H ⊓ M)) : H ≤ M := by
  have hMN : M = Subgroup.normalizer (V : Set G) :=
    (hM.2 _ ⟨V, hV, hV2, rfl⟩ hVM).symm
  have hVH : V = conjClosure (V ⊓ quasithinOmegaOneCenter T) H := by
    apply le_antisymm
    · conv_lhs => rw [hgen]
      exact conjClosure_mono le_rfl inf_le_left
    · refine conjClosure_le fun h hh z hz => ?_
      have hzV : z ∈ VZ T H :=
        le_conjClosure (quasithinOmegaOneCenter T) H hz.2
      obtain ⟨a, ha, heq⟩ := conj_of_ordLE hle hh hzV
      rw [heq, hgen]
      exact mem_conjClosure ha hz
  rw [hMN, hVH]
  exact le_normalizer_conjClosure _ _

end CFSG.Quasithin
