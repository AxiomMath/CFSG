module

public import CFSG.RankThree.GF2n.Smith81.S81QRadNu

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


variable (K : Type) [Field K] [CharP K 2]

@[expose] def genSet0 : Set (W K ≃ₗ[K] W K) :=
  {g | ∃ β, ∃ hβ : β ∈ Perp, ∃ c : K, g = vAut0 K (xuWUnit hβ c)}

variable {K}

theorem genSet0_subset_EAut0 : genSet0 K ⊆ (EAut0 K : Set (W K ≃ₗ[K] W K)) := by
  rintro _ ⟨β, hβ, c, rfl⟩
  exact vAut0_xuWUnit_mem_EAut0 hβ c

theorem vAut0_mem_closure_genSet0_of_induces {l : (Module.End K (V K))ˣ} (hl : l ∈ Lam K) :
    ∃ g : (Module.End K (W K))ˣ, Induces g l ∧ vAut0 K g ∈ Subgroup.closure (genSet0 K) := by
  unfold Lam at hl
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, c, rfl⟩ := hx
    exact ⟨xuWUnit hβ c, xuWUnit_induces hβ c, Subgroup.subset_closure ⟨β, hβ, c, rfl⟩⟩
  | one => exact ⟨1, induces_one, one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨g₁, h₁, m₁⟩ := ihx
    obtain ⟨g₂, h₂, m₂⟩ := ihy
    exact ⟨g₁ * g₂, h₁.mul h₂, by rw [map_mul]; exact mul_mem m₁ m₂⟩
  | inv x hx ihx =>
    obtain ⟨g, h, m⟩ := ihx
    exact ⟨g⁻¹, h.inv, by rw [map_inv]; exact inv_mem m⟩

theorem EAut0_eq_closure_genSet0 : EAut0 K = Subgroup.closure (genSet0 K) := by
  apply le_antisymm
  · rintro _ ⟨g, ⟨l, hl, hg⟩, rfl⟩
    obtain ⟨g', h', m'⟩ := vAut0_mem_closure_genSet0_of_induces hl
    rw [show g = g' from Induces.unique hg h']
    exact m'
  · rw [Subgroup.closure_le]
    exact genSet0_subset_EAut0

theorem subgroupOf_closure_eq {G : Type*} [Group G] (H : Subgroup G) (S : Set G) (hS : S ⊆ H) :
    (Subgroup.closure S).subgroupOf H = Subgroup.closure ((Subtype.val : H → G) ⁻¹' S) := by
  apply le_antisymm
  · intro x hx
    have h1 : (x : G) ∈ (Subgroup.closure ((Subtype.val : H → G) ⁻¹' S)).map H.subtype := by
      rw [MonoidHom.map_closure]
      have : (H.subtype : H → G) '' ((Subtype.val : H → G) ⁻¹' S) = S :=
        Set.image_preimage_eq_of_subset (by simpa using hS)
      rw [this]
      exact hx
    obtain ⟨y, hy, hyx⟩ := h1
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  · rw [Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hg)

end CFSG.RankThree.GF2n.Smith81.D6Spin
