module

public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.RankThree.PartOne.S12.WeylIso
public import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

@[expose] def fixedIn (E : Subgroup G) (X : Set (MulAut E)) : Subgroup G where
  carrier := {g | ∃ h : g ∈ E, ∀ x ∈ X, x ⟨g, h⟩ = ⟨g, h⟩}
  mul_mem' := by
    rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
    refine ⟨E.mul_mem ha hb, fun x hx => ?_⟩
    have h1 : (⟨a * b, E.mul_mem ha hb⟩ : E) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [h1, map_mul, hfa x hx, hfb x hx]
  one_mem' := ⟨E.one_mem, fun x _ => by
    have h1 : (⟨1, E.one_mem⟩ : E) = 1 := rfl
    rw [h1, map_one]⟩
  inv_mem' := by
    rintro a ⟨ha, hfa⟩
    refine ⟨E.inv_mem ha, fun x hx => ?_⟩
    have h1 : (⟨a⁻¹, E.inv_mem ha⟩ : E) = (⟨a, ha⟩ : E)⁻¹ := rfl
    rw [h1, map_inv, hfa x hx]

theorem fixedIn_le {E : Subgroup G} (X : Set (MulAut E)) : fixedIn E X ≤ E :=
  fun _ ⟨h, _⟩ => h

theorem fixedIn_anti {E : Subgroup G} {X Y : Set (MulAut E)} (h : X ⊆ Y) :
    fixedIn E Y ≤ fixedIn E X := fun _ ⟨hg, hf⟩ => ⟨hg, fun x hx => hf x (h hx)⟩

theorem eq_one_of_fixedIn_eq {E : Subgroup G} {X : Set (MulAut E)} (h : fixedIn E X = E) :
    ∀ x ∈ X, x = 1 := by
  intro x hx
  ext e
  have : (e : G) ∈ fixedIn E X := by rw [h]; exact e.2
  obtain ⟨he, hf⟩ := this
  exact congrArg (fun z : E => (z : G)) (hf x hx)

theorem fixed_of_closure {E : Subgroup G} {S : Set (MulAut E)} {e : E}
    (he : ∀ x ∈ S, x e = e) : ∀ x ∈ Subgroup.closure S, x e = e := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact he x hx
  | one => simp
  | mul x y _ _ hx hy => simp [MulAut.mul_apply, hx, hy]
  | inv x _ hx =>
    have : x⁻¹ e = e := by
      conv_lhs => rw [← hx]
      simp
    exact this

section Torus

theorem coe_conjAut_apply {E : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (e : E) : ((conjAut E w hw e : E) : G) = w * e * w⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨w, hw⟩ e

theorem torusImage_exists {E Y : Subgroup G} {φ : MulAut E} (hφ : φ ∈ torusImage E Y) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), w ∈ Y ∧ φ = conjAut E w hw := by
  obtain ⟨⟨w, hw⟩, hwY, rfl⟩ := Subgroup.mem_map.1 hφ
  exact ⟨w, hw, Subgroup.mem_subgroupOf.1 hwY, rfl⟩

theorem conjAut_mem_torusImage {E Y : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (hY : w ∈ Y) : conjAut E w hw ∈ torusImage E Y :=
  Subgroup.mem_map.2 ⟨⟨w, hw⟩, Subgroup.mem_subgroupOf.2 hY, rfl⟩

theorem torusNormalizer_le_of_stable {E : Subgroup G} {c : G}
    (hst : ∀ w ∈ Subgroup.normalizer (E : Set G), ∀ b ∈ Subgroup.zpowers c,
      w * b * w⁻¹ ∈ Subgroup.zpowers c) : torusNormalizer E ≤ cNormalizer c := by
  intro w hw
  rw [cNormalizer, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hst w hw y hy, fun hy => ?_⟩
  have := hst w⁻¹ (inv_mem hw) _ hy
  simpa [mul_assoc] using this

end Torus

section Weyl

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem torusImage_fixes_c (h : Sec12Hyp G p A c L E) {φ : MulAut E}
    (hφ : φ ∈ torusImage E L) : φ ⟨c, h.A_le_E h.c_mem⟩ = ⟨c, h.A_le_E h.c_mem⟩ := by
  obtain ⟨w, hw, hwL, rfl⟩ := torusImage_exists hφ
  apply Subtype.ext
  rw [coe_conjAut_apply hw]
  have hcw : c * w = w * c := Sec12Three.comm_c_L h w hwL
  show w * c * w⁻¹ = c
  rw [mul_inv_eq_iff_eq_mul, hcw]

theorem torusImage_le_reflectionGroup (hF : Sec12Facts G p A c L E) :
    torusImage E L ≤ reflectionGroup p E := by
  calc torusImage E L
      = Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) := hF.three.1
    _ ≤ reflectionGroup p E := Subgroup.closure_mono Set.inter_subset_left

theorem conj_mem_reflectionGroup (hp : p.Prime) {g : MulAut E} (hg : g ∈ torusWeyl E)
    {x : MulAut E} (hx : x ∈ reflectionGroup p E) : g * x * g⁻¹ ∈ reflectionGroup p E := by
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact Subgroup.subset_closure (WeylIso.conj_mem_reflectionSet_of_weyl hp hg ht)
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem fixedIn_stable (hp : p.Prime) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    {b : G} (hb : b ∈ fixedIn E (reflectionGroup p E : Set (MulAut E))) :
    w * b * w⁻¹ ∈ fixedIn E (reflectionGroup p E : Set (MulAut E)) := by
  obtain ⟨hbE, hbf⟩ := hb
  set g := conjAut E w hw with hg
  have hgW : g ∈ torusWeyl E := ⟨⟨w, hw⟩, rfl⟩
  have hmem : w * b * w⁻¹ ∈ E := by
    have := (g ⟨b, hbE⟩).2
    rwa [coe_conjAut_apply hw] at this
  refine ⟨hmem, fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ reflectionGroup p E :=
    conj_mem_reflectionGroup hp (inv_mem hgW) hx
  have h1 := hbf _ hx'
  apply Subtype.ext
  have h2 : (⟨w * b * w⁻¹, hmem⟩ : E) = g ⟨b, hbE⟩ :=
    Subtype.ext (coe_conjAut_apply hw ⟨b, hbE⟩).symm
  rw [h2]
  have h3 : x (g ⟨b, hbE⟩) = g ((g⁻¹ * x * g⁻¹⁻¹) ⟨b, hbE⟩) := by
    simp [MulAut.mul_apply]
  rw [h3, h1]

end Weyl

end CFSG.RankThree.PartOne.U5K.Pkg
