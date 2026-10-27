module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.FixedAux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T85

variable {G : Type*} [Group G]

theorem lHat_le (H L : Subgroup G) : lHat H L ≤ H :=
  sSup_le fun _ hR => lcal_le hR.1

theorem le_lHat {H L R : Subgroup G} (hR : R ∈ lcal H)
    (hRL : ¬ L ≤ Subgroup.centralizer (R : Set G)) : R ≤ lHat H L :=
  le_sSup ⟨hR, hRL⟩

theorem lHat_le_of_forall {H L X : Subgroup G}
    (h : ∀ R ∈ lcal H, ¬ L ≤ Subgroup.centralizer (R : Set G) → R ≤ X) : lHat H L ≤ X :=
  sSup_le fun R hR => h R hR.1 hR.2

theorem map_conj_le_centralizer_iff (g : G) {X R : Subgroup G} :
    X.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ((R.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
      X ≤ Subgroup.centralizer (R : Set G) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := Subgroup.mem_centralizer_iff.mp (h ⟨x, hx, rfl⟩) (g * r * g⁻¹) ⟨r, hr, rfl⟩
    have h2 : g * (r * x) * g⁻¹ = g * (x * r) * g⁻¹ := by
      calc g * (r * x) * g⁻¹ = g * r * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * r * g⁻¹) := h1
        _ = g * (x * r) * g⁻¹ := by group
    simpa using h2
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (h hx) r hr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * r * g⁻¹ * (g * x * g⁻¹) = g * (r * x) * g⁻¹ := by group
      _ = g * (x * r) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * r * g⁻¹) := by group

theorem map_conj_lHat_le {H L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    (lHat H L).map (MulAut.conj g).toMonoidHom ≤
      lHat H (L.map (MulAut.conj g).toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun R hR => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_lHat (map_conj_mem_lcal hR.1 hg) fun hle => hR.2 ((map_conj_le_centralizer_iff g).mp hle)

theorem map_conj_lHat {H L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    (lHat H L).map (MulAut.conj g).toMonoidHom =
      lHat H (L.map (MulAut.conj g).toMonoidHom) := by
  refine le_antisymm (map_conj_lHat_le hg) ?_
  have h1 := map_conj_lHat_le (H := H) (L := L.map (MulAut.conj g).toMonoidHom) (inv_mem hg)
  rw [Near.Lemma212.map_conj_map_conj_inv] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  have h3 := Near.Lemma212.map_conj_map_conj_inv
    (lHat H (L.map (MulAut.conj g).toMonoidHom)) g⁻¹
  rw [inv_inv] at h3
  rwa [h3] at h2

section Orbits

variable [Finite G] {Ω : Set (Subgroup G)} {H F : Subgroup G}

omit [Finite G] in
theorem lHat_smear_le_orbitClosure (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω)
    (hcomp : ∀ R ∈ lcal H, ∃ Q ∈ Ω, R ≤ Q) {Q₁ : Subgroup G} (hQ₁ : Q₁ ∈ Ω) :
    lHat H (smear Q₁ F) ≤ orbitClosure Q₁ F := by
  refine lHat_le_of_forall fun R hR hnc => ?_
  obtain ⟨Q, hQ, hRQ⟩ := hcomp R hR
  by_cases hmem : Q ∈ RegFam.conjOrbit Q₁ F
  · obtain ⟨f, hf, rfl⟩ := hmem
    exact hRQ.trans (map_conj_le_orbitClosure Q₁ hf)
  · exfalso
    refine hnc fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact (RegFam.commute_orbitClosure hΩ hF hQ₁ hQ hmem x (smear_le_orbitClosure Q₁ F hx) y
      (le_orbitClosure Q F (hRQ hy))).eq.symm

theorem le_lHat_smear (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω)
    (hfree : ∀ f ∈ F, f ≠ 1 → ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ≠ J)
    {Q₁ Q : Subgroup G} (hQ₁ : Q₁ ∈ Ω) (hQ : Q ∈ RegFam.conjOrbit Q₁ F) {R : Subgroup G}
    (hR : R ∈ lcal H) (hRQ : R ≤ Q) : R ≤ lHat H (smear Q₁ F) := by
  have hQΩ : Q ∈ Ω := RegFam.conjOrbit_subset hQ₁ hF hQ
  refine le_lHat hR fun hle => ?_
  have hsm : smear Q F = smear Q₁ F := by
    obtain ⟨f, hf, rfl⟩ := hQ
    unfold smear
    rw [Near.Lemma212.orbitClosure_map_conj_of_mem Q₁ hf]
  have hW : smear Q₁ F ≤ H ⊓ Subgroup.centralizer (F : Set G) :=
    le_inf ((smear_le_orbitClosure Q₁ F).trans (orbitClosure_le fun f hf =>
      hΩ.le (hF f hf Q₁ hQ₁))) (smear_le_centralizer Q₁ F)
  have h1 := le_projIn_of_smear_le hΩ hF hfree hW hQΩ le_rfl hsm.le
  have hQc : Q ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    obtain ⟨-, l, hl, hxl⟩ := (mem_proj_iff (hΩ.commute_sSup_diff hQΩ)).mp (h1 hx)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 := Subgroup.mem_centralizer_iff.mp (hle hxl) z hz
    have h3 := (hΩ.commute_sSup_diff hQΩ z (hRQ hz) l hl).eq
    apply mul_right_cancel (b := l)
    calc z * x * l = z * (x * l) := mul_assoc _ _ _
      _ = x * l * z := h2
      _ = x * (l * z) := mul_assoc _ _ _
      _ = x * (z * l) := by rw [h3]
      _ = x * z * l := (mul_assoc _ _ _).symm
  refine (mem_lcal_iff.mp hR).2.2.2 (isMulCommutative_iff.mpr fun a b => ?_)
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hQc (hRQ a.2)) b b.2).symm)

end Orbits

end T85

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
