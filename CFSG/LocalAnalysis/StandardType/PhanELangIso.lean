module

public import CFSG.LocalAnalysis.StandardType.PhanEFixedTorus
public import CFSG.LocalAnalysis.StandardType.PhanELangAdjust
public import CFSG.LocalAnalysis.StandardType.PhanEStdPanel
public import CFSG.LocalAnalysis.StandardType.PhanEDMPanel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

theorem exists_flipOp_of_isSphericalFlip {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {C : Type} {δ : C → C → W} {w₀ : W} {t : C → C}
    (hB : IsWeylDistanceBuilding cs δ) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) (x : C) : ∃ y : C, δ y (t y) = w₀ := by
  have hw0 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  have key : ∀ n : ℕ, (∀ z : C, cs.length (DM.dstar δ w₀ t z) = n →
      ∃ y : C, δ y (t y) = w₀) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz
      by_cases h1 : DM.dstar δ w₀ t z = 1
      · refine ⟨z, ?_⟩
        have h' : δ z (t z) * w₀ = 1 := h1
        calc δ z (t z) = δ z (t z) * w₀ * w₀ := by rw [mul_assoc, hw0, mul_one]
          _ = w₀ := by rw [h', one_mul]
      · obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one h1
        obtain ⟨z', _hz'mem, hz'lt⟩ := DM.exists_panel_dstar_lt hB hw ht hj
        exact ih (cs.length (DM.dstar δ w₀ t z')) (by rw [← hz]; exact hz'lt) z' rfl
  exact key (cs.length (DM.dstar δ w₀ t x)) x rfl

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

section Lang

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀) (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

include hext hw₀ hsq in
theorem exists_inv_mul_phi_eq (hBU : BruhatExtras D H) (L : StdLevi F (nrep hct w₀))
    (R : RankOneField hct F) : ∃ g : K, g⁻¹ * F.φ g = nrep hct w₀ := by
  have hpanel1 : StdPanel hct F 1 :=
    stdPanel_of_rankOneField (hct := hct) (F := F) (n₀ := 1) (hext := hext) (hw₀ := hw₀)
      (hsq := hsq) (R := R)
  have ht : IsSphericalFlip (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) w₀
      (stdFlip F 1) := stdIsSphericalFlip_one (hct := hct) (F := F) (hext := hext) (hw₀ := hw₀)
        (hpanel := hpanel1)
  have hbuilding : IsWeylDistanceBuilding (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (stdδ hct) := stdBuilding hct hext
  have hlength : ∀ w : (coxeterMatrix D.isFiniteType).Group,
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (w * w₀) +
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w =
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w₀ := fun w => by
    simpa using hw₀.length_mul_left (q2nPE_mem_parabolic_univ w)
  obtain ⟨y, hy⟩ := exists_flipOp_of_isSphericalFlip hbuilding hlength ht
    ((1 : K) : K ⧸ borel D H)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hcell : g⁻¹ * F.φ g ∈ bruhatCell hct w₀ := by
    have h := (stdδ_flip_mk_eq_iff (hct := hct) (F := F) (hext := hext) (hw₀ := hw₀)
      (n₀ := 1) (g := g) (w := w₀)).mp hy
    simpa using h
  obtain ⟨b₁, hb₁, b₂, hb₂, hg_eq⟩ := hcell
  have hn₀ : F.φ (nrep hct w₀) = (nrep hct w₀)⁻¹ :=
    eq_inv_of_mul_eq_one_right (nrep_mul_phi_self hct F hext hw₀ hsq)
  have hφB : ∀ b ∈ borel D H, F.φ b ∈ borel D H :=
    fun b hb => F.borel_map (Subgroup.mem_map_of_mem F.φ hb)
  have hBT : borel D H ⊓ (borel D H).map
      (MulAut.conj (nrep hct w₀)).toMonoidHom = ⨆ i, H i :=
    borel_inf_map_conj (hct := hct) (hext := hext) (hw₀ := hw₀) (hsq := hsq) (hBU := hBU)
  have hlang : ∀ s ∈ ⨆ i, H i, nrep hct w₀ * F.φ s * (nrep hct w₀)⁻¹ = s⁻¹ →
      ∃ r ∈ ⨆ i, H i, s = r * (nrep hct w₀ * F.φ r * (nrep hct w₀)⁻¹)⁻¹ := by
    intro s hs hτ
    obtain ⟨r, hr, hr_eq⟩ := torus_lang (F := F) (hext := hext) (L := L) (hs := hs)
      (hτ := by rw [stdTau_apply]; exact hτ)
    exact ⟨r, hr, by rw [hr_eq, stdTau_apply]⟩
  obtain ⟨b, _hb, hb_eq⟩ := exists_mul_inv_mul_eq (φ := F.φ) (hφ := F.invol)
    (B := borel D H) (T := ⨆ i, H i) (n₀ := nrep hct w₀) (hn₀ := hn₀) (hB := hφB)
    (hBT := hBT) (hlang := hlang) (hb₁ := hb₁) (hb₂ := hb₂) (hg := hg_eq)
  exact ⟨g * b, hb_eq⟩

end Lang

section Iso

variable {w₀ : W} (F : FrobData D n H w₀) {n₀ g : K} (hg : g⁻¹ * F.φ g = n₀)

include hg in
theorem conj_mem_stdFix {x : K} (hx : x ∈ frobFix F) : g⁻¹ * x * g ∈ stdFix F n₀ := by
  have hφg : F.φ g = g * n₀ := by
    rw [← hg]
    group
  have hx' : F.φ x = x := hx
  rw [mem_stdFix_iff]
  simp only [map_mul, map_inv, hφg, hx']
  group

include hg in
theorem conj_mem_frobFix {y : K} (hy : y ∈ stdFix F n₀) : g * y * g⁻¹ ∈ frobFix F := by
  have hφg : F.φ g = g * n₀ := by
    rw [← hg]
    group
  have hy0 : n₀ * F.φ y * n₀⁻¹ = y := hy
  have hy' : F.φ y = n₀⁻¹ * y * n₀ := by
    have h := congrArg (fun z => n₀⁻¹ * z * n₀) hy0
    rw [show n₀⁻¹ * (n₀ * F.φ y * n₀⁻¹) * n₀ = F.φ y by group] at h
    exact h
  rw [mem_frobFix_iff]
  simp only [map_mul, map_inv, hφg, hy']
  group

@[expose] noncomputable def frobFixEquiv : frobFix F ≃* stdFix F n₀ where
  toFun x := ⟨g⁻¹ * x * g, conj_mem_stdFix F hg x.2⟩
  invFun y := ⟨g * y * g⁻¹, conj_mem_frobFix F hg y.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

variable {G : Type} [Group G] (e : G ≃* frobFix F)

@[expose] noncomputable def stdEmbed : G →* K :=
  (stdFix F n₀).subtype.comp ((frobFixEquiv F hg).toMonoidHom.comp e.toMonoidHom)

theorem stdEmbed_injective : Function.Injective (stdEmbed F hg e) := by
  intro x y hxy
  have h1 : frobFixEquiv F hg (e x) = frobFixEquiv F hg (e y) := by
    apply Subtype.coe_injective
    exact hxy
  exact e.injective ((frobFixEquiv F hg).injective h1)

theorem range_stdEmbed : (stdEmbed F hg e).range = stdFix F n₀ := by
  rw [stdEmbed, MonoidHom.range_comp]
  have hf : ((frobFixEquiv F hg).toMonoidHom.comp e.toMonoidHom).range = ⊤ :=
    MonoidHom.range_eq_top.mpr ((frobFixEquiv F hg).surjective.comp e.surjective)
  rw [hf, Subgroup.map_top, Subgroup.range_subtype]

end Iso

end CFSG.ClassicalInvolution.Phan.PhanE
