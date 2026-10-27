module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin

private def transportedConj {D : Type} [Group D] (L : Subgroup D) (hL : L.Normal)
    {L₀ : Type} [Group L₀] (κ : ↥L ≃* L₀) : D →* MulAut L₀ :=
  letI : L.Normal := hL
  (MulAut.congr κ).toMonoidHom.comp (MulAut.conjNormal (H := L))

private theorem transportedConj_apply {D : Type} [Group D] (L : Subgroup D) (hL : L.Normal)
    {L₀ : Type} [Group L₀] (κ : ↥L ≃* L₀) (d : D) (x : ↥L) :
    transportedConj L hL κ d (κ x) =
      κ ⟨d * (x : D) * d⁻¹, hL.conj_mem (x : D) x.2 d⟩ := by
  letI : L.Normal := hL
  change (MulAut.congr κ) (MulAut.conjNormal d) (κ x) =
    κ ⟨d * (x : D) * d⁻¹, hL.conj_mem (x : D) x.2 d⟩
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  apply congrArg κ
  apply Subtype.ext
  simp [MulAut.conjNormal_apply]

private theorem mem_map_subgroupOf_map_iff {D : Type} [Group D] (L : Subgroup D)
    {L₀ : Type} [Group L₀] (κ : ↥L ≃* L₀) (H : Subgroup D) (x : ↥L) :
    κ x ∈ (H.subgroupOf L).map κ.toMonoidHom ↔ (x : D) ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp [Subgroup.mem_subgroupOf]

private theorem transportedConj_mem_autStab_iff_normalizer
    {D : Type} [Group D] {L : Subgroup D} (hL : L.Normal)
    {L₀ : Type} [Group L₀] (κ : ↥L ≃* L₀)
    (H : Subgroup D) (hHL : H ≤ L) (P : Subgroup L₀) (d : D)
    (hmem : ∀ x : ↥L, κ x ∈ P ↔ (x : D) ∈ H) :
    transportedConj L hL κ d ∈ autStab P ↔
      d ∈ Subgroup.normalizer (H : Set D) := by
  constructor
  · intro hd
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhL : h ∈ L := hHL hh
      have hmemκ : transportedConj L hL κ d (κ ⟨h, hhL⟩) ∈ P :=
        (hd (κ ⟨h, hhL⟩)).mp ((hmem ⟨h, hhL⟩).mpr hh)
      rw [transportedConj_apply] at hmemκ
      exact (hmem ⟨d * h * d⁻¹, hL.conj_mem h hhL d⟩).mp hmemκ
    · intro hh
      have hconjL : d * h * d⁻¹ ∈ L := hHL hh
      have hhL : h ∈ L := by
        have hconj := hL.conj_mem' (d * h * d⁻¹) hconjL d
        rwa [show d⁻¹ * (d * h * d⁻¹) * d = h from by group] at hconj
      have hmemκ : transportedConj L hL κ d (κ ⟨h, hhL⟩) ∈ P := by
        rw [transportedConj_apply]
        exact (hmem ⟨d * h * d⁻¹, hconjL⟩).mpr hh
      exact (hmem ⟨h, hhL⟩).mp ((hd (κ ⟨h, hhL⟩)).mpr hmemκ)
  · intro hd y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := κ.surjective y
      have hxH : (x : D) ∈ H := (hmem x).mp hy
      have hconjH : d * (x : D) * d⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp hd (x : D)).mp hxH
      rw [transportedConj_apply]
      exact (hmem ⟨d * (x : D) * d⁻¹, hHL hconjH⟩).mpr hconjH
    · intro hy
      obtain ⟨x, rfl⟩ := κ.surjective y
      rw [transportedConj_apply] at hy
      have hconjL : d * (x : D) * d⁻¹ ∈ L := hL.conj_mem (x : D) x.2 d
      have hconjH : d * (x : D) * d⁻¹ ∈ H :=
        (hmem ⟨d * (x : D) * d⁻¹, hconjL⟩).mp hy
      exact (hmem x).mpr ((Subgroup.mem_normalizer_iff.mp hd (x : D)).mpr hconjH)

private theorem transportedConj_injective {D : Type} [Group D] {L : Subgroup D}
    (hL : L.Normal) {L₀ : Type} [Group L₀] (κ : ↥L ≃* L₀)
    (hcent : Subgroup.centralizer (L : Set D) = ⊥) :
    Function.Injective (transportedConj L hL κ) := by
  intro d e hde
  have hmem : e⁻¹ * d ∈ Subgroup.centralizer (L : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxκ : transportedConj L hL κ d (κ ⟨x, hx⟩) =
        transportedConj L hL κ e (κ ⟨x, hx⟩) := by rw [hde]
    rw [transportedConj_apply, transportedConj_apply] at hxκ
    have hconj : d * x * d⁻¹ = e * x * e⁻¹ := by
      simpa using congrArg Subtype.val (κ.injective hxκ)
    calc x * (e⁻¹ * d) = e⁻¹ * (e * x * e⁻¹) * d := by group
      _ = e⁻¹ * (d * x * d⁻¹) * d := by rw [hconj]
      _ = (e⁻¹ * d) * x := by group
  rw [hcent] at hmem
  have h1 : e⁻¹ * d = 1 := by simpa using hmem
  calc d = e * (e⁻¹ * d) := by group
    _ = e := by rw [h1, mul_one]

private theorem conj_range_le_transportedConj_range {D : Type} [Group D] {L : Subgroup D}
    (hL : L.Normal) {L₀ : Type} [Group L₀] (κ : ↥L ≃* L₀) :
    (MulAut.conj : L₀ →* MulAut L₀).range ≤ (transportedConj L hL κ).range := by
  rintro φ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := κ.surjective y
  refine ⟨x, ?_⟩
  ext z
  obtain ⟨w, rfl⟩ := κ.surjective z
  rw [transportedConj_apply, MulAut.conj_apply]
  have harg : (⟨(x : D) * (w : D) * (x : D)⁻¹,
      hL.conj_mem (w : D) w.2 (x : D)⟩ : ↥L) = x * w * x⁻¹ := by
    ext
    simp
  rw [harg, map_mul, map_mul, map_inv]

private def rangeCorestrict {A D L₀ : Type} [Group A] [Group D] [Group L₀]
    (ρ : D →* MulAut L₀) (f : A →* D) (K : Subgroup (MulAut L₀)) (H : Subgroup D)
    (hrange : f.range = H) (hK : ∀ d : D, ρ d ∈ K ↔ d ∈ H) :
    A →* ↥(ρ.range ⊓ K) :=
  (ρ.comp f).codRestrict _ fun a =>
    ⟨⟨f a, rfl⟩, (hK (f a)).mpr (by rw [← hrange]; exact ⟨a, rfl⟩)⟩

private theorem rangeCorestrict_bijective {A D L₀ : Type} [Group A] [Group D] [Group L₀]
    (ρ : D →* MulAut L₀) (f : A →* D) (K : Subgroup (MulAut L₀)) (H : Subgroup D)
    (hρinj : Function.Injective ρ) (hfinj : Function.Injective f)
    (hrange : f.range = H) (hK : ∀ d : D, ρ d ∈ K ↔ d ∈ H) :
    Function.Bijective (rangeCorestrict ρ f K H hrange hK) := by
  constructor
  · intro a b hab
    have hab' := congrArg (fun t : ↥(ρ.range ⊓ K) => (t : MulAut L₀)) hab
    change ρ (f a) = ρ (f b) at hab'
    exact hfinj (hρinj hab')
  · intro φ
    obtain ⟨hφM, hφK⟩ := Subgroup.mem_inf.mp φ.2
    obtain ⟨d, hd⟩ := hφM
    have hdH : d ∈ H := (hK d).mp (hd ▸ hφK)
    obtain ⟨a, ha⟩ := (show d ∈ f.range from by rwa [hrange])
    refine ⟨a, ?_⟩
    apply Subtype.ext
    show ρ (f a) = φ.val
    rw [ha, hd]

theorem extensionOfStabilizers : ExtensionOfStabilizers := by
  intro X _ P1 P2 D _ L Du Dv ψ₁ ψ₂ hL hψ1 hψ2 hcomm hrange1 hrange2 hrangeB hcent
    hNDu hNDv hNdiag L₀ _ κ TD hyam
  classical
  let ρ : D →* MulAut L₀ := transportedConj L hL κ
  let P1' : Subgroup L₀ := (Du.subgroupOf L).map κ.toMonoidHom
  let P2' : Subgroup L₀ := (Dv.subgroupOf L).map κ.toMonoidHom
  have hmem1 : ∀ x : ↥L, κ x ∈ P1' ↔ (x : D) ∈ L ⊓ Du := by
    intro x
    change κ x ∈ (Du.subgroupOf L).map κ.toMonoidHom ↔ (x : D) ∈ L ⊓ Du
    rw [mem_map_subgroupOf_map_iff L κ Du x]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hmem2 : ∀ x : ↥L, κ x ∈ P2' ↔ (x : D) ∈ L ⊓ Dv := by
    intro x
    change κ x ∈ (Dv.subgroupOf L).map κ.toMonoidHom ↔ (x : D) ∈ L ⊓ Dv
    rw [mem_map_subgroupOf_map_iff L κ Dv x]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hmemB : ∀ x : ↥L, κ x ∈ P1' ⊓ P2' ↔ (x : D) ∈ L ⊓ Du ⊓ Dv := by
    intro x
    change κ x ∈ (Du.subgroupOf L).map κ.toMonoidHom ⊓
        (Dv.subgroupOf L).map κ.toMonoidHom ↔ (x : D) ∈ L ⊓ Du ⊓ Dv
    rw [Subgroup.mem_inf, mem_map_subgroupOf_map_iff L κ Du x,
      mem_map_subgroupOf_map_iff L κ Dv x, Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨⟨x.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  have hstab1 : ∀ d : D, ρ d ∈ autStab P1' ↔ d ∈ Du := by
    intro d
    have h := transportedConj_mem_autStab_iff_normalizer hL κ (L ⊓ Du) inf_le_left
      P1' d hmem1
    rw [hNDu] at h
    simpa [ρ] using h
  have hstab2 : ∀ d : D, ρ d ∈ autStab P2' ↔ d ∈ Dv := by
    intro d
    have h := transportedConj_mem_autStab_iff_normalizer hL κ (L ⊓ Dv) inf_le_left
      P2' d hmem2
    rw [hNDv] at h
    simpa [ρ] using h
  have hstabB : ∀ d : D,
      ρ d ∈ autStab (P1' ⊓ P2') → d ∈ Subgroup.normalizer
        ((L ⊓ Du ⊓ Dv : Subgroup D) : Set D) := by
    intro d
    have h := transportedConj_mem_autStab_iff_normalizer hL κ (L ⊓ Du ⊓ Dv)
      (fun x hx => hx.1.1) (P1' ⊓ P2') d hmemB
    simpa [ρ] using h.mp
  have hρ_inj : Function.Injective ρ := by
    simpa [ρ] using transportedConj_injective (L := L) hL κ hcent
  have hinn : (MulAut.conj : L₀ →* MulAut L₀).range ≤ ρ.range := by
    simpa [ρ] using conj_range_le_transportedConj_range (L := L) hL κ
  have hdiag : ∀ φ ∈ ρ.range, φ ∈ autStab (P1' ⊓ P2') → φ ∈ autStab P1' := by
    intro φ hφ hφB
    obtain ⟨d, rfl⟩ := hφ
    exact (hstab1 d).mpr (hNdiag (hstabB d hφB))
  let φ1h : ↥P1 →* ↥(ρ.range ⊓ autStab P1') :=
    rangeCorestrict ρ ψ₁ (autStab P1') Du hrange1 hstab1
  have hφ1_bij : Function.Bijective φ1h := by
    simpa [φ1h] using rangeCorestrict_bijective ρ ψ₁ (autStab P1') Du hρ_inj hψ1
      hrange1 hstab1
  let φ2h : ↥P2 →* ↥(ρ.range ⊓ autStab P2') :=
    rangeCorestrict ρ ψ₂ (autStab P2') Dv hrange2 hstab2
  have hφ2_bij : Function.Bijective φ2h := by
    simpa [φ2h] using rangeCorestrict_bijective ρ ψ₂ (autStab P2') Dv hρ_inj hψ2
      hrange2 hstab2
  have hmidK : ∀ d : D, ρ d ∈ autStab P1' ⊓ autStab P2' ↔ d ∈ Du ⊓ Dv := by
    intro d
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨(hstab1 d).mp h.1, (hstab2 d).mp h.2⟩,
      fun h => ⟨(hstab1 d).mpr h.1, (hstab2 d).mpr h.2⟩⟩
  have hpsiBinj : Function.Injective (psiB P2 ψ₁) :=
    hψ1.comp (Subgroup.inclusion_injective (inf_le_left : P1 ⊓ P2 ≤ P1))
  let φ12h : ↥(P1 ⊓ P2) →*
      ↥(ρ.range ⊓ (autStab P1' ⊓ autStab P2')) :=
    rangeCorestrict ρ (psiB P2 ψ₁) (autStab P1' ⊓ autStab P2') (Du ⊓ Dv)
      hrangeB hmidK
  have hφ12_bij : Function.Bijective φ12h := by
    simpa [φ12h] using rangeCorestrict_bijective ρ (psiB P2 ψ₁)
      (autStab P1' ⊓ autStab P2') (Du ⊓ Dv) hρ_inj hpsiBinj hrangeB hmidK
  have htarget : ρ.range ⊓ (autStab P1' ⊓ autStab P2') =
      (ρ.range ⊓ autStab P1') ⊓ (ρ.range ⊓ autStab P2') := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  let φ1 : ↥P1 ≃* ↥(ρ.range ⊓ autStab P1') := MulEquiv.ofBijective φ1h hφ1_bij
  let φ2 : ↥P2 ≃* ↥(ρ.range ⊓ autStab P2') := MulEquiv.ofBijective φ2h hφ2_bij
  let φ12 : ↥(P1 ⊓ P2) ≃*
      ↥((ρ.range ⊓ autStab P1') ⊓ (ρ.range ⊓ autStab P2')) :=
    (MulEquiv.ofBijective φ12h hφ12_bij).trans (MulEquiv.subgroupCongr htarget)
  refine ⟨ρ.range, TD, P1', P2', hinn, by simpa [P1', P2'] using hyam, hdiag, ?_⟩
  refine ⟨⟨φ1, φ12, φ2, ?_, ?_⟩⟩
  · intro g
    apply Subtype.ext
    change ((MulEquiv.subgroupCongr htarget) (φ12h g) : MulAut L₀) =
      (φ1h (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) g) : MulAut L₀)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  · intro g
    apply Subtype.ext
    change ((MulEquiv.subgroupCongr htarget) (φ12h g) : MulAut L₀) =
      (φ2h (Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2) g) : MulAut L₀)
    rw [MulEquiv.subgroupCongr_apply]
    exact congrArg ρ (hcomm g)

end CFSG.Quasithin.Stroth
