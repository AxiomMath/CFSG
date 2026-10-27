module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CoreK
public import CFSG.LocalAnalysis.WeakClosure81.W183B2TrQ
import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits (IsInv isIrreducible_iff)

private lemma w183b2_quad_of_span {F K G W Q : Type*} [Field F] [Field K] [Group G]
    [AddCommGroup W] [Module F W] [AddCommGroup Q] [Module K Q]
    {ρ : Representation F G W} {σ : Representation K G Q} {ψ : W →+ Q}
    (hψ : ∀ (g : G) (w : W), ψ (ρ g w) = σ g (ψ w))
    (hspan : Submodule.span K (Set.range ψ) = ⊤)
    {d d' : G} (h : ∀ w : W, ρ d (ρ d' w - w) = ρ d' w - w) :
    ∀ q : Q, σ d (σ d' q - q) = σ d' q - q := by
  have hle : Submodule.span K (Set.range ψ) ≤ LinearMap.ker ((σ d - 1) * (σ d' - 1)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.sub_apply, Module.End.one_apply]
    rw [← hψ d' w]
    have hx : ψ (ρ d' w) - ψ w = ψ (ρ d' w - w) := (map_sub ψ _ _).symm
    rw [hx, ← hψ d (ρ d' w - w), h w, sub_self]
  intro q
  have hq : q ∈ LinearMap.ker ((σ d - 1) * (σ d' - 1)) :=
    hle (by rw [hspan]; exact Submodule.mem_top)
  have h0 := LinearMap.mem_ker.mp hq
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.sub_apply, Module.End.one_apply] at h0
  exact sub_eq_zero.mp h0

private lemma w183b2_mem_asGroupHom_ker_iff {K : Type*} [Field K] {G : Type} [Group G]
    {Q : Type} [AddCommGroup Q] [Module K Q] {σ : Representation K G Q} {x : G} :
    x ∈ σ.asGroupHom.ker ↔ σ x = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp [Representation.asGroupHom_apply]

private lemma w183b2_central_kernel {K : Type*} [Field K] {G : Type} [Group G] {Q : Type}
    [AddCommGroup Q] [Module K Q] {σ : Representation K G Q} {H : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥H) (hnt : ∃ a ∈ H, ∃ q : Q, σ a q ≠ q) :
    ∀ a ∈ H, (∀ q : Q, σ a q = q) → a ∈ W183K3.quasiCentre H := by
  let σH : Representation K ↥H Q := σ.comp H.subtype
  let N : Subgroup ↥H := σH.asGroupHom.ker
  have hNtop : N ≠ ⊤ := by
    intro htop
    obtain ⟨a, ha, q, hq⟩ := hnt
    have hmem : (⟨a, ha⟩ : ↥H) ∈ N := by rw [htop]; trivial
    have h1 : σH (⟨a, ha⟩ : ↥H) = 1 := (w183b2_mem_asGroupHom_ker_iff).mp hmem
    refine hq ?_
    have := congrArg (fun F : Q →ₗ[K] Q => F q) h1
    simpa [σH] using this
  haveI : N.Normal := MonoidHom.normal_ker σH.asGroupHom
  have hNc : N ≤ Subgroup.center ↥H :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq N hNtop
  intro a ha hfix
  have hmem : (⟨a, ha⟩ : ↥H) ∈ N :=
    (w183b2_mem_asGroupHom_ker_iff (σ := σH)).mpr (by
      change σ a = 1
      exact LinearMap.ext hfix)
  exact Subgroup.mem_map.mpr ⟨_, hNc hmem, rfl⟩

private lemma w183b2_span_diff_isInv {F : Type*} [Field F] {G : Type} [Group G] {W : Type*}
    [AddCommGroup W] [Module F W] {ρ : Representation F G W} {H M Δ : Subgroup G}
    (hgen : H ⊔ M ⊔ Δ = ⊤) (hcomm : ∀ a ∈ H, ∀ b ∈ M, a * b = b * a)
    (hnorm : ∀ d ∈ Δ, ∀ a ∈ H, d * a * d⁻¹ ∈ H) :
    IsInv ρ (Submodule.span F {x : W | ∃ a ∈ H, ∃ w : W, x = ρ a w - w}) := by
  let C : Submodule F W := Submodule.span F {x : W | ∃ a ∈ H, ∃ w : W, x = ρ a w - w}
  have hH : ∀ g ∈ H, ∀ x ∈ C, ρ g x ∈ C := by
    intro g hg x hx
    have hle : C ≤ C.comap (ρ g) := by
      rw [Submodule.span_le]
      rintro y ⟨a, ha, w, rfl⟩
      refine Submodule.mem_comap.mpr ?_
      have h1 : ρ g (ρ a w) = ρ (g * a) w := by
        change (ρ g * ρ a) w = ρ (g * a) w
        rw [← map_mul]
      have h2 : ρ (g * a * g⁻¹) (ρ g w) = ρ (g * a) w := by
        change (ρ (g * a * g⁻¹) * ρ g) w = ρ (g * a) w
        rw [← map_mul, show (g * a * g⁻¹) * g = g * a from by group]
      have hconj : ρ g (ρ a w - w) = ρ (g * a * g⁻¹) (ρ g w) - ρ g w := by
        rw [map_sub, h1, h2]
      rw [hconj]
      exact Submodule.subset_span ⟨g * a * g⁻¹, H.mul_mem (H.mul_mem hg ha) (H.inv_mem hg),
        ρ g w, rfl⟩
    exact Submodule.mem_comap.mp (hle hx)
  have hM : ∀ g ∈ M, ∀ x ∈ C, ρ g x ∈ C := by
    intro g hg x hx
    have hle : C ≤ C.comap (ρ g) := by
      rw [Submodule.span_le]
      rintro y ⟨a, ha, w, rfl⟩
      refine Submodule.mem_comap.mpr ?_
      have hcomm' : ρ g * ρ a = ρ a * ρ g := by
        rw [← map_mul, ← map_mul, hcomm a ha g hg]
      have h1 : ρ g (ρ a w) = ρ a (ρ g w) := by
        change (ρ g * ρ a) w = (ρ a * ρ g) w
        rw [hcomm']
      have hconj : ρ g (ρ a w - w) = ρ a (ρ g w) - ρ g w := by
        rw [map_sub, h1]
      rw [hconj]
      exact Submodule.subset_span ⟨a, ha, ρ g w, rfl⟩
    exact Submodule.mem_comap.mp (hle hx)
  have hΔ : ∀ g ∈ Δ, ∀ x ∈ C, ρ g x ∈ C := by
    intro g hg x hx
    have hle : C ≤ C.comap (ρ g) := by
      rw [Submodule.span_le]
      rintro y ⟨a, ha, w, rfl⟩
      refine Submodule.mem_comap.mpr ?_
      have h1 : ρ g (ρ a w) = ρ (g * a) w := by
        change (ρ g * ρ a) w = ρ (g * a) w
        rw [← map_mul]
      have h2 : ρ (g * a * g⁻¹) (ρ g w) = ρ (g * a) w := by
        change (ρ (g * a * g⁻¹) * ρ g) w = ρ (g * a) w
        rw [← map_mul, show (g * a * g⁻¹) * g = g * a from by group]
      have hconj : ρ g (ρ a w - w) = ρ (g * a * g⁻¹) (ρ g w) - ρ g w := by
        rw [map_sub, h1, h2]
      rw [hconj]
      exact Submodule.subset_span ⟨g * a * g⁻¹, hnorm g hg a ha, ρ g w, rfl⟩
    exact Submodule.mem_comap.mp (hle hx)
  let St : Subgroup G :=
    { carrier := {g | ∀ x ∈ C, ρ g x ∈ C ∧ ρ g⁻¹ x ∈ C}
      mul_mem' := fun {g g'} hg hg' u hu => by
        refine ⟨?_, ?_⟩
        · rw [map_mul, Module.End.mul_apply]
          exact (hg _ ((hg' u hu).1)).1
        · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact (hg' _ ((hg u hu).2)).2
      one_mem' := fun u hu => by simpa using hu
      inv_mem' := fun {g} hg u hu => by simpa using (hg u hu).symm }
  have hHSt : H ≤ St := fun g hg x hx => ⟨hH g hg x hx, hH g⁻¹ (H.inv_mem hg) x hx⟩
  have hMSt : M ≤ St := fun g hg x hx => ⟨hM g hg x hx, hM g⁻¹ (M.inv_mem hg) x hx⟩
  have hΔSt : Δ ≤ St := fun g hg x hx => ⟨hΔ g hg x hx, hΔ g⁻¹ (Δ.inv_mem hg) x hx⟩
  have hSttop : St = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le hHSt hMSt) hΔSt
  intro g x hx
  have hg : g ∈ St := by rw [hSttop]; trivial
  exact (hg x hx).1

theorem w183b2_no_mixed_abstract_of_quasi {G : Type} [Group G] [Finite G]
    {A₁ A₂ Δ : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hirr : ρ.IsIrreducible)
    (hgen : A₁ ⊔ A₂ ⊔ Δ = ⊤) (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hn₁ : ∀ d ∈ Δ, ∀ a ∈ A₁, d * a * d⁻¹ ∈ A₁) (hn₂ : ∀ d ∈ Δ, ∀ b ∈ A₂, d * b * d⁻¹ ∈ A₂)
    (helem : IsElemAbelian 2 Δ)
    (hquad : ∀ d ∈ Δ, ∀ d' ∈ Δ, ∀ w : W, ρ d (ρ d' w - w) = ρ d' w - w)
    (hq₁ : CFSG.Open.IsQuasisimple ↥A₁) (hq₂ : CFSG.Open.IsQuasisimple ↥A₂)
    (hnt₁ : ∃ a ∈ A₁, ∃ w : W, ρ a w ≠ w) (hnt₂ : ∃ b ∈ A₂, ∃ w : W, ρ b w ≠ w)
    (hcent : ∀ d ∈ Δ, (∀ a ∈ A₁, d * a = a * d) → (∀ b ∈ A₂, d * b = b * d) → d = 1)
    (htwo₁ : ¬ Δ ≤ Subgroup.centralizer (A₂ : Set G))
    (htwo₂ : ¬ Δ ≤ Subgroup.centralizer (A₁ : Set G)) (hAbs : AbsIrrOverF4 ↥A₁) :
    Nat.card ↥Δ ≤ 4 := by
  obtain ⟨hWnt, honly⟩ := (isIrreducible_iff ρ).1 hirr
  haveI : Nontrivial W := hWnt
  obtain ⟨Q, hQadd, hQmod, hQfd, σ, ψ, hσ, hψ, hspan⟩ := w183b2_exists_irr_quotient ρ
  letI : Module (ZMod 2) Q :=
    Module.compHom Q (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
  have hntriv₁ : ∃ a ∈ A₁, ∃ q : Q, σ a q ≠ q := by
    by_contra hcon
    have htriv : ∀ a ∈ A₁, ∀ q : Q, σ a q = q := by
      intro a ha q
      by_contra hq
      exact hcon ⟨a, ha, q, hq⟩
    let S : Set W := {x : W | ∃ a ∈ A₁, ∃ w : W, x = ρ a w - w}
    let C : Submodule (ZMod 2) W := Submodule.span (ZMod 2) S
    have hCinv : IsInv ρ C := w183b2_span_diff_isInv (H := A₁) (M := A₂) hgen hcomm hn₁
    have hCne : C ≠ ⊥ := by
      intro hbot
      obtain ⟨a, ha, w, hne⟩ := hnt₁
      have hmem : ρ a w - w ∈ C := Submodule.subset_span ⟨a, ha, w, rfl⟩
      rw [hbot] at hmem
      exact sub_ne_zero.mpr hne ((Submodule.mem_bot (ZMod 2)).mp hmem)
    have hCtop : C = ⊤ := (honly C hCinv).resolve_left hCne
    let ψₗ : W →ₗ[ZMod 2] Q := ψ.toZModLinearMap 2
    have hker : C ≤ LinearMap.ker ψₗ := by
      rw [Submodule.span_le]
      rintro y ⟨a, ha, w, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      change ψ (ρ a w - w) = 0
      rw [map_sub, hψ a w, htriv a ha (ψ w), sub_self]
    have hzero : ∀ x : W, ψ x = 0 := by
      intro x
      have : x ∈ LinearMap.ker ψₗ := hker (by rw [hCtop]; trivial)
      have hx := LinearMap.mem_ker.mp this
      simpa [ψₗ] using hx
    have hspan_bot : Submodule.span (AlgebraicClosure (ZMod 2)) (Set.range ψ) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact hzero x
    obtain ⟨q₁, q₂, hne⟩ := ((isIrreducible_iff σ).1 hσ).1
    have hbot : (⊥ : Submodule (AlgebraicClosure (ZMod 2)) Q) = ⊤ := by
      rw [← hspan_bot, hspan]
    have hq₁ : q₁ = 0 :=
      (Submodule.mem_bot (AlgebraicClosure (ZMod 2))).mp (hbot ▸ Submodule.mem_top)
    have hq₂ : q₂ = 0 :=
      (Submodule.mem_bot (AlgebraicClosure (ZMod 2))).mp (hbot ▸ Submodule.mem_top)
    exact hne (hq₁.trans hq₂.symm)
  have hntriv₂ : ∃ b ∈ A₂, ∃ q : Q, σ b q ≠ q := by
    by_contra hcon
    have htriv : ∀ b ∈ A₂, ∀ q : Q, σ b q = q := by
      intro b hb q
      by_contra hq
      exact hcon ⟨b, hb, q, hq⟩
    let S : Set W := {x : W | ∃ b ∈ A₂, ∃ w : W, x = ρ b w - w}
    let C : Submodule (ZMod 2) W := Submodule.span (ZMod 2) S
    have hgen' : A₂ ⊔ A₁ ⊔ Δ = ⊤ := by rw [sup_comm A₂ A₁]; exact hgen
    have hcomm' : ∀ a ∈ A₂, ∀ b ∈ A₁, a * b = b * a :=
      fun a ha b hb => (hcomm b hb a ha).symm
    have hCinv : IsInv ρ C :=
      w183b2_span_diff_isInv (H := A₂) (M := A₁) hgen' hcomm' hn₂
    have hCne : C ≠ ⊥ := by
      intro hbot
      obtain ⟨b, hb, w, hne⟩ := hnt₂
      have hmem : ρ b w - w ∈ C := Submodule.subset_span ⟨b, hb, w, rfl⟩
      rw [hbot] at hmem
      exact sub_ne_zero.mpr hne ((Submodule.mem_bot (ZMod 2)).mp hmem)
    have hCtop : C = ⊤ := (honly C hCinv).resolve_left hCne
    let ψₗ : W →ₗ[ZMod 2] Q := ψ.toZModLinearMap 2
    have hker : C ≤ LinearMap.ker ψₗ := by
      rw [Submodule.span_le]
      rintro y ⟨b, hb, w, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      change ψ (ρ b w - w) = 0
      rw [map_sub, hψ b w, htriv b hb (ψ w), sub_self]
    have hzero : ∀ x : W, ψ x = 0 := by
      intro x
      have : x ∈ LinearMap.ker ψₗ := hker (by rw [hCtop]; trivial)
      have hx := LinearMap.mem_ker.mp this
      simpa [ψₗ] using hx
    have hspan_bot : Submodule.span (AlgebraicClosure (ZMod 2)) (Set.range ψ) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact hzero x
    obtain ⟨q₁, q₂, hne⟩ := ((isIrreducible_iff σ).1 hσ).1
    have hbot : (⊥ : Submodule (AlgebraicClosure (ZMod 2)) Q) = ⊤ := by
      rw [← hspan_bot, hspan]
    have hq₁ : q₁ = 0 :=
      (Submodule.mem_bot (AlgebraicClosure (ZMod 2))).mp (hbot ▸ Submodule.mem_top)
    have hq₂ : q₂ = 0 :=
      (Submodule.mem_bot (AlgebraicClosure (ZMod 2))).mp (hbot ▸ Submodule.mem_top)
    exact hne (hq₁.trans hq₂.symm)
  have hquad' : ∀ d ∈ Δ, ∀ d' ∈ Δ, ∀ q : Q, σ d (σ d' q - q) = σ d' q - q :=
    fun d hd d' hd' => w183b2_quad_of_span hψ hspan (hquad d hd d' hd')
  have hcen₁ := w183b2_central_kernel (σ := σ) (H := A₁) hq₁ hntriv₁
  have hcen₂ := w183b2_central_kernel (σ := σ) (H := A₂) hq₂ hntriv₂
  have hfaith : ∀ d ∈ Δ, (∀ q : Q, σ d q = q) → d = 1 := by
    intro d hd hfix
    have hd1 : σ d = 1 := LinearMap.ext hfix
    have hdinv : σ d⁻¹ = 1 := by
      have h := map_mul σ d⁻¹ d
      rw [inv_mul_cancel, map_one, hd1, mul_one] at h
      exact h.symm
    have hfix₁ : ∀ a ∈ A₁, d * a = a * d := by
      have hc : ∀ a ∈ A₁, d * a * d⁻¹ * a⁻¹ ∈ W183K3.quasiCentre A₁ := by
        intro a ha
        have hcA : d * a * d⁻¹ * a⁻¹ ∈ A₁ := A₁.mul_mem (hn₁ d hd a ha) (A₁.inv_mem ha)
        have haa : σ a * σ a⁻¹ = 1 := by
          have h := map_mul σ a a⁻¹
          rw [mul_inv_cancel, map_one] at h
          exact h.symm
        have hc1 : σ (d * a * d⁻¹ * a⁻¹) = 1 := by
          calc σ (d * a * d⁻¹ * a⁻¹)
              = σ d * σ a * σ d⁻¹ * σ a⁻¹ := by rw [map_mul, map_mul, map_mul]
            _ = 1 := by rw [hd1, hdinv, one_mul, mul_one, haa]
        exact hcen₁ _ hcA (fun q => by rw [hc1]; rfl)
      exact W183K3.quasi_comm_of_comm_mod_centre hq₁ (hn₁ d hd) hc
    have hfix₂ : ∀ b ∈ A₂, d * b = b * d := by
      have hc : ∀ b ∈ A₂, d * b * d⁻¹ * b⁻¹ ∈ W183K3.quasiCentre A₂ := by
        intro b hb
        have hcA : d * b * d⁻¹ * b⁻¹ ∈ A₂ := A₂.mul_mem (hn₂ d hd b hb) (A₂.inv_mem hb)
        have hbb : σ b * σ b⁻¹ = 1 := by
          have h := map_mul σ b b⁻¹
          rw [mul_inv_cancel, map_one] at h
          exact h.symm
        have hc1 : σ (d * b * d⁻¹ * b⁻¹) = 1 := by
          calc σ (d * b * d⁻¹ * b⁻¹)
              = σ d * σ b * σ d⁻¹ * σ b⁻¹ := by rw [map_mul, map_mul, map_mul]
            _ = 1 := by rw [hd1, hdinv, one_mul, mul_one, hbb]
        exact hcen₂ _ hcA (fun q => by rw [hc1]; rfl)
      exact W183K3.quasi_comm_of_comm_mod_centre hq₂ (hn₂ d hd) hc
    exact hcent d hd hfix₁ hfix₂
  have hsetting : CoreSetting σ A₁ A₂ Δ :=
    { irr := hσ
      gen := hgen
      comm := hcomm
      norm₁ := hn₁
      norm₂ := hn₂
      elem := helem
      quad := hquad'
      faith := hfaith
      quasi₁ := hq₁
      quasi₂ := hq₂
      nontriv₁ := hntriv₁
      nontriv₂ := hntriv₂
      two₁ := htwo₁
      two₂ := htwo₂ }
  exact w183b2_core_k_of_abs hsetting hAbs

end CFSG.LocalAnalysis.WeakClosure81

end
