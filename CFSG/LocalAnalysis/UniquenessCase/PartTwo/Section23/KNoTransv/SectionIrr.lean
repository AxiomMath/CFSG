module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.SectionDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesDef
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OutcomeLocal

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

private theorem mem_secP_self (X : Subgroup 𝔾) (a : M) : a ∈ secP X a :=
  Submodule.subset_span ⟨1, X.one_mem, rfl⟩

private theorem mem_secP_map {X : Subgroup 𝔾} {a : M} {g : 𝔾} (hg : g ∈ X) {v : M}
    (hv : v ∈ secP X a) : (g : M →ₗ[ZMod 2] M) v ∈ secP X a :=
  ((le_stab_secP X a hg) v).2 hv

private theorem mem_secQ_map_iff {X : Subgroup 𝔾} {φ : Module.Dual (ZMod 2) M} {g : 𝔾}
    (hg : g ∈ X) (v : M) : (g : M →ₗ[ZMod 2] M) v ∈ secQ X φ ↔ v ∈ secQ X φ :=
  (le_stab_secQ X φ hg) v

private theorem exists_apply_of_not_mem_secQ {X : Subgroup 𝔾}
    {φ : Module.Dual (ZMod 2) M} {a : M} (haQ : a ∉ secQ X φ) :
    ∃ h ∈ X, φ ((h : M →ₗ[ZMod 2] M) a) ≠ 0 := by
  by_contra h
  apply haQ
  intro g hg
  by_contra hne
  exact h ⟨g, hg, hne⟩

private theorem conjClosure_le_self {X : Subgroup 𝔾} {τ : 𝔾} (hτX : τ ∈ X) :
    conjClosure X τ ≤ X := by
  rw [conjClosure, Subgroup.closure_le]
  rintro y ⟨g, hg, rfl⟩
  exact X.mul_mem (X.mul_mem (X.inv_mem hg) hτX) hg

private theorem secRho_tv_eq_one_of_mem_secQ {X : Subgroup 𝔾}
    {φ : Module.Dual (ZMod 2) M} {a : M} (hφa : φ a = 0)
    (hτX : tv φ a hφa ∈ X) (haQ : a ∈ secQ X φ) :
    secRho X φ a ⟨tv φ a hφa, hτX⟩ = 1 := by
  apply tv_ext
  intro w
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective
    ((secQ X φ).comap (secP X a).subtype) w
  rw [i285_one_apply, secRho, i285_secHom_mk, Submodule.Quotient.eq]
  change (tv φ a hφa : M →ₗ[ZMod 2] M) v - v ∈ secQ X φ
  rw [tv_apply, add_sub_cancel_left]
  exact (secQ X φ).smul_mem _ haQ

private theorem pow_four_of_secRho_tv_eq_one [Finite M] {X : Subgroup 𝔾}
    {φ : Module.Dual (ZMod 2) M} {a : M} (hφa : φ a = 0)
    (hτX : tv φ a hφa ∈ X) (hgen : X ≤ conjClosure X (tv φ a hφa))
    (h1 : secRho X φ a ⟨tv φ a hφa, hτX⟩ = 1) : ∀ x ∈ X, x ^ 4 = 1 := by
  have hker : conjClosure X (tv φ a hφa) ≤ (secRho X φ a).ker.map X.subtype := by
    rw [conjClosure, Subgroup.closure_le]
    rintro y ⟨g, hg, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨g⁻¹ * tv φ a hφa * g, ?_⟩, ?_, rfl⟩
    · exact X.mul_mem (X.mul_mem (X.inv_mem hg) hτX) hg
    · rw [MonoidHom.mem_ker]
      have hconj : (⟨g⁻¹ * tv φ a hφa * g,
          X.mul_mem (X.mul_mem (X.inv_mem hg) hτX) hg⟩ : ↥X) =
          ⟨g, hg⟩⁻¹ * ⟨tv φ a hφa, hτX⟩ * ⟨g, hg⟩ := Subtype.ext rfl
      rw [hconj, map_mul, map_mul, map_inv, h1]
      group
  intro x hx
  obtain ⟨y, hyker, hyx⟩ := hker (hgen hx)
  have hxy : y = ⟨x, hx⟩ := Subtype.ext (by simpa using hyx)
  have hxker : (⟨x, hx⟩ : ↥X) ∈ (secRho X φ a).ker := hxy ▸ hyker
  have h4 := pow_four_of_mem_ker_secRho hφa hgen hxker
  simpa using h4

private theorem secRho_tv_ne_one [Finite M] {X : Subgroup 𝔾}
    {φ : Module.Dual (ZMod 2) M} {a : M} (hφa : φ a = 0)
    (hτX : tv φ a hφa ∈ X) (hgen : X ≤ conjClosure X (tv φ a hφa))
    (hX4 : ∃ x ∈ X, x ^ 4 ≠ 1) :
    secRho X φ a ⟨tv φ a hφa, hτX⟩ ≠ 1 := by
  intro h1
  obtain ⟨x, hx, hx4⟩ := hX4
  exact hx4 (pow_four_of_secRho_tv_eq_one hφa hτX hgen h1 x hx)

private theorem secRho_conj_isTransvection {X : Subgroup 𝔾} {φ : Module.Dual (ZMod 2) M}
    {a : M} (hφa : φ a = 0) (hτX : tv φ a hφa ∈ X) (haQ : a ∉ secQ X φ)
    {g : 𝔾} (hg : g ∈ X) (hdX : g⁻¹ * tv φ a hφa * g ∈ X) :
    IsF2Transvection (secRho X φ a ⟨g⁻¹ * tv φ a hφa * g, hdX⟩) := by
  let P : Submodule (ZMod 2) M := secP X a
  let V := ↥P ⧸ (secQ X φ).comap P.subtype
  have haP : a ∈ P := mem_secP_self X a
  have hα : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a ∈ P := mem_secP_map (X.inv_mem hg) haP
  let abar : V := Submodule.Quotient.mk ⟨_, hα⟩
  have hact : ∀ v : ↥P,
      (secRho X φ a ⟨g⁻¹ * tv φ a hφa * g, hdX⟩ : V →ₗ[ZMod 2] V)
        (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk v + φ ((g : M →ₗ[ZMod 2] M) v) • abar := by
    intro v
    rw [secRho, i285_secHom_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    change ((g⁻¹ * tv φ a hφa * g : 𝔾) : M →ₗ[ZMod 2] M) v =
      v + φ ((g : M →ₗ[ZMod 2] M) v) • ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a
    rw [i285_mul_apply, i285_mul_apply, tv_apply, map_add, map_smul, i285_inv_apply_apply]
  have hane : abar ≠ 0 := by
    change Submodule.Quotient.mk (p := (secQ X φ).comap P.subtype) ⟨_, hα⟩ ≠ 0
    intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a ∈ secQ X φ := h0
    have hga : (g : M →ₗ[ZMod 2] M) (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a) ∈ secQ X φ :=
      (mem_secQ_map_iff hg _).2 hmem
    rw [i285_apply_inv_apply] at hga
    exact haQ hga
  have hex : ∃ v : ↥P, φ ((g : M →ₗ[ZMod 2] M) v) = 1 := by
    obtain ⟨h, hh, hhne⟩ := exists_apply_of_not_mem_secQ haQ
    have hmem : ((h : M →ₗ[ZMod 2] M) a) ∈ P := mem_secP_map hh haP
    have hmem' : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) (((h : M →ₗ[ZMod 2] M) a)) ∈ P :=
      mem_secP_map (X.inv_mem hg) hmem
    refine ⟨⟨_, hmem'⟩, ?_⟩
    rw [i285_apply_inv_apply]
    rcases zmod2_eq_zero_or_one (φ ((h : M →ₗ[ZMod 2] M) a)) with h0 | h1
    · exact absurd h0 hhne
    · exact h1
  have hcomm : commutatorSpace (secRho X φ a ⟨g⁻¹ * tv φ a hφa * g, hdX⟩) =
      Submodule.span (ZMod 2) {abar} := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective
        ((secQ X φ).comap P.subtype) w
      change Submodule.Quotient.mk v +
        (secRho X φ a ⟨g⁻¹ * tv φ a hφa * g, hdX⟩ : V →ₗ[ZMod 2] V)
          (Submodule.Quotient.mk v) ∈ Submodule.span (ZMod 2) {abar}
      rw [hact]
      have hz : Submodule.Quotient.mk v +
          (Submodule.Quotient.mk v + φ ((g : M →ₗ[ZMod 2] M) v) • abar) =
          φ ((g : M →ₗ[ZMod 2] M) v) • abar := by
        rw [← add_assoc, zmod2_add_self, zero_add]
      rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self abar)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨v, hv⟩ := hex
      refine ⟨Submodule.Quotient.mk v, ?_⟩
      change Submodule.Quotient.mk v +
        (secRho X φ a ⟨g⁻¹ * tv φ a hφa * g, hdX⟩ : V →ₗ[ZMod 2] V)
          (Submodule.Quotient.mk v) = abar
      rw [hact, hv]
      rw [← add_assoc, zmod2_add_self, zero_add, one_smul]
  refine ⟨?_, ?_⟩
  · intro h1
    obtain ⟨v, hv⟩ := hex
    have h := hact v
    rw [h1, i285_one_apply, hv, one_smul] at h
    have h' : (0 : V) = abar := by
      have h2 := congrArg (fun y => Submodule.Quotient.mk v + y) h
      rwa [← add_assoc, zmod2_add_self, zero_add] at h2
    exact hane h'.symm
  · rw [hcomm, finrank_span_singleton hane]

private theorem secRho_range {X : Subgroup 𝔾} {φ : Module.Dual (ZMod 2) M} {a : M}
    (hφa : φ a = 0) (hτX : tv φ a hφa ∈ X) (hgen : X ≤ conjClosure X (tv φ a hφa)) :
    (secRho X φ a).range = Subgroup.closure ((secRho X φ a) ''
      (Subtype.val ⁻¹' {x : 𝔾 | ∃ g ∈ X, x = g⁻¹ * tv φ a hφa * g})) := by
  let U : Set 𝔾 := {x | ∃ g ∈ X, x = g⁻¹ * tv φ a hφa * g}
  have hclosure : Subgroup.closure U = X := le_antisymm (conjClosure_le_self hτX) hgen
  have hUmap : X.subtype '' (Subtype.val ⁻¹' U) = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hclosure ▸ (Subgroup.subset_closure (k := U) hy)⟩, hy, rfl⟩
  have hmap : Subgroup.map X.subtype (Subgroup.closure (Subtype.val ⁻¹' U)) = X := by
    rw [MonoidHom.map_closure, hUmap, hclosure]
  have hmaptop : Subgroup.map X.subtype (⊤ : Subgroup ↥X) = X := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have htop : (⊤ : Subgroup ↥X) = Subgroup.closure (Subtype.val ⁻¹' U) :=
    Subgroup.map_injective X.subtype_injective (by rw [hmaptop, hmap])
  calc (secRho X φ a).range = Subgroup.map (secRho X φ a) ⊤ :=
        MonoidHom.range_eq_map _
    _ = Subgroup.map (secRho X φ a) (Subgroup.closure (Subtype.val ⁻¹' U)) := by rw [htop]
    _ = Subgroup.closure ((secRho X φ a) '' (Subtype.val ⁻¹' U)) := MonoidHom.map_closure _ _

private theorem secRho_irred {X : Subgroup 𝔾} {φ : Module.Dual (ZMod 2) M} {a : M}
    (hφa : φ a = 0) (hτX : tv φ a hφa ∈ X)
    (W : Submodule (ZMod 2) (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype))
    (hW : ∀ g ∈ (secRho X φ a).range, ∀ w ∈ W,
      (g : (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype) →ₗ[ZMod 2]
        (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype)) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let Z : Submodule (ZMod 2) ↥(secP X a) := (secQ X φ).comap (secP X a).subtype
  let T : Submodule (ZMod 2) M := (W.comap Z.mkQ).map (secP X a).subtype
  have hmemT : ∀ v : ↥(secP X a), ((v : M) ∈ T ↔ Z.mkQ v ∈ W) := by
    intro v
    constructor
    · rintro ⟨y, hy, hyv⟩
      have hyv' : y = v := Subtype.ext hyv
      rwa [hyv'] at hy
    · intro h
      exact ⟨v, h, rfl⟩
  have hTP : T ≤ secP X a := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPQT : secP X a ⊓ secQ X φ ≤ T := by
    intro v hv
    have hvP : v ∈ secP X a := hv.1
    refine (hmemT ⟨v, hvP⟩).2 ?_
    have hz : Z.mkQ (⟨v, hvP⟩ : ↥(secP X a)) = 0 := by
      change Submodule.Quotient.mk (p := Z) (⟨v, hvP⟩ : ↥(secP X a)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hv.2
    rw [hz]
    exact W.zero_mem
  have hTX : X ≤ i285_stab T := by
    apply i285_le_stab
    intro x hx v hv
    have hvP : v ∈ secP X a := hTP hv
    refine (hmemT ⟨(x : M →ₗ[ZMod 2] M) v, mem_secP_map hx hvP⟩).2 ?_
    have hWmem : Z.mkQ (⟨v, hvP⟩ : ↥(secP X a)) ∈ W := (hmemT ⟨v, hvP⟩).1 hv
    have hxW := hW (secRho X φ a ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ (Z.mkQ ⟨v, hvP⟩) hWmem
    simpa only [secRho, i285_secHom_mk, Submodule.mkQ_apply] using hxW
  by_cases hTQ : T ≤ secQ X φ
  · left
    have hTeq : T = secP X a ⊓ secQ X φ := le_antisymm (le_inf hTP hTQ) hPQT
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Z w
    have hwT : (v : M) ∈ T := (hmemT v).2 (by simpa using hw)
    have hvQ : (v : M) ∈ secQ X φ := (hTeq ▸ hwT).2
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hvQ
  · right
    have hexT : ∃ t ∈ T, t ∉ secQ X φ := by
      by_contra h
      apply hTQ
      intro t ht
      by_contra htQ
      exact h ⟨t, ht, htQ⟩
    obtain ⟨t, htT, htQ⟩ := hexT
    obtain ⟨g, hg, hgt⟩ := exists_apply_of_not_mem_secQ htQ
    have hgt1 : φ ((g : M →ₗ[ZMod 2] M) t) = 1 := by
      rcases zmod2_eq_zero_or_one (φ ((g : M →ₗ[ZMod 2] M) t)) with h0 | h1
      · exact absurd h0 hgt
      · exact h1
    have hdX : g⁻¹ * tv φ a hφa * g ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hg) hτX) hg
    have hdT : ((g⁻¹ * tv φ a hφa * g : 𝔾) : M →ₗ[ZMod 2] M) t ∈ T :=
      ((hTX hdX) t).2 htT
    have hsub : ((g⁻¹ * tv φ a hφa * g : 𝔾) : M →ₗ[ZMod 2] M) t - t ∈ T :=
      T.sub_mem hdT htT
    have hform : ((g⁻¹ * tv φ a hφa * g : 𝔾) : M →ₗ[ZMod 2] M) t - t =
        φ ((g : M →ₗ[ZMod 2] M) t) • ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a := by
      rw [i285_mul_apply, i285_mul_apply, tv_apply, map_add, map_smul,
        i285_inv_apply_apply]
      abel
    have hgaT : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a ∈ T := by
      have := hform ▸ hsub
      rwa [hgt1, one_smul] at this
    have haT : a ∈ T := by
      have h := ((hTX hg) (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) a)).2 hgaT
      rwa [i285_apply_inv_apply] at h
    have hPT : secP X a ≤ T := by
      rw [secP, Submodule.span_le]
      rintro _ ⟨h, hh, rfl⟩
      exact ((hTX hh) a).2 haT
    have hTeq : T = secP X a := le_antisymm hTP hPT
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Z w
    exact (hmemT v).1 (by rw [hTeq]; exact v.2)

private theorem not_mem_secQ [Finite M] {X : Subgroup 𝔾}
    {φ : Module.Dual (ZMod 2) M} {a : M} (hφa : φ a = 0)
    (hτX : tv φ a hφa ∈ X) (hgen : X ≤ conjClosure X (tv φ a hφa))
    (hX4 : ∃ x ∈ X, x ^ 4 ≠ 1) : a ∉ secQ X φ := by
  intro haQ
  exact secRho_tv_ne_one hφa hτX hgen hX4
    (secRho_tv_eq_one_of_mem_secQ hφa hτX haQ)

theorem exists_section [Finite M] {X : Subgroup 𝔾} {τ : 𝔾} (hτ : IsF2Transvection τ)
    (hτX : τ ∈ X) (hgen : X ≤ conjClosure X τ) (hX4 : ∃ x ∈ X, x ^ 4 ≠ 1) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (ρ : ↥X →* LinearMap.GeneralLinearGroup (ZMod 2) V),
      UniquenessMaximal.IsMcLaughlinGroup ↥ρ.range ∧ ∀ x ∈ ρ.ker, x ^ 4 = 1 := by
  obtain ⟨φ, a, hφa, hφ, ha, rfl⟩ := (isF2Transvection_iff τ).1 hτ
  let P : Submodule (ZMod 2) M := secP X a
  let Q : Submodule (ZMod 2) M := secQ X φ
  let Z : Submodule (ZMod 2) ↥P := Q.comap P.subtype
  let V := ↥P ⧸ Z
  let ρ : ↥X →* LinearMap.GeneralLinearGroup (ZMod 2) V := secRho X φ a
  haveI : Finite V :=
    Finite.of_surjective (Submodule.mkQ Z) (Submodule.mkQ_surjective Z)
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have haQ : a ∉ secQ X φ := not_mem_secQ hφa hτX hgen hX4
  let U : Set 𝔾 := {x | ∃ g ∈ X, x = g⁻¹ * tv φ a hφa * g}
  let S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    (secRho X φ a) '' (Subtype.val ⁻¹' U)
  have hSne : S.Nonempty := by
    refine ⟨secRho X φ a ⟨tv φ a hφa, hτX⟩, ?_⟩
    refine ⟨⟨tv φ a hφa, hτX⟩, ?_, rfl⟩
    exact ⟨1, X.one_mem, by group⟩
  have hStv : ∀ t ∈ S, IsF2Transvection t := by
    rintro t ⟨x, hxU, rfl⟩
    obtain ⟨g, hg, hgx⟩ := hxU
    have hdX : g⁻¹ * tv φ a hφa * g ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hg) hτX) hg
    have hxeq : x = ⟨g⁻¹ * tv φ a hφa * g, hdX⟩ := Subtype.ext hgx
    rw [hxeq]
    exact secRho_conj_isTransvection hφa hτX haQ hg hdX
  have hSgen : (secRho X φ a).range = Subgroup.closure S :=
    secRho_range hφa hτX hgen
  have hirred : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ (secRho X φ a).range, ∀ w ∈ W,
        (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => secRho_irred hφa hτX W hW
  have hmcl := mcLaughlinTypes_holds V (secRho X φ a).range ⟨S, hSne, hStv, hSgen⟩ hirred
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρ, ?_, ?_⟩
  · exact hmcl
  · intro x hx
    exact pow_four_of_mem_ker_secRho hφa hgen hx

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
