module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType.GGQ2Frame.CoverComponents

open CFSG CFSG.Assembly CFSG.StandardType
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem commutatorElement_mul_left_central {H : Type*} [Group H]
    {z : H} (hz : z ∈ Subgroup.center H) (a b : H) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h1 : ⁅a * z, b⁆ = a * ⁅z, b⁆ * a⁻¹ * ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
  have h2 : ⁅z, b⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz b).symm
  rw [h1, h2]; group

theorem commutatorElement_mul_right_central {H : Type*} [Group H]
    {z : H} (hz : z ∈ Subgroup.center H) (a b : H) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h1 : ⁅a, b * z⁆ = ⁅a, b⁆ * b * ⁅a, z⁆ * b⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
  have h2 : ⁅a, z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp hz a
  rw [h1, h2]; group

theorem commutatorElement_mul_central {H : Type*} [Group H]
    {z₁ z₂ : H} (hz₁ : z₁ ∈ Subgroup.center H) (hz₂ : z₂ ∈ Subgroup.center H) (c₁ c₂ : H) :
    ⁅c₁ * z₁, c₂ * z₂⁆ = ⁅c₁, c₂⁆ := by
  rw [commutatorElement_mul_left_central hz₁ c₁ (c₂ * z₂),
    commutatorElement_mul_right_central hz₂ c₁ c₂]

@[expose] def fixedSubgroup {H : Type*} [Group H] (φ : MulAut H) : Subgroup H where
  carrier := {x | φ x = x}
  mul_mem' := by
    intro a b ha hb
    show φ (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one φ
  inv_mem' := by
    intro a ha
    show φ a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mulAut_fixes_commutator {H : Type*} [Group H]
    (φ : MulAut H) (Q : Subgroup H)
    (h : ∀ q ∈ Q, φ q * q⁻¹ ∈ Subgroup.center H) :
    ∀ z ∈ ⁅Q, Q⁆, φ z = z := by
  have hle : ⁅Q, Q⁆ ≤ fixedSubgroup φ := by
    rw [Subgroup.commutator_def]
    apply (Subgroup.closure_le (fixedSubgroup φ)).mpr
    rintro g ⟨q₁, hq₁, q₂, hq₂, rfl⟩
    show φ ⁅q₁, q₂⁆ = ⁅q₁, q₂⁆
    rw [map_commutatorElement]
    have e₁ : φ q₁ = q₁ * (φ q₁ * q₁⁻¹) := by
      rw [Subgroup.mem_center_iff.mp (h q₁ hq₁) q₁]; group
    have e₂ : φ q₂ = q₂ * (φ q₂ * q₂⁻¹) := by
      rw [Subgroup.mem_center_iff.mp (h q₂ hq₂) q₂]; group
    rw [e₁, e₂, commutatorElement_mul_central (h q₁ hq₁) (h q₂ hq₂)]
  intro z hz
  exact hle hz

theorem commutatorElement_mul_central' {H : Type*} [Group H]
    {z₁ z₂ : H} (hz₁ : z₁ ∈ Subgroup.center H) (hz₂ : z₂ ∈ Subgroup.center H) (c₁ c₂ : H) :
    ⁅z₁ * c₁, z₂ * c₂⁆ = ⁅c₁, c₂⁆ := by
  rw [show z₁ * c₁ = c₁ * z₁ from (Subgroup.mem_center_iff.mp hz₁ c₁).symm,
    show z₂ * c₂ = c₂ * z₂ from (Subgroup.mem_center_iff.mp hz₂ c₂).symm,
    commutatorElement_mul_central hz₁ hz₂]

theorem isQuasisimple_map_injective {P Q : Type*} [Group P] [Group Q]
    (f : P →* Q) (hf : Function.Injective f) {K : Subgroup P}
    (hK : CFSG.IsQuasisimple ↥K) : CFSG.IsQuasisimple ↥(K.map f) :=
  (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (Subgroup.equivMapOfInjective K f hf)).mp hK

theorem commutator_comap_eq {H R : Type*} [Group H] [Group R]
    (π : H →* R) (hker : π.ker ≤ Subgroup.center H) {Y : Subgroup R} {C' : Subgroup H}
    (hYC : Y ≤ C'.map π) :
    ⁅Y.comap π, Y.comap π⁆ = ⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    obtain ⟨c₁, hc₁, hc₁π⟩ := Subgroup.mem_map.mp (hYC hq₁)
    obtain ⟨c₂, hc₂, hc₂π⟩ := Subgroup.mem_map.mp (hYC hq₂)
    have hz₁ : q₁ * c₁⁻¹ ∈ Subgroup.center H := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc₁π]; group
    have hz₂ : q₂ * c₂⁻¹ ∈ Subgroup.center H := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc₂π]; group
    have hc₁Y : c₁ ∈ Y.comap π := by
      rw [Subgroup.mem_comap, hc₁π]; exact hq₁
    have hc₂Y : c₂ ∈ Y.comap π := by
      rw [Subgroup.mem_comap, hc₂π]; exact hq₂
    have e₁ : q₁ = (q₁ * c₁⁻¹) * c₁ := by group
    have e₂ : q₂ = (q₂ * c₂⁻¹) * c₂ := by group
    rw [e₁, e₂, commutatorElement_mul_central' hz₁ hz₂]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨hc₁Y, hc₁⟩)
      (Subgroup.mem_inf.mpr ⟨hc₂Y, hc₂⟩)
  · exact Subgroup.commutator_mono inf_le_left inf_le_left

private theorem l02qcov_mulAut_fixes_comap_commutator {G : Type} [Group G]
    {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R)
    (hker : π.ker ≤ Subgroup.center ↥H) (hEq : Equivariant hAN π ρ)
    {Y : Subgroup R} (hYle : Y ≤ Subgroup.centralizer ((ρ.range : Subgroup R) : Set R))
    (a : ↥A) {z : ↥H} (hz : z ∈ ⁅Y.comap π, Y.comap π⁆) :
    H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ z = z := by
  refine mulAut_fixes_commutator (H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩)
    (Y.comap π) ?_ z hz
  intro q hq
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have hramem : ρ a ∈ ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_top a, rfl⟩
  have hqY : π q ∈ Y := Subgroup.mem_comap.mp hq
  have hc := Subgroup.mem_centralizer_iff.mp (hYle hqY) (ρ a) hramem
  have hφq : π (H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ q) = π q := by
    rw [hEq a q, hc]; group
  rw [hφq, mul_inv_cancel]

theorem isQuasisimple_commutator_comap {H R : Type*} [Group H] [Group R]
    (π : H →* R) (hker : π.ker ≤ Subgroup.center H) {Y : Subgroup R} {C' : Subgroup H}
    (hYC : Y ≤ C'.map π) (hYnat : CFSG.IsQuasisimple ↥Y) :
    CFSG.IsQuasisimple ↥(⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆) := by
  let Q : Subgroup H := Y.comap π ⊓ C'
  let pQ : ↥Q →* ↥Y :=
    { toFun := fun q => ⟨π (q : H), Subgroup.mem_comap.mp (Subgroup.mem_inf.mp q.2).1⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : H) (b : H)) }
  have hpQsurj : Function.Surjective pQ := by
    intro y
    have hy : (y : R) ∈ C'.map π := hYC y.2
    obtain ⟨c, hcC, hcπ⟩ := Subgroup.mem_map.mp hy
    have hcY : c ∈ Y.comap π := by rw [Subgroup.mem_comap, hcπ]; exact y.2
    exact ⟨⟨c, Subgroup.mem_inf.mpr ⟨hcY, hcC⟩⟩, Subtype.ext hcπ⟩
  have hkercent : pQ.ker ≤ Subgroup.center ↥Q := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro q'
    have hq1 : π (q : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
    have hcent : (q : H) ∈ Subgroup.center H := hker (MonoidHom.mem_ker.mpr hq1)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcent (q' : H))
  have hQquot : CFSG.IsQuasisimple (↥Q ⧸ pQ.ker) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.quotientKerEquivOfSurjective pQ hpQsurj)).mpr hYnat
  have hcommQ : CFSG.IsQuasisimple ↥(commutator ↥Q) :=
    CFSG.LocalCores.quasisimple_central_extension_derived pQ.ker hkercent hQquot
  have hZ : CFSG.IsQuasisimple ↥(⁅Q, Q⁆) := by
    have h := isQuasisimple_map_injective Q.subtype Q.subtype_injective hcommQ
    rwa [Subgroup.map_subtype_commutator Q] at h
  simpa only [Q] using hZ

theorem isSubnormal_commutator_comap {H R : Type*} [Group H] [Group R]
    (π : H →* R) (_hker : π.ker ≤ Subgroup.center H) {Y : Subgroup R} {C' : Subgroup H}
    {CR : Subgroup R} (hC' : C'.map π = CR) (_hYC : Y ≤ CR)
    (hYsub : IsSubnormal Y CR) :
    IsSubnormal (⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆) C' := by
  let Q : Subgroup H := Y.comap π ⊓ C'
  let p : ↥C' →* R := π.comp C'.subtype
  have hp_range : p.range = CR := by
    rw [MonoidHom.range_comp, Subgroup.subtype_range, hC']
  have hcomap : CR.comap p = ⊤ := by
    apply le_antisymm le_top
    intro x _
    rw [Subgroup.mem_comap, ← hp_range, MonoidHom.range_eq_map]
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_top x, rfl⟩
  have h1 : IsSubnormal (Y.comap p) ⊤ := by
    have h := IsSubnormal.comap p hYsub
    rwa [hcomap] at h
  have h2 : IsSubnormal ((Y.comap p).map C'.subtype) C' := by
    have h := IsSubnormal.map C'.subtype h1
    rwa [Subgroup.map_top, Subgroup.subtype_range] at h
  have hQeq : (Y.comap p).map C'.subtype = Q := by
    ext h
    constructor
    · intro hh
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hh
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_comap.mpr (show π (c : H) ∈ Y from hc), c.2⟩
    · intro hh
      obtain ⟨hhY, hhC⟩ := Subgroup.mem_inf.mp hh
      exact Subgroup.mem_map.mpr ⟨⟨h, hhC⟩, Subgroup.mem_comap.mp hhY, rfl⟩
  have hQsub : IsSubnormal Q C' := by rw [← hQeq]; exact h2
  have hZQ : ⁅Q, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hq₁ hq₂) (inv_mem hq₁)) (inv_mem hq₂)
  have hZnormal : ((⁅Q, Q⁆).subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZQ).mpr
      (Subgroup.normalizer_commutator_ge_left Q Q)
  have hZsub : IsSubnormal ⁅Q, Q⁆ C' :=
    IsSubnormal.step hZQ hZnormal hQsub
  simpa only [Q] using hZsub

theorem mapCentralizerEq_holds :
    ∀ {G : Type} [Group G] [Finite G] {H A : Subgroup G} {R : Type} [Group R]
      (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R),
      IsPGroup 3 A → Function.Surjective π → ¬ 3 ∣ Nat.card π.ker → Equivariant hAN π ρ →
      ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H).map π =
        Subgroup.centralizer ((ρ.range : Subgroup R) : Set R) := by
  intro G _ _ H A R _ hAN π ρ hA hπ hker hEq
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨a, rfl⟩ := hr
    have hhA : (h : G) ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.mem_subgroupOf.mp hh).2
    have hacomm : (a : G) * (h : G) = (h : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hhA a a.2
    have hconj : H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ h = h := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe, hacomm]
      group
    have h1 : ρ a * π h * (ρ a)⁻¹ = π h := by
      rw [← hEq a h, hconj]
    exact mul_inv_eq_iff_eq_mul.mp h1
  · intro y hy
    obtain ⟨h₀, hh₀⟩ := hπ y
    let fiber := {h : ↥H // π h = y}
    let φ : ↥A →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
    have hφ_apply : ∀ (a : ↥A) (h : ↥H),
        φ a h = H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ h := fun _ _ => rfl
    have hφ_coe : ∀ (a : ↥A) (h : ↥H),
        ((φ a h : ↥H) : G) = (a : G) * (h : G) * (a : G)⁻¹ := by
      intro a h
      rw [hφ_apply a h, normalizerMonoidHom_coe]
    have hramem : ∀ a : ↥A, ρ a ∈ ρ.range := by
      intro a
      rw [MonoidHom.range_eq_map]
      exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_top a, rfl⟩
    have hact_mem : ∀ (a : ↥A) {h : ↥H}, π h = y → π (φ a h) = y := by
      intro a h hh
      rw [hφ_apply a h, hEq a h, hh]
      have hyc : ρ a * y = y * ρ a :=
        Subgroup.mem_centralizer_iff.mp hy (ρ a) (hramem a)
      rw [hyc]; group
    let : MulAction ↥A fiber :=
      { smul := fun a h => ⟨φ a h.1, hact_mem a h.2⟩
        one_smul := by
          intro h
          apply Subtype.ext
          show φ 1 h.1 = h.1
          rw [map_one]
          rfl
        mul_smul := by
          intro a b h
          apply Subtype.ext
          show φ (a * b) h.1 = φ a (φ b h.1)
          rw [map_mul]
          rfl }
    have hcard : Nat.card fiber = Nat.card π.ker := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun h => ⟨h₀⁻¹ * h.1, ?_⟩
          invFun := fun k => ⟨h₀ * k.1, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hh₀, h.2]
        group
      · rw [map_mul, hh₀, MonoidHom.mem_ker.mp k.2, mul_one]
      · intro h
        apply Subtype.ext
        show h₀ * (h₀⁻¹ * h.1) = h.1
        group
      · intro k
        apply Subtype.ext
        show h₀⁻¹ * (h₀ * k.1) = k.1
        group
    have hcard3 : ¬ 3 ∣ Nat.card fiber := by rw [hcard]; exact hker
    obtain ⟨h, hhfix⟩ :=
      IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA fiber hcard3
    refine Subgroup.mem_map.mpr ⟨h.1, ?_, h.2⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨h.1.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    let a : ↥A := ⟨g, hg⟩
    have hfixa : φ a h.1 = h.1 := congrArg Subtype.val (hhfix a)
    have hcoe : (a : G) * (h.1 : G) = (h.1 : G) * (a : G) := by
      have hc := hφ_coe a h.1
      rw [hfixa] at hc
      exact mul_inv_eq_iff_eq_mul.mp hc.symm
    simpa using hcoe

private theorem l02qcov_exists_component_of_isComponentOf {G : Type} [Group G] [Finite G]
    {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R)
    (hA : IsPGroup 3 A) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (_hHperf : commutator H = ⊤) (hEq : Equivariant hAN π ρ)
    {X : Subgroup G} (hX : IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G))) :
    ∃ Y : Subgroup R,
      IsComponentOf Y (Subgroup.centralizer ((ρ.range : Subgroup R) : Set R)) ∧
        X = (⁅Y.comap π, Y.comap π⁆).map H.subtype := by
  obtain ⟨hXle, hXsub, hXq⟩ := hX
  have hXH : X ≤ H := hXle.trans inf_le_left
  let X' : Subgroup ↥H := X.subgroupOf H
  let Y : Subgroup R := X'.map π
  have hmapC : ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H).map π
      = Subgroup.centralizer ((ρ.range : Subgroup R) : Set R) :=
    mapCentralizerEq_holds hAN π ρ hA hπ hker3 hEq
  have hXnat : CFSG.IsQuasisimple ↥X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥X).mp hXq
  have hX'nat : CFSG.IsQuasisimple ↥X' :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hXH)).mpr hXnat
  have : Group.IsPerfect ↥X' := hX'nat.1
  have hX'le : X' ≤ Y.comap π := Subgroup.map_le_iff_le_comap.mp le_rfl
  have hZeq : ⁅Y.comap π, Y.comap π⁆ = X' := by
    rw [commutator_comap_eq π hker (le_rfl : Y ≤ X'.map π),
      inf_eq_right.mpr hX'le, Subgroup.commutator_eq_self]
  refine ⟨Y, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hmapC]
    exact Subgroup.map_mono (fun x hx => by
      rw [Subgroup.mem_subgroupOf]; exact hXle hx)
  · have hsub' : IsSubnormal X'
        ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H) := by
      simpa only [X', Subgroup.comap_subtype] using
        IsSubnormal.comap H.subtype hXsub
    have h := IsSubnormal.map π hsub'
    rwa [hmapC] at h
  · have hnot : ¬ X' ≤ π.ker := by
      intro hle
      have : Nontrivial (↥X' ⧸ Subgroup.center ↥X') := hX'nat.2.1.toNontrivial
      have : Nontrivial ↥X' := (QuotientGroup.mk'_surjective (Subgroup.center ↥X')).nontrivial
      have : IsMulCommutative ↥X' :=
        IsMulCommutative.of_comm fun (a b : ↥X') =>
          Subtype.ext_iff.mpr (by
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            exact (Subgroup.mem_center_iff.mp (hker (hle a.2)) (b : ↥H)).symm)
      exact Group.IsPerfect.not_isMulCommutative (G := ↥X') inferInstance
    have hYnat : CFSG.IsQuasisimple ↥Y :=
      CFSG.LocalCores.isQuasisimple_map hX'nat π hnot
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mpr hYnat
  · rw [hZeq, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show X ≤ H from hXH)]

private theorem l02qcov_isComponentOf_commutator_comap {G : Type} [Group G] [Finite G]
    {H A : Subgroup G} {R : Type} [Group R]
    (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R)
    (hA : IsPGroup 3 A) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (_hHperf : commutator H = ⊤) (hEq : Equivariant hAN π ρ)
    {Y : Subgroup R}
    (hY : IsComponentOf Y (Subgroup.centralizer ((ρ.range : Subgroup R) : Set R))) :
    IsComponentOf ((⁅Y.comap π, Y.comap π⁆).map H.subtype)
      (H ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨hYle, hYsub, hYq⟩ := hY
  have hYnat : CFSG.IsQuasisimple ↥Y :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mp hYq
  let C : Subgroup G := H ⊓ Subgroup.centralizer (A : Set G)
  let C' : Subgroup ↥H := C.subgroupOf H
  have hC'map : C'.map π = Subgroup.centralizer ((ρ.range : Subgroup R) : Set R) :=
    mapCentralizerEq_holds hAN π ρ hA hπ hker3 hEq
  have hYC' : Y ≤ C'.map π := by rw [hC'map]; exact hYle
  let Z : Subgroup ↥H := ⁅Y.comap π, Y.comap π⁆
  have hZeq : Z = ⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆ :=
    commutator_comap_eq π hker hYC'
  have hZnat : CFSG.IsQuasisimple ↥Z := by
    rw [hZeq]
    exact isQuasisimple_commutator_comap π hker hYC' hYnat
  have hZsub' : IsSubnormal (⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆) C' :=
    isSubnormal_commutator_comap π hker hC'map hYle hYsub
  have hZsub : IsSubnormal Z C' := by rw [hZeq]; exact hZsub'
  have hXsub : IsSubnormal (Z.map H.subtype) C := by
    have h := IsSubnormal.map H.subtype hZsub
    rwa [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show C ≤ H from inf_le_left)] at h
  have hXle : Z.map H.subtype ≤ C := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g hg
    let a : ↥A := ⟨g, hg⟩
    have hfix := l02qcov_mulAut_fixes_comap_commutator hAN π ρ hker hEq hYle a hz
    have hc : ((H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ z : ↥H) : G)
        = (a : G) * (z : G) * (a : G)⁻¹ := by
      rw [normalizerMonoidHom_coe]
    have hcoe : (a : G) * (z : G) * (a : G)⁻¹ = (z : G) := by rw [← hc, hfix]
    exact mul_inv_eq_iff_eq_mul.mp hcoe
  have hXq : CFSG.Open.IsQuasisimple ↥(Z.map H.subtype) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(Z.map H.subtype)).mpr
      (isQuasisimple_map_injective H.subtype H.subtype_injective hZnat)
  exact ⟨hXle, hXsub, hXq⟩

theorem isComponentOfCoverIff_holds : IsComponentOfCoverIff := by
  intro G _ _ H A R _ hAN π ρ hA hπ hker hker3 hHperf hEq X
  constructor
  · intro hX
    exact l02qcov_exists_component_of_isComponentOf hAN π ρ hA hπ hker hker3 hHperf hEq hX
  · rintro ⟨Y, hY, rfl⟩
    exact l02qcov_isComponentOf_commutator_comap hAN π ρ hA hπ hker hker3 hHperf hEq hY

theorem commuteCoverIff_holds : CommuteCoverIff := by
  intro G _ _ H A R _ hAN π ρ hker hEq X hXperf e
  constructor
  · intro hXe y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hconj : H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩ x = x := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe, hXe x hx]
      group
    have h1 : ρ e * π x * (ρ e)⁻¹ = π x := by
      rw [← hEq e x, hconj]
    exact mul_inv_eq_iff_eq_mul.mp h1
  · intro hcomm x hx
    have : Group.IsPerfect ↥X := ⟨hXperf⟩
    let φ : MulAut ↥H := H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩
    have hφfix : ∀ z ∈ ⁅X, X⁆, φ z = z := by
      apply mulAut_fixes_commutator
      intro q hq
      apply hker
      rw [MonoidHom.mem_ker]
      show π (φ q * q⁻¹) = 1
      rw [map_mul, map_inv]
      have hqmap : π q ∈ X.map π := Subgroup.mem_map_of_mem π hq
      have hcq := hcomm (π q) hqmap
      have hφq : π (φ q) = π q := by
        show π (H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩ q) = π q
        rw [hEq e q, hcq]; group
      rw [hφq, mul_inv_cancel]
    have hperf : φ (x : ↥H) = (x : ↥H) :=
      hφfix (x : ↥H) (by rw [Subgroup.commutator_eq_self]; exact hx)
    have hc : ((φ (x : ↥H) : ↥H) : G) = (e : G) * (x : G) * (e : G)⁻¹ := by
      rw [show φ (x : ↥H) = H.normalizerMonoidHom ⟨(e : G), hAN e.2⟩ (x : ↥H) from rfl,
        normalizerMonoidHom_coe]
    have hcoe : (e : G) * (x : G) * (e : G)⁻¹ = (x : G) := by
      rw [← hc, congrArg Subtype.val hperf]
    exact mul_inv_eq_iff_eq_mul.mp hcoe

theorem memDerivedComapIff_holds : MemDerivedComapIff := by
  intro G _ _ H R _ π hπ hker hker3 Y hYperf e he3
  constructor
  · intro he
    have hmem : π e ∈ (⁅Y.comap π, Y.comap π⁆).map π := Subgroup.mem_map_of_mem π he
    rwa [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ Y, hYperf] at hmem
  · intro hpe
    set Z : Subgroup ↥H := ⁅Y.comap π, Y.comap π⁆ with hZdef
    have hZmap : Z.map π = Y := by
      rw [hZdef, Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ Y, hYperf]
    have hpeZ : π e ∈ Z.map π := by rw [hZmap]; exact hpe
    obtain ⟨x, hxZ, hxπ⟩ := Subgroup.mem_map.mp hpeZ
    have hzker : x⁻¹ * e ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ, inv_mul_cancel]
    have hzcent : x⁻¹ * e ∈ Subgroup.center ↥H := hker hzker
    have hcommxz : Commute x (x⁻¹ * e) := Subgroup.mem_center_iff.mp hzcent x
    have hzpow : (x⁻¹ * e) ^ Nat.card π.ker = 1 := by
      have hzcard : Nat.card (Subgroup.zpowers (x⁻¹ * e)) ∣ Nat.card π.ker :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzker)
      have hzord : orderOf (x⁻¹ * e) ∣ Nat.card π.ker := by
        rwa [Nat.card_zpowers] at hzcard
      exact orderOf_dvd_iff_pow_eq_one.mp hzord
    have hepow : e ^ Nat.card π.ker ∈ Z := by
      have h1 : e = x * (x⁻¹ * e) := by group
      rw [h1, hcommxz.mul_pow, hzpow, mul_one]
      exact Subgroup.pow_mem Z hxZ _
    have hcop : Nat.Coprime (Nat.card π.ker) 3 :=
      Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)
    have hone : (1 : ℤ) = (Nat.card π.ker : ℤ) * ((Nat.card π.ker).gcdA 3)
        + ((3 : ℕ) : ℤ) * ((Nat.card π.ker).gcdB 3) := by
      have h := Nat.gcd_eq_gcd_ab (Nat.card π.ker) 3
      rw [hcop] at h
      simpa using h
    have hmain : e = (e ^ Nat.card π.ker) ^ ((Nat.card π.ker).gcdA 3)
        * (e ^ 3) ^ ((Nat.card π.ker).gcdB 3) := by
      calc e = e ^ (1 : ℤ) := (zpow_one e).symm
        _ = e ^ ((Nat.card π.ker : ℤ) * ((Nat.card π.ker).gcdA 3)
              + ((3 : ℕ) : ℤ) * ((Nat.card π.ker).gcdB 3)) := by rw [hone]
        _ = e ^ ((Nat.card π.ker : ℤ) * ((Nat.card π.ker).gcdA 3))
              * e ^ (((3 : ℕ) : ℤ) * ((Nat.card π.ker).gcdB 3)) := by rw [zpow_add]
        _ = (e ^ ((Nat.card π.ker : ℕ) : ℤ)) ^ ((Nat.card π.ker).gcdA 3)
              * (e ^ ((3 : ℕ) : ℤ)) ^ ((Nat.card π.ker).gcdB 3) := by
              rw [zpow_mul, zpow_mul]
        _ = (e ^ Nat.card π.ker) ^ ((Nat.card π.ker).gcdA 3)
              * (e ^ 3) ^ ((Nat.card π.ker).gcdB 3) := by
              rw [zpow_natCast, zpow_natCast]
    rw [hmain, he3, one_zpow, mul_one]
    exact Subgroup.zpow_mem Z hepow _

end

end CFSG.StandardType.GGQ2Frame.CoverComponents
