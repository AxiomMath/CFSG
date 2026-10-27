module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RepresentationTheory.Basic
public import CFSG.GroupTheory.CentralSplitTransfer
public import CFSG.GF2Type.Smith1979W3.CaseD.Jordan
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Subgroup
open scoped Pointwise

variable {H : Type*} [Group H] [Finite H]

private theorem nat_card_eq_1080
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6))) :
    Nat.card H = 1080 := by
  obtain ⟨e⟩ := hA6
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hq : Nat.card (H ⧸ Subgroup.center H) = 360 := by
    rw [Nat.card_congr e.toEquiv, hA6card]
  calc Nat.card H
      = Nat.card (H ⧸ Subgroup.center H) * Nat.card ↥(Subgroup.center H) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = 360 * 3 := by rw [hq, hZ]
    _ = 1080 := by norm_num

private theorem nat_card_eq_60 {E : Subgroup H}
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) : Nat.card E = 60 := by
  obtain ⟨e⟩ := hE
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  calc Nat.card E = Nat.card (alternatingGroup (Fin 5)) := Nat.card_congr e.toEquiv
    _ = 60 := hA5card

private theorem center_eq_bot_of_alt_five {E : Subgroup H}
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    Subgroup.center ↥E = ⊥ := by
  obtain ⟨e⟩ := hE
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxe : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (hx z)
  rw [alternatingGroup.center_eq_bot (α := Fin 5) (by norm_num)] at hxe
  exact e.injective (by simpa using hxe)

private theorem inf_center_eq_bot {E : Subgroup H}
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    E ⊓ Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxE, hxZ⟩ := hx
  have hxcenter : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (y : H)
  rw [center_eq_bot_of_alt_five hE] at hxcenter
  simpa using hxcenter

private noncomputable def prodCenter (E : Subgroup H) : Subgroup H where
  carrier := (E : Set H) * (Subgroup.center H : Set H)
  one_mem' := by
    simpa using Set.mul_mem_mul E.one_mem (Subgroup.center H).one_mem
  mul_mem' := by
    rintro _ _ ⟨e₁, he₁, z₁, hz₁, rfl⟩ ⟨e₂, he₂, z₂, hz₂, rfl⟩
    have hcomm : z₁ * e₂ = e₂ * z₁ :=
      (Subgroup.mem_center_iff.mp hz₁ e₂).symm
    have hEq : (e₁ * z₁) * (e₂ * z₂) = (e₁ * e₂) * (z₁ * z₂) := by
      calc (e₁ * z₁) * (e₂ * z₂) = e₁ * (z₁ * e₂) * z₂ := by group
        _ = e₁ * (e₂ * z₁) * z₂ := by rw [hcomm]
        _ = (e₁ * e₂) * (z₁ * z₂) := by group
    rw [hEq]
    exact Set.mul_mem_mul (E.mul_mem he₁ he₂) ((Subgroup.center H).mul_mem hz₁ hz₂)
  inv_mem' := by
    rintro _ ⟨e, he, z, hz, rfl⟩
    have hze : z⁻¹ * e⁻¹ = e⁻¹ * z⁻¹ := by
      calc z⁻¹ * e⁻¹ = (e * z)⁻¹ := by rw [mul_inv_rev]
        _ = (z * e)⁻¹ := by rw [Subgroup.mem_center_iff.mp hz e]
        _ = e⁻¹ * z⁻¹ := by rw [mul_inv_rev]
    rw [show (e * z)⁻¹ = z⁻¹ * e⁻¹ from mul_inv_rev _ _, hze]
    exact Set.mul_mem_mul (E.inv_mem he) ((Subgroup.center H).inv_mem hz)

private theorem mem_prodCenter {E : Subgroup H} {x : H} :
    x ∈ prodCenter E ↔ ∃ e ∈ E, ∃ z ∈ Subgroup.center H, e * z = x := by
  show (x ∈ ((E : Set H) * (Subgroup.center H : Set H))) ↔
    (∃ e ∈ E, ∃ z ∈ Subgroup.center H, e * z = x)
  rw [Set.mem_mul]
  rfl

private theorem prodCenter_eq_sup (E : Subgroup H) :
    prodCenter E = E ⊔ Subgroup.center H := by
  apply le_antisymm
  · rintro x ⟨e, he, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup he hz
  · refine sup_le ?_ ?_
    · intro e he
      exact mem_prodCenter.mpr ⟨e, he, 1, (Subgroup.center H).one_mem, by simp⟩
    · intro z hz
      exact mem_prodCenter.mpr ⟨1, E.one_mem, z, hz, by simp⟩

private theorem center_le_prodCenter (E : Subgroup H) :
    Subgroup.center H ≤ prodCenter E :=
  prodCenter_eq_sup E ▸ le_sup_right

private noncomputable instance fintypeQuotientProdCenter (E : Subgroup H) :
    Fintype (H ⧸ prodCenter E) :=
  haveI : Finite (H ⧸ prodCenter E) :=
    Finite.of_surjective (QuotientGroup.mk (s := prodCenter E)) QuotientGroup.mk_surjective
  Fintype.ofFinite _

private noncomputable instance decidableEqQuotientProdCenter (E : Subgroup H) :
    DecidableEq (H ⧸ prodCenter E) :=
  fun a b => Classical.propDecidable (a = b)

private theorem nat_card_prodCenter (hZ : Nat.card (Subgroup.center H) = 3)
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    Nat.card (prodCenter E) = 180 := by
  have hdisj : Disjoint E (Subgroup.center H) := by
    rw [disjoint_iff, inf_center_eq_bot hE]
  let f : ↥E × ↥(Subgroup.center H) → ↥(prodCenter E) :=
    fun p => ⟨(p.1 : H) * (p.2 : H), Set.mul_mem_mul p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have h : (p.1 : H) * (p.2 : H) = (q.1 : H) * (q.2 : H) := congrArg Subtype.val hpq
    exact Subgroup.mul_injective_of_disjoint hdisj h
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_prodCenter.mp x.2)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩),
    Nat.card_prod, nat_card_eq_60 hE, hZ]

private theorem index_prodCenter (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    (prodCenter E).index = 6 := by
  have h := Subgroup.card_mul_index (prodCenter E)
  rw [nat_card_prodCenter hZ hE, nat_card_eq_1080 hZ hA6] at h
  omega

private theorem nat_card_quotient (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    Nat.card (H ⧸ prodCenter E) = 6 := by
  rw [← Subgroup.index_eq_card]
  exact index_prodCenter hZ hA6 hE

private theorem normalCore_prodCenter_eq_center
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    (prodCenter E).normalCore = Subgroup.center H := by
  obtain ⟨e⟩ := hA6
  haveI hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  haveI hqsimple : IsSimpleGroup (H ⧸ Subgroup.center H) := e.isSimpleGroup
  have hBne : prodCenter E ≠ ⊤ := by
    intro htop
    have h1 : (prodCenter E).index = 1 := by
      rw [htop, Subgroup.index_top]
    rw [index_prodCenter hZ ⟨e⟩ hE] at h1
    omega
  apply le_antisymm ?_ ?_
  · let q : H →* H ⧸ Subgroup.center H := QuotientGroup.mk' (Subgroup.center H)
    let N : Subgroup H := (prodCenter E).normalCore
    have hNnormal : N.Normal := Subgroup.normalCore_normal _
    have hNleB : N ≤ prodCenter E := Subgroup.normalCore_le _
    have hqN : (N.map q).Normal := hNnormal.map q (QuotientGroup.mk'_surjective _)
    rcases Subgroup.Normal.eq_bot_or_eq_top (N.map q) with hbot | htop
    · rw [Subgroup.map_eq_bot_iff] at hbot
      rw [QuotientGroup.ker_mk'] at hbot
      exact hbot
    · exfalso
      have htopN : N ⊔ Subgroup.center H = ⊤ := by
        have hmap : N.map q = (⊤ : Subgroup H).map q := by
          rw [htop, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
        have hthis := (Subgroup.map_eq_map_iff (f := q) (H := N) (K := ⊤)).mp hmap
        rw [QuotientGroup.ker_mk', top_sup_eq] at hthis
        exact hthis
      have hle : N ⊔ Subgroup.center H ≤ prodCenter E :=
        sup_le hNleB (center_le_prodCenter E)
      rw [htopN] at hle
      exact hBne (top_le_iff.mp hle)
  · rw [Subgroup.normal_le_normalCore]
    exact center_le_prodCenter E

private theorem ker_toPermHom_quotient (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    (MulAction.toPermHom H (H ⧸ prodCenter E)).ker = Subgroup.center H := by
  rw [← Subgroup.normalCore_eq_ker (prodCenter E),
    normalCore_prodCenter_eq_center hZ hA6 hE]

private theorem range_toPermHom_eq_alternating (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    (MulAction.toPermHom H (H ⧸ prodCenter E)).range =
      alternatingGroup (H ⧸ prodCenter E) := by
  classical
  haveI := hperf
  let σ : H →* Equiv.Perm (H ⧸ prodCenter E) :=
    MulAction.toPermHom H (H ⧸ prodCenter E)
  have hker : σ.ker = Subgroup.center H := ker_toPermHom_quotient hZ hA6 hE
  have hsgn : ∀ g : H, Equiv.Perm.sign (σ g) = 1 := by
    intro g
    have hmem : g ∈ commutator H := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact Subgroup.mem_top g
    have h := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp σ) hmem
    simpa using h
  have hle : σ.range ≤ alternatingGroup (H ⧸ prodCenter E) := by
    rintro _ ⟨g, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    exact hsgn g
  have hcardΩ : Nat.card (H ⧸ prodCenter E) = 6 := nat_card_quotient hZ hA6 hE
  haveI : Nontrivial (H ⧸ prodCenter E) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcardΩ]
    norm_num
  have hcardAlt : Nat.card (alternatingGroup (H ⧸ prodCenter E)) = 360 := by
    rw [nat_card_alternatingGroup, hcardΩ]
    decide
  have hcardZ : Nat.card (H ⧸ Subgroup.center H) = 360 := by
    obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcardRange : Nat.card σ.range = 360 := by
    have h1 : Nat.card (H ⧸ σ.ker) = Nat.card σ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv
    rw [hker, hcardZ] at h1
    exact h1.symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardAlt, hcardRange])

private noncomputable def pointRep (E : Subgroup H) (α : H ⧸ prodCenter E) : H :=
  Quotient.out α

private theorem pointRep_smul (E : Subgroup H) (α : H ⧸ prodCenter E) :
    pointRep E α • ((1 : H) : H ⧸ prodCenter E) = α := by
  rw [pointRep, show Quotient.out α • ((1 : H) : H ⧸ prodCenter E) =
    ((Quotient.out α : H) : H ⧸ prodCenter E) by simp]
  exact QuotientGroup.out_eq' α

private theorem rho_mul_apply {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) (g h : H) (x : V) :
    ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul, Module.End.coe_mul, Function.comp_apply]

private noncomputable def pointV {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) (v : V) (E : Subgroup H)
    (α : H ⧸ prodCenter E) : V :=
  ρ (pointRep E α) v

private theorem rho_apply_ne_zero {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0) (g : H) :
    ρ g v ≠ 0 := by
  intro h
  have hinv : ρ g⁻¹ (ρ g v) = v := by
    calc ρ g⁻¹ (ρ g v) = (ρ g⁻¹ * ρ g) v := rfl
      _ = (1 : V →ₗ[𝕜] V) v := by rw [← map_mul, inv_mul_cancel, map_one]
      _ = v := rfl
  rw [h, map_zero] at hinv
  exact hv hinv.symm

private theorem pointV_ne_zero {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0) (E : Subgroup H)
    (α : H ⧸ prodCenter E) : pointV ρ v E α ≠ 0 :=
  rho_apply_ne_zero ρ hv _

private theorem exists_smul_of_mem_prodCenter {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {b : H} (hb : b ∈ prodCenter E) : ∃ μ : 𝕜, ρ b v = μ • v := by
  obtain ⟨e, he, z, hz, rfl⟩ := mem_prodCenter.mp hb
  obtain ⟨μ, hμ⟩ := hZs z hz
  refine ⟨μ, ?_⟩
  calc ρ (e * z) v = ρ e (ρ z v) := by rw [map_mul, Module.End.coe_mul, Function.comp_apply]
    _ = ρ e (μ • v) := by rw [hμ]
    _ = μ • ρ e v := by rw [map_smul]
    _ = μ • v := by rw [hEv e he]

private theorem exists_smul_of_mem_stabilizer {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (α : H ⧸ prodCenter E) {s : H} (hs : s ∈ MulAction.stabilizer H α) :
    ∃ μ : 𝕜, ρ s (pointV ρ v E α) = μ • pointV ρ v E α := by
  have hwα : pointRep E α • ((1 : H) : H ⧸ prodCenter E) = α := pointRep_smul E α
  have hb : (pointRep E α)⁻¹ * s * pointRep E α ∈ prodCenter E := by
    have hs' : s • α = α := MulAction.mem_stabilizer_iff.mp hs
    have h : ((pointRep E α)⁻¹ * s * pointRep E α) •
        ((1 : H) : H ⧸ prodCenter E) = ((1 : H) : H ⧸ prodCenter E) := by
      calc ((pointRep E α)⁻¹ * s * pointRep E α) • ((1 : H) : H ⧸ prodCenter E)
          = ((pointRep E α)⁻¹ * s) •
              (pointRep E α • ((1 : H) : H ⧸ prodCenter E)) := by rw [mul_smul]
        _ = ((pointRep E α)⁻¹ * s) • α := by rw [hwα]
        _ = (pointRep E α)⁻¹ • (s • α) := by rw [mul_smul]
        _ = (pointRep E α)⁻¹ • α := by rw [hs']
        _ = (pointRep E α)⁻¹ •
              (pointRep E α • ((1 : H) : H ⧸ prodCenter E)) := by rw [hwα]
        _ = ((pointRep E α)⁻¹ * pointRep E α) • ((1 : H) : H ⧸ prodCenter E) := by
              rw [mul_smul]
        _ = ((1 : H) : H ⧸ prodCenter E) := by rw [inv_mul_cancel, one_smul]
    rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h
  obtain ⟨μ, hμ⟩ := exists_smul_of_mem_prodCenter ρ hEv hZs hb
  refine ⟨μ, ?_⟩
  have hs_eq : s * pointRep E α =
      pointRep E α * ((pointRep E α)⁻¹ * s * pointRep E α) := by group
  calc ρ s (pointV ρ v E α) = ρ s (ρ (pointRep E α) v) := rfl
    _ = ρ (s * pointRep E α) v := by
        rw [map_mul, Module.End.coe_mul, Function.comp_apply]
    _ = ρ (pointRep E α * ((pointRep E α)⁻¹ * s * pointRep E α)) v := by rw [hs_eq]
    _ = ρ (pointRep E α) (ρ ((pointRep E α)⁻¹ * s * pointRep E α) v) := by
        rw [map_mul, Module.End.coe_mul, Function.comp_apply]
    _ = ρ (pointRep E α) (μ • v) := by rw [hμ]
    _ = μ • ρ (pointRep E α) v := by rw [map_smul]
    _ = μ • pointV ρ v E α := rfl

private noncomputable def charOf {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (α : H ⧸ prodCenter E) (s : ↥(MulAction.stabilizer H α)) : 𝕜 :=
  Classical.choose (exists_smul_of_mem_stabilizer ρ hEv hZs α s.2)

private theorem charOf_spec {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (α : H ⧸ prodCenter E) (s : ↥(MulAction.stabilizer H α)) :
    ρ (s : H) (pointV ρ v E α) = charOf ρ hEv hZs α s • pointV ρ v E α :=
  Classical.choose_spec (exists_smul_of_mem_stabilizer ρ hEv hZs α s.2)

private theorem charOf_mul {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) {hv : v ≠ 0}
    (α : H ⧸ prodCenter E) (s t : ↥(MulAction.stabilizer H α)) :
    charOf ρ hEv hZs α (s * t) = charOf ρ hEv hZs α s * charOf ρ hEv hZs α t := by
  apply smul_left_injective 𝕜 (pointV_ne_zero ρ hv E α)
  calc charOf ρ hEv hZs α (s * t) • pointV ρ v E α
      = ρ ((s * t : ↥(MulAction.stabilizer H α)) : H) (pointV ρ v E α) :=
        (charOf_spec ρ hEv hZs α (s * t)).symm
    _ = ρ ((s : H) * (t : H)) (pointV ρ v E α) := rfl
    _ = ρ (s : H) (ρ (t : H) (pointV ρ v E α)) := by
        rw [map_mul, Module.End.coe_mul, Function.comp_apply]
    _ = ρ (s : H) (charOf ρ hEv hZs α t • pointV ρ v E α) := by
        rw [charOf_spec ρ hEv hZs α t]
    _ = charOf ρ hEv hZs α t • ρ (s : H) (pointV ρ v E α) := by rw [map_smul]
    _ = charOf ρ hEv hZs α t • (charOf ρ hEv hZs α s • pointV ρ v E α) := by
        rw [charOf_spec ρ hEv hZs α s]
    _ = (charOf ρ hEv hZs α s * charOf ρ hEv hZs α t) • pointV ρ v E α := by
        rw [smul_smul, mul_comm]

private theorem charOf_one {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) {hv : v ≠ 0}
    (α : H ⧸ prodCenter E) : charOf ρ hEv hZs α 1 = 1 := by
  apply smul_left_injective 𝕜 (pointV_ne_zero ρ hv E α)
  calc charOf ρ hEv hZs α 1 • pointV ρ v E α
      = ρ ((1 : ↥(MulAction.stabilizer H α)) : H) (pointV ρ v E α) :=
        (charOf_spec ρ hEv hZs α 1).symm
    _ = pointV ρ v E α := by
        rw [show ((1 : ↥(MulAction.stabilizer H α)) : H) = 1 from rfl, map_one]
        rfl
    _ = (1 : 𝕜) • pointV ρ v E α := (one_smul _ _).symm

private theorem charOf_ne_zero {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) {hv : v ≠ 0}
    (α : H ⧸ prodCenter E) (s : ↥(MulAction.stabilizer H α)) :
    charOf ρ hEv hZs α s ≠ 0 := by
  intro h0
  have h : ρ (s : H) (pointV ρ v E α) = 0 := by
    rw [charOf_spec ρ hEv hZs α s, h0, zero_smul]
  have hinv : ρ (s : H)⁻¹ (ρ (s : H) (pointV ρ v E α)) = pointV ρ v E α := by
    calc ρ (s : H)⁻¹ (ρ (s : H) (pointV ρ v E α))
        = (ρ (s : H)⁻¹ * ρ (s : H)) (pointV ρ v E α) := by
          rw [Module.End.coe_mul, Function.comp_apply]
      _ = (1 : V →ₗ[𝕜] V) (pointV ρ v E α) := by
          rw [← map_mul, inv_mul_cancel, map_one]
      _ = pointV ρ v E α := rfl
  rw [h, map_zero] at hinv
  exact pointV_ne_zero ρ hv E α hinv.symm

private noncomputable def charHom {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) {hv : v ≠ 0}
    (α : H ⧸ prodCenter E) : ↥(MulAction.stabilizer H α) →* 𝕜ˣ where
  toFun s := Units.mk0 (charOf ρ hEv hZs α s) (charOf_ne_zero ρ hEv hZs (hv := hv) α s)
  map_one' := Units.ext (charOf_one ρ hEv hZs (hv := hv) α)
  map_mul' s t := Units.ext (by
    show (charOf ρ hEv hZs α (s * t) : 𝕜) =
      charOf ρ hEv hZs α s * charOf ρ hEv hZs α t
    exact charOf_mul ρ hEv hZs (hv := hv) α s t)

private theorem charHom_spec {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) {hv : v ≠ 0}
    (α : H ⧸ prodCenter E) (s : ↥(MulAction.stabilizer H α)) :
    ρ (s : H) (pointV ρ v E α) =
      (charHom ρ hEv hZs (hv := hv) α s : 𝕜) • pointV ρ v E α :=
  charOf_spec ρ hEv hZs α s

private noncomputable def centralChar {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) :
    ↥(Subgroup.center H) →* 𝕜ˣ where
  toFun z := Units.mk0 (Classical.choose (hZs z z.2)) (by
    intro h0
    have hzv : ρ (z : H) v = 0 := by
      rw [Classical.choose_spec (hZs z z.2), h0, zero_smul]
    have hinv : ρ (z : H)⁻¹ (ρ (z : H) v) = v := by
      calc ρ (z : H)⁻¹ (ρ (z : H) v) = (ρ (z : H)⁻¹ * ρ (z : H)) v := by
            rw [Module.End.coe_mul, Function.comp_apply]
        _ = (1 : V →ₗ[𝕜] V) v := by rw [← map_mul, inv_mul_cancel, map_one]
        _ = v := rfl
    rw [hzv, map_zero] at hinv
    exact hv hinv.symm)
  map_one' := Units.ext (by
    rw [Units.val_one, Units.val_mk0]
    apply smul_left_injective 𝕜 hv
    calc Classical.choose (hZs 1 (Subgroup.one_mem _)) • v
        = ρ (1 : H) v := (Classical.choose_spec (hZs 1 (Subgroup.one_mem _))).symm
      _ = v := by rw [map_one]; rfl
      _ = (1 : 𝕜) • v := (one_smul _ _).symm)
  map_mul' z w := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    apply smul_left_injective 𝕜 hv
    have hzw : ρ (((z * w : ↥(Subgroup.center H)) : H)) v
        = Classical.choose (hZs (((z * w : ↥(Subgroup.center H)) : H))
            (Subgroup.mul_mem (H := Subgroup.center H) z.2 w.2)) • v :=
      Classical.choose_spec (hZs (((z * w : ↥(Subgroup.center H)) : H))
        (Subgroup.mul_mem (H := Subgroup.center H) z.2 w.2))
    calc Classical.choose (hZs (((z * w : ↥(Subgroup.center H)) : H))
          (Subgroup.mul_mem (H := Subgroup.center H) z.2 w.2)) • v
        = ρ (((z * w : ↥(Subgroup.center H)) : H)) v := hzw.symm
      _ = ρ (z : H) (ρ (w : H) v) := by
          change ρ ((z : H) * (w : H)) v = ρ (z : H) (ρ (w : H) v)
          rw [map_mul, Module.End.coe_mul, Function.comp_apply]
      _ = ρ (z : H) (Classical.choose (hZs w w.2) • v) := by
          congr 1
          exact Classical.choose_spec (hZs w w.2)
      _ = Classical.choose (hZs w w.2) • ρ (z : H) v := by rw [map_smul]
      _ = Classical.choose (hZs w w.2) •
            (Classical.choose (hZs z z.2) • v) := by
          congr 1
          exact Classical.choose_spec (hZs z z.2)
      _ = (Classical.choose (hZs z z.2) * Classical.choose (hZs w w.2)) • v := by
          rw [smul_smul, mul_comm])

private theorem centralChar_spec {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (z : ↥(Subgroup.center H)) :
    ρ (z : H) v = (centralChar ρ hv hZs z : 𝕜) • v :=
  Classical.choose_spec (hZs z z.2)

private theorem centralChar_ne_one {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {z : ↥(Subgroup.center H)} (hz : z ≠ 1) : (centralChar ρ hv hZs z : 𝕜) ≠ 1 := by
  intro h1
  have hzH : (z : H) ≠ 1 := fun h => hz (Subtype.ext h)
  apply hZv (z : H) z.2 hzH
  rw [centralChar_spec ρ hv hZs z, h1, one_smul]

private theorem centralChar_smul_pointV {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) (E : Subgroup H)
    (z : ↥(Subgroup.center H)) (α : H ⧸ prodCenter E) :
    ρ (z : H) (pointV ρ v E α) = (centralChar ρ hv hZs z : 𝕜) • pointV ρ v E α := by
  have hcomm : (z : H) * pointRep E α = pointRep E α * (z : H) := by
    exact (Subgroup.mem_center_iff.mp z.2 (pointRep E α)).symm
  calc ρ (z : H) (ρ (pointRep E α) v) = ρ ((z : H) * pointRep E α) v := by
        rw [map_mul, Module.End.coe_mul, Function.comp_apply]
    _ = ρ (pointRep E α * (z : H)) v := by rw [hcomm]
    _ = ρ (pointRep E α) (ρ (z : H) v) := by
        rw [map_mul, Module.End.coe_mul, Function.comp_apply]
    _ = ρ (pointRep E α) ((centralChar ρ hv hZs z : 𝕜) • v) := by rw [centralChar_spec]
    _ = (centralChar ρ hv hZs z : 𝕜) • ρ (pointRep E α) v := by rw [map_smul]
    _ = (centralChar ρ hv hZs z : 𝕜) • pointV ρ v E α := rfl

private theorem commutative_closure_of_commute {c g : H} (hcomm : c * g = g * c) :
    IsMulCommutative ↥(Subgroup.closure (({c, g} : Set H) ∪ (Subgroup.center H : Set H))) := by
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy hxy
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with (hxc | hxc) | hxZ
  · rcases hy with (hyc | hyc) | hyZ
    · rw [hxc, hyc]
    · rw [hxc, hyc]
      exact hcomm
    · rw [hxc]
      exact Subgroup.mem_center_iff.mp hyZ c
  · rcases hy with (hyc | hyc) | hyZ
    · rw [hxc, hyc]
      exact hcomm.symm
    · rw [hxc, hyc]
    · rw [hxc]
      exact Subgroup.mem_center_iff.mp hyZ g
  · rcases hy with (hyc | hyc) | hyZ
    · rw [hyc]
      exact (Subgroup.mem_center_iff.mp hxZ c).symm
    · rw [hyc]
      exact (Subgroup.mem_center_iff.mp hxZ g).symm
    · exact (Subgroup.mem_center_iff.mp hxZ y).symm

private theorem map_closure_threeCycles (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) {c g : H} :
    (Subgroup.closure (({c, g} : Set H) ∪ (Subgroup.center H : Set H))).map
        (MulAction.toPermHom H (H ⧸ prodCenter E)) =
      Subgroup.closure ({MulAction.toPermHom H (H ⧸ prodCenter E) c,
        MulAction.toPermHom H (H ⧸ prodCenter E) g} :
        Set (Equiv.Perm (H ⧸ prodCenter E))) := by
  have hσker : (MulAction.toPermHom H (H ⧸ prodCenter E)).ker = Subgroup.center H :=
    ker_toPermHom_quotient hZ hA6 hE
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨y, hy | hy, rfl⟩
    · rcases hy with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · have hyker : y ∈ (MulAction.toPermHom H (H ⧸ prodCenter E)).ker := hσker.symm ▸ hy
      rw [MonoidHom.mem_ker.mp hyker]
      exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure ⟨c, Or.inl (by simp), rfl⟩
    · exact Subgroup.subset_closure ⟨g, Or.inl (by simp), rfl⟩

private theorem nat_card_closure_threeCycles_center (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) {c g : H}
    (hc : (MulAction.toPermHom H (H ⧸ prodCenter E) c).IsThreeCycle)
    (hg : (MulAction.toPermHom H (H ⧸ prodCenter E) g).IsThreeCycle)
    (hd : (MulAction.toPermHom H (H ⧸ prodCenter E) c).Disjoint
      (MulAction.toPermHom H (H ⧸ prodCenter E) g)) :
    Nat.card ↥(Subgroup.closure (({c, g} : Set H) ∪ (Subgroup.center H : Set H))) = 27 := by
  set Q : Subgroup H := Subgroup.closure (({c, g} : Set H) ∪ (Subgroup.center H : Set H))
    with hQ
  have hQmap : Q.map (MulAction.toPermHom H (H ⧸ prodCenter E)) =
      Subgroup.closure ({MulAction.toPermHom H (H ⧸ prodCenter E) c,
        MulAction.toPermHom H (H ⧸ prodCenter E) g} :
        Set (Equiv.Perm (H ⧸ prodCenter E))) := by
    rw [hQ]
    exact map_closure_threeCycles hZ hA6 hE
  have hcardImage : Nat.card ↥(Subgroup.closure
      ({MulAction.toPermHom H (H ⧸ prodCenter E) c,
        MulAction.toPermHom H (H ⧸ prodCenter E) g} :
        Set (Equiv.Perm (H ⧸ prodCenter E)))) = 9 :=
    CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles hc hg hd
  have hZQ : Subgroup.center H ≤ Q := by
    rw [hQ]
    exact fun z hz => Subgroup.subset_closure (Or.inr hz)
  let ψ : ↥Q →* Equiv.Perm (H ⧸ prodCenter E) :=
    (MulAction.toPermHom H (H ⧸ prodCenter E)).comp Q.subtype
  have hψrange : ψ.range = Q.map (MulAction.toPermHom H (H ⧸ prodCenter E)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_map_of_mem _ y.2
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hσker : (MulAction.toPermHom H (H ⧸ prodCenter E)).ker = Subgroup.center H :=
    ker_toPermHom_quotient hZ hA6 hE
  have hψker : ψ.ker = (Subgroup.center H).subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    show (MulAction.toPermHom H (H ⧸ prodCenter E)) (x : H) = 1 ↔
      (x : H) ∈ Subgroup.center H
    rw [← hσker]
    exact MonoidHom.mem_ker
  have hcardker : Nat.card ↥((Subgroup.center H).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv, hZ]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hψrange, hQmap,
    hcardImage, hψker, hcardker] at h
  omega

private theorem exists_central_element_order_three (hZ : Nat.card (Subgroup.center H) = 3) :
    ∃ z : ↥(Subgroup.center H), z ≠ 1 ∧ orderOf (z : H) = 3 := by
  haveI : Fintype ↥(Subgroup.center H) := Fintype.ofFinite _
  have hZcard : Fintype.card ↥(Subgroup.center H) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hZ
  haveI : Nontrivial ↥(Subgroup.center H) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hZcard]
    norm_num
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center H))
  refine ⟨z, hz1, ?_⟩
  have hdvd : orderOf (z : H) ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard (s := Subgroup.center H) z.2
    rw [hZ] at h
    exact h
  have hne : orderOf (z : H) ≠ 1 := by
    intro h1
    exact hz1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
  exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd |>.resolve_left hne

private theorem not_commute_of_disjoint_threeCycles (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {c g : H}
    (hc : (MulAction.toPermHom H (H ⧸ prodCenter E) c).IsThreeCycle)
    (hg : (MulAction.toPermHom H (H ⧸ prodCenter E) g).IsThreeCycle)
    (hd : (MulAction.toPermHom H (H ⧸ prodCenter E) c).Disjoint
      (MulAction.toPermHom H (H ⧸ prodCenter E) g)) :
    c * g ≠ g * c := by
  classical
  haveI := hperf
  intro hcomm
  let P : Subgroup H :=
    Subgroup.closure (({c, g} : Set H) ∪ (Subgroup.center H : Set H))
  have hZP : Subgroup.center H ≤ P := fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hPcomm : IsMulCommutative ↥P := commutative_closure_of_commute hcomm
  have hPcard : Nat.card P = 27 := nat_card_closure_threeCycles_center hZ hA6 hE hc hg hd
  have hidx : P.index = 40 := by
    have h := Subgroup.card_mul_index P
    rw [hPcard, nat_card_eq_1080 hZ hA6] at h
    omega
  have h3 : ¬ 3 ∣ P.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right, hidx]
    norm_num
  obtain ⟨z, hz1, hzord⟩ := exists_central_element_order_three hZ
  have hzc : ∀ x ∈ (⊤ : Subgroup H), Commute (z : H) x := fun x _ =>
    (Subgroup.mem_center_iff.mp z.2 x).symm
  have hznc : (z : H) ∉ ⁅P, P⁆ := by
    rw [Subgroup.commutator_self_eq_bot_iff.mpr hPcomm]
    exact fun h => hz1 (Subtype.ext (by simpa using h))
  have hres : (z : H) ∉ ⁅(⊤ : Subgroup H), ⊤⁆ :=
    CFSG.GroupTheory.not_mem_commutator_of_relIndex (C := ⊤) (H := P) (p := 3)
      le_top h3 (hZP z.2) hzc hzord hznc
  have hmem : (z : H) ∈ commutator H := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top _
  exact hres hmem

private theorem exists_smul_pointV_of_smul {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} {E : Subgroup H}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) {hv : v ≠ 0}
    {g : H} {α β : H ⧸ prodCenter E} (h : g • α = β) :
    ∃ a : 𝕜, a ≠ 0 ∧ ρ g (pointV ρ v E α) = a • pointV ρ v E β := by
  classical
  have hwα : pointRep E α • ((1 : H) : H ⧸ prodCenter E) = α := pointRep_smul E α
  have hwβ : pointRep E β • ((1 : H) : H ⧸ prodCenter E) = β := pointRep_smul E β
  have hb : (pointRep E β)⁻¹ * g * pointRep E α ∈ prodCenter E := by
    have h' : ((pointRep E β)⁻¹ * g * pointRep E α) •
        ((1 : H) : H ⧸ prodCenter E) = ((1 : H) : H ⧸ prodCenter E) := by
      calc ((pointRep E β)⁻¹ * g * pointRep E α) • ((1 : H) : H ⧸ prodCenter E)
          = ((pointRep E β)⁻¹ * g) •
              (pointRep E α • ((1 : H) : H ⧸ prodCenter E)) := by rw [mul_smul]
        _ = ((pointRep E β)⁻¹ * g) • α := by rw [hwα]
        _ = (pointRep E β)⁻¹ • (g • α) := by rw [mul_smul]
        _ = (pointRep E β)⁻¹ • β := by rw [h]
        _ = (pointRep E β)⁻¹ •
              (pointRep E β • ((1 : H) : H ⧸ prodCenter E)) := by rw [hwβ]
        _ = ((pointRep E β)⁻¹ * pointRep E β) • ((1 : H) : H ⧸ prodCenter E) := by
              rw [mul_smul]
        _ = ((1 : H) : H ⧸ prodCenter E) := by rw [inv_mul_cancel, one_smul]
    rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h'
  obtain ⟨μ, hμ⟩ := exists_smul_of_mem_prodCenter ρ hEv hZs hb
  refine ⟨μ, ?_, ?_⟩
  · intro h0
    exact rho_apply_ne_zero ρ hv ((pointRep E β)⁻¹ * g * pointRep E α) (by rw [hμ, h0, zero_smul])
  · have hs : g * pointRep E α =
        pointRep E β * ((pointRep E β)⁻¹ * g * pointRep E α) := by group
    calc ρ g (pointV ρ v E α) = ρ g (ρ (pointRep E α) v) := rfl
      _ = ρ (g * pointRep E α) v := by rw [map_mul, Module.End.coe_mul, Function.comp_apply]
      _ = ρ (pointRep E β * ((pointRep E β)⁻¹ * g * pointRep E α)) v := by rw [hs]
      _ = ρ (pointRep E β) (ρ ((pointRep E β)⁻¹ * g * pointRep E α) v) := by
          rw [map_mul, Module.End.coe_mul, Function.comp_apply]
      _ = ρ (pointRep E β) (μ • v) := by rw [hμ]
      _ = μ • ρ (pointRep E β) v := by rw [map_smul]
      _ = μ • pointV ρ v E β := rfl

private theorem exists_fixed_outside {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (c : Equiv.Perm Ω) (hc3 : c.IsThreeCycle) (hcard : Fintype.card Ω = 6)
    {α β : Ω} (hαβ : α ≠ β) (hα : c α = α) (hβ : c β = β) :
    ∃ γ : Ω, γ ≠ α ∧ γ ≠ β ∧ c γ = γ := by
  classical
  let T : Finset Ω := c.support
  have hTcard : T.card = 3 := hc3.card_support
  have hαT : α ∉ T := by
    rw [show α ∈ T ↔ c α ≠ α from Equiv.Perm.mem_support, not_not]
    exact hα
  have hβT : β ∉ T := by
    rw [show β ∈ T ↔ c β ≠ β from Equiv.Perm.mem_support, not_not]
    exact hβ
  let U : Finset Ω := Tᶜ \ {α, β}
  have hcard2 : ({α, β} : Finset Ω).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa using hαβ
  have hUcard : U.card = 1 := by
    change (Tᶜ \ {α, β}).card = 1
    rw [Finset.card_sdiff, Finset.card_compl, hTcard]
    have hsub : ({α, β} : Finset Ω) ⊆ Tᶜ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_compl]
      rcases hx with rfl | rfl
      · exact hαT
      · exact hβT
    rw [Finset.inter_eq_left.mpr hsub, hcard2, hcard]
  obtain ⟨γ, hγU⟩ := Finset.card_pos.mp (by rw [hUcard]; norm_num)
  have hγT : γ ∉ T := by
    have h := (Finset.mem_sdiff.mp hγU).1
    rwa [Finset.mem_compl] at h
  have hγnot : γ ∉ ({α, β} : Finset Ω) := (Finset.mem_sdiff.mp hγU).2
  have hγα : γ ≠ α := by simpa using fun h => hγnot (by rw [h]; simp)
  have hγβ : γ ≠ β := by simpa using fun h => hγnot (by rw [h]; simp)
  refine ⟨γ, hγα, hγβ, ?_⟩
  have h : γ ∉ c.support := hγT
  rwa [Equiv.Perm.mem_support, not_not] at h

private theorem exists_threeCycle_moving {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {c : Equiv.Perm Ω} {α β γ : Ω} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα : c α = α) (hβ : c β = β) (hγ : c γ = γ) :
    ∃ g' : Equiv.Perm Ω, g'.IsThreeCycle ∧ g' α = β ∧ g'.Disjoint c := by
  let g' : Equiv.Perm Ω := Equiv.swap α γ * Equiv.swap α β
  have hg'3 : g'.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hαγ hαβ hβγ.symm
  have hg'α : g' α = β := by
    show Equiv.swap α γ (Equiv.swap α β α) = β
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hαβ.symm hβγ
  have hdisj : g'.Disjoint c := by
    intro x
    by_cases hxα : x = α
    · exact Or.inr (by rw [hxα]; exact hα)
    by_cases hxβ : x = β
    · exact Or.inr (by rw [hxβ]; exact hβ)
    by_cases hxγ : x = γ
    · exact Or.inr (by rw [hxγ]; exact hγ)
    · refine Or.inl ?_
      show Equiv.swap α γ (Equiv.swap α β x) = x
      rw [Equiv.swap_apply_of_ne_of_ne hxα hxβ,
        Equiv.swap_apply_of_ne_of_ne hxα hxγ]
  exact ⟨g', hg'3, hg'α, hdisj⟩

private theorem exists_commutator_central (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {α β : H ⧸ prodCenter E} {c g : H} (hgα : g • α = β)
    (hc3 : (MulAction.toPermHom H (H ⧸ prodCenter E) c).IsThreeCycle)
    (hg3 : (MulAction.toPermHom H (H ⧸ prodCenter E) g).IsThreeCycle)
    (hdisj : (MulAction.toPermHom H (H ⧸ prodCenter E) c).Disjoint
      (MulAction.toPermHom H (H ⧸ prodCenter E) g)) :
    ∃ (z : ↥(Subgroup.center H)) (a : 𝕜), a ≠ 0 ∧
      (centralChar ρ hv hZs z : 𝕜) ≠ 1 ∧ c * g = (z : H) * (g * c) ∧
      ρ g (pointV ρ v E α) = a • pointV ρ v E β := by
  classical
  let σ : H →* Equiv.Perm (H ⧸ prodCenter E) :=
    MulAction.toPermHom H (H ⧸ prodCenter E)
  have hσker : σ.ker = Subgroup.center H := ker_toPermHom_quotient hZ hA6 hE
  obtain ⟨z, hz_def⟩ : ∃ z : H, z = c * g * c⁻¹ * g⁻¹ := ⟨_, rfl⟩
  have hzker : z ∈ σ.ker := by
    rw [hz_def]
    rw [MonoidHom.mem_ker]
    have hcomm : Commute (σ c) (σ g) := Equiv.Perm.Disjoint.commute hdisj
    calc σ (c * g * c⁻¹ * g⁻¹) = σ c * σ g * (σ c)⁻¹ * (σ g)⁻¹ := by simp [map_mul]
      _ = 1 := by rw [hcomm.eq]; group
  have hzZ : z ∈ Subgroup.center H := hσker ▸ hzker
  have hz1 : z ≠ 1 := by
    rw [hz_def]
    intro hz
    have hne := not_commute_of_disjoint_threeCycles hperf hZ hA6 hE hc3 hg3 hdisj
    apply hne
    calc c * g = (c * g * c⁻¹ * g⁻¹) * (g * c) := by group
      _ = 1 * (g * c) := by rw [hz]
      _ = g * c := one_mul _
  have hzsub : (⟨z, hzZ⟩ : ↥(Subgroup.center H)) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext_iff.mp h)
  have hω : (centralChar ρ hv hZs ⟨z, hzZ⟩ : 𝕜) ≠ 1 :=
    centralChar_ne_one ρ hv hZs hZv hzsub
  obtain ⟨a, ha0, hline⟩ := exists_smul_pointV_of_smul ρ hEv hZs (hv := hv) hgα
  have hcg : c * g = z * (g * c) := by
    rw [hz_def]
    group
  exact ⟨⟨z, hzZ⟩, a, ha0, hω, hcg, hline⟩

private theorem rho_commute_apply {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V)
    {v : V} {α : H ⧸ prodCenter E} {z g : H} (hz : z ∈ Subgroup.center H) :
    ρ z (ρ g (pointV ρ v E α)) = ρ g (ρ z (pointV ρ v E α)) := by
  have hcommEnd : Commute (ρ z) (ρ g) := by
    show ρ z * ρ g = ρ g * ρ z
    rw [← map_mul, ← map_mul]
    rw [show z * g = g * z from (Subgroup.mem_center_iff.mp hz g).symm]
  calc ρ z (ρ g (pointV ρ v E α)) = (ρ z * ρ g) (pointV ρ v E α) := by
        rw [Module.End.coe_mul, Function.comp_apply]
    _ = (ρ g * ρ z) (pointV ρ v E α) := by rw [hcommEnd.eq]
    _ = ρ g (ρ z (pointV ρ v E α)) := by
        rw [Module.End.coe_mul, Function.comp_apply]

private theorem scalar_relation_of_commutator {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V)
    {v : V} (hv : v ≠ 0) (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {α β : H ⧸ prodCenter E} {c g : H}
    (hcα : c ∈ MulAction.stabilizer H α) (hcβ : c ∈ MulAction.stabilizer H β)
    {z : ↥(Subgroup.center H)} (hcg : c * g = (z : H) * (g * c))
    {a : 𝕜} (ha0 : a ≠ 0)
    (hline : ρ g (pointV ρ v E α) = a • pointV ρ v E β) :
    (charHom ρ hEv hZs (hv := hv) β ⟨c, hcβ⟩ : 𝕜) =
      (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) * (centralChar ρ hv hZs z : 𝕜) := by
  have hline' : pointV ρ v E β = a⁻¹ • ρ g (pointV ρ v E α) := by
    rw [hline, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  apply smul_left_injective 𝕜 (pointV_ne_zero ρ hv E β)
  calc (charHom ρ hEv hZs (hv := hv) β ⟨c, hcβ⟩ : 𝕜) • pointV ρ v E β
      = ρ c (pointV ρ v E β) :=
        (charHom_spec ρ hEv hZs (hv := hv) β ⟨c, hcβ⟩).symm
    _ = ρ c (a⁻¹ • ρ g (pointV ρ v E α)) := by rw [hline']
    _ = a⁻¹ • ρ c (ρ g (pointV ρ v E α)) := by rw [map_smul]
    _ = a⁻¹ • ρ (c * g) (pointV ρ v E α) := by rw [rho_mul_apply]
    _ = a⁻¹ • ρ (z * (g * c)) (pointV ρ v E α) := by rw [hcg]
    _ = a⁻¹ • ρ z (ρ (g * c) (pointV ρ v E α)) := by rw [rho_mul_apply]
    _ = a⁻¹ • ρ z (ρ g (ρ c (pointV ρ v E α))) := by rw [rho_mul_apply]
    _ = a⁻¹ • ρ z (ρ g ((charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          pointV ρ v E α)) := by
        rw [charHom_spec ρ hEv hZs (hv := hv) α ⟨c, hcα⟩]
    _ = a⁻¹ • ρ z ((charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          ρ g (pointV ρ v E α)) := by rw [map_smul]
    _ = a⁻¹ • (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          ρ z (ρ g (pointV ρ v E α)) := by rw [map_smul]
    _ = a⁻¹ • (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          ρ g (ρ z (pointV ρ v E α)) := by
        rw [rho_commute_apply (z := (z : H)) (g := g) ρ z.2]
    _ = a⁻¹ • (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          ρ g ((centralChar ρ hv hZs z : 𝕜) • pointV ρ v E α) := by
        rw [centralChar_smul_pointV ρ hv hZs E z α]
    _ = a⁻¹ • (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          ((centralChar ρ hv hZs z : 𝕜) • ρ g (pointV ρ v E α)) := by rw [map_smul]
    _ = a⁻¹ • (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) •
          ((centralChar ρ hv hZs z : 𝕜) • (a • pointV ρ v E β)) := by rw [hline]
    _ = ((charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) *
          (centralChar ρ hv hZs z : 𝕜)) • pointV ρ v E β := by
        rw [smul_smul, smul_smul, smul_smul]
        congr 1
        field_simp

private theorem commutator_scalar_relation (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {α β : H ⧸ prodCenter E} {c g : H}
    (hcα : c ∈ MulAction.stabilizer H α) (hcβ : c ∈ MulAction.stabilizer H β)
    (hgα : g • α = β)
    (hc3 : (MulAction.toPermHom H (H ⧸ prodCenter E) c).IsThreeCycle)
    (hg3 : (MulAction.toPermHom H (H ⧸ prodCenter E) g).IsThreeCycle)
    (hdisj : (MulAction.toPermHom H (H ⧸ prodCenter E) c).Disjoint
      (MulAction.toPermHom H (H ⧸ prodCenter E) g)) :
    ∃ z : ↥(Subgroup.center H), (centralChar ρ hv hZs z : 𝕜) ≠ 1 ∧
      (charHom ρ hEv hZs (hv := hv) β ⟨c, hcβ⟩ : 𝕜) =
        (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) *
          (centralChar ρ hv hZs z : 𝕜) := by
  obtain ⟨z, a, ha0, hω, hcg, hline⟩ :=
    exists_commutator_central hperf hZ hA6 hE ρ hv hEv hZs hZv hgα hc3 hg3 hdisj
  exact ⟨z, hω, scalar_relation_of_commutator ρ hv hEv hZs hcα hcβ hcg ha0 hline⟩

private theorem char_ne_of_threeCycle (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {α β : H ⧸ prodCenter E} (hαβ : α ≠ β) {c : H}
    (hcα : c ∈ MulAction.stabilizer H α) (hcβ : c ∈ MulAction.stabilizer H β)
    (hc3 : (MulAction.toPermHom H (H ⧸ prodCenter E) c).IsThreeCycle) :
    (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) ≠
      (charHom ρ hEv hZs (hv := hv) β ⟨c, hcβ⟩ : 𝕜) := by
  classical
  let σ : H →* Equiv.Perm (H ⧸ prodCenter E) :=
    MulAction.toPermHom H (H ⧸ prodCenter E)
  have hσrange : σ.range = alternatingGroup (H ⧸ prodCenter E) :=
    range_toPermHom_eq_alternating hperf hZ hA6 hE
  have hcα' : σ c α = α := MulAction.mem_stabilizer_iff.mp hcα
  have hcβ' : σ c β = β := MulAction.mem_stabilizer_iff.mp hcβ
  have hΩcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact nat_card_quotient hZ hA6 hE
  obtain ⟨γ, hγα, hγβ, hγfix⟩ :=
    exists_fixed_outside (σ c) hc3 hΩcard hαβ hcα' hcβ'
  obtain ⟨g', hg'3, hg'α, hdisj⟩ :=
    exists_threeCycle_moving hαβ hγα.symm hγβ.symm hcα' hcβ' hγfix
  have hg'mem : g' ∈ σ.range := by
    rw [hσrange]
    exact hg'3.mem_alternatingGroup
  obtain ⟨g, hg⟩ := hg'mem
  have hgα : g • α = β := by
    have h1 : σ g • α = β := by
      rw [hg]
      exact hg'α
    rwa [MulAction.toPermHom_apply] at h1
  have hg3 : (σ g).IsThreeCycle := by rw [hg]; exact hg'3
  have hdisj' : (σ c).Disjoint (σ g) := by rw [hg]; exact hdisj.symm
  obtain ⟨z, hω, hrel⟩ :=
    commutator_scalar_relation hperf hZ hA6 hE ρ hv hEv hZs hZv hcα hcβ hgα hc3 hg3 hdisj'
  intro hEq
  have h1 : (centralChar ρ hv hZs z : 𝕜) = 1 := by
    have h2 : (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) *
        (centralChar ρ hv hZs z : 𝕜) =
        (charHom ρ hEv hZs (hv := hv) α ⟨c, hcα⟩ : 𝕜) * 1 := by
      rw [mul_one, ← hrel, hEq]
    exact mul_left_cancel₀ (charOf_ne_zero ρ hEv hZs (hv := hv) α ⟨c, hcα⟩) h2
  exact hω h1

private theorem isMultiplyPretransitive_two (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5))) :
    MulAction.IsMultiplyPretransitive H (H ⧸ prodCenter E) 2 := by
  classical
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  have hΩcard : Nat.card (H ⧸ prodCenter E) = 6 := nat_card_quotient hZ hA6 hE
  haveI : Finite (H ⧸ prodCenter E) :=
    Finite.of_surjective (QuotientGroup.mk (s := prodCenter E)) QuotientGroup.mk_surjective
  have hFcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact hΩcard
  have h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (H ⧸ prodCenter E))
      (H ⧸ prodCenter E) 4 := by
    simpa [hFcard] using alternatingGroup.isMultiplyPretransitive (H ⧸ prodCenter E)
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (H ⧸ prodCenter E))
      (H ⧸ prodCenter E) 2 :=
    MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 4) (by norm_num)
      (by rw [hΩcard]; norm_num)
  obtain ⟨g', hg'a, hg'b⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hab hcd
  have hg'mem : (g' : Equiv.Perm (H ⧸ prodCenter E)) ∈
      (MulAction.toPermHom H (H ⧸ prodCenter E)).range := by
    rw [range_toPermHom_eq_alternating hperf hZ hA6 hE]
    exact g'.2
  obtain ⟨g, hg⟩ := hg'mem
  refine ⟨g, ?_, ?_⟩
  · have h1 : g • a = g' • a := by
      rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply, hg]
      rfl
    rw [h1]
    exact hg'a
  · have h1 : g • b = g' • b := by
      rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply, hg]
      rfl
    rw [h1]
    exact hg'b

private theorem nat_card_ne_pairs {E : Subgroup H}
    (hΩcard : Nat.card (H ⧸ prodCenter E) = 6) :
    Nat.card {p : (H ⧸ prodCenter E) × (H ⧸ prodCenter E) // p.1 ≠ p.2} = 30 := by
  classical
  haveI : Fintype (H ⧸ prodCenter E) := fintypeQuotientProdCenter E
  have hcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact hΩcard
  let e : (H ⧸ prodCenter E) ≃ Fin 6 := Fintype.equivFinOfCardEq hcard
  let ee : {p : (H ⧸ prodCenter E) × (H ⧸ prodCenter E) // p.1 ≠ p.2} ≃
      {p : Fin 6 × Fin 6 // p.1 ≠ p.2} :=
    Equiv.subtypeEquiv (e.prodCongr e) (fun p => by
      simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, ne_eq]
      constructor
      · intro h h2
        exact h (e.injective (by simpa using h2))
      · intro h h2
        exact h (by simpa using congrArg e h2))
  have h : Fintype.card {p : Fin 6 × Fin 6 // p.1 ≠ p.2} = 30 := by decide
  haveI : Fintype {p : (H ⧸ prodCenter E) × (H ⧸ prodCenter E) // p.1 ≠ p.2} :=
    Fintype.ofFinite _
  calc Nat.card {p : (H ⧸ prodCenter E) × (H ⧸ prodCenter E) // p.1 ≠ p.2}
      = Fintype.card {p : (H ⧸ prodCenter E) × (H ⧸ prodCenter E) // p.1 ≠ p.2} :=
        Nat.card_eq_fintype_card
    _ = Fintype.card {p : Fin 6 × Fin 6 // p.1 ≠ p.2} := Fintype.card_congr ee
    _ = 30 := h

private theorem nat_card_stabilizer_pair (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {β : H ⧸ prodCenter E} (hβ : β ≠ ((1 : H) : H ⧸ prodCenter E)) :
    Nat.card ↥(MulAction.stabilizer H ((1 : H) : H ⧸ prodCenter E) ⊓
      MulAction.stabilizer H β) = 36 := by
  classical
  have h2 := isMultiplyPretransitive_two hperf hZ hA6 hE
  have hΩcard : Nat.card (H ⧸ prodCenter E) = 6 := nat_card_quotient hZ hA6 hE
  let α₀ : H ⧸ prodCenter E := ((1 : H) : H ⧸ prodCenter E)
  have hαβ : α₀ ≠ β := hβ.symm
  have horbit : MulAction.orbit H (α₀, β) =
      {p : (H ⧸ prodCenter E) × (H ⧸ prodCenter E) | p.1 ≠ p.2} := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      show (g • α₀) ≠ (g • β)
      intro h
      exact hαβ ((MulAction.toPermHom H (H ⧸ prodCenter E) g).injective (by
        simpa [MulAction.toPermHom_apply] using h))
    · intro hp
      have hp' : p.1 ≠ p.2 := hp
      obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hαβ hp'
      exact ⟨g, Prod.ext hg1 hg2⟩
  have hcardOrbit : Nat.card ↥(MulAction.orbit H (α₀, β)) = 30 := by
    rw [horbit]
    exact nat_card_ne_pairs hΩcard
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Fintype ↥(MulAction.orbit H (α₀, β)) := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer H (α₀, β)) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := H) (b := (α₀, β))
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  have hstab : MulAction.stabilizer H (α₀, β) =
      MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β := by
    ext g
    simp [MulAction.mem_stabilizer_iff, Prod.ext_iff]
  have h1 : Nat.card ↥(MulAction.orbit H (α₀, β)) = 30 := hcardOrbit
  have h2 : Nat.card H = 1080 := nat_card_eq_1080 hZ hA6
  rw [h1, h2] at h
  have h3 : Nat.card ↥(MulAction.stabilizer H (α₀, β)) = 36 := by omega
  rwa [hstab] at h3

private theorem sum_eq_zero_of_right_mul_char {𝕜 : Type*} [Field 𝕜] {G W : Type*}
    [Group G] [Fintype G] [AddCommGroup W] [Module 𝕜 W] (f : G → W) (k : G) (c : 𝕜) (hc : c ≠ 1)
    (hf : ∀ b : G, f (b * k) = c • f b) : ∑ b : G, f b = 0 := by
  classical
  have hbij : ∑ b : G, f (b * k) = ∑ b : G, f b :=
    Fintype.sum_equiv (Equiv.mulRight k) (fun b => f (b * k)) f (fun b => rfl)
  have h1 : c • (∑ b : G, f b) = ∑ b : G, f b := by
    calc c • (∑ b : G, f b) = ∑ b, c • f b := by rw [Finset.smul_sum]
      _ = ∑ b, f (b * k) := Finset.sum_congr rfl (fun b _ => (hf b).symm)
      _ = ∑ b : G, f b := hbij
  have h2 : (c - 1) • (∑ b : G, f b) = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)

private theorem exists_threeCycle_fixing_compl {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 6) {S : Finset Ω} (hS : S.card ≤ 3) :
    ∃ c : Equiv.Perm Ω, c.IsThreeCycle ∧ c ∈ alternatingGroup Ω ∧ ∀ x ∈ S, c x = x := by
  classical
  let T : Finset Ω := Finset.univ \ S
  have hTcard : 3 ≤ T.card := by
    change 3 ≤ (Finset.univ \ S).card
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hΩ]
    omega
  obtain ⟨a, haT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hT2 : 0 < (T.erase a).card := by
    rw [Finset.card_erase_of_mem haT]
    omega
  obtain ⟨b, hbT⟩ := Finset.card_pos.mp hT2
  have hbT' : b ∈ T := Finset.mem_of_mem_erase hbT
  have hba : b ≠ a := Finset.ne_of_mem_erase hbT
  have hT3 : 0 < ((T.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hbT, Finset.card_erase_of_mem haT]
    omega
  obtain ⟨c, hcT⟩ := Finset.card_pos.mp hT3
  have hcT' : c ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcT)
  have hca : c ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcT)
  have hcb : c ≠ b := Finset.ne_of_mem_erase hcT
  have hSdisj : ∀ x ∈ S, x ∉ T := fun x hx hxT => (Finset.mem_sdiff.mp hxT).2 hx
  let u' : Equiv.Perm Ω := Equiv.swap a b * Equiv.swap a c
  have hu'3 : u'.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hba.symm hca.symm hcb.symm
  refine ⟨u', hu'3, hu'3.mem_alternatingGroup, ?_⟩
  intro x hx
  have hax : x ≠ a := fun h => hSdisj x hx (h ▸ haT)
  have hbx : x ≠ b := fun h => hSdisj x hx (h ▸ hbT')
  have hcx : x ≠ c := fun h => hSdisj x hx (h ▸ hcT')
  show Equiv.swap a b (Equiv.swap a c x) = x
  rw [Equiv.swap_apply_of_ne_of_ne hax hcx, Equiv.swap_apply_of_ne_of_ne hax hbx]

private theorem exists_lift_of_mem_range {E : Subgroup H} {c : Equiv.Perm (H ⧸ prodCenter E)}
    (hc : c ∈ (MulAction.toPermHom H (H ⧸ prodCenter E)).range)
    {S : Finset (H ⧸ prodCenter E)} (hfix : ∀ x ∈ S, c x = x) :
    ∃ u : H, (∀ x ∈ S, u ∈ MulAction.stabilizer H x) ∧
      MulAction.toPermHom H (H ⧸ prodCenter E) u = c := by
  obtain ⟨u, hu⟩ := hc
  refine ⟨u, ?_, hu⟩
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  have h1 : u • x = c x := by
    rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply, hu]
  rw [h1, hfix x hx]

private theorem exists_threeCycle_fixing_pair (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {α δ : H ⧸ prodCenter E} (hαδ : α ≠ δ) :
    ∃ u : H, u ∈ MulAction.stabilizer H α ∧ u ∈ MulAction.stabilizer H δ ∧
      (MulAction.toPermHom H (H ⧸ prodCenter E) u).IsThreeCycle := by
  classical
  have hΩcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact nat_card_quotient hZ hA6 hE
  have hS : ({α, δ} : Finset (H ⧸ prodCenter E)).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa using hαδ
  obtain ⟨u', hu'3, hu'alt, hfix⟩ :=
    exists_threeCycle_fixing_compl hΩcard (S := {α, δ}) (by rw [hS]; norm_num)
  have hu'mem : u' ∈ (MulAction.toPermHom H (H ⧸ prodCenter E)).range := by
    rw [range_toPermHom_eq_alternating hperf hZ hA6 hE]
    exact hu'alt
  obtain ⟨u, hstab, hu⟩ := exists_lift_of_mem_range hu'mem hfix
  exact ⟨u, hstab α (by simp), hstab δ (by simp), by rw [hu]; exact hu'3⟩

private theorem exists_threeCycle_fixing_three (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {α β γ : H ⧸ prodCenter E} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    ∃ u : H, u ∈ MulAction.stabilizer H α ∧ u ∈ MulAction.stabilizer H β ∧
      u ∈ MulAction.stabilizer H γ ∧
      (MulAction.toPermHom H (H ⧸ prodCenter E) u).IsThreeCycle := by
  classical
  have hΩcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact nat_card_quotient hZ hA6 hE
  have hS : ({α, β, γ} : Finset (H ⧸ prodCenter E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hβγ
    · simp [hαβ, hαγ]
  obtain ⟨u', hu'3, hu'alt, hfix⟩ :=
    exists_threeCycle_fixing_compl hΩcard (S := {α, β, γ}) (by rw [hS])
  have hu'mem : u' ∈ (MulAction.toPermHom H (H ⧸ prodCenter E)).range := by
    rw [range_toPermHom_eq_alternating hperf hZ hA6 hE]
    exact hu'alt
  obtain ⟨u, hstab, hu⟩ := exists_lift_of_mem_range hu'mem hfix
  exact ⟨u, hstab α (by simp), hstab β (by simp), hstab γ (by simp), by rw [hu]; exact hu'3⟩

private noncomputable def pointProj {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V) {v : V}
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v) (hv : v ≠ 0)
    (α₀ β : H ⧸ prodCenter E)
    [Fintype ↥(MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β)] : V →ₗ[𝕜] V :=
  ∑ s : ↥(MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β),
    ((charHom ρ hEv hZs (hv := hv) α₀) ⟨s.1, s.2.1⟩ : 𝕜)⁻¹ • ρ (s : H)

private theorem pointProj_apply_self (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {β : H ⧸ prodCenter E} (hβ : β ≠ ((1 : H) : H ⧸ prodCenter E))
    [Fintype ↥(MulAction.stabilizer H ((1 : H) : H ⧸ prodCenter E) ⊓
      MulAction.stabilizer H β)] :
    pointProj ρ hEv hZs hv ((1 : H) : H ⧸ prodCenter E) β
        (pointV ρ v E ((1 : H) : H ⧸ prodCenter E)) =
      (36 : 𝕜) • pointV ρ v E ((1 : H) : H ⧸ prodCenter E) := by
  classical
  have hScard : Nat.card ↥(MulAction.stabilizer H ((1 : H) : H ⧸ prodCenter E) ⊓
      MulAction.stabilizer H β) = 36 :=
    nat_card_stabilizer_pair hperf hZ hA6 hE hβ
  have hχspec : ∀ s : ↥(MulAction.stabilizer H ((1 : H) : H ⧸ prodCenter E) ⊓
        MulAction.stabilizer H β),
      ρ (s : H) (pointV ρ v E ((1 : H) : H ⧸ prodCenter E)) =
        ((charHom ρ hEv hZs (hv := hv) ((1 : H) : H ⧸ prodCenter E)) ⟨s.1, s.2.1⟩ : 𝕜) •
          pointV ρ v E ((1 : H) : H ⧸ prodCenter E) :=
    fun s => charHom_spec ρ hEv hZs (hv := hv) ((1 : H) : H ⧸ prodCenter E) ⟨s.1, s.2.1⟩
  simp only [pointProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun s _ => by
    rw [hχspec s, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul])]
  rw [Finset.sum_const]
  calc (Finset.univ : Finset ↥(MulAction.stabilizer H ((1 : H) : H ⧸ prodCenter E) ⊓
        MulAction.stabilizer H β)).card • pointV ρ v E ((1 : H) : H ⧸ prodCenter E)
      = (Finset.univ.card : 𝕜) • pointV ρ v E ((1 : H) : H ⧸ prodCenter E) :=
        (Nat.cast_smul_eq_nsmul (R := 𝕜) _ _).symm
    _ = (36 : 𝕜) • pointV ρ v E ((1 : H) : H ⧸ prodCenter E) := by
        rw [Finset.card_univ, Fintype.card_eq_nat_card, hScard]
        norm_num

private theorem exists_threeCycle_fixing_stabilizer (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {α₀ β δ : H ⧸ prodCenter E} (hβ : β ≠ α₀) (hδ : δ ≠ α₀) :
    ∃ c : H, c ∈ MulAction.stabilizer H α₀ ∧ c ∈ MulAction.stabilizer H β ∧
      c ∈ MulAction.stabilizer H δ ∧
      (MulAction.toPermHom H (H ⧸ prodCenter E) c).IsThreeCycle := by
  by_cases hδβ : δ = β
  · subst hδβ
    obtain ⟨c, hcα, hcβ, hc3⟩ :=
      exists_threeCycle_fixing_pair hperf hZ hA6 hE hβ.symm
    exact ⟨c, hcα, hcβ, hcβ, hc3⟩
  · exact exists_threeCycle_fixing_three hperf hZ hA6 hE hβ.symm hδ.symm (Ne.symm hδβ)

private theorem char_mul_pointV_of_threeCycle {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V) {v : V}
    (hv : v ≠ 0) (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {S : Subgroup H} [Fintype ↥S] (χ : ↥S →* 𝕜ˣ)
    {δ : H ⧸ prodCenter E} {c : H} (hcS : c ∈ S)
    (hcδ : c ∈ MulAction.stabilizer H δ) :
    ∀ s : ↥S, (χ (s * ⟨c, hcS⟩) : 𝕜)⁻¹ •
        ρ ((s * ⟨c, hcS⟩ : ↥S) : H) (pointV ρ v E δ) =
      ((charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) / (χ ⟨c, hcS⟩ : 𝕜)) •
        ((χ s : 𝕜)⁻¹ • ρ (s : H) (pointV ρ v E δ)) := by
  intro s
  have hkδ : ρ ((⟨c, hcS⟩ : ↥S) : H) (pointV ρ v E δ) =
      (charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) • pointV ρ v E δ :=
    charHom_spec ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩
  calc (χ (s * ⟨c, hcS⟩) : 𝕜)⁻¹ •
        ρ ((s * ⟨c, hcS⟩ : ↥S) : H) (pointV ρ v E δ)
      = ((χ s : 𝕜) * (χ ⟨c, hcS⟩ : 𝕜))⁻¹ •
          ρ ((s : H) * ((⟨c, hcS⟩ : ↥S) : H)) (pointV ρ v E δ) := by
        rw [map_mul, Units.val_mul]
        rfl
    _ = ((χ s : 𝕜) * (χ ⟨c, hcS⟩ : 𝕜))⁻¹ •
          ρ (s : H) (ρ ((⟨c, hcS⟩ : ↥S) : H) (pointV ρ v E δ)) := by
        rw [rho_mul_apply]
    _ = ((χ s : 𝕜) * (χ ⟨c, hcS⟩ : 𝕜))⁻¹ •
          ρ (s : H) ((charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) • pointV ρ v E δ) := by
        rw [hkδ]
    _ = ((χ s : 𝕜) * (χ ⟨c, hcS⟩ : 𝕜))⁻¹ •
          ((charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) •
            ρ (s : H) (pointV ρ v E δ)) := by rw [map_smul]
    _ = ((charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) / (χ ⟨c, hcS⟩ : 𝕜)) •
          ((χ s : 𝕜)⁻¹ • ρ (s : H) (pointV ρ v E δ)) := by
        rw [mul_inv, smul_smul, smul_smul]
        congr 1
        field_simp

private theorem sum_eq_zero_of_char_ne {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V) {v : V}
    (hv : v ≠ 0) (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {S : Subgroup H} [Fintype ↥S] (χ : ↥S →* 𝕜ˣ)
    {δ : H ⧸ prodCenter E} {c : H} (hcS : c ∈ S)
    (hcδ : c ∈ MulAction.stabilizer H δ)
    (hχc : (χ ⟨c, hcS⟩ : 𝕜) ≠
      (charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜)) :
    ∑ s : ↥S, (χ s : 𝕜)⁻¹ • ρ (s : H) (pointV ρ v E δ) = 0 := by
  have hf := char_mul_pointV_of_threeCycle ρ hv hEv hZs χ hcS hcδ
  have hcne : ((charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) /
      (χ ⟨c, hcS⟩ : 𝕜)) ≠ 1 := by
    intro h1
    apply hχc
    have h2 : (charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) =
        (χ ⟨c, hcS⟩ : 𝕜) := by
      rw [div_eq_iff (Units.ne_zero _)] at h1
      simpa using h1
    exact h2.symm
  exact sum_eq_zero_of_right_mul_char
    (fun s : ↥S => (χ s : 𝕜)⁻¹ • ρ (s : H) (pointV ρ v E δ))
    ⟨c, hcS⟩ _ hcne hf

private theorem pointProj_apply_ne (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {α₀ β δ : H ⧸ prodCenter E} (hβ : β ≠ α₀) (hδ : δ ≠ α₀)
    [Fintype ↥(MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β)] :
    pointProj ρ hEv hZs hv α₀ β (pointV ρ v E δ) = 0 := by
  classical
  let S : Subgroup H := MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β
  obtain ⟨c, hcα, hcβ, hcδ, hc3⟩ :=
    exists_threeCycle_fixing_stabilizer hperf hZ hA6 hE hβ hδ
  have hcS : c ∈ S := ⟨hcα, hcβ⟩
  let χ : ↥S →* 𝕜ˣ :=
    (charHom ρ hEv hZs (hv := hv) α₀).comp (Subgroup.inclusion inf_le_left)
  have hχeq : ∀ s : ↥S, (χ s : 𝕜) =
      (charHom ρ hEv hZs (hv := hv) α₀ ⟨s.1, s.2.1⟩ : 𝕜) := fun s => rfl
  have hχc : (χ ⟨c, hcS⟩ : 𝕜) ≠
      (charHom ρ hEv hZs (hv := hv) δ ⟨c, hcδ⟩ : 𝕜) := by
    rw [hχeq]
    exact char_ne_of_threeCycle hperf hZ hA6 hE ρ hv hEv hZs hZv
      (α := α₀) (β := δ) hδ.symm hcα hcδ hc3
  have hsumχ := sum_eq_zero_of_char_ne ρ hv hEv hZs χ hcS hcδ hχc
  have hsum : ∑ s : ↥S,
      ((charHom ρ hEv hZs (hv := hv) α₀) ⟨s.1, s.2.1⟩ : 𝕜)⁻¹ •
        ρ (s : H) (pointV ρ v E δ) = 0 := by
    simpa only [hχeq] using hsumχ
  simp only [pointProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply]
  exact hsum

private theorem exists_transport_eq_zero {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H}
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {α₀ β : H ⧸ prodCenter E}
    [Fintype ↥(MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β)]
    (a : H ⧸ prodCenter E → 𝕜) (ha : ∑ δ, a δ • pointV ρ v E δ = 0)
    (γ : H ⧸ prodCenter E) :
    ∃ (h : H) (b : H ⧸ prodCenter E → 𝕜), (∀ δ, b δ ≠ 0) ∧ h • γ = α₀ ∧
      pointProj ρ hEv hZs hv α₀ β
        (∑ δ, a δ • (b δ • pointV ρ v E (h • δ))) = 0 := by
  classical
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H γ α₀
  have h2 : (∑ δ : H ⧸ prodCenter E, a δ • ρ h (pointV ρ v E δ)) = 0 := by
    have := congrArg (ρ h) ha
    simpa only [map_sum, map_smul, map_zero] using this
  choose b hb using fun δ : H ⧸ prodCenter E =>
    exists_smul_pointV_of_smul ρ hEv hZs (hv := hv) (g := h) (α := δ) (β := h • δ) rfl
  have h3 : (∑ δ : H ⧸ prodCenter E, a δ • (b δ • pointV ρ v E (h • δ))) = 0 := by
    rw [← h2]
    exact Finset.sum_congr rfl (fun δ _ => by rw [(hb δ).2])
  exact ⟨h, b, fun δ => (hb δ).1, hh, by rw [h3, map_zero]⟩

private theorem coeff_eq_zero_of_relation {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (h36 : (36 : 𝕜) ≠ 0)
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {α₀ β : H ⧸ prodCenter E}
    [Fintype ↥(MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β)]
    (heα : pointProj ρ hEv hZs hv α₀ β (pointV ρ v E α₀) =
      (36 : 𝕜) • pointV ρ v E α₀)
    (heδ : ∀ δ : H ⧸ prodCenter E, δ ≠ α₀ →
      pointProj ρ hEv hZs hv α₀ β (pointV ρ v E δ) = 0)
    (a : H ⧸ prodCenter E → 𝕜) (ha : ∑ δ, a δ • pointV ρ v E δ = 0)
    (γ : H ⧸ prodCenter E) : a γ = 0 := by
  classical
  obtain ⟨h, b, hbne, hh, h4⟩ :=
    exists_transport_eq_zero (α₀ := α₀) (β := β) ρ hv hEv hZs a ha γ
  rw [map_sum] at h4
  rw [Finset.sum_eq_single γ] at h4
  · rw [map_smul, map_smul, hh, heα] at h4
    have h5 : (a γ * b γ * (36 : 𝕜)) • pointV ρ v E α₀ = 0 := by
      rwa [smul_smul, smul_smul] at h4
    have h6 : a γ * b γ * (36 : 𝕜) = 0 := by
      rcases smul_eq_zero.mp h5 with h6 | h6
      · exact h6
      · exact absurd h6 (pointV_ne_zero ρ hv E α₀)
    have hab : a γ * b γ = 0 := by
      rcases mul_eq_zero.mp h6 with h | h
      · exact h
      · exact absurd h h36
    exact (mul_eq_zero.mp hab).resolve_right (hbne γ)
  · intro δ _ hδγ
    have hne : h • δ ≠ α₀ := by
      intro hcon
      apply hδγ
      have h1 : h • δ = h • γ := by rw [hcon, hh]
      have h2 : MulAction.toPerm h δ = MulAction.toPerm h γ := by
        rw [MulAction.toPerm_apply, MulAction.toPerm_apply]
        exact h1
      exact (MulAction.toPerm h).injective h2
    rw [map_smul, map_smul, heδ (h • δ) hne, smul_zero, smul_zero]
  · intro hγ
    exact absurd (Finset.mem_univ γ) hγ

private theorem linearIndependent_pointV (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] (h6 : (6 : 𝕜) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v) :
    LinearIndependent 𝕜 (fun α : H ⧸ prodCenter E => pointV ρ v E α) := by
  classical
  let α₀ : H ⧸ prodCenter E := ((1 : H) : H ⧸ prodCenter E)
  have hΩcard : Nat.card (H ⧸ prodCenter E) = 6 := nat_card_quotient hZ hA6 hE
  have hΩcard' : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact hΩcard
  have hpos : 1 < Fintype.card (H ⧸ prodCenter E) := by rw [hΩcard']; norm_num
  obtain ⟨β, hβ⟩ := Fintype.exists_ne_of_one_lt_card hpos α₀
  have hβ' : β ≠ α₀ := hβ
  haveI : Fintype ↥(MulAction.stabilizer H α₀ ⊓ MulAction.stabilizer H β) :=
    Fintype.ofFinite _
  have heα := pointProj_apply_self hperf hZ hA6 hE ρ hv hEv hZs hβ'
  have heδ : ∀ δ : H ⧸ prodCenter E, δ ≠ α₀ →
      pointProj ρ hEv hZs hv α₀ β (pointV ρ v E δ) = 0 :=
    fun δ hδ => pointProj_apply_ne hperf hZ hA6 hE ρ hv hEv hZs hZv hβ' hδ
  have h36 : (36 : 𝕜) ≠ 0 := by
    have h36' : (36 : 𝕜) = (6 : 𝕜) * 6 := by norm_num
    rw [h36']
    exact mul_ne_zero h6 h6
  rw [Fintype.linearIndependent_iff]
  exact fun a ha γ => coeff_eq_zero_of_relation h36 ρ hv hEv hZs heα heδ a ha γ

private theorem center_eq_one_of_sq_eq_one (hZ : Nat.card (Subgroup.center H) = 3)
    {z : H} (hz : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1) : z = 1 := by
  have hdvd : orderOf z ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard (s := Subgroup.center H) hz
    rw [hZ] at h
    exact h
  have h3 : z ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hz2, inv_one, mul_one]

private theorem exists_conj_center_decomp {E : Subgroup H} {t : H} {α : H ⧸ prodCenter E}
    (htα : t ∈ MulAction.stabilizer H α) :
    ∃ e z : H, e ∈ E ∧ z ∈ Subgroup.center H ∧
      t = (pointRep E α * e * (pointRep E α)⁻¹) * z := by
  classical
  let w : H := pointRep E α
  have hw : w • ((1 : H) : H ⧸ prodCenter E) = α := pointRep_smul E α
  have hb : w⁻¹ * t * w ∈ prodCenter E := by
    have h : (w⁻¹ * t * w) • ((1 : H) : H ⧸ prodCenter E) =
        ((1 : H) : H ⧸ prodCenter E) := by
      calc (w⁻¹ * t * w) • ((1 : H) : H ⧸ prodCenter E)
          = (w⁻¹ * t) • (w • ((1 : H) : H ⧸ prodCenter E)) := by rw [mul_smul]
        _ = (w⁻¹ * t) • α := by rw [hw]
        _ = w⁻¹ • (t • α) := by rw [mul_smul]
        _ = w⁻¹ • α := by rw [MulAction.mem_stabilizer_iff.mp htα]
        _ = w⁻¹ • (w • ((1 : H) : H ⧸ prodCenter E)) := by rw [hw]
        _ = (w⁻¹ * w) • ((1 : H) : H ⧸ prodCenter E) := by rw [mul_smul]
        _ = ((1 : H) : H ⧸ prodCenter E) := by rw [inv_mul_cancel, one_smul]
    rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h
  obtain ⟨e, he, z, hz, hez⟩ := mem_prodCenter.mp hb
  have htz : w * z * w⁻¹ = z := by
    have hcw : Commute w z := Subgroup.mem_center_iff.mp hz w
    rw [hcw.eq]
    group
  have ht_eq : t = (w * e * w⁻¹) * z := by
    calc t = w * (w⁻¹ * t * w) * w⁻¹ := by group
      _ = w * (e * z) * w⁻¹ := by rw [hez]
      _ = (w * e * w⁻¹) * (w * z * w⁻¹) := by group
      _ = (w * e * w⁻¹) * z := by rw [htz]
  exact ⟨e, z, he, hz, ht_eq⟩

private theorem sq_eq_one_of_conj_center (hZ : Nat.card (Subgroup.center H) = 3)
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {t w e z : H} (he : e ∈ E) (hz : z ∈ Subgroup.center H)
    (ht_eq : t = (w * e * w⁻¹) * z) (ht2 : t ^ 2 = 1) : z ^ 2 = 1 := by
  have hcomm : Commute (w * e * w⁻¹) z :=
    Subgroup.mem_center_iff.mp hz (w * e * w⁻¹)
  have hsq : (w * e * w⁻¹) ^ 2 * z ^ 2 = 1 := by
    rw [← hcomm.mul_pow, ← ht_eq]
    exact ht2
  have hwe2 : (w * e * w⁻¹) ^ 2 = (z ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hconj : w⁻¹ * (w * e * w⁻¹) ^ 2 * w = e ^ 2 := by
    rw [pow_two, pow_two]
    group
  have hzconj : w⁻¹ * (z ^ 2)⁻¹ * w = (z ^ 2)⁻¹ := by
    have hc : Commute w ((z ^ 2)⁻¹) := by
      have hz2 : z ^ 2 ∈ Subgroup.center H := (Subgroup.center H).pow_mem hz 2
      have h : Commute w (z ^ 2) := Subgroup.mem_center_iff.mp hz2 w
      exact h.inv_right.eq
    calc w⁻¹ * (z ^ 2)⁻¹ * w = w⁻¹ * ((z ^ 2)⁻¹ * w) := by group
      _ = w⁻¹ * (w * (z ^ 2)⁻¹) := by rw [← hc.eq]
      _ = (z ^ 2)⁻¹ := by group
  have he2z : e ^ 2 = (z ^ 2)⁻¹ := by
    rw [← hconj, ← hzconj, hwe2]
  have he2 : e ^ 2 = 1 := by
    have hmem : e ^ 2 ∈ E ⊓ Subgroup.center H :=
      ⟨E.pow_mem he 2, by
        rw [he2z]
        exact (Subgroup.center H).inv_mem ((Subgroup.center H).pow_mem hz 2)⟩
    rw [inf_center_eq_bot hE] at hmem
    simpa using hmem
  have h1 : (z ^ 2)⁻¹ = 1 := by rw [← he2z, he2]
  exact inv_eq_one.mp h1

private theorem exists_conj_decomp_of_mem_stabilizer
    (hZ : Nat.card (Subgroup.center H) = 3)
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {t : H} (ht2 : t ^ 2 = 1) {α : H ⧸ prodCenter E}
    (htα : t ∈ MulAction.stabilizer H α) :
    ∃ e : H, e ∈ E ∧ t = pointRep E α * e * (pointRep E α)⁻¹ := by
  obtain ⟨e, z, he, hz, ht_eq⟩ := exists_conj_center_decomp htα
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_conj_center hZ hE he hz ht_eq ht2
  have hz1 : z = 1 := center_eq_one_of_sq_eq_one hZ hz hz2
  exact ⟨e, he, by rw [ht_eq, hz1, mul_one]⟩


private theorem charHom_eq_one_of_mem_stabilizer
    (hZ : Nat.card (Subgroup.center H) = 3)
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {t : H} (ht2 : t ^ 2 = 1) {α : H ⧸ prodCenter E}
    (htα : t ∈ MulAction.stabilizer H α) :
    (charHom ρ hEv hZs (hv := hv) α ⟨t, htα⟩ : 𝕜) = 1 := by
  obtain ⟨e, he, ht_eq⟩ := exists_conj_decomp_of_mem_stabilizer hZ hE ht2 htα
  have hfix : ρ t (pointV ρ v E α) = pointV ρ v E α := by
    rw [ht_eq]
    calc ρ (pointRep E α * e * (pointRep E α)⁻¹) (pointV ρ v E α) =
          ρ (pointRep E α * e * (pointRep E α)⁻¹) (ρ (pointRep E α) v) := rfl
      _ = ρ ((pointRep E α * e * (pointRep E α)⁻¹) * pointRep E α) v :=
        (rho_mul_apply ρ _ _ _).symm
      _ = ρ (pointRep E α * e) v := by
        rw [show (pointRep E α * e * (pointRep E α)⁻¹) * pointRep E α =
          pointRep E α * e by group]
      _ = ρ (pointRep E α) (ρ e v) := rho_mul_apply ρ _ _ _
      _ = ρ (pointRep E α) v := by rw [hEv e he]
  apply smul_left_injective 𝕜 (pointV_ne_zero ρ hv E α)
  calc (charHom ρ hEv hZs (hv := hv) α ⟨t, htα⟩ : 𝕜) • pointV ρ v E α
      = ρ t (pointV ρ v E α) :=
        (charHom_spec ρ hEv hZs (hv := hv) α ⟨t, htα⟩).symm
    _ = pointV ρ v E α := hfix
    _ = (1 : 𝕜) • pointV ρ v E α := (one_smul _ _).symm


private theorem involution_fixed_card {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {c : Equiv.Perm Ω} (h2 : c ^ 2 = 1) (hne : c ≠ 1) (hcard : Fintype.card Ω = 6)
    (hEven : Even ((Fintype.card Ω - Fintype.card {x : Ω // c x = x}) / 2))
    (hsuppf : Fintype.card {x : Ω // c x = x} + c.support.card = 6) :
    Fintype.card {x : Ω // c x = x} = 2 := by
  have hf : Fintype.card {x : Ω // c x = x} = 2 := by
    have h2dvd : 2 ∣ c.support.card := Equiv.Perm.two_dvd_card_support h2
    have hpos : 0 < c.support.card := by
      rw [Finset.card_pos]
      by_contra hempty
      apply hne
      apply Equiv.Perm.ext
      intro x
      by_contra hx
      exact hempty ⟨x, Equiv.Perm.mem_support.mpr hx⟩
    have hle : c.support.card ≤ 6 := by
      have := Finset.card_le_univ c.support
      simpa [hcard] using this
    obtain ⟨m, hm⟩ := h2dvd
    have hmpos : 0 < m := by omega
    have hmle : m ≤ 3 := by omega
    have hEvenm : Even m := by
      have h6 : Fintype.card Ω - Fintype.card {x : Ω // c x = x} = c.support.card := by
        omega
      rw [h6, hm, mul_comm] at hEven
      simpa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] using hEven
    have hm2 : m = 2 := by
      rcases hEvenm with ⟨k, hk⟩
      omega
    omega
  exact hf

private theorem involution_fixed_support_card {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (c : Equiv.Perm Ω) (h2 : c ^ 2 = 1) (hne : c ≠ 1)
    (halt : c ∈ alternatingGroup Ω) (hcard : Fintype.card Ω = 6) :
    Fintype.card {x : Ω // c x = x} = 2 ∧ c.support.card = 4 := by
  classical
  have hsign : Equiv.Perm.sign c = 1 := Equiv.Perm.mem_alternatingGroup.mp halt
  have hsign2 := Equiv.Perm.sign_of_pow_two_eq_one h2
  have hfixeq : Fintype.card (Function.fixedPoints c) =
      Fintype.card {x : Ω // c x = x} := rfl
  rw [hfixeq] at hsign2
  rw [hsign2] at hsign
  have hEven : Even ((Fintype.card Ω - Fintype.card {x : Ω // c x = x}) / 2) := by
    by_contra hodd
    rw [neg_one_pow_eq_ite, if_neg hodd] at hsign
    exact absurd hsign (by decide : (-1 : ℤˣ) ≠ 1)
  have hsuppf : Fintype.card {x : Ω // c x = x} + c.support.card = 6 := by
    have hcompl := Fintype.card_subtype_compl (p := fun x : Ω => c x = x)
    have hsupp : Fintype.card {x : Ω // ¬ (c x = x)} = c.support.card :=
      Fintype.card_ofFinset (p := {x : Ω | ¬ (c x = x)}) c.support (fun x => by
        rw [Equiv.Perm.mem_support]
        rfl)
    rw [hsupp, hcard] at hcompl
    have hle : Fintype.card {x : Ω // c x = x} ≤ 6 := by
      simpa [hcard] using Fintype.card_subtype_le (fun x : Ω => c x = x)
    omega
  have hf := involution_fixed_card h2 hne hcard hEven hsuppf
  exact ⟨hf, by omega⟩

private theorem exists_first_transposition_pair {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {c : Equiv.Perm Ω} (h2 : c ^ 2 = 1) (hS : c.support.card = 4) :
    ∃ α₁ α₂ : Ω, c α₁ = α₂ ∧ c α₂ = α₁ ∧ α₁ ≠ α₂ ∧
      α₁ ∈ c.support ∧ α₂ ∈ c.support := by
  classical
  obtain ⟨α₁, hα₁⟩ := Finset.card_pos.mp (by rw [hS]; norm_num)
  have hcα₁ : c α₁ ≠ α₁ := Equiv.Perm.mem_support.mp hα₁
  let α₂ : Ω := c α₁
  have hcα₁₂ : c α₁ = α₂ := rfl
  have hcα₂ : c α₂ = α₁ := by
    have h := congrArg (fun f : Equiv.Perm Ω => f α₁) h2
    simpa [pow_two, α₂] using h
  have hα₂_mem : α₂ ∈ c.support := by
    rw [Equiv.Perm.mem_support]
    rw [hcα₂]
    exact hcα₁.symm
  have hα₁₂ : α₁ ≠ α₂ := by simpa [α₂] using hcα₁.symm
  exact ⟨α₁, α₂, hcα₁₂, hcα₂, hα₁₂, hα₁, hα₂_mem⟩

private theorem exists_two_transposition_pairs {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {c : Equiv.Perm Ω} (h2 : c ^ 2 = 1) (hS : c.support.card = 4) :
    ∃ α₁ α₂ α₃ α₄ : Ω,
      c α₁ = α₂ ∧ c α₂ = α₁ ∧ c α₃ = α₄ ∧ c α₄ = α₃ ∧
      α₁ ≠ α₂ ∧ α₃ ≠ α₄ ∧ α₁ ≠ α₃ ∧ α₁ ≠ α₄ ∧ α₂ ≠ α₃ ∧ α₂ ≠ α₄ ∧
      α₁ ∈ c.support ∧ α₂ ∈ c.support ∧ α₃ ∈ c.support ∧ α₄ ∈ c.support := by
  classical
  obtain ⟨α₁, α₂, hcα₁₂, hcα₂, hα₁₂, hα₁, hα₂_mem⟩ :=
    exists_first_transposition_pair h2 hS
  have hcard_erase : (c.support.erase α₁).card = 3 := by
    rw [Finset.card_erase_of_mem hα₁, hS]
  have hα₂_erase : α₂ ∈ c.support.erase α₁ :=
    Finset.mem_erase.mpr ⟨hα₁₂.symm, hα₂_mem⟩
  have hcard_erase2 : ((c.support.erase α₁).erase α₂).card = 2 := by
    rw [Finset.card_erase_of_mem hα₂_erase, hcard_erase]
  obtain ⟨α₃, hα₃⟩ := Finset.card_pos.mp (by rw [hcard_erase2]; norm_num)
  have hα₃_mem : α₃ ∈ c.support :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hα₃)
  have hα₃_ne1 : α₃ ≠ α₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hα₃)).1
  have hα₃_ne2 : α₃ ≠ α₂ := (Finset.mem_erase.mp hα₃).1
  have hcα₃ : c α₃ ≠ α₃ := Equiv.Perm.mem_support.mp hα₃_mem
  let α₄ : Ω := c α₃
  have hcα₃₄ : c α₃ = α₄ := rfl
  have hcα₄ : c α₄ = α₃ := by
    have h := congrArg (fun f : Equiv.Perm Ω => f α₃) h2
    simpa [pow_two, α₄] using h
  have hα₄_mem : α₄ ∈ c.support := by
    rw [Equiv.Perm.mem_support]
    rw [hcα₄]
    exact hcα₃.symm
  have hα₃₄ : α₃ ≠ α₄ := by simpa [α₄] using hcα₃.symm
  have hα₄_ne1 : α₄ ≠ α₁ := by
    intro h
    apply hα₃_ne2
    apply c.injective
    rw [hcα₃₄, h, hcα₂]
  have hα₄_ne2 : α₄ ≠ α₂ := by
    intro h
    apply hα₃_ne1
    apply c.injective
    rw [hcα₃₄, h, hcα₁₂]
  exact ⟨α₁, α₂, α₃, α₄, hcα₁₂, hcα₂, hcα₃₄, hcα₄, hα₁₂, hα₃₄, hα₃_ne1.symm,
    hα₄_ne1.symm, hα₃_ne2.symm, hα₄_ne2.symm, hα₁, hα₂_mem, hα₃_mem, hα₄_mem⟩
private theorem exists_involution_points {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (c : Equiv.Perm Ω) (h2 : c ^ 2 = 1) (hne : c ≠ 1)
    (halt : c ∈ alternatingGroup Ω) (hcard : Fintype.card Ω = 6) :
    ∃ α₁ α₂ α₃ α₄ α₅ α₆ : Ω,
      c α₁ = α₂ ∧ c α₂ = α₁ ∧ c α₃ = α₄ ∧ c α₄ = α₃ ∧
      c α₅ = α₅ ∧ c α₆ = α₆ ∧
      α₁ ≠ α₂ ∧ α₃ ≠ α₄ ∧ α₅ ≠ α₆ ∧
      α₁ ≠ α₃ ∧ α₁ ≠ α₄ ∧ α₂ ≠ α₃ ∧ α₂ ≠ α₄ ∧
      α₁ ≠ α₅ ∧ α₁ ≠ α₆ ∧ α₂ ≠ α₅ ∧ α₂ ≠ α₆ ∧
      α₃ ≠ α₅ ∧ α₃ ≠ α₆ ∧ α₄ ≠ α₅ ∧ α₄ ≠ α₆ := by
  classical
  obtain ⟨hf, hS⟩ := involution_fixed_support_card c h2 hne halt hcard
  obtain ⟨x₅, x₆, hx56⟩ :=
    Fintype.exists_pair_of_one_lt_card (α := {x : Ω // c x = x}) (by rw [hf]; norm_num)
  obtain ⟨α₁, α₂, α₃, α₄, hc12, hc21, hc34, hc43, hd12, hd34, hd13, hd14, hd23, hd24,
    hα₁, hα₂, hα₃, hα₄⟩ := exists_two_transposition_pairs h2 hS
  have hα₅ : c x₅.1 = x₅.1 := x₅.2
  have hα₆ : c x₆.1 = x₆.1 := x₆.2
  have hx56' : x₅.1 ≠ x₆.1 := fun h => hx56 (Subtype.ext h)
  have hα₅_supp : x₅.1 ∉ c.support := by
    rw [Equiv.Perm.mem_support]
    exact not_not.mpr hα₅
  have hα₆_supp : x₆.1 ∉ c.support := by
    rw [Equiv.Perm.mem_support]
    exact not_not.mpr hα₆
  exact ⟨α₁, α₂, α₃, α₄, x₅.1, x₆.1, hc12, hc21, hc34, hc43, hα₅, hα₆,
    hd12, hd34, hx56', hd13, hd14, hd23, hd24,
    (fun h => hα₅_supp (h ▸ hα₁)), (fun h => hα₆_supp (h ▸ hα₁)),
    (fun h => hα₅_supp (h ▸ hα₂)), (fun h => hα₆_supp (h ▸ hα₂)),
    (fun h => hα₅_supp (h ▸ hα₃)), (fun h => hα₆_supp (h ▸ hα₃)),
    (fun h => hα₅_supp (h ▸ hα₄)), (fun h => hα₆_supp (h ▸ hα₄))⟩


private theorem rho_mul_self_apply {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {t : H} (ht2 : t ^ 2 = 1) (x : V) :
    ρ (t * t) x = x := by
  rw [show t * t = 1 by rw [← pow_two]; exact ht2, map_one]
  exact Module.End.one_apply x

private theorem fix_of_mem_stabilizer {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (hZ : Nat.card (Subgroup.center H) = 3)
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {t : H} (ht2 : t ^ 2 = 1) {α : H ⧸ prodCenter E}
    (htα : t ∈ MulAction.stabilizer H α) :
    ρ t (pointV ρ v E α) = pointV ρ v E α := by
  have h := charHom_eq_one_of_mem_stabilizer hZ hE ρ hv hEv hZs ht2 htα
  calc ρ t (pointV ρ v E α) =
        (charHom ρ hEv hZs (hv := hv) α ⟨t, htα⟩ : 𝕜) • pointV ρ v E α :=
      charHom_spec ρ hEv hZs (hv := hv) α ⟨t, htα⟩
    _ = pointV ρ v E α := by rw [h, one_smul]

private theorem finrank_ker_ge_four {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 H V) {t : H} {w : Fin 4 → V}
    (hw : ∀ i, w i ∈ LinearMap.ker (ρ t - 1))
    (hli : LinearIndependent 𝕜 w) :
    4 ≤ Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) := by
  have hliKer : LinearIndependent 𝕜
      (Set.codRestrict w (LinearMap.ker (ρ t - 1)) hw) :=
    hli.codRestrict _ hw
  haveI : FiniteDimensional 𝕜 (LinearMap.ker (ρ t - 1)) :=
    FiniteDimensional.finiteDimensional_submodule _
  have h := LinearIndependent.fintype_card_le_finrank hliKer
  simpa using h

private theorem smul_eq_of_toPermHom_eq {E : Subgroup H} {t : H} {a b : H ⧸ prodCenter E}
    (h : MulAction.toPermHom H (H ⧸ prodCenter E) t a = b) : t • a = b := by
  have h1 : t • a = (MulAction.toPermHom H (H ⧸ prodCenter E) t) • a := by
    rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply]
    rfl
  rw [h1]
  exact h

private theorem four_vectors_mem_ker {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V)
    {v : V} {t : H} {α₁ α₂ α₃ α₄ α₅ α₆ : H ⧸ prodCenter E} {b₁ b₃ : 𝕜}
    (hfix5 : ρ t (pointV ρ v E α₅) = pointV ρ v E α₅)
    (hfix6 : ρ t (pointV ρ v E α₆) = pointV ρ v E α₆)
    (hu₁ : ρ t (pointV ρ v E α₁ + b₁ • pointV ρ v E α₂) =
      pointV ρ v E α₁ + b₁ • pointV ρ v E α₂)
    (hu₃ : ρ t (pointV ρ v E α₃ + b₃ • pointV ρ v E α₄) =
      pointV ρ v E α₃ + b₃ • pointV ρ v E α₄) :
    ∀ i : Fin 4,
      ![(pointV ρ v E α₅), (pointV ρ v E α₆),
        pointV ρ v E α₁ + b₁ • pointV ρ v E α₂,
        pointV ρ v E α₃ + b₃ • pointV ρ v E α₄] i ∈ LinearMap.ker (ρ t - 1) := by
  intro i
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  fin_cases i
  · exact hfix5
  · exact hfix6
  · exact hu₁
  · exact hu₃

private theorem involution_not_mem_center (hZ : Nat.card (Subgroup.center H) = 3)
    {t : H} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : t ∉ Subgroup.center H := by
  intro ht
  have hdvd : orderOf t ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard (s := Subgroup.center H) ht
    rw [hZ] at h
    exact h
  have h3 : t ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have h2 : t ^ 3 = t := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, ht2, one_mul]
  rw [h2] at h3
  exact ht1 h3

private theorem involution_sigma_props (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {t : H} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    (MulAction.toPermHom H (H ⧸ prodCenter E) t) ^ 2 = 1 ∧
      (MulAction.toPermHom H (H ⧸ prodCenter E) t) ≠ 1 ∧
      (MulAction.toPermHom H (H ⧸ prodCenter E) t) ∈
        alternatingGroup (H ⧸ prodCenter E) ∧
      Fintype.card (H ⧸ prodCenter E) = 6 := by
  classical
  have htZ := involution_not_mem_center hZ ht2 ht1
  have hσker : (MulAction.toPermHom H (H ⧸ prodCenter E)).ker = Subgroup.center H :=
    ker_toPermHom_quotient hZ hA6 hE
  have hσrange : (MulAction.toPermHom H (H ⧸ prodCenter E)).range =
      alternatingGroup (H ⧸ prodCenter E) := range_toPermHom_eq_alternating hperf hZ hA6 hE
  have hσt2 : (MulAction.toPermHom H (H ⧸ prodCenter E) t) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hσt_ne : (MulAction.toPermHom H (H ⧸ prodCenter E) t) ≠ 1 := by
    intro h
    apply htZ
    rw [← hσker]
    exact MonoidHom.mem_ker.mpr h
  have hσt_alt : (MulAction.toPermHom H (H ⧸ prodCenter E) t) ∈
      alternatingGroup (H ⧸ prodCenter E) := by
    rw [← hσrange]
    exact ⟨t, rfl⟩
  have hΩcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact nat_card_quotient hZ hA6 hE
  exact ⟨hσt2, hσt_ne, hσt_alt, hΩcard⟩

private theorem exists_block_fixed_vector {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V) {v : V}
    (hv : v ≠ 0) (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    {t : H} (ht2 : t ^ 2 = 1) {α β : H ⧸ prodCenter E}
    (hα : t • α = β) (hβ : t • β = α) :
    ∃ b : 𝕜, b ≠ 0 ∧ ρ t (pointV ρ v E α) = b • pointV ρ v E β ∧
      ρ t (pointV ρ v E α + b • pointV ρ v E β) =
        pointV ρ v E α + b • pointV ρ v E β := by
  obtain ⟨b, hbne, hb⟩ := exists_smul_pointV_of_smul ρ hEv hZs (hv := hv) hα
  obtain ⟨b', hb'ne, hb'⟩ := exists_smul_pointV_of_smul ρ hEv hZs (hv := hv) hβ
  have hbb' : b * b' = 1 := by
    have h := rho_mul_self_apply ρ ht2 (pointV ρ v E α)
    rw [rho_mul_apply, hb, map_smul, hb', smul_smul] at h
    exact smul_left_injective 𝕜 (pointV_ne_zero ρ hv E α) (by simpa using h)
  refine ⟨b, hbne, hb, ?_⟩
  show ρ t (pointV ρ v E α + b • pointV ρ v E β) =
    pointV ρ v E α + b • pointV ρ v E β
  rw [map_add, map_smul, hb, hb', smul_smul, hbb', one_smul]
  abel

private theorem sum_single_pointV {𝕜 : Type*} [Field 𝕜] {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] {E : Subgroup H} (ρ : Representation 𝕜 H V) {v : V}
    (i : H ⧸ prodCenter E) (a : 𝕜) :
    ∑ γ : H ⧸ prodCenter E, (Pi.single i a : H ⧸ prodCenter E → 𝕜) γ •
      pointV ρ v E γ = a • pointV ρ v E i := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem four_vectors_independent (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] (h6 : (6 : 𝕜) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {α₁ α₂ α₃ α₄ α₅ α₆ : H ⧸ prodCenter E} {b₁ b₃ : 𝕜}
    (hd12 : α₁ ≠ α₂) (hd34 : α₃ ≠ α₄) (hd56 : α₅ ≠ α₆)
    (hd13 : α₁ ≠ α₃) (hd14 : α₁ ≠ α₄) (hd23 : α₂ ≠ α₃) (hd24 : α₂ ≠ α₄)
    (hd15 : α₁ ≠ α₅) (hd16 : α₁ ≠ α₆) (hd25 : α₂ ≠ α₅) (hd26 : α₂ ≠ α₆)
    (hd35 : α₃ ≠ α₅) (hd36 : α₃ ≠ α₆) (hd45 : α₄ ≠ α₅) (hd46 : α₄ ≠ α₆) :
    LinearIndependent 𝕜
      ![(pointV ρ v E α₅), (pointV ρ v E α₆),
        pointV ρ v E α₁ + b₁ • pointV ρ v E α₂,
        pointV ρ v E α₃ + b₃ • pointV ρ v E α₄] := by
  classical
  have hli := linearIndependent_pointV hperf hZ hA6 hE h6 ρ hv hEv hZs hZv
  have hli6 := (Fintype.linearIndependent_iff.mp hli)
  rw [Fintype.linearIndependent_iff]
  intro a ha
  rw [Fin.sum_univ_four] at ha
  change a 0 • pointV ρ v E α₅ + a 1 • pointV ρ v E α₆ +
    a 2 • (pointV ρ v E α₁ + b₁ • pointV ρ v E α₂) +
    a 3 • (pointV ρ v E α₃ + b₃ • pointV ρ v E α₄) = 0 at ha
  have hexp : a 0 • pointV ρ v E α₅ + a 1 • pointV ρ v E α₆ +
      a 2 • (pointV ρ v E α₁ + b₁ • pointV ρ v E α₂) +
      a 3 • (pointV ρ v E α₃ + b₃ • pointV ρ v E α₄) =
      a 0 • pointV ρ v E α₅ + a 1 • pointV ρ v E α₆ +
        a 2 • pointV ρ v E α₁ + (a 2 * b₁) • pointV ρ v E α₂ +
        a 3 • pointV ρ v E α₃ + (a 3 * b₃) • pointV ρ v E α₄ := by
    module
  rw [hexp] at ha
  let c : H ⧸ prodCenter E → 𝕜 :=
    Pi.single α₅ (a 0) + Pi.single α₆ (a 1) + Pi.single α₁ (a 2) +
      Pi.single α₂ (a 2 * b₁) + Pi.single α₃ (a 3) + Pi.single α₄ (a 3 * b₃)
  have hcsum : (∑ γ : H ⧸ prodCenter E, c γ • pointV ρ v E γ) = 0 := by
    rw [show (∑ γ, c γ • pointV ρ v E γ) =
        a 0 • pointV ρ v E α₅ + a 1 • pointV ρ v E α₆ +
          a 2 • pointV ρ v E α₁ + (a 2 * b₁) • pointV ρ v E α₂ +
          a 3 • pointV ρ v E α₃ + (a 3 * b₃) • pointV ρ v E α₄ by
      simp only [c, Pi.add_apply, add_smul, Finset.sum_add_distrib, sum_single_pointV,
        zero_smul]]
    rw [← ha]
  have hc := hli6 c hcsum
  intro i
  fin_cases i
  · have h1 := hc α₅
    simpa [c, Pi.single_apply, hd15, hd16, hd13.symm, hd14.symm, hd12.symm,
      hd23.symm, hd24.symm, hd25.symm, hd26.symm, hd35.symm, hd36.symm,
      hd45.symm, hd46.symm, hd56, hd34.symm] using h1
  · have h1 := hc α₆
    simpa [c, Pi.single_apply, hd56.symm, hd16.symm, hd26.symm, hd36.symm,
      hd46.symm, hd15.symm, hd25.symm, hd35.symm, hd45.symm, hd12.symm,
      hd13.symm, hd14.symm, hd23.symm, hd24.symm, hd34.symm] using h1
  · have h1 := hc α₁
    simpa [c, Pi.single_apply, hd13, hd14, hd12, hd15, hd16, hd23, hd24,
      hd25, hd26, hd35, hd36, hd45, hd46, hd34, hd56] using h1
  · have h1 := hc α₃
    simpa [c, Pi.single_apply, hd13.symm, hd23.symm, hd34, hd35, hd36,
      hd12.symm, hd14.symm, hd24.symm, hd45, hd46, hd56, hd15.symm,
      hd16.symm, hd25.symm, hd26.symm] using h1

private theorem four_le_finrank_ker (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] (h6 : (6 : 𝕜) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0)
    (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v)
    {t : H} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    4 ≤ Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) := by
  classical
  obtain ⟨hσt2, hσt_ne, hσt_alt, hΩcard⟩ := involution_sigma_props hperf hZ hA6 hE ht2 ht1
  let σ : H →* Equiv.Perm (H ⧸ prodCenter E) :=
    MulAction.toPermHom H (H ⧸ prodCenter E)
  obtain ⟨α₁, α₂, α₃, α₄, α₅, α₆, hc12, hc21, hc34, hc43, hc55, hc66,
    hd12, hd34, hd56, hd13, hd14, hd23, hd24, hd15, hd16, hd25, hd26,
    hd35, hd36, hd45, hd46⟩ :=
    exists_involution_points (σ t) hσt2 hσt_ne hσt_alt hΩcard
  have hstab : ∀ (a b : H ⧸ prodCenter E),
      MulAction.toPermHom H (H ⧸ prodCenter E) t a = b → t • a = b :=
    fun a b h => smul_eq_of_toPermHom_eq h
  have hfix5 : ρ t (pointV ρ v E α₅) = pointV ρ v E α₅ :=
    fix_of_mem_stabilizer hZ hE ρ hv hEv hZs ht2 (by
      rw [MulAction.mem_stabilizer_iff]; exact hstab α₅ α₅ hc55)
  have hfix6 : ρ t (pointV ρ v E α₆) = pointV ρ v E α₆ :=
    fix_of_mem_stabilizer hZ hE ρ hv hEv hZs ht2 (by
      rw [MulAction.mem_stabilizer_iff]; exact hstab α₆ α₆ hc66)
  obtain ⟨b₁, hb₁ne, hb₁, hu₁fix⟩ :=
    exists_block_fixed_vector ρ hv hEv hZs ht2 (hstab α₁ α₂ hc12) (hstab α₂ α₁ hc21)
  obtain ⟨b₃, hb₃ne, hb₃, hu₃fix⟩ :=
    exists_block_fixed_vector ρ hv hEv hZs ht2 (hstab α₃ α₄ hc34) (hstab α₄ α₃ hc43)
  let u₁ : V := pointV ρ v E α₁ + b₁ • pointV ρ v E α₂
  let u₃ : V := pointV ρ v E α₃ + b₃ • pointV ρ v E α₄
  have hli4 : LinearIndependent 𝕜
      ![(pointV ρ v E α₅), (pointV ρ v E α₆), u₁, u₃] :=
    four_vectors_independent hperf hZ hA6 hE h6 ρ hv hEv hZs hZv
      hd12 hd34 hd56 hd13 hd14 hd23 hd24 hd15 hd16 hd25 hd26 hd35 hd36 hd45 hd46
  have hmem := four_vectors_mem_ker ρ hfix5 hfix6 hu₁fix hu₃fix
  exact finrank_ker_ge_four ρ hmem hli4


theorem six_le_finrank_and_four_le_finrank_fixed {H : Type*} [Group H] [Finite H]
    (hperf : Group.IsPerfect H) (hZ : Nat.card (Subgroup.center H) = 3)
    (hA6 : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6)))
    {E : Subgroup H} (hE : Nonempty (E ≃* alternatingGroup (Fin 5)))
    {𝕜 : Type*} [Field 𝕜] (h6 : (6 : 𝕜) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 H V) {v : V} (hv : v ≠ 0) (hEv : ∀ e ∈ E, ρ e v = v)
    (hZs : ∀ z ∈ Subgroup.center H, ∃ μ : 𝕜, ρ z v = μ • v)
    (hZv : ∀ z ∈ Subgroup.center H, z ≠ 1 → ρ z v ≠ v) :
    6 ≤ Module.finrank 𝕜 V ∧
      ∀ t : H, t ^ 2 = 1 → t ≠ 1 → 4 ≤ Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) := by
  constructor
  · have hli := linearIndependent_pointV hperf hZ hA6 hE h6 ρ hv hEv hZs hZv
    have hcard : Fintype.card (H ⧸ prodCenter E) = 6 := by
      rw [← Nat.card_eq_fintype_card]
      exact nat_card_quotient hZ hA6 hE
    have h := LinearIndependent.fintype_card_le_finrank hli
    rwa [hcard] at h
  · intro t ht2 ht1
    exact four_le_finrank_ker hperf hZ hA6 hE h6 ρ hv hEv hZs hZv ht2 ht1

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end
