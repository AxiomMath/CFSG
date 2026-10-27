module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCRedInj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNRedA6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNRedKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TC914R

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

variable {X : Type} [Group X]

@[expose, reducible] def CoordB (Lb Tb : Subgroup X) : Type :=
  ↥(tcN1 Lb Tb) ⧸ CFSG.pCore 2 ↥(tcN1 Lb Tb)

@[expose, reducible] def coordπ (Lb Tb : Subgroup X) : ↥(tcN1 Lb Tb) →* CoordB Lb Tb :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥(tcN1 Lb Tb))

variable {Lb Tb : Subgroup X}

theorem coordπ_surjective : Function.Surjective (coordπ Lb Tb) :=
  QuotientGroup.mk'_surjective _

theorem coordπ_eq_one_iff (x : ↥(tcN1 Lb Tb)) :
    coordπ Lb Tb x = 1 ↔ (x : X) ∈ pCoreOf 2 (tcN1 Lb Tb) := by
  rw [CFSG.mem_openPCoreOf_iff]
  exact QuotientGroup.eq_one_iff x

theorem coord_o2 : ∀ K : Subgroup (CoordB Lb Tb), K.Normal → IsPGroup 2 K → K = ⊥ :=
  NF914.eq_bot_of_normal_of_isPGroup_two (coordπ Lb Tb) coordπ_surjective coordπ_eq_one_iff

theorem coord_normal : (NFW.barSub (coordπ Lb Tb) Lb).Normal :=
  NFW.barSub_normal coordπ_surjective (sup_le le_normalizer inf_le_right)

theorem coord_sup : NFW.barSub (coordπ Lb Tb) Lb ⊔ NFW.barSub (coordπ Lb Tb) Tb = ⊤ := by
  have htop : Lb.subgroupOf (tcN1 Lb Tb) ⊔ (tcT1 Lb Tb).subgroupOf (tcN1 Lb Tb) = ⊤ := by
    apply Subgroup.map_injective (tcN1 Lb Tb).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left, Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  have h := congrArg (Subgroup.map (coordπ Lb Tb)) htop
  rw [Subgroup.map_sup, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ coordπ_surjective] at h
  rw [eq_top_iff, ← h]
  exact sup_le_sup_left (NFW.barSub_mono inf_le_left) _

namespace Pre

variable (c : Pre Lb Tb)
include c

theorem coord_isPGroup : IsPGroup 2 (NFW.barSub (coordπ Lb Tb) Tb) :=
  NFW.isPGroup_barSub c.sylow.isPGroup

theorem coord_sylow [Finite X] : IsSylowIn 2 (NFW.barSub (coordπ Lb Tb) Tb) ⊤ := by
  refine ⟨le_top, c.coord_isPGroup, fun hd => c.isSylowIn_T1.not_dvd_relIndex ?_⟩
  rw [relIndex_top_right] at hd
  have h1 : 2 ∣ Tb.relIndex (tcN1 Lb Tb) := hd.trans (Subgroup.index_map_dvd _ coordπ_surjective)
  have hT : Tb ⊓ tcN1 Lb Tb = tcT1 Lb Tb :=
    le_antisymm (fun x hx => ⟨hx.1, (sup_le le_normalizer inf_le_right) hx.2⟩)
      (le_inf inf_le_left le_sup_right)
  rwa [← inf_relIndex_right, hT] at h1

theorem coordπ_injOn [Finite X] {x y : ↥(tcN1 Lb Tb)} (hx : (x : X) ∈ Lb) (hy : (y : X) ∈ Lb)
    (h : coordπ Lb Tb x = coordπ Lb Tb y) : x = y := by
  have h1 : coordπ Lb Tb (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((x⁻¹ * y : ↥(tcN1 Lb Tb)) : X) ∈ pCoreOf 2 (tcN1 Lb Tb) ⊓ Lb :=
    ⟨(coordπ_eq_one_iff _).mp h1, by simpa using mul_mem (inv_mem hx) hy⟩
  rw [c.pCore_inf_Lb, mem_bot] at h2
  exact inv_mul_eq_one.mp (Subtype.ext h2)

theorem nonempty_coordEquiv [Finite X] :
    Nonempty (↥Lb ≃* ↥(NFW.barSub (coordπ Lb Tb) Lb)) := by
  set K := Lb.subgroupOf (tcN1 Lb Tb)
  set f : ↥K →* CoordB Lb Tb := (coordπ Lb Tb).comp K.subtype
  have hf : Function.Injective f := fun a b h => Subtype.ext (c.coordπ_injOn a.2 b.2 h)
  have hr : f.range = NFW.barSub (coordπ Lb Tb) Lb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact ⟨(Subgroup.subgroupOfEquivOfLe le_sup_left).symm.trans
    ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr))⟩

theorem mem_centralizer_coordπ_iff [Finite X] (y : ↥(tcN1 Lb Tb)) :
    coordπ Lb Tb y ∈ centralizer (NFW.barSub (coordπ Lb Tb) Lb : Set (CoordB Lb Tb)) ↔
      (y : X) ∈ centralizer (Lb : Set X) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro l hl
    have hlN : l ∈ tcN1 Lb Tb := mem_sup_left hl
    have hc := mem_centralizer_iff.mp h _ (NFW.mem_barSub_of_mem (π := coordπ Lb Tb) hlN hl)
    have hyL : (y : X) ∈ normalizer (Lb : Set X) := (sup_le le_normalizer inf_le_right) y.2
    have h1 : ((y * ⟨l, hlN⟩ * y⁻¹ : ↥(tcN1 Lb Tb)) : X) ∈ Lb :=
      (mem_normalizer_iff.mp hyL l).mp hl
    have h2 : coordπ Lb Tb (y * ⟨l, hlN⟩ * y⁻¹) = coordπ Lb Tb ⟨l, hlN⟩ := by
      rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right]
    have h4 : (y : X) * l * (y : X)⁻¹ = l := congrArg Subtype.val (c.coordπ_injOn h1 hl h2)
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4.symm
  · intro h
    rw [mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h' : l * y = y * l := Subtype.ext (mem_centralizer_iff.mp h _ hl)
    rw [← map_mul, ← map_mul, h']

theorem exists_coord_automizer [Finite X] {A : Type} [Group A]
    (φb : ↥(normalizer (Lb : Set X)) →* A) (hs : Function.Surjective φb)
    (hk : ∀ y, φb y = 1 ↔ (y : X) ∈ centralizer (Lb : Set X)) :
    ∃ ρ : CoordB Lb Tb →* A, Function.Surjective ρ ∧
      ρ.ker = centralizer (NFW.barSub (coordπ Lb Tb) Lb : Set (CoordB Lb Tb)) := by
  have hN1 : tcN1 Lb Tb ≤ normalizer (Lb : Set X) := sup_le le_normalizer inf_le_right
  set ρ₀ : ↥(tcN1 Lb Tb) →* A := φb.comp (Subgroup.inclusion hN1)
  have hle : CFSG.pCore 2 ↥(tcN1 Lb Tb) ≤ ρ₀.ker := fun y hy => by
    rw [MonoidHom.mem_ker]
    exact (hk _).mpr (c.pCore_le_centralizer ((CFSG.mem_openPCoreOf_iff y).mpr hy))
  set ρ := QuotientGroup.lift (CFSG.pCore 2 ↥(tcN1 Lb Tb)) ρ₀ hle
  have hρ : ∀ y, ρ (coordπ Lb Tb y) = ρ₀ y := fun y => QuotientGroup.lift_mk _ _ _
  refine ⟨ρ, fun a => ?_, ?_⟩
  · obtain ⟨⟨x, hx⟩, rfl⟩ := hs a
    obtain ⟨z, hz, y, hy, rfl⟩ := c.exists_mul_of_mem_normalizer hx
    have hzN : z ∈ normalizer (Lb : Set X) := Subgroup.centralizer_le_normalizer _ hz
    have h1 : φb ⟨z, hzN⟩ = 1 := (hk _).mpr hz
    have he : (⟨z * y, hx⟩ : ↥(normalizer (Lb : Set X))) =
        ⟨z, hzN⟩ * Subgroup.inclusion hN1 ⟨y, hy⟩ := rfl
    refine ⟨coordπ Lb Tb ⟨y, hy⟩, ?_⟩
    rw [hρ, he, map_mul, h1, one_mul]
    rfl
  · ext b
    obtain ⟨y, rfl⟩ := coordπ_surjective b
    rw [MonoidHom.mem_ker, hρ, c.mem_centralizer_coordπ_iff]
    exact hk _

theorem center_eq_bot_of_card [Finite X] {A : Type} [Group A] (ρ : CoordB Lb Tb →* A)
    (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = centralizer (NFW.barSub (coordπ Lb Tb) Lb : Set (CoordB Lb Tb)))
    (hq : CFSG.IsQuasisimple ↥(NFW.barSub (coordπ Lb Tb) Lb)) (hA : Nat.card A = 336) :
    center ↥(NFW.barSub (coordπ Lb Tb) Lb) = ⊥ := by
  have : Finite (CoordB Lb Tb) := Finite.of_surjective _ coordπ_surjective
  have := coord_normal (Lb := Lb) (Tb := Tb)
  have hcb := NF914.eq_bot_of_forall_commutator_mem_center (Cb := ρ.ker) hq c.coord_isPGroup
    coord_sup coord_o2 (fun x hx l hl => by
      rw [hρk] at hx
      rw [(mem_centralizer_iff.mp hx l hl).symm, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    (dvd_of_eq (by rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ρ hρs,
      Subgroup.card_top, hA]))
  rw [eq_bot_iff]
  intro z hz
  have hzC : ((z : ↥(NFW.barSub (coordπ Lb Tb) Lb)) : CoordB Lb Tb) ∈ ρ.ker := by
    rw [hρk, mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  rw [hcb, mem_bot] at hzC
  exact Subtype.ext hzC

theorem isCoordGroup914_of_pre [Finite X] {A : Type} [Group A]
    (φb : ↥(normalizer (Lb : Set X)) →* A) (hs : Function.Surjective φb)
    (hk : ∀ y, φb y = 1 ↔ (y : X) ∈ centralizer (Lb : Set X))
    (hA : CFSG.Quasithin.F6.IsPGL2 7 A ∨ Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨
      Inputs1719.IsM10 A ∨ CFSG.Quasithin.F6.IsPGL2 9 A) :
    IsCoordGroup914 (CoordB Lb Tb) (NFW.barSub (coordπ Lb Tb) Lb)
      (NFW.barSub (coordπ Lb Tb) Tb) ∧ IsPGroup 3 (center ↥Lb) := by
  have : Finite (CoordB Lb Tb) := Finite.of_surjective _ coordπ_surjective
  obtain ⟨e⟩ := c.nonempty_coordEquiv
  set Lh := NFW.barSub (coordπ Lb Tb) Lb
  have := coord_normal (Lb := Lb) (Tb := Tb)
  have hq : CFSG.IsQuasisimple ↥Lh := CFSG.LocalCores.isQuasisimple_of_mulEquiv e c.quasi
  have hCL := NF914.centralizer_le_of_isPGroup_quotient c.coord_isPGroup coord_sup coord_o2
  obtain ⟨ρ, hρs, hρk⟩ := c.exists_coord_automizer φb hs hk
  have h3 : IsPGroup 3 (center ↥Lh) → IsPGroup 3 (center ↥Lb) := fun h =>
    h.of_equiv (Subgroup.centerCongr e).symm
  by_cases hZ : center ↥Lh = ⊥
  · have hker : ρ.ker = ⊥ := by
      rw [hρk, NF914.centralizer_eq_map_center hCL, hZ, Subgroup.map_bot]
    let eB : CoordB Lb Tb ≃* A :=
      MulEquiv.ofBijective ρ ⟨(MonoidHom.ker_eq_bot_iff ρ).mp hker, hρs⟩
    refine ⟨⟨c.coord_sylow, inferInstance, Or.inl ⟨?_, isPerfect_iff.mp hq.1, ?_⟩⟩, h3 ?_⟩
    · have := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact (nontrivial_iff_ne_bot _).mp inferInstance
    · rcases hA with h | h | h | h
      · exact Or.inl (CFSG.GroupTheory.isPGL2_of_mulEquiv eB h)
      · exact Or.inr (Or.inr (Or.inr (Inputs1719.isAutOf_of_mulEquiv eB h)))
      · exact Or.inr (Or.inr (Or.inl (Inputs1719.isM10_of_mulEquiv eB h)))
      · exact Or.inr (Or.inl (CFSG.GroupTheory.isPGL2_of_mulEquiv eB h))
    · rw [hZ]
      exact IsPGroup.of_bot
  · have hA' : CFSG.Quasithin.F6.IsPGL2 9 A ∨ Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨
        Inputs1719.IsM10 A := by
      rcases hA with h | h | h | h
      · exact absurd (c.center_eq_bot_of_card ρ hρs hρk hq
          (CFSG.GroupTheory.card_of_isPGL2_seven h)) hZ
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    have hcard := NF914.card_center_eq_three hq (isPerfect_iff.mp hq.1) ρ hρs hρk hA'
      (NF914.odd_card_center_of_normal coord_o2) hZ
    refine ⟨⟨c.coord_sylow, inferInstance, Or.inr ⟨hq, hcard, hCL, A, inferInstance, ρ, hρs, hρk,
      hA'⟩⟩, h3 (IsPGroup.of_card (n := 1) (by rw [hcard, pow_one]))⟩

end Pre

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TC914R
