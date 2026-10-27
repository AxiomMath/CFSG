module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

namespace CFSG.StandardType.F4ExplicitPos.FixedTorus

variable {τ : Tag} {R S : Type} [Field R] [Field S]

theorem torusGroup_le_adjointGroup
    (τ : Tag) (R : Type*) [Field R] :
    torusGroup τ R ≤ adjointGroup τ R := by
  rw [torusGroup, Subgroup.closure_le]
  rintro x ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

theorem bcGL_torusElt
    (φ : R →+* S) (i : Fin τ.rank) (t : Rˣ) :
    bcGL φ (torusElt τ R i t) = torusElt τ S i (Units.map φ.toMonoidHom t) := by
  rw [torusElt, torusElt, map_mul, bcGL_weylElt, bcGL_weylElt,
    show Units.map φ.toMonoidHom (-1 : Rˣ) = (-1 : Sˣ) from Units.ext (by simp)]

theorem bcGL_torusCoordHom
    (φ : R →+* S) (t : Fin τ.rank → Rˣ) :
    bcGL φ ((torusCoordHom τ R t : torusGroup τ R) : ModGL τ R) =
      ((torusCoordHom τ S (fun i => Units.map φ.toMonoidHom (t i)) : torusGroup τ S) :
        ModGL τ S) := by
  rw [coe_torusCoordHom, coe_torusCoordHom, map_list_prod, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun i => bcGL_torusElt φ i (t i))

theorem units_map_entrywiseHom_torusCoordHom
    {K : Type} [Field K]
    (Fr : K →+* K) (t : Fin Tag.F4.rank → Kˣ) :
    Units.map (entrywiseHom Fr)
        ((torusCoordHom Tag.F4 K t : torusGroup Tag.F4 K) : ModGL Tag.F4 K) =
      ((torusCoordHom Tag.F4 K (fun i => Units.map Fr.toMonoidHom (t i)) :
        torusGroup Tag.F4 K) : ModGL Tag.F4 K) := by
  have hm : (Units.map (entrywiseHom Fr) : ModGL Tag.F4 K →* ModGL Tag.F4 K) =
      bcGL (τ := Tag.F4) Fr := by
    apply MonoidHom.ext
    intro g
    exact Units.ext rfl
  rw [hm, bcGL_torusCoordHom]

theorem fixed_torus_mem_map_adjointGroup
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {h : ModGL Tag.F4 Ω} (hh : h ∈ torusGroup Tag.F4 Ω)
    (hfix : Units.map (entrywiseHom Fr) h = h) :
    h ∈ (adjointGroup Tag.F4 K).map (bcGL (algebraMap K Ω)) := by
  classical
  obtain ⟨t, ht⟩ := torusCoordHom_surjective (τ := Tag.F4) (R := Ω) ⟨h, hh⟩
  have hcoord : (fun i => Units.map Fr.toMonoidHom (t i)) = t := by
    apply torusCoordHom_injective_of_mul_eq_one (τ := Tag.F4) (R := Ω) cartan_mul_cartanInv_F4
    apply Subtype.ext
    rw [← units_map_entrywiseHom_torusCoordHom Fr t, ht, hfix]
  have hFrval : ∀ i, Fr ((t i : Ωˣ) : Ω) = ((t i : Ωˣ) : Ω) := fun i =>
    congrArg (fun u : Ωˣ => (u : Ω)) (congrFun hcoord i)
  have hrange : ∀ i, ((t i : Ωˣ) : Ω) ∈ Set.range (algebraMap K Ω) := by
    intro i
    apply mem_range_algebraMap_of_pow_card_eq
    rw [← hFr ((t i : Ωˣ) : Ω), hFrval i]
  choose a ha using hrange
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i h
    have ht0 : ((t i : Ωˣ) : Ω) = 0 := by rw [← ha i, h, map_zero]
    exact (t i).ne_zero ht0
  let u : Fin Tag.F4.rank → Kˣ := fun i => Units.mk0 (a i) (ha0 i)
  have hu : ∀ i, Units.map (algebraMap K Ω).toMonoidHom (u i) = t i := by
    intro i
    apply Units.ext
    change (algebraMap K Ω) (a i) = ((t i : Ωˣ) : Ω)
    exact ha i
  refine Subgroup.mem_map.mpr ⟨(torusCoordHom Tag.F4 K u : torusGroup Tag.F4 K), ?_, ?_⟩
  · exact torusGroup_le_adjointGroup Tag.F4 K (torusCoordHom Tag.F4 K u).2
  · rw [bcGL_torusCoordHom]
    rw [show (fun i => Units.map (algebraMap K Ω).toMonoidHom (u i)) = t from funext hu]
    exact congrArg Subtype.val ht

end CFSG.StandardType.F4ExplicitPos.FixedTorus

end

end
