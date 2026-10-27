module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open Matrix CFSG.Quasithin

@[expose] def embedJ {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G} (hJX : J ≤ X)
    (ε : ↥X ≃* Γ) : ↥J →* Γ :=
  ε.toMonoidHom.comp (Subgroup.inclusion hJX)

theorem embedJ_injective {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G} (hJX : J ≤ X)
    (ε : ↥X ≃* Γ) : Function.Injective (embedJ hJX ε) := by
  intro a b hab
  exact Subgroup.inclusion_injective hJX (ε.injective hab)

theorem embedJ_apply {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G} (hJX : J ≤ X)
    (ε : ↥X ≃* Γ) (g : ↥J) : embedJ hJX ε g = ε ⟨(g : G), hJX g.2⟩ := by
  rfl

theorem sylow_le_range_embedJ {G Γ : Type} [Group G] [Group Γ] {X J S : Subgroup G}
    (hJX : J ≤ X) (hSJ : S ≤ J) (ε : ↥X ≃* Γ) {T : Sylow 2 Γ}
    (hT : (T : Subgroup Γ) = (S.subgroupOf X).map ε.toMonoidHom) :
    (T : Subgroup Γ) ≤ (embedJ hJX ε).range := by
  intro y hy
  rw [hT, Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [Subgroup.mem_subgroupOf] at hx
  refine ⟨⟨(x : G), hSJ hx⟩, ?_⟩
  rw [embedJ_apply]
  exact congrArg ε (Subtype.ext rfl)

theorem range_le_normalizer_map {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G}
    (hJX : J ≤ X) (ε : ↥X ≃* Γ) (R₀ : Subgroup ↥J) [R₀.Normal] :
    (embedJ hJX ε).range ≤
      Subgroup.normalizer ((R₀.map (embedJ hJX ε) : Subgroup Γ) : Set Γ) := by
  have hR₀ : R₀.Normal := inferInstance
  intro g' hg'
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hg'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hh
    exact Subgroup.mem_map.mpr ⟨g * r * g⁻¹, hR₀.conj_mem r hr g, by simp⟩
  · intro hh
    obtain ⟨r, hr, hr'⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * r * g, by simpa using hR₀.conj_mem r hr g⁻¹, ?_⟩
    calc embedJ hJX ε (g⁻¹ * r * g)
        = (embedJ hJX ε g)⁻¹ * embedJ hJX ε r * embedJ hJX ε g := by simp
      _ = (embedJ hJX ε g)⁻¹ * (embedJ hJX ε g * h * (embedJ hJX ε g)⁻¹)
            * embedJ hJX ε g := by rw [hr']
      _ = h := by group

theorem not_isSolvable_range_embedJ {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G}
    (hJX : J ≤ X) (ε : ↥X ≃* Γ) (h : ¬ Group.IsSolvable ↥J) :
    ¬ Group.IsSolvable ↥(embedJ hJX ε).range := by
  intro hs
  haveI := hs
  exact h (Group.isSolvable_of_isSolvable_injective
    (f := (embedJ hJX ε).rangeRestrict)
    ((MonoidHom.rangeRestrict_injective_iff (f := embedJ hJX ε)).mpr
      (embedJ_injective hJX ε)))

theorem isPGroup_map_embedJ {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G} (hJX : J ≤ X)
    (ε : ↥X ≃* Γ) {p : ℕ} {R₀ : Subgroup ↥J} (h : IsPGroup p ↥R₀) :
    IsPGroup p ↥(R₀.map (embedJ hJX ε)) := by
  exact h.map (embedJ hJX ε)

theorem natCard_map_embedJ {G Γ : Type} [Group G] [Group Γ] {X J : Subgroup G} (hJX : J ≤ X)
    (ε : ↥X ≃* Γ) (R₀ : Subgroup ↥J) :
    Nat.card ↥(R₀.map (embedJ hJX ε)) = Nat.card ↥R₀ := by
  exact Subgroup.card_map_of_injective (embedJ_injective hJX ε)

theorem exists_fixed_vector {W : Type} [CommGroup W] {X : Subgroup (MulAut W)} {I : Subgroup W}
    {F : Type} [Field F] {b c : F} (ε : ↥X ≃* ↥(Omega6 F b c))
    (ψ : ↥I ≃* Multiplicative (Idx → F))
    (hψ : ∀ (x : ↥X) (s : ↥I) (hx : (x : MulAut W) (s : W) ∈ I),
      ψ ⟨(x : MulAut W) (s : W), hx⟩ = Multiplicative.ofAdd
        (((ε x : GL Idx F) : Matrix Idx Idx F).mulVec (Multiplicative.toAdd (ψ s))))
    {J : Subgroup (MulAut W)} (hJX : J ≤ X) (h : I ⊓ fixV J ≠ ⊥) :
    ∃ v : Idx → F, v ≠ 0 ∧ ∀ g : ↥J,
      ((embedJ hJX ε g : GL Idx F) : Matrix Idx Idx F).mulVec v = v := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have haI : (a : W) ∈ I := (Subgroup.mem_inf.mp a.2).1
  have hafix : (a : W) ∈ fixV J := (Subgroup.mem_inf.mp a.2).2
  let s : ↥I := ⟨(a : W), haI⟩
  let v : Idx → F := Multiplicative.toAdd (ψ s)
  have hs_ne : s ≠ 1 := by
    intro hs1
    exact ha1 (Subtype.ext (by simpa [s] using congrArg Subtype.val hs1))
  have hψs_ne : ψ s ≠ 1 := fun h1 => hs_ne (ψ.injective (by simpa using h1))
  have hv_ne : v ≠ 0 := by
    intro hv0
    apply hψs_ne
    have h2 : (ψ s).toAdd = (1 : Multiplicative (Idx → F)).toAdd := by
      simpa [v] using hv0
    exact Multiplicative.toAdd.injective h2
  refine ⟨v, hv_ne, ?_⟩
  intro g
  let x : ↥X := ⟨(g : MulAut W), hJX g.2⟩
  have hgfix : (x : MulAut W) (s : W) = (s : W) := (mem_fixV.mp hafix) g g.2
  have hx : (x : MulAut W) (s : W) ∈ I := by rw [hgfix]; exact s.2
  have hsub : (⟨(x : MulAut W) (s : W), hx⟩ : ↥I) = s := Subtype.ext hgfix
  have hψx := hψ x s hx
  rw [hsub] at hψx
  have hv_eq : (((ε x : GL Idx F) : Matrix Idx Idx F).mulVec v) = v := by
    have h' := congrArg Multiplicative.toAdd hψx
    simpa [v] using h'.symm
  rw [embedJ_apply]
  simpa [x] using hv_eq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
