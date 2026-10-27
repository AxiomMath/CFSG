module

public import CFSG.Quasithin.EmptyFaithful.S143EM
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G]

theorem isSylowTwoOf_map_range' {G W : Type*} [Group G] [Group W] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* W) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

section Action

variable (Z U H : Subgroup G) (hHN : H ≤ Subgroup.normalizer (Z : Set G))
  (hHU : H ≤ Subgroup.normalizer (U : Set G))

omit hHN in
theorem secMk_mem_normalizer_tildeOf {a : ↥(Subgroup.normalizer (Z : Set G))}
    (ha : (a : G) ∈ Subgroup.normalizer (U : Set G)) :
    secMk (Subgroup.normalizer (Z : Set G)) Z a ∈
      Subgroup.normalizer (tildeOf Z U : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)) :=
  secMk_mem_normalizer_secImg ha

noncomputable def actTilde : ↥H →* MulAut ↥(tildeOf Z U) :=
  (conjAct (tildeOf Z U)).comp
    (MonoidHom.codRestrict
      ((secMk (Subgroup.normalizer (Z : Set G)) Z).comp (Subgroup.inclusion hHN))
      (Subgroup.normalizer (tildeOf Z U : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)))
      (fun h => secMk_mem_normalizer_tildeOf Z U (hHU h.2)))

theorem actTilde_apply (h : ↥H) (w : ↥(tildeOf Z U)) :
    ((actTilde Z U H hHN hHU h w : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩ * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩)⁻¹ :=
  conjAct_coe_apply _ _ _

theorem range_actTilde :
    (actTilde Z U H hHN hHU).range = autOn (tildeOf Z H) (tildeOf Z U) := by
  ext σ
  rw [MonoidHom.mem_range, autOn, Subgroup.mem_map]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩,
      secMk_mem_normalizer_tildeOf Z U (hHU h.2)⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (secMk_mem_secImg (X := H) (x := ⟨h, hHN h.2⟩) h.2)
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hxH, hxy⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨x, hxH⟩, ?_⟩
    show conjAct (tildeOf Z U) _ = conjAct (tildeOf Z U) y
    congr 1
    exact Subtype.ext hxy

theorem actTilde_eq_one_iff (hUN : U ≤ Subgroup.normalizer (Z : Set G)) (h : ↥H) :
    actTilde Z U H hHN hHU h = 1 ↔ ∀ u ∈ U, (h : G) * u * (h : G)⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h1 u hu
    have hw : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ ∈ tildeOf Z U :=
      secMk_mem_secImg (X := U) (x := ⟨u, hUN hu⟩) hu
    have h2 := actTilde_apply Z U H hHN hHU h ⟨_, hw⟩
    rw [h1] at h2
    have h3 : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩ *
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨h, hHN h.2⟩)⁻¹ =
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ := h2.symm
    have h4 : secMk (Subgroup.normalizer (Z : Set G)) Z
        (⟨h, hHN h.2⟩ * ⟨u, hUN hu⟩ * ⟨h, hHN h.2⟩⁻¹ * ⟨u, hUN hu⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h3]; simp
    exact secMk_eq_one_iff.mp h4
  · intro hall
    refine MulEquiv.ext fun w => Subtype.ext ?_
    obtain ⟨x, hxU, hxw⟩ := mem_secImg.1 w.2
    rw [actTilde_apply, MulAut.one_apply, ← hxw]
    have h5 : (h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹ ∈ Z := hall x hxU
    have h6 : secMk (Subgroup.normalizer (Z : Set G)) Z
        (⟨h, hHN h.2⟩ * x * ⟨h, hHN h.2⟩⁻¹ * x⁻¹) = 1 :=
      secMk_eq_one_iff.mpr h5
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h6
    exact mul_inv_eq_one.mp h6

end Action


section Model

variable [Finite G] {Z U H E T₀ : Subgroup G}

theorem card_le_of_invariant
    (hHN : H ≤ Subgroup.normalizer (Z : Set G)) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hUN : U ≤ Subgroup.normalizer (Z : Set G)) (hEU : E ≤ U) (hZE : Z ≤ E)
    (hcomm : IsMulCommutative ↥(tildeOf Z U)) (hexp : ∀ w : ↥(tildeOf Z U), w * w = 1)
    (q : ↥(tildeOf Z U) → ZMod 2) (hq1 : IsQuadraticFormOn q) (hq2 : IsNondegQuadratic q)
    (hq3 : IsPlusType q) (hq4 : Nat.card ↥(tildeOf Z U) = 16)
    (hq5 : ∀ (x : SecQuot (Subgroup.normalizer (Z : Set G)) Z) (hx : x ∈ tildeOf Z U)
        (u : ↥(Subgroup.normalizer (Z : Set G))), (u : G) ∈ U →
          secMk (Subgroup.normalizer (Z : Set G)) Z u = x → (q ⟨x, hx⟩ = 0 ↔ (u : G) ^ 2 = 1))
    (hq6 : autOn (tildeOf Z H) (tildeOf Z U) = orthogonalGroupOf q)
    (hT : IsSylowTwoOf T₀ H) (hTE : T₀ ≤ Subgroup.normalizer (E : Set G))
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    Nat.card E ≤ 2 * Nat.card Z := by
  let _ : CommGroup ↥(tildeOf Z U) :=
    { (inferInstance : Group ↥(tildeOf Z U)) with mul_comm := fun a b => hcomm.is_comm.comm a b }
  obtain ⟨L₁, L₂, t, hS, hsing⟩ := exists_ofourStruct_of_plusType (W := ↥(tildeOf Z U)) (q := q)
    hexp hq4 hq1 hq2 hq3
  set ρ := actTilde Z U H hHN hHU with hρ
  have hrange : ρ.range = orthogonalGroupOf q := (range_actTilde Z U H hHN hHU).trans hq6
  have hT' : IsSylowTwoOf ((T₀.subgroupOf H).map ρ) (orthogonalGroupOf q) := by
    have := isSylowTwoOf_map_range' hT ρ
    rwa [hrange] at this
  set F : Subgroup ↥(tildeOf Z U) := (tildeOf Z E).subgroupOf (tildeOf Z U) with hFdef
  have hF : ∀ f ∈ F, q f = 0 := by
    intro f hf
    obtain ⟨x, hxE, hxf⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.mp hf)
    exact (hq5 f f.2 x (hEU hxE) hxf).mpr (hE2 _ hxE)
  have hinv : ∀ x ∈ (T₀.subgroupOf H).map ρ, ∀ f ∈ F, x f ∈ F := by
    intro x hx f hf
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hx
    have hτE : ((⟨τ, hHN τ.2⟩ : ↥(Subgroup.normalizer (Z : Set G))) : G) ∈
        Subgroup.normalizer (E : Set G) := hTE (Subgroup.mem_subgroupOf.mp hτ)
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [actTilde_apply]
    exact secMk_conj_mem_secImg hτE (Subgroup.mem_subgroupOf.mp hf)
  have hFc : Nat.card F ≤ 2 := card_le_two_of_invariant hS hsing hT' F hF hinv
  set f₀ : ↥E →* SecQuot (Subgroup.normalizer (Z : Set G)) Z :=
    (secMk (Subgroup.normalizer (Z : Set G)) Z).comp (Subgroup.inclusion (hEU.trans hUN)) with hf₀
  have hcard := Subgroup.card_ker_mul_card_range f₀
  have hkerZ : f₀.ker = Z.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact secMk_eq_one_iff
  have hrangeE : f₀.range = tildeOf Z E := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact secMk_mem_secImg (X := E) (x := Subgroup.inclusion (hEU.trans hUN) e) e.2
    · intro hy
      obtain ⟨x, hxE, hxy⟩ := mem_secImg.1 hy
      exact ⟨⟨x, hxE⟩, hxy⟩
  have h1 : Nat.card f₀.ker = Nat.card Z := by
    rw [hkerZ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  have h2 : Nat.card f₀.range = Nat.card F := by
    rw [hrangeE]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono hEU)).toEquiv).symm
  rw [h1, h2] at hcard
  calc Nat.card E = Nat.card Z * Nat.card F := hcard.symm
    _ ≤ Nat.card Z * 2 := Nat.mul_le_mul_left _ hFc
    _ = 2 * Nat.card Z := mul_comm _ _

end Model

end S143

end CFSG.Quasithin
