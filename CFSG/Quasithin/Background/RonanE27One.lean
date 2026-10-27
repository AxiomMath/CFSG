module

public import CFSG.Quasithin.Vol2.E2SevenKG7Close
public import CFSG.Quasithin.Background.RonanE27Model
public import CFSG.Quasithin.Background.RonanE27Six

public section

namespace CFSG.Quasithin.RonanE27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Ch3E213M B6
  CFSG.Quasithin.Ch3E213M.P6E CFSG.QuasithinUnique.Borel252.A6

section Transport

variable {G : Type} [Group G]

private theorem subgroupOf_inf' {X : Subgroup G} (A B : Subgroup G) :
    (A ⊓ B).subgroupOf X = A.subgroupOf X ⊓ B.subgroupOf X := by
  ext x
  simp [Subgroup.mem_subgroupOf]

private theorem mem_normalizer_subgroupOf_iff' {X U : Subgroup G} (hUX : U ≤ X) (y : ↥X) :
    y ∈ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (y : G) ∈ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUX, Subgroup.mem_subgroupOf]

private theorem mem_normalizer_map_subtype_iff' {X : Subgroup G} (P : Subgroup ↥X) (y : ↥X) :
    (y : G) ∈ Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) ↔
      y ∈ Subgroup.normalizer (P : Set ↥X) := by
  have hP : (P.map X.subtype).subgroupOf X = P :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective P
  rw [← mem_normalizer_subgroupOf_iff' (Subgroup.map_subtype_le P), hP]

private theorem map_subtype_conjugate {X : Subgroup G} (E : Subgroup ↥X) (x : ↥X) :
    (CFSG.conjugate E x).map X.subtype = conjSub ((x : G)⁻¹) (E.map X.subtype) := by
  ext y
  rw [mem_conjSub]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    simp [mul_assoc]
  · rintro ⟨w, hw, hwy⟩
    refine ⟨x⁻¹ * w * x, ⟨w, hw, by simp⟩, ?_⟩
    have : (w : G) = x * y * (x : G)⁻¹ := by simpa using hwy
    simp [this, mul_assoc]

end Transport

theorem e27Sp4One_holds : E2.E27Sp4One := by
  intro G _ _ X T M K V h hker hKX hXN hC hKT hSp hD hMK hnX hV4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.minParabolic
  have hTX : T ≤ X := hmp.isSylow.1
  have hMX : M ≤ X := hmp.maximal.1.le
  have hVX : V ≤ X := h.le_H
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hAlt : IsAlt 6 ↥(K.subgroupOf X) := by
    have hK6 : IsAlt 6 ↥K := by
      have h' : E2.IsSp4Prime 1 ↥K = IsAlt 6 ↥K := rfl
      exact cast h' hSp
    obtain ⟨f⟩ := hK6
    exact ⟨(Subgroup.subgroupOfEquivOfLe hKX).trans f⟩
  have hS : IsSylowTwoOf (T.subgroupOf X) ⊤ := P5.isSylowTwoOf_subgroupOf_top hmp.isSylow
  have hC' : ∀ a : ↥X, (∀ x ∈ K.subgroupOf X, a * x = x * a) → a = 1 := by
    intro a ha
    have hmem : (a : G) ∈ X ⊓ Subgroup.centralizer (K : Set G) := by
      refine ⟨a.2, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have := ha ⟨k, hKX hk⟩ (Subgroup.mem_subgroupOf.2 hk)
      exact (congrArg Subtype.val this).symm
    rw [hC, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hKS : K.subgroupOf X ⊔ T.subgroupOf X = ⊤ := Ch3E213M.subgroupOf_sup_eq_top hKT.symm
  have hTKX : T ⊓ K ≤ X := inf_le_left.trans hTX
  have hNX : (Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)).subgroupOf X =
      Subgroup.normalizer (((T ⊓ K).subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    Subgroup.subgroupOf_normalizer_eq hTKX
  have hSK : T.subgroupOf X ⊓ K.subgroupOf X = (T ⊓ K).subgroupOf X :=
    (subgroupOf_inf' T K).symm
  have hBorel : ∃ S₀ : Subgroup ↥X, IsSylowTwoOf S₀ (K.subgroupOf X) ∧
      M.subgroupOf X ⊓ K.subgroupOf X =
        K.subgroupOf X ⊓ Subgroup.normalizer (S₀ : Set ↥X) := by
    refine ⟨T.subgroupOf X ⊓ K.subgroupOf X,
      A4.isSylowTwoOf_inf_normal hS le_top
        (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge, ?_⟩
    rw [hSK, ← hNX, ← subgroupOf_inf' (X := X) M K,
      ← subgroupOf_inf' (X := X) K (Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)), hMK]
  have hdiag : ∀ P : Subgroup ↥X, IsMaxParabolic2 (K.subgroupOf X) P →
      K.subgroupOf X ⊓ Subgroup.normalizer ((T.subgroupOf X ⊓ K.subgroupOf X : Subgroup ↥X) :
        Set ↥X) ≤ P → ¬ T.subgroupOf X ≤ Subgroup.normalizer (P : Set ↥X) := by
    intro P hP hle hSP
    refine hD (P.map X.subtype) (E2.isMaxParabolic2_map_subtype hKX hP) ?_ ?_
    · rintro g ⟨hgK, hgN⟩
      have hgN' : (⟨g, hKX hgK⟩ : ↥X) ∈
          Subgroup.normalizer (((T ⊓ K).subgroupOf X : Subgroup ↥X) : Set ↥X) :=
        (mem_normalizer_subgroupOf_iff' hTKX _).2 hgN
      exact ⟨⟨g, hKX hgK⟩, hle ⟨Subgroup.mem_subgroupOf.2 hgK, by rwa [hSK]⟩, rfl⟩
    · intro t ht
      exact (mem_normalizer_map_subtype_iff' P ⟨t, hTX ht⟩).2
        (hSP (Subgroup.mem_subgroupOf.2 ht))
  have hEmap : (V.subgroupOf X).map X.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVX
  have hSB : T.subgroupOf X ≤ M.subgroupOf X := fun x hx => hmp.le hx
  have hES : V.subgroupOf X ≤ T.subgroupOf X := fun x hx => h.le_T hx
  have hSE : T.subgroupOf X ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    fun s hs => (mem_normalizer_map_subtype_iff' (V.subgroupOf X) s).1
      (by rw [hEmap]; exact h.normal_T hs)
  have hE2 : ∀ x ∈ V.subgroupOf X, x * x = 1 := fun x hx =>
    Subtype.ext (by simpa [pow_two] using h.elem.2 (x : G) hx)
  have hE4 : 4 ≤ Nat.card (V.subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv]
    exact hV4
  haveI : (K.subgroupOf X).Normal := hKn
  obtain ⟨χ, ⟨x, hxK, hFeq⟩, hBF, hSF, hEZ, hS06⟩ :=
    model_sp4_one_coord (K := K.subgroupOf X) (S := T.subgroupOf X) (B := M.subgroupOf X)
      (E := V.subgroupOf X) hS hC' hAlt hKS hdiag hBorel hSB hES hSE hE2 hE4
  have hEF : V.subgroupOf X ≤ K.subgroupOf X ⊔ V.subgroupOf X := le_sup_right
  have hxF : x ∈ K.subgroupOf X ⊔ V.subgroupOf X :=
    (le_sup_left : K.subgroupOf X ≤ K.subgroupOf X ⊔ V.subgroupOf X) hxK
  generalize K.subgroupOf X ⊔ V.subgroupOf X = F at χ hFeq hBF hSF hEZ hEF hxF
  let ψ : P6 →* ↥X := F.subtype.comp χ.symm.toMonoidHom
  let φ : P6 →* G := X.subtype.comp ψ
  have hφinj : Function.Injective φ :=
    X.subtype_injective.comp (F.subtype_injective.comp χ.symm.injective)
  have hφtop : (⊤ : Subgroup P6).map φ = F.map X.subtype := by
    show (⊤ : Subgroup P6).map (X.subtype.comp (F.subtype.comp χ.symm.toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ χ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomap : ∀ Q : Subgroup G,
      Q.comap φ = ((Q.subgroupOf X).subgroupOf F).map χ.toMonoidHom := by
    intro Q
    ext y
    constructor
    · intro hy
      exact ⟨χ.symm y, hy, χ.apply_symm_apply y⟩
    · rintro ⟨z, hz, rfl⟩
      show φ (χ z) ∈ Q
      have : φ (χ z) = (((z : ↥F) : ↥X) : G) := by simp [φ, ψ]
      rw [this]
      exact hz
  have hT : T.comap φ = S06 := by
    rw [hcomap, ← Subgroup.inf_subgroupOf_right (T.subgroupOf X) F, hSF]
  have hM : M.comap φ = S06 := by
    rw [hcomap, ← Subgroup.inf_subgroupOf_right (M.subgroupOf X) F, hBF, hSF]
  have hV : V.comap φ = Z6 := by
    rw [hcomap]
    exact hEZ
  have hVr : V ≤ (⊤ : Subgroup P6).map φ := by
    rw [hφtop, ← hEmap]
    exact Subgroup.map_mono hEF
  have hgx : φ (χ ⟨x, hxF⟩)⁻¹ = (x : G)⁻¹ := by
    simp [φ, ψ]
  have hgen : (⊤ : Subgroup P6).map φ = V ⊔ conjSub (φ (χ ⟨x, hxF⟩)⁻¹) V := by
    rw [hgx, hφtop, hFeq, Subgroup.map_sup, map_subtype_conjugate, hEmap]
  refine ⟨(⊤ : Subgroup P6).map φ, isInIHTVC_of_permSix hφinj ?_ hT hM hV hVr hgen hS06
    ⟨1, E2.isSp4Prime_oTwoUpper_star hmp hker hKX hXN hC hKT hSp⟩ ⟨1, by rw [hnX]; simp⟩⟩
  rw [hφtop]
  exact Subgroup.map_subtype_le _

end CFSG.Quasithin.RonanE27
