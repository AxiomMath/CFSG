module

public import CFSG.Quasithin.Recognition.F112Crit.BenderLocalOf
public import CFSG.Quasithin.Recognition.F112Crit.L2Sixteen
public import CFSG.Quasithin.Recognition.F112Crit.TorusQuot
public import CFSG.Holt.Centralizer
public import CFSG.Holt.Witt

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)
open scoped Pointwise

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

namespace TorusLocalOf

open BenderLocalOf

section Lift

variable [Finite G] {X T : Subgroup G}
variable (hK : IsTorusQuot (oTwoQuot ↥X)) (hT : IsSylowTwoOf T X)
include hK hT

theorem lift_trans {x y y' : G} (hx : x ∈ X) (hy : y ∈ X) (hy' : y' ∈ X)
    (hxN : x ∉ Subgroup.normalizer (T : Set G)) (hyN : y ∉ Subgroup.normalizer (T : Set G))
    (hy'N : y' ∉ Subgroup.normalizer (T : Set G))
    (hxy : x⁻¹ * y ∉ Subgroup.normalizer (T : Set G))
    (hxy' : x⁻¹ * y' ∉ Subgroup.normalizer (T : Set G)) :
    ∃ t ∈ X, t ∈ Subgroup.normalizer (T : Set G) ∧
      x⁻¹ * t * x ∈ Subgroup.normalizer (T : Set G) ∧
      y'⁻¹ * t * y ∈ Subgroup.normalizer (T : Set G) := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, QuotientGroup.mk' (pCore 2 ↥X) z ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) ↔
        (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  obtain ⟨tq, htq, h1, h2⟩ := hK.trans P (QuotientGroup.mk' _ ⟨x, hx⟩)
    (QuotientGroup.mk' _ ⟨y, hy⟩) (QuotientGroup.mk' _ ⟨y', hy'⟩)
    (fun h => hxN ((hmem _).mp h)) (fun h => hyN ((hmem _).mp h))
    (fun h => hy'N ((hmem _).mp h))
    (fun h => hxy (by
      simpa using (hmem (⟨x, hx⟩⁻¹ * ⟨y, hy⟩)).mp (by simpa [map_mul, map_inv] using h)))
    (fun h => hxy' (by
      simpa using (hmem (⟨x, hx⟩⁻¹ * ⟨y', hy'⟩)).mp (by simpa [map_mul, map_inv] using h)))
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥X) tq
  refine ⟨t, t.2, (hmem t).mp htq, ?_, ?_⟩
  · simpa using (hmem (⟨x, hx⟩⁻¹ * t * ⟨x, hx⟩)).mp (by simpa [map_mul, map_inv] using h1)
  · simpa using (hmem (⟨y', hy'⟩⁻¹ * t * ⟨y, hy⟩)).mp (by simpa [map_mul, map_inv] using h2)

theorem lift_reg {t x y : G} (ht : t ∈ X) (hx : x ∈ X) (hy : y ∈ X)
    (htN : t ∈ Subgroup.normalizer (T : Set G))
    (hxN : x ∉ Subgroup.normalizer (T : Set G)) (hyN : y ∉ Subgroup.normalizer (T : Set G))
    (hxy : x⁻¹ * y ∉ Subgroup.normalizer (T : Set G))
    (hxt : x⁻¹ * t * x ∈ Subgroup.normalizer (T : Set G))
    (hyt : y⁻¹ * t * y ∈ Subgroup.normalizer (T : Set G)) : t ∈ pCoreOf 2 X := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, QuotientGroup.mk' (pCore 2 ↥X) z ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) ↔
        (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  have h1 := hK.reg P (QuotientGroup.mk' _ ⟨t, ht⟩) ((hmem _).mpr htN)
    (QuotientGroup.mk' _ ⟨x, hx⟩) (QuotientGroup.mk' _ ⟨y, hy⟩)
    (fun h => hxN ((hmem _).mp h)) (fun h => hyN ((hmem _).mp h))
    (fun h => hxy (by
      simpa using (hmem (⟨x, hx⟩⁻¹ * ⟨y, hy⟩)).mp (by simpa [map_mul, map_inv] using h)))
    (by simpa [map_mul, map_inv] using
      (hmem (⟨x, hx⟩⁻¹ * ⟨t, ht⟩ * ⟨x, hx⟩)).mpr (by simpa using hxt))
    (by simpa [map_mul, map_inv] using
      (hmem (⟨y, hy⟩⁻¹ * ⟨t, ht⟩ * ⟨y, hy⟩)).mpr (by simpa using hyt))
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (F1.mem_pCore_iff_coe _).mp h1

end Lift

section Base

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

theorem smul_γ₁_eq_smul_iff (hs : Setting L₁ L₂ S Z) {g h : ↥(L₁ ⊔ L₂ ⊔ S)}
    (hg : (g : G) ∈ L₂) (hh : (h : G) ∈ L₂) :
    g • γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) = h • γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) ↔
      (g : G)⁻¹ * h ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
  rw [smul_eq_smul_iff_mem_stab, stab_γ₁_eq hs]
  exact mem_P₁_iff hs (L₂.mul_mem (L₂.inv_mem hg) hh)

end Base

end TorusLocalOf

namespace Setting

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

open TorusLocalOf BenderLocalOf in
theorem torusLocal (hs : Setting L₁ L₂ S Z) {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    (hT : IsTorusQuot (oTwoQuot ↥L₂)) :
    TorusLocal (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) L₂ := by
  have hS₂ := isSylowTwoOf_inf hs
  have key : ∀ {g h : ↥(L₁ ⊔ L₂ ⊔ S)}, (g : G) ∈ L₂ → (h : G) ∈ L₂ →
      (g • γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) =
        h • γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) ↔
      (g : G)⁻¹ * h ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G)) :=
    fun hg hh => smul_γ₁_eq_smul_iff hs hg hh
  refine { le_stab := ?_, normal := ?_, trans := ?_, reg := ?_ }
  · rw [stab_γ₀_eq hs]
    exact le_sup_left
  · rw [stab_γ₀_eq hs]
    exact P₂_le_normalizer hs
  · intro δ hδ δ' hδ' hne ε hε ε' hε' h1 h2 h3 h4
    obtain ⟨a, ha, rfl⟩ := exists_smul_γ₁_eq hK hs hδ
    obtain ⟨b, hb, rfl⟩ := exists_smul_γ₁_eq hK hs hδ'
    obtain ⟨c, hc, rfl⟩ := exists_smul_γ₁_eq hK hs hε
    obtain ⟨c', hc', rfl⟩ := exists_smul_γ₁_eq hK hs hε'
    have ha₂ : (a : G) ∈ L₂ := MS93.oddGen_le L₂ ha
    have hb₂ : (b : G) ∈ L₂ := MS93.oddGen_le L₂ hb
    have hc₂ : (c : G) ∈ L₂ := MS93.oddGen_le L₂ hc
    have hc'₂ : (c' : G) ∈ L₂ := MS93.oddGen_le L₂ hc'
    have e1 : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * c) = (b : G)⁻¹ * c := by group
    have e2 : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * c') = (b : G)⁻¹ * c' := by group
    obtain ⟨t, ht₂, htN, htx, hty⟩ := TorusLocalOf.lift_trans hT hS₂
      (x := (a : G)⁻¹ * b) (y := (a : G)⁻¹ * c) (y' := (a : G)⁻¹ * c')
      (L₂.mul_mem (L₂.inv_mem ha₂) hb₂) (L₂.mul_mem (L₂.inv_mem ha₂) hc₂)
      (L₂.mul_mem (L₂.inv_mem ha₂) hc'₂)
      (fun h => hne ((key ha₂ hb₂).mpr h))
      (fun h => h1 ((key ha₂ hc₂).mpr h).symm)
      (fun h => h3 ((key ha₂ hc'₂).mpr h).symm)
      (fun h => h2 ((key hb₂ hc₂).mpr (e1 ▸ h)).symm)
      (fun h => h4 ((key hb₂ hc'₂).mpr (e2 ▸ h)).symm)
    have htΛ : t ∈ L₁ ⊔ L₂ ⊔ S := Subgroup.mem_sup_left (Subgroup.mem_sup_right ht₂)
    have hg₂ : (a : G) * t * (a : G)⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem ha₂ ht₂) (L₂.inv_mem ha₂)
    refine ⟨a * ⟨t, htΛ⟩ * a⁻¹, hg₂, ?_, ?_, ?_⟩
    · rw [← mul_smul]
      refine (key (L₂.mul_mem hg₂ ha₂) ha₂).mpr ?_
      have e : ((a : G) * t * (a : G)⁻¹ * a)⁻¹ * a = t⁻¹ := by group
      show ((a : G) * t * (a : G)⁻¹ * a)⁻¹ * a ∈ _
      rw [e]
      exact Subgroup.inv_mem _ htN
    · rw [← mul_smul]
      refine (key (L₂.mul_mem hg₂ hb₂) hb₂).mpr ?_
      have e : ((a : G) * t * (a : G)⁻¹ * b)⁻¹ * b =
          (((a : G)⁻¹ * b)⁻¹ * t * ((a : G)⁻¹ * b))⁻¹ := by group
      show ((a : G) * t * (a : G)⁻¹ * b)⁻¹ * b ∈ _
      rw [e]
      exact Subgroup.inv_mem _ htx
    · rw [← mul_smul]
      refine (key (L₂.mul_mem hg₂ hc₂) hc'₂).mpr ?_
      have e : ((a : G) * t * (a : G)⁻¹ * c)⁻¹ * c' =
          (((a : G)⁻¹ * c')⁻¹ * t * ((a : G)⁻¹ * c))⁻¹ := by group
      show ((a : G) * t * (a : G)⁻¹ * c)⁻¹ * c' ∈ _
      rw [e]
      exact Subgroup.inv_mem _ hty
  · intro g hg δ hδ δ' hδ' ε hε hne h1 h2 hgδ hgδ' hgε
    obtain ⟨a, ha, rfl⟩ := exists_smul_γ₁_eq hK hs hδ
    obtain ⟨b, hb, rfl⟩ := exists_smul_γ₁_eq hK hs hδ'
    obtain ⟨c, hc, rfl⟩ := exists_smul_γ₁_eq hK hs hε
    have ha₂ : (a : G) ∈ L₂ := MS93.oddGen_le L₂ ha
    have hb₂ : (b : G) ∈ L₂ := MS93.oddGen_le L₂ hb
    have hc₂ : (c : G) ∈ L₂ := MS93.oddGen_le L₂ hc
    have hfix : ∀ {d : ↥(L₁ ⊔ L₂ ⊔ S)}, (d : G) ∈ L₂ →
        g • d • γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) =
          d • γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) →
        (d : G)⁻¹ * g * d ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
      intro d hd h
      rw [← mul_smul] at h
      have h' : ((g : G) * d)⁻¹ * d ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) :=
        (key (L₂.mul_mem hg hd) hd).mp h
      have e : (d : G)⁻¹ * g * d = (((g : G) * d)⁻¹ * d)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ h'
    have e1 : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * c) = (b : G)⁻¹ * c := by group
    have e3 : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * g * a) * ((a : G)⁻¹ * b) = (b : G)⁻¹ * g * b := by
      group
    have e4 : ((a : G)⁻¹ * c)⁻¹ * ((a : G)⁻¹ * g * a) * ((a : G)⁻¹ * c) = (c : G)⁻¹ * g * c := by
      group
    have hO := TorusLocalOf.lift_reg hT hS₂ (t := (a : G)⁻¹ * g * a) (x := (a : G)⁻¹ * b)
      (y := (a : G)⁻¹ * c) (L₂.mul_mem (L₂.mul_mem (L₂.inv_mem ha₂) hg) ha₂)
      (L₂.mul_mem (L₂.inv_mem ha₂) hb₂) (L₂.mul_mem (L₂.inv_mem ha₂) hc₂) (hfix ha₂ hgδ)
      (fun h => hne ((key ha₂ hb₂).mpr h))
      (fun h => h1 ((key ha₂ hc₂).mpr h).symm)
      (fun h => h2 ((key hb₂ hc₂).mpr (e1 ▸ h)).symm)
      (by rw [e3]; exact hfix hb₂ hgδ') (by rw [e4]; exact hfix hc₂ hgε)
    have hgO : (g : G) ∈ pCoreOf 2 L₂ := by
      have e5 : (g : G) = a * ((a : G)⁻¹ * g * a) * (a : G)⁻¹ := by group
      rw [e5]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L₂ ha₂) _).mp hO
    exact pCoreOf_le_ballStab hs hgO

end Setting

end CFSG.Quasithin.F112Crit

end
