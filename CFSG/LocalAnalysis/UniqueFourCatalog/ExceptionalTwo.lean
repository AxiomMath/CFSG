module

public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcBasic
public import CFSG.LocalAnalysis.UniqueFourCatalog.Glue

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open CFSG.LocalAnalysis.RankThreeUC (twoLocalClosure twoLocalClosure_eq_top_of_invariant_two_subgroups)

theorem twoLocalClosure_eq_top_of_map_eq_top {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (E : Subgroup G) (h : twoLocalClosure (E.map e.toMonoidHom) = ⊤) :
    twoLocalClosure E = ⊤ := by
  have hle := CFSG.LocalAnalysis.RankThreeUC.map_twoLocalClosure_le e.symm (E.map e.toMonoidHom)
  have hEE : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    ext x
    simp
  rw [hEE, h] at hle
  rw [eq_top_iff]
  intro x _
  exact hle (Subgroup.mem_map.mpr ⟨e x, Subgroup.mem_top _, by simp⟩)

theorem mem_normalizer_map_subtype {G : Type} [Group G] {C : Subgroup G} {S : Subgroup C}
    {x : C} (hx : x ∈ Subgroup.normalizer (S : Set C)) :
    (x : G) ∈ Subgroup.normalizer ((S.map C.subtype : Subgroup G) : Set G) := by
  have fwd : ∀ y : C, y ∈ Subgroup.normalizer (S : Set C) → ∀ z : G,
      z ∈ S.map C.subtype → (y : G) * z * (y : G)⁻¹ ∈ S.map C.subtype := by
    intro y hy z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hz
    have hs' : y * s * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hy s).1 hs
    exact Subgroup.mem_map.2 ⟨y * s * y⁻¹, hs', by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact fwd x hx z
  · intro hz
    have h := fwd x⁻¹ (inv_mem hx) _ hz
    rw [Subgroup.coe_inv, inv_inv] at h
    have e : (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * (x : G) = z := by group
    rwa [e] at h

section Certified

theorem twoLocalClosure_adjoint_eq_top_of_normalizes
    {τ : Tag} {k : Type} [Field k] [Finite k] [CharP k 2] [IsSimpleGroup (adjointGroup τ k)]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E S₀ : Subgroup (adjointGroup τ k)} (hE : IsElemAbelian p E) (hS₀ : S₀ ≠ ⊥)
    (hS₀2 : IsPGroup 2 S₀) (hEN : E ≤ Subgroup.normalizer (S₀ : Set (adjointGroup τ k))) :
    twoLocalClosure E = ⊤ := by
  have := finite_modGL (τ := τ) (K := k)
  haveI : Fact p.Prime := ⟨hp⟩
  have hrp : (2 : ℕ) ≠ p := fun h => hp2 h.symm
  have hEp : IsPGroup p E := by
    intro x
    refine ⟨1, ?_⟩
    have := hE.2 (x : adjointGroup τ k) x.2
    apply Subtype.ext
    simpa using this
  set A : Subgroup (ModGL τ k) := E.map (adjointGroup τ k).subtype with hAdef
  set Q₀ : Subgroup (ModGL τ k) := S₀.map (adjointGroup τ k).subtype with hQ₀def
  have hAp : IsPGroup p A := hEp.map _
  have hAC : A ≤ adjointGroup τ k := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQ₀p : IsPGroup 2 Q₀ := hS₀2.map _
  have hQ₀C : Q₀ ≤ adjointGroup τ k := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQ₀ne : Q₀ ≠ ⊥ := by
    intro h
    exact hS₀ ((Subgroup.map_eq_bot_iff_of_injective S₀
      (adjointGroup τ k).subtype_injective).1 h)
  have hAR : A ≤ Subgroup.normalizer (Q₀ : Set (ModGL τ k)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_normalizer_map_subtype (hEN hx)
  obtain ⟨M, -, -, -, F, -, -, ⟨g₀, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    (RootWeightDatum.ordinary τ : RootWeightDatum k).root_p_subgroup_optimal_parabolic_containment
      2 Q₀ hQ₀C hQ₀p hQ₀ne
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g₀ hg l hl hl1 hgl
  obtain ⟨g, rfl⟩ : ∃ g : ModGL τ k, g = g₀ := ⟨g₀, rfl⟩
  have hgC : g ∈ adjointGroup τ k := hg
  have hJ' : ((RootWeightDatum.ordinary τ : RootWeightDatum k).face l : Set (Fin τ.rank)) ≠
      Set.univ := hJ
  set J : Set (Fin τ.rank) := (RootWeightDatum.ordinary τ : RootWeightDatum k).face l
  change {x : ModGL τ k | x ∈ adjointGroup τ k ∧
      ∀ c : ℝ, (F c).map (x : Module.End k (RootModule τ k)) = F c} =
    ((parabolicSubgroup τ k J).map (MulAut.conj g).toMonoidHom : Set (ModGL τ k)) at hset
  have hA1' : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ parabolicSubgroup τ k J := by
    rintro _ ⟨a, ha, rfl⟩
    have hmem := (Set.ext_iff.1 hset a).1
      (And.intro (hAC ha) (hN a (Subgroup.mem_inf.2 ⟨hAC ha, hAR ha⟩)))
    rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hmem
  have hindex : ¬ p ∣ ((parabolicLevi τ k J).subgroupOf (parabolicSubgroup τ k J)).index := by
    rw [parabolicLevi_index_eq]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ k J
    exact not_dvd_card_of_isPGroup hrp (hfin 2).2.1
  have hA1p : IsPGroup p (A.map (MulAut.conj g⁻¹).toMonoidHom) := hAp.map _
  obtain ⟨y, hy, hyA⟩ := exists_conj_le_of_not_dvd_index hA1' hA1p hindex
  have hyC : y ∈ adjointGroup τ k := parabolicSubgroup_le_adjointGroup τ k J hy
  have hxC : y * g⁻¹ ∈ adjointGroup τ k := mul_mem hyC (inv_mem hgC)
  obtain ⟨w, hw⟩ : ∃ w : adjointGroup τ k, (w : ModGL τ k) = y * g⁻¹ := ⟨⟨y * g⁻¹, hxC⟩, rfl⟩
  have hE' : ∀ x ∈ E.map (MulAut.conj w).toMonoidHom,
      (x : ModGL τ k) ∈ parabolicLevi τ k J := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : ((e : adjointGroup τ k) : ModGL τ k) ∈ A :=
      Subgroup.mem_map_of_mem (adjointGroup τ k).subtype he
    have h3 := hyA (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom h1))
    have h7 : ∀ a : ModGL τ k, (MulAut.conj y).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom a) =
        y * g⁻¹ * a * (y * g⁻¹)⁻¹ := by
      intro a
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h6 : (((MulAut.conj w).toMonoidHom e : adjointGroup τ k) : ModGL τ k) =
        (MulAut.conj y).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom
          ((e : adjointGroup τ k) : ModGL τ k)) := by
      rw [h7]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, hw]
    rw [h6]
    exact h3
  obtain ⟨Q, Q', hQp, hQ'p, hQC, hQ'C, hMQ, hMQ', hCX⟩ :=
    exists_radicals_of_parabolicLevi (k := k) (r := 2) hJ'
  have hcl : ∀ X : Subgroup (ModGL τ k), IsPGroup 2 X →
      parabolicLevi τ k J ≤ Subgroup.normalizer (X : Set (ModGL τ k)) →
      X.subgroupOf (adjointGroup τ k) ≤
        twoLocalClosure (E.map (MulAut.conj w).toMonoidHom) := by
    intro X hXp hXN
    by_cases hX : X.subgroupOf (adjointGroup τ k) = ⊥
    · rw [hX]
      exact bot_le
    · have hloc : IsTwoLocal (Subgroup.normalizer
          ((X.subgroupOf (adjointGroup τ k) : Subgroup (adjointGroup τ k)) :
            Set (adjointGroup τ k))) :=
        ⟨X.subgroupOf (adjointGroup τ k), hX, hXp.comap_subtype, rfl⟩
      have hEN' : E.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer
          ((X.subgroupOf (adjointGroup τ k) : Subgroup (adjointGroup τ k)) :
            Set (adjointGroup τ k)) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro z
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.1 (hXN (hE' x hx)) z
      have hle : Subgroup.normalizer
          ((X.subgroupOf (adjointGroup τ k) : Subgroup (adjointGroup τ k)) :
            Set (adjointGroup τ k)) ≤
          twoLocalClosure (E.map (MulAut.conj w).toMonoidHom) :=
        le_iSup₂_of_le _ ⟨hloc, hEN'⟩ le_rfl
      exact le_trans Subgroup.le_normalizer hle
  have hQ := hcl Q hQp hMQ
  have hQ' := hcl Q' hQ'p hMQ'
  have htop : twoLocalClosure (E.map (MulAut.conj w).toMonoidHom) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxs : x ∈ Q.subgroupOf (adjointGroup τ k) ⊔ Q'.subgroupOf (adjointGroup τ k) := by
      rw [← Subgroup.subgroupOf_sup hQC hQ'C]
      exact hCX x.2
    exact (sup_le hQ hQ') hxs
  exact twoLocalClosure_eq_top_of_map_eq_top (MulAut.conj w) E htop

end Certified

theorem not_uniqueFour_of_untwistedChevalleyModel_two
    {G : Type} [Group G] [Finite G] (τ : Tag) {f : ℕ} (hS : Standing4 G)
    (h : UntwistedChevalleyModel G τ (2 ^ f)) : ¬ uniqueFourUnique G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.RankThreeUC.charP_two_of_card hK
  have := finite_modGL (τ := τ) (K := K)
  let e2 : AdjointQuotient τ K ≃* adjointGroup τ K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  have hsimp : IsSimpleGroup (adjointGroup τ K) :=
    (MulEquiv.isSimpleGroup_congr (e.trans e2)).mp hS.simple
  haveI := hsimp
  have hcl : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ E S₀ : Subgroup (adjointGroup τ K),
      IsElemAbelian p E → S₀ ≠ ⊥ → IsPGroup 2 S₀ →
        E ≤ Subgroup.normalizer (S₀ : Set (adjointGroup τ K)) → twoLocalClosure E = ⊤ :=
    fun p hp hp2 E S₀ hE hS₀ hS₀2 hEN =>
      twoLocalClosure_adjoint_eq_top_of_normalizes (τ := τ) (k := K) hp hp2 hE hS₀ hS₀2 hEN
  exact not_uniqueFour_of_closure hS (closure_hyp_of_mulEquiv (e.trans e2) hcl)

set_option linter.unusedSectionVars false

end CFSG.LocalAnalysis.UniqueFourCatalog
