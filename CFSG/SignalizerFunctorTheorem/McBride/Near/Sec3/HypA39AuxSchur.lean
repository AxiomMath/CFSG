module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.External
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxM

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem IsDirectProduct.of_map {G H : Type*} [Group G] [Group H] {f : H →* G}
    (hf : Function.Injective f) {S : Set (Subgroup H)} {K : Subgroup H}
    (h : IsDirectProduct ((Subgroup.map f) '' S) (K.map f)) : IsDirectProduct S K where
  commute J hJ L hL hne x hx y hy := by
    have := h.commute (J.map f) ⟨J, hJ, rfl⟩ (L.map f) ⟨L, hL, rfl⟩
      (fun h' => hne (Subgroup.map_injective hf h')) (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩
    exact hf (by simpa [map_mul] using this.eq)
  indep J hJ := by
    have h0 := h.indep (Set.mem_image_of_mem _ hJ)
    have h1 : (Subgroup.map f) '' S \ {J.map f} = (Subgroup.map f) '' (S \ {J}) := by
      ext L
      constructor
      · rintro ⟨⟨L', hL', rfl⟩, hne⟩
        exact ⟨L', ⟨hL', fun h => hne (h ▸ rfl)⟩, rfl⟩
      · rintro ⟨L', ⟨hL', hne⟩, rfl⟩
        exact ⟨⟨L', hL', rfl⟩, fun h => hne (Subgroup.map_injective hf h)⟩
    have h2 : sSup ((Subgroup.map f) '' (S \ {J})) = (sSup (S \ {J})).map f := by
      rw [sSup_image, (Subgroup.gc_map_comap f).l_sSup]
    rw [h1, h2, disjoint_iff, ← Subgroup.map_inf_eq _ _ f hf] at h0
    rw [disjoint_iff]
    exact (Subgroup.map_eq_bot_iff_of_injective _ hf).mp h0
  sSup_eq := by
    have h0 := h.sSup_eq
    rw [sSup_image, ← (Subgroup.gc_map_comap f).l_sSup] at h0
    exact Subgroup.map_injective hf h0

end CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R K₁ : Subgroup Γ}

namespace Red

theorem schur_model
    [Finite Γ] (c : Red p H A D D₁ D₂ E L R) (d : K1Data H A D₁ E L R K₁)
    (hnc : ∃ x ∈ K₁, ∃ y ∈ K₁, ⁅x, y⁆ ∉ L) {r : ℕ} (hr : r.Prime) (hrL : ∀ x ∈ L, x ^ r = 1) :
    p ≠ 3 ∧ ∃ J ∈ lcal (AChief.qimg L K₁),
      (r = 2 ∧ Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) ∨
      (r = 3 ∧ Nonempty (↥J ≃* PSU3 2 p)) := by
  have hK₁H := c.K₁_le_H d
  have hLK₁ := L_le_K₁ d
  have hK₁n : K₁ ≤ AChief.nrm L := hK₁H.trans (le_sup_left.trans c.hLG)
  have hLK₁N : (L.subgroupOf K₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLK₁]
    intro h k hh hk
    exact c.hLG.conj_mem (Subgroup.mem_sup_left (hK₁H hk)) hh
  have hLc : L.subgroupOf K₁ ≤ Subgroup.center ↥K₁ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (c.K₁_cen d g g.2 x (Subgroup.mem_subgroupOf.mp hx))
  have hLr : IsPGroup r ↥(L.subgroupOf K₁) := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hrL x (Subgroup.mem_subgroupOf.mp x.2)⟩
  have hL1 : L.subgroupOf K₁ ≠ ⊥ := by
    intro h0
    apply c.hL0
    rw [← Subgroup.map_subgroupOf_eq_of_le hLK₁, h0, Subgroup.map_bot]
  have hY : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr (c.commutator_eq d hnc)
  have hY' : signalizerNearPSolvable p ↥K₁ := signalizerNearPSolvable_of_le hK₁H c.h15.a1_near.1
  have hnearW : signalizerNearPSolvable p (↥K₁ ⧸ L.subgroupOf K₁) := by
    obtain ⟨hcop, hmodel⟩ := McBride.signalizerNearPSolvable_iff.mp hY'
    refine McBride.signalizerNearPSolvable_iff.mpr ⟨?_, fun S _ _ hS hnc' => hmodel S
      (hS.trans (IsSectionOf.of_surjective (QuotientGroup.mk' (L.subgroupOf K₁))
        (QuotientGroup.mk'_surjective _))) hnc'⟩
    exact hcop.coprime_dvd_right
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (L.subgroupOf K₁)))
  have hAS := c.qK_isASimple d hnc
  have hss0 : IsSemisimple (AChief.qimg L K₁) := AChief.isDirectProduct_simpleComponents hAS
  let ε : ↥K₁ ⧸ L.subgroupOf K₁ ≃* ↥(AChief.qimg L K₁) :=
    (QuotientGroup.quotientMulEquivOfEq (SolQuot.ker_qres hK₁n).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (SolQuot.qres L K₁ hK₁n)
        (SolQuot.qres_surjective hK₁n))
  let ψ : (↥K₁ ⧸ L.subgroupOf K₁) →* AChief.QG L :=
    (AChief.qimg L K₁).subtype.comp ε.toMonoidHom
  have hψ : Function.Injective ψ := (AChief.qimg L K₁).subtype_injective.comp ε.injective
  have hψtop : (⊤ : Subgroup (↥K₁ ⧸ L.subgroupOf K₁)).map ψ = AChief.qimg L K₁ := by
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ ε.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hss : IsSemisimple (⊤ : Subgroup (↥K₁ ⧸ L.subgroupOf K₁)) := by
    have h1 : IsDirectProduct (Nonsolvable.simpleComponents
        ((⊤ : Subgroup (↥K₁ ⧸ L.subgroupOf K₁)).map ψ))
        ((⊤ : Subgroup (↥K₁ ⧸ L.subgroupOf K₁)).map ψ) := by
      rw [hψtop]
      exact hss0
    rw [simpleComponents_map hψ] at h1
    exact IsDirectProduct.of_map hψ h1
  have := hLK₁N
  obtain ⟨J₀, hJ₀, hcases⟩ := schur_multiplier_input c.h15.prime c.h15.odd hr (L.subgroupOf K₁)
    hLc hLr hL1 hY hss hnearW
  have hp3 : p ≠ 3 := by
    intro hp3
    have hr23 : r = 2 ∨ r = 3 := by
      rcases hcases with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨⟨x, hxL⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp c.hL0
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨k, hk⟩ := c.h5 hp3 x (c.L_le_D₁ hxL)
    have hxk : x ^ (5 ^ k) = 1 := by
      have : x ^ (5 ^ k) ∈ D₂ ⊓ L := Subgroup.mem_inf.mpr ⟨hk, pow_mem hxL _⟩
      rw [c.hD₂L, Subgroup.mem_bot] at this
      exact this
    have hcop : Nat.Coprime r (5 ^ k) := by
      rcases hr23 with rfl | rfl <;> exact Nat.Coprime.pow_right _ (by norm_num)
    have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one (hrL x hxL)) (orderOf_dvd_of_pow_eq_one hxk)
    exact hx1' (orderOf_eq_one_iff.mp h1)
  have hJ₁ : J₀.map ε.toMonoidHom ∈ lcalOf ↥(AChief.qimg L K₁) :=
    (map_mem_lcalOf_iff ε).mpr hJ₀
  have hJ₂ : (J₀.map ε.toMonoidHom).map (AChief.qimg L K₁).subtype ∈ lcal (AChief.qimg L K₁) := by
    rw [lcal_eq_image]
    exact ⟨_, hJ₁, rfl⟩
  refine ⟨hp3, _, hJ₂, ?_⟩
  let e : ↥((J₀.map ε.toMonoidHom).map (AChief.qimg L K₁).subtype) ≃* ↥J₀ :=
    ((Subgroup.equivMapOfInjective J₀ ε.toMonoidHom ε.injective).trans
      (Subgroup.equivMapOfInjective (J₀.map ε.toMonoidHom) (AChief.qimg L K₁).subtype
        (AChief.qimg L K₁).subtype_injective)).symm
  rcases hcases with ⟨hr2, h | ⟨hp3', -⟩⟩ | ⟨hr3, h⟩
  · exact Or.inl ⟨hr2, h.map fun f => e.trans f⟩
  · exact absurd hp3' hp3
  · exact Or.inr ⟨hr3, h.map fun f => e.trans f⟩

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
