module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_transport_fix_ord_quot {Q : Type} [CommGroup Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : Vtil V₀ V hV →* Q} {ρ : ↥(lBar V₀ V hV L) →* MulAut Q}
    (hqs : Function.Surjective q) (hqk : ∀ x : Vtil V₀ V hV, q x = 1 ↔ x ∈ fixV (lBar V₀ V hV L))
    (hρ : Function.Injective ρ)
    (heq : ∀ (l : ↥(lBar V₀ V hV L)) (x : Vtil V₀ V hV),
      q ((l : MulAut (Vtil V₀ V hV)) x) = ρ l (q x))
    (hne : ∃ w : Q, w ≠ 1) (hfix : ∀ w : Q, w ≠ 1 → ∃ g ∈ ρ.range, orderOf g = p ∧ g w = w) :
    ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ y ∈ lBar V₀ V hV L, orderOf y = p ∧ y x = x := by
  intro x _hx1
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  by_cases hxZ : x ∈ fixV (lBar V₀ V hV L)
  · obtain ⟨w, hw⟩ := hne
    obtain ⟨g, hg, hgp, hgw⟩ := hfix w hw
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.1 hg
    refine ⟨(l : MulAut (Vtil V₀ V hV)), l.2, ?_,
      (mem_fixV.1 hxZ) (l : MulAut (Vtil V₀ V hV)) l.2⟩
    exact (orderOf_injective (lBar V₀ V hV L).subtype
        (lBar V₀ V hV L).subtype_injective l).trans
      ((orderOf_injective ρ hρ l).symm.trans hgp)
  · have hw : q x ≠ 1 := fun h => hxZ ((hqk x).1 h)
    obtain ⟨g, hg, hgp, hgw⟩ := hfix (q x) hw
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.1 hg
    refine ⟨(l : MulAut (Vtil V₀ V hV)), l.2, ?_, ?_⟩
    · exact (orderOf_injective (lBar V₀ V hV L).subtype
          (lBar V₀ V hV L).subtype_injective l).trans
        ((orderOf_injective ρ hρ l).symm.trans hgp)
    · have hq1 : q ((l : MulAut (Vtil V₀ V hV)) x * x⁻¹) = 1 := by
        rw [map_mul, map_inv, heq l x, hgw, mul_inv_cancel]
      have hZmem : (l : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈ fixV (lBar V₀ V hV L) :=
        (hqk ((l : MulAut (Vtil V₀ V hV)) x * x⁻¹)).1 hq1
      have hord : orderOf (l : MulAut (Vtil V₀ V hV)) = p :=
        (orderOf_injective (lBar V₀ V hV L).subtype
            (lBar V₀ V hV L).subtype_injective l).trans
          ((orderOf_injective ρ hρ l).symm.trans hgp)
      have hodd : Odd (orderOf (l : MulAut (Vtil V₀ V hV))) := by
        rw [hord]; exact hp.odd_of_ne_two hp2
      exact s16g_apply_eq_of_odd hW hodd (pow_orderOf_eq_one _)
        (fun z hz => (mem_fixV.1 hz) (l : MulAut (Vtil V₀ V hV)) l.2) hZmem

private theorem s16k_nc_lift {Q : Type} [CommGroup Q] {p : ℕ} {ρ : ↥(lBar V₀ V hV L) →* MulAut Q}
    (hρ : Function.Injective ρ) {B₀ : Subgroup (MulAut Q)} (hB₀range : B₀ ≤ ρ.range)
    (hB₀p : IsPGroup p B₀) (hB₀nc : ¬ IsCyclic ↥B₀) :
    ∃ B : Subgroup (MulAut (Vtil V₀ V hV)),
      B ≤ lBar V₀ V hV L ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, ∃ l : ↥(lBar V₀ V hV L), ρ l ∈ B₀ ∧ (l : MulAut (Vtil V₀ V hV)) = b := by
  let B₁ : Subgroup ↥(lBar V₀ V hV L) := B₀.comap ρ
  let B : Subgroup (MulAut (Vtil V₀ V hV)) := B₁.map (lBar V₀ V hV L).subtype
  have hB₁p : IsPGroup p B₁ := hB₀p.comap_of_injective ρ hρ
  have hBmap : B₁.map ρ = B₀ := Subgroup.map_comap_eq_self hB₀range
  have hBsub : B ≤ lBar V₀ V hV L := Subgroup.map_subtype_le B₁
  have hBp : IsPGroup p B := hB₁p.map (lBar V₀ V hV L).subtype
  have hBnc : ¬ IsCyclic ↥B := by
    intro hcyc
    refine hB₀nc ?_
    have e1 : ↥B₁ ≃* ↥B := Subgroup.equivMapOfInjective B₁ (lBar V₀ V hV L).subtype
      (lBar V₀ V hV L).subtype_injective
    have e2 : ↥B₁ ≃* ↥B₀ := (Subgroup.equivMapOfInjective B₁ ρ hρ).trans
      (MulEquiv.subgroupCongr hBmap)
    exact ((e1.symm.trans e2).isCyclic).mp hcyc
  refine ⟨B, hBsub, hBp, hBnc, ?_⟩
  intro b hb
  obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.1 hb
  exact ⟨l, hl, hl_eq⟩

theorem s16k_transport_fix_nc_quot {Q : Type} [CommGroup Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV)
    {q : Vtil V₀ V hV →* Q} {ρ : ↥(lBar V₀ V hV L) →* MulAut Q}
    (hqs : Function.Surjective q) (hqk : ∀ x : Vtil V₀ V hV, q x = 1 ↔ x ∈ fixV (lBar V₀ V hV L))
    (hρ : Function.Injective ρ)
    (heq : ∀ (l : ↥(lBar V₀ V hV L)) (x : Vtil V₀ V hV),
      q ((l : MulAut (Vtil V₀ V hV)) x) = ρ l (q x))
    (hne : ∃ w : Q, w ≠ 1)
    (hfix : ∀ w : Q, w ≠ 1 → ∃ B : Subgroup (MulAut Q), B ≤ ρ.range ∧ IsPGroup p B ∧
      ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b w = w) :
    ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ B : Subgroup (MulAut (Vtil V₀ V hV)),
      B ≤ Mbar D.M V₀ V hV ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x := by
  intro x _hx1
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  by_cases hxZ : x ∈ fixV (lBar V₀ V hV L)
  · obtain ⟨w, hw⟩ := hne
    obtain ⟨B₀, hB₀range, hB₀p, hB₀nc, _hB₀fix⟩ := hfix w hw
    obtain ⟨B, hBsub, hBp, hBnc, hBrep⟩ := s16k_nc_lift (V₀ := V₀) (V := V) (L := L) (hV := hV)
      (p := p) hρ hB₀range hB₀p hB₀nc
    refine ⟨B, hBsub.trans hLM, hBp, hBnc, fun b hb => ?_⟩
    obtain ⟨l, _hlB₀, hl_eq⟩ := hBrep b hb
    rw [← hl_eq]
    exact (mem_fixV.1 hxZ) (l : MulAut (Vtil V₀ V hV)) l.2
  · have hw : q x ≠ 1 := fun h => hxZ ((hqk x).1 h)
    obtain ⟨B₀, hB₀range, hB₀p, hB₀nc, hB₀fix⟩ := hfix (q x) hw
    obtain ⟨B, hBsub, hBp, hBnc, hBrep⟩ := s16k_nc_lift (V₀ := V₀) (V := V) (L := L) (hV := hV)
      (p := p) hρ hB₀range hB₀p hB₀nc
    refine ⟨B, hBsub.trans hLM, hBp, hBnc, fun b hb => ?_⟩
    obtain ⟨l, hlB₀, hl_eq⟩ := hBrep b hb
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hBp.exists_orderOf_eq_pow (⟨b, hb⟩ : ↥B)
    have hborder : Odd (orderOf b) := by
      have h1 : orderOf b = p ^ k := by rw [← Subgroup.orderOf_mk b hb, hk]
      rw [h1]; exact (hp.odd_of_ne_two hp2).pow
    have hodd : Odd (orderOf (l : MulAut (Vtil V₀ V hV))) := by rw [hl_eq]; exact hborder
    rw [← hl_eq]
    have hq1 : q ((l : MulAut (Vtil V₀ V hV)) x * x⁻¹) = 1 := by
      rw [map_mul, map_inv, heq l x, hB₀fix (ρ l) hlB₀, mul_inv_cancel]
    have hZmem : (l : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈ fixV (lBar V₀ V hV L) :=
      (hqk ((l : MulAut (Vtil V₀ V hV)) x * x⁻¹)).1 hq1
    exact s16g_apply_eq_of_odd hW hodd (pow_orderOf_eq_one _)
      (fun z hz => (mem_fixV.1 hz) (l : MulAut (Vtil V₀ V hV)) l.2) hZmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
