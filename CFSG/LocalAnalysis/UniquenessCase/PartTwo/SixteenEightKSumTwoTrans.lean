module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_mk_eq_mk_of_mul_inv_mem {D : FFModel} {m : ↥D.sec} {a : D.Amb}
    (ha : a ∈ D.sec) (h : a * (m : D.Amb)⁻¹ ∈ D.ker) :
    QuotientGroup.mk (s := D.ker.subgroupOf D.sec) (⟨a, ha⟩ : ↥D.sec) =
      QuotientGroup.mk (s := D.ker.subgroupOf D.sec) m := by
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, div_eq_mul_inv]
  exact h

theorem s16k_sum_two_transport_of_le {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hbar : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV) {D₁ D₂ : FFModel}
    {I₁ I₂ : Subgroup (Vtil V₀ V hV)} {π₁ : D₁.Gam →* ↥(lBar V₀ V hV L)}
    {π₂ : D₂.Gam →* ↥(lBar V₀ V hV L)}
    (hZ₁ : fixV (lBar V₀ V hV L) ≤ I₁) (hZ₂ : fixV (lBar V₀ V hV L) ≤ I₂)
    (hsup : fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) = ⊤)
    (h₁ : D₁.RealizesVia (lBar V₀ V hV L) I₁ (fixV (lBar V₀ V hV L)) π₁)
    (h₂ : D₂.RealizesVia (lBar V₀ V hV L) I₂ (fixV (lBar V₀ V hV L)) π₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hne : ∃ m : ↥D₁.sec, (m : D₁.Amb) ∉ D₁.ker)
    (hfix : ∀ (m₁ : ↥D₁.sec) (m₂ : ↥D₂.sec),
      ((m₁ : D₁.Amb) ∉ D₁.ker ∨ (m₂ : D₂.Amb) ∉ D₂.ker) →
      ∃ B : Subgroup ↥(lBar V₀ V hV L), IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B,
        (∃ γ : D₁.Gam, π₁ γ = b ∧ D₁.act γ (m₁ : D₁.Amb) * (m₁ : D₁.Amb)⁻¹ ∈ D₁.ker) ∧
        (∃ γ : D₂.Gam, π₂ γ = b ∧ D₂.act γ (m₂ : D₂.Amb) * (m₂ : D₂.Amb)⁻¹ ∈ D₂.ker)) :
    ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ B : Subgroup (MulAut (Vtil V₀ V hV)),
      B ≤ Mbar D.M V₀ V hV ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x := by
  intro x hx1
  obtain ⟨-, -, -, hHU₁, -, hsec₁, -, β₁, -, hβ₁k, hβ₁e⟩ := h₁
  obtain ⟨-, -, -, hHU₂, -, hsec₂, -, β₂, -, hβ₂k, hβ₂e⟩ := h₂
  have hxmem : x ∈ fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) := by
    rw [hsup]; exact Subgroup.mem_top x
  obtain ⟨z, w, hzw⟩ := (Subgroup.mem_sup').1 hxmem
  obtain ⟨u₁, u₂, hu₁₂⟩ := (Subgroup.mem_sup').1 w.2
  have hxeq : x = (z : Vtil V₀ V hV) * ((u₁ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)) := by
    rw [← hzw, ← hu₁₂]
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (β₁ u₁)
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (β₂ u₂)
  have hm₁eq : β₁ u₁ = QuotientGroup.mk m₁ := hm₁.symm
  have hm₂eq : β₂ u₂ = QuotientGroup.mk m₂ := hm₂.symm
  have build : ∀ (B₀ : Subgroup ↥(lBar V₀ V hV L)), IsPGroup p B₀ → ¬ IsCyclic ↥B₀ →
      (∀ b ∈ B₀, ((b : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x = x) →
      ∃ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≤ Mbar D.M V₀ V hV ∧ IsPGroup p B ∧
        ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x := by
    intro B₀ hBp hBc hfixB
    refine ⟨B₀.map (lBar V₀ V hV L).subtype, ?_, hBp.map (lBar V₀ V hV L).subtype, ?_, ?_⟩
    · intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      exact hbar b₀.2
    · intro hcyc
      haveI : IsCyclic ↥(B₀.map (lBar V₀ V hV L).subtype) := hcyc
      exact hBc (isCyclic_of_injective
        (Subgroup.equivMapOfInjective B₀ (lBar V₀ V hV L).subtype
          (lBar V₀ V hV L).subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective B₀ (lBar V₀ V hV L).subtype
          (lBar V₀ V hV L).subtype_injective).injective)
    · intro b hb
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      exact hfixB b₀ hb₀
  by_cases hA : (m₁ : D₁.Amb) ∈ D₁.ker ∧ (m₂ : D₂.Amb) ∈ D₂.ker
  · obtain ⟨m, hmker⟩ := hne
    obtain ⟨B₀, hB₀p, hB₀c, -⟩ := hfix m 1 (Or.inl hmker)
    have hm₁k : QuotientGroup.mk m₁ = 1 :=
      (QuotientGroup.eq_one_iff (N := D₁.ker.subgroupOf D₁.sec) m₁).mpr
        (Subgroup.mem_subgroupOf.mpr hA.1)
    have hm₂k : QuotientGroup.mk m₂ = 1 :=
      (QuotientGroup.eq_one_iff (N := D₂.ker.subgroupOf D₂.sec) m₂).mpr
        (Subgroup.mem_subgroupOf.mpr hA.2)
    have hu₁Z : (u₁ : Vtil V₀ V hV) ∈ fixV (lBar V₀ V hV L) :=
      (hβ₁k u₁).mp (hm₁eq.trans hm₁k)
    have hu₂Z : (u₂ : Vtil V₀ V hV) ∈ fixV (lBar V₀ V hV L) :=
      (hβ₂k u₂).mp (hm₂eq.trans hm₂k)
    have hxZ : x ∈ fixV (lBar V₀ V hV L) := by
      rw [hxeq]
      exact mul_mem z.2 (mul_mem hu₁Z hu₂Z)
    exact build B₀ hB₀p hB₀c
      (fun b _ => (mem_fixV.1 hxZ) (b : MulAut (Vtil V₀ V hV)) b.2)
  · have hcond : (m₁ : D₁.Amb) ∉ D₁.ker ∨ (m₂ : D₂.Amb) ∉ D₂.ker := not_and_or.mp hA
    obtain ⟨B₀, hB₀p, hB₀c, hB₀fix⟩ := hfix m₁ m₂ hcond
    refine build B₀ hB₀p hB₀c (fun b hb => ?_)
    obtain ⟨⟨γ₁, hγ₁π, hγ₁ker⟩, ⟨γ₂, hγ₂π, hγ₂ker⟩⟩ := hB₀fix b hb
    have hγ₁val : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) =
        (b : MulAut (Vtil V₀ V hV)) := Subtype.ext_iff.mp hγ₁π
    have hγ₂val : ((π₂ γ₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) =
        (b : MulAut (Vtil V₀ V hV)) := Subtype.ext_iff.mp hγ₂π
    have hZu₁ : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
          (u₁ : Vtil V₀ V hV) * (u₁ : Vtil V₀ V hV)⁻¹ ∈ fixV (lBar V₀ V hV L) := by
      have hu₁'' : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
          (u₁ : Vtil V₀ V hV) ∈ I₁ := hHU₁ (π₁ γ₁) (u₁ : Vtil V₀ V hV) u₁.2
      have hm₁' : D₁.act γ₁ (m₁ : D₁.Amb) ∈ D₁.sec := hsec₁ γ₁ (m₁ : D₁.Amb) m₁.2
      have heq₁ := hβ₁e γ₁ u₁ m₁ hu₁'' hm₁' hm₁eq
      have hmk₁ : QuotientGroup.mk (⟨D₁.act γ₁ (m₁ : D₁.Amb), hm₁'⟩ : ↥D₁.sec) =
          QuotientGroup.mk m₁ := s16k_mk_eq_mk_of_mul_inv_mem hm₁' hγ₁ker
      have heq₁' : β₁ ⟨((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
            (u₁ : Vtil V₀ V hV), hu₁''⟩ = β₁ u₁ := (heq₁.trans hmk₁).trans hm₁eq.symm
      have h1 : β₁ (⟨((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
            (u₁ : Vtil V₀ V hV), hu₁''⟩ * u₁⁻¹) = 1 := by
        rw [map_mul, map_inv, heq₁', mul_inv_cancel]
      simpa using (hβ₁k _).mp h1
    have hZu₂ : ((π₂ γ₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
          (u₂ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)⁻¹ ∈ fixV (lBar V₀ V hV L) := by
      have hu₂'' : ((π₂ γ₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
          (u₂ : Vtil V₀ V hV) ∈ I₂ := hHU₂ (π₂ γ₂) (u₂ : Vtil V₀ V hV) u₂.2
      have hm₂' : D₂.act γ₂ (m₂ : D₂.Amb) ∈ D₂.sec := hsec₂ γ₂ (m₂ : D₂.Amb) m₂.2
      have heq₂ := hβ₂e γ₂ u₂ m₂ hu₂'' hm₂' hm₂eq
      have hmk₂ : QuotientGroup.mk (⟨D₂.act γ₂ (m₂ : D₂.Amb), hm₂'⟩ : ↥D₂.sec) =
          QuotientGroup.mk m₂ := s16k_mk_eq_mk_of_mul_inv_mem hm₂' hγ₂ker
      have heq₂' : β₂ ⟨((π₂ γ₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
            (u₂ : Vtil V₀ V hV), hu₂''⟩ = β₂ u₂ := (heq₂.trans hmk₂).trans hm₂eq.symm
      have h2 : β₂ (⟨((π₂ γ₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
            (u₂ : Vtil V₀ V hV), hu₂''⟩ * u₂⁻¹) = 1 := by
        rw [map_mul, map_inv, heq₂', mul_inv_cancel]
      simpa using (hβ₂k _).mp h2
    have hZu₂' : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
          (u₂ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)⁻¹ ∈ fixV (lBar V₀ V hV L) := by
      rw [hγ₁val, ← hγ₂val]
      exact hZu₂
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hB₀p.exists_orderOf_eq_pow (⟨b, hb⟩ : ↥B₀)
    have hbord : orderOf b = p ^ k := by rw [← Subgroup.orderOf_mk b hb, hk]
    have hzord : orderOf (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))) = p ^ k := by
      rw [hγ₁val]
      exact (orderOf_injective (lBar V₀ V hV L).subtype
        (lBar V₀ V hV L).subtype_injective b).trans hbord
    have hodd : Odd (orderOf (((π₁ γ₁ : ↥(lBar V₀ V hV L)) :
        MulAut (Vtil V₀ V hV)))) := by
      rw [hzord]; exact (hp.odd_of_ne_two hp2).pow
    have hpow : (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))) ^
        orderOf (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))) = 1 :=
      pow_orderOf_eq_one _
    have hZfix : ∀ w ∈ fixV (lBar V₀ V hV L),
        ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) w = w :=
      fun w hw => (mem_fixV.1 hw) (π₁ γ₁) (π₁ γ₁).2
    have hmain : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈
        fixV (lBar V₀ V hV L) := by
      have hsplit : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x * x⁻¹ =
          (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
              (u₁ : Vtil V₀ V hV) * (u₁ : Vtil V₀ V hV)⁻¹) *
            (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
              (u₂ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)⁻¹) := by
        rw [hxeq, map_mul, map_mul, hZfix (z : Vtil V₀ V hV) z.2, mul_inv_rev, mul_inv_rev]
        rw [show
          ((z : Vtil V₀ V hV) * (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
                (u₁ : Vtil V₀ V hV) * ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
                (u₂ : Vtil V₀ V hV))) *
              (((u₂ : Vtil V₀ V hV)⁻¹ * (u₁ : Vtil V₀ V hV)⁻¹) * (z : Vtil V₀ V hV)⁻¹)
            = ((((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
                  (u₁ : Vtil V₀ V hV) * (u₁ : Vtil V₀ V hV)⁻¹) *
                (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
                  (u₂ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)⁻¹)) *
              ((z : Vtil V₀ V hV) * (z : Vtil V₀ V hV)⁻¹) by ac_rfl]
        rw [mul_inv_cancel, mul_one]
      rw [hsplit]
      exact mul_mem hZu₁ hZu₂'
    have hyx : ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) x = x :=
      s16g_apply_eq_of_odd (s15_Infra_vtil_sq_eq_one V₀ V hV) hodd hpow hZfix hmain
    rw [hγ₁val] at hyx
    exact hyx

theorem s16k_sum_two_transport (h : S16gRowCtx D V₀ V L hV) {D₁ D₂ : FFModel}
    {I₁ I₂ : Subgroup (Vtil V₀ V hV)} {π₁ : D₁.Gam →* ↥(lBar V₀ V hV L)}
    {π₂ : D₂.Gam →* ↥(lBar V₀ V hV L)}
    (hZ₁ : fixV (lBar V₀ V hV L) ≤ I₁) (hZ₂ : fixV (lBar V₀ V hV L) ≤ I₂)
    (hsup : fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) = ⊤)
    (h₁ : D₁.RealizesVia (lBar V₀ V hV L) I₁ (fixV (lBar V₀ V hV L)) π₁)
    (h₂ : D₂.RealizesVia (lBar V₀ V hV L) I₂ (fixV (lBar V₀ V hV L)) π₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hne : ∃ m : ↥D₁.sec, (m : D₁.Amb) ∉ D₁.ker)
    (hfix : ∀ (m₁ : ↥D₁.sec) (m₂ : ↥D₂.sec),
      ((m₁ : D₁.Amb) ∉ D₁.ker ∨ (m₂ : D₂.Amb) ∉ D₂.ker) →
      ∃ B : Subgroup ↥(lBar V₀ V hV L), IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B,
        (∃ γ : D₁.Gam, π₁ γ = b ∧ D₁.act γ (m₁ : D₁.Amb) * (m₁ : D₁.Amb)⁻¹ ∈ D₁.ker) ∧
        (∃ γ : D₂.Gam, π₂ γ = b ∧ D₂.act γ (m₂ : D₂.Amb) * (m₂ : D₂.Amb)⁻¹ ∈ D₂.ker)) :
    ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ B : Subgroup (MulAut (Vtil V₀ V hV)),
      B ≤ Mbar D.M V₀ V hV ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x :=
  s16k_sum_two_transport_of_le (barSub_mono V₀ V hV h.setting.hyp151.le)
    hZ₁ hZ₂ hsup h₁ h₂ hp hp2 hne hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
