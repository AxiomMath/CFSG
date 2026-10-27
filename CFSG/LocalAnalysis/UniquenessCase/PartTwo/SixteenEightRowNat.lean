module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
variable {W : Type} [CommGroup W]

theorem s16g_transport_fix (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    {H : Subgroup (MulAut W)} {Z : Subgroup W} (hR : (FFModel.nat Γ).Realizes H ⊤ Z)
    (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hne : ∃ a : Multiplicative (ι → K), a ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfix : ∀ a : Multiplicative (ι → K), a ≠ 1 → ∃ B : Subgroup ↥Γ, IsPGroup p B ∧
      ¬ IsCyclic ↥B ∧ ∀ b ∈ B, natAct Γ b a = a)
    {x : W} (hx1 : x ≠ 1) :
    ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b x = x := by
  simp only [FFModel.nat] at hR
  obtain ⟨π, hπ⟩ := hR
  have hπi : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful Γ) hπ
  obtain ⟨hπs, hZU, hkerle, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := hπ
  have build : ∀ (B₀ : Subgroup ↥Γ), IsPGroup p B₀ → ¬ IsCyclic ↥B₀ →
      (∀ b ∈ B₀, ((π b : ↥H) : MulAut W) x = x) →
      ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, b x = x := by
    intro B₀ hBp hBc hfixB
    refine ⟨B₀.map (H.subtype.comp π), ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_map]; exact Subgroup.map_subtype_le (B₀.map π)
    · exact hBp.map (H.subtype.comp π)
    · intro hcyc
      haveI : IsCyclic ↥(B₀.map (H.subtype.comp π)) := hcyc
      exact hBc (isCyclic_of_injective
        (Subgroup.equivMapOfInjective B₀ (H.subtype.comp π)
          (H.subtype_injective.comp hπi)).toMonoidHom
        (Subgroup.equivMapOfInjective B₀ (H.subtype.comp π)
          (H.subtype_injective.comp hπi)).injective)
    · intro b hb
      obtain ⟨b₀, hb₀, hb_eq⟩ := Subgroup.mem_map.mp hb
      rw [← hb_eq]
      exact hfixB b₀ hb₀
  by_cases hxZ : x ∈ Z
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨B₀, hBp, hBc, hfixsub⟩ := hfix a ha
    refine build B₀ hBp hBc ?_
    intro b hb
    exact hZ (π b) (π b).2 x hxZ
  · have hβx_ne : β ⟨x, trivial⟩ ≠ 1 := fun h => hxZ ((hβk ⟨x, trivial⟩).mp h)
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨x, trivial⟩)
    set a : Multiplicative (ι → K) := (m : Multiplicative (ι → K)) with ha_def
    have ha : a ≠ 1 := by
      intro ha1
      have hm1 : m = 1 := Subtype.ext (by rw [← ha_def]; exact ha1)
      have hm' := hm
      rw [hm1] at hm'
      exact hβx_ne (hm'.symm.trans (map_one (QuotientGroup.mk' _)))
    obtain ⟨B₀, hBp, hBc, hfixsub⟩ := hfix a ha
    refine build B₀ hBp hBc ?_
    intro b hb
    have hkey := hβe b ⟨x, trivial⟩ m trivial trivial hm.symm
    have h2 : QuotientGroup.mk (⟨natAct Γ b (m : Multiplicative (ι → K)), trivial⟩ :
        ↥(⊤ : Subgroup (Multiplicative (ι → K)))) = β ⟨x, trivial⟩ := by
      have hsub : (⟨natAct Γ b (m : Multiplicative (ι → K)), trivial⟩ :
          ↥(⊤ : Subgroup (Multiplicative (ι → K)))) = m :=
        Subtype.ext (by rw [← ha_def]; exact hfixsub b hb)
      rw [hsub, hm]
    have h3 : β ⟨((π b : ↥H) : MulAut W) x, trivial⟩ = β ⟨x, trivial⟩ :=
      hkey.trans h2
    have h5 : (⟨((π b : ↥H) : MulAut W) x, trivial⟩ : ↥(⊤ : Subgroup W)) *
        (⟨x, trivial⟩ : ↥(⊤ : Subgroup W))⁻¹ =
        ⟨((π b : ↥H) : MulAut W) x * x⁻¹, trivial⟩ := Subtype.ext rfl
    have h4 : β (⟨((π b : ↥H) : MulAut W) x * x⁻¹, trivial⟩ : ↥(⊤ : Subgroup W)) = 1 := by
      rw [← h5, map_mul, map_inv, h3, mul_inv_cancel]
    have hZmem : ((π b : ↥H) : MulAut W) x * x⁻¹ ∈ Z :=
      (hβk ⟨((π b : ↥H) : MulAut W) x * x⁻¹, trivial⟩).mp h4
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hBp.exists_orderOf_eq_pow (⟨b, hb⟩ : ↥B₀)
    have hbord : orderOf b = p ^ k := by rw [← Subgroup.orderOf_mk b hb, hk]
    have hodd : Odd (orderOf b) := by rw [hbord]; exact (hp.odd_of_ne_two hp2).pow
    have hpow : ((π b : ↥H) : MulAut W) ^ orderOf b = 1 := by
      have h1 : (π b : ↥H) ^ orderOf b = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      simpa using congrArg (fun g : ↥H => (g : MulAut W)) h1
    exact s16g_apply_eq_of_odd hW hodd hpow (fun z hz => hZ (π b) (π b).2 z hz) hZmem

theorem s16g_transport_fix_ord (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    {H : Subgroup (MulAut W)} {Z : Subgroup W} (hR : (FFModel.nat Γ).Realizes H ⊤ Z)
    (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hne : ∃ a : Multiplicative (ι → K), a ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfix : ∀ a : Multiplicative (ι → K), a ≠ 1 → ∃ g : ↥Γ, orderOf g = p ∧ natAct Γ g a = a)
    {x : W} (hx1 : x ≠ 1) :
    ∃ y ∈ H, orderOf y = p ∧ y x = x := by
  simp only [FFModel.nat] at hR
  obtain ⟨π, hπ⟩ := hR
  have hπi : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful Γ) hπ
  obtain ⟨hπs, hZU, hkerle, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := hπ
  have horder : ∀ g : ↥Γ, orderOf g = p → orderOf ((π g : ↥H) : MulAut W) = p := by
    intro g hg
    calc orderOf ((π g : ↥H) : MulAut W) = orderOf (π g) :=
          orderOf_injective H.subtype H.subtype_injective (π g)
      _ = orderOf g := orderOf_injective π hπi g
      _ = p := hg
  by_cases hxZ : x ∈ Z
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨g, hgp, hgfix⟩ := hfix a ha
    exact ⟨((π g : ↥H) : MulAut W), (π g).2, horder g hgp, hZ (π g) (π g).2 x hxZ⟩
  · have hβx_ne : β ⟨x, trivial⟩ ≠ 1 := fun h => hxZ ((hβk ⟨x, trivial⟩).mp h)
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨x, trivial⟩)
    set a : Multiplicative (ι → K) := (m : Multiplicative (ι → K)) with ha_def
    have ha : a ≠ 1 := by
      intro ha1
      have hm1 : m = 1 := Subtype.ext (by rw [← ha_def]; exact ha1)
      have hm' := hm
      rw [hm1] at hm'
      exact hβx_ne (hm'.symm.trans (map_one (QuotientGroup.mk' _)))
    obtain ⟨g, hgp, hgfix⟩ := hfix a ha
    have hkey := hβe g ⟨x, trivial⟩ m trivial trivial hm.symm
    have h2 : QuotientGroup.mk (⟨natAct Γ g (m : Multiplicative (ι → K)), trivial⟩ :
        ↥(⊤ : Subgroup (Multiplicative (ι → K)))) = β ⟨x, trivial⟩ := by
      have hsub : (⟨natAct Γ g (m : Multiplicative (ι → K)), trivial⟩ :
          ↥(⊤ : Subgroup (Multiplicative (ι → K)))) = m :=
        Subtype.ext (by rw [← ha_def]; exact hgfix)
      rw [hsub, hm]
    have h3 : β ⟨((π g : ↥H) : MulAut W) x, trivial⟩ = β ⟨x, trivial⟩ :=
      hkey.trans h2
    have h5 : (⟨((π g : ↥H) : MulAut W) x, trivial⟩ : ↥(⊤ : Subgroup W)) *
        (⟨x, trivial⟩ : ↥(⊤ : Subgroup W))⁻¹ =
        ⟨((π g : ↥H) : MulAut W) x * x⁻¹, trivial⟩ := Subtype.ext rfl
    have h4 : β (⟨((π g : ↥H) : MulAut W) x * x⁻¹, trivial⟩ : ↥(⊤ : Subgroup W)) = 1 := by
      rw [← h5, map_mul, map_inv, h3, mul_inv_cancel]
    have hZmem : ((π g : ↥H) : MulAut W) x * x⁻¹ ∈ Z :=
      (hβk ⟨((π g : ↥H) : MulAut W) x * x⁻¹, trivial⟩).mp h4
    have hodd : Odd (orderOf g) := by rw [hgp]; exact hp.odd_of_ne_two hp2
    have hpow : ((π g : ↥H) : MulAut W) ^ orderOf g = 1 := by
      have h1 : (π g : ↥H) ^ orderOf g = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      simpa using congrArg (fun y : ↥H => (y : MulAut W)) h1
    exact ⟨((π g : ↥H) : MulAut W), (π g).2, horder g hgp,
      s16g_apply_eq_of_odd hW hodd hpow (fun z hz => hZ (π g) (π g).2 z hz) hZmem⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
