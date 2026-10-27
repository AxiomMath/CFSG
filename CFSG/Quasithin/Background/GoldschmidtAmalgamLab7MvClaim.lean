module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7MvE
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Claim
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Crit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem exists_nbr_not_le_mv (h : TwoSys A B z V c V₂) (hmv : ∃ g ∈ A, g * c * g⁻¹ ≠ c)
    {α α' β ε : CosetGeom (A ⊔ B) A B} (hα'0 : vtype α' = false)
    (hαβ : (graph (A ⊔ B) A B).Adj α β) (hα'ε : (graph (A ⊔ B) A B).Adj α' ε)
    (hnot : ¬ Nm A B V V₂ α ≤ ballStab 1 α')
    (hαε : Nm A B V V₂ α ≤ ballStab 1 ε) (hα'β : Nm A B V V₂ α' ≤ ballStab 1 β) :
    ∃ μ, (graph (A ⊔ B) A B).Adj α' μ ∧ μ ≠ ε ∧ ¬ Nm A B V V₂ μ ≤ ballStab 1 β := by
  by_contra hcon
  push Not at hcon
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have hVα := goodV_all h α
  have hVα' := goodV_all h α'
  have hEα'ε := goodE_of_typ0 h hmv hα'0 hα'ε
  have hEαβ := goodE0_all h hαβ
  have hαst : ∀ a ∈ Nm A B V V₂ α, a ∈ stab α' := fun a ha =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := ε) (δ := α')
      (dist_eq_one_iff_adj.mpr hα'ε.symm).le (hαε ha)
  obtain ⟨F, hFα, hFn⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hFst : F ∈ stab α' := hαst F hFα
  have hFstε : F ∈ stab ε := ballStab_le_stab 1 ε (hαε hFα)
  obtain ⟨μ₁, hμ₁adj, hμ₁ne⟩ := exists_adj_ne hEα'ε hα'ε
  have hF'st : F⁻¹ ∈ stab α' := (stab α').inv_mem hFst
  have hF'stε : F⁻¹ ∈ stab ε := (stab ε).inv_mem hFstε
  have hF'n : F⁻¹ ∉ ballStab 1 α' := fun hh => hFn (by simpa using (ballStab 1 α').inv_mem hh)
  obtain ⟨hμ₂adj, hμ₂ne1, hμ₂neε⟩ :=
    smul_nbr_facts hEα'ε hα'ε hα'ε hμ₁adj hμ₁ne.symm hF'st hF'stε hF'n
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ₂, μ₂ = (⟨F⁻¹, stab_le α' hF'st⟩ : ↥(A ⊔ B)) • μ₁ := ⟨_, rfl⟩
  rw [← hμ₂] at hμ₂adj hμ₂ne1 hμ₂neε
  have hNμ₁ : Nm A B V V₂ μ₁ ≤ ballStab 1 β := hcon μ₁ hμ₁adj hμ₁ne
  have hNμ₂ : Nm A B V V₂ μ₂ ≤ ballStab 1 β := hcon μ₂ hμ₂adj hμ₂neε
  have hnot' : ¬ Nm A B V V₂ α' ≤ ballStab 1 α :=
    not_nm_le_symm hVα hVα' (fun a ha => hαst a ha) hnot
  obtain ⟨ν, hνα', hνn⟩ := IsConcreteLE.not_le_iff_exists.mp hnot'
  have hQβ : ∀ x ∈ ballStab 1 β, x ∈ stab α ⊓ stab β := fun x hx =>
    ⟨ballStab_le_stab_of_dist_le (n := 1) (γ := β) (δ := α)
      (dist_eq_one_iff_adj.mpr hαβ.symm).le hx, ballStab_le_stab 1 β hx⟩
  have hdec : ∀ u ∈ ballStab 1 β, ∃ n ∈ Nm A B V V₂ α', ∃ q ∈ ballStab 1 α, u = n * q := by
    intro u hu
    by_cases huq : u ∈ ballStab 1 α
    · exact ⟨1, (Nm A B V V₂ α').one_mem, u, huq, by simp⟩
    · have := hEαβ.index ν u (hQβ ν (hα'β hνα')) (hQβ u hu) hνn huq
      exact ⟨ν, hνα', ν⁻¹ * u, this, by group⟩
  have hNα : ∀ x ∈ Nm A B V V₂ α, ∀ k ∈ stab α, k * x * k⁻¹ ∈ Nm A B V V₂ α := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (hVα.norm hk) x).mp hx
  have hNα' : ∀ x ∈ Nm A B V V₂ α', ∀ k ∈ stab α', k * x * k⁻¹ ∈ Nm A B V V₂ α' := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (hVα'.norm hk) x).mp hx
  have hsub : ∀ w ∈ Nm A B V V₂ μ₂, ∃ u ∈ Nm A B V V₂ μ₁, ∃ m ∈ Nm A B V V₂ α', w = u * m := by
    intro w hw
    have hw' : F * w * F⁻¹ ∈ Nm A B V V₂ μ₁ := by
      have := hw
      rw [hμ₂, Nm_smul hA hB, mem_conjSub] at this
      simpa using this
    obtain ⟨u, hu⟩ : ∃ u, u = F * w * F⁻¹ := ⟨_, rfl⟩
    rw [← hu] at hw'
    obtain ⟨n, hn, q, hq, huq⟩ := hdec u (hNμ₁ hw')
    have hn_stab : n ∈ stab α := (hQβ n (hα'β hn)).1
    have hm' : n⁻¹ * F⁻¹ * n ∈ Nm A B V V₂ α := by
      have := hNα F⁻¹ ((Nm A B V V₂ α).inv_mem hFα) n⁻¹ ((stab α).inv_mem hn_stab)
      simpa using this
    have hmα : n⁻¹ * F⁻¹ * n * F ∈ Nm A B V V₂ α := (Nm A B V V₂ α).mul_mem hm' hFα
    have hmα' : n⁻¹ * F⁻¹ * n * F ∈ Nm A B V V₂ α' := by
      have h1 := hNα' n hn F⁻¹ hF'st
      have := (Nm A B V V₂ α').mul_mem ((Nm A B V V₂ α').inv_mem hn) h1
      simpa [mul_assoc] using this
    have hqF : F * q = q * F := hVα.qv_cent q hq F hFα
    have hmq : (n⁻¹ * F⁻¹ * n * F) * q = q * (n⁻¹ * F⁻¹ * n * F) :=
      hVα.qv_cent q hq _ hmα
    refine ⟨u, hw', n⁻¹ * F⁻¹ * n * F, hmα', ?_⟩
    have hweq : w = F⁻¹ * u * F := by rw [hu]; group
    rw [hweq, huq]
    calc F⁻¹ * (n * q) * F = F⁻¹ * n * (q * F) := by group
      _ = F⁻¹ * n * (F * q) := by rw [← hqF]
      _ = (F⁻¹ * n * F) * q := by group
      _ = (n * (n⁻¹ * F⁻¹ * n * F)) * q := by group
      _ = n * ((n⁻¹ * F⁻¹ * n * F) * q) := by group
      _ = n * (q * (n⁻¹ * F⁻¹ * n * F)) := by rw [hmq]
      _ = (n * q) * (n⁻¹ * F⁻¹ * n * F) := by group
  have hne₁ : ¬ ballStab 1 α' ≤ ballStab 1 μ₁ := (goodE0_all h hμ₁adj).ne
  have hne₂ : ¬ ballStab 1 α' ≤ ballStab 1 μ₂ := (goodE0_all h hμ₂adj).ne
  obtain ⟨qs, hqsQ, hqs1, hqs2⟩ := exists_mem_not_mem_two hne₁ hne₂
  have hqs_α' : qs ∈ stab α' := ballStab_le_stab 1 α' hqsQ
  have hqs_μ₁ : qs ∈ stab μ₁ := ballStab_le_stab_of_dist_le (n := 1) (γ := α') (δ := μ₁)
    (dist_eq_one_iff_adj.mpr hμ₁adj).le hqsQ
  have hqs_μ₂ : qs ∈ stab μ₂ := ballStab_le_stab_of_dist_le (n := 1) (γ := α') (δ := μ₂)
    (dist_eq_one_iff_adj.mpr hμ₂adj).le hqsQ
  have hVμ₁ := goodV_all h μ₁
  have hVμ₂ := goodV_all h μ₂
  apply hqs2
  refine hVμ₂.cent_le qs hqs_μ₂ fun w hw => ?_
  obtain ⟨u, hu, m, hm, rfl⟩ := hsub w hw
  have ht₁ := commutator_mem_Fx0 hVμ₁ (goodE0_all h hμ₁adj.symm) (u := qs) ⟨hqs_μ₁, hqs_α'⟩ hqs1 hu
  have ht₂ := commutator_mem_Fx0 hVμ₂ (goodE0_all h hμ₂adj.symm) (u := qs) ⟨hqs_μ₂, hqs_α'⟩ hqs2 hw
  have hmqs : m * qs = qs * m := hVα'.qv_cent qs hqsQ m hm
  have hm_μ₁ : m ∈ ballStab 1 μ₁ := (goodE0_all h hμ₁adj).nm_le hm
  have hct : (u⁻¹ * qs⁻¹ * u * qs) * m = m * (u⁻¹ * qs⁻¹ * u * qs) :=
    hVμ₁.qv_cent m hm_μ₁ _ (mem_Fx.mp ht₁).1
  have heq : (u * m)⁻¹ * qs⁻¹ * (u * m) * qs = u⁻¹ * qs⁻¹ * u * qs := by
    calc (u * m)⁻¹ * qs⁻¹ * (u * m) * qs = m⁻¹ * (u⁻¹ * qs⁻¹ * u) * (m * qs) := by group
      _ = m⁻¹ * (u⁻¹ * qs⁻¹ * u) * (qs * m) := by rw [hmqs]
      _ = m⁻¹ * ((u⁻¹ * qs⁻¹ * u * qs) * m) := by group
      _ = m⁻¹ * (m * (u⁻¹ * qs⁻¹ * u * qs)) := by rw [hct]
      _ = u⁻¹ * qs⁻¹ * u * qs := by group
  have ht₂' : (u * m)⁻¹ * qs⁻¹ * (u * m) * qs ∈ Fx V V₂ μ₁ α' := by
    rw [heq]
    exact ht₁
  have h1 := eq_one_of_mem_Fx_of_mem_Fx hA hB hEα'ε hα'ε hμ₁adj hμ₂adj hμ₂ne1.symm ht₂' ht₂
  have h2 : qs⁻¹ * (u * m) * qs = u * m := by
    calc qs⁻¹ * (u * m) * qs = (u * m) * ((u * m)⁻¹ * qs⁻¹ * (u * m) * qs) := by group
      _ = u * m := by rw [h1, mul_one]
  calc (u * m) * qs = qs * (qs⁻¹ * (u * m) * qs) := by group
    _ = qs * (u * m) := by rw [h2]

end GoldAmLab7

end F6

end CFSG.Quasithin
