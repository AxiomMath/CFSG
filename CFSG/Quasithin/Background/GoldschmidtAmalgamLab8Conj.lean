module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7SysAll

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem exists_two_others (h3 : GoldAmL3.GoldHyp3 A B z V) {w ε : CosetGeom (A ⊔ B) A B}
    (hε : (graph (A ⊔ B) A B).Adj w ε) :
    ∃ μ₁ μ₂, (graph (A ⊔ B) A B).Adj w μ₁ ∧ (graph (A ⊔ B) A B).Adj w μ₂ ∧ μ₁ ≠ ε ∧ μ₂ ≠ ε ∧
      μ₁ ≠ μ₂ ∧ ∀ y, (graph (A ⊔ B) A B).Adj w y → y = ε ∨ y = μ₁ ∨ y = μ₂ := by
  obtain ⟨a, b, e, hab, hae, hbe, hset⟩ := Set.ncard_eq_three.mp (h3.ncard_nbrs w)
  have hm : ∀ y, (graph (A ⊔ B) A B).Adj w y → y = a ∨ y = b ∨ y = e := by
    intro y hy
    have : y ∈ nbrs w := hy
    rw [hset] at this
    simpa using this
  have ha : (graph (A ⊔ B) A B).Adj w a := by
    have : a ∈ nbrs w := by rw [hset]; simp
    exact this
  have hb : (graph (A ⊔ B) A B).Adj w b := by
    have : b ∈ nbrs w := by rw [hset]; simp
    exact this
  have he : (graph (A ⊔ B) A B).Adj w e := by
    have : e ∈ nbrs w := by rw [hset]; simp
    exact this
  rcases hm ε hε with h1 | h1 | h1
  · refine ⟨b, e, hb, he, by rw [h1]; exact hab.symm, by rw [h1]; exact hae.symm, hbe, ?_⟩
    intro y hy
    rcases hm y hy with e1 | e1 | e1
    · exact Or.inl (e1.trans h1.symm)
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr e1)
  · refine ⟨a, e, ha, he, by rw [h1]; exact hab, by rw [h1]; exact hbe.symm, hae, ?_⟩
    intro y hy
    rcases hm y hy with e1 | e1 | e1
    · exact Or.inr (Or.inl e1)
    · exact Or.inl (e1.trans h1.symm)
    · exact Or.inr (Or.inr e1)
  · refine ⟨a, b, ha, hb, by rw [h1]; exact hae, by rw [h1]; exact hbe, hab, ?_⟩
    intro y hy
    rcases hm y hy with e1 | e1 | e1
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr e1)
    · exact Or.inl (e1.trans h1.symm)

theorem conj_mem_mul (h : TwoSys A B z V c V₂) {α α' p₁ μ : CosetGeom (A ⊔ B) A B}
    (hαp : (graph (A ⊔ B) A B).Adj α p₁) (hμα' : (graph (A ⊔ B) A B).Adj μ α')
    (hα'p : Nm A B V V₂ α' ≤ ballStab 1 p₁) (hnot' : ¬ Nm A B V V₂ α' ≤ ballStab 1 α)
    {k u : D} (hk : k ∈ Nm A B V V₂ α) (hkα' : k ∈ stab α') (hu : u ∈ Nm A B V V₂ μ)
    (hup : u ∈ ballStab 1 p₁) : ∃ n ∈ Nm A B V V₂ α', k⁻¹ * u * k = u * n := by
  have hVα := goodV_all h α
  have hVα' := goodV_all h α'
  have hE := goodE0_all h hαp
  have hEμ := goodE0_all h hμα'
  have hp1α : CosetGeom.dist p₁ α ≤ 1 := (dist_eq_one_iff_adj.mpr hαp.symm).le
  have hupα : u ∈ stab α := ballStab_le_stab_of_dist_le (n := 1) (γ := p₁) (δ := α) hp1α hup
  have hupp : u ∈ stab p₁ := ballStab_le_stab 1 p₁ hup
  have huQ : u ∈ ballStab 1 α' := hEμ.nm_le hu
  by_cases hq : u ∈ ballStab 1 α
  · refine ⟨1, one_mem _, ?_⟩
    have hc : k * u = u * k := hVα.qv_cent u hq k hk
    calc k⁻¹ * u * k = k⁻¹ * (u * k) := by group
      _ = k⁻¹ * (k * u) := by rw [← hc]
      _ = u * 1 := by group
  · obtain ⟨n₀, hn₀, hn₀α⟩ := IsConcreteLE.not_le_iff_exists.mp hnot'
    have hn₀p : n₀ ∈ ballStab 1 p₁ := hα'p hn₀
    have hn₀E : n₀ ∈ stab α ⊓ stab p₁ :=
      ⟨ballStab_le_stab_of_dist_le (n := 1) (γ := p₁) (δ := α) hp1α hn₀p,
        ballStab_le_stab 1 p₁ hn₀p⟩
    have hqq : n₀⁻¹ * u ∈ ballStab 1 α := hE.index n₀ u hn₀E ⟨hupα, hupp⟩ hn₀α hq
    have hkq : k * (n₀⁻¹ * u) = (n₀⁻¹ * u) * k := hVα.qv_cent _ hqq k hk
    have hN : ∀ w ∈ Nm A B V V₂ α', ∀ g ∈ stab α', g * w * g⁻¹ ∈ Nm A B V V₂ α' :=
      fun w hw g hg => (Subgroup.mem_normalizer_iff.mp (hVα'.norm hg) w).mp hw
    have hn' : k⁻¹ * n₀ * k ∈ Nm A B V V₂ α' := by
      have := hN n₀ hn₀ k⁻¹ ((stab α').inv_mem hkα')
      simpa using this
    have hm : (k⁻¹ * n₀ * k) * n₀⁻¹ ∈ Nm A B V V₂ α' :=
      (Nm A B V V₂ α').mul_mem hn' ((Nm A B V V₂ α').inv_mem hn₀)
    refine ⟨(k⁻¹ * n₀ * k) * n₀⁻¹, hm, ?_⟩
    have e1 : k⁻¹ * u * k = ((k⁻¹ * n₀ * k) * n₀⁻¹) * u := by
      calc k⁻¹ * u * k = k⁻¹ * n₀ * ((n₀⁻¹ * u) * k) := by group
        _ = k⁻¹ * n₀ * (k * (n₀⁻¹ * u)) := by rw [← hkq]
        _ = ((k⁻¹ * n₀ * k) * n₀⁻¹) * u := by group
    rw [e1]
    exact hVα'.qv_cent u huQ _ hm

omit [Finite D] in
theorem conjSub_ballStab_inf (g : ↥(A ⊔ B)) {α' μ : CosetGeom (A ⊔ B) A B} (hg : g • α' = α') :
    conjSub (g : D) (ballStab 1 α' ⊓ ballStab 1 μ) = ballStab 1 α' ⊓ ballStab 1 (g • μ) := by
  rw [conjSub_inf, ← ballStab_smul, ← ballStab_smul, hg]

end GoldAmLab8

end F6

end CFSG.Quasithin
