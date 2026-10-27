module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F6

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section PGL

variable {F : Type*} [Field F] [Finite F]

theorem pgl2_involution_data614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {z : PGL2 F}
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) :
    ∃ (U : Subgroup (PGL2 F)) (w : PGL2 F), IsCyclic U ∧ z ∈ U ∧ w * w = 1 ∧ w ∉ U ∧
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({z} : Set (PGL2 F)) = U ⊔ Subgroup.zpowers w ∧
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  classical
  by_cases hzJ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  · exact pgl2_inner_involution_data614 hK hcard hzJ hz
  · exact pgl2_outer_involution_data614 hK hcard hzJ hz

theorem card_le_four_of_isElemAbelian_pgl2_614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) (V : Subgroup (PGL2 F)) (hVe : IsElemAbelian 2 V) :
    Nat.card V ≤ 4 := by
  classical
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have := hVe.1.is_comm.comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩
    exact congrArg Subtype.val this
  by_cases hVb : ∀ v ∈ V, v = 1
  · exact card_le_four_of_subset614 (a := 1) (b := 1) (c := 1) (d := 1)
      fun v hv => Or.inl (hVb v hv)
  push Not at hVb
  obtain ⟨u, huV, hu1⟩ := hVb
  have huI : BenderSuzuki.PFAppendixIII.IsInvolution u := ⟨hu1, hVe.2 u huV⟩
  obtain ⟨U, w, hUc, huU, hww, -, hwinv, hC, -⟩ := pgl2_involution_data614 hK hcard huI
  have hVC : ∀ v ∈ V, v ∈ U ⊔ Subgroup.zpowers w := by
    intro v hv
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact hVc v hv u huV
  have hA : ∀ v ∈ V, v ∈ U → v = 1 ∨ v = u := by
    intro v hv hvU
    by_cases hv1 : v = 1
    · exact Or.inl hv1
    · exact Or.inr (pgl2_unique_involution_of_cyclic_subgroup U hUc hvU
        (by rw [← pow_two]; exact hVe.2 v hv) hv1 huU (by rw [← pow_two]; exact huI.2) hu1).symm
  by_cases hB : ∀ v ∈ V, v ∈ U
  · exact card_le_four_of_subset614 (a := 1) (b := u) (c := 1) (d := 1) fun v hv => by
      rcases hA v hv (hB v hv) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  push Not at hB
  obtain ⟨b, hbV, hbU⟩ := hB
  have hbw : ∃ u₀ ∈ U, b = u₀ * w := by
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv (hVC b hbV) with h | h
    · exact absurd h hbU
    · exact h
  obtain ⟨u₀, hu₀, rfl⟩ := hbw
  refine card_le_four_of_subset614 (a := 1) (b := u) (c := u₀ * w) (d := u * (u₀ * w))
    fun v hv => ?_
  rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv (hVC v hv) with h | ⟨u₁, hu₁, rfl⟩
  · rcases hA v hv h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  ·
    have hprod : u₁ * w * (u₀ * w) ∈ U := by
      have e : u₁ * w * (u₀ * w) = u₁ * (w * u₀ * w⁻¹) * (w * w) := by group
      rw [e, hwinv u₀ hu₀, hww, mul_one]
      exact U.mul_mem hu₁ (U.inv_mem hu₀)
    have hb2 : (u₀ * w) * (u₀ * w) = 1 := by rw [← pow_two]; exact hVe.2 _ hbV
    rcases hA _ (V.mul_mem hv hbV) hprod with h' | h'
    · right; right; left
      calc u₁ * w = u₁ * w * (u₀ * w) * (u₀ * w) := by rw [mul_assoc (u₁ * w), hb2, mul_one]
        _ = u₀ * w := by rw [h', one_mul]
    · right; right; right
      calc u₁ * w = u₁ * w * (u₀ * w) * (u₀ * w) := by rw [mul_assoc (u₁ * w), hb2, mul_one]
        _ = u * (u₀ * w) := by rw [h']

theorem card_le_four_of_isElemAbelian_pglRange614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) (V : Subgroup (PGammaL2 F)) (hV : V ≤ pGammaL2PGLRange F)
    (hVe : IsElemAbelian 2 V) : Nat.card V ≤ 4 := by
  classical
  set ι := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) with hι
  have hinj : Function.Injective ι := SemidirectProduct.inl_injective
  set W := V.comap ι with hW
  have hVι : V ≤ ι.range := fun v hv => by
    obtain ⟨x, rfl⟩ := hV hv
    exact ⟨_, rfl⟩
  have hWV : W.map ι = V := Subgroup.map_comap_eq_self hVι
  have hcardW : Nat.card W = Nat.card V := by
    rw [← hWV]
    exact (Subgroup.card_map_of_injective hinj).symm
  rw [← hcardW]
  refine card_le_four_of_isElemAbelian_pgl2_614 hK hcard W ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply hinj
    show ι (a * b) = ι (b * a)
    rw [map_mul, map_mul]
    have := hVe.1.is_comm.comm (⟨ι a, a.2⟩ : ↥V) ⟨ι b, b.2⟩
    exact congrArg Subtype.val this
  · intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hVe.2 _ hx

theorem mem_normalizer_of_commute_pglRange614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {y u g : PGammaL2 F}
    (hy : y ∈ pGammaL2PGLRange F) (hu : u ∈ pGammaL2PGLRange F) (hg : g ∈ pGammaL2PGLRange F)
    (hy5 : orderOf y = 5) (hu2 : orderOf u = 2) (hyu : Commute y u) (hgu : Commute g u) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) := by
  classical
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set ι := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hinj : Function.Injective ι := SemidirectProduct.inl_injective
  obtain ⟨y₁, rfl⟩ := hy
  obtain ⟨u₁, rfl⟩ := hu
  obtain ⟨g₁, rfl⟩ := hg
  have hu₁ : BenderSuzuki.PFAppendixIII.IsInvolution u₁ := by
    have h2 : orderOf u₁ = 2 := by rw [← orderOf_injective _ hinj u₁]; exact hu2
    refine ⟨fun h => ?_, ?_⟩
    · rw [h, orderOf_one] at h2; norm_num at h2
    · have h := pow_orderOf_eq_one u₁
      simp only [h2] at h
      exact h
  have hy₁ : orderOf y₁ = 5 := by rw [← orderOf_injective _ hinj y₁]; exact hy5
  have hyu₁ : Commute y₁ u₁ := hinj (by rw [map_mul, map_mul]; exact hyu.eq)
  have hgu₁ : Commute g₁ u₁ := hinj (by rw [map_mul, map_mul]; exact hgu.eq)
  obtain ⟨U, w, hUc, -, hww, -, hwinv, hC, -⟩ := pgl2_involution_data614 hK hcard hu₁
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have : IsCyclic ↥U := hUc
    let _ : CommGroup ↥U := IsCyclic.commGroup
    have := mul_comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hsq : ∀ u ∈ U, (u * w) ^ 2 = 1 := by
    intro u hu
    rw [pow_two]
    calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
      _ = u * u⁻¹ * (w * w) := by rw [hwinv u hu]
      _ = 1 := by rw [hww]; group
  have hUw : ∀ u ∈ U, ∀ x ∈ U, (u * w) * x * (u * w)⁻¹ = x⁻¹ := by
    intro u hu x hx
    calc (u * w) * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hwinv x hx]
      _ = x⁻¹ := by rw [hUcomm u hu _ (U.inv_mem hx)]; group
  have hyU : y₁ ∈ U := by
    have hyC : y₁ ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hC, Subgroup.mem_centralizer_singleton_iff]
      exact hyu₁.eq
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hyC with h | ⟨u, hu, rfl⟩
    · exact h
    · exfalso
      have h2 := orderOf_dvd_of_pow_eq_one (hsq u hu)
      rw [hy₁] at h2
      norm_num at h2
  have hgnorm : g₁ ∈ Subgroup.normalizer (Subgroup.zpowers y₁ : Set (PGL2 F)) := by
    have hgC : g₁ ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hC, Subgroup.mem_centralizer_singleton_iff]
      exact hgu₁.eq
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hgC with hgU | ⟨u, hu, rfl⟩
    ·
      have hc : g₁ * y₁ = y₁ * g₁ := hUcomm g₁ hgU y₁ hyU
      apply mem_normalizer_zpowers_of_conj614
      · rw [hc, mul_inv_cancel_right]
        exact Subgroup.mem_zpowers y₁
      · have e : g₁⁻¹ * y₁ * g₁ = y₁ := by
          calc g₁⁻¹ * y₁ * g₁ = g₁⁻¹ * (y₁ * g₁) := by rw [mul_assoc]
            _ = g₁⁻¹ * (g₁ * y₁) := by rw [hc]
            _ = y₁ := inv_mul_cancel_left g₁ y₁
        rw [e]
        exact Subgroup.mem_zpowers y₁
    ·
      have hgg : u * w * (u * w) = 1 := by
        have h2 := hsq u hu
        rwa [pow_two] at h2
      have hginv : (u * w)⁻¹ = u * w := inv_eq_of_mul_eq_one_right hgg
      have hconj : u * w * y₁ * (u * w)⁻¹ = y₁⁻¹ := hUw u hu y₁ hyU
      apply mem_normalizer_zpowers_of_conj614
      · rw [hconj]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y₁)
      · rw [hginv] at hconj ⊢
        rw [hconj]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y₁)
  have := Subgroup.le_normalizer_map ι ⟨g₁, hgnorm, rfl⟩
  rwa [MonoidHom.map_zpowers] at this

end PGL

end CFSG.Quasithin.H13
