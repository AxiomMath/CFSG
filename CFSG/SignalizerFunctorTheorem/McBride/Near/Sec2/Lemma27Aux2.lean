module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Simple
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.Nonsolvable (simpleComponents IsASimple)
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27

variable {Γ : Type*} [Group Γ]

theorem eq_bot_or_eq_of_conj_mem {J N : Subgroup Γ} (hJ : IsSimpleGroup J) (hNJ : N ≤ J)
    (hN : ∀ u ∈ N, ∀ j ∈ J, j * u * j⁻¹ ∈ N) : N = ⊥ ∨ N = J := by
  have hnorm : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff hNJ).mpr fun p j hp hj => hN p hp j hj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf J) with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (⟨x, hNJ hx⟩ : J) ∈ N.subgroupOf J := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · right
    refine le_antisymm hNJ fun x hx => ?_
    have hmem : (⟨x, hx⟩ : J) ∈ N.subgroupOf J := by rw [h]; trivial
    exact hmem

variable [Finite Γ]

theorem simpleComponents_eq_of_isDirectProduct {L : Subgroup Γ} {𝒟 : Set (Subgroup Γ)}
    (hL : IsDirectProduct 𝒟 L)
    (hD : ∀ D ∈ 𝒟, IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) :
    simpleComponents L = 𝒟 := by
  ext T
  constructor
  · rintro ⟨hTL, hTn, hTs, x, hx, y, hy, hxy⟩
    by_contra hT
    have hTconj : ∀ t ∈ T, ∀ g ∈ L, g * t * g⁻¹ ∈ T := fun t ht g hg =>
      (Subgroup.normal_subgroupOf_iff hTL).mp hTn t g ht hg
    have hbot : ∀ D ∈ 𝒟, T ⊓ D = ⊥ := by
      intro D hDm
      have hDconj : ∀ d ∈ D, ∀ g ∈ L, g * d * g⁻¹ ∈ D := fun d hd g hg =>
        (Subgroup.mem_normalizer_iff.mp (hL.le_normalizer hDm hg) d).mp hd
      have hnorm : ∀ u ∈ T ⊓ D, ∀ t ∈ T, t * u * t⁻¹ ∈ T ⊓ D := fun u hu t ht =>
        Subgroup.mem_inf.mpr
          ⟨mul_mem (mul_mem ht (Subgroup.mem_inf.mp hu).1) (inv_mem ht),
            hDconj u (Subgroup.mem_inf.mp hu).2 t (hTL ht)⟩
      rcases eq_bot_or_eq_of_conj_mem hTs inf_le_left hnorm with h | h
      · exact h
      · exfalso
        have hle : T ≤ D := fun t ht => (Subgroup.mem_inf.mp (h.symm ▸ ht : t ∈ T ⊓ D)).2
        have hnormD : ∀ u ∈ T, ∀ d ∈ D, d * u * d⁻¹ ∈ T := fun u hu d hd =>
          hTconj u hu d (hL.le hDm hd)
        rcases eq_bot_or_eq_of_conj_mem (hD D hDm).1 hle hnormD with h1 | h1
        · exact hxy (by
            have hx1 : x = 1 := by
              have := h1 ▸ hx
              exact Subgroup.mem_bot.mp this
            rw [hx1, one_mul, mul_one])
        · exact hT (h1 ▸ hDm)
    have hcomm : ∀ t ∈ T, ∀ D ∈ 𝒟, ∀ d ∈ D, d * t = t * d := by
      intro t ht D hDm d hd
      have hDconj : ∀ d ∈ D, ∀ g ∈ L, g * d * g⁻¹ ∈ D := fun d hd g hg =>
        (Subgroup.mem_normalizer_iff.mp (hL.le_normalizer hDm hg) d).mp hd
      have hmem : t * d * t⁻¹ * d⁻¹ ∈ T ⊓ D := Subgroup.mem_inf.mpr
        ⟨by
          have h1 := mul_mem ht (hTconj t⁻¹ (inv_mem ht) d (hL.le hDm hd))
          simpa [mul_assoc] using h1,
         mul_mem (hDconj d hd t (hTL ht)) (inv_mem hd)⟩
      rw [hbot D hDm, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
      exact hmem.symm
    have hone : ∀ t ∈ T, t = 1 := by
      intro t ht
      have htL : t ∈ L := hTL ht
      have h1 : (⟨t, htL⟩ : L) = 1 := by
        refine hL.ext_coord fun D hDm => ?_
        rw [map_one]
        apply Subtype.ext
        refine AChief.eq_one_of_forall_commute (hD D hDm).1 (hD D hDm).2
          (hL.coord hDm ⟨t, htL⟩).2 ?_
        intro d hd
        have hcm : (⟨d, hL.le hDm hd⟩ : L) * ⟨t, htL⟩ = ⟨t, htL⟩ * ⟨d, hL.le hDm hd⟩ :=
          Subtype.ext (hcomm t ht D hDm d hd)
        have h2 := congrArg (hL.coord hDm) hcm
        rw [map_mul, map_mul] at h2
        have h3 : hL.coord hDm ⟨d, hL.le hDm hd⟩ = ⟨d, hd⟩ :=
          Subtype.ext (hL.coord_of_mem hDm hd)
        rw [h3] at h2
        simpa using congrArg Subtype.val h2
      exact congrArg Subtype.val h1
    exact hxy (by rw [hone x hx, one_mul, mul_one])
  · intro hT
    refine ⟨hL.le hT, (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le hT)).mpr
      (hL.le_normalizer hT), (hD T hT).1, (hD T hT).2⟩

theorem isSemisimple_of_isDirectProduct {L : Subgroup Γ} {𝒟 : Set (Subgroup Γ)}
    (hL : IsDirectProduct 𝒟 L)
    (hD : ∀ D ∈ 𝒟, IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) : IsSemisimple L := by
  unfold IsSemisimple
  rw [simpleComponents_eq_of_isDirectProduct hL hD]
  exact hL

theorem lcal_eq_of_isDirectProduct {L : Subgroup Γ} {𝒟 : Set (Subgroup Γ)}
    (hL : IsDirectProduct 𝒟 L)
    (hD : ∀ D ∈ 𝒟, IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) : lcal L = 𝒟 := by
  rw [(isSemisimple_of_isDirectProduct hL hD).lcal_eq, simpleComponents_eq_of_isDirectProduct hL hD]

theorem isASimple_of_isDirectProduct {L H : Subgroup Γ} {𝒟 : Set (Subgroup Γ)}
    (hL : IsDirectProduct 𝒟 L)
    (hD : ∀ D ∈ 𝒟, IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) (hne : 𝒟.Nonempty)
    (hHL : H ≤ Subgroup.normalizer (L : Set Γ))
    (htrans : ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, ∃ h ∈ H, D' = D.map (MulAut.conj h).toMonoidHom) :
    IsASimple H L := by
  obtain ⟨D₀, hD₀⟩ := hne
  refine ⟨hHL, ?_, fun N hNL hNn hHN => ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := (hD D₀ hD₀).2
    exact ⟨x, hL.le hD₀ hx, y, hL.le hD₀ hy, hxy⟩
  · by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      have hNconj : ∀ u ∈ N, ∀ g ∈ L, g * u * g⁻¹ ∈ N := fun u hu g hg =>
        (Subgroup.normal_subgroupOf_iff hNL).mp hNn u g hu hg
      obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hN ((Subgroup.eq_bot_iff_forall N).mpr hcon)
      have hnL : n ∈ L := hNL hnN
      obtain ⟨D, hDm, hcoord⟩ : ∃ D, ∃ hDm : D ∈ 𝒟, hL.coord hDm ⟨n, hnL⟩ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : (⟨n, hnL⟩ : L) = 1 := hL.ext_coord fun D hD => by rw [map_one]; exact hcon D hD
        exact hn1 (congrArg Subtype.val this)
      set d₀ : D := hL.coord hDm ⟨n, hnL⟩ with hd₀
      obtain ⟨t, htD, ht⟩ : ∃ t ∈ D, t * (d₀ : Γ) ≠ (d₀ : Γ) * t := by
        by_contra hcon
        push Not at hcon
        refine hcoord (Subtype.ext ?_)
        exact AChief.eq_one_of_forall_commute (hD D hDm).1 (hD D hDm).2 d₀.2 hcon
      have htL : t ∈ L := hL.le hDm htD
      have hDconj : ∀ d ∈ D, ∀ g ∈ L, g * d * g⁻¹ ∈ D := fun d hd g hg =>
        (Subgroup.mem_normalizer_iff.mp (hL.le_normalizer hDm hg) d).mp hd
      have hw : n * t * n⁻¹ * t⁻¹ ∈ N ⊓ D := Subgroup.mem_inf.mpr
        ⟨by
          have h1 := mul_mem hnN (hNconj n⁻¹ (inv_mem hnN) t htL)
          simpa [mul_assoc] using h1,
         mul_mem (hDconj t htD n hnL) (inv_mem htD)⟩
      have hw1 : n * t * n⁻¹ * t⁻¹ ≠ 1 := by
        intro h
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        have hcm : (⟨n, hnL⟩ : L) * ⟨t, htL⟩ = ⟨t, htL⟩ * ⟨n, hnL⟩ := Subtype.ext h
        have h2 := congrArg (hL.coord hDm) hcm
        rw [map_mul, map_mul] at h2
        have h3 : hL.coord hDm ⟨t, htL⟩ = ⟨t, htD⟩ := Subtype.ext (hL.coord_of_mem hDm htD)
        rw [h3, ← hd₀] at h2
        exact ht (congrArg Subtype.val h2).symm
      have hND : D ≤ N := by
        have hnorm : ∀ u ∈ N ⊓ D, ∀ j ∈ D, j * u * j⁻¹ ∈ N ⊓ D := fun u hu j hj =>
          Subgroup.mem_inf.mpr
            ⟨hNconj u (Subgroup.mem_inf.mp hu).1 j (hL.le hDm hj),
              mul_mem (mul_mem hj (Subgroup.mem_inf.mp hu).2) (inv_mem hj)⟩
        rcases eq_bot_or_eq_of_conj_mem (hD D hDm).1 inf_le_right hnorm with h | h
        · exact absurd (by
            have := h ▸ hw
            exact Subgroup.mem_bot.mp this) hw1
        · exact fun x hx => (Subgroup.mem_inf.mp (h.symm ▸ hx : x ∈ N ⊓ D)).1
      refine le_antisymm hNL ?_
      rw [← hL.sSup_eq]
      refine sSup_le fun D' hD' => ?_
      obtain ⟨h, hh, rfl⟩ := htrans D hDm D' hD'
      rintro _ ⟨d, hd, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hHN hh) d).mp (hND hd)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27
