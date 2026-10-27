module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBstarStd
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

open TableBSymp SeitzReduction.OmegaPilot
open scoped commutatorElement

variable {K : Type} [Field K]

section PlusBstar

theorem siegelGL_mem_fixSub {m : ℕ} (i₀ i₁ : Fin m) (c : K) :
    siegelGL i₀ i₁ c ∈ fixSub (fun i => i ≠ Sum.inr i₀ ∧ i ≠ Sum.inr i₁) := by
  intro i hi i'
  rw [coe_siegelGL, siegelMat]
  rcases i with j | j <;> rcases i' with j' | j'
  · simp [Matrix.one_apply]
  · simp
  · have h0 : j ≠ i₀ := fun h => hi.1 (by rw [h])
    have h1 : j ≠ i₁ := fun h => hi.2 (by rw [h])
    simp [siegelS, Ne.symm h0, Ne.symm h1]
  · simp [Matrix.one_apply]

theorem bstar_conclusion_map {G : Type*} [Group G] (c : G ≃* G) {E₀ : Subgroup G}
    {φ : MulAut G} {U₁ : Subgroup G} (hU : U₁ ≠ ⊥) (hU2 : IsPGroup 2 U₁)
    (hUE : ∀ e ∈ E₀.map c.toMonoidHom, ∀ u ∈ U₁, e * u * e⁻¹ ∈ U₁)
    (hUφ : ∀ u ∈ U₁, MulAut.congr c φ u ∈ U₁) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ e ∈ E₀, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧
      ∀ u ∈ U, φ u ∈ U := by
  refine ⟨U₁.map c.symm.toMonoidHom, ?_, hU2.map _, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ c.symm.injective]
    exact hU
  · rintro e he _ ⟨u, hu, rfl⟩
    refine ⟨c e * u * (c e)⁻¹, hUE _ ⟨e, he, rfl⟩ u hu, ?_⟩
    simp
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨MulAut.congr c φ u, hUφ u hu, ?_⟩
    simp

variable [Finite K] [CharP K 2]

theorem ggBstarElt_omegaPlusGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 2 ≤ m) :
    GGBstarElt p m (LargeEvenOmega (LargeEvenQPlus K m)) := by
  intro E₀ hE₀ hr _ φ hφ hφE
  have := Fact.mk hp
  obtain ⟨ζ, hζo, hζ, hζ1, hζ2⟩ := exists_zeta (K := K) hp hp2 hpq
  have hAGO : E₀.map (LargeEvenOmega (LargeEvenQPlus K m)).subtype ≤
      LargeEvenOrthGroup (LargeEvenQPlus K m) :=
    (Subgroup.map_subtype_le E₀).trans (omega_le_orth _)
  have hAGc : Nat.card (E₀.map (LargeEvenOmega (LargeEvenQPlus K m)).subtype) = Nat.card E₀ :=
    (Nat.card_congr (E₀.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hAGe : IsElemAbelian p (E₀.map (LargeEvenOmega (LargeEvenQPlus K m)).subtype) :=
    TableB.isElemAbelian_map hE₀ _
  obtain ⟨g, hgO, χ, hχ, hsurj⟩ := exists_orth_conj_plus hp2 hζo hAGO hAGe (hAGc ▸ hr)
  have hcA : ∀ (a : LargeEvenOmega (LargeEvenQPlus K m)) (ha : a ∈ E₀),
      ((conjOmega hgO a : LargeEvenOmega (LargeEvenQPlus K m)) : GL (Fin m ⊕ Fin m) K) =
      TauCeti.diagGL (pairedUnits fun j => χ j ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩) := by
    intro a ha
    have h1 := hχ ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩
    rw [coe_conjOmega]
    rw [← h1]
  have hE₁diag : ∀ e ∈ E₀.map (conjOmega hgO).toMonoidHom,
      ∃ δ, (e : GL (Fin m ⊕ Fin m) K) = TauCeti.diagGL δ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, hcA a ha⟩
  have hE₁surj : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) →
      ∃ e ∈ E₀.map (conjOmega hgO).toMonoidHom,
        (e : GL (Fin m ⊕ Fin m) K) = TauCeti.diagGL (pairedUnits u) := by
    intro u hu
    obtain ⟨x, hx⟩ := hsurj u hu
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    refine ⟨conjOmega hgO a, ⟨a, ha, rfl⟩, ?_⟩
    have hx' : x = ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩ := Subtype.ext hax.symm
    rw [hcA a ha, ← hx']
    congr 2
    funext j
    exact hx j
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hζinv1 : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hζ1
  have hne : ζ ≠ ζ⁻¹ := fun h => hζ2 (by nth_rewrite 2 [h]; exact mul_inv_cancel ζ)
  have hpow1 : ∀ (j : Fin m) (z : Kˣ), z ^ p = 1 → ∀ k, (Pi.mulSingle j z : Fin m → Kˣ) k ^ p = 1 :=
    fun j z hz k => by
      rw [Pi.mulSingle_apply]
      split_ifs
      · exact hz
      · exact one_pow p
  have hζinvp : ζ⁻¹ ^ p = 1 := by rw [inv_pow, hζ, inv_one]
  set u₁ : Fin m → Kˣ := Pi.mulSingle i₀ ζ * Pi.mulSingle i₁ ζ⁻¹ with hu₁
  have hu₁p : ∀ k, u₁ k ^ p = 1 := fun k => by
    rw [hu₁, Pi.mul_apply, mul_pow, hpow1 i₀ ζ hζ k, hpow1 i₁ ζ⁻¹ hζinvp k, one_mul]
  have hu₁0 : u₁ i₀ = ζ := by
    rw [hu₁, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm h01), mul_one]
  have hu₁1 : u₁ i₁ = ζ⁻¹ := by
    rw [hu₁, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, one_mul]
  have hu₁o : ∀ j, j ≠ i₀ → j ≠ i₁ → u₁ j = 1 := fun j h0 h1 => by
    rw [hu₁, Pi.mul_apply, Pi.mulSingle_eq_of_ne h0, Pi.mulSingle_eq_of_ne h1, one_mul]
  set E₁ := E₀.map (conjOmega hgO).toMonoidHom with hE₁
  set H : Set (LargeEvenOmega (LargeEvenQPlus K m)) := {h | h ∈ E₁ ∧
    ((h : GL (Fin m ⊕ Fin m) K) = TauCeti.diagGL (pairedUnits u₁) ∨
      ∃ j : Fin m, j ≠ i₀ ∧ j ≠ i₁ ∧
        (h : GL (Fin m ⊕ Fin m) K) = TauCeti.diagGL (pairedUnits (Pi.mulSingle j ζ)))} with hH
  have hHE : H ⊆ E₁ := fun h hh => hh.1
  obtain ⟨h₁, h₁E, hh₁⟩ := hE₁surj u₁ hu₁p
  have hHsiegel : ∀ h ∈ H, ∃ u : Fin m → Kˣ, (h : GL (Fin m ⊕ Fin m) K) =
      TauCeti.diagGL (pairedUnits u) ∧ (u i₀ : K) * (u i₁ : K) = 1 := by
    rintro h ⟨-, hh | ⟨j, hj0, hj1, hh⟩⟩
    · refine ⟨u₁, hh, ?_⟩
      rw [hu₁0, hu₁1]
      exact Units.mul_inv ζ
    · refine ⟨Pi.mulSingle j ζ, hh, ?_⟩
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hj0), Pi.mulSingle_eq_of_ne (Ne.symm hj1), Units.val_one,
        one_mul]
  have hsieΩ : ∀ c : K, siegelGL i₀ i₁ c ∈ LargeEvenOmega (LargeEvenQPlus K m) := fun c =>
    siegelGL_mem_omegaPlus hζ hζ1 h01 c
  set Y : Subgroup (LargeEvenOmega (LargeEvenQPlus K m)) :=
    (siegelHom i₀ i₁).range.comap (LargeEvenOmega (LargeEvenQPlus K m)).subtype with hY
  have hmemY : ∀ y : LargeEvenOmega (LargeEvenQPlus K m), y ∈ Y ↔
      ∃ c : K, siegelGL i₀ i₁ c = (y : GL (Fin m ⊕ Fin m) K) := by
    intro y
    rw [hY, Subgroup.mem_comap]
    exact ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩
  have hYF : BFam H E₁ Y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨c, hc⟩ := (hmemY y).mp y.2
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hc, sq, siegelGL_mul, CharTwo.add_self_eq_zero]
      exact Units.ext (siegelMat_zero i₀ i₁)
    · intro y hy h hh
      obtain ⟨c, hc⟩ := (hmemY y).mp hy
      obtain ⟨u, hu, hu1⟩ := hHsiegel h hh
      apply Subtype.ext
      have h1 := diagGL_pairedUnits_conj_siegelGL u i₀ i₁ c
      rw [hu1, one_mul, ← hu, hc] at h1
      simp only [Subgroup.coe_mul]
      calc (y : GL (Fin m ⊕ Fin m) K) * (h : GL (Fin m ⊕ Fin m) K) =
          (h : GL (Fin m ⊕ Fin m) K) * (y : GL (Fin m ⊕ Fin m) K) *
            (h : GL (Fin m ⊕ Fin m) K)⁻¹ * (h : GL (Fin m ⊕ Fin m) K) := by rw [h1]
        _ = (h : GL (Fin m ⊕ Fin m) K) * (y : GL (Fin m ⊕ Fin m) K) := by group
    · intro e he y hy
      obtain ⟨c, hc⟩ := (hmemY y).mp hy
      obtain ⟨a, ha, rfl⟩ := he
      rw [hmemY]
      set u := fun j => χ j ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩ with hu
      refine ⟨(u i₀ : K) * (u i₁ : K) * c, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, hcA a ha, ← hc]
      exact (diagGL_pairedUnits_conj_siegelGL u i₀ i₁ c).symm
    · intro y hy
      obtain ⟨c, hc⟩ := (hmemY y).mp hy
      obtain ⟨t₀, ht₀E, ht₀⟩ := hE₁surj (Pi.mulSingle i₀ ζ) (hpow1 i₀ ζ hζ)
      have hζK : (1 : K) - (ζ : K) ≠ 0 := sub_ne_zero.mpr fun h => hζ1 (Units.ext h.symm)
      set c' := c / ((1 : K) - (ζ : K)) with hc'
      obtain ⟨y', hy'⟩ : ∃ y' : LargeEvenOmega (LargeEvenQPlus K m),
          (y' : GL (Fin m ⊕ Fin m) K) = siegelGL i₀ i₁ c' := ⟨⟨_, hsieΩ c'⟩, rfl⟩
      have hy'Y : y' ∈ Y := (hmemY y').mpr ⟨c', hy'.symm⟩
      have hcomm : ⁅y', t₀⁆ = y := by
        apply Subtype.ext
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht₀]
        have h1 := diagGL_pairedUnits_conj_siegelGL (Pi.mulSingle i₀ ζ) i₀ i₁ (-c')
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, Units.val_one, mul_one] at h1
        calc (y' : GL (Fin m ⊕ Fin m) K) * TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ)) *
              (y' : GL (Fin m ⊕ Fin m) K)⁻¹ *
              (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ)))⁻¹ =
            siegelGL i₀ i₁ c' * (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ)) *
              siegelGL i₀ i₁ (-c') * (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ)))⁻¹) := by
              rw [hy', siegelGL_inv]
              group
          _ = siegelGL i₀ i₁ (c' + (ζ : K) * -c') := by rw [h1, siegelGL_mul]
          _ = (y : GL (Fin m ⊕ Fin m) K) := by
            rw [← hc]
            congr 1
            rw [hc']
            field_simp
            ring
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hy'Y ht₀E
  have hYU : Y ≤ (fixSub fun i => i ≠ Sum.inr i₀ ∧ i ≠ Sum.inr i₁).comap
      (LargeEvenOmega (LargeEvenQPlus K m)).subtype := by
    intro y hy
    obtain ⟨c, hc⟩ := (hmemY y).mp hy
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, ← hc]
    exact siegelGL_mem_fixSub i₀ i₁ c
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    have h1 : (⟨siegelGL i₀ i₁ 1, hsieΩ 1⟩ : LargeEvenOmega (LargeEvenQPlus K m)) ∈ Y :=
      (hmemY _).mpr ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    have h3 : siegelGL i₀ i₁ (1 : K) = siegelGL i₀ i₁ 0 := by
      rw [show siegelGL i₀ i₁ (0 : K) = 1 from Units.ext (siegelMat_zero i₀ i₁)]
      exact h2
    exact one_ne_zero (siegelGL_injective h01 h3)
  set φ₁ := MulAut.congr (conjOmega hgO) φ with hφ₁
  have hφ₁p : φ₁ ^ p = 1 := by rw [hφ₁, ← map_pow, hφ, map_one]
  have hφ₁E : ∀ e ∈ E₁, φ₁ e = e := by
    rintro _ ⟨a, ha, rfl⟩
    simp [hφ₁, hφE a ha]
  obtain ⟨t₀, ht₀E, ht₀⟩ := hE₁surj (Pi.mulSingle i₀ ζ) (hpow1 i₀ ζ hζ)
  have hsep : ∀ i, i ≠ Sum.inl i₀ → i ≠ Sum.inr i₀ → i ≠ Sum.inl i₁ → i ≠ Sum.inr i₁ → ∀ k,
      (∀ h ∈ H, ∀ δ, (h : GL (Fin m ⊕ Fin m) K) = TauCeti.diagGL δ → δ k = δ i) →
      ∀ e ∈ E₁, ∀ δ, (e : GL (Fin m ⊕ Fin m) K) = TauCeti.diagGL δ → δ k = δ i := by
    intro i hi0 hi0' hi1 hi1' k hk e _ δ _
    obtain ⟨j, hj0, hj1, hij⟩ : ∃ j : Fin m, j ≠ i₀ ∧ j ≠ i₁ ∧ (i = Sum.inl j ∨ i = Sum.inr j) := by
      rcases i with j | j
      · exact ⟨j, fun h => hi0 (by rw [h]), fun h => hi1 (by rw [h]), Or.inl rfl⟩
      · exact ⟨j, fun h => hi0' (by rw [h]), fun h => hi1' (by rw [h]), Or.inr rfl⟩
    obtain ⟨hj, hjE, hhj⟩ := hE₁surj (Pi.mulSingle j ζ) (hpow1 j ζ hζ)
    have h1 := hk hj ⟨hjE, Or.inr ⟨j, hj0, hj1, hhj⟩⟩ _ hhj
    have hki : k = i := by
      rcases hij with rfl | rfl <;> rcases k with k | k
      · by_cases hkj : k = j
        · rw [hkj]
        · simp only [pairedUnits, Sum.elim_inl, Pi.mulSingle_eq_same,
            Pi.mulSingle_eq_of_ne hkj] at h1
          exact absurd h1.symm hζ1
      · exfalso
        by_cases hkj : k = j
        · rw [hkj] at h1
          simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same] at h1
          exact hne h1.symm
        · simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same,
            Pi.mulSingle_eq_of_ne hkj, inv_one] at h1
          exact hζ1 h1.symm
      · exfalso
        by_cases hkj : k = j
        · rw [hkj] at h1
          simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same] at h1
          exact hne h1
        · simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr, Pi.mulSingle_eq_same,
            Pi.mulSingle_eq_of_ne hkj] at h1
          exact hζinv1 h1.symm
      · by_cases hkj : k = j
        · rw [hkj]
        · simp only [pairedUnits, Sum.elim_inr, Pi.mulSingle_eq_same,
            Pi.mulSingle_eq_of_ne hkj, inv_one] at h1
          exact absurd h1.symm hζinv1
    rw [hki]
  have hδ₁o : ∀ j, j ≠ Sum.inl i₀ → j ≠ Sum.inr i₀ → j ≠ Sum.inl i₁ → j ≠ Sum.inr i₁ →
      pairedUnits u₁ j ≠ ζ ∧ pairedUnits u₁ j ≠ ζ⁻¹ := by
    intro j hj0 hj0' hj1 hj1'
    rcases j with j | j
    · rw [pairedUnits, Sum.elim_inl, hu₁o j (fun h => hj0 (by rw [h])) (fun h => hj1 (by rw [h]))]
      exact ⟨hζ1.symm, hζinv1.symm⟩
    · rw [pairedUnits, Sum.elim_inr,
        hu₁o j (fun h => hj0' (by rw [h])) (fun h => hj1' (by rw [h])), inv_one]
      exact ⟨hζ1.symm, hζinv1.symm⟩
  obtain ⟨U₁, hU₁, hU₁2, hU₁E, hU₁φ⟩ := exists_invariant_twoSubgroup (QF := qPlusForm K m)
    (isHypCoord_qPlusForm i₀) (isHypCoord_qPlusForm i₁)
    (fun h => h01 (Sum.inl_injective h).symm) Sum.inl_ne_inr Sum.inr_ne_inl
    (fun h => h01 (Sum.inr_injective h).symm)
    (by rw [coe_qPlusForm]; exact omega_le_orth _) hHE hζ2 (δ₁ := pairedUnits u₁)
    ⟨h₁, ⟨h₁E, Or.inl hh₁⟩, hh₁⟩ hu₁0 (by rw [pairedUnits, Sum.elim_inr, hu₁1, inv_inv])
    (by rw [pairedUnits, Sum.elim_inr, hu₁0]) hu₁1 hδ₁o hE₁diag hsep
    (δ₀ := pairedUnits (Pi.mulSingle i₀ ζ))
    ⟨t₀, ht₀E, ht₀⟩ (by simp [pairedUnits]) (by simp [pairedUnits, Pi.mulSingle_eq_of_ne h01])
    hYF hYU hY1 (hp.odd_of_ne_two hp2) φ₁ hφ₁p hφ₁E
  exact bstar_conclusion_map (conjOmega hgO) hU₁ hU₁2 hU₁E hU₁φ

theorem ggBstarBound_omegaPlus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {m : ℕ} (hm : 3 ≤ m) :
    GGBstarBound p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) :=
  ggBstarBound_of_elt hp subset_rfl (center_omegaPlus_eq_bot hp hp2 hpq hm)
    (ggBstarElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (by omega)))
      (ggBstarElt_omegaPlusGroup hp hp2 hpq (by omega)))

end PlusBstar

end TableBOrth

end CFSG.StandardType
