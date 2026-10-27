module

public import CFSG.Quasithin.Vol2.Ch10SecQ4F6
public import CFSG.Quasithin.Background.G6Transvection
public import CFSG.Quasithin.Vol2.Ch10SecQ4F5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem sup_commV_eq_top {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)}
    (hsupV : (⨆ i, commV (Ks i)) = ⊤) (i₀ : Fin s) :
    commV (Ks i₀) ⊔ (⨆ (i : Fin s) (_ : i ≠ i₀), commV (Ks i)) = ⊤ := by
  rw [eq_top_iff, ← hsupV]
  refine iSup_le fun i => ?_
  by_cases hi : i = i₀
  · rw [hi]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂ (f := fun i (_ : i ≠ i₀) => commV (Ks i)) i hi)

theorem lin_two_case_aux (hV2 : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    {a : MulAut V} {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)}
    (hsupK : (⨆ i, Ks i) = conjClosure (Subgroup.zpowers a) G) (hind : iSupIndep Ks)
    (hcommK : ∀ i j, i ≠ j → ∀ x ∈ Ks i, ∀ y ∈ Ks j, x * y = y * x)
    (hfixV : ∀ i j, i ≠ j → commV (Ks j) ≤ fixV (Ks i)) {i₀ : Fin s}
    (h3 : (s = 1 ∧ G = conjClosure (Subgroup.zpowers a) G) ∨
      (s = 2 ∧ (∀ i, G64.FactorType (Ks i)) ∧ ∃ t ∈ G, t ≠ 1 ∧ t ^ 2 = 1 ∧
        G = conjClosure (Subgroup.zpowers a) G ⊔ Subgroup.zpowers t ∧
        ∀ i j, i ≠ j → (Ks i).map (MulAut.conj t).toMonoidHom = Ks j))
    (hKG : conjClosure (Subgroup.zpowers a) G ≤ G)
    (hKsK : ∀ i, Ks i ≤ conjClosure (Subgroup.zpowers a) G)
    (hW4 : Nat.card (commV (Ks i₀)) = 4)
    (hKW : ∀ k ∈ Ks i₀, ∀ w ∈ commV (Ks i₀), k w ∈ commV (Ks i₀))
    (hfaith : ∀ k ∈ Ks i₀, (∀ w ∈ commV (Ks i₀), k w = w) → k = 1)
    {y : MulAut V} (hyK : y ∈ Ks i₀) (hy3 : orderOf y = 3)
    {v₁ : V} (hv₁W : v₁ ∈ commV (Ks i₀)) (hv₁1 : v₁ ≠ 1)
    {g : MulAut V} {j : Fin s} (hj : (Ks i₀).map (MulAut.conj g⁻¹).toMonoidHom = Ks j)
    (hbK : g⁻¹ * a * g ∈ Ks j)
    (hv₂b : g⁻¹ v₁ ∈ commV (Subgroup.zpowers (g⁻¹ * a * g))) (hji : ¬ j = i₀) :
    ∃ y ∈ G, y (g⁻¹ v₁) = g⁻¹ v₁ ∧ orderOf y = 3 ∧ y v₁ ≠ v₁ ∧
      ∀ z ∈ G, z (g⁻¹ v₁) = g⁻¹ v₁ → Odd (orderOf z) → z ∈ Subgroup.zpowers y := by
  have hv₂fix : g⁻¹ v₁ ∈ fixV (Ks i₀) :=
    hfixV i₀ j (Ne.symm hji) (commV_mono (Subgroup.zpowers_le.mpr hbK) hv₂b)
  refine ⟨y, hKG (hKsK i₀ hyK), hv₂fix y hyK, hy3,
    apply_ne_of_three hV2 hW4 hKW hfaith hyK hy3 hv₁W hv₁1, ?_⟩
  intro z hzG hzv hzodd
  have hs : s = 2 := by
    rcases h3 with ⟨hs1, -⟩ | ⟨hs, -⟩
    · exfalso
      subst hs1
      exact hji (Subsingleton.elim _ _)
    · exact hs
  obtain ⟨-, -, t, htG, -, ht2, hGt, -⟩ := h3.resolve_left (by rintro ⟨h, -⟩; omega)
  have hzK : z ∈ conjClosure (Subgroup.zpowers a) G :=
    mem_of_odd_of_mem_sup_zpowers ht2 (le_normalizer_conjClosure _ G htG) (hGt ▸ hzG) hzodd
  have hcover : ∀ i : Fin s, i = i₀ ∨ i = j := by
    intro i
    have h1 := i.isLt
    have h4 : i₀.val ≠ j.val := fun h => hji (Fin.ext h).symm
    have h2 := i₀.isLt
    have h5 := j.isLt
    rcases (by omega : i.val = i₀.val ∨ i.val = j.val) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hKsup : conjClosure (Subgroup.zpowers a) G = Ks i₀ ⊔ Ks j := by
    apply le_antisymm
    · rw [← hsupK]
      refine iSup_le fun i => ?_
      rcases hcover i with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (hKsK i₀) (hKsK j)
  have hcen : Ks i₀ ≤ Subgroup.centralizer (Ks j : Set (MulAut V)) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => (hcommK i₀ j (Ne.symm hji) x hx w hw).symm
  obtain ⟨z₀, hz₀, z₁, hz₁, rfl⟩ := G6.mem_sup_of_centralizes hcen (hKsup ▸ hzK)
  have hcomm01 : z₀ * z₁ = z₁ * z₀ := hcommK i₀ j (Ne.symm hji) z₀ hz₀ z₁ hz₁
  have hpow : z₀ ^ orderOf (z₀ * z₁) * z₁ ^ orderOf (z₀ * z₁) = 1 := by
    rw [← (Commute.mul_pow hcomm01 _), pow_orderOf_eq_one]
  have hdisj : Ks i₀ ⊓ Ks j = ⊥ := disjoint_iff.mp (hind.pairwiseDisjoint (Ne.symm hji))
  have hz₁1 : z₁ ^ orderOf (z₀ * z₁) = 1 := by
    have hmem : z₁ ^ orderOf (z₀ * z₁) ∈ Ks i₀ ⊓ Ks j := by
      refine ⟨?_, Subgroup.pow_mem _ hz₁ _⟩
      rw [eq_inv_of_mul_eq_one_right hpow]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz₀ _)
    rw [hdisj] at hmem
    exact hmem
  have hz₁odd : Odd (orderOf z₁) := Odd.of_dvd_nat hzodd (orderOf_dvd_of_pow_eq_one hz₁1)
  have hz₀1 : z₀ ^ orderOf (z₀ * z₁) = 1 := by
    rw [hz₁1, mul_one] at hpow
    exact hpow
  have hz₀odd : Odd (orderOf z₀) := Odd.of_dvd_nat hzodd (orderOf_dvd_of_pow_eq_one hz₀1)
  have hz₁v : z₁ (g⁻¹ v₁) = g⁻¹ v₁ := by
    have h1 : z₀ (z₁ (g⁻¹ v₁)) = g⁻¹ v₁ := hzv
    have h2 : z₀⁻¹ (g⁻¹ v₁) = g⁻¹ v₁ := hv₂fix _ (Subgroup.inv_mem _ hz₀)
    calc z₁ (g⁻¹ v₁) = z₀⁻¹ (z₀ (z₁ (g⁻¹ v₁))) := by
          simp only [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      _ = g⁻¹ v₁ := by rw [h1, h2]
  have hz₁e : z₁ = 1 := by
    rw [← hj] at hz₁
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz₁
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hkz
    have hko : orderOf k = orderOf z₁ := by
      rw [← hkz]
      exact (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * k = g⁻¹ * k * g * g⁻¹ by group))
    have hkv : k v₁ = v₁ := by
      have h1 : (g⁻¹ * k * g) (g⁻¹ v₁) = g⁻¹ v₁ := by rw [hkz]; exact hz₁v
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply] at h1
      exact g.symm.injective h1
    have hk1 := eq_one_of_odd_of_fix hV2 hW4 hKW hfaith hk (hko ▸ hz₁odd) hv₁W hv₁1 hkv
    rw [← hkz, hk1, mul_one, inv_mul_cancel]
  rw [hz₁e, mul_one]
  exact mem_zpowers_of_odd hV2 hW4 hKW hfaith hyK hy3 hz₀ hz₀odd

theorem lin_two_case (hV2 : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    {a : MulAut V} (h61 : G64.Hyp61 G a) {v₁ : V}
    (hc : commV (Subgroup.zpowers a) = Subgroup.zpowers v₁) (hv₁1 : v₁ ≠ 1)
    {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)}
    (hsupK : (⨆ i, Ks i) = conjClosure (Subgroup.zpowers a) G) (hind : iSupIndep Ks)
    (hcommK : ∀ i j, i ≠ j → ∀ x ∈ Ks i, ∀ y ∈ Ks j, x * y = y * x)
    (hsupV : (⨆ i, commV (Ks i)) = ⊤) (hfixV : ∀ i j, i ≠ j → commV (Ks j) ≤ fixV (Ks i))
    {i₀ : Fin s} (haK : a ∈ Ks i₀)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, (Ks i).map (MulAut.conj g).toMonoidHom = Ks j)
    (h3 : (s = 1 ∧ G = conjClosure (Subgroup.zpowers a) G) ∨
      (s = 2 ∧ (∀ i, G64.FactorType (Ks i)) ∧ ∃ t ∈ G, t ≠ 1 ∧ t ^ 2 = 1 ∧
        G = conjClosure (Subgroup.zpowers a) G ⊔ Subgroup.zpowers t ∧
        ∀ i j, i ≠ j → (Ks i).map (MulAut.conj t).toMonoidHom = Ks j))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {π : ↥(StatedSL 2 F) →* ↥(Ks i₀)}
    (hπ : (FFModel.nat (StatedSL 2 F)).RealizesVia (Ks i₀) (commV (Ks i₀)) ⊥ π)
    {g : MulAut V} (hg : g ∈ G) (hcomm : a * (g⁻¹ * a * g) = g⁻¹ * a * g * a)
    (hmove : g⁻¹ v₁ ≠ v₁) :
    ∃ y ∈ G, y (g⁻¹ v₁) = g⁻¹ v₁ ∧ orderOf y = 3 ∧ y v₁ ≠ v₁ ∧
      ∀ z ∈ G, z (g⁻¹ v₁) = g⁻¹ v₁ → Odd (orderOf z) → z ∈ Subgroup.zpowers y := by
  have hKG : conjClosure (Subgroup.zpowers a) G ≤ G := conjClosure_le fun h hh z hz =>
    G.mul_mem (G.mul_mem hh ((Subgroup.zpowers_le.mpr h61.mem) hz)) (G.inv_mem hh)
  have hKsK : ∀ i, Ks i ≤ conjClosure (Subgroup.zpowers a) G := fun i => hsupK ▸ le_iSup Ks i
  have hW'fix : (⨆ (i : Fin s) (_ : i ≠ i₀), commV (Ks i)) ≤ fixV (Ks i₀) :=
    iSup₂_le fun i hi => hfixV i₀ i (Ne.symm hi)
  have hVsup := sup_commV_eq_top hsupV i₀
  have hW4 : Nat.card (commV (Ks i₀)) = 4 := by
    rw [card_sec_of_realizesVia_nat 2 hπ, hF]
    norm_num
  have hKW : ∀ k ∈ Ks i₀, ∀ w ∈ commV (Ks i₀), k w ∈ commV (Ks i₀) :=
    fun k hk w hw => hπ.2.2.2.1 ⟨k, hk⟩ w hw
  have hfaith : ∀ k ∈ Ks i₀, (∀ w ∈ commV (Ks i₀), k w = w) → k = 1 := by
    intro k hk hkW
    ext v
    have hv : v ∈ commV (Ks i₀) ⊔ (⨆ (i : Fin s) (_ : i ≠ i₀), commV (Ks i)) :=
      hVsup ▸ Subgroup.mem_top v
    obtain ⟨w, hw, w', hw', rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hkW w hw, hW'fix hw' k hk, MulAut.one_apply]
  obtain ⟨γ, hγ3, hγv⟩ := S153EB6.exists_stated_of_cube hF (S153EB6.cblock (0 : Fin 2) 1)
    (S153EB6.cblock_cube (S153EB6.two_eq_zero_of_card_two hF) (by decide))
  obtain ⟨y, hyK, hy3⟩ := exists_orderOf_eq_three_sec hπ hγ3
    (m' := Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : F))) (Subgroup.mem_top _) (by
      intro hmem
      apply S153EB6.cblock_ne (K := F) (j := (0 : Fin 2)) (k := 1) (by decide)
      have h1 : natAct (StatedSL 2 F) γ (Multiplicative.ofAdd (Pi.single 0 1)) =
          Multiplicative.ofAdd (Pi.single 0 1) := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
      have h2 := congrArg Multiplicative.toAdd h1
      simp only [natAct, toAdd_ofAdd, hγv] at h2
      exact h2)
  have hv₁W : v₁ ∈ commV (Ks i₀) :=
    commV_mono (Subgroup.zpowers_le.mpr haK) (hc ▸ Subgroup.mem_zpowers v₁)
  obtain ⟨j, hj⟩ := hperm g⁻¹ (G.inv_mem hg) i₀
  have hbK : g⁻¹ * a * g ∈ Ks j := by
    rw [← hj]
    exact ⟨a, haK, by simp⟩
  have hv₂b := mem_commV_conj (g := g) hc (hV2 v₁) h61.ne_one
  have hv₂1 : g⁻¹ v₁ ≠ 1 := fun h => hv₁1 (g⁻¹.injective (h.trans (map_one _).symm))
  by_cases hji : j = i₀
  · exfalso
    rw [hji] at hbK
    have hv₂W : g⁻¹ v₁ ∈ commV (Ks i₀) := commV_mono (Subgroup.zpowers_le.mpr hbK) hv₂b
    have hmoveW : ∀ k ∈ Ks i₀, k ≠ 1 → ∃ w ∈ commV (Ks i₀), k w ≠ w := fun k hk hk1 => by
      by_contra hall
      push Not at hall
      exact hk1 (hfaith k hk hall)
    have hb1 : g⁻¹ * a * g ≠ 1 := fun h => h61.ne_one (by
      have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [e, h]
      group)
    exact false_of_commute_transv hV2 hW4 hv₁W hv₂W hv₁1 hv₂1 (Ne.symm hmove)
      (apply_eq_or_of_commV hc (hV2 v₁)) (conj_transv_apply hc (hV2 v₁))
      (hmoveW a haK h61.ne_one) (hmoveW _ hbK hb1) hcomm
  · exact lin_two_case_aux hV2 hsupK hind hcommK hfixV h3 hKG hKsK hW4 hKW hfaith
      hyK hy3 hv₁W hv₁1 hj hbK hv₂b hji

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4
