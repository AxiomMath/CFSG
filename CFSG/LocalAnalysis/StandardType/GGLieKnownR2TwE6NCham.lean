module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NDefs
public import CFSG.LieType.RootSystem.Positivity
public import CFSG.LieType.Steinberg.Minuscule.Datum

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

private def teCham_root (k : Fin 48) : Fin (Tag.rank .F4) → ℤ :=
  (Tag.rootCertificate .F4).root (k : ℕ)

private lemma teCham_root_length : (Tag.rootCertificate .F4).roots.length = 48 := by decide +kernel

private lemma teCham_exists {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) : ∃ k : Fin 48, teCham_root k = γ := by
  obtain ⟨k, hk, hroot⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hγ
  exact ⟨⟨k, by rwa [teCham_root_length] at hk⟩, hroot⟩

private lemma teCham_pos_of_level :
    ∀ k : Fin 48, 1 ≤ teCham_root k twE6Last → 0 < ht (teCham_root k) := by
  decide +kernel

private lemma teCham_ht_pos_of_psi
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (hψ : γ ∈ twE6Psi) : 0 < ht γ := by
  rcases hψ with hlev | hlong
  · obtain ⟨k, hk⟩ := teCham_exists hγ
    rw [← hk] at hlev ⊢
    exact teCham_pos_of_level k hlev
  · simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff] at hlong
    rcases hlong with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma teCham_reflect_last (v : Fin (Tag.rank .F4) → ℤ) :
    reflect .F4 (nf 2) v twE6Last = v twE6Last := by
  simp only [reflect, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  rw [if_neg (by decide : twE6Last ≠ nf 2)]
  simp

private lemma teCham_single0_psi :
    (Pi.single (nf 0) 1 : Fin (Tag.rank .F4) → ℤ) ∈ twE6Psi := by
  have he : (Pi.single (nf 0) 1 : Fin (Tag.rank .F4) → ℤ) = ![1, 0, 0, 0] := by
    funext j; fin_cases j <;> decide
  rw [he]
  right
  simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inr (Or.inr (Or.inl rfl))

private lemma teCham_single1_psi :
    (Pi.single (nf 1) 1 : Fin (Tag.rank .F4) → ℤ) ∈ twE6Psi := by
  have he : (Pi.single (nf 1) 1 : Fin (Tag.rank .F4) → ℤ) = ![0, 1, 0, 0] := by
    funext j; fin_cases j <;> decide
  rw [he]
  right
  simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inl rfl

private lemma teCham_single3_psi :
    (Pi.single (nf 3) 1 : Fin (Tag.rank .F4) → ℤ) ∈ twE6Psi := by
  left
  decide

private lemma teCham_reflect_psi_of_pair_neg
    {γ : Fin (Tag.rank .F4) → ℤ} (hψ : γ ∈ twE6Psi)
    (hpair : (∑ j, Tag.cartan .F4 (nf 2) j * γ j) < 0) :
    reflect .F4 (nf 2) γ ∈ twE6Psi := by
  rcases hψ with hlev | hlong
  · left
    rw [teCham_reflect_last]
    exact hlev
  · simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff] at hlong
    rcases hlong with rfl | rfl | rfl | rfl | rfl | rfl
    · right
      have he : reflect .F4 (nf 2) (![0, 1, 0, 0] : Fin (Tag.rank .F4) → ℤ) = ![0, 1, 2, 0] := by
        funext j; fin_cases j <;> decide
      rw [he]
      simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inl rfl)
    · exfalso; exact absurd hpair (by decide)
    · exfalso; exact absurd hpair (by decide)
    · right
      have he : reflect .F4 (nf 2) (![1, 1, 0, 0] : Fin (Tag.rank .F4) → ℤ) = ![1, 1, 2, 0] := by
        funext j; fin_cases j <;> decide
      rw [he]
      simp only [twE6LongPos0, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exfalso; exact absurd hpair (by decide)
    · exfalso; exact absurd hpair (by decide)

private lemma teCham_reflect_simple_eq :
    ∀ k : Fin 48, 0 < ht (teCham_root k) →
      ht (reflect .F4 (nf 2) (teCham_root k)) < 0 →
      teCham_root k = Pi.single (nf 2) 1 := by
  decide +kernel

private theorem teCham_ht_sub {ι : Type} [Fintype ι] (u v : ι → ℤ) :
    ht (u - v) = ht u - ht v := by
  simp [ht, Finset.sum_sub_distrib]

private theorem teCham_ht_zsmul {ι : Type} [Fintype ι] (m : ℤ) (v : ι → ℤ) :
    ht (m • v) = m * ht v := by
  simp [ht, Finset.mul_sum]

private lemma teCham_single_psi (i : Fin (Tag.rank .F4)) (hi : i ≠ nf 2) :
    (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ twE6Psi := by
  fin_cases i
  · exact teCham_single0_psi
  · exact teCham_single1_psi
  · exact absurd rfl hi
  · exact teCham_single3_psi

private lemma teCham_rightDescent_eq_two (w : WeylGroup .F4)
    (hgood : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ ∈ twE6Psi →
      0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ))
    {i : Fin (Tag.rank .F4)} (hi : (CFSG.LieType.Chevalley.coxeterSystem .F4).IsRightDescent w i) :
    i = nf 2 := by
  by_contra hne
  have hpos := hgood (Pi.single i 1) (IsRoot.basis i) (teCham_single_psi i hne)
  have hle : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w (Pi.single i 1) ≤ 0 :=
    (isRightDescent_iff (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w i).mp hi
  have hsum : ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w
      (Pi.single i 1)) ≤ 0 := by
    rw [ht]
    exact Finset.sum_nonpos fun j _ => hle j
  omega

private lemma teCham_good_mul_simple (w : WeylGroup .F4)
    (hgood : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ ∈ twE6Psi →
      0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ))
    (hi : (CFSG.LieType.Chevalley.coxeterSystem .F4).IsRightDescent w (nf 2)) :
    ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ ∈ twE6Psi →
      0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
        (w * (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2)) γ) := by
  intro γ hγ hψ
  have hαroot' : IsRoot .F4
      (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w (Pi.single (nf 2) 1)) := by
    have h := CFSG.LieType.Chevalley.IsRoot.smul (IsRoot.basis (nf 2)) w
    rwa [smul_def] at h
  have hαle : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w
      (Pi.single (nf 2) 1) ≤ 0 :=
    (isRightDescent_iff (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w (nf 2)).mp hi
  have hαsum : ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w
      (Pi.single (nf 2) 1)) ≤ 0 := by
    rw [ht]
    exact Finset.sum_nonpos fun j _ => hαle j
  have hαneg : ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w
      (Pi.single (nf 2) 1)) < 0 :=
    lt_of_le_of_ne hαsum hαroot'.height_ne_zero
  have hwγ : 0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ) :=
    hgood γ hγ hψ
  rw [← smul_def, mul_smul, simple_smul, smul_def]
  by_cases hp : 0 ≤ (∑ j, Tag.cartan .F4 (nf 2) j * γ j)
  · have hlin : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w
        (reflect .F4 (nf 2) γ) =
        weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ -
          (∑ j, Tag.cartan .F4 (nf 2) j * γ j) •
            weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w (Pi.single (nf 2) 1) := by
      simp only [reflect]
      rw [map_sub, map_zsmul]
    rw [hlin, teCham_ht_sub, teCham_ht_zsmul]
    nlinarith
  · have hpair : (∑ j, Tag.cartan .F4 (nf 2) j * γ j) < 0 := lt_of_not_ge hp
    have hmem := teCham_reflect_psi_of_pair_neg hψ hpair
    exact hgood _ (IsRoot.reflect (nf 2) hγ) hmem

private theorem teCham_good_eq_one_or_simple (w : WeylGroup .F4)
    (hgood : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ ∈ twE6Psi →
      0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ)) :
    w = 1 ∨ w = (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) := by
  suffices H : ∀ n, ∀ w : WeylGroup .F4,
      (CFSG.LieType.Chevalley.coxeterSystem .F4).length w = n →
      (∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ ∈ twE6Psi →
        0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ)) →
      w = 1 ∨ w = (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) by
    exact H _ w rfl hgood
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hlen hg
    by_cases hw : w = 1
    · exact Or.inl hw
    · obtain ⟨i, hi⟩ := (CFSG.LieType.Chevalley.coxeterSystem .F4).exists_rightDescent_of_ne_one hw
      have hi2 : i = nf 2 := teCham_rightDescent_eq_two w hg hi
      rw [hi2] at hi
      have hlt : (CFSG.LieType.Chevalley.coxeterSystem .F4).length
          (w * (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2)) <
          (CFSG.LieType.Chevalley.coxeterSystem .F4).length w := hi
      have hg' := teCham_good_mul_simple w hg hi
      rcases ih ((CFSG.LieType.Chevalley.coxeterSystem .F4).length
            (w * (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2))) (by omega)
          (w * (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2)) rfl hg' with h | h
      · right
        have hs : (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) *
            (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) = 1 :=
          (CFSG.LieType.Chevalley.coxeterSystem .F4).simple_mul_simple_self (nf 2)
        calc w = w * 1 := by rw [mul_one]
          _ = w * ((CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) *
              (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2)) := by rw [hs]
          _ = (w * (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2)) *
              (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) := by rw [mul_assoc]
          _ = 1 * (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) := by rw [h]
          _ = (CFSG.LieType.Chevalley.coxeterSystem .F4).simple (nf 2) := by rw [one_mul]
      · left
        exact mul_right_cancel (by rw [h, one_mul])

private lemma teCham_weyl_simple
    {k : Type} [Field k] (θ : k →+* k) (i : Fin (Tag.rank .F4))
    (β : Fin (twistedDatum k θ).rank → ℤ) :
    weylAction (twistedDatum k θ).isFiniteType
        ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple i) β =
      reflect .F4 i β :=
  CFSG.LieType.Steinberg.Minuscule.weylAction_simple_apply
    (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) i β

private lemma teCham_inv_simple_le
    {k : Type} [Field k] (θ : k →+* k) :
    inversionUnipotent (twistedDatum k θ)
        ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2)) ≤
      (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) := by
  refine iSup₂_le fun γ hγ => ?_
  rcases hγ with ⟨hγroot, hpos, hneg⟩
  have hγr : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγroot
  rw [teCham_weyl_simple θ (nf 2) γ] at hneg
  obtain ⟨k', hk'⟩ := teCham_exists hγr
  have hk'' : teCham_root k' = Pi.single (nf 2) 1 :=
    teCham_reflect_simple_eq k' (by rwa [← hk'] at hpos) (by rwa [← hk'] at hneg)
  rw [← hk', hk'']
  exact le_rfl


theorem twE6_mem_borel_or_panel_of_forall_le
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {g : fixedGroup k θ}
    (h : ∀ γ ∈ (twistedDatum k θ).roots, γ ∈ twE6Psi →
      (twistedDatum k θ).rootGroup γ ≤ twE6Cj g (twE6PosUnip θ)) :
    g ∈ twE6Borel θ ∨ ∃ y ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1), ∃ b ∈ twE6Borel θ,
      g = y * nHat θ (nf 2) * b := by
  have hct := twE6_hct θ hθ
  have hext := twistedDatum_steinbergExtras θ hθ
  have hBU := twistedDatum_bruhatExtras (k := k) (θ := θ)
  obtain ⟨⟨w, b, u⟩, ⟨⟨hb, hu⟩, hg⟩, -⟩ := existsUnique_bruhat_normalForm hct hext hBU g⁻¹
  simp only [Prod.fst, Prod.snd] at hb hu hg
  have hgoodD : ∀ γ ∈ (twistedDatum k θ).roots, γ ∈ twE6Psi →
      0 < ht (weylAction (twistedDatum k θ).isFiniteType w γ) := by
    intro γ hγ hψ
    by_contra hlt
    have hγr : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ
    have hpos : 0 < ht γ := teCham_ht_pos_of_psi hγr hψ
    have hwγroot : IsRoot .F4 (weylAction (twistedDatum k θ).isFiniteType w γ) :=
      isRoot_of_mem_twistedDatum_roots θ
        (weylAction_mem_roots (twistedDatum k θ).isFiniteType w hγ)
    have hneg : ht (weylAction (twistedDatum k θ).isFiniteType w γ) < 0 := by
      rcases IsRoot.height_pos_or_neg hwγroot with hh | hh
      · exact absurd hh hlt
      · exact hh
    have hx1 : ∀ x ∈ (twistedDatum k θ).rootGroup γ, x = 1 := by
      intro x hx
      have hxU : g⁻¹ * x * g ∈ twE6PosUnip θ := by
        obtain ⟨x', hx'U, hx'eq⟩ := Subgroup.mem_map.1 (h γ hγ hψ hx)
        rw [← hx'eq]
        change g⁻¹ * (g * x' * g⁻¹) * g ∈ twE6PosUnip θ
        have heq : g⁻¹ * (g * x' * g⁻¹) * g = x' := by group
        rw [heq]
        exact hx'U
      have hg_inv : g = (b * nrep hct w * u)⁻¹ := by
        rw [← hg]; simp
      have heq : g⁻¹ * x * g =
          b * (nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹) * b⁻¹ := by
        rw [hg, hg_inv]
        group
      have hzU : nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹ ∈ twE6PosUnip θ :=
        (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_posUnipotent hct hb)
          (nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹)).2 (heq ▸ hxU)
      have hxinv : x ∈ inversionUnipotent (twistedDatum k θ) w :=
        rootGroup_le_inversionUnipotent hγ hpos hneg hx
      have hux : u * x * u⁻¹ ∈ inversionUnipotent (twistedDatum k θ) w :=
        mul_mem (mul_mem hu hxinv) (inv_mem hu)
      have hzneg : nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹ ∈
          negUnipotent (twistedDatum k θ) :=
        nrep_conj_mem_negUnipotent hct hux
      have hbot : nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹ = 1 := by
        have hmem := Subgroup.mem_inf.2 ⟨hzU, hzneg⟩
        rwa [posUnipotent_inf_negUnipotent hext, Subgroup.mem_bot] at hmem
      have hy1 : u * x * u⁻¹ = 1 := by
        have := congrArg (fun t => (nrep hct w)⁻¹ * t * nrep hct w) hbot
        simpa [mul_assoc] using this
      have hx1' : x = 1 := by
        have := congrArg (fun t => u⁻¹ * t * u) hy1
        simpa [mul_assoc] using this
      exact hx1'
    have hbot : (twistedDatum k θ).rootGroup γ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hx1 x hx
    exact hext.ne_bot γ hγ hbot
  have hgood0 : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ ∈ twE6Psi →
      0 < ht (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ) := by
    intro γ hγr hψ
    exact hgoodD γ (by rwa [twistedDatum_roots]) hψ
  rcases teCham_good_eq_one_or_simple w hgood0 with hw | hw
  · left
    have hg1 : g⁻¹ = b * nrep hct (1 : twE6W k θ) * u := by
      have hh := hg
      rw [hw] at hh
      exact hh
    have hn1 : nrep hct (1 : twE6W k θ) = 1 := nrep_one hct
    have hmem : g⁻¹ ∈ twE6Borel θ := by
      rw [hg1, hn1, mul_one]
      rw [hw] at hu
      exact mul_mem hb
        (posUnipotent_le_borel (inversionUnipotent_le_posUnipotent (1 : twE6W k θ) hu))
    simpa using inv_mem hmem
  · right
    have hwu : u ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) := by
      rw [hw] at hu
      exact teCham_inv_simple_le θ hu
    have hns : nrep hct
        ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2)) =
        nHat θ (nf 2) := nrep_simple hct (nf 2)
    have hnw : nrep hct w = nHat θ (nf 2) := by
      rw [hw]
      exact hns
    have hg' : g = u⁻¹ * (nHat θ (nf 2))⁻¹ * b⁻¹ := by
      have h1 := congrArg Inv.inv hg
      simp only [inv_inv] at h1
      rw [hnw] at h1
      rw [h1, mul_inv_rev, mul_inv_rev]
      exact (mul_assoc _ _ _).symm
    refine ⟨u⁻¹, inv_mem hwu, (nHat θ (nf 2) ^ 2)⁻¹ * b⁻¹, ?_, ?_⟩
    · exact mul_mem (inv_mem (iSup_le_borel (le_iSup (hHat k θ) (nf 2) (nHat_sq_mem θ (nf 2)))))
        (inv_mem hb)
    · rw [hg']
      group

end CFSG.StandardType.LieKnownR2.Short
