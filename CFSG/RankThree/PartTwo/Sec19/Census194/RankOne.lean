module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LargeExtraspecial.S111BA5Facts

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

theorem rankOne_eq_top_of_borelQuotient {K Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}
    (h : BorelQuotient D n H π M) (hrank : D.rank = 1) (i : Fin D.rank) :
    CFSG.LieType.CurtisTits.rankOne D.rootGroup i = ⊤ := by
  have hsub : ∀ k : Fin D.rank, k = i := fun k => Fin.ext (by
    have := k.isLt
    have := i.isLt
    omega)
  have hle : (⨆ γ ∈ D.roots, D.rootGroup γ) ≤ CFSG.LieType.CurtisTits.rankOne D.rootGroup i :=
    iSup₂_le fun γ hγ => h.ct.le_rankOne i γ hγ fun k hk => absurd (hsub k) hk
  rw [h.ct.iSup_eq_top] at hle
  exact top_le_iff.1 hle

theorem eq_normalizer_or_top_of_borelQuotient {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    {π : K →* Y} {M : ℕ} (h : BorelQuotient D n H π M) (hrank : D.rank = 1) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) :
    J = Subgroup.normalizer ((T : Subgroup Y) : Set Y) ∨ J = ⊤ := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : borel D H ≤ J.comap π' := fun b hb => by
    rw [Subgroup.mem_comap]
    exact hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  by_cases he : J.comap π' = borel D H
  · left
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  · right
    obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt h.ct h.extras hBJ he
    have hcomap : (⊤ : Subgroup K) ≤ J.comap π' := by
      rw [← rankOne_eq_top_of_borelQuotient h hrank i]
      exact sup_le ((rootGroup_le_borel
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) (ht_single_pos i)).trans
          hBJ) hi
    have hJ' : J.comap π' = ⊤ := top_le_iff.1 hcomap
    have hmap : (J.comap π').map π' = J := Subgroup.map_comap_eq_self_of_surjective hπ' J
    rw [hJ'] at hmap
    rw [← hmap]
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, rfl⟩ := hπ' y
    exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_top x, rfl⟩

theorem eq_normalizer_or_top_psl_two {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) (T : Sylow 2 X) (J : Subgroup X)
    (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J) :
    J = Subgroup.normalizer ((T : Subgroup X) : Set X) ∨ J = ⊤ := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  let e2 : Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1)) K ≃* StatedProj (StatedSL 2 K) :=
    projectiveSpecialLinearGroupEquivStatedProj 2 K
  exact eq_normalizer_or_top_of_borelQuotient (borelQuotient_sl (e2.trans e.symm)) rfl T J hNJ

theorem eq_normalizer_or_top_psu_three {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : StatedClassicalModel X .PSU 3 2 f) (T : Sylow 2 X) (J : Subgroup X)
    (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J) :
    J = Subgroup.normalizer ((T : Subgroup X) : Set X) ∨ J = ⊤ := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact eq_normalizer_or_top_of_borelQuotient
    (borelQuotient_su hcard (by norm_num : 2 ≤ 3) ζ hζ e) rfl T J hNJ

theorem eq_normalizer_or_top_alt_five {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) (T : Sylow 2 X) (J : Subgroup X)
    (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J) :
    J = Subgroup.normalizer ((T : Subgroup X) : Set X) ∨ J = ⊤ := by
  obtain ⟨φ⟩ := h
  have hX : Nat.card X = 60 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.LargeExtraspecial.S11.nat_card_alternating_five]
  have hfac : Nat.factorization 60 2 = 2 := by
    rw [Nat.factorization_def 60 Nat.prime_two]
    have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h60, padicValNat.mul (p := 2) (show (2 : ℕ) ^ 2 ≠ 0 by norm_num)
      (show (15 : ℕ) ≠ 0 by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
  have hT4 : Nat.card (T : Subgroup X) = 4 := by
    have h := Sylow.card_eq_multiplicity T
    rw [hX, hfac] at h
    exact h.trans (by norm_num)
  obtain ⟨T', hT'⟩ : ∃ T' : Subgroup (alternatingGroup (Fin 5)),
      T' = (T : Subgroup X).map φ.toMonoidHom := ⟨_, rfl⟩
  have hmemT : ∀ y : X, φ y ∈ T' ↔ y ∈ (T : Subgroup X) := fun y => by
    rw [hT', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hT'card : Nat.card T' = 4 := by
    rw [hT']
    exact (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).trans hT4
  obtain ⟨c', hc'norm, hc'fix⟩ :=
    CFSG.LargeExtraspecial.S11.exists_conj_fixfree_alternating hT'card
  have hc'T : c' ∉ T' := by
    intro hc
    have h1 : c' = 1 := hc'fix c' hc (by simp)
    have hbot : T' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact fun t ht => hc'fix t ht (by simp [h1])
    rw [hbot, Subgroup.card_bot] at hT'card
    norm_num at hT'card
  obtain ⟨c, hc⟩ : ∃ c : X, φ c = c' := ⟨φ.symm c', φ.apply_symm_apply c'⟩
  have hcT : c ∉ (T : Subgroup X) := by
    intro hcT
    apply hc'T
    rw [← hc]
    exact (hmemT c).2 hcT
  have hcN : c ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    show c * n * c⁻¹ ∈ (T : Subgroup X)
    refine (hmemT (c * n * c⁻¹)).1 ?_
    rw [map_mul, map_mul, map_inv, hc]
    exact hc'norm (φ n) ((hmemT n).2 hn)
  have hN4 : Nat.card (Subgroup.normalizer ((T : Subgroup X) : Set X)) ≠ 4 := by
    intro h4
    have heq : (T : Subgroup X) = Subgroup.normalizer ((T : Subgroup X) : Set X) :=
      Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (le_of_eq (by rw [h4, hT4]))
    apply hcT
    rw [heq]
    exact hcN
  have hdvdN : Nat.card (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∣ 60 := by
    rw [← hX]
    exact Subgroup.card_subgroup_dvd_card _
  have h4N : 4 ∣ Nat.card (Subgroup.normalizer ((T : Subgroup X) : Set X)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (T : Subgroup X)))
    rwa [hT4] at this
  have hab : Nat.card (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∣ Nat.card J :=
    Subgroup.card_dvd_of_le hNJ
  have hb60 : Nat.card J ∣ 60 := by
    rw [← hX]
    exact Subgroup.card_subgroup_dvd_card J
  have key : ∀ a b : ℕ, a ∣ 60 → 4 ∣ a → a ≠ 4 → a ∣ b → b ∣ 60 → b = a ∨ b = 60 := by
    intro a b ha h4 ha4 hdiv hb
    have ha' : a ≤ 60 := Nat.le_of_dvd (by norm_num) ha
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha (by norm_num)
    have hb' : b ≤ 60 := Nat.le_of_dvd (by norm_num) hb
    interval_cases a <;> try omega
    all_goals (interval_cases b <;> omega)
  rcases key _ _ hdvdN h4N hN4 hab hb60 with hba | hb
  · left
    exact (Subgroup.eq_of_le_of_card_ge hNJ (le_of_eq hba)).symm
  · right
    exact Subgroup.eq_top_of_card_eq J (hb.trans hX.symm)

end CFSG.RankThree.PartTwo.Sec19
