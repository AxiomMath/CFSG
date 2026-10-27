module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423Basic
public import CFSG.RankThree.PartTwo.Sec4.RonanK423D4Aux
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFacts
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423.D4

open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartTwo.Sec4.Res423Two CFSG.RankThree.PartTwo.Sec4.RonanK423

section Generic

theorem not_le_sup_of_quasisimple {G : Type*} [Group G] {A B N : Subgroup G}
    (hnorm : ∀ g ∈ A, ∀ h ∈ B, g * h * g⁻¹ ∈ B) (hBN : B ≤ N)
    (hperf : commutator ↥B = ⊤) (hnonab : ∃ u ∈ B, ∃ v ∈ B, u * v ≠ v * u)
    (hcentB : ∀ x ∈ B, (∀ g ∈ B, g * x = x * g) → x ^ 3 = 1 → x = 1)
    (hq : CFSG.IsQuasisimple ↥N) {x : G} (hxN : x ∈ N) (hxc : ∀ n ∈ N, x * n = n * x)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) : ¬ N ≤ A ⊔ B := by
  intro hNle
  obtain ⟨hcomm', hsimp⟩ := hq
  have hcommN : commutator ↥N = ⊤ := Group.isPerfect_def.mp hcomm'
  have hSimple : IsSimpleGroup (↥N ⧸ Subgroup.center ↥N) := hsimp.1
  have hBnorm : (B.subgroupOf N).Normal := core_subgroupOf_normal hnorm hNle
  haveI hMnorm : ((B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N))).Normal :=
    Subgroup.Normal.map hBnorm (QuotientGroup.mk' (Subgroup.center ↥N))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥N))
  rcases hSimple.eq_bot_or_eq_top_of_normal
      ((B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N))) with hM | hM
  · obtain ⟨u, hu, v, hv, huv⟩ := hnonab
    have hmem : (⟨u, hBN hu⟩ : ↥N) ∈ B.subgroupOf N := Subgroup.mem_subgroupOf.mpr hu
    have h1 : QuotientGroup.mk' (Subgroup.center ↥N) (⟨u, hBN hu⟩ : ↥N) ∈
        (B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N)) :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center ↥N)) hmem
    rw [hM, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcv := Subgroup.mem_center_iff.mp h1 (⟨v, hBN hv⟩ : ↥N)
    apply huv
    exact (congrArg Subtype.val hcv).symm
  · have hdec : ∀ w : ↥N, ∃ b ∈ B.subgroupOf N, ∃ k ∈ Subgroup.center ↥N, w = b * k := by
      intro w
      have hw : QuotientGroup.mk' (Subgroup.center ↥N) w ∈
          (B.subgroupOf N).map (QuotientGroup.mk' (Subgroup.center ↥N)) := by
        rw [hM]; exact Subgroup.mem_top _
      obtain ⟨b, hbB, hbw⟩ := Subgroup.mem_map.mp hw
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hbw
      exact ⟨b, hbB, b⁻¹ * w, QuotientGroup.eq.mp hbw, (mul_inv_cancel_left b w).symm⟩
    have hsub : commutator ↥N ≤ B.subgroupOf N := core_commutator_le hdec
    rw [hcommN] at hsub
    have hNB : N ≤ B := by
      intro n hn
      exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_top (⟨n, hn⟩ : ↥N)))
    have hxB : x ∈ B := hNB hxN
    have hxcB : ∀ g ∈ B, g * x = x * g := fun g hg => (hxc g (hBN hg)).symm
    exact hx1 (hcentB x hxB hxcB hx3)

end Generic

section Models

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem Bsub_facts
    (P : D4Par n X σ) (hn : 2 ≤ n) :
    commutator ↥(Bsub σ) = ⊤ ∧ (∃ u ∈ Bsub σ, ∃ v ∈ Bsub σ, u * v ≠ v * u) ∧
      ∀ x ∈ Bsub σ, (∀ g ∈ Bsub σ, g * x = x * g) → x ^ 3 = 1 → x = 1 := by
  haveI := P.charP
  haveI := P.charP_fix
  haveI : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [P.card_fix]; positivity)
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := P.four_le_card_fix hn
  let e := bsubEquiv P
  refine ⟨?_, ?_, ?_⟩
  · haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :=
      (KS11Lie4Proof.isQuasisimple_sl2 hk4).1
    haveI : Group.IsPerfect ↥(Bsub σ) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.isPerfect_def.mp inferInstance
  · refine ⟨(e (CFSG.LieType.Steinberg.sl2Upper 1) : C0 σ), (e _).2,
      (e (CFSG.LieType.Steinberg.sl2Lower 1) : C0 σ), (e _).2, fun h => ?_⟩
    apply sl2_upper_lower_noncomm (F := fixSubfield σ)
    apply e.injective
    apply Subtype.ext
    simpa using h
  · intro x hx hcent _
    have hy : e (e.symm ⟨x, hx⟩) = ⟨x, hx⟩ := e.apply_symm_apply _
    have hyc : e.symm ⟨x, hx⟩ ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, hy]
      exact hcent (e m : C0 σ) (e m).2
    rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot, Subgroup.mem_bot] at hyc
    have : (⟨x, hx⟩ : ↥(Bsub σ)) = 1 := by rw [← hy, hyc, map_one]
    exact congrArg Subtype.val this

theorem Bsub_le_layer
    (P : D4Par n X σ) (hn : 2 ≤ n) {a : C0 σ} (ha : a ∈ Asub σ) :
    Bsub σ ≤ ⁅Subgroup.centralizer ({a} : Set _), Subgroup.centralizer ({a} : Set _)⁆ := by
  have hBC : Bsub σ ≤ Subgroup.centralizer ({a} : Set _) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute ha hb).symm
  haveI : Group.IsPerfect ↥(Bsub σ) := ⟨(Bsub_facts P hn).1⟩
  calc (Bsub σ : Subgroup (C0 σ)) = ⁅Bsub σ, Bsub σ⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ _ := Subgroup.commutator_mono hBC hBC

theorem layer_not_le_AB
    (P : D4Par n X σ) (hn : 2 ≤ n) {a : C0 σ} (ha : a ∈ Asub σ)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ¬ ⁅Subgroup.centralizer ({a} : Set _), Subgroup.centralizer ({a} : Set _)⁆ ≤
      Asub σ ⊔ Bsub σ := by
  haveI : Finite (C0 σ) := finite_C0
  obtain ⟨hperf, hnonab, hcentB⟩ := Bsub_facts P hn
  obtain ⟨hq, hc⟩ := threeA_layer_of_mem_short (K := X) (f := n) hn P.card P.frob ha ha3 ha1
  set R := ⁅Subgroup.centralizer ({a} : Set _), Subgroup.centralizer ({a} : Set _)⁆
    with hR
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥R)) 3 (by rw [hc])
  have hxR : ((w : ↥R) : C0 σ) ∈ R := (w : ↥R).2
  have hxc : ∀ m ∈ R, ((w : ↥R) : C0 σ) * m = m * ((w : ↥R) : C0 σ) := by
    intro m hm
    have h1 := Subgroup.mem_center_iff.mp w.2 ⟨m, hm⟩
    have h2 := congrArg Subtype.val h1
    exact h2.symm
  have hx3 : ((w : ↥R) : C0 σ) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hw] at h
    have h' := congrArg (fun y : ↥(Subgroup.center ↥R) => ((y : ↥R) : C0 σ)) h
    simpa using h'
  have hx1 : ((w : ↥R) : C0 σ) ≠ 1 := by
    intro h
    have h1 : w = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    rw [h1, orderOf_one] at hw
    omega
  exact not_le_sup_of_quasisimple (A := Asub σ) (B := Bsub σ) (N := R)
    (fun g hg h hh => by rw [Asub_Bsub_commute hg hh, mul_inv_cancel_right]; exact hh)
    (Bsub_le_layer P hn ha) hperf hnonab hcentB hq hxR hxc hx1 hx3

theorem layerGen_standard
    (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n)
    {a b : C0 σ} (ha : a ∈ Asub σ) (hb : b ∈ Bsub σ) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    (⊤ : Subgroup (C0 σ)) ≤
      Subgroup.closure {x : C0 σ | ∃ d ∈ Subgroup.closure ({a, b} : Set (C0 σ)),
        d ≠ 1 ∧ x ∈ ⁅Subgroup.centralizer ({d} : Set _),
          Subgroup.centralizer ({d} : Set _)⁆} := by
  set H := Subgroup.closure {x : C0 σ | ∃ d ∈ Subgroup.closure ({a, b} : Set (C0 σ)),
      d ≠ 1 ∧ x ∈ ⁅Subgroup.centralizer ({d} : Set _),
        Subgroup.centralizer ({d} : Set _)⁆} with hH
  have haD : a ∈ Subgroup.closure ({a, b} : Set (C0 σ)) := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Subgroup.closure ({a, b} : Set (C0 σ)) := Subgroup.subset_closure (by simp)
  have hRa : ⁅Subgroup.centralizer ({a} : Set _), Subgroup.centralizer ({a} : Set _)⁆ ≤ H :=
    fun x hx => Subgroup.subset_closure ⟨a, haD, ha1, hx⟩
  have hRb : ⁅Subgroup.centralizer ({b} : Set _), Subgroup.centralizer ({b} : Set _)⁆ ≤ H :=
    fun x hx => Subgroup.subset_closure ⟨b, hbD, hb1, hx⟩
  have hA : Asub σ ≤ H := by
    rw [← layer_eq_Asub_of_mem_Bsub P hb hb3 hb1]
    exact hRb
  have hB : Bsub σ ≤ H := (Bsub_le_layer P hn ha).trans hRa
  have hnot : ¬ H ≤ Asub σ ⊔ Bsub σ := fun h => layer_not_le_AB P hn ha ha3 ha1 (hRa.trans h)
  exact (eq_top_of_maximal_pair (ab_maximal hgold P hn) hA hB hnot).ge

theorem alphaVanishes_C0_big
    (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {D : Subgroup (C0 σ)} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hDexp : ∀ x ∈ D, x ^ 3 = 1) (hD9 : Nat.card D = 9) : AlphaVanishes (C0 σ) D := by
  classical
  haveI : Finite (C0 σ) := finite_C0
  have hZ : Subgroup.center (C0 σ) = ⊥ := center_C0_eq_bot P
  have hDel : CFSG.IsElementaryAbelian 3 D := isElementaryAbelian_three_of hDc hDexp
  by_cases hY : ∃ y ∈ D, y ≠ 1 ∧ ∃ g : C0 σ, g * y * g⁻¹ ∈ Bsub σ
  · obtain ⟨y, hyD, hy1, hyB⟩ := hY
    have hAB := trialityABFacts_of_par hgold P hn
    obtain ⟨g, a, b, ha, hb, ha3, hb3, ha1, hb1, hmap⟩ := inner_Y_case σ hAB n hn P.card P.frob hDel
      (by rw [hD9]; norm_num) hyD (hDexp y hyD) hy1 hyB
    refine alphaVanishes_of_mulEquiv (MulAut.conj g) ?_
    have hDel' := isElementaryAbelian_map_three hDel (MulAut.conj g)
    rw [hmap] at hDel' ⊢
    refine alphaVanishes_of_derived_layers hZ (elemAb_comm hDel') (elemAb_cube hDel')
      (fun d hd hd1 => (layerOK_of_order_three P hn (elemAb_cube hDel' d hd) hd1).1)
      (fun d hd hd1 => (layerOK_of_order_three P hn (elemAb_cube hDel' d hd) hd1).hZ3) ?_
    exact layerGen_standard hgold P hn ha hb ha3 hb3 ha1 hb1
  · push Not at hY
    have hall : ∀ y ∈ D, y ≠ 1 → IsClassX σ y := by
      intro y hy hy1
      rcases three_conj_dichotomy σ n P.one_le P.card P.frob (hDexp y hy) hy1 with h | ⟨g, hg⟩
      · exact h
      · exact absurd hg (hY y hy hy1 g)
    obtain ⟨x₁, hx₁E, hx₁1⟩ : ∃ x₁ ∈ D, x₁ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hle : D ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
      have := Subgroup.card_le_of_le hle
      rw [Subgroup.card_bot] at this
      omega
    have hx₁3 : x₁ ^ 3 = 1 := hDexp x₁ hx₁E
    obtain ⟨x₂, hx₂E, hx₂n⟩ : ∃ x₂ ∈ D, x₂ ∉ Subgroup.zpowers x₁ := by
      by_contra hcon
      push Not at hcon
      have hle : D ≤ Subgroup.zpowers x₁ := fun y hy => hcon y hy
      have h1 := Subgroup.card_le_of_le hle
      rw [card_zpowers_of_cube_one hx₁3 hx₁1, hD9] at h1
      omega
    have hx₂1 : x₂ ≠ 1 := fun h => hx₂n (h ▸ Subgroup.one_mem _)
    have hlay : (⊤ : Subgroup (C0 σ)) ≤ Subgroup.closure {x : C0 σ | ∃ b ∈ D, b ≠ 1 ∧
        x ∈ ⁅Subgroup.centralizer ({b} : Set _), Subgroup.centralizer ({b} : Set _)⁆} := by
      set H := Subgroup.closure {x : C0 σ | ∃ b ∈ D, b ≠ 1 ∧
        x ∈ ⁅Subgroup.centralizer ({b} : Set _), Subgroup.centralizer ({b} : Set _)⁆}
        with hH
      have h1 : ⁅Subgroup.centralizer ({x₁} : Set _),
          Subgroup.centralizer ({x₁} : Set _)⁆ ≤ H :=
        fun x hx => Subgroup.subset_closure ⟨x₁, hx₁E, hx₁1, hx⟩
      have h2 : ⁅Subgroup.centralizer ({x₂} : Set _),
          Subgroup.centralizer ({x₂} : Set _)⁆ ≤ H :=
        fun x hx => Subgroup.subset_closure ⟨x₂, hx₂E, hx₂1, hx⟩
      exact (closure_layer_two_X σ n hn P.card P.frob (hall x₁ hx₁E hx₁1) (hall x₂ hx₂E hx₂1)
        (hDc x₁ hx₁E x₂ hx₂E) (fun h => hx₂n (h ▸ Subgroup.mem_zpowers x₂)) h1 h2).ge
    exact alphaVanishes_of_derived_layers hZ hDc hDexp
      (fun d hd hd1 => (layerOK_of_order_three P hn (hDexp d hd) hd1).1)
      (fun d hd hd1 => (layerOK_of_order_three P hn (hDexp d hd) hd1).hZ3) hlay

end Models

end CFSG.RankThree.PartTwo.Sec4.RonanK423.D4
