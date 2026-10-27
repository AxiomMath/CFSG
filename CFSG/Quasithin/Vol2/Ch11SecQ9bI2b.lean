module

public import CFSG.Quasithin.Vol2.Ch11SecA12B
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c
public import CFSG.Quasithin.Vol2.Ch11SecSPGL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem card_xTwo (hC : CartanFacts) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hX : IsCartanX T L X) : Nat.card ↥(xOne X (LOf L V₂)) = 2 ^ n - 1 := by
  have d := transportData hN h1102 h hV₁ hV₂ hX
  rw [← d.card (inf_le_left : xOne X (LOf L V₂) ≤ X), d.f₂]
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hP := isSylowTwoOf_P h
  have hU₁ := isFlagW_of_isVi h hV₁
  have hU₂ := isFlagW_of_isVi h hV₂
  have hD := isHall_autOn_cartan h1102 h hX
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  rcases hk with ⟨K, _, _, hK, e, π, hπ, -⟩ | ⟨K, _, _, hK, e, π, hπ, -⟩ |
      ⟨K, _, _, hK, e, hnat⟩
  · exact (hC.sl3 K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).2.2.2.2.2.2
  · exact (hC.sp4 K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1.2.2.2.2.2.2
  · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
    exact (hC.g2 K' n hn hK' _ hsq _ _ π hπ _ hP _ _ hU₁ hU₂ _ hD).1.2.2.2.2.2.2

theorem cartan_inf_centralizer_V2 (hFc : Facts12c) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X) :
    X ⊓ Subgroup.centralizer (V₂ : Set G) = ⊥ := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hP := isSylowTwoOf_P h
  have hU₂ := isFlagW_of_isVi h hV₂
  have hD := isHall_autOn_cartan h1102 h hX
  have hn : 2 ≤ n := h.one_lt
  have hline : CartanLine ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
      (V₂.subgroupOf (fsuV T I)) (autOn X (fsuV T I)) := by
    obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
    rcases hk with ⟨K, _, _, hK, e, π, hπ, -⟩ | ⟨K, _, _, hK, e, π, hπ, -⟩ |
        ⟨K, _, _, hK, e, hnat⟩
    · exact hFc.lineSL3 K n hn hK _ hsq _ _ π hπ _ hP _ hU₂ _ hD
    · exact hFc.lineSp4 K n hn hK _ hsq _ _ π hπ _ hP _ hU₂ _ hD
    · obtain ⟨K', _, _, hK', π, hπ⟩ := hnat
      exact hFc.lineG2 K' n hn hK' _ hsq _ _ π hπ _ hP _ hU₂ _ hD
  rw [eq_bot_iff]
  rintro x ⟨hxX, hxC⟩
  have hxV := L_le_normalizer_fsuV h (hX.1 hxX).1
  have h1 := hline _ (conjV_mem_autOn hxX hxV) fun u hu => by
    have hfix : conjV (fsuV T I) x hxV u = u := Subtype.ext (by
      rw [conjV_apply_coe, ← Subgroup.mem_centralizer_iff.mp hxC u (Subgroup.mem_subgroupOf.mp hu),
        mul_inv_cancel_right])
    rw [hfix, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hxCV : x ∈ X ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h2 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) h1
    simp only [conjV_apply_coe, MulAut.one_apply] at h2
    calc v * x = x * v * x⁻¹ * x := by rw [h2]
      _ = x * v := by group
  rwa [cartan_inf_centralizer h1102 h hX] at hxCV

theorem a318_sup_i (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp11 G T L I n) {i : ℕ} (hi : 1 ≤ i) {U Y : Subgroup G} (hU : IsVi T L I n i U)
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hYV : Y ≤ Subgroup.normalizer (U : Set G))
    (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    A318Conclusion p (K.subgroupOf (K ⊔ Y)) := by
  have hKN := le_of_mem_cComp hK
  have hHN : K ⊔ Y ≤ Subgroup.normalizer (U : Set G) := sup_le hKN hYV
  have hS := sqtkGroup_of_le_normalizer_Vi h hU hi hHN
  have hSQ := SQTKHyp.of_sqtkGroup ↥(K ⊔ Y) hS
  have hKc : K ∈ cComp (K ⊔ Y) := cComp_mem_of_le hK le_sup_left hHN
  obtain ⟨e⟩ := quotPCore_subgroupOf_equiv (L := K) (le_sup_left : K ≤ K ⊔ Y)
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  have hr : 1 < CFSG.Open.pRank p (K.subgroupOf (K ⊔ Y)) := by
    rw [pRank_subgroupOf_eq le_sup_left hp hp2]
    omega
  exact a318 h318 hS (h36 _ hSQ) (h38 _ hSQ) (subgroupOf_mem_cComp hKc) hQ' hp hp2 hr

theorem starImage_equiv {Y : Subgroup G} (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hY : IsPGroup 3 Y) (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∣ 3)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) :
    Nonempty (↥(starImage 3 (K.subgroupOf (K ⊔ Y))) ≃* (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  set H := K ⊔ Y with hH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hYK)
  have hsup : K.subgroupOf H ⊔ Y.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _
  have hA : IsPGroup 3 ↥(Y.subgroupOf H) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  obtain ⟨e⟩ := quotPCore_subgroupOf_equiv (L := K) (le_sup_left : K ≤ H)
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  have hZ' : Nat.card (Subgroup.center (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)))
      ∣ 3 := by
    rw [← Subgroup.map_center_eq e.symm, Subgroup.card_map_of_injective e.symm.injective]
    exact hZ
  have h3' : 3 ∣ Nat.card (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)) := by
    rw [Nat.card_congr e.toEquiv]
    exact h3
  obtain ⟨hO, -⟩ := pPrimeCore_three_eq hsup hA hQ' hZ' h3'
  obtain ⟨φ⟩ := starImage_mulEquiv hO
  exact ⟨φ.trans e⟩

theorem false_of_case_b (hFb : Facts12b) (hFc : Facts12c) (hC : CartanFacts) (hN : NatFacts)
    (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂)
    (hX : IsCartanX T L X) (hK : K ∈ cComp (Subgroup.normalizer (V₂ : Set G)))
    (hNK : Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₂ ≤ K)
    (hA7 : IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7)))
    (hZc : ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
      (y : G) ∈ Subgroup.centralizer (V₂ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX2card := card_xTwo hC hN h1102 h hV₁ hV₂ hX
  obtain ⟨x, hxX, hx1, hxo⟩ := exists_orderOf_eq_of_dvd Nat.prime_three hX2card (by norm_num)
  have hX2V : xOne X (LOf L V₂) ≤ Subgroup.normalizer (V₂ : Set G) :=
    inf_le_left.trans (cartan_le_normalizer_Vi hN h1102 h (Or.inr rfl) hV₂ hX)
  have hX2K : xOne X (LOf L V₂) ≤ Subgroup.normalizer (K : Set G) := hX2V.trans hNK
  have hX23 : IsPGroup 3 ↥(xOne X (LOf L V₂)) :=
    IsPGroup.of_card (n := 1) (by rw [hX2card]; norm_num)
  obtain ⟨hQ, hZ, hrk, -⟩ := hFb.list3.1 _ (hA7.elim Or.inl fun h7 => Or.inr (Or.inl h7))
  have hA7c := hFc.a7 _ hA7
  have h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (show (3 : ℕ) ∣ 9 by norm_num).trans (nine_dvd_card_of_pRank hrk)
  obtain ⟨φ⟩ := starImage_equiv hX2K hX23 hQ hZ h3
  have hxH : x ∈ K ⊔ xOne X (LOf L V₂) := Subgroup.mem_sup_right hxX
  have hxK : x ∈ K := by
    rcases a318_sup_i h318 h36 h38 h (by norm_num) hV₂ hK hX2V hQ Nat.prime_three (by norm_num)
        hrk with h1 | ⟨-, h2⟩ | ⟨-, -, h3a | h3b⟩
    · have hmem : (⟨x, hxH⟩ : ↥(K ⊔ xOne X (LOf L V₂))) ∈ K.subgroupOf (K ⊔ xOne X (LOf L V₂)) := by
        rw [h1]
        exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1,
          by rw [pow_one, Subgroup.orderOf_mk, hxo]⟩
      exact Subgroup.mem_subgroupOf.mp hmem
    · obtain ⟨s, q, -, ⟨p, e, -, -, rfl, hS⟩, -⟩ := h2
      exact (hA7c.2.2 s p e (IsPSLEps3.of_mulEquiv φ hS)).elim
    · have hmem : (⟨x, hxH⟩ : ↥(K ⊔ xOne X (LOf L V₂))) ∈ K.subgroupOf (K ⊔ xOne X (LOf L V₂)) := by
        rw [h3a]
        exact Subgroup.subset_closure ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk, hxo]⟩
      exact Subgroup.mem_subgroupOf.mp hmem
    · obtain ⟨s, q, -, hSL, -⟩ := h3b
      exact (hA7c.2.1 s q (IsSLEps3.of_mulEquiv φ hSL)).elim
  have hB4 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image K (LOf L V₂)) ⧸ CFSG.pCore 2 ↥(modO2Image K (LOf L V₂)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF4, ⟨e₁⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inr rfl) hV₂
    obtain ⟨e₂⟩ := modO2Image_quotEquiv hLK
    exact ⟨F, inferInstance, inferInstance, hF4.trans (by norm_num), ⟨e₂.symm.trans e₁⟩⟩
  have hxbo : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hxK⟩) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simp [← hxo])
      rw [this, map_one]
    · intro h0
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, h0⟩
      have hj' : x ^ 2 ^ j = 1 := by
        simpa using congrArg (fun y => ((y : ↥K) : G)) (congrArg Subtype.val hj)
      have := orderOf_dvd_of_pow_eq_one hj'
      rw [hxo] at this
      exact absurd (Nat.prime_three.dvd_of_dvd_pow this) (by norm_num)
  have hcent := hA7c.1 (modO2Image K (LOf L V₂)) hB4 _ hxbo
    (mk_mem_sectionCentralizer hLK hxK hxX.2)
  have hxC := hZc ⟨x, hxK⟩ hcent (by rw [Subgroup.orderOf_mk, hxo]; exact ⟨1, rfl⟩)
  have hbot : x ∈ X ⊓ Subgroup.centralizer (V₂ : Set G) := ⟨hxX.1, hxC⟩
  rw [cartan_inf_centralizer_V2 hFc h1102 h hV₂ hX, Subgroup.mem_bot] at hbot
  exact hx1 hbot

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
