
module

public import CFSG.Quasithin.Background.C1GNA7Base
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C1GN

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonJ_le_baum (T : Subgroup G) : thompsonJ T ≤ baum T := by
  refine le_inf (thompsonJ_le T) ?_
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact (Subgroup.mem_centralizer_iff.1 (omegaOneCenterOf_le_centerOf (thompsonJ T) he).2 j hj).symm

omit [Finite G] in
theorem conjSub_le_of_mem {M K : Subgroup G} {t : G} (ht : t ∈ M) (hK : K ≤ M) :
    B6.conjSub t K ≤ M := by
  intro x hx
  have h : t⁻¹ * x * t ∈ K := B6.mem_conjSub.1 hx
  have h2 : t * (t⁻¹ * x * t) * t⁻¹ ∈ M := M.mul_mem (M.mul_mem ht (hK h)) (M.inv_mem ht)
  have h3 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
  rwa [h3] at h2

omit [Finite G] in
theorem conjClosure_eq_iSup {T : Subgroup G} {r : ℕ} (K : Fin r → Subgroup G)
    (hperm : ∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j)
    (htrans : ∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j) (i : Fin r) :
    conjClosure (K i) T = ⨆ j, K j := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨j, hj⟩ := hperm h hh i
    have h1 : h * z * h⁻¹ ∈ B6.conjSub h (K i) := by
      rw [B6.mem_conjSub]
      have : h⁻¹ * (h * z * h⁻¹) * h = z := by group
      rwa [this]
    rw [hj] at h1
    exact Subgroup.mem_iSup_of_mem j h1
  · refine iSup_le fun j => ?_
    obtain ⟨t, ht, htj⟩ := htrans i j
    intro x hx
    rw [← htj, B6.mem_conjSub] at hx
    have h1 := mem_conjClosure ht hx
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [h2] at h1

omit [Finite G] in
theorem isChiBlock_of_isChi0Block {X U K : Subgroup G} (hX : IsBlock2 X K) (h : IsChi0Block U K) :
    IsChiBlock X K := by
  refine ⟨hX, ?_⟩
  rcases h.2 with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨3, by decide, le_rfl, h⟩
  · exact Or.inr ⟨5, by decide, by norm_num, h⟩

omit [Finite G] in
theorem commutator_le_of_le_normalizer {L J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (L : Set G)) : ⁅L, J⁆ ≤ L := by
  refine Subgroup.commutator_le.2 fun l hl j hj => ?_
  have h1 : j * l⁻¹ * j⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hJ hj) l⁻¹).1 (L.inv_mem hl)
  have h2 : ⁅l, j⁆ = l * (j * l⁻¹ * j⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact L.mul_mem hl h1

theorem isTwoReducedIn_VZ {X T : Subgroup G} (hX : CharTwo X) (hT : IsSylowTwoOf T X) :
    IsTwoReducedIn X (VZ T X) :=
  isTwoReducedIn_conjClosure_of_sylowIn hT.1 hT.2.1 hT.2.2 hX le_rfl

@[expose] def chiBlocksOutside (X T M : Subgroup G) : Set (Subgroup G) :=
  {L | IsChiBlock X L ∧ ⁅L, thompsonJ T⁆ = L ∧ ¬ L ≤ M}

theorem le_of_isExceptionalA7Block {C₁ C₂ : Subgroup G → Subgroup G}
    (h123 : C123TwoStatement C₁ C₂)
    {X T L M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hL : IsBlock2 X L) (hexc : IsExcA7Block L) : L ≤ M := by
  have hTN : T ≤ Subgroup.normalizer (L : Set G) :=
    hT.1.trans (le_normalizer_of_exceptionalA7 hSQ h38 hL hexc)
  have hLX : L ≤ X := hL.2.1
  have hYX : L ⊔ T ≤ X := sup_le hLX hT.1
  have hTY : T ≤ L ⊔ T := le_sup_right
  have hnorm : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTN)
  have hsub : IsSubnormal L (L ⊔ T) := A3.subnormal_of_normal le_sup_left hnorm
  have hLc : L ∈ cComp (L ⊔ T) :=
    mem_cComp_of_short hL.1 (isQuasisimple_of_isExceptionalA7Block hexc) hsub
  have hprod : ∀ y ∈ L ⊔ T, ∃ l ∈ L, ∃ r ∈ T, y = l * r := by
    intro y hy
    have hy' : y ∈ ((L ⊔ T : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTN] at hy'
    obtain ⟨l, hl, r, hr, hlr⟩ := hy'
    exact ⟨l, hl, r, hr, hlr.symm⟩
  have hY := h123 T T (L ⊔ T) L hT.2.1 (baum_le T) le_rfl (isSylowTwoOf_of_le hT hTY hYX)
    (charTwo_of_le hX hT hTY hYX) hLc hprod hexc
  calc L ≤ L ⊔ T := le_sup_left
    _ = ((L ⊔ T) ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔
        ((L ⊔ T) ⊓ Subgroup.normalizer (C₂ T : Set G)) := hY
    _ ≤ M := sup_le ((inf_le_inf_right _ hYX).trans (le_sup_left.trans hM))
        ((inf_le_inf_right _ hYX).trans (le_sup_right.trans hM))

theorem exists_chiBlock_of_chi0Block {C₁ C₂ : Subgroup G → Subgroup G}
    (h127 : C127Statement (G := G)) (h123 : C123TwoStatement C₁ C₂)
    (h116 : BaumNormalizesChiBlocksStatement (G := G)) (hB42 : AltBlockStatement (G := G))
    {X T U K M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hU : U ∈ uFamHat X T) (hK : IsChi0Block U K) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hUK : U = T ⊔ conjClosure K T) (hKM : ¬ K ≤ M) :
    ∃ L : Subgroup G, IsChiBlock X L ∧ ⁅L, thompsonJ T⁆ = L ∧ K ≤ L ∧ ¬ L ≤ M := by
  obtain ⟨L, hLblock, hKL, -, hULV, hcases⟩ := h127 X T U K hX hT hSQ.1 hU hK.1 hKJ hUK
  rcases hcases with hKL' | ⟨m, n, hm, hn, hm3, hn3, hmL, hnK⟩
  · subst hKL'
    exact ⟨K, isChiBlock_of_isChi0Block hLblock hK, hKJ, le_rfl, hKM⟩
  · have hnotKC : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G) := not_le_of_isAltQuotient hnK hn3
    have hKLJ : K ≤ ⁅L, thompsonJ T⁆ :=
      calc K = ⁅K, thompsonJ T⁆ := hKJ.symm
        _ ≤ ⁅L, thompsonJ T⁆ := Subgroup.commutator_mono hKL le_rfl
    have hnotLJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) := fun h =>
      hnotKC (hKLJ.trans h)
    have hLchi : IsChiBlock X L := by
      rcases hB42 X T L hX hSQ hT hLblock hULV hnotLJ ⟨m, hm, hmL⟩ with h | hexc
      · exact h
      · exact absurd (hKL.trans (le_of_isExceptionalA7Block h123 hX hSQ h38 hT hM hLblock hexc))
          hKM
    have hbaum : baum T ≤ Subgroup.normalizer (L : Set G) :=
      h116 X T (VZ T X) L hX (isTwoReducedIn_VZ hX hT) hT hLchi hnotLJ
    have hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G) := (thompsonJ_le_baum T).trans hbaum
    have hNL : ⁅L, thompsonJ T⁆ ≤ L := commutator_le_of_le_normalizer hJN
    have hLN : L ≤ Subgroup.normalizer ((⁅L, thompsonJ T⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left L (thompsonJ T)
    have hEq : ⁅L, thompsonJ T⁆ = L :=
      isShort2_eq_of_isAltQuotient hLblock.1 hm hm3 hmL hNL hLN hnotLJ
    exact ⟨L, hLchi, hEq, hKL, fun hLM => hKM (hKL.trans hLM)⟩

theorem uFamHat_le_sup_chiBlocks {C₁ C₂ : Subgroup G → Subgroup G}
    (h126 : C126Statement C₁ C₂) (h127 : C127Statement (G := G)) (h123 : C123TwoStatement C₁ C₂)
    (h116 : BaumNormalizesChiBlocksStatement (G := G)) (hB42 : AltBlockStatement (G := G))
    {X T M U : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hTM : T ≤ M) (hU : U ∈ uFamHat X T) :
    U ≤ M ⊔ ⨆ L ∈ chiBlocksOutside X T M, L := by
  by_cases hUM : U ≤ M
  · exact hUM.trans le_sup_left
  have hUX : U ≤ X := hU.1.1
  have hTU : T < U := hU.1.2.1
  have hTSyl : IsSylowTwoOf T U := isSylowTwoOf_of_le hT hTU.le hUX
  have hUmin : IsMinParabolicOf U U := ⟨T, hTSyl, ⟨le_rfl, hTU, hU.1.2.2⟩, hU.2⟩
  have hUchar : CharTwo U := charTwo_of_le hX hT hTU.le hUX
  rcases h126 U T (IsSQTKTC.mono hUX hSQ) hTSyl hUchar hUmin with
    h1 | h2 | ⟨r, K, hr, hK, -, hres, hperm, htrans⟩
  · exfalso
    apply hUM
    have hUC : U ≤ X ⊓ Subgroup.centralizer (C₁ T : Set G) :=
      le_inf hUX fun u hu => Subgroup.mem_centralizer_iff.2 fun c hc =>
        (Subgroup.mem_centralizer_iff.1 (h1 hc).2 u hu).symm
    exact (hUC.trans le_sup_left).trans hM
  · exfalso
    apply hUM
    exact ((le_inf hUX h2).trans le_sup_right).trans hM
  · have hUeq : U = T ⊔ twoResidual U := (sup_twoResidual_eq hTSyl).symm
    have hex : ∃ i₀, ¬ K i₀ ≤ M := by
      by_contra hall
      push Not at hall
      apply hUM
      calc U = T ⊔ twoResidual U := hUeq
        _ = T ⊔ ⨆ i, K i := by rw [hres]
        _ ≤ M := sup_le hTM (iSup_le hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hall : ∀ i, ¬ K i ≤ M := by
      intro i hi
      obtain ⟨t, ht, hconj⟩ := htrans i i₀
      exact hi₀ (hconj ▸ conjSub_le_of_mem (hTM ht) hi)
    have hKle : ∀ i, K i ≤ ⨆ L ∈ chiBlocksOutside X T M, L := by
      intro i
      have hUK : U = T ⊔ conjClosure (K i) T := by
        rw [conjClosure_eq_iSup K hperm htrans i, ← hres]; exact hUeq
      obtain ⟨L, hL, hLJ, hKL, hLM⟩ := exists_chiBlock_of_chi0Block h127 h123 h116 hB42 hX hSQ h38
        hT hM hU (hK i).1 (hK i).2 hUK (hall i)
      exact hKL.trans (le_iSup₂_of_le L ⟨hL, hLJ, hLM⟩ le_rfl)
    calc U = T ⊔ twoResidual U := hUeq
      _ = T ⊔ ⨆ i, K i := by rw [hres]
      _ ≤ M ⊔ ⨆ L ∈ chiBlocksOutside X T M, L :=
        sup_le (hTM.trans le_sup_left) (le_sup_of_le_right (iSup_le hKle))

theorem lemma_C128_of_le {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (h126 : C126Statement C₁ C₂) (h127 : C127Statement (G := G)) (h123 : C123TwoStatement C₁ C₂)
    (h19 : DistinctBlocksCommuteStatement (G := G))
    (h116 : BaumNormalizesChiBlocksStatement (G := G)) (hB42 : AltBlockStatement (G := G))
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hT0 : T ≠ ⊥)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hMX : M ≤ X) :
    X = M ∨ ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
      (∀ i, IsChiBlock X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M) ∧ X = M ⊔ ⨆ i, L i := by
  classical
  obtain ⟨-, -, -, -, hC₂B, hC₂char, -⟩ := hC.pair T hT.2.1 hT0
  have hNC₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ T : Set G) :=
    (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂B hC₂char)
  have hTM : T ≤ M := fun t ht =>
    hM (Subgroup.mem_sup_right ⟨hT.1 ht, hNC₂ (Subgroup.le_normalizer ht)⟩)
  have hNTM : X ⊓ Subgroup.normalizer (T : Set G) ≤ M := fun x hx =>
    hM (Subgroup.mem_sup_right ⟨hx.1, hNC₂ hx.2⟩)
  have hXle : X ≤ M ⊔ ⨆ L ∈ chiBlocksOutside X T M, L := by
    obtain ⟨-, -, hXeq⟩ := uHat_normal_and_eq_sup hT.1
    calc X = uHat X T ⊔ (X ⊓ Subgroup.normalizer (T : Set G)) := hXeq
      _ ≤ M ⊔ ⨆ L ∈ chiBlocksOutside X T M, L := by
        refine sup_le (iSup₂_le fun U hU => ?_) (hNTM.trans le_sup_left)
        exact uFamHat_le_sup_chiBlocks h126 h127 h123 h116 hB42 hX hSQ h38 hT hM hTM hU
  have hBX : ∀ L ∈ chiBlocksOutside X T M, L ≤ X := fun L hL => hL.1.1.2.1
  have htwo : ∀ A ∈ chiBlocksOutside X T M, ∀ B ∈ chiBlocksOutside X T M,
      ∀ C ∈ chiBlocksOutside X T M, A = B ∨ A = C ∨ B = C := by
    intro A hA B hB C hC'
    by_contra hcon
    push Not at hcon
    obtain ⟨hAB, hAC, hBC⟩ := hcon
    exact three_blocks_false hSQ (hBX A hA) (hBX B hB) (hBX C hC')
      ⟨hA.1.1.1.2.1, hB.1.1.1.2.1, hC'.1.1.1.2.1⟩
      ⟨three_dvd_card_of_isChiBlock hA.1, three_dvd_card_of_isChiBlock hB.1,
        three_dvd_card_of_isChiBlock hC'.1⟩ hAB hAC hBC
      ⟨h19 X A B hX hA.1.1 hB.1.1 hAB, h19 X A C hX hA.1.1 hC'.1.1 hAC,
        h19 X B C hX hB.1.1 hC'.1.1 hBC⟩
  by_cases hne : ∃ A, A ∈ chiBlocksOutside X T M
  · right
    obtain ⟨A, hA⟩ := hne
    by_cases hB : ∃ B ∈ chiBlocksOutside X T M, B ≠ A
    · obtain ⟨B, hB, hBA⟩ := hB
      have hall : ∀ C ∈ chiBlocksOutside X T M, C = A ∨ C = B := fun C hC' => by
        rcases htwo A hA B hB C hC' with h | h | h
        · exact absurd h.symm hBA
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      refine ⟨2, ![A, B], by norm_num, le_rfl, ?_, ?_⟩
      · intro i
        fin_cases i
        · exact hA
        · exact hB
      · refine le_antisymm (hXle.trans (sup_le_sup_left ?_ M)) ?_
        · refine iSup₂_le fun C hC' => ?_
          rcases hall C hC' with h | h
          · rw [h]
            exact le_iSup (fun i => (![A, B] : Fin 2 → Subgroup G) i) 0
          · rw [h]
            exact le_iSup (fun i => (![A, B] : Fin 2 → Subgroup G) i) 1
        · refine sup_le hMX (iSup_le fun i => ?_)
          fin_cases i
          · exact hBX A hA
          · exact hBX B hB
    · push Not at hB
      refine ⟨1, fun _ => A, le_rfl, by norm_num, fun _ => hA, ?_⟩
      refine le_antisymm (hXle.trans (sup_le_sup_left ?_ M)) ?_
      · refine iSup₂_le fun C hC' => ?_
        rw [hB C hC']
        exact le_iSup (fun _ : Fin 1 => A) 0
      · exact sup_le hMX (iSup_le fun _ => hBX A hA)
  · left
    refine le_antisymm (hXle.trans (sup_le le_rfl (iSup₂_le fun L hL => absurd ⟨L, hL⟩ hne))) ?_
    exact hMX

theorem lemma_C128 {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (h126 : C126Statement C₁ C₂) (h127 : C127Statement (G := G)) (h123 : C123TwoStatement C₁ C₂)
    (h19 : DistinctBlocksCommuteStatement (G := G))
    (h116 : BaumNormalizesChiBlocksStatement (G := G)) (hB42 : AltBlockStatement (G := G))
    {X T : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hT0 : T ≠ ⊥) :
    X = (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ∨
      ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
        (∀ i, IsChiBlock X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i) ∧
        X = ((X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔
          (X ⊓ Subgroup.normalizer (C₂ T : Set G))) ⊔ ⨆ i, L i := by
  rcases lemma_C128_of_le (M := (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔
      (X ⊓ Subgroup.normalizer (C₂ T : Set G))) hC h126 h127 h123 h19 h116 hB42 hX hSQ h38 hT hT0
    le_rfl (sup_le inf_le_left inf_le_left) with h | ⟨s, L, hs1, hs2, hL, hXL⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, L, hs1, hs2, fun i => ⟨(hL i).1, (hL i).2.1⟩, hXL⟩

end C1GN

end CFSG.Quasithin
