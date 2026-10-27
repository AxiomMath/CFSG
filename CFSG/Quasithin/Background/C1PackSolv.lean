module

public import CFSG.Quasithin.Background.C1PackC126Solv
public import CFSG.Quasithin.Background.C1PackC127Solv
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj
public import CFSG.Quasithin.EmptyFaithful.S14111Alt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C1Pack

variable {G : Type} [Group G] [Finite G]

theorem uFamHat_le_sup_chiBlocks_solv_Solv {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T M U : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X) (hT : IsSylowTwoOf T X)
    (hsolv : perfectCore X ≤ Subgroup.centralizer (VZ T X : Set G))
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hTM : T ≤ M) (hU : U ∈ uFamHat X T) :
    U ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
  by_cases hUM : U ≤ M
  · exact hUM.trans le_sup_left
  have hUX : U ≤ X := hU.1.1
  have hTU : T < U := hU.1.2.1
  obtain ⟨K, hK, hKalt, hKJ, hUK, hKM⟩ :=
    exists_a3Block_of_not_le hC hX hSQ hT hsolv hU hM hTM hUM
  have hT0 : T ≠ ⊥ := by
    intro h0
    apply hU.2
    rw [h0]
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  obtain ⟨-, h1Z, -, -, -, -, -⟩ := hC.pair T hT.2.1 hT0
  have hC1V : C₁ T ≤ VZ T X := h1Z.trans (le_conjClosure _ X)
  have hKV : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G) := by
    intro hle
    apply hKM
    have hKX : K ≤ X := hK.1.2.1.trans hUX
    have hKC : K ≤ X ⊓ Subgroup.centralizer (C₁ T : Set G) :=
      le_inf hKX (hle.trans (Subgroup.centralizer_le hC1V))
    exact (hKC.trans le_sup_left).trans hM
  obtain ⟨hKbX, -⟩ := isBlock2_of_a3Block hX hT hsolv hUX hTU.le hK.1 hKalt hKJ hKV
  have hKchi : IsChiBlock X K := ⟨hKbX, Or.inr ⟨3, by decide, le_rfl, hKalt⟩⟩
  have hKmem : K ∈ C1GN.chiBlocksOutside X T M := ⟨hKchi, hKJ, hKM⟩
  have hconj : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ∈ C1GN.chiBlocksOutside X T M :=
    fun t ht => L238.mem_chiBlocksOutside_conj hT.1 hTM hKmem ht
  have hconjle : conjClosure K T ≤ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L :=
    conjClosure_le fun t ht z hz =>
      (le_iSup₂_of_le (f := fun (L : Subgroup G) (_ : L ∈ C1GN.chiBlocksOutside X T M) => L)
        (K.map (MulAut.conj t).toMonoidHom) (hconj t ht) le_rfl) ⟨z, hz, rfl⟩
  calc U = T ⊔ conjClosure K T := hUK
    _ ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L :=
      sup_le (hTM.trans le_sup_left) (hconjle.trans le_sup_right)

theorem lemma_C128_solv_of_le_Solv {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X) (hT : IsSylowTwoOf T X)
    (hT0 : T ≠ ⊥) (hsolv : perfectCore X ≤ Subgroup.centralizer (VZ T X : Set G))
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
  have hXle : X ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
    obtain ⟨-, -, hXeq⟩ := uHat_normal_and_eq_sup hT.1
    calc X = uHat X T ⊔ (X ⊓ Subgroup.normalizer (T : Set G)) := hXeq
      _ ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
        refine sup_le (iSup₂_le fun U hU => ?_) (hNTM.trans le_sup_left)
        exact uFamHat_le_sup_chiBlocks_solv_Solv hC hX hSQ hT hsolv hM hTM hU
  have hBX : ∀ L ∈ C1GN.chiBlocksOutside X T M, L ≤ X := fun L hL => hL.1.1.2.1
  have htwo : ∀ A ∈ C1GN.chiBlocksOutside X T M, ∀ B ∈ C1GN.chiBlocksOutside X T M,
      ∀ C ∈ C1GN.chiBlocksOutside X T M, A = B ∨ A = C ∨ B = C := by
    intro A hA B hB C hC'
    by_contra hcon
    push Not at hcon
    obtain ⟨hAB, hAC, hBC⟩ := hcon
    exact C1GN.three_blocks_false hSQ (hBX A hA) (hBX B hB) (hBX C hC')
      ⟨hA.1.1.1.2.1, hB.1.1.1.2.1, hC'.1.1.1.2.1⟩
      ⟨C1GN.three_dvd_card_of_isChiBlock hA.1, C1GN.three_dvd_card_of_isChiBlock hB.1,
        C1GN.three_dvd_card_of_isChiBlock hC'.1⟩ hAB hAC hBC
      ⟨distinctBlocksCommuteStatement X A B hX hA.1.1 hB.1.1 hAB,
        distinctBlocksCommuteStatement X A C hX hA.1.1 hC'.1.1 hAC,
        distinctBlocksCommuteStatement X B C hX hB.1.1 hC'.1.1 hBC⟩
  by_cases hne : ∃ A, A ∈ C1GN.chiBlocksOutside X T M
  · right
    obtain ⟨A, hA⟩ := hne
    by_cases hB : ∃ B ∈ C1GN.chiBlocksOutside X T M, B ≠ A
    · obtain ⟨B, hB, hBA⟩ := hB
      have hall : ∀ C ∈ C1GN.chiBlocksOutside X T M, C = A ∨ C = B := fun C hC' => by
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

theorem lemma_C128_solv_Solv {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKTC X) (hT : IsSylowTwoOf T X)
    (hT0 : T ≠ ⊥) (hsolv : perfectCore X ≤ Subgroup.centralizer (VZ T X : Set G)) :
    X = (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ∨
      ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
        (∀ i, IsChiBlock X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i) ∧
        X = ((X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔
          (X ⊓ Subgroup.normalizer (C₂ T : Set G))) ⊔ ⨆ i, L i := by
  rcases lemma_C128_solv_of_le_Solv (M := (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔
      (X ⊓ Subgroup.normalizer (C₂ T : Set G))) hC hX hSQ hT hT0 hsolv
    le_rfl (sup_le inf_le_left inf_le_left) with h | ⟨s, L, hs1, hs2, hL, hXL⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, L, hs1, hs2, fun i => ⟨(hL i).1, (hL i).2.1⟩, hXL⟩

end C1Pack

theorem gNCampbellC128Solv_of_Solv (h118 : TheoremC118) : GNCampbellC128Solv := by
  intro G _ _ T hsimple hqtke hsyl hT0
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair T hsyl.1 hT0
  refine ⟨C₁ T, C₂ T, h1ne, h1Z, h1char, h2ne, h2B, h2char, fun M hM hsolv => ?_⟩
  obtain ⟨hMchar, hMsq, hSylM⟩ := inM_facts hsimple hqtke hsyl hM
  exact C1Pack.lemma_C128_solv_Solv hC hMchar hMsq hSylM hT0 hsolv

end CFSG.Quasithin
