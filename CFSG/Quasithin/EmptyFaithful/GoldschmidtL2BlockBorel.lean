module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockWreath
public import CFSG.Quasithin.EmptyFaithful.S151S4B

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem borel_of_cComp_mod (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hLcomp : L ∈ cComp (g1_1516 Z₁)) (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsBorelIn L (mZ1516 Mc Z₁ ⊓ L) := by
  have h18 := hc.h18
  have h19 := hc.h19
  have hS4 : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := h18.four
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516 h18
  have hLG : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hP : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow h18.four hc.hL
  have hOG : ∀ H : Subgroup G, s1516 T Z₁ ⊓ L ≤ H → H ≤ L → H ≠ L →
      H ≤ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) :=
    fun H hPH hHL hH => le_normalizer_of_overgroup hP hB hPH hHL hH
  have hN : mZ1516 Mc Z₁ ⊓ L ≤ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) :=
    inf_le_normalizer hSM hP inf_le_left hOG hc.hL.not_le
  have hpc : pCoreOf 2 (mZ1516 Mc Z₁ ⊓ L) = s1516 T Z₁ ⊓ L := pCoreOf_inf_eq hSM hP inf_le_left hN
  have hsqtk : IsSQTKIn (g1_1516 Z₁) := h18.five.2.2.sqtk
  obtain ⟨horb, hcase⟩ :=
    a3Orbits_of_a37_a38 h37 h38 (g1_1516 Z₁) (s1516 T Z₁) L hsqtk hS4 hLcomp
  have hstar : ∀ m ∈ mZ1516 Mc Z₁, ∃ s ∈ s1516 T Z₁, conjByElt m L = conjByElt s L :=
    fun m hm => exists_conj_eq_of_orbits horb (mZ1516_le_g1 Mc Z₁ hm)
  have hK := normalizes_conjClosure hSM hstar
    (fun n hn hnL => (normalizer_stable hpc hn hnL).2)
  have hcase' : (∀ t ∈ s1516 T Z₁, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ s1516 T Z₁, t ∉ Subgroup.normalizer (L : Set G) ∧
        conjSubgroupsBy (s1516 T Z₁) L = {L, conjByElt t L} ∧
        ⁅L, conjByElt t L⁆ ≤ pCoreOf 2 (g1_1516 Z₁) ∧
        (L ⊔ pCoreOf 2 (g1_1516 Z₁)) ⊓ (conjByElt t L ⊔ pCoreOf 2 (g1_1516 Z₁)) =
          pCoreOf 2 (g1_1516 Z₁) := by
    rcases hcase with h | ⟨t, ht, htN, hconj, hcom, hint0, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, htN, hconj, hcom, hint0⟩
  obtain ⟨K, Q, hKe, hKc⟩ := exists_carrier_conjClosure_mod (X := g1_1516 Z₁) (S := s1516 T Z₁)
    hLG (s1516_le_g1 T Z₁) hP rfl hB horb hcase'
  have hKG : K ≤ g1_1516 Z₁ := by
    rw [← hKe]
    refine conjClosure_le fun s hs b hb => ?_
    have hsG := s1516_le_g1 T Z₁ hs
    exact (g1_1516 Z₁).mul_mem ((g1_1516 Z₁).mul_mem hsG (hLG hb.1)) ((g1_1516 Z₁).inv_mem hsG)
  obtain ⟨hchar, hodd⟩ := hKc.charTwo_odd
  rw [hKe] at hK
  have hKM : K ≤ mZ1516 Mc Z₁ := h19.two K hKG hodd hK hchar
  have hBK : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ K := by
    rw [← hKe]
    exact le_conjClosure _ _
  exact ⟨s1516 T Z₁ ⊓ L, hP, le_antisymm (fun x hx => ⟨hx.2, hN hx⟩)
    (fun x hx => ⟨hKM (hBK hx), hx.1⟩)⟩

omit [Finite G] in
theorem isBorelOfBlock_of_isBorelIn {L B : Subgroup G} (h : IsBorelIn L B)
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ 3) : IsBorelOfBlock L B := by
  unfold IsBorelOfBlock
  split_ifs with h3
  · exact absurd h3 hcard
  · obtain ⟨S', hS', rfl⟩ := h
    exact ⟨S', hS', sup_eq_left.mpr (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      (hS'.pCoreOf_le.trans Subgroup.le_normalizer))⟩

theorem center_eq_bot_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨K, hF, hfin, hchar, hcard, ⟨e⟩⟩ := S151S4.exists_equiv_sl2 h
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [S151S4.center_sl2_eq_bot K, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using h1)

theorem card_ne_three_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Nat.card X ≠ 3 := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic X := isCyclic_of_prime_card h3
  have hcomm : ∀ a b : X, a * b = b * a := isMulCommutative_iff.1 hcyc.isMulCommutative
  have hc : Subgroup.center X = ⊥ := center_eq_bot_of_isPSL h
  have htop : Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.mpr fun g => hcomm g x
  rw [hc] at htop
  have : Nat.card X = 1 := by
    rw [← Subgroup.card_top (G := X), ← htop, Subgroup.card_bot]
  omega

theorem isBorelOfBlock_of_cComp (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hLcomp : L ∈ cComp (g1_1516 Z₁)) (hA : ListA15120 L) :
    IsBorelOfBlock L (mZ1516 Mc Z₁ ⊓ L) := by
  obtain ⟨n, hn, h⟩ := hA
  exact isBorelOfBlock_of_isBorelIn
    (borel_of_cComp_mod h37 h38 hc hLcomp (A5.C25.fusionIsBenderGroup_of_isPSL h))
    (card_ne_three_of_isPSL h)

end CFSG.Quasithin.GoldMLA
