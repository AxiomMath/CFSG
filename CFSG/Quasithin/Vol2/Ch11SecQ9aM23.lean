module

public import CFSG.Quasithin.Vol2.Ch11SecA12B
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.RankThree.Asc83Table.M23

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecA

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem not_isPSU35_of_M23 {Y : Type} [Group Y] (hM : IsSporadic .M23 Y) :
    ¬ IsPSLEps3 false 5 1 Y := by
  intro hU
  have h1 := (CFSG.RankThree.Classical.unitary_three_five_model Y hU).1
  obtain ⟨e⟩ := hM
  have h2 : Nat.card Y = 10200960 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.Asc83Table.M23.card_M23
  omega

theorem false_of_M23 (hL3 : FactList3Table) (hF : Facts12) (hC : CartanFacts) (hF11 : Facts11)
    (hN : NatFacts) (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K) (hM : IsSporadic .M23 (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  obtain ⟨hQ, hZ, hrk, hPSL⟩ := hL3.1 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM)))))
  have hKC := le_centralizer_of_cComp hF11 hN h1102 h hV₁ hK hLK
  have hX1V := xOne_le_normalizer_V1 hN h1102 h hV₁ hX
  have hX1K : xOne X (LOf L V₁) ≤ Subgroup.normalizer (K : Set G) := hX1V.trans hNK
  have hX1card := card_xOne hC hF hN h1102 h hV₁ hV₂ hX
  have hX1K' : xOne X (LOf L V₁) ⊓ K = ⊥ := by
    rw [eq_bot_iff, ← xOne_inf_centralizer hC hF hN h1102 h hV₁ hV₂ hX]
    exact inf_le_inf_left _ hKC
  have hd3 : (3 : ℕ) ∣ 2 ^ 2 - 1 := by norm_num
  obtain ⟨x, hxX, hx1, hxo⟩ := exists_orderOf_eq_of_dvd Nat.prime_three hX1card hd3
  set H := K ⊔ xOne X (LOf L V₁) with hH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hX1K)
  have hsup : K.subgroupOf H ⊔ (xOne X (LOf L V₁)).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _
  have hA3 : Nat.card ↥((xOne X (LOf L V₁)).subgroupOf H) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, hX1card]
    norm_num
  have hA : IsPGroup 3 ↥((xOne X (LOf L V₁)).subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by rw [hA3, pow_one])
  have hAK : (xOne X (LOf L V₁)).subgroupOf H ⊓ K.subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    have hy : (y : G) ∈ xOne X (LOf L V₁) ⊓ K := ⟨hy1, hy2⟩
    rw [hX1K', Subgroup.mem_bot] at hy
    exact (Subgroup.mem_bot).mpr (Subtype.ext hy)
  obtain ⟨e⟩ := quotPCore_subgroupOf_equiv (L := K) (le_sup_left : K ≤ H)
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  have hZ' : Nat.card (Subgroup.center (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)))
      ∣ 3 := by
    rw [← Subgroup.map_center_eq e.symm, Subgroup.card_map_of_injective e.symm.injective]
    exact hZ
  have h9' : 9 ∣ Nat.card (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)) := by
    rw [Nat.card_congr e.toEquiv]
    exact nine_dvd_card_of_pRank hrk
  have h3' := (show (3 : ℕ) ∣ 9 by norm_num).trans h9'
  obtain ⟨hO, -⟩ := pPrimeCore_three_eq hsup hA hQ' hZ' h3'
  have hOK := pPrimeCore_le_of_sup hsup hA
  rcases a318_sup h318 h36 h38 h hV₁ hK hX1V hQ Nat.prime_three (by norm_num) hrk with
    h1 | ⟨-, h2⟩ | ⟨-, -, h3a | h3b⟩
  · refine not_mem_subgroupOf_of_inf hX1K' hxX hx1 ?_
    rw [h1]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1,
      by rw [pow_one, Subgroup.orderOf_mk, hxo]⟩
  · obtain ⟨s, q, -, ⟨p, f, hp, hf, rfl, hS⟩, -⟩ := h2
    obtain ⟨φ⟩ := starImage_mulEquiv hO
    have hS' := IsPSLEps3.of_mulEquiv (φ.trans e) hS
    obtain ⟨rfl, rfl, rfl⟩ := hPSL s p f hp hf hS'
    exact not_isPSU35_of_M23 hM hS'
  · refine not_mem_subgroupOf_of_inf hX1K' hxX hx1 ?_
    rw [h3a]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, by rw [Subgroup.orderOf_mk, hxo]⟩
  · set D := (LOf L V₁ ⊓ Subgroup.centralizer (xOne X (LOf L V₁) : Set G)).subgroupOf H
      with hD
    have hDK : D ≤ K.subgroupOf H := fun d hd =>
      Subgroup.mem_subgroupOf.mpr (hLK (Subgroup.mem_subgroupOf.mp hd).1)
    have hDA : D ≤ Subgroup.centralizer (((xOne X (LOf L V₁)).subgroupOf H : Subgroup ↥H) :
        Set ↥H) := fun d hd => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hd).2 a ha)
    have hc := commutator_le_of_case3b hOK hA3 hAK hDK hDA h3b
    have hDD2 : IsPGroup 2 ↥⁅D, D⁆ := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (CFSG.pCore_isPGroup.map (K.subgroupOf H).subtype).to_le (hO ▸ hc)
    have hle : LOf L V₁ ⊓ Subgroup.centralizer (xOne X (LOf L V₁) : Set G) ≤ H :=
      inf_le_left.trans (hLK.trans le_sup_left)
    have hmap : (⁅D, D⁆).map H.subtype =
        ⁅LOf L V₁ ⊓ Subgroup.centralizer (xOne X (LOf L V₁) : Set G),
          LOf L V₁ ⊓ Subgroup.centralizer (xOne X (LOf L V₁) : Set G)⁆ := by
      rw [Subgroup.map_commutator, hD, Subgroup.map_subgroupOf_eq_of_le hle]
    have e' : ↥⁅D, D⁆ ≃* ↥((⁅D, D⁆).map H.subtype) :=
      Subgroup.equivMapOfInjective _ _ H.subtype_injective
    rw [hmap] at e'
    exact false_of_isPGroup_commutator hN h1102 h hV₁
      (IsPGroup.of_card (n := 1) (by rw [hX1card]; norm_num)) inf_le_right (hDD2.of_equiv e')

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
