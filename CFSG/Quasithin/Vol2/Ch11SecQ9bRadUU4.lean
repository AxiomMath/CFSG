module

public import CFSG.Quasithin.Vol2.Ch11SecOE6G
public import CFSG.Quasithin.Vol2.Ch11SecQ9bI2b
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUU2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem false_of_case_b_U (hFb : Facts12b) (hFc : Facts12c) (hC : CartanFacts) (hN : NatFacts)
    (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂)
    (hX : IsCartanX T L X) {U : Subgroup G}
    (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂)
    (hLU : L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₂ ≤ K)
    (hA7 : IsAlt 7 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsHat (↥K ⧸ CFSG.pCore 2 ↥K) (alternatingGroup (Fin 7)))
    (hZc : ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
      (y : G) ∈ Subgroup.centralizer (U : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX2card := card_xTwo hC hN h1102 h hV₁ hV₂ hX
  obtain ⟨x, hxX, hx1, hxo⟩ := exists_orderOf_eq_of_dvd Nat.prime_three hX2card (by norm_num)
  have hUV' : U ≤ fsuV T I := (le_V2_of_sup_eq hUV).trans (IsVi.le_fsuV hV₂)
  have hX2V : xOne X (LOf L V₂) ≤ Subgroup.normalizer (U : Set G) := fun x hx =>
    hLU ⟨(hX.1 hx.1).1, cartan_le_normalizer_Vi hN h1102 h (Or.inr rfl) hV₂ hX hx.1⟩
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
    rcases a318_sup_W h318 h36 h38 h hUV' (ne_bot_of_sup_eq h hV₂ hUV) hK hX2V hQ
        Nat.prime_three (by norm_num) hrk with h1 | ⟨-, h2⟩ | ⟨-, -, h3a | h3b⟩
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
  have hxC₂ : x ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [← hUV]
    exact mem_centralizer_sup hxC (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 x (hX.1 hxX.1).1).symm)
  have hbot : x ∈ X ⊓ Subgroup.centralizer (V₂ : Set G) := ⟨hxX.1, hxC₂⟩
  rw [cartan_inf_centralizer_V2 hFc h1102 h hV₂ hX, Subgroup.mem_bot] at hbot
  exact hx1 hbot

theorem lOf_le_normalizer_xi_gen (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h : Hyp11 G T L I 2) {V₀ K₁ Y B : Subgroup G}
    (hH₁ : pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) ≠ ⊥)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (V₀ : Set G)))
    (hNK₁ : Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hL₁K₁ : B ≤ K₁)
    (hdesc : IsPSL 3 2 2 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ¬ CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hXi : IsXi T Y) (hYH : Y ⊔ T ≤ Subgroup.normalizer (V₀ : Set G))
    (hY5 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card Y → 5 ≤ q) :
    B ≤ Subgroup.normalizer (Y : Set G) := by
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  exact hL₁K₁.trans
    (OE6.cComp_le_normalizer_xi h36c hloc h.fsu.sylow hH₁ hK₁ hNK₁ hdesc hXi hYH hY5)

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
