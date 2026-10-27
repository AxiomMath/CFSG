module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5d
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.Vol2.Ch12Sec7Orb
public import CFSG.Quasithin.Vol2.Ch12Sec7L5c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127

@[expose] def Lemma12_7_5K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Hyp1271 G T L V → t ∈ V →
    (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    HypC28 (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
      (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({t} : Set G)) →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) ≤ K →
      ¬ K ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) →
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer (K : Set G) →
      C48KDescribed (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G))
        (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V K →
      IsComponentOf (conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
          (Subgroup.centralizer ({t} : Set G))) (Subgroup.centralizer ({t} : Set G)) ∧
        (Subgroup.center ↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
            (Subgroup.centralizer ({t} : Set G)))).map
          (conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
            (Subgroup.centralizer ({t} : Set G))).subtype = Vt L t ∧
        IsPSL 3 2 2
          (↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
              (Subgroup.centralizer ({t} : Set G))) ⧸
            Subgroup.center ↥(conjClosure (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)))
              (Subgroup.centralizer ({t} : Set G))))

namespace S127.L5

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t : G}

theorem D127.exists_K (d : D127 G T L V t) (h12212 : Stmt12_2_12) (h48 : ASC48Statement G)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)))
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({t} : Set G)) ∧
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ Lt L t ≤ K ∧
      ¬ K ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ∧
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer (K : Set G) ∧
      C48KDescribed (Subgroup.centralizer ({t} : Set G)) (pCoreOf 2 (L ⊔ T))
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) (Lt L t) V K ∧
      t ∈ centerOf K := by
  have hC := d.hypC28 h12212 hTV hsyl
  have hlt : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) <
      Subgroup.centralizer ({t} : Set G) :=
    lt_of_le_not_ge inf_le_right fun hle => hnot (hle.trans inf_le_left)
  obtain ⟨hM0, K, hK, hKq, hLK, hcase⟩ := h48 _ _ _ _ _ hC hlt
  rcases hcase with h10 | ⟨-, hKM, hMK, hdesc⟩
  · exfalso
    obtain ⟨-, -, hMeq, h2⟩ := h10
    rw [← hM0] at hMeq
    exact hnot ((le_of_relIndex_eq_two inf_le_right d.theta hMeq h2).trans inf_le_left)
  refine ⟨K, hK, hKq, hLK, hKM, hMK, hdesc, ?_⟩
  exact mem_centerOf (le_of_mem_cComp hK) (hLK (d.v_le_lt d.mem))

end S127.L5

open S127.L5 in
theorem lemma12_7_5_of (h71 : Setup1271) (h74 : Lemma12_7_4) (h1222 : Stmt12_2_2)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12)
    (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (hK : Lemma12_7_5K) :
    Lemma12_7_5 := by
  intro G _ _ T L V h t ht h18
  by_cases hle : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)
  · exact Or.inl hle
  right
  obtain ⟨-, -, hTV⟩ := card_eq_of_1222 h1222 h
  have ht1 := (d127_of h71 h74 h ht h18).ne_one
  obtain ⟨k, hk, hsyl⟩ := exists_mem_isSylowTwoOf h1225 h74 h hTV ht ht1 h18
  have h' := hyp1271_conj h hTV hk
  have hTV' : CFSG.conjugate T k⁻¹ ≤ Subgroup.normalizer (V : Set G) :=
    L14328.conjugate_le_normalizer (le_normalizer_V h hk) hTV
  have d := d127_of h71 h74 h' ht h18
  obtain ⟨K, hKc, hKq, hLK, hKM, hMK, hdesc, -⟩ := d.exists_K h12212 (h48 G) hTV' hsyl hle
  exact hK G _ L V t h' ht h18 (d.hypC28 h12212 hTV' hsyl) K hKc hKq hLK hKM hMK hdesc

end CFSG.Quasithin.H13
