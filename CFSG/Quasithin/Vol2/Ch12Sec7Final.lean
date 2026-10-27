module

public import CFSG.Quasithin.Vol2.Ch12Sec7Lemmas

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

namespace S127

structure Setting1274 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G) : Prop
    extends Setting1273 G T L V t where
  z_mem : z ∈ V1 T L V
  z_ne_one : z ≠ 1
  T_le_Gz : T ≤ Subgroup.centralizer ({z} : Set G)
  V_le : V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))

end S127

@[expose] def Lemma12_7_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G), Setting1274 G T L V t z →
    (∀ g : G, V ⊓ conjSubgroup V g ≠ ⊥ → ⁅V, conjSubgroup V g⁆ = ⊥) ∧
    (E3.wClos V 1 T ≤ Subgroup.centralizer (V : Set G) ∨
      (autOn (E3.wClos V 1 T) V = autOn (R2 T L V) V ∧ E3.rParam V = 3)) ∧
    Subgroup.centralizer (E3.cClos V 1 T : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
    (3 < E3.rParam V →
      Subgroup.centralizer (E3.cClos V 2 T : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
    ∀ g : G, V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ≠ ⊥ →
      IsPGroup 2 ↥(V ⊔ conjSubgroup V g)

@[expose] def Display12_7_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G), Setting1274 G T L V t z →
    ¬ Nonempty (G ≃* NativeSporadic.M24) →
      ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H ∧
        H ≤ Subgroup.centralizer ({z} : Set G)

@[expose] def Lemma12_7_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G), Setting1274 G T L V t z →
    ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
      H ≤ Subgroup.centralizer ({z} : Set G) →
        E1.nParam H = 2 ∧
        (IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) ∨
          IsPSL 3 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) ∧
        L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_7_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G), Setting1274 G T L V t z →
    3 < E3.rParam V

@[expose] def Final1271Para : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G), Setting1274 G T L V t z →
    ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
      H ≤ Subgroup.centralizer ({z} : Set G) →
      E1.nParam H = 2 →
      (IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) ∨
        IsPSL 3 2 2 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) →
      L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G) →
      3 < E3.rParam V → False

namespace S127

variable {G : Type} [Group G]

theorem centralizer_conj (l z : G) :
    Subgroup.centralizer ({l * z * l⁻¹} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj l).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have h1 : l⁻¹ * x * l * z = l⁻¹ * (x * (l * z * l⁻¹)) * l := by group
    have h2 : z * (l⁻¹ * x * l) = l⁻¹ * ((l * z * l⁻¹) * x) * l := by group
    rw [h1, h2, hx]
  · intro hx
    have h1 : x * (l * z * l⁻¹) = l * ((l⁻¹ * x * l) * z) * l⁻¹ := by group
    have h2 : l * z * l⁻¹ * x = l * (z * (l⁻¹ * x * l)) * l⁻¹ := by group
    rw [h1, h2, hx]

theorem relIndex_centralizer_conj [Finite G] {L : Subgroup G} {l : G} (hl : l ∈ L) (z : G) :
    (Subgroup.centralizer ({l * z * l⁻¹} : Set G)).relIndex L =
      (Subgroup.centralizer ({z} : Set G)).relIndex L := by
  have hLmap : L.map (MulAut.conj l).toMonoidHom = L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    constructor
    · intro hx
      have : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
      rw [this]
      exact L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    · intro hx
      exact L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
  have hcard : Nat.card ↥(Subgroup.centralizer ({l * z * l⁻¹} : Set G) ⊓ L) =
      Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ L) := by
    rw [centralizer_conj, ← hLmap,
      ← Subgroup.map_inf_eq _ _ (MulAut.conj l).toMonoidHom (MulAut.conj l).injective, hLmap,
      Subgroup.card_map_of_injective (f := (MulAut.conj l).toMonoidHom) (MulAut.conj l).injective]
  have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({l * z * l⁻¹} : Set G))
    (K := L)
  have h2 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({z} : Set G)) (K := L)
  rw [hcard] at h1
  have hpos : 0 < Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ L) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem le_pCoreOf_centralizer_conj {V : Subgroup G} {l z z₀ : G}
    (hl : l ∈ Subgroup.normalizer (V : Set G)) (hz : l * z * l⁻¹ = z₀)
    (hV : V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :
    V ≤ pCoreOf 2 (Subgroup.centralizer ({z₀} : Set G)) := by
  rw [← hz, centralizer_conj, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
  intro v hv
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  apply hV
  have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hl) v).1 hv
  rwa [inv_inv] at h

end S127

theorem lemma12_7_4_one_of (h4 : Lemma12_7_4) : Lemma12_7_4_one := by
  intro G _ _ T L V hH
  obtain ⟨⟨z, hz, -, -, t, ht, -, h45, h18, horb⟩, -⟩ := h4 G T L V hH
  exact ⟨z, (Subgroup.mem_inf.1 hz).1, t, ht, h45, h18, horb⟩

theorem final1271_of_lemmas (h4 : Lemma12_7_4) (hdisp : Display12_7_22) (h23 : Lemma12_7_23)
    (h24 : Lemma12_7_24) (hfin : Final1271Para) : Final1271 := by
  intro G _ _ T L V hH hM24 _ t ht ht18 z hz hz45 hGt hVz
  obtain ⟨⟨z₀, hz₀, hz₀1, hTz₀, t₀, -, -, h45, h18, horb⟩, -⟩ := h4 G T L V hH
  have hz1 : z ≠ 1 := by
    rintro rfl
    have : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [this, Subgroup.relIndex_top_left] at hz45
    exact absurd hz45 (by decide)
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨l, hl, hlz⟩ | ⟨l, hl, hlz⟩ := horb z hz hz1
  · have hV₀ := S127.le_pCoreOf_centralizer_conj (hLV hl) hlz hVz
    have hS : S127.Setting1274 G T L V t z₀ := ⟨⟨hH, ht, ht18, hGt⟩, hz₀, hz₀1, hTz₀, hV₀⟩
    obtain ⟨H, hHs, hHz⟩ := hdisp G T L V t z₀ hS hM24
    obtain ⟨hn, hK, hLT⟩ := h23 G T L V t z₀ hS H hHs hHz
    exact hfin G T L V t z₀ hS H hHs hHz hn hK hLT (h24 G T L V t z₀ hS)
  · rw [← hlz, S127.relIndex_centralizer_conj hl] at h18
    rw [h18] at hz45
    exact absurd hz45 (by decide)

theorem stmt12_7_1_of_decomp (h4 : Lemma12_7_4) (h1277 : Theorem12_7_7)
    (h12714 : Theorem12_7_14) (hdisp : Display12_7_22) (h23 : Lemma12_7_23) (h24 : Lemma12_7_24)
    (hfin : Final1271Para) : Stmt12_7_1 :=
  stmt12_7_1_of_lemmas (lemma12_7_4_one_of h4) h1277 h12714
    (final1271_of_lemmas h4 hdisp h23 h24 hfin)

end CFSG.Quasithin.H13
