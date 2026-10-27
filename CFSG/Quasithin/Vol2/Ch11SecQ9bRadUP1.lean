module

public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA12Setup
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34A
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G} {n : ℕ}

namespace C11P9B

theorem pCoreOf_normalizer_ne_bot_of_le (h : Hyp11 G T L I n) {W : Subgroup G}
    (hWV : W ≤ fsuV T I) (hW : W ≠ ⊥) : pCoreOf 2 (Subgroup.normalizer (W : Set G)) ≠ ⊥ := by
  intro h0
  apply hW
  rw [eq_bot_iff, ← h0]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    ((isPGroup_fsuV h).to_le hWV)

theorem sqtkGroup_of_le_normalizer_W (h : Hyp11 G T L I n) {W : Subgroup G}
    (hWV : W ≤ fsuV T I) (hW : W ≠ ⊥) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.normalizer (W : Set G)) : SQTKGroup ↥Z := by
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  exact InternalSec.sqtkGroup_mono
    (InternalSec.sqtkGroup_of_localSQTK hloc (pCoreOf_normalizer_ne_bot_of_le h hWV hW)) hZ

theorem a318_sup_W (h318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp11 G T L I n) {W Y : Subgroup G} (hWV : W ≤ fsuV T I) (hW : W ≠ ⊥)
    (hK : K ∈ cComp (Subgroup.normalizer (W : Set G)))
    (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    A318Conclusion p (K.subgroupOf (K ⊔ Y)) := by
  have hKN := le_of_mem_cComp hK
  have hHN : K ⊔ Y ≤ Subgroup.normalizer (W : Set G) := sup_le hKN hYW
  have hS := sqtkGroup_of_le_normalizer_W h hWV hW hHN
  have hSQ := SQTKHyp.of_sqtkGroup ↥(K ⊔ Y) hS
  have hKc : K ∈ cComp (K ⊔ Y) := cComp_mem_of_le hK le_sup_left hHN
  obtain ⟨e⟩ := quotPCore_subgroupOf_equiv (L := K) (le_sup_left : K ≤ K ⊔ Y)
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQ
  have hr : 1 < CFSG.Open.pRank p (K.subgroupOf (K ⊔ Y)) := by
    rw [pRank_subgroupOf_eq le_sup_left hp hp2]
    omega
  exact a318 h318 hS (h36 _ hSQ) (h38 _ hSQ) (subgroupOf_mem_cComp hKc) hQ' hp hp2 hr

theorem le_centralizer_point (hF11 : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) {V₀ : Subgroup G} (hV₀₁ : V₀ ≤ V₁)
    (hK : K ∈ cComp (Subgroup.normalizer (V₀ : Set G))) (hLK : LOf L V₁ ≤ K) :
    K ≤ Subgroup.centralizer (V₀ : Set G) :=
  le_of_cComp_of_perfect hK (Subgroup.centralizer_le_normalizer _)
    (fun _ hk => mem_normalizer_centralizer (le_of_mem_cComp hK hk))
    (lOf_ne_bot hN h1102 h hV₁ (Or.inl rfl)) (perfectCore_perfect _) hLK
    ((lOf_one_le_centralizer hF11 h1102 h hV₁).trans (Subgroup.centralizer_le hV₀₁))

theorem not_le_normalizer_point (hF11 : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) {V₀ : Subgroup G} (hV₀₁ : V₀ ≤ V₁)
    (hLV₀ : L ⊓ Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (V₁ : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (V₀ : Set G))) (hlt : LOf L V₁ < K) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hKN := le_of_mem_cComp hK
  have hL₁ : LOf L V₁ ≤ L ⊓ Subgroup.normalizer (V₀ : Set G) :=
    le_inf ((perfectCore_le _).trans inf_le_left)
      (((lOf_one_le_centralizer hF11 h1102 h hV₁).trans (Subgroup.centralizer_le hV₀₁)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hKX : K ≤ L ⊓ Subgroup.normalizer (V₀ : Set G) := by
    refine le_of_cComp_of_perfect hK inf_le_right ?_ (lOf_ne_bot hN h1102 h hV₁ (Or.inl rfl))
      (perfectCore_perfect _) hlt.le hL₁
    exact (le_inf hKM (hKN.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKL : K ≤ LOf L V₁ := by
    rw [← perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)]
    exact perfectCore_mono (hKX.trans (le_inf inf_le_left hLV₀))
  exact hlt.not_ge hKL

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
