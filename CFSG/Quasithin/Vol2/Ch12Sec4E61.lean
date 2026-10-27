module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma5
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.Quasithin.Background.E6Hyp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem sup_le_normalizer_of_cx (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (hcx : Cx1242 G T L V) :
    L ⊔ T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  rw [← pCoreOf_sup_eq_of_hyp1223 h1222 h3228 hcx.hyp]
  exact LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)

theorem isUniqueM_sup_of_cx (h331 : Stmt3_3_1) (hcx : Cx1242 G T L V) :
    IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) := by
  have hyp := hcx.hyp
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨hmax, -, huniq⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at hmax huniq
  exact ⟨⟨hmax, sup_le Subgroup.le_normalizer hyp.normalizes⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩

theorem hypE61_of_cx (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hcx : Cx1242 G T L V) (hVe : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    E6.HypE61 T (Subgroup.normalizer (L : Set G)) V := by
  have hyp := hcx.hyp
  obtain ⟨⟨hmax, hLT⟩, huniq⟩ := isUniqueM_sup_of_cx h331 hcx
  have hLTX : L ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) :=
    le_inf (sup_le_normalizer_of_cx h1222 h3228 hcx) (le_inf hLT (sup_le hLV hTV))
  refine
    { simple := hyp.simple
      nonabelian := hyp.nonabelian
      qtke := hyp.qtke
      sylow := hyp.sylow
      inM := ⟨hmax, hyp.normalizes⟩
      ne_bot := hV1
      isElemAbelian := hVe
      le := hVT
      normal := hTV
      tiSet := ⟨hVT.trans hyp.normalizes, fun g hg hgN => ?_⟩
      unique := ⟨⟨hmax, inf_le_right.trans inf_le_left⟩, fun M' hM' =>
        huniq M' ⟨hM'.1, hLTX.trans hM'.2⟩⟩ }
  rcases (stmt12_2_6_of h1222 h323 G T L V hyp).1 g hg with h | h
  · exact absurd (mem_normalizer_of_conjugate_eq h) hgN
  · exact h

end CFSG.Quasithin.H13
