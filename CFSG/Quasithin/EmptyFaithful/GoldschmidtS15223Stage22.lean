module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223W21
public import CFSG.Quasithin.EmptyFaithful.S152U22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement Pointwise

namespace S15223

theorem stageLemma15222Canon_of (h2 : StageLemma15202) (h1515 : StageLemma1515CE)
    (h1521 : StageLemma15201) (hN : StageNotation15209) (h16 : StageLemma15216)
    (h17 : StageLemma15217) (h18 : StageLemma15218) (h21 : StageLemma15221W)
    (hIn : Input15222ThreeCanon) : StageLemma15222Canon := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hii hCh h3p hnirr Y₁ hcanon hY₁eq hY₁N hSY hq
    hcomm
  have hData : S152Y.Data T Mc M :=
    ⟨hs.qtfe, hs.mf, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1521 G T Mc M hs⟩
  have c21 := h21 G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI
  have c18 := h18 G T Mc M hs H hH B₀ hB₀ I hI
  have c16 := h16 G T Mc M hs H hH B₀ hB₀ I hI
  have c17 := h17 G T Mc M hs B₀ hB₀ I hI
  have cN := hN G T Mc M hs H hH
  obtain ⟨hKS, hKconj, -, -⟩ := c21.one hnirr
  obtain ⟨t, htT, htS, hcommt, hautY⟩ :=
    hIn G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hii hCh h3p hnirr Y₁ hcanon hY₁eq hY₁N hSY hq
  have hTM : T ≤ M := hData.T_le
  have hT2 : IsPGroup 2 T := (isSylowTwoOf_of_le151 hs.qtfe.sylow hTM).2.1
  have hST : sOf152 T Mc M B₀ ≤ T := inf_le_left
  have hrel : (sOf152 T Mc M B₀).relIndex T = 2 := c17.2.2
  have hKSle := c16.KS_le
  have hSI : sOf152 T Mc M B₀ ≤ I := (le_sup_right.trans hKSle).trans inf_le_right
  have hKI : oTwoUpper H ≤ I := (le_sup_left.trans hKSle).trans inf_le_right
  have hY₁M : Y₁ ≤ M := hY₁N.trans inf_le_left
  have hY₁I : Y₁ ≤ I := hY₁N.trans inf_le_right
  have hK₁H : oTwoUpper H₁ ≤ oTwoUpper H := oTwoUpper_mono hP.le₁.2
  have hK₁I : oTwoUpper H₁ ≤ I := hK₁H.trans hKI
  have hPK₁ : H₁ ⊔ H₂ ≤ Subgroup.normalizer (oTwoUpper H₁ : Set G) :=
    sup_le (le_normalizer_oTwoUpper H₁)
      ((hp152_le_normalizer_one hP).trans (normalizer_le_normalizer_oTwoUpper H₁))
  have hPK₂ : H₁ ⊔ H₂ ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) :=
    sup_le ((hp152_le_normalizer_two hP).trans (normalizer_le_normalizer_oTwoUpper H₂))
      (le_normalizer_oTwoUpper H₂)
  have hSP : sOf152 T Mc M B₀ ≤ H₁ ⊔ H₂ := le_sup_right.trans hKS.le
  have hK₁P : oTwoUpper H₁ ≤ H₁ ⊔ H₂ := (oTwoUpper_le H₁).trans le_sup_left
  have hK₂P : oTwoUpper H₂ ≤ H₁ ⊔ H₂ := (oTwoUpper_le H₂).trans le_sup_right
  have hSK₁ : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (oTwoUpper H₁ : Set G) := hSP.trans hPK₁
  have hSK₂ : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := hSP.trans hPK₂
  have hK₁K₂ : oTwoUpper H₁ ≤ Subgroup.normalizer (oTwoUpper H₂ : Set G) := hK₁P.trans hPK₂
  have hK₂K₁ : oTwoUpper H₂ ≤ Subgroup.normalizer (oTwoUpper H₁ : Set G) := hK₂P.trans hPK₁
  have htinv : t⁻¹ ∈ T := T.inv_mem htT
  have htinvS : t⁻¹ ∉ sOf152 T Mc M B₀ := fun h => htS (by simpa using (sOf152 T Mc M B₀).inv_mem h)
  have hconjK₁ : conjSub t (oTwoUpper H₁) = oTwoUpper H₂ := hKconj t htT htS
  have hconjK₂ : conjSub t (oTwoUpper H₂) = oTwoUpper H₁ := by
    have := hKconj t⁻¹ htinv htinvS
    rw [← this, conjSub_inv_conjSub]
  obtain ⟨hY₁K₂, hK₂Y₁⟩ := normalizes_of_commutator_le_inf152 hcomm
  have hcommB : ⁅conjSub t Y₁, oTwoUpper H₁⁆ ≤ conjSub t Y₁ ⊓ oTwoUpper H₁ := by
    have := conjSub_mono t hcomm
    rwa [← conjSub_commutator, conjSub_inf, hconjK₂] at this
  obtain ⟨hY₁tK₁, hK₁Y₁t⟩ := normalizes_of_commutator_le_inf152 hcommB
  obtain ⟨hY₁Y₁t, hY₁tY₁⟩ := normalizes_of_commutator_le_inf152 hcommt
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = Y₁ ⊔ oTwoUpper H₁ := ⟨_, rfl⟩
  obtain ⟨Xt, hXt⟩ : ∃ Xt : Subgroup G, Xt = conjSub t Y₁ ⊔ oTwoUpper H₂ := ⟨_, rfl⟩
  have hXt' : conjSub t X = Xt := by rw [hX, hXt, conjSub_sup, hconjK₁]
  have hXN : X ≤ Subgroup.normalizer (Xt : Set G) := by
    rw [hX, hXt]
    refine sup_le (le_normalizer_sup152 hY₁Y₁t hY₁K₂) (le_normalizer_sup152 hK₁Y₁t hK₁K₂)
  have hXtN : Xt ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX, hXt]
    refine sup_le (le_normalizer_sup152 hY₁tY₁ hY₁tK₁) (le_normalizer_sup152 hK₂Y₁ hK₂K₁)
  have hSX : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact le_normalizer_sup152 hSY hSK₁
  have hSXt : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Xt : Set G) := by
    intro s hs
    have hs' : t⁻¹ * s * t ∈ sOf152 T Mc M B₀ := by
      have := conj_mem_of_relIndex_two152 hST hrel htinv hs
      simpa using this
    have hN' : t⁻¹ * s * t ∈ Subgroup.normalizer (X : Set G) := hSX hs'
    have e : s * t = t * (t⁻¹ * s * t) := by group
    rw [← hXt']
    apply mem_normalizer_of_conjSub_eq152
    rw [← conjSub_mul, e, conjSub_mul, conjSub_eq_self152 hN']
  have ht2S : t * t ∈ sOf152 T Mc M B₀ := by
    have := sq_mem_of_relIndex_two152 hrel htT htS
    rwa [sq] at this
  have hconjXt : conjSub t Xt = X := by
    rw [← hXt', ← conjSub_mul, conjSub_eq_self152 (hSX ht2S)]
  have htXXt : t ∈ Subgroup.normalizer ((X ⊔ Xt : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conjSub_eq152
    rw [conjSub_sup, hXt', hconjXt, sup_comm]
  have hTN : T ≤ Subgroup.normalizer ((X ⊔ Xt : Subgroup G) : Set G) := by
    rw [← sup_zpowers_eq_of_relIndex_two152 hST hrel htT htS]
    exact sup_le (le_normalizer_sup152 hSX hSXt) ((Subgroup.zpowers_le).mpr htXXt)
  have hXSI : X ⊔ sOf152 T Mc M B₀ ≤ I := by
    rw [hX]
    exact sup_le (sup_le hY₁I hK₁I) hSI
  have hCXS : CharTwo (X ⊔ sOf152 T Mc M B₀) := by
    refine charTwo_of_pCore_centralizer_le hCh hXSI ?_
    exact (inf_le_left.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf c18.sylow)).trans
      le_sup_right
  have hCX : CharTwo X := by
    refine CharTwo.of_normal hCXS le_sup_left ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSX)
  have hK₁ne : oTwoUpper H₁ ≠ ⊥ := oTwoUpper_ne_bot_of_iso152 hP
  have hK₁X : oTwoUpper H₁ ≤ X := by rw [hX]; exact le_sup_right
  have hXne : X ≠ ⊥ := fun h0 => hK₁ne (le_bot_iff.mp (h0 ▸ hK₁X))
  have hO2X : pCoreOf 2 X ≠ ⊥ := by
    intro hbot
    refine hXne (le_bot_iff.mp fun x hx => ?_)
    have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ pCoreOf 2 X := hy
      rw [hbot, Subgroup.mem_bot] at hy'
      rw [hy']
      simp
    have := hCX ⟨hx, hxc⟩
    rwa [hbot] at this
  have hQXN : X ⊔ Xt ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    sup_le (BorelTits.le_normalizer_pCoreOf 2 X)
      (hXtN.trans (BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hO2XXt : pCoreOf 2 (X ⊔ Xt) ≠ ⊥ := by
    intro hbot
    apply hO2X
    rw [eq_bot_iff]
    have := BorelTits.le_pCoreOf_of_le_normalizer 2
      ((BorelTits.pCoreOf_le 2 X).trans le_sup_left) hQXN (BorelTits.pCoreOf_isPGroup 2 X)
    rwa [hbot] at this
  have hRN : (X ⊔ Xt) ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ Xt) : Set G) :=
    sup_le (BorelTits.le_normalizer_pCoreOf 2 _)
      (hTN.trans (BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hO2 : pCoreOf 2 ((X ⊔ Xt) ⊔ T) ≠ ⊥ := by
    intro hbot
    apply hO2XXt
    rw [eq_bot_iff]
    have := BorelTits.le_pCoreOf_of_le_normalizer 2
      ((BorelTits.pCoreOf_le 2 (X ⊔ Xt)).trans le_sup_left) hRN
      (BorelTits.pCoreOf_isPGroup 2 (X ⊔ Xt))
    rwa [hbot] at this
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO2
  have hY₁tM : conjSub t Y₁ ≤ M := by
    intro x hx
    have h1 := mem_conjSub.mp hx
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (hTM htT) (hY₁M h1)) (M.inv_mem (hTM htT))
  have hU := unique_of_autOn_eq152 hs hData h2 (sup_le hY₁M hY₁tM) hautY
  have hY₁X : Y₁ ≤ X := by rw [hX]; exact le_sup_left
  have hY₁tXt : conjSub t Y₁ ≤ Xt := by rw [hXt]; exact le_sup_left
  have hMM' : M' = M := hU.2 M' ⟨hM'.1, sup_le_sup_right (sup_le_sup hY₁X hY₁tXt) T |>.trans hM'.2⟩
  have hK₁M : oTwoUpper H₁ ≤ M := by
    rw [← hMM']
    exact hK₁X.trans (le_sup_left.trans (le_sup_left.trans hM'.2))
  have hK₁H' : oTwoUpper H₁ ≤ H := (oTwoUpper_le H₁).trans hP.le₁.2
  have hK₁T : oTwoUpper H₁ ≤ T := by
    rw [cN.eq_inf]
    exact le_inf hK₁M hK₁H'
  apply hK₁ne
  have h1 : oTwoUpper (oTwoUpper H₁) ≤ ⊥ := by
    rw [← oTwoUpper_eq_bot_of_isPGroup152 hT2]
    exact oTwoUpper_mono hK₁T
  rwa [A4.oTwoUpper_oTwoUpper, le_bot_iff] at h1

theorem stageLemma15222Canon_of_stages (h2 : StageLemma15202) (h1515 : StageLemma1515CE)
    (h1521 : StageLemma15201) (hN : StageNotation15209) (h16 : StageLemma15216)
    (h17 : StageLemma15217) (h18 : StageLemma15218) (h21 : StageLemma15221W)
    (h5 : StageLemma15205) (h159 : StageLemma1519) (h11 : StageLemma15211)
    (h13 : StageLemma15213) (h14 : StageLemma15214) : StageLemma15222Canon :=
  stageLemma15222Canon_of h2 h1515 h1521 hN h16 h17 h18 h21
    (input15222ThreeCanon_of h5 h159 h11 h13 h14 hN h16 h17)

end S15223

end CFSG.Quasithin
