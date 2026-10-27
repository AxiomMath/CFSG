module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4E3
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4E4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Hyp611.normalizer_thompsonJ_le_ch614 (h331 : Stmt3_3_1) {T M L V : Subgroup G} {n : ℕ}
    (h : Hyp611 G T M L V n) (hJN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G)) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hB⟩ := h331 G T h.simple h.nonabelian h.qtke h.sylow
  obtain ⟨⟨-, -, huniq⟩, -, -, -⟩ := hB L h.maximal h.toHyp5_0_1.isQuasisimple
  have hMeq := huniq M h.maxTwoLocal (sup_le h.L_le h.T_le)
  have hJ : thompsonJ T ≠ ⊥ := by
    intro hJ
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have hA₀b : A₀ = ⊥ := le_bot_iff.mp (hJ ▸ B6.le_thompsonJ hA₀)
    have hV := hA₀.2.2 V h.le_T h.isElemAbelian
    rw [hA₀b, Subgroup.card_bot] at hV
    exact h.ne_bot (Subgroup.eq_bot_of_card_le V hV)
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := h.sylow.1.to_le (B6.thompsonJ_le T)
  have hO : pCoreOf 2 (Subgroup.normalizer (thompsonJ T : Set G)) ≠ ⊥ := fun h0 =>
    hJ (le_bot_iff.mp (h0 ▸ CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hJ2))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hM'eq := huniq M' hM'.1 (hJN.trans hM'.2)
  rw [hMeq, ← hM'eq]
  exact hM'.2

theorem res614EndGame_of (h331 : Stmt3_3_1) (h512 : Stmt5_1_2) (h513 : Stmt5_1_3)
    (h37 : A37ForSQTK) (hFive : KG614Five) (hFus : KG614Fusion) (hTits : Res614Tits) :
    Res614EndGame := by
  intro G _ _ T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ hK₁q hK₁M hXL hXM₁ hX2 hX5 hXn hTX hXK₁
    hXK₀ hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsG : IsSimpleGroup G := h.simple
  have hnab := h.nonabelian
  have hK := h.qtke
  have hM₁ne : pCoreOf 2 M₁ ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM₁.1
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    quasithinOmegaOneCenter_le_inf T
  have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hZT.trans inf_le_right)
  have hTM₁ : T ≤ M₁ := hTC.trans hCM₁
  have hsylM₁ : IsSylowTwoOf T M₁ := h.toHyp5_0_1.isSylowTwoOf hTM₁
  obtain ⟨hVL, hVC⟩ := h.commutator_eq_and_inf_of_orth_ch6 horth (by norm_num)
  have hJN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rcases ((stmt6_1_2 h512 h513) G T M L V 4 h).2 with hnat | ⟨-, -, hJN, -⟩
    · exact (horth.false_of_isNatQuot_ch6 hVL.symm.le hVC hnat).elim
    · exact hJN
  have hNJM := h.normalizer_thompsonJ_le_ch614 h331 hJN
  have hJK₁ : ¬ K₁ ≤ Subgroup.normalizer (thompsonJ T : Set G) := fun h' => hK₁M (h'.trans hNJM)
  have hJX : X ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    sup_le ((hXL.trans le_sup_left).trans hJN) (le_sup_right.trans hJN)
  have hE1 := not_commutator_le_pCoreOf_ch614 hsylM₁ hK₁ hTX hXK₀ hnot
  have hinner : X ≤ K₁ ⊔ centralizerMod (pCoreOf 2 K₁) M₁ K₁ :=
    hXK₀.trans (conjClosure_le_sup_ch614 hK hsG hnab h37 hM₁ne hK₁ hTM₁)
  have hK₁M₁ : K₁ ≤ M₁ := le_of_mem_cComp hK₁
  have hTK₁syl : IsSylowTwoOf (T ⊓ K₁) K₁ :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₁) hsylM₁
  have hT₁K : (T ⊓ Subgroup.normalizer (K₁ : Set G)) ⊓ K₁ = T ⊓ K₁ := by
    rw [inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
  have hXT₁ : X ⊓ (T ⊓ Subgroup.normalizer (K₁ : Set G)) = X ⊓ T := by
    rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hXK₁)]
  rcases hFive G M₁ K₁ (T ⊓ Subgroup.normalizer (K₁ : Set G)) X
      (sqtkGroup_of_pCoreOf_ne_bot hK hsG hnab hM₁ne) hK₁ hK₁q (inf_le_left.trans hTM₁)
      (h.sylow.1.to_le inf_le_left) inf_le_right (by rw [hT₁K]; exact hTK₁syl) hXM₁ hX2
      (by rw [hXT₁]; exact hX5) (by rw [hXT₁]; exact hXn) (inf_le_left.trans hTX) hXK₁ hinner
      hE1 with hc | ⟨hXK, htype⟩ | htits
  ·
    rw [hT₁K] at hc
    have hK₀M₁ : conjClosure K₁ T ≤ M₁ := conjClosure_le fun t ht k hk =>
      M₁.mul_mem (M₁.mul_mem (hTM₁ ht) (hK₁M₁ hk)) (M₁.inv_mem (hTM₁ ht))
    have hsylK₀T : IsSylowTwoOf T (conjClosure K₁ T ⊔ T) :=
      B6.isSylowTwoOf_mono hsylM₁ le_sup_right (sup_le hK₀M₁ hTM₁)
    have hSK₀ : IsSylowTwoOf (T ⊓ conjClosure K₁ T) (conjClosure K₁ T) :=
      A4.isSylowTwoOf_inf_normal hsylK₀T le_sup_left
        (sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K₁ T))
    exact hnot (le_normalizer_inf_conjClosure_ch614
      (conj_le_normalizer_conj_ch614 hK hsG hnab h37 hM₁ne hK₁ hTM₁) hSK₀ hTX hc)
  ·
    have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) :=
      le_normalizer_of_le_ch614 hK hsG hnab h37 hM₁ne hK₁ hTM₁ hTX hXK hE1
    have hsylKT : IsSylowTwoOf T (K₁ ⊔ T) :=
      B6.isSylowTwoOf_mono hsylM₁ le_sup_right (sup_le hK₁M₁ hTM₁)
    have hK₀ : conjClosure K₁ T = K₁ := le_antisymm
      (conjClosure_le fun t ht k hk => (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
      (le_conjClosure K₁ T)
    rw [hK₀] at hnot
    exact false_of_fusion_ch614 hFus hK₁q htype hTK hsylKT hXK hX2 hX5 hXn hTX hnot hJX hJK₁
  · exact hTits G T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ htits hK₁M hXL hXM₁ hX2 hX5 hXn hTX
      hXK₁ hXK₀ hnot

end CFSG.Quasithin.H13
