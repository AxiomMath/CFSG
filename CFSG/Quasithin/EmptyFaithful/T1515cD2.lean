module

public import CFSG.Quasithin.EmptyFaithful.T1515cC
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.EmptyFaithful.T1515Inputs
public import CFSG.Quasithin.EmptyFaithful.T1515cB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_19_two1515c {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h18 : Lemma15118Concl T Mc M Z₁)
    (hx18 : Lemma15118Extra T Mc M Z₁) :
    ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
      mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁ := by
  intro K hKG hKodd hKN hKchar
  by_contra hKnot
  obtain ⟨hcgs, hMzN, hHyp⟩ := h18.five
  set G1 := g1_1516 Z₁ with hG1
  set Mz := mZ1516 Mc Z₁ with hMz
  set Q := q1_1516 Mc Z₁ with hQdef
  have hQMz : Q ≤ Mz := q1_1516_le Mc Z₁
  have hMzG1 : Mz ≤ G1 := mZ1516_le_g1 Mc Z₁
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQN : Q ≤ Subgroup.normalizer (K : Set G) := hQMz.trans hKN
  have hMzNQ : Mz ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 Mz
  have hSMz : s1516 T Z₁ ≤ Mz :=
    le_inf (s1516_le_g1 T Z₁) ((s1516_le T Z₁).trans hC.qtfe.t_le_mc)
  have hOQ : pCoreOf 2 K ≤ Q := by
    have hH'G1 : K ⊔ Mz ≤ G1 := sup_le hKG hMzG1
    have hSylH' : IsSylowTwoOf (s1516 T Z₁) (K ⊔ Mz) :=
      A4.isSylowTwoOf_mono h18.four (hSMz.trans le_sup_right) hH'G1
    have hDn : K ⊔ Mz ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      sup_le (le_normalizer_pCoreOf 2 K) (hKN.trans (normalizer_le_normalizer_pCoreOf 2 K))
    have hD1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Mz) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left) hDn
        (pCoreOf_isPGroup 2 K)
    have hDMz : pCoreOf 2 K ≤ Mz := hD1.trans ((IsSylowTwoOf.pCoreOf_le hSylH').trans hSMz)
    exact le_pCoreOf_of_le_normalizer 2 hDMz
      (hKN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hSyl : IsSylowTwoOf Q (K ⊔ Q) := isSylowTwoOf_sup_of_odd_quotient1515c hQ2 hQN hKodd hOQ
  have hCT : CharTwo (K ⊔ Q) := charTwo_sup_of_odd_quotient1515c hQ2 hQN hKchar
  have hsolv : Group.IsSolvable ↥(K ⊔ Q) := isSolvable_sup_of_odd_quotient1515c hQ2 hQN hKodd
  have hHG1 : K ⊔ Q ≤ G1 := sup_le hKG (hQMz.trans hMzG1)
  have hsqtk : IsSQTKIn (K ⊔ Q) := hHyp.sqtk.mono hHG1
  have hQHN : Q ≤ (K ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  have hrad_eq : Q = pCoreOf 2 ((K ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G)) := by
    have hQle : Q ≤ pCoreOf 2 ((K ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 hQHN inf_le_right hQ2
    exact le_antisymm hQle ((A4.isSylowTwoOf_iff_maximal.mp hSyl).2.2 _
      ((pCoreOf_le 2 _).trans inf_le_left) (pCoreOf_isPGroup 2 _) hQle)
  have hcgsH : cgsIn (K ⊔ Q) Q ≤ Mz ⊓ (K ⊔ Q) :=
    le_inf ((C2Nine.cgsIn_mono_left hHG1 Q).trans hcgs.le) (cgsIn_le _ _)
  have hconj : conjClosure Q (Mz ⊓ (K ⊔ Q)) = Q :=
    le_antisymm (conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.mp (hMzNQ hh.1) z).mp hz) (le_conjClosure _ _)
  have hsylQ : IsSylowTwoOf Q (conjClosure Q (Mz ⊓ (K ⊔ Q))) := by
    rw [hconj]
    exact ⟨le_rfl, hQ2, by simp⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ := asc129StatementSolv G (K ⊔ Q) Q (Mz ⊓ (K ⊔ Q)) hsqtk hCT hSyl
    hcgsH inf_le_right hsolv
  have hex : ∃ i, ¬ Lb i ≤ Mz := by
    by_contra hall
    push Not at hall
    apply hKnot
    intro k hk
    obtain ⟨m, hm, x, hx, hkx⟩ := hprod k (Subgroup.mem_sup_left hk)
    rw [hkx]
    refine Mz.mul_mem hm.1 (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hall i (hx i)
  obtain ⟨i, hi⟩ := hex
  have hXchi : IsChi0Block (K ⊔ Q) (Lb i) := (hLb i).1
  have hXblock : IsBlock2 (K ⊔ Q) (Lb i) := hXchi.1
  have hXA3 : IsAltType (Lb i) 3 :=
    C1Pack.isAltType_three_of_isChiBlock_of_isSolvable
      (C1GN.isChiBlock_of_isChi0Block hXblock hXchi) hsolv
  have hXK : Lb i ≤ K := le_of_isShort2_of_le_sup1515c hQ2 hQN hXblock.1 hXblock.2.1
  obtain ⟨c, hcX, hcp, hc2, hcc⟩ := exists_noncentral_odd_prime_of_isChi0Block hXchi
  have hXQ : pCoreOf 2 (Lb i) ≤ Q :=
    (A4.pCoreOf_le_of_subnormal 2 (IsBlock2.isSubnormal hXblock)).trans
      (IsSylowTwoOf.pCoreOf_le hSyl)
  have hMzNH : Mz ≤ Subgroup.normalizer ((K ⊔ Q : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_sup1515c (hKN hy) (hMzNQ hy)
  have hincl : ∀ x ∈ Lb i, ∀ h ∈ oTwoUpper Mz, x * h * x⁻¹ ∈ oTwoUpper Mz := by
    intro x hx
    have key : oTwoUpper Mz ≤ (oTwoUpper Mz).comap (MulAut.conj x).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      have hyN : y ∈ Subgroup.normalizer (Lb i : Set G) :=
        mem_normalizer_of_odd1515c hsqtk hCT hXblock hcX hcp hc2 hcc (hMzNH hy.1) hy.2
      have hcomm := commutator_mem_pCoreOf_of_odd1515c hXA3 hyN hy.2 hx
      have hd : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (Lb i) := by
        have := (pCoreOf 2 (Lb i)).inv_mem hcomm
        simpa [mul_assoc] using this
      have hdMz : x * y * x⁻¹ * y⁻¹ ∈ Mz := hQMz (hXQ hd)
      have hxyMz : x * y * x⁻¹ ∈ Mz := by
        have := Mz.mul_mem hdMz hy.1
        simpa [mul_assoc] using this
      show x * y * x⁻¹ ∈ oTwoUpper Mz
      refine mem_oTwoUpper_of_odd hxyMz ?_
      rw [C2Eleven.orderOf_conj_eq]
      exact hy.2
    intro h hh
    exact key hh
  have hXNY : Lb i ≤ Subgroup.normalizer (oTwoUpper Mz : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hincl x hx h hh, fun hh => ?_⟩
    have := hincl x⁻¹ ((Lb i).inv_mem hx) _ hh
    simpa [mul_assoc] using this
  have hYne : oTwoUpper Mz ≠ ⊥ :=
    oTwoUpper_ne_bot_of_isUniqueM1515c h18.four hSMz hMzG1 (s1516_le T Z₁) h18.seven.1
      hC.mf.1.1 hC.mf.2.1
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC.qtfe.omegaOneCenter_ne_bot
  have hzZ : (a : G) ∈ quasithinOmegaOneCenter T := a.2
  have hz1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hCTMz : CharTwo Mz := (h18.six (a : G) hzZ hz1).charTwo_inf
  have hXMc : Lb i ≤ Mc :=
    hXNY.trans (normalizer_oTwoUpper_le_of_isUniqueM1515c h18.seven.1 hx18.mz_normal hCTMz hYne)
  exact hi fun x hx => ⟨hKG (hXK hx), hXMc hx⟩

end CFSG.Quasithin
