module

public import CFSG.Quasithin.EmptyFaithful.T1515cC
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.EmptyFaithful.T1515Inputs
public import CFSG.Quasithin.EmptyFaithful.T1515cB

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Two

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ x ∈ Subgroup.centralizer (V : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) v).mp hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hx _ hv'
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * v := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key g hg x, fun hx => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx⟩

theorem oTwoUpper_centralizer_ne_bot {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) :
    oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≠ ⊥ := by
  intro hbot
  set X := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hX
  have hX2 : IsPGroup 2 X :=
    isPGroup_two_of_odd_orderOf_eq_one1515c fun x hx ho =>
      eq_one_of_odd_orderOf_of_oTwoUpper_eq_bot1515c hbot hx ho
  have hTX : T ≤ X := by
    rw [hX, Subgroup.le_centralizer_iff]
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    exact hz.1.2
  have hSyl : IsSylowTwoOf T X := isSylowTwoOf_of_quasithinIsSylowTwo hq.sylow hTX
  have hXT : X ≤ T := (hSyl.eq_of_le hTX le_rfl hX2).le
  exact hM.2.1 (hq.mc_unique M hM.1.1.1 (hXT.trans hM.1.1.2))

theorem pCoreOf_oTwoUpper_ne_bot {Mz X : Subgroup G} (hCT : CharTwo Mz) (hXMz : X ≤ Mz)
    (hMzN : Mz ≤ Subgroup.normalizer (oTwoUpper X : Set G)) (hY : oTwoUpper X ≠ ⊥) :
    pCoreOf 2 (oTwoUpper X) ≠ ⊥ := by
  set Y := oTwoUpper X with hYdef
  set Q := pCoreOf 2 Mz with hQ
  have hYMz : Y ≤ Mz := (oTwoUpper_le X).trans hXMz
  intro hP
  have hYQ : Y ≤ Subgroup.centralizer (Q : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hyMz : y ∈ Mz := hYMz hy
    have hqMz : q ∈ Mz := pCoreOf_le 2 Mz hq
    have h1 : y * q * y⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mz hyMz) q).mp hq
    have h2 : q * y⁻¹ * q⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hMzN hqMz) y⁻¹).mp (Y.inv_mem hy)
    have hc1 : y * q * y⁻¹ * q⁻¹ ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
    have hc2 : y * q * y⁻¹ * q⁻¹ ∈ Y := by
      have := Y.mul_mem hy h2
      simpa [mul_assoc] using this
    have hYQnorm : Y ≤ Subgroup.normalizer ((Y ⊓ Q : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 Mz (hYMz hg)⟩
    have hle : Y ⊓ Q ≤ pCoreOf 2 Y :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hYQnorm
        ((pCoreOf_isPGroup 2 Mz).to_le inf_le_right)
    have : y * q * y⁻¹ * q⁻¹ ∈ pCoreOf 2 Y := hle ⟨hc2, hc1⟩
    rw [hP, Subgroup.mem_bot] at this
    have h3 : y * q = q * y := by
      have := congrArg (· * (q * y)) this
      simpa [mul_assoc] using this
    exact h3.symm
  have hYQ' : Y ≤ Q := fun y hy => hCT ⟨hYMz hy, hYQ hy⟩
  apply hY
  rw [eq_bot_iff, hYdef, oTwoUpper, Subgroup.closure_le]
  intro x hx
  have hxQ : x ∈ Q := hYQ' (Subgroup.subset_closure hx)
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Mz) ⟨x, hxQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hx.2)
  have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp this)

theorem normalizer_le_of_isMaxTwoLocal {Mc Y : Subgroup G} (hMc : quasithinIsMaxTwoLocal Mc)
    (hMcN : Mc ≤ Subgroup.normalizer (Y : Set G)) (hP : pCoreOf 2 Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ Mc := by
  have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Y
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
    ⟨pCoreOf 2 Y, hP, pCoreOf_isPGroup 2 Y, rfl⟩
  exact hNY.trans (hMc.2 _ hloc (hMcN.trans hNY)).le

end Two

theorem lemma_15_1_19_two_e9 {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h18 : Lemma15118Concl T Mc M Z₁)
    (h14 : Lemma15114Concl T Mc M)
    (hMc : Mc = Subgroup.normalizer (vE1516 T Mc M : Set G))
    (hQ1 : q1_1516 Mc Z₁ = pCoreOf 2 (Subgroup.centralizer (vE1516 T Mc M : Set G))) :
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
  have hMzMc : Mz ≤ Mc := mZ1516_le_mc Mc Z₁
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
  set VE := vE1516 T Mc M with hVE
  set C := Subgroup.centralizer (VE : Set G) with hCdef
  have hMcN : Mc ≤ Subgroup.normalizer (VE : Set G) := hMc.le
  have hCG1 : C ≤ G1 := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h18.one.1)
  have hCMc : C ≤ Mc := fun g hg => hMc.ge (Subgroup.centralizer_le_normalizer _ hg)
  have hCMz : C ≤ Mz := le_inf hCG1 hCMc
  have hQC : Q ≤ C := hQ1.le.trans (pCoreOf_le 2 C)
  have hY0Mc : Mc ≤ Subgroup.normalizer (oTwoUpper C : Set G) :=
    (hMcN.trans (Two.normalizer_le_normalizer_centralizer VE)).trans
      (normalizer_le_normalizer_oTwoUpper C)
  have hY0Mz : oTwoUpper C ≤ Mz := (oTwoUpper_le C).trans hCMz
  have hincl : ∀ x ∈ Lb i, ∀ h ∈ oTwoUpper C, x * h * x⁻¹ ∈ oTwoUpper C := by
    intro x hx
    have key : oTwoUpper C ≤ (oTwoUpper C).comap (MulAut.conj x).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      have hyN : y ∈ Subgroup.normalizer (Lb i : Set G) :=
        mem_normalizer_of_odd1515c hsqtk hCT hXblock hcX hcp hc2 hcc (hMzNH (hCMz hy.1)) hy.2
      have hcomm := commutator_mem_pCoreOf_of_odd1515c hXA3 hyN hy.2 hx
      have hd : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (Lb i) := by
        have := (pCoreOf 2 (Lb i)).inv_mem hcomm
        simpa [mul_assoc] using this
      have hdC : x * y * x⁻¹ * y⁻¹ ∈ C := hQC (hXQ hd)
      have hxyC : x * y * x⁻¹ ∈ C := by
        have := C.mul_mem hdC hy.1
        simpa [mul_assoc] using this
      show x * y * x⁻¹ ∈ oTwoUpper C
      refine mem_oTwoUpper_of_odd hxyC ?_
      rw [C2Eleven.orderOf_conj_eq]
      exact hy.2
    intro h hh
    exact key hh
  have hXNY : Lb i ≤ Subgroup.normalizer (oTwoUpper C : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hincl x hx h hh, fun hh => ?_⟩
    have := hincl x⁻¹ ((Lb i).inv_mem hx) _ hh
    simpa [mul_assoc] using this
  have hYne : oTwoUpper C ≠ ⊥ := by
    intro hbot
    refine Two.oTwoUpper_centralizer_ne_bot hC.qtfe hC.mf (eq_bot_iff.mpr ?_)
    rw [← hbot]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    exact mem_oTwoUpper_of_odd
      (h14.one (Ce15.not_case3b hC.setting.ce15) (mem_oTwoUpper_of_odd hy.1 hy.2)) hy.2
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC.qtfe.omegaOneCenter_ne_bot
  have hzZ : (a : G) ∈ quasithinOmegaOneCenter T := a.2
  have hz1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hCTMz : CharTwo Mz := (h18.six (a : G) hzZ hz1).charTwo_inf
  have hPne : pCoreOf 2 (oTwoUpper C) ≠ ⊥ :=
    Two.pCoreOf_oTwoUpper_ne_bot hCTMz hCMz (hMzMc.trans hY0Mc) hYne
  have hXMc : Lb i ≤ Mc :=
    hXNY.trans (Two.normalizer_le_of_isMaxTwoLocal hC.qtfe.mc_max hY0Mc hPne)
  exact hi fun x hx => ⟨hKG (hXK hx), hXMc hx⟩

end CFSG.Quasithin.E9
