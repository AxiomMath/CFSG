module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddG2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsOddAb
public import CFSG.Quasithin.Background.G13Two
public import CFSG.Quasithin.Background.G2L2Six

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.SL2Model
open scoped MatrixGroups commutatorElement

section General

variable {G : Type} [Group G]

theorem coprime_le_commutator_sup_inf_centralizer [Finite G] {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ Subgroup.centralizer (X : Set G)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ Subgroup.centralizer (X : Set G)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

theorem coprime_commutator_commutator_eq [Finite G] {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : G) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : G)⁻¹, (a : G)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup G).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  ·
    have hN : X ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
      refine le_normalizer_of_conj_mem fun r hr w hw => ?_
      have hle : ⁅P, X⁆ ≤ (⁅P, X⁆ : Subgroup G).comap (MulAut.conj r).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro p hp x hx
        show r * ⁅p, x⁆ * r⁻¹ ∈ ⁅P, X⁆
        have e : r * ⁅p, x⁆ * r⁻¹ = ⁅r * p * r⁻¹, r * x * r⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.commutator_mem_commutator
          ((Subgroup.mem_normalizer_iff.mp (hXP hr) p).mp hp)
          (X.mul_mem (X.mul_mem hr hx) (X.inv_mem hr))
      exact hle hw
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hN
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

theorem isElemAbelian_conjClosure_of_le_centralizer {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : conjClosure V X ≤ Subgroup.centralizer (V : Set G)) :
    IsElemAbelian 2 (conjClosure V X) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall hV fun k hk v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hU (HypF91.conjSub_le_conjClosure hk hy)) v hv).symm

theorem almostSpecial_commutator_mem_of_mem_pCoreOf [Finite G] {V V₁ L T H : Subgroup G}
    (h : AlmostSpecialHyp V V₁ L T H) {u x : G} (hu : u ∈ conjClosure V H)
    (hx : x ∈ pCoreOf 2 H) : u * x * u⁻¹ * x⁻¹ ∈ V₁ := by
  have hcc := h.conjClosure_le_N
  have hmem : tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    (secImg_le_iff.1 h.G22_one.2) ⟨u, hcc hu⟩ hu
  have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) := h.H_le (pCoreOf_le 2 H hx)
  have hxQ : tmk V₁ ⟨x, hxN⟩ ∈ tildeOf V₁ (pCoreOf 2 H) := secMk_mem_secImg hx
  exact commutator_mem_of_secMk_commute (mem_centralizer_of_mem_omegaOneCenterOf hmem hxQ).symm

end General

theorem sl2_mul_self_eq_one_of_smul_eq {F : Type} [Field F] [CharP F 2]
    {A : Matrix.SpecialLinearGroup (Fin 2) F} {w : Fin 2 → F} (hw : w ≠ 0) (hA : A • w = w) :
    A * A = 1 := by
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_single w hw
  have hA' : A ∈ sl2Stab w := hA
  obtain ⟨b, rfl⟩ := (mem_sl2Stab_iff hB A).mp hA'
  have hX : sl2X b * sl2X b = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2X, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  calc B * sl2X b * B⁻¹ * (B * sl2X b * B⁻¹) = B * (sl2X b * sl2X b) * B⁻¹ := by group
    _ = 1 := by rw [hX]; group

theorem stmt5_1_17_abelian_of (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first) (h126 : A126TwoFact) (hnb : Stmt5_1_17_noBlock) :
    Stmt5_1_17_abelian := by
  intro G _ _ T M L V H B D n s _ H₁ hH₁ hH₁N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hA := s.almostSpecialHyp hI hF hH₁ hH₁N
  have hTH₁ : T ≤ H₁ := s.hyp.hyp.hStar.1.1.trans (le_sup_left.trans hH₁)
  by_contra hU
  have hUO : ¬ conjClosure V H₁ ≤ pCoreOf 2 (L ⊔ T) := fun hle => hU
    (isElemAbelian_conjClosure_of_le_centralizer s.elemAbelian
      (hle.trans ((hh.sup_inf_centralizer_eq s.hyp.module).ge.trans inf_le_right)))
  have hyp2 : AlmostSpecialL2Hyp n V (quasithinOmegaOneCenter T ⊓ V) L T H₁ :=
    ⟨hA, by have := s.one_le_n; omega, s.V_eq_conjClosure, s.isNaturalSL2Module hI, hUO⟩
  obtain ⟨g, hgL, hgN⟩ : ∃ g ∈ L,
      g ∉ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) := by
    by_contra hcon
    have hall : ∀ l ∈ L,
        l ∈ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) :=
      fun l hl => by_contra fun hn => hcon ⟨l, hl, hn⟩
    have hle : V ≤ quasithinOmegaOneCenter T ⊓ V :=
      calc V = conjClosure (quasithinOmegaOneCenter T ⊓ V) L := s.V_eq_conjClosure
        _ ≤ quasithinOmegaOneCenter T ⊓ V := conjClosure_le fun l hl z hz =>
          (Subgroup.mem_normalizer_iff.mp (hall l hl) z).mp hz
    exact hA.irred.1.not_ge hle
  set U := conjClosure V H₁ with hUdef
  set I := U ⊔ rconj U g with hIdef
  set S := pCoreOf 2 I with hSdef
  set S₂ := U ⊓ rconj U g with hS₂def
  have h2 : I = L ⊔ U := hyp2.G23_two hgL hgN
  have h4 := hyp2.G23_four hgL hgN
  have hVS₂ : V ≤ S₂ := h4.1
  have hIS : I ≤ Subgroup.normalizer (S : Set G) := h4.2.2.2.2.2
  have h5 : ⁅S₂, I⁆ ≤ V := (hyp2.G23_five hgL hgN).1
  obtain ⟨⟨r, β, φ, -, hβk, -, hφk, hφe⟩, -, -, hWS⟩ :=
    hyp2.G23_six (U := U) (I := I) (S := S) (W := U ⊓ S) rfl hgL hgN rfl rfl rfl
      G1.theorem_G_1_3_two
  obtain ⟨D₀⟩ := hyp2.natural.nonempty_data
  have hSO : S ≤ pCoreOf 2 (L ⊔ T) :=
    (⟨hyp2, D₀⟩ : L2Setting n V (quasithinOmegaOneCenter T ⊓ V) L T H₁).pCoreOf_I_le_O hgL hgN
  have hN1M : Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) ≤
      Subgroup.normalizer (oTwoUpper H : Set G) := by
    have hloc : IsTwoLocal
        (Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G)) :=
      ⟨_, s.Z₁_ne_bot, hA.isPGroup_V₁, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hHM' : H ≤ M' := ((le_sup_left.trans hH₁).trans hH₁N).trans hle
    rw [← (s.hyp.isUniqueM h5114).2 M' ⟨hM', hHM'⟩]
    exact hle
  have hLI : L ≤ I := by rw [h2]; exact le_sup_left
  have hDI : D ≤ I := (s.hyp.notation59.2.1.1.trans inf_le_left).trans hLI
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := hDI.trans hIS
  have hDodd : Odd (Nat.card D) := s.hyp.notation59.2.1.2.1
  have hcardD : Nat.card D = 2 ^ n - 1 := (hh.isCyclic_card_of_isHall hF s.hyp.notation59.2.1).2
  have hodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd => Odd.of_dvd_nat hDodd (by
    rw [← Subgroup.orderOf_mk d hd]
    exact orderOf_dvd_natCard _)
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 I
  have hcop : Nat.Coprime (Nat.card D) (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hDodd)
  have hSsolv : Group.IsSolvable ↥S := by
    have := hS2.isNilpotent
    infer_instance
  have hfac := coprime_le_commutator_sup_inf_centralizer hDS hSsolv hcop
  have hidem := coprime_commutator_commutator_eq hDS hcop
  have hCS : S ⊓ Subgroup.centralizer (D : Set G) ≤ S₂ := by
    rintro c ⟨hcS, hcC⟩
    obtain ⟨d, hdD, hd1'⟩ : ∃ d ∈ D, d ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one D with h0 | h0
      · exfalso
        have h1 : Nat.card D = 1 := by rw [h0, Subgroup.card_bot]
        have h4' : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hh.two_le
        omega
      · exact h0
    have hβ : β ⟨d, hDI hdD⟩ ≠ 1 := fun h1 =>
      hd1' (eq_one_of_odd_orderOf_of_mem hS2 ((hβk ⟨d, hDI hdD⟩).mp h1) (hodd d hdD))
    have hβodd : Odd (orderOf (β ⟨d, hDI hdD⟩)) := Odd.of_dvd_nat (hodd d hdD) (by
      have := orderOf_map_dvd β ⟨d, hDI hdD⟩
      rwa [Subgroup.orderOf_mk] at this)
    have hfix := hφe ⟨d, hDI hdD⟩ ⟨c, hcS⟩ ⟨c, hcS⟩ (by
      show c = d * c * d⁻¹
      rw [Subgroup.mem_centralizer_iff.mp hcC d hdD, mul_inv_cancel_right])
    have hw : ∀ j, Multiplicative.toAdd (φ ⟨c, hcS⟩) j = 0 := by
      intro j
      by_contra hj
      have hj' := congrFun (congrArg Multiplicative.toAdd hfix) j
      simp only [toAdd_ofAdd] at hj'
      have hAA := sl2_mul_self_eq_one_of_smul_eq hj hj'.symm
      apply hβ
      have h1 : orderOf (β ⟨d, hDI hdD⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hAA)
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.mpr hβodd) h1)
    have h1 : φ ⟨c, hcS⟩ = 1 := by
      rw [← ofAdd_toAdd (φ ⟨c, hcS⟩), show Multiplicative.toAdd (φ ⟨c, hcS⟩) = 0 from funext hw,
        ofAdd_zero]
    exact (hφk ⟨c, hcS⟩).mp h1
  have hST : S ≤ T := hSO.trans (pCoreOf_two_le_of_isSylowTwoOf hA.sylow_LT)
  have hDC : D ≤ centralizerModO2 (oTwoUpper H) := s.D_le_centralizer
  have hMC := normalizer_le_normalizer_centralizerModO2 (oTwoUpper H)
  have hSDS : ⁅S, D⁆ ≤ S := (Subgroup.le_normalizer_iff_commutator_le_left).mp hDS
  have hSDC : ⁅S, D⁆ ≤ centralizerModO2 (oTwoUpper H) :=
    Subgroup.commutator_le.mpr fun x hx d hd => by
      have h1 : x * d * x⁻¹ ∈ centralizerModO2 (oTwoUpper H) :=
        (Subgroup.mem_normalizer_iff.mp (hMC (s.hyp.T_le_Mp (hST hx))) d).mp (hDC hd)
      rw [commutatorElement_def]
      exact (centralizerModO2 (oTwoUpper H)).mul_mem h1
        ((centralizerModO2 (oTwoUpper H)).inv_mem (hDC hd))
  have hD3 : ¬ 3 ∣ Nat.card D := by
    rw [hcardD]
    exact s.not_three_dvd
  have hcop6 : Nat.Coprime (Nat.card D) 6 := by
    have h3 : Nat.Coprime (Nat.card D) 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3)
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hDodd) h3
  have hA126 : ⁅S, D⁆ ≤ pCoreOf 2 (centralizerModO2 (oTwoUpper H)) := by
    refine h126 G (centralizerModO2 (oTwoUpper H)) D ⁅S, D⁆ hDC ?_ hSDC (hS2.to_le hSDS) hidem
      s.solvable ?_ ?_
    · exact le_antisymm (oTwoUpper_le D) fun d hd => mem_oTwoUpper_of_odd hd (hodd d hd)
    · intro p hp hp2
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp
        (centralizerModO2_le_normalizer (oTwoUpper H))).trans
          (s.hyp.pRank_Mp_le_two h5114 hp hp2)
    · refine le_antisymm ((Subgroup.closure_le D).mpr fun x hx => hx.1) fun d hd => ?_
      refine Subgroup.subset_closure ⟨hd, Nat.Coprime.coprime_dvd_left ?_ hcop6⟩
      rw [← Subgroup.orderOf_mk d hd]
      exact orderOf_dvd_natCard _
  have hH₁M : H₁ ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hH₁N.trans hN1M
  have hMP : Subgroup.normalizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (centralizerModO2 (oTwoUpper H)) : Set G) :=
    hMC.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hPT : pCoreOf 2 (centralizerModO2 (oTwoUpper H)) ≤ T :=
    (le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 _).trans (centralizerModO2_le_normalizer (oTwoUpper H))) hMP
      (pCoreOf_isPGroup 2 _)).trans
      (pCoreOf_two_le_of_isSylowTwoOf (hh.isSylowTwoOf s.hyp.T_le_Mp))
  have hPQ : pCoreOf 2 (centralizerModO2 (oTwoUpper H)) ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 (hPT.trans hTH₁) (hH₁M.trans hMP) (pCoreOf_isPGroup 2 _)
  have hUQ : U ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 (hA.G22_three.1.trans hTH₁) (le_normalizer_conjClosure V H₁)
      (hA.isPGroup_T.to_le hA.G22_three.1)
  have hSQ : S ≤ pCoreOf 2 H₁ :=
    hfac.trans (sup_le (hA126.trans hPQ) (hCS.trans (inf_le_left.trans hUQ)))
  have hSU : S ≤ U := fun x hx => ((hWS x hx).mpr fun u hu =>
    hVS₂ (almostSpecial_commutator_mem_of_mem_pCoreOf hA hu (hSQ hx)).2).1
  have hSS₂ : S ≤ S₂ := fun x hx =>
    ⟨hSU hx, mem_rconj.mpr (hSU ((Subgroup.mem_normalizer_iff.mp (hIS (hLI hgL)) x).mp hx))⟩
  have hOL : pCoreOf 2 L ≤ S := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI) ?_ (pCoreOf_isPGroup 2 L)
    rw [h2]
    exact sup_le (le_normalizer_pCoreOf 2 L)
      ((hA.G22_three.1.trans hA.T_le_normL).trans (normalizer_le_normalizer_pCoreOf 2 L))
  exact hnb G T M L V H B D n s ((Subgroup.commutator_mono (hOL.trans hSS₂) hLI).trans h5)

end CFSG.Quasithin.H13
