module

public import CFSG.Quasithin.Vol2.Ch11SecB21Case1
public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch11SecCB51
public import CFSG.Quasithin.Vol2.Ch11SecB21Odd
public import CFSG.Quasithin.Vol2.Ch11SecBBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

theorem stmt11_2_1_of (hDHB : DerivedHallBorel) (h51 : AsB51) (h56 : AsB56)
    (hKF : SecC.KindModuleFacts) (h322 : Ch10.TmpL6_3_2_2_two)
    (h4413 : Ch10.TmpL6_4_4_13) (h442 : TmpL4_4_2) (h338 : ASInputs.AS_E_3_38_perH)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hNS : FactNotSmall443) (hNP : FactNPrimeNat) (hNP2 : FactNPrimeTwoNat)
    (hFC : FactCentralizerTwo) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) :
    Stmt11_2_1 := by
  intro G _ _ T L I n hyp H hH
  by_cases hle : E1.nParam H ≤ n
  · exact Or.inl hle
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := fsuV T I with hVdef
  have hlt : (n : ℕ∞) < E1.nParam H := not_le.mp hle
  have hn1 : 1 < E1.nParam H := lt_of_le_of_lt (by exact_mod_cast hyp.one_lt.le) hlt
  obtain ⟨B, hB, hBab, hTB⟩ := hDHB G T M H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩ (normalizer_T_le h331 hyp) hH hn1
  have hBV := inf_centralizer_hall_eq_bot h4413 h442 hNS h331 h3228 hyp hH hn1 hB hBab hTB
  by_cases hBN : B ≤ Subgroup.normalizer (V : Set G)
  · exact absurd (nParam_le_of_le_normalizer h338 hNP h331 h1102 hyp hH hn1 hB hBV hBN) hle
  have h03 := h1103 G T L I n hyp
  have hSL3 : KindSL3 L V n := by
    rcases kind_cases h1102 hyp with h | h | h
    · exact h
    · exact absurd (hB.1.trans (h03.2.2.2.2 (Or.inl h) H hH)) hBN
    · exact absurd (hB.1.trans (h03.2.2.2.2 (Or.inr h) H hH)) hBN
  obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hBN fun x hx => hcon x hx
  have hTI := h03.2.2.2.1.2 b (hB.1 hbB).2 hbN
  have hCH : V ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hTI]
    rintro v ⟨hvV, hvC⟩
    refine ⟨hvV, mem_conjSubgroup_iff.mpr ?_⟩
    rw [Subgroup.mem_centralizer_iff.mp hvC b (hB.1 hbB).1, mul_inv_cancel_right]
    exact hvV
  have hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    obtain ⟨hVLT, hVred, hcent⟩ := h3228 G T L I hyp.fsu
    rw [fsuL0_eq hyp] at hVLT hVred hcent
    have h318 : Hyp318 T M L V :=
      { inM := ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩
        nonempty := ⟨H, hH⟩
        perfect := (C2Nine.oTwoUpper_eq_of_perfect hyp.fsu.faithful.1.2.1.2.1).symm
        le_M := Subgroup.le_normalizer
        normal := le_rfl
        unique := isUniqueM_LT h331 hyp
        reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩
        centralizer := hcent }
    rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
        hyp.fsu.sylow h318 with h | ⟨-, hZ, -⟩
    · exact h.1
    exfalso
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (inf_centralizer_ne_bot hyp.fsu.sylow.1 (fsuV_le_T hyp) (T_le_normalizer_fsuV T I)
        (fsuV_ne_bot hyp))
    have hvZ : v ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨fsuV_le_T hyp hv.1, hv.2⟩, (isElemAbelian_fsuV hyp).2 v hv.1⟩
    have hvC : v ∈ V ⊓ Subgroup.centralizer (H : Set G) := ⟨hv.1, (hZ H hH hvZ).2⟩
    rw [hCH, Subgroup.mem_bot] at hvC
    exact hv1 (Subtype.ext hvC)
  have hLJ := eq_commutator_thompsonJ hFC h1102 hyp hJ
  have hMVM : M ≤ Subgroup.normalizer (VM T L I : Set G) := le_normalizer_conjClosure V M
  have hVVM : V ≠ VM T L I := fun h => hBN (hB.1.trans (inf_le_right.trans (h ▸ hMVM)))
  have hVM : VMTwoNatural T L I n := by
    rcases SecC.fsuV_eq_VM_or h51 h56 h1102 hKF h322 hyp hLJ with h | ⟨-, -, h⟩
    · exact absurd h hVVM
    · exact h
  have hVMtr : IsTwoReducedIn M (VM T L I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 h03.1
  have hU := hVMtr.2.2.1
  have hVU : V ≤ VM T L I := le_conjClosure V M
  have hUT : VM T L I ≤ T := (le_pCoreOf_of_isTwoReducedIn hVMtr).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_M hyp))
  have hLTU : L ⊔ T ≤ Subgroup.normalizer (VM T L I : Set G) :=
    (sup_le Subgroup.le_normalizer hyp.normal).trans hMVM
  have hBU : B ⊓ Subgroup.centralizer (VM T L I : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left B (Subgroup.centralizer_le hVU)).trans hBV.le)
  have h1 := nParam_le_nPrime_of_le_normalizer h338 h331 h1102 hyp hH hn1 hB hU hVU hUT hLTU
    (inf_le_right.trans hMVM) hBU
  have hU1 : VM T L I ≠ ⊥ := fun h => fsuV_ne_bot hyp (le_bot_iff.mp (h ▸ hVU))
  have hNU : Subgroup.normalizer (VM T L I : Set G) ≤ M :=
    normalizer_le_of_isPGroup h331 hyp (hyp.fsu.sylow.1.to_le hUT) hU1 hLTU
  have h2 := hNP2 G L (VM T L I) n hU hyp.one_lt (Subgroup.le_normalizer.trans hMVM)
    ((vmTwoNatural_iff T L I n).mp hVM) ⊤ le_top (inf_le_right.trans hNU)
  exact ⟨hSL3, hVM, hCH, hLJ, h1.trans (by exact_mod_cast h2)⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
