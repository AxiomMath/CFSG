module

public import CFSG.Quasithin.Background.E6TwentySevenMain

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6

variable {G : Type} [Group G] [Finite G]

theorem e6_27_unbarred (hPT : ParabolicTorusFact) {T M V U : Subgroup G} (h : HypE61 T M V)
    (hU1 : U ≠ ⊥) (hUV : U ≤ V) {j : ℕ} (hj : 0 < j) (hr : (j : ℕ∞) < E3.rParam V)
    (h2 : H13.thompsonJk j (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G))
    (h3 : E3.nPrime (M ⊓ Subgroup.centralizer (U : Set G)) ≤ j) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set CMU := M ⊓ Subgroup.centralizer (U : Set G) with hCMUdef
  set MV := M ⊓ Subgroup.normalizer (V : Set G) with hMVdef
  have hQsyl : IsSylowIn 2 Q (M ⊓ Subgroup.centralizer (V : Set G)) := h.isSylowIn_centralizer
  have hCVU : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.centralizer_le hUV
  have hQCMU : Q ≤ CMU := le_inf (inf_le_left.trans h.inM.2) (inf_le_right.trans hCVU)
  obtain ⟨S, hS, hQS⟩ := A4.exists_isSylowTwoOf_ge hQCMU (h.isPGroup_Q)
  have hCN : CMU ≤ Subgroup.normalizer (V : Set G) := inf_centralizer_le_normalizer_of_le h hU1 hUV
  have hSMV : S ≤ MV := le_inf (hS.1.trans inf_le_left) (hS.1.trans hCN)
  have hTMV : IsSylowTwoOf T MV :=
    A4.isSylowTwoOf_mono h.isSylowIn_normalizer (le_inf h.inM.2 h.normal) inf_le_right
  obtain ⟨T', hT', hST'⟩ := A4.exists_isSylowTwoOf_ge hSMV hS.2.1
  obtain ⟨g, hgMV, hgT⟩ := B6.isSylowTwoOf_exists_conj hTMV hT'
  have hT'syl : quasithinIsSylowTwo T' := by
    refine ⟨hT'.2.1, ?_⟩
    have e : T'.index = T.index := by
      rw [hgT]
      exact Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).bijective T
    rw [e]
    exact h.sylow.2
  have hVMV : V ≤ MV := le_inf h.tiSet.1 Subgroup.le_normalizer
  have hVT' : V ≤ T' := IsSylowIn.le_of_normal (p := 2) hT' hVMV
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVMV).2 inf_le_right) h.isPGroup_V
  have hT'Q : T' ⊓ Subgroup.centralizer (V : Set G) = Q := by
    refine le_antisymm ?_ (le_inf (hQS.trans hST') inf_le_right)
    have h1 : T' ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
      inf_le_inf_right _ (hT'.1.trans inf_le_left)
    exact (A4.isSylowTwoOf_iff_maximal.1 hQsyl).2.2 _ h1 (hT'.2.1.to_le inf_le_left)
      (le_inf (hQS.trans hST') inf_le_right)
  have h' : HypE61 T' M V :=
    { simple := h.simple
      nonabelian := h.nonabelian
      qtke := h.qtke
      sylow := hT'syl
      inM := ⟨h.inM.1, hT'.1.trans inf_le_left⟩
      ne_bot := h.ne_bot
      isElemAbelian := h.isElemAbelian
      le := hVT'
      normal := hT'.1.trans inf_le_right
      tiSet := h.tiSet
      unique := by rw [hT'Q]; exact h.unique }
  have hSeq : T' ⊓ Subgroup.centralizer (U : Set G) = S := by
    refine le_antisymm ?_ (le_inf hST' (hS.1.trans inf_le_right))
    exact (A4.isSylowTwoOf_iff_maximal.1 hS).2.2 _
      (le_inf (inf_le_left.trans (hT'.1.trans inf_le_left)) inf_le_right)
      (hT'.2.1.to_le inf_le_left) (le_inf hST' (hS.1.trans inf_le_right))
  have hS' : IsSylowTwoOf (T' ⊓ Subgroup.centralizer (U : Set G)) CMU := by rw [hSeq]; exact hS
  have hJS : H13.thompsonJk j S ≤ S ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (E5.thompsonJk_le j S)
      ((thompsonJk_le_of_isSylowTwoOf hS).trans (h2.trans inf_le_right))
  have hS2 : IsPGroup 2 S := hS.2.1
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hNS : Subgroup.normalizer (S : Set G) ≤ M := by
    have hJQ : thompsonJ S ≤ Q :=
      (thompsonJ_le_thompsonJk j S).trans (hJS.trans (le_inf (inf_le_left.trans
        (hST'.trans' le_rfl)) inf_le_right |>.trans (by rw [← hT'Q])))
    have hJ1 : thompsonJ S ≠ ⊥ := thompsonJ_ne_bot (hVQ.trans hQS) h.isElemAbelian h.ne_bot
    have hNJ := normalizer_thompsonJ_le h.isUniqueM_normalizer_Q hJQ hQS hS2 hJ1
    exact fun x hx => hNJ (E5.mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hx))
  have hSM : S ≤ M := hS.1.trans inf_le_left
  have hSK : IsSylowTwoOf S (Subgroup.centralizer (U : Set G)) :=
    isSylowTwoOf_of_normalizer_le hS (hS.1.trans inf_le_right) hSM hNS
  have hQ'S : T' ⊓ Subgroup.centralizer (V : Set G) ≤ S := hT'Q ▸ hQS
  refine e6_27_of_parabolics h' hUV hj hr hS' h2 ?_
  rw [hSeq]
  intro H hH hn
  exfalso
  obtain ⟨⟨hHK, hSH, hmax⟩, hHN⟩ := hH
  obtain ⟨MH, hMH⟩ := Set.ncard_eq_one.1 hmax
  have hHC : H ≤ Subgroup.centralizer (U : Set G) := by
    refine hHK.trans ?_
    rw [← conjClosure_eq_twoPrimeResidual hSK]
    exact conjClosure_le fun k hk s hs => Subgroup.mul_mem _ (Subgroup.mul_mem _ hk
      (hSK.1 hs)) (Subgroup.inv_mem _ hk)
  have hSHsyl : IsSylowTwoOf S H := A4.isSylowTwoOf_mono hSK hSH.le hHC
  have hmin : MinParabolic H S MH := ⟨hSHsyl, hHN, hMH⟩
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    have hUH : U ≤ H := (hUV.trans (hVQ.trans hQS)).trans hSH.le
    have hUO : U ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf 2 hUH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).2
        (hHC.trans (Subgroup.centralizer_le_normalizer _)))
      (h.isPGroup_V.to_le hUV)
    exact fun hb => hU1 (le_bot_iff.1 (hb ▸ hUO))
  have hn1 : 1 < E1.nParam H := lt_of_le_of_lt (by exact_mod_cast hj) hn
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    absurd (E1.solvable_nParam_le_one hs) (not_le.2 hn1)
  obtain ⟨hMHs, c, B, Y, hc, hYB, hBMH, hBab, hBodd, hBS, hYcyc, hYcard, -⟩ :=
    hPT G H S MH h.simple h.nonabelian h.qtke hO2 hmin hns hn1
  have hMHH : MH ≤ H := (hMH ▸ Set.mem_singleton MH : MH ∈ maxOver H S).1.le
  have hSMH : S ≤ MH := (hMH ▸ Set.mem_singleton MH : MH ∈ maxOver H S).2
  have hMHM : MH ≤ M := by
    refine le_of_parabolics (A4.isSylowTwoOf_mono hSHsyl hSMH hMHH) hSM hNS fun P hP => ?_
    have hPMH : P ≤ MH := hP.1.1.trans (conjClosure_le fun k hk s hs =>
      MH.mul_mem (MH.mul_mem hk (hSMH hs)) (MH.inv_mem hk))
    have hPs : Group.IsSolvable ↥P := by
      have := hMHs
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPMH)
    have hSP : IsSylowTwoOf S P := A4.isSylowTwoOf_mono hSHsyl hP.1.2.1.le (hPMH.trans hMHH)
    exact (e6_26 h'.sylow.1 h.ne_bot h.isElemAbelian hVT' h.normalizer_le
      (by rw [hT'Q]; exact h.isUniqueM_normalizer_Q) hj
      ((E1.solvable_nParam_le_one hPs).trans (by exact_mod_cast hj)) hSP hQ'S hST' hr hJS).1
  have hBM : B ≤ CMU := le_inf (hBMH.trans hMHM) ((hBMH.trans hMHH).trans hHC)
  have hle : c ≤ E3.nPrime CMU :=
    E3.le_nPrime (Y := Y) (B := B) (S := S) (c := c) hYB hBM hYcyc hYcard hBab hBodd hS hBS
  have hcj : c ≤ j := hle.trans h3
  have hjc : (j : ℕ∞) < c := lt_of_lt_of_le hn hc
  exact absurd hcj (not_le.2 (by exact_mod_cast hjc))

end CFSG.Quasithin.RonanE628
