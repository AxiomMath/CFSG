module

public import CFSG.Quasithin.Vol2.Ch10SecC3B
public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch10SecC3A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt3_2_10_nine_of (hC58 : TheoremC58) (h317 : AS317Sylow) (h331 : Stmt3_3_1)
    (h3228 : Stmt3_2_2_eight) (h323 : Stmt3_2_3) : Stmt3_2_10_nine := by
  intro G _ _ T L I Vp hfsu hVp hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVH, hVred, hOC⟩ := h3228 G T L I hfsu
  have hred : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVH, hVred⟩
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp (cComp_of_isLocal hfsu.maximal.1)
  obtain ⟨⟨hmax, hLTM, huniq⟩, -, hHne, -⟩ :=
    (h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L hfsu.maximal
      hfsu.quasisimple
  have hLT : fsuL0 T L ⊔ T = L ⊔ T := Vol2.Ch10.C3.conjClosure_sup_eq L T
  have hTM : T ≤ fsuM T L := le_sup_right.trans hLTM
  have hyp : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) :=
    { inM := ⟨hmax, hTM⟩
      nonempty := hHne
      perfect := eq_oTwoUpper_of_perfect (perfect_conjClosure hperf)
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := ⟨⟨hmax, hLT ▸ hLTM⟩, fun M' hM' => huniq M' hM'.1 (hLT ▸ hM'.2)⟩
      reduced := hred
      centralizer := hOC }
  have hVT : fsuV T I ≤ T :=
    (A4.le_pCoreOf_of_isTwoReducedIn hred).trans (hOC ▸ inf_le_left)
  have hVp' : fsuV T I ≤ Vp ∧ Vp ≤ T ∧ T ≤ Subgroup.normalizer (Vp : Set G) := by
    rcases hVp with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · have hR : IsTwoReducedIn (fsuM T L) (fsuVM T L I) :=
        isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2
          (Vol2.Ch10.tmpL6_3_2_2_two_of h3228 h323 G T L I hfsu)
      have hTsyl : IsSylowIn 2 T (fsuM T L) := ⟨hTM, hfsu.sylow.1,
        fun h => hfsu.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
      exact ⟨le_conjClosure _ _,
        (A4.le_pCoreOf_of_isTwoReducedIn hR).trans (pCoreOf_le_of_isSylowIn hTsyl),
        hTM.trans (le_normalizer_conjClosure _ _)⟩
    · exact ⟨le_rfl, hVT, le_normalizer_conjClosure I T⟩
  obtain ⟨hVVp, hVpT, hTVp⟩ := hVp'
  have hJV : thompsonJ T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    le_inf (iSup_le fun _ => iSup_le fun hA => hA.1) (hJ.trans (Subgroup.centralizer_le hVVp))
  rcases theorem318_three hC58 h317 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow hyp with
    ⟨hJ', -⟩ | ⟨-, -, hZ⟩
  · exact absurd hJV hJ'
  refine ⟨eq_bot_iff.2 fun z hz => ?_, ?_⟩
  · have hz' := Vol2.Ch10.C3.omegaOneCenter_le T hz.1
    have hzc := Vol2.Ch10.C3.mem_centerOf hz'.1 hz'.2 hz.2
    rw [hZ] at hzc
    exact hzc
  · by_contra hne
    have hTY : T ≤ Subgroup.normalizer
        ((Vp ⊓ Subgroup.centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hTVp ht,
        A1b.le_normalizer_centralizer (le_normalizer_conjClosure L T) ht⟩
    obtain ⟨z, hzY, hz1, hzT⟩ :=
      Vol2.Ch10.C3.exists_ne_one_mem_centralizer hfsu.sylow.1 (inf_le_left.trans hVpT) hTY hne
    have hzc := Vol2.Ch10.C3.mem_centerOf (hVpT hzY.1) hzT hzY.2
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hz1 hzc

end CFSG.Quasithin.H13
