module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.A1bReduced
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13

namespace C3

variable {G : Type} [Group G]

theorem omegaOneCenter_le (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  Subgroup.closure_le _ |>.2 fun _ hz => hz.1

theorem exists_ne_one_mem_centralizer [Finite G] {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hYT : Y ≤ T) (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hY : Y ≠ ⊥) :
    ∃ z ∈ Y, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have : (Y.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYT).mpr hTY
  have hne : Y.subgroupOf T ≠ ⊥ := by
    intro h
    refine hY (eq_bot_iff.mpr fun y hy => ?_)
    have hy' : (⟨y, hYT hy⟩ : ↥T) ∈ Y.subgroupOf T := Subgroup.mem_subgroupOf.mpr hy
    rw [h, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy')
  obtain ⟨⟨a, haY, haZ⟩, ha1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(a : G), Subgroup.mem_subgroupOf.mp haY, fun h => ha1 (Subtype.ext (Subtype.ext h)),
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp haZ ⟨t, ht⟩)

theorem conjClosure_sup_eq (L T : Subgroup G) : conjClosure L T ⊔ T = L ⊔ T := by
  apply le_antisymm
  · refine sup_le (conjClosure_le fun t ht l hl => ?_) le_sup_right
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht)
      (Subgroup.mem_sup_left hl)) ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  · exact sup_le ((le_conjClosure L T).trans le_sup_left) le_sup_right

theorem mem_centerOf {T L₀ : Subgroup G} {z : G} (hzT : z ∈ T)
    (hzC : z ∈ Subgroup.centralizer (T : Set G)) (hzL : z ∈ Subgroup.centralizer (L₀ : Set G)) :
    z ∈ centerOf (L₀ ⊔ T) := by
  have hle : L₀ ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := sup_le
    (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzL l hl))
    (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzC t ht))
  exact ⟨Subgroup.mem_sup_right hzT, Subgroup.mem_centralizer_iff.mpr fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hg)⟩

end C3

theorem tmpL6_3_2_10_nine_of_thm318 (hC58 : TheoremC58) (h317 : AS317Sylow) (h331 : Stmt3_3_1)
    (h3228 : TmpL6_3_2_2_eight) (h322 : TmpL6_3_2_2_two) : TmpL6_3_2_10_nine := by
  intro G _ _ T L I Vp hfsu hVp hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVH, hVred, hOC⟩ := h3228 G T L I hfsu
  have hred : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVH, hVred⟩
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp (cComp_of_isLocal hfsu.maximal.1)
  obtain ⟨⟨hmax, hLTM, huniq⟩, -, hHne, -⟩ :=
    (h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L hfsu.maximal
      hfsu.quasisimple
  have hLT : fsuL0 T L ⊔ T = L ⊔ T := C3.conjClosure_sup_eq L T
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
    rcases hVp with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · have hR : IsTwoReducedIn (fsuM T L) (fsuVM T L I) :=
        isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 (h322 G T L I hfsu)
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
  · have hz' := C3.omegaOneCenter_le T hz.1
    have hzc := C3.mem_centerOf hz'.1 hz'.2 hz.2
    rw [hZ] at hzc
    exact hzc
  · by_contra hne
    have hTY : T ≤ Subgroup.normalizer
        ((Vp ⊓ Subgroup.centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hTVp ht,
        A1b.le_normalizer_centralizer (le_normalizer_conjClosure L T) ht⟩
    obtain ⟨z, hzY, hz1, hzT⟩ :=
      C3.exists_ne_one_mem_centralizer hfsu.sylow.1 (inf_le_left.trans hVpT) hTY hne
    have hzc := C3.mem_centerOf (hVpT hzY.1) hzT hzY.2
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hz1 hzc

end CFSG.Quasithin.Vol2.Ch10
