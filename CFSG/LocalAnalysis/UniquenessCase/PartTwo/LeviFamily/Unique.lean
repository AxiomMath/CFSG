module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Dynkin
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import CFSG.Quasithin.MS93.S59Set
import CFSG.Quasithin.SteinbergCDBestOffenderRestriction
import CFSG.GroupTheory.PCore.PCoreOfNormalEq
import CFSG.GroupTheory.PElementCommutator
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
import CFSG.GroupTheory.PElementSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open scoped commutatorElement
open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Q : Type} [Group Q] [Finite Q]

namespace IsLeviFamily

variable {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}

private theorem le_of_oUpperTwo_le_of_commutator_sup
    {H N O : Subgroup Q} (_hNH : N ≤ H) (hOH : O ≤ H) (hNOP : O ≤ N)
    (hNnormal : (N.subgroupOf H).Normal)
    (hHperf : ⁅H, H⁆ ⊔ O = H)
    (hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo H ≤ N) :
    H ≤ N := by
  have : (N.subgroupOf H).Normal := hNnormal
  let π : ↥H →* (↥H ⧸ N.subgroupOf H) := QuotientGroup.mk' (N.subgroupOf H)
  have h2 : IsPGroup 2 (↥H ⧸ N.subgroupOf H) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) q
    obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.SUPair.exists_two_pow_mem h.2
    have ha' : (h : Q) ^ 2 ^ a ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo H := by
      simpa [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo] using ha
    refine ⟨a, ?_⟩
    change π h ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (hO2 ha')
  have hC : (⁅H, H⁆.subgroupOf H) = commutator (↥H) := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self H),
      Subgroup.map_subtype_commutator]
  have hsup : commutator (↥H) ⊔ O.subgroupOf H = ⊤ := by
    rw [← hC, ← Subgroup.subgroupOf_sup (Subgroup.commutator_le_self H) hOH, hHperf,
      Subgroup.subgroupOf_self]
  have hcomm : commutator (↥H ⧸ N.subgroupOf H) = ⊤ := by
    have hCm : (commutator (↥H)).map π = commutator (↥H ⧸ N.subgroupOf H) := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
      rw [_root_.commutator_def]
    have hbot : (O.subgroupOf H).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      show x ∈ π.ker
      rw [show π.ker = N.subgroupOf H from QuotientGroup.ker_mk' _]
      exact Subgroup.mem_subgroupOf.mpr (hNOP (Subgroup.mem_subgroupOf.mp hx))
    have hmap := congrArg (Subgroup.map π) hsup
    rw [Subgroup.map_sup, hCm, hbot, sup_bot_eq,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at hmap
    exact hmap
  have : Group.IsNilpotent (↥H ⧸ N.subgroupOf H) := h2.isNilpotent
  have : Group.IsSolvable (↥H ⧸ N.subgroupOf H) := IsNilpotent.to_isSolvable
  by_contra hHN
  obtain ⟨h, hhH, hhN⟩ := SetLike.not_le_iff_exists.mp hHN
  have hnt : Nontrivial (↥H ⧸ N.subgroupOf H) := by
    refine ⟨⟨π ⟨h, hhH⟩, 1, ?_⟩⟩
    intro hEq
    apply hhN
    have hmem : (⟨h, hhH⟩ : ↥H) ∈ N.subgroupOf H :=
      (QuotientGroup.eq_one_iff (⟨h, hhH⟩ : ↥H)).mp hEq
    exact Subgroup.mem_subgroupOf.mp hmem
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H ⧸ N.subgroupOf H)
  rw [hcomm] at hlt
  exact lt_irrefl _ hlt

private theorem le_of_isLeviFamily_of_normal
    {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily P d L) (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 P = L i)
    {N : Subgroup Q} (hNle : N ≤ P) (hNnormal : (N.subgroupOf P).Normal)
    (hON : pCoreOf 2 P ≤ N) (l : Fin d)
    (hnot : ¬ ⁅N, L l⁆ ≤ pCoreOf 2 P) : L l ≤ N := by
  let O := pCoreOf 2 P
  let N' : Subgroup Q := ⁅L l, N⁆ ⊔ O
  have hLlP : L l ≤ P := hL.le l
  have hN_normalizer_Ll : N ≤ normalizer (L l : Set Q) :=
    hNle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLlP).mp (hL.normal l))
  have hLl_normalizer_N : L l ≤ normalizer (N : Set Q) :=
    hLlP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp hNnormal)
  have hN'le_Ll : N' ≤ L l := by
    refine sup_le ?_ (hL.pCoreOf_le l)
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hN_normalizer_Ll
  have hN'le_N : N' ≤ N := by
    refine sup_le ?_ hON
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hLl_normalizer_N
  have hN'normal : (N'.subgroupOf (L l)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN'le_Ll]
    refine (le_inf ?_ ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup (⁅L l, N⁆) O)
    · exact Subgroup.normalizer_commutator_ge_left (L l) N
    · exact hLlP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hnotN' : ¬ ⁅N', L l⁆ ≤ O := by
    intro h
    have hdouble : ⁅⁅L l, N⁆, L l⁆ ≤ CFSG.Open.pCoreOf 2 (L l) := by
      rw [hL.pCoreOf_eq l]
      exact (Subgroup.commutator_mono le_sup_left le_rfl).trans h
    have hcomm := CFSG.GroupTheory.commutator_le_pCoreOf_of_commutator_commutator_le
      (hL.opp_eq l) hN_normalizer_Ll hdouble
    rw [hL.pCoreOf_eq l] at hcomm
    refine hnot ?_
    rw [Subgroup.commutator_comm N (L l)]
    exact hcomm
  have hO2' : CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo (L l) ≤ N' :=
    hL.tits l N' le_sup_right hN'le_Ll hN'normal hnotN'
  have hO2N : CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo (L l) ≤ N :=
    hO2'.trans hN'le_N
  have hO_le_Ll : O ≤ L l := hL.pCoreOf_le l
  have hnew_normal : ((N ⊓ L l).subgroupOf (L l)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    refine (le_inf hLl_normalizer_N le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hnew : L l ≤ N ⊓ L l :=
    le_of_oUpperTwo_le_of_commutator_sup inf_le_right hO_le_Ll (le_inf hON hO_le_Ll)
      hnew_normal (hperf l) (le_inf hO2N (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.oUpperTwo_le (L l)))
  exact hnew.trans inf_le_left



private theorem odd_card_quotient_of_le_center
    {K M O : Subgroup Q} (_hOM : O ≤ M) (hMK : M ≤ K)
    (_hMnormal : (M.subgroupOf K).Normal) (hOK : O ≤ K)
    (_hOnormal : (O.subgroupOf K).Normal) (hcent : ⁅M, K⁆ ≤ O)
    (hcore : CFSG.Open.pCoreOf 2 K = O) :
    Odd (Nat.card (M ⧸ O.subgroupOf M)) := by
  let G := ↥K
  let O' : Subgroup G := CFSG.pCore 2 G
  have hpc : O' = O.subgroupOf K := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le hOK]
    exact hcore
  let π : G →* (G ⧸ O') := QuotientGroup.mk' O'
  have hquot : CFSG.pCore 2 (G ⧸ O') = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hoddZ : Odd (Nat.card (Subgroup.center (G ⧸ O'))) :=
    CFSG.Quasithin.SteinbergCD.odd_card_center_of_pCore_eq_bot hquot
  let incl : ↥M →* G := Subgroup.inclusion hMK
  let f : ↥M →* (G ⧸ O') := π.comp incl
  have hMtop : ⁅M.subgroupOf K, (⊤ : Subgroup G)⁆ ≤ O' := by
    rw [hpc, Subgroup.commutator_le]
    intro m hm k _
    rw [Subgroup.mem_subgroupOf]
    exact hcent (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hm) k.2)
  have hrange_center : f.range ≤ Subgroup.center (G ⧸ O') := by
    have hmapbot : ⁅(M.subgroupOf K).map π, (⊤ : Subgroup (G ⧸ O'))⁆ = ⊥ := by
      have hmap := Subgroup.map_commutator (H₁ := M.subgroupOf K) (H₂ := (⊤ : Subgroup G)) π
      rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O')] at hmap
      rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hMtop
    have hrange_le : f.range ≤ (M.subgroupOf K).map π := by
      rintro _ ⟨x, rfl⟩
      refine Subgroup.mem_map_of_mem π ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact x.2
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm : ⁅x, y⁆ = 1 := by
      have hle := (le_of_eq hmapbot : ⁅(M.subgroupOf K).map π, ⊤⁆ ≤ ⊥)
      have hmem := Subgroup.commutator_le.mp hle x (hrange_le hx) y (Subgroup.mem_top y)
      simpa using hmem
    have hmul : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.mp hcomm
    exact hmul.symm
  have hker : f.ker = O.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker]
    change π (incl x) = 1 ↔ x ∈ O.subgroupOf M
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hpc,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hoddRange : Odd (Nat.card f.range) :=
    hoddZ.of_dvd_nat (Subgroup.card_dvd_of_le hrange_center)
  have hcard : Nat.card (M ⧸ O.subgroupOf M) = Nat.card f.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hcard]
  exact hoddRange

private def badSet (P N : Subgroup Q) {d : ℕ} (L : Fin d → Subgroup Q) : Set (Fin d) :=
  {l | ¬ ⁅N, L l⁆ ≤ pCoreOf 2 P}

private noncomputable def badPart (P N : Subgroup Q) {d : ℕ} (L : Fin d → Subgroup Q) :
    Fin d → Subgroup Q := by
  classical
  exact fun l => if l ∈ badSet P N L then L l else ⊥

private noncomputable def badTf (P N : Subgroup Q) {d : ℕ} (L : Fin d → Subgroup Q) :
    Fin d → Subgroup Q := by
  classical
  exact fun l => if l ∈ badSet P N L then pCoreOf 2 P else L l

omit [Finite Q] in
private theorem badSet_K0_le
    {P N O N0 T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Mf Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L)
    (hMf : Mf = badPart P N L) (hTf : Tf = badTf P N L)
    (hN0 : N0 = O ⊔ ⨆ l, Mf l) (hT : T = ⨆ l, Tf l)
    (hL : IsLeviFamily P d L) :
    Opp 2 P ⊔ O ≤ N0 ⊔ T := by
  classical
  have hM_of_mem {l : Fin d} (hl : l ∈ S) : Mf l = L l := by
    rw [hMf]
    have hlb : l ∈ badSet P N L := by simpa only [hS] using hl
    simp [badPart, hlb]
  have hT_of_mem {l : Fin d} (hl : l ∈ S) : Tf l = O := by
    rw [hTf]
    have hlb : l ∈ badSet P N L := by simpa only [hS] using hl
    simp [badTf, hlb]
    exact hO.symm
  have hM_of_not {l : Fin d} (hl : l ∉ S) : Mf l = ⊥ := by
    rw [hMf]
    have hlb : l ∉ badSet P N L := by simpa only [hS] using hl
    simp [badPart, hlb]
  have hT_of_not {l : Fin d} (hl : l ∉ S) : Tf l = L l := by
    rw [hTf]
    have hlb : l ∉ badSet P N L := by simpa only [hS] using hl
    simp [badTf, hlb]
  have hLl_eq : ∀ l, L l = Mf l ⊔ Tf l := by
    intro l
    by_cases hl : l ∈ S
    · rw [hM_of_mem hl, hT_of_mem hl, sup_eq_left.mpr (hO ▸ hL.pCoreOf_le l)]
    · rw [hM_of_not hl, hT_of_not hl, bot_sup_eq]
  rw [hN0, hT, hO, ← hL.iSup_eq]
  refine iSup_le fun l => ?_
  rw [hLl_eq l]
  exact sup_le (((le_iSup Mf l).trans le_sup_right).trans le_sup_left)
    ((le_iSup Tf l).trans le_sup_right)

private theorem badSet_K0_ge
    {P N O N0 T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Mf Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L)
    (hMf : Mf = badPart P N L) (hTf : Tf = badTf P N L)
    (hN0 : N0 = O ⊔ ⨆ l, Mf l) (hT : T = ⨆ l, Tf l)
    (hL : IsLeviFamily P d L) :
    N0 ⊔ T ≤ Opp 2 P ⊔ O := by
  classical
  have hM_of_mem {l : Fin d} (hl : l ∈ S) : Mf l = L l := by
    rw [hMf]
    have hlb : l ∈ badSet P N L := by simpa only [hS] using hl
    simp [badPart, hlb]
  have hT_of_mem {l : Fin d} (hl : l ∈ S) : Tf l = O := by
    rw [hTf]
    have hlb : l ∈ badSet P N L := by simpa only [hS] using hl
    simp [badTf, hlb]
    exact hO.symm
  have hM_of_not {l : Fin d} (hl : l ∉ S) : Mf l = ⊥ := by
    rw [hMf]
    have hlb : l ∉ badSet P N L := by simpa only [hS] using hl
    simp [badPart, hlb]
  have hT_of_not {l : Fin d} (hl : l ∉ S) : Tf l = L l := by
    rw [hTf]
    have hlb : l ∉ badSet P N L := by simpa only [hS] using hl
    simp [badTf, hlb]
  have hLleK0 : ∀ l, L l ≤ Opp 2 P ⊔ O := fun l => (hL.le_opp l).trans le_sup_left
  rw [hN0, hT]
  refine sup_le ?_ ?_
  · refine sup_le le_sup_right ?_
    exact iSup_le fun l => by
      by_cases hl : l ∈ S
      · rw [hM_of_mem hl]; exact hLleK0 l
      · rw [hM_of_not hl]; exact bot_le
  · exact iSup_le fun l => by
      by_cases hl : l ∈ S
      · rw [hT_of_mem hl]; exact le_sup_right
      · rw [hT_of_not hl]; exact hLleK0 l

private theorem badSet_K0_eq
    {P N O N0 T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Mf Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L)
    (hMf : Mf = badPart P N L) (hTf : Tf = badTf P N L)
    (hN0 : N0 = O ⊔ ⨆ l, Mf l) (hT : T = ⨆ l, Tf l)
    (hL : IsLeviFamily P d L) :
    Opp 2 P ⊔ O = N0 ⊔ T :=
  le_antisymm (badSet_K0_le hO hS hMf hTf hN0 hT hL)
    (badSet_K0_ge hO hS hMf hTf hN0 hT hL)

omit [Finite Q] in
private theorem badSet_N0_normal
    {P N O N0 : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Mf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (hMf : Mf = badPart P N L)
    (hN0 : N0 = O ⊔ ⨆ l, Mf l) (hL : IsLeviFamily P d L) :
    N0 ≤ P ∧ (N0.subgroupOf P).Normal := by
  classical
  have hM_of_mem {l : Fin d} (hl : l ∈ S) : Mf l = L l := by
    rw [hMf]
    have hlb : l ∈ badSet P N L := by simpa [hS] using hl
    simp [badPart, hlb]
  have hM_of_not {l : Fin d} (hl : l ∉ S) : Mf l = ⊥ := by
    rw [hMf]
    have hlb : l ∉ badSet P N L := by simpa [hS] using hl
    simp [badPart, hlb]
  have hPnormO : P ≤ normalizer (O : Set Q) := hO ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hPnormM : ∀ l, P ≤ normalizer (Mf l : Set Q) := by
    intro l
    by_cases hl : l ∈ S
    · rw [hM_of_mem hl]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le l)).mp (hL.normal l)
    · rw [hM_of_not hl, Subgroup.normalizer_eq_top]
      exact le_top
  have hOleP : O ≤ P := hO.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hMleP : ∀ l, Mf l ≤ P := by
    intro l
    by_cases hl : l ∈ S
    · rw [hM_of_mem hl]; exact hL.le l
    · rw [hM_of_not hl]; exact bot_le
  have hN0leP : N0 ≤ P := by rw [hN0]; exact sup_le hOleP (iSup_le hMleP)
  refine ⟨hN0leP, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN0leP, hN0]
  refine (le_inf hPnormO ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup O (⨆ l, Mf l))
  exact (le_iInf hPnormM).trans (Subgroup.iInf_normalizer_le_normalizer_iSup Mf)

omit [Finite Q] in
private theorem badSet_T_normal
    {P N T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {Tf : Fin d → Subgroup Q}
    (hTf : Tf = badTf P N L) (hT : T = ⨆ l, Tf l) (hL : IsLeviFamily P d L) :
    T ≤ P ∧ (T.subgroupOf P).Normal := by
  classical
  have hOleP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPnormO : P ≤ normalizer (pCoreOf 2 P : Set Q) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hT_of_mem {l : Fin d} (hl : l ∈ badSet P N L) : Tf l = pCoreOf 2 P := by
    rw [hTf]; simp [badTf, hl]
  have hT_of_not {l : Fin d} (hl : l ∉ badSet P N L) : Tf l = L l := by
    rw [hTf]; simp [badTf, hl]
  have hTleP : T ≤ P := by
    rw [hT]
    exact iSup_le fun l => by
      by_cases hl : l ∈ badSet P N L
      · rw [hT_of_mem hl]; exact hOleP
      · rw [hT_of_not hl]; exact hL.le l
  refine ⟨hTleP, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTleP, hT]
  refine (le_iInf fun l => ?_).trans (Subgroup.iInf_normalizer_le_normalizer_iSup Tf)
  by_cases hl : l ∈ badSet P N L
  · rw [hT_of_mem hl]; exact hPnormO
  · rw [hT_of_not hl]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le l)).mp (hL.normal l)

omit [Finite Q] in
private theorem badSet_M_normal
    {P N T : Subgroup Q}
    (hNle : N ≤ P) (hNnormal : (N.subgroupOf P).Normal)
    (hTleP : T ≤ P) (hTnormalP : (T.subgroupOf P).Normal) :
    ((N ⊓ T).subgroupOf P).Normal := by
  have hMleP : N ⊓ T ≤ P := inf_le_left.trans hNle
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMleP]
  refine (le_inf ?_ ?_).trans (Subgroup.inf_normalizer_le_normalizer_inf)
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp hNnormal
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTleP).mp hTnormalP

private theorem badSet_N0_le_N
    {P N O N0 : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Mf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (hMf : Mf = badPart P N L)
    (hN0 : N0 = O ⊔ ⨆ l, Mf l)
    (hL : IsLeviFamily P d L) (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 P = L i)
    (hNle : N ≤ P) (hNnormal : (N.subgroupOf P).Normal) (hON : pCoreOf 2 P ≤ N) :
    N0 ≤ N := by
  classical
  rw [hN0]
  refine sup_le (hO ▸ hON) (iSup_le fun l => ?_)
  by_cases hl : l ∈ S
  · have hMl : Mf l = L l := by
      rw [hMf]
      have hlb : l ∈ badSet P N L := by simpa [hS] using hl
      simp [badPart, hlb]
    rw [hMl]
    have hlb : l ∈ badSet P N L := by simpa only [hS] using hl
    exact le_of_isLeviFamily_of_normal hL hperf hNle hNnormal hON l hlb
  · have hMl : Mf l = ⊥ := by
      rw [hMf]
      have hlb : l ∉ badSet P N L := by simpa [hS] using hl
      simp [badPart, hlb]
    rw [hMl]; exact bot_le

private theorem badSet_decomp
    {P N O N0 T : Subgroup Q}
    (hO : O = pCoreOf 2 P) (hNopp : N = Opp 2 N ⊔ pCoreOf 2 P)
    (hNle : N ≤ P) :
    N0 ≤ N → (N0.subgroupOf P).Normal → N0 ≤ P → T ≤ P →
      Opp 2 P ⊔ O = N0 ⊔ T → N = N0 ⊔ (N ⊓ T) := by
  intro hN0_le_N hN0normalP hN0leP hTleP hK0_eq
  have hTnormN0 : T ≤ normalizer (N0 : Set Q) :=
    le_trans hTleP ((Subgroup.normal_subgroupOf_iff_le_normalizer hN0leP).mp hN0normalP)
  have hOpp_mono : Opp 2 N ≤ Opp 2 P := by
    simpa [Opp] using s13_Thirteen2_pElementSubgroup_mono (p := 2) hNle
  have hNopp' : N = Opp 2 N ⊔ O := by rwa [← hO] at hNopp
  have hN_le_K0 : N ≤ Opp 2 P ⊔ O := by
    rw [hNopp']
    exact sup_le (le_trans hOpp_mono le_sup_left) le_sup_right
  have hNle' : N ≤ N0 ⊔ T := by rw [← hK0_eq]; exact hN_le_K0
  have h := Subgroup.inf_sup_assoc_of_le (H := T) (K := N) (N := N0) hTnormN0 hN0_le_N
  rw [sup_comm, sup_comm T N0, inf_eq_left.mpr hNle'] at h
  exact h.symm

private theorem badSet_pCore_K0 {P O : Subgroup Q} (hO : O = pCoreOf 2 P) :
    CFSG.Open.pCoreOf 2 (Opp 2 P ⊔ O) = O := by
  have hOleP : O ≤ P := hO.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hK0leP : Opp 2 P ⊔ O ≤ P := sup_le (close16_opp_le 2 P) hOleP
  have hPnormO : P ≤ normalizer (O : Set Q) := hO ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hK0normalP : ((Opp 2 P ⊔ O).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK0leP]
    refine ((le_inf ?_ hPnormO).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (Opp 2 P) O))
    intro g hg
    exact close16_mem_normalizer_opp 2 (Subgroup.le_normalizer hg)
  have hOleK0 : pCoreOf 2 P ≤ Opp 2 P ⊔ O := hO ▸ le_sup_right
  exact (CFSG.GroupTheory.pCoreOf_eq_of_le_of_normal 2 hK0leP hK0normalP hOleK0).trans hO.symm

omit [Finite Q] in
private theorem badSet_T_L
    {P N O T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (hTf : Tf = badTf P N L)
    (hT : T = ⨆ l, Tf l) (hL : IsLeviFamily P d L) :
    ∀ {l : Fin d}, l ∈ S → ⁅T, L l⁆ ≤ O := by
  classical
  have hPnormO : P ≤ normalizer (O : Set Q) := hO ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hKL : ∀ l, L l ≤ normalizer (O : Set Q) := fun l => (hL.le l).trans hPnormO
  have hT_of_mem {l : Fin d} (hl : l ∈ S) : Tf l = O := by
    rw [hTf]
    have hlb : l ∈ badSet P N L := by simpa only [hS] using hl
    simp [badTf, hlb]
    exact hO.symm
  have hT_of_not {l : Fin d} (hl : l ∉ S) : Tf l = L l := by
    rw [hTf]
    have hlb : l ∉ badSet P N L := by simpa only [hS] using hl
    simp [badTf, hlb]
  intro l hl
  rw [hT]
  refine CFSG.Quasithin.MS93.S59.commutator_iSup_le (K := Tf) ?_ ?_
  · intro m
    by_cases hm : m ∈ S
    · rw [hT_of_mem hm]; exact Subgroup.le_normalizer
    · rw [hT_of_not hm]; exact hKL m
  · intro m
    by_cases hm : m ∈ S
    · rw [hT_of_mem hm]
      exact (Subgroup.le_normalizer_iff_commutator_le_left).mp (hKL l)
    · rw [hT_of_not hm, hO]
      exact hL.commutator_le m l (fun h => hm (h ▸ hl))

omit [Finite Q] in
private theorem badSet_central_LM
    {P N O T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (_hL : IsLeviFamily P d L)
    (hTL : ∀ {l : Fin d}, l ∈ S → ⁅T, L l⁆ ≤ O) :
    ∀ l, ⁅L l, N ⊓ T⁆ ≤ O := by
  intro l
  by_cases hl : l ∈ S
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono inf_le_right le_rfl).trans (hTL hl)
  · rw [Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono inf_le_left le_rfl).trans ?_
    rw [hO]
    by_contra hcon
    exact hl (by rw [hS]; exact hcon)

omit [Finite Q] in
private theorem badSet_central
    {P N O T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (hTf : Tf = badTf P N L)
    (hT : T = ⨆ l, Tf l) (hL : IsLeviFamily P d L) :
    ⁅N ⊓ T, Opp 2 P ⊔ O⁆ ≤ O := by
  have hPnormO : P ≤ normalizer (O : Set Q) := hO ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hKL : ∀ l, L l ≤ normalizer (O : Set Q) := fun l => (hL.le l).trans hPnormO
  have hTL : ∀ {l : Fin d}, l ∈ S → ⁅T, L l⁆ ≤ O := badSet_T_L hO hS hTf hT hL
  have hLM : ∀ l, ⁅L l, N ⊓ T⁆ ≤ O := badSet_central_LM hO hS hL hTL
  have hsup : ⁅⨆ l, L l, N ⊓ T⁆ ≤ O :=
    CFSG.Quasithin.MS93.S59.commutator_iSup_le (K := L) (A := N ⊓ T) (N := O) hKL hLM
  rw [hL.iSup_eq] at hsup
  have hK0O : Opp 2 P ⊔ O = Opp 2 P ⊔ pCoreOf 2 P := by rw [hO]
  rw [hK0O, Subgroup.commutator_comm (N ⊓ T) (Opp 2 P ⊔ pCoreOf 2 P)]
  exact hsup

private theorem badSet_N_le_K0
    {P N O : Subgroup Q} (hO : O = pCoreOf 2 P)
    (hNopp : N = Opp 2 N ⊔ pCoreOf 2 P) (hNle : N ≤ P) :
    N ≤ Opp 2 P ⊔ O := by
  have hOpp_mono : Opp 2 N ≤ Opp 2 P := by
    simpa [Opp] using s13_Thirteen2_pElementSubgroup_mono (p := 2) hNle
  have hNopp' : N = Opp 2 N ⊔ O := by rwa [← hO] at hNopp
  rw [hNopp']
  exact sup_le (le_trans hOpp_mono le_sup_left) le_sup_right

omit [Finite Q] in
private theorem badSet_O_le_T
    {P N O T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {Tf : Fin d → Subgroup Q} (hO : O = pCoreOf 2 P) (hTf : Tf = badTf P N L)
    (hT : T = ⨆ l, Tf l) (hL : IsLeviFamily P d L) (hd : Nonempty (Fin d)) :
    O ≤ T := by
  obtain ⟨l0⟩ := hd
  have h : Tf l0 ≤ T := hT ▸ le_iSup Tf l0
  by_cases hl0 : l0 ∈ badSet P N L
  · have h1 : Tf l0 = pCoreOf 2 P := by rw [hTf]; simp [badTf, hl0]
    rw [h1] at h
    rw [hO]
    exact h
  · have h1 : Tf l0 = L l0 := by rw [hTf]; simp [badTf, hl0]
    rw [h1] at h
    rw [hO]
    exact (hL.pCoreOf_le l0).trans h

omit [Finite Q] in
private theorem badSet_pow_mem
    {P N O T : Subgroup Q} {m : ℕ}
    (hOM : O ≤ N ⊓ T) (hMleP : N ⊓ T ≤ P) (hPnormO : P ≤ normalizer (O : Set Q))
    (hm : m = Nat.card (↥(N ⊓ T) ⧸ O.subgroupOf (N ⊓ T))) :
    ∀ u ∈ N ⊓ T, u ^ m ∈ O := by
  intro u hu
  have : (O.subgroupOf (N ⊓ T)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOM]
    exact hMleP.trans hPnormO
  have hq : ((QuotientGroup.mk' (O.subgroupOf (N ⊓ T)) ⟨u, hu⟩) ^ m) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    have hdvd := Subgroup.orderOf_dvd_natCard
      (s := (⊤ : Subgroup (↥(N ⊓ T) ⧸ O.subgroupOf (N ⊓ T))))
      (x := QuotientGroup.mk' (O.subgroupOf (N ⊓ T)) ⟨u, hu⟩) (Subgroup.mem_top _)
    simpa [hm] using hdvd
  have hq' : QuotientGroup.mk' (O.subgroupOf (N ⊓ T)) (⟨u, hu⟩ ^ m) = 1 := by
    simpa only [map_pow] using hq
  have hmem : (⟨u, hu⟩ : ↥(N ⊓ T)) ^ m ∈ O.subgroupOf (N ⊓ T) :=
    (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using hq')
  simpa using Subgroup.mem_subgroupOf.mp hmem

omit [Finite Q] in
private theorem badSet_two_mem_setup
    {P N N0 T : Subgroup Q}
    (hNle : N ≤ P) (hN0_le_N : N0 ≤ N) (hN0leP : N0 ≤ P)
    (hN0normalP : (N0.subgroupOf P).Normal) (hMnormalP : ((N ⊓ T).subgroupOf P).Normal)
    (hN_decomp : N = N0 ⊔ (N ⊓ T)) :
    (N0.subgroupOf N).Normal ∧ ((N ⊓ T).subgroupOf N).Normal ∧
      (⊤ : Subgroup ↥N) = N0.subgroupOf N ⊔ (N ⊓ T).subgroupOf N := by
  have hN0normalN : (N0.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0_le_N).mpr
      (hNle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hN0leP).mp hN0normalP))
  have hMleP : N ⊓ T ≤ P := inf_le_left.trans hNle
  have hMnormalN : ((N ⊓ T).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (hNle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMleP).mp hMnormalP))
  have hdecomp : (⊤ : Subgroup ↥N) = N0.subgroupOf N ⊔ (N ⊓ T).subgroupOf N := by
    have h1 : (N0 ⊔ (N ⊓ T)).subgroupOf N = N0.subgroupOf N ⊔ (N ⊓ T).subgroupOf N :=
      Subgroup.subgroupOf_sup hN0_le_N inf_le_left
    rw [← hN_decomp, Subgroup.subgroupOf_self] at h1
    exact h1
  exact ⟨hN0normalN, hMnormalN, hdecomp⟩

private theorem quotient_mk_eq_one_of_odd_card
    {G : Type} [Group G] [Finite G] {K : Subgroup G} [K.Normal]
    {m k : ℕ} (hm : Odd m) {x t : G}
    (hxt : QuotientGroup.mk' K x = QuotientGroup.mk' K t)
    (hx : x ^ m ∈ K) (ht : t ^ 2 ^ k = 1) :
    QuotientGroup.mk' K x = 1 := by
  have hq_m : (QuotientGroup.mk' K x) ^ m = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  have hq2 : (QuotientGroup.mk' K x) ^ 2 ^ k = 1 := by
    rw [hxt, ← map_pow, ht, map_one]
  have hdm := orderOf_dvd_of_pow_eq_one hq_m
  have hd2 := orderOf_dvd_of_pow_eq_one hq2
  have hcop : Nat.Coprime m (2 ^ k) := (hm.coprime_two_right).pow_right k
  rw [← orderOf_eq_one_iff, Nat.eq_one_of_dvd_coprimes hcop hdm hd2]

private theorem badSet_two_mem
    {P N O N0 T : Subgroup Q} {m : ℕ}
    (hNle : N ≤ P) (hN0_le_N : N0 ≤ N) (hN0leP : N0 ≤ P)
    (hN0normalP : (N0.subgroupOf P).Normal) (hMnormalP : ((N ⊓ T).subgroupOf P).Normal)
    (hN_decomp : N = N0 ⊔ (N ⊓ T)) (hO_le_N0 : O ≤ N0)
    (hm_odd : Odd m) (hpowO : ∀ u ∈ N ⊓ T, u ^ m ∈ O) :
    ∀ t ∈ N, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ∈ N0 := by
  obtain ⟨hN0normalN, hMnormalN, hdecomp⟩ :=
    badSet_two_mem_setup hNle hN0_le_N hN0leP hN0normalP hMnormalP hN_decomp
  intro t ht ht2
  obtain ⟨k, hk⟩ := ht2
  have : N0.subgroupOf N |>.Normal := hN0normalN
  have : (N ⊓ T).subgroupOf N |>.Normal := hMnormalN
  let tG : ↥N := ⟨t, ht⟩
  have htGmem : tG ∈ (⊤ : Subgroup ↥N) := Subgroup.mem_top tG
  rw [hdecomp, Subgroup.mem_sup_of_normal_right] at htGmem
  obtain ⟨a, ha, u, hu, hau⟩ := htGmem
  have haN0 : (a : Q) ∈ N0 := Subgroup.mem_subgroupOf.mp ha
  have huM : (u : Q) ∈ N ⊓ T := Subgroup.mem_subgroupOf.mp hu
  have hau' : (a : Q) * (u : Q) = t := by
    have h := congrArg (fun x : ↥N => (x : Q)) hau
    change (a : Q) * (u : Q) = (tG : Q) at h
    exact h
  let q : ↥N →* (↥N ⧸ N0.subgroupOf N) := QuotientGroup.mk' (N0.subgroupOf N)
  have hu_pow : ((u : Q) ^ m) ∈ O := hpowO (u : Q) huM
  have huN0 : (u : ↥N) ^ m ∈ N0.subgroupOf N := by
    rw [Subgroup.mem_subgroupOf]
    change ((u : Q) ^ m) ∈ N0
    exact hO_le_N0 hu_pow
  have ha1 : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  have hqt_eq : q u = q tG := by rw [← hau, map_mul, ha1, one_mul]
  have htGpow : tG ^ 2 ^ k = 1 := by
    apply Subtype.ext
    change t ^ 2 ^ k = 1
    exact hk
  have hqu1 : q u = 1 :=
    quotient_mk_eq_one_of_odd_card (K := N0.subgroupOf N) hm_odd hqt_eq huN0 htGpow
  have huN0' : u ∈ N0.subgroupOf N :=
    (QuotientGroup.eq_one_iff u).mp (by simpa [q, QuotientGroup.mk'_apply] using hqu1)
  have huN0 : (u : Q) ∈ N0 := Subgroup.mem_subgroupOf.mp huN0'
  rw [← hau']
  exact N0.mul_mem haN0 huN0

omit [Finite Q] in
private theorem badSet_opp_le
    {N N0 : Subgroup Q}
    (h2mem : ∀ t ∈ N, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ∈ N0) : Opp 2 N ≤ N0 := by
  rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
  refine (Subgroup.closure_le N0).2 ?_
  rintro x ⟨hxN, k, hxk⟩
  exact h2mem x hxN ⟨k, by rw [← hxk]; exact pow_orderOf_eq_one x⟩

private theorem badSet_odd
    {P N O T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (hTf : Tf = badTf P N L)
    (hT : T = ⨆ l, Tf l) (hL : IsLeviFamily P d L)
    (hNopp : N = Opp 2 N ⊔ pCoreOf 2 P) (hNle : N ≤ P)
    (hOM : O ≤ N ⊓ T) (hMnormalP : ((N ⊓ T).subgroupOf P).Normal) :
    Odd (Nat.card (↥(N ⊓ T) ⧸ O.subgroupOf (N ⊓ T))) := by
  have hMleP : N ⊓ T ≤ P := inf_le_left.trans hNle
  have hNleK0 : N ≤ Opp 2 P ⊔ O := badSet_N_le_K0 hO hNopp hNle
  have hMleK0 : N ⊓ T ≤ Opp 2 P ⊔ O := inf_le_left.trans hNleK0
  have hK0leP : Opp 2 P ⊔ O ≤ P := by
    refine sup_le (close16_opp_le 2 P) ?_
    rw [hO]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPnormO : P ≤ normalizer (O : Set Q) := hO ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hMnormalK : ((N ⊓ T).subgroupOf (Opp 2 P ⊔ O)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMleK0]
    exact hK0leP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMleP).mp hMnormalP)
  have hOnormalK : (O.subgroupOf (Opp 2 P ⊔ O)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : O ≤ Opp 2 P ⊔ O)]
    exact hK0leP.trans hPnormO
  have hcent : ⁅N ⊓ T, Opp 2 P ⊔ O⁆ ≤ O :=
    badSet_central hO hS hTf hT hL
  have hcoreK : CFSG.Open.pCoreOf 2 (Opp 2 P ⊔ O) = O := badSet_pCore_K0 hO
  exact odd_card_quotient_of_le_center hOM hMleK0 hMnormalK (le_sup_right : O ≤ Opp 2 P ⊔ O)
    hOnormalK hcent hcoreK

private theorem badSet_pow_and_odd
    {P N O T : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {S : Set (Fin d)} {Tf : Fin d → Subgroup Q}
    (hO : O = pCoreOf 2 P) (hS : S = badSet P N L) (hTf : Tf = badTf P N L)
    (hT : T = ⨆ l, Tf l) (hL : IsLeviFamily P d L) (hNopp : N = Opp 2 N ⊔ pCoreOf 2 P)
    (hNle : N ≤ P) (hON : pCoreOf 2 P ≤ N)
    (hMnormalP : ((N ⊓ T).subgroupOf P).Normal) (hd : Nonempty (Fin d)) :
    (∀ u ∈ N ⊓ T, u ^ Nat.card (↥(N ⊓ T) ⧸ O.subgroupOf (N ⊓ T)) ∈ O) ∧
      Odd (Nat.card (↥(N ⊓ T) ⧸ O.subgroupOf (N ⊓ T))) := by
  have hOleT : O ≤ T := badSet_O_le_T hO hTf hT hL hd
  have hOleM : O ≤ N ⊓ T := le_inf (hO ▸ hON) hOleT
  have hPnormO : P ≤ normalizer (O : Set Q) := by
    rw [hO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  refine ⟨badSet_pow_mem hOleM (inf_le_left.trans hNle) hPnormO rfl, ?_⟩
  exact badSet_odd hO hS hTf hT hL hNopp hNle hOleM hMnormalP

private theorem le_sup_badSet
    {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily P d L) (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 P = L i)
    {N : Subgroup Q} (hNle : N ≤ P) (hNnormal : (N.subgroupOf P).Normal)
    (hON : pCoreOf 2 P ≤ N) (hNopp : N = Opp 2 N ⊔ pCoreOf 2 P)
    (hd : Nonempty (Fin d)) :
    N ≤ pCoreOf 2 P ⊔ ⨆ l, badPart P N L l := by
  classical
  let O := pCoreOf 2 P
  let S : Set (Fin d) := badSet P N L
  let Mf : Fin d → Subgroup Q := badPart P N L
  let Tf : Fin d → Subgroup Q := badTf P N L
  let N0 : Subgroup Q := O ⊔ ⨆ l, Mf l
  let T : Subgroup Q := ⨆ l, Tf l
  have hN0P : N0 ≤ P ∧ (N0.subgroupOf P).Normal :=
    badSet_N0_normal (hO := rfl) (hS := rfl) (hMf := rfl) (hN0 := rfl) hL
  have hTP : T ≤ P ∧ (T.subgroupOf P).Normal :=
    badSet_T_normal (hTf := rfl) (hT := rfl) hL
  have hMnormalP : ((N ⊓ T).subgroupOf P).Normal :=
    badSet_M_normal hNle hNnormal hTP.1 hTP.2
  have hN0leN : N0 ≤ N :=
    badSet_N0_le_N (hO := rfl) (hS := rfl) (hMf := rfl) (hN0 := rfl) hL hperf hNle hNnormal hON
  have hK0eq : Opp 2 P ⊔ O = N0 ⊔ T :=
    badSet_K0_eq (hO := rfl) (hS := rfl) (hMf := rfl) (hTf := rfl) (hN0 := rfl) (hT := rfl) hL
  have hNdecomp : N = N0 ⊔ (N ⊓ T) :=
    badSet_decomp (hO := rfl) hNopp hNle hN0leN hN0P.2 hN0P.1 hTP.1 hK0eq
  obtain ⟨hpowO, hm_odd⟩ :=
    badSet_pow_and_odd (hO := rfl) (hS := rfl) (hTf := rfl) (hT := rfl) hL hNopp hNle hON
      hMnormalP hd
  have h2mem : ∀ t ∈ N, (∃ k : ℕ, t ^ 2 ^ k = 1) → t ∈ N0 :=
    badSet_two_mem hNle hN0leN hN0P.1 hN0P.2 hMnormalP hNdecomp
      (le_sup_left : O ≤ N0) hm_odd hpowO
  change N ≤ N0
  rw [show N = Opp 2 N ⊔ O from hNopp]
  exact sup_le (badSet_opp_le h2mem) (le_sup_left : O ≤ N0)

private theorem le_badPart_sup
    {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily P d L) (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 P = L i)
    {N : Subgroup Q} (hNle : N ≤ P) (hNnormal : (N.subgroupOf P).Normal)
    (hON : pCoreOf 2 P ≤ N) :
    pCoreOf 2 P ⊔ ⨆ l, badPart P N L l ≤ N := by
  classical
  let O := pCoreOf 2 P
  let S : Set (Fin d) := badSet P N L
  let Mf : Fin d → Subgroup Q := badPart P N L
  refine sup_le hON (iSup_le fun l => ?_)
  change Mf l ≤ N
  by_cases hl : l ∈ S
  · have hM : Mf l = L l := by simp [Mf, badPart, S, hl]
    rw [hM]
    exact le_of_isLeviFamily_of_normal hL hperf hNle hNnormal hON l
      (by simpa [S, badSet] using hl)
  · have hM : Mf l = ⊥ := by simp [Mf, badPart, S, hl]
    rw [hM]
    exact bot_le

private noncomputable def restPart (P N : Subgroup Q) {d : ℕ} (L : Fin d → Subgroup Q)
    (l0 : Fin d) : Fin d → Subgroup Q := by
  classical
  exact fun l => if l ∈ badSet P N L ∧ l ≠ l0 then L l else
    if l = l0 then pCoreOf 2 P else ⊥


omit [Finite Q] in
private theorem restPart_facts
    {P N : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q} (l0 : Fin d) :
    let Rf := restPart P N L l0
    Rf l0 = pCoreOf 2 P ∧
      (∀ l, l ∈ badSet P N L → l ≠ l0 → Rf l = L l) ∧
      (∀ l, l = l0 → Rf l = pCoreOf 2 P) ∧
      (∀ l, ¬(l ∈ badSet P N L ∧ l ≠ l0) → l ≠ l0 → Rf l = ⊥) := by
  classical
  let Rf : Fin d → Subgroup Q := restPart P N L l0
  have hRf_l0 : Rf l0 = pCoreOf 2 P := by
    have h1 : ¬ (l0 ∈ badSet P N L ∧ l0 ≠ l0) := fun h => h.2 rfl
    change restPart P N L l0 l0 = pCoreOf 2 P
    simp [restPart]
  have hRf_mem : ∀ l, l ∈ badSet P N L → l ≠ l0 → Rf l = L l := by
    intro l hl hne; simp [Rf, restPart, hl, hne]
  have hRf_mem_or : ∀ l, l = l0 → Rf l = pCoreOf 2 P := by
    intro l hl; rw [hl]; exact hRf_l0
  have hRf_not : ∀ l, ¬(l ∈ badSet P N L ∧ l ≠ l0) → l ≠ l0 → Rf l = ⊥ := by
    intro l h hne
    have hnb : l ∉ badSet P N L := fun hb => h ⟨hb, hne⟩
    simp [Rf, restPart, hnb, hne]
  exact ⟨hRf_l0, hRf_mem, hRf_mem_or, hRf_not⟩

private theorem restPart_opp {P N : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q} {l0 : Fin d}
    (hL : IsLeviFamily P d L) :
    (⨆ l, restPart P N L l0 l) = Opp 2 (⨆ l, restPart P N L l0 l) ⊔ pCoreOf 2 P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := pCoreOf 2 P
  let S : Set (Fin d) := badSet P N L
  let Rf : Fin d → Subgroup Q := restPart P N L l0
  let B : Subgroup Q := ⨆ l, Rf l
  have hRf_l0 : Rf l0 = O := by
    have h1 : ¬ (l0 ∈ S ∧ l0 ≠ l0) := fun h => h.2 rfl
    change restPart P N L l0 l0 = O
    simp [restPart]
    rfl
  have hRf_mem : ∀ l, l ∈ S → l ≠ l0 → Rf l = L l := by
    intro l hl hne; simp [Rf, restPart, S, hl, hne]
  have hRf_mem_or : ∀ l, l = l0 → Rf l = O := by
    intro l hl; subst hl; exact hRf_l0
  have hRf_not : ∀ l, ¬(l ∈ S ∧ l ≠ l0) → l ≠ l0 → Rf l = ⊥ := by
    intro l h hne
    have hnb : l ∉ badSet P N L := fun hb => h ⟨by simpa [S] using hb, hne⟩
    simp [Rf, restPart, hnb, hne]
  have hO_le_B : O ≤ B := by rw [← hRf_l0]; exact le_iSup Rf l0
  have hO_le_OppB : O ≤ Opp 2 B :=
    CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) hO_le_B
  refine le_antisymm ?_ (sup_le (close16_opp_le 2 B) hO_le_B)
  refine iSup_le fun l => ?_
  change Rf l ≤ Opp 2 B ⊔ pCoreOf 2 P
  by_cases h1 : l ∈ S ∧ l ≠ l0
  · rw [hRf_mem l h1.1 h1.2, hL.eq_opp_sup l]
    have hRlB : L l ≤ B := (hRf_mem l h1.1 h1.2).symm ▸ le_iSup Rf l
    have hmono : Opp 2 (L l) ≤ Opp 2 B := by
      simpa [Opp] using s13_Thirteen2_pElementSubgroup_mono (p := 2) hRlB
    exact sup_le (hmono.trans le_sup_left) le_sup_right
  · by_cases h2 : l = l0
    · rw [hRf_mem_or l h2]; exact le_sup_right
    · rw [hRf_not l h1 h2]; exact bot_le

omit [Finite Q] in
private theorem restPart_commutator {P N : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    {l0 : Fin d} (hL : IsLeviFamily P d L) :
    ⁅L l0, ⨆ l, restPart P N L l0 l⁆ ≤ pCoreOf 2 P := by
  classical
  let O := pCoreOf 2 P
  let S : Set (Fin d) := badSet P N L
  let Rf : Fin d → Subgroup Q := restPart P N L l0
  let A : Subgroup Q := L l0
  let B : Subgroup Q := ⨆ l, Rf l
  have hRf_mem : ∀ l, l ∈ S → l ≠ l0 → Rf l = L l := by
    intro l hl hne; simp [Rf, restPart, S, hl, hne]
  have hRf_mem_or : ∀ l, l = l0 → Rf l = O := by
    intro l hl
    rw [hl]
    have h1 : ¬ (l0 ∈ S ∧ l0 ≠ l0) := fun h => h.2 rfl
    change restPart P N L l0 l0 = O
    simp [restPart]
    rfl
  have hRf_not : ∀ l, ¬(l ∈ S ∧ l ≠ l0) → l ≠ l0 → Rf l = ⊥ := by
    intro l h hne
    have hnb : l ∉ badSet P N L := fun hb => h ⟨by simpa [S] using hb, hne⟩
    simp [Rf, restPart, hnb, hne]
  have hKL : ∀ l, L l ≤ normalizer (O : Set Q) := fun l =>
    (hL.le l).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hRf_norm : ∀ l, Rf l ≤ normalizer (O : Set Q) := by
    intro l
    by_cases h1 : l ∈ S ∧ l ≠ l0
    · rw [hRf_mem l h1.1 h1.2]
      exact (hL.le l).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    · by_cases h2 : l = l0
      · rw [hRf_mem_or l h2]; exact Subgroup.le_normalizer
      · rw [hRf_not l h1 h2]; exact bot_le
  have hRf_comm : ∀ l, ⁅Rf l, A⁆ ≤ O := by
    intro l
    by_cases h1 : l ∈ S ∧ l ≠ l0
    · rw [hRf_mem l h1.1 h1.2, show A = L l0 from rfl]
      exact hL.commutator_le l l0 h1.2
    · by_cases h2 : l = l0
      · rw [hRf_mem_or l h2, show A = L l0 from rfl]
        exact (Subgroup.le_normalizer_iff_commutator_le_left).mp (hKL l0)
      · rw [hRf_not l h1 h2]; simp
  have h : ⁅B, A⁆ ≤ O :=
    CFSG.Quasithin.MS93.S59.commutator_iSup_le (K := Rf) (A := A) (N := O) hRf_norm hRf_comm
  rwa [Subgroup.commutator_comm] at h

omit [Finite Q] in
private theorem badSet_nonempty
    {P N : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hNne : N ≠ pCoreOf 2 P)
    (hN_eq : N = pCoreOf 2 P ⊔ ⨆ l, badPart P N L l) :
    (badSet P N L).Nonempty := by
  classical
  by_contra hS
  have hSempty : badSet P N L = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
  have hsupbot : (⨆ l, badPart P N L l) = ⊥ := by
    refine iSup_eq_bot.mpr fun l => ?_
    simp [badPart, hSempty]
  have hN_eq_O : N = pCoreOf 2 P := by rw [hN_eq, hsupbot, sup_bot_eq]
  exact hNne hN_eq_O

private theorem exists_eq_of_isLeviFamily
    {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily P d L) (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 P = L i)
    {N : Subgroup Q} (hNle : N ≤ P) (hNnormal : (N.subgroupOf P).Normal)
    (hON : pCoreOf 2 P ≤ N) (hNopp : N = Opp 2 N ⊔ pCoreOf 2 P)
    (hNne : N ≠ pCoreOf 2 P)
    (hindec : ∀ A B : Subgroup Q, pCoreOf 2 P ≤ A → pCoreOf 2 P ≤ B →
      A = Opp 2 A ⊔ pCoreOf 2 P → B = Opp 2 B ⊔ pCoreOf 2 P →
      A ⊔ B = N → ⁅A, B⁆ ≤ pCoreOf 2 P → A = N ∨ B = N)
    (hd : Nonempty (Fin d)) :
    ∃ l, N = L l := by
  classical
  let O := pCoreOf 2 P
  let S : Set (Fin d) := badSet P N L
  let Mf : Fin d → Subgroup Q := badPart P N L
  have hN_eq : N = O ⊔ ⨆ l, Mf l :=
    le_antisymm (le_sup_badSet hL hperf hNle hNnormal hON hNopp hd)
      (le_badPart_sup hL hperf hNle hNnormal hON)
  have hMf_mem : ∀ l, l ∈ S → Mf l = L l := by
    intro l hl; simp [Mf, badPart, S, hl]
  have hMf_not : ∀ l, l ∉ S → Mf l = ⊥ := by
    intro l hl; simp [Mf, badPart, S, hl]
  have hS_ne : S.Nonempty := badSet_nonempty hNne hN_eq
  obtain ⟨l0, hl0⟩ := hS_ne
  let A : Subgroup Q := L l0
  let B : Subgroup Q := ⨆ l, restPart P N L l0 l
  obtain ⟨hRf_l0, hRf_mem, hRf_mem_or, hRf_not⟩ :=
    restPart_facts (P := P) (N := N) (L := L) l0
  have hO_le_B : O ≤ B := by
    change pCoreOf 2 P ≤ B
    rw [← hRf_l0]; exact le_iSup (restPart P N L l0) l0
  have hO_le_A : O ≤ A := hL.pCoreOf_le l0
  have hA_le_N : A ≤ N := by
    refine le_of_isLeviFamily_of_normal hL hperf hNle hNnormal hON l0 ?_
    simpa [S, badSet] using hl0
  have hB_le_N : B ≤ N := by
    refine iSup_le fun l => ?_
    by_cases h1 : l ∈ S ∧ l ≠ l0
    · rw [hRf_mem l h1.1 h1.2]
      exact le_of_isLeviFamily_of_normal hL hperf hNle hNnormal hON l
        (by simpa [S, badSet] using h1.1)
    · by_cases h2 : l = l0
      · rw [hRf_mem_or l h2]; exact hON
      · rw [hRf_not l h1 h2]; exact bot_le
  have hAB : A ⊔ B = N := by
    refine le_antisymm (sup_le hA_le_N hB_le_N) ?_
    rw [hN_eq]
    refine sup_le (hO_le_B.trans le_sup_right) (iSup_le fun l => ?_)
    by_cases hl : l ∈ S
    · by_cases hll : l = l0
      · subst hll; rw [hMf_mem l hl]; exact le_sup_left
      · have hRl : restPart P N L l0 l = L l := hRf_mem l hl hll
        rw [hMf_mem l hl, ← hRl]
        exact (le_iSup (restPart P N L l0) l).trans le_sup_right
    · rw [hMf_not l hl]; exact bot_le
  have hBopp : B = Opp 2 B ⊔ O := restPart_opp hL (N := N) (l0 := l0)
  have hc : ⁅A, B⁆ ≤ O := restPart_commutator hL (N := N) (l0 := l0)
  rcases hindec A B hO_le_A hO_le_B (hL.eq_opp_sup l0) hBopp hAB hc with hA | hB
  · exact ⟨l0, hA.symm⟩
  · exfalso
    have hcomm : ⁅N, L l0⁆ ≤ O := by
      rw [← hB]
      rw [Subgroup.commutator_comm A B] at hc
      simpa [A] using hc
    have hnot : ¬ ⁅N, L l0⁆ ≤ O := by simpa [S, badSet] using hl0
    exact hnot hcomm


theorem injective (hL : IsLeviFamily P d L)
    (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 P = L i) : Function.Injective L := by
  have _ : Finite Q := inferInstance
  intro i j hij
  by_contra hne
  have hle : ⁅L i, L j⁆ ≤ pCoreOf 2 P := hL.commutator_le i j hne
  rw [hij] at hle
  have hO : L j ≤ pCoreOf 2 P := by
    rw [← hperf j]
    exact sup_le hle le_rfl
  exact hL.ne j (le_antisymm hO (hL.pCoreOf_le j))

private theorem exists_eq_of_K
    {M Dsub : Subgroup Q} {d d' : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily (Dsub ⊓ M) d L)
    (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 (Dsub ⊓ M) = L i)
    {K J : Fin d' → Subgroup Q} (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J) (k : Fin d') :
    ∃ l, K k = L l := by
  let P := Dsub ⊓ M
  let O := pCoreOf 2 P
  obtain ⟨hbasic, hcomm, hiSup, hindec, hJ⟩ := hKJ
  have hKle : ∀ k, K k ≤ P := fun k => (hbasic k).2.1
  have hOK : ∀ k, O ≤ K k := fun k => (hbasic k).1
  have hKnormal : ∀ k, ((K k).subgroupOf P).Normal := fun k => (hbasic k).2.2.1
  have hKopp : ∀ k, K k = Opp 2 (K k) ⊔ O := fun k => (hbasic k).2.2.2.1
  have hJk : ∀ k, ¬ J k ≤ O := fun k => (hbasic k).2.2.2.2
  have hd : Nonempty (Fin d) := by
    by_contra hne
    have : IsEmpty (Fin d) := not_nonempty_iff.mp hne
    have hsupbot : Opp 2 P ⊔ O = ⊥ := by
      rw [← hL.iSup_eq]
      exact iSup_of_empty L
    have hPopp : Opp 2 P = ⊥ := le_bot_iff.mp (hsupbot ▸ le_sup_left)
    have hObot : O = ⊥ := le_bot_iff.mp (hsupbot ▸ le_sup_right)
    have hmono : Opp 2 (K k) ≤ Opp 2 P := by
      simpa [Opp] using s13_Thirteen2_pElementSubgroup_mono (p := 2) (hKle k)
    have hKbot : K k = ⊥ := by
      rw [hKopp k, hObot, sup_bot_eq]
      exact le_bot_iff.mp (hmono.trans (le_of_eq hPopp))
    apply hJk k
    rw [hJ k, hKbot]
    simpa [hObot] using S17.oUpperTwo_le (⊥ : Subgroup Q)
  have hKne : K k ≠ O := by
    intro hKO
    apply hJk k
    rw [hJ k, hKO]
    exact S17.oUpperTwo_le O
  exact exists_eq_of_isLeviFamily hL hperf (hKle k) (hKnormal k) (hOK k)
    (hKopp k) hKne (hindec k) hd

theorem exists_equiv_of_isDynkinFamilyIn {M Dsub : Subgroup Q} {d : ℕ}
    {L : Fin d → Subgroup Q} (hL : IsLeviFamily (Dsub ⊓ M) d L)
    (hperf : ∀ i, ⁅L i, L i⁆ ⊔ pCoreOf 2 (Dsub ⊓ M) = L i) {d' : ℕ}
    {K J : Fin d' → Subgroup Q} (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J) :
    ∃ σ : Fin d' ≃ Fin d, ∀ k, K k = L (σ k) := by
  let P := Dsub ⊓ M
  let O := pCoreOf 2 P
  have hKJ' : S19.IsDynkinFamilyIn M Dsub d' K J := hKJ
  obtain ⟨hbasic, hcomm, hiSup, hindec, hJ⟩ := hKJ
  have hperf' : ∀ i, ⁅L i, L i⁆ ⊔ O = L i := hperf
  have hKle : ∀ k, K k ≤ P := fun k => (hbasic k).2.1
  have hOK : ∀ k, O ≤ K k := fun k => (hbasic k).1
  have hKnormal : ∀ k, ((K k).subgroupOf P).Normal := fun k => (hbasic k).2.2.1
  have hKopp : ∀ k, K k = Opp 2 (K k) ⊔ O := fun k => (hbasic k).2.2.2.1
  have hJk : ∀ k, ¬ J k ≤ O := fun k => (hbasic k).2.2.2.2
  have hKiSup : (⨆ k, K k) = Opp 2 P ⊔ O := hiSup
  have hExists : ∀ k, ∃ l, K k = L l := fun k => exists_eq_of_K hL hperf hKJ' k
  choose σfun hσspec using hExists
  have hσinj : Function.Injective σfun := by
    intro i j hij
    by_contra hne
    have hKiKj : K i = K j := by rw [hσspec i, hσspec j, hij]
    have hle : ⁅K i, K j⁆ ≤ O := hcomm i j hne
    rw [hKiKj, hσspec j] at hle
    have hO : L (σfun j) ≤ O := by
      rw [← hperf (σfun j)]
      exact sup_le hle le_rfl
    exact hL.ne (σfun j) (le_antisymm hO (hL.pCoreOf_le (σfun j)))
  have hσsurj : Function.Surjective σfun := by
    intro l
    by_contra hnotmem
    have hnot : ∀ k, σfun k ≠ l := fun k h => hnotmem ⟨k, h⟩
    have hLK : ⁅L l, ⨆ k, K k⁆ ≤ O := by
      have h : ⁅⨆ k, K k, L l⁆ ≤ O := by
        refine CFSG.Quasithin.MS93.S59.commutator_iSup_le (K := K) (A := L l) (N := O) ?_ ?_
        · intro k
          exact (hKle k).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
        · intro k
          rw [hσspec k, Subgroup.commutator_comm]
          exact hL.commutator_le l (σfun k) (fun hkl => hnot k hkl.symm)
      rwa [Subgroup.commutator_comm] at h
    have hLle : L l ≤ ⨆ k, K k := by
      rw [hKiSup]
      exact (hL.le_opp l).trans le_sup_left
    have hle : ⁅L l, L l⁆ ≤ O :=
      (Subgroup.commutator_mono le_rfl hLle).trans hLK
    have hO : L l ≤ O := by
      rw [← hperf l]
      exact sup_le hle le_rfl
    exact hL.ne l (le_antisymm hO (hL.pCoreOf_le l))
  refine ⟨Equiv.ofBijective σfun ⟨hσinj, hσsurj⟩, ?_⟩
  intro k
  change K k = L (σfun k)
  exact hσspec k


end IsLeviFamily

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
