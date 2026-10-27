module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Theorem8108
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyNine
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem pRank_subgroupOf_eq {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {H K : Subgroup A} (hHK : H ≤ K) :
    CFSG.Open.pRank p (H.subgroupOf K) = CFSG.Open.pRank p H := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H.subgroupOf K),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (Subgroup.subgroupOfEquivOfLe hHK)

theorem centralizer_sup_eq_inf_centralizer_of_commute {Y : Type*} [Group Y]
    {A B : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Subgroup.centralizer ((A ⊔ B : Subgroup Y) : Set Y) =
      Subgroup.centralizer (A : Set Y) ⊓ Subgroup.centralizer (B : Set Y) := by
  apply le_antisymm
  · intro x hx
    exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hx,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hx⟩
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (GL83.CompFam.mem_sup_of_commute hcomm).1 hy
    rw [← hab]
    have hxa : a * x = x * a := hx.1 a ha
    have hxb : b * x = x * b := hx.2 b hb
    calc a * b * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [hxb]
      _ = (a * x) * b := by group
      _ = (x * a) * b := by rw [hxa]
      _ = x * (a * b) := by group

theorem pCoreOf_eq_inf_pCoreOf_of_subnormal {M L : Subgroup G}
    (hL : CFSG.Open.IsSubnormal L M) :
    CFSG.Open.pCoreOf 2 L = L ⊓ CFSG.Open.pCoreOf 2 M := by
  refine le_antisymm ?_ ?_
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hL)
  · exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (CFSG.Quasithin.A4.subnormal_le hL)

theorem mem_ker_rhoL_iff_mem_centralizer_barImage
    {M L M0 : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC M)
    (hM0M : M0 ≤ M) (hM0N : M0 ≤ Subgroup.normalizer (L : Set G))
    (m : ↥M0) :
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
        ⟨(m : G), hM0N m.2⟩ = 1 ↔
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩ : Bar2 M) ∈
        Subgroup.centralizer
          (CFSG.LocalAnalysis.UniquenessCase.UC22.barImage M L : Set (Bar2 M)) := by
  have hLM : L ≤ M := hL.1.le
  have hO2 : CFSG.Open.pCoreOf 2 L = L ⊓ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_eq_inf_pCoreOf_of_subnormal hL.1
  have hO2_le : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 M := by
    rw [hO2]; exact inf_le_right
  constructor
  · intro hρ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hxL, rfl⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barImage.1 hy
    have hxG : (x : G) ∈ L := hxL
    have hxM : (x : G) ∈ M := hLM hxG
    have hfix : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
        ⟨(m : G), hM0N m.2⟩ (QuotientGroup.mk ⟨(x : G), hxG⟩) =
        QuotientGroup.mk ⟨(x : G), hxG⟩ := by
      rw [hρ, MulAut.one_apply]
    have hcL : (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 L :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
        ⟨(m : G), hM0N m.2⟩ ⟨(x : G), hxG⟩).1 hfix
    have hcM : (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 M := hO2_le hcL
    have hmemM : (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem (hM0M m.2) hxM) (M.inv_mem (hM0M m.2)))
        (M.inv_mem hxM)
    have hcM' : (⟨(m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹, hmemM⟩ : ↥M) ∈
        CFSG.pCore 2 ↥M := (CFSG.mem_openPCoreOf_iff (p := 2) ⟨_, hmemM⟩).mp hcM
    have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        ⟨(m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹, hmemM⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 hcM' 
    have hcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩ := by
      have hq' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩)⁻¹ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩)⁻¹ = 1 := by
        rw [← hq]
        congr 1
      exact commutatorElement_eq_one_iff_mul_comm.mp (by
        simpa [commutatorElement_def] using hq')
    exact hcomm.symm
  · intro hcent
    refine MulEquiv.ext fun q => ?_
    refine QuotientGroup.induction_on q ?_
    intro x
    rw [MulAut.one_apply]
    refine (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
      ⟨(m : G), hM0N m.2⟩ x).2 ?_
    have hxG : (x : G) ∈ L := x.2
    have hxM : (x : G) ∈ M := hLM hxG
    have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩ ∈
        CFSG.LocalAnalysis.UniquenessCase.UC22.barImage M L :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barImage.2
        ⟨⟨(x : G), hxM⟩, hxG, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hcent _ hxbar
    have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(m : G), hM0M m.2⟩)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(x : G), hxM⟩)⁻¹ = 1 := by
      rw [hcomm.symm]
      group
    have hmemM : (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem (hM0M m.2) hxM) (M.inv_mem (hM0M m.2)))
        (M.inv_mem hxM)
    have hq' : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        ⟨(m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹, hmemM⟩ = 1 := by
      rw [← hq]
      congr 1
    have hcM' : (⟨(m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹, hmemM⟩ : ↥M) ∈
        CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 hq'
    have hcM : (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 M := (CFSG.mem_openPCoreOf_iff (p := 2) ⟨_, hmemM⟩).mpr hcM'
    have hxL : (m : G) * (x : G) * (m : G)⁻¹ ∈ L := by
      have hmap : L.map (MulAut.conj (m : G)).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hM0N m.2)
      have hmem : (MulAut.conj (m : G)) (x : G) ∈
          L.map (MulAut.conj (m : G)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hxG
      rwa [hmap] at hmem
    have hcL : (m : G) * (x : G) * (m : G)⁻¹ * (x : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 L := by
      rw [hO2]
      exact ⟨L.mul_mem hxL (L.inv_mem hxG), hcM⟩
    exact hcL

theorem pRank_mulAut_barImage_le_one
    {M L : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC M)
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(CFSG.LocalAnalysis.UniquenessCase.UC22.barImage M L))) ≤ 1 := by
  obtain ⟨e, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_equiv hL
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)]
  have hperf : Group.IsPerfect (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) :=
    Group.isPerfect_def.mpr hSL.1.1.1
  haveI : Group.IsPerfect (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) := hperf
  refine (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_mulAut_le
    (J := CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) hp).trans ?_
  have hcardAut : Nat.card (MulAut (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L ⧸
      Subgroup.center (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))) =
      2 ^ 8 * 3 ^ 3 * 5 * 7 := by
    obtain ⟨K, hfield, hfin, hKcard, ⟨eK⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hSL.1.2
    letI := hfield
    letI := hfin
    have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
    rw [Nat.card_congr (MulAut.congr eK).toEquiv,
      CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hk]
    norm_num
  refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
  rw [hcardAut]
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.prime_sq_not_dvd_aut_L34 hp hp2 hp3

theorem pRank_eq_of_relIndex_le_two {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H K : Subgroup A} (hHK : H ≤ K)
    (hidx : H.relIndex K ≤ 2) :
    CFSG.Open.pRank p H = CFSG.Open.pRank p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (CFSG.SectionRank.pRank_mono hp.one_lt hHK) ?_
  obtain ⟨E, hEK, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K
  have hHK0 : H.relIndex K ≠ 0 := by
    exact (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := H) (K := K))
      Nat.card_pos).ne'
  have hEidx : (E ⊓ H).relIndex E ≤ 2 := by
    rw [inf_comm E H, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right hEK hHK0).trans hidx
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).index ((E ⊓ H).subgroupOf E)
  have hn' : (E ⊓ H).relIndex E = p ^ n := by simpa [Subgroup.relIndex] using hn
  have hn0 : n = 0 := by
    by_contra h
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h1 : p ^ 1 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at h1
    have h2 : p ^ n ≤ 2 := by rw [← hn']; exact hEidx
    omega
  have hE_le_H : E ≤ H := by
    have h1 : (E ⊓ H).relIndex E = 1 := by rw [hn', hn0, pow_zero]
    exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
  exact CFSG.SectionRank.le_pRank hp.one_lt hE_le_H hE hEcard

theorem inf_normalizer_le_normalizer_of_conjSetOf_eq_pair {M L L' : Subgroup G}
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf M L = {L, L'}) :
    M ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (L' : Set G) := by
  intro m hm
  have hmM : m ∈ M := hm.1
  have hmL : L.map (MulAut.conj m).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hm.2
  by_cases hLL' : L = L'
  · rw [← hLL']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmL
  have hL'conj : L' ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf M L := by
    rw [hset]; simp
  obtain ⟨g, hgM, hL'map⟩ := hL'conj
  have hcomp : L'.map (MulAut.conj m).toMonoidHom =
      L.map (MulAut.conj (m * g)).toMonoidHom := by
    rw [hL'map, Subgroup.map_map]
    congr 1
    ext x
    show m * (g * x * g⁻¹) * m⁻¹ = (m * g) * x * (m * g)⁻¹
    group
  have hmem : L'.map (MulAut.conj m).toMonoidHom ∈
      CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf M L :=
    ⟨m * g, M.mul_mem hmM hgM, hcomp⟩
  rw [hset] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exfalso
    apply hLL'
    exact Subgroup.map_injective (f := (MulAut.conj m).toMonoidHom)
      (MulAut.conj m).injective (by rw [h, hmL])
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem relIndex_inf_normalizer_le_two {M L L' : Subgroup G}
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf M L = {L, L'}) :
    (M ⊓ Subgroup.normalizer (L : Set G)).relIndex M ≤ 2 := by
  classical
  let act : MulAction ↥M (Subgroup G) :=
    MulAction.compHom _ ((MulAut.conj : G →* MulAut G).comp M.subtype)
  letI := act
  have horbit : MulAction.orbit ↥M L =
      CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf M L := by
    ext K
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨(m : G), m.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hstab : MulAction.stabilizer ↥M L =
      (M ⊓ Subgroup.normalizer (L : Set G)).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    change (L.map (MulAut.conj (m : G)).toMonoidHom = L) ↔
      (m : G) ∈ M ∧ L.map (MulAut.conj (m : G)).toMonoidHom = L
    simp
  have hidx := MulAction.index_stabilizer ↥M L
  rw [hstab, horbit, hset] at hidx
  rw [Subgroup.relIndex, hidx]
  have hcard : ({L, L'} : Set (Subgroup G)).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le L ({L'} : Set (Subgroup G))
  exact hcard

theorem two_le_pRank_centralizer_barX
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) :
    2 ≤ CFSG.Open.pRank S.p
      (⊤ ⊓ Subgroup.centralizer
        (CFSG.LocalAnalysis.UniquenessCase.UC22.barImage S.M
          (CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L) : Set (Bar2 S.M))) := by
  classical
  haveI : Fact S.p.Prime := ⟨S.hp.1.1⟩
  have hp := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  have h3β : 3 ∉ CFSG.Open.uniqueFourBeta G :=
    three_not_mem_uniqueFourBeta_of_not_strong hU S hMS hnot
  have hp5 : 5 ≤ S.p :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.five_le_of_mem_uniqueFourSigma S.hp h3β
  have hp3 : S.p ≠ 3 := by
    intro h
    exact h3β (h ▸ S.hp.1)
  have hXeq : conjClosure S.M L = L ⊔ L' := by
    unfold conjClosure
    rw [hset]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun X => iSup_le fun hX => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup₂_of_le L (by simp) le_rfl)
        (le_iSup₂_of_le L' (by simp) le_rfl)
  have hL'conj : L' ∈ conjSetOf S.M L := by
    rw [hset]
    simp
  obtain ⟨g, hgM, hL'map⟩ := hL'conj
  have hL'calC : L' ∈ calC S.M := by
    rw [hL'map]
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map S.M (MulAut.conj g)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.1
        (Subgroup.le_normalizer hgM)) hL
  have hLM : L ≤ S.M := hL.1.le
  have hL'LM : L' ≤ S.M := hL'calC.1.le
  have hSL' : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (Bar2 L') := by
    obtain ⟨eBar⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20d_bar2_conj g L
    have hL'map' : L' = CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20bCj g L := by
      simpa [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20bCj] using hL'map
    have e : Bar2 L ≃* Bar2 L' := by
      rw [hL'map']
      exact eBar
    obtain ⟨hSL3, hcenter⟩ := hSL
    let ec : (Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
        (Bar2 L' ⧸ Subgroup.center (Bar2 L')) :=
      QuotientGroup.congr (Subgroup.center (Bar2 L)) (Subgroup.center (Bar2 L'))
        e (Subgroup.map_center_eq e)
    refine ⟨⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hSL3.1,
      CFSG.Blueprint.LieModel.of_mulEquiv ec hSL3.2⟩, ?_⟩
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hcenter
  set K1 : Subgroup (Bar2 S.M) := barImage S.M L with hK1def
  set K2 : Subgroup (Bar2 S.M) := barImage S.M L' with hK2def
  set K : Subgroup (Bar2 S.M) := barImage S.M (conjClosure S.M L) with hKdef
  have hK_eq : K = K1 ⊔ K2 := by
    rw [hKdef, hK1def, hK2def, hXeq]
    show barImage S.M (L ⊔ L') = barImage S.M L ⊔ barImage S.M L'
    simp only [barImage, Subgroup.subgroupOf_sup hLM hL'LM, Subgroup.map_sup]
  have hK1_comp : CFSG.IsComponent K1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_isComponent hL
  have hK2_comp : CFSG.IsComponent K2 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_isComponent hL'calC
  set M0 : Subgroup G := S.M ⊓ Subgroup.normalizer (L : Set G) with hM0def
  have hM0_le_M : M0 ≤ S.M := inf_le_left
  have hM0_le_NL : M0 ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hM0_index : M0.relIndex S.M ≤ 2 :=
    relIndex_inf_normalizer_le_two hset
  have hM0_rank : CFSG.Open.pRank S.p M0 = CFSG.Open.pRank S.p S.M :=
    pRank_eq_of_relIndex_le_two hp hp2 hM0_le_M hM0_index
  have hM0_le_NL' : M0 ≤ Subgroup.normalizer (L' : Set G) :=
    inf_normalizer_le_normalizer_of_conjSetOf_eq_pair hset
  have hAut1 : CFSG.Open.pRank S.p (⊤ : Subgroup (MulAut ↥K1)) ≤ 1 :=
    pRank_mulAut_barImage_le_one hL hSL hp hp2 hp3
  have hAut2 : CFSG.Open.pRank S.p (⊤ : Subgroup (MulAut ↥K2)) ≤ 1 :=
    pRank_mulAut_barImage_le_one hL'calC hSL' hp hp2 hp3
  set C : Subgroup (Bar2 S.M) := Subgroup.centralizer (K : Set (Bar2 S.M)) with hCdef
  set P : Subgroup G := CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M C with hPdef
  obtain ⟨e1, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_equiv hL
  obtain ⟨e2, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_equiv hL'calC
  let ρ1 : ↥M0 →* MulAut (Bar2 L) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion hM0_le_NL)
  let ρ2 : ↥M0 →* MulAut (Bar2 L') :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L').comp (Subgroup.inclusion hM0_le_NL')
  let ψ1 : ↥M0 →* MulAut ↥K1 := (MulAut.congr e1).toMonoidHom.comp ρ1
  let ψ2 : ↥M0 →* MulAut ↥K2 := (MulAut.congr e2).toMonoidHom.comp ρ2
  let ψ : ↥M0 →* MulAut ↥K1 × MulAut ↥K2 := ψ1.prod ψ2
  have hC_eq : C = Subgroup.centralizer (K1 : Set (Bar2 S.M)) ⊓
      Subgroup.centralizer (K2 : Set (Bar2 S.M)) := by
    rw [hCdef, hK_eq]
    by_cases hLL' : L = L'
    · have hK12 : K1 = K2 := by rw [hK1def, hK2def, hLL']
      rw [hK12, sup_idem, inf_idem]
    · have hcomm : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_barImage_commute hL hL'calC hLL'
      exact centralizer_sup_eq_inf_centralizer_of_commute hcomm
  have hker1 : ψ1.ker = (CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M
      (Subgroup.centralizer (K1 : Set (Bar2 S.M)))).subgroupOf M0 := by
    ext m
    rw [MonoidHom.mem_ker]
    have hψ1 : ψ1 m = 1 ↔ ρ1 m = 1 := by
      constructor
      · intro h
        have h' : (MulAut.congr e1) (ρ1 m) = (MulAut.congr e1) 1 := by
          rw [map_one]
          exact h
        exact (MulAut.congr e1).injective h' 
      · intro h
        change (MulAut.congr e1) (ρ1 m) = 1
        rw [h, map_one]
    rw [hψ1]
    have hρ1 : ρ1 m = 1 ↔ CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
        ⟨(m : G), hM0_le_NL m.2⟩ = 1 := Iff.rfl
    rw [hρ1]
    rw [mem_ker_rhoL_iff_mem_centralizer_barImage hL hM0_le_M hM0_le_NL m]
    rw [hK1def]
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage]
      exact ⟨hM0_le_M m.2, h⟩
    · intro hmP
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage] at hmP
      exact hmP.2
  have hker2 : ψ2.ker = (CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M
      (Subgroup.centralizer (K2 : Set (Bar2 S.M)))).subgroupOf M0 := by
    ext m
    rw [MonoidHom.mem_ker]
    have hψ2 : ψ2 m = 1 ↔ ρ2 m = 1 := by
      constructor
      · intro h
        have h' : (MulAut.congr e2) (ρ2 m) = (MulAut.congr e2) 1 := by
          rw [map_one]
          exact h
        exact (MulAut.congr e2).injective h'
      · intro h
        change (MulAut.congr e2) (ρ2 m) = 1
        rw [h, map_one]
    rw [hψ2]
    have hρ2 : ρ2 m = 1 ↔ CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L'
        ⟨(m : G), hM0_le_NL' m.2⟩ = 1 := Iff.rfl
    rw [hρ2]
    rw [mem_ker_rhoL_iff_mem_centralizer_barImage hL'calC hM0_le_M hM0_le_NL' m]
    rw [hK2def]
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage]
      exact ⟨hM0_le_M m.2, h⟩
    · intro hmP
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage] at hmP
      exact hmP.2
  have hker_prod : ψ.ker = ψ1.ker ⊓ ψ2.ker := by
    ext m
    simp [ψ, MonoidHom.mem_ker, Subgroup.mem_inf]
  have hsub_inf : ∀ A B : Subgroup G,
      (A.subgroupOf M0) ⊓ (B.subgroupOf M0) = (A ⊓ B).subgroupOf M0 := by
    intro A B
    ext m
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hpre_inf : CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M
      (Subgroup.centralizer (K1 : Set (Bar2 S.M)) ⊓
        Subgroup.centralizer (K2 : Set (Bar2 S.M))) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M
          (Subgroup.centralizer (K1 : Set (Bar2 S.M))) ⊓
        CFSG.LocalAnalysis.UniquenessCase.UC22.barPreimage S.M
          (Subgroup.centralizer (K2 : Set (Bar2 S.M))) := by
    ext x
    rw [Subgroup.mem_inf]
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage,
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage,
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_mem_barPreimage]
    constructor
    · rintro ⟨hxM, hx⟩
      exact ⟨⟨hxM, hx.1⟩, ⟨hxM, hx.2⟩⟩
    · rintro ⟨⟨hxM1, hx1⟩, ⟨hxM2, hx2⟩⟩
      refine ⟨hxM1, ⟨hx1, ?_⟩⟩
      simpa using hx2
  have hC_eq' : Subgroup.centralizer (K : Set (Bar2 S.M)) =
      Subgroup.centralizer (K1 : Set (Bar2 S.M)) ⊓
        Subgroup.centralizer (K2 : Set (Bar2 S.M)) := by
    rw [← hCdef]
    exact hC_eq
  have hker : ψ.ker = P.subgroupOf M0 := by
    rw [hker_prod, hker1, hker2, hsub_inf, hPdef, hCdef, hC_eq', ← hpre_inf]
  have hrange : CFSG.Open.pRank S.p ψ.range ≤ 2 := by
    refine (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : ψ.range ≤ ⊤)).trans ?_
    refine (CFSG.Quasithin.H13.NQBlock.pRank_prod_le hp).trans ?_
    omega
  have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
    (p := S.p) hp ψ (⊤ : Subgroup ↥M0)
  rw [top_inf_eq, ← MonoidHom.range_eq_map] at hineq
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M0] at hineq
  have hP_le_M : P ≤ S.M := by
    rw [hPdef]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_barPreimage_le S.M C
  have hPidx : (P ⊓ M0).relIndex P ≤ 2 := by
    rw [inf_comm P M0, Subgroup.inf_relIndex_right]
    have hPM : P ≤ S.M := hP_le_M
    have h0 : M0.relIndex S.M ≠ 0 := by
      exact (Nat.pos_of_dvd_of_pos
        (Subgroup.relIndex_dvd_card (H := M0) (K := S.M)) Nat.card_pos).ne'
    exact (Subgroup.relIndex_le_of_le_right hPM h0).trans hM0_index
  have hker_rank : CFSG.Open.pRank S.p ψ.ker = CFSG.Open.pRank S.p P := by
    rw [hker, ← Subgroup.inf_subgroupOf_right P M0]
    rw [pRank_subgroupOf_eq hp (inf_le_right : P ⊓ M0 ≤ M0)]
    exact pRank_eq_of_relIndex_le_two hp hp2 inf_le_left hPidx
  have hPC_rank : CFSG.Open.pRank S.p P = CFSG.Open.pRank S.p C := by
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_barImage
      (p := S.p) (M := S.M) (P := P) hp hp2 hP_le_M
    rw [hPdef, CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage] at h
    exact h.symm
  have h4 : 4 ≤ CFSG.Open.pRank S.p S.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_of_sigma S.hp
  have hmain : CFSG.Open.pRank S.p S.M ≤ CFSG.Open.pRank S.p C + 2 := by
    calc CFSG.Open.pRank S.p S.M = CFSG.Open.pRank S.p M0 := hM0_rank.symm
      _ ≤ CFSG.Open.pRank S.p ψ.ker + CFSG.Open.pRank S.p ψ.range := hineq
      _ = CFSG.Open.pRank S.p C + CFSG.Open.pRank S.p ψ.range := by
          rw [hker_rank, hPC_rank]
      _ ≤ CFSG.Open.pRank S.p C + 2 := by omega
  rw [top_inf_eq]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
