module

public import CFSG.LocalAnalysis.UniquenessCase.UC22ConjClosureSelf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixRanks
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251j
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofCore
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.CGT.PushingUp.CampbellPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem centralizer_omegaOneCenter_le_of_r869 {D : Data G} (h869 : F08.R869 D)
    {Y : Subgroup G} {n : ℕ} (hY : Y ∈ calC D.M) (hSU3 : IsSU3 (Bar2 Y) n) (hn : Odd n)
    (hYZ : Y ≤ centralizer (D.Z : Set G)) :
    centralizer (D.Z : Set G) ≤ D.M := by
  have hT2 : IsPGroup 2 D.T := D.sylowG.isPGroup
  have hT1 : D.T ≠ ⊥ := by
    have hO2M : pCoreOf 2 D.M ≠ ⊥ :=
      CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal D.maxLocal.1
    intro h
    exact hO2M (le_bot_iff.mp (h ▸ uc22p20b_pCoreOf_le_T D D.sylowM.le))
  have hZ1 : D.Z ≠ ⊥ := by
    change CFSG.RankThree.PartOne.omegaOneCenterIn D.T ≠ ⊥
    exact CFSG.CGT.PushingUp.omegaOneCenterIn_ne_bot hT2 hT1
  have hNcal : calNOf Y = {D.M} :=
    h869 Y (Or.inl hY) Y le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) Y))
      (not_thin8_of_isSU3 hSU3 hn)
  refine UC22.P2251j.le_of_calNOf hNcal hYZ ?_
  intro htop
  have hZc : D.Z ≤ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.mp htop
  have hcenter : Subgroup.center G = ⊥ := by
    rcases D.standing.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := D.standing.nonab
      refine hab ?_
      have hb : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  rw [hcenter] at hZc
  exact hZ1 (le_bot_iff.mp hZc)

theorem conjClosure_omegaOneCenter_le_pCoreOf_inf_centralizer {D : Data G}
    {N : Subgroup G} (hN : N ∈ calMOf D.T) :
    conjClosure N D.Z ≤ pCoreOf 2 N ⊓ centralizer (pCoreOf 2 N : Set G) := by
  have hTN : D.T ≤ N := hN.2
  have hO2T : pCoreOf 2 N ≤ D.T := uc22p20b_pCoreOf_le_T D hTN
  have hZTN : D.Z ≤ N :=
    (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le D.T).trans hTN
  have hZC : D.Z ≤ centralizer (pCoreOf 2 N : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hz' : z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn D.T := by
      simpa [Data.Z] using hz
    obtain ⟨-, hzc, -⟩ :=
      CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz'
    exact hzc c (hO2T hc)
  have hZW : D.Z ≤ pCoreOf 2 N ⊓ centralizer (pCoreOf 2 N : Set G) :=
    le_inf ((le_inf hZTN hZC).trans (D.standing.charTwo N hN.1.1)) hZC
  have hNW : N ≤ Subgroup.normalizer
      ((pCoreOf 2 N ⊓ centralizer (pCoreOf 2 N : Set G) : Subgroup G) : Set G) := by
    intro n hn
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hn
    · exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (pCoreOf 2 N)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hn)
  exact uc22p22v_conjClosure_le hNW hZW

theorem le_normalizer_commutator_of_five_six {T A U : Subgroup G}
    (hT : IsPGroup 2 T) (hAab : IsMulCommutative A) (hAodd : Odd (Nat.card A))
    (hperm : Permutes A T) (hUAsub : ⁅U, A⁆ ≤ U)
    (hSU : ⁅pCoreOf 2 (A ⊔ T), A⁆ ≤ Subgroup.centralizer (U : Set G))
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    T ≤ Subgroup.normalizer ((⁅U, A⁆ : Subgroup G) : Set G) := by
  intro t ht
  obtain ⟨s, hs, n, hn, rfl⟩ :=
    (uc22p22vb_five_six T A hT hAab hAodd hperm).2 t ht
  refine (Subgroup.normalizer _).mul_mem ?_ ?_
  · exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hUAsub) (hSU hs))
  · exact CFSG.RankThree.PartTwo.Sec13.L3Proof.mem_normalizer_commutator
      (hTU (Subgroup.mem_inf.1 hn).1) (Subgroup.mem_inf.1 hn).2

theorem exists_mem_inf_omegaOneCenter_of_normal {T V : Subgroup G}
    (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hVnorm : T ≤ Subgroup.normalizer (V : Set G)) (hVne : V ≠ ⊥) :
    ∃ x ∈ V, x ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T ∧ x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : V.subgroupOf T ≠ ⊥ := by
    intro h
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hVT] at h
    exact hVne h
  have : (V.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hVnorm
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hcenter : V.subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hsub
  let L : Subgroup ↥T := V.subgroupOf T ⊓ Subgroup.center ↥T
  have hL2 : IsPGroup 2 ↥L := hT.to_subgroup L
  have hLnt : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hcenter
  obtain ⟨k, hk0, hk⟩ := hL2.nontrivial_iff_card.mp hLnt
  have hdvd : 2 ∣ Nat.card ↥L := by
    rw [hk]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hk0)
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 hdvd
  refine ⟨((y : ↥T) : G), ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (y.2).1
  · rw [CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff]
    refine ⟨(y : ↥T).2, fun k hk => ?_, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (y.2).2 ⟨k, hk⟩)
    · have hy2 : (y : ↥L) ^ 2 = 1 := by
        rw [← hyord]
        exact pow_orderOf_eq_one y
      simpa using congrArg (fun z : ↥L => ((z : ↥T) : G)) hy2
  · intro h
    have hy1 : (y : ↥L) = 1 := Subtype.ext (Subtype.ext h)
    rw [hy1, orderOf_one] at hyord
    omega

omit [Finite G] in
theorem le_normalizer_conjClosure_of_normalizes_centralizes {X H E : Subgroup G}
    (hXH : X ≤ Subgroup.normalizer (H : Set G))
    (hXE : X ≤ Subgroup.centralizer (E : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure H E : Set G) := by
  have key : ∀ g : G, g ∈ X → ∀ h ∈ H, ∀ z ∈ E,
      ∃ h' ∈ H, ∃ z' ∈ E, g * (h * z * h⁻¹) * g⁻¹ = h' * z' * h'⁻¹ := by
    intro g hg h hh z hz
    refine ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hXH hg) h).1 hh, z, hz, ?_⟩
    have hgz : g * z * g⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp (hXE hg) z hz
      rw [this.symm]
      group
    calc g * (h * z * h⁻¹) * g⁻¹
        = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
      _ = (g * h * g⁻¹) * z * (g * h * g⁻¹)⁻¹ := by rw [hgz]
  intro x hx
  exact uc22p22v_mem_normalizer_conjClosure (key x hx) (key x⁻¹ (X.inv_mem hx))

theorem conjClosure_le_centralizer_of_conjClosure_eq {N A U : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hAN : A ≤ N) (hA : Nat.card A = r)
    (hrk : CFSG.Open.pRank r N ≤ 1)
    (hNU : conjClosure N A ≤ Subgroup.normalizer (U : Set G))
    (hAcent : A ≤ Subgroup.centralizer (U : Set G)) :
    conjClosure N A ≤ Subgroup.centralizer (U : Set G) := by
  rw [← UC22.conjClosure_conjClosure_eq hr hAN hA hrk]
  exact uc22p22v_conjClosure_le
    (hNU.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer U)) hAcent

theorem uc2_14_6_paraTwo {D : Data G} (h869 : F08.R869 D) {Y : Subgroup G} {n : ℕ}
    (hY : Y ∈ calC D.M) (hSU3 : IsSU3 (Bar2 Y) n) (hn : Odd n) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {A : Subgroup G} (hAY : A ≤ Y) (hA : Nat.card A = r)
    (hperm : Permutes A D.T) (hAU : A ∈ uniqueSet D.M) {N : Subgroup G}
    (hN : N ∈ calMOf (A ⊔ D.T)) (hNM : N ≠ D.M) (hrk : CFSG.Open.pRank r N ≤ 1)
    (hcore : ⁅pCoreOf 2 (A ⊔ D.T), A⁆ ≤ pCoreOf 2 (conjClosure N A))
    (hYZ : Y ≤ centralizer (D.Z : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have hTN : D.T ≤ N := le_sup_right.trans hN.2
  have hAN : A ≤ N := le_sup_left.trans hN.2
  have hCZ : centralizer (D.Z : Set G) ≤ D.M :=
    centralizer_omegaOneCenter_le_of_r869 h869 hY hSU3 hn hYZ
  let H : Subgroup G := conjClosure N A
  let U : Subgroup G := conjClosure H D.Z
  let W : Subgroup G := pCoreOf 2 N ⊓ centralizer (pCoreOf 2 N : Set G)
  have hAH : A ≤ H := uc22p22v_le_conjClosure N A
  have hHN : H ≤ N := uc22p22v_conjClosure_le (Subgroup.le_normalizer) hAN
  have hNH : N ≤ Subgroup.normalizer (H : Set G) := uc22p22v_le_normalizer_conjClosure N A
  have hUW : U ≤ W := (uc22p22v_conjClosure_mono hHN D.Z).trans
    (conjClosure_omegaOneCenter_le_pCoreOf_inf_centralizer ⟨hN.1, hTN⟩)
  have hUO2 : U ≤ pCoreOf 2 N := hUW.trans inf_le_left
  have hO2T : pCoreOf 2 N ≤ D.T := uc22p20b_pCoreOf_le_T D hTN
  have hHU : H ≤ Subgroup.normalizer (U : Set G) :=
    uc22p22v_le_normalizer_conjClosure H D.Z
  have hTZ : D.T ≤ Subgroup.centralizer (D.Z : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn D.T := by
      simpa [Data.Z] using hz
    exact (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz').2.1 t ht |>.symm
  have hTU : D.T ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure_of_normalizes_centralizes (hTN.trans hNH) hTZ
  have hO2H : pCoreOf 2 H ≤ pCoreOf 2 N :=
    CFSG.Quasithin.MS93.map_pCore_le_pCoreOf hHN hNH
  have hSU : ⁅pCoreOf 2 (A ⊔ D.T), A⁆ ≤ Subgroup.centralizer (U : Set G) :=
    hcore.trans (hO2H.trans (Subgroup.le_centralizer_iff.mp (hUW.trans inf_le_right)))
  have hAnc : ¬ A ≤ Subgroup.centralizer (U : Set G) := by
    intro hAcent
    have hHleC : H ≤ Subgroup.centralizer (U : Set G) :=
      conjClosure_le_centralizer_of_conjClosure_eq hr hAN hA hrk hHU hAcent
    have hZleU : D.Z ≤ U := uc22p22v_le_conjClosure H D.Z
    have hHleM : H ≤ D.M :=
      hHleC.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hZleU)).trans hCZ)
    exact not_conjClosure_le_of_mem_uniqueSet D.maxLocal hN.1 hAU hNM hHleM
  have hAnormU : A ≤ Subgroup.normalizer (U : Set G) := hAH.trans hHU
  have hUAsub : ⁅U, A⁆ ≤ U :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := A) (K := U)).1 hAnormU
  have hUA1 : ⁅U, A⁆ ≠ ⊥ := by
    intro hbot
    exact hAnc (Subgroup.le_centralizer_iff.mpr
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot))
  have hAab : IsMulCommutative A := by
    have : IsCyclic ↥A := isCyclic_of_prime_card (α := ↥A) (p := r) hA
    infer_instance
  have hAodd : Odd (Nat.card A) := by
    rw [hA]
    exact hr.odd_of_ne_two hr2
  have hTn : D.T ≤ Subgroup.normalizer ((⁅U, A⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_five_six D.sylowG.isPGroup hAab hAodd hperm hUAsub hSU hTU
  have hUA_le_T : ⁅U, A⁆ ≤ D.T := hUAsub.trans (hUO2.trans hO2T)
  obtain ⟨x, hxV, hxZ, hx1⟩ :=
    exists_mem_inf_omegaOneCenter_of_normal D.sylowG.isPGroup hUA_le_T hTn hUA1
  have hxZ' : x ∈ D.Z := by
    simpa [Data.Z] using hxZ
  have hU2 : IsPGroup 2 ↥U := by
    obtain ⟨k, hk⟩ :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) N).exists_card_dvd_pow
    exact IsPGroup.of_card_dvd_pow ((Subgroup.card_dvd_of_le hUO2).trans hk)
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥U) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hA, hk]
    exact (Nat.coprime_primes hr Nat.prime_two).mpr hr2 |>.pow_right k
  have hWmul : ∀ y ∈ W, ∀ z ∈ W, y * z = z * y := by
    intro y hy z hz
    exact (Subgroup.mem_centralizer_iff.mp hy.2 z hz.1).symm
  have hUab : IsMulCommutative ↥U :=
    IsMulCommutative.of_setLike_mul_comm fun y hy z hz => hWmul y (hUW hy) z (hUW hz)
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hYZ (hAY ha)) x hxZ').symm
  have hbot := CFSG.RankThree.PartTwo.Sec13.L3Proof.commutator_inf_centralizer_eq_bot
    hUab hAnormU hcop
  exact hx1 (Subgroup.mem_bot.mp (hbot.le ⟨hxV, hxC⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
