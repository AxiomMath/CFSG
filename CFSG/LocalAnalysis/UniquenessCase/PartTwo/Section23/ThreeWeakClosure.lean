module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22k
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

theorem inf_omegaOneCenter_ne_bot {X : Subgroup G} (hXel : IsElemAbelian 2 X) (hXT : X ≤ D.T)
    (hX : X ≠ ⊥) (hT : D.T ≤ Subgroup.normalizer (X : Set G)) : X ⊓ D.Z ≠ ⊥ := by
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hXel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXe : CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2 X := fun x hx y hy =>
    ⟨hXcomm x hx y hy, by simpa [pow_two] using hXel.2 x hx⟩
  have hTZ : ∀ t ∈ D.T, CFSG.CGT.PushingUpLit.A78Sp4.cj t X = X := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hT ht)
  obtain ⟨z, hzX, hz1, hzT⟩ :=
    CFSG.CGT.PushingUpLit.A78Sp4.exists_fixed_ne_one D.sylowG.isPGroup hXe hX hTZ
  have hzT' : ∀ t ∈ D.T, t * z = z * t := by
    intro t ht
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hzT t ht]
  have hzZ : z ∈ D.Z :=
    CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
      ⟨hXT hzX, hzT', by simpa [pow_two] using hXel.2 z hzX⟩
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨z, hzX, hzZ⟩, ?_⟩
  exact fun h => hz1 (congrArg Subtype.val h)

theorem irrOn_U (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z)
    (hirr : IrrOn (c.L0 ⊓ D.M) c.U0) : IrrOn D.M D.U := by
  intro X hXU hXM
  by_cases hX : X = ⊥
  · exact Or.inl hX
  · refine Or.inr ?_
    have hT : D.T ≤ Subgroup.normalizer (X : Set G) := D.sylowM.le.trans hXM
    have hUel : IsElemAbelian 2 D.U :=
      (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
    have hXel : IsElemAbelian 2 X := B2F.isElemAbelian_mono hXU hUel
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (inf_omegaOneCenter_ne_bot hXel (hXU.trans (Data.u_le_T D)) hX hT)
    have hZleU0 : D.Z ≤ c.U0 := hU0 ▸ uc22p22v_le_conjClosure (c.L0 ⊓ D.M) D.Z
    obtain ⟨hzX, hzZ⟩ := Subgroup.mem_inf.mp z.2
    have hXU0ne : X ⊓ c.U0 ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨z, hzX, hZleU0 hzZ⟩, ?_⟩
      intro h
      have h1 : (z : G) = 1 := by
        simpa using congrArg (fun w : ↥(X ⊓ c.U0) => (w : G)) h
      exact hz (Subtype.ext h1)
    have hHU0 : c.L0 ⊓ D.M ≤ Subgroup.normalizer (c.U0 : Set G) := by
      rw [hU0]
      exact uc22p22v_le_normalizer_conjClosure (c.L0 ⊓ D.M) D.Z
    have hHXU0 : c.L0 ⊓ D.M ≤ Subgroup.normalizer (X ⊓ c.U0 : Set G) :=
      (le_inf (inf_le_right.trans hXM) hHU0).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hU0leX : c.U0 ≤ X := by
      rcases hirr _ inf_le_right hHXU0 with hbot | htop
      · exact absurd hbot hXU0ne
      · exact htop ▸ inf_le_left
    have hUleX : D.U ≤ X := by
      rw [Data.U, uCore_eq_conjClosure, ← omegaOneCenterIn_eq_quasithinOmegaOneCenter]
      change Quasithin.conjClosure D.Z D.M ≤ X
      refine Quasithin.conjClosure_le fun m hm z hz => ?_
      have hmN : m ∈ Subgroup.normalizer (X : Set G) := hXM hm
      exact ((Subgroup.mem_normalizer_iff.mp hmN) z).mp (hU0leX (hZleU0 hz))
    exact le_antisymm hXU hUleX

theorem U_ne_bot (c : Ctx23L D Ch) : D.U ≠ ⊥ := fun h =>
  CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup
    (ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM)
    (le_bot_iff.mp (h ▸ Data.Z_le_U D))

theorem four_le_card_U (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U) :
    4 ≤ Nat.card D.U := by
  have hZleU0 : D.Z ≤ c.U0 := hU0 ▸ uc22p22v_le_conjClosure (c.L0 ⊓ D.M) D.Z
  have hZne : D.Z ≠ ⊥ :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup
      (ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM)
  have hU0ne : c.U0 ≠ ⊥ := fun h => hZne (le_bot_iff.mp (h ▸ hZleU0))
  have h1 : 1 < Nat.card c.U0 := (Subgroup.one_lt_card_iff_ne_bot c.U0).mpr hU0ne
  have h2 : Nat.card c.U0 < Nat.card D.U := Subgroup.card_lt_of_lt hlt
  have hUel : IsElemAbelian 2 D.U :=
    (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
  obtain ⟨n, hn⟩ := (uc22p22e_isPGroup_of_elem hUel).exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n ≤ 1 := by omega
    interval_cases n <;> omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    _ = Nat.card D.U := hn.symm

theorem wClos_zero_gt (c : Ctx23L D Ch)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h4 : 4 ≤ Nat.card D.U) : D.U < E3.wClos D.U 0 D.T := by
  have hne : E3.wClos D.U 0 D.T ≠ D.U :=
    TwelveFourteen.wClos_zero_ne_self hTim hcat D (uc22p22e_inCalV_U D) c.hTI h4
  have hle : D.U ≤ E3.wClos D.U 0 D.T :=
    E3.le_wClos ⟨Data.u_le_T D, 1, by rw [conjSubgroup_one],
      by rw [conjSubgroup_one, E3.mQuot_self]⟩
  exact lt_of_le_of_ne hle hne.symm

theorem conjSubgroup_U_le_normalizer (c : Ctx23L D Ch) {g : G}
    (hg : conjSubgroup D.U g ≤ D.T) :
    conjSubgroup D.U g ≤ Subgroup.normalizer (D.U : Set G) :=
  hg.trans (D.sylowM.le.trans (le_normalizer_uCore D.M D.T))

theorem wClos_zero_le_centralizer (c : Ctx23L D Ch) :
    E3.wClos D.U 0 D.T ≤ Subgroup.centralizer (D.U : Set G) := by
  refine E3.wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAT, g, hAg, hmg⟩ := hA
  have hUel : IsElemAbelian 2 D.U :=
    (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
  have hUg2 : IsPGroup 2 (conjSubgroup D.U g) :=
    (uc22p22e_isPGroup_of_elem hUel).map _
  have hAUg : A = conjSubgroup D.U g := (E3.mQuot_eq_zero_iff hUg2 hAg).mp hmg
  subst hAUg
  have hUleN : D.U ≤ Subgroup.normalizer (conjSubgroup D.U g : Set G) :=
    (CFSG.LocalAnalysis.WeakClosure81.le_normalizer_conj_iff hUel c.hTI).mp
      (conjSubgroup_U_le_normalizer c hAT)
  have hN : D.U ⊓ Subgroup.normalizer (conjSubgroup D.U g : Set G) ≠ ⊥ := by
    rw [inf_eq_left.mpr hUleN]
    exact U_ne_bot c
  have hP : IsPGroup 2 ↥(D.U ⊔ conjSubgroup D.U g) :=
    D.sylowM.isPGroup.to_le (sup_le (Data.u_le_T D) hAT)
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (CFSG.LocalAnalysis.WeakClosure81.commute_of_isPGroup_sup hUel c.hTI
    ⟨1, by rw [conjSubgroup_one]⟩ ⟨g, rfl⟩ hN hP) u hu v hv

theorem isWeaklyClosedIn_iff {A B : Subgroup G} :
    CFSG.Quasithin.IsWeaklyClosedIn A B ↔ CFSG.ASVolI.ChIJK.IsWeaklyClosedIn A B :=
  Iff.rfl

theorem frattini_decomp (c : Ctx23L D Ch) {m : G} (hm : m ∈ D.M) :
    ∃ k ∈ D.M ⊓ Subgroup.centralizer (D.U : Set G),
      ∃ n ∈ D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G), m = k * n := by
  have hV : IsElemAbelian 2 D.U :=
    (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
  have hW0T : E3.wClos D.U 0 D.T ≤ D.T := E3.wClos_le 0 D.T
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (E3.wClos D.U 0 D.T) D.T :=
    isWeaklyClosedIn_iff.mpr
      (CFSG.LocalAnalysis.WeakClosure81.wClos_zero_isWeaklyClosedIn hV)
  have hMnormU : D.M ≤ Subgroup.normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  have hMnormC : D.M ≤ Subgroup.normalizer (Subgroup.centralizer (D.U : Set G) : Set G) :=
    hMnormU.trans (normalizer_le_normalizer_centralizer D.U)
  have hKn : D.M ≤
      Subgroup.normalizer ((D.M ⊓ Subgroup.centralizer (D.U : Set G)) : Set G) :=
    (le_inf Subgroup.le_normalizer hMnormC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hP0K : E3.wClos D.U 0 D.T ≤ D.M ⊓ Subgroup.centralizer (D.U : Set G) :=
    le_inf (hW0T.trans D.sylowM.le) (wClos_zero_le_centralizer c)
  exact uc22p22k_frattini (p := 2) D.sylowM hW0T hwc inf_le_left hKn hP0K m hm

theorem frattini_U (c : Ctx23L D Ch) :
    D.M = (D.M ⊓ Subgroup.centralizer (D.U : Set G)) ⊔
      (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) := by
  refine le_antisymm ?_ ?_
  · intro m hm
    obtain ⟨k, hkK, n, hn, hkn⟩ := frattini_decomp c hm
    rw [hkn]
    exact mul_mem (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right hn)
  · exact sup_le inf_le_left inf_le_left

theorem U_eq_conjClosure_normalizer_wClos (c : Ctx23L D Ch) :
    D.U = conjClosure (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) D.Z := by
  let Y : Subgroup G := D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)
  have hYleM : Y ≤ D.M := inf_le_left
  have hUeq : D.U = Quasithin.conjClosure D.Z D.M := by
    rw [Data.U, uCore_eq_conjClosure, ← omegaOneCenterIn_eq_quasithinOmegaOneCenter]
    rfl
  refine le_antisymm ?_ ?_
  · calc D.U = Quasithin.conjClosure D.Z D.M := hUeq
      _ ≤ conjClosure Y D.Z := by
        refine Quasithin.conjClosure_le fun m hm z hz => ?_
        obtain ⟨k, hk, n, hn, hkn⟩ := frattini_decomp c hm
        have hzU : z ∈ D.U := by
          rw [hUeq]
          exact Quasithin.le_conjClosure D.Z D.M hz
        have hnU : n * z * n⁻¹ ∈ D.U :=
          ((Subgroup.mem_normalizer_iff.mp ((le_normalizer_uCore D.M D.T) hn.1)) z).mp hzU
        have hcomm : (n * z * n⁻¹) * k = k * (n * z * n⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hk.2 _ hnU
        have hkconj : k * (n * z * n⁻¹) * k⁻¹ = n * z * n⁻¹ := by
          rw [← hcomm]
          group
        have hmem : n * z * n⁻¹ ∈ conjClosure Y D.Z :=
          ((Subgroup.mem_normalizer_iff.mp
            (uc22p22v_le_normalizer_conjClosure Y D.Z ⟨hn.1, hn.2⟩)) z).mp
            (uc22p22v_le_conjClosure Y D.Z hz)
        have hmul : (k * n) * z * (k * n)⁻¹ = k * (n * z * n⁻¹) * k⁻¹ := by
          group
        rw [hkn, hmul, hkconj]
        exact hmem
  · refine uc22p22v_conjClosure_le ?_ (Data.Z_le_U D)
    exact hYleM.trans (le_normalizer_uCore D.M D.T)

theorem irrOn_normalizer_wClos (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z)
    (hirr : IrrOn (c.L0 ⊓ D.M) c.U0) :
    IrrOn (D.M ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) D.U := by
  intro W hWU hYW
  have hMW : D.M ≤ Subgroup.normalizer (W : Set G) := by
    rw [frattini_U c]
    refine sup_le ?_ hYW
    exact inf_le_right.trans
      ((Subgroup.centralizer_le hWU).trans (Subgroup.centralizer_le_normalizer (W : Set G)))
  exact irrOn_U c hU0 hirr W hWU hMW

theorem centralizersInM_U (c : Ctx23L D Ch) :
    CFSG.LocalAnalysis.WeakClosure81.CentralizersInM D.U (c.L0 ⊔ D.T) D.T := by
  intro z hzT hzcent hz1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp D.sylowM.isPGroup) ⟨z, hzT⟩
  have hk' : orderOf z = 2 ^ k := by simpa using hk
  have hZpow2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk'])
  have hZpowne : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    have : z ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers z
    exact hz1 (Subgroup.mem_bot.mp this)
  obtain ⟨y, hyz, hyord⟩ := exists_mem_orderOf_two_of_isPGroup hZpow2 hZpowne
  have hyT : y ∈ D.T := (Subgroup.zpowers_le.mpr hzT) hyz
  have hycent : ∀ t ∈ D.T, y * t = t * y := by
    intro t ht
    have hcomm : Commute y t := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyz
      exact (show Commute z t from hzcent t ht).zpow_left m
    exact hcomm.eq
  have hy2 : y ^ 2 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hyZ : y ∈ D.Z :=
    CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
      ⟨hyT, fun t ht => (hycent t ht).symm, by simpa [pow_two] using hy2⟩
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    exact absurd hyord (by norm_num)
  have hyU : y ∈ D.U := Data.Z_le_U D hyZ
  have hCy : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    have hCeq : Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hCeq]
    exact Subgroup.centralizer_le (by simpa using hyz)
  exact (inf_le_right.trans hCy).trans
    ((Ctx23.centralizer_le_M c.toCtx23 hyU hy1).trans (le_normalizer_uCore D.M D.T))

theorem isCalH_U (c : Ctx23L D Ch) :
    CFSG.LocalAnalysis.WeakClosure81.IsCalH D.U (c.L0 ⊔ D.T) :=
  TwelveSeven.isCalH_of_mem_hSet D (uc22p22e_inCalV_U D) c.hL0.1.2.2.1

theorem wClos_eq_of_gammaSet_le {V Q T : Subgroup G} {i : ℕ}
    (hQ : ∀ A ∈ E3.gammaSet V i T, A ≤ Q) (hQT : Q ≤ T) :
    E3.wClos V i T = E3.wClos V i Q := by
  refine le_antisymm ?_ ?_
  · exact E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨hQ A hA, hA.2⟩
  · exact E3.wClos_le_of_forall fun A hA => E3.le_wClos (E3.gammaSet_mono hQT hA)

theorem normalizer_wClos_mem_hSet (c : Ctx23L D Ch)
    (hL0W : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) :
    Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) ∈ hSet D.T D.M := by
  have hUleW : D.U ≤ E3.wClos D.U 0 D.T :=
    E3.le_wClos ⟨Data.u_le_T D, 1, by rw [conjSubgroup_one],
      by rw [conjSubgroup_one, E3.mQuot_self]⟩
  have hWne : E3.wClos D.U 0 D.T ≠ ⊥ :=
    fun h => U_ne_bot c (le_bot_iff.mp (h ▸ hUleW))
  have hW2 : IsPGroup 2 (E3.wClos D.U 0 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  have hNT : D.T ≤ Subgroup.normalizer (D.T : Set G) := Subgroup.le_normalizer
  have hTW : D.T ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
    hNT.trans (E3.normalizer_le_normalizer_wClos (V := D.U) (i := 0) D.T)
  refine ⟨hTW, fun h => Ctx23L.L0_not_le_M c (hL0W.trans h), ?_⟩
  exact D.standing.charTwo _ ⟨_, hWne, hW2, rfl⟩
