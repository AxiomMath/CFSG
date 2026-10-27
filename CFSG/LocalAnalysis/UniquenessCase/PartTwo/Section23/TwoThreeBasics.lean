module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.A78Sp4.AuxLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3c
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Data

theorem u_le_T (D : Data G) : D.U ≤ D.T :=
  ((uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).1 |>.trans inf_le_left)
    |>.trans (uc22p22e_pCoreOf_le_T D)

theorem u_inf_centralizer_T (D : Data G) :
    D.U ⊓ Subgroup.centralizer (D.T : Set G) = D.Z := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
      ⟨u_le_T D hx.1,
        fun t ht => (Subgroup.mem_centralizer_iff.mp hx.2 t ht),
        (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2.2 x hx.1⟩
  · refine le_inf (Z_le_U D) ?_
    exact ((omegaOneCenterIn_le_inf_centralizer D.T).trans inf_le_right)

end Data

namespace Ctx23

theorem centralizer_le_M {D : Data G} {Ch : Choice2011 G} (c : Ctx23 D Ch) {u : G}
    (hu : u ∈ D.U) (h1 : u ≠ 1) : Subgroup.centralizer ({u} : Set G) ≤ D.M :=
  Data.centralizer_le_of_mem_U D c.hTI hu h1

theorem mem_M_of_ne_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23 D Ch) {x : G}
    (h : D.U ⊓ conjSubgroup x D.U ≠ ⊥) : x ∈ D.M := by
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hu1' : (u : G) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hxU : x⁻¹ * (u : G) * x ∈ D.U :=
    CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp u.2.2
  have hxU' : x⁻¹ * (u : G) * (x⁻¹)⁻¹ ∈ D.U := by simpa using hxU
  have hxM : x⁻¹ ∈ D.M :=
    Data.mem_M_of_conj_mem_U D c.hTI u.2.1 hu1' hxU'
  simpa using D.M.inv_mem hxM

end Ctx23

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem T_le_N : D.T ≤ c.N :=
  (le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)

theorem L_le_N : c.L ≤ c.N :=
  (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_N D Ch c)

theorem L_not_le_M : ¬ c.L ≤ D.M := by
  intro hLM
  exact c.hL.1.2.2.1.2.1 (sup_le hLM D.sylowM.le)

private theorem isTwoLocal_N : IsTwoLocal c.N := by
  have hmem : c.N ∈ calMOf (c.L ⊔ D.T) := by rw [c.hN]; simp
  exact hmem.1.1

private theorem isSylowOf_T_N : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N := by
  have h1 : ¬ 2 ∣ D.T.index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG).2.2
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨T_le_N c, D.sylowM.isPGroup, fun hdvd => ?_⟩
  exact h1 (hdvd.trans (Subgroup.relIndex_dvd_index_of_le (T_le_N c)))

private def X : Subgroup G :=
  ⨆ K ∈ calLOf D.T D.M (Subgroup.normalizer (c.L : Set G)), K

private theorem N_eq_normalizer_X (h208 : S20_8 D) (h1930 : H1930 D) :
    c.N = Subgroup.normalizer ((X c : Subgroup G) : Set G) := by
  have h := h208 h1930 c.L c.hL
  rw [c.hN] at h
  exact Set.singleton_eq_singleton_iff.mp h

private theorem isSubnormal_L_X (h208 : S20_8 D) (h1930 : H1930 D) :
    CFSG.Open.IsSubnormal c.L (X c) := by
  have hLmem : c.L ∈ calLOf D.T D.M (Subgroup.normalizer (c.L : Set G)) :=
    ⟨c.hL.1, CFSG.Quasithin.A3.subnormal_of_normal Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)⟩
  have hLX : c.L ≤ X c := le_iSup₂_of_le c.L hLmem le_rfl
  have hXle : X c ≤ Subgroup.normalizer (c.L : Set G) :=
    iSup₂_le fun K hK => CFSG.Quasithin.A3.subnormal_le hK.2
  exact CFSG.Quasithin.A3.subnormal_of_le_of_le
    (CFSG.Quasithin.A3.subnormal_of_normal Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl))
    hLX hXle

theorem N_facts (h208 : S20_8 D) (h1930 : H1930 D) :
    D.T ≤ c.N ∧ c.L ≤ c.N ∧ CFSG.Open.IsSubnormal c.L c.N ∧ c.N ≠ ⊤ ∧
      (c.N ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 c.N : Set G) ≤
        CFSG.Open.pCoreOf 2 c.N) := by
  have hXnorm := N_eq_normalizer_X c h208 h1930
  have hleXN : X c ≤ c.N := hXnorm.symm ▸ Subgroup.le_normalizer
  have hXN : CFSG.Open.IsSubnormal (X c) c.N :=
    CFSG.Quasithin.A3.subnormal_of_normal hleXN (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hleXN]
      exact le_of_eq hXnorm)
  have hsub : CFSG.Open.IsSubnormal c.L c.N :=
    CFSG.Quasithin.A3.subnormal_trans (isSubnormal_L_X c h208 h1930) hXN
  have hmax : rankThreeIsMaxTwoLocal c.N := by
    have hmem : c.N ∈ calMOf (c.L ⊔ D.T) := by rw [c.hN]; simp
    exact hmem.1
  haveI : IsSimpleGroup G := D.standing.simple
  exact ⟨T_le_N c, L_le_N c, hsub,
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hmax.1,
    D.standing.charTwo c.N (isTwoLocal_N c)⟩

theorem pCoreOf_N_le_T : CFSG.Open.pCoreOf 2 c.N ≤ D.T :=
  CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn (uc22p22ta_isSylowIn D (T_le_N c))

private theorem V_eq_uCore : c.V = uCore c.N D.T := by
  rw [Ctx23L.V, Data.Z, uCore, conjClosure, conjSetOf]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun K => iSup_le fun hK => ?_
    obtain ⟨m, hm, rfl⟩ := hK
    exact le_iSup (fun m : c.N =>
      (CFSG.RankThree.PartOne.omegaOneCenterIn D.T).map
        (MulAut.conj (m : G)).toMonoidHom) ⟨m, hm⟩
  · refine iSup_le fun m => ?_
    exact le_iSup_of_le
      ((CFSG.RankThree.PartOne.omegaOneCenterIn D.T).map
        (MulAut.conj (m : G)).toMonoidHom)
      (le_iSup_of_le ⟨m, m.2, rfl⟩ le_rfl)

theorem isElemAbelian_V_basic : IsElemAbelian 2 c.V := by
  rw [V_eq_uCore c]
  exact (uCore_le_and_isElemAbelian D.standing.charTwo (isTwoLocal_N c) (isSylowOf_T_N c)).2

theorem V_le_T_basic : c.V ≤ D.T := by
  rw [V_eq_uCore c]
  exact ((uCore_le_and_isElemAbelian D.standing.charTwo (isTwoLocal_N c) (isSylowOf_T_N c)).1
    |>.trans inf_le_left) |>.trans (pCoreOf_N_le_T c)

theorem V_le_centralizer_pCore : c.V ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 c.N : Set G) := by
  rw [V_eq_uCore c]
  exact (uCore_le_and_isElemAbelian D.standing.charTwo (isTwoLocal_N c) (isSylowOf_T_N c)).1
    |>.trans inf_le_right

theorem inf_Z_ne_bot {X : Subgroup G} (hXV : X ≤ c.V) (hX : X ≠ ⊥)
    (hT : D.T ≤ Subgroup.normalizer (X : Set G)) : X ⊓ D.Z ≠ ⊥ := by
  have hVcomm : ∀ a ∈ c.V, ∀ b ∈ c.V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElemAbelian_V_basic c).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVsq : ∀ a ∈ c.V, a ^ 2 = 1 := (isElemAbelian_V_basic c).2
  have hXe : CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2 X := fun x hx y hy =>
    ⟨hVcomm x (hXV hx) y (hXV hy), by
      simpa [pow_two] using hVsq x (hXV hx)⟩
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
      ⟨V_le_T_basic c (hXV hzX), hzT', by simpa [pow_two] using hVsq z (hXV hzX)⟩
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨z, hzX, hzZ⟩, ?_⟩
  intro h
  exact hz1 (congrArg Subtype.val h)

theorem fixed_L_eq_bot : c.V ⊓ Subgroup.centralizer (c.L : Set G) = ⊥ := by
  by_contra hne
  have hTV : D.T ≤ Subgroup.normalizer (c.V : Set G) :=
    (le_sup_right : D.T ≤ c.L ⊔ D.T).trans (Ctx23L.sup_le_normalizer_V D Ch c)
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hTC : D.T ≤ Subgroup.normalizer (Subgroup.centralizer (c.L : Set G) : Set G) :=
    hTL.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer c.L)
  have hT : D.T ≤ Subgroup.normalizer
      ((c.V ⊓ Subgroup.centralizer (c.L : Set G) : Subgroup G) : Set G) :=
    (le_inf hTV hTC).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨z, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (inf_Z_ne_bot c inf_le_left hne hT)
  have hzC : (z : G) ∈ Subgroup.centralizer (c.L : Set G) := z.2.1.2
  have hzZ : (z : G) ∈ D.Z := z.2.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hLz : c.L ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro l hl
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.mp hzC l hl).symm
  exact L_not_le_M c
    (hLz.trans (Ctx23.centralizer_le_M c.toCtx23 (Data.Z_le_U D hzZ) hz1'))

theorem inf_centralizer_V_le_M (X : Subgroup G) :
    X ⊓ Subgroup.centralizer (c.V : Set G) ≤ D.M := by
  have hZ : D.Z ≠ ⊥ :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup
      (ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM)
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  refine inf_le_right.trans ?_
  refine (Subgroup.centralizer_le ?_).trans
    (Ctx23.centralizer_le_M c.toCtx23 (Data.Z_le_U D z.2) (fun h => hz1 (Subtype.ext h)))
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact uc22p22v_le_conjClosure c.N D.Z z.2

theorem exists_irreducible_submodule :
    ∃ A : Subgroup G, A ≤ c.V ∧ A ≠ ⊥ ∧ c.N ≤ Subgroup.normalizer (A : Set G) ∧
      ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A := by
  have hZ : D.Z ≠ ⊥ :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup
      (ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM)
  have hVne : c.V ≠ ⊥ := fun h =>
    hZ (le_bot_iff.mp (h ▸ uc22p22v_le_conjClosure c.N D.Z))
  let S : Set (Subgroup G) :=
    {A | A ≤ c.V ∧ A ≠ ⊥ ∧ c.N ≤ Subgroup.normalizer (A : Set G)}
  have hSne : S.Nonempty :=
    ⟨c.V, le_rfl, hVne, uc22p22v_le_normalizer_conjClosure c.N D.Z⟩
  obtain ⟨A, hA, hmin⟩ :=
    Set.Finite.exists_minimalFor (fun A : Subgroup G => A) S (Set.toFinite _) hSne
  refine ⟨A, hA.1, hA.2.1, hA.2.2, fun B hBA hBN => ?_⟩
  by_cases hB : B = ⊥
  · exact Or.inl hB
  · exact Or.inr (le_antisymm hBA (hmin ⟨hBA.trans hA.1, hB, hBN⟩ hBA))

theorem A_eq_conjClosure {A : Subgroup G} (hA : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    A = conjClosure c.N (A ⊓ D.Z) := by
  have hT : D.T ≤ Subgroup.normalizer (A : Set G) :=
    (le_sup_right : D.T ≤ c.L ⊔ D.T).trans
      ((Ctx23L.sup_le_N D Ch c).trans hAN)
  have hinf : A ⊓ D.Z ≠ ⊥ := inf_Z_ne_bot c hA hAne hT
  have hAle : conjClosure c.N (A ⊓ D.Z) ≤ A :=
    uc22p22v_conjClosure_le hAN inf_le_left
  have hne : conjClosure c.N (A ⊓ D.Z) ≠ ⊥ := fun h =>
    hinf (le_bot_iff.mp (h ▸ uc22p22v_le_conjClosure c.N (A ⊓ D.Z)))
  have hNA : c.N ≤ Subgroup.normalizer (conjClosure c.N (A ⊓ D.Z) : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N (A ⊓ D.Z)
  rcases hmin _ hAle hNA with h | h
  · exact absurd h hne
  · exact h.symm

theorem L0_le_N : c.L0 ≤ c.N := c.hL0L.trans (L_le_N c)

theorem T_le_normalizer_L0 : D.T ≤ Subgroup.normalizer (c.L0 : Set G) := c.hL0.1.1

theorem isSylowIn_T_inf : IsSylowIn 2 (D.T ⊓ c.L0) c.L0 := by
  have h1 : ¬ 2 ∣ D.T.index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG).2.2
  have hS : CFSG.RankThree.PartOne.IsSylowOf 2 D.T (c.L0 ⊔ D.T) := by
    have h' : CFSG.ABGLocalTools.IsSylowOf 2 D.T (c.L0 ⊔ D.T) := by
      refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
        ⟨le_sup_right, D.sylowM.isPGroup, fun hdvd => ?_⟩
      exact h1 (hdvd.trans (Subgroup.relIndex_dvd_index_of_le
        (le_sup_right : D.T ≤ c.L0 ⊔ D.T)))
    exact CFSG.ABGLocalTools.isSylowOf_iff.mp h'
  have h := CFSG.CGT.PushingUpLit.BHS.FourTwoTools.isSylowOf_inf_of_le_normalizer
    (K := c.L0 ⊔ D.T) (N := c.L0) hS le_sup_left
      (sup_le Subgroup.le_normalizer c.hL0.1.1)
  rw [inf_comm] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem L0_not_le_M : ¬ c.L0 ≤ D.M :=
  fun h => c.hL0.1.2.2.1.2.1 (sup_le h D.sylowM.le)

theorem exists_minTInvParabolic (h209 : S20_9 D) (h1930 : H1930 D) :
    ∃ P : Subgroup G, MinTInvParabolic D.T D.M c.L P ∧ c.L0 = Hinf P := by
  have h := (h209 h1930 c.L c.hL.1) c.L0
  exact h.mp ⟨c.hL0, c.hL0L⟩

theorem three_le_n (hE : UC22P20gExcFacts) (h207 : S20_7 D) : H1930 D → 3 ≤ c.n :=
  fun h1930 => uc22p20g_three_le_of_nparam hE h207 h1930 c.hL0 c.hn

theorem isSylowIn_inf_of_le_normalizer {N : Subgroup G}
    (hTN : D.T ≤ Subgroup.normalizer (N : Set G)) : IsSylowIn 2 (D.T ⊓ N) N := by
  have h1 : ¬ 2 ∣ D.T.index := by
    simpa [Subgroup.relIndex_top_right] using
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG).2.2
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 D.T (N ⊔ D.T) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_sup_right, D.sylowM.isPGroup, fun hdvd => ?_⟩
    exact h1 (hdvd.trans (Subgroup.relIndex_dvd_index_of_le
      (le_sup_right : D.T ≤ N ⊔ D.T)))
  have hS : CFSG.RankThree.PartOne.IsSylowOf 2 D.T (N ⊔ D.T) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hS'
  have h := CFSG.CGT.PushingUpLit.BHS.FourTwoTools.isSylowOf_inf_of_le_normalizer
    (K := N ⊔ D.T) (N := N) hS le_sup_left (sup_le Subgroup.le_normalizer hTN)
  rw [inf_comm] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

private theorem barImage_borel_solvable (h207 : S20_7 D) (hBS : KBorelSolv20_7)
    (h1930 : H1930 D) :
    Group.IsSolvable ↥(barImage c.L
      (c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G))) := by
  have hSyl : IsSylowIn 2 (D.T ⊓ c.L) c.L := isSylowIn_inf_of_le_normalizer c.hL.1.1
  let q : ↥c.L →* Bar2 c.L := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  let Qbar : Sylow 2 (Bar2 c.L) :=
    (hSyl.toSylow).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hBsub : (c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)).subgroupOf c.L =
      Subgroup.normalizer ((D.T ⊓ c.L).subgroupOf c.L : Set ↥c.L) := by
    rw [Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq (inf_le_right : D.T ⊓ c.L ≤ c.L)]
  have hH : barImage c.L
      (c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) =
      Subgroup.normalizer (Qbar : Set (Bar2 c.L)) := by
    rw [barImage, hBsub]
    calc (Subgroup.normalizer ((D.T ⊓ c.L).subgroupOf c.L)).map q
        = Subgroup.normalizer
            (((hSyl.toSylow : Subgroup ↥c.L).map q) : Set (Bar2 c.L)) := by
          rw [CFSG.Quasithin.IsSylowIn.coe_toSylow]
          exact (CFSG.LocalAnalysis.UniquenessCase.UC22.normalizer_map_sylow_eq
            q (QuotientGroup.mk'_surjective _) hSyl.toSylow).symm
      _ = Subgroup.normalizer (Qbar : Set (Bar2 c.L)) := by
          exact congrArg
            (fun H : Subgroup (Bar2 c.L) => Subgroup.normalizer (H : Set (Bar2 c.L)))
            (Sylow.coe_mapSurjective (f := q) (hf := QuotientGroup.mk'_surjective _)
              (P := hSyl.toSylow)).symm
  rw [hH]
  exact hBS (Bar2 c.L) (s20_7Shape_of h207 h1930 c.hL.1) Qbar

private theorem hinf_borel_eq_bot (h207 : S20_7 D) (hBS : KBorelSolv20_7)
    (h1930 : H1930 D) :
    Hinf (c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) = ⊥ := by
  have hBL : c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) ≤ c.L := inf_le_left
  have hSyl : IsSylowIn 2 (D.T ⊓ c.L) c.L := isSylowIn_inf_of_le_normalizer c.hL.1.1
  have hHsolv := barImage_borel_solvable c h207 hBS h1930
  have hOleB : CFSG.Open.pCoreOf 2 c.L ≤
      c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) := by
    have hOleS : CFSG.Open.pCoreOf 2 c.L ≤ D.T ⊓ c.L :=
      CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn hSyl
    exact le_inf (hOleS.trans inf_le_right) (hOleS.trans Subgroup.le_normalizer)
  have hBsolv : Group.IsSolvable ↥(c.L ⊓
      Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) := by
    have hBpre : (c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) =
        barPreimage c.L (barImage c.L
          (c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G))) :=
      (barPreimage_barImage_of_pCoreOf_le hBL hOleB).symm
    rw [hBpre]
    exact uc22s21ru3c_isSolvable_barPreimage hHsolv
  rw [Hinf, CFSG.inSubgroup,
    show CFSG.perfectResidual ↥(c.L ⊓
      Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) = ⊥ from
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mpr
        hBsolv]
  simp

private theorem false_of_borel_not_le_M (h209 : S20_9 D) (h1930 : H1930 D) {B : Subgroup G}
    (hpar : ParabolicOf c.L B) (hTB : D.T ≤ Subgroup.normalizer (B : Set G))
    (hBM : ¬ B ≤ D.M) (hHinfB : Hinf B = ⊥) : False := by
  let Tset : Set (Subgroup G) :=
    {Q | ParabolicOf c.L Q ∧ D.T ≤ Subgroup.normalizer (Q : Set G) ∧
      ¬ Q ≤ D.M ∧ Q ≤ B}
  have hTne : Tset.Nonempty := ⟨B, hpar, hTB, hBM, le_rfl⟩
  obtain ⟨P, hPmem, hPmin⟩ :=
    Set.Finite.exists_minimalFor (fun Q : Subgroup G => Q) Tset (Set.toFinite _) hTne
  have hP : MinTInvParabolic D.T D.M c.L P := by
    refine ⟨⟨hPmem.1, hPmem.2.1, hPmem.2.2.1⟩, ?_⟩
    intro Q hQS hQP
    have hQB : Q ≤ B := hQP.trans hPmem.2.2.2
    exact hPmin ⟨hQS.1, hQS.2.1, hQS.2.2, hQB⟩ hQP
  have hHinfLow : Hinf P ∈ calLLow D.T D.M :=
    (((h209 h1930 c.L c.hL.1) (Hinf P)).mpr ⟨P, hP, rfl⟩).1
  have hHinfPB : Hinf P ≤ B := (uc22p21c_Hinf_le P).trans hPmem.2.2.2
  have hHinfPbot : Hinf P = ⊥ :=
    le_bot_iff.mp
      ((uc22p21c_le_Hinf hHinfPB (uc22p21c_Hinf_perfect P)).trans (le_of_eq hHinfB))
  exact hHinfLow.1.2.2.1.2.1 (by rw [hHinfPbot]; simpa using D.sylowM.le)

theorem borel_le_M (h207 : S20_7 D) (h209 : S20_9 D) (hBS : KBorelSolv20_7)
    (h1930 : H1930 D) :
    c.L ⊓ Subgroup.normalizer ((D.T ⊓ c.L : Subgroup G) : Set G) ≤ D.M := by
  classical
  set S : Subgroup G := D.T ⊓ c.L with hSdef
  set B : Subgroup G := c.L ⊓ Subgroup.normalizer (S : Set G) with hBdef
  have hBL : B ≤ c.L := inf_le_left
  have hSyl : IsSylowIn 2 S c.L := isSylowIn_inf_of_le_normalizer c.hL.1.1
  have hBsub : B.subgroupOf c.L =
      Subgroup.normalizer (S.subgroupOf c.L : Set ↥c.L) := by
    rw [hBdef, hSdef, Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq (inf_le_right : D.T ⊓ c.L ≤ c.L)]
  have hHinfB : Hinf B = ⊥ := hinf_borel_eq_bot c h207 hBS h1930
  have hTS : D.T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    constructor
    · intro hx
      exact ⟨D.T.mul_mem (D.T.mul_mem ht hx.1) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (c.hL.1.1 ht) x).mp hx.2⟩
    · intro hx
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (c.hL.1.1 ht) x).mpr hx.2⟩
      simpa [mul_assoc] using D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hx.1) ht
  have hTB : D.T ≤ Subgroup.normalizer (B : Set G) :=
    (le_inf c.hL.1.1 (hTS.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  by_contra hBM
  have hpar : ParabolicOf c.L B := by
    refine parabolicOf_iff.mpr ⟨hBL, ⟨hSyl.toSylow, ?_⟩⟩
    rw [hBsub]
    exact le_of_eq (congrArg
      (fun H : Subgroup ↥c.L => Subgroup.normalizer (H : Set ↥c.L))
      (CFSG.Quasithin.IsSylowIn.coe_toSylow (P := S) (H := c.L) hSyl))
  exact false_of_borel_not_le_M c h209 h1930 hpar hTB hBM hHinfB

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
