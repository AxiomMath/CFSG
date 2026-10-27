module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Mbar_eq_barSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (N : Subgroup G) :
    Mbar N (⊥ : Subgroup G) A hA = barSub (⊥ : Subgroup G) A hA N := rfl

theorem N_le_stabTil_of_le_normalizer {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    c.N ≤ stabTil (⊥ : Subgroup G) A :=
  le_inf hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)

theorem isSylowIn_T_Mbar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    IsSylowIn 2 (barSub (⊥ : Subgroup G) A hA D.T) (Mbar c.N (⊥ : Subgroup G) A hA) := by
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hTN : D.T ≤ c.N := Ctx23L.T_le_N c
  have hS : IsSylowIn 2 (D.T ⊓ c.N) c.N :=
    Ctx23L.isSylowIn_inf_of_le_normalizer (N := c.N) (hTN.trans Subgroup.le_normalizer)
  have hS' : IsSylowIn 2 D.T c.N := by simpa [inf_eq_left.mpr hTN] using hS
  simpa [Mbar_eq_barSub hA c.N] using isSylowIn_barSub hA hTN hNstab hS'

theorem isKGroup_Mbar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) (h208 : S20_8 D)
    (h1930 : H1930 D) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    CFSG.Open.IsKGroup ↥(Mbar c.N (⊥ : Subgroup G) A hA) := by
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hNtop : c.N ≠ ⊤ := (Ctx23L.N_facts c h208 h1930).2.2.2.1
  simpa [Mbar_eq_barSub hA c.N] using isKGroup_barSub c hA hNstab hNtop

theorem o2Trivial_Mbar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    O2Trivial (Mbar c.N (⊥ : Subgroup G) A hA) := by
  simpa [Mbar_eq_barSub hA c.N] using Ctx23L.o2Trivial_barSub c hA hAV hAN hAne hmin

theorem isIrrOn_Mbar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    IsIrrOn (Mbar c.N (⊥ : Subgroup G) A hA) ⊤ ⊥ := by
  simpa [Mbar_eq_barSub hA c.N] using Ctx23L.isIrrOn_barSub c hA hAV hAN hAne hmin

theorem isComponentOf_K_Mbar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAV : A ≤ c.V) (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    IsComponentOf (barSub (⊥ : Subgroup G) A hA K) (Mbar c.N (⊥ : Subgroup G) A hA) := by
  simpa [Mbar_eq_barSub hA c.N] using
    isComponentOf_barSub_of_sup_conj c h208 h1930 hA hAV hAN hAne hK hgen

omit [Finite G] in
theorem barSub_K_ne_bot {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K) Y) :
    barSub (⊥ : Subgroup G) A hA K ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot _).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcomp.2.2))

theorem Hinf_eq_self_of_perfect {X : Type} [Group X] [Finite X] (H : Subgroup X)
    (hperf : ⁅H, H⁆ = H) : Hinf H = H :=
  le_antisymm (uc22p21c_Hinf_le H) (uc22p21c_le_Hinf le_rfl hperf)

theorem Hinf_barSub_K_eq {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K) Y) :
    Hinf (barSub (⊥ : Subgroup G) A hA K) = barSub (⊥ : Subgroup G) A hA K :=
  Hinf_eq_self_of_perfect _ (CFSG.Quasithin.B15P4.perfect_of_isComponentOf hcomp)

theorem barSub_eq_iSup_conj {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) :
    barSub (⊥ : Subgroup G) A hA c.L =
      ⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj t).toMonoidHom := by
  classical
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) A :=
    ((CFSG.Quasithin.A3.subnormal_le hK.1).trans (Ctx23L.L_le_N c)).trans hNstab
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A :=
    (Ctx23L.T_le_N c).trans hNstab
  have hKtstab : ∀ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ≤
      stabTil (⊥ : Subgroup G) A := by
    intro t
    calc K.map (MulAut.conj (t : G)).toMonoidHom
        ≤ (stabTil (⊥ : Subgroup G) A).map (MulAut.conj (t : G)).toMonoidHom :=
          Subgroup.map_mono hKstab
      _ = stabTil (⊥ : Subgroup G) A :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hTstab t.2))
  have hiSup : barSub (⊥ : Subgroup G) A hA c.L =
      ⨆ t : D.T,
        (barSub (⊥ : Subgroup G) A hA K).map
          (MulAut.conj (actTil (⊥ : Subgroup G) A hA ⟨(t : G), hTstab t.2⟩)).toMonoidHom := by
    conv_lhs => rw [hgen]
    have hiSupK : barSub (⊥ : Subgroup G) A hA
        (⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom) =
        ⨆ t : D.T, barSub (⊥ : Subgroup G) A hA
          (K.map (MulAut.conj (t : G)).toMonoidHom) :=
      barSub_iSup_of_le (V₀ := ⊥) (V := A) hA (fun t => hKtstab t)
    rw [hiSupK]
    refine iSup_congr fun t => ?_
    rw [TwelveTwentyThree.barSub_map_conj hA hKstab (hTstab t.2)]
  refine hiSup.trans (le_antisymm ?_ ?_)
  · refine iSup_le fun t =>
      le_iSup₂_of_le (actTil (⊥ : Subgroup G) A hA ⟨(t : G), hTstab t.2⟩)
        (actTil_mem_barSub (⊥ : Subgroup G) A hA t.2 (hTstab t.2)) le_rfl
  · refine iSup₂_le fun s hs => ?_
    obtain ⟨g, hgT, hgs⟩ := (mem_barSub (⊥ : Subgroup G) A hA D.T s).1 hs
    refine le_iSup_of_le ⟨g, hgT⟩ ?_
    rw [show actTil (⊥ : Subgroup G) A hA ⟨g, hTstab hgT⟩ = s from hgs]

theorem Ctx23L.fourteen_five {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h145 : Inputs1719.W4Thm14_5) (h208 : S20_8 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hncard : (conjSet (barSub (⊥ : Subgroup G) A hA K)
      (barSub (⊥ : Subgroup G) A hA D.T)).ncard ≤ 2)
    {P : Subgroup G} {e : ℕ}
    (hPle : barSub (⊥ : Subgroup G) A hA P ≤ barSub (⊥ : Subgroup G) A hA K)
    (hPpar : IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
      ((barSub (⊥ : Subgroup G) A hA P).subgroupOf (barSub (⊥ : Subgroup G) A hA K)))
    (hHinfPne : Hinf (barSub (⊥ : Subgroup G) A hA P) ≠ ⊥)
    (hnorm : normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA P : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))))
    (hcomm : commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
      (Hinf (barSub (⊥ : Subgroup G) A hA P)) ≠ ⊥)
    (hnParam : NParam (Hinf (barSub (⊥ : Subgroup G) A hA P)) c.n) (hn2 : 2 < c.n)
    (hshape : ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsSz ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsU3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
        IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) e) ∨
      (((barSub (⊥ : Subgroup G) A hA K).subgroupOf (Mbar c.N (⊥ : Subgroup G) A hA)).Normal ∧
        (IsL3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsSL3 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsSp4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsU4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          IsG2 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          Is3D4 ↥(barSub (⊥ : Subgroup G) A hA K) e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .twistedF4 0 2 e ∨
          (e = 2 ∧ IsU5 ↥(barSub (⊥ : Subgroup G) A hA K) 2) ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .PSL 4 2 e ∨
          LieModel ↥(barSub (⊥ : Subgroup G) A hA K) .PSp 3 2 e ∨
          IsOmega8m ↥(barSub (⊥ : Subgroup G) A hA K) e))))
    (hminPar : ∀ Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      Q < barSub (⊥ : Subgroup G) A hA P →
      IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
        (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) →
      normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
        Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) →
      Hinf Q = ⊥)
    (hbounds : ∃ K₀ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      ∃ W₀ : Subgroup (Vtil (⊥ : Subgroup G) A hA),
      K₀ = (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
        (Hinf (barSub (⊥ : Subgroup G) A hA P)).map (MulAut.conj t).toMonoidHom) ∧
      W₀ = (⨆ k ∈ K₀, (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map
        (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) ∧
      E3.mParam (Mbar c.N (⊥ : Subgroup G) A hA) ≤
        E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) + 1 ∧
      E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) ≤ c.n) :
    ((⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
        (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      IsDirSumOver (conjSet (barSub (⊥ : Subgroup G) A hA K)
        (Mbar c.N (⊥ : Subgroup G) A hA)) (fun X => commV X) ∧
      ((IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∧
          BinaryNaturalSL (barSub (⊥ : Subgroup G) A hA K)
            (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 2 c.n) ∨
        (Even c.n ∧ IsOmegaMinus ↥(barSub (⊥ : Subgroup G) A hA K) 4 (c.n / 2) ∧
          NatOmegaMinus (barSub (⊥ : Subgroup G) A hA K)
            (commV (barSub (⊥ : Subgroup G) A hA K)) ⊥ 4 (c.n / 2)))) ∨
      IsNaturalClassicalModule
        (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
          (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) c.n ∨
      (Even c.n ∧ IsOmegaMinus
          ↥(⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
            (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) 4 (c.n / 2) ∧
        NatOmegaMinus
          (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
            (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) ⊤ ⊥ 4
            (c.n / 2)) := by
  classical
  obtain ⟨K₀, W₀, hK₀, hW₀, hb1, hb2⟩ := hbounds
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K)
      (Mbar c.N (⊥ : Subgroup G) A hA) :=
    isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  have hKgroup' : CFSG.IsKGroup ↥(Mbar c.N (⊥ : Subgroup G) A hA) :=
    CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple
      (isKGroup_Mbar c h208 h1930 hA hAN)
  have hO2 : O2Trivial (Mbar c.N (⊥ : Subgroup G) A hA) :=
    o2Trivial_Mbar c hA hAV hAne hAN hmin
  have hirr : IsIrrOn (Mbar c.N (⊥ : Subgroup G) A hA) ⊤ ⊥ :=
    isIrrOn_Mbar c hA hAV hAne hAN hmin
  have hTY : barSub (⊥ : Subgroup G) A hA D.T ≤ Mbar c.N (⊥ : Subgroup G) A hA :=
    barSub_mono (⊥ : Subgroup G) A hA (Ctx23L.T_le_N c)
  have hTsyl : IsSylowIn 2 (barSub (⊥ : Subgroup G) A hA D.T)
      (Mbar c.N (⊥ : Subgroup G) A hA) :=
    isSylowIn_T_Mbar c hA hAN
  have hfix : fixV (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj t).toMonoidHom) = ⊥ := by
    rw [← barSub_eq_iSup_conj c hA hAN hK hgen]
    exact fixV_barSub_eq_bot c hA hAV hAN
  exact h145 (Vtil (⊥ : Subgroup G) A hA) (s15_Infra_vtil_sq_eq_one ⊥ A hA)
    (Mbar c.N (⊥ : Subgroup G) A hA) (barSub (⊥ : Subgroup G) A hA K)
    (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA P) e c.n
    hKgroup' hO2 hirr hcomp hTY hTsyl hfix hncard hshape hPle hPpar hHinfPne hnorm hcomm hnParam
    hn2
    hminPar K₀ hK₀ W₀ hW₀ hb1 hb2
    (⨆ g ∈ Mbar c.N (⊥ : Subgroup G) A hA,
      (barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj g).toMonoidHom) rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
