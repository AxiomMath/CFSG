module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNinePointStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Dich
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelSolv20_7.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveInst
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveNum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem centralizer_inf_commutator_le_pCore {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    c.L ⊓ Subgroup.centralizer (A : Set G) ≠ c.L ∧
      ⁅c.L ⊓ Subgroup.centralizer (A : Set G), c.L⁆ ≤
        CFSG.Open.pCoreOf 2 c.L := by
  let X : Subgroup G := c.L ⊓ Subgroup.centralizer (A : Set G)
  have hXL : X ≤ c.L := inf_le_left
  have hLX : c.L ≤ Subgroup.normalizer (X : Set G) := by
    have hLA : c.L ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.L_le_N c).trans hAN
    exact (le_inf Subgroup.le_normalizer
      (hLA.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hXn : (X.subgroupOf c.L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hLX
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) := by
    have hTA : D.T ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.T_le_N c).trans hAN
    exact (le_inf c.hL.1.1
      (hTA.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hXne : X ≠ c.L := by
    intro hXc
    have hLle : c.L ≤ Subgroup.centralizer (A : Set G) := hXc ▸ inf_le_right
    have hAleC : A ≤ Subgroup.centralizer (c.L : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (Subgroup.mem_centralizer_iff.mp (hLle hl) a ha).symm
    have hAle : A ≤ c.V ⊓ Subgroup.centralizer (c.L : Set G) := le_inf hAV hAleC
    rw [Ctx23L.fixed_L_eq_bot c] at hAle
    exact hAne (le_bot_iff.mp hAle)
  have hcomm : ⁅X, c.L⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (Ctx23L.commutator_le_pCoreOf_or_eq c hXL hXn hTX).resolve_left hXne
  exact ⟨hXne, hcomm⟩

private theorem map_subgroupOf_le_center_of_commutator_le_pCore {D : Data G}
    {Ch : Choice2011 G} (c : Ctx23L D Ch) {X : Subgroup G} (hXL : X ≤ c.L)
    (hcomm : ⁅X, c.L⁆ ≤ CFSG.Open.pCoreOf 2 c.L) :
    (X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) ≤
      Subgroup.center (Bar2 c.L) := by
  intro z hz
  obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥c.L) y
  have hxX' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hmem : ⁅(x : G), (w : G)⁆ ∈ CFSG.Open.pCoreOf 2 c.L :=
    Subgroup.commutator_le.mp hcomm (x : G) hxX' (w : G) w.2
  have hmemL : ⁅x, w⁆ ∈ CFSG.pCore 2 ↥c.L := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 c.L, Subgroup.mem_subgroupOf,
      show ((⁅x, w⁆ : ↥c.L) : G) = ⁅(x : G), (w : G)⁆ from
        map_commutatorElement (Subgroup.subtype c.L) x w]
    exact hmem
  have hmemL' : ⁅w, x⁆ ∈ CFSG.pCore 2 ↥c.L := by
    have h : ⁅w, x⁆ = ⁅x, w⁆⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [h]
    exact (CFSG.pCore 2 ↥c.L).inv_mem hmemL
  have h1 : ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) w,
      QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) x⁆ = 1 := by
    rw [← map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) w x]
    exact (QuotientGroup.eq_one_iff ⁅w, x⁆).mpr hmemL'
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem le_parabolic_of_commutator_le_pCore {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A P : Subgroup G}
    (hP : MinTInvParabolic D.T D.M c.L P)
    (hcomm : ⁅c.L ⊓ Subgroup.centralizer (A : Set G), c.L⁆ ≤
      CFSG.Open.pCoreOf 2 c.L) :
    c.L ⊓ Subgroup.centralizer (A : Set G) ≤ P := by
  let X : Subgroup G := c.L ⊓ Subgroup.centralizer (A : Set G)
  have hXL : X ≤ c.L := inf_le_left
  have hcenter := map_subgroupOf_le_center_of_commutator_le_pCore c hXL hcomm
  intro x hxX
  let xL : ↥c.L := ⟨x, hXL hxX⟩
  have hxmem : QuotientGroup.mk xL ∈ Subgroup.center (Bar2 c.L) :=
    hcenter (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxX))
  obtain ⟨hOP, -, hPpar⟩ := hP.1.1
  obtain ⟨S, hS⟩ := hPpar
  have hxN : QuotientGroup.mk xL ∈
      Subgroup.normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L)) :=
    Subgroup.center_le_normalizer ((S : Subgroup (Bar2 c.L)) : Set (Bar2 c.L)) hxmem
  obtain ⟨p, hpP, hpx⟩ :=
    Subgroup.mem_map.mp (hS hxN : QuotientGroup.mk xL ∈
      (P.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)))
  have hpPg : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hpP
  have hk : p⁻¹ * xL ∈ CFSG.pCore 2 ↥c.L := (QuotientGroup.eq).1 hpx
  have hkO : ((p⁻¹ * xL : ↥c.L) : G) ∈ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.mem_openPCoreOf_iff (p⁻¹ * xL)).mpr hk
  have hkP : ((p⁻¹ * xL : ↥c.L) : G) ∈ P := hOP hkO
  have he : x = (p : G) * ((p⁻¹ * xL : ↥c.L) : G) := by simp [xL]
  rw [he]
  exact P.mul_mem hpPg hkP

theorem Ctx23L.centralizer_le_parabolic_single {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L)
    {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P)
    (hL0P : c.L0 = Hinf P) :
    c.L ⊓ Subgroup.centralizer (A : Set G) ≤ P :=
  le_parabolic_of_commutator_le_pCore c hP
    (centralizer_inf_commutator_le_pCore c hAV hAne hAN).2

theorem Ctx23L.normalizer_preBarSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hTQ : barSub (⊥ : Subgroup G) A hA D.T ≤
      Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))) :
    D.T ≤ Subgroup.normalizer (preBarSub c.L (⊥ : Subgroup G) A hA Q : Set G) := by
  intro t ht
  have htN : t ∈ c.N := Ctx23L.T_le_N c ht
  have htstab : t ∈ stabTil (⊥ : Subgroup G) A :=
    N_le_stabTil_of_le_normalizer c hAN htN
  have hforward : ∀ s ∈ D.T, ∀ x ∈ preBarSub c.L (⊥ : Subgroup G) A hA Q,
      s * x * s⁻¹ ∈ preBarSub c.L (⊥ : Subgroup G) A hA Q := by
    intro s hs x hx
    obtain ⟨hxL, hxstab, hxQ⟩ := (mem_preBarSub c.L (⊥ : Subgroup G) A hA Q).1 hx
    have hsN : s ∈ c.N := Ctx23L.T_le_N c hs
    have hsstab : s ∈ stabTil (⊥ : Subgroup G) A :=
      N_le_stabTil_of_le_normalizer c hAN hsN
    have hsmap : c.L.map (MulAut.conj s).toMonoidHom = c.L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.hL.1.1 hs)
    have hsL : s * x * s⁻¹ ∈ c.L := hsmap ▸ Subgroup.mem_map_of_mem _ hxL
    have hstab : s * x * s⁻¹ ∈ stabTil (⊥ : Subgroup G) A :=
      (stabTil (⊥ : Subgroup G) A).mul_mem
        ((stabTil (⊥ : Subgroup G) A).mul_mem hsstab hxstab)
        ((stabTil (⊥ : Subgroup G) A).inv_mem hsstab)
    refine (mem_preBarSub c.L (⊥ : Subgroup G) A hA Q).2 ⟨hsL, hstab, ?_⟩
    have hsub : (⟨s * x * s⁻¹, hstab⟩ : ↥(stabTil (⊥ : Subgroup G) A)) =
        ⟨s, hsstab⟩ * ⟨x, hxstab⟩ * ⟨s, hsstab⟩⁻¹ := Subtype.ext rfl
    rw [hsub, map_mul, map_mul, map_inv]
    have hQmap : Q.map (MulAut.conj (actTil (⊥ : Subgroup G) A hA ⟨s, hsstab⟩)).toMonoidHom =
        Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hTQ (actTil_mem_barSub (⊥ : Subgroup G) A hA hs hsstab))
    exact hQmap ▸ Subgroup.mem_map_of_mem _ hxQ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward t ht x
  · intro hx
    have h := hforward t⁻¹ (D.T.inv_mem ht) (t * x * t⁻¹) hx
    simpa [mul_assoc] using h

theorem barSub_le_normalizer_of_le_normalizer {A H X : Subgroup G}
    (hA : IsElemAbelian 2 A) (hH : H ≤ stabTil (⊥ : Subgroup G) A)
    (hX : X ≤ stabTil (⊥ : Subgroup G) A)
    (hNX : H ≤ Subgroup.normalizer (X : Set G)) :
    barSub (⊥ : Subgroup G) A hA H ≤
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA X : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) := by
  intro y hy
  obtain ⟨g, hgH, hgy⟩ := (mem_barSub (⊥ : Subgroup G) A hA H y).1 hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc (barSub (⊥ : Subgroup G) A hA X).map (MulAut.conj y).toMonoidHom
      = barSub (⊥ : Subgroup G) A hA (X.map (MulAut.conj (g : G)).toMonoidHom) := by
        rw [← hgy]
        exact (TwelveTwentyThree.barSub_map_conj hA hX (hH hgH)).symm
    _ = barSub (⊥ : Subgroup G) A hA X :=
        congrArg (fun Y => barSub (⊥ : Subgroup G) A hA Y)
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNX hgH))

private theorem exists_data_single_nonmin {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h2010 : S20_10 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L) :
    ∃ P : Subgroup G, MinTInvParabolic D.T D.M c.L P ∧ c.L0 = Hinf P ∧
      barSub (⊥ : Subgroup G) A hA P ≤ barSub (⊥ : Subgroup G) A hA K ∧
      IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
        ((barSub (⊥ : Subgroup G) A hA P).subgroupOf
          (barSub (⊥ : Subgroup G) A hA K)) ∧
      Hinf (barSub (⊥ : Subgroup G) A hA P) = barSub (⊥ : Subgroup G) A hA c.L0 ∧
      Hinf (barSub (⊥ : Subgroup G) A hA P) ≠ ⊥ ∧
      normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
        Subgroup.normalizer
          (barSub (⊥ : Subgroup G) A hA P : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) ∧
      commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
        (Hinf (barSub (⊥ : Subgroup G) A hA P)) ≠ ⊥ := by
  classical
  obtain ⟨P, hP, hL0P⟩ := c.exists_minTInvParabolic h209 h1930
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hPstab : P ≤ stabTil (⊥ : Subgroup G) A := hPL.trans hLstab
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.T_le_N c).trans hNstab
  have hPle : barSub (⊥ : Subgroup G) A hA P ≤ barSub (⊥ : Subgroup G) A hA K := by
    rw [hsingle]
    exact barSub_mono (⊥ : Subgroup G) A hA hPL
  have hPparK : IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
      ((barSub (⊥ : Subgroup G) A hA P).subgroupOf
        (barSub (⊥ : Subgroup G) A hA K)) := by
    rw [hsingle]
    exact Ctx23L.isParabolicTwo_barSub c hA hAN hP.1.1
  have hHinfEq : Hinf (barSub (⊥ : Subgroup G) A hA P) =
      barSub (⊥ : Subgroup G) A hA c.L0 := Hinf_barSub_eq c hA hAN hPL hL0P
  have hcomm : commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
      (Hinf (barSub (⊥ : Subgroup G) A hA P)) ≠ ⊥ :=
    commSub_fixV_T_hinf_ne_bot c hA hAV hAne hAN hPL hL0P
  have hHinfPne : Hinf (barSub (⊥ : Subgroup G) A hA P) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hcomm
    exact hcomm (by simp [commSub])
  have hTAle : barSub (⊥ : Subgroup G) A hA D.T ≤
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA P : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) :=
    barSub_le_normalizer_of_le_normalizer hA hTstab hPstab hP.1.2.1
  have hnorm : normIn (barSub (⊥ : Subgroup G) A hA D.T)
      (barSub (⊥ : Subgroup G) A hA K) ≤ Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA P : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) := by
    rw [hsingle]
    exact inf_le_left.trans hTAle
  exact ⟨P, hP, hL0P, hPle, hPparK, hHinfEq, hHinfPne, hnorm, hcomm⟩

private theorem minPar_single {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h2010 : S20_10 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L) {P : Subgroup G} (hP : MinTInvParabolic D.T D.M c.L P)
    (hL0P : c.L0 = Hinf P) :
    ∀ Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      Q < barSub (⊥ : Subgroup G) A hA P →
      IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
        (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) →
      normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
        Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) →
      Hinf Q = ⊥ := by
  classical
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.T_le_N c).trans hNstab
  have hTAnormL : barSub (⊥ : Subgroup G) A hA D.T ≤
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA c.L : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) :=
    barSub_le_normalizer_of_le_normalizer hA hTstab hLstab c.hL.1.1
  intro Q hQlt hQpar hQnorm
  have hQparL : IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA c.L)
      (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA c.L)) := by
    have h := hQpar
    rw [hsingle] at h
    exact h
  have hQnormL : (barSub (⊥ : Subgroup G) A hA D.T ⊓
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA c.L : Set (MulAut (Vtil (⊥ : Subgroup G) A hA)))) ≤
      Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) := by
    simpa [normIn, hsingle] using hQnorm
  have hTQ : barSub (⊥ : Subgroup G) A hA D.T ≤
      Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) :=
    (le_inf le_rfl hTAnormL).trans hQnormL
  exact minimal_parabolic_barSub c h2010 h207 kRankOneBorel_holds kBorelSolv20_7_holds
    h1930 hA hAN hP hL0P
    (Ctx23L.centralizer_le_parabolic_single c h208 h1930 hA hAV hAne hAN hmin hK
      hgen hsingle hP hL0P) Q hQlt hQparL hQnormL
    (Ctx23L.normalizer_preBarSub c hA hAN hTQ)

theorem Ctx23L.exists_fourteen_five_data_single {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h2010 : S20_10 D) (h1930 : H1930 D) (h1A : S23_1A D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hsingle : K = c.L)
    (hnParam : NParam (barSub (⊥ : Subgroup G) A hA c.L0) c.n) :
    ∃ P : Subgroup G,
      barSub (⊥ : Subgroup G) A hA P ≤ barSub (⊥ : Subgroup G) A hA K ∧
      IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
        ((barSub (⊥ : Subgroup G) A hA P).subgroupOf
          (barSub (⊥ : Subgroup G) A hA K)) ∧
      Hinf (barSub (⊥ : Subgroup G) A hA P) = barSub (⊥ : Subgroup G) A hA c.L0 ∧
      Hinf (barSub (⊥ : Subgroup G) A hA P) ≠ ⊥ ∧
      normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
        Subgroup.normalizer
          (barSub (⊥ : Subgroup G) A hA P : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) ∧
      commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
        (Hinf (barSub (⊥ : Subgroup G) A hA P)) ≠ ⊥ ∧
      (∀ Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
        Q < barSub (⊥ : Subgroup G) A hA P →
        IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
          (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) →
        normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
          Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) →
        Hinf Q = ⊥) ∧
      (∃ K₀ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
        ∃ W₀ : Subgroup (Vtil (⊥ : Subgroup G) A hA),
        K₀ = (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
          (Hinf (barSub (⊥ : Subgroup G) A hA P)).map (MulAut.conj t).toMonoidHom) ∧
        W₀ = (⨆ k ∈ K₀, (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map
          (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) ∧
        E3.mParam (Mbar c.N (⊥ : Subgroup G) A hA) ≤
          E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) + 1 ∧
        E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) ≤ c.n) := by
  obtain ⟨P, hP, hL0P, hPle, hPparK, hHinfEq, hHinfPne, hnorm, hcomm⟩ :=
    exists_data_single_nonmin c h207 h208 h209 h2010 h1930 hA hAV hAne hAN hmin hK hgen hsingle
  obtain ⟨K₀, W₀, hK₀, hW₀, hb1, hb2⟩ :=
    aBar_bounds_W4Thm14_5 c h1A h1930 hA hAV hAne hAN hmin hP hL0P
  exact ⟨P, hPle, hPparK, hHinfEq, hHinfPne, hnorm, hcomm,
    minPar_single c h207 h208 h209 h2010 h1930 hA hAV hAne hAN hmin hK hgen hsingle hP hL0P,
    ⟨K₀, W₀, hK₀, hW₀, hb1, hb2⟩⟩

private theorem commSub_fixV_T_join_barSub_ne_bot {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hL0L : c.L0 = c.L) {t : G} (htT : t ∈ D.T)
    (hsup : c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
      (barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)) ≠ ⊥ := by
  obtain ⟨P, hP, hL0P⟩ := c.exists_minTInvParabolic h209 h1930
  have hPle : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hHinfP : Hinf (barSub (⊥ : Subgroup G) A hA P) =
      barSub (⊥ : Subgroup G) A hA c.L := by
    rw [Ctx23L.Hinf_barSub c hA hAN hPle, ← hL0P, hL0L]
  have hcommP := commSub_fixV_T_hinf_ne_bot c hA hAV hAne hAN hPle hL0P
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.T_le_N c).trans hNstab
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) A :=
    (CFSG.Quasithin.A3.subnormal_le hK.1).trans hLstab
  have hKtstab : K.map (MulAut.conj t).toMonoidHom ≤ stabTil (⊥ : Subgroup G) A := by
    calc K.map (MulAut.conj t).toMonoidHom
        ≤ (stabTil (⊥ : Subgroup G) A).map (MulAut.conj t).toMonoidHom :=
          Subgroup.map_mono hKstab
      _ = stabTil (⊥ : Subgroup G) A :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hTstab htT))
  have hsupbar : barSub (⊥ : Subgroup G) A hA c.L =
      barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) := by
    rw [show barSub (⊥ : Subgroup G) A hA c.L =
        barSub (⊥ : Subgroup G) A hA (K ⊔ K.map (MulAut.conj t).toMonoidHom) from by
      rw [hsup]]
    exact s16c7_barSub_sup (⊥ : Subgroup G) A hA hKstab hKtstab
  rw [← hsupbar, ← hHinfP]
  exact hcommP

private theorem fixV_T_le_fixV_map_conj {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A K : Subgroup G} (hA : IsElemAbelian 2 A) {t : G}
    (hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A) (htT : t ∈ D.T)
    (hWfix : fixV (barSub (⊥ : Subgroup G) A hA D.T) ≤
      fixV (barSub (⊥ : Subgroup G) A hA K)) :
    fixV (barSub (⊥ : Subgroup G) A hA D.T) ≤
      fixV ((barSub (⊥ : Subgroup G) A hA K).map
        (MulAut.conj (actTil (⊥ : Subgroup G) A hA ⟨t, hTstab htT⟩)).toMonoidHom) := by
  let x : MulAut (Vtil (⊥ : Subgroup G) A hA) :=
    actTil (⊥ : Subgroup G) A hA ⟨t, hTstab htT⟩
  have hxT : x ∈ barSub (⊥ : Subgroup G) A hA D.T :=
    actTil_mem_barSub (⊥ : Subgroup G) A hA htT (hTstab htT)
  have hle : (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map x.toMonoidHom ≤
      fixV (barSub (⊥ : Subgroup G) A hA D.T) := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ z ∈ barSub (⊥ : Subgroup G) A hA D.T, z w = w :=
      mem_fixV.mp (by simpa using hw)
    rw [mem_fixV]
    intro y hy
    rw [show (MulEquiv.toMonoidHom x) w = w from hw' x hxT]
    exact hw' y hy
  have hWmap : (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map x.toMonoidHom =
      fixV (barSub (⊥ : Subgroup G) A hA D.T) :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective x.injective).ge
  rw [show fixV ((barSub (⊥ : Subgroup G) A hA K).map (MulAut.conj x).toMonoidHom) =
      (fixV (barSub (⊥ : Subgroup G) A hA K)).map x.toMonoidHom from
    fixV_conjBy x (barSub (⊥ : Subgroup G) A hA K)]
  calc fixV (barSub (⊥ : Subgroup G) A hA D.T)
      = (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map x.toMonoidHom := hWmap.symm
    _ ≤ (fixV (barSub (⊥ : Subgroup G) A hA K)).map x.toMonoidHom :=
        Subgroup.map_mono hWfix

private theorem commSub_fixV_T_barSub_K_ne_bot {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hL0L : c.L0 = c.L) :
    commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
      (Hinf (barSub (⊥ : Subgroup G) A hA K)) ≠ ⊥ := by
  obtain ⟨t, htT, -, hsup⟩ := hprod
  have hJoin := commSub_fixV_T_join_barSub_ne_bot c h208 h209 h1930 hA hAV hAne hAN
    hK hgen hL0L htT hsup
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K) (Mbar c.N ⊥ A hA) :=
    isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  have hHinfK : Hinf (barSub (⊥ : Subgroup G) A hA K) =
      barSub (⊥ : Subgroup G) A hA K := Hinf_barSub_K_eq hA hcomp
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.T_le_N c).trans hNstab
  have hKA_t : barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) =
      (barSub (⊥ : Subgroup G) A hA K).map
        (MulAut.conj (actTil (⊥ : Subgroup G) A hA ⟨t, hTstab htT⟩)).toMonoidHom :=
    s16c7_barSub_map_conj (⊥ : Subgroup G) A hA (hTstab htT) K
  intro hbot
  rw [hHinfK] at hbot
  have hWfix : fixV (barSub (⊥ : Subgroup G) A hA D.T) ≤
      fixV (barSub (⊥ : Subgroup G) A hA K) := commSub_eq_bot_iff.mp hbot
  have hWt := fixV_T_le_fixV_map_conj c hA hTstab htT hWfix
  have hzero : commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
      (barSub (⊥ : Subgroup G) A hA K ⊔
        barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom)) = ⊥ := by
    rw [hKA_t, commSub_eq_bot_iff, fixV_sup_eq]
    exact le_inf hWfix hWt
  exact hJoin hzero

private theorem minPar_product {D : Data G}
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) {n : ℕ}
    (hnat : IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) n ∨
      IsSz ↥(barSub (⊥ : Subgroup G) A hA K) n ∨
      IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) n) :
    ∀ Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      Q < barSub (⊥ : Subgroup G) A hA K →
      IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
        (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) →
      normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
        Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) →
      Hinf Q = ⊥ := by
  intro Q hQlt hQpar _
  have hRO : RankOneBorel.RankOneOver ↥(barSub (⊥ : Subgroup G) A hA K) :=
    RankOneBorel.rankOneOver_of_shape (by
      rcases hnat with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
  obtain ⟨S, hS⟩ := hQpar
  have hSH : (S : Subgroup ↥(barSub (⊥ : Subgroup G) A hA K)) ≤
      Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K) :=
    Subgroup.le_normalizer.trans hS
  rcases hRO S (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) hSH with hN | htop
  · haveI : Group.IsSolvable
        ↥(Subgroup.normalizer ((S : Subgroup ↥(barSub (⊥ : Subgroup G) A hA K)) :
          Set ↥(barSub (⊥ : Subgroup G) A hA K))) :=
      CFSG.GH74.GLS.C3.Layer1.U1a.isSolvable_normalizer_sylow_two S
    haveI : Group.IsSolvable
        ↥((Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup ↥(barSub (⊥ : Subgroup G) A hA K)) :
            Set ↥(barSub (⊥ : Subgroup G) A hA K)))) :=
      subgroup_solvable_of_solvable _
    haveI : Group.IsSolvable
        ↥(Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) := by
      refine Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hN).symm.toMonoidHom) ?_
      exact (Subgroup.subgroupOfEquivOfLe hN).symm.injective
    haveI : Group.IsSolvable ↥Q := by
      refine Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQlt.le).symm.toMonoidHom) ?_
      exact (Subgroup.subgroupOfEquivOfLe hQlt.le).symm.injective
    exact Hinf_eq_bot_of_isSolvable inferInstance
  · exact absurd (le_antisymm hQlt.le (Subgroup.subgroupOf_eq_top.mp htop)) hQlt.ne

private theorem bounds_product {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h209 : S20_9 D) (h1930 : H1930 D)
    (h1A : S23_1A D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hL0L : c.L0 = c.L) :
    ∃ K₀ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      ∃ W₀ : Subgroup (Vtil (⊥ : Subgroup G) A hA),
      K₀ = (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
        (Hinf (barSub (⊥ : Subgroup G) A hA K)).map (MulAut.conj t).toMonoidHom) ∧
      W₀ = (⨆ k ∈ K₀, (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map
        (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) ∧
      E3.mParam (Mbar c.N (⊥ : Subgroup G) A hA) ≤
        E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) + 1 ∧
      E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) ≤ c.n := by
  obtain ⟨P, hP, hL0P⟩ := c.exists_minTInvParabolic h209 h1930
  obtain ⟨K₀, W₀, hK₀, hW₀, hb1, hb2⟩ :=
    aBar_bounds_W4Thm14_5 c h1A h1930 hA hAV hAne hAN hmin hP hL0P
  have hPle : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hHinfP : Hinf (barSub (⊥ : Subgroup G) A hA P) =
      barSub (⊥ : Subgroup G) A hA c.L := by
    rw [Ctx23L.Hinf_barSub c hA hAN hPle, ← hL0P, hL0L]
  have hcomp : IsComponentOf (barSub (⊥ : Subgroup G) A hA K) (Mbar c.N ⊥ A hA) :=
    isComponentOf_K_Mbar c h208 h1930 hA hAV hAne hAN hK hgen
  have hHinfK : Hinf (barSub (⊥ : Subgroup G) A hA K) =
      barSub (⊥ : Subgroup G) A hA K := Hinf_barSub_K_eq hA hcomp
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A := N_le_stabTil_of_le_normalizer c hAN
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hTstab : D.T ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.T_le_N c).trans hNstab
  have hTAnorm : barSub (⊥ : Subgroup G) A hA D.T ≤
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) A hA c.L : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) :=
    barSub_le_normalizer_of_le_normalizer hA hTstab hLstab c.hL.1.1
  have hJoin : (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
      (barSub (⊥ : Subgroup G) A hA c.L).map (MulAut.conj t).toMonoidHom) =
      barSub (⊥ : Subgroup G) A hA c.L := by
    refine le_antisymm (iSup₂_le fun s hs => ?_) ?_
    · exact le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTAnorm hs))
    · refine le_iSup₂_of_le (1 : MulAut (Vtil (⊥ : Subgroup G) A hA))
        (barSub (⊥ : Subgroup G) A hA D.T).one_mem ?_
      exact le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTAnorm (one_mem _))).symm
  refine ⟨K₀, W₀, ?_, hW₀, hb1, hb2⟩
  rw [hK₀, hHinfP, hHinfK]
  exact hJoin.trans (barSub_eq_iSup_conj c hA hAN hK hgen)

theorem Ctx23L.exists_fourteen_five_data_product {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D)
    (h1930 : H1930 D) (h1A : S23_1A D Ch)
    {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A)
    (hK : K ∈ calC c.L)
    (hgen : c.L = ⨆ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hprod : ∃ t ∈ D.T,
      barSub (⊥ : Subgroup G) A hA (K.map (MulAut.conj t).toMonoidHom) ≠
        barSub (⊥ : Subgroup G) A hA K ∧
      c.L = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hL0L : c.L0 = c.L)
    (hnat : IsL2 ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∨
      IsSz ↥(barSub (⊥ : Subgroup G) A hA K) c.n ∨
      IsSU3 ↥(barSub (⊥ : Subgroup G) A hA K) c.n)
    (hnParam : NParam (barSub (⊥ : Subgroup G) A hA K) c.n) :
    IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
      ((barSub (⊥ : Subgroup G) A hA K).subgroupOf
        (barSub (⊥ : Subgroup G) A hA K)) ∧
    commSub (fixV (barSub (⊥ : Subgroup G) A hA D.T))
      (Hinf (barSub (⊥ : Subgroup G) A hA K)) ≠ ⊥ ∧
    (∀ Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      Q < barSub (⊥ : Subgroup G) A hA K →
      IsParabolicTwo ↥(barSub (⊥ : Subgroup G) A hA K)
        (Q.subgroupOf (barSub (⊥ : Subgroup G) A hA K)) →
      normIn (barSub (⊥ : Subgroup G) A hA D.T) (barSub (⊥ : Subgroup G) A hA K) ≤
        Subgroup.normalizer (Q : Set (MulAut (Vtil (⊥ : Subgroup G) A hA))) →
      Hinf Q = ⊥) ∧
    (∃ K₀ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)),
      ∃ W₀ : Subgroup (Vtil (⊥ : Subgroup G) A hA),
      K₀ = (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
        (Hinf (barSub (⊥ : Subgroup G) A hA K)).map (MulAut.conj t).toMonoidHom) ∧
      W₀ = (⨆ k ∈ K₀, (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map
        (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) ∧
      E3.mParam (Mbar c.N (⊥ : Subgroup G) A hA) ≤
        E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) + 1 ∧
      E3.aParam (autSub (K₀ ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) ≤ c.n) := by
  classical
  refine ⟨?_, ?_, minPar_product hA hnat, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    obtain ⟨S⟩ := Sylow.nonempty (p := 2)
      (G := ↥(barSub (⊥ : Subgroup G) A hA K))
    exact ⟨S, le_top⟩
  · exact commSub_fixV_T_barSub_K_ne_bot c h208 h209 h1930 hA hAV hAne hAN hK hgen hprod hL0L
  · exact bounds_product c h208 h209 h1930 h1A hA hAV hAne hAN hmin hK hgen hL0L

end CFSG.LocalAnalysis.UniquenessCase.UC22
