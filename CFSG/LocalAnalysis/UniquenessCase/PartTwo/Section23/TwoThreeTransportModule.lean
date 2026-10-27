module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Quasithin.H13.A6S13821zz11
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

private theorem N_le_stabTil {A : Subgroup G} (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) :
    c.N ≤ stabTil ⊥ A :=
  le_inf hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)

private theorem nontrivial_vtil {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAne : A ≠ ⊥) :
    Nontrivial (Vtil (⊥ : Subgroup G) A hA) := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  let x : IntMod A hA := IntMod.mk hA a
  have hx : mkTil ⊥ A hA x ≠ 1 := by
    intro h
    have h1 := (mkTil_eq_iff ⊥ A hA x 1).1 h
    rw [Subgroup.mem_bot] at h1
    have h1a : (a : G) = 1 := by
      have hxval : x.val = (a : G) := rfl
      rw [hxval] at h1
      simpa using h1
    exact ha1 (Subtype.ext h1a)
  exact ⟨⟨mkTil ⊥ A hA x, 1, hx⟩⟩

private theorem le_centralizer_of_forall_actTil_eq_one {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hNs : c.N ≤ stabTil ⊥ A) {X : Subgroup G} (hXN : X ≤ c.N)
    (hX : ∀ x (hx : x ∈ X), actTil ⊥ A hA ⟨x, hNs (hXN hx)⟩ = 1) :
    X ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 := (actTil_eq_one_iff ⊥ A hA ⟨x, hNs (hXN hx)⟩).1 (hX x hx) a ha
  rw [Subgroup.mem_bot] at h1
  have h2 : x * a * x⁻¹ = a := mul_inv_eq_one.mp h1
  calc a * x = (x * a * x⁻¹) * x := by rw [h2]
    _ = x * a := by group

theorem barSub_N_ne_bot {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥) :
    barSub ⊥ A hA c.N ≠ ⊥ := by
  intro hbot
  have hNcent : c.N ≤ Subgroup.centralizer (A : Set G) := by
    refine le_centralizer_of_forall_actTil_eq_one c hA (N_le_stabTil c hAN) le_rfl
      fun x hx => ?_
    have hmem : actTil ⊥ A hA ⟨x, N_le_stabTil c hAN hx⟩ ∈ barSub ⊥ A hA c.N :=
      actTil_mem_barSub ⊥ A hA hx (N_le_stabTil c hAN hx)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hAL : A ≤ Subgroup.centralizer (c.L : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hNcent (L_le_N c hl)) a ha).symm
  have hAle : A ≤ (⊥ : Subgroup G) := by
    rw [← fixed_L_eq_bot c]
    exact le_inf hAV hAL
  exact hAne (le_bot_iff.mp hAle)

theorem isIrrOn_barSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    IsIrrOn (barSub ⊥ A hA c.N) ⊤ ⊥ := by
  have hNs : c.N ≤ stabTil ⊥ A := N_le_stabTil (A := A) c hAN
  haveI := nontrivial_vtil hA hAne
  have htopne : (⊤ : Subgroup (Vtil (⊥ : Subgroup G) A hA)) ≠ ⊥ := top_ne_bot
  refine ⟨bot_lt_iff_ne_bot.mpr htopne, ?_, ?_, ?_⟩
  · intro y hy u hu
    exact Subgroup.mem_top _
  · intro y hy u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJstab hbotJ hJtop
    have hpre := hmin (preTil ⊥ A hA J) (preTil_le ⊥ A hA J)
      (TwelveSeventeen.le_normalizer_preTil hA hNs hJstab)
    have hJeq : J = imgTil ⊥ A hA (preTil ⊥ A hA J) :=
      (imgTil_preTil ⊥ A hA J).symm
    rcases hpre with h | h
    · left
      rw [hJeq, h, TwelveSeventeen.imgTil_bot]
    · right
      have hAimg : imgTil (⊥ : Subgroup G) A hA A = ⊤ := by
        refine le_antisymm le_top fun q _ => ?_
        obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ A hA q
        exact (mem_imgTil ⊥ A hA A _).2 ⟨x, x.val_mem, rfl⟩
      rw [hJeq, h, hAimg]

theorem isIndivisible_barSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    IsIndivisible (barSub ⊥ A hA c.N) := by
  have hirr := isIrrOn_barSub c hA hAV hAN hAne hmin
  intro U₁ U₂ hU₁ hU₂ hsup
  rcases hirr.2.2.2 U₁ hU₁ bot_le le_top with h | h
  · exact Or.inr (by rw [h, bot_sup_eq] at hsup; exact hsup)
  · exact Or.inl h

theorem isBasicModule_barSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    IsBasicModule (barSub ⊥ A hA c.N) := by
  have hirr := isIrrOn_barSub c hA hAV hAN hAne hmin
  have hNne := barSub_N_ne_bot c hA hAV hAN hAne
  refine ⟨isIndivisible_barSub c hA hAV hAN hAne hmin, ?_⟩
  intro U hU hfaith
  rcases hirr.2.2.2 U hU bot_le le_top with h | h
  · exfalso
    apply hNne
    refine le_bot_iff.mp ?_
    intro y hy
    by_contra hy1
    have hyfix : ∀ u ∈ U, y u = u := by
      intro u hu
      rw [h, Subgroup.mem_bot] at hu
      rw [hu, map_one]
    exact hy1 (hfaith y hy hyfix)
  · exact h

theorem o2Trivial_barSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    O2Trivial (barSub ⊥ A hA c.N) := by
  have hirr := isIrrOn_barSub c hA hAV hAN hAne hmin
  intro P hPN hPnorm hP2
  haveI := nontrivial_vtil hA hAne
  have hfixne : fixV P ≠ ⊥ :=
    CFSG.Quasithin.H13.A6.A6S20.fixV_ne_bot_of_two_group
      (s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) A hA) hP2
  have hfixstab : StableUnder (barSub ⊥ A hA c.N) (fixV P) := by
    intro y hy u hu
    rw [mem_fixV] at hu ⊢
    intro p hp
    have hyinv : y⁻¹ ∈ barSub ⊥ A hA c.N := (barSub ⊥ A hA c.N).inv_mem hy
    have hconj : y⁻¹ * p * y ∈ P :=
      Subgroup.mem_subgroupOf.mp (hPnorm.conj_mem ⟨p, hPN hp⟩ hp ⟨y⁻¹, hyinv⟩)
    calc p (y u) = (p * y) u := rfl
      _ = (y * (y⁻¹ * p * y)) u := by group
      _ = y ((y⁻¹ * p * y) u) := rfl
      _ = y u := by rw [hu (y⁻¹ * p * y) hconj]
  rcases hirr.2.2.2 (fixV P) hfixstab bot_le le_top with h | h
  · exfalso
    exact hfixne h
  ·
    apply le_bot_iff.mp
    intro p hp
    rw [Subgroup.mem_bot]
    have hfixall : ∀ u : Vtil (⊥ : Subgroup G) A hA, p u = u := by
      intro u
      have hu : u ∈ fixV P := by rw [h]; exact Subgroup.mem_top u
      exact (mem_fixV.mp hu) p hp
    exact MulEquiv.ext fun u => by simpa using hfixall u

theorem isBasic_barSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hAne : A ≠ ⊥)
    (hmin : ∀ B : Subgroup G, B ≤ A → c.N ≤ Subgroup.normalizer (B : Set G) →
      B = ⊥ ∨ B = A) :
    O2Trivial (barSub ⊥ A hA c.N) ∧ IsIrrOn (barSub ⊥ A hA c.N) ⊤ ⊥ ∧
      IsIndivisible (barSub ⊥ A hA c.N) ∧ IsBasicModule (barSub ⊥ A hA c.N) :=
  ⟨o2Trivial_barSub c hA hAV hAN hAne hmin,
    isIrrOn_barSub c hA hAV hAN hAne hmin,
    isIndivisible_barSub c hA hAV hAN hAne hmin,
    isBasicModule_barSub c hA hAV hAN hAne hmin⟩

theorem barSubHom_map_subgroupOf {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {X P : Subgroup G} (hP : P ≤ X) (hX : X ≤ stabTil ⊥ A) :
    (P.subgroupOf X).map (barSubHom hA X hX) =
      (barSub ⊥ A hA P).subgroupOf (barSub ⊥ A hA X) := by
  ext φ
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_barSub]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine (mem_barSub ⊥ A hA P _).2 ⟨⟨p, hX p.2⟩, Subgroup.mem_subgroupOf.mp hp, ?_⟩
    exact (barSubHom_apply hA X hX p).symm
  · rintro ⟨g, hgP, hg⟩
    refine ⟨⟨g, hP hgP⟩, Subgroup.mem_subgroupOf.mpr hgP, ?_⟩
    apply Subtype.ext
    rw [barSubHom_apply]
    have hgg : (⟨(g : G), hX (hP hgP)⟩ : ↥(stabTil ⊥ A)) = g := Subtype.ext rfl
    rw [hgg]
    exact hg

theorem Hinf_subgroupOf_of_le {X : Type} [Group X] [Finite X] {L A : Subgroup X} (hA : A ≤ L) :
    Hinf (A.subgroupOf L) = (Hinf A).subgroupOf L := by
  haveI : Finite ↥L := inferInstance
  apply Subgroup.map_subtype_inj.mp
  rw [Hinf_map, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le ((uc22p21c_Hinf_le A).trans hA)]

theorem isParabolicTwo_barSub {A P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hP : ParabolicOf c.L P) :
    IsParabolicTwo ↥(barSub ⊥ A hA c.L)
      ((barSub ⊥ A hA P).subgroupOf (barSub ⊥ A hA c.L)) := by
  have hLstab : c.L ≤ stabTil ⊥ A := (L_le_N c).trans (N_le_stabTil c hAN)
  have hmap := barSubHom_map_subgroupOf (X := c.L) (P := P) hA (parabolicOf_iff.mp hP).1
    hLstab
  have hsurj := barSubHom_surjective hA c.L hLstab
  have h := IsParabolicTwo.map (parabolicOf_iff.mp hP).2 (barSubHom hA c.L hLstab) hsurj
  rwa [hmap] at h

theorem Hinf_barSub {A P : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) (hPL : P ≤ c.L) :
    Hinf (barSub ⊥ A hA P) = barSub ⊥ A hA (Hinf P) := by
  have hLstab : c.L ≤ stabTil ⊥ A := (L_le_N c).trans (N_le_stabTil c hAN)
  have hmap := barSubHom_map_subgroupOf (X := c.L) (P := P) hA hPL hLstab
  have hH := Hinf_map (barSubHom hA c.L hLstab) (P.subgroupOf c.L)
  rw [hmap, Hinf_subgroupOf_of_le hPL] at hH
  have hHinfle : Hinf P ≤ c.L := (uc22p21c_Hinf_le P).trans hPL
  have hmapH := barSubHom_map_subgroupOf (X := c.L) (P := Hinf P) hA hHinfle hLstab
  have hHsub : Hinf ((barSub ⊥ A hA P).subgroupOf (barSub ⊥ A hA c.L)) =
      (Hinf (barSub ⊥ A hA P)).subgroupOf (barSub ⊥ A hA c.L) :=
    Hinf_subgroupOf_of_le (barSub_mono ⊥ A hA hPL)
  rw [hmapH, hHsub] at hH
  have hEqInf := Subgroup.subgroupOf_inj.mp hH
  rw [inf_eq_left.mpr (barSub_mono ⊥ A hA ((uc22p21c_Hinf_le P).trans hPL))] at hEqInf
  rw [inf_eq_left.mpr ((uc22p21c_Hinf_le (barSub ⊥ A hA P)).trans
    (barSub_mono ⊥ A hA hPL))] at hEqInf
  exact hEqInf.symm

private theorem preBarSub_subgroupOf_comap {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))} :
    (preBarSub c.L (⊥ : Subgroup G) A hA Q).subgroupOf c.L =
      (Q.subgroupOf (barSub ⊥ A hA c.L)).comap
        (barSubHom hA c.L ((L_le_N c).trans (N_le_stabTil c hAN))) := by
  ext l
  rw [Subgroup.mem_subgroupOf, mem_preBarSub, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨-, h, hq⟩
    rw [barSubHom_apply]
    have hgg : (⟨(l : G), (L_le_N c).trans (N_le_stabTil c hAN) l.2⟩ :
        ↥(stabTil ⊥ A)) = ⟨(l : G), h⟩ := Subtype.ext rfl
    rwa [hgg]
  · intro hq
    refine ⟨l.2, ⟨(L_le_N c).trans (N_le_stabTil c hAN) l.2, ?_⟩⟩
    rw [barSubHom_apply] at hq
    exact hq

theorem isParabolicTwo_preBarSub {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    {Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hQpar : IsParabolicTwo ↥(barSub ⊥ A hA c.L)
      (Q.subgroupOf (barSub ⊥ A hA c.L))) :
    IsParabolicTwo ↥c.L
      ((preBarSub c.L (⊥ : Subgroup G) A hA Q).subgroupOf c.L) := by
  rw [preBarSub_subgroupOf_comap c hA hAN]
  exact IsParabolicTwo.comap (barSubHom hA c.L ((L_le_N c).trans (N_le_stabTil c hAN)))
    (barSubHom_surjective hA c.L ((L_le_N c).trans (N_le_stabTil c hAN))) hQpar

theorem barSub_preBarSub_eq {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA))}
    (hQL : Q ≤ barSub ⊥ A hA c.L) :
    barSub ⊥ A hA (preBarSub c.L (⊥ : Subgroup G) A hA Q) = Q := by
  rw [show barSub ⊥ A hA (preBarSub c.L (⊥ : Subgroup G) A hA Q) =
      Q ⊓ barSub ⊥ A hA c.L from barSub_preBarSub c.L (⊥ : Subgroup G) A hA Q]
  exact inf_eq_left.mpr hQL

end Ctx23L

theorem aBar_eq_aParam_autSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A W : Subgroup G} (hA : IsElemAbelian 2 A) (hW : IsElemAbelian 2 W)
    {e : ↥(imgTil (⊥ : Subgroup G) A hA W) ≃*
      Vtil (⊥ : Subgroup G) W hW}
    (hmap : Mbar (c.L0 ⊔ D.T) (⊥ : Subgroup G) W hW =
      (autSub ((barSub (⊥ : Subgroup G) A hA c.L0) ⊔
        (barSub (⊥ : Subgroup G) A hA D.T))
        (imgTil (⊥ : Subgroup G) A hA W)).map
        (CFSG.Quasithin.H.congrHom e)) :
    aBar (c.L0 ⊔ D.T) (⊥ : Subgroup G) W hW =
      E3.aParam (autSub ((barSub (⊥ : Subgroup G) A hA c.L0) ⊔
        (barSub (⊥ : Subgroup G) A hA D.T))
        (imgTil (⊥ : Subgroup G) A hA W)) := by
  unfold aBar
  rw [hmap, CFSG.Quasithin.H.aParam_map_congrHom]

end CFSG.LocalAnalysis.UniquenessCase.UC22
