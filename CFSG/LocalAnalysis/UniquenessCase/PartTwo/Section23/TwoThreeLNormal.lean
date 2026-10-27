module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNormalCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive
public import CFSG.Quasithin.Vol2.Ch5Sec1HallE22
public import CFSG.Quasithin.SteinbergCDFullSylowLocalCharTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Parts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_mem_calL_of_ne {T M L X : Subgroup G} (hL : L ∈ calL T M)
    (hXL : X ≤ L) (hXn : (X.subgroupOf L).Normal)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hne : X ≠ L) :
    Group.IsSolvable ↥X := by
  have hLX : L ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mp hXn
  by_cases hcover : L ≤ X ⊔ CFSG.Open.pCoreOf 2 L
  ·
    have h2 : ∀ l ∈ L, ∃ k : ℕ, l ^ 2 ^ k ∈ X := by
      intro l hl
      have hOleNX : CFSG.Open.pCoreOf 2 L ≤ Subgroup.normalizer (X : Set G) :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLX
      have hmem : l ∈ X ⊔ CFSG.Open.pCoreOf 2 L := hcover hl
      change l ∈ ((X ⊔ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) at hmem
      rw [Subgroup.coe_mul_of_right_le_normalizer_left X (CFSG.Open.pCoreOf 2 L) hOleNX]
        at hmem
      obtain ⟨x, hx, o, ho, rfl⟩ := hmem
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (⟨o, ho⟩ : ↥(CFSG.Open.pCoreOf 2 L)) ^ 2 ^ k = 1 :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨o, ho⟩
      have hk' : o ^ 2 ^ k = 1 := congrArg Subtype.val hk
      obtain ⟨x', hx', hpow⟩ :=
        CFSG.Quasithin.A4.exists_pow_mul_eq hx (hLX (CFSG.LieType.BorelTits.pCoreOf_le 2 L ho))
          (2 ^ k)
      exact ⟨k, by rw [hpow, hk', mul_one]; exact hx'⟩
    exact absurd (CFSG.Quasithin.SteinbergCD.eq_of_perfect_of_two_group_quotient
      hL.2.1 hXL hXn h2) hne
  ·
    have hcomm : ⁅X, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
      commutator_le_pCoreOf_of_mem_calL hL hXL hLX hTX hcover
    exact CFSG.Quasithin.H13.isSolvable_of_commutator_le
      ((Subgroup.commutator_mono le_rfl hXL).trans hcomm) (uc22p22u_isSolvable_pCoreOf L)

theorem ne_bot_of_isNaturalClassicalModule {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {k : ℕ} (h : IsNaturalClassicalModule H k) : H ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot H).mp
    (CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.kOrd_nontrivial h)

theorem Ctx23L.barSub_ne_bot_of_isNaturalClassicalModule {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A) {k : ℕ}
    (h : IsNaturalClassicalModule (barSub ⊥ A hA c.L) k) :
    barSub ⊥ A hA c.L ≠ ⊥ :=
  ne_bot_of_isNaturalClassicalModule h

theorem Ctx23L.not_le_centralizer_of_barSub_ne_bot {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (h : barSub ⊥ A hA c.L ≠ ⊥) : ¬ c.L ≤ Subgroup.centralizer (A : Set G) := by
  intro hC
  apply h
  refine le_bot_iff.mp fun φ hφ => ?_
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ A hA c.L φ).1 hφ
  rw [Subgroup.mem_bot, TwelveTwentyThree.actTil_bot_eq_one_iff A hA g]
  exact hC hgL

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

private theorem barSub_inf_conj_eq (h208 : S20_8 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ c.N)
    (hconj : barSub ⊥ A hA (c.L.map (MulAut.conj x).toMonoidHom) =
      barSub ⊥ A hA c.L) :
    barSub ⊥ A hA (c.L ⊓ c.L.map (MulAut.conj x).toMonoidHom) =
      barSub ⊥ A hA c.L := by
  let Lx : Subgroup G := c.L.map (MulAut.conj x).toMonoidHom
  let J : Subgroup G := c.L ⊓ Lx
  have hLxN : Lx ≤ c.N := (Ctx23L.conj_L_le D Ch h208 h1930 c hx).1
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A :=
    le_stabTil hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hLxstab : Lx ≤ stabTil (⊥ : Subgroup G) A := hLxN.trans hNstab
  have hcommJ : ⁅c.L, Lx⁆ ≤ J := by
    simpa [Lx, J] using commutator_le_inf D Ch h208 h1930 c hx
  have hconj' : barSub (⊥ : Subgroup G) A hA Lx = barSub (⊥ : Subgroup G) A hA c.L := hconj
  refine le_antisymm (barSub_mono ⊥ A hA inf_le_left) ?_
  calc barSub ⊥ A hA c.L
      = ⁅barSub ⊥ A hA c.L, barSub ⊥ A hA c.L⁆ :=
        (S18.commutator_barSub_self hA hLstab c.hL.1.2.1).symm
    _ = ⁅barSub ⊥ A hA c.L, barSub ⊥ A hA Lx⁆ := by rw [hconj']
    _ ≤ barSub ⊥ A hA ⁅c.L, Lx⁆ := S18.commutator_barSub_le hA hLstab hLxstab
    _ ≤ barSub ⊥ A hA J := barSub_mono ⊥ A hA hcommJ

private theorem le_sup_centralizer_of_barSub_inf_eq {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ c.N)
    (hbar : barSub ⊥ A hA (c.L ⊓ c.L.map (MulAut.conj x).toMonoidHom) =
      barSub ⊥ A hA c.L) :
    c.L ≤ (c.L ⊓ c.L.map (MulAut.conj x).toMonoidHom) ⊔
      (c.L ⊓ Subgroup.centralizer (A : Set G)) := by
  intro l hl
  let Lx : Subgroup G := c.L.map (MulAut.conj x).toMonoidHom
  let J : Subgroup G := c.L ⊓ Lx
  let C : Subgroup G := c.L ⊓ Subgroup.centralizer (A : Set G)
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A :=
    le_stabTil hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hlbar : actTil ⊥ A hA ⟨l, hLstab hl⟩ ∈ barSub ⊥ A hA c.L :=
    actTil_mem_barSub ⊥ A hA hl (hLstab hl)
  rw [← hbar] at hlbar
  obtain ⟨s, hsJ, hsa⟩ := (mem_barSub ⊥ A hA J _).1 hlbar
  have hst : (s : G)⁻¹ * l ∈ stabTil (⊥ : Subgroup G) A :=
    (stabTil ⊥ A).mul_mem ((stabTil ⊥ A).inv_mem s.2) (hLstab hl)
  have hsm : (⟨(s : G)⁻¹ * l, hst⟩ : stabTil ⊥ A) =
      (⟨s, s.2⟩ : stabTil ⊥ A)⁻¹ * ⟨l, hLstab hl⟩ := Subtype.ext rfl
  have h1 : actTil ⊥ A hA ⟨(s : G)⁻¹ * l, hst⟩ = 1 := by
    rw [hsm, map_mul, map_inv, hsa]
    simp
  have hcent : (s : G)⁻¹ * l ∈ Subgroup.centralizer (A : Set G) :=
    (TwelveTwentyThree.actTil_bot_eq_one_iff A hA ⟨_, hst⟩).1 h1
  have hmemC : (s : G)⁻¹ * l ∈ C :=
    Subgroup.mem_inf.mpr ⟨c.L.mul_mem (c.L.inv_mem hsJ.1) hl, hcent⟩
  rw [← show (s : G) * ((s : G)⁻¹ * l) = l from by group]
  exact Subgroup.mul_mem_sup hsJ hmemC

private theorem normal_inf_conj_and_solvable_centralizer (h208 : S20_8 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hLA : ¬ c.L ≤ Subgroup.centralizer (A : Set G)) {x : G} (hx : x ∈ c.N) :
    ((c.L ⊓ c.L.map (MulAut.conj x).toMonoidHom).subgroupOf c.L).Normal ∧
      ((c.L ⊓ Subgroup.centralizer (A : Set G)).subgroupOf c.L).Normal ∧
      D.T ≤ Subgroup.normalizer (c.L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ∧
      c.L ⊓ Subgroup.centralizer (A : Set G) ≠ c.L ∧
      Group.IsSolvable ↥(c.L ⊓ Subgroup.centralizer (A : Set G)) := by
  let Lx : Subgroup G := c.L.map (MulAut.conj x).toMonoidHom
  let J : Subgroup G := c.L ⊓ Lx
  let C : Subgroup G := c.L ⊓ Subgroup.centralizer (A : Set G)
  have hLleA : c.L ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.L_le_N c).trans hAN
  have hTleA : D.T ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.T_le_N c).trans hAN
  have hJleL : J ≤ c.L := inf_le_left
  have hCL : C ≤ c.L := inf_le_left
  have hLnormJ : c.L ≤ Subgroup.normalizer (J : Set G) := by
    have hLx : c.L ≤ Subgroup.normalizer (Lx : Set G) :=
      (Ctx23L.L_le_calLJoin D Ch c).trans
        (Ctx23L.conj_L_le D Ch h208 h1930 c hx).2.2
    exact (le_inf Subgroup.le_normalizer hLx).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hLnormC : c.L ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf Subgroup.le_normalizer
      (CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hLleA)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTC : D.T ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf c.hL.1.1
      (CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hTleA)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCne : C ≠ c.L := fun h => hLA (h ▸ inf_le_right)
  have hCsolv : Group.IsSolvable ↥C :=
    isSolvable_of_mem_calL_of_ne c.hL.1 hCL
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mpr hLnormC) hTC hCne
  exact ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hJleL).mpr hLnormJ,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mpr hLnormC, hTC, hCne, hCsolv⟩

theorem normal_L_N_of_barSub_eq (h208 : S20_8 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hLA : ¬ c.L ≤ Subgroup.centralizer (A : Set G))
    (hconj : ∀ x ∈ c.N, barSub ⊥ A hA (c.L.map (MulAut.conj x).toMonoidHom) =
      barSub ⊥ A hA c.L) :
    (c.L.subgroupOf c.N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Ctx23L.L_le_N c)]
  intro x hx
  let Lx : Subgroup G := c.L.map (MulAut.conj x).toMonoidHom
  let J : Subgroup G := c.L ⊓ Lx
  let C : Subgroup G := c.L ⊓ Subgroup.centralizer (A : Set G)
  obtain ⟨hJn, -, hTC, hCne, hCsolv⟩ :=
    normal_inf_conj_and_solvable_centralizer c h208 h1930 hA hAN hLA hx
  have hbar : barSub ⊥ A hA J = barSub ⊥ A hA c.L :=
    barSub_inf_conj_eq c h208 h1930 hA hAN hx (hconj x hx)
  have hsup : c.L ≤ J ⊔ C :=
    le_sup_centralizer_of_barSub_inf_eq c hA hAN hx hbar
  have hJleL : J ≤ c.L := inf_le_left
  have hCL : C ≤ c.L := inf_le_left
  have hCJ : C ⊔ J = c.L := le_antisymm (sup_le hCL hJleL) (by rwa [sup_comm])
  have hCnormJ : C ≤ Subgroup.normalizer (J : Set G) :=
    hCL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJleL).mp hJn)
  haveI : (J.subgroupOf (C ⊔ J)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hCnormJ Subgroup.le_normalizer)
  haveI : (J.subgroupOf c.L).Normal := hJn
  haveI : (J.subgroupOf C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCnormJ
  haveI : Group.IsSolvable ↥C := hCsolv
  let e := (QuotientGroup.quotientInfEquivProdNormalizerQuotient C J hCnormJ).trans
    (QuotientGroup.equivQuotientSubgroupOfOfEq (A := C ⊔ J) (B := c.L)
      (A' := J) (B' := J) rfl hCJ)
  have hQsolv : Group.IsSolvable (↥c.L ⧸ (J.subgroupOf c.L)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  haveI : Group.IsPerfect ↥c.L := Subgroup.isPerfect_iff.mpr c.hL.1.2.1
  haveI : Group.IsPerfect (↥c.L ⧸ (J.subgroupOf c.L)) := inferInstance
  have hsub : Subsingleton (↥c.L ⧸ (J.subgroupOf c.L)) := by
    rcases subsingleton_or_nontrivial (↥c.L ⧸ (J.subgroupOf c.L)) with h | h
    · exact h
    · exact (Group.IsPerfect.not_isSolvable (↥c.L ⧸ (J.subgroupOf c.L)) hQsolv).elim
  have hLleJ : c.L ≤ J :=
    Subgroup.subgroupOf_eq_top.mp (QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub)
  have hLleLx : c.L ≤ Lx := hLleJ.trans inf_le_right
  have hcard : Nat.card Lx = Nat.card c.L :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hLeq : c.L = Lx := Subgroup.eq_of_le_of_card_ge hLleLx (le_of_eq hcard)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [Lx] using hLeq.symm)

theorem normal_L_N_of_barSub_normal (h208 : S20_8 D) (h1930 : H1930 D)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hLA : ¬ c.L ≤ Subgroup.centralizer (A : Set G))
    (hY : ((barSub ⊥ A hA c.L).subgroupOf (barSub ⊥ A hA c.N)).Normal) :
    (c.L.subgroupOf c.N).Normal := by
  have hNstab : c.N ≤ stabTil (⊥ : Subgroup G) A :=
    le_stabTil hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) A := (Ctx23L.L_le_N c).trans hNstab
  have hYN : barSub ⊥ A hA c.N ≤
      Subgroup.normalizer ((barSub ⊥ A hA c.L) : Set (MulAut (Vtil ⊥ A hA))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (barSub_mono ⊥ A hA (Ctx23L.L_le_N c))).mp hY
  refine normal_L_N_of_barSub_eq c h208 h1930 hA hAN hLA fun x hx => ?_
  have hxst : x ∈ stabTil (⊥ : Subgroup G) A := hNstab hx
  rw [TwelveTwentyThree.barSub_map_conj (V₀ := ⊥) (V := A) hA hLstab hxst]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (hYN (actTil_mem_barSub ⊥ A hA hx hxst))

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
