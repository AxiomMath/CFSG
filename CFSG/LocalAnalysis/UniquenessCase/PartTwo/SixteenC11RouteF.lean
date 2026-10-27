module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteFC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteFG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c11_normalizer_le_of_factor (D : Data G) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig)
    {Xbar : Subgroup (MulAut (Vtil V₀ V hV))} (hXM : Xbar ≤ Mbar D.M V₀ V hV)
    (hfac : (Xbar : Set (MulAut (Vtil V₀ V hV))) =
      ((Xbar ⊓ centSub (fixV (barSub V₀ V hV D.T)) : Subgroup _) : Set _) *
        ((Xbar ⊓ normalizer
          ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) : Subgroup _) : Set _))
    (hexp : ∀ x ∈ Xbar, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p = 1)
    (hcount : padicValNat p (Nat.card ↥(Xbar ⊓ centSub (fixV (barSub V₀ V hV D.T)))) + 2 ≤
      padicValNat p (Nat.card ↥Xbar)) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  have hpp : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let C : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Xbar ⊓ centSub (fixV (barSub V₀ V hV D.T))
  let N : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Xbar ⊓ normalizer ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _)
  have hle : padicValNat p (Nat.card Xbar) ≤
      padicValNat p (Nat.card C) + padicValNat p (Nat.card N) :=
    s16c11_padicValNat_card_le_of_set_mul hfac p
  have hcountC : padicValNat p (Nat.card C) + 2 ≤ padicValNat p (Nat.card Xbar) := hcount
  have hN2 : 2 ≤ padicValNat p (Nat.card N) := by omega
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := ↥N)
  let P : Subgroup (MulAut (Vtil V₀ V hV)) := (Q : Subgroup ↥N).map N.subtype
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hPX : P ≤ Xbar := hPN.trans inf_le_left
  have hPM : P ≤ Mbar D.M V₀ V hV := hPX.trans hXM
  have hPW : P ≤ normalizer
      ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) :=
    hPN.trans inf_le_right
  have hPp : IsPGroup p ↥P := Q.isPGroup'.map N.subtype
  have hPcard : Nat.card P = p ^ padicValNat p (Nat.card N) := by
    rw [show P = (Q : Subgroup ↥N).map N.subtype from rfl,
      Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity Q,
      Nat.factorization_def _ hpp]
  have hcard2 : p ^ 2 ∣ Nat.card P := by
    rw [hPcard]
    exact pow_dvd_pow p hN2
  have hexpP : ∀ x ∈ P, x ^ p = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := hPp ⟨x, hx⟩
    exact hexp x (hPX hx) ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hPc : ¬ IsCyclic ↥P := s16c11_not_isCyclic_of_exponent hpp hexpP hcard2
  exact s16c11_normalizer_le_of_bar_noncyclic D h61 hV h hp hPM hPp hPc hPW

theorem s16c11_normalizer_le_of_routeF (D : Data G) (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D)
    (h169 : R16_9 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p ∈ D.sig)
    {Xbar : Subgroup (MulAut (Vtil V₀ V hV))} (hXM : Xbar ≤ Mbar D.M V₀ V hV)
    (hTX : barSub V₀ V hV D.T ≤ Xbar) (hsolv : Group.IsSolvable ↥Xbar)
    (hexp : ∀ x ∈ Xbar, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p = 1)
    (hcount : padicValNat p (Nat.card ↥(Xbar ⊓ centSub (fixV (barSub V₀ V hV D.T)))) + 2 ≤
      padicValNat p (Nat.card ↥Xbar)) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  exact s16c11_normalizer_le_of_factor D h61 hV hc.setting.hyp16.hyp125 hp hXM
    (s16c11_barSub_factor_of_routeF D h1610 h169 hV hc hXM hTX hsolv) hexp hcount

theorem s16c11_le_normalizer_barSub_wClos_of_pGroup (D : Data G) (h1610 : R16_10_2 D)
    (h169 : R16_9 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P)
    (hPT : barSub V₀ V hV D.T ≤ normalizer (P : Set (MulAut (Vtil V₀ V hV)))) :
    P ≤ normalizer ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let Tbar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  let Wbar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (E3.wClos V 0 D.T)
  let Xbar : Subgroup (MulAut (Vtil V₀ V hV)) := P ⊔ Tbar
  have hXM : Xbar ≤ Mbar D.M V₀ V hV :=
    sup_le hPM (barSub_mono V₀ V hV D.sylowM.le)
  have hTX : Tbar ≤ Xbar := le_sup_right
  have hPX : P ≤ Xbar := le_sup_left
  have hTbar : IsPGroup 2 Tbar :=
    D.sylowM.isPGroup.comap_subtype.map (actTil V₀ V hV)
  have hnorm : Xbar ≤ normalizer (P : Set (MulAut (Vtil V₀ V hV))) :=
    sup_le Subgroup.le_normalizer hPT
  have hodd : ¬ 2 ∣ Nat.card P := by
    intro h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hPp
    rw [hk] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hsolv : Group.IsSolvable ↥Xbar := by
    haveI : (P.subgroupOf Xbar).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).2 hnorm
    have hPp' : IsPGroup p (P.subgroupOf Xbar) := hPp.comap_subtype
    haveI : Group.IsNilpotent ↥(P.subgroupOf Xbar) := hPp'.isNilpotent
    haveI : Group.IsSolvable ↥(P.subgroupOf Xbar) := inferInstance
    have hQ : IsPGroup 2 (↥Xbar ⧸ P.subgroupOf Xbar) := by
      refine (hTbar.comap_subtype).of_surjective
        ((QuotientGroup.mk' (P.subgroupOf Xbar)).comp
          (Tbar.subgroupOf Xbar).subtype) ?_
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hy : (y : MulAut (Vtil V₀ V hV)) ∈
          ((P ⊔ Tbar : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) := by
        have hX : Xbar = P ⊔ Tbar := rfl
        rw [← hX]
        exact y.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left P Tbar hPT] at hy
      obtain ⟨k, hk, t, ht, hkt⟩ := hy
      refine ⟨⟨⟨t, hTX ht⟩, ht⟩, ?_⟩
      change QuotientGroup.mk (⟨t, hTX ht⟩ : ↥Xbar) = QuotientGroup.mk y
      rw [QuotientGroup.eq]
      show t⁻¹ * (y : MulAut (Vtil V₀ V hV)) ∈ P
      rw [← hkt]
      have hmem : t⁻¹ * k * t ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hPT (Tbar.inv_mem ht)) k).mp hk
      convert hmem using 1
      group
    haveI : Group.IsNilpotent (↥Xbar ⧸ P.subgroupOf Xbar) := hQ.isNilpotent
    haveI : Group.IsSolvable (↥Xbar ⧸ P.subgroupOf Xbar) := inferInstance
    exact Group.isSolvable_of_subgroup_quotient (P.subgroupOf Xbar)
  have hfac := s16c11_barSub_factor_of_routeF D h1610 h169 hV hc hXM hTX hsolv
  let C : Subgroup (MulAut (Vtil V₀ V hV)) := Xbar ⊓ centSub (fixV Tbar)
  let N : Subgroup (MulAut (Vtil V₀ V hV)) := Xbar ⊓ normalizer (Wbar : Set _)
  have hcent : P ⊓ centSub (fixV Tbar) = ⊥ :=
    s16c11_inf_centSub_fixV_eq_bot (s15_Infra_vtil_sq_eq_one V₀ V hV) hodd hTbar hPT
  have hCP : C ⊓ P = ⊥ := by
    refine le_bot_iff.1 ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans ?_)
    rw [hcent]
  have hPN : P ≤ N :=
    s16c11_le_of_normal_pGroup_of_set_mul hp hp2 hTbar hPp hPT rfl hfac hCP
  exact hPN.trans inf_le_right

theorem s16c11_normalizer_le_of_routeF_normalized (D : Data G) (h61 : UC6.R6_1 D)
    (h1610 : R16_10_2 D) (h169 : R16_9 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P)
    (hPc : ¬ IsCyclic ↥P)
    (hPT : barSub V₀ V hV D.T ≤ normalizer (P : Set (MulAut (Vtil V₀ V hV)))) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  exact s16c11_normalizer_le_of_bar_noncyclic D h61 hV hc.setting.hyp16.hyp125 hp hPM hPp hPc
    (s16c11_le_normalizer_barSub_wClos_of_pGroup D h1610 h169 hV hc hpp hp2 hPM hPp hPT)

theorem s16c11_normalizer_le_of_routeF_normal (D : Data G) (h61 : UC6.R6_1 D)
    (h1610 : R16_10_2 D) (h169 : R16_9 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hPM : P ≤ Mbar D.M V₀ V hV) (hPp : IsPGroup p ↥P)
    (hPc : ¬ IsCyclic ↥P)
    (hPN : Mbar D.M V₀ V hV ≤ normalizer (P : Set (MulAut (Vtil V₀ V hV)))) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hPT : barSub V₀ V hV D.T ≤
      normalizer (P : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV D.sylowM.le).trans hPN
  exact s16c11_normalizer_le_of_routeF_normalized D h61 h1610 h169 hV hc hp hPM hPp hPc hPT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
