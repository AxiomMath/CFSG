module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLie
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_abaa_conjSubgroup_le_of_mem {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_abaa_barSub_sup {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A B : Subgroup G} (hA : A ≤ stabTil V₀ V) (hB : B ≤ stabTil V₀ V) :
    barSub V₀ V hV (A ⊔ B) = barSub V₀ V hV A ⊔ barSub V₀ V hV B := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem s16h_e3_l3_two_le_pRank_centralizer_of_ctilde_coprime
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2)
    (hsig : D.sig = {3})
    (h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V)) :
    2 ≤ CFSG.Open.pRank 3 (D.M ⊓
      Subgroup.centralizer (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hnorm : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hnorm h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hxM, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 (by rw [hs2]; norm_num)
  let Lx : Subgroup G := conjSubgroup L x
  have hLxM : Lx ≤ D.M := s16h_abaa_conjSubgroup_le_of_mem h.hyp151.le hxM
  let H : Subgroup G := L ⊔ Lx
  have hHM : H ≤ D.M := sup_le h.hyp151.le hLxM
  have hHstab : H ≤ stabTil ⊥ V := sup_le (h.hyp151.le.trans hMs) (hLxM.trans hMs)
  have hHc : H ≤ Subgroup.centralizer (v1Sub D.M ⊥ V hV L : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Sixteen21.commute_of_mem_v1Sub hV h.hyp151 rfl hy hu).symm
    · have hLc : L ≤ Subgroup.centralizer (v1Sub D.M ⊥ V hV L : Set G) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Sixteen21.commute_of_mem_v1Sub hV h.hyp151 rfl hy hu).symm
      have h1 := E3.conjSubgroup_mono_left x hLc
      rw [E3.conjSubgroup_centralizer (v1Sub D.M ⊥ V hV L) x,
        s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 hV hxM] at h1
      exact h1
  have hcomm : ⁅barSub ⊥ V hV L, barSub ⊥ V hV Lx⁆ = ⊥ := by
    have h1 := (h.hyp151.commute x hxM hxn).1
    simpa only [Lx] using h1
  haveI : Group.IsPerfect ↥(barSub ⊥ V hV L) := ⟨hcomp.2.2.1⟩
  have hperfLx : ⁅barSub ⊥ V hV Lx, barSub ⊥ V hV Lx⁆ = barSub ⊥ V hV Lx := by
    have hperf : Group.IsPerfect ↥(barSub ⊥ V hV Lx) := by
      rw [show Lx = conjSubgroup L x from rfl,
        s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L]
      exact Group.IsPerfect.map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom
    exact Subgroup.isPerfect_iff.mp hperf
  have hdivLx : 3 ∣ Nat.card ↥(barSub ⊥ V hV Lx) := by
    rw [show Lx = conjSubgroup L x from rfl,
      s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L,
      Subgroup.card_map_of_injective (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).injective]
    exact s16h_three_dvd_of_isSLn hcomp.2.2 hL3.1
  have h3dvdL : 3 ∣ Nat.card ↥(barSub ⊥ V hV L) :=
    s16h_three_dvd_of_isSLn hcomp.2.2 hL3.1
  have hrankL : CFSG.Open.pRank 3 (barSub ⊥ V hV L) = 1 := by
    refine le_antisymm (hthin 3 Nat.prime_three (by norm_num)) ?_
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three h3dvdL
  have hbarRank : 2 ≤ CFSG.Open.pRank 3
      (barSub ⊥ V hV L ⊔ barSub ⊥ V hV Lx) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hstep := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf
      (q := 3) (by norm_num) (M := barSub ⊥ V hV L ⊔ barSub ⊥ V hV Lx)
      (L := barSub ⊥ V hV L) (X := barSub ⊥ V hV Lx) le_sup_left le_sup_right
      (by rw [hcomm]; exact bot_le) hperfLx hdivLx
    rw [hrankL] at hstep
    omega
  let φ : ↥H →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hHstab)
  have hker : φ.ker = (H ⊓ F11.CTilde D.M ⊥ V).subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hg
      refine ⟨g.2, ?_⟩
      refine (mem_cTilde_iff hV hnorm).2 ⟨hHM g.2, hHstab g.2, ?_⟩
      show actTil ⊥ V hV (Subgroup.inclusion hHstab g) = 1
      exact hg
    · rintro ⟨-, hgC⟩
      obtain ⟨-, hgs, h1⟩ := (mem_cTilde_iff hV hnorm).1 hgC
      show φ g = 1
      change actTil ⊥ V hV (Subgroup.inclusion hHstab g) = 1
      rw [show Subgroup.inclusion hHstab g = (⟨(g : G), hgs⟩ : stabTil ⊥ V) from Subtype.ext rfl,
        h1]
  have hrange : φ.range = barSub ⊥ V hV H := by
    ext ψ
    constructor
    · rintro ⟨g, rfl⟩
      exact actTil_mem_barSub ⊥ V hV g.2 (hHstab g.2)
    · intro hψ
      obtain ⟨g, hgH, hgψ⟩ := (mem_barSub ⊥ V hV H ψ).1 hψ
      exact ⟨⟨g, hgH⟩, hgψ⟩
  have hker_coprime : ¬ 3 ∣ Nat.card ↥φ.ker := by
    rw [hker]
    have hkercard : Nat.card ↥((H ⊓ F11.CTilde D.M ⊥ V).subgroupOf H) =
        Nat.card ↥(H ⊓ F11.CTilde D.M ⊥ V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : H ⊓ F11.CTilde D.M ⊥ V ≤ H)).toEquiv
    have hCcard : Nat.card ↥((H ⊓ F11.CTilde D.M ⊥ V).subgroupOf
        (F11.CTilde D.M ⊥ V)) = Nat.card ↥(H ⊓ F11.CTilde D.M ⊥ V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : H ⊓ F11.CTilde D.M ⊥ V ≤ F11.CTilde D.M ⊥ V)).toEquiv
    intro hdvd
    rw [hkercard] at hdvd
    refine h3C (hdvd.trans ?_)
    rw [← hCcard]
    exact Subgroup.card_subgroup_dvd_card
      ((H ⊓ F11.CTilde D.M ⊥ V).subgroupOf (F11.CTilde D.M ⊥ V))
  have hiso : (↥H ⧸ φ.ker) ≃* ↥(barSub ⊥ V hV H) :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hEq : CFSG.Open.pRank 3 H = CFSG.Open.pRank 3 (barSub ⊥ V hV H) := by
    have hp := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
      (p := 3) Nat.prime_three φ.ker hker_coprime
    have hcongr := CFSG.pRank_congr_of_mulEquiv hiso 3
    have h12 : CFSG.pRank 3 ↥H = CFSG.pRank 3 ↥(barSub ⊥ V hV H) := hp.symm.trans hcongr
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank 3 H,
      CFSG.SectionRank.pRank_coe_eq_openPRank 3 (barSub ⊥ V hV H)] at h12
  have hHrank : 2 ≤ CFSG.Open.pRank 3 H := by
    rw [hEq, s16h_abaa_barSub_sup hV (h.hyp151.le.trans hMs) (hLxM.trans hMs)]
    exact hbarRank
  refine le_trans hHrank (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) ?_)
  exact le_inf hHM hHc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
