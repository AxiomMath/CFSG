module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.GroupTheory.Frattini.NormalConjugation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_hyp_of_mem_B0 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    {b : G} (hb : b ∈ c.B0) (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup q ↥X →
      X ≤ D.M ⊓ Subgroup.centralizer ({b} : Set G) → X ∉ uniqueSet D.M ∧ q ∉ D.sig := by
  intro X hXne hXq hXle
  let c₀ : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hfacts := (h54 h1930 c₀ b hb hbZ).2 q hq X hXne hXq hXle
  refine ⟨hfacts.1, ?_⟩
  rw [h6 h1930 c]
  exact hfacts.2

private theorem exists_mem_sup_commute_of_mem_centralizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c) {e : G} (he : e ∈ D.M)
    (heodd : Odd (orderOf e))
    {x : Bar2 D.M} (hxE : x ∈ d.E)
    (hxC : x ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨e, he⟩} : Set (Bar2 D.M)))
    (hxne : x ≠ 1) :
    ∃ z : ↥D.M, z ^ d.q = 1 ∧ z ≠ 1 ∧
      z * ⟨e, he⟩ = ⟨e, he⟩ * z ∧
      (z : G) ∈ CFSG.Open.pCoreOf 2 D.M ⊔ d.Q := by
  classical
  haveI : Fact d.q.Prime := ⟨d.hq⟩
  let eM : ↥D.M := ⟨e, he⟩
  let eBar : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) eM
  have heoddM : Odd (orderOf eM) := (Subgroup.orderOf_coe eM).symm ▸ heodd
  have hxq : x ^ d.q = 1 := d.hEexp x hxE
  have hxb : eBar * x = x * eBar :=
    (Subgroup.mem_centralizer_iff.mp hxC) eBar (Set.mem_singleton _)
  obtain ⟨z, hzcomm, hzq, hzne, hzmem⟩ :=
    exists_pow_eq_one_commute_of_commute_bar heoddM d.hq d.hq2 hxne hxq hxb
  have hzbarE : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) z ∈ d.E :=
    (Subgroup.zpowers_le.mpr hxE) hzmem
  have hzP : (z : G) ∈ CFSG.Open.pCoreOf 2 D.M ⊔ d.Q := by
    have hzPre : (z : G) ∈ barPreimage D.M d.E :=
      uc22p21c_mem_barPreimage.2 ⟨z.2, hzbarE⟩
    rw [← d.hEQ, barPreimage_barImage_eq_sup_pCore d.hQM] at hzPre
    simpa only [sup_comm, CFSG.Open.pCoreOf] using hzPre
  exact ⟨z, hzq, hzne, hzcomm, hzP⟩

private theorem exists_sylow_sup_mem {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c)
    {z : ↥D.M} (hzP : (z : G) ∈ CFSG.Open.pCoreOf 2 D.M ⊔ d.Q)
    (hzq : z ^ d.q = 1) (hzne : z ≠ 1) :
    ∃ Q₁ : Subgroup G, Q₁ ≤ D.M ∧ IsPGroup d.q ↥Q₁ ∧
      (∀ y ∈ Q₁, y ^ d.q = 1) ∧ ⁅⁅Q₁, Q₁⁆, Q₁⁆ = ⊥ ∧ ¬ IsCyclic ↥Q₁ ∧
      (z : G) ∈ Q₁ ∧
      D.M ≤ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 D.M ⊔ Q₁ : Subgroup G) : Set G) := by
  classical
  haveI : Fact d.q.Prime := ⟨d.hq⟩
  let P : Subgroup G := CFSG.Open.pCoreOf 2 D.M ⊔ d.Q
  have hzP' : (z : G) ∈ P := hzP
  let X : Subgroup G := Subgroup.zpowers (z : G)
  have hzneG : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  have hzqG : (z : G) ^ d.q = 1 := by simpa using congrArg Subtype.val hzq
  have hXq : IsPGroup d.q X :=
    IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hzqG hzneG, pow_one])
  have hXP : X ≤ P := Subgroup.zpowers_le.mpr hzP'
  have hXPq : IsPGroup d.q ↥(X.subgroupOf P) :=
    hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXP).symm
  obtain ⟨S, hXS⟩ := hXPq.exists_le_sylow
  let Q₁ : Subgroup G := (S : Subgroup ↥P).map P.subtype
  have hQ₁sylP : CFSG.ABGLocalTools.IsSylowOf d.q Q₁ P := ⟨S, rfl⟩
  have hPM : P ≤ D.M := sup_le (uc22p21c_pCoreOf_le D.M) d.hQM
  have hQ₁M : Q₁ ≤ D.M := hQ₁sylP.le.trans hPM
  have hPbar : P = barPreimage D.M d.E := by
    rw [← d.hEQ, barPreimage_barImage_eq_sup_pCore d.hQM]
    exact sup_comm (CFSG.Open.pCoreOf 2 D.M) d.Q
  have hQ₁sylY : CFSG.ABGLocalTools.IsSylowOf d.q Q₁ (barPreimage D.M d.E) :=
    hPbar ▸ hQ₁sylP
  obtain ⟨hbarE, hinfE⟩ := uc22p22u_sylow_barPreimage d.hq d.hq2 d.hEp hQ₁sylY
  have hprops := uc22p22u_lift_props (r := d.q) hbarE hinfE hQ₁M
  have hQ₁exp : ∀ y ∈ Q₁, y ^ d.q = 1 := hprops.1 d.hEexp
  have hQ₁cl : ⁅⁅Q₁, Q₁⁆, Q₁⁆ = ⊥ := hprops.2.1 d.hEclass
  have hQ₁nc : ¬ IsCyclic ↥Q₁ := hprops.2.2 d.hEnc
  have hQ₁norm : D.M ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 D.M ⊔ Q₁ : Subgroup G) : Set G) := by
    have hsup : CFSG.Open.pCoreOf 2 D.M ⊔ Q₁ = P := by
      rw [sup_comm]
      change Q₁ ⊔ (CFSG.pCore 2 ↥D.M).map D.M.subtype = _
      rw [← barPreimage_barImage_eq_sup_pCore hQ₁M, hbarE, ← d.hEQ,
        barPreimage_barImage_eq_sup_pCore d.hQM]
      exact sup_comm d.Q ((CFSG.pCore 2 ↥D.M).map D.M.subtype)
    rw [hsup]
    exact d.hQnorm
  have hzQ₁ : (z : G) ∈ Q₁ := by
    have hzX : (z : G) ∈ X := Subgroup.mem_zpowers (z : G)
    have hzS : (⟨(z : G), hXP hzX⟩ : ↥P) ∈ (S : Subgroup ↥P) :=
      hXS (Subgroup.mem_subgroupOf.mpr hzX)
    exact Subgroup.mem_map.mpr ⟨⟨(z : G), hXP hzX⟩, hzS, rfl⟩
  exact ⟨Q₁, hQ₁M, hQ₁sylP.isPGroup, hQ₁exp, hQ₁cl, hQ₁nc, hzQ₁, hQ₁norm⟩

private theorem false_of_mem_sup_commute {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c) (h1930 : H1930 D)
    (hSem : S23_9_Semireg D Ch) {e : G} (he : e ∈ D.M)
    (hXhyp : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup d.q ↥X →
      X ≤ D.M ⊓ Subgroup.centralizer ({e} : Set G) → X ∉ uniqueSet D.M ∧ d.q ∉ D.sig)
    {z : ↥D.M} (hzP : (z : G) ∈ CFSG.Open.pCoreOf 2 D.M ⊔ d.Q)
    (hzq : z ^ d.q = 1) (hzne : z ≠ 1)
    (hzcomm : z * ⟨e, he⟩ = ⟨e, he⟩ * z) : False := by
  classical
  obtain ⟨Q₁, hQ₁M, hQ₁p, hQ₁exp, hQ₁cl, hQ₁nc, hzQ₁, hQ₁norm⟩ :=
    exists_sylow_sup_mem c d hzP hzq hzne
  have hQC₁ : Q₁ ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ :=
    hSem h1930 c d.q d.hq d.hq2 Q₁ hQ₁M hQ₁p hQ₁nc hQ₁exp hQ₁cl hQ₁norm e he hXhyp
  have hzC : (z : G) ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (congrArg Subtype.val hzcomm).symm
  have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
    rw [← hQC₁]
    exact ⟨hzQ₁, hzC⟩
  exact (fun h => hzne (Subtype.ext h)) (Subgroup.mem_bot.mp hzbot)

private theorem E_inf_centralizer_eq_bot {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c) (h1930 : H1930 D)
    (hSem : S23_9_Semireg D Ch) {e : G} (he : e ∈ D.M)
    (heodd : Odd (orderOf e))
    (hXhyp : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup d.q ↥X →
      X ≤ D.M ⊓ Subgroup.centralizer ({e} : Set G) → X ∉ uniqueSet D.M ∧ d.q ∉ D.sig) :
    d.E ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨e, he⟩} : Set (Bar2 D.M)) = ⊥ := by
  classical
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  obtain ⟨z, hzq, hzne, hzcomm, hzP⟩ :=
    exists_mem_sup_commute_of_mem_centralizer c d he heodd hx.1 hx.2 hxne
  exact false_of_mem_sup_commute c d h1930 hSem he hXhyp hzP hzq hzne hzcomm

theorem S23_9_A0Data.fixV_zpowers_eq_bot_of_semireg_hyp {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (d : S23_9_A0Data D Ch c) (h1930 : H1930 D)
    (hSem : S23_9_Semireg D Ch) {e : G} (he : e ∈ D.M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (her : orderOf e = r)
    (hXhyp : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup d.q ↥X →
      X ≤ D.M ⊓ Subgroup.centralizer ({e} : Set G) → X ∉ uniqueSet D.M ∧ d.q ∉ D.sig) :
    d.fixV (barImage D.M (Subgroup.zpowers e)) = ⊥ ∧ r ≠ d.q := by
  classical
  let eM : ↥D.M := ⟨e, he⟩
  let eBar : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) eM
  have heodd : Odd (orderOf e) := by rw [her]; exact hr.odd_of_ne_two hr2
  have hnotdvd : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup hr hr2
  have heMr : orderOf eM = r := (Subgroup.orderOf_coe eM).symm.trans her
  haveI : Fact r.Prime := ⟨hr⟩
  have hebar : orderOf eBar = r :=
    CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime hnotdvd heMr
  have hEcent := E_inf_centralizer_eq_bot c d h1930 hSem he heodd hXhyp
  constructor
  · letI : Fact d.q.Prime := ⟨d.hq⟩
    letI : d.E.Normal := d.hEnorm
    letI : IsPGroup d.q ↥d.E := d.hEp
    letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
    letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
    have heBarMem : eBar ∈ barImage D.M (Subgroup.zpowers e) :=
      Subgroup.mem_map.mpr
        ⟨eM, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers e), rfl⟩
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv' : d.rep eBar v = v := hv eBar heBarMem
    have hrep : d.rep = CFSG.RankThree.PartOne.FixedRank36.frattiniRep d.q
        (MulAut.conjNormal (H := d.E)) := rfl
    rw [hrep] at hv'
    exact CFSG.GroupTheory.frattiniRep_conjNormal_eq_zero_of_inf_centralizer_eq_bot
      (P := d.E) d.hEp hr hebar hEcent v hv'
  · intro hrq
    haveI : Fact d.q.Prime := ⟨d.hq⟩
    haveI : d.E.Normal := d.hEnorm
    have hord : orderOf eBar ≠ d.q :=
      CFSG.GroupTheory.orderOf_ne_of_inf_centralizer_eq_bot (P := d.E) d.hEp d.hEne
        (Subgroup.le_normalizer_of_normal (H := d.E) (Subgroup.mem_zpowers eBar)) hEcent
    exact hord (by rw [hebar, hrq])

theorem s23_9_ASem_of (D : Data G) (Ch : Choice2011 G) (h54 : S23_5_4 D Ch)
    (h6 : S23_6 D Ch) (hSem : S23_9_Semireg D Ch) : S23_9_ASem D Ch := by
  intro h1930 c d b hb r hr hr2 hbr hbZ
  exact S23_9_A0Data.fixV_zpowers_eq_bot_of_semireg_hyp d h1930 hSem (c.hBM hb) hr hr2 hbr
    (centralizer_hyp_of_mem_B0 c h1930 h54 h6 hb hbZ d.hq d.hq2)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
