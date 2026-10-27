module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomyBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyHypG0

public section

namespace CFSG.StandardType.GGDichotomy

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

variable {G : Type} [Group G]

theorem rawDatum_elim_const {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun (R : Type) [Group R] _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h; exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h; exact hq)

theorem marking_elim_const {X : Type*} [Group X] {Q : Prop}
    (h : LargeEvenMarking X (fun _ _ _ _ _ _ => Q)) : Q := by
  obtain ⟨-, lab, -, hraw⟩ := h
  exact rawDatum_elim_const
    (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, -, hθ⟩ := hq
      exact hθ) hraw)

theorem le_normalizer_of_innerDiagOn {Bs X : Subgroup G} (h : GGInnerDiagOn Bs X) :
    Bs ≤ normalizer (X : Set G) :=
  marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h)

theorem le_normalizer_stdSub {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hBsB : B ≤ Bs)
    (hDJ : LargeEvenStdSubPre p B x L D J) (hN : Bs ≤ normalizer (L : Set G)) :
    Bs ≤ normalizer (J : Set G) := by
  have hBsD : Bs ≤ centralizer (D : Set G) := fun b hb => by
    rw [mem_centralizer_iff]
    intro d hd
    exact hcomm d (hBsB (hDJ.1 hd)) b hb
  rw [hDJ.2.2.2.2.1]
  exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
    (mem_normalizer_inf_centralizer (hN hg) (hBsD hg))

section Finite

variable [Finite G]

theorem le_normalizer_of_pComponent {p : ℕ} [Fact p.Prime] {Bs J X : Subgroup G} {d : G}
    (hBsd : Bs ≤ centralizer ({d} : Set G))
    (hX : LargeEvenPComponent p (centralizer ({d} : Set G)) X) (hJX : J ≤ X)
    (hJ : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J) (hBsJ : Bs ≤ normalizer (J : Set G)) :
    Bs ≤ normalizer (X : Set G) := by
  intro g hg
  have hgd : d * g = g * d := (mem_centralizer_singleton_iff.mp (hBsd hg)).symm
  have hgdg : g * d * g⁻¹ = d := by
    calc g * d * g⁻¹ = d * g * g⁻¹ := by rw [hgd]
      _ = d := mul_inv_cancel_right d g
  have hCg : (centralizer ({d} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({d} : Set G) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hgdg]
  have hX' := largeEvenPComponent_map_conj' hX g
  rw [hCg] at hX'
  have hJ' : J ≤ X.map (MulAut.conj g).toMonoidHom := by
    calc J = J.map (MulAut.conj g).toMonoidHom := (map_conj_eq_of_mem_normalizer (hBsJ hg)).symm
      _ ≤ X.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hJX
  exact mem_normalizer_iff_map_conj.mpr
    (GGDichotomy.eq_of_le_of_pComponent ((largeEvenPComponent_iff_lBalance p _ X).1 hX).2
      ((largeEvenPComponent_iff_lBalance p _ _).1 hX').2 hJX hJ' hJ hpJ)

theorem aut_commute_of_comm {Bs : Subgroup G} {n m : G} {t a : MulAut ↥Bs}
    (ht : ∀ b : ↥Bs, ((t b : ↥Bs) : G) = n * b * n⁻¹)
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = m * b * m⁻¹)
    (hc : ∀ b ∈ Bs, (n * m * n⁻¹ * m⁻¹) * b = b * (n * m * n⁻¹ * m⁻¹)) :
    t * a = a * t := by
  refine MulEquiv.ext fun b => Subtype.ext ?_
  have h1 : ((a (t b) : ↥Bs) : G) = m * (n * b * n⁻¹) * m⁻¹ := by rw [ha, ht]
  have h2 : (((t * a) b : ↥Bs) : G) = n * (m * b * m⁻¹) * n⁻¹ := by
    rw [MulAut.mul_apply, ht, ha]
  have h3 : (((a * t) b : ↥Bs) : G) = m * (n * b * n⁻¹) * m⁻¹ := by
    rw [MulAut.mul_apply, ha, ht]
  rw [h2, h3]
  have hw : (n * m * n⁻¹ * m⁻¹) * (m * (n * b * n⁻¹) * m⁻¹) =
      (m * (n * b * n⁻¹) * m⁻¹) * (n * m * n⁻¹ * m⁻¹) := by
    rw [← h1]
    exact hc _ (a (t b)).2
  calc n * (m * b * m⁻¹) * n⁻¹
      = (n * m * n⁻¹ * m⁻¹) * (m * (n * b * n⁻¹) * m⁻¹) * (n * m * n⁻¹ * m⁻¹)⁻¹ := by group
    _ = m * (n * b * n⁻¹) * m⁻¹ := by rw [hw, mul_inv_cancel_right]

theorem comm_of_mem_primeCore {p : ℕ} [Fact p.Prime] {Y Bs : Subgroup G} (hBsY : Bs ≤ Y)
    (hexp : ∀ b ∈ Bs, b ^ p = 1) {c : G} (hcN : c ∈ normalizer (Bs : Set G))
    (hcO : c ∈ CFSG.Open.lBalancePrimeCore p Y) : ∀ b ∈ Bs, c * b = b * c := by
  intro b hb
  have hOn : Y ≤ normalizer (CFSG.Open.lBalancePrimeCore p Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p Y)).mp
      (LBalance.primeCore_normal p Y)
  have hu_Bs : b * c * b⁻¹ * c⁻¹ ∈ Bs := by
    have h1 : c * b⁻¹ * c⁻¹ ∈ Bs := (mem_normalizer_iff.mp hcN b⁻¹).mp (Bs.inv_mem hb)
    have e : b * c * b⁻¹ * c⁻¹ = b * (c * b⁻¹ * c⁻¹) := by group
    rw [e]
    exact Bs.mul_mem hb h1
  have hu_O : b * c * b⁻¹ * c⁻¹ ∈ CFSG.Open.lBalancePrimeCore p Y := by
    have h1 : b * c * b⁻¹ ∈ CFSG.Open.lBalancePrimeCore p Y :=
      (mem_normalizer_iff.mp (hOn (hBsY hb)) c).mp hcO
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hcO)
  have hu1 : b * c * b⁻¹ * c⁻¹ = 1 :=
    eq_one_of_mem_of_coprime (LBalance.primeCore_coprime p Y) hu_O (hexp _ hu_Bs)
  have h1 : b * c * b⁻¹ = c := mul_inv_eq_one.mp hu1
  calc c * b = b * c * b⁻¹ * b := by rw [h1]
    _ = b * c := by group

theorem aut_commute_of_commutator_le {p : ℕ} [Fact p.Prime] {Y Bs Jt X J : Subgroup G}
    {t : MulAut ↥Bs} (hBsY : Bs ≤ Y) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hind : t ∈ ggInduced Jt Bs) (hJX : J ≤ X)
    (h : ⁅Jt, X⁆ ≤ CFSG.Open.lBalancePrimeCore p Y) :
    ∀ a ∈ ggInduced J Bs, t * a = a * t := by
  rintro a ⟨m, hmJ, hmN, hm⟩
  obtain ⟨n, hnJt, hnN, hn⟩ := hind
  have hc : n * m * n⁻¹ * m⁻¹ ∈ CFSG.Open.lBalancePrimeCore p Y :=
    h (Subgroup.commutator_mem_commutator hnJt (hJX hmJ))
  have hcN : n * m * n⁻¹ * m⁻¹ ∈ normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN hmN)
      (Subgroup.inv_mem _ hnN)) (Subgroup.inv_mem _ hmN)
  exact aut_commute_of_comm hn hm (comm_of_mem_primeCore hBsY hexp hcN hc)

theorem relIndex_ggFixG {p : ℕ} {Bs : Subgroup G} {t : MulAut ↥Bs} (hr : GGIsReflection p t) :
    (ggFixG Bs t).relIndex Bs = p := by
  have h1 : (ggFixG Bs t).subgroupOf Bs = ggFix t :=
    Subgroup.comap_map_eq_self_of_injective Bs.subtype_injective _
  have h2 := Subgroup.card_mul_index (ggFix t)
  have h3 : Nat.card ↥(ggFix t) = Nat.card {b : ↥Bs // t b = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => Iff.rfl)
  have hpos : 0 < Nat.card ↥(ggFix t) := Nat.card_pos
  unfold Subgroup.relIndex
  rw [h1]
  rw [h3] at h2 hpos
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans hr.2.symm)

theorem exists_mem_not_mem_zpowers {p : ℕ} (hp : p.Prime) {Bs D E : Subgroup G} {x : G}
    (hDBs : D ≤ Bs) (hD : Nat.card D = p ^ 2) (hxp : x ^ p = 1)
    (hE : E.relIndex Bs = p) (hxE : x ∉ E) : ∃ d ∈ D, d ∈ E ∧ d ∉ zpowers x := by
  by_contra hcon
  push_neg at hcon
  have hbot : E.subgroupOf D = ⊥ := by
    rw [eq_bot_iff_forall]
    intro z hz
    have hzE : (z : G) ∈ E := mem_subgroupOf.mp hz
    have hzx : (z : G) ∈ zpowers x := hcon z z.2 hzE
    by_contra hz1
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    exact hxE ((zpowers_le.mpr hzE) (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp hzx hz1'))
  have h1 : E.relIndex D = p ^ 2 := by
    unfold Subgroup.relIndex
    rw [hbot, Subgroup.index_bot, hD]
  have h2 : E.relIndex D ≤ E.relIndex Bs :=
    Subgroup.relIndex_le_of_le_right hDBs (by rw [hE]; exact hp.ne_zero)
  rw [h1, hE] at h2
  nlinarith [hp.two_le]

theorem mem_ggFixG_of_induced {Bs : Subgroup G} {t : MulAut ↥Bs} {n x : G} (hx : x ∈ Bs)
    (ht : ∀ b : ↥Bs, ((t b : ↥Bs) : G) = n * b * n⁻¹) (hnx : n * x * n⁻¹ = x) :
    x ∈ ggFixG Bs t :=
  ⟨⟨x, hx⟩, Subtype.ext ((ht ⟨x, hx⟩).trans hnx), rfl⟩

theorem dichotomy_core (hL : GGLBalanceInput) {p : ℕ} (hp : p.Prime) {Bs E Jt X : Subgroup G}
    {d : G} (hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hEBs : E ≤ Bs) (hdE : d ∈ E) (hYK : CFSG.Open.lBalanceIsKGroup ↥(centralizer ({d} : Set G)))
    (hBsX : Bs ≤ normalizer (X : Set G))
    (hX : CFSG.Open.lBalanceIsPComponent p (centralizer ({d} : Set G)) X)
    (hT : CFSG.Open.lBalanceIsPComponent p (centralizer (E : Set G)) Jt) :
    Jt ≤ X ∨ ⁅Jt, X⁆ ≤ CFSG.Open.lBalancePrimeCore p (centralizer ({d} : Set G)) := by
  classical
  let S : Finset G := (Set.toFinite (E : Set G)).toFinset
  have hSE : ∀ e, e ∈ S ↔ e ∈ E := fun e => Set.Finite.mem_toFinset _
  have hSset : (S : Set G) = (E : Set G) := Set.Finite.coe_toFinset _
  have hcd : centralizer ({d} : Set G) ⊓ centralizer (S : Set G) = centralizer (E : Set G) := by
    rw [hSset]
    exact inf_eq_right.mpr (centralizer_le (Set.singleton_subset_iff.mpr hdE))
  refine GGDichotomy.pComponent_le_or_commutator_le hL hp hYK hX S
    (fun e he => mem_centralizer_singleton_iff.mpr
      (hcomm e (hEBs ((hSE e).1 he)) d (hEBs hdE)))
    (fun e he => hexp e (hEBs ((hSE e).1 he)))
    (fun e he => hBsX (hEBs ((hSE e).1 he)))
    (fun e he f hf => hcomm e (hEBs ((hSE e).1 he)) f (hEBs ((hSE f).1 hf))) Jt ?_
  rw [hcd]
  exact hT

end Finite

end CFSG.StandardType.GGDichotomy

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggDichotomy_of_hyp (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {t : MulAut ↥Bs} {Jt : Subgroup G}
    (hr : GGIsReflection p t) (hind : t ∈ ggInduced Jt Bs)
    (hJC : Jt ≤ centralizer (ggFixG Bs t : Set G))
    (hpc : IsPComponent p (Jt.subgroupOf (centralizer (ggFixG Bs t : Set G)))) :
    Jt ≤ ggG0 p B x L D J ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t := by
  obtain ⟨⟨hI, hBsB, hDJ⟩, -, hInn, -, -⟩ := hHyp
  have hsimple : IsSimpleGroup G := hI.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hI.2.1
  have hKP : KProper InCatalog G := hI.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hS.2.2.1
  have hBsabel : IsElemAbelian p Bs := hBsB.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hxBs : x ∈ Bs := hBsB.1 hS.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  have hJJ : ⁅J, J⁆ = J :=
    commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hInn.1
  have hBsJ : Bs ≤ normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBsB.1 hDJ.1 hBsL
  have hEBs : ggFixG Bs t ≤ Bs := Subgroup.map_subtype_le _
  have hT : CFSG.Open.lBalanceIsPComponent p (centralizer (ggFixG Bs t : Set G)) Jt :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ Jt hJC).mp hpc
  have hKGroup : ∀ d : G, d ≠ 1 →
      CFSG.Open.lBalanceIsKGroup ↥(centralizer ({d} : Set G)) := fun d hd =>
    lBalanceIsKGroup_of_kProper hKP (centralizer_singleton_ne_top_of_isSimpleGroup hnab hd)
  have step : ∀ (d : G) (X : Subgroup G), d ≠ 1 → d ∈ ggFixG Bs t →
      LargeEvenPComponent p (centralizer ({d} : Set G)) X → J ≤ X →
      Jt ≤ X ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t := by
    intro d X hd1 hdE hX hJX
    have hBsd : Bs ≤ centralizer ({d} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr (hcomm b hb d (hEBs hdE))
    have hBsX := GGDichotomy.le_normalizer_of_pComponent hBsd hX hJX hJJ hpJ hBsJ
    rcases GGDichotomy.dichotomy_core hL hp hcomm hexp hEBs hdE (hKGroup d hd1) hBsX
        ((largeEvenPComponent_iff_lBalance p _ X).1 hX).2 hT with h | h
    · exact Or.inl h
    · exact Or.inr (GGDichotomy.aut_commute_of_commutator_le hBsd hexp hind hJX h)
  by_cases hxE : x ∈ ggFixG Bs t
  ·
    obtain ⟨hJL, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
    rcases step x L hx1 hxE hLpc hJL with h | h
    · exact Or.inl (h.trans (le_ggG0_left p B x L D J))
    · exact Or.inr h
  ·
    obtain ⟨d, hdD, hdE, hdx⟩ := GGDichotomy.exists_mem_not_mem_zpowers hp
      ((hDJ.1.1).trans hBsB.1) hDJ.1.2.2.1 (hexp x hxBs) (GGDichotomy.relIndex_ggFixG hr) hxE
    have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
    have hD : D = Subgroup.closure {x, d} := eq_closure_pair_of_mem hI hDJ hdD hdx
    obtain ⟨hKpc, hJK, -, hN | hV⟩ :=
      pumpup_of_stdSub (ggPumpupInput_of_lBalance hL) hI hDJ hpJ hD
    · rcases step d _ hd1 hdE hKpc hJK with h | h
      · exact Or.inl (h.trans (le_ggG0_of_ggNbr hN))
      · exact Or.inr h
    · rcases step d _ hd1 hdE hKpc hJK with h | h
      ·
        exfalso
        obtain ⟨n, hnJt, hnN, hn⟩ := hind
        have hsub : IsSubnormal (ggLayerClosure p (centralizer ({d} : Set G)) J)
            (centralizer ({d} : Set G)) :=
          (AssemblyBPredicates.isSubnormal_iff_open _ _).2
            ((largeEvenPComponent_iff_lBalance p _ _).1 hKpc).2.1
        have hO : n * x * n⁻¹ * x⁻¹ ∈
            CFSG.Open.lBalancePrimeCore p (centralizer ({d} : Set G)) :=
          largeEvenPPrimeCoreOf_le_of_isSubnormal hsub
            (hV (Subgroup.commutator_mem_commutator (h hnJt) (Subgroup.mem_zpowers x)))
        have hBs' : n * x * n⁻¹ * x⁻¹ ∈ Bs := by
          have h1 : n * x * n⁻¹ ∈ Bs := (mem_normalizer_iff.mp hnN x).mp hxBs
          exact Bs.mul_mem h1 (Bs.inv_mem hxBs)
        have hnx : n * x * n⁻¹ * x⁻¹ = 1 :=
          GGDichotomy.eq_one_of_mem_of_coprime (LBalance.primeCore_coprime p _) hO
            (hexp _ hBs')
        exact hxE (GGDichotomy.mem_ggFixG_of_induced hxBs hn (mul_inv_eq_one.mp hnx))
      · exact Or.inr h

theorem ggHypDichotomyInput_of_lBalance (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGHypDichotomyInput :=
  fun G _ _ p B Bs x L D J hHyp _ _ _ t Jt hr hind hJC hpc =>
    ggDichotomy_of_hyp hL hP hHyp hr hind hJC hpc

theorem ggHypDichotomyInput_of_catalogueSchreier (hS : CatalogueRelativeB.CatalogueSchreier)
    (hP : GGStdSubPrimeInput) : GGHypDichotomyInput :=
  ggHypDichotomyInput_of_lBalance (ggLBalanceInput_of_catalogueSchreier hS) hP

theorem ggHypG0Input_of_lBalance (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hE : GGExcReflInput) : GGHypG0Input :=
  ggHypG0Input_of_dichotomy (ggHypDichotomyInput_of_lBalance hL hP) hE

end Main

end CFSG.StandardType

end
