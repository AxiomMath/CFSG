module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Glauberman
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.LowTwoRankDefs

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
open scoped commutatorElement Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.HypAAux

variable {Γ : Type u} [Group Γ]

theorem inf_sup_le_sup_inf {S U X : Subgroup Γ} (hSU : S ≤ U)
    (hS : S ≤ Subgroup.normalizer (X : Set Γ)) : U ⊓ (S ⊔ X) ≤ S ⊔ (U ⊓ X) := by
  intro x hx
  obtain ⟨hxU, hxSX⟩ := Subgroup.mem_inf.mp hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right S X hS
  have hx' : x ∈ (S : Set Γ) * (X : Set Γ) := by
    rw [← hmul]
    exact hxSX
  obtain ⟨s, hs, n, hn, rfl⟩ := Set.mem_mul.mp hx'
  have hs' : s ∈ S := hs
  have hn' : n ∈ X := hn
  have hnU : n ∈ U ⊓ X :=
    Subgroup.mem_inf.mpr ⟨by simpa using mul_mem (inv_mem (hSU hs')) hxU, hn'⟩
  exact mul_mem (Subgroup.mem_sup_left hs') (Subgroup.mem_sup_right hnU)

theorem inf_sup_le_of_le_normalizer {S U N : Subgroup Γ} (hSU : S ≤ U)
    (hS : S ≤ Subgroup.normalizer (N : Set Γ)) (hNU : U ⊓ N ≤ S) : U ⊓ (S ⊔ N) ≤ S :=
  (inf_sup_le_sup_inf hSU hS).trans (sup_le le_rfl hNU)

variable {N : Subgroup Γ}

theorem isChiefFactorOf_qimg_iff {Y L M : Subgroup Γ} (hLY : L ≤ Y) (hML : M ≤ L)
    (hY : Y ≤ nrm N) (hNM : Y ⊓ N ≤ M) :
    IsChiefFactorOf (qimg N Y) (qimg N L) (qimg N M) ↔ IsChiefFactorOf Y L M := by
  have hMY : M ≤ Y := hML.trans hLY
  have hMn : M ≤ nrm N := hMY.trans hY
  have hLn : L ≤ nrm N := hLY.trans hY
  have hNL : Y ⊓ N ≤ L := hNM.trans hML
  constructor
  · rintro ⟨⟨hMY', hYM'⟩, ⟨hLY', hYL'⟩, hlt', hmin'⟩
    refine ⟨⟨hMY, ?_⟩, ⟨hLY, ?_⟩, lt_of_le_of_ne hML fun heq => hlt'.ne
      (congrArg (qimg N) heq), fun K hK hMK hKL => ?_⟩
    · exact (qimg_le_normalizer_iff (X := Y) hMY hNM hY le_rfl).mp hYM'
    · exact (qimg_le_normalizer_iff (X := Y) hLY hNL hY le_rfl).mp hYL'
    · have hKY : K ≤ Y := hK.1
      have hKn : K ≤ nrm N := hKY.trans hY
      have hNK : Y ⊓ N ≤ K := hNM.trans hMK
      rcases hmin' (qimg N K) ⟨qimg_mono hKY, qimg_le_normalizer hK.2⟩ (qimg_mono hMK)
        (qimg_mono hKL) with h | h
      · left
        have h1 : K ≤ M ⊔ N := (qimg_le_qimg_iff hKn hMn).mp h.le
        exact le_antisymm ((le_inf hKY h1).trans (inf_sup_le_of_le_normalizer hMY hMn hNM)) hMK
      · right
        have h1 : L ≤ K ⊔ N := (qimg_le_qimg_iff hLn hKn).mp h.ge
        exact le_antisymm hKL ((le_inf hLY h1).trans (inf_sup_le_of_le_normalizer hKY hKn hNK))
  · rintro ⟨⟨hMY', hYM'⟩, ⟨hLY', hYL'⟩, hlt, hmin⟩
    refine ⟨⟨qimg_mono hMY, qimg_le_normalizer hYM'⟩, ⟨qimg_mono hLY, qimg_le_normalizer hYL'⟩,
      lt_of_le_of_ne (qimg_mono hML) fun heq => ?_, fun K' hK' hMK' hK'L => ?_⟩
    · have h1 : L ≤ M ⊔ N := (qimg_le_qimg_iff hLn hMn).mp heq.ge
      exact hlt.ne (le_antisymm hML
        ((le_inf hLY h1).trans (inf_sup_le_of_le_normalizer hMY hMn hNM)))
    · have hqK : qpre N K' ≤ nrm N := qpre_le_nrm K'
      have hNq : N ≤ qpre N K' := le_qpre K'
      have hK'Y : K' ≤ qimg N Y := hK'.1
      have himg : qimg N (Y ⊓ qpre N K') = K' := by
        rw [qimg_inf_of_le hqK hNq, qimg_qpre]
        exact inf_eq_right.mpr hK'Y
      have hMK : M ≤ Y ⊓ qpre N K' := le_inf hMY ((qimg_le_iff hMn).mp hMK')
      have hKL : Y ⊓ qpre N K' ≤ L := by
        refine (inf_le_inf_left Y (qpre_mono hK'L)).trans ?_
        rw [qpre_qimg hLn]
        exact inf_sup_le_of_le_normalizer hLY hLn hNL
      have hnorm : Y ≤ Subgroup.normalizer ((Y ⊓ qpre N K' : Subgroup Γ) : Set Γ) := by
        refine fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hy, ?_⟩
        have key := (qimg_le_normalizer_iff (R := N) (Y := nrm N) (M := qpre N K') (X := Y) hqK
          (inf_le_right.trans hNq) le_rfl hY).mp
        rw [qimg_qpre] at key
        exact key hK'.2 hy
      rcases hmin _ ⟨inf_le_left, hnorm⟩ hMK hKL with h | h
      · left
        rw [← himg, h]
      · right
        rw [← himg, h]

theorem isSolvableSection_bot_iff {X : Subgroup Γ} :
    IsSolvableSection X ⊥ ↔ Group.IsSolvable ↥X := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨⟨n, ?_⟩⟩
    rw [Subgroup.bot_subgroupOf] at hn
    exact le_bot_iff.mp hn
  · intro h
    obtain ⟨n, hn⟩ := h.solvable
    exact ⟨n, by rw [Subgroup.bot_subgroupOf]; exact hn.le⟩

theorem isSolvableSection_qimg {X₁ X₂ : Subgroup Γ} (h₁ : X₁ ≤ nrm N) (h₂ : X₂ ≤ X₁)
    (h : IsSolvableSection X₁ X₂) : IsSolvableSection (qimg N X₁) (qimg N X₂) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  refine (derivedSeries_le_map_derivedSeries (qres_surjective (R := N) h₁) n).trans ?_
  rw [subgroupOf_qimg h₁ h₂]
  exact Subgroup.map_mono hn

theorem qpre_le_of_le_qimg {Y : Subgroup Γ} (hY : Y ≤ nrm N) (hNY : N ≤ Y) {X' : Subgroup (QG N)}
    (h : X' ≤ qimg N Y) : qpre N X' ≤ Y := by
  refine (qpre_mono h).trans ?_
  rw [qpre_qimg hY, sup_eq_left.mpr hNY]

theorem admits_qpre {Q : Subgroup Γ} {X' : Subgroup (QG N)} (hQ : Q ≤ nrm N)
    (h : Admits (qimg N Q) X') : Admits Q (qpre N X') := by
  have key := (qimg_le_normalizer_iff (R := N) (Y := nrm N) (M := qpre N X') (X := Q)
    (qpre_le_nrm X') (inf_le_right.trans (le_qpre X')) le_rfl hQ).mp
  rw [qimg_qpre] at key
  exact key h

theorem admits_qimg {Q X : Subgroup Γ} (h : Admits Q X) : Admits (qimg N Q) (qimg N X) :=
  qimg_le_normalizer h

theorem inf_le_of_qimg_inf_le {S U T : Subgroup Γ} (hU : U ≤ nrm N) (hSU : S ≤ U)
    (hNU : U ⊓ N ≤ S) (hNT : N ≤ T) (hT : T ≤ nrm N)
    (h : qimg N U ⊓ qimg N T ≤ qimg N S) : U ⊓ T ≤ S := by
  have hS : S ≤ nrm N := hSU.trans hU
  have h1 : U ⊓ T ≤ S ⊔ N := by
    have h2 : qimg N (U ⊓ T) ≤ qimg N S := by
      rw [qimg_inf_of_le hT hNT]
      exact h
    have := (qimg_le_iff (inf_le_left.trans hU)).mp h2
    rwa [qpre_qimg hS] at this
  exact (le_inf inf_le_left h1).trans (inf_sup_le_of_le_normalizer hSU hS hNU)

theorem centralizer_zpowers_eq (e : Γ) :
    Subgroup.centralizer ((Subgroup.zpowers e : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer {e} := by
  refine le_antisymm (Subgroup.centralizer_le ?_) ?_
  · rw [Set.singleton_subset_iff]
    exact Subgroup.mem_zpowers e
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute g e := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact (hc.zpow_right k).eq.symm

theorem qimg_inf_centralizer_singleton {p : ℕ} (hp : p.Prime) {A H : Subgroup Γ}
    (hA : IsElemAbelian p A) (hAH : A ≤ Subgroup.normalizer (H : Set Γ)) (hAN : A ≤ nrm N)
    (hHN : H ≤ nrm N) (hcop : Nat.Coprime p (Nat.card H)) {e : Γ} (he : e ∈ A) :
    qimg N (H ⊓ Subgroup.centralizer {e}) =
      qimg N H ⊓ Subgroup.centralizer {qmap N ⟨e, hAN he⟩} := by
  have hE : IsElemAbelian p (Subgroup.zpowers e) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have := hA.2 e he
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
  have h := qimg_inf_centralizer hp hE (Subgroup.zpowers_le.mpr (hAH he))
    (Subgroup.zpowers_le.mpr (hAN he)) hHN hcop
  rw [qimg_zpowers (hAN he), centralizer_zpowers_eq, centralizer_zpowers_eq] at h
  exact h

theorem card_lt_of_ne [Finite Γ] {H K : Subgroup Γ} (hHK : H ≤ K) (hne : H ≠ K) :
    Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le hHK) fun heq =>
    hne (Subgroup.eq_of_le_of_card_ge hHK heq.ge)

theorem card_qimg_lt [Finite Γ] {Y : Subgroup Γ} (hNY : N ≤ Y) (hY : Y ≤ nrm N) (hN : N ≠ ⊥) :
    Nat.card (qimg N Y) < Nat.card Y := by
  have h1 := card_qimg_mul_card hNY hY
  have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  have h3 : 0 < Nat.card (qimg N Y) := Nat.card_pos
  nlinarith

theorem qimg_inf_qpre {H₀ : Subgroup Γ} {X' : Subgroup (QG N)} (hX' : X' ≤ qimg N H₀) :
    qimg N (H₀ ⊓ qpre N X') = X' := by
  rw [qimg_inf_of_le (qpre_le_nrm X') (le_qpre X'), qimg_qpre]
  exact inf_eq_right.mpr hX'

theorem eq_of_qimg_eq {H₀ X Y : Subgroup Γ} (hH₀ : H₀ ≤ nrm N) (hX : X ≤ H₀) (hY : Y ≤ H₀)
    (hXN : H₀ ⊓ N ≤ X) (hYN : H₀ ⊓ N ≤ Y) (h : qimg N X = qimg N Y) : X = Y := by
  refine le_antisymm ?_ ?_
  · have h1 : X ≤ Y ⊔ N := (qimg_le_qimg_iff (hX.trans hH₀) (hY.trans hH₀)).mp h.le
    exact (le_inf hX h1).trans (inf_sup_le_of_le_normalizer hY (hY.trans hH₀) hYN)
  · have h1 : Y ≤ X ⊔ N := (qimg_le_qimg_iff (hY.trans hH₀) (hX.trans hH₀)).mp h.ge
    exact (le_inf hY h1).trans (inf_sup_le_of_le_normalizer hX (hX.trans hH₀) hXN)

theorem card_qimg_eq_of_inf_eq_bot {E : Subgroup Γ} (hE : E ≤ nrm N) (h : N ⊓ E = ⊥) :
    Nat.card (qimg N E) = Nat.card E := by
  have hinj : Function.Injective (qres N E hE) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_qres hE, Subgroup.subgroupOf_eq_bot]
    exact disjoint_iff.mpr h
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, qres_surjective hE⟩)).symm

theorem card_qimg_eq_of_coprime {E : Subgroup Γ} (hE : E ≤ nrm N)
    (h : Nat.Coprime (Nat.card N) (Nat.card E)) : Nat.card (qimg N E) = Nat.card E :=
  card_qimg_eq_of_inf_eq_bot hE (disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard h))

theorem qmap_commutator {x y : Γ} (hx : x ∈ nrm N) (hy : y ∈ nrm N) :
    ∃ h : ⁅x, y⁆ ∈ nrm N,
      qmap N ⟨⁅x, y⁆, h⟩ = ⁅qmap N ⟨x, hx⟩, qmap N ⟨y, hy⟩⁆ :=
  ⟨(⁅(⟨x, hx⟩ : ↥(nrm N)), ⟨y, hy⟩⁆ : ↥(nrm N)).2,
    map_commutatorElement (qmap N) ⟨x, hx⟩ ⟨y, hy⟩⟩

theorem commutator_mem_qpre_iff {T : Subgroup (QG N)} {x y : Γ} (hx : x ∈ nrm N)
    (hy : y ∈ nrm N) :
    ⁅x, y⁆ ∈ qpre N T ↔ ⁅qmap N ⟨x, hx⟩, qmap N ⟨y, hy⟩⁆ ∈ T := by
  obtain ⟨h, hq⟩ := qmap_commutator hx hy
  rw [mem_qpre_iff]
  constructor
  · rintro ⟨h', h2⟩
    rwa [← hq]
  · intro h2
    exact ⟨h, by rwa [hq]⟩

theorem nearASolvable_qimg {p : ℕ} {A X : Subgroup Γ} (hp : p.Prime) (hE : IsElemAbelian p A)
    (hAX : Admits A X) (hXn : X ≤ nrm N) (hAn : A ≤ nrm N) (h : NearASolvable p A X) :
    NearASolvable p (qimg N A) (qimg N X) := by
  obtain ⟨hnear, hsol⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hcop, hsec⟩ := signalizerNearPSolvable_iff.1 hnear
    refine signalizerNearPSolvable_iff.2 ⟨?_, fun S _ _ hS hnc => ?_⟩
    · have h1 : Nat.card (qimg N X) ∣ Nat.card (X.subgroupOf (nrm N)) :=
        Subgroup.card_map_dvd _ _
      rw [card_subgroupOf hXn] at h1
      exact hcop.coprime_dvd_right h1
    · exact hsec S ((isSectionOf_of_isSectionOf_map (qmap N) (X.subgroupOf (nrm N)) hS).trans
        (IsSectionOf.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXn).symm)) hnc
  · have himg := qimg_inf_centralizer hp hE hAX hAn hXn hnear.1
    have hY : X ⊓ Subgroup.centralizer (A : Set Γ) ≤ nrm N := inf_le_left.trans hXn
    show Group.IsSolvable (qimg N X ⊓ Subgroup.centralizer
      ((qimg N A : Subgroup (QG N)) : Set (QG N)) : Subgroup (QG N))
    rw [← himg]
    exact Group.isSolvable_of_surjective (qres_surjective hY)

theorem secCenIn_qimg_eq {D D₁ D₂ : Subgroup Γ} (hD : D ≤ nrm N) (hD₂₁ : D₂ ≤ D₁)
    (hD₁ : D₁ ≤ D) (hn₂ : D ≤ Subgroup.normalizer (D₂ : Set Γ))
    (hn₁ : D ≤ Subgroup.normalizer (D₁ : Set Γ)) (hND : N ⊓ D ≤ D₂)
    (h : secCenIn D D₁ D₂ = D₁) :
    secCenIn (qimg N D) (qimg N D₁) (qimg N D₂) = qimg N D₁ := by
  have hD₂D : D₂ ≤ D := hD₂₁.trans hD₁
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨hzD, hzs⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨a, ha, rfl⟩ := (mem_qimg_iff N D z).mp hzD
    obtain ⟨-, -, hcomm⟩ := McBride.mem_sectionCentralizer_iff.mp hzs
    have haD : (a : Γ) ∈ D := ha
    have hmem : (a : Γ) ∈ secCenIn D D₁ D₂ := by
      refine Subgroup.mem_inf.mpr ⟨haD, McBride.mem_sectionCentralizer_iff.mpr
        ⟨hn₂ haD, hn₁ haD, fun y hy => ?_⟩⟩
      have hyn : y ∈ nrm N := hD (hD₁ hy)
      have hyD : y ∈ D := hD₁ hy
      have h1 : ⁅qmap N a, qmap N ⟨y, hyn⟩⁆ ∈ qimg N D₂ :=
        hcomm _ ((mem_qimg_iff N D₁ _).mpr ⟨⟨y, hyn⟩, hy, rfl⟩)
      have h2 : ⁅(a : Γ), y⁆ ∈ qpre N (qimg N D₂) :=
        (commutator_mem_qpre_iff a.2 hyn).mpr h1
      rw [qpre_qimg (hD₂D.trans hD)] at h2
      have h3 : ⁅(a : Γ), y⁆ ∈ D := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem haD hyD) (inv_mem haD)) (inv_mem hyD)
      exact inf_sup_le_of_le_normalizer hD₂D (hD₂D.trans hD) (by rwa [inf_comm]) ⟨h3, h2⟩
    rw [h] at hmem
    exact (mem_qimg_iff N D₁ _).mpr ⟨a, hmem, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := (mem_qimg_iff N D₁ z).mp hz
    have haD : (a : Γ) ∈ D := hD₁ ha
    have hmem : (a : Γ) ∈ secCenIn D D₁ D₂ := by
      rw [h]
      exact ha
    obtain ⟨-, -, hc⟩ := McBride.mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp hmem).2
    have hzD : qmap N a ∈ qimg N D := (mem_qimg_iff N D _).mpr ⟨a, haD, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hzD, McBride.mem_sectionCentralizer_iff.mpr
      ⟨qimg_le_normalizer hn₂ hzD, qimg_le_normalizer hn₁ hzD, fun y' hy' => ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := (mem_qimg_iff N D₁ y').mp hy'
    obtain ⟨hmn, hq⟩ := qmap_commutator a.2 b.2
    have : ⁅qmap N a, qmap N b⁆ = qmap N ⟨⁅(a : Γ), (b : Γ)⁆, hmn⟩ := hq.symm
    rw [this]
    exact (mem_qimg_iff N D₂ _).mpr ⟨⟨⁅(a : Γ), (b : Γ)⁆, hmn⟩, hc _ hb, rfl⟩

theorem le_sectionCentralizer_inf_qpre {X H₀ : Subgroup Γ} {N' L' : Subgroup (QG N)}
    (hX : X ≤ nrm N) (hXH₀ : X ≤ Subgroup.normalizer (H₀ : Set Γ))
    (h : qimg N X ≤ McBride.sectionCentralizer N' L') :
    X ≤ McBride.sectionCentralizer (H₀ ⊓ qpre N N') (H₀ ⊓ qpre N L') := by
  intro g hg
  have hgn : g ∈ nrm N := hX hg
  have hq : qmap N ⟨g, hgn⟩ ∈ McBride.sectionCentralizer N' L' :=
    h ((mem_qimg_iff N X _).mpr ⟨⟨g, hgn⟩, hg, rfl⟩)
  obtain ⟨hq1, hq2, hq3⟩ := McBride.mem_sectionCentralizer_iff.mp hq
  refine McBride.mem_sectionCentralizer_iff.mpr ⟨?_, ?_, fun y hy => ?_⟩
  · have key := (mem_normalizer_qimg_iff (R := N) (Y := nrm N) (M := qpre N N') (qpre_le_nrm N')
      (inf_le_right.trans (le_qpre N')) le_rfl hgn).mp
    rw [qimg_qpre] at key
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXH₀ hg, key hq1⟩
  · have key := (mem_normalizer_qimg_iff (R := N) (Y := nrm N) (M := qpre N L') (qpre_le_nrm L')
      (inf_le_right.trans (le_qpre L')) le_rfl hgn).mp
    rw [qimg_qpre] at key
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXH₀ hg, key hq2⟩
  · obtain ⟨hyH, hyL⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyn, hyL'⟩ := mem_qpre_iff.mp hyL
    refine Subgroup.mem_inf.mpr ⟨?_, (commutator_mem_qpre_iff hgn hyn).mpr (hq3 _ hyL')⟩
    have : g * y * g⁻¹ ∈ H₀ := (Subgroup.mem_normalizer_iff.mp (hXH₀ hg) y).mp hyH
    rw [commutatorElement_def]
    exact mul_mem this (inv_mem hyH)

theorem isDirectProductMod_inf_qpre {H₀ D₁ D₂ : Subgroup Γ} {N' L' : Subgroup (QG N)}
    (hH₀ : H₀ ≤ nrm N) (hD₁ : D₁ ≤ H₀) (hD₂ : D₂ ≤ H₀) (hN'H : N' ≤ qimg N H₀)
    (hL'H : L' ≤ qimg N H₀)
    (h : IsDirectProductMod N' (qimg N D₁ ⊔ N') (qimg N D₂ ⊔ N') L') :
    IsDirectProductMod (H₀ ⊓ qpre N N') (D₁ ⊔ H₀ ⊓ qpre N N') (D₂ ⊔ H₀ ⊓ qpre N N')
      (H₀ ⊓ qpre N L') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hN₁H : H₀ ⊓ qpre N N' ≤ H₀ := inf_le_left
  have hL₁H : H₀ ⊓ qpre N L' ≤ H₀ := inf_le_left
  have hqN₁ : qimg N (H₀ ⊓ qpre N N') = N' := qimg_inf_qpre hN'H
  have hqL₁ : qimg N (H₀ ⊓ qpre N L') = L' := qimg_inf_qpre hL'H
  have hMN₁ : H₀ ⊓ N ≤ H₀ ⊓ qpre N N' := inf_le_inf_left H₀ (le_qpre N')
  have hN₁L₁ : H₀ ⊓ qpre N N' ≤ H₀ ⊓ qpre N L' := inf_le_inf_left H₀ (qpre_mono h2)
  have hP : D₂ ⊔ H₀ ⊓ qpre N N' ≤ H₀ := sup_le hD₂ hN₁H
  have hPn : D₂ ⊔ H₀ ⊓ qpre N N' ≤ nrm N := hP.trans hH₀
  have hD₂n : D₂ ≤ nrm N := hD₂.trans hH₀
  have hD₁n : D₁ ≤ nrm N := hD₁.trans hH₀
  have hN₁n : H₀ ⊓ qpre N N' ≤ nrm N := hN₁H.trans hH₀
  have hL₁n : H₀ ⊓ qpre N L' ≤ nrm N := hL₁H.trans hH₀
  refine ⟨le_sup_right, hN₁L₁, ?_, ?_, ?_⟩
  · refine eq_of_qimg_eq hH₀ (sup_le hP hL₁H) (sup_le hD₁ hN₁H)
      (hMN₁.trans (le_sup_right.trans le_sup_left)) (hMN₁.trans le_sup_right) ?_
    rw [qimg_sup hPn hL₁n, qimg_sup hD₂n hN₁n, qimg_sup hD₁n hN₁n, hqN₁, hqL₁]
    exact h3
  · have hinf : (D₂ ⊔ H₀ ⊓ qpre N N') ⊓ (H₀ ⊓ qpre N L') =
        (D₂ ⊔ H₀ ⊓ qpre N N') ⊓ qpre N L' := by
      rw [← inf_assoc, inf_eq_left.mpr hP]
    rw [hinf]
    refine eq_of_qimg_eq hH₀ (inf_le_left.trans hP) hN₁H
      (le_inf (hMN₁.trans le_sup_right) ((hMN₁.trans hN₁L₁).trans inf_le_right)) hMN₁ ?_
    rw [qimg_inf_of_le (qpre_le_nrm L') (le_qpre L'), qimg_sup hD₂n hN₁n, hqN₁, qimg_qpre]
    exact h4
  · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hxn : x ∈ nrm N := hPn hx
    obtain ⟨hyH, hyL⟩ := Subgroup.mem_inf.mp hy
    have hyn : y ∈ nrm N := hL₁n hy
    refine Subgroup.mem_inf.mpr ⟨?_, (commutator_mem_qpre_iff hxn hyn).mpr (h5 ?_)⟩
    · have hx₀ : x ∈ H₀ := hP hx
      have : x * y * x⁻¹ ∈ H₀ := mul_mem (mul_mem hx₀ hyH) (inv_mem hx₀)
      rw [commutatorElement_def]
      exact mul_mem this (inv_mem hyH)
    · refine Subgroup.commutator_mem_commutator ?_ ?_
      · have := (mem_qimg_iff N (D₂ ⊔ H₀ ⊓ qpre N N') (qmap N ⟨x, hxn⟩)).mpr ⟨⟨x, hxn⟩, hx, rfl⟩
        rwa [qimg_sup hD₂n hN₁n, hqN₁] at this
      · exact (mem_qpre_iff.mp hyL).2

theorem isPGroup_of_isElemAbelian {p : ℕ} {A : Subgroup Γ} (hA : IsElemAbelian p A) :
    IsPGroup p A := CFSG.Open.IsElemAbelian.isPGroup hA

theorem exists_mul_of_mem_sup_of_centralizer [Finite Γ] {p : ℕ} (hp : p.Prime)
    {A K₁ K₂ : Subgroup Γ} (hA : IsElemAbelian p A) (h₁ : Nat.Coprime p (Nat.card K₁))
    (hA₁ : A ≤ Subgroup.normalizer (K₁ : Set Γ)) (hA₂ : A ≤ Subgroup.normalizer (K₂ : Set Γ))
    (h₁₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set Γ)) {x : Γ} (hx : x ∈ K₁ ⊔ K₂)
    (hxA : x ∈ Subgroup.centralizer (A : Set Γ)) :
    ∃ a ∈ K₁ ⊓ Subgroup.centralizer (A : Set Γ), ∃ b ∈ K₂ ⊓ Subgroup.centralizer (A : Set Γ),
      x = a * b := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ h₁₂
  have hx' : x ∈ (K₁ : Set Γ) * (K₂ : Set Γ) := by
    rw [← hmul]
    exact hx
  exact McBride.exists_mul_of_mem_centralizer hp (isPGroup_of_isElemAbelian hA) h₁ hA₁ hA₂ hx' hxA

theorem inf_centralizer_sup_le [Finite Γ] {p : ℕ} (hp : p.Prime) {A K₁ K₂ : Subgroup Γ}
    (hA : IsElemAbelian p A) (h₁ : Nat.Coprime p (Nat.card K₁))
    (hA₁ : A ≤ Subgroup.normalizer (K₁ : Set Γ)) (hA₂ : A ≤ Subgroup.normalizer (K₂ : Set Γ))
    (h₁₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set Γ)) :
    (K₁ ⊔ K₂) ⊓ Subgroup.centralizer (A : Set Γ) ≤
      (K₁ ⊓ Subgroup.centralizer (A : Set Γ)) ⊔ (K₂ ⊓ Subgroup.centralizer (A : Set Γ)) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_centralizer hp hA h₁ hA₁ hA₂ h₁₂
    hx.1 hx.2
  exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

end CFSG.SignalizerFunctorTheorem.McBride.Near.HypAAux
