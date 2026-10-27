module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSignedCompare
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.CentralQuotientPRank
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport

open CFSG.Open CFSG.GroupTheory Subgroup

@[expose] def ModelK6rRank {G : Type} [Group G] [Finite G]
    (c₀ : Multiplicative (Fin 3 → ZMod 3) →* G) (r : ℕ) : Prop :=
  (2 ≤ CFSG.Open.pRank r (centralizer ({c₀ (Multiplicative.ofAdd ![1, 0, 0])} : Set G)) ∧
    2 ≤ CFSG.Open.pRank r (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 0])} : Set G)) ∧
    2 ≤ CFSG.Open.pRank r (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 1])} : Set G))) ∧
  1 ≤ CFSG.Open.pRank r (centralizer ({c₀ (Multiplicative.ofAdd ![1, 0, 0]),
    c₀ (Multiplicative.ofAdd ![0, 1, 0])} : Set G)) ∧
  1 ≤ CFSG.Open.pRank r (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 1]),
    c₀ (Multiplicative.ofAdd ![0, 0, 1])} : Set G))

@[expose] def ModelK7Dvd {G : Type} [Group G] [Finite G]
    (c₀ : Multiplicative (Fin 3 → ZMod 3) →* G) (p : ℕ) : Prop :=
  ¬ p ∣ Nat.card (centralizer (c₀.range : Set G)) ∧
  p ∣ Nat.card (centralizer ({c₀ (Multiplicative.ofAdd ![1, 0, 0])} : Set G)) ∧
  p ∣ Nat.card (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 0])} : Set G)) ∧
  p ∣ Nat.card (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 1])} : Set G))

section Model

variable {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
  {N : Subgroup H} [N.Normal] {Z : Subgroup Y} [Z.Normal]

theorem exists_centralizer_map_eq_of_model
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ g : H ⧸ N,
      centralizer ((((A.map (QuotientGroup.mk' Z)).map e.toMonoidHom : Subgroup (H ⧸ N)) :
        Set (H ⧸ N))) =
      (centralizer ((A₀.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))).map
        (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₀' : IsElemAbelian 3 (A₀.map (QuotientGroup.mk' N)) := hA₀.map _
  have hA' : IsElemAbelian 3 ((A.map (QuotientGroup.mk' Z)).map e.toMonoidHom) :=
    (hA.map _).map _
  have h27₀' : Nat.card (A₀.map (QuotientGroup.mk' N)) = 3 ^ 3 := by
    rw [Theorem82.Coords.card_map_mk' N hN hA₀.isPGroup, h₀27]
    norm_num
  have h27' : Nat.card ((A.map (QuotientGroup.mk' Z)).map e.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Theorem82.Coords.card_map_mk' Z hZ hA.isPGroup, h27]
    norm_num
  obtain ⟨g, hg⟩ := UniqueElemSylow.exists_conj_eq hU hA₀' h27₀' hA' h27'
  refine ⟨g, ?_⟩
  rw [hg]
  exact CoprimeTransport.centralizer_map_mulEquiv (MulAut.conj g) _

theorem pRank_centralizer_map_eq_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    CFSG.Open.pRank ℓ (centralizer ((A.map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) :
        Set (Y ⧸ Z))) =
      CFSG.Open.pRank ℓ (centralizer ((A₀.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) :
        Set (H ⧸ N))) := by
  obtain ⟨g, hg⟩ := exists_centralizer_map_eq_of_model hU hN hZ e hA₀ h₀27 hA h27
  rw [← CoprimeTransport.pRank_centralizer_map_mulEquiv e (A.map (QuotientGroup.mk' Z)), hg,
    Theorem82.Coords.pRank_map_conj (Fact.out : ℓ.Prime).one_lt]

theorem card_centralizer_map_eq_of_model
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    Nat.card (centralizer ((A.map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z))) =
      Nat.card (centralizer ((A₀.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) :
        Set (H ⧸ N))) := by
  obtain ⟨g, hg⟩ := exists_centralizer_map_eq_of_model hU hN hZ e hA₀ h₀27 hA h27
  rw [← CoprimeTransport.card_centralizer_map_mulEquiv e (A.map (QuotientGroup.mk' Z)), hg,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem pRank_centralizer_eq_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    CFSG.Open.pRank ℓ (centralizer (A : Set Y)) = CFSG.Open.pRank ℓ (centralizer (A₀ : Set H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CoprimeTransport.pRank_centralizer_map_mk_eq (s := 3) hZ hZℓ hA.isPGroup,
    ← CoprimeTransport.pRank_centralizer_map_mk_eq (s := 3) hN hNℓ hA₀.isPGroup]
  exact pRank_centralizer_map_eq_of_model hU hN hZ e hA₀ h₀27 hA h27

theorem dvd_card_centralizer_iff_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ℓ ∣ Nat.card (centralizer (A : Set Y)) ↔ ℓ ∣ Nat.card (centralizer (A₀ : Set H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CoprimeTransport.dvd_card_centralizer_map_mk_iff (s := 3) hZ hZℓ hA.isPGroup,
    ← CoprimeTransport.dvd_card_centralizer_map_mk_iff (s := 3) hN hNℓ hA₀.isPGroup,
    card_centralizer_map_eq_of_model hU hN hZ e hA₀ h₀27 hA h27]

theorem two_le_pRank_centralizer_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (hℓ : ¬ ℓ ∣ Nat.card Z ∨ (ℓ ≠ 2 ∧ Z ≤ center Y ∧ Nat.card Z = ℓ))
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    (h : 2 ≤ CFSG.Open.pRank ℓ (centralizer ((A₀.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) :
      Set (H ⧸ N))))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    2 ≤ CFSG.pRank ℓ (centralizer (A : Set Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  refine CentralQuotient.two_le_pRank_centralizer_of_quotient (s := 3) hZ hℓ hA.isPGroup ?_
  rwa [pRank_centralizer_map_eq_of_model hU hN hZ e hA₀ h₀27 hA h27]

theorem two_le_pRank_centralizer_of_model_of_coprime {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    (h : 2 ≤ CFSG.Open.pRank ℓ (centralizer (A₀ : Set H)))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    2 ≤ CFSG.pRank ℓ (centralizer (A : Set Y)) := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
    pRank_centralizer_eq_of_model hU hN hZ hNℓ hZℓ e hA₀ h₀27 hA h27]
  exact h

theorem pRank_le_pRank_map_mk_add_one_of_isCyclic {G : Type} [Group G] [Finite G] {ℓ : ℕ}
    [Fact ℓ.Prime] (N : Subgroup G) [N.Normal] [IsCyclic N] (C : Subgroup G) :
    CFSG.Open.pRank ℓ C ≤ CFSG.Open.pRank ℓ (C.map (QuotientGroup.mk' N)) + 1 := by
  have hp : ℓ.Prime := Fact.out
  obtain ⟨E, hEC, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt C
  have h1 := CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank ℓ hp
    (QuotientGroup.mk' N) hE _ hEc
  have h2 : CFSG.Open.pRank ℓ (QuotientGroup.mk' N).ker ≤ 1 := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.SectionRank.pRank_le_one_of_isCyclic hp ‹IsCyclic N›
  have h3 : CFSG.Open.pRank ℓ (E.map (QuotientGroup.mk' N)) ≤
      CFSG.Open.pRank ℓ (C.map (QuotientGroup.mk' N)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.map_mono hEC)
  omega

theorem two_le_pRank_centralizer_map_mk_of_three_le {H : Type} [Group H] [Finite H] {ℓ : ℕ}
    [Fact ℓ.Prime] {N : Subgroup H} [N.Normal] [IsCyclic N] (hN : ¬ 3 ∣ Nat.card N)
    {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀)
    (h : 3 ≤ CFSG.Open.pRank ℓ (centralizer (A₀ : Set H))) :
    2 ≤ CFSG.Open.pRank ℓ (centralizer ((A₀.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) :
      Set (H ⧸ N))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) hN hA₀.isPGroup]
  have := pRank_le_pRank_map_mk_add_one_of_isCyclic (ℓ := ℓ) N (centralizer (A₀ : Set H))
  omega

theorem pRank_centralizer_image_eq_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 3 → ZMod 3) →* Y} (h : IsSignedCoords A c)
    (S : Set (Multiplicative (Fin 3 → ZMod 3))) :
    CFSG.Open.pRank ℓ (centralizer (c '' S)) = CFSG.Open.pRank ℓ (centralizer (c₀ '' S)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSA : c '' S ⊆ A := by
    rintro _ ⟨v, -, rfl⟩
    rw [← h.2.1]
    exact ⟨v, rfl⟩
  have hSA₀ : c₀ '' S ⊆ A₀ := by
    rintro _ ⟨v, -, rfl⟩
    rw [← h₀.2.1]
    exact ⟨v, rfl⟩
  obtain ⟨g, hg⟩ := IsSignedCoords.exists_centralizer_eq_of_model h₀ N hN hU Z hZ e h S
  have h1 := CoprimeTransport.pRank_centralizer_image_mk_eq (s := 3) (p := ℓ) hZ hZℓ
    h.isElemAbelian.isPGroup hSA
  have h2 := CoprimeTransport.pRank_centralizer_image_mk_eq (s := 3) (p := ℓ) hN hNℓ
    h₀.isElemAbelian.isPGroup hSA₀
  have h3 := CoprimeTransport.pRank_centralizer_image_mulEquiv (p := ℓ) e
    (QuotientGroup.mk' Z '' (c '' S))
  have himg : e '' (QuotientGroup.mk' Z '' (c '' S)) =
      (fun v => e (QuotientGroup.mk' Z (c v))) '' S := by
    simp only [Set.image_image]
  have himg₀ : QuotientGroup.mk' N '' (c₀ '' S) = (fun v => QuotientGroup.mk' N (c₀ v)) '' S := by
    simp only [Set.image_image]
  rw [← h1, ← h2, ← h3, himg, himg₀, hg,
    Theorem82.Coords.pRank_map_conj (Fact.out : ℓ.Prime).one_lt]

theorem dvd_card_centralizer_image_iff_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 3 → ZMod 3) →* Y} (h : IsSignedCoords A c)
    (S : Set (Multiplicative (Fin 3 → ZMod 3))) :
    ℓ ∣ Nat.card (centralizer (c '' S)) ↔ ℓ ∣ Nat.card (centralizer (c₀ '' S)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSA : c '' S ⊆ A := by
    rintro _ ⟨v, -, rfl⟩
    rw [← h.2.1]
    exact ⟨v, rfl⟩
  have hSA₀ : c₀ '' S ⊆ A₀ := by
    rintro _ ⟨v, -, rfl⟩
    rw [← h₀.2.1]
    exact ⟨v, rfl⟩
  obtain ⟨g, hg⟩ := IsSignedCoords.exists_centralizer_eq_of_model h₀ N hN hU Z hZ e h S
  have himg : e '' (QuotientGroup.mk' Z '' (c '' S)) =
      (fun v => e (QuotientGroup.mk' Z (c v))) '' S := by
    simp only [Set.image_image]
  have himg₀ : QuotientGroup.mk' N '' (c₀ '' S) = (fun v => QuotientGroup.mk' N (c₀ v)) '' S := by
    simp only [Set.image_image]
  have hcard : Nat.card (centralizer (QuotientGroup.mk' Z '' (c '' S))) =
      Nat.card (centralizer (QuotientGroup.mk' N '' (c₀ '' S))) := by
    rw [← Subgroup.card_map_of_injective e.injective (f := e.toMonoidHom),
      ← CoprimeTransport.centralizer_image_mulEquiv e, himg, himg₀, hg,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← CoprimeTransport.dvd_card_map_mk_iff (N := Z) hZℓ (centralizer (c '' S)),
    ← CoprimeTransport.dvd_card_map_mk_iff (N := N) hNℓ (centralizer (c₀ '' S)),
    ← CoprimeTransport.centralizer_image_mk_eq (s := 3) hZ h.isElemAbelian.isPGroup hSA,
    ← CoprimeTransport.centralizer_image_mk_eq (s := 3) hN h₀.isElemAbelian.isPGroup hSA₀, hcard]

theorem k6r_of_model {r : ℕ} [Fact r.Prime]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNr : ¬ r ∣ Nat.card N) (hZr : ¬ r ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    (hr : ModelK6rRank c₀ r) {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → 2 ≤ CFSG.pRank r (centralizer (X : Set Y))) ∧
    (∀ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c →
      1 ≤ CFSG.pRank r (centralizer ({c (Multiplicative.ofAdd ![1, 0, 0]),
        c (Multiplicative.ofAdd ![0, 1, 0])} : Set Y)) ∧
      1 ≤ CFSG.pRank r (centralizer ({c (Multiplicative.ofAdd ![1, 1, 1]),
        c (Multiplicative.ofAdd ![0, 0, 1])} : Set Y))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hp1, hp2, hp3⟩, hpl1, hpl2⟩ := hr
  have hpt : ∀ c : Multiplicative (Fin 3 → ZMod 3) →* Y, IsSignedCoords A c →
      ∀ x : Multiplicative (Fin 3 → ZMod 3),
        2 ≤ CFSG.Open.pRank r (centralizer ({c₀ x} : Set H)) →
          2 ≤ CFSG.Open.pRank r (centralizer ({c x} : Set Y)) := by
    intro c hc x hx
    have := pRank_centralizer_image_eq_of_model h₀ hN hU hZ hNr hZr e hc {x}
    rw [Set.image_singleton, Set.image_singleton] at this
    rw [this]
    exact hx
  refine ⟨?_, fun c hc => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := IsSignedCoords.exists_of_model h₀ N hN hU Z hZ e hA h27
    intro X hXA hX3
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hc.le_pRank_centralizer_of_points (Fact.out : r.Prime).one_lt (hpt c hc _ hp1)
      (hpt c hc _ hp2) (hpt c hc _ hp3) X hXA hX3
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    have := pRank_centralizer_image_eq_of_model h₀ hN hU hZ hNr hZr e hc
      {Multiplicative.ofAdd ![1, 0, 0], Multiplicative.ofAdd ![0, 1, 0]}
    rw [Set.image_pair, Set.image_pair] at this
    rw [this]
    exact hpl1
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    have := pRank_centralizer_image_eq_of_model h₀ hN hU hZ hNr hZr e hc
      {Multiplicative.ofAdd ![1, 1, 1], Multiplicative.ofAdd ![0, 0, 1]}
    rw [Set.image_pair, Set.image_pair] at this
    rw [this]
    exact hpl2

theorem not_dvd_card_centralizer_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hN : ¬ 3 ∣ Nat.card N) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* H ⧸ N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀) (h₀27 : Nat.card A₀ = 27)
    (h : ¬ ℓ ∣ Nat.card (centralizer (A₀ : Set H)))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ¬ ℓ ∣ Nat.card (centralizer (A : Set Y)) := by
  rwa [dvd_card_centralizer_iff_of_model hU hN hZ hNℓ hZℓ e hA₀ h₀27 hA h27]

theorem dvd_card_centralizer_points_of_model {ℓ : ℕ} [Fact ℓ.Prime]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 3 → ZMod 3) →* H} (h₀ : IsSignedCoords A₀ c₀)
    (hN : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N)) (hZ : ¬ 3 ∣ Nat.card Z)
    (hNℓ : ¬ ℓ ∣ Nat.card N) (hZℓ : ¬ ℓ ∣ Nat.card Z) (e : Y ⧸ Z ≃* H ⧸ N)
    (h₁ : ℓ ∣ Nat.card (centralizer ({c₀ (Multiplicative.ofAdd ![1, 0, 0])} : Set H)))
    (h₂ : ℓ ∣ Nat.card (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 0])} : Set H)))
    (h₃ : ℓ ∣ Nat.card (centralizer ({c₀ (Multiplicative.ofAdd ![1, 1, 1])} : Set H)))
    {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → ℓ ∣ Nat.card (centralizer (X : Set Y)) := by
  obtain ⟨c, hc⟩ := IsSignedCoords.exists_of_model h₀ N hN hU Z hZ e hA h27
  have key : ∀ x : Multiplicative (Fin 3 → ZMod 3),
      ℓ ∣ Nat.card (centralizer ({c₀ x} : Set H)) → ℓ ∣ Nat.card (centralizer ({c x} : Set Y)) := by
    intro x hx
    have := (dvd_card_centralizer_image_iff_of_model h₀ hN hU hZ hNℓ hZℓ e hc {x}).2
      (by simpa using hx)
    simpa using this
  exact hc.dvd_card_centralizer_of_points (key _ h₁) (key _ h₂) (key _ h₃)

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport
