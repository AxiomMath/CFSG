module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T2
public import CFSG.LocalAnalysis.UniquenessCase.UC6S25
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactInnerAction KFactWeakClosure)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree (DichThree)

@[expose] def K332Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ →
    (∀ x ∈ S, x ^ 3 = 1 → ∀ y ∈ S, x * y = y * x) → CFSG.Open.pRank 3 S ≤ 3 →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1

@[expose] def K332ThreeAb : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ →
    (∀ x ∈ S, x ^ 3 = 1 → ∀ y ∈ S, y ^ 3 = 1 → x * y = y * x) → CFSG.Open.pRank 3 S ≤ 3 →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = 3 → IsWeaklyClosedIn Z S →
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1

theorem k332Three_of_ab (h : K332ThreeAb) : K332Three := by
  intro G _ _ hK S hS hΩ hrank Z hZS hZcard hwc
  exact h G hK S hS (fun x hx hx3 y hy _ => hΩ x hx hx3 y hy) hrank Z hZS hZcard hwc

namespace N588T.Hyp3

variable {G : Type} [Group G] [Finite G] {S Z : Subgroup G}

theorem concl_of_core (hM3 : UCK.KMult3Ab) (hD : DichThree) (hIA : KFactInnerAction)
    (hWC : KFactWeakClosure) (h : Hyp3 G S Z) (hcore : CFSG.pPrimeCore 3 G = ⊥) :
    CFSG.Open.pRank 3 (normalClosure (Z : Set G)) = 1 := by
  by_cases hZn : Z.Normal
  · exact h.concl_of_normal hZn
  obtain ⟨J, hJ, hZJ⟩ := h.exists_component hcore hZn
  obtain ⟨hZleJ, hTc⟩ := h.le_and_isCyclic hM3 hD hIA hWC hcore hJ hZJ
  have hJn : J.Normal := by
    have hconj : ∀ g : G, J.map (MulAut.conj g).toMonoidHom = J := by
      intro g
      by_contra hne
      have hJ' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ
      have hcomm : ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hJ hJ').resolve_left (Ne.symm hne)
      have hJ'C : J.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hZgJ' : CFSG.conjugate Z g⁻¹ ≤ J.map (MulAut.conj g).toMonoidHom := by
        intro x hx
        rw [N588A.mem_conjugate_iff, inv_inv] at hx
        refine ⟨g⁻¹ * x * g, hZleJ hx, ?_⟩
        change g * (g⁻¹ * x * g) * g⁻¹ = x
        group
      have hZg : CFSG.conjugate Z g⁻¹ = Z := by
        apply h.conjugate_eq_of_le_normalizer
        exact (hZgJ'.trans hJ'C).trans
          ((Subgroup.centralizer_le hZleJ).trans (Subgroup.centralizer_le_normalizer _))
      apply hZJ
      have hZJ'' : Z ≤ J.map (MulAut.conj g).toMonoidHom := hZg ▸ hZgJ'
      exact hZJ''.trans hJ'C
    refine ⟨fun n hn g => ?_⟩
    rw [← hconj g]
    exact ⟨n, hn, rfl⟩
  refine h.concl_of_le ?_
  have hX : normalClosure (Z : Set G) ≤ J := Subgroup.normalClosure_le_normal hZleJ
  have hJr : CFSG.Open.pRank 3 J ≤ 1 := by
    have h1 := N588A.pRank_map_subtype (p := 3) (by norm_num) J (⊤ : Subgroup J)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [h1]
    exact (N588A.pRank_le_of_isSylowOf Nat.prime_three (h.isSylowOf_subgroupOf hJ.2) _).trans
      (N588A.pRank_le_one_of_isCyclic (by norm_num) hTc)
  exact (CFSG.SectionRank.pRank_mono (by norm_num) hX).trans hJr

end N588T.Hyp3

theorem k332ThreeAb_of_inputs (hM3 : UCK.KMult3Ab) (hD : DichThree) (hIA : KFactInnerAction)
    (hWC : KFactWeakClosure) : K332ThreeAb := by
  intro G _ _ hK S hS hΩ hrank Z hZS hZcard hwc
  have h : N588T.Hyp3 G S Z := ⟨hK, hS, hΩ, hrank, hZS, hZcard, hwc⟩
  have hq := h.quotient (CFSG.pPrimeCore 3 G) CFSG.pPrimeCore_coprime_card
  exact h.concl_of_quotient
    (hq.concl_of_core hM3 hD hIA hWC (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three))

end CFSG.LocalAnalysis.UniquenessCase.UCK

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem six25_of_K332Three (hK : UCK.K332Three) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (hr3 : m.r = 3) (h623 : m.C623) : m.C625 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hKM : CFSG.Open.IsKGroup ↥m.M := m.hS.kProper.isKGroup m.M m.M_ne_top
  set Z' : Subgroup ↥m.M := m.Z.subgroupOf m.M with hZ'
  have hZ'card : Nat.card Z' = m.r := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_M).toEquiv]
    exact m.card_Z
  have hZ'p : IsPGroup m.r Z' :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZ'card)
  have hrank : CFSG.Open.pRank m.r (⊤ : Subgroup ↥m.M) ≤ 3 := by
    have h1 := pRank_map_subtype_uc6 m.hr m.M (⊤ : Subgroup ↥m.M)
    have h2 : (⊤ : Subgroup ↥m.M).map m.M.subtype = m.M := by
      rw [← MonoidHom.range_eq_map]; exact Subgroup.range_subtype _
    rw [h2] at h1
    rw [← h1]
    exact pRank_le_three_of_not_mem_sigma m.hU m.S.maxLocal m.hr m.d.odd m.hrσ
  obtain ⟨S', hS'syl, hZS'⟩ := exists_isSylowOf_ge (p := m.r) (K := (⊤ : Subgroup ↥m.M))
    (Q := Z') (fun x _ => trivial) hZ'p
  have hS''p : IsPGroup m.r (S'.map m.M.subtype) := hS'syl.isPGroup.map _
  have hS''M : S'.map m.M.subtype ≤ m.M := Subgroup.map_subtype_le _
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isSylowOf m.d.sylow hS''M hS''p
  have hsix := m.hZ.sixteen h69
  have hS'comm : ∀ x ∈ S', x ^ m.r = 1 → ∀ y ∈ S', x * y = y * x := by
    intro x hx hxr y hy
    have hxR : k⁻¹ * (x : G) * k ∈ m.R := hk _ ⟨x, hx, rfl⟩
    have hxA : k⁻¹ * (x : G) * k ∈ m.Z ⊔ m.E := by
      refine hsix.2 _ hxR ?_
      have hx1 : (x : G) ^ m.r = 1 := by simpa using congrArg Subtype.val hxr
      have := conj_pow (a := k⁻¹) (b := (x : G)) (i := m.r)
      rw [inv_inv] at this
      rw [this, hx1]
      simp
    have hyR : k⁻¹ * (y : G) * k ∈ m.R := hk _ ⟨y, hy, rfl⟩
    have hc := hsix.1 _ hxA _ hyR
    apply Subtype.ext
    have h3 : k⁻¹ * ((x : G) * y) * k = k⁻¹ * ((y : G) * x) * k := by
      calc k⁻¹ * ((x : G) * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
        _ = (k⁻¹ * y * k) * (k⁻¹ * x * k) := hc
        _ = k⁻¹ * ((y : G) * x) * k := by group
    have h4 := congrArg (fun t => k * t * k⁻¹) h3
    simpa [mul_assoc] using h4
  have hS'rank : CFSG.Open.pRank m.r S' ≤ 3 :=
    le_trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono m.r m.hr (le_top : S' ≤ ⊤)) hrank
  have hS'wc : IsWeaklyClosedIn Z' S' := by
    intro g hg
    have hZk : CFSG.conjugate m.Z k ≤ m.R := by
      intro y hy
      have hz : k * y * k⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hy
      have hzS : (⟨k * y * k⁻¹, m.Z_le_M hz⟩ : ↥m.M) ∈ S' := hZS' hz
      have := hk _ ⟨_, hzS, rfl⟩
      simpa [mul_assoc] using this
    have hZgk : CFSG.conjugate m.Z ((g : G) * k) ≤ m.R := by
      intro y hy
      have hz : (g : G) * k * y * ((g : G) * k)⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hy
      have hwM : k * y * k⁻¹ ∈ m.M := by
        have e : k * y * k⁻¹ = (g : G)⁻¹ * ((g : G) * k * y * ((g : G) * k)⁻¹) * g := by group
        rw [e]
        exact m.M.mul_mem (m.M.mul_mem (m.M.inv_mem g.2) (m.Z_le_M hz)) g.2
      have hw' : (⟨k * y * k⁻¹, hwM⟩ : ↥m.M) ∈ CFSG.conjugate Z' g := by
        rw [mem_conjugate_iff_uc6]
        show (g : G) * (k * y * k⁻¹) * (g : G)⁻¹ ∈ m.Z
        have e : (g : G) * (k * y * k⁻¹) * (g : G)⁻¹ = (g : G) * k * y * ((g : G) * k)⁻¹ := by
          group
        rw [e]
        exact hz
      have := hk _ ⟨_, hg hw', rfl⟩
      simpa [mul_assoc] using this
    have hk1 := h623 k hZk
    have hk2 := h623 ((g : G) * k) hZgk
    have e1 : ∀ y : G, k * y * k⁻¹ ∈ m.Z ↔ y ∈ m.Z := fun y => by
      rw [← mem_conjugate_iff_uc6, hk1]
    have e2 : ∀ y : G, (g : G) * k * y * ((g : G) * k)⁻¹ ∈ m.Z ↔ y ∈ m.Z := fun y => by
      rw [← mem_conjugate_iff_uc6, hk2]
    ext x
    rw [mem_conjugate_iff_uc6]
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ m.Z ↔ (x : G) ∈ m.Z
    have h1 := e2 (k⁻¹ * (x : G) * k)
    have h2 := e1 (k⁻¹ * (x : G) * k)
    have e3 : (g : G) * k * (k⁻¹ * (x : G) * k) * ((g : G) * k)⁻¹ =
        (g : G) * (x : G) * (g : G)⁻¹ := by
      group
    have e4 : k * (k⁻¹ * (x : G) * k) * k⁻¹ = (x : G) := by group
    rw [e3] at h1
    rw [e4] at h2
    exact h1.trans h2.symm
  rw [hr3] at hS'syl hS'comm hS'rank hZ'card
  have h1 := hK ↥m.M hKM S' hS'syl hS'comm hS'rank Z' hZS' hZ'card hS'wc
  show CFSG.Open.pRank m.r m.K = 1
  rw [m.K_eq_map_normalClosure, pRank_map_subtype_uc6 m.hr m.M, hr3]
  exact h1

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
