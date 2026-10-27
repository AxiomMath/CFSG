module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts
public import CFSG.GroupTheory.PPrimePartConj
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CentOverO2Inner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusEightOutOrderHolds
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem exists_sylow_le_centralizer_of_isMulCommutative {M X E : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hXM : X ≤ M) (hMN : M ≤ normalizer (X : Set G))
    (hab : ∀ P : Sylow r (Bar2 X), IsMulCommutative (P : Subgroup (Bar2 X)))
    (hout : ¬ r ∣ (X ⊔ F08.CentOverO2 M X).relIndex M) (hEX : E ≤ X) (hEr : IsPGroup r E) :
    ∃ R, IsSylowOf r R M ∧ E ≤ R ⊓ centralizer (R : Set G) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let C : Subgroup G := F08.CentOverO2 M X
  let N : Subgroup G := X ⊔ C
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  have hCM : C ≤ M := fun x hx => (mem_centOverO2_iff.mp hx).1
  have hker : C.subgroupOf M = ρ.ker := by
    change (F08.CentOverO2 M X).subgroupOf M = ρ.ker
    rw [← Subgroup.comap_subtype, centOverO2_eq_ker_map hMN]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hNM : N ≤ M := sup_le hXM hCM
  haveI hCN : (C.subgroupOf M).Normal := by rw [hker]; infer_instance
  have hNle : M ≤ normalizer (N : Set G) :=
    (le_inf hMN (Subgroup.le_normalizer_of_normal_subgroupOf hCM)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup X C)
  have hNnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hNle
  haveI := hNnorm
  obtain ⟨R, hR, hER⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge (K := M) (Q := E)
      (hEX.trans hXM) hEr
  have hRN : R ≤ N :=
    le_of_isPGroup_of_not_dvd_relIndex hR.isPGroup hR.le hNM hNle (by simpa [N] using hout)
  have hRxsyl : IsSylowOf r (R ⊓ X) X := hR.inf_of_le_normalizer hXM hMN
  obtain ⟨Q, hQ⟩ := hRxsyl.exists_sylow_eq_subgroupOf
  let Qbar : Sylow r (Bar2 X) :=
    Q.mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      (QuotientGroup.mk'_surjective _)
  let P : Subgroup (Bar2 X) := Qbar
  have hPcoe : P = (Q : Subgroup ↥X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      (QuotientGroup.mk'_surjective _) Q
  have hPsyl : IsSylowOf r P ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, Qbar.isPGroup', by simpa using Qbar.not_dvd_index⟩
  have hPcomm : IsMulCommutative P := hab Qbar
  have hcentral : ∀ g ∈ R, ∀ e ∈ R ⊓ X, g * e = e * g := by
    intro g hg e he
    have hgM : g ∈ M := hR.le hg
    have hgN : g ∈ N := hRN hg
    have hgm : ((⟨g, hgM⟩ : ↥M) : G) ∈ X ⊔ F08.CentOverO2 M X := by
      simpa [C] using hgN
    obtain ⟨x, hxconj⟩ :=
      mem_inner_of_mem_sup_centOverO2 hXM hMN (m := ⟨g, hgM⟩) hgm
    have hconjpow : ∃ k, orderOf (ρ ⟨g, hgM⟩) = r ^ k := by
      obtain ⟨k, hk⟩ := hR.isPGroup.exists_card_eq
      have hcard : Nat.card (R.subgroupOf M) = r ^ k := by
        rw [← hk]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.le).toEquiv
      have hdvd : orderOf (ρ ⟨g, hgM⟩) ∣ r ^ k := by
        rw [← hcard]
        exact (orderOf_map_dvd ρ _).trans
          (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_subgroupOf.mpr hg))
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp hdvd
      exact ⟨j, hj⟩
    have hxpow : ∃ k, orderOf (MulAut.conj x) = r ^ k := by
      obtain ⟨k, hk⟩ := hconjpow
      exact ⟨k, by rwa [hxconj]⟩
    obtain ⟨y, hyord, hyconj0⟩ :=
      CFSG.GroupTheory.exists_isPGroup_zpowers_conj_eq (H := Bar2 X) (p := r) (x := x) hr hxpow
    have hyconj : MulAut.conj y = ρ ⟨g, hgM⟩ := hyconj0.trans hxconj
    have heX : e ∈ X := he.2
    have hPmap : P.map (ρ ⟨g, hgM⟩).toMonoidHom = P := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro p ⟨p', hp', rfl⟩
        rw [hPcoe] at hp' ⊢
        obtain ⟨x0, hx0Q, rfl⟩ := Subgroup.mem_map.mp hp'
        have hx0 : (x0 : G) ∈ R ⊓ X := by
          rw [hQ] at hx0Q; exact Subgroup.mem_subgroupOf.mp hx0Q
        have hconjmem : g * (x0 : G) * g⁻¹ ∈ R ⊓ X :=
          ⟨R.mul_mem (R.mul_mem hg hx0.1) (R.inv_mem hg),
            (Subgroup.mem_normalizer_iff.mp (hMN hgM) (x0 : G)).mp hx0.2⟩
        have heq : ρ ⟨g, hgM⟩ (QuotientGroup.mk x0) =
            QuotientGroup.mk (⟨g * (x0 : G) * g⁻¹, hconjmem.2⟩ : ↥X) := by
          rw [show ρ ⟨g, hgM⟩ = rhoL X ⟨g, hMN hgM⟩ from rfl, rhoL_mk]
          exact congrArg (QuotientGroup.mk (s := CFSG.pCore 2 ↥X))
            (Subtype.ext (rhoL_mk_coe X ⟨g, hMN hgM⟩ x0))
        change ρ ⟨g, hgM⟩ (QuotientGroup.mk x0) ∈
          Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Q : Subgroup ↥X)
        rw [heq]
        exact Subgroup.mem_map_of_mem _ (by rw [hQ]; exact Subgroup.mem_subgroupOf.mpr hconjmem)
      · rw [Subgroup.card_map_of_injective (K := P)
          (f := (ρ ⟨g, hgM⟩).toMonoidHom) (ρ ⟨g, hgM⟩).injective]
    have hyord' : IsPGroup r (Subgroup.zpowers y) := hyord
    have hynorm : y ∈ Subgroup.normalizer (P : Set (Bar2 X)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hyconj]
      exact hPmap
    have heP : (QuotientGroup.mk (⟨e, heX⟩ : ↥X)) ∈ P := by
      rw [hPcoe]
      refine Subgroup.mem_map_of_mem _ ?_
      rw [hQ]
      exact Subgroup.mem_subgroupOf.mpr he
    have hycomm := hPsyl.centralizes_of_mem_normalizer_of_isMulCommutative hPcomm hynorm hyord'
    have hyfix : MulAut.conj y (QuotientGroup.mk (⟨e, heX⟩ : ↥X)) =
        QuotientGroup.mk (⟨e, heX⟩ : ↥X) := by
      have hcomm := hycomm (QuotientGroup.mk (⟨e, heX⟩ : ↥X)) heP
      rw [MulAut.conj_apply, hcomm, mul_inv_cancel_right]
    have hfix : rhoL X ⟨g, hMN hgM⟩ (QuotientGroup.mk ⟨e, heX⟩) =
        QuotientGroup.mk ⟨e, heX⟩ := by
      change ρ ⟨g, hgM⟩ (QuotientGroup.mk ⟨e, heX⟩) = _
      rw [← hyconj]
      exact hyfix
    have hcomO2 : g * e * g⁻¹ * e⁻¹ ∈ pCoreOf 2 X :=
      (rhoL_fix_iff X ⟨g, hMN hgM⟩ ⟨e, heX⟩).mp hfix
    have hcomR : g * e * g⁻¹ * e⁻¹ ∈ R := by
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ hg he.1) (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ he.1)
    have hdvdR : orderOf (g * e * g⁻¹ * e⁻¹) ∣ Nat.card R :=
      Subgroup.orderOf_dvd_natCard R hcomR
    have hdvdO : orderOf (g * e * g⁻¹ * e⁻¹) ∣ Nat.card (pCoreOf 2 X) :=
      Subgroup.orderOf_dvd_natCard _ hcomO2
    have hcop : Nat.Coprime (Nat.card R) (Nat.card (pCoreOf 2 X)) := by
      obtain ⟨a, ha⟩ := hR.isPGroup.exists_card_eq
      obtain ⟨b, hb⟩ := (isPGroup_pCoreOf X).exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow a b (Nat.Prime.odd_of_ne_two hr hr2).coprime_two_right
    have hcom1 : g * e * g⁻¹ * e⁻¹ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdR hdvdO)
    have h2 : g * e * g⁻¹ = e := by
      have := congrArg (· * e) hcom1
      simpa [mul_assoc] using this
    have h3 : g * e = e * g := by
      have := congrArg (· * g) h2
      simpa [mul_assoc] using this
    exact h3
  refine ⟨R, hR, fun e he => Subgroup.mem_inf.mpr ⟨hER he, ?_⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  exact fun g hg => hcentral g hg e ⟨hER he, hEX he⟩

theorem relIndex_centOverO2_dvd_card_outer {M X : Subgroup G} (hXM : X ≤ M)
    (hMN : M ≤ normalizer (X : Set G)) :
    (X ⊔ F08.CentOverO2 M X).relIndex M ∣ Nat.card (Outer (Bar2 X)) := by
  classical
  let C : Subgroup G := F08.CentOverO2 M X
  let N : Subgroup G := X ⊔ C
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  let φ : ↥M →* Outer (Bar2 X) :=
    (QuotientGroup.mk' (Inn (Bar2 X))).comp ρ
  have hker : φ.ker = N.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun hm => mem_sup_centOverO2_of_mem_inner hXM hMN
        ((QuotientGroup.eq_one_iff (ρ m)).mp hm), fun hm =>
      (QuotientGroup.eq_one_iff (ρ m)).mpr (mem_inner_of_mem_sup_centOverO2 hXM hMN hm)⟩
  have hrel : N.relIndex M = Nat.card φ.range := by
    show (N.subgroupOf M).index = Nat.card φ.range
    rw [← Subgroup.index_ker φ, hker]
  change N.relIndex M ∣ Nat.card (Outer (Bar2 X))
  rw [hrel]
  exact Subgroup.card_subgroup_dvd_card φ.range

theorem not_dvd_card_outer_bar2 {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} {m n r : ℕ}
    (hmodel : CFSG.Blueprint.LieModel (BarInf L) t m 2 n)
    (ht : (t = .PSL ∧ (m = 3 ∨ m = 4)) ∨ (t = .PSU ∧ m = 6) ∨
      (t = .PSp ∧ m = 3) ∨ (t = .POmegaMinus ∧ m = 4))
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrn : ¬ r ∣ n) :
    ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
  classical
  haveI hperf : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have houter : Nat.card (Outer (BarInf L)) = Nat.card (Outer (Bar2 L ⧸ center (Bar2 L))) :=
    Nat.card_congr (equivalence e).toEquiv
  have hdvd : Nat.card (Outer (Bar2 L)) ∣ Nat.card (Outer (BarInf L)) := by
    rw [houter]
    have hcard : Nat.card (Outer (Bar2 L)) = Nat.card (centerQuotientOuterHom (Bar2 L)).range :=
      Nat.card_congr (MonoidHom.ofInjective (centerQuotient_outer_injective (Bar2 L))).toEquiv
    rw [hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hr2 : ¬ r ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hnot2n : ¬ r ∣ 2 * n := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h2 | hn
    exacts [hr2 h2, hrn hn]
  have finish (d : ℕ) (hb : Nat.card (Outer (BarInf L)) ∣ 2 * n * d) (hrd : ¬ r ∣ d) :
      ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp (h.trans (hdvd.trans hb)) with h2n | hd
    exacts [hnot2n h2n, hrd hd]
  have hclass : t ∈ CFSG.Blueprint.classicalTags := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [CFSG.Blueprint.classicalTags]
  rcases ht with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨rfl, hm⟩
  · have hSCM : StatedClassicalModel (BarInf L) .PSL m 2 n :=
      hmodel.statedClassicalModel hclass
    refine finish (CFSG.RankThree.OuterOrder.determinantParameter .PSL m (2 ^ n)) ?_ ?_
    · exact (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (T := BarInf L) (Or.inl rfl) (by omega) Nat.prime_two
        (CFSG.Blueprint.LieModel.admissible hmodel).2.1 hSCM).1
    · have hdm : CFSG.RankThree.OuterOrder.determinantParameter .PSL m (2 ^ n) ∣ m := by
        simpa [CFSG.RankThree.OuterOrder.determinantParameter] using
          Nat.gcd_dvd_left m (2 ^ n - 1)
      rcases hm with rfl | rfl <;> intro h <;>
        have := Nat.le_of_dvd (by norm_num) (h.trans hdm) <;> omega
  · have hSCM : StatedClassicalModel (BarInf L) .PSU m 2 n :=
      hmodel.statedClassicalModel hclass
    refine finish (CFSG.RankThree.OuterOrder.determinantParameter .PSU m (2 ^ n)) ?_ ?_
    · exact (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (T := BarInf L) (Or.inr rfl) (by omega) Nat.prime_two
        (CFSG.Blueprint.LieModel.admissible hmodel).2.1 hSCM).1
    · have hdm : CFSG.RankThree.OuterOrder.determinantParameter .PSU m (2 ^ n) ∣ m := by
        simpa [CFSG.RankThree.OuterOrder.determinantParameter] using
          Nat.gcd_dvd_left m (2 ^ n + 1)
      subst hm
      intro h
      have h6 : r ∣ 6 := h.trans hdm
      have hle := Nat.le_of_dvd (by norm_num) h6
      interval_cases r
      · norm_num at h6
      · norm_num at hr
  · subst hm
    exact fun h => hnot2n (h.trans (hdvd.trans (k_SpSixOutOrder_holds hmodel)))
  · subst hm
    exact fun h => hnot2n (h.trans (hdvd.trans
      (k_OmegaMinusEightOutOrder_holds (BarInf L) n hmodel)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
