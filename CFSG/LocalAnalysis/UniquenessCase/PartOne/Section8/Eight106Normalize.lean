module

public import CFSG.Open.Defs
import CFSG.HardMathSupport.Solomon.Proving.Tables112T0
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp
import CFSG.ClassicalInvolution.RouteD.GapsPerfect
import CFSG.Quasithin.Vol2.Ch10SecCGroup
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Native
import CFSG.ClassicalInvolution.Uniform.UTwinSolv
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC12Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[reducible] private def conjActMulAction (K : Subgroup G) : MulAction K (Subgroup G) where
  smul n H := H.map (MulAut.conj (n : G)).toMonoidHom
  one_smul H := by
    change H.map (MulAut.conj ((1 : K) : G)).toMonoidHom = H
    rw [show ((1 : K) : G) = 1 from rfl, map_one]
    exact Subgroup.map_id H
  mul_smul m n H := by
    change H.map (MulAut.conj ((m * n : K) : G)).toMonoidHom =
      (H.map (MulAut.conj (n : G)).toMonoidHom).map
        (MulAut.conj (m : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

attribute [local instance] conjActMulAction

private theorem commute_of_isComponentOf_ne {A B X : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A X) (hB : CFSG.Open.IsComponentOf B X) (hne : A ≠ B) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have mk : ∀ {D : Subgroup G}, CFSG.Open.IsComponentOf D X →
      CFSG.Open.IsComponentOf (D.subgroupOf X) ⊤ := by
    intro D hD
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.ClassicalInvolution.Uniform.isSubnormal_subgroupOf_top hD.2.1
    · exact (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hD.1).symm
          (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hD.2.2)))
  have hAc : CFSG.IsComponent (A.subgroupOf X) := (CFSG.isComponent_iff_open _).mpr (mk hA)
  have hBc : CFSG.IsComponent (B.subgroupOf X) := (CFSG.isComponent_iff_open _).mpr (mk hB)
  rcases CFSG.LocalCores.distinct_components_commute hAc hBc with heq | hbot
  · exfalso
    apply hne
    have h := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at h
  · exact CFSG.StandardType.SmallExcC12.commute_of_commutator_subgroupOf_eq_bot hA.1 hB.1 hbot

private theorem rank_bound_of_commuting_components
    (hrank : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → ∀ r : ℕ, r.Prime → r ≠ 2 →
      Open.pRank r (centralizer ({t} : Set G)) ≤ 3)
    {t : G} (ht : orderOf t = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {n : ℕ} {A : Fin n → Subgroup G} (hA : ∀ i, CFSG.Open.IsQuasisimple ↥(A i))
    (hrdvd : ∀ i, r ∣ Nat.card (A i))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a)
    (htc : ∀ i, ∀ a ∈ A i, t * a = a * t) :
    n ≤ Open.pRank r (centralizer ({t} : Set G)) := by
  classical
  have hxi : ∀ i, ∃ x : A i, orderOf x = r ∧ x ∉ Subgroup.center (A i) :=
    fun i => CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      (hA i) hr hr2 (hrdvd i)
  choose x hxord hxnc using hxi
  let xG : Fin n → G := fun i => (x i : G)
  have hxGmem : ∀ i, xG i ∈ A i := fun i => (x i).2
  have hxGpow : ∀ i, (xG i) ^ r = 1 := by
    intro i
    rw [← hxord i, ← Subgroup.coe_pow, pow_orderOf_eq_one]
    rfl
  have hxGnc : ∀ i, ∃ a ∈ A i, a * xG i ≠ xG i * a := by
    intro i
    by_contra hc
    push Not at hc
    apply hxnc i
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hc a a.2)
  obtain ⟨E, hEsub, hEea, hEcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20d_elemAbelian_of_commuting
      r n hr A xG hcomm hxGmem hxGpow hxGnc
  have hgen : Set.range xG ⊆ centralizer ({t} : Set G) := by
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact htc i (x i) (x i).2)
  have hclos : Subgroup.closure (Set.range xG) ≤ centralizer ({t} : Set G) :=
    (Subgroup.closure_le _).2 hgen
  exact CFSG.HardMathSupport.Solomon.Coordinator.le_pRank_of_elemAbelian
    hr.one_lt (hEsub.trans hclos) hEea hEcard

private theorem orbit_members_are_components {X K Y : Subgroup G} (hKX : K ≤ X)
    (hY : CFSG.Open.IsComponentOf Y X) :
    ∀ A ∈ MulAction.orbit K Y, CFSG.Open.IsComponentOf A X := by
  rintro A ⟨k, rfl⟩
  exact CFSG.Assembly.isComponentOf_iff_open.mp
    (CFSG.StandardType.ggIsComponentOf_conj
      (CFSG.Assembly.isComponentOf_iff_open.mpr hY) (hKX k.2))

private theorem orbit_index {X K Y : Subgroup G} (hKX : K ≤ X)
    (hY : CFSG.Open.IsComponentOf Y X) :
    ∃ (n : ℕ) (A : Fin n → Subgroup G),
      (∀ i, A i ∈ MulAction.orbit K Y) ∧
      (∀ i, CFSG.Open.IsComponentOf (A i) X) ∧
      (∀ i, A i ≠ Y) ∧
      (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) ∧
      Nat.card (MulAction.orbit K Y) = n + 1 := by
  classical
  let O : Set (Subgroup G) := MulAction.orbit K Y
  have hYinO : Y ∈ O := MulAction.mem_orbit_self Y
  have hOcomp : ∀ A ∈ O, CFSG.Open.IsComponentOf A X :=
    orbit_members_are_components hKX hY
  let S : Set (Subgroup G) := {A | A ∈ O ∧ A ≠ Y}
  have hSfin : S.Finite := Set.toFinite S
  let _ : Fintype S := Fintype.ofFinite S
  let n : ℕ := Fintype.card S
  let e : S ≃ Fin n := Fintype.equivFin S
  let A : Fin n → Subgroup G := fun i => (e.symm i).1
  have hAmem : ∀ i, A i ∈ S := fun i => (e.symm i).2
  have hAO : ∀ i, A i ∈ O := fun i => (hAmem i).1
  have hAcomp : ∀ i, CFSG.Open.IsComponentOf (A i) X :=
    fun i => hOcomp (A i) (hAO i)
  have hAne : ∀ i, A i ≠ Y := fun i => (hAmem i).2
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := by
    intro i j hij
    exact commute_of_isComponentOf_ne (hAcomp i) (hAcomp j) (by
      intro heq
      apply hij
      exact e.symm.injective (Subtype.ext heq))
  have hcard : Nat.card O = n + 1 := by
    have h1 : S.ncard = O.ncard - 1 := by
      rw [show S = O \ {Y} from by ext A; simp [S],
        Set.ncard_diff_singleton_of_mem hYinO]
    have h2 : O.ncard = Nat.card O := by
      let _ : Fintype O := Fintype.ofFinite O
      rw [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card O (Set.toFinite O),
        Set.Finite.card_toFinset (Set.toFinite O)]
    have h3 : S.ncard = n := by
      rw [Set.ncard_eq_toFinset_card S hSfin, Set.Finite.card_toFinset hSfin]
    have hOpos : 0 < Nat.card O :=
      Nat.card_pos_iff.mpr ⟨⟨Y, hYinO⟩, inferInstance⟩
    have hOpos' : 0 < O.ncard := by rwa [h2]
    have h4 : O.ncard = S.ncard + 1 := by
      rw [h1]
      exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hOpos')).symm
    rw [← h2, ← h3]
    exact h4
  exact ⟨n, A, hAO, hAcomp, hAne, hcomm, hcard⟩

private theorem orbit_rank_bound
    (hrank : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → ∀ r : ℕ, r.Prime → r ≠ 2 →
      Open.pRank r (centralizer ({t} : Set G)) ≤ 3)
    {X K Y : Subgroup G} (hXk : CFSG.Open.IsKGroup ↥X) (hKX : K ≤ X)
    (hY : CFSG.Open.IsComponentOf Y X) {n : ℕ} {A : Fin n → Subgroup G}
    (hAO : ∀ i, A i ∈ MulAction.orbit K Y)
    (hAcomp : ∀ i, CFSG.Open.IsComponentOf (A i) X)
    (hAne : ∀ i, A i ≠ Y)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) :
    n ≤ 3 := by
  obtain ⟨r, hr, hr2, hrdvdY⟩ :=
    CFSG.QuasithinUnique.Vol2Native.exists_odd_prime_dvd_card_of_quasisimple
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hY.2.2)
  obtain ⟨t, ht⟩ := CFSG.HardMathSupport.Solomon.Proving.tables112_T0_holds ↥Y hY.2.2
    (CFSG.HardMathSupport.Solomon.Coordinator.Generation228.isKGroup_of_le hXk hY.1)
  let tG : G := t
  have htG : orderOf tG = 2 := by
    change orderOf (t : G) = 2
    rw [Subgroup.orderOf_coe, ht]
  have hrdvd : ∀ i, r ∣ Nat.card (A i) := by
    intro i
    rcases hAO i with ⟨k, hk⟩
    have hcard : Nat.card (A i) = Nat.card Y := by
      rw [← hk]
      change Nat.card (Y.map (MulAut.conj (k : G)).toMonoidHom) = Nat.card Y
      rw [Subgroup.card_map_of_injective (MulAut.conj (k : G)).injective]
    rw [hcard]
    exact hrdvdY
  have htc : ∀ i, ∀ a ∈ A i, tG * a = a * tG := by
    intro i a ha
    exact commute_of_isComponentOf_ne hY (hAcomp i) (Ne.symm (hAne i)) t t.2 a ha
  have hb := rank_bound_of_commuting_components hrank htG hr hr2
    (fun i => (hAcomp i).2.2) hrdvd hcomm htc
  have ht_ne : tG ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  have ht2 : tG ^ 2 = 1 := by simpa [htG] using pow_orderOf_eq_one tG
  have hlt := hrank tG ht_ne ht2 r hr hr2
  omega

private theorem orbit_card_le_four
    (hrank : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → ∀ r : ℕ, r.Prime → r ≠ 2 →
      Open.pRank r (centralizer ({t} : Set G)) ≤ 3)
    {X K Y : Subgroup G} (hXk : CFSG.Open.IsKGroup ↥X) (hKX : K ≤ X)
    (hY : CFSG.Open.IsComponentOf Y X) :
    Nat.card (MulAction.orbit K Y) ≤ 4 := by
  obtain ⟨n, A, hAO, hAcomp, hAne, hcomm, hcard⟩ := orbit_index hKX hY
  have hn : n ≤ 3 := orbit_rank_bound hrank hXk hKX hY hAO hAcomp hAne hcomm
  omega

theorem le_normalizer_of_isComponentOf
    (hrank : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → ∀ r : ℕ, r.Prime → r ≠ 2 →
      pRank r (centralizer ({t} : Set G)) ≤ 3)
    {X K Y : Subgroup G} (hXk : CFSG.Open.IsKGroup ↥X) (hKX : K ≤ X) (hK : ⁅K, K⁆ = K)
    (hY : CFSG.Open.IsComponentOf Y X) :
    K ≤ normalizer (Y : Set G) := by
  let O : Set (Subgroup G) := MulAction.orbit K Y
  have hYinO : Y ∈ O := MulAction.mem_orbit_self Y
  have hperf : Group.IsPerfect K :=
    CFSG.Quasithin.Vol2.Ch10.SecC.isPerfect_of_commutator_eq hK
  have hOcard : Nat.card O ≤ 4 := orbit_card_le_four hrank hXk hKX hY
  have hact : ∀ k : K, ∀ A ∈ O, k • A = A := by
    intro k A hA
    have h := CFSG.ClassicalInvolution.RouteD.Gaps.perfect_smul_eq_of_card_le_four
      hOcard k ⟨A, hA⟩
    exact congrArg Subtype.val h
  intro k hk
  have h := hact ⟨k, hk⟩ Y hYinO
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Y.map (MulAut.conj k).toMonoidHom = Y at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
