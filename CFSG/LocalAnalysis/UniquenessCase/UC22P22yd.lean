module

import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22yd_mem_of_mk_mem (D : Data G) {K : Subgroup G} (hK : D.M ⊓ centralizer (D.U : Set G) ≤ K)
    {x : G} (hx : x ∈ D.M) (hmk : (QuotientGroup.mk ⟨x, hx⟩ : MBar D.M D.U) ∈ mbarImage D.M D.U K) :
    x ∈ K := by
  obtain ⟨y, hyK, hy⟩ := hmk
  have hyK' : (y : G) ∈ K := hyK
  have h1 : y⁻¹ * ⟨x, hx⟩ ∈ (kerAct D.M D.U).normalCore :=
    QuotientGroup.eq.1 hy
  have h2 : y⁻¹ * ⟨x, hx⟩ ∈ kerAct D.M D.U := Subgroup.normalCore_le _ h1
  have h3 : (y : G)⁻¹ * x ∈ centralizer (D.U : Set G) := Subgroup.mem_subgroupOf.1 h2
  have h4 : (y : G)⁻¹ * x ∈ K := hK ⟨D.M.mul_mem (D.M.inv_mem y.2) hx, h3⟩
  have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [e]
  exact K.mul_mem hyK' h4

theorem uc22p22yd_exists_lift (D : Data G) {r : ℕ} (hr : r.Prime) {Y : Subgroup (MBar D.M D.U)}
    (hYr : IsPGroup r ↥Y) (hYc : ¬ IsCyclic ↥Y) :
    ∃ R : Subgroup G, R ≤ preMbar D Y ∧ IsPGroup r ↥R ∧ ¬ IsCyclic ↥R := by
  haveI : Fact r.Prime := ⟨hr⟩
  set W : Subgroup ↥D.M := Y.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore) with hW
  set g : ↥W →* ↥Y := ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp W.subtype).codRestrict Y
    (fun w => w.2) with hg
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (kerAct D.M D.U).normalCore (y : MBar D.M D.U)
    have hxW : x ∈ W := by
      show QuotientGroup.mk' _ x ∈ Y
      rw [hx]
      exact y.2
    exact ⟨⟨x, hxW⟩, Subtype.ext hx⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow r ↥W))
  have hStop : ((S.mapSurjective hgs : Sylow r ↥Y) : Subgroup ↥Y) = ⊤ :=
    ((S.mapSurjective hgs).is_maximal' (IsPGroup.of_equiv hYr Subgroup.topEquiv.symm) le_top).symm
  have hSc : ¬ IsCyclic ↥(S : Subgroup ↥W) := by
    intro hS
    apply hYc
    have h1 : IsCyclic ↥((S : Subgroup ↥W).map g) := by
      haveI := hS
      exact isCyclic_of_surjective (g.subgroupMap (S : Subgroup ↥W)) (g.subgroupMap_surjective _)
    have h2 : (S : Subgroup ↥W).map g = ⊤ := hStop
    rw [h2] at h1
    exact isCyclic_of_surjective (Subgroup.topEquiv (G := ↥Y)).toMonoidHom
      (Subgroup.topEquiv (G := ↥Y)).surjective
  refine ⟨((S : Subgroup ↥W).map W.subtype).map D.M.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    exact ⟨(s : ↥D.M), s.2, rfl⟩
  · exact (S.isPGroup'.map _).map _
  · intro hc
    apply hSc
    have e := ((S : Subgroup ↥W).equivMapOfInjective W.subtype W.subtype_injective).trans
      (((S : Subgroup ↥W).map W.subtype).equivMapOfInjective D.M.subtype D.M.subtype_injective)
    exact isCyclic_of_injective e.toMonoidHom e.injective

theorem uc22p22yd_nb_injective (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) (hne : ∀ j, Nb j ≠ ⊥) : Function.Injective Nb := by
  intro j k hjk
  by_contra hne'
  apply hne j
  have h1 := hNb.1.2.2 j
  rw [eq_bot_iff] at h1 ⊢
  intro x hx
  refine h1 ⟨hx, ?_⟩
  have hxk : x ∈ Nb k := hjk ▸ hx
  exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem (fun h => hne' h.symm) hxk)

theorem uc22p22yd_factor_le (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U))
    (hNb : NbarSplit D Nb) {i k : Fin m} (hki : k ≠ i) :
    Nb k ≤ mbarImage D.M D.U (D.M ⊓ centralizer (proofEiHat D (preN D (Nb i)) : Set G)) := by
  have hle : Nb k ≤ mbarImage D.M D.U (proofN D) := by
    rw [← hNb.1.1]
    exact le_iSup Nb k
  rw [← P22x.mbarImage_preN D hle]
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ⟨y.2, ?_⟩, rfl⟩
  exact uc22p22xg_preN_le_centralizer D Ch h2 h3 h51 hH c m Nb hNb hki hy

theorem uc22p22yd_two_factors (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U))
    (hNb : NbarSplit D Nb) {i k l : Fin m} (hki : k ≠ i) (hli : l ≠ i) (hkl : k ≠ l) {r : ℕ}
    (hr : r.Prime) (hrk : r ∣ Nat.card (Nb k)) (hrl : r ∣ Nat.card (Nb l)) :
    ∃ X : Subgroup G, X ≤ D.M ∧ X ≤ normalizer (proofEiHat D (preN D (Nb i)) : Set G) ∧
      IsPGroup r ↥X ∧ ¬ IsCyclic ↥X := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' r hrk
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrl
  set A : Subgroup (MBar D.M D.U) := Subgroup.zpowers (a : MBar D.M D.U) with hA
  set B : Subgroup (MBar D.M D.U) := Subgroup.zpowers (b : MBar D.M D.U) with hB
  have hAk : A ≤ Nb k := Subgroup.zpowers_le.2 a.2
  have hBl : B ≤ Nb l := Subgroup.zpowers_le.2 b.2
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hNb.1.2.1 k l hkl x (hAk hx) y (hBl hy)
  have ha' : orderOf (a : MBar D.M D.U) = r := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : MBar D.M D.U) = r := by rw [Subgroup.orderOf_coe]; exact hb
  have hAel : IsElemAbelian r A := isElemAbelian_zpowers (by rw [← ha']; exact pow_orderOf_eq_one _)
  have hBel : IsElemAbelian r B := isElemAbelian_zpowers (by rw [← hb']; exact pow_orderOf_eq_one _)
  have hYel : IsElemAbelian r (A ⊔ B) := hAel.sup_of_commute hBel hcomm
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxA, hxB⟩
    have h1 := hNb.1.2.2 k
    rw [← h1]
    exact ⟨hAk hxA, Subgroup.mem_iSup_of_mem l (Subgroup.mem_iSup_of_mem (fun h => hkl h.symm) (hBl hxB))⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, hA, hB, Nat.card_zpowers, Nat.card_zpowers, ha', hb'] at hcard
  have hYc : ¬ IsCyclic ↥(A ⊔ B) :=
    CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_isElemAbelian hYel (by rw [hcard, sq])
  obtain ⟨R, hRY, hRp, hRc⟩ := uc22p22yd_exists_lift D hr hYel.isPGroup hYc
  refine ⟨R, hRY.trans (P22x.preMbar_le_M D _), ?_, hRp, hRc⟩
  intro x hx
  obtain ⟨hxM, hxY⟩ := (P22x.mem_preMbar D).1 (hRY hx)
  have hKk := uc22p22yd_factor_le D Ch h2 h3 h51 hH c m Nb hNb hki
  have hKl := uc22p22yd_factor_le D Ch h2 h3 h51 hH c m Nb hNb hli
  have hxK : x ∈ D.M ⊓ centralizer (proofEiHat D (preN D (Nb i)) : Set G) :=
    uc22p22yd_mem_of_mk_mem D (le_inf inf_le_left
      (uc22p22xg_cent_le_centralizer D (P22x.preN_le_M D (Nb i)))) hxM
      ((sup_le (hAk.trans hKk) (hBl.trans hKl)) hxY)
  exact Subgroup.centralizer_le_normalizer _ hxK.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
