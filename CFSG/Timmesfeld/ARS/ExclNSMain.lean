module

public import CFSG.Timmesfeld.ARS.ExclNSLowest
public import CFSG.Timmesfeld.ARS.ExclNSExceptional
public import CFSG.Timmesfeld.ARS.CaseEStep
public import CFSG.Timmesfeld.ARS.CaseEPointType

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg
open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
  {F : NSLFrameData (LeviBar R A A₀) (quotClass (levi R A A₀) (leviSet R A A₀))}

theorem quotMap_sup {X Y : Subgroup G} (hX : X ≤ levi R A A₀) (hY : Y ≤ levi R A A₀) :
    quotMap (levi R A A₀) (X ⊔ Y) = quotMap (levi R A A₀) X ⊔ quotMap (levi R A A₀) Y := by
  rw [quotMap, quotMap, quotMap, Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem LowMember.map_iSup_le_stabBar (hS : Sec13 R A A₀) {B : Subgroup G} (hB : LowMember F B)
    {i0 : Fin F.D.rank} (h0 : -Pi.single i0 1 ∈ lowSet F B)
    (hn : ∀ s, s ≠ i0 → F.Ψ (F.n s) ∈ stabBar R A A₀ B) :
    (⨆ i, F.H i).map F.Ψ ≤ stabBar R A A₀ B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hq := quotHyp hS
  rw [Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  have hα : (Pi.single i 1 : Fin F.D.rank → ℤ) ∈ F.D.roots :=
    (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin F.D.rank → ℤ) ∈ F.D.roots :=
    (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).neg_mem _ hα
  have hHle : (F.H i).map F.Ψ ≤ (F.D.rootGroup (Pi.single i 1)).map F.Ψ ⊔
      (F.D.rootGroup (-Pi.single i 1)).map F.Ψ := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono (F.hct.H_le i)
  have hneg : (F.D.rootGroup (-Pi.single i 1)).map F.Ψ ≤ stabBar R A A₀ B :=
    (Subgroup.map_mono (rootGroup_le_negUnipotent hα' (by rw [ht_neg, ht_single]; omega))).trans
      hB.le
  by_cases hi : i = i0
  · subst hi
    obtain ⟨Y, hY, hYq⟩ := h0.2
    have hαO : Pi.single i 1 ∈ memberRoots F := by
      have := neg_mem_memberRoots F h0.1
      rwa [neg_neg] at this
    obtain ⟨P, hP, hPq⟩ := exists_mem_leviSet_of_mem_quotClass (map_rootGroup_mem F hq.root hαO)
    have hopp : Opposite Y P := by
      refine opposite_of_quot hS hY.1 hP ?_
      rw [hYq, hPq]
      exact (opposite_map_rootGroup F hαO).symm
    have hYB : Commuting B Y := hY.2.1.2.2
    by_cases hc : Commuting P B
    · refine hHle.trans (sup_le ?_ hneg)
      rw [← hPq]
      exact (commuting_iff_quotMap_le_stabBar hS hB.mem hP).1 hc
    · have hs : Special R P B := (special_of_not_commuting_of_mem_leviSet hS.hyp hS.mem hB.mem hP
        fun h => hc h.symm).symm
      have hl : B ∈ lambdaSet R Y := mem_lambdaSet_comm hB.mem.1.1.1 hY.2
      have hψ : B ∈ psiSet R P := ⟨hB.mem.1.1.1, hs⟩
      rintro _ ⟨h, hh, rfl⟩
      have hmem : F.Ψ h ∈ quotMap (levi R A A₀) (Y ⊔ P) := by
        have := hHle ⟨h, hh, rfl⟩
        rw [← hPq, ← hYq, sup_comm, ← quotMap_sup (le_gen hY.1) (le_gen hP)] at this
        exact this
      obtain ⟨t, ht, hte⟩ := LeviQuot.exists_of_mem_quotMap hmem
      have htY : conjSub Y (t : G) = Y := by
        refine quot_injOn hS (Levi.conjSub_mem_leviSet_of_mem_levi hR hY.1 t.2) hY.1 ?_
        rw [LeviQuot.quotMap_conjSub Y t.2]
        have e : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) ⟨(t : G), t.2⟩ = F.Ψ h := hte
        rw [e, hYq, map_conjSub_eq,
          (RankOne.map_conj_eq_self_iff).2
            (iSup_le_normalizer_rootGroup F.hct hα' ((le_iSup F.H i) hh))]
      have hinv := Sec3.conjSub_sup_commutator_eq hR hiso hY.1.1.1 hP.1.1 hopp hl hψ ht
      have hBt : conjSub B (t : G) ≤ B := by
        intro y hy
        refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY.1.1.1 hP.1.1 hopp hl hψ ?_ ?_
        · rw [← hinv]
          exact Subgroup.map_mono le_sup_left hy
        · intro a ha
          have h1 := hYB.conjSub (t : G)
          rw [htY] at h1
          exact (h1 y hy a ha).symm
      have hBt' : conjSub B (t : G) = B := Subgroup.eq_of_le_of_card_ge hBt
        (Subgroup.card_map_of_injective (MulAut.conj (t : G)).injective).ge
      rw [← hte]
      exact (mk_mem_stabBar_iff hS hB.mem t).2 (conjSub_eq_self_iff.1 hBt')
  · refine hHle.trans (sup_le ?_ hneg)
    have e := actsAs_n F.hct i _ hα'
    rw [map_neg, weylAction_simple_single, neg_neg] at e
    rw [← e, ← map_conjSub_eq]
    have h1 := Subgroup.map_mono (f := (MulAut.conj (F.Ψ (F.n i))).toMonoidHom) hneg
    exact h1.trans (le_of_eq (conjSub_of_mem (hn i hi)))

theorem exists_member_normalizer_of_ht_le
    (h : ∃ w : (coxeterMatrix F.D.isFiniteType).Group, ∀ ε ∈ roots F.D.isFiniteType ∅,
      ht (weylAction F.D.isFiniteType w (Pi.single F.i₀ 1)) ≤ ht ε) :
    ∃ γ₁ ∈ memberRoots F,
      negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨_, ⟨w, rfl⟩, negUnipotent_le_normalizer_of_forall_ht_le F.hext F.hdiv
    (memberRoots_subset F ⟨w, rfl⟩) fun ε hε => hw ε ?_⟩
  have : ε ∈ roots F.D.isFiniteType F.D.divisible := hε
  rwa [F.hdiv] at this

theorem exists_member_normalizer_cartanC (hC : F.D.cartan = Symplectic.cartanC F.D.rank)
    (hn : 3 ≤ F.D.rank) (hi₀ : F.i₀.val + 1 < F.D.rank) :
    ∃ γ₁ ∈ memberRoots F,
      negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K) := by
  obtain ⟨w, w', h1, h2, hneg, hcone⟩ := exists_lowest_cartanC F.D.isFiniteType hC hn hi₀
  set γ₁ := weylAction F.D.isFiniteType w (Pi.single F.i₀ 1) with hγ₁def
  have hγ₁R : γ₁ ∈ F.D.roots := memberRoots_subset F ⟨w, rfl⟩
  refine ⟨γ₁, ⟨w, rfl⟩, negUnipotent_le_normalizer_rootGroup fun δ hδ hδ0 hne => ?_⟩
  by_cases hδα : δ = -Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1
  · rw [hδα]
    set i : Fin F.D.rank := ⟨F.D.rank - 2, by omega⟩
    set j : Fin F.D.rank := ⟨F.D.rank - 1, by omega⟩
    have hij : F.D.cartan i j = -2 := by
      rw [hC]
      simp only [Symplectic.cartanC, Matrix.of_apply, i, j, Fin.mk.injEq]
      split_ifs <;> omega
    have hα : (Pi.single i 1 : Fin F.D.rank → ℤ) ∈ F.D.roots :=
      (RootSystem.ofCartan F.D.isFiniteType F.D.divisible).single_mem i
    have hsum : (Pi.single i 1 + Pi.single j 1 : Fin F.D.rank → ℤ) ∈ F.D.roots := by
      have e : (Pi.single i 1 + Pi.single j 1 : Fin F.D.rank → ℤ) =
          weylAction F.D.isFiniteType w'⁻¹ (-Pi.single (⟨0, by omega⟩ : Fin F.D.rank) 1) := by
        rw [← h2, weylAction_inv_apply_apply]
      rw [e]
      exact weylAction_mem_roots _ _ ((RootSystem.ofCartan F.D.isFiniteType
        F.D.divisible).neg_mem _ ((RootSystem.ofCartan F.D.isFiniteType
          F.D.divisible).single_mem _))
    have hc := (F.comm hC i j hij).conjSub (nrep F.hct w')
    have e1 : conjSub (F.D.rootGroup (Pi.single i 1)) (nrep F.hct w') =
        F.D.rootGroup (weylAction F.D.isFiniteType w' (Pi.single i 1)) :=
      actsAs_nrep F.hct w' _ hα
    have e2 : conjSub (F.D.rootGroup (Pi.single i 1 + Pi.single j 1)) (nrep F.hct w') =
        F.D.rootGroup (weylAction F.D.isFiniteType w' (Pi.single i 1 + Pi.single j 1)) :=
      actsAs_nrep F.hct w' _ hsum
    rw [e1, e2, h1, h2] at hc
    exact hc
  · refine commuting_of_forall_notMem_openCone F.hext hγ₁R hδ
      (linIndepPair_of_ht_neg F.hdiv hγ₁R hneg hδ hδ0 (Ne.symm hne)) ?_
    rintro ε hε ⟨a, b, ha, hb, he⟩
    have hε' : ε ∈ roots F.D.isFiniteType ∅ := by
      have : ε ∈ roots F.D.isFiniteType F.D.divisible := hε
      rwa [F.hdiv] at this
    exact hδα (hcone δ hδ0 ε hε' a b ha hb he)

@[expose] def EpsCoords.ofEq {n : ℕ} {C C' : Matrix (Fin n) (Fin n) ℤ} (h : C = C')
    (P : EpsCoords C') : EpsCoords C :=
  h ▸ P

theorem LowMember.reflection_mem (hS : Sec13 R A A₀) {B : Subgroup G} (hB : LowMember F B)
    {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    (t : Fin F.D.rank) (ht : -Pi.single t 1 ∉ lowSet F B) {β : Fin F.D.rank → ℤ}
    (hβ : β ∈ lowSet F B) : reflection F.D.cartan t β ∈ lowSet F B := by
  have := LowMember.weylAction_mem hS hB hγ₁ hγ₁U ht hβ
  rwa [weylAction_simple] at this

theorem false_of_epsCoords (hS : Sec13 R A A₀) (hpt : PointTypeInput) {B : Subgroup G}
    (hB : LowMember F B) {γ₁ : Fin F.D.rank → ℤ} (hγ₁ : γ₁ ∈ memberRoots F)
    (hγ₁U : negUnipotent F.D ≤ Subgroup.normalizer (F.D.rootGroup γ₁ : Set F.K))
    (P : EpsCoords F.D.cartan)
    (hcase : F.D.cartan = Spin.cartanB F.D.rank ∨ F.D.cartan = Symplectic.cartanC F.D.rank)
    (hn : 3 ≤ F.D.rank) (hi₀ : F.i₀.val + 1 < F.D.rank) : False := by
  have hnorm : ∀ β ∈ lowSet F B, P.invForm.Q β β = 2 := fun β hβ =>
    (P.invForm.memberRoots_norm hβ.1).trans (P.invForm_single_of_lt hi₀)
  have hM : ∀ i, P.invForm.Q (Pi.single i 1) (Pi.single i 1) ≤
      2 * P.invForm.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
    intro i
    rw [P.invForm_single_of_lt hi₀]
    linarith [P.invForm_single_le i]
  have hzero : ∀ s, -Pi.single s 1 ∈ lowSet F B → s.val = 0 := fun s hs =>
    val_eq_zero_of_neg_single_mem P hnorm (LowMember.reflection_mem hS hB hγ₁ hγ₁U)
      (fun β hβ β' hβ' => LowMember.form_nonneg hS hB P.invForm hM hβ hβ') hs
  obtain ⟨s, hs⟩ := LowMember.exists_neg_single_mem hS hB hγ₁ hγ₁U
  have hs0 := hzero s hs
  have hns : ∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar R A A₀ B := fun s' hs' =>
    LowMember.mem_stabBar_n hS hB hγ₁ hγ₁U fun h => hs' (hzero s' h)
  have htorus := LowMember.map_iSup_le_stabBar hS hB hs fun s' hs' =>
    hns s' fun h => hs' (Fin.ext (h.trans hs0.symm))
  exact hpt G R A A₀ hS F B hcase hn hB htorus hns

theorem false_of_frame (hS : Sec13 R A A₀) (hpt : PointTypeInput)
    (F : NSLFrameData (LeviBar R A A₀) (quotClass (levi R A A₀) (leviSet R A A₀))) : False := by
  obtain ⟨B, hB⟩ := exists_lowMember F hS
  rcases NSLType.elim F.type with ⟨hn, hi₀, hC⟩ | ⟨hn, hi₀, hC⟩ | ⟨hr, hi₀, hC⟩ | ⟨hr, hi₀, hC⟩
  · obtain ⟨γ₁, hγ₁, hγ₁U⟩ := exists_member_normalizer_cartanC hC hn hi₀
    exact false_of_epsCoords hS hpt hB hγ₁ hγ₁U (EpsCoords.ofEq hC (epsC _)) (Or.inr hC) hn hi₀
  · obtain ⟨γ₁, hγ₁, hγ₁U⟩ :=
      exists_member_normalizer_of_ht_le (exists_ht_le_cartanB F.D.isFiniteType hC (by omega) hi₀)
    exact false_of_epsCoords hS hpt hB hγ₁ hγ₁U (EpsCoords.ofEq hC (epsB _)) (Or.inl hC) hn hi₀
  · obtain ⟨γ₁, hγ₁, hγ₁U⟩ :=
      exists_member_normalizer_of_ht_le (exists_ht_le_g2 F.D.isFiniteType hr hC hi₀)
    set q : Fin F.D.rank → ℤ := fun i => if i.val = 0 then 3 else 1 with hqdef
    have hq : ∀ k, 0 < q k := fun k => by simp only [hqdef]; split_ifs <;> norm_num
    have key : ∀ a < 2, ∀ b < 2,
        (if a = 0 then (3 : ℤ) else 1) * g2e a b = (if b = 0 then 3 else 1) * g2e b a := by
      decide
    have hsymm : ∀ i j, q i * F.D.cartan i j = q j * F.D.cartan j i := fun i j => by
      rw [hC, hC]
      exact key _ (hr ▸ i.isLt) _ (hr ▸ j.isLt)
    set Q := InvForm.ofSymmetrizer F.D.isFiniteType q hq hsymm
    have hM : ∀ i, Q.Q (Pi.single i 1) (Pi.single i 1) ≤
        2 * Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
      intro i
      change symForm q _ _ _ ≤ 2 * symForm q _ _ _
      rw [symForm_single_single F.D.isFiniteType hsymm,
        symForm_single_single F.D.isFiniteType hsymm]
      simp only [hqdef, hi₀, ite_true]
      split_ifs <;> norm_num
    exact false_of_g2 hr hC hi₀ (q := q) (fun _ => rfl)
      (fun β hβ => Q.memberRoots_norm hβ.1) (LowMember.exists_neg_single_mem hS hB hγ₁ hγ₁U)
      (LowMember.reflection_mem hS hB hγ₁ hγ₁U)
      (fun β hβ β' hβ' => LowMember.form_nonneg hS hB Q hM hβ hβ')
  · obtain ⟨γ₁, hγ₁, hγ₁U⟩ :=
      exists_member_normalizer_of_ht_le (exists_ht_le_f4 F.D.isFiniteType hr hC hi₀)
    set q : Fin F.D.rank → ℤ := fun i => if i.val < 2 then 2 else 1 with hqdef
    have hq : ∀ k, 0 < q k := fun k => by simp only [hqdef]; split_ifs <;> norm_num
    have key : ∀ a < 4, ∀ b < 4,
        (if a < 2 then (2 : ℤ) else 1) * f4e a b = (if b < 2 then 2 else 1) * f4e b a := by
      decide
    have hsymm : ∀ i j, q i * F.D.cartan i j = q j * F.D.cartan j i := fun i j => by
      rw [hC, hC]
      exact key _ (hr ▸ i.isLt) _ (hr ▸ j.isLt)
    set Q := InvForm.ofSymmetrizer F.D.isFiniteType q hq hsymm
    have hM : ∀ i, Q.Q (Pi.single i 1) (Pi.single i 1) ≤
        2 * Q.Q (Pi.single F.i₀ 1) (Pi.single F.i₀ 1) := by
      intro i
      change symForm q _ _ _ ≤ 2 * symForm q _ _ _
      rw [symForm_single_single F.D.isFiniteType hsymm,
        symForm_single_single F.D.isFiniteType hsymm]
      simp only [hqdef, hi₀, ite_true]
      split_ifs <;> norm_num
    exact false_of_f4 hr hC hi₀ (q := q) (fun _ => rfl)
      (fun β hβ => Q.memberRoots_norm hβ.1) (LowMember.exists_neg_single_mem hS hB hγ₁ hγ₁U)
      (LowMember.reflection_mem hS hB hγ₁ hγ₁U)
      (fun β hβ β' hβ' => LowMember.form_nonneg hS hB Q hM hβ hβ')

end CFSG.Timmesfeld.ARS.ExclNS

namespace CFSG.Timmesfeld.ARS

theorem ExclNS.caseENonSimplyLacedInput_of_pointType (hpt : ExclNS.PointTypeInput) :
    CaseENonSimplyLacedInput := by
  rintro G _ R h - A hA hcoat hAne hmax A₀ hA₀ h1 hnd ⟨-, hdata⟩
  have hS := Sec13.of_caseE h hA hcoat hAne hmax hA₀ h1 hnd
  rcases hdata with hSL | hF
  · exact ExclNS.not_sigmaEqLambda_quot hS hSL
  · exact Nonempty.elim hF fun F => ExclNS.false_of_frame hS hpt F

theorem ExclNS.caseENonSimplyLacedInput : CaseENonSimplyLacedInput :=
  ExclNS.caseENonSimplyLacedInput_of_pointType ExclNS.pointTypeInput

end CFSG.Timmesfeld.ARS
