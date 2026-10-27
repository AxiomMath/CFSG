module

public import CFSG.Timmesfeld.ARS.CaseELevel
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseESpecial

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {G : Type} [Group G] {R : Set (Subgroup G)} {K : Type*} [Group K] {A A₀ : Subgroup G}
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

private theorem conjSub_conjSub_inv_aux (X : Subgroup G) (g : G) :
    conjSub (conjSub X g) g⁻¹ = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

private theorem commuting_conjSub_iff {X Y : Subgroup G} (g : G) :
    Commuting (conjSub X g) (conjSub Y g) ↔ Commuting X Y := by
  refine ⟨fun h => ?_, fun h => h.conjSub g⟩
  have h1 := h.conjSub g⁻¹
  rwa [conjSub_conjSub_inv_aux, conjSub_conjSub_inv_aux] at h1


theorem exists_caseENode_highest (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : LeviFrame R A A₀ D n H Ψ)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) {j : Fin D.rank}
    (hj : ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j) :
    ∃ (w₀ : (coxeterMatrix D.isFiniteType).Group) (σ : Fin D.rank → Fin D.rank),
      (∀ i, (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w₀ i) ∧
      (∀ k, weylAction D.isFiniteType w₀ (Pi.single k 1) = -Pi.single (σ k) 1) ∧
      Function.Injective σ ∧ σ j = j ∧
      conjSub E (Ψ (nrep hF.hct w₀))⁻¹ ∈ lambdaStar R A A₀ ∧
      Commuting (conjSub E (Ψ (nrep hF.hct w₀))⁻¹) ((posUnipotent D).map Ψ) ∧
      (⨆ i, H i).map Ψ ≤
        Subgroup.normalizer ((conjSub E (Ψ (nrep hF.hct w₀))⁻¹ : Subgroup G) : Set G) ∧
      Special R E (conjSub E (Ψ (nrep hF.hct w₀))⁻¹) ∧
      ⁅E, conjSub E (Ψ (nrep hF.hct w₀))⁻¹⁆ = A ∧
      (∀ k, Commuting (conjSub E (Ψ (nrep hF.hct w₀))⁻¹)
        ((D.rootGroup (-Pi.single k 1)).map Ψ) ↔ k ≠ j) ∧
      conjSub E (Ψ (nrep hF.hct w₀))⁻¹ ∈ lambdaSet R ((D.rootGroup (Pi.single j 1)).map Ψ) ∧
      CaseENode R A A₀ (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
        (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ) E ⁅A₀, conjSub E (Ψ (nrep hF.hct w₀))⁻¹⁆
        j := by
  classical
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  set P : Fin D.rank → Subgroup G := fun k => (D.rootGroup (Pi.single k 1)).map Ψ with hPdef
  set Q : Fin D.rank → Subgroup G := fun k => (D.rootGroup (-Pi.single k 1)).map Ψ with hQdef
  have hk : ∀ k, (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem
  have hPl : ∀ k, P k ∈ leviSet R A A₀ := fun k => hF.mem _ (hk k)
  have hQl : ∀ k, Q k ∈ leviSet R A A₀ := fun k => hF.mem _ (Φ.neg_mem _ (hk k))
  have hQU : ∀ k, Q k ≤ (negUnipotent D).map Ψ := fun k =>
    map_rootGroup_le_map_negUnipotent (Φ.neg_mem _ (hk k)) (by rw [ht_neg, ht_single]; omega)
  have hER : E ∈ R := hE.1.1.1
  have hA₀R : A₀ ∈ R := hA₀.1
  have := finite_group D.isFiniteType
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w => cs.length w
  have hdesc : ∀ i, cs.IsRightDescent w₀ i := fun i => by_contra fun hi => by
    have h1 := cs.not_isRightDescent_iff.mp hi
    have := hw₀ (w₀ * cs.simple i)
    omega
  choose σ hσ using exists_weylAction_eq_neg_single D.isFiniteType hpd hw₀
  have hσinj : Function.Injective σ := fun a b e => by
    have h1 : weylAction D.isFiniteType w₀ (Pi.single a 1) =
        weylAction D.isFiniteType w₀ (Pi.single b 1) := by rw [hσ a, hσ b, e]
    have h2 := congrFun (weylAction_apply_injective D.isFiniteType w₀ h1) a
    by_contra hab
    simp [Pi.single_eq_of_ne hab] at h2
  have hnat : ∀ x ∈ weylN n H, ∀ j,
      Commuting (conjSub E (Ψ x)) ((D.rootGroup (-Pi.single j 1)).map Ψ) →
      ¬ Commuting (conjSub E (Ψ x)) ((D.rootGroup (Pi.single j 1)).map Ψ) →
      conjSub E (Ψ x) ∈ lambdaSet R ((D.rootGroup (-Pi.single j 1)).map Ψ) :=
    fun x hx j _ h2 =>
      mem_lambdaSet_of_mem_weylN h hA hAne hmax hA₀ hF.toCompFrame hpd hE hEU hX hadj hx j h2
  obtain ⟨hC, hCU, hCT, hsEC, hECA⟩ :=
    highest_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU hnat hdesc
  set n₀ := nrep hF.hct w₀
  set C := conjSub E (Ψ n₀)⁻¹ with hCdef
  have hact := actsAs_nrep hF.hct w₀
  have hCR : C ∈ R := hC.1.1.1
  have hCE : conjSub C (Ψ n₀) = E := by
    rw [hCdef, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hQσ : ∀ k, conjSub (Q k) (Ψ n₀) = P (σ k) := fun k => by
    rw [hQdef, map_conjSub_eq, hact _ (Φ.neg_mem _ (hk k)), map_neg, hσ k, neg_neg]
  have hCQ : ∀ k, Commuting C (Q k) ↔ σ k ≠ j := fun k => by
    rw [← commuting_conjSub_iff (Ψ n₀), hCE, hQσ k, ne_eq, ← hj (σ k), not_not]
  have hCP : ∀ k, Commuting C (P k) := fun k => hCU.mono le_rfl
    (Subgroup.map_mono (rootGroup_le_posUnipotent (hk k) (ht_single_pos k)))
  obtain ⟨hF', hFC, hAFC, hFlevi⟩ := CaseD4.commutator_props h hA hA₀ hC
  set F := ⁅A₀, C⁆ with hFdef
  have hFR : F ∈ R := hF'.1.1.1
  have hEF : Opposite E F := CaseD4.opposite_of_extremal hR hiso hA hCR hER hFR hC.1.1.2.2
    hE.1.1.2.2.symm hsEC hECA hFC hF'.2.2 hAFC
  have hFP : ∀ k, Commuting F (P k) := fun k => (hFlevi _ (hPl k) (hCP k).symm).symm
  have hEPj : ¬ Commuting E (P j) := (hj j).2 rfl
  have hsEP : Special R E (P j) := special_of_not_commuting_of_mem_leviSet h hA hE (hPl j) hEPj
  have hEQl : E ∈ lambdaSet R (Q j) :=
    mem_lambdaSet_of_commuting_negUnipotent h hA hAne hmax hA₀ hF.toCompFrame hE hEU j hEPj
  have hEψ : E ∈ psiSet R (P j) := ⟨hER, hsEP.symm⟩
  have hQPo : Opposite (Q j) (P j) := (hF.opp j).symm
  have hPjR : P j ∈ R := (hPl j).1.1
  have hQjR : Q j ∈ R := (hQl j).1.1
  have hFQj : ¬ Commuting F (Q j) := by
    intro hFQ
    have hDR : ⁅P j, E⁆ ∈ R := hsEP.symm.1
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
    obtain ⟨g, hg, hgd⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hQjR hPjR hQPo hEQl hEψ
      (Subgroup.mem_sup_left he) he1 (Subgroup.mem_sup_right hd) hd1
    have hEg : conjSub E g = ⁅P j, E⁆ := Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hER g) hDR
      (hgd ▸ conj_mem_conjSub g he) hd hd1
    have hFg : conjSub F g = F := conjSub_of_forall_commute fun f hf =>
      ((hFQ.sup_right (hFP j)) f hf g hg).symm
    have hDF : Opposite ⁅P j, E⁆ F := by
      have h1 := Sec3.opposite_conjSub hEF g
      rwa [hEg, hFg] at h1
    have hψ := Sec3.commutator_mem_psiSet_of_commuting hR hiso hFR hER hEF.symm
      ⟨hPjR, hsEP⟩ (hFP j)
    rw [Subgroup.commutator_comm] at hψ
    exact Special.not_opposite hR hFR hψ.2 hDF.symm
  have hσj : σ j = j := by
    by_contra hne
    exact hFQj (hFlevi _ (hQl j) ((hCQ j).2 hne).symm).symm
  have hFQ : ∀ k, k ≠ j → Commuting F (Q k) := fun k hkj =>
    (hFlevi _ (hQl k) ((hCQ k).2 fun e => hkj (hσinj (e.trans hσj.symm))).symm).symm
  have hw₀j : weylAction D.isFiniteType w₀⁻¹ (-Pi.single j 1) = Pi.single j 1 := by
    have h1 : weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single j 1 := by
      rw [hσ j, hσj]
    rw [← h1, weylAction_inv_apply_apply]
  have hCPl : C ∈ lambdaSet R (P j) := by
    have h1 : C ∈ conjSet (lambdaSet R (Q j)) (Ψ n₀)⁻¹ := conjSub_mem_conjSet hEQl _
    rw [conjSet_lambdaSet hR] at h1
    have h2 : conjSub (Q j) (Ψ n₀)⁻¹ = P j := by
      rw [hQdef, ← map_inv, map_conjSub_eq, hact.inv _ (Φ.neg_mem _ (hk j)), hw₀j]
    rwa [h2] at h1
  have hFPl : P j ∈ lambdaSet R F := by
    have hA₀N : A₀ ≤ Subgroup.normalizer ((M R (P j) : Subgroup G) : Set G) :=
      QD.le_normalizer_M hR hPjR ⟨hA₀R, (hPl j).2.2.2.symm⟩
    have hle : F ≤ M R (P j) := Linear.commutator_le_of_le_normalizer hA₀N (QD.le_M hCPl)
    have hne : F ≠ P j := fun e => hF'.2.2.not_commuting hR (by rw [e]; exact (hPl j).1.2.2)
    exact mem_lambdaSet_comm hPjR (mem_lambdaSet_of_le_M_of_hyp h hPjR hFR hle hne)
  have hinvE : ∀ x ∈ Q j ⊔ P j, conjSub (E ⊔ ⁅P j, E⁆) x = E ⊔ ⁅P j, E⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hQjR hPjR hQPo hEQl hEψ hx
  have hfixE : ∀ m ∈ E ⊔ ⁅P j, E⁆, (∀ y ∈ Q j, Commute y m) → m ∈ E := fun m hm hmQ =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hQjR hPjR hQPo hEQl hEψ hm hmQ
  have hD : ⁅E, P j⁆ ∈ lambdaStar R A A₀ := (commutator_mem_lambdaStar h hA hAne hA₀ hE (hPl j)
    hsEP).1
  have hDR : ⁅P j, E⁆ ∈ R := hsEP.symm.1
  have hDE : ⁅P j, E⁆ ≠ E := by
    have := hsEP.ne_commutator hR
    rw [Subgroup.commutator_comm E (P j)] at this
    exact this.symm
  have hsQD : Special R (Q j) ⁅P j, E⁆ := by
    have hnc : ¬ Commuting (Q j) ⁅P j, E⁆ := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (hR.card_eq hER hDR).le)
      exact hfixE d (Subgroup.mem_sup_right hd) fun y hy => hc y hy d hd
    have hne : Q j ≠ ⁅P j, E⁆ := fun e => hnc (by rw [← e]; exact hR.commuting_self hQjR)
    rcases hR.rel _ hQjR _ hDR hne with hc | ho | hs
    · exact absurd hc hnc
    · rw [Subgroup.commutator_comm] at ho
      exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hD (hQl j))
    · exact hs
  have hQN : Q j ≤ Subgroup.normalizer ((E ⊔ ⁅P j, E⁆ : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hinvE y (Subgroup.mem_sup_left hy))
  have h3 : ⁅Q j, ⁅P j, E⁆⁆ = E := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hER hsQD.1).le
    exact hfixE x (Linear.commutator_le_of_le_normalizer hQN le_sup_right hx) fun y hy =>
      (hsQD.2.1 x hx y hy).symm
  have hPψ : P j ∈ psiSet R E := ⟨hPjR, hsEP⟩
  have hinvP : ∀ x ∈ F ⊔ E, conjSub (P j ⊔ ⁅E, P j⁆) x = P j ⊔ ⁅E, P j⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hFR hER hEF.symm hFPl hPψ hx
  have hfixP : ∀ m ∈ P j ⊔ ⁅E, P j⁆, (∀ a ∈ F, Commute a m) → m ∈ P j := fun m hm hmF =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hFR hER hEF.symm hFPl hPψ hm hmF
  have hFN : F ≤ Subgroup.normalizer ((P j ⊔ ⁅E, P j⁆ : Subgroup G) : Set G) := fun f hf =>
    conjSub_eq_self_iff.1 (hinvP f (Subgroup.mem_sup_left hf))
  have hDR' : ⁅E, P j⁆ ∈ R := hsEP.1
  have hsDF : Special R ⁅E, P j⁆ F := by
    have hnc : ¬ Commuting ⁅E, P j⁆ F := by
      intro hc
      have hDP : ⁅E, P j⁆ = P j := Subgroup.eq_of_le_of_card_ge (fun d hd =>
        hfixP d (Subgroup.mem_sup_right hd) fun f hf => (hc d hd f hf).symm)
        (hR.card_eq hPjR hDR').le
      exact hD.2.2.not_commuting hR (by rw [hDP]; exact (hPl j).2.2.2)
    have hne : ⁅E, P j⁆ ≠ F := fun e => hnc (by rw [← e]; exact hR.commuting_self hDR')
    rcases hR.rel _ hDR' _ hFR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd hsEP.2.2 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR' ho hFPl)
    · exact hs
  have h5 : ⁅⁅E, P j⁆, F⁆ = P j := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hPjR hsDF.1).le
    exact hfixP x (commutator_le_of_le_normalizer le_sup_right hFN hx) fun f hf =>
      (hsDF.2.2 x hx f hf).symm
  have hsFQ : Special R F (Q j) := by
    have hne : F ≠ Q j := fun e => hFQj (by rw [e]; exact hR.commuting_self hQjR)
    rcases hR.rel _ hFR _ hQjR hne with hc | ho | hs
    · exact absurd hc hFQj
    · have hQl' : Q j ∈ leviSet R A₀ A := by
        rw [show leviSet R A₀ A = leviSet R A A₀ by simp only [leviSet, Set.inter_comm]]
        exact hQl j
      exact absurd ho.symm (CaseD4.not_opposite_of_mem_leviSet hR hA₀R hF' hQl')
    · exact hs
  have hCQ' : ∀ k, Commuting C (Q k) ↔ k ≠ j := fun k => by
    rw [hCQ k]
    exact ⟨fun h1 e => h1 (e ▸ hσj), fun h1 e => h1 (hσinj (e.trans hσj.symm))⟩
  refine ⟨w₀, σ, hdesc, hσ, hσinj, hσj, hC, hCU, hCT, hsEC, hECA, hCQ', hCPl,
    ⟨hE, hF', hEF, fun k hkj => ?_, ?_⟩⟩
  · exact ⟨by by_contra hc; exact hkj ((hj k).1 hc), hEU.mono le_rfl (hQU k), hFP k, hFQ k hkj⟩
  · refine ⟨hsEP, hFP j, ?_, hEU.mono le_rfl (hQU j), ?_, hsFQ⟩
    · rw [Subgroup.commutator_comm F]
      exact h5
    · rw [Subgroup.commutator_comm E (P j), Subgroup.commutator_comm _ (Q j)]
      exact h3

theorem exists_caseENode (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hF : LeviFrame R A A₀ D n H Ψ) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) {j : Fin D.rank}
    (hj : ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j) :
    ∃ F, CaseENode R A A₀ (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ) E F j := by
  obtain ⟨w₀, σ, -, -, -, -, -, -, -, -, -, -, -, hN⟩ :=
    exists_caseENode_highest h hA hAne hmax hA₀ hF hpd hX hadj hE hEU hj
  exact ⟨_, hN⟩

end CFSG.Timmesfeld.ARS
