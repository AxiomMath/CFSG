module

public import CFSG.Timmesfeld.ARS.CaseOAInter
public import CFSG.Timmesfeld.ARS.CaseOANode
public import CFSG.Timmesfeld.ARS.CaseENonSph
public import CFSG.Timmesfeld.ARS.CaseOALevelInv

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {G : Type} [Group G] {R : Set (Subgroup G)} {K : Type*} [Group K] {A A₀ : Subgroup G}
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

namespace CaseOA

theorem eq_or_eq_of_card_two [Finite G] (h2 : Nat.card (leviComps R A A₀) = 2)
    {Δ₁ Δ₂ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀)
    (hne : Δ₁ ≠ Δ₂) {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) : Δ = Δ₁ ∨ Δ = Δ₂ := by
  have hcard : Nat.card (leviComps R A A₀) = (leviComps R A A₀).ncard := Nat.card_coe_set_eq _
  rw [hcard, Set.ncard_eq_two] at h2
  obtain ⟨X, Y, hXY, hXYs⟩ := h2
  rw [hXYs] at hΔ₁ hΔ₂ hΔ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΔ₁ hΔ₂ hΔ
  rcases hΔ₁ with rfl | rfl <;> rcases hΔ₂ with rfl | rfl <;> rcases hΔ with rfl | rfl <;>
    simp_all

theorem exists_eq_mul_n_mul_of_mem_lambdaSet (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    (hS₂ : IsSL2Comp Δ₂) {Q₂ : Subgroup G} (hQ₂ : Q₂ ∈ Δ₂) (hF : CompFrame R A A₀ D n H Ψ)
    (hmem₁ : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ Δ₁) (hsurj : ∀ v ∈ gen Δ₁, ∃ g, Ψ g = v)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {C : Subgroup G}
    (hC : C ∈ lambdaStar R A A₀) (hCU : Commuting C ((posUnipotent D).map Ψ))
    (hCT : (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (C : Set G)) {j : Fin D.rank}
    (hCQ : ∀ k, Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ) ↔ k ≠ j)
    (hCPl : C ∈ lambdaSet R ((D.rootGroup (Pi.single j 1)).map Ψ))
    (hpat : ∀ γ ∈ D.roots, ¬ Commuting C ((D.rootGroup γ).map Ψ) → γ j = -1)
    (hCQ₂ : Commuting Q₂ C) {Y : Subgroup G} (hY : Y ∈ lambdaStar R A A₀)
    (hYC : Y ∈ lambdaSet R C) (hYQ : Commuting Q₂ Y) :
    ∃ a ∈ stabOf Ψ C, ∃ b ∈ stabOf Ψ C, Y = conjSub C (Ψ (a * n j * b)) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hct := hF.hct
  have hCR : C ∈ R := hC.1.1.1
  have hYR : Y ∈ R := hY.1.1.1
  have hB : borel D H ≤ stabOf Ψ C := borel_le_stabOf hCT hCU
  have hPk : ∀ k, Commuting C ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k =>
    hCU.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent (Φ.single_mem k)
      (ht_single_pos k)))
  have hn : ∀ k ∈ ({k | k ≠ j} : Set (Fin D.rank)), n k ∈ stabOf Ψ C := fun k hk =>
    n_mem_stabOf hF k (hPk k) ((hCQ k).2 hk)
  have hl₂ := fun {Z : Subgroup G} (hZ : Z ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hZ
  obtain ⟨X, hX, hCX⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hC hY
    (mem_lambdaSet_comm hCR hYC)
  have hsCX : Special R C X := special_of_commutator_mem_of_mem_leviSet h hA hC hX (hCX ▸ hYR)
  have hXΔ₁ : X ∈ Δ₁ := by
    obtain ⟨Δ, hΔ, hXΔ⟩ := Sec9.mem_comp_self hX
    rcases eq_or_eq_of_card_two h2 hΔ₁ hΔ₂ hne hΔ with rfl | rfl
    · exact hXΔ
    · exfalso
      have hXQ : X ≠ Q₂ := by
        rintro rfl
        have hbot : Y = ⊥ := by
          rw [← hCX]
          exact commuting_iff_commutator_eq_bot.1 hCQ₂.symm
        exact hR.ne_bot Y hYR hbot
      obtain ⟨-, hgen⟩ := hS₂.opposite_of_ne hR (fun Z hZ => (hl₂ hZ).1.1) hXΔ hQ₂ hXQ
      have hYX : Commuting Y X := hCX ▸ hsCX.2.2
      have hYV : Commuting Y (gen Δ) := by
        rw [← hgen]
        exact hYX.sup_right hYQ.symm
      exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ hY fun Z hZ =>
        (hYV.mono le_rfl (le_gen hZ)).symm
  obtain ⟨θ, hθ, hmaxθ⟩ : ∃ θ ∈ D.roots, ∀ γ ∈ D.roots, ht γ ≤ ht θ :=
    Set.exists_max_image _ ht (finite_roots D.isFiniteType D.divisible) ⟨_, Φ.single_mem j⟩
  obtain ⟨v, hv, hvX⟩ := Sec9.exists_conjSub_eq h hΔ₁ (hmem₁ θ hθ) hXΔ₁
  obtain ⟨h₀, rfl⟩ := hsurj v hv
  obtain ⟨y, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hF.hext h₀
  have hNθ := borel_le_normalizer_rootGroup_of_max hct hF.hext hF.hdiv hθ hmaxθ
  set γ := weylAction D.isFiniteType y θ with hγdef
  have hγ : γ ∈ D.roots := weylAction_mem_roots _ _ hθ
  have hX' : X = conjSub ((D.rootGroup γ).map Ψ) (Ψ b₁) := by
    rw [← hvX, map_mul, map_mul, conjSub_mul, conjSub_mul, map_conjSub_eq Ψ _ b₂,
      (RankOne.map_conj_eq_self_iff).2 (hNθ hb₂), map_conjSub_eq, actsAs_nrep hct y _ hθ]
  have hCb₁ : conjSub C (Ψ b₁) = C := mem_stabOf.1 (hB hb₁)
  have e1 : ⁅C, X⁆ = conjSub ⁅C, (D.rootGroup γ).map Ψ⁆ (Ψ b₁) := by
    rw [hX', conjSub_commutator, hCb₁]
  have hnc : ¬ Commuting C ((D.rootGroup γ).map Ψ) := by
    intro hc
    rw [commuting_iff_commutator_eq_bot.1 hc] at e1
    have hbot : Y = ⊥ := by
      rw [← hCX, e1]
      exact Subgroup.map_bot _
    exact hR.ne_bot Y hYR hbot
  have hγj : γ j = -1 := hpat γ hγ hnc
  have hαj : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.neg_mem _ (Φ.single_mem j)
  have hγ' : -γ ∈ roots D.isFiniteType ∅ := by
    rw [← roots_eq_of_divisible hF]
    exact Φ.neg_mem _ hγ
  obtain ⟨u, hu, hue⟩ := exists_mem_parabolic_eq_of_level_one D.isFiniteType hpd j hγ'
    (by rw [Pi.neg_apply, hγj, neg_neg])
  have hγu : γ = weylAction D.isFiniteType u (-Pi.single j 1) := by rw [map_neg, hue, neg_neg]
  have hMγ : (D.rootGroup γ).map Ψ =
      conjSub ((D.rootGroup (-Pi.single j 1)).map Ψ) (Ψ (nrep hct u)) := by
    rw [map_conjSub_eq, actsAs_nrep hct u _ hαj, ← hγu]
  have hCu : conjSub C (Ψ (nrep hct u)) = C := mem_stabOf.1 (nrep_mem_stabOf hct hn hu)
  have e2 : ⁅C, (D.rootGroup γ).map Ψ⁆ =
      conjSub ⁅C, (D.rootGroup (-Pi.single j 1)).map Ψ⁆ (Ψ (nrep hct u)) := by
    rw [hMγ, conjSub_commutator, hCu]
  set P := (D.rootGroup (Pi.single j 1)).map Ψ with hPdef
  set Q := (D.rootGroup (-Pi.single j 1)).map Ψ with hQdef
  have hPl := hF.mem _ (Φ.single_mem j)
  have hQl := hF.mem _ hαj
  have hQj : ¬ Commuting C Q := fun hc => ((hCQ j).1 hc) rfl
  have hsCQ : Special R C Q := special_of_not_commuting_of_mem_leviSet h hA hC hQl hQj
  have hCψ : C ∈ psiSet R Q := ⟨hCR, hsCQ.symm⟩
  have hPQo : Opposite P Q := hF.opp j
  have hDR : ⁅Q, C⁆ ∈ R := hsCQ.symm.1
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hCR
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨x, hx, hxd⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hPl.1.1 hQl.1.1 hPQo hCPl hCψ
    (Subgroup.mem_sup_left he) he1 (Subgroup.mem_sup_right hd) hd1
  have hCx : conjSub C x = ⁅Q, C⁆ := Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hCR x) hDR
    (hxd ▸ conj_mem_conjSub x he) hd hd1
  rw [← Subgroup.map_sup] at hx
  obtain ⟨y', hy', rfl⟩ := hx
  have hy'B : y' ∈ bruhatCell hct (cs.simple j) := by
    obtain ⟨w, hw, hy'w⟩ := (mem_cellUnion hct).1 (mem_cellUnion_of_mem_rankOne hct hF.hext j hy')
    rcases hw with rfl | rfl
    · exfalso
      rw [bruhatCell_one] at hy'w
      rw [mem_stabOf.1 (hB hy'w)] at hCx
      refine hsCQ.ne_commutator hR ?_
      rw [Subgroup.commutator_comm]
      exact hCx
    · exact hy'w
  have e3 : Y = conjSub C (Ψ (b₁ * nrep hct u * y')) := by
    rw [← hCX, e1, e2, Subgroup.commutator_comm C Q, ← hCx, ← conjSub_mul, ← conjSub_mul,
      ← map_mul, ← map_mul]
  obtain ⟨b₃, hb₃, b₄, hb₄, hy'e⟩ := hy'B
  rw [nrep_simple] at hy'e
  refine ⟨b₁ * nrep hct u * b₃, mul_mem (mul_mem (hB hb₁) (nrep_mem_stabOf hct hn hu)) (hB hb₃),
    b₄, hB hb₄, ?_⟩
  rw [e3, hy'e]
  congr 2
  group

theorem notMem_of_ne {Δ Δ' : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    (hΔ' : Δ' ∈ leviComps R A A₀) (hne : Δ ≠ Δ') {X : Subgroup G} (hX : X ∈ Δ') : X ∉ Δ := by
  obtain ⟨E, -, rfl⟩ := hΔ
  obtain ⟨F, -, rfl⟩ := hΔ'
  intro hXE
  exact hne ((Levi.comp_eq_of_mem hXE).symm.trans (Levi.comp_eq_of_mem hX))

theorem false_of_starOneAt (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
    (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂) (hF : CompFrame R A A₀ D n H Ψ)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hmem₁ : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ Δ₁) (hrange : ∀ g, Ψ g ∈ gen Δ₁)
    (hsurj : ∀ v ∈ gen Δ₁, ∃ g, Ψ g = v) {adj : Fin D.rank → Fin D.rank → Prop}
    (hX : IsConfig R adj (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ))
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ))
    (hQ₂E : Commuting Q₂ E) {j : Fin D.rank}
    (hjE : ∀ k, ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ↔ k = j)
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ w, (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w ≤
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w₀)
    (hjw : weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single j 1)
    (hstar : StarOneAt D.cartan D.isFiniteType j) : False := by
  have := h.finite
  have hR := h.root
  have hct := hF.hct
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hS₂ : IsSL2Comp Δ₂ := ⟨P₂, hP₂, Q₂, hQ₂, hPQ₂, hgen₂⟩
  have hk : ∀ k, (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem
  have hER : E ∈ R := hE.1.1.1
  choose σ hσ using exists_weylAction_eq_neg_single D.isFiniteType hpd hw₀
  have hσinj : Function.Injective σ := fun a b e => by
    have h1 : weylAction D.isFiniteType w₀ (Pi.single a 1) =
        weylAction D.isFiniteType w₀ (Pi.single b 1) := by rw [hσ a, hσ b, e]
    have h2 := congrFun (weylAction_apply_injective D.isFiniteType w₀ h1) a
    by_contra hab
    simp [Pi.single_eq_of_ne hab] at h2
  have hσj : σ j = j := by
    by_contra hne'
    have h1 := congrFun (neg_injective ((hσ j).symm.trans hjw)) j
    rw [Pi.single_eq_of_ne (Ne.symm hne'), Pi.single_eq_same] at h1
    exact zero_ne_one h1
  have hσk : ∀ k, σ k = j ↔ k = j := fun k =>
    ⟨fun e => hσinj (e.trans hσj.symm), fun e => e ▸ hσj⟩
  have hw₀d : ∀ i, cs.IsRightDescent w₀ i := fun i => by_contra fun hi => by
    have h1 := cs.not_isRightDescent_iff.mp hi
    have := hw₀ (w₀ * cs.simple i)
    omega
  set n₀ := nrep hct w₀ with hn₀def
  set C := conjSub E (Ψ n₀)⁻¹ with hCdef
  have hCE : conjSub C (Ψ n₀) = E := by rw [hCdef, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hC : C ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hE (inv_mem (hF.range _))
  have hCR : C ∈ R := hC.1.1.1
  have hCU : Commuting C ((posUnipotent D).map Ψ) := commuting_posUnipotent_conjSub hct hw₀d hEU
  have hET := map_iSup_le_normalizer_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU
  have hCT := map_iSup_le_normalizer_conjSub hct w₀ hET
  have hcV : ∀ x ∈ gen Δ₁, ∀ q ∈ Q₂, Commute x q := fun x hx q hq =>
    Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne x hx q (le_gen hQ₂ hq)
  have hQ₂fix : conjSub Q₂ (Ψ n₀)⁻¹ = Q₂ :=
    conjSub_of_forall_commute fun q hq => hcV _ (inv_mem (hrange _)) q hq
  have hCQ₂ : Commuting Q₂ C := by
    have h1 := hQ₂E.conjSub (Ψ n₀)⁻¹
    rwa [hQ₂fix] at h1
  have hact := actsAs_nrep hct w₀
  have hQσ : ∀ k, conjSub ((D.rootGroup (-Pi.single k 1)).map Ψ) (Ψ n₀) =
      (D.rootGroup (Pi.single (σ k) 1)).map Ψ := fun k => by
    rw [map_conjSub_eq, hact _ (Φ.neg_mem _ (hk k)), map_neg, hσ k, neg_neg]
  have hCQ : ∀ k, Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ) ↔ k ≠ j := fun k => by
    rw [← commuting_conjSub_iff' (Ψ n₀), hCE, hQσ k, ne_eq, ← hσk k, ← hjE (σ k), not_not]
  have hlow := natural_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU
  obtain ⟨hEl, -⟩ := (hlow j).resolve_left ((hjE j).2 rfl)
  have hwj : weylAction D.isFiniteType w₀⁻¹ (-Pi.single j 1) = Pi.single j 1 := by
    rw [← hjw, weylAction_inv_apply_apply]
  have e2 : conjSub ((D.rootGroup (-Pi.single j 1)).map Ψ) (Ψ n₀)⁻¹ =
      (D.rootGroup (Pi.single j 1)).map Ψ := by
    rw [← map_inv, map_conjSub_eq, hact.inv _ (Φ.neg_mem _ (hk j)), hwj]
  have hCPl : C ∈ lambdaSet R ((D.rootGroup (Pi.single j 1)).map Ψ) := by
    have h1 := conjSub_mem_lambdaSet hR hEl (Ψ n₀)⁻¹
    rwa [e2] at h1
  have hpat : ∀ γ ∈ D.roots, ¬ Commuting C ((D.rootGroup γ).map Ψ) → γ j = -1 :=
    fun γ hγ hnc => highest_pattern h hA hAne hmax hA₀ hF hpd hX hadj hE hEU hjE hσ hσinj hσj hγ
      hnc
  obtain ⟨E₀, hE₀, hΔ₁e⟩ := id hΔ₁
  have hQ₂l := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hQ₂
  have hEC : Commuting E C := commuting_conjSub_of_isSigmaMaximal h hA hAne hmax hA₀ hE₀ hQ₂l
    (hΔ₁e ▸ notMem_of_ne hΔ₁ hΔ₂ hne hQ₂) hE (hΔ₁e ▸ inv_mem (hrange n₀))
  have hECne : E ≠ C := by
    intro e
    refine (hjE j).2 rfl ?_
    rw [e]
    exact hCU.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent (hk j) (ht_single_pos j)))
  obtain ⟨Y, ⟨hY, hYC⟩, hYE⟩ :=
    lambdaStar_inter_nonempty h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne hC hE hEC.symm
  have hYQ : Commuting Q₂ Y := by
    by_contra hc
    have hYQ' : ¬ Commuting Y Q₂ := fun h' => hc h'.symm
    have h1 := eq_commutator_of_mem_lambdaSet h hA hAne hmax hA₀ hΔ₂ hS₂ hQ₂ hE hY hQ₂E hYQ'
      (mem_lambdaSet_comm hER hYE)
    have h2 := eq_commutator_of_mem_lambdaSet h hA hAne hmax hA₀ hΔ₂ hS₂ hQ₂ hC hY hCQ₂ hYQ'
      (mem_lambdaSet_comm hCR hYC)
    exact hECne (h1.trans h2.symm)
  have hB : borel D H ≤ stabOf Ψ C := borel_le_stabOf hCT hCU
  have hPk : ∀ k, Commuting C ((D.rootGroup (Pi.single k 1)).map Ψ) := fun k =>
    hCU.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent (hk k) (ht_single_pos k)))
  have hQj : ¬ Commuting C ((D.rootGroup (-Pi.single j 1)).map Ψ) := fun hc => ((hCQ j).1 hc) rfl
  have hn : ∀ k, k ≠ j → n k ∈ stabOf Ψ C := fun k hk' =>
    n_mem_stabOf hF k (hPk k) ((hCQ k).2 hk')
  have hpar := mem_parabolic_of_nrep_mem_stabOf hct hCU hQj hn
  have hSt : ∀ g ∈ stabOf Ψ C, g ∈ cellUnion hct (cs.parabolic {k | k ≠ j} : Set _) :=
    fun g hg => stabOf_subset_cellUnion hct hF.hext hB hpar hg
  obtain ⟨a, ha, b, hb, hYg⟩ := exists_eq_mul_n_mul_of_mem_lambdaSet h hA hAne hmax hA₀ h2 hΔ₁
    hΔ₂ hne hS₂ hQ₂ hF hmem₁ hsurj hpd hC hCU hCT hCQ hCPl hpat hCQ₂ hY hYC hYQ
  have hY' : conjSub Y (Ψ n₀)⁻¹ ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hY (inv_mem (hF.range _))
  have hY'C : conjSub Y (Ψ n₀)⁻¹ ∈ lambdaSet R C := conjSub_mem_lambdaSet hR hYE (Ψ n₀)⁻¹
  have hY'Q : Commuting Q₂ (conjSub Y (Ψ n₀)⁻¹) := by
    have h1 := hYQ.conjSub (Ψ n₀)⁻¹
    rwa [hQ₂fix] at h1
  obtain ⟨a', ha', b', hb', hY'g⟩ := exists_eq_mul_n_mul_of_mem_lambdaSet h hA hAne hmax hA₀ h2
    hΔ₁ hΔ₂ hne hS₂ hQ₂ hF hmem₁ hsurj hpd hC hCU hCT hCQ hCPl hpat hCQ₂ hY' hY'C hY'Q
  have hYn : Y = conjSub C (Ψ (n₀ * (a' * n j * b'))) := by
    rw [map_mul, conjSub_mul, ← hY'g, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hstab : (a * n j * b)⁻¹ * (n₀ * (a' * n j * b')) ∈ stabOf Ψ C := by
    rw [mem_stabOf, map_mul, conjSub_mul, ← hYn, map_inv, hYg, ← conjSub_mul, inv_mul_cancel,
      conjSub_one]
  have hsq : ((n j) ^ 2)⁻¹ ∈ stabOf Ψ C := inv_mem (hB (iSup_le_borel (sq_n_mem_iSup hct j)))
  have hn₀ : n₀ = a * n j * (b * ((a * n j * b)⁻¹ * (n₀ * (a' * n j * b'))) * b'⁻¹) * n j *
      ((n j ^ 2)⁻¹ * a'⁻¹) := by group
  have hcell := mem_cellUnion_twoStep hct hF.hext hSt ha
    (mul_mem (mul_mem hb hstab) (inv_mem hb')) (mul_mem hsq (inv_mem ha'))
  rw [← hn₀] at hcell
  obtain ⟨y, hy, hny⟩ := (mem_cellUnion hct).1 hcell
  have hyw : w₀ = y := eq_of_mem_bruhatCell hct hF.hext (nrep_mem_bruhatCell hct w₀) hny
  rw [← hyw] at hy
  exact not_twoStep_of_starOneAt hpd hstar hσ hσinj hσj hy

theorem exists_node_star (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    (hS₁ : ¬ IsSL2Comp Δ₁) (hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) {P₂ Q₂ : Subgroup G}
    (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂) (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hmem : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ Δ₁) (hrange : ∀ g, Ψ g ∈ gen Δ₁)
    (hsurj : ∀ v ∈ gen Δ₁, ∃ g, Ψ g = v) {P Q : Fin D.rank → Subgroup G}
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ = P k)
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ = Q k)
    {adj : Fin D.rank → Fin D.rank → Prop} (hX : IsConfig R adj P Q)
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁)
    {θ : Fin D.rank → ℤ} (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) :
    ∃ E C, Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧
      ∃ j, θ j = 1 ∧ (∀ k, ¬ Commuting E (P k) ↔ k = j) ∧
        ¬ StarOneAt D.cartan D.isFiniteType j ∧
        ∃ w₀ : (coxeterMatrix D.isFiniteType).Group,
          (∀ w, (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w ≤
            (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w₀) ∧
          weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single j 1 := by
  obtain ⟨E, C, hLow, hEC, hEU, j, hj, hjE, w₀, hw₀, hjw⟩ := exists_node h hA hAne hmax hA₀ h2
    hΔ₁ hΔ₂ hne hS₁ hnd hP₂ hQ₂ hPQ₂ hgen₂ hct hext hdiv hpd hmem hrange hsurj hP hQ hX hadj
    hgen₁ hθ hθ1
  refine ⟨E, C, hLow, hEC, j, hj, hjE, fun hstar => ?_, w₀, hw₀, hjw⟩
  obtain rfl : (fun k => (D.rootGroup (Pi.single k 1)).map Ψ) = P := funext hP
  obtain rfl : (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ) = Q := funext hQ
  have hF := compFrame_of_frame h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hct hext hdiv hmem hrange hsurj
    hX.opp
  exact false_of_starOneAt h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂ hgen₂ hF hpd hmem
    hrange hsurj hX hadj hLow.memE hEU hLow.commE₂ hjE hw₀ hjw hstar

end CaseOA

end CFSG.Timmesfeld.ARS
