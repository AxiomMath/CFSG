module

public import CFSG.Timmesfeld.ARS.CaseD4Collinear
public import CFSG.Timmesfeld.ARS.LinearDict

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem conjSub_mem_lambdaStar_of_mem_levi (hR : IsRootClass R) {A A₀ X : Subgroup G}
    (hX : X ∈ lambdaStar R A A₀) {v : G} (hv : v ∈ levi R A A₀) :
    conjSub X v ∈ lambdaStar R A A₀ := by
  have hvA : conjSub A v = A := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hv) a ha).symm
  have hvA₀ : conjSub A₀ v = A₀ := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hv) a ha).symm
  refine ⟨?_, hR.conjSub_mem hX.1.1.1 v, ?_⟩
  · have := conjSub_mem_lambdaSet hR hX.1 v
    rwa [hvA] at this
  · have := Sec3.special_conjSub hR hX.2.2 v
    rwa [hvA₀] at this

theorem commuting_commutator_of_commuting {X Y Z : Subgroup G} (hXZ : Commuting X Z)
    (hYZ : Commuting Y Z) : Commuting ⁅X, Y⁆ Z := by
  refine commuting_iff_commutator_eq_bot.2 (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_)
  · rw [commuting_iff_commutator_eq_bot.1 hYZ, Subgroup.commutator_bot_left]
  · rw [commuting_iff_commutator_eq_bot.1 hXZ.symm, Subgroup.commutator_bot_left]

namespace CaseD4

section Frame

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  {ι : Type*} {P Q : ι → Subgroup G} (hPQ : LeviSL2Family R A A₀ P Q)
include h hA hAne hmax hA₀ hPQ

theorem natural_of_commuting {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (i : ι)
    (hQX : Commuting (Q i) X) :
    Special R (P i) X ∧ (∀ u ∈ Q i ⊔ P i, conjSub (X ⊔ ⁅P i, X⁆) u = X ⊔ ⁅P i, X⁆) ∧
      (∀ n ∈ X ⊔ ⁅P i, X⁆, (∀ y ∈ Q i, Commute y n) → n ∈ X) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hs := special_of_commuting h hA hAne hmax hA₀ hPQ.swap hX i hQX
  have hl := mem_lambdaSet_of_commuting h hA hAne hmax hA₀ hPQ hX i hQX
  have hQ : Q i ∈ R := (hPQ.mem_right i).1.1
  have hP : P i ∈ R := (hPQ.mem_left i).1.1
  have hop : Opposite (Q i) (P i) := (hPQ.opposite i).symm
  exact ⟨hs, fun u hu => Sec3.conjSub_sup_commutator_eq hR hiso hQ hP hop hl ⟨hX.1.1.1, hs⟩ hu,
    fun n hn hnQ => Sec3.mem_of_forall_commute_of_mem_sup hR hiso hQ hP hop hl ⟨hX.1.1.1, hs⟩ hn
      hnQ⟩

theorem commuting_conjSub_of_commuting {X C : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (k : ι)
    (hQX : Commuting (Q k) X) (hXC : Commuting X C) (hPC : Commuting (P k) C) {u : G}
    (hu : u ∈ P k ⊔ Q k) : Commuting (conjSub X u) C := by
  obtain ⟨-, hinv, -⟩ := natural_of_commuting h hA hAne hmax hA₀ hPQ hX k hQX
  have hN : Commuting (X ⊔ ⁅P k, X⁆) C :=
    Commuting.sup_left hXC (commuting_commutator_of_commuting hPC hXC)
  refine hN.mono ?_ le_rfl
  rw [← hinv u (sup_comm (P k) (Q k) ▸ hu)]
  exact Subgroup.map_mono le_sup_left

theorem conjSub_props_of_mem_iSup {E C : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hEQ : ∀ i, Commuting (Q i) E) (hEC : Commuting E C) (hCP : ∀ i, Commuting (P i) C)
    [DecidableEq ι] (s : Finset ι) {v : G} (hv : v ∈ ⨆ i ∈ s, (P i ⊔ Q i)) :
    conjSub E v ∈ lambdaStar R A A₀ ∧ Commuting (conjSub E v) C ∧
      ∀ j ∉ s, Commuting (Q j) (conjSub E v) := by
  classical
  have hR := h.root
  induction s using Finset.induction_on generalizing v with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Subgroup.mem_bot] at hv
    subst hv
    simp only [conjSub_one]
    exact ⟨hE, hEC, fun j _ => hEQ j⟩
  | insert k s hks ih =>
    rw [Finset.iSup_insert] at hv
    have hW : (⨆ i ∈ s, (P i ⊔ Q i)) ≤ Subgroup.normalizer ((P k ⊔ Q k : Subgroup G) : Set G) := by
      refine iSup₂_le fun j hj => ?_
      have hjk : j ≠ k := fun e => hks (e ▸ hj)
      exact (commuting_iff_le_centralizer.1 (hPQ.commuting k j hjk.symm)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hv' : v ∈ ((P k ⊔ Q k ⊔ ⨆ i ∈ s, (P i ⊔ Q i) : Subgroup G) : Set G) := hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hW] at hv'
    obtain ⟨u, hu, w, hw, rfl⟩ := hv'
    obtain ⟨hX, hXC, hXQ⟩ := ih hw
    rw [conjSub_mul]
    have hlevi : P k ⊔ Q k ≤ levi R A A₀ := hPQ.levi_eq ▸ le_iSup (fun i => P i ⊔ Q i) k
    refine ⟨conjSub_mem_lambdaStar_of_mem_levi hR hX (hlevi hu),
      commuting_conjSub_of_commuting h hA hAne hmax hA₀ hPQ hX k (hXQ k hks) hXC (hCP k) hu,
      fun j hj => ?_⟩
    have hjk : j ≠ k := fun e => hj (e ▸ Finset.mem_insert_self k s)
    have hjs : j ∉ s := fun h' => hj (Finset.mem_insert_of_mem h')
    have h1 := (hXQ j hjs).conjSub u
    rwa [conjSub_of_forall_commute fun y hy =>
      ((hPQ.commuting k j hjk.symm) u hu y (Subgroup.mem_sup_right hy))] at h1

theorem not_commuting_of_extremal [Finite ι] {E C : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hEQ : ∀ i, Commuting (Q i) E) (hC : C ∈ lambdaStar R A A₀) (hCP : ∀ i, Commuting (P i) C) :
    ¬ Commuting E C := by
  classical
  have := Fintype.ofFinite ι
  intro hEC
  have := h.finite
  have hall : ∀ v ∈ levi R A A₀, Commuting (conjSub E v) C := by
    intro v hv
    rw [hPQ.levi_eq] at hv
    have hv' : v ∈ ⨆ i ∈ (Finset.univ : Finset ι), (P i ⊔ Q i) := by
      simpa only [Finset.mem_univ, iSup_true] using hv
    exact (conjSub_props_of_mem_iSup h hA hAne hmax hA₀ hPQ hE hEQ hEC hCP _ hv').2.1
  have hCM : Commuting C (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE hY
    exact commuting_iff_le_centralizer.1 (hall v hv).symm
  have hmem : C ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hC.1.1.1, hCM⟩
  rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact hC.1.1.2.1 hmem

theorem commutator_eq_of_extremal [Finite ι] {E C : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hEQ : ∀ i, Commuting (Q i) E) (hC : C ∈ lambdaStar R A A₀) (hCP : ∀ i, Commuting (P i) C) :
    Special R E C ∧ ⁅E, C⁆ = A := by
  have := h.finite
  have hR := h.root
  obtain ⟨-, -, hcommA, -, hMP⟩ := Q_eq_M h hA
  have hnc := not_commuting_of_extremal h hA hAne hmax hA₀ hPQ hE hEQ hC hCP
  have hER : E ∈ R := hE.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  have hle : E ⊔ C ≤ M R A := sup_le (QD.le_M hE.1) (QD.le_M hC.1)
  have hs : Special R E C := by
    have hne : E ≠ C := fun e => hnc (by rw [← e]; exact hR.commuting_self hER)
    rcases hR.rel _ hER _ hCR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hER hCR (hMP.to_le hle))
    · exact hs
  refine ⟨hs, Subgroup.eq_of_le_of_card_ge ?_ (hR.card_eq hA hs.1).le⟩
  rw [← hcommA]
  exact Subgroup.commutator_mono (le_sup_left.trans hle) (le_sup_right.trans hle)

theorem hyp_symm : A₀ ∈ R ∧ sigmaSet R A₀ ≠ lambdaSet R A₀ ∧
    IsSigmaMaximal R (centralGroup R A₀) ∧ A ∈ omegaSet R A₀ ∧ LeviSL2Family R A₀ A P Q :=
  ⟨hA₀.1, sigmaSet_ne_lambdaSet_of_mem h.root hA hA₀.1 hAne,
    isSigmaMaximal_centralGroup_of_mem h.root hA hA₀.1 hmax, ⟨hA, hA₀.2.symm⟩, hPQ.symm⟩

theorem config {E F : Subgroup G} (hE : E ∈ lambdaStar R A A₀) (hEQ : ∀ i, Commuting (Q i) E)
    (hF : F ∈ lambdaStar R A₀ A) (hFP : ∀ i, Commuting (P i) F) (hEF : Opposite E F)
    (i : ι) :
    Special R (P i) E ∧ Commuting (Q i) E ∧ ⁅Q i, ⁅P i, E⁆⁆ = E ∧ Commuting (P i) F ∧
      ⁅⁅P i, E⁆, F⁆ = P i ∧ Special R (Q i) F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hA₀R, hA₀ne, hmax₀, hAΩ, hPQ'⟩ := hyp_symm h hA hAne hmax hA₀ hPQ
  have hPl := hPQ.mem_left i
  have hQl := hPQ.mem_right i
  have hPR : P i ∈ R := hPl.1.1
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  obtain ⟨hsPE, hinv, hfix⟩ := natural_of_commuting h hA hAne hmax hA₀ hPQ hE i (hEQ i)
  set D := ⁅P i, E⁆ with hDdef
  have hDR : D ∈ R := hsPE.1
  have hD : D ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hPl hE hsPE.symm).1 D hDR
    rw [Subgroup.commutator_comm E (P i)] at this
    exact this le_sup_right
  have hDE : D ≠ E := by
    have := hsPE.symm.ne_commutator hR
    rw [Subgroup.commutator_comm E (P i)] at this
    exact this.symm
  have hQN : Q i ≤ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hinv y (Subgroup.mem_sup_left hy))
  have hsQD : Special R (Q i) D := by
    have hnc : ¬ Commuting (Q i) D := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun d hd => ?_) (hR.card_eq hER hDR).le)
      exact hfix d (Subgroup.mem_sup_right hd) fun y hy => hc y hy d hd
    have hne : Q i ≠ D := fun e => hnc (by rw [← e]; exact hR.commuting_self hQl.1.1)
    rcases hR.rel _ hQl.1.1 _ hDR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho (not_opposite_of_mem_leviSet hR hA hD hQl)
    · exact hs
  have h3 : ⁅Q i, D⁆ = E := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hER hsQD.1).le
    exact hfix x (Linear.commutator_le_of_le_normalizer hQN le_sup_right hx) fun y hy =>
      (hsQD.2.1 x hx y hy).symm
  have hFl : F ∈ lambdaSet R (P i) :=
    mem_lambdaSet_of_commuting' h hA₀R hA₀ne hmax₀ hAΩ hPQ' hF i (hFP i)
  have hPFl : P i ∈ lambdaSet R F := mem_lambdaSet_comm hPR hFl
  have hPψ : P i ∈ psiSet R E := ⟨hPR, hsPE.symm⟩
  have hinv' : ∀ x ∈ F ⊔ E, conjSub (P i ⊔ ⁅E, P i⁆) x = P i ⊔ ⁅E, P i⁆ := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hFR hER hEF.symm hPFl hPψ hx
  have hfix' : ∀ n ∈ P i ⊔ ⁅E, P i⁆, (∀ a ∈ F, Commute a n) → n ∈ P i := fun n hn hnF =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hFR hER hEF.symm hPFl hPψ hn hnF
  rw [Subgroup.commutator_comm E (P i)] at hinv' hfix'
  have hFN : F ≤ Subgroup.normalizer ((P i ⊔ D : Subgroup G) : Set G) := fun f hf =>
    conjSub_eq_self_iff.1 (hinv' f (Subgroup.mem_sup_left hf))
  have hsDF : Special R D F := by
    have hnc : ¬ Commuting D F := by
      intro hc
      have hDP : D = P i := (Subgroup.eq_of_le_of_card_ge (fun d hd =>
        hfix' d (Subgroup.mem_sup_right hd) fun f hf => (hc d hd f hf).symm)
        (hR.card_eq hPR hDR).le)
      exact hD.2.2.not_commuting hR (hDP ▸ hPl.2.2.2)
    have hne : D ≠ F := fun e => hnc (by rw [← e]; exact hR.commuting_self hDR)
    rcases hR.rel _ hDR _ hFR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd hsPE.2.1 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR ho hPFl)
    · exact hs
  have h5 : ⁅D, F⁆ = P i := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hPR hsDF.1).le
    exact hfix' x (commutator_le_of_le_normalizer le_sup_right hFN hx) fun f hf =>
      (hsDF.2.2 x hx f hf).symm
  exact ⟨hsPE, hEQ i, h3, hFP i, h5,
    special_of_commuting h hA₀R hA₀ne hmax₀ hAΩ hPQ' hF i (hFP i)⟩

theorem iSup_sup_sup_eq_top {E F : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hF : F ∈ lambdaStar R A₀ A) : (⨆ i, (P i ⊔ Q i)) ⊔ E ⊔ F = ⊤ := by
  obtain ⟨hA₀R, hA₀ne, hmax₀, hAΩ, -⟩ := hyp_symm h hA hAne hmax hA₀ hPQ
  set H := (⨆ i, (P i ⊔ Q i)) ⊔ E ⊔ F with hH
  have hV : levi R A A₀ ≤ H := hPQ.levi_eq ▸ le_sup_left.trans le_sup_left
  have hV' : levi R A₀ A ≤ H := by
    have e : levi R A₀ A = levi R A A₀ := by simp only [levi, leviSet, Set.inter_comm]
    rw [e]
    exact hV
  have hMA : M R A ≤ H := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE hY
    exact conjSub_le (le_sup_right.trans le_sup_left) (hV hv)
  have hMA₀ : M R A₀ ≤ H := by
    rw [M_eq_gen_lambdaStar h hA₀R hAΩ]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ :=
      exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA₀R hA₀ne hmax₀ hAΩ hF hY
    exact conjSub_le le_sup_right (hV' hv)
  rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top h hA hA₀]
  exact sup_le ((gen_le fun B hB => QD.le_M hB).trans hMA) (QD.le_M_self.trans hMA₀)

end Frame

theorem commutator_props (h : Hyp G R) {A A₀ C : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hC : C ∈ lambdaStar R A A₀) :
    ⁅A₀, C⁆ ∈ lambdaStar R A₀ A ∧ Commuting ⁅A₀, C⁆ C ∧ ⁅A, ⁅A₀, C⁆⁆ = C ∧
      ∀ Y ∈ leviSet R A A₀, Commuting Y C → Commuting Y ⁅A₀, C⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hA₀R : A₀ ∈ R := hA₀.1
  have hCR : C ∈ R := hC.1.1.1
  have hs₀ : Special R A₀ C := hC.2.2
  set F := ⁅A₀, C⁆ with hFdef
  have hFR : F ∈ R := hs₀.1
  have hFl : F ∈ lambdaSet R A₀ :=
    mem_lambdaSet_comm hFR (mem_lambdaSet_commutator hR hiso hA₀R hCR hs₀).1
  have hCFl : C ∈ lambdaSet R F := (mem_lambdaSet_commutator hR hiso hA₀R hCR hs₀).2
  have hCF : C ≠ F := by
    have := hs₀.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm C A₀] at this
  have hinv : ∀ x ∈ A ⊔ A₀, conjSub (C ⊔ F) x = C ⊔ F := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hA hA₀R hA₀.2 hC.1 hC.2 hx
  have hfix : ∀ n ∈ C ⊔ F, (∀ a ∈ A, Commute a n) → n ∈ C := fun n hn hnA =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hA hA₀R hA₀.2 hC.1 hC.2 hn hnA
  have hAN : A ≤ Subgroup.normalizer ((C ⊔ F : Subgroup G) : Set G) := fun a ha =>
    conjSub_eq_self_iff.1 (hinv a (Subgroup.mem_sup_left ha))
  have hAF : Special R A F := by
    have hnc : ¬ Commuting A F := by
      intro hc
      refine hCF (Subgroup.eq_of_le_of_card_ge (fun f hf => ?_) (hR.card_eq hCR hFR).le).symm
      exact hfix f (Subgroup.mem_sup_right hf) fun a ha => hc a ha f hf
    have hne : A ≠ F := fun e => hnc (by rw [← e]; exact hR.commuting_self hA)
    rcases hR.rel _ hA _ hFR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd hC.1.1.2.2 (not_commuting_of_opposite_of_mem_lambdaSet hR hA ho hCFl)
    · exact hs
  have hAFC : ⁅A, F⁆ = C := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hCR hAF.1).le
    exact hfix x (Linear.commutator_le_of_le_normalizer hAN le_sup_right hx) fun a ha =>
      (hAF.2.1 x hx a ha).symm
  exact ⟨⟨hFl, hFR, hAF⟩, hs₀.2.2, hAFC, fun Y hY hYC =>
    (commuting_commutator_of_commuting hY.2.2.2 hYC.symm).symm⟩

theorem opposite_of_extremal [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A C E F : Subgroup G} (hA : A ∈ R) (hC : C ∈ R) (hE : E ∈ R) (hF : F ∈ R)
    (hAC : Commuting A C) (hEA : Commuting E A) (hEC : Special R E C) (hECA : ⁅E, C⁆ = A)
    (hFC : Commuting F C) (hAF : Special R A F) (hAFC : ⁅A, F⁆ = C) : Opposite E F := by
  have hEF : E ≠ F := fun e => hAF.not_commuting hR (by rw [← e]; exact hEA.symm)
  have hnc : ¬ Commuting E F := by
    intro hc
    obtain ⟨c, hc', hc1⟩ := hR.exists_ne_one hC
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
    obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hF
    have hmem : ⁅c, e⁆ ∈ A := by
      rw [← hECA, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hc' he
    have hne : ⁅c, e⁆ ≠ 1 := fun h1 =>
      hc1 (eq_one_of_commute_of_special hR hiso hE hC hEC he he1 hc'
        ((commutatorElement_eq_one_iff_commute.1 h1).symm))
    have hfc : Commute f c := hFC f hf c hc'
    have hfe : Commute f e := (hc e he f hf).symm
    have hfce : Commute f ⁅c, e⁆ := by
      rw [commutatorElement_def]
      exact ((hfc.mul_right hfe).mul_right hfc.inv_right).mul_right hfe.inv_right
    exact hf1 (eq_one_of_commute_of_special hR hiso hA hF hAF hmem hne hf hfce.symm)
  have hns : ¬ Special R E F := by
    intro hs
    have hK : IsPGroup 2 ↥(E ⊔ F) := hs.isPGroup_sup hR hE hF
    have hL : IsPGroup 2 ↥(A ⊔ C) := isPGroup_sup_of_commuting (hR.isPGroup hA) (hR.isPGroup hC)
      hAC
    have hEN : E ≤ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
      refine le_normalizer_of_conjSub_le fun e he => ?_
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        conjSub_of_forall_commute fun a ha => hEA e he a ha]
      refine sup_le le_sup_left ((conjSub_le_commutator_sup he).trans (sup_le ?_ le_sup_right))
      rw [Subgroup.commutator_comm, hECA]
      exact le_sup_left
    have hFN : F ≤ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
      refine le_normalizer_of_conjSub_le fun f hf => ?_
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        conjSub_of_forall_commute fun c hc => hFC f hf c hc]
      refine sup_le ((conjSub_le_commutator_sup hf).trans (sup_le ?_ le_sup_left)) le_sup_right
      rw [hAFC]
      exact le_sup_right
    have hLne : A ⊔ C ≠ ⊥ := fun h1 => hR.ne_bot A hA (le_bot_iff.1 (h1 ▸ le_sup_left))
    obtain ⟨t, ht, ht1, htK⟩ :=
      Linear.exists_ne_one_commute_of_le_normalizer hK hL (sup_le hEN hFN) hLne
    have hCN : C ≤ Subgroup.normalizer ((A : Subgroup G) : Set G) := fun c hc =>
      conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun a ha => (hAC a ha c hc).symm)
    have ht' : t ∈ ((A ⊔ C : Subgroup G) : Set G) := ht
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN] at ht'
    obtain ⟨a, ha, c, hc, rfl⟩ := ht'
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
    obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hF
    have hec : Commute e c := by
      have h1 := htK e (Subgroup.mem_sup_left he)
      have h2 : Commute e a := hEA e he a ha
      have h3 := h2.inv_right.mul_right h1
      rwa [inv_mul_cancel_left] at h3
    have hc1 : c = 1 := eq_one_of_commute_of_special hR hiso hE hC hEC he he1 hc hec
    subst hc1
    simp only [mul_one] at ht1 htK
    exact ht1 (eq_one_of_commute_of_special hR hiso hF hA hAF.symm hf hf1 ha
      (htK f (Subgroup.mem_sup_right hf)))
  rcases hR.rel E hE F hF hEF with hc | ho | hs
  · exact absurd hc hnc
  · exact ho
  · exact absurd hs hns

end CaseD4

end CFSG.Timmesfeld.ARS
