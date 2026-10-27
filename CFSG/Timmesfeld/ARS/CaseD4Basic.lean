module

public import CFSG.Timmesfeld.ARS.Sec8Sigma

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

structure LeviSL2Family (R : Set (Subgroup G)) (A A₀ : Subgroup G) {ι : Type*}
    (P Q : ι → Subgroup G) : Prop where
  mem_left : ∀ i, P i ∈ leviSet R A A₀
  mem_right : ∀ i, Q i ∈ leviSet R A A₀
  opposite : ∀ i, Opposite (P i) (Q i)
  commuting : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)
  levi_eq : levi R A A₀ = ⨆ i, (P i ⊔ Q i)

abbrev LeviSL2Cube (R : Set (Subgroup G)) (A A₀ : Subgroup G) (P Q : Fin 3 → Subgroup G) :
    Prop :=
  LeviSL2Family R A A₀ P Q

namespace LeviSL2Family

variable {A A₀ : Subgroup G} {ι : Type*} {P Q : ι → Subgroup G}

theorem swap (hPQ : LeviSL2Family R A A₀ P Q) : LeviSL2Family R A A₀ Q P where
  mem_left := hPQ.mem_right
  mem_right := hPQ.mem_left
  opposite i := (hPQ.opposite i).symm
  commuting i j hij := by
    rw [sup_comm (Q i), sup_comm (Q j)]
    exact hPQ.commuting i j hij
  levi_eq := by
    rw [hPQ.levi_eq]
    exact iSup_congr fun i => sup_comm _ _

theorem symm (hPQ : LeviSL2Family R A A₀ P Q) : LeviSL2Family R A₀ A P Q where
  mem_left i := (Set.inter_comm _ _).subset (hPQ.mem_left i)
  mem_right i := (Set.inter_comm _ _).subset (hPQ.mem_right i)
  opposite := hPQ.opposite
  commuting := hPQ.commuting
  levi_eq := by
    rw [← hPQ.levi_eq]
    simp only [levi, leviSet, Set.inter_comm]

theorem comp_equiv (hPQ : LeviSL2Family R A A₀ P Q) {κ : Type*} (e : κ ≃ ι) :
    LeviSL2Family R A A₀ (P ∘ e) (Q ∘ e) where
  mem_left k := hPQ.mem_left (e k)
  mem_right k := hPQ.mem_right (e k)
  opposite k := hPQ.opposite (e k)
  commuting k l hkl := hPQ.commuting (e k) (e l) (e.injective.ne hkl)
  levi_eq := by
    rw [hPQ.levi_eq]
    exact (e.iSup_comp (g := fun i => P i ⊔ Q i)).symm

theorem commuting_of_le (hPQ : LeviSL2Family R A A₀ P Q) {i j : ι} (hij : i ≠ j)
    {X Y : Subgroup G} (hX : X ≤ P i ⊔ Q i) (hY : Y ≤ P j ⊔ Q j) : Commuting X Y :=
  (hPQ.commuting i j hij).mono hX hY

end LeviSL2Family

theorem IsSigmaSubgroup.conjSub (hR : IsRootClass R) {H : Subgroup G} (hH : IsSigmaSubgroup R H)
    (g : G) : IsSigmaSubgroup R (conjSub H g) := by
  obtain ⟨S, hS, rfl⟩ := hH
  refine ⟨conjSet S g, ?_, conjSub_gen S g⟩
  rintro _ ⟨B, hB, rfl⟩
  exact hR.conjSub_mem (hS hB) g

theorem IsSigmaMaximal.conjSub (hR : IsRootClass R) {H : Subgroup G} (hH : IsSigmaMaximal R H)
    (g : G) : IsSigmaMaximal R (conjSub H g) := by
  obtain ⟨hS, hne, hmax⟩ := hH
  refine ⟨hS.conjSub hR g, fun htop => hne ?_, fun K hK hle => ?_⟩
  · have := congrArg (fun X => ARS.conjSub X g⁻¹) htop
    simp only [Plane.conjSub_conjSub_inv] at this
    rw [this, ARS.conjSub, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective]
  · have hle' : H ≤ ARS.conjSub K g⁻¹ := by
      have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
      change ARS.conjSub (ARS.conjSub H g) g⁻¹ ≤ ARS.conjSub K g⁻¹ at this
      rwa [Plane.conjSub_conjSub_inv] at this
    rcases hmax _ (hK.conjSub hR g⁻¹) hle' with h1 | h1
    · left
      rw [← h1, Plane.conjSub_inv_conjSub]
    · right
      rw [← Plane.conjSub_inv_conjSub K g, h1, ARS.conjSub,
        Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

theorem isSigmaMaximal_centralGroup_of_mem (hR : IsRootClass R) {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ R) (hmax : IsSigmaMaximal R (centralGroup R A)) :
    IsSigmaMaximal R (centralGroup R D) := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hD
  rw [← conjSub_centralGroup hR A g]
  exact hmax.conjSub hR g

namespace CaseD4

theorem special_of_commuting_of_not [Finite G] (hR : IsRootClass R) {A A₀ X Y Y' : Subgroup G}
    (hA : A ∈ R) (hX : X ∈ lambdaStar R A A₀) (hY' : Y' ∈ leviSet R A A₀)
    (hfix : Commuting Y X → Commuting Y' X → False) (hYX : Commuting Y X) : Special R Y' X := by
  have hnc : ¬ Commuting Y' X := fun hc => hfix hYX hc
  have hno : ¬ Opposite Y' X := fun ho =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hY'.1.1 ho (mem_lambdaSet_comm hA hX.1)
      hY'.1.2.2.symm
  have hne : Y' ≠ X := fun e => hnc (e ▸ hR.commuting_self hY'.1.1)
  rcases hR.rel _ hY'.1.1 _ hX.1.1.1 hne with hc | ho | hs
  · exact absurd hc hnc
  · exact absurd ho hno
  · exact hs

section Factors

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  {ι : Type*} {P Q : ι → Subgroup G} (hPQ : LeviSL2Family R A A₀ P Q)
include h hA hAne hmax hA₀ hPQ

theorem not_commuting_and_commuting {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (i : ι)
    (hP : Commuting (P i) X) (hQ : Commuting (Q i) X) : False := by
  have := h.finite
  have hR := h.root
  set W := P i ⊔ Q i with hW
  have key : ∀ v ∈ levi R A A₀, ∀ Y : Subgroup G, Commuting W Y → Commuting W (conjSub Y v) := by
    intro v hv
    rw [hPQ.levi_eq] at hv
    refine Subgroup.iSup_induction (fun j => P j ⊔ Q j)
      (C := fun v => ∀ Y : Subgroup G, Commuting W Y → Commuting W (conjSub Y v)) hv
      (fun j x hx Y hY => ?_) (fun Y hY => by rwa [conjSub_one])
      (fun x y hx hy Y hY => by rw [conjSub_mul]; exact hx _ (hy Y hY))
    by_cases hij : j = i
    · subst hij
      rw [conjSub_of_forall_commute fun y hy => hY x hx y hy]
      exact hY
    · have h1 := hY.conjSub x
      rwa [conjSub_of_forall_commute fun w hw => (hPQ.commuting j i hij) x hx w hw] at h1
  have hPM : Commuting (P i) (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hX hY
    exact commuting_iff_le_centralizer.1
      ((key v hv X (Commuting.sup_left hP hQ)).mono le_sup_left le_rfl)
  have hmem : P i ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨(hPQ.mem_left i).1.1, hPM⟩
  rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact (hPQ.mem_left i).1.2.1 hmem

theorem special_of_commuting {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (i : ι)
    (hP : Commuting (P i) X) : Special R (Q i) X :=
  have := h.finite
  special_of_commuting_of_not h.root hA hX (hPQ.mem_right i)
    (not_commuting_and_commuting h hA hAne hmax hA₀ hPQ hX i) hP

end Factors

theorem not_opposite_of_mem_leviSet [Finite G] (hR : IsRootClass R) {A A₀ X Y : Subgroup G}
    (hA : A ∈ R) (hX : X ∈ lambdaStar R A A₀) (hY : Y ∈ leviSet R A A₀) : ¬ Opposite Y X :=
  fun ho => not_commuting_of_opposite_of_mem_lambdaSet hR hY.1.1 ho (mem_lambdaSet_comm hA hX.1)
    hY.1.2.2.symm

theorem exists_mem_lambdaStar_forall_commuting (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) {ι : Type*}
    {Q : ι → Subgroup G} (hQ : ∀ i, Q i ∈ leviSet R A A₀)
    (hQQ : ∀ i j, Commuting (Q i) (Q j)) (hne : (lambdaStar R A A₀).Nonempty) (s : Finset ι) :
    ∃ E ∈ lambdaStar R A A₀, ∀ i ∈ s, Commuting (Q i) E := by
  classical
  have := h.finite
  have hR := h.root
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨E, hE⟩ := hne
    exact ⟨E, hE, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert k s hks ih =>
    obtain ⟨D, hD, hDs⟩ := ih
    by_cases hDk : Commuting (Q k) D
    · refine ⟨D, hD, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hDk
      · exact hDs i hi
    have hDQ : Special R D (Q k) := by
      have hne : D ≠ Q k := fun e => hDk (by rw [← e]; exact hR.commuting_self hD.1.1.1)
      rcases hR.rel _ hD.1.1.1 _ (hQ k).1.1 hne with hc | ho | hs
      · exact absurd hc.symm hDk
      · exact absurd ho.symm (not_opposite_of_mem_leviSet hR hA hD (hQ k))
      · exact hs
    refine ⟨⁅D, Q k⁆, (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hQ k) hD hDQ).1 _ hDQ.1
      le_sup_right, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hDQ.2.2.symm
    ·
      refine commuting_iff_commutator_eq_bot.2 ?_
      rw [Subgroup.commutator_comm]
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [commuting_iff_commutator_eq_bot.1 (hQQ k i), Subgroup.commutator_bot_left]
      · rw [commuting_iff_commutator_eq_bot.1 (hDs i hi), Subgroup.commutator_bot_left]

theorem lambdaStar_nonempty (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) : (lambdaStar R A A₀).Nonempty := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hM : M R A = ⊥ := by
    rw [M_eq_gen_lambdaStar h hA hA₀, hemp]
    exact le_bot_iff.1 (gen_le fun _ hB => absurd hB (Set.notMem_empty _))
  exact hR.ne_bot A hA (le_bot_iff.1 (hM ▸ QD.le_M_self))

end CaseD4

end CFSG.Timmesfeld.ARS
