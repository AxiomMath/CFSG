module

public import CFSG.Timmesfeld.ARS.CaseHApartment

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem commutator_le_sup' (H K : Subgroup G) : ⁅H, K⁆ ≤ H ⊔ K :=
  Subgroup.commutator_le.2 fun h hh k hk => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right hk)) (Subgroup.mem_sup_left (H.inv_mem hh)))
      (Subgroup.mem_sup_right (K.inv_mem hk))

theorem Commuting.commutator {U H K : Subgroup G} (hH : Commuting U H) (hK : Commuting U K) :
    Commuting U ⁅H, K⁆ :=
  (hH.sup_right hK).mono le_rfl (commutator_le_sup' H K)

section Short

theorem commuting_shortRoot_left (X Y Z : Subgroup G) : Commuting (shortRoot R X Y Z) X :=
  fun _ hu x hx => (Subgroup.mem_centralizer_iff.1 hu.1 x (Subgroup.mem_sup_left hx)).symm

theorem commuting_shortRoot_right (X Y Z : Subgroup G) : Commuting (shortRoot R X Y Z) Y :=
  fun _ hu y hy => (Subgroup.mem_centralizer_iff.1 hu.1 y (Subgroup.mem_sup_right hy)).symm

theorem shortRoot_le_M (X Y Z : Subgroup G) : shortRoot R X Y Z ≤ M R Z := inf_le_right

variable (h : Hyp G R)
include h

theorem commuting_shortRoot_mid {X Y Z : Subgroup G} (hZ : Z ∈ R) :
    Commuting (shortRoot R X Y Z) Z := by
  have := h.finite
  exact fun u hu z hz => (QD.commuting_M h.root hZ z hz u hu.2).symm

theorem commuting_shortRoot_mid' {X Y Z : Subgroup G} (hZ : Z ∈ R) :
    Commuting (shortRoot R X Y Z) ⁅Y, Z⁆ :=
  Commuting.commutator (commuting_shortRoot_right (R := R) X Y Z) (commuting_shortRoot_mid h hZ)

theorem commutator_shortRoot_le {X Y X' Y' Z : Subgroup G} (hZ : Z ∈ R) :
    ⁅shortRoot R X Y Z, shortRoot R X' Y' Z⁆ ≤ Z := by
  have := h.finite
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M h hZ
  exact (Subgroup.commutator_mono (shortRoot_le_M X Y Z) (shortRoot_le_M X' Y' Z)).trans hMM.le

end Short

section Positive

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

theorem positive_relations (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    ⁅shortRoot R A A₀ P', shortRoot R P ⁅A₀, P'⁆ A⁆ ≤ P' ∧
    Commuting (shortRoot R A A₀ P') P' ∧ Commuting (shortRoot R A A₀ P') A ∧
    Commuting (shortRoot R P' ⁅A₀, P⁆ A) P ∧ Commuting (shortRoot R P ⁅A₀, P'⁆ A) P ∧
    ⁅P, P'⁆ = A ∧ Commuting P A ∧
    ⁅shortRoot R P' ⁅A₀, P⁆ A, shortRoot R P ⁅A₀, P'⁆ A⁆ ≤ A ∧
    Commuting (shortRoot R P' ⁅A₀, P⁆ A) P' ∧ Commuting (shortRoot R P' ⁅A₀, P⁆ A) A ∧
    Commuting (shortRoot R P ⁅A₀, P'⁆ A) P' ∧ Commuting (shortRoot R P ⁅A₀, P'⁆ A) A ∧
    Commuting P' A := by
  have := h.finite
  have hR := h.root
  have hPR : P ∈ R := hP.2.1
  have hP'R : P' ∈ R := hP'.2.1
  obtain ⟨hQP, hQA₀, hQ'P', hQ'A₀, ⟨-, hcPP'⟩, ⟨hsAQ, hcAQ⟩, ⟨hsAQ', hcAQ'⟩, -, hQ'Ω, hQΩ⟩ :=
    apartment h hH hA hA₀ hP hP' hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ :=
    ⟨mem_lambdaSet_comm hA hP.1, hA, hsAQ'.symm⟩
  have hL : 3 ≤ (linesThrough R P).ncard := (ncard_linesThrough_eq h hA hPR) ▸ h3
  have h2ab : shortRoot R P ⁅A₀, P'⁆ A = shortRoot R ⁅A₀, P'⁆ P P' := by
    rw [shortRoot_eq_shortRoot h hH hT hPR hL hQ'Ω hAs, Subgroup.commutator_comm ⁅A₀, P'⁆ A,
      hcAQ']
  have hAP' : P' = ⁅⁅A₀, P'⁆, A⁆ := by rw [Subgroup.commutator_comm, hcAQ']
  refine ⟨?_, commuting_shortRoot_mid h hP'R, commuting_shortRoot_left A A₀ P', ?_,
    commuting_shortRoot_left P _ A, hcPP', hP.1.1.2.2.symm, commutator_shortRoot_le h hA,
    commuting_shortRoot_left P' _ A, commuting_shortRoot_mid h hA, ?_,
    commuting_shortRoot_mid h hA, hP'.1.1.2.2.symm⟩
  · rw [h2ab]
    exact commutator_shortRoot_le h hP'R
  · have := commuting_shortRoot_mid' (X := P') (Y := ⁅A₀, P⁆) h hA
    rwa [Subgroup.commutator_comm ⁅A₀, P⁆ A, hcAQ] at this
  · have := commuting_shortRoot_mid' (X := P) (Y := ⁅A₀, P'⁆) h hA
    rwa [← hAP'] at this

end Positive

end CaseH

end CFSG.Timmesfeld.ARS
