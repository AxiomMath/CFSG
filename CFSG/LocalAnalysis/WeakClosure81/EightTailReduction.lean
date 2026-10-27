module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
public import CFSG.LocalAnalysis.WeakClosure81.EightSixHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeInHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightFive
public import CFSG.LocalAnalysis.WeakClosure81.EightSixMain
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped Pointwise
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1 W3Thm88)

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem85TwoKT (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
      (∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ H →
          U ∈ omegaHIn V H ∨ ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) ∨
        ∃ m n : ℕ, 3 < m ∧ (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
          KBarCenterShape V H T (fun X _ => IsPSUGp X m n))

@[expose] def W3Lem85TwoBad (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T U : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
    (∃ g : G, U = conjSubgroup V g) → U ≤ T → (∀ h ∈ H, U ≠ conjSubgroup V h) →
    (¬ ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ conjSubgroup V h, u * v = v * u) →
    U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥ →
    (∀ u ∈ U, u ≠ 1 → eSub V H T ⊓ Subgroup.centralizer (U : Set G) =
      eSub V H T ⊓ Subgroup.centralizer ({u} : Set G)) →
    (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) →
      ∃ m n : ℕ, 3 < m ∧ (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
        KBarCenterShape V H T (fun X _ => IsPSUGp X m n))

@[expose] def W3Lem85ThreeFirst (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
      Hyp85Three V H T →
        H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G))

@[expose] def Shape86WeakC (V H T : Subgroup G) : Prop :=
  (¬ ∃ m n : ℕ, 3 < m ∧ (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
      KBarCenterShape V H T (fun X _ => IsPSUGp X m n))) ∧
    ∀ x ∈ H, conjSubgroup V x ≤ T → conjSubgroup V x = V

@[expose] def W3Shape86C (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
    E3.wClos V 0 T ≠ V →
    (CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) →
      Hyp85Three V H T ∨ Shape86Delta V H T ∨ Shape86WeakC V H T

theorem exists_bad_conjugate_in_sylow {V H T : Subgroup G} (hV7 : Hyp7 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hnot : ¬ ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ H →
      U ∈ omegaHIn V H ∨ ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) :
    ∃ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) ∧ U ≤ T ∧
      (∀ h ∈ H, U ≠ conjSubgroup V h) ∧
      ¬ ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ conjSubgroup V h, u * v = v * u := by
  push_neg at hnot
  obtain ⟨U₁, ⟨g, rfl⟩, hU₁H, hU₁Ω, W, hW, u, hu, w, hw, hne⟩ := hnot
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH hT
  have hU₁p : IsPGroup 2 (conjSubgroup V g) := (isElemAbelian_conjSubgroup' hV7.1 g).isPGroup
  obtain ⟨h, hh, hcj⟩ := exists_conj_le_of_isSylowTwoOf hTH hU₁H hU₁p
  have hcjeq : ∀ A : Subgroup G, cjSub h A = conjSubgroup A h⁻¹ := fun A => by
    ext x
    rw [mem_cjSub, mem_conjSubgroup_iff, inv_inv]
  have hmem : ∀ A : Subgroup G, ∀ x : G, x ∈ conjSubgroup A h⁻¹ ↔ h⁻¹ * x * h ∈ A := fun A x => by
    rw [mem_conjSubgroup_iff, inv_inv]
  refine ⟨conjSubgroup (conjSubgroup V g) h⁻¹, ⟨g * h⁻¹, conjSubgroup_conjSubgroup _ _ _⟩, ?_,
    ?_, ?_⟩
  · rw [← hcjeq]
    exact hcj
  · intro x hx heq
    apply hU₁Ω
    refine ⟨x * h, H.mul_mem hx hh, ?_⟩
    have h1 : conjSubgroup (conjSubgroup (conjSubgroup V g) h⁻¹) h = conjSubgroup V g := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    rw [← h1, heq, conjSubgroup_conjSubgroup]
  · intro hall
    obtain ⟨a, ha, rfl⟩ := hW
    have hu' : h * u * h⁻¹ ∈ conjSubgroup (conjSubgroup V g) h⁻¹ := by
      rw [hmem]
      simpa [mul_assoc] using hu
    have hw' : h * w * h⁻¹ ∈ conjSubgroup V (a * h⁻¹) := by
      rw [← conjSubgroup_conjSubgroup, hmem]
      simpa [mul_assoc] using hw
    have hc := hall (a * h⁻¹) (H.mul_mem ha (H.inv_mem hh)) _ hu' _ hw'
    apply hne
    have e : h * (u * w) * h⁻¹ = h * (w * u) * h⁻¹ := by
      calc h * (u * w) * h⁻¹ = (h * u * h⁻¹) * (h * w * h⁻¹) := by group
        _ = (h * w * h⁻¹) * (h * u * h⁻¹) := hc
        _ = h * (w * u) * h⁻¹ := by group
    simpa using e

theorem w3Lem85TwoKT_of_bad (hbad : W3Lem85TwoBad G) : W3Lem85TwoKT G := by
  intro V H T hV7 hH hH0 hT hKT
  by_cases halt : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ H →
      U ∈ omegaHIn V H ∨ ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u
  · exact Or.inl halt
  · right
    obtain ⟨U, hUconj, hUT, hUV, hUC⟩ := exists_bad_conjugate_in_sylow hV7 hH hT halt
    have hUH : U ≤ H := hUT.trans (hT.le.trans inf_le_left)
    have hVne : V ≠ ⊥ := by
      rintro rfl
      have h2 := hV7.2.1
      rw [Subgroup.card_bot] at h2
      omega
    obtain ⟨hbot, hcent⟩ := inf_centralizer_eSub_eq_bot_of_not_mem hV7.1 hV7.2.2 hVne hH hT
      hUconj hUH hUV hUC
    have hUN : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans (hT.le.trans inf_le_right)
    have hVU : V ≤ Subgroup.normalizer (U : Set G) := by
      obtain ⟨g, rfl⟩ := hUconj
      exact (le_normalizer_conj_iff hV7.1 hV7.2.2).mp hUN
    have hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u :=
      commute_of_le_normalizer_of_le_normalizer hV7.1 hV7.2.2 hUconj ⟨1, (conjSubgroup_one V).symm⟩
        hUN hVU
    exact hbad V H T U hV7 hH hH0 hT hKT hUconj hUT hUV hUC hbot hcent hcomm

private theorem pCoreOf_inf_le_pCoreOf_of_le' {K H : Subgroup G} (hKH : K ≤ H) :
    pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
  · intro x hx
    have hxH : x ∈ H := hKH hx
    have h1 : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (Subgroup.le_normalizer hxH)
    have h2 : x ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hx
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 y, h2 y]
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left

private theorem isSylowIn_two_restrict' {P K K' : Subgroup G} (hP : IsSylowIn 2 P K)
    (hPK' : P ≤ K') (hK'K : K' ≤ K) : IsSylowIn 2 P K' := by
  refine ⟨hPK', hP.isPGroup, fun h => hP.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K' K hPK' hK'K]
  exact h.mul_right _

theorem eight_six_one_of_eq_sup_C (h85two : W3Lem85TwoKT G) (h85three : W3Lem85ThreeFirst G)
    (hsh : W3Shape86C G) (hbor : W3Borel86 G) {V H T : Subgroup G} (hV7 : Hyp7 V)
    (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hKT : H = kGenIn V H ⊔ T)
    (hW : E3.wClos V 0 T ≠ V)
    (hcond : CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
  rcases hsh V H T hV7 hH hH0 hT hKT hW hcond with h3 | hdelta | ⟨hnot, hweak⟩
  · exact h85three V H T hV7 hH hH0 hT hKT h3
  · exact absurd hdelta (hbor V H T hV7 hH hH0 hT hKT hW hcond)
  · rcases h85two V H T hV7 hH hH0 hT hKT with halt | hex
    · have hno := eight_six_step_three_in hV7.1 hH hT hW
        (not_kGenIn_le_normalizer hV7.1 hH hH0 (hT.le.trans inf_le_right) hKT) hweak halt
      exact absurd hcond (by rintro (h | h); exacts [hno.1 h, hno.2 h])
    · exact absurd hex hnot

theorem eight_six_one_C (h83 : W3Lem83In G) (h85two : W3Lem85TwoKT G)
    (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G) (hbor : W3Borel86 G)
    {V H T : Subgroup G} (hV7 : Hyp7 V) (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hW : E3.wClos V 0 T ≠ V)
    (hcond : CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) ∧
      ¬ H ≤ Subgroup.normalizer (V : Set G) := by
  refine ⟨?_, fun hHM => hH0 (isCalH0_of_le_normalizer hV7.1 hH hHM)⟩
  obtain ⟨hA, hB⟩ := h83 V H T hV7 hH hH0 hT
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hTM : T ≤ Subgroup.normalizer (V : Set G) := hT.le.trans inf_le_right
  have hKH : kGenIn V H ≤ H := kGenIn_le_H hH.1
  have hH'H : kGenIn V H ⊔ T ≤ H := sup_le hKH hTH
  have hH' : IsCalH V (kGenIn V H ⊔ T) := isCalH_of_le hV7.1 hH hT le_sup_right hH'H
  have hT' : IsSylowIn 2 T ((kGenIn V H ⊔ T) ⊓ Subgroup.normalizer (V : Set G)) :=
    isSylowIn_two_restrict' hT (le_inf le_sup_right hTM) (inf_le_inf_right _ hH'H)
  have hH0' : ¬ IsCalH0 V (kGenIn V H ⊔ T) := fun h =>
    hH0 ⟨hH, ((le_inf h.2 (le_kGenIn_self V H)).trans
      (pCoreOf_inf_le_pCoreOf_of_le' (le_sup_left : kGenIn V H ≤ kGenIn V H ⊔ T))).trans
        (pCoreOf_kGenIn_le hH.1)⟩
  have hKC' : kGenIn V H ≤ conjClosure V (kGenIn V H ⊔ T) := by
    refine iSup₂_le fun k hk => ?_
    obtain ⟨a, ha, hka⟩ := hA k hk
    rw [hka]
    exact conjSubgroup_le_conjClosure V _ (Subgroup.mem_sup_left ha)
  have hKK' : kGenIn V H ≤ kGenIn V (kGenIn V H ⊔ T) := by
    refine iSup₂_le fun k hk => ?_
    obtain ⟨a, ha, hka⟩ := hA k hk
    rw [hka]
    exact conjSubgroup_le_kGenIn (hKC' ha)
  have hKT' : kGenIn V H ⊔ T = kGenIn V (kGenIn V H ⊔ T) ⊔ T :=
    le_antisymm (sup_le_sup_right hKK' T) (sup_le (kGenIn_le_H hH'.1) le_sup_right)
  have hcond' : CentralizersInM V (kGenIn V H ⊔ T) T ∨
      NormalizersInMTwo V (kGenIn V H ⊔ T) (E3.wClos V 0 T) :=
    hcond.imp
      (fun h z hz hzc hz1 => (inf_le_inf_right _ hH'H).trans (h z hz hzc hz1))
      (fun h X hX hXp hXle hXN => (inf_le_inf_right _ hH'H).trans (h X hX hXp hXle hXN))
  have hcore := eight_six_one_of_eq_sup_C h85two h85three hsh hbor hV7 hH' hH0' hT' hKT'
    hW hcond'
  set P : Subgroup G := (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
    (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) with hP
  have hH'P : kGenIn V H ⊔ T ≤ P :=
    hcore.le.trans (sup_le_sup (inf_le_inf_right _ hH'H) (inf_le_inf_right _ hH'H))
  have hKP : kGenIn V H ≤ P := le_sup_left.trans hH'P
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  have hx' : x ∈ (kGenIn V H : Set G) *
      ((H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) *
      ((H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) : Subgroup G) : Set G) := by
    rw [← hB]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, hk, m, hm, rfl⟩ := Set.mem_mul.mp ha
  exact P.mul_mem (P.mul_mem (hKP hk) (Subgroup.mem_sup_left hm)) (Subgroup.mem_sup_right hb)

theorem w3Lem86_1Two_of_kt_inputs (h85two : W3Lem85TwoKT G) (h85three : W3Lem85ThreeFirst G)
    (hsh : W3Shape86C G) (hbor : W3Borel86 G) : W3Lem86_1Two G :=
  fun V H T hV7 hH hH0 hT hW hcond =>
    eight_six_one_C w3Lem83In_holds h85two h85three hsh hbor hV7 hH hH0 hT hW hcond

theorem w3Lem86_1_of_kt_inputs (h85two : W3Lem85TwoKT G) (h85three : W3Lem85ThreeFirst G)
    (hsh : W3Shape86C G) (hbor : W3Borel86 G) : W3Lem86_1 G :=
  fun V H T hV7 hH hH0 hT hW hcond =>
    w3Lem86_1Two_of_kt_inputs h85two h85three hsh hbor V H T hV7 hH hH0 hT hW
      (hcond.imp_right NormalizersInM.toTwo)

theorem w3Lem86_1_of_tail_inputs (hbad : W3Lem85TwoBad G) (h85three : W3Lem85ThreeFirst G)
    (hsh : W3Shape86C G) (hbor : W3Borel86 G) : W3Lem86_1 G :=
  w3Lem86_1_of_kt_inputs (w3Lem85TwoKT_of_bad hbad) h85three hsh hbor

end CFSG.LocalAnalysis.WeakClosure81

end
