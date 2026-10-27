module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmall
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriBridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriMod
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem TrialityMarked.exists_line {X : Type} [Group X] {s : X}
    {ε : X →* Equiv.Perm (Fin 3)} (h : TrialityMarked X s ε) :
    ∃ a b t : X, IsConj s a ∧ IsConj s b ∧ IsConj s t ∧ orderOf (a * b) = 3 ∧
      orderOf (t * a) = 3 ∧ orderOf (t * b) = 3 ∧ orderOf (t * (b * a * b⁻¹)) = 3 := by
  obtain ⟨a, b, t, ha, hb, ht, -, -, hab, hta, htb, htf⟩ := h.config
  exact ⟨a, b, t, ha, hb, ht, hab, hta, htb, htf⟩

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}


private theorem trialityHyp_of_cent_line (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : X}
    (hs : s ∈ barSub (kSub V H E) φ V) (hs1 : s ≠ 1)
    (hcent : ∀ r : X, IsConj s r → Subgroup.centralizer ({r} : Set X) =
      Subgroup.closure ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({r} : Set X) : Set X)))
    (hline : ∃ a b t : X, IsConj s a ∧ IsConj s b ∧ IsConj s t ∧ orderOf (a * b) = 3 ∧
      orderOf (t * a) = 3 ∧ orderOf (t * b) = 3 ∧ orderOf (t * (b * a * b⁻¹)) = 3) :
    TrialityHyp φ {k : ↥(kSub V H E) | (k : G) ∈ dSet V H E} s := by
  obtain ⟨hord, -, hnc, -⟩ := seven_eleven_small_hyps h hφ hS hs hs1
  have hsq : s ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one s
  have hker_eq : φ.ker = (pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E))).symm
  have himage : φ '' {k : ↥(kSub V H E) | (k : G) ∈ dSet V H E} = {x : X | IsConj s x} :=
    barSet_dSet_eq_setOf_isConj h.toHyp73 h.transitive hφ hS hs hs1
  exact ⟨hφ.surjective, hker2, hsq, hnc, himage, hcent, hline⟩

theorem not_hasTrialityMarked (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : X}
    (hs : s ∈ barSub (kSub V H E) φ V) (hs1 : s ≠ 1) : ¬ HasTrialityMarked X s := by
  rintro ⟨ε, hε⟩
  obtain ⟨A, _, _, _, ρ, hI, hker⟩ := exists_trialityRep h hφ hS
  exact false_of_isNilpotent_rep
    (trialityHyp_of_cent_line h hφ hS hs hs1 hε.centralizer_gen
      (TrialityMarked.exists_line hε)) ρ hI hker

theorem not_isTrialityOddTransp (hMarked : TrialityMarkedInput) (h : Hyp711 V H E) {X : Type}
    [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : X}
    (hs : s ∈ barSub (kSub V H E) φ V) (hs1 : s ≠ 1) : ¬ IsTrialityOddTransp X s :=
  fun hT => not_hasTrialityMarked h hφ hS hs hs1 (hMarked X s hT)

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
