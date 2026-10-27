module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Dih
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47OrdB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_conj_eq {M V₀ V : Subgroup G} (hN : normalizer (V : Set G) = M)
    (hN₀ : M ≤ normalizer (V₀ : Set G)) {g h : G}
    (hgh : conjSubgroup V g = conjSubgroup V h) :
    conjSubgroup M g = conjSubgroup M h ∧ conjSubgroup V₀ g = conjSubgroup V₀ h := by
  have hconj : conjSubgroup V (g * h⁻¹) = V := by
    have h' := congrArg (fun X => conjSubgroup X h⁻¹) hgh
    rw [conjSubgroup_conjSubgroup V g h⁻¹, E3.conjSubgroup_conj_inv V h] at h'
    exact h'
  have hmem : g * h⁻¹ ∈ M := by
    rw [← hN]
    exact conjSubgroup_eq_iff_mem_normalizer.mp hconj
  have key : ∀ A : Subgroup G, g * h⁻¹ ∈ normalizer (A : Set G) →
      conjSubgroup A g = conjSubgroup A h := by
    intro A hA
    have hA' : conjSubgroup A (g * h⁻¹) = A := conjSubgroup_eq_iff_mem_normalizer.mpr hA
    have hg_eq : g = (g * h⁻¹) * h := by group
    calc conjSubgroup A g = conjSubgroup A ((g * h⁻¹) * h) :=
          congrArg (fun t => conjSubgroup A t) hg_eq
      _ = conjSubgroup (conjSubgroup A (g * h⁻¹)) h := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup A h := by rw [hA']
  exact ⟨key M (Subgroup.le_normalizer hmem), key V₀ (hN₀ hmem)⟩

theorem s16c1_G47_inCalO1_of_mem {n : ℕ} {M V₀ V : Subgroup G}
    (hN : normalizer (V : Set G) = M) (hN₀ : M ≤ normalizer (V₀ : Set G)) {g : G}
    (hg : conjSubgroup V g ∈ calO1 n M V₀ V) : InCalO1 n M V₀ V g := by
  rw [calO1, Set.mem_ofPred_eq] at hg
  obtain ⟨g', hgg', hO⟩ := hg
  obtain ⟨hMeq, hV₀eq⟩ := s16c1_G47_conj_eq hN hN₀ hgg'
  simp only [InCalO1, InCalO, OFirst, ODual, OneFirst, OneDual] at hO ⊢
  rw [hgg', hMeq, hV₀eq]
  exact hO

theorem s16c1_G47_A7 (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) {z : G} (hz : z ∈ V)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z)) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) {w : G} (hwV : w ∈ V)
    (hw : w ∉ pCoreOf 2 (centralizer ({z} : Set G)))
    (hnc : ⁅w, h⁻¹ * w * h⁆ ∉ pCoreOf 2 (centralizer ({z} : Set G))) :
    V ⊓ conjSubgroup D.M h = uOne V z ∧
      conjSubgroup V h ⊓ D.M = conjSubgroup (uOne V z) h := by
  let H := centralizer ({z} : Set G)
  let Q := pCoreOf 2 H
  have hQM : Q ≤ D.M := s16c1_pCoreOf_le_M D hSyl
  obtain ⟨hnot1, hnot2⟩ := s16c1_not_le_of_noncomm hV hz hcard hh hwV hw hnc
  have hUleV : uOne V z ≤ V := inf_le_left
  have hrel : (uOne V z).relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_card (H := uOne V z) (K := V)
    rw [inf_eq_left.2 hUleV, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hdich : ∀ X : Subgroup G, uOne V z ≤ X → X ≤ V → X = uOne V z ∨ X = V := by
    intro X hUX hXV
    have hmul := Subgroup.relIndex_mul_relIndex (uOne V z) X V hUX hXV
    rw [hrel] at hmul
    have hdvd : X.relIndex V ∣ 2 := Dvd.intro_left _ hmul
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact Or.inr (le_antisymm hXV (Subgroup.relIndex_eq_one.mp h1))
    · rw [h1] at hmul
      have h2 : (uOne V z).relIndex X = 1 := by omega
      exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h2) hUX)
  have key : ∀ k ∈ H, ¬ V ≤ conjSubgroup D.M k → V ⊓ conjSubgroup D.M k = uOne V z := by
    intro k hk hnotV
    have hUle : uOne V z ≤ V ⊓ conjSubgroup D.M k := by
      refine le_inf inf_le_left ?_
      calc uOne V z ≤ Q := inf_le_right
        _ = conjSubgroup Q k := (s16c1_conjSubgroup_pCoreOf_self H hk).symm
        _ ≤ conjSubgroup D.M k := E3.conjSubgroup_mono_left k hQM
    rcases hdich _ hUle inf_le_left with h' | h'
    · exact h'
    · exact absurd (h' ▸ inf_le_right) hnotV
  refine ⟨key h hh hnot2, ?_⟩
  have hnot' : ¬ V ≤ conjSubgroup D.M h⁻¹ := by
    intro hle
    apply hnot1
    calc conjSubgroup V h ≤ conjSubgroup (conjSubgroup D.M h⁻¹) h :=
          E3.conjSubgroup_mono_left h hle
      _ = D.M := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have h2 := key h⁻¹ (H.inv_mem hh) hnot'
  have hinf : conjSubgroup (V ⊓ conjSubgroup D.M h⁻¹) h = conjSubgroup V h ⊓ D.M := by
    ext x
    simp only [mem_conjSubgroup_iff, Subgroup.mem_inf]
    rw [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group]
  rw [← hinf, h2]

theorem s16c1_G47_odd_data {M V₀ V Q : Subgroup G} {g : G} (hO : InCalOStar 1 M V₀ V g)
    (hU : V ⊓ conjSubgroup M g ≤ Q) (hB : conjSubgroup V g ⊓ M ≤ Q) {w w' : G} (hw : w ∈ V)
    (hw' : w' ∈ conjSubgroup V g) (hww : w * w = 1) (hw'w' : w' * w' = 1) (hwQ : w ∉ Q)
    (hw'Q : w' ∉ Q) :
    ∃ K : Subgroup G, ∃ _ : (K.subgroupOf (V ⊔ conjSubgroup V g)).Normal,
      (K : Set G) = ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) *
          ((V ⊓ conjSubgroup M g : Subgroup G) : Set G) ∧
        K ≤ Q ∧ ∃ n : ℕ, Odd n ∧ ∀ j : ℕ, (w * w') ^ j ∈ K ↔ n ∣ j := by
  obtain ⟨hO1, K, hKn, hset, hshape, -⟩ := hO
  haveI := hKn
  have hKQ : K ≤ Q := by
    intro x hx
    have hx' : x ∈ (K : Set G) := hx
    rw [hset] at hx'
    obtain ⟨b, hb, u, hu, rfl⟩ := Set.mem_mul.1 hx'
    exact Q.mul_mem (hB hb) (hU hu)
  have hr : twoRank (↥(V ⊔ conjSubgroup V g) ⧸ K.subgroupOf (V ⊔ conjSubgroup V g)) ≤ 1 := by
    have h1 := hshape.2
    have h2 : E3.mQuot V (conjSubgroup M g) ≤ 1 := hO1.1.2.1
    omega
  obtain ⟨n, hn, hdvd⟩ := s16c1_G47_order_data hr (Subgroup.mem_sup_left hw)
    (Subgroup.mem_sup_right hw') hww hw'w' (fun h => hwQ (hKQ h)) (fun h => hw'Q (hKQ h))
  exact ⟨K, hKn, hset, hKQ, n, hn, hdvd⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
