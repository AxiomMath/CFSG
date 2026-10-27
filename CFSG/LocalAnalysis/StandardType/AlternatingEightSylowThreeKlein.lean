module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmNumerics
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHopf
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.StandardType

namespace AlternatingEightSylow

open Equiv Equiv.Perm

private abbrev s8a : Perm (Fin 8) := swap 0 1 * swap 1 2

private abbrev s8b : Perm (Fin 8) := swap 3 4 * swap 4 5

private abbrev s8c : Perm (Fin 8) := swap 0 1 * swap 2 6

private abbrev s8d : Perm (Fin 8) := swap 0 2 * swap 1 6

def sylowThree : Subgroup (Perm (Fin 8)) :=
  Subgroup.closure {swap 0 1 * swap 1 2, swap 3 4 * swap 4 5}

def kleinFour : Subgroup (Perm (Fin 8)) :=
  Subgroup.closure {swap 0 1 * swap 2 6, swap 0 2 * swap 1 6}

private theorem sylowThree_eq :
    sylowThree = Subgroup.closure ({s8a, s8b} : Set (Perm (Fin 8))) := rfl

private theorem kleinFour_eq :
    kleinFour = Subgroup.closure ({s8c, s8d} : Set (Perm (Fin 8))) := rfl

theorem card_sylowThree : Nat.card sylowThree = 9 := by
  rw [sylowThree_eq]
  let F : Fin 3 × Fin 3 → Perm (Fin 8) := fun ij => s8a ^ (ij.1 : ℕ) * s8b ^ (ij.2 : ℕ)
  have hmul : ∀ ij kl : Fin 3 × Fin 3, F (ij + kl) = F ij * F kl := by decide
  have hinv : ∀ ij : Fin 3 × Fin 3, F (-ij) = (F ij)⁻¹ := by decide
  have hinj : Function.Injective F := by decide
  have hmem : ∀ ij, F ij ∈ Subgroup.closure ({s8a, s8b} : Set (Perm (Fin 8))) := by
    intro ij
    exact mul_mem
      (pow_mem (Subgroup.subset_closure (by simp)) (ij.1 : ℕ))
      (pow_mem (Subgroup.subset_closure (by simp)) (ij.2 : ℕ))
  have hrange : Set.range F =
      (Subgroup.closure ({s8a, s8b} : Set (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨ij, rfl⟩
      exact hmem ij
    · intro x hx
      refine Subgroup.closure_induction (p := fun z _ => z ∈ Set.range F) ?_ ?_ ?_ ?_ hx
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact ⟨(1, 0), by decide⟩
        · exact ⟨(0, 1), by decide⟩
      · exact ⟨(0, 0), by decide⟩
      · intro x y _ _ ihx ihy
        rcases ihx with ⟨ij, rfl⟩
        rcases ihy with ⟨kl, rfl⟩
        exact ⟨ij + kl, hmul ij kl⟩
      · intro x _ ihx
        rcases ihx with ⟨ij, rfl⟩
        exact ⟨-ij, hinv ij⟩
  have hbij : Function.Bijective (fun ij : Fin 3 × Fin 3 =>
      (⟨F ij, hmem ij⟩ : Subgroup.closure ({s8a, s8b} : Set (Perm (Fin 8))))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : Perm (Fin 8)) ∈ Set.range F := by
        rw [hrange]; exact y.2
      rcases hy with ⟨ij, hij⟩
      exact ⟨ij, Subtype.ext hij⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  norm_num

theorem card_kleinFour : Nat.card kleinFour = 4 := by
  rw [kleinFour_eq]
  let G : Fin 2 × Fin 2 → Perm (Fin 8) := fun ij => s8c ^ (ij.1 : ℕ) * s8d ^ (ij.2 : ℕ)
  have hmul : ∀ ij kl : Fin 2 × Fin 2, G (ij + kl) = G ij * G kl := by decide
  have hinv : ∀ ij : Fin 2 × Fin 2, G (-ij) = (G ij)⁻¹ := by decide
  have hinj : Function.Injective G := by decide
  have hmem : ∀ ij, G ij ∈ Subgroup.closure ({s8c, s8d} : Set (Perm (Fin 8))) := by
    intro ij
    exact mul_mem
      (pow_mem (Subgroup.subset_closure (by simp)) (ij.1 : ℕ))
      (pow_mem (Subgroup.subset_closure (by simp)) (ij.2 : ℕ))
  have hrange : Set.range G =
      (Subgroup.closure ({s8c, s8d} : Set (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨ij, rfl⟩
      exact hmem ij
    · intro x hx
      refine Subgroup.closure_induction (p := fun z _ => z ∈ Set.range G) ?_ ?_ ?_ ?_ hx
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact ⟨(1, 0), by decide⟩
        · exact ⟨(0, 1), by decide⟩
      · exact ⟨(0, 0), by decide⟩
      · intro x y _ _ ihx ihy
        rcases ihx with ⟨ij, rfl⟩
        rcases ihy with ⟨kl, rfl⟩
        exact ⟨ij + kl, hmul ij kl⟩
      · intro x _ ihx
        rcases ihx with ⟨ij, rfl⟩
        exact ⟨-ij, hinv ij⟩
  have hbij : Function.Bijective (fun ij : Fin 2 × Fin 2 =>
      (⟨G ij, hmem ij⟩ : Subgroup.closure ({s8c, s8d} : Set (Perm (Fin 8))))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : Perm (Fin 8)) ∈ Set.range G := by
        rw [hrange]; exact y.2
      rcases hy with ⟨ij, hij⟩
      exact ⟨ij, Subtype.ext hij⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  norm_num

theorem kleinFour_le_alternatingGroup : kleinFour ≤ alternatingGroup (Fin 8) := by
  rw [kleinFour_eq, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Equiv.Perm.mem_alternatingGroup.mpr (by decide)
  · exact Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem sylowThree_le_normalizer_kleinFour :
    sylowThree ≤ Subgroup.normalizer (kleinFour : Set (Perm (Fin 8))) := by
  have hc_mem : s8c ∈ kleinFour := by
    rw [kleinFour_eq]; exact Subgroup.subset_closure (by simp)
  have hd_mem : s8d ∈ kleinFour := by
    rw [kleinFour_eq]; exact Subgroup.subset_closure (by simp)
  have conj_map (g : Perm (Fin 8)) (hc : g * s8c * g⁻¹ ∈ kleinFour)
      (hd : g * s8d * g⁻¹ ∈ kleinFour) :
      ∀ k ∈ kleinFour, g * k * g⁻¹ ∈ kleinFour := by
    intro k hk
    rw [kleinFour_eq] at hk
    refine Subgroup.closure_induction (p := fun z _ => g * z * g⁻¹ ∈ kleinFour) ?_ ?_ ?_ ?_ hk
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hc
      · exact hd
    · simpa using Subgroup.one_mem kleinFour
    · intro x y _ _ ihx ihy
      have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [hxy]
      exact mul_mem ihx ihy
    · intro x _ ihx
      have hx' : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [hx']
      exact inv_mem ihx
  rw [sylowThree_eq, Subgroup.le_normalizer_iff]
  intro h hh k hk
  have key : ∀ h ∈ Subgroup.closure ({s8a, s8b} : Set (Perm (Fin 8))),
      (∀ k ∈ kleinFour, h * k * h⁻¹ ∈ kleinFour) ∧
      (∀ k ∈ kleinFour, h⁻¹ * k * h ∈ kleinFour) := by
    intro h hh
    refine Subgroup.closure_induction (p := fun z _ =>
      (∀ k ∈ kleinFour, z * k * z⁻¹ ∈ kleinFour) ∧
      (∀ k ∈ kleinFour, z⁻¹ * k * z ∈ kleinFour)) ?_ ?_ ?_ ?_ hh
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · refine ⟨?_, ?_⟩
        · exact conj_map s8a
            (by rw [show s8a * s8c * s8a⁻¹ = s8c * s8d by decide]
                exact mul_mem hc_mem hd_mem)
            (by rw [show s8a * s8d * s8a⁻¹ = s8c by decide]
                exact hc_mem)
        · exact conj_map s8a⁻¹
            (by rw [show s8a⁻¹ * s8c * (s8a⁻¹)⁻¹ = s8d by decide]
                exact hd_mem)
            (by rw [show s8a⁻¹ * s8d * (s8a⁻¹)⁻¹ = s8c * s8d by decide]
                exact mul_mem hc_mem hd_mem)
      · refine ⟨?_, ?_⟩
        · exact conj_map s8b
            (by rw [show s8b * s8c * s8b⁻¹ = s8c by decide]
                exact hc_mem)
            (by rw [show s8b * s8d * s8b⁻¹ = s8d by decide]
                exact hd_mem)
        · exact conj_map s8b⁻¹
            (by rw [show s8b⁻¹ * s8c * (s8b⁻¹)⁻¹ = s8c by decide]
                exact hc_mem)
            (by rw [show s8b⁻¹ * s8d * (s8b⁻¹)⁻¹ = s8d by decide]
                exact hd_mem)
    · refine ⟨?_, ?_⟩ <;> intro k hk <;> simpa using hk
    · intro x y _ _ ihx ihy
      obtain ⟨hx1, hx2⟩ := ihx
      obtain ⟨hy1, hy2⟩ := ihy
      refine ⟨?_, ?_⟩
      · intro k hk
        have h1 : y * k * y⁻¹ ∈ kleinFour := hy1 k hk
        have h2 : x * (y * k * y⁻¹) * x⁻¹ ∈ kleinFour := hx1 _ h1
        simpa [mul_assoc] using h2
      · intro k hk
        have h1 : x⁻¹ * k * x ∈ kleinFour := hx2 k hk
        have h2 : y⁻¹ * (x⁻¹ * k * x) * y ∈ kleinFour := hy2 _ h1
        simpa [mul_assoc] using h2
    · intro x _ ihx
      obtain ⟨hx1, hx2⟩ := ihx
      exact ⟨hx2, hx1⟩
  exact (key h hh).1 k hk

theorem exists_two_subgroup_normalized_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup (Perm (Fin 8))} (hS : IsPGroup p S) (hcard : p ^ 2 ≤ Nat.card S) :
    ∃ V : Subgroup (Perm (Fin 8)), V ≠ ⊥ ∧ IsPGroup 2 V ∧ V ≤ alternatingGroup (Fin 8) ∧
      S ≤ Subgroup.normalizer (V : Set (Perm (Fin 8))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have h40 : Nat.card (Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hk2 : 2 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  have hdvd : Nat.card S ∣ 40320 := by
    have h := Subgroup.card_subgroup_dvd_card S
    rwa [h40] at h
  have hp3 : p = 3 :=
    eq_three_of_sq_dvd_forty_thousand hp hp2 ((pow_dvd_pow p hk2).trans (hk ▸ hdvd))
  subst hp3
  have hk2' : k ≤ 2 := by
    by_contra h
    exact not_three_pow_three_dvd_forty_thousand
      ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans (hk ▸ hdvd))
  have hS9 : Nat.card S = 9 := by
    rw [hk, show k = 2 by omega]
    norm_num
  have hE : IsPGroup 3 sylowThree := IsPGroup.of_card (n := 2) (by rw [card_sylowThree]; norm_num)
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  have hsyl_card : ∀ R : Sylow 3 (Perm (Fin 8)), Nat.card R ≤ 9 := by
    intro R
    obtain ⟨m, hm⟩ := R.isPGroup'.exists_card_eq
    have hRdvd : Nat.card R ∣ 40320 := by
      have h := Subgroup.card_subgroup_dvd_card (R : Subgroup (Perm (Fin 8)))
      rwa [h40] at h
    have hm2 : m ≤ 2 := by
      by_contra h
      exact not_three_pow_three_dvd_forty_thousand
        ((pow_dvd_pow 3 (by omega : 3 ≤ m)).trans (hm ▸ hRdvd))
    rw [hm]
    calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 9 := by norm_num
  have hSeq : S = (P : Subgroup _) :=
    Subgroup.eq_of_le_of_card_ge hSP (by rw [hS9]; exact hsyl_card P)
  have hEeq : sylowThree = (Q : Subgroup _) :=
    Subgroup.eq_of_le_of_card_ge hEQ (by rw [card_sylowThree]; exact hsyl_card Q)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 8)) Q P
  have hconj : ∀ s ∈ S, g⁻¹ * s * g ∈ sylowThree := by
    intro s hs
    rw [hEeq]
    have hsP : s ∈ (P : Subgroup (Perm (Fin 8))) := hSeq ▸ hs
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsP
    simpa [MulAut.smul_def, MulAut.conj_apply, map_inv] using hsP
  have hK2 : IsPGroup 2 kleinFour :=
    IsPGroup.of_card (n := 2) (by rw [card_kleinFour]; norm_num)
  have hnorm := sylowThree_le_normalizer_kleinFour
  refine ⟨kleinFour.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hk : swap (0 : Fin 8) 1 * swap 2 6 ∈ kleinFour := Subgroup.subset_closure (by simp)
    have hmem : g * (swap (0 : Fin 8) 1 * swap 2 6) * g⁻¹ ∈
        kleinFour.comap (MulAut.conj g⁻¹).toMonoidHom := by
      simpa [MulAut.conj_apply, mul_assoc] using hk
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : swap (0 : Fin 8) 1 * swap 2 6 = 1 := by
      have h2 := congrArg (fun y => g⁻¹ * y * g) hmem
      simpa [mul_assoc] using h2
    exact absurd h1 (by decide)
  · intro v
    have hv : g⁻¹ * (v : Perm (Fin 8)) * g ∈ kleinFour := by
      have := v.2
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    obtain ⟨n, hn⟩ := hK2 ⟨_, hv⟩
    have h1 : (g⁻¹ * (v : Perm (Fin 8)) * g) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 := conj_pow (a := g⁻¹) (b := (v : Perm (Fin 8))) (i := 2 ^ n)
    rw [inv_inv] at h3
    rw [h3] at h1
    have h2 := congrArg (fun y => g * y * g⁻¹) h1
    have hpow : (v : Perm (Fin 8)) ^ (2 ^ n) = 1 := by simpa [mul_assoc] using h2
    exact ⟨n, Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hpow)⟩
  · intro v hv
    have hv' : g⁻¹ * v * g ∈ kleinFour := by
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using hv
    have hA := kleinFour_le_alternatingGroup hv'
    have hA' : g * (g⁻¹ * v * g) * g⁻¹ ∈ alternatingGroup (Fin 8) :=
      (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ hA g
    simpa [mul_assoc] using hA'
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have he := hnorm (hconj s hs)
    rw [Subgroup.mem_normalizer_iff] at he
    have hiff := he (g⁻¹ * v * g)
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv] at hiff ⊢
    rw [hiff]
    group

theorem le_seven_of_prime_dvd_forty_thousand {p : ℕ} (hp : p.Prime) (hd : p ∣ 40320) : p ≤ 7 := by
  have h40 : (40320 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [h40] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd1 | hd1
  · rcases (Nat.Prime.dvd_mul hp).1 hd1 with hd2 | hd2
    · rcases (Nat.Prime.dvd_mul hp).1 hd2 with hd3 | hd3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd3)
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd2
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd1
    omega

theorem card_le_nine_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup (Perm (Fin 8))} (hS : IsPGroup p S) : Nat.card S ≤ 9 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have h40 : Nat.card (Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdvd : p ^ k ∣ 40320 := by
    have h := Subgroup.card_subgroup_dvd_card S
    rwa [h40, hk] at h
  rw [hk]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · simp
    · have hp7 : p ≤ 7 := le_seven_of_prime_dvd_forty_thousand hp (by simpa using hdvd)
      simp only [pow_one]
      omega
  · have hp3 : p = 3 :=
      eq_three_of_sq_dvd_forty_thousand hp hp2 ((pow_dvd_pow p hk2).trans hdvd)
    subst hp3
    have hk2' : k ≤ 2 := by
      by_contra h
      exact not_three_pow_three_dvd_forty_thousand
        ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd)
    have hk2'' : k = 2 := by omega
    subst hk2''
    norm_num

end AlternatingEightSylow

end CFSG.StandardType
