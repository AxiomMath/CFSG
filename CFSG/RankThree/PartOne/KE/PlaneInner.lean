module

public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement IsMulCommutative

theorem planeLocalCoreOdd_of_inner_centralized {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥)
    (hOut : ∀ A : Subgroup (MulAut C), IsPGroup p A →
      A ≤ (MulAut.conj : C →* MulAut C).range)
    (hV : ∀ A₀ : Subgroup C, Nat.card A₀ = p ^ 2 → (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) →
      (∀ a ∈ A₀, a ^ p = 1) → ∀ x ∈ A₀, x ≠ 1 →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
          ∀ v ∈ V, ∀ a ∈ A₀, a * (v : C) = (v : C) * a)
    (hI : ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : C →* MulAut C).range → Odd (Nat.card ↥(autThetaT p B A))) :
    PlaneLocalCoreOdd p C := by
  intro B hB A hAB hA hcard t htA ht1
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hAin : A ≤ (MulAut.conj : C →* MulAut C).range := hOut A (IsPGroup.of_card hcard)
  have hIntinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  obtain ⟨x, rfl⟩ := hAin htA
  have hxp : orderOf x = p := by
    have htp : orderOf (MulAut.conj x : MulAut C) = p := orderOf_eq_prime (hpow _ htA) ht1
    exact ((orderOf_injective _ hIntinj x).symm).trans htp
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → autThetaT p B A ≤
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set (MulAut C))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  have hAM : A ≤ M := by
    intro a ha
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hAB ha, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact congrArg Subtype.val (mul_comm' (⟨_, htA⟩ : A) ⟨a, ha⟩)
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSnormalizer : ∀ m ∈ M, m ∈ Subgroup.normalizer (S : Set (MulAut C)) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSnorm m hm s hs, fun hs => ?_⟩
    have := hSnorm m⁻¹ (inv_mem hm) _ hs
    simpa [mul_assoc] using this
  have hSp : ¬ p ∣ Nat.card S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).2.2.1
    rw [hS, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
    exact h
  have hSA : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs => hSnorm a (hAM ha) s hs
  have hUS : (⁅S, A⁆ : Subgroup (MulAut C)) ≤ S := by
    refine Subgroup.commutator_le.2 fun s hs a ha => ?_
    have h := hSA a ha s⁻¹ (inv_mem hs)
    have e : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hs h
  have hUinn : (⁅S, A⁆ : Subgroup (MulAut C)) ≤ (MulAut.conj : C →* MulAut C).range := by
    refine Subgroup.commutator_le.2 fun s hs a ha => ?_
    obtain ⟨a₀, rfl⟩ := hAin ha
    have e : ⁅s, MulAut.conj a₀⁆ = (s * MulAut.conj a₀ * s⁻¹) * (MulAut.conj a₀)⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    have hs' : s * MulAut.conj a₀ * s⁻¹ ∈ (MulAut.conj : C →* MulAut C).range := by
      have := (innerNormal C).conj_mem (MulAut.conj a₀) ⟨a₀, rfl⟩ s
      exact this
    exact mul_mem hs' (inv_mem ⟨a₀, rfl⟩)
  obtain ⟨V, hVn, hVs, hVl⟩ := inner_core_preimage hp hC hB x
  set A₀ : Subgroup C := A.comap (MulAut.conj : C →* MulAut C) with hA₀
  have hA₀map : A₀.map (MulAut.conj : C →* MulAut C) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hA₀comm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := by
    intro a ha b hb
    apply hIntinj
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : A) ⟨_, hb⟩)
  have hA₀exp : ∀ a ∈ A₀, a ^ p = 1 := fun a ha => by
    apply hIntinj
    rw [map_pow, map_one]
    exact hpow _ ha
  have hxA₀ : x ∈ A₀ := htA
  have hx1 : x ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have hAcent : ∀ q ∈ S ⊓ (MulAut.conj : C →* MulAut C).range, ∀ a ∈ A, a * q = q * a := by
    intro q hq a ha
    have hq' : q ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range := by
      rw [← hM, ← hS]
      exact hq
    obtain ⟨v, hvV, rfl⟩ := hVl q hq'
    obtain ⟨a₀, rfl⟩ := hAin ha
    have ha₀ : a₀ ∈ A₀ := ha
    have h := hV A₀ hA₀card hA₀comm hA₀exp x hxA₀ hx1 V hVn hVs v hvV a₀ ha₀
    rw [← map_mul, ← map_mul, h]
  have hU1 : (⁅S, A⁆ : Subgroup (MulAut C)) = ⊥ := by
    have hidem : (⁅⁅S, A⁆, A⁆ : Subgroup (MulAut C)) = ⁅S, A⁆ :=
      CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent hp A S
        (IsPGroup.of_card hcard) hSp (fun a ha => hSnormalizer a (hAM ha))
    rw [← hidem]
    refine le_bot_iff.1 (Subgroup.commutator_le.2 fun u hu a ha => ?_)
    have hu' : u ∈ S ⊓ (MulAut.conj : C →* MulAut C).range := Subgroup.mem_inf.2 ⟨hUS hu, hUinn hu⟩
    rw [Subgroup.mem_bot, commutatorElement_def]
    have h := hAcent u hu' a ha
    calc u * a * u⁻¹ * a⁻¹ = (u * a) * (u⁻¹ * a⁻¹) := by group
      _ = (a * u) * (u⁻¹ * a⁻¹) := by rw [← h]
      _ = 1 := by group
  have hIS : autThetaT p B A ≤ S := by
    have := hthetaT_le (MulAut.conj x) htA ht1
    rwa [← hM, ← hS] at this
  have hplane : autPlaneProduct p B A (MulAut.conj x) = ⁅S, A⁆ ⊔ autThetaT p B A := by
    rw [autPlaneProduct, ← hM, ← hS]
  rw [hplane, hU1, bot_sup_eq]
  exact (hI B hB A hAB hA hcard hAin).not_two_dvd_nat

end CFSG.RankThree.PartOne.KE
