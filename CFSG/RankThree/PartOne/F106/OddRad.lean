module

public import CFSG.RankThree.PartOne.F106.KFact
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def OddRadFive : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    CFSG.Blueprint.EvenLieType T → Census3.TheoremThreeList T →
    ∀ β : MulAut T, orderOf β = 5 →
      Odd (Nat.card ↥(solvableRadical
        ↥(perfectResidual ↥((β : T →* T).eqLocus (MonoidHom.id T)))))

theorem fixed_conj_aux {Kg : Type} [Group Kg] {γ : MulAut Kg}
    {β : MulAut (Kg ⧸ Subgroup.center Kg)}
    (hβ : ∀ k : Kg, β (k : Kg ⧸ Subgroup.center Kg) = ((γ k : Kg) : Kg ⧸ Subgroup.center Kg))
    {x : Kg ⧸ Subgroup.center Kg} (hx : β x = x) {k : Kg} (hk : γ k = k) :
    ∃ k' : Kg, γ k' = k' ∧
      (k' : Kg ⧸ Subgroup.center Kg) = x * (k : Kg ⧸ Subgroup.center Kg) * x⁻¹ := by
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  rw [hβ] at hx
  have hz : x'⁻¹ * γ x' ∈ Subgroup.center Kg := QuotientGroup.eq.mp hx.symm
  have hz' : γ x' = x' * (x'⁻¹ * γ x') := by group
  refine ⟨x' * k * x'⁻¹, ?_, by simp⟩
  rw [map_mul, map_mul, map_inv, hk, hz']
  have hc := Subgroup.mem_center_iff.mp hz
  have h1 : x' * (x'⁻¹ * γ x') * k * (x' * (x'⁻¹ * γ x'))⁻¹ = x' * k * x'⁻¹ := by
    have e : (x'⁻¹ * γ x') * k = k * (x'⁻¹ * γ x') := (hc k).symm
    calc x' * (x'⁻¹ * γ x') * k * (x' * (x'⁻¹ * γ x'))⁻¹
        = x' * ((x'⁻¹ * γ x') * k) * (x'⁻¹ * γ x')⁻¹ * x'⁻¹ := by group
      _ = x' * (k * (x'⁻¹ * γ x')) * (x'⁻¹ * γ x')⁻¹ * x'⁻¹ := by rw [e]
      _ = x' * k * x'⁻¹ := by group
  exact h1

theorem kFactFive_of_oddRadFive (h : OddRadFive) : KFactFive := by
  intro X _ _ K c hc hKq hEven hList hord P hPQ hPmem y hy hy2 k hk
  have hp5 : (5 : ℕ).Prime := by norm_num
  have hKperf : Group.IsPerfect ↥K := hKq.1
  set γ : MulAut ↥K := K.normalizerMonoidHom ⟨c, hc⟩ with hγ
  have hγk : ∀ g : ↥K, ((γ g : ↥K) : X) = c * g * c⁻¹ :=
    fun g => Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨c, hc⟩ g
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K γ with hβdef
  have hβo : orderOf β = 5 := by
    rw [hβdef, orderOf_injective _
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥K) γ]
    exact hord
  have hβ : ∀ g : ↥K,
      β (g : ↥K ⧸ Subgroup.center ↥K) = ((γ g : ↥K) : ↥K ⧸ Subgroup.center ↥K) :=
    CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk ↥K γ
  have hT := h (↥K ⧸ Subgroup.center ↥K) hKq.2.1 hKq.2.2 hEven hList β hβo
  set Cβ : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
    (β : (↥K ⧸ Subgroup.center ↥K) →* (↥K ⧸ Subgroup.center ↥K)).eqLocus
      (MonoidHom.id (↥K ⧸ Subgroup.center ↥K)) with hCβdef
  have hmemCβ : ∀ x : ↥K ⧸ Subgroup.center ↥K, x ∈ Cβ ↔ β x = x := fun x => Iff.rfl
  set Q : Subgroup X := K ⊓ Subgroup.centralizer ({c} : Set X) with hQdef
  have hQK : Q ≤ K := inf_le_left
  have hQc : ∀ g ∈ Q, c * g = g * c := fun g hg =>
    Subgroup.mem_centralizer_iff.mp hg.2 c rfl
  have hγQ : ∀ g : ↥Q, γ (Subgroup.inclusion hQK g) = Subgroup.inclusion hQK g := by
    intro g
    apply Subtype.ext
    rw [hγk]
    show c * (g : X) * c⁻¹ = g
    rw [hQc g g.2]
    group
  let φ : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' _
  have hψmem : ∀ g : ↥Q, φ (Subgroup.inclusion hQK g) ∈ Cβ := by
    intro g
    rw [hmemCβ]
    have := hβ (Subgroup.inclusion hQK g)
    rw [hγQ g] at this
    exact this
  let ψ : ↥Q →* ↥Cβ := (φ.comp (Subgroup.inclusion hQK)).codRestrict Cβ hψmem
  have hψc : ∀ g : ↥Q, ((ψ g : ↥Cβ) : ↥K ⧸ Subgroup.center ↥K) =
      ((Subgroup.inclusion hQK g : ↥K) : ↥K ⧸ Subgroup.center ↥K) := fun g => rfl
  have hRnorm : (ψ.range).Normal := by
    refine ⟨?_⟩
    rintro _ ⟨g, rfl⟩ ⟨x, hx⟩
    obtain ⟨k', hk'γ, hk'⟩ :=
      fixed_conj_aux hβ ((hmemCβ x).mp hx) (k := Subgroup.inclusion hQK g) (hγQ g)
    have hk'Q : (k' : X) ∈ Q := by
      refine ⟨k'.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      have h1 := congrArg Subtype.val hk'γ
      rw [hγk] at h1
      calc c * (k' : X) = (c * k' * c⁻¹) * c := by group
        _ = (k' : X) * c := by rw [h1]
    refine ⟨⟨(k' : X), hk'Q⟩, ?_⟩
    apply Subtype.ext
    show ((ψ ⟨(k' : X), hk'Q⟩ : ↥Cβ) : ↥K ⧸ Subgroup.center ↥K) =
      x * ((ψ g : ↥Cβ) : ↥K ⧸ Subgroup.center ↥K) * x⁻¹
    rw [hψc, hψc, ← hk']
    rfl
  set θQ : Subgroup ↥Q := aschbacherSolvableCore 5 ↥Q with hθQdef
  have hθQn : θQ.Normal := aschbacherSolvableCore_normal 5 ↥Q
  have hθQs : Group.IsSolvable ↥θQ :=
    (solvable_prime_complement_core_characterization (H := ↥Q) hp5).1
  set N1 : Subgroup ↥Cβ := θQ.map ψ with hN1def
  have hN1s : Group.IsSolvable ↥N1 :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective ψ θQ)
  have hN1sn : N1.IsSubnormal := by
    have h1 : (θQ.map ψ.rangeRestrict).IsSubnormal :=
      Subgroup.IsSubnormal.map (MonoidHom.rangeRestrict_surjective ψ) hθQn.isSubnormal
    have h2 := h1.trans' hRnorm.isSubnormal
    rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2
  have hPsn : (P.subgroupOf Q).IsSubnormal := hPmem.2.1
  have hcore := inSubgroup_core_eq_inf_of_subgroupOf_isSubnormal hp5 hPQ hPsn
  have hyP : y ∈ P := by
    obtain ⟨yP, -, rfl⟩ := hy
    exact yP.2
  have hyQ : y ∈ inSubgroup (aschbacherSolvableCore 5) Q := by
    rw [hcore] at hy
    exact hy.2
  obtain ⟨yQ, hyQθ, hyQe⟩ := hyQ
  have hyQe' : ((yQ : ↥Q) : X) = y := hyQe
  have hnN1 : ψ yQ ∈ N1 := Subgroup.mem_map_of_mem ψ hyQθ
  have hyQP : yQ ∈ P.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf, hyQe']
    exact hyP
  have hPperf : Group.IsPerfect ↥(P.subgroupOf Q) := hPmem.1
  have hψPperf : Group.IsPerfect ↥((P.subgroupOf Q).map ψ) := Group.IsPerfect.map ψ
  have hnD : ψ yQ ∈ perfectResidual ↥Cβ :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual _ hψPperf
      (Subgroup.mem_map_of_mem ψ hyQP)
  set D : Subgroup ↥Cβ := perfectResidual ↥Cβ with hDdef
  have hsubD : (N1.subgroupOf D).IsSubnormal := hN1sn.subgroupOf
  have hsolD : Group.IsSolvable ↥(N1.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (D.subtype.comp (N1.subgroupOf D).subtype).codRestrict N1 fun x => x.2)
      (fun a b hab => by
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1))
  have hrad : N1.subgroupOf D ≤ solvableRadical ↥D :=
    (CFSG.RankThree.solvable_radical_subnormal_intersection hsubD).2 hsolD
  have hmem : (⟨ψ yQ, hnD⟩ : ↥D) ∈ solvableRadical ↥D := hrad hnN1
  have hsq : (⟨ψ yQ, hnD⟩ : ↥D) ^ 2 = 1 := by
    apply Subtype.ext
    show ψ yQ ^ 2 = 1
    rw [← map_pow]
    have : yQ ^ 2 = 1 := Subtype.ext (by simpa [hyQe'] using hy2)
    rw [this, map_one]
  have hord1 : orderOf (⟨ψ yQ, hnD⟩ : ↥D) = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard (solvableRadical ↥D) hmem
    have h2 : orderOf (⟨ψ yQ, hnD⟩ : ↥D) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · exact h1
    · rw [h2'] at hdvd
      exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hT)
  have hψ1 : ψ yQ = 1 := by
    have := orderOf_eq_one_iff.mp hord1
    exact congrArg (fun z : ↥D => ((z : ↥Cβ))) this
  have hyc : Subgroup.inclusion hQK yQ ∈ Subgroup.center ↥K := by
    have h1 : φ (Subgroup.inclusion hQK yQ) = 1 := congrArg Subtype.val hψ1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨k, hk⟩)
  exact (show k * y = y * k by simpa [hyQe'] using h3).symm

end CFSG.RankThree.PartOne.F106
