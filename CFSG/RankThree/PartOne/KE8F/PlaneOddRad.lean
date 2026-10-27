module

public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE
open scoped Pointwise commutatorElement IsMulCommutative

theorem odd_card_of_ker_odd {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hker : Odd (Nat.card f.ker)) (hH : Odd (Nat.card H)) : Odd (Nat.card G) := by
  have h1 : Nat.card f.ker * f.ker.index = Nat.card G := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have h3 : Nat.card f.range ∣ Nat.card H := Subgroup.card_subgroup_dvd_card f.range
  rw [← h1, h2]
  exact hker.mul (Odd.of_dvd_nat hH h3)

theorem inner_core_card_odd {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hV : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
      ¬ p ∣ Nat.card V → Odd (Nat.card V)) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range)) := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set Int : C →* MulAut C := MulAut.conj with hInt
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup C, D = Subgroup.centralizer ({x} : Set C) := ⟨_, rfl⟩
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSsol : Group.IsSolvable S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).1
    rw [hS, inSubgroup]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p M) M.subtype
        M.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    rw [hD] at hd
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  have hYSD : S.comap Int ≤ D := by
    intro y hy
    have hyM : Int y ∈ M := hSM hy
    rw [hM] at hyM
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyM).2 (Int x) rfl
    rw [hD]
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hinj (by rw [map_mul, map_mul]; exact h1.symm))
  have hVnormal : ((S.comap Int).subgroupOf D).Normal := ⟨fun v hv d => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    change Int ((d : C) * (v : C) * (d : C)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSnorm _ (hIntD d d.2) _ hv⟩
  let f : ((S.comap Int).subgroupOf D) →* S :=
    ((Int.comp D.subtype).comp ((S.comap Int).subgroupOf D).subtype).codRestrict S
      fun v => Subgroup.mem_subgroupOf.1 v.2
  have hfi : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext (hinj (congrArg Subtype.val hab)))
  have hVsol : Group.IsSolvable ((S.comap Int).subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective (f := f) hfi
  have hSp : ¬ p ∣ Nat.card S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).2.2.1
    rw [hS, inSubgroup, Subgroup.card_map_of_injective M.subtype_injective]
    exact h
  have hVp : ¬ p ∣ Nat.card ((S.comap Int).subgroupOf D) :=
    fun h => hSp (h.trans (Subgroup.card_dvd_of_injective f hfi))
  have hVodd : Odd (Nat.card ((S.comap Int).subgroupOf D)) := by
    rw [hD] at hVnormal hVsol hVp ⊢
    exact hV _ hVnormal hVsol hVp
  have hlift : ∀ q ∈ S ⊓ Int.range, ∃ v : (S.comap Int).subgroupOf D, Int (v : D) = q := by
    intro q hq
    obtain ⟨hqS, y, hy⟩ := Subgroup.mem_inf.1 hq
    have hyS : y ∈ S.comap Int := by
      rw [Subgroup.mem_comap, hy]
      exact hqS
    exact ⟨⟨⟨y, hYSD hyS⟩, Subgroup.mem_subgroupOf.2 hyS⟩, hy⟩
  let φ : ((S.comap Int).subgroupOf D) → ↥(S ⊓ Int.range) := fun v =>
    ⟨Int (v : D), Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 v.2, ⟨(v : D), rfl⟩⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (Subtype.ext (hinj (congrArg Subtype.val hab))), fun q => ?_⟩
    obtain ⟨v, hv⟩ := hlift q.1 q.2
    exact ⟨v, Subtype.ext hv⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  exact hVodd

theorem planeLocalCoreOdd_of_odd_radicals {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥)
    (hV : ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → ¬ p ∣ Nat.card V → Odd (Nat.card V))
    (hout : Odd (Nat.card (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range) :
    PlaneLocalCoreOdd p C := by
  intro B hB A hAB hA hcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have htp : orderOf t = p := orderOf_eq_prime (hpow t htA) ht1
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → autThetaT p B A ≤
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({a} : Set (MulAut C))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  by_cases htn : t ∈ (MulAut.conj : C →* MulAut C).range
  · obtain ⟨x, rfl⟩ := htn
    have hxp : orderOf x = p :=
      ((orderOf_injective _ (conj_injective_of_center_eq_bot hC) x).symm).trans htp
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
    have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
      intro m hm s hs
      rw [hS] at hs ⊢
      obtain ⟨s', hs', rfl⟩ := hs
      refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
      exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
    have hin := inner_core_card_odd hp hC hB (hV x hxp)
    rw [← hM, ← hS] at hin
    have hSodd : Odd (Nat.card S) := by
      let f : S →* Outer C := (QuotientGroup.mk' (inner C)).comp S.subtype
      refine odd_card_of_ker_odd f ?_ hout
      have e : f.ker ≃ ↥(S ⊓ (MulAut.conj : C →* MulAut C).range) :=
        { toFun := fun k => ⟨k.1.1, Subgroup.mem_inf.2 ⟨k.1.2,
            (QuotientGroup.eq_one_iff (N := inner C) (k.1 : MulAut C)).1 k.2⟩⟩
          invFun := fun q => ⟨⟨q.1, (Subgroup.mem_inf.1 q.2).1⟩,
            (QuotientGroup.eq_one_iff (N := inner C) (q.1 : MulAut C)).2
              (Subgroup.mem_inf.1 q.2).2⟩
          left_inv := fun k => rfl
          right_inv := fun q => rfl }
      rw [Nat.card_congr e]
      exact hin
    have hIS : autThetaT p B A ≤ S := by
      have := hthetaT_le (MulAut.conj x) htA ht1
      rwa [← hM, ← hS] at this
    have hUS : ⁅S, A⁆ ≤ S := by
      refine Subgroup.commutator_le.2 fun s hs a ha => ?_
      have h1 : a * s⁻¹ * a⁻¹ ∈ S := hSnorm a (hAM ha) s⁻¹ (inv_mem hs)
      have e : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem hs h1
    have hle : autPlaneProduct p B A (MulAut.conj x) ≤ S := by
      rw [autPlaneProduct, ← hM, ← hS]
      exact sup_le hUS hIS
    exact (Odd.of_dvd_nat hSodd (Subgroup.card_dvd_of_le hle)).not_two_dvd_nat
  · have hθt := hcore B hB t (hAB htA) htn htp
    have hT : autThetaT p B A = ⊥ :=
      le_bot_iff.1 ((hthetaT_le t htA ht1).trans hθt.le)
    have hplane : autPlaneProduct p B A t = ⊥ := by
      rw [autPlaneProduct, hθt, Subgroup.commutator_bot_left, hT, sup_bot_eq]
    rw [hplane, Subgroup.card_bot]
    omega

end CFSG.RankThree.PartOne.KE8F
