module

public import CFSG.RankThree.PartOne.KE.CoreInner
public import CFSG.RankThree.PartOne.KE.PlaneOdd

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE (aut_mul_conj_mul_inv fixes_of_commute_conj
  commutes_of_quasisimple_embedding odd_card_inf_range_of_solvable conj_injective_of_center_eq_bot)
open scoped Pointwise commutatorElement

@[expose] def OddSolvNormal (D : Type*) [Group D] : Prop :=
  ∀ V : Subgroup D, V.Normal → Group.IsSolvable V → Odd (Nat.card V)

theorem oddSolvNormal_of_mulEquiv {D D' : Type*} [Group D] [Group D'] (e : D ≃* D')
    (h : OddSolvNormal D') : OddSolvNormal D := by
  intro V hVn hVs
  have h1 := h (V.map e.toMonoidHom) (Subgroup.Normal.map hVn _ e.surjective)
    (by
      have := hVs
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap V)
        (MonoidHom.subgroupMap_surjective _ V))
  rwa [Subgroup.card_map_of_injective e.injective] at h1

@[expose] def centralizerEquivOfInjective {C Γ : Type*} [Group C] [Group Γ] (f : C →* Γ)
    (hf : Function.Injective f) (x : C) :
    Subgroup.centralizer ({x} : Set C) ≃*
      ↥(f.range ⊓ Subgroup.centralizer ({f x} : Set Γ)) :=
  MulEquiv.ofBijective
    (((f.comp (Subgroup.centralizer ({x} : Set C)).subtype).codRestrict
      (f.range ⊓ Subgroup.centralizer ({f x} : Set Γ)) fun d => by
        refine Subgroup.mem_inf.2 ⟨⟨d, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h := Subgroup.mem_centralizer_singleton_iff.1 d.2
        change f (d : C) * f x = f x * f (d : C)
        rw [← map_mul, ← map_mul, h]) : _)
    ⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun z => by
      obtain ⟨⟨d, hdz⟩, hz⟩ := Subgroup.mem_inf.1 z.2
      have hd : d ∈ Subgroup.centralizer ({x} : Set C) := by
        refine Subgroup.mem_centralizer_singleton_iff.2 (hf ?_)
        have h := Subgroup.mem_centralizer_singleton_iff.1 hz
        rw [map_mul, map_mul, hdz]
        exact h
      exact ⟨⟨d, hd⟩, Subtype.ext hdz⟩⟩

theorem odd_card_of_involutions_in {G : Type*} [Group G] [Finite G] (S R : Subgroup G)
    (hS : Odd (Nat.card ↥(S ⊓ R))) (h : ∀ η ∈ S, η ^ 2 = 1 → η ∈ R) :
    Odd (Nat.card S) := by
  by_contra hnodd
  have h2 : 2 ∣ Nat.card S := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨η, hη⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hη2 : (η : G) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hη, pow_orderOf_eq_one]
    rfl
  have hηR : (η : G) ∈ R := h η η.2 hη2
  have hmem : (η : G) ∈ S ⊓ R := Subgroup.mem_inf.2 ⟨η.2, hηR⟩
  have hord : orderOf (⟨(η : G), hmem⟩ : ↥(S ⊓ R)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hη]
  have hdvd : 2 ∣ Nat.card ↥(S ⊓ R) := hord ▸ orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.2 hS) (even_iff_two_dvd.2 hdvd)

theorem core_odd_of_involutions_inner {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hsolv : OddSolvNormal (Subgroup.centralizer ({x} : Set C)))
    (hinv : ∀ η ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))),
      η ^ 2 = 1 → η ∈ (MulAut.conj : C →* MulAut C).range) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))))) :=
  odd_card_of_involutions_in _ _ (odd_card_inf_range_of_solvable hp hC hB hsolv) hinv

theorem core_fixes_perfectResidual {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hq : CFSG.IsQuasisimple ((CFSG.perfectResidual (Subgroup.centralizer ({x} : Set C))).map
      (Subgroup.centralizer ({x} : Set C)).subtype))
    {η : MulAut C} (hη : η ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)))) :
    η x = x ∧ ∀ d ∈ (CFSG.perfectResidual (Subgroup.centralizer ({x} : Set C))).map
      (Subgroup.centralizer ({x} : Set C)).subtype, η d = d := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set D : Subgroup C := Subgroup.centralizer ({x} : Set C) with hD
  set D₀ : Subgroup C := (CFSG.perfectResidual D).map D.subtype with hD₀
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM] at hη
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS] at hη
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
  have hmx : ∀ m ∈ M, m x = x := by
    intro m hm
    rw [hM] at hm
    refine fixes_of_commute_conj hC m x ?_
    have h := Subgroup.mem_centralizer_iff.1 hm.2 (MulAut.conj x) rfl
    exact h.symm
  have hmD : ∀ m ∈ M, ∀ d ∈ D, m d ∈ D := by
    intro m hm d hd
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h := Subgroup.mem_centralizer_singleton_iff.1 hd
    calc m d * x = m d * m x := by rw [hmx m hm]
      _ = m (d * x) := (map_mul m d x).symm
      _ = m (x * d) := by rw [h]
      _ = m x * m d := map_mul m x d
      _ = x * m d := by rw [hmx m hm]
  have hD₀D : D₀ ≤ D := Subgroup.map_subtype_le _
  have hmD₀ : ∀ m ∈ M, ∀ d ∈ D₀, m d ∈ D₀ := by
    intro m hm d hd
    obtain ⟨d₀, hd₀', rfl⟩ := hd
    have hd₀ : d₀ ∈ CFSG.perfectResidual D := hd₀'
    let f : D →* D := ((m : C →* C).comp D.subtype).codRestrict D fun e => hmD m hm e e.2
    have hfd : f d₀ ∈ CFSG.perfectResidual D := by
      rw [CFSG.perfectResidual, Subgroup.mem_iInf] at hd₀ ⊢
      exact fun n => map_derivedSeries_le_derivedSeries f n ⟨d₀, hd₀ n, rfl⟩
    exact ⟨f d₀, hfd, rfl⟩
  set P : Subgroup (MulAut C) := D₀.map (MulAut.conj : C →* MulAut C) with hP
  have hPq : CFSG.IsQuasisimple P :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective D₀ (MulAut.conj : C →* MulAut C) hinj) hq
  have hPM : P ≤ M := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 (hD₀D hd)).symm
  set ψ : M →* MulAut C := M.subtype with hψ
  have hψinj : Function.Injective ψ := M.subtype_injective
  have hPψ : P ≤ ψ.range := by
    intro u hu
    exact ⟨⟨u, hPM hu⟩, rfl⟩
  have hnorm : ∀ m : M, ∀ u ∈ P, ψ m * u * (ψ m)⁻¹ ∈ P := by
    rintro ⟨m, hm⟩ _ ⟨d, hd, rfl⟩
    refine ⟨m d, hmD₀ m hm d hd, ?_⟩
    change MulAut.conj (m d) = m * MulAut.conj d * m⁻¹
    rw [aut_mul_conj_mul_inv]
  have hVn : (S.subgroupOf M).Normal := ⟨fun s hs m => by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hSnorm m m.2 s hs⟩
  have hVs : Group.IsSolvable (S.subgroupOf M) := by
    have e : S.subgroupOf M ≃* S := Subgroup.subgroupOfEquivOfLe hSM
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hcomm := commutes_of_quasisimple_embedding ψ hψinj P hPψ hPq hnorm (S.subgroupOf M)
  refine ⟨hmx η (hSM hη), fun d hd => ?_⟩
  have h1 : ψ ⟨η, hSM hη⟩ * MulAut.conj d = MulAut.conj d * ψ ⟨η, hSM hη⟩ :=
    hcomm ⟨η, hSM hη⟩ (Subgroup.mem_subgroupOf.2 hη) _ ⟨d, hd, rfl⟩
  apply hinj
  rw [← aut_mul_conj_mul_inv]
  have h2 : η * MulAut.conj d = MulAut.conj d * η := h1
  rw [h2, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.RankThree.PartOne.KETw3
