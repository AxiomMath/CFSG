module

public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.GroupTheory.SteinbergCDCyclicNormalHall
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms

variable {C : Type*} [Group C]

theorem conj_injective_of_center_eq_bot (hC : Subgroup.center C = ⊥) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut C => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rwa [hC, Subgroup.mem_bot] at hxc

theorem not_le_range_conj_of_cyclic [Finite C] {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.center C = ⊥) (hcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q)
    {A : Subgroup (MulAut C)} (hA : ∀ a ∈ A, a ^ p = 1) (hcard : Nat.card A = p ^ 2) :
    ¬ A ≤ (MulAut.conj : C →* MulAut C).range := by
  intro hle
  have hinj := conj_injective_of_center_eq_bot hC
  set c : C →* MulAut C := MulAut.conj with hc
  set Q : Subgroup C := A.comap c with hQ
  have hQp : IsPGroup p Q := by
    intro q
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hinj
    have h1 := hA (c q) q.2
    simpa [map_pow] using h1
  have hQc := hcyc Q hQp
  have hAeq : Q.map c = A := Subgroup.map_comap_eq_self hle
  have hAc : IsCyclic A := by
    rw [← hAeq]
    exact isCyclic_of_surjective (c.subgroupMap Q) (c.subgroupMap_surjective Q)
  have hdvd : Nat.card A ∣ p := by
    rw [← hAc.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    apply Subtype.ext
    simpa using hA g g.2
  rw [hcard] at hdvd
  have hp1 := hp.one_lt
  have := Nat.le_of_dvd hp.pos hdvd
  nlinarith

@[expose] noncomputable def outerHom (M : Subgroup (MulAut C)) : M →* Outer C :=
  (QuotientGroup.mk' (inner C)).comp M.subtype

theorem mem_ker_outerHom {M : Subgroup (MulAut C)} (m : M) :
    m ∈ (outerHom M).ker ↔ (m : MulAut C) ∈ (MulAut.conj : C →* MulAut C).range := by
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff (N := inner C) (m : MulAut C)

theorem isCyclic_ker_outerHom (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hx : IsCyclic (Subgroup.centralizer ({x} : Set C))) :
    IsCyclic (outerHom
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)))).ker := by
  have hinj := conj_injective_of_center_eq_bot hC
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  have hmem : ∀ y ∈ Subgroup.centralizer ({x} : Set C), (MulAut.conj y : MulAut C) ∈ M := by
    intro y hy
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul, hy x rfl]
  let g0 : Subgroup.centralizer ({x} : Set C) →* M :=
    ((MulAut.conj : C →* MulAut C).comp (Subgroup.centralizer ({x} : Set C)).subtype).codRestrict M
      (fun y => hmem y y.2)
  let g : Subgroup.centralizer ({x} : Set C) →* (outerHom M).ker :=
    g0.codRestrict (outerHom M).ker (fun y => (mem_ker_outerHom (g0 y)).2 ⟨y, rfl⟩)
  refine isCyclic_of_surjective g ?_
  intro d
  obtain ⟨y, hy⟩ := (mem_ker_outerHom d.1).1 d.2
  have hyc : y ∈ Subgroup.centralizer ({x} : Set C) := by
    have hdM : (d.1 : MulAut C) ∈
        B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := by
      rw [← hM]
      exact d.1.2
    have hd := (Subgroup.mem_inf.1 hdM).2
    rw [Subgroup.mem_centralizer_iff] at hd ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply hinj
    rw [map_mul, map_mul, hy]
    exact hd _ rfl
  refine ⟨⟨y, hyc⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hy

theorem card_commutator_dvd_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card (commutator G) ∣ Nat.card (commutator H) := by
  have h1 : (commutator G).map f ≤ commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h2 := Subgroup.card_dvd_of_le h1
  rwa [Subgroup.card_map_of_injective hf] at h2

theorem odd_card_commutator_quotient_ker_outerHom
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C))) (M : Subgroup (MulAut C)) :
    Odd (Nat.card (commutator (M ⧸ (outerHom M).ker))) := by
  have h := card_commutator_dvd_of_injective (QuotientGroup.kerLift (outerHom M))
    (QuotientGroup.kerLift_injective _)
  exact Nat.not_even_iff_odd.1 fun h2 => hout ((even_iff_two_dvd.1 h2).trans h)

theorem odd_card_commutator_of_cyclic_ker [Finite C]
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C))) {M S A : Subgroup (MulAut C)}
    (hS : S ≤ M) (hA : A ≤ M) (hAodd : Odd (Nat.card A))
    (hD : IsCyclic (outerHom M).ker) : Odd (Nat.card (⁅S, A⁆ : Subgroup (MulAut C))) := by
  obtain ⟨_, -, -, -, hB0⟩ := cyclic_normal_odd_derived_quotient_normal_hall_odd (M := M)
    (outerHom M).ker hD (odd_card_commutator_quotient_ker_outerHom hout M)
  have hAodd' : Odd (Nat.card (A.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]
  have h := (hB0 (A.subgroupOf M) hAodd' (S.subgroupOf M)).2.2
  have hmap : (⁅S.subgroupOf M, A.subgroupOf M⁆).map M.subtype = ⁅S, A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hS,
      Subgroup.map_subgroupOf_eq_of_le hA]
  rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective]
  exact h

theorem native_plane_of_cyclic_centralizers_abstract [Finite C] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hC : Subgroup.center C = ⊥)
    (hcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q)
    (hcent : ∀ x : C, orderOf x = p → IsCyclic (Subgroup.centralizer {x}))
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range) :
    ∀ B : Subgroup (MulAut C), (MulAut.conj : C →* MulAut C).range ≤ B →
      ∀ A : Subgroup (MulAut C), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
        ¬ A ≤ (MulAut.conj : C →* MulAut C).range ∧
        autThetaT p B A = ⊥ ∧
        ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : C →* MulAut C).range →
            inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) = ⊥ ∧
              autPlaneProduct p B A t = ⊥) := by
  intro B hB A hAB hA hcard
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hnot : ¬ A ≤ (MulAut.conj : C →* MulAut C).range :=
    not_le_range_conj_of_cyclic hp hC hcyc hpow hcard
  obtain ⟨b, hbA, hbn⟩ : ∃ b ∈ A, b ∉ (MulAut.conj : C →* MulAut C).range := by
    by_contra hcon
    refine hnot fun a ha => ?_
    by_contra h
    exact hcon ⟨a, ha, h⟩
  have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
  have hθb := hcore B hB b (hAB hbA) hbn (orderOf_eq_prime (hpow b hbA) hb1)
  have hθT : autThetaT p B A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    simp only [autThetaT, Subgroup.mem_iInf] at hy
    have h1 := hy b hbA hb1
    rw [hθb] at h1
    exact h1
  refine ⟨hnot, hθT, fun t htA ht1 => ?_⟩
  have htp : orderOf t = p := orderOf_eq_prime (hpow t htA) ht1
  by_cases htn : t ∈ (MulAut.conj : C →* MulAut C).range
  · obtain ⟨x, rfl⟩ := htn
    have hxp : orderOf x = p :=
      ((orderOf_injective _ (conj_injective_of_center_eq_bot hC) x).symm).trans htp
    obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
        B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
    have hAM : A ≤ M := by
      intro a ha
      rw [hM]
      refine Subgroup.mem_inf.2 ⟨hAB ha, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact congrArg Subtype.val (mul_comm' (⟨_, htA⟩ : A) ⟨a, ha⟩)
    have hSM : inSubgroup (aschbacherSolvableCore p) M ≤ M := Subgroup.map_subtype_le _
    have hAodd : Odd (Nat.card A) := by
      rw [hcard]
      exact Odd.pow (hp.odd_of_ne_two (by omega))
    have hD : IsCyclic (outerHom M).ker := by
      rw [hM]
      exact isCyclic_ker_outerHom hC hB (hcent x hxp)
    have hodd := odd_card_commutator_of_cyclic_ker hout hSM hAM hAodd hD
    have hplane : autPlaneProduct p B A (MulAut.conj x) =
        ⁅inSubgroup (aschbacherSolvableCore p) M, A⁆ := by
      rw [autPlaneProduct, hθT, sup_bot_eq, hM]
    rw [hplane]
    exact ⟨hodd.not_two_dvd_nat, fun h => absurd ⟨x, rfl⟩ h⟩
  · have hθt := hcore B hB t (hAB htA) htn htp
    have hplane : autPlaneProduct p B A t = ⊥ := by
      rw [autPlaneProduct, hθt, Subgroup.commutator_bot_left, hθT, sup_bot_eq]
    refine ⟨?_, fun _ => ⟨hθt, hplane⟩⟩
    rw [hplane, Subgroup.card_bot]
    omega

theorem planeLocalCoreOdd_of_cyclic_centralizers_abstract [Finite C] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hC : Subgroup.center C = ⊥)
    (hcyc : ∀ Q : Subgroup C, IsPGroup p Q → IsCyclic Q)
    (hcent : ∀ x : C, orderOf x = p → IsCyclic (Subgroup.centralizer {x}))
    (hout : ¬ 2 ∣ Nat.card (commutator (Outer C)))
    (hcore : LocalCoreTrivialOn p fun α : MulAut C =>
      α ∉ (MulAut.conj : C →* MulAut C).range) :
    PlaneLocalCoreOdd p C := fun B hB A hAB hA hcard t htA ht1 =>
  ((native_plane_of_cyclic_centralizers_abstract hp hp3 hC hcyc hcent hout hcore B hB A hAB hA
    hcard).2.2 t htA ht1).1

end CFSG.RankThree.PartOne.KE
