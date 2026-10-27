module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.Recognition.M12AscCoxInputs
public import Certificates.Certificate8083

public section

namespace CFSG.Quasithin

open CFSG.CosetTable

theorem coxA5_card_le :
    Finite (PG 5 (coxRels 5)) ∧ Nat.card (PG 5 (coxRels 5)) ≤ 720 :=
  Certificates.certificate8083

theorem lift_mk_coxWord {n : ℕ} {G : Type*} [Group G] (f : Fin n → G) (i j : Fin n) (m : ℕ) :
    FreeGroup.lift f (FreeGroup.mk (coxWord i j m)) = (f i * f j) ^ m := by
  induction m with
  | zero => simp [coxWord]
  | succ m ih =>
    have : coxWord i j (m + 1) = [(i, true), (j, true)] ++ coxWord i j m := by
      simp [coxWord, List.replicate_succ]
    rw [this, ← FreeGroup.mul_mk, map_mul, ih, pow_succ']
    simp [FreeGroup.lift_mk]

theorem lift_coxRels {n : ℕ} {G : Type*} [Group G] (f : Fin n → G)
    (hsq : ∀ i, f i * f i = 1)
    (hrel : ∀ i j : Fin n, i.val < j.val → (f i * f j) ^ coxExp i j = 1) :
    ∀ r ∈ (coxRels n), FreeGroup.lift f (FreeGroup.mk r) = 1 := by
  intro r hr
  unfold coxRels at hr
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at hr
  obtain ⟨i, j, hj⟩ := hr
  split_ifs at hj with hij hlt
  · obtain rfl := Option.some.inj hj
    rw [lift_mk_coxWord, pow_one, hij]
    exact hsq j
  · obtain rfl := Option.some.inj hj
    rw [lift_mk_coxWord]
    exact hrel i j hlt

theorem swap_coxeter_five :
    (∀ i : Fin 5, Equiv.swap i.castSucc i.succ * Equiv.swap i.castSucc i.succ = 1) ∧
    ∀ i j : Fin 5, i.val < j.val →
      (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ) ^ coxExp i j = 1 := by
  decide +kernel

theorem exists_perm_hom_of_coxeter
    {G : Type*} [Group G] (z : Fin 5 → G)
    (hsq : ∀ i, z i * z i = 1)
    (hrel : ∀ i j : Fin 5, i.val < j.val → (z i * z j) ^ coxExp i j = 1) :
    ∃ ρ : Equiv.Perm (Fin 6) →* G, ∀ i : Fin 5, ρ (Equiv.swap i.castSucc i.succ) = z i := by
  obtain ⟨hfin, hle⟩ := coxA5_card_le
  let ψ : PG 5 (coxRels 5) →* G := PresentedGroup.toGroup (f := z) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_coxRels z hsq hrel w hw)
  let σ : PG 5 (coxRels 5) →* Equiv.Perm (Fin 6) :=
    PresentedGroup.toGroup (f := fun i : Fin 5 => Equiv.swap i.castSucc i.succ) (by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      exact lift_coxRels _ swap_coxeter_five.1 swap_coxeter_five.2 w hw)
  have hσof : ∀ i : Fin 5, σ (PresentedGroup.of i) = Equiv.swap i.castSucc i.succ := fun i => by
    rw [PresentedGroup.toGroup.of]
  have hψof : ∀ i : Fin 5, ψ (PresentedGroup.of i) = z i := fun i => by
    rw [PresentedGroup.toGroup.of]
  have hsurj : Function.Surjective σ := by
    intro g
    have hg : g ∈ Submonoid.closure (Set.range fun i : Fin 5 => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ 5]
      trivial
    have hsub : Submonoid.closure (Set.range fun i : Fin 5 => Equiv.swap i.castSucc i.succ) ≤
        σ.range.toSubmonoid := by
      refine Submonoid.closure_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨PresentedGroup.of i, hσof i⟩
    exact hsub hg
  have hcardP : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hbij : Function.Bijective σ := hsurj.bijective_of_nat_card_le (by rw [hcardP]; exact hle)
  let e : PG 5 (coxRels 5) ≃* Equiv.Perm (Fin 6) := MulEquiv.ofBijective σ hbij
  refine ⟨ψ.comp e.symm.toMonoidHom, fun i => ?_⟩
  have : e.symm (Equiv.swap i.castSucc i.succ) = PresentedGroup.of i := by
    rw [MulEquiv.symm_apply_eq]
    exact (hσof i).symm
  show ψ (e.symm (Equiv.swap i.castSucc i.succ)) = z i
  rw [this, hψof]

theorem coxeterA5_injective {G : Type*} [Group G] (ρ : Equiv.Perm (Fin 6) →* G)
    (hne : ρ (Equiv.swap 0 1 * Equiv.swap 2 3) ≠ 1) : Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hker
  have hnt : Nontrivial ρ.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hker
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) hnt
  have hmem : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  exact hne (MonoidHom.mem_ker.1 (hle hmem))

theorem coxeterA5_order_five {G : Type*} [Group G] (z : Fin 5 → G)
    (hsq : ∀ i, z i * z i = 1)
    (hrel : ∀ i j : Fin 5, i.val < j.val → (z i * z j) ^ coxExp i j = 1)
    (h13 : z 0 * z 2 ≠ 1) : orderOf (z 0 * z 1 * z 2 * z 3) = 5 := by
  obtain ⟨ρ, hρ⟩ := exists_perm_hom_of_coxeter z hsq hrel
  have hinj : Function.Injective ρ := by
    apply coxeterA5_injective
    have h0 := hρ 0
    have h2 := hρ 2
    rw [map_mul]
    exact fun h => h13 (by
      have e0 : ρ (Equiv.swap 0 1) = z 0 := h0
      have e2 : ρ (Equiv.swap 2 3) = z 2 := h2
      rw [e0, e2] at h
      exact h)
  have hw : z 0 * z 1 * z 2 * z 3 =
      ρ (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) := by
    have e0 : ρ (Equiv.swap 0 1) = z 0 := hρ 0
    have e1 : ρ (Equiv.swap 1 2) = z 1 := hρ 1
    have e2 : ρ (Equiv.swap 2 3) = z 2 := hρ 2
    have e3 : ρ (Equiv.swap 3 4) = z 3 := hρ 3
    simp only [map_mul, e0, e1, e2, e3]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [hw, orderOf_injective ρ hinj]
  have h5 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) ^ 5 = 1 := by
    decide +kernel
  have hne : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) ≠ 1 := by
    decide +kernel
  exact orderOf_eq_prime h5 hne

end CFSG.Quasithin
