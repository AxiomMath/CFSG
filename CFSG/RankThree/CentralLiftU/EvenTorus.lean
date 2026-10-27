module

public import CFSG.RankThree.CentralLiftU.UnitaryLiftGen
public import CFSG.RankThree.CentralLiftU.UnitaryTorusWeylOdd
public import CFSG.RankThree.CentralLiftU.UnitaryThreeEven

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.CentralLift (IsLargeCentralExt)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)

namespace Gen

section TorusGen

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r : ℕ}

section Torus

variable {R : Type*} [Group R] {π : R →* hypSU h r 1} (hS : LiftHyp h π)
  {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
include hS

theorem commute_hKappa (i j : Fin r) (a b : Kˣ) : Commute (hKappa h π i a) (hKappa h π j b) :=
  (commute_of_conj_eq (conj_hKappa_of_diag h hS (coe_pi_hKappa h hS j b) i a)).symm

theorem torusOdd_commute {x y : R} (hx : x ∈ torusOdd h π) (hy : y ∈ torusOdd h π) :
    Commute x y := by
  have hcomm := Subgroup.isMulCommutative_closure (k := Set.range fun p : Fin r × Kˣ =>
    hKappa h π p.1 p.2) (by
      rintro _ ⟨⟨i, a⟩, rfl⟩ _ ⟨⟨j, b⟩, rfl⟩ _
      exact commute_hKappa h hS i j a b)
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : torusOdd h π) ⟨y, hy⟩)

@[expose] noncomputable def thetaOdd : hypTorus h r 1 →* R :=
  prodHom (fun m => (hKappa h π m).comp (tcoord h m))
    (fun i j _ _ _ => commute_hKappa h hS i j _ _)

theorem thetaOdd_apply (t : hypTorus h r 1) :
    thetaOdd h hS t = (List.ofFn fun m => hKappa h π m (tcoord h m t)).prod :=
  prodHom_apply _ _ t

theorem thetaOdd_mem (t : hypTorus h r 1) : thetaOdd h hS t ∈ torusOdd h π := by
  rw [thetaOdd_apply]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
  exact hKappa_mem_torusOdd h π m _

theorem pi_thetaOdd (t : hypTorus h r 1) : π (thetaOdd h hS t) = t := by
  obtain ⟨a, d, -, hp, hm⟩ := t.2
  have ha : ∀ m, ((tcoord h m t : Kˣ) : K) = a m := fun m => by
    rw [coe_tcoord_of_diag h m hm]
    rfl
  rw [thetaOdd_apply, map_list_prod, List.map_ofFn]
  refine hypSU_eq_of_diag h (coe_prod_ofFn_of_diag h _ _
    fun m => coe_pi_hKappa h hS m (tcoord h m t)) hm (fun x => ?_) (fun k => ?_)
  · simp [kappaDiag, torusEntries, ha]
  · have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    have hp' : (∏ i, (a i : K) / h.bar (a i)) * (d 0 : K) = 1 := by
      simpa [torusRatio] using hp
    have hinv : (∏ m, h.bar (a m : K) / (a m : K)) = (∏ i, (a i : K) / h.bar (a i))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp only [inv_div]
    simp only [kappaDiag, torusEntries, ha]
    rw [hinv]
    exact (eq_inv_of_mul_eq_one_right hp').symm

theorem thetaOdd_injective : Function.Injective (thetaOdd h hS) := fun t t' htt' =>
  Subtype.ext (by rw [← pi_thetaOdd h hS t, ← pi_thetaOdd h hS t', htt'])

theorem thetaOdd_pi_hKappa (k : Fin r) (a : Kˣ) :
    thetaOdd h hS ⟨π (hKappa h π k a), mem_hypTorus_of_diag h (coe_pi_hKappa h hS k a)⟩ =
      hKappa h π k a := by
  have hc' := fun m => coe_tcoord_of_diag h m
    (t := ⟨π (hKappa h π k a), mem_hypTorus_of_diag h (coe_pi_hKappa h hS k a)⟩)
    (coe_pi_hKappa h hS k a)
  rw [thetaOdd_apply, prod_ofFn_eq_single _ k]
  · congr 1
    ext
    rw [hc' k]
    simp [kappaDiag]
  · intro m hm
    have h1 : tcoord h m ⟨π (hKappa h π k a), mem_hypTorus_of_diag h (coe_pi_hKappa h hS k a)⟩ =
        1 := by
      ext
      rw [hc' m]
      simp [kappaDiag, hm]
    rw [h1, map_one]

theorem range_thetaOdd : (thetaOdd h hS).range = torusOdd h π := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    exact thetaOdd_mem h hS t
  · rw [torusOdd, Subgroup.closure_le]
    rintro _ ⟨⟨k, a⟩, rfl⟩
    exact ⟨_, thetaOdd_pi_hKappa h hS k a⟩

@[expose] noncomputable def thetaOddEquiv : hypTorus h r 1 ≃* torusOdd h π :=
  (MonoidHom.ofInjective (thetaOdd_injective h hS)).trans
    (MulEquiv.subgroupCongr (range_thetaOdd h hS))

theorem coe_thetaOddEquiv (t : hypTorus h r 1) :
    ((thetaOddEquiv h hS t : torusOdd h π) : R) = thetaOdd h hS t := by
  rw [thetaOddEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

theorem injOn_pi_torusOdd : Set.InjOn π (torusOdd h π) := by
  intro y hy y' hy' hyy'
  rw [SetLike.mem_coe, ← range_thetaOdd h hS] at hy hy'
  obtain ⟨t, rfl⟩ := hy
  obtain ⟨t', rfl⟩ := hy'
  rw [pi_thetaOdd, pi_thetaOdd] at hyy'
  rw [Subtype.ext hyy']

theorem hRho_eq_odd {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    hRho h π hij t = hKappa h π i t * (hKappa h π j t)⁻¹ := by
  rw [hKappa_eq_hRho_mul h hS hij t, mul_inv_cancel_right]

theorem torusHyp_odd : TorusHyp h π hc hc0 (torusOdd h π) where
  diag := by
    rw [torusOdd, Subgroup.closure_le]
    rintro _ ⟨⟨k, a⟩, rfl⟩
    exact mem_hypTorus_of_diag h (coe_pi_hKappa h hS k a)
  rho i j hij t := by
    rw [hRho_eq_odd h hS hij t]
    exact mul_mem (hKappa_mem_torusOdd h π i t) (inv_mem (hKappa_mem_torusOdd h π j t))
  iota k b := by
    rw [hIota_eq_hKappa h hS hc hc0 k b]
    exact hKappa_mem_torusOdd h π k _

end Torus

end TorusGen

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ}

include h in
theorem charP_two : CharP K 2 := h.charP

theorem charP_two_fixedField : CharP h.fixedField 2 :=
  (RingHom.charP_iff_charP h.fixedField.subtype 2).mpr h.charP

theorem odd_card_ker {R : Type*} [Group R] [Finite R] {G : Type*} [Group G] {π : R →* G}
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpk : IsPGroup p π.ker) : Odd (Nat.card π.ker) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hpk.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two (by omega)).pow

theorem liftHyp_of_even {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε}
    (hπ : IsLargeCentralExt π) : LiftHyp h π := by
  have := h.finite
  have := h.charP
  have : CharP h.fixedField 2 := charP_two_fixedField h
  have : Finite (hypSU h r ε) := inferInstance
  obtain ⟨p, hp, hp3, hpk⟩ := hπ.large
  have hodd := odd_card_ker hp hp3 hpk
  exact ⟨fun α => (CFSG.SectionRank.EvenCover.even_linear_homomorphism_lifting le_rfl hπ.surj
      hπ.cen hodd α).1,
    fun α => (CFSG.SectionRank.EvenCover.even_linear_homomorphism_lifting le_rfl hπ.surj
      hπ.cen hodd α).1,
    fun α => (even_unitary_three_central_large_prime_homomorphism_lifting h (gramJ3_herm h)
      det_gramJ3 hp hp3 π hπ.surj hπ.cen hpk α).1⟩

end Even

end Gen

end CFSG.RankThree.CentralLiftU
