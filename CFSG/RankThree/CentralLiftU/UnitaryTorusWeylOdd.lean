module

public import CFSG.RankThree.CentralLiftU.UnitaryWeyl
public import CFSG.RankThree.CentralLiftU.UnitaryTorus

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r : ℕ}

section Defs

variable {R : Type*} [Group R] (π : R →* hypSU h r 1)

@[expose] noncomputable def torusOdd : Subgroup R :=
  Subgroup.closure (Set.range fun p : Fin r × Kˣ => hKappa h π p.1 p.2)

theorem hKappa_mem_torusOdd (k : Fin r) (a : Kˣ) : hKappa h π k a ∈ torusOdd h π :=
  Subgroup.subset_closure ⟨(k, a), rfl⟩

end Defs

section Torus

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r 1} (hS : UHyp h π)
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

theorem odd_unitary_higher_central_large_prime_lifted_torus_and_weyl_odd {ℓ f : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hℓ : Odd ℓ) {r : ℕ} (_hr : 2 ≤ r) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {R : Type*} [Group R] [Finite R]
    (π : R →* hypSU h r 1) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center R)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpk : IsPGroup p π.ker) :
    (∀ (i j : Fin r) (hij : i ≠ j), π.comp (rhoLift h π hij) = rhoU h hij ∧
      ∀ ψ : SpecialLinearGroup (Fin 2) K →* R, π.comp ψ = rhoU h hij → ψ = rhoLift h π hij) ∧
    (∀ k : Fin r, π.comp (iotaLift h π hc hc0 k) = iotaU h hc hc0 k ∧
      ∀ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* R, π.comp ψ = iotaU h hc hc0 k →
        ψ = iotaLift h π hc hc0 k) ∧
    (∀ k : Fin r, π.comp (kappaLift h π k) = kappaU h k ∧
      ∀ ψ : gramSU h (gramJ3 K) →* R, π.comp ψ = kappaU h k → ψ = kappaLift h π k) ∧
    IsMulCommutative (torusOdd h π) ∧
    (∀ (i j : Fin r) (hij : i ≠ j) (t : Kˣ), hRho h π hij t ∈ torusOdd h π ∧
      hRho h π hij t = hKappa h π i t * (hKappa h π j t)⁻¹) ∧
    (∃ θ : hypTorus h r 1 ≃* torusOdd h π, (∀ x, π (θ x) = x) ∧
      ∀ (x : hypTorus h r 1) (a : Fin r → Kˣ) (d : Fin 1 → Kˣ),
        (((x : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
          diagonal (torusEntries h a d) →
        (θ x : R) = (List.ofFn fun i => hKappa h π i (a i)).prod) ∧
    torusOdd h π ≤ liftWeylU h π hc hc0 (torusOdd h π) ∧
    liftWeylU h π hc hc0 (torusOdd h π) ≤ Subgroup.normalizer (torusOdd h π : Set R) ∧
    (∀ k : Fin r, vIota h π hc hc0 k ∈ liftWeylU h π hc hc0 (torusOdd h π)) ∧
    (∃ φ : liftWeylU h π hc hc0 (torusOdd h π) →* hypWeyl r,
      (∀ (n : liftWeylU h π hc hc0 (torusOdd h π)) (x y : HypIndex r 1),
        (((π n : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)
          y x ≠ 0 ↔ y = weylPerm (φ n : Equiv.Perm (Fin r ⊕ Fin r)) x) ∧
      Function.Surjective φ ∧
      φ.ker = (torusOdd h π).subgroupOf (liftWeylU h π hc hc0 (torusOdd h π)) ∧
      ∃ _ : ((torusOdd h π).subgroupOf (liftWeylU h π hc hc0 (torusOdd h π))).Normal,
        ∃ e : liftWeylU h π hc hc0 (torusOdd h π) ⧸
            (torusOdd h π).subgroupOf (liftWeylU h π hc hc0 (torusOdd h π)) ≃* hypWeyl r,
          ∀ n : liftWeylU h π hc hc0 (torusOdd h π), e n = φ n) ∧
    Function.Injective (π.comp (liftWeylU h π hc hc0 (torusOdd h π)).subtype) ∧
    ∀ i : Fin r, sLift h π hc hc0 i ^ 2 ∈ torusOdd h π := by
  have hℓ2 : ℓ ≠ 2 := fun e => by
    rw [e] at hℓ
    exact absurd hℓ (by decide)
  have hS : UHyp h π := ⟨hℓ2, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hT := torusHyp_odd h hS hc hc0
  have hN := normal_subgroupOf_liftWeylU h hS hc hc0 hT
  have := h.finite
  refine ⟨fun i j hij => ⟨?_, fun ψ hψ => ?_⟩, fun k => ⟨?_, fun ψ hψ => ?_⟩,
    fun k => ⟨?_, fun ψ hψ => ?_⟩,
    ⟨⟨fun x y => Subtype.ext (torusOdd_commute h hS x.2 y.2).eq⟩⟩,
    fun i j hij t => ⟨hT.rho i j hij t, hRho_eq_odd h hS hij t⟩,
    ⟨thetaOddEquiv h hS, fun x => by rw [coe_thetaOddEquiv, pi_thetaOdd], fun x a d hx => ?_⟩,
    le_liftWeylU h π hc hc0 _, liftWeylU_le_normalizer h hS hc hc0 hT,
    fun k => vIota_mem_liftWeylU h hS hc hc0 k,
    ⟨weylHomU h hS hc hc0 hT, fun n x y => isLinePerm_weylHomU h hS hc hc0 hT n x y,
      weylHomU_surjective h hS hc hc0 hT, ker_weylHomU h hS hc hc0 hT, hN,
      weylQuotEquivU h hS hc hc0 hT, weylQuotEquivU_mk h hS hc hc0 hT⟩,
    injective_pi_liftWeylU h hS hc hc0 hT (injOn_pi_torusOdd h hS),
    fun i => by rw [sq]; exact sLift_mul_self_mem h hc hc0 hT i⟩
  · exact CFSG.RankThree.CentralLift.comp_sl2Lift_large hS.charK hS.large _
  · exact CFSG.RankThree.CentralLift.eq_sl2Lift_large hS.charK hS.large hψ
  · exact CFSG.RankThree.CentralLift.comp_sl2Lift_large hS.charF hS.large _
  · exact CFSG.RankThree.CentralLift.eq_sl2Lift_large hS.charF hS.large hψ
  · exact comp_su3Lift_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large _
  · exact eq_su3Lift_large h hS.odd (gramJ3_herm h) det_gramJ3 hS.large hψ
  · rw [coe_thetaOddEquiv, thetaOdd_apply]
    congr 1
    refine List.ofFn_inj.2 (funext fun m => ?_)
    congr 1
    ext
    rw [coe_tcoord_of_diag h m hx]
    rfl

end CFSG.RankThree.CentralLiftU
