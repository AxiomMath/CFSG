module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open43
public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.RankThree.PartOne.KP.UnitaryTorus
import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Adapters.RankTwoModelTransports
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Fischer

namespace TripleCoverU62

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CentralCoverThree
  CFSG.RankThree.PartOne.KPUnitaryTorus

abbrev U62 : Type := StatedProj (StatedSU 6 (2 ^ 1) F4)

theorem nonempty_carrierEquiv (q : PrimePower) (hv : (LieTypeIndex.twistedA 5 q).Valid)
    (hp : q.p = 2) (hf : q.exponent = 1) :
    Nonempty ((CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group ≃* U62) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := hf
  exact ⟨(CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 _ hv).trans
    (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr F4.equivGaloisField.symm)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU _ 6 (2 ^ 1))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars _))⟩

section Torus

variable {G : Type} [Group G] {φ : G →* U62}

theorem commute_of_mem_range (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {x y : G} (hx : φ x ∈ unitaryTorusHom.range) (hy : φ y ∈ unitaryTorusHom.range) :
    x * y = y * x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h := torusPairing_eq hφ unitaryTorusHom hker (a := Multiplicative.toAdd a)
    (b := Multiplicative.toAdd b) (y := x) (z := y) (by rw [ofAdd_toAdd]; exact ha.symm)
    (by rw [ofAdd_toAdd]; exact hb.symm)
  rw [torusPairing_eq_one hφ unitaryTorusHom hker unitaryTorus_conj] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem permSumZero_swap_zero_dvec (i : Fin 6) :
    permSumZero (Equiv.swap 0 i) (dvec i) = -dvec i := by
  apply Subtype.ext
  funext k
  rw [permSumZero_apply, Equiv.symm_swap, NegMemClass.coe_neg, Pi.neg_apply, dvec_apply,
    dvec_apply]
  revert i k
  decide

theorem exists_lift_dvec (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (i : Fin 6) :
    ∃ y : G, φ y = unitaryTorusHom (Multiplicative.ofAdd (dvec i)) ∧ y ^ 3 = 1 := by
  obtain ⟨n, hn⟩ := unitaryTorus_conj (Equiv.swap 0 i)
  refine TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide) ?_ (n := n) ?_
  · rw [← map_pow, pow_three_eq_one_sumZero6, map_one]
  · rw [hn, permSumZero_swap_zero_dvec, ofAdd_neg, map_inv]

theorem exists_lift_of_mem_range (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {e : U62} (he : e ∈ unitaryTorusHom.range) :
    ∃ y : G, φ y = e ∧ y ^ 3 = 1 := by
  set S : Set U62 := Set.range fun i => unitaryTorusHom (Multiplicative.ofAdd (dvec i))
  have hclosure : ∀ b : sumZero6,
      unitaryTorusHom (Multiplicative.ofAdd b) ∈ Subgroup.closure S := fun b =>
    AddSubgroup.closure_induction (k := Set.range dvec)
      (p := fun b _ => unitaryTorusHom (Multiplicative.ofAdd b) ∈ Subgroup.closure S)
      (by
        rintro _ ⟨i, rfl⟩
        exact Subgroup.subset_closure ⟨i, rfl⟩)
      (by rw [ofAdd_zero, map_one]; exact one_mem _)
      (fun x y _ _ hx hy => by rw [ofAdd_add, map_mul]; exact mul_mem hx hy)
      (fun x _ hx => by rw [ofAdd_neg, map_inv]; exact inv_mem hx)
      (mem_closure_dvec b)
  refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure (E := unitaryTorusHom.range)
    (fun x hx y hy => commute_of_mem_range hφ hker hx hy) (S := S) ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact exists_lift_dvec hφ hker i
  · obtain ⟨a, rfl⟩ := he
    simpa only [ofAdd_toAdd] using hclosure (Multiplicative.toAdd a)

end Torus

@[expose] def vecFun (b : Fin 3 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![0, 0, b 0, b 1, b 2, -(b 0 + b 1 + b 2)]

theorem vecFun_mem (b : Fin 3 → ZMod 3) : vecFun b ∈ sumZero6 := by
  rw [mem_sumZero6, Fin.sum_univ_six]
  simp only [vecFun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

@[expose] def vecHom : (Fin 3 → ZMod 3) →+ sumZero6 where
  toFun b := ⟨vecFun b, vecFun_mem b⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [vecFun]
  map_add' a b := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [vecFun]
    ring

theorem vecHom_apply (b : Fin 3 → ZMod 3) (i : Fin 6) :
    ((vecHom b : sumZero6) : Fin 6 → ZMod 3) i = vecFun b i :=
  rfl

noncomputable def theta : Multiplicative (Fin 3 → ZMod 3) →* U62 :=
  unitaryTorusHom.comp (AddMonoidHom.toMultiplicative vecHom)

theorem theta_injective : Function.Injective theta := by
  rw [injective_iff_map_eq_one]
  intro b hb
  obtain ⟨k, hk⟩ := (unitaryTorusHom_eq_one_iff (vecHom (Multiplicative.toAdd b))).1 hb
  have h0 := hk 0
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  simp only [vecHom_apply, vecFun, Matrix.cons_val_zero, Matrix.cons_val] at h0 h2 h3 h4
  apply Multiplicative.toAdd.injective
  funext j
  fin_cases j
  · exact h2.trans h0.symm
  · exact h3.trans h0.symm
  · exact h4.trans h0.symm

theorem card_range_theta : Nat.card theta.range = 3 ^ 3 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective theta_injective, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem range_theta_le : theta.range ≤ unitaryTorusHom.range := by
  rintro _ ⟨b, rfl⟩
  exact ⟨_, rfl⟩

abbrev swap01 : Equiv.Perm (Fin 6) := Equiv.swap 0 1

noncomputable def tSwap : U62 := QuotientGroup.mk ⟨permGL swap01, permGL_mem swap01⟩

theorem tSwap_sq : tSwap ^ 2 = 1 := by
  have h : (⟨permGL swap01, permGL_mem swap01⟩ : StatedSU 6 (2 ^ 1) F4) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
    show swap01.permMatrix F4 * swap01.permMatrix F4 = 1
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  rw [tSwap, ← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]

theorem tSwap_ne_one : tSwap ≠ 1 := by
  intro h
  rw [tSwap, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg (fun A : GL (Fin 6) F4 => (A : Matrix (Fin 6) (Fin 6) F4) 0 0) hc
  have h2 := congrArg (fun A : GL (Fin 6) F4 => (A : Matrix (Fin 6) (Fin 6) F4) 2 2) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    permGL] at h1 h2
  have e00 : swap01.permMatrix F4 0 0 = 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, swap01]
  have e22 : swap01.permMatrix F4 2 2 = 1 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, swap01, Equiv.swap_apply_of_ne_of_ne]
  rw [e00] at h1
  rw [e22, h1] at h2
  exact zero_ne_one h2

theorem permGL_mul_torusGL (b : Fin 3 → ZMod 3) :
    permGL swap01 * torusGL (vecFun b) = torusGL (vecFun b) * permGL swap01 := by
  apply Units.ext
  simp only [Units.val_mul, permGL, torusGL, coe_diagGL]
  rw [permMatrix_mul_diagonal]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem commute_tSwap {e : U62} (he : e ∈ theta.range) : Commute tSwap e := by
  obtain ⟨b, rfl⟩ := he
  have h : (⟨permGL swap01, permGL_mem swap01⟩ : StatedSU 6 (2 ^ 1) F4) *
      torusElt (vecHom (Multiplicative.toAdd b)) =
      torusElt (vecHom (Multiplicative.toAdd b)) * ⟨permGL swap01, permGL_mem swap01⟩ :=
    Subtype.ext (permGL_mul_torusGL (Multiplicative.toAdd b))
  show tSwap * QuotientGroup.mk (torusElt (vecHom (Multiplicative.toAdd b))) =
    QuotientGroup.mk (torusElt (vecHom (Multiplicative.toAdd b))) * tSwap
  rw [tSwap, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem four_le_twoLocalOddRank_of_cover {G : Type} [Group G] [Finite G] (φ : G →* U62)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) : 4 ≤ CFSG.twoLocalOddRank G := by
  have h := TripleCoverLift.succ_le_localRank_of_lift hφ hker Nat.prime_three (by norm_num) h3
    (E := theta.range)
    (fun x hx y hy => commute_of_mem_range hφ hker (range_theta_le hx) (range_theta_le hy))
    (fun e he => exists_lift_of_mem_range hφ hker (range_theta_le he)) tSwap_ne_one tSwap_sq
    (fun e he => commute_tSwap he) (r := 3) card_range_theta.ge
  exact CFSG.RankThree.PartOne.Census3.four_le_twoLocalOddRank_of_localRank Nat.prime_three
    (by norm_num) h

end TripleCoverU62

open TripleCoverU62 in
theorem tripleCoverU62RankFour : TripleCoverU62RankFour := by
  intro q hv hp hf G _ _ hG
  obtain ⟨-, h3, ⟨e⟩⟩ := hG
  obtain ⟨eX⟩ := nonempty_carrierEquiv q hv hp hf
  let φ : G →* U62 := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center G := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact four_le_twoLocalOddRank_of_cover φ hφ hker.le (hker ▸ h3)

end CFSG.RankThree.PartTwo.Sec4.Census
