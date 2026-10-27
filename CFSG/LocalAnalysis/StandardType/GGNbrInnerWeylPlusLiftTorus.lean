module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylPlusLiftSL2
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus

public section

namespace CFSG.StandardType.GGPlusLiftTorus

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

variable {R : Type} [Group R]

section Reflections

variable {p d : ℕ}

@[expose] def reflHom (i : Fin d) :
    (Fin d → Multiplicative (ZMod p)) →* (Fin d → Multiplicative (ZMod p)) where
  toFun f j := if j = i then (f j)⁻¹ else f j
  map_one' := by
    funext j
    simp only [Pi.one_apply]
    split_ifs
    · exact inv_one
    · rfl
  map_mul' f g := by
    funext j
    simp only [Pi.mul_apply]
    split_ifs
    · exact mul_inv (f j) (g j)
    · rfl

theorem reflHom_apply (i : Fin d) (f : Fin d → Multiplicative (ZMod p)) (j : Fin d) :
    reflHom i f j = if j = i then (f j)⁻¹ else f j :=
  rfl

theorem reflHom_mulSingle (i j : Fin d) (a : Multiplicative (ZMod p)) :
    reflHom i (Pi.mulSingle j a) = Pi.mulSingle j (if j = i then a⁻¹ else a) := by
  funext k
  rw [reflHom_apply]
  by_cases hkj : k = j
  · subst hkj
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hkj, Pi.mulSingle_eq_of_ne hkj]
    split_ifs
    · exact inv_one
    · rfl

@[expose] noncomputable def reflCoeff (i : Fin d) :
    (Fin d → ZMod p) →ₗ[ZMod p] ZMod p :=
  (2 : ZMod p) • LinearMap.proj i

theorem reflCoeff_apply (i : Fin d) (v : Fin d → ZMod p) : reflCoeff i v = 2 * v i := by
  simp [reflCoeff]

theorem reflCoeff_single (i : Fin d) :
    reflCoeff i (Pi.single i (1 : ZMod p)) = (2 : ZMod p) := by
  rw [reflCoeff_apply, Pi.single_eq_same, mul_one]

theorem sub_two_mul_eq_neg (x : ZMod p) : x - 2 * x = -x := by ring

theorem reflVec_apply_self (i : Fin d) (v : Fin d → ZMod p) :
    (v - reflCoeff i v • Pi.single i (1 : ZMod p) : Fin d → ZMod p) i = -v i := by
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, reflCoeff_apply, mul_one]
  exact sub_two_mul_eq_neg (v i)

theorem reflVec_apply_of_ne {i j : Fin d} (hji : j ≠ i) (v : Fin d → ZMod p) :
    (v - reflCoeff i v • Pi.single i (1 : ZMod p) : Fin d → ZMod p) j = v j := by
  simp [Pi.single_eq_of_ne hji]

theorem reflHom_ofAdd (i : Fin d) (v : Fin d → ZMod p) :
    reflHom i (fun j => Multiplicative.ofAdd (v j)) =
      fun j =>
        Multiplicative.ofAdd
          ((v - reflCoeff i v • Pi.single i (1 : ZMod p) : Fin d → ZMod p) j) := by
  funext j
  rw [reflHom_apply]
  split_ifs with hji
  · subst hji
    rw [reflVec_apply_self]
    exact (ofAdd_neg (v j)).symm
  · rw [reflVec_apply_of_ne hji]

end Reflections

section Commuting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p d : ℕ}

theorem ggTorusLift_of_commutingSL2 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (ρ : Fin (d + 1) → SL2 K →* R)
    (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B)) :
    GGTorusLift p d R := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, n, hsorder, hconj⟩ := GGPlusLiftSL2.exists_order_p_inverting_sl2 hp hp2 hpq
  have hs_pow : s ^ p = 1 := by rw [← hsorder]; exact pow_orderOf_eq_one s
  have hpow : ∀ i : Fin d, (ρ i.castSucc s) ^ p = 1 := fun i => by
    rw [← map_pow, hs_pow, map_one]
  let coord : Fin d → Multiplicative (ZMod p) →* R := fun i => TableBSymp.zmodPowHom (hpow i)
  have coord_apply : ∀ (i : Fin d) (a : Multiplicative (ZMod p)),
      coord i a = ρ i.castSucc (s ^ (Multiplicative.toAdd a).val) := fun i a => by
    change TableBSymp.zmodPowHom (hpow i) a = ρ i.castSucc (s ^ (Multiplicative.toAdd a).val)
    rw [TableBSymp.zmodPowHom_apply, map_pow]
  have coord_inj : ∀ i, Function.Injective (coord i) := fun i => by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hto : orderOf (ρ i.castSucc s) = p := by
      rw [orderOf_injective _ (hρ i.castSucc), hsorder]
    exact (TableBSymp.zmodPowHom_eq_one_iff (hpow i) hto).mp ha
  have coord_comm : Pairwise fun i j : Fin d => ∀ a b, Commute (coord i a) (coord j b) := by
    intro i j hij a b
    rw [coord_apply, coord_apply]
    exact hc i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h)) _ _
  let ePi : (Fin d → Multiplicative (ZMod p)) →* R := MonoidHom.noncommPiCoprod coord coord_comm
  let e : Multiplicative (Fin d → ZMod p) →* R :=
    ePi.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).toMonoidHom
  have e_apply : ∀ v : Fin d → ZMod p, e (.ofAdd v) = ePi (fun j => .ofAdd (v j)) := fun v => rfl
  have coord_indep : iSupIndep fun i => (coord i).range := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := hx
    have hle : (⨆ (j) (_ : j ≠ i), (coord j).range) ≤
        Subgroup.centralizer (Set.range (ρ i.castSucc)) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨B, rfl⟩ := hy
      rw [coord_apply]
      exact (hc i.castSucc j.castSucc (fun h => (Ne.symm hj) (Fin.castSucc_injective _ h)) B
        (s ^ (Multiplicative.toAdd b).val)).eq
    have hcen := hle hx'
    have hs_center : s ^ (Multiplicative.toAdd a).val ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      have h1 := Subgroup.mem_centralizer_iff.mp hcen (ρ i.castSucc B) ⟨B, rfl⟩
      rw [coord_apply] at h1
      have h2 : ρ i.castSucc (B * s ^ (Multiplicative.toAdd a).val) =
          ρ i.castSucc (s ^ (Multiplicative.toAdd a).val * B) := by
        rw [map_mul, map_mul]
        exact h1
      exact hρ i.castSucc h2
    obtain ⟨r, hr2, hr⟩ :=
      (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 2) (R := K)).mp hs_center
    have hr1 : r = 1 := by
      have h2 : r ^ 2 = 1 := by simpa using hr2
      have h : (r - 1) ^ 2 = 0 := by
        have h3 : (r - 1) ^ 2 = (2 : K) * (1 - r) := by linear_combination h2
        rw [h3, CharTwo.two_eq_zero, zero_mul]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    have hs_one : s ^ (Multiplicative.toAdd a).val = 1 := by
      apply Subtype.ext
      rw [← hr, hr1]
      exact map_one (Matrix.scalar (Fin 2))
    have hdvd : p ∣ (Multiplicative.toAdd a).val := by
      have := orderOf_dvd_of_pow_eq_one hs_one
      rwa [hsorder] at this
    have hval0 : (Multiplicative.toAdd a).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have ha1 : a = 1 := by
      rw [← ofAdd_toAdd a, (ZMod.val_eq_zero (Multiplicative.toAdd a)).mp hval0, ofAdd_zero]
    rw [ha1, map_one]
  have ePi_inj : Function.Injective ePi :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep coord coord_indep coord_inj
  have e_inj : Function.Injective e :=
    ePi_inj.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).injective
  have reflGen_conj_coord : ∀ (i j : Fin d) (a : Multiplicative (ZMod p)),
      ρ i.castSucc n * coord j a * (ρ i.castSucc n)⁻¹ =
        coord j (if j = i then a⁻¹ else a) := by
    intro i j a
    split_ifs with hji
    · subst hji
      rw [show coord j a⁻¹ = (coord j a)⁻¹ from map_inv _ a, coord_apply, ← map_inv,
        ← map_mul, ← map_mul, ← map_inv]
      congr 1
      rw [← conj_pow, hconj, inv_pow]
    · rw [coord_apply,
        (hc i.castSucc j.castSucc (fun h => hji (Fin.castSucc_injective _ h).symm) n
          (s ^ (Multiplicative.toAdd a).val)).eq, mul_inv_cancel_right]
  have reflGen_conj_ePi : ∀ (i : Fin d) (f : Fin d → Multiplicative (ZMod p)),
      ρ i.castSucc n * ePi f * (ρ i.castSucc n)⁻¹ = ePi (reflHom i f) := by
    intro i f
    have h : (MulAut.conj (ρ i.castSucc n)).toMonoidHom.comp ePi = ePi.comp (reflHom i) :=
      MonoidHom.pi_ext fun j a => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ePi,
          MonoidHom.noncommPiCoprod_mulSingle, reflHom_mulSingle]
        exact reflGen_conj_coord i j a
    have h1 := congrArg (fun φ => φ f) h
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have reflGen_conj_e : ∀ (i : Fin d) (v : Fin d → ZMod p),
      ρ i.castSucc n * e (.ofAdd v) * (ρ i.castSucc n)⁻¹ =
        e (.ofAdd (v - reflCoeff i v • Pi.single i (1 : ZMod p))) := by
    intro i v
    rw [e_apply, e_apply, reflGen_conj_ePi, reflHom_ofAdd]
  have e_commute_rootInv : ∀ v : Multiplicative (Fin d → ZMod p),
      Commute (e v) (ρ (Fin.last d) (uSL 1)) := by
    intro v
    have hmem : e v ∈ ePi.range := ⟨_, rfl⟩
    have hle : ePi.range ≤ Subgroup.centralizer {ρ (Fin.last d) (uSL 1)} := by
      change (MonoidHom.noncommPiCoprod coord coord_comm).range ≤
        Subgroup.centralizer {ρ (Fin.last d) (uSL 1)}
      rw [MonoidHom.noncommPiCoprod_range]
      refine iSup_le fun i => ?_
      rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, coord_apply]
      exact (hc i.castSucc (Fin.last d) (Fin.castSucc_lt_last i).ne _ _).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hmem)
  let U : Subgroup R := Subgroup.zpowers (ρ (Fin.last d) (uSL 1))
  have hU : U ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    exact TableBF4Two.uSL_one_ne_one (K := K)
      (hρ (Fin.last d) (h.trans (map_one (ρ (Fin.last d))).symm))
  have hU2 : IsPGroup 2 U := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_injective (ρ (Fin.last d)) (hρ (Fin.last d)),
      orderOf_eq_prime (TableBF4Two.uSL_one_sq (K := K) CharTwo.two_eq_zero)
        TableBF4Two.uSL_one_ne_one, pow_one]
  have hTU : ∀ v, ∀ u ∈ U, e v * u * (e v)⁻¹ ∈ U := by
    intro v u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [((e_commute_rootInv v).zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _
  exact TableBF4.ggTorusLift_of_reflections hp hp2 e e_inj reflCoeff reflCoeff_single
    (fun i => ρ i.castSucc n) reflGen_conj_e hU hU2 hTU

end Commuting

end CFSG.StandardType.GGPlusLiftTorus

end
