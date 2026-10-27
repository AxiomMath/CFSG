module

public import CFSG.Quasithin.Vol2.Ch11SecO6S1
public import CFSG.Quasithin.Vol2.Ch11SecO6B

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open scoped MatrixGroups IsMulCommutative

section LinAlg

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_smul_of_mul_self_eq_one [FiniteDimensional k V] (hV : Module.finrank k V ≤ 2)
    (h2 : (2 : k) ≠ 0) {T : Module.End k V} (hT : T * T = 1) (hdet : LinearMap.det T = 1) :
    ∃ c : k, T = c • 1 := by
  by_contra hT'
  obtain ⟨v, hv⟩ : ∃ v, LinearIndependent k ![v, T v] := by
    by_contra h
    push Not at h
    exact hT' (LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h)
  have hcard : Fintype.card (Fin 2) = Module.finrank k V := by
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at this ⊢
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hv hcard
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = T v := by simp [b]
  have h0 : T (b 0) = b 1 := by rw [hb0, hb1]
  have h1 : T (b 1) = b 0 := by
    rw [hb1, hb0, ← Module.End.mul_apply, hT, Module.End.one_apply]
  have e00 : LinearMap.toMatrix b b T 0 0 = 0 := by
    rw [LinearMap.toMatrix_apply, h0, b.repr_self]
    simp
  have e01 : LinearMap.toMatrix b b T 0 1 = 1 := by
    rw [LinearMap.toMatrix_apply, h1, b.repr_self]
    simp
  have e10 : LinearMap.toMatrix b b T 1 0 = 1 := by
    rw [LinearMap.toMatrix_apply, h0, b.repr_self]
    simp
  have e11 : LinearMap.toMatrix b b T 1 1 = 0 := by
    rw [LinearMap.toMatrix_apply, h1, b.repr_self]
    simp
  have hd := LinearMap.det_toMatrix b T
  rw [hdet, Matrix.det_fin_two, e00, e01, e10, e11] at hd
  apply h2
  linear_combination -hd

end LinAlg

section Act

variable {X : Type} [Group X] [Finite X] (r : ℕ) [Fact r.Prime]

theorem det_linConj_eq_one (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) (x : X) :
    LinearMap.det (A := ZMod r)
      (M := Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) (linConj r x) = 1 := by
  let d : X →* ZMod r := MonoidHom.comp (LinearMap.det (A := ZMod r)
    (M := Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)))) (linConj r)
  have hle : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ d.toHomUnits.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_right_comm, mul_inv_cancel_right, mul_inv_cancel]
  have h := MonoidHom.mem_ker.mp (hle (by rw [hX]; exact Subgroup.mem_top x))
  have h' := congrArg Units.val h
  rw [MonoidHom.coe_toHomUnits, Units.val_one] at h'
  exact h'

theorem inverts_of_perfect (hD : Case1Data X) (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hrF : r ∣ Nat.card (CFSG.fittingSubgroup X)) {s : X} (hs : s ∉ CFSG.fittingSubgroup X)
    (hs2 : s ^ 2 ∈ CFSG.fittingSubgroup X) : ActsScalar r (MulAut.conj s) (r - 1) := by
  obtain ⟨-, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hD.struct
  have : Fact q.Prime := ⟨hq⟩
  have hr5 : 5 ≤ r := hprimes r Fact.out hrF
  have hna := exists_not_triv r hD hrF (Or.inl hX)
  have h2z : ∀ m : ℕ, 5 ≤ m → (2 : ZMod m) ≠ 0 := by
    intro m hm h
    have h' : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 m).mp h')
    omega
  have h2q := h2z q hq5
  have hmemF : ∀ x : X, ψ x = 1 → x ∈ CFSG.fittingSubgroup X := fun x hx => by
    rw [← hker]
    exact hx
  have hψs : ψ s = -1 := by
    have hc : ψ s ∈ Subgroup.center SL(2, ZMod q) := mem_center_of_sq_eq_one h2q (by
      rw [← map_pow, ← MonoidHom.mem_ker, hker]
      exact hs2)
    rcases (SecD.O6S.mem_center_iff h2q).mp hc with h | h
    · exact absurd (hmemF s h) hs
    · exact h
  have hcent : ∀ x : X, x⁻¹ * MulAut.conj s x ∈ CFSG.fittingSubgroup X := fun x => hmemF _ (by
    rw [MulAut.conj_apply, map_mul, map_mul, map_mul, map_inv, map_inv, hψs,
      show (-1 : SL(2, ZMod q)) * ψ x = ψ x * -1 by rw [neg_one_mul, mul_neg_one]]
    group)
  obtain ⟨k, hk⟩ := actsScalar_of_comm r (hD.rank r Fact.out hrF)
    (fun f hf => fitting_acts_triv r hf) hna hcent
  have hsq : ActsScalar r (MulAut.conj s ^ 2) 1 := by
    rw [← map_pow, ← actsTrivially_iff]
    exact fitting_acts_triv r hs2
  refine (actsScalar_sign r hk hsq).resolve_left fun h1 => ?_
  have hLF : ∀ f ∈ CFSG.fittingSubgroup X, linConj r f = 1 := fun f hf =>
    MonoidHom.mem_ker.mp ((mem_ker_linConj r).mpr (fitting_acts_triv r hf))
  have hLs : linConj r s = 1 :=
    MonoidHom.mem_ker.mp ((mem_ker_linConj r).mpr ((actsTrivially_iff r s).mpr h1))
  obtain ⟨w, hw⟩ := hψ SecG.SL2.wElt
  have hw2 : ψ (w ^ 2) = -1 := by
    rw [map_pow, hw]
    rcases (SecD.O6S.mem_center_iff h2q).mp (SecG.SL2.wElt_sq_mem_center (k := ZMod q)) with
      h | h
    · exact absurd h (wElt_sq_ne_one (p := q) (by omega))
    · exact h
  have hT : linConj r w * linConj r w = 1 := by
    have hf : s⁻¹ * w ^ 2 ∈ CFSG.fittingSubgroup X :=
      hmemF _ (by rw [map_mul, map_inv, hw2, hψs, inv_mul_cancel])
    rw [← map_mul, ← sq, show w ^ 2 = s * (s⁻¹ * w ^ 2) by group, map_mul, hLs, hLF _ hf,
      one_mul]
  obtain ⟨c, hc⟩ := exists_smul_of_mul_self_eq_one (T := linConj r w)
    (finrank_le_two r (hD.rank r Fact.out hrF)) (h2z r hr5) hT (det_linConj_eq_one r hX w)
  let S : Subgroup X :=
    { carrier := {x | ∃ a : ZMod r, linConj r x = a • 1}
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a * b, by rw [map_mul, ha, hb, smul_mul_smul_comm, mul_one]⟩
      one_mem' := ⟨1, by rw [map_one, one_smul]⟩
      inv_mem' := by
        rintro x ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        have h : a • linConj r x⁻¹ = 1 := by
          rw [← mul_one (linConj r x⁻¹), ← mul_smul_comm, ← ha, ← map_mul, inv_mul_cancel,
            map_one]
        rcases eq_or_ne a 0 with h0 | h0
        · rw [h0, zero_smul] at h
          rw [h0, inv_zero, zero_smul, ← mul_one (linConj r x⁻¹), ← h, mul_zero]
        · rw [← h, smul_smul, inv_mul_cancel₀ h0, one_smul] }
  have hSn : S.Normal := ⟨fun x ⟨a, ha⟩ g => ⟨a, by
    rw [map_mul, map_mul, ha, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul,
      mul_inv_cancel, map_one]⟩⟩
  have hwS : w ∈ S := ⟨c, hc⟩
  have htop : S.map ψ = ⊤ := by
    rcases SecD.O6S.le_center_or_eq_top_of_normal (by rw [Nat.card_zmod]; omega)
      (hSn.map ψ hψ) with h | h
    · exact absurd (SecG.SL2.sq_eq_one_of_mem_center (h ⟨w, hwS, hw⟩))
        (wElt_sq_ne_one (p := q) (by omega))
    · exact h
  have hall : ∀ x : X, x ∈ S := fun x => by
    obtain ⟨y, hy, hyx⟩ : ψ x ∈ S.map ψ := htop ▸ Subgroup.mem_top _
    have hf : y⁻¹ * x ∈ CFSG.fittingSubgroup X :=
      hmemF _ (by rw [map_mul, map_inv, hyx, inv_mul_cancel])
    have h := S.mul_mem hy (show y⁻¹ * x ∈ S from ⟨1, by rw [hLF _ hf, one_smul]⟩)
    rwa [mul_inv_cancel_left] at h
  obtain ⟨x, y, hxy⟩ := hna
  apply hxy
  rw [← mem_ker_linConj r, MonoidHom.mem_ker]
  obtain ⟨a, ha⟩ := hall x
  have hcomm : linConj r x * linConj r y = linConj r y * linConj r x := by
    rw [ha, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  calc linConj r (x * y * x⁻¹ * y⁻¹)
      = linConj r x * linConj r y * linConj r x⁻¹ * linConj r y⁻¹ := by simp only [map_mul]
    _ = linConj r y * (linConj r x * linConj r x⁻¹) * linConj r y⁻¹ := by
        rw [hcomm, mul_assoc (linConj r y)]
    _ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

end Act

end CFSG.Quasithin.Vol2.Ch11.O6
