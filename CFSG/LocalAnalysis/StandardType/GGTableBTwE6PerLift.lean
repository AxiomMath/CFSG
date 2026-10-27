module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerRel

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Chevalley.ExceptionalCover
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

namespace TwE6Per


variable {k : Type} [Field k] [CharP k 2] {θ : k →+* k} (hθ : ∀ c, θ (θ c) = c) (μ : kˣ)
  (hθμ : Units.map (θ : k →* k) μ = μ⁻¹)

omit [CharP k 2] in
theorem torusHom_pair_ne_one {a b : Fin (Tag.rank .E6)}
    (hb : cartanCoord (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) b = 0)
    (hμ : μ * μ ≠ 1) : torusHom k (Pi.mulSingle a μ * Pi.mulSingle b μ⁻¹) ≠ 1 := by
  intro h
  have e := minTorus_conj_xm e6Data_valid k (Pi.mulSingle a μ * Pi.mulSingle b μ⁻¹)
    (IsRoot.basis a) 1
  rw [← torusHom_eq_minTorus, h, one_mul, inv_one, mul_one] at e
  have e2 := e6Data_valid.xm_injective k (IsRoot.basis a) e
  have ha : cartanCoord (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) a = 2 := by
    simp [cartanCoord, Pi.single_apply, Tag.cartan_self]
  rw [map_mul, rootChar_mulSingle, rootChar_mulSingle, ha, hb, zpow_zero, mul_one,
    mul_one] at e2
  apply hμ
  apply Units.ext
  rw [Units.val_mul, Units.val_one, e2, zpow_two, Units.val_mul]

variable (θ) in
@[expose] noncomputable def xTh : Multiplicative (fixedSubfield θ) →* fixedGroup k θ where
  toFun a := ⟨e6Data_valid.xm k vth ((Multiplicative.toAdd a : fixedSubfield θ) : k),
    xth_mem θ (theta_coe θ _)⟩
  map_one' := Subtype.ext (by simp [e6Data_valid.xm_zero])
  map_mul' a b := Subtype.ext (by simp [e6Data_valid.xm_add])

theorem xTh_mul_self (a : Multiplicative (fixedSubfield θ)) : xTh θ a * xTh θ a = 1 :=
  Subtype.ext (xm_mul_self_two vth _)

omit [CharP k 2] in
theorem xTh_ne_one : xTh θ (Multiplicative.ofAdd 1) ≠ 1 := by
  intro h
  have e : ((xTh θ (Multiplicative.ofAdd 1) : fixedGroup k θ) : e6Data_valid.minGroup k) = 1 := by
    rw [h]
    rfl
  have e' : e6Data_valid.xm k vth 1 = 1 := by simpa [xTh] using e
  rw [← e6Data_valid.xm_zero k vth] at e'
  exact one_ne_zero (e6Data_valid.xm_injective k isRoot_vth e')

theorem bU_comm_xTh (i : Fin 5) (a : Multiplicative (fixedSubfield θ)) :
    Commute (bU hθ μ hθμ i) (xTh θ a) := by
  have hs := slot_bU hθ μ hθμ i
  refine Subtype.ext ?_
  fin_cases i
  · exact (commute_rankOne_th (Or.inl rfl) hs _).eq
  · exact (commute_rankOne_th (Or.inr (Or.inl rfl)) hs _).eq
  · exact (commute_rankOne_th (Or.inr (Or.inr rfl)) hs _).eq
  · exact (commute_torus_th μ (Or.inl rfl) _).eq
  · exact (commute_torus_th μ (Or.inr rfl) _).eq

theorem bU_pow (hμ : μ * μ ≠ 1) {p : ℕ} (hp : μ ^ p = 1) (i : Fin 5) :
    bU hθ μ hθμ i ^ p = 1 := by
  have h3 : uS3 μ hθμ ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact sElt_pow (nd 3) μ hμ hp)
  have h2 : uS2 μ hθμ ^ p = 1 := by rw [uS2, conj_pow, h3, mul_one, mul_inv_cancel]
  have hu : ∀ a b : Fin (Tag.rank .E6),
      (Pi.mulSingle a μ * Pi.mulSingle b μ⁻¹ : Fin (Tag.rank .E6) → kˣ) ^ p = 1 := by
    intro a b
    rw [mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, inv_pow, hp, inv_one, Pi.mulSingle_one,
      Pi.mulSingle_one, mul_one]
  fin_cases i
  · show uS1 μ hθμ ^ p = 1
    rw [uS1, conj_pow, h2, mul_one, mul_inv_cancel]
  · exact h2
  · exact h3
  · exact Subtype.ext (by
      rw [Subgroup.coe_pow]
      change torusHom k (uOne μ) ^ p = 1
      rw [← map_pow, uOne, hu, map_one])
  · exact Subtype.ext (by
      rw [Subgroup.coe_pow]
      change torusHom k (uTwo μ) ^ p = 1
      rw [← map_pow, uTwo, hu, map_one])

omit [CharP k 2] in
theorem bU_ne_one (hμ : μ * μ ≠ 1) (i : Fin 5) : bU hθ μ hθμ i ≠ 1 := by
  have h3 : uS3 μ hθμ ≠ 1 := fun h => sElt_ne_one (nd 3) _ (congrArg Subtype.val h)
  have hconj : ∀ {M x : fixedGroup k θ}, x ≠ 1 → M * x * M⁻¹ ≠ 1 := fun hx h =>
    hx (by rw [mul_inv_eq_one, mul_eq_left] at h; exact h)
  have h2 : uS2 μ hθμ ≠ 1 := hconj h3
  fin_cases i
  · exact hconj h2
  · exact h2
  · exact h3
  · intro h
    exact torusHom_pair_ne_one μ (a := nd 0) (b := nd 5) (by decide) hμ
      (congrArg Subtype.val h)
  · intro h
    exact torusHom_pair_ne_one μ (a := nd 2) (b := nd 4) (by decide) hμ
      (congrArg Subtype.val h)

section Hom

variable {R : Type} [Group R] (q : fixedGroup k θ →* R)
  (hqk : q.ker ≤ Subgroup.center (fixedGroup k θ)) (hq2 : ∀ z ∈ q.ker, z * z = 1 → z = 1)

include hqk in
theorem map_bU_ne_one (hμ : μ * μ ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hμp : μ ^ p = 1)
    (i : Fin 5) : q (bU hθ μ hθμ i) ≠ 1 := by
  intro h
  have hc := hqk h
  have e1 := wU_inv hθ μ hθμ i
  rw [Subgroup.mem_center_iff.1 hc (wU θ i), mul_inv_cancel_right] at e1
  exact bU_ne_one hθ μ hθμ hμ i
    (eq_one_of_inv_eq (hp.odd_of_ne_two hp2) (bU_pow hθ μ hθμ hμ hμp i) e1.symm)

include hq2 in
theorem range_xTh_ne_bot : (q.comp (xTh θ)).range ≠ ⊥ := by
  intro h
  have h1 : q (xTh θ (Multiplicative.ofAdd 1)) = 1 := by
    have : (q.comp (xTh θ)) (Multiplicative.ofAdd 1) ∈ (q.comp (xTh θ)).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  exact xTh_ne_one (hq2 _ h1 (xTh_mul_self _))

omit [CharP k 2] in
theorem isPGroup_range_xTh [CharP k 2] : IsPGroup 2 (q.comp (xTh θ)).range := by
  rintro ⟨_, a, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  show ((q.comp (xTh θ)) a) ^ (2 ^ 1) = 1
  rw [pow_one, MonoidHom.comp_apply, pow_two, ← map_mul, xTh_mul_self, map_one]

theorem commute_range_xTh (i : Fin 5) :
    ∀ u ∈ (q.comp (xTh θ)).range, Commute (q (bU hθ μ hθμ i)) u := by
  rintro _ ⟨a, rfl⟩
  exact (bU_comm_xTh hθ μ hθμ i a).map q

include hθ hθμ hqk hq2 in
theorem ggTorusLift_four_of_hom (hμ : μ * μ ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hμp : μ ^ p = 1) : GGTorusLift p 4 R := by
  refine ggTorusLift_four hp hp2 (fun i => q (bU hθ μ hθμ (Fin.castSucc i)))
    (fun i j => (bU_comm hθ μ hθμ _ _).map q)
    (fun i => by rw [← map_pow, bU_pow hθ μ hθμ hμ hμp, map_one])
    (fun i => map_bU_ne_one hθ μ hθμ q hqk hμ hp hp2 hμp _)
    (fun i => q (wU θ (Fin.castSucc i)))
    (fun i => by rw [← map_inv, ← map_mul, ← map_mul, wU_inv, map_inv])
    (fun i j hi hj => by
      rw [← map_inv, ← map_mul, ← map_mul, wU_comm hθ μ hθμ _ _ ?_ ?_]
      · have := i.2
        have h3 : i.val ≠ 3 := fun h => hi (Fin.ext h)
        simp only [Fin.val_castSucc]
        omega
      · exact fun h => hj (Fin.castSucc_injective _ h))
    (range_xTh_ne_bot q hq2) (isPGroup_range_xTh q) (fun i => commute_range_xTh hθ μ hθμ q _)

include hθ hθμ hqk hq2 in
theorem ggTorusLift_five_of_hom (hμ : μ * μ ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hμp : μ ^ p = 1) : GGTorusLift p 5 R := by
  refine ggTorusLift_five hp hp2 hp3 (fun i => q (bU hθ μ hθμ i))
    (fun i j => (bU_comm hθ μ hθμ _ _).map q)
    (fun i => by rw [← map_pow, bU_pow hθ μ hθμ hμ hμp, map_one])
    (fun i => map_bU_ne_one hθ μ hθμ q hqk hμ hp hp2 hμp _)
    (fun i => q (wU θ i))
    (fun i => by rw [← map_inv, ← map_mul, ← map_mul, wU_inv, map_inv])
    (fun i j hi hj => by rw [← map_inv, ← map_mul, ← map_mul, wU_comm hθ μ hθμ _ _ hi hj])
    (by rw [← map_inv, ← map_mul, ← map_mul, wU_34, map_mul])
    (by rw [← map_inv, ← map_mul, ← map_mul, wU_43, map_mul])
    (range_xTh_ne_bot q hq2) (isPGroup_range_xTh q) (fun i => commute_range_xTh hθ μ hθμ q _)

end Hom

end TwE6Per

end CFSG.StandardType
