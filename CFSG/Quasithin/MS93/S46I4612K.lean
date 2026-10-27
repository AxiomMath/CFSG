module

public import CFSG.Quasithin.MS93.S46X3Grp

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.X3
open scoped commutatorElement Matrix

namespace KC

section Lin

variable {F : Type} [Field F]

private noncomputable def diag12 : Fˣ →* SL3 F where
  toFun a := ⟨Matrix.diagonal ![1, (a : F), ((a⁻¹ : Fˣ) : F)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  map_mul' a b := by
    refine Subtype.ext ?_
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

private theorem coe_diag12 (a : Fˣ) :
    ((diag12 a : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![1, (a : F), ((a⁻¹ : Fˣ) : F)] :=
  rfl

private theorem odd_orderOf_diag12 [Fintype F] [CharP F 2] (a : Fˣ) :
    Odd (orderOf (diag12 a : SL3 F)) := by
  classical
  have h1 : orderOf (diag12 a : SL3 F) ∣ orderOf a := orderOf_map_dvd _ a
  have h2 : orderOf a ∣ Fintype.card Fˣ := orderOf_dvd_card
  rw [Fintype.card_units] at h2
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hodd : Odd (Fintype.card F - 1) := by
    rw [hn]
    refine Nat.Even.sub_odd (Nat.one_le_two_pow) ?_ odd_one
    exact (Nat.even_pow' n.ne_zero).mpr even_two
  exact hodd.of_dvd_nat (h1.trans h2)

private theorem diag12_mulVec_apply_zero (a : Fˣ) (v : Fin 3 → F) :
    (((diag12 a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 := by
  rw [coe_diag12, Matrix.mulVec_diagonal]
  simp

private theorem diag12_mul_rootElt10 (a : Fˣ) (c : F) :
    diag12 a * rootElt 1 0 c = rootElt 1 0 ((a : F) * c) * diag12 a := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diag12,
    coe_rootElt (show (1 : Fin 3) ≠ 0 by decide), coe_rootElt (show (1 : Fin 3) ≠ 0 by decide)]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply]

private theorem diag12_mul_rootElt20 (a : Fˣ) (c : F) :
    diag12 a * rootElt 2 0 c = rootElt 2 0 (((a⁻¹ : Fˣ) : F) * c) * diag12 a := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diag12,
    coe_rootElt (show (2 : Fin 3) ≠ 0 by decide), coe_rootElt (show (2 : Fin 3) ≠ 0 by decide)]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply]

private theorem map_conj_diag12_le (a : Fˣ) :
    (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)).map (MulAut.conj (diag12 a)).toMonoidHom
      ≤ rootGroup 1 0 ⊔ rootGroup 2 0 := by
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_ <;> rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩ <;>
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rw [diag12_mul_rootElt10, mul_inv_cancel_right]
    exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 _)
  · rw [diag12_mul_rootElt20, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 _)

private theorem diag12_mem_normalizer (a : Fˣ) : (diag12 a : SL3 F) ∈
    Subgroup.normalizer ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact map_conj_diag12_le a ⟨x, hx, rfl⟩
  · intro hx
    have := map_conj_diag12_le a⁻¹ ⟨_, hx, rfl⟩
    simpa [mul_assoc, map_inv] using this

private theorem diag12_inv_mul_rootElt21 (a : Fˣ) (ha : (a : F) ^ 2 ≠ 1) (c : F) :
    ∃ t : F, (diag12 a)⁻¹ * rootElt 2 1 c = rootElt 2 1 t * (diag12 a)⁻¹ * (rootElt 2 1 t)⁻¹ := by
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have hd : (a : F)⁻¹ - a ≠ 0 := by
    intro h
    apply ha
    have h1 : (a : F)⁻¹ = a := sub_eq_zero.mp h
    calc (a : F) ^ 2 = a * a := sq _
      _ = a * (a : F)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel₀ ha0
  refine ⟨c * a * ((a : F)⁻¹ - a)⁻¹, ?_⟩
  rw [eq_mul_inv_iff_mul_eq, ← map_inv]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag12,
    coe_rootElt (show (2 : Fin 3) ≠ 1 by decide)]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply]
  field_simp
  ring

end Lin

section Lift

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

private theorem exists_odd_lift {A B : Type*} [Group A] [Group B] [Finite A] {f : A →* B}
    (hf : Function.Surjective f) {g : B} (hg : Odd (orderOf g)) :
    ∃ a : A, f a = g ∧ Odd (orderOf a) := by
  obtain ⟨q, rfl⟩ := hf g
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
  have hr : orderOf (q ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : (2 ^ k).Coprime (orderOf (f q)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg.not_two_dvd_nat)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(q ^ 2 ^ k) ^ t, by rw [map_pow, map_pow, ht], ?_⟩
  have hdvd : orderOf ((q ^ 2 ^ k) ^ t) ∣ m := hr ▸ orderOf_pow_dvd t
  exact hm.of_dvd_nat hdvd

variable {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

theorem exists_lift_odd (d : X3Data c α β γ ψ) {s : SL3 F} (hs : Odd (orderOf s))
    (hsN : s ∈ Subgroup.normalizer
      ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)))
    (hs0 : ∀ v : Fin 3 → F, (((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0) :
    ∃ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k = s ∧
      ∀ x ∈ ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α,
        ⁅x, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have : Finite ↥(stab (puAmalgam c.pu.le) α) := d.lh.fin
  obtain ⟨k, hψk, hkodd⟩ := exists_odd_lift (toSL3_surjective d.lh.surj) hs
  have hodd : Odd (orderOf (k : (puAmalgam c.pu.le).Universal)) := by
    rwa [Subgroup.orderOf_coe]
  have hN := d.mem_normalizer_qv (k := k) (by rw [hψk]; exact hsN)
  have hZ : ∀ z ∈ ZM (puAmalgam c.pu.le) α,
      ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZH (puAmalgam c.pu.le) β := by
    intro z hz
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc c.pu hfull d.mα hz
    set kk : (puAmalgam c.pu.le).Universal := (k : (puAmalgam c.pu.le).Universal) with hkk
    have hζk : ζ * kk = kk * ζ := (d.lh.comm_z0_k hζ k.2).symm
    have e1 : ⁅u * ζ, kk⁆ = ⁅u, kk⁆ := by
      simp only [commutatorElement_def]
      calc u * ζ * kk * (u * ζ)⁻¹ * kk⁻¹ = u * (ζ * kk) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by group
        _ = u * (kk * ζ) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by rw [hζk]
        _ = u * kk * u⁻¹ * kk⁻¹ := by group
    rw [e1]
    have hmem : ⁅u, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ Uloc c.pu.le L α :=
      I467.commutator_mem_of_natural d.lh.nat ⟨u, hu⟩ k
    have hnat := natVec_commutator d.lh.nat k ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    have hc : natVec d.lh.nat ⟨_, hmem⟩ ∈ commN (natImage ψ (Qv (puAmalgam c.pu.le) β)) := by
      rw [d.qvβ]
      apply mem_commN_of_apply_zero
      rw [hnat, hψk, Pi.sub_apply, hs0, sub_self]
    have h1 := (mem_commutator_iff_natVec d.lh.nat d.qβK ⟨_, hmem⟩).mpr hc
    rw [← usup_eq_commutator_uloc c.pu hfull d.mα d.adjαβ] at h1
    exact d.uZ h1
  have hV := d.odd (k : (puAmalgam c.pu.le).Universal) k.2 hN hZ hodd
  refine ⟨k, hψk, fun x hx => ?_⟩
  refine commutator_mem_of_mem_sup (stab_le_normalizer_zm _ α) d.zγK d.lh.zK
    (fun z hz => zh_le_zm _ d.adjαβ (hV z (d.zγVβ hz))) (fun z hz => ?_) hx
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp (stab_le_normalizer_zm _ α)
    (Subgroup.commutator_mem_commutator hz k.2)

theorem commutator_mem_of_rootGroup21 (d : X3Data c α β γ ψ) (hq : 4 ≤ Fintype.card F)
    {k : ↥(stab (puAmalgam c.pu.le) α)} (hk : toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)))
    {x : (puAmalgam c.pu.le).Universal} (hx : x ∈ ZM (puAmalgam c.pu.le) γ ⊔ ZM _ α) :
    ⁅x, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  set S := commRight (stab (puAmalgam c.pu.le) α) (ZM _ α) (stab_le_normalizer_zm _ α) x with hS
  have hxV : x ∈ Vv (puAmalgam c.pu.le) α := (sup_le d.zγVα d.lh.zv) hx
  have hQS : Qv (puAmalgam c.pu.le) α ≤ S := fun q hq =>
    ⟨d.lh.qK hq, d.lh.vqc (Subgroup.commutator_mem_commutator hxV hq)⟩
  obtain ⟨b, hb⟩ := hk
  obtain ⟨a, ha⟩ : ∃ a : Fˣ, a ≠ 1 := by
    classical
    have h1 : 1 < Fintype.card Fˣ := by rw [Fintype.card_units]; omega
    exact Fintype.exists_ne_of_one_lt_card h1 1
  have ha2 : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha
    have h1 : ((a : F) + 1) ^ 2 = 0 := by
      have e : ((a : F) + 1) ^ 2 = (a : F) ^ 2 + 1 + 2 * a := by ring
      rw [e, h, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    have h2 : (a : F) + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    have h3 : (a : F) = 1 := by
      calc (a : F) = ((a : F) + 1) + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = 1 := by rw [h2, zero_add]
    exact Units.ext h3
  obtain ⟨t, ht⟩ := diag12_inv_mul_rootElt21 a ha2 b
  obtain ⟨k₁, hk₁, hk₁x⟩ := exists_lift_odd d (odd_orderOf_diag12 a) (diag12_mem_normalizer a)
    (diag12_mulVec_apply_zero a)
  have hs₂odd : Odd (orderOf ((diag12 a)⁻¹ * rootElt 2 1 b : SL3 F)) := by
    rw [ht, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv]
    exact odd_orderOf_diag12 a
  have hs₂N : ((diag12 a)⁻¹ * rootElt 2 1 b : SL3 F) ∈ Subgroup.normalizer
      ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (diag12_mem_normalizer a))
      (rootElt21_mem_normalizer b)
  have hs₂0 : ∀ v : Fin 3 → F,
      ((((diag12 a)⁻¹ * rootElt 2 1 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 := by
    intro v
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← map_inv,
      diag12_mulVec_apply_zero, rootElt_mulVec_apply_zero (by decide)]
  obtain ⟨k₂, hk₂, hk₂x⟩ := exists_lift_odd d hs₂odd hs₂N hs₂0
  have hs : ((k₁ * k₂ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) ∈ S :=
    S.mul_mem ⟨k₁.2, hk₁x x hx⟩ ⟨k₂.2, hk₂x x hx⟩
  have he : toSL3 ψ (k₁ * k₂) = toSL3 ψ k := by
    rw [map_mul, hk₁, hk₂, mul_inv_cancel_left, hb]
  exact (d.mem_of_toSL3_eq hQS hs he).2

end Lift

end KC

end CFSG.Quasithin.MS93.S46
