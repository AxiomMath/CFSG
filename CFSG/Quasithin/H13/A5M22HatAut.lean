module

public import Certificates.Certificate7106
public import CFSG.Quasithin.Background.HMathieuFacts22Base

public section

namespace CFSG.Quasithin.H13.A5.M22Hat

open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu

theorem getElem!_id24 {i : ℕ} (hi : i < 24) : id24[i]! = i := by
  rw [id24, getElem!_pos _ i (by simpa using hi), Array.getElem_range]

theorem getElem!_comp24 (a b : Array ℕ) {i : ℕ} (hi : i < 24) :
    (comp24 a b)[i]! = a[b[i]!]! := by
  rw [comp24, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem hasArr_one_id24 : HasArr (1 : Equiv.Perm (Fin 24)) id24 := fun i => by
  rw [getElem!_id24 i.2]
  rfl

theorem hasArr_mul {σ τ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ b) : HasArr (σ * τ) (comp24 a b) := fun i => by
  rw [getElem!_comp24 a b i.2, Equiv.Perm.mul_apply, hσ, hτ]

theorem hasArr_pow {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a) :
    ∀ k, HasArr (σ ^ k) (pow24 a k)
  | 0 => by
    rw [pow_zero]
    exact hasArr_one_id24
  | k + 1 => by
    rw [pow_succ']
    exact hasArr_mul hσ (hasArr_pow hσ k)

theorem hasArr_conj {σ τ : Equiv.Perm (Fin 24)} {a t : Array ℕ} (hσ : HasArr σ a)
    (hσi : HasArr σ⁻¹ (invArr a)) (hτ : HasArr τ t) : HasArr (σ * τ * σ⁻¹) (conj24 a t) :=
  hasArr_mul (hasArr_mul hσ hτ) hσi

theorem orderOf_eq_eleven_of_arr {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (h : order11OK a = true) : orderOf σ = 11 := by
  simp only [order11OK, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨i, hi, hne⟩, hpow⟩ := h
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Equiv.ext fun j => Fin.ext ?_) fun h1 => hne ?_
  · rw [hasArr_pow hσ 11 j, hpow j j.2]
    rfl
  · have := hσ ⟨i, hi⟩
    rw [h1] at this
    exact this.symm

theorem cert22h_mem :
    ∀ a ∈ pool22, inAutOK a = true ∧ a[0]! = 0 ∧ a[1]! = 1 :=
  Certificates.certificate7106.1

theorem cert22h_wit :
    ∀ p < T22s2.n, p ≠ T22s2.one → T22s2.mulIdx p p = T22s2.one → wit22OK p = true :=
  Certificates.certificate7106.2

theorem exists_perm_of_pool {i : ℕ} (hi : i < pool22.length) :
    ∃ σ ∈ mog22, HasArr σ pool22[i]! ∧ HasArr σ⁻¹ (invArr pool22[i]!) := by
  have hmem : pool22[i]! ∈ pool22 := by
    rw [getElem!_pos pool22 i hi]
    exact List.getElem_mem hi
  obtain ⟨hok, h0, h1⟩ := cert22h_mem _ hmem
  simp only [inAutOK, Bool.and_eq_true] at hok
  exact ⟨permOfArr 24 _ _ hok.1, mem_mog22_of_arr (mem_AutPerm_of_arr hok.1 hok.2)
    (hasArr_permOfArr hok.1) h0 h1, hasArr_permOfArr hok.1, hasArr_permOfArr_inv hok.1⟩

theorem exists_wit22
    (t : T22s2.Elem) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ σ₁ ∈ mog22, ∃ σ₂ ∈ mog22, ∃ σ₃ ∈ mog22,
      orderOf (T22s2.perm t * (σ₁ * T22s2.perm t * σ₁⁻¹) *
        ((σ₂ * T22s2.perm t * σ₂⁻¹) * (σ₃ * T22s2.perm t * σ₃⁻¹))) = 11 := by
  have hne : t.idx ≠ T22s2.one := fun h => ht1 (PT.Elem.ext' h)
  have hsq : T22s2.mulIdx t.idx t.idx = T22s2.one := congrArg PT.Elem.idx ht2
  have hw := cert22h_wit t.idx t.lt hne hsq
  simp only [wit22OK, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hI, hJ⟩, hK⟩, hord⟩ := hw
  obtain ⟨σ₁, h₁, ha₁, hb₁⟩ := exists_perm_of_pool hI
  obtain ⟨σ₂, h₂, ha₂, hb₂⟩ := exists_perm_of_pool hJ
  obtain ⟨σ₃, h₃, ha₃, hb₃⟩ := exists_perm_of_pool hK
  have ht : HasArr (T22s2.perm t) T22s2.elems[t.idx]! := T22s2.hasArr_perm t
  exact ⟨σ₁, h₁, σ₂, h₂, σ₃, h₃, orderOf_eq_eleven_of_arr (hasArr_mul
    (hasArr_mul ht (hasArr_conj ha₁ hb₁ ht))
    (hasArr_mul (hasArr_conj ha₂ hb₂ ht) (hasArr_conj ha₃ hb₃ ht))) hord⟩

@[expose] noncomputable def conj22 : ↥mog22plus →* MulAut ↥mog22 where
  toFun s :=
    { toFun := fun m => ⟨(s : Equiv.Perm (Fin 24)) * m * (s : Equiv.Perm (Fin 24))⁻¹,
        mog22_normal_in_plus s.2 m.2⟩
      invFun := fun m => ⟨(s : Equiv.Perm (Fin 24))⁻¹ * m * (s : Equiv.Perm (Fin 24)), by
        have h := mog22_normal_in_plus (mog22plus.inv_mem s.2) m.2
        rwa [inv_inv] at h⟩
      left_inv := fun m => Subtype.ext (by group)
      right_inv := fun m => Subtype.ext (by group)
      map_mul' := fun m n => Subtype.ext (by
        change (s : Equiv.Perm (Fin 24)) * (m * n) * (s : Equiv.Perm (Fin 24))⁻¹ =
          s * m * (s : Equiv.Perm (Fin 24))⁻¹ * (s * n * (s : Equiv.Perm (Fin 24))⁻¹)
        group) }
  map_one' := MulEquiv.ext fun m => Subtype.ext (by
    change ((1 : ↥mog22plus) : Equiv.Perm (Fin 24)) * m *
      ((1 : ↥mog22plus) : Equiv.Perm (Fin 24))⁻¹ = m
    rw [Subgroup.coe_one]
    group)
  map_mul' s s' := MulEquiv.ext fun m => Subtype.ext (by
    change ((s * s' : ↥mog22plus) : Equiv.Perm (Fin 24)) * (m : Equiv.Perm (Fin 24)) *
      ((s * s' : ↥mog22plus) : Equiv.Perm (Fin 24))⁻¹ =
      (s : Equiv.Perm (Fin 24)) * ((s' : Equiv.Perm (Fin 24)) * (m : Equiv.Perm (Fin 24)) *
        (s' : Equiv.Perm (Fin 24))⁻¹) * (s : Equiv.Perm (Fin 24))⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem coe_conj22 (s : ↥mog22plus) (m : ↥mog22) :
    ((conj22 s m : ↥mog22) : Equiv.Perm (Fin 24)) =
      (s : Equiv.Perm (Fin 24)) * m * (s : Equiv.Perm (Fin 24))⁻¹ := rfl

theorem conj22_injective : Function.Injective conj22 := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hc : ∀ m : ↥mog22, (s : Equiv.Perm (Fin 24)) * m * (s : Equiv.Perm (Fin 24))⁻¹ = m :=
    fun m =>
    congrArg Subtype.val (DFunLike.congr_fun hs m)
  have hcent : rho10 mog22plus le_rfl s ∈ Subgroup.centralizer
      ((rho10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, rfl⟩
    have e1 : rho10 mog22 mog22_le_mog22plus m =
        rho10 mog22plus le_rfl ⟨m, mog22_le_mog22plus m.2⟩ := MulEquiv.ext fun w => rfl
    have e2 : (⟨m, mog22_le_mog22plus m.2⟩ : ↥mog22plus) * s = s * ⟨m, mog22_le_mog22plus m.2⟩ := by
      apply Subtype.ext
      change (m : Equiv.Perm (Fin 24)) * s = s * m
      calc (m : Equiv.Perm (Fin 24)) * s =
          s * m * (s : Equiv.Perm (Fin 24))⁻¹ * s := by rw [hc m]
        _ = s * m := by group
    rw [e1, ← map_mul, ← map_mul, e2]
  rw [centralizer_rho10_mog22, Subgroup.mem_bot] at hcent
  exact rho10_mog22plus_injective (hcent.trans (map_one _).symm)

theorem conj22_bijective :
    Function.Bijective conj22 := by
  have : Finite (MulAut ↥mog22) := MulEquiv.finite_left
  refine conj22_injective.bijective_of_nat_card_le ?_
  rw [card_mulAut_congr mog22EquivM22, card_mog22plus]
  have h := CFSG.Sporadic.Schreier.m22_mulAut_card
  rw [CFSG.Sporadic.Schreier.m22_card] at h
  exact h

theorem exists_orderOf_eleven
    (β : MulAut ↥mog22) (hβ2 : β * β = 1) (hβ1 : β ≠ 1) :
    ∃ m₁ m₂ m₃ : ↥mog22, orderOf (β m₁ * m₁⁻¹ * (m₂ * β (m₂⁻¹ * m₃) * m₃⁻¹)) = 11 := by
  obtain ⟨s, rfl⟩ := conj22_bijective.2 β
  have hs2 : s * s = 1 := conj22_injective (by rw [map_mul, hβ2, map_one])
  have hs1 : s ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  obtain ⟨g, t, ht1, hgt⟩ :=
    exists_conj_of_prime phi22 (T22s2.toSub_injective _ _) card_T22s2 hord
  have ht2 : t * t = 1 := by
    apply T22s2.toSub_injective mog22plus (T22s2.mem_mog22plus T22s2_ok.2.2)
    rw [map_mul, map_one]
    change phi22 t * phi22 t = 1
    rw [← hgt]
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  obtain ⟨σ₁, h₁, σ₂, h₂, σ₃, h₃, h11⟩ := exists_wit22 t ht1 ht2
  have hm : ∀ {σ : Equiv.Perm (Fin 24)}, σ ∈ mog22 →
      (g : Equiv.Perm (Fin 24))⁻¹ * σ * g ∈ mog22 := fun {σ} hσ => by
    have h := mog22_normal_in_plus (mog22plus.inv_mem g.2) hσ
    rwa [inv_inv] at h
  refine ⟨⟨_, hm h₁⟩, ⟨_, hm h₂⟩, ⟨_, hm h₃⟩, ?_⟩
  set T : Equiv.Perm (Fin 24) := T22s2.perm t with hT
  have hTs : (s : Equiv.Perm (Fin 24)) = (g : Equiv.Perm (Fin 24))⁻¹ * T * g := by
    have h := congrArg Subtype.val hgt
    change (g : Equiv.Perm (Fin 24)) * s * (g : Equiv.Perm (Fin 24))⁻¹ = T at h
    rw [← h]
    group
  have hTT : T * T = 1 := by
    have h := congrArg Subtype.val (congrArg phi22 ht2)
    rwa [map_mul, map_one] at h
  have hTi : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTT
  have hcoe : ((conj22 s ⟨_, hm h₁⟩ * (⟨_, hm h₁⟩ : ↥mog22)⁻¹ *
      ((⟨_, hm h₂⟩ : ↥mog22) * conj22 s ((⟨_, hm h₂⟩ : ↥mog22)⁻¹ * ⟨_, hm h₃⟩) *
        (⟨_, hm h₃⟩ : ↥mog22)⁻¹) : ↥mog22) : Equiv.Perm (Fin 24)) =
      (g : Equiv.Perm (Fin 24))⁻¹ * (T * (σ₁ * T * σ₁⁻¹) *
        ((σ₂ * T * σ₂⁻¹) * (σ₃ * T * σ₃⁻¹))) * (g : Equiv.Perm (Fin 24)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conj22, hTs]
    calc _ = (g : Equiv.Perm (Fin 24))⁻¹ * (T * (σ₁ * T⁻¹ * σ₁⁻¹) *
          ((σ₂ * T * σ₂⁻¹) * (σ₃ * T⁻¹ * σ₃⁻¹))) * (g : Equiv.Perm (Fin 24)) := by group
      _ = _ := by rw [hTi]
  rw [← Subgroup.orderOf_coe, hcoe]
  have hconj := orderOf_injective (MulAut.conj (g : Equiv.Perm (Fin 24))⁻¹).toMonoidHom
    (MulAut.conj _).injective (T * (σ₁ * T * σ₁⁻¹) * ((σ₂ * T * σ₂⁻¹) * (σ₃ * T * σ₃⁻¹)))
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hconj
  rw [hconj, h11]

end CFSG.Quasithin.H13.A5.M22Hat
