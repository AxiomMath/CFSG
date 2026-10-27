module

public import CFSG.Quasithin.EmptyFaithful.S153QPC2
public import CFSG.Quasithin.EmptyFaithful.S153QPC3
public import CFSG.Quasithin.EmptyFaithful.S153QPC4
public import CFSG.Quasithin.EmptyFaithful.S153QPR

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem five_dvd_of_seventeen_dvd_card_sl3 (h : 17 ∣ Nat.card (SpecialLinearGroup (Fin 3) F)) :
    5 ∣ Nat.card F - 1 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have h1 : Nat.card (SpecialLinearGroup (Fin 3) F) * Nat.card Fˣ = Nat.card (GL (Fin 3) F) :=
    Matrix.card_SL_mul_card_units
  have h2 : Nat.card (GL (Fin 3) F) =
      ∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ)) := Matrix.card_GL_field 3
  have h3 : 17 ∣ ∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ)) := by
    rw [← h2, ← h1]
    exact Dvd.dvd.mul_right h _
  rw [hn] at h3
  have h4 := five_dvd_two_pow_sub_one_of_seventeen_dvd h3
  rwa [hq]

omit [Finite F] in
theorem radU_mul_self {n : ℕ} {W : Submodule F (Fin n → F)} {g : SpecialLinearGroup (Fin n) F}
    (hg : g ∈ radU F W) : g * g = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  apply eq_one_of_forall_mulVec
  intro v
  rw [← mulVec_mulVec]
  have h1 : (g : Matrix (Fin n) (Fin n) F) *ᵥ ((g : Matrix (Fin n) (Fin n) F) *ᵥ v - v) =
      (g : Matrix (Fin n) (Fin n) F) *ᵥ v - v := hg.2 _ (hg.1 v)
  rw [mulVec_sub] at h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  funext i
  have h3 := congrFun h1 i
  simp only [Pi.sub_apply] at h3
  linear_combination h3 + (((g : Matrix (Fin n) (Fin n) F) *ᵥ v) i - v i) * h2

open scoped commutatorElement

theorem five_dvd_card_sub_one_of_normal_flag1 {N : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hNQ : N ≤ stabilizer (flagSpace 3 F 1))
    (hnorm : ∀ q ∈ stabilizer (flagSpace 3 F 1), ∀ y ∈ N, q * y * q⁻¹ ∈ N)
    (hcomm : IsPGroup 2 ↥⁅N, N⁆) {x : SpecialLinearGroup (Fin 3) F} (hx : x ∈ N)
    (hx5 : orderOf x = 5) : 5 ∣ Nat.card F - 1 := by
  by_contra h5
  set Q := stabilizer (flagSpace 3 F 1) with hQ
  have hcN : ∀ q ∈ Q, ∀ y ∈ ⁅N, N⁆, q * y * q⁻¹ ∈ ⁅N, N⁆ := by
    intro q hq y hy
    have h1 : N.map (MulAut.conj q).toMonoidHom ≤ N := by
      rintro _ ⟨z, hz, rfl⟩
      exact hnorm q hq z hz
    have h2 : ((MulAut.conj q).toMonoidHom y) ∈ ⁅N, N⁆.map (MulAut.conj q).toMonoidHom := ⟨y, hy, rfl⟩
    rw [Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono h1 h1 h2
  have hrad : ⁅N, N⁆ ≤ radU F (flagSpace 3 F 1) :=
    le_radU_of_isPGroup (by norm_num) (by norm_num) hcomm hcN
  have hxQ : x ∈ Q := hNQ hx
  set N₁ : Subgroup ↥Q := N.subgroupOf Q with hN₁
  set N₀ : Subgroup (GL (Fin 2) F) := N₁.map levi with hN₀
  have hρx : levi ⟨x, hxQ⟩ ∈ N₀ := ⟨⟨x, hxQ⟩, hx, rfl⟩
  have hnormal : N₀.Normal := by
    refine ⟨fun n hn A => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨q, rfl⟩ := levi_surjective A
    refine ⟨q * y * q⁻¹, ?_, by simp⟩
    show ((q * y * q⁻¹ : ↥Q) : SpecialLinearGroup (Fin 3) F) ∈ N
    simpa using hnorm q q.2 y hy
  have habel : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have hy' : (y : SpecialLinearGroup (Fin 3) F) ∈ N := hy
    have hz' : (z : SpecialLinearGroup (Fin 3) F) ∈ N := hz
    have hyz : ((⁅y, z⁆ : ↥Q) : SpecialLinearGroup (Fin 3) F) ∈ ⁅N, N⁆ := by
      have := Subgroup.commutator_mem_commutator hy' hz'
      simpa [commutatorElement_def] using this
    have h1 : levi ⁅y, z⁆ = 1 := (levi_eq_one_iff (⁅y, z⁆).2).2 (hrad hyz)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hρx5 : (levi ⟨x, hxQ⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxQ⟩ : ↥Q) ^ 5 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hx5]
      exact pow_orderOf_eq_one x
    rw [this, map_one]
  have hρx1 : levi ⟨x, hxQ⟩ ≠ 1 := by
    intro h
    have hxr : x ∈ radU F (flagSpace 3 F 1) := (levi_eq_one_iff hxQ).1 h
    have h2 := radU_mul_self hxr
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hx5] at h3
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (levi ⟨x, hxQ⟩) = 5 := orderOf_eq_prime hρx5 hρx1
  have h4 : 4 ≤ Nat.card F := by
    by_contra hlt0
    have hlt := not_le.1 hlt0
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨m, -, hm⟩ := FiniteField.card F 2
    have hq : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
    have hm1 : (m : ℕ) = 1 := by
      have hpos := m.pos
      have h2 : 2 ^ (m : ℕ) < 4 := hq ▸ hlt
      by_contra hne
      have h3 : 2 ≤ (m : ℕ) := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
      omega
    have hcard : Nat.card (GL (Fin 2) F) = 6 := by
      rw [Matrix.card_GL_field 2, hm, hm1, Fin.prod_univ_two]
      norm_num
    have := orderOf_dvd_natCard (levi ⟨x, hxQ⟩)
    rw [hord, hcard] at this
    omega
  obtain ⟨c, hc⟩ := exists_scalar_of_abelian_normal h4 N₀ habel hρx
  have hc5 : c ^ 5 = 1 := by
    have h1 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hρx5
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hc] at h1
    rw [← map_pow] at h1
    simpa [Matrix.scalar_apply, ← Units.val_pow_eq_pow_val] using h1
  have hc1 : c ≠ 1 := by
    intro h
    apply hρx1
    apply Units.ext
    rw [hc, h]
    simp
  have hcord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  apply h5
  have := orderOf_dvd_natCard c
  rwa [hcord, Nat.card_units] at this

theorem five_dvd_card_sub_one_of_normal_parabolic {P N : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hP : IsMaxParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)) P) (hNP : N ≤ P)
    (hnorm : ∀ p ∈ P, ∀ y ∈ N, p * y * p⁻¹ ∈ N) {x : SpecialLinearGroup (Fin 3) F} (hx : x ∈ N)
    (hx5 : orderOf x = 5) (hshape : IsPGroup 2 ↥⁅N, N⁆ ∨ 17 ∣ Nat.card ↥N) : 5 ∣ Nat.card F - 1 := by
  rcases hshape with h2 | h17
  · obtain ⟨θ, hθ⟩ := exists_aut_map_eq_stabilizer_flag1 hP
    set θ' := (θ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) with hθ'
    refine five_dvd_card_sub_one_of_normal_flag1 (N := N.map θ') ?_ ?_ ?_ (x := θ x) ⟨x, hx, rfl⟩ ?_
    · rintro _ ⟨n, hn, rfl⟩
      rw [← hθ]
      exact ⟨n, hNP hn, rfl⟩
    · intro q hq y hy
      rw [← hθ] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      obtain ⟨n, hn, rfl⟩ := hy
      refine ⟨p * n * p⁻¹, hnorm p hp n hn, ?_⟩
      simp [hθ']
    · rw [← Subgroup.map_commutator]
      exact h2.of_equiv (⁅N, N⁆.equivMapOfInjective θ' θ.injective)
    · exact (orderOf_injective θ' θ.injective x).trans hx5
  · exact five_dvd_of_seventeen_dvd_card_sl3 (h17.trans (Subgroup.card_subgroup_dvd_card N))

end CFSG.Quasithin.QP
