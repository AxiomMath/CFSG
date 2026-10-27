module

public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem card_sz_zero_eq_twenty : Nat.card ↥(CFSG.Open.Sz 0) = 20 := card_sz_zero

private def szzA : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1]

private def szzW : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

private theorem szzA_mul : szzA * szzA ^ 3 = 1 := by decide

private theorem szzA_mul' : szzA ^ 3 * szzA = 1 := by decide

private theorem szzW_mul : szzW * szzW = 1 := by decide

private def szzAU : GL (Fin 4) (ZMod 2) := ⟨szzA, szzA ^ 3, szzA_mul, szzA_mul'⟩

private def szzWU : GL (Fin 4) (ZMod 2) := ⟨szzW, szzW, szzW_mul, szzW_mul⟩

private def szzBU : GL (Fin 4) (ZMod 2) := szzWU * szzAU * szzWU⁻¹

private theorem szzAU_order : orderOf szzAU = 4 := by
  have h : orderOf szzAU = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  simpa using h

private theorem szzBU_order : orderOf szzBU = 4 := by
  have h : orderOf szzBU = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  simpa using h

private theorem szz_inter_aux :
    ∀ i j : Fin 4, szzAU ^ (i : ℕ) = szzBU ^ (j : ℕ) → (i : ℕ) = 0 := by decide

private noncomputable def szzField : GaloisField 2 (2 * 0 + 1) ≃+* ZMod 2 :=
  (GaloisField.equivZmodP (p := 2)).toRingEquiv

private noncomputable def szzEquiv :
    GL (Fin 4) (GaloisField 2 (2 * 0 + 1)) ≃* GL (Fin 4) (ZMod 2) :=
  Units.mapEquiv (RingEquiv.mapMatrix szzField).toMulEquiv

private theorem szzEquiv_symm_apply (g : GL (Fin 4) (ZMod 2)) (i j : Fin 4) :
    ((szzEquiv.symm g : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))) i j =
      szzField.symm ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) := rfl

private noncomputable def szzA' : GL (Fin 4) (GaloisField 2 (2 * 0 + 1)) := szzEquiv.symm szzAU

private noncomputable def szzW' : GL (Fin 4) (GaloisField 2 (2 * 0 + 1)) := szzEquiv.symm szzWU

private theorem szzA'_mem : szzA' ∈ Sz 0 := by
  refine Subgroup.subset_closure ?_
  show ((szzA' : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))) ∈ SzGenerators 0
  refine Or.inl ⟨1, 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szzA', szzEquiv_symm_apply, szzAU, szzA]

private theorem szzW'_mem : szzW' ∈ Sz 0 := by
  refine Subgroup.subset_closure ?_
  show ((szzW' : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))) ∈ SzGenerators 0
  refine Or.inr (Or.inr ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szzW', szzEquiv_symm_apply, szzWU, szzW]

private noncomputable def szzx : ↥(Sz 0) := ⟨szzA', szzA'_mem⟩

private noncomputable def szzy : ↥(Sz 0) :=
  ⟨szzW' * szzA' * szzW'⁻¹,
    mul_mem (mul_mem szzW'_mem szzA'_mem) (inv_mem szzW'_mem)⟩

private theorem szzEquiv_x : szzEquiv (szzx : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) = szzAU := by
  simp [szzx, szzA']

private theorem szzEquiv_y : szzEquiv (szzy : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) = szzBU := by
  simp [szzy, szzA', szzW', szzBU]

private theorem szzx_order : orderOf szzx = 4 := by
  rw [← Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq szzEquiv, szzEquiv_x, szzAU_order]

private theorem szzy_order : orderOf szzy = 4 := by
  rw [← Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq szzEquiv, szzEquiv_y, szzBU_order]

private theorem szz_finite : Finite ↥(Sz 0) :=
  Nat.finite_of_card_ne_zero (by rw [card_sz_zero_eq_twenty]; norm_num)

private noncomputable def szzSylow (x : ↥(Sz 0)) (hx : orderOf x = 4) : Sylow 2 ↥(Sz 0) :=
  have hcard : Nat.card (Subgroup.zpowers x) = 2 ^ 2 := by
    rw [Nat.card_zpowers, hx]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card hcard).toSylow (by
    have h := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hcard, card_sz_zero_eq_twenty] at h
    have h5 : (Subgroup.zpowers x).index = 5 := by omega
    rw [h5]; norm_num)

private theorem szzSylow_coe (x : ↥(Sz 0)) (hx : orderOf x = 4) :
    (szzSylow x hx : Subgroup ↥(Sz 0)) = Subgroup.zpowers x := rfl

private theorem szz_zpowers_inf : Subgroup.zpowers szzx ⊓ Subgroup.zpowers szzy = ⊥ := by
  classical
  have := szz_finite
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  rw [Finset.mem_range, szzx_order] at hi
  rw [Finset.mem_range, szzy_order] at hj
  have hij : szzAU ^ i = szzBU ^ j := by
    have := congrArg (fun z : ↥(Sz 0) => szzEquiv (z : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))))
      (hgi.trans hgj.symm)
    simpa [← szzEquiv_x, ← szzEquiv_y] using this
  have hi0 : i = 0 := szz_inter_aux ⟨i, hi⟩ ⟨j, hj⟩ hij
  rw [← hgi, hi0, pow_zero]

theorem pCore_two_sz_zero_eq_bot : CFSG.Open.pCore 2 ↥(CFSG.Open.Sz 0) = ⊥ := by
  have := szz_finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.Open.pCore 2 ↥(Sz 0)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(Sz 0)) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h1 : CFSG.Open.pCore 2 ↥(Sz 0) ≤ Subgroup.zpowers szzx :=
    hp.le_sylow_of_normal (szzSylow szzx szzx_order)
  have h2 : CFSG.Open.pCore 2 ↥(Sz 0) ≤ Subgroup.zpowers szzy :=
    hp.le_sylow_of_normal (szzSylow szzy szzy_order)
  exact le_bot_iff.mp (szz_zpowers_inf ▸ le_inf h1 h2)

end CFSG.Quasithin
