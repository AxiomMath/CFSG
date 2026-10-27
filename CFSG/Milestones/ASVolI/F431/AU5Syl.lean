module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieAutC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieClsC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocF
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylE
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylP
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnStd

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique

section Index

theorem burnsideF4m_index_odd {G : Type} [Group G] [Finite G] {N H : Subgroup G} (hNH : N ≤ H)
    {m : ℕ} (hm : Odd m)
    (hx : ∀ x ∈ H, ∃ t : G, (∀ n ∈ N, t * n * t⁻¹ ∈ N) ∧ t ^ m = 1 ∧ t⁻¹ * x ∈ N) :
    ¬ 2 ∣ (N.subgroupOf H).index := by
  have hnorm : (N.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNH]
    intro n k hn hk
    obtain ⟨t, ht, -, htk⟩ := hx k hk
    have e : k * n * k⁻¹ = t * ((t⁻¹ * k) * n * (t⁻¹ * k)⁻¹) * t⁻¹ := by group
    rw [e]
    exact ht _ (mul_mem (mul_mem htk hn) (inv_mem htk))
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : 2 ∣ Nat.card (H ⧸ N.subgroupOf H) := h2
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ N.subgroupOf H) 2 h2'
  obtain ⟨⟨x, hxH⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨t, -, htm, htx⟩ := hx x hxH
  have htH : t ∈ H := by
    have e : t = x * (t⁻¹ * x)⁻¹ := by group
    rw [e]
    exact mul_mem hxH (inv_mem (hNH htx))
  have e : (QuotientGroup.mk ⟨x, hxH⟩ : H ⧸ N.subgroupOf H) = QuotientGroup.mk ⟨t, htH⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show x⁻¹ * t ∈ N
    have e' : x⁻¹ * t = (t⁻¹ * x)⁻¹ := by group
    rw [e']
    exact inv_mem htx
  have hpow : (QuotientGroup.mk ⟨t, htH⟩ : H ⧸ N.subgroupOf H) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨t, htH⟩ : H) ^ m = 1 := Subtype.ext (by simp [htm])
    rw [this, QuotientGroup.mk_one]
  have hdvd := orderOf_dvd_of_pow_eq_one (e ▸ hpow)
  rw [hq] at hdvd
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hdvd)

end Index

section General

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem burnsideF4m_u5_isUnit_smul_one {lam : K} (hl : lam * h.bar lam = 1) :
    IsUnit (lam • (1 : Matrix (Fin 2) (Fin 2) K)).det := by
  have hl0 : lam ≠ 0 := left_ne_zero_of_mul_eq_one hl
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (IsUnit.mk0 lam hl0).pow _

theorem burnsideF4m_u5_cent_decomp {x : hypPSU h 2 1}
    (hx : x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) :
    ∃ (lam : K) (hl : lam * h.bar lam = 1) (B : SpecialLinearGroup (Fin 2) h.fixedField),
      ∃ s ∈ Ssub h, x = hypProj h 2 1 (lev (hK := h) (lam • (1 : Matrix (Fin 2) (Fin 2) K))
        (burnsideF4m_u5_isUnit_smul_one hl)) * hypProj h 2 1 (levHom h B * s) := by
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 1 x
  obtain ⟨A, C, x', d, -, hC, hd, -, hAJ, hmat⟩ :=
    syl_decomp_of_comm ((syl_mem_centralizer_iff g).1 hx)
  obtain ⟨lam, B, hl, hAB⟩ := syl_scalar_decomp hAJ
  obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub (hK := h) hC
  refine ⟨lam, hl, B, s, hs, ?_⟩
  rw [← map_mul]
  congr 1
  apply mat_injective
  rw [mat_mul, mat_mul, mat_lev, syl_mat_levHom, hsm, hmat, hd, hAB, ← mul_assoc, oddDiag_mul,
    mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Matrix.det_smul, det_slM,
    Matrix.det_one]

theorem burnsideF4m_u5_tau_comm {lam : K} (hl : lam * h.bar lam = 1)
    (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    lev (hK := h) (lam • (1 : Matrix (Fin 2) (Fin 2) K)) (burnsideF4m_u5_isUnit_smul_one hl) *
        levHom h B =
      levHom h B * lev (hK := h) (lam • (1 : Matrix (Fin 2) (Fin 2) K))
        (burnsideF4m_u5_isUnit_smul_one hl) := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_lev, syl_mat_levHom, oddDiag_mul, oddDiag_mul, mul_one, one_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem burnsideF4m_u5_oddDiag_pow (A : Matrix (Fin 2) (Fin 2) K) (d : K) (n : ℕ) :
    oddDiag h A d ^ n = oddDiag h (A ^ n) (d ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, oddDiag_one]
  | succ n ih => rw [pow_succ, ih, oddDiag_mul, ← pow_succ, ← pow_succ]

theorem burnsideF4m_u5_mat_pow (g : hypSU h 2 1) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem burnsideF4m_u5_tau_pow {lam : K} (hl : lam * h.bar lam = 1) :
    lev (hK := h) (lam • (1 : Matrix (Fin 2) (Fin 2) K)) (burnsideF4m_u5_isUnit_smul_one hl) ^
      (2 ^ f + 1) = 1 := by
  have hq : lam ^ (2 ^ f + 1) = 1 := by
    rw [h.bar_apply] at hl
    rw [pow_succ']
    exact hl
  apply mat_injective
  rw [burnsideF4m_u5_mat_pow, mat_lev, burnsideF4m_u5_oddDiag_pow, mat_one, smul_pow, one_pow, hq,
    one_smul, Matrix.det_smul, Matrix.det_one, mul_one, div_pow, ← map_pow, pow_right_comm, hq,
    one_pow, map_one, div_one, oddDiag_one]

theorem burnsideF4m_u5_conj_N {τ : hypSU h 2 1} (hS : ∀ s ∈ Ssub h, τ * s * τ⁻¹ ∈ Ssub h)
    (hL : ∀ B, τ * levHom h B = levHom h B * τ) {n : hypPSU h 2 1}
    (hn : n ∈ sylSY h ⊔ lY h) :
    hypProj h 2 1 τ * n * (hypProj h 2 1 τ)⁻¹ ∈ sylSY h ⊔ lY h := by
  have key : sylSY h ⊔ lY h ≤
      (sylSY h ⊔ lY h).comap (MulAut.conj (hypProj h 2 1 τ)).toMonoidHom := by
    refine sup_le ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul,
        ← map_mul]
      exact Subgroup.mem_sup_left ⟨_, hS s hs, rfl⟩
    · rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul,
        ← map_mul, hL B, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right ⟨_, ⟨B, rfl⟩, rfl⟩
  have := key hn
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem burnsideF4m_u5_uni_decomp {x : hypPSU h 2 1}
    (hxU : x ∈ hypProjUnitriangular h 2 1)
    (hx : x ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) :
    ∃ a : h.fixedField, ∃ s ∈ Ssub h,
      x = hypProj h 2 1 (levHom h (CFSG.LieType.Universal.Spin.upperSL2 a) * s) := by
  obtain ⟨u, hu, rfl⟩ := hxU
  obtain ⟨A, C, x', d, -, hC, hd, hA, hAJ, hmat⟩ :=
    syl_decomp_of_comm ((syl_mem_centralizer_iff u).1 hx)
  obtain ⟨⟨d00, d11, -, -, -⟩, ⟨l10, -, -, -, -, -, -, -, -, -⟩⟩ := U_entries hu
  have hA00 : A 0 0 = 1 := by rw [hA]; exact d00
  have hA11 : A 1 1 = 1 := by rw [hA]; exact d11
  have hA10 : A 1 0 = 0 := by rw [hA]; exact l10
  have hbar : h.bar (A 0 1) = A 0 1 := by
    obtain ⟨e00, -, -, -⟩ := syl_entries hAJ
    have := h.charP
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [hA00, map_one] at e00
    linear_combination e00 - A 0 1 * h2
  let a : h.fixedField := ⟨A 0 1, hbar⟩
  have hAeq : A = slM (CFSG.LieType.Universal.Spin.upperSL2 a) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slM_apply, a, hA00, hA11, hA10]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two, hA00, hA11, hA10]
    ring
  have hd1 : d = 1 := by rw [hd, hdet, map_one, div_one]
  obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub (hK := h) hC
  refine ⟨a, s, hs, ?_⟩
  congr 1
  apply mat_injective
  rw [mat_mul, syl_mat_levHom, hsm, hmat, hd1, hAeq]

theorem burnsideF4m_u5_sylow_t :
    IsSylowTwoOf
      (hypProjUnitriangular h 2 1 ⊓ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)))
      (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) := by
  have := h.finite
  have hf1 := h.one_le
  haveI : Finite (hypPSU h 2 1) := CFSG.RankThree.PartOne.U5K.Hyp.finite_hypPSU h
  have hP : hypProjUnitriangular h 2 1 ⊓ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) =
      sylSY h ⊔ sylBY h :=
    syl_inf_cent_eq_sup (fun x hU hx => burnsideF4m_u5_uni_decomp hU hx)
  have hPN : hypProjUnitriangular h 2 1 ⊓ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) ≤
      sylSY h ⊔ lY h := hP ▸ sup_le_sup_left syl_bY_le_lY _
  have hNC : sylSY h ⊔ lY h ≤ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) :=
    sup_le syl_sY_le_cent syl_lY_le_cent
  have hPcard : Nat.card (hypProjUnitriangular h 2 1 ⊓
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) : Subgroup (hypPSU h 2 1)) =
        (2 ^ f) ^ 8 * 2 ^ f := by
    rw [hP, syl_card_sup_bY]
  have hidx1 : ((hypProjUnitriangular h 2 1 ⊓
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))).subgroupOf (sylSY h ⊔ lY h)).index =
        (2 ^ f) ^ 2 - 1 := by
    have e := Subgroup.card_mul_index ((hypProjUnitriangular h 2 1 ⊓
      Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))).subgroupOf (sylSY h ⊔ lY h))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv, hPcard, syl_card_sup_lY] at e
    refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2 ^ f) ^ 8 * 2 ^ f) ?_
    rw [e]
    ring
  have hidx2 : ¬ 2 ∣ ((sylSY h ⊔ lY h).subgroupOf
      (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)))).index := by
    have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    refine burnsideF4m_index_odd hNC hodd fun x hx => ?_
    obtain ⟨lam, hl, B, s, hs, rfl⟩ := burnsideF4m_u5_cent_decomp hx
    refine ⟨_, fun n hn => burnsideF4m_u5_conj_N (fun s hs => lev_conj_mem_Ssub _ _ hs)
      (burnsideF4m_u5_tau_comm hl) hn, by rw [← map_pow, burnsideF4m_u5_tau_pow hl, map_one], ?_⟩
    rw [inv_mul_cancel_left, map_mul]
    exact mul_mem (Subgroup.mem_sup_right ⟨levHom h B, ⟨B, rfl⟩, rfl⟩)
      (Subgroup.mem_sup_left ⟨s, hs, rfl⟩)
  refine ⟨inf_le_right, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := f * 9) (by rw [hPcard, ← pow_succ, ← pow_mul])
  · intro h2
    have e := Subgroup.relIndex_mul_relIndex _ _ _ hPN hNC
    have h2' : 2 ∣ (hypProjUnitriangular h 2 1 ⊓
        Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))).relIndex (sylSY h ⊔ lY h) *
          (sylSY h ⊔ lY h).relIndex (Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))) := by
      rw [e]
      exact h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2' with h3 | h3
    · have h3' : 2 ∣ ((hypProjUnitriangular h 2 1 ⊓
          Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))).subgroupOf
            (sylSY h ⊔ lY h)).index := h3
      rw [hidx1] at h3'
      have h4 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
      have h5 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    · exact hidx2 h3

theorem burnsideF4m_unStdLoc_u5Y (hf : 2 ≤ f) :
    UnStdLoc (hypPSU h 2 1) (hypProjUnitriangular h 2 1) (z5Y h) (t5Y h) (vY h) (ucY h) (rY h)
      (kY h) := by
  have := h.charP
  exact
    { comm := comm_zt
      sylow_t := burnsideF4m_u5_sylow_t
      V_le := vY_le_Ct
      V_aut := fun φ hφ v hv => aut_vY h φ hφ v hv
      V_ab := fun a ha b hb => vY_ab ha hb
      V_sq := fun a ha => vY_sq ha
      z_V := z5Y_mem_vY
      U_le := ucY_le_vY
      U_aut := fun φ hφ u hu => aut_ucY h φ hφ u hu
      t_U := t5Y_mem_ucY
      K_le := kY_le_Ct
      K_perf := kY_perfect hf
      V_K := vY_le_kY
      K_cent := fun k hk u hu => kY_cent_ucY hk hu
      coset := coset_Y h hf
      nonsolv := nonsolv_Y hf
      R_le := rY_le_vY
      R_two := R_two_Y h hf
      R_cls := R_cls_Y h
      R_U := R_U_Y h
      z_cent := fun y hy => z5Y_cent hy
      P_U := fun y hy u hu => P_U_Y hy hu }

end General

end CFSG.Quasithin.H13.F431.Un.L5
