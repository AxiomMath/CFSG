module

public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.J4.QT2LocBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open scoped Pointwise

theorem card_J_factorization_b (hF : J4Basic) : (Nat.card J).factorization 2 = 21 := by
  rw [hF.cardJ]
  have h : (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem exists_conj_le_P0_b
    (hF : J4Basic) (A : Subgroup J) (hpA : IsPGroup 2 A) :
    ∃ g : J, ∀ x ∈ A, g⁻¹ * x * g ∈ P0 := by
  obtain ⟨Q, hAQ⟩ := hpA.exists_le_sylow
  let P : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0_b hF, card_J_factorization_b hF])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P Q
  have hQ : (Q : Subgroup J) = MulAut.conj g • P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ MulAut.conj g • P0 := by rw [← hQ]; exact hAQ hx
  obtain ⟨s, hs, hsx⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) P0).1 hxQ
  have : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    group
  rw [this]
  exact hs

theorem eta_conj_orbit_b (hM : MatFacts)
    {o : ℕ × List (ℕ × List ℤ) × List (List ℕ)} (ho : o ∈ orbits)
    {p : ℕ × List ℤ} (hp : p ∈ o.2.1) : IsConj (eta uJ 11 o.1) (eta uJ 11 p.1) := by
  obtain ⟨hlet, hfold⟩ := orbit_words o ho p hp
  rw [isConj_iff]
  refine ⟨(p.2.map XJ).prod, ?_⟩
  rw [word_conj XJ act p.2 (fun ℓ hℓ c => hX_all hM (hlet ℓ hℓ) c), hfold]

theorem eta_conj_root_b
    (hM : MatFacts) {c : ℕ} (hc0 : c ≠ 0) (hc : c < 2 ^ 11) :
    IsConj (eta uJ 11 1) (eta uJ 11 c) ∨ IsConj (eta uJ 11 3) (eta uJ 11 c) := by
  obtain ⟨o, ho, p, hp, hpc⟩ := orbit_cover c hc hc0
  have hconj := eta_conj_orbit_b hM ho hp
  rw [hpc] at hconj
  rcases orbit_roots o ho with h | h
  · left; rwa [h] at hconj
  · right; rwa [h] at hconj

theorem inv_conj_of_mem_P0_b
    (hF : J4Basic) {r : J} (hr : r ∈ P0) (hsq : r * r = 1)
    (hne : r ≠ 1) : IsConj (eta uJ 11 1) r ∨ IsConj (eta uJ 11 3) r := by
  have hM := hF.mat
  obtain ⟨c, hc, e, he, hre⟩ := exists_eta_mul_Kel_b hF hr
  have hAct : Acts r (tabE e) := by rw [hre]; exact Acts_eta_mul_Kel hM he
  have hAct2 := hAct.mul hAct
  rw [hsq] at hAct2
  have hcomp : compT (tabE e) (tabE e) = idT := hAct2.unique hM Acts.one
  by_cases hid : tabE e = idT
  · have hrE : r ∈ Eg uJ 11 := by
      refine centralizer_Hj_b hF r (P0_le_Hj hr) (fun y hy => ?_)
      obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hAct.2 d hd
      rw [hid, actT_idT hd] at this
      calc r * eta uJ 11 d = (r * eta uJ 11 d * r⁻¹) * r := by group
        _ = eta uJ 11 d * r := by rw [this]
    obtain ⟨c', hc', hrc'⟩ := (mem_Eg_iff (elem_uJ hM)).1 hrE
    have hc'0 : c' ≠ 0 := fun h0 => hne (by rw [hrc', h0, eta_zero])
    rcases eta_conj_root_b hM hc'0 hc' with h | h
    · left; rwa [← hrc'] at h
    · right; rwa [← hrc'] at h
  · have hinv : isInvE e = true := by
      simp [isInvE, hcomp, hid]
    obtain ⟨x, hx, hxe⟩ := invData_cover e he hinv
    obtain ⟨hx1, hq, hKK, hcov, hfuse⟩ := invOKT_spec (invAllOK_spec x hx)
    have hK := Acts_Kel hM he
    have hKel2 : Kel e * Kel e = eta uJ 11 x.2.1 := by
      apply Mx_injective
      have h1 := congrArg rowsMatrix (eqRows_iff.1 hKK)
      rw [hxe, rowsMatrix_mulRows] at h1
      rw [map_mul, Mx_Kel hM he, Mx_etaR hM]
      exact h1
    have hKc : Kel e * eta uJ 11 c = eta uJ 11 (actT (tabE e) c) * Kel e := by
      have := hK.2 c hc
      rwa [mul_inv_eq_iff_eq_mul] at this
    have hrr : r * r = eta uJ 11 (c ^^^ actT (tabE e) c ^^^ x.2.1) := by
      rw [hre]
      calc eta uJ 11 c * Kel e * (eta uJ 11 c * Kel e)
          = eta uJ 11 c * (Kel e * eta uJ 11 c) * Kel e := by group
        _ = eta uJ 11 c * (eta uJ 11 (actT (tabE e) c) * Kel e) * Kel e := by rw [hKc]
        _ = eta uJ 11 c * eta uJ 11 (actT (tabE e) c) * (Kel e * Kel e) := by group
        _ = eta uJ 11 c * eta uJ 11 (actT (tabE e) c) * eta uJ 11 x.2.1 := by rw [hKel2]
        _ = eta uJ 11 (c ^^^ actT (tabE e) c ^^^ x.2.1) := by
          rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl]
    have hxor0 : c ^^^ actT (tabE e) c ^^^ x.2.1 = 0 := by
      have hlt : c ^^^ actT (tabE e) c ^^^ x.2.1 < 2 ^ 11 :=
        Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hc (actT_lt hK.1 c)) (by simpa using hq)
      refine eta_inj hM _ hlt 0 (by norm_num) ?_
      rw [← hrr, hsq, eta_zero]
    have hqc : c ^^^ actT (tabE x.1) c = x.2.1 := by
      rw [hxe]
      exact Nat.eq_of_xor_eq_zero hxor0
    obtain ⟨y, hy, m, hm, hmy⟩ := classCover_spec hcov (by simpa using hc) hqc
    rw [hxe] at hmy
    have hηinv : (eta uJ 11 m)⁻¹ = eta uJ 11 m :=
      inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) m)
    have hconj : eta uJ 11 m * r * (eta uJ 11 m)⁻¹ = eta uJ 11 y.1 * Kel e := by
      rw [hηinv, hre]
      have hKm : Kel e * eta uJ 11 m = eta uJ 11 (actT (tabE e) m) * Kel e := by
        have := hK.2 m (by simpa using hm)
        rwa [mul_inv_eq_iff_eq_mul] at this
      calc eta uJ 11 m * (eta uJ 11 c * Kel e) * eta uJ 11 m
          = eta uJ 11 m * eta uJ 11 c * (Kel e * eta uJ 11 m) := by group
        _ = eta uJ 11 m * eta uJ 11 c * (eta uJ 11 (actT (tabE e) m) * Kel e) := by rw [hKm]
        _ = (eta uJ 11 m * eta uJ 11 c * eta uJ 11 (actT (tabE e) m)) * Kel e := by group
        _ = eta uJ 11 (m ^^^ c ^^^ actT (tabE e) m) * Kel e := by
          rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl]
        _ = eta uJ 11 y.1 * Kel e := by
          have : m ^^^ c ^^^ actT (tabE e) m = y.1 := by
            have h1 : m ^^^ c ^^^ actT (tabE e) m = c ^^^ (m ^^^ actT (tabE e) m) := by
              rw [Nat.xor_comm m c, Nat.xor_assoc]
            rw [h1, hmy, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
          rw [this]
    have hyf := hfuse y hy
    rw [hxe] at hyf
    obtain ⟨hg3, hn0, hn, hodd, hpow⟩ := fuseOKT_spec hyf
    have hR2 : (eta uJ 11 y.1 * Kel e) * (eta uJ 11 y.1 * Kel e) = 1 := by
      rw [← hconj]
      calc eta uJ 11 m * r * (eta uJ 11 m)⁻¹ * (eta uJ 11 m * r * (eta uJ 11 m)⁻¹)
          = eta uJ 11 m * (r * r) * (eta uJ 11 m)⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    set g := gEl y.2.1 with hgdef
    set n := y.2.2.1 with hndef
    have hee : (g * eta uJ 11 n * g⁻¹) * (g * eta uJ 11 n * g⁻¹) = 1 := by
      calc (g * eta uJ 11 n * g⁻¹) * (g * eta uJ 11 n * g⁻¹)
          = g * (eta uJ 11 n * eta uJ 11 n) * g⁻¹ := by group
        _ = 1 := by rw [eta_sq (elem_uJ hM)]; group
    have hMR : Mx (eta uJ 11 y.1 * Kel e) = rowsMatrix (mulRows (etaR y.1) (KelRows e)) := by
      rw [map_mul, Mx_etaR hM, Mx_Kel hM he, rowsMatrix_mulRows]
    have hMe : Mx (g * eta uJ 11 n * g⁻¹) =
        rowsMatrix (mulRows (mulRows (gMat y.2.1) (etaR n)) (gInv y.2.1)) := by
      rw [map_mul, map_mul, (Mx_gEl hM hg3).1, (Mx_gEl hM hg3).2, Mx_etaR hM, rowsMatrix_mulRows,
        rowsMatrix_mulRows]
    have hpowJ : ((eta uJ 11 y.1 * Kel e) * (g * eta uJ 11 n * g⁻¹)) ^ y.2.2.2 = 1 := by
      apply Mx_injective
      have h1 := congrArg rowsMatrix (eqRows_iff.1 hpow)
      rw [rowsMatrix_powRows, rowsMatrix_idRows] at h1
      rw [map_pow, map_mul, hMR, hMe, map_one Mx, ← rowsMatrix_mulRows]
      exact h1
    obtain ⟨k, hk⟩ := @dihedral_conj_odd J inferInstance (eta uJ 11 y.1 * Kel e)
      (g * eta uJ 11 n * g⁻¹) hR2 hee y.2.2.2 (Nat.odd_iff.2 hodd) hpowJ
    have h1 : IsConj (eta uJ 11 n) (g * eta uJ 11 n * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
    have h2 : IsConj (eta uJ 11 y.1 * Kel e) (g * eta uJ 11 n * g⁻¹) := isConj_iff.2 ⟨k, hk⟩
    have h3 : IsConj r (eta uJ 11 y.1 * Kel e) := isConj_iff.2 ⟨eta uJ 11 m, hconj⟩
    have h4 : IsConj (eta uJ 11 n) r := (h1.trans h2.symm).trans h3.symm
    rcases eta_conj_root_b hM (by omega : n ≠ 0) (by simpa using hn) with h | h
    · left; exact h.trans h4
    · right; exact h.trans h4

theorem inv_conj_root_b
    (hF : J4Basic) {r : J} (hsq : r * r = 1) (hne : r ≠ 1) :
    IsConj (eta uJ 11 1) r ∨ IsConj (eta uJ 11 3) r := by
  have hp : IsPGroup 2 (Subgroup.zpowers r) := by
    have hord : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    have hc : Nat.card (Subgroup.zpowers r) = orderOf r := Nat.card_zpowers r
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hc, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [hc, h]; rfl)
  obtain ⟨g, hg⟩ := exists_conj_le_P0_b hF _ hp
  have hr' : g⁻¹ * r * g ∈ P0 := hg r (Subgroup.mem_zpowers r)
  have hsq' : (g⁻¹ * r * g) * (g⁻¹ * r * g) = 1 := by
    calc (g⁻¹ * r * g) * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g := by group
      _ = 1 := by rw [hsq]; group
  have hne' : g⁻¹ * r * g ≠ 1 := by
    intro h
    apply hne
    calc r = g * (g⁻¹ * r * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hconj : IsConj r (g⁻¹ * r * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  rcases inv_conj_of_mem_P0_b hF hr' hsq' hne' with h | h
  · left; exact h.trans hconj.symm
  · right; exact h.trans hconj.symm

end CFSG.Sporadic.J4.QT2
