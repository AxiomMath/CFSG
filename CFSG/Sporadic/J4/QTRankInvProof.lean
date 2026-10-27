module

public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.J4.QTRankInvCheck

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open scoped Pointwise

theorem dihedral_conj_odd {G : Type*} [Group G] (s t : G) (hs : s * s = 1) (ht : t * t = 1)
    {m : ℕ} (hm : Odd m) (hp : (s * t) ^ m = 1) : ∃ h : G, h * s * h⁻¹ = t := by
  obtain ⟨k, rfl⟩ := hm
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    calc s * (s * t) * s⁻¹ = (s * s) * t * s⁻¹ := by group
      _ = t * s := by rw [hs, one_mul, hs']
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hs', ht']
  have h2 : s * (s * t) ^ k * s⁻¹ = ((s * t) ^ k)⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h3 : s * ((s * t) ^ k)⁻¹ * s⁻¹ = (s * t) ^ k := by
    calc s * ((s * t) ^ k)⁻¹ * s⁻¹ = s * (s * (s * t) ^ k * s⁻¹) * s⁻¹ := by rw [h2]
      _ = (s * s) * (s * t) ^ k * (s⁻¹ * s⁻¹) := by group
      _ = (s * t) ^ k := by rw [hs, hs', hs, one_mul, mul_one]
  have h4 : (s * t) ^ (2 * k) = (s * t)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hp
  refine ⟨(s * t) ^ k, ?_⟩
  calc (s * t) ^ k * s * ((s * t) ^ k)⁻¹
      = (s * t) ^ k * (s * ((s * t) ^ k)⁻¹ * s⁻¹) * s := by group
    _ = (s * t) ^ k * (s * t) ^ k * s := by rw [h3]
    _ = (s * t) ^ (2 * k) * s := by rw [← pow_add, two_mul]
    _ = t := by rw [h4, mul_inv_rev, ht', hs', mul_assoc, hs, mul_one]

section Mats

variable (hM : MatFacts)
include hM

theorem Mx_kJ {i : ℕ} (hi : i < 4) : Mx (kJ i) = rowsMatrix ((kRowsTab ())[i]?.getD idRows) := by
  have : (kRowsTab ())[i]? = some (kRows i) := by
    simp [kRowsTab, hi]
  rw [this, Option.getD_some]
  exact Mx_wordProd hM (kWords.getD i [])

theorem Mx_foldl : ∀ (s : List ℕ), (∀ i ∈ s, i < 4) → ∀ (acc : Array V2) (g : J),
    Mx g = rowsMatrix acc →
      Mx (g * (s.map kJ).prod) =
        rowsMatrix (s.foldl (fun acc i => mulRows acc ((kRowsTab ())[i]?.getD idRows)) acc)
  | [], _, acc, g, h => by simpa using h
  | i :: s, hs, acc, g, h => by
    rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
    refine Mx_foldl s (fun x hx => hs x (List.mem_cons_of_mem _ hx)) _ _ ?_
    rw [map_mul, h, Mx_kJ hM (hs i (List.mem_cons_self ..)), rowsMatrix_mulRows]

theorem Mx_Kel {e : ℕ} (he : e < 1024) : Mx (Kel e) = rowsMatrix (KelRows e) := by
  have := Mx_foldl hM (pcSeq e) (pcSeq_lt e he) idRows 1 (by rw [map_one, rowsMatrix_idRows])
  rw [one_mul] at this
  exact this

theorem Mx_etaR (c : ℕ) : Mx (eta uJ 11 c) = rowsMatrix (etaR c) := Mx_eta hM 11 le_rfl c

end Mats

@[expose] noncomputable def gEl (i : ℕ) : J := if i = 0 then a else if i = 1 then b else b⁻¹

section Conj

variable (hM : MatFacts)
include hM

theorem Mx_b : Mx b = rowsMatrix rowsB := by
  rw [Mx_apply, b_coe, gB_val hM, rowsMatrix_rowsB]

omit hM in
theorem Mx_inv_of (g : J) (R : Array V2)
    (h : rowsMatrix R = (((g : GL (Fin 112) (ZMod 2))⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2))) : Mx g⁻¹ = rowsMatrix R := by
  rw [h, Mx_apply]
  rfl

theorem Mx_a_inv : Mx a⁻¹ = rowsMatrix (baseInvs[0]?.getD idRows) := by
  have hb := baseInvs_spec hM 0
  have hA : (baseGL 0 : GL (Fin 112) (ZMod 2)) = (a : GL (Fin 112) (ZMod 2)) := by
    simp [baseGL, a_coe]
  rw [hA] at hb
  exact Mx_inv_of a _ hb

theorem Mx_b_inv : Mx b⁻¹ = rowsMatrix (baseInvs[1]?.getD idRows) := by
  have hb := baseInvs_spec hM 1
  have hB : (baseGL 1 : GL (Fin 112) (ZMod 2)) = (b : GL (Fin 112) (ZMod 2)) := by
    simp [baseGL, b_coe]
  rw [hB] at hb
  exact Mx_inv_of b _ hb

theorem Mx_gEl {i : ℕ} (hi : i < 3) :
    Mx (gEl i) = rowsMatrix (gMat i) ∧ Mx (gEl i)⁻¹ = rowsMatrix (gInv i) := by
  interval_cases i
  · refine ⟨?_, ?_⟩
    · show Mx a = rowsMatrix (if (0 : ℕ) == 2 then _ else _)
      simpa [gMat, baseMats] using Mx_a hM
    ·
      show Mx a⁻¹ = rowsMatrix (if (0 : ℕ) == 2 then _ else _)
      rw [if_neg (by decide)]
      exact Mx_a_inv hM
  · refine ⟨?_, ?_⟩
    · show Mx b = rowsMatrix (if (1 : ℕ) == 2 then _ else _)
      simpa [gMat, baseMats] using Mx_b hM
    · show Mx b⁻¹ = rowsMatrix (if (1 : ℕ) == 2 then _ else _)
      rw [if_neg (by decide)]
      exact Mx_b_inv hM
  · refine ⟨?_, ?_⟩
    · show Mx b⁻¹ = rowsMatrix (if (2 : ℕ) == 2 then _ else _)
      simpa [gMat, baseMats] using Mx_b_inv hM
    · show Mx b⁻¹⁻¹ = rowsMatrix (if (2 : ℕ) == 2 then _ else _)
      rw [inv_inv]
      simpa [gInv, baseMats, baseInvs] using Mx_b hM

end Conj

theorem invOKT_spec {T K : Array (Array V2)} {x : ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ)}
    (h : invOKT T K x = true) :
    x.1 < 1024 ∧ x.2.1 < 2048 ∧
      eqRows (mulRows (KelRowsK K x.1) (KelRowsK K x.1)) (etaRT T x.2.1) = true ∧
      classCover x = true ∧ ∀ y ∈ x.2.2, fuseOKT T K x.1 y = true := by
  unfold invOKT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem classCover_spec {x : ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ)} (h : classCover x = true) {c : ℕ}
    (hc : c < 2048) (hq : c ^^^ actT (tabE x.1) c = x.2.1) :
    ∃ y ∈ x.2.2, ∃ m < 2048, m ^^^ actT (tabE x.1) m = c ^^^ y.1 := by
  unfold classCover at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true,
    List.contains_iff_mem, imSet, List.mem_eraseDups, List.mem_map] at h
  rcases h c hc with h1 | ⟨y, hy, m, hm, hmy⟩
  · exact absurd hq h1
  · exact ⟨y, hy, m, hm, hmy⟩

theorem fuseOKT_spec {T K : Array (Array V2)} {e : ℕ} {y : ℕ × ℕ × ℕ × ℕ}
    (h : fuseOKT T K e y = true) :
    y.2.1 < 3 ∧ 0 < y.2.2.1 ∧ y.2.2.1 < 2048 ∧ y.2.2.2 % 2 = 1 ∧
      eqRows (powRows (mulRows (mulRows (etaRT T y.1) (KelRowsK K e))
        (mulRows (mulRows (gMat y.2.1) (etaRT T y.2.2.1)) (gInv y.2.1))) y.2.2.2) idRows = true := by
  unfold fuseOKT at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

section Classify

variable (hF : J4Facts)
include hF

theorem eta_conj_orbit {o : ℕ × List (ℕ × List ℤ) × List (List ℕ)} (ho : o ∈ orbits)
    {p : ℕ × List ℤ} (hp : p ∈ o.2.1) : IsConj (eta uJ 11 o.1) (eta uJ 11 p.1) := by
  obtain ⟨hlet, hfold⟩ := orbit_words o ho p hp
  rw [isConj_iff]
  refine ⟨(p.2.map XJ).prod, ?_⟩
  rw [word_conj XJ act p.2 (fun ℓ hℓ c => hX_all hF.mat (hlet ℓ hℓ) c), hfold]

theorem eta_conj_root {c : ℕ} (hc0 : c ≠ 0) (hc : c < 2 ^ 11) :
    IsConj (eta uJ 11 1) (eta uJ 11 c) ∨ IsConj (eta uJ 11 3) (eta uJ 11 c) := by
  obtain ⟨o, ho, p, hp, hpc⟩ := orbit_cover c hc hc0
  have hconj := eta_conj_orbit hF ho hp
  rw [hpc] at hconj
  rcases orbit_roots o ho with h | h
  · left; rwa [h] at hconj
  · right; rwa [h] at hconj

omit hF in
theorem invAllOK_spec : ∀ x ∈ invData, invOKT (uTab (locMats ()) (locInvs ())) (kRowsTab ()) x =
    true := by
  have h := invAllOK_true
  unfold invAllOK at h
  simpa only [List.all_eq_true] using h

end Classify

section Classify2

variable (hF : J4Facts)
include hF

theorem inv_conj_of_mem_P0 {r : J} (hr : r ∈ P0) (hsq : r * r = 1) (hne : r ≠ 1) :
    IsConj (eta uJ 11 1) r ∨ IsConj (eta uJ 11 3) r := by
  have hM := hF.mat
  obtain ⟨c, hc, e, he, hre⟩ := exists_eta_mul_Kel hM hF hr
  have hAct : Acts r (tabE e) := by rw [hre]; exact Acts_eta_mul_Kel hM he
  have hAct2 := hAct.mul hAct
  rw [hsq] at hAct2
  have hcomp : compT (tabE e) (tabE e) = idT := hAct2.unique hM Acts.one
  by_cases hid : tabE e = idT
  ·
    have hrE : r ∈ Eg uJ 11 := by
      refine centralizer_Hj hM hF r (P0_le_Hj hr) (fun y hy => ?_)
      obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hAct.2 d hd
      rw [hid, actT_idT hd] at this
      calc r * eta uJ 11 d = (r * eta uJ 11 d * r⁻¹) * r := by group
        _ = eta uJ 11 d * r := by rw [this]
    obtain ⟨c', hc', hrc'⟩ := (mem_Eg_iff (elem_uJ hM)).1 hrE
    have hc'0 : c' ≠ 0 := fun h0 => hne (by rw [hrc', h0, eta_zero])
    rcases eta_conj_root hF hc'0 hc' with h | h
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
    rcases eta_conj_root hF (by omega : n ≠ 0) (by simpa using hn) with h | h
    · left; exact h.trans h4
    · right; exact h.trans h4

theorem inv_conj_root {r : J} (hsq : r * r = 1) (hne : r ≠ 1) :
    IsConj (eta uJ 11 1) r ∨ IsConj (eta uJ 11 3) r := by
  have hM := hF.mat
  have hp : IsPGroup 2 (Subgroup.zpowers r) := by
    have hord : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    have hc : Nat.card (Subgroup.zpowers r) = orderOf r := Nat.card_zpowers r
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hc, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [hc, h]; rfl)
  obtain ⟨g, hg⟩ := exists_conj_le_P0 hM hF _ hp
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
  rcases inv_conj_of_mem_P0 hF hr' hsq' hne' with h | h
  · left; exact h.trans hconj.symm
  · right; exact h.trans hconj.symm

end Classify2

end CFSG.Sporadic.J4.QT
