module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordSpecK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCoordGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoordA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6
  CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.CoordA6.Core

private theorem cpow_length (a : List ℕ) (n : ℕ) : (cpow a n).length = a.length := by
  induction n with
  | zero => simp [cpow]
  | succ n ih => simp [cpow, cmul]

private theorem cmul_getD {a b : List ℕ} {j : ℕ} (hj : j < b.length) :
    (cmul a b).getD j 0 = a.getD (b.getD j 0) 0 := by
  show (b.map (fun x => a.getD x 0)).getD j 0 = _
  rw [List.getD_eq_getElem (l := b.map (fun x => a.getD x 0)) (d := 0) (n := j)
      (by simpa using hj), List.getElem_map, List.getD_eq_getElem (l := b) (d := 0) hj]

private theorem cmul_code_eq_of_length {a a' : List ℕ} {κ : P10} (ha : a.length = 10)
    (ha' : a'.length = 10) (h : cmul a (code κ) = cmul a' (code κ)) : a = a' := by
  apply List.ext_getElem (by omega : a.length = a'.length)
  intro i hi hi'
  have h1 := congrArg (fun l => l.getD ((κ⁻¹ ⟨i, by omega⟩ : Fin 10) : ℕ) 0) h
  rw [cmul_getD (a := a) (b := code κ) (by rw [code_length]; exact (κ⁻¹ ⟨i, by omega⟩).isLt),
    cmul_getD (a := a') (b := code κ) (by rw [code_length]; exact (κ⁻¹ ⟨i, by omega⟩).isLt)] at h1
  rw [code_getD κ (κ⁻¹ ⟨i, by omega⟩), Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h1
  have hval : a.getD i 0 = a'.getD i 0 := h1
  calc a[i] = a.getD i 0 := (List.getD_eq_getElem (l := a) (d := 0) hi).symm
    _ = a'.getD i 0 := hval
    _ = a'[i] := List.getD_eq_getElem (l := a') (d := 0) hi'

private theorem KData.check_contains_y {D : KData} {TL : List (List ℕ)}
    (h : D.check TL = true) : D.K.lit.contains D.y = true := by
  simp only [KData.check, Bool.and_eq_true, and_assoc] at h
  tauto

private theorem fixCheck_data {K E : Subgroup P10} {TL : List (List ℕ)} {D : KData} {f : FixW}
    {L : List (List ℕ)} (hK : Desc K D.K.lit) (hE : Desc E L)
    (hfix : fixCheck TL D L f = true) :
    ∃ κ ε : P10, κ ∈ K ∧ ε ∈ E ∧ code κ = f.κ ∧ code ε = f.e ∧ E ≤ K ∧
      f.c.length = 10 ∧ f.c = code (κ * ε * κ⁻¹) ∧
      ((ε * (κ * ε * κ⁻¹)) ^ f.j) ^ D.p = 1 ∧
      (ε * (κ * ε * κ⁻¹)) ^ f.j ≠ 1 ∧ threeB TL D.y D.p f.w = true := by
  simp only [fixCheck, Bool.and_eq_true, and_assoc, beq_iff_eq, bne_iff_ne, ne_eq] at hfix
  obtain ⟨hEL, heL, hκL, hκe, hpow, hne, hthree⟩ := hfix
  obtain ⟨κ, hκK, hκcode⟩ := hK.surj f.κ (List.contains_iff_mem.mp hκL)
  obtain ⟨ε, hεE, hεcode⟩ := hE.surj f.e (List.contains_iff_mem.mp heL)
  have hLEK : E ≤ K := by
    intro x hx
    rw [hK.mem]
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp hEL) _ ((hE.mem x).mp hx))
  have hlen : f.c.length = 10 := by
    have h1 := congrArg List.length hpow
    simpa [cpow_length, cmul, cid] using h1
  have hκe' : cmul (code κ) (code ε) = cmul f.c (code κ) := by
    simpa [← hκcode, ← hεcode] using hκe
  have hfc : f.c = code (κ * ε * κ⁻¹) := by
    have h1 : cmul (code (κ * ε * κ⁻¹)) (code κ) = cmul f.c (code κ) := by
      calc cmul (code (κ * ε * κ⁻¹)) (code κ) = code ((κ * ε * κ⁻¹) * κ) :=
            (code_mul _ _).symm
        _ = code (κ * ε) := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = cmul (code κ) (code ε) := code_mul _ _
        _ = cmul f.c (code κ) := hκe'
    exact (cmul_code_eq_of_length (code_length _) hlen h1).symm
  have hec : cmul f.e f.c = code (ε * (κ * ε * κ⁻¹)) := by
    rw [hfc, ← hεcode]
    exact (code_mul ε (κ * ε * κ⁻¹)).symm
  have hqpow : ((ε * (κ * ε * κ⁻¹)) ^ f.j) ^ D.p = 1 := by
    have h1 := hpow
    rw [hec, ← code_pow, ← code_pow, code_eq_cid_iff] at h1
    exact h1
  have hqne : (ε * (κ * ε * κ⁻¹)) ^ f.j ≠ 1 := by
    intro hq1
    apply hne
    rw [hec, ← code_pow, hq1, code_one]
  exact ⟨κ, ε, hκK, hεE, hκcode, hεcode, hLEK, hlen, hfc, hqpow, hqne, hthree⟩

private theorem not_mem_pCoreOf_of_orderOf_prime {K : Subgroup P10} {x k : P10} {j p : ℕ}
    (hk : k ∈ K) (hord : orderOf ((x * (k * x * k⁻¹)) ^ j) = p)
    (hp : p.Prime) (hp2 : p ≠ 2) : x ∉ pCoreOf 2 K := by
  intro hx
  have hconj : k * x * k⁻¹ ∈ pCoreOf 2 K := by
    have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
    exact (Subgroup.mem_normalizer_iff.mp hnorm x).mp hx
  have hmem : (x * (k * x * k⁻¹)) ^ j ∈ pCoreOf 2 K := pow_mem (mul_mem hx hconj) j
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  obtain ⟨n, hn⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hP ⟨_, hmem⟩
  have hp2n : p = 2 ^ n := by
    rw [← hord, ← Subgroup.orderOf_mk _ hmem]
    exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hp2n
    exact hp.ne_one hp2n
  have h2dvd : 2 ∣ p := by
    rw [hp2n]
    exact dvd_pow_self 2 hn0
  have h2p : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd
  exact hp2 h2p.symm

private theorem exists_fixModel_of_some {G T₀ : Subgroup P10} {TL : List (List ℕ)}
    (hT : Desc T₀ TL) (hT2 : IsPGroup 2 T₀) {Ks : List KData}
    (hKs : ∀ D ∈ Ks, D.check TL = true)
    (hKg : ∀ D ∈ Ks, ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c)
    {D : KData} (hDmem : D ∈ Ks) {L : List (List ℕ)} {f : FixW}
    (hfix : fixCheck TL D L f = true) {E : Subgroup P10} (hE : Desc E L) :
    ∃ (K Xh : Subgroup P10) (p : ℕ), Coord.FixModel G T₀ E K Xh p := by
  have hDcheck : D.check TL = true := hKs D hDmem
  have hDy : D.K.lit.contains D.y = true := KData.check_contains_y hDcheck
  obtain ⟨K, hKG, hK, -, hTwo⟩ := kdata_spec hT hT2 hDcheck (hKg D hDmem)
  obtain ⟨κ, ε, hκK, hεE, hκcode, hεcode, hLEK, hlen, hfc, hqpow, hqne, hthree⟩ :=
    fixCheck_data hK hE hfix
  obtain ⟨y, -, hycode⟩ := hK.surj D.y (List.contains_iff_mem.mp hDy)
  obtain ⟨hTwoK, hcard⟩ := hTwo y hycode
  have hord : orderOf ((ε * (κ * ε * κ⁻¹)) ^ f.j) = D.p := by
    have : Fact D.p.Prime := ⟨hTwoK.prime⟩
    exact orderOf_eq_prime hqpow hqne
  have hnle : ¬ E ≤ pCoreOf 2 K := by
    intro hEpc
    exact not_mem_pCoreOf_of_orderOf_prime hκK hord hTwoK.prime hTwoK.odd (hEpc hεE)
  have hthree' : threeB TL (code y) D.p f.w = true := by rwa [← hycode] at hthree
  exact ⟨K, zpowers y, D.p, hKG, hLEK, hnle, hTwoK, hcard, three_spec hT hthree'⟩

theorem fix_spec {G T₀ Es₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {Ks : List KData} (hKs : ∀ D ∈ Ks, D.check TL = true)
    (hKg : ∀ D ∈ Ks, ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c)
    {El : List (List (List ℕ))} {fs : List (Option FixW)} {Est : List (List ℕ)}
    (hEst : ∀ x, x ∈ Es₀ ↔ code x ∈ Est) (h : fixAll TL Ks El fs Est = true)
    {E : Subgroup P10} {L : List (List ℕ)} (hL : L ∈ El) (hE : Desc E L) (hE1 : E ≠ ⊥) :
    (∃ (K Xh : Subgroup P10) (p : ℕ), Coord.FixModel G T₀ E K Xh p) ∨ E = Es₀ := by
  rw [fixAll, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hLen, hall⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have hziplen : (El.zip fs).length = El.length := by
    rw [List.length_zip, hLen, Nat.min_self]
  have hiZip : i < (El.zip fs).length := hziplen ▸ hi
  have hpass := hall _ (List.getElem_mem hiZip)
  rw [List.getElem_zip] at hpass
  cases hfs : fs[i] with
  | none =>
      simp only [hfs] at hpass
      rw [Bool.or_eq_true, beq_iff_eq] at hpass
      rcases hpass with hl | hset
      · have hbot : E = ⊥ := by
          ext x
          rw [hE.mem, hl, List.mem_singleton, code_eq_cid_iff, mem_bot]
        exact (hE1 hbot).elim
      · right
        ext x
        rw [hE.mem, setEq_mem hset (code x), hEst]
  | some f =>
      simp only [hfs] at hpass
      rw [Bool.and_eq_true, decide_eq_true_eq] at hpass
      obtain ⟨hfk, hfix⟩ := hpass
      exact Or.inl
        (exists_fixModel_of_some hT hT2 hKs hKg (getD_mem_of_lt KData.dflt hfk) hfix hE)

end CFSG.LocalAnalysis.WeakClosure81.CoordA6
