module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3Check
public import CFSG.Sporadic.Schreier.Co3First

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native

private theorem co3K_parts :
    (allLt 28 fun L => isInvA 276 (co3KArr L) (invCand 276 (co3KArr L))) = true ∧
    siftA 276 co3TLevels co3TBaseArr 0 co3KE = true ∧
    eqA 276 (compA 276 co3KE co3KE) (idA 276) = true ∧
    eqA 276 co3KE (idA 276) = false ∧ eqA 276 co3KE co3ZArr = false ∧
    co3KECheck co3TLevels co3KE co3ZArr = true ∧
    siftA 276 co3TLevels co3TBaseArr 0 co3KT1 = true ∧
    eqA 276 (compA 276 co3KT1 co3KE) (compA 276 (compA 276 co3KE co3ZArr) co3KT1) = true ∧
    siftA 276 co3ChainLevels co3ChainBaseArr 0 co3KG1 = true ∧
    eqA 276 (compA 276 co3KG1 co3KE) (compA 276 co3ZArr co3KG1) = true ∧
    siftA 276 co3MLevels co3MBaseArr 0 co3KX5 = true ∧
    eqA 276 (co3KPow co3KX5 5) (idA 276) = true ∧ eqA 276 co3KX5 (idA 276) = false ∧
    co3KFix1 (co3KKappa co3KX5) = true ∧
    siftA 276 co3MLevels co3MBaseArr 0 co3KX7 = true ∧
    eqA 276 (co3KPow co3KX7 7) (idA 276) = true ∧ eqA 276 co3KX7 (idA 276) = false ∧
    co3KFix1 (co3KKappa co3KX7) = true ∧
    co3KK3Check co3TLevels co3KGens co3KGensInv co3KD = true ∧
    co3KK5Check co3KD co3KW co3ZArr = true := by
  have h := co3K_check
  simp only [co3KCheck, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  exact h

private theorem getElem!_ofFn' {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

private theorem iff_of_beq_beq {x y u v : ℕ} (h : ((x == y) == (u == v)) = true) :
    x = y ↔ u = v := by
  by_cases h1 : x = y <;> by_cases h2 : u = v <;> simp_all

@[expose] def co3KPerm (L : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 (co3KArr L)

theorem rep_co3KPerm {L : ℕ} (hL : L < 28) :
    Rep 276 (co3KArr L) (co3KPerm L) :=
  (rep_permOfArr (allLt_spec co3K_parts.1 hL)).1

@[expose] def co3Ke : Equiv.Perm (Fin 276) := co3KPerm 0

@[expose] def co3Kt1 : Equiv.Perm (Fin 276) := co3KPerm 1

@[expose] def co3Kg1 : Equiv.Perm (Fin 276) := co3KPerm 2

@[expose] def co3Kx5 : Equiv.Perm (Fin 276) := co3KPerm 3

@[expose] def co3Kx7 : Equiv.Perm (Fin 276) := co3KPerm 4

@[expose] def co3Kd (i : ℕ) : Equiv.Perm (Fin 276) := co3KPerm (5 + i)

theorem rep_co3Ke : Rep 276 co3KE co3Ke :=
  rep_co3KPerm (L := 0) (by norm_num)

theorem rep_co3Kt1 : Rep 276 co3KT1 co3Kt1 :=
  rep_co3KPerm (L := 1) (by norm_num)

theorem rep_co3Kg1 : Rep 276 co3KG1 co3Kg1 :=
  rep_co3KPerm (L := 2) (by norm_num)

theorem rep_co3Kx5 : Rep 276 co3KX5 co3Kx5 :=
  rep_co3KPerm (L := 3) (by norm_num)

theorem rep_co3Kx7 : Rep 276 co3KX7 co3Kx7 :=
  rep_co3KPerm (L := 4) (by norm_num)

theorem co3KD_size : co3KD.size = 23 := by
  simp [co3KD]

theorem co3KD_get {i : ℕ} (hi : i < 23) : co3KD[i]! = co3KArr (5 + i) := by
  rw [co3KD]
  exact getElem!_ofFn' _ hi

theorem rep_co3KD {i : ℕ} (hi : i < 23) :
    Rep 276 co3KD[i]! (co3Kd i) := by
  rw [co3KD_get hi]
  exact rep_co3KPerm (by omega)

theorem co3KGens_size : co3KGens.size = 8 := by
  simp [co3KGens, co3TArrs_size]

theorem rep_co3KGens {k : ℕ} (hk : k < 8) :
    Rep 276 co3KGens[k]! (co3TGen k) := by
  rw [co3KGens, co3TExtract_get hk]
  exact rep_co3TGen (by omega)

theorem rep_invCand_co3KGens {k : ℕ} (hk : k < 8) :
    Rep 276 (invCand 276 co3KGens[k]!) (co3TGen k)⁻¹ := by
  have h := (rep_permOfArr (co3TArrs_inv k (by rw [co3TArrs_size]; omega))).2
  rw [rawInvs, co3_getElem!_map (by rw [co3TArrs_size]; omega)] at h
  rw [co3KGens, co3TExtract_get hk]
  exact h

theorem rep_co3KGensInv {k : ℕ} (hk : k < 8) :
    Rep 276 co3KGensInv[k]! (co3TGen k)⁻¹ := by
  rw [co3KGensInv, co3_getElem!_map (by rw [co3KGens_size]; exact hk)]
  exact rep_invCand_co3KGens hk

theorem rep_co3KPow {a : Array ℕ} {g : Equiv.Perm (Fin 276)} (h : Rep 276 a g) :
    ∀ k : ℕ, Rep 276 (co3KPow a k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pow_succ']
    exact rep_compA h (rep_co3KPow h k)

@[expose] def co3Kw (t : ℕ) : Equiv.Perm (Fin 276) :=
  if t < 64 then co3TGen (t % 8) * co3TGen (t / 8) * (co3TGen (t % 8))⁻¹ * (co3TGen (t / 8))⁻¹
  else co3TGen (t - 64) ^ 4

theorem co3KW_size : co3KW.size = 72 := by
  simp [co3KW]

theorem rep_co3KW {t : ℕ} (ht : t < 72) :
    Rep 276 co3KW[t]! (co3Kw t) := by
  rw [co3KW, getElem!_ofFn' _ ht]
  dsimp only
  by_cases h : t < 64
  · rw [if_pos h, co3Kw, if_pos h, commA]
    have h1 : t / 8 < 8 := by omega
    have h2 : t % 8 < 8 := Nat.mod_lt _ (by norm_num)
    exact rep_compA (rep_compA (rep_compA (rep_co3KGens h2) (rep_co3KGens h1))
      (rep_invCand_co3KGens h2)) (rep_invCand_co3KGens h1)
  · rw [if_neg h, co3Kw, if_neg h]
    exact rep_co3KPow (rep_co3KGens (by omega)) 4

theorem co3Kw_cases {t : ℕ} (ht : t < 72) :
    (∃ a < 8, ∃ b < 8, co3Kw t = co3TGen a * co3TGen b * (co3TGen a)⁻¹ * (co3TGen b)⁻¹) ∨
      ∃ a < 8, co3Kw t = co3TGen a ^ 4 := by
  by_cases h : t < 64
  · exact Or.inl ⟨t % 8, Nat.mod_lt _ (by norm_num), t / 8, by omega, by rw [co3Kw, if_pos h]⟩
  · exact Or.inr ⟨t - 64, by omega, by rw [co3Kw, if_neg h]⟩

theorem co3KAllProd3_spec
    {p : Array ℕ → Bool} (h : co3KAllProd3 co3TLevels p = true) {x : Equiv.Perm (Fin 276)}
    (hx : x ∈ co3T) : ∃ g : Array ℕ, Rep 276 g x ∧ p g = true := by
  have hF := chainCheckFacts co3TChain_check.1
  obtain ⟨a, ha, b, hb, c, hc', hprod⟩ := ChainArrays.exists_prod3 co3TArrays (by norm_num)
    co3TChain_check.1 (by decide) (fun i h3 hi => absurd hi (by
      change ¬ i < 3; omega)) hx
  have h0 : (0 : ℕ) < co3TChain.baseCount := by decide
  have h1 : (1 : ℕ) < co3TChain.baseCount := by decide
  have h2 : (2 : ℕ) < co3TChain.baseCount := by decide
  rw [co3KAllProd3] at h
  refine ⟨compA 276 (compA 276 (co3TLevels[0]!).tr[a]! (co3TLevels[1]!).tr[b]!)
    (co3TLevels[2]!).tr[c]!, ?_, allLt_spec (allLt_spec (allLt_spec h ha) hb) hc'⟩
  rw [← hprod]
  exact rep_compA (rep_compA (co3TArrays.rep_levT hF h0 ha) (co3TArrays.rep_levT hF h1 hb))
    (co3TArrays.rep_levT hF h2 hc')

theorem co3Ke_mem :
    co3Ke ∈ co3T :=
  mem_co3T_of_sift rep_co3Ke co3K_parts.2.1

theorem co3Ke_mul_self : co3Ke * co3Ke = 1 :=
  eq_of_eqA (rep_compA rep_co3Ke rep_co3Ke) rep_idA co3K_parts.2.2.1

theorem co3Ke_conj
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3T) :
    g * co3Ke = co3Ke * g ∨ g * co3Ke = co3Ke * co3Z * g := by
  have hE := co3K_parts.2.2.2.2.2.1
  rw [co3KECheck] at hE
  obtain ⟨a, ha, hp⟩ := co3KAllProd3_spec hE hg
  simp only [Bool.or_eq_true] at hp
  rcases hp with hp | hp
  · exact Or.inl (eq_of_eqA (rep_compA ha rep_co3Ke) (rep_compA rep_co3Ke ha) hp)
  · exact Or.inr (eq_of_eqA (rep_compA ha rep_co3Ke)
      (rep_compA (rep_compA rep_co3Ke rep_co3Z) ha) hp)

theorem co3Kt1_mem :
    co3Kt1 ∈ co3T :=
  mem_co3T_of_sift rep_co3Kt1 co3K_parts.2.2.2.2.2.2.1

theorem co3Kt1_mul_e :
    co3Kt1 * co3Ke = co3Ke * co3Z * co3Kt1 :=
  eq_of_eqA (rep_compA rep_co3Kt1 rep_co3Ke) (rep_compA (rep_compA rep_co3Ke rep_co3Z) rep_co3Kt1)
    co3K_parts.2.2.2.2.2.2.2.1

theorem co3Kg1_mem :
    co3Kg1 ∈ co3P :=
  mem_co3P_of_sift rep_co3Kg1 co3K_parts.2.2.2.2.2.2.2.2.1

theorem co3Kg1_mul_e :
    co3Kg1 * co3Ke = co3Z * co3Kg1 :=
  eq_of_eqA (rep_compA rep_co3Kg1 rep_co3Ke) (rep_compA rep_co3Z rep_co3Kg1)
    co3K_parts.2.2.2.2.2.2.2.2.2.1

theorem card_support_of_fix_one {σ : Equiv.Perm (Fin 36)} {p : Fin 36}
    (h : ∀ i, σ i = i ↔ i = p) : σ.support.card = 35 := by
  have : σ.support = Finset.univ.erase p := by
    ext i
    simp [Equiv.Perm.mem_support, h]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem fix_one_of_co3KFix1 {a : Array ℕ} {σ : Equiv.Perm (Fin 36)} (ha : Rep 36 a σ)
    (h : co3KFix1 a = true) : σ.support.card = 35 := by
  rw [co3KFix1, anyLt_iff] at h
  obtain ⟨p, hp, h⟩ := h
  refine card_support_of_fix_one (p := ⟨p, hp⟩) fun i => ?_
  have hi : ((a[(i : ℕ)]! == (i : ℕ)) == ((i : ℕ) == p)) = true := allLt_spec h i.2
  rw [ha i] at hi
  simp only [Fin.ext_iff]
  exact iff_of_beq_beq hi

theorem co3Kx5_mem :
    co3Kx5 ∈ co3M :=
  mem_co3M_of_sift rep_co3Kx5 co3K_parts.2.2.2.2.2.2.2.2.2.2.1

theorem co3Kx5_pow : co3Kx5 ^ 5 = 1 :=
  eq_of_eqA (rep_co3KPow rep_co3Kx5 5) rep_idA co3K_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem co3Kx5_ne_one : co3Kx5 ≠ 1 := by
  intro h
  have h1 := co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [(eqA_iff rep_co3Kx5 rep_idA).2 h] at h1
  exact absurd h1 (by decide)

theorem co3Kx5_support :
    (co3Kappa ⟨co3Kx5, co3Kx5_mem⟩).support.card = 35 :=
  fix_one_of_co3KFix1 (rep_kappa (m := ⟨co3Kx5, co3Kx5_mem⟩) rep_co3Kx5)
    co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem co3Kx7_mem :
    co3Kx7 ∈ co3M :=
  mem_co3M_of_sift rep_co3Kx7 co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem co3Kx7_pow : co3Kx7 ^ 7 = 1 :=
  eq_of_eqA (rep_co3KPow rep_co3Kx7 7) rep_idA co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem co3Kx7_ne_one : co3Kx7 ≠ 1 := by
  intro h
  have h1 := co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [(eqA_iff rep_co3Kx7 rep_idA).2 h] at h1
  exact absurd h1 (by decide)

theorem co3Kx7_support :
    (co3Kappa ⟨co3Kx7, co3Kx7_mem⟩).support.card = 35 :=
  fix_one_of_co3KFix1 (rep_kappa (m := ⟨co3Kx7, co3Kx7_mem⟩) rep_co3Kx7)
    co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem co3K_inv_cases
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3T)
    (h2 : g * g = 1) (h1 : g ≠ 1)
    (hc : ∀ k < 8, g * (co3TGen k * g * (co3TGen k)⁻¹) = co3TGen k * g * (co3TGen k)⁻¹ * g) :
    ∃ i < 23, g = co3Kd i := by
  have hK := co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [co3KK3Check] at hK
  obtain ⟨a, ha, hp⟩ := co3KAllProd3_spec hK hg
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rw [(eqA_iff (rep_compA ha ha) rep_idA).2 h2] at hp
    exact absurd hp (by decide)
  · exact absurd (eq_of_eqA ha rep_idA hp) h1
  · have hall : allLt co3KGens.size (fun k => commutesA 276 a
        (compA 276 (compA 276 co3KGens[k]! a) co3KGensInv[k]!)) = true := by
      rw [allLt_iff]
      intro k hk
      rw [co3KGens_size] at hk
      have hr := rep_compA (rep_compA (rep_co3KGens hk) ha) (rep_co3KGensInv hk)
      rw [commutesA]
      exact (eqA_iff (rep_compA ha hr) (rep_compA hr ha)).2 (hc k hk)
    rw [hall] at hp
    exact absurd hp (by decide)
  · simp only [anyLt_iff] at hp
    obtain ⟨i, hi, hp⟩ := hp
    rw [co3KD_size] at hi
    exact ⟨i, hi, eq_of_eqA ha (rep_co3KD hi) hp⟩

theorem co3K_witness
    {i j : ℕ} (hi : i < 23) (hj : j < 23) (hc : co3Kd i * co3Kd j = co3Kd j * co3Kd i)
    (hiz : co3Kd i ≠ co3Z) (hjz : co3Kd j ≠ co3Z) (hji : co3Kd j ≠ co3Kd i)
    (hjiz : co3Kd j ≠ co3Kd i * co3Z) :
    ∃ w : Equiv.Perm (Fin 276),
      ((∃ a < 8, ∃ b < 8, w = co3TGen a * co3TGen b * (co3TGen a)⁻¹ * (co3TGen b)⁻¹) ∨
        ∃ a < 8, w = co3TGen a ^ 4) ∧
      ¬ (w * co3Kd i = co3Kd i * w ∧ w * co3Kd j = co3Kd j * w) := by
  have hK := co3K_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [co3KK5Check] at hK
  have hp := allLt_spec (allLt_spec hK (show i < co3KD.size by rw [co3KD_size]; exact hi))
    (show j < co3KD.size by rw [co3KD_size]; exact hj)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hp
  have ri := rep_co3KD hi
  have rj := rep_co3KD hj
  rcases hp with ((((hp | hp) | hp) | hp) | hp) | hp
  · rw [commutesA, (eqA_iff (rep_compA ri rj) (rep_compA rj ri)).2 hc] at hp
    exact absurd hp (by decide)
  · exact absurd (eq_of_eqA ri rep_co3Z hp) hiz
  · exact absurd (eq_of_eqA rj rep_co3Z hp) hjz
  · exact absurd (eq_of_eqA rj ri hp) hji
  · exact absurd (eq_of_eqA rj (rep_compA ri rep_co3Z) hp) hjiz
  · simp only [anyLt_iff] at hp
    obtain ⟨t, ht, hp⟩ := hp
    rw [co3KW_size] at ht
    refine ⟨co3Kw t, co3Kw_cases ht, fun ⟨h1, h2⟩ => ?_⟩
    have rw' := rep_co3KW ht
    rw [commutesA, commutesA, (eqA_iff (rep_compA rw' ri) (rep_compA ri rw')).2 h1,
      (eqA_iff (rep_compA rw' rj) (rep_compA rj rw')).2 h2] at hp
    exact absurd hp (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K
