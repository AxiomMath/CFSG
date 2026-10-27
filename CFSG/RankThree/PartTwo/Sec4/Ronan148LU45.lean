module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Tor
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58Blk
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Tor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S

theorem eq_one_of_pow_27 {G : Type} [Group G] {N : Subgroup G}
    (hN : ∀ z ∈ N, z ^ 3 = 1 → z = 1) {x : G} (hx : x ∈ N) (h27 : x ^ 27 = 1) : x = 1 := by
  have h9 : x ^ 9 = 1 := hN _ (N.pow_mem hx 9) (by rw [← pow_mul]; exact h27)
  have h3 : x ^ 3 = 1 := hN _ (N.pow_mem hx 3) (by rw [← pow_mul]; exact h9)
  exact hN x hx h3

theorem E27Move.of_surjective {G H : Type} [Group G] [Group H] [Finite G] (π : G →* H)
    (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) (h : E27Move G) :
    E27Move H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro E hE s hs hs1
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.2]; norm_num)
  set P : Subgroup G := E.comap π with hP
  have hPE : Nat.card E ∣ Nat.card P := by
    refine Subgroup.card_dvd_of_surjective (f := (π.comp P.subtype).codRestrict E fun x => x.2) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  obtain ⟨Q₀, hQ₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 3 (n := 3)
    (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]; exact hPE)
  set Q : Subgroup G := Q₀.map P.subtype with hQ
  have hQcard : Nat.card Q = 27 := by
    rw [hQ, Subgroup.card_map_of_injective P.subtype_injective, hQ₀]; norm_num
  have hQP : Q ≤ P := Subgroup.map_subtype_le Q₀
  have hQ27 : ∀ x ∈ Q, x ^ 27 = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := Q) (x := ⟨x, hx⟩)
    rw [hQcard] at this
    simpa using congrArg Subtype.val this
  have hinj : ∀ x ∈ Q, ∀ y ∈ Q, π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 := eq_one_of_pow_27 hker h1 (hQ27 _ (Q.mul_mem hx (Q.inv_mem hy)))
    rwa [mul_inv_eq_one] at h2
  have hQE : Q.map π = E := by
    refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨x, hx, hxe⟩ => hxe ▸ hQP hx) ?_
    rw [hE.2]
    have hi : Function.Injective (π.comp Q.subtype) := fun x y hxy =>
      Subtype.ext (hinj _ x.2 _ y.2 hxy)
    have hrange : (π.comp Q.subtype).range = Q.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, hQcard]
  have hQe : Late.IsE27 Q := by
    refine ⟨⟨⟨⟨fun a b => Subtype.ext (hinj _ (Q.mul_mem a.2 b.2) _ (Q.mul_mem b.2 a.2) ?_)⟩⟩,
      fun x hx => ?_⟩, hQcard⟩
    · have ha : π a ∈ E := hQP a.2
      have hb : π b ∈ E := hQP b.2
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hE.1.1.is_comm.comm ⟨π a, ha⟩ ⟨π b, hb⟩)
    · refine eq_one_of_pow_27 hker ?_ ?_
      · rw [MonoidHom.mem_ker, map_pow]
        exact hE.1.2 _ (hQP hx)
      · rw [← pow_mul]
        have h27 := hQ27 x hx
        calc x ^ (3 * 27) = (x ^ 27) ^ 3 := by rw [← pow_mul, mul_comm]
          _ = 1 := by rw [h27, one_pow]
  rw [← hQE] at hs
  obtain ⟨s', hs'Q, rfl⟩ := hs
  have hs'1 : s' ≠ 1 := by
    rintro rfl
    exact hs1 (map_one π)
  obtain ⟨n, hn, hns⟩ := h Q hQe s' hs'Q hs'1
  refine ⟨π n, ?_, fun hmem => hns ?_⟩
  · rw [← hQE]
    exact Subgroup.le_normalizer_map π ⟨n, hn, rfl⟩
  ·
    have h1 : π n * π s' * (π n)⁻¹ ∈ Subgroup.zpowers (π s') :=
      (Subgroup.mem_normalizer_iff.mp hmem _).mp (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hnQ : n * s' * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hn s').mp hs'Q
    have hk' : s' ^ k = n * s' * n⁻¹ :=
      hinj _ (Q.zpow_mem hs'Q k) _ hnQ (by rw [map_zpow, hk, map_mul, map_mul, map_inv])
    have hle : (Subgroup.zpowers s').map (MulAut.conj n).toMonoidHom ≤ Subgroup.zpowers s' := by
      rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.mpr ?_
      change n * s' * n⁻¹ ∈ Subgroup.zpowers s'
      rw [← hk']
      exact Subgroup.zpow_mem_zpowers s' k
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])

section Emb

open Matrix

variable {K : Type} [Field K]

@[expose] def blk4G (A : GL (Fin 3) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (A : Matrix (Fin 3) (Fin 3) K) 0 0
      (diagonal fun _ : Fin 1 => (((GeneralLinearGroup.det A)⁻¹ : Kˣ) : K)))

theorem det_blk4G (A : GL (Fin 3) K) : (blk4G A).det = 1 := by
  rw [blk4G, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal, Fin.prod_univ_one,
    ← GeneralLinearGroup.val_det_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem blk4G_mul (A B : GL (Fin 3) K) : blk4G (A * B) = blk4G A * blk4G B := by
  simp only [blk4G, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Units.val_mul,
    map_mul, mul_inv, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem blk4G_one : blk4G (1 : GL (Fin 3) K) = 1 := by
  simp [blk4G, reindex_apply]

@[expose] def emb4G : GL (Fin 3) K →* GL (Fin 4) K where
  toFun A := ⟨blk4G A, blk4G A⁻¹, by rw [← blk4G_mul, mul_inv_cancel, blk4G_one],
    by rw [← blk4G_mul, inv_mul_cancel, blk4G_one]⟩
  map_one' := Units.ext blk4G_one
  map_mul' A B := Units.ext (blk4G_mul A B)

theorem coe_emb4G (A : GL (Fin 3) K) : ((emb4G A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    blk4G A := rfl

theorem emb4G_injective : Function.Injective (emb4G (K := K)) := by
  intro A B h
  have h' : blk4G A = blk4G B := by rw [← coe_emb4G, ← coe_emb4G, h]
  apply Units.ext
  ext i j
  have := congrFun₂ h' (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i))
    (finSumFinEquiv (m := 3) (n := 1) (Sum.inl j))
  simpa [blk4G, reindex_apply] using this

theorem blk4G_diagGL (t : Fin 3 → Kˣ) :
    blk4G (TauCeti.diagGL t) = diagonal ![(t 0 : K), (t 1 : K), (t 2 : K),
      (((t 0 * t 1 * t 2)⁻¹ : Kˣ) : K)] := by
  have hdet : GeneralLinearGroup.det (TauCeti.diagGL t) = t 0 * t 1 * t 2 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, TauCeti.diagGL_coe, det_diagonal, Fin.prod_univ_three]
    simp
  rw [blk4G, hdet, TauCeti.diagGL_coe, fromBlocks_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Emb

section U45

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.DFT

theorem fact_prime_five_U45 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] fact_prime_five_U45

abbrev F25 : Type := GaloisField 5 (2 * 1)

noncomputable abbrev SU45 : Subgroup (GL (Fin 4) F25) := CFSG.Open.StatedSU 4 (5 ^ 1) F25

theorem card_units_F25 : Nat.card F25ˣ = 24 := by
  classical
  have := Fintype.ofFinite F25
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    GaloisField.card 5 (2 * 1) (by norm_num)]
  norm_num

theorem exists_omega25 : ∃ ω : F25ˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 (by rw [card_units_F25]; norm_num)

theorem det_pow_mul_det25 {A : Matrix (Fin 3) (Fin 3) F25}
    (hA : (A.map (· ^ (5 ^ 1)))ᵀ * A = 1) : A.det ^ (5 ^ 1) * A.det = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_transpose, det_one] at h
  have hmap : (A.map (· ^ (5 ^ 1))).det = A.det ^ (5 ^ 1) := by
    have := (iterateFrobenius F25 5 1).map_det A
    rw [iterateFrobenius_def] at this
    rw [this, RingHom.mapMatrix_apply]
    congr 1
  rwa [hmap] at h

theorem unitary_blk4G (A : GL (Fin 3) F25)
    (hA : ((A : Matrix (Fin 3) (Fin 3) F25).map (· ^ (5 ^ 1)))ᵀ * A = 1) :
    ((blk4G A).map (· ^ (5 ^ 1)))ᵀ * blk4G A = 1 := by
  have hdet := det_pow_mul_det25 hA
  have hc : (((GeneralLinearGroup.det A)⁻¹ : F25ˣ) : F25) ^ (5 ^ 1) *
      (((GeneralLinearGroup.det A)⁻¹ : F25ˣ) : F25) = 1 := by
    rw [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, inv_pow, ← mul_inv, hdet,
      inv_one]
  have h0 : ((0 : F25) ^ (5 ^ 1)) = 0 := by norm_num
  simp only [blk4G, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
    fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
    Matrix.map_zero (fun x : F25 => x ^ (5 ^ 1)) h0,
    diagonal_map (f := fun x : F25 => x ^ (5 ^ 1)) h0, diagonal_transpose, transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal, hA]
  rw [show (fun _ : Fin 1 => (((GeneralLinearGroup.det A)⁻¹ : F25ˣ) : F25) ^ (5 ^ 1) *
      (((GeneralLinearGroup.det A)⁻¹ : F25ˣ) : F25)) = fun _ => 1 from funext fun _ => hc]
  rw [diagonal_one, fromBlocks_one]
  simp

theorem emb4G_mem {A : GL (Fin 3) F25}
    (hA : ((A : Matrix (Fin 3) (Fin 3) F25).map (· ^ (5 ^ 1)))ᵀ * A = 1) :
    emb4G A ∈ SU45 :=
  Subgroup.subset_closure ⟨det_blk4G A, unitary_blk4G A hA⟩

theorem unitary_tau3_25 {ω : F25ˣ} (hω3 : ω ^ 3 = 1) (v : Fin 3 → ZMod 3) :
    (((tau3 hω3 (.ofAdd v) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25).map
      (· ^ (5 ^ 1)))ᵀ * (tau3 hω3 (.ofAdd v) : GL (Fin 3) F25) = 1 := by
  have h0 : ((0 : F25) ^ (5 ^ 1)) = 0 := by norm_num
  rw [tau3_apply, TauCeti.diagGL_coe, diagonal_map (f := fun x : F25 => x ^ (5 ^ 1)) h0,
    diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, ← pow_mul,
    show (v i).val * (5 ^ 1 + 1) = 3 * (2 * (v i).val) by ring, pow_mul, hω3, one_pow,
    Units.val_one]

theorem unitary_permGL3_25 :
    (((permGL3 : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25).map (· ^ (5 ^ 1)))ᵀ *
      (permGL3 : GL (Fin 3) F25) = 1 := by
  rw [coe_permGL3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat3, Matrix.mul_apply, Fin.sum_univ_three]

theorem card_SU45 : Nat.card SU45 = 3 ^ (3 + 1) * 364000000 := by
  have h := CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_statedSU_eq_int
    (unitaryFieldData_galoisField 5 1 le_rfl) (n := 4) (by norm_num)
  have h' : ((Nat.card SU45 : ℕ) : ℤ) = ((3 ^ (3 + 1) * 364000000 : ℕ) : ℤ) := by
    rw [h]
    decide
  exact_mod_cast h'

section Torus

variable {ω : F25ˣ} (hω3 : ω ^ 3 = 1)

theorem tau3_mem_SU45 (v : Multiplicative (Fin 3 → ZMod 3)) : emb4G (tau3 hω3 v) ∈ SU45 := by
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective v
  exact emb4G_mem (unitary_tau3_25 hω3 v)

@[expose] noncomputable def τU : Multiplicative (Fin 3 → ZMod 3) →* SU45 :=
  (emb4G.comp (tau3 hω3)).codRestrict SU45 (tau3_mem_SU45 hω3)

theorem τU_injective (hω : orderOf ω = 3) : Function.Injective (τU hω3) := fun _ _ h =>
  tau3_injective hω3 hω (emb4G_injective (congrArg Subtype.val h))

theorem coe_τU (v : Fin 3 → ZMod 3) :
    (((τU hω3 (.ofAdd v) : SU45) : GL (Fin 4) F25) : Matrix (Fin 4) (Fin 4) F25) =
      diagonal fun i => ((expHom ω hω3 (.ofAdd (Sec21.TablesL44.ext v i)) : F25ˣ) : F25) := by
  change blk4G (tau3 hω3 (.ofAdd v)) = _
  rw [tau3_apply, blk4G_diagGL]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · show ((((ω ^ (v 0).val) * (ω ^ (v 1).val) * (ω ^ (v 2).val))⁻¹ : F25ˣ) : F25) =
      ((expHom ω hω3 (.ofAdd (-(v 0 + v 1 + v 2))) : F25ˣ) : F25)
    congr 1
    rw [ofAdd_neg, map_inv, ofAdd_add, ofAdd_add, map_mul, map_mul]
    rfl

@[expose] noncomputable def wU : SU45 := ⟨emb4G permGL3, emb4G_mem unitary_permGL3_25⟩

theorem wU_pow_three : wU ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  change emb4G permGL3 ^ 3 = 1
  rw [← map_pow, permGL3_pow_three, map_one]

theorem wU_mul_τU (v : Fin 3 → ZMod 3) :
    wU * τU hω3 (.ofAdd v) = τU hω3 (.ofAdd (rot3 v)) * wU := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  change emb4G permGL3 * emb4G (tau3 hω3 (.ofAdd v)) =
    emb4G (tau3 hω3 (.ofAdd (rot3 v))) * emb4G permGL3
  rw [← map_mul, ← map_mul, permGL3_mul_tau3]

theorem exists_conj_eq_torusU (hω : orderOf ω = 3) (E : Subgroup SU45) (hE : Late.IsE27 E) :
    ∃ x : SU45, E.map (MulAut.conj x).toMonoidHom = torusOmega (τU hω3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_torusExt (τU_injective hω3 hω) wU_pow_three (wU_mul_τU hω3)
    rot3_ne KFacts.KS21.L44.card_V3 card_SU45 (by norm_num)
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE.2]; norm_num)
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq SU45 P₀ Q
  have hle : E.map (MulAut.conj h⁻¹).toMonoidHom ≤ P₀ := map_conj_inv_le hh hEQ
  rw [hP₀] at hle
  have hfix : 3 * Nat.card {u : Fin 3 → ZMod 3 // rot3 u = u ∧ 3 • u = 0} <
      Nat.card (torusOmega (τU hω3)) := by
    rw [card_torusOmega (τU_injective hω3 hω)]
    exact card_fix3_lt
  obtain ⟨-, heq⟩ := card_le_of_le_torusExt (τU_injective hω3 hω) wU_pow_three (wU_mul_τU hω3)
    rot3_norm' hfix (isElemAbelian_map _ hE.1) hle
  refine ⟨h⁻¹, heq ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hE.2,
    card_torusOmega (τU_injective hω3 hω), card_V3_three]
  norm_num

theorem move_U45 : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ σ : Equiv.Perm (Fin 4),
    Equiv.Perm.sign σ = 1 ∧
      ∀ c : ZMod 3, Sec21.TablesL44.res (Sec21.TablesL44.ext v ∘ σ) ≠ c • v := by
  decide

theorem exists_permMat_SU45 (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1) :
    ∃ n : SU45, ((n : GL (Fin 4) F25) : Matrix (Fin 4) (Fin 4) F25) = σ.toPEquiv.toMatrix := by
  have hPP' : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F25) *
      σ.symm.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hP'P : (σ.symm.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F25) *
      σ.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let g : GL (Fin 4) F25 := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, hPP', hP'P⟩
  have hdet : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F25).det = 1 := by
    have h := Matrix.det_permutation (R := F25) σ
    rw [Equiv.Perm.permMatrix] at h
    rw [h, hσ]
    simp
  have hmap : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F25).map (· ^ (5 ^ 1)) =
      σ.toPEquiv.toMatrix := by
    have h := PEquiv.map_toMatrix (iterateFrobenius F25 5 1) σ.toPEquiv
    rw [← h]
    congr 1
  have hT : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F25)ᵀ = σ.symm.toPEquiv.toMatrix := by
    rw [← PEquiv.toMatrix_symm, Equiv.toPEquiv_symm]
  have hmem : g ∈ SU45 := Subgroup.subset_closure ⟨hdet, by
    change ((σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) F25).map (· ^ (5 ^ 1)))ᵀ *
      σ.toPEquiv.toMatrix = 1
    rw [hmap, hT, hP'P]⟩
  exact ⟨⟨g, hmem⟩, rfl⟩

theorem conj_permMat_τU {n : SU45} {σ : Equiv.Perm (Fin 4)}
    (hn : ((n : GL (Fin 4) F25) : Matrix (Fin 4) (Fin 4) F25) = σ.toPEquiv.toMatrix)
    (v : Fin 3 → ZMod 3) :
    n * τU hω3 (.ofAdd v) * n⁻¹ =
      τU hω3 (.ofAdd (Sec21.TablesL44.res (Sec21.TablesL44.ext v ∘ σ))) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_τU, coe_τU, hn]
  have hsum : ∑ i, (Sec21.TablesL44.ext v ∘ σ) i = 0 := by
    change ∑ i, Sec21.TablesL44.ext v (σ i) = 0
    rw [Equiv.sum_comp σ (Sec21.TablesL44.ext v)]
    exact Sec21.TablesL44.sum_ext v
  rw [Sec21.TablesL44.ext_res hsum, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [submatrix_apply, diagonal_apply, Function.comp_apply, id]
  by_cases h : σ i = j
  · subst h
    simp
  · have h' : ¬ i = σ.symm j := fun h' => h (by rw [h', Equiv.apply_symm_apply])
    simp [h, h']

theorem moves_torusU (hω : orderOf ω = 3) :
    ∀ s ∈ torusOmega (τU hω3), s ≠ 1 → ∃ n ∈ Subgroup.normalizer (torusOmega (τU hω3) : Set SU45),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set SU45) := by
  rintro _ ⟨a, -, rfl⟩ hs1
  have ha : a ≠ 0 := fun h => hs1 (by rw [h, ofAdd_zero, map_one])
  obtain ⟨σ, hσs, hσ⟩ := move_U45 a ha
  obtain ⟨n, hn⟩ := exists_permMat_SU45 σ hσs
  have hT : (torusOmega (τU hω3)).map (MulAut.conj n).toMonoidHom = torusOmega (τU hω3) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
      refine ⟨Sec21.TablesL44.res (Sec21.TablesL44.ext b ∘ σ),
        KFacts.KS21.L44.three_smul_V3 _, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_permMat_τU hω3 hn b]
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hns : n * τU hω3 (.ofAdd a) * n⁻¹ ∉ Subgroup.zpowers (τU hω3 (.ofAdd a)) := by
    rw [conj_permMat_τU hω3 hn a]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hk
    have h2 := congrArg Multiplicative.toAdd (τU_injective hω3 hω hk)
    rw [toAdd_zpow_zmod, toAdd_ofAdd] at h2
    exact hσ (k : ZMod 3) h2.symm
  exact ⟨n, (mover_of_conj hT hns).1, (mover_of_conj hT hns).2⟩

end Torus

theorem e27Move_SU45 : E27Move SU45 := by
  obtain ⟨ω, hω⟩ := exists_omega25
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  exact e27Move_of_conj (exists_conj_eq_torusU hω3 hω) (moves_torusU hω3 hω)

@[expose] noncomputable def projEquivU : CFSG.Open.StatedProj SU45 ≃*
    CFSG.Assembly.RankThreeEven.projSU 4 5 1 :=
  (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage SU45).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 5 1))

@[expose] noncomputable def piU : SU45 →* CFSG.Assembly.RankThreeEven.projSU 4 5 1 :=
  projEquivU.toMonoidHom.comp
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 4) F25).subgroupOf SU45))

theorem piU_surjective : Function.Surjective piU :=
  projEquivU.surjective.comp (QuotientGroup.mk'_surjective _)

theorem mem_ker_piU {z : SU45} (hz : z ∈ piU.ker) :
    z ∈ (CFSG.Open.StatedScalars (Fin 4) F25).subgroupOf SU45 := by
  rw [MonoidHom.mem_ker] at hz
  have h : QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 4) F25).subgroupOf SU45) z = 1 :=
    (map_eq_one_iff projEquivU projEquivU.injective).mp hz
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

theorem piU_ker (z : SU45) (hz : z ∈ piU.ker) (hz3 : z ^ 3 = 1) : z = 1 := by
  have hzS := mem_ker_piU hz
  rw [Subgroup.mem_subgroupOf, CFSG.Open.StatedScalars, MonoidHom.mem_range] at hzS
  obtain ⟨c, hc⟩ := hzS
  have hdet := CFSG.RankThree.Classical2.statedSU_le_ker_det 4 (5 ^ 1) F25 z.2
  rw [MonoidHom.mem_ker, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg Subtype.val hz3
    rw [Subgroup.coe_pow, ← hc, ← map_pow] at h
    apply Units.ext
    have := congrArg (fun g : GL (Fin 4) F25 => (g : Matrix (Fin 4) (Fin 4) F25) 0 0) h
    simpa [GeneralLinearGroup.scalar, diagonal_pow] using this
  have hc1 : c = 1 := by
    have h4 : c ^ 4 = c ^ 3 * c := pow_succ c 3
    rw [hdet, hc3, one_mul] at h4
    exact h4.symm
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem e27Move_projSU45 : E27Move (CFSG.Assembly.RankThreeEven.projSU 4 5 1) :=
  E27Move.of_surjective piU piU_surjective piU_ker e27Move_SU45

theorem piU_injOn {B : Subgroup SU45} (hB : ∀ x ∈ B, x ^ 3 = 1) :
    Function.Injective (piU.comp B.subtype) := by
  intro x y hxy
  have h1 : (x : SU45) * (y : SU45)⁻¹ ∈ piU.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    exact mul_inv_eq_one.mpr hxy
  have h2 := piU_ker _ h1 (hB _ (B.mul_mem x.2 (B.inv_mem y.2)))
  exact Subtype.ext (mul_inv_eq_one.mp h2)

@[expose] def incl2 : Multiplicative (Fin 2 → ZMod 3) →* Multiplicative (Fin 3 → ZMod 3) where
  toFun v := .ofAdd ![Multiplicative.toAdd v 0, Multiplicative.toAdd v 1, 0]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp

theorem incl2_injective : Function.Injective incl2 := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  have h' := congrArg (fun u : Multiplicative (Fin 3 → ZMod 3) => Multiplicative.toAdd u
    (Fin.castSucc i)) h
  fin_cases i <;> simpa [incl2] using h'

theorem unitary_diagGL_neg :
    (((TauCeti.diagGL ![-1, -1, 1] : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25).map
      (· ^ (5 ^ 1)))ᵀ * (TauCeti.diagGL ![-1, -1, 1] : GL (Fin 3) F25) = 1 := by
  have h0 : ((0 : F25) ^ (5 ^ 1)) = 0 := by norm_num
  rw [TauCeti.diagGL_coe, diagonal_map (f := fun x : F25 => x ^ (5 ^ 1)) h0,
    diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have hm : ((-1 : F25ˣ) : F25) ^ (5 ^ 1) * ((-1 : F25ˣ) : F25) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ,
      show (5 : ℕ) ^ 1 + 1 = 2 * 3 by norm_num, pow_mul, neg_one_sq, one_pow, Units.val_one]
  fin_cases i
  · exact hm
  · exact hm
  · simp

@[expose] noncomputable def tU : SU45 :=
  ⟨emb4G (TauCeti.diagGL ![-1, -1, 1]), emb4G_mem unitary_diagGL_neg⟩

theorem tU_sq : tU ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  change emb4G (TauCeti.diagGL ![-1, -1, 1]) ^ 2 = 1
  rw [← map_pow, ← map_pow]
  have : (![-1, -1, 1] : Fin 3 → F25ˣ) ^ 2 = 1 := by
    funext i
    fin_cases i <;> simp
  rw [this, map_one, map_one]

theorem tU_comm {ω : F25ˣ} (hω3 : ω ^ 3 = 1) (v : Multiplicative (Fin 3 → ZMod 3)) :
    tU * τU hω3 v = τU hω3 v * tU := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  change emb4G (TauCeti.diagGL ![-1, -1, 1]) * emb4G (tau3 hω3 v) =
    emb4G (tau3 hω3 v) * emb4G (TauCeti.diagGL ![-1, -1, 1])
  rw [← map_mul, ← map_mul]
  congr 1
  change TauCeti.diagGL ![-1, -1, 1] * TauCeti.diagGL (powVec ω hω3 v) =
    TauCeti.diagGL (powVec ω hω3 v) * TauCeti.diagGL ![-1, -1, 1]
  rw [← map_mul, ← map_mul, mul_comm (![-1, -1, 1] : Fin 3 → F25ˣ)]

theorem tU_ne_one : piU tU ≠ 1 := by
  intro h
  have hS := mem_ker_piU (by rw [MonoidHom.mem_ker]; exact h)
  rw [Subgroup.mem_subgroupOf, CFSG.Open.StatedScalars, MonoidHom.mem_range] at hS
  obtain ⟨c, hc⟩ := hS
  have h0 := congrArg (fun g : GL (Fin 4) F25 => (g : Matrix (Fin 4) (Fin 4) F25) 0 0) hc
  have h3 := congrArg (fun g : GL (Fin 4) F25 => (g : Matrix (Fin 4) (Fin 4) F25) 3 3) hc
  change _ = blk4G (TauCeti.diagGL ![-1, -1, 1]) 0 0 at h0
  change _ = blk4G (TauCeti.diagGL ![-1, -1, 1]) 3 3 at h3
  rw [blk4G_diagGL] at h0 h3
  simp [GeneralLinearGroup.scalar] at h0 h3
  have hm : ((-1 : F25ˣ) : F25) = 1 := by rw [← h0, h3, Units.val_one]
  have h2 : (2 : F25) = 0 := by
    simp only [Units.val_neg, Units.val_one] at hm
    linear_combination -hm
  have h5 : (5 : F25) = 0 := by
    have := CharP.cast_eq_zero F25 5
    exact_mod_cast this
  have : (1 : F25) = 0 := by linear_combination 3 * h2 - h5
  exact one_ne_zero this

theorem invE9_projSU45 : InvE9 (CFSG.Assembly.RankThreeEven.projSU 4 5 1) := by
  obtain ⟨ω, hω⟩ := exists_omega25
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  set T := torusOmega (τU hω3) with hT
  set F₀ : Subgroup SU45 := ((τU hω3).comp incl2).range with hF₀
  have hF₀T : F₀ ≤ T := by
    rintro _ ⟨v, rfl⟩
    exact ⟨Multiplicative.toAdd (incl2 v), KFacts.KS21.L44.three_smul_V3 _, rfl⟩
  have hTe : CFSG.Assembly.IsElemAbelian 3 T := isElemAbelian_torusOmega _
  have hT3 : ∀ x ∈ T, x ^ 3 = 1 := fun x hx => hTe.2 x hx
  have hF₀e : CFSG.Assembly.IsElemAbelian 3 F₀ := isElemAbelian_mono hF₀T hTe
  have hTc : Nat.card T = 27 := by
    rw [hT, card_torusOmega (τU_injective hω3 hω), card_V3_three]
    norm_num
  have hF₀c : Nat.card F₀ = 9 := by
    rw [hF₀, ← Nat.card_congr (MonoidHom.ofInjective (f := (τU hω3).comp incl2)
      (fun x y h => incl2_injective (τU_injective hω3 hω h))).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
    norm_num
  have hcardmap : ∀ B : Subgroup SU45, B ≤ T → Nat.card (B.map piU) = Nat.card B := by
    intro B hBT
    have hi := piU_injOn (fun x hx => hT3 x (hBT hx))
    have hr : (piU.comp B.subtype).range = B.map piU := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  refine ⟨F₀.map piU, T.map piU, Subgroup.map_mono hF₀T, isElemAbelian_map _ hF₀e,
    by rw [hcardmap F₀ hF₀T, hF₀c], ⟨isElemAbelian_map _ hTe, by rw [hcardmap T le_rfl, hTc]⟩,
    piU tU, tU_ne_one, by rw [← map_pow, tU_sq, map_one], ?_⟩
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact tU_comm hω3 _

theorem noThreeCover_projSU45 :
    HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover
      (CFSG.Assembly.RankThreeEven.projSU 4 5 1) := by
  have hSU : CFSG.Open.StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSU 4 5 1) .PSU 4 5 1 :=
    ⟨⟨by norm_num, le_rfl, by norm_num, by decide⟩, F25, inferInstance, inferInstance,
      by rw [GaloisField.card 5 (2 * 1) (by norm_num)]; norm_num, ⟨projEquivU.symm⟩⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row hSU
    (by decide) (Or.inl (by norm_num))
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 5 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 5 1) = 2 := by
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      Nat.card_prod, card_multiplicative_zmod]
    rfl
  haveI : Finite (CFSG.Blueprint.Multiplier.generic .PSU 4 5 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 5 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact noThreeCover_of_hopf e (by rw [hcard]; norm_num)

end U45

theorem center_eq_bot_of_noThreeCover' {X : Type} [Group X]
    (h3 : HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover X) :
    ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* X) →
      Subgroup.center L = ⊥ := by
  intro L _ _ _ hL hp ⟨e⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hn3 := h3 L (HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hL) ⟨e⟩
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
  · exact absurd (hk ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)) hn3

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
