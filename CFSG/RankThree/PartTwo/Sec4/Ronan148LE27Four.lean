module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LE27Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Open (StatedProj StatedSL StatedSU StatedClassicalModel)
open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)
open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.DFT

theorem not_three_dvd_mul {x y : ℕ} (hx : ¬ 3 ∣ x) (hy : ¬ 3 ∣ y) : ¬ 3 ∣ x * y := fun h =>
  ((Nat.Prime.dvd_mul Nat.prime_three).mp h).elim hx hy

theorem not_three_dvd_pow {x : ℕ} (n : ℕ) (hx : ¬ 3 ∣ x) : ¬ 3 ∣ x ^ n := fun h =>
  hx (Nat.prime_three.dvd_of_dvd_pow h)

theorem exists_three_pow_succ {n : ℕ} (hn : n ≠ 0) (h3 : 3 ∣ n) :
    ∃ a m : ℕ, ¬ 3 ∣ m ∧ n = 3 ^ (a + 1) * m := by
  obtain ⟨a', m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  rcases a' with _ | a
  · rw [pow_zero, one_mul] at hnm
    exact absurd (hnm ▸ h3) hm
  · exact ⟨a, m, hm, hnm⟩

theorem three_pow_mul_cube (a m : ℕ) :
    3 ^ (3 * (a + 1) + 1) * m ^ 3 = 81 * (3 ^ a * m) ^ 3 := by
  ring

theorem exists_orderOf_eq_of_dvd {F : Type} [Field F] [Finite F] {d : ℕ}
    (hd : d ∣ Nat.card F - 1) : ∃ ζ : Fˣ, orderOf ζ = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hF : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨e, he⟩ := hd
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [mul_zero] at he
    omega
  refine ⟨g ^ e, ?_⟩
  rw [orderOf_pow_of_dvd he0 (by rw [hg, hcard, he]; exact Dvd.intro_left d rfl), hg, hcard, he,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero he0)]

section Gen

variable {F : Type} [Field F] {G : Subgroup (GL (Fin 4) F)}

theorem τ4_mem_of {a : ℕ}
    (hT : ∀ t : Fin 3 → Fˣ, (∀ i, t i ^ (3 ^ (a + 1)) = 1) → emb4G (TauCeti.diagGL t) ∈ G)
    {ω : Fˣ} (hω3 : ω ^ 3 = 1) (v : Multiplicative (Fin 3 → ZMod 3)) : τ4 hω3 v ∈ G := by
  refine hT _ fun i => ?_
  obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective v
  change (ω ^ (u i).val) ^ (3 ^ (a + 1)) = 1
  rw [← pow_mul, show (u i).val * 3 ^ (a + 1) = 3 * ((u i).val * 3 ^ a) by ring, pow_mul, hω3,
    one_pow]

end Gen

section SU

variable {p : ℕ} [Fact p.Prime]

abbrev FU (p : ℕ) [Fact p.Prime] : Type := GaloisField p (2 * 1)

noncomputable abbrev SU4 (p : ℕ) [Fact p.Prime] : Subgroup (GL (Fin 4) (FU p)) :=
  StatedSU 4 (p ^ 1) (FU p)

theorem card_FU : Nat.card (FU p) = p ^ 2 := by
  have h := GaloisField.card p (2 * 1) (by norm_num)
  simpa using h

theorem zero_pow_p : ((0 : FU p) ^ (p ^ 1)) = 0 :=
  zero_pow (pow_ne_zero 1 (Fact.out : p.Prime).ne_zero)

theorem det_pow_mul_det_FU {A : Matrix (Fin 3) (Fin 3) (FU p)}
    (hA : (A.map (· ^ (p ^ 1)))ᵀ * A = 1) : A.det ^ (p ^ 1) * A.det = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_transpose, det_one] at h
  have hmap : (A.map (· ^ (p ^ 1))).det = A.det ^ (p ^ 1) := by
    have := (iterateFrobenius (FU p) p 1).map_det A
    rw [iterateFrobenius_def] at this
    rw [this, RingHom.mapMatrix_apply]
    congr 1
  rwa [hmap] at h

theorem unitary_blk4G_FU (A : GL (Fin 3) (FU p))
    (hA : ((A : Matrix (Fin 3) (Fin 3) (FU p)).map (· ^ (p ^ 1)))ᵀ * A = 1) :
    ((blk4G A).map (· ^ (p ^ 1)))ᵀ * blk4G A = 1 := by
  have hdet := det_pow_mul_det_FU hA
  have hc : (((GeneralLinearGroup.det A)⁻¹ : (FU p)ˣ) : FU p) ^ (p ^ 1) *
      (((GeneralLinearGroup.det A)⁻¹ : (FU p)ˣ) : FU p) = 1 := by
    rw [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, inv_pow, ← mul_inv, hdet,
      inv_one]
  have h0 := zero_pow_p (p := p)
  simp only [blk4G, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
    fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
    Matrix.map_zero (fun x : FU p => x ^ (p ^ 1)) h0,
    diagonal_map (f := fun x : FU p => x ^ (p ^ 1)) h0, diagonal_transpose, transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal, hA]
  rw [show (fun _ : Fin 1 => (((GeneralLinearGroup.det A)⁻¹ : (FU p)ˣ) : FU p) ^ (p ^ 1) *
      (((GeneralLinearGroup.det A)⁻¹ : (FU p)ˣ) : FU p)) = fun _ => 1 from funext fun _ => hc]
  rw [diagonal_one, fromBlocks_one]
  simp

theorem emb4G_mem_SU4 {A : GL (Fin 3) (FU p)}
    (hA : ((A : Matrix (Fin 3) (Fin 3) (FU p)).map (· ^ (p ^ 1)))ᵀ * A = 1) :
    emb4G A ∈ SU4 p :=
  Subgroup.subset_closure ⟨det_blk4G A, unitary_blk4G_FU A hA⟩

theorem unitary_diagGL_FU (t : Fin 3 → (FU p)ˣ) (ht : ∀ i, t i ^ (p ^ 1) * t i = 1) :
    (((TauCeti.diagGL t : GL (Fin 3) (FU p)) : Matrix (Fin 3) (Fin 3) (FU p)).map
      (· ^ (p ^ 1)))ᵀ * (TauCeti.diagGL t : GL (Fin 3) (FU p)) = 1 := by
  rw [TauCeti.diagGL_coe, diagonal_map (f := fun x : FU p => x ^ (p ^ 1)) zero_pow_p,
    diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ht i, Units.val_one]

theorem unitary_permGL3_FU :
    (((permGL3 : GL (Fin 3) (FU p)) : Matrix (Fin 3) (Fin 3) (FU p)).map (· ^ (p ^ 1)))ᵀ *
      (permGL3 : GL (Fin 3) (FU p)) = 1 := by
  have h0 := zero_pow_p (p := p)
  rw [coe_permGL3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMat3, Matrix.mul_apply, Fin.sum_univ_three, h0, (Fact.out : p.Prime).ne_zero]

theorem exists_permMat_SU4 (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1) :
    ∃ n ∈ SU4 p, (n : Matrix (Fin 4) (Fin 4) (FU p)) = σ.toPEquiv.toMatrix := by
  have hPP' : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FU p)) *
      σ.symm.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hP'P : (σ.symm.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FU p)) *
      σ.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let g : GL (Fin 4) (FU p) := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, hPP', hP'P⟩
  have hdet : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FU p)).det = 1 := by
    have h := Matrix.det_permutation (R := FU p) σ
    rw [Equiv.Perm.permMatrix] at h
    rw [h, hσ]
    simp
  have hmap : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FU p)).map (· ^ (p ^ 1)) =
      σ.toPEquiv.toMatrix := by
    have h := PEquiv.map_toMatrix (iterateFrobenius (FU p) p 1) σ.toPEquiv
    rw [← h]
    congr 1
  have hT : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FU p))ᵀ =
      σ.symm.toPEquiv.toMatrix := by
    rw [← PEquiv.toMatrix_symm, Equiv.toPEquiv_symm]
  have hmem : g ∈ SU4 p := Subgroup.subset_closure ⟨hdet, by
    change ((σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FU p)).map (· ^ (p ^ 1)))ᵀ *
      σ.toPEquiv.toMatrix = 1
    rw [hmap, hT, hP'P]⟩
  exact ⟨g, hmem, rfl⟩

theorem neg_mem_SU4 (hp2 : p ≠ 2) : emb4G (TauCeti.diagGL ![-1, -1, 1]) ∈ SU4 p := by
  refine emb4G_mem_SU4 (unitary_diagGL_FU _ fun i => ?_)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hm : ((-1 : (FU p)ˣ)) ^ (p ^ 1) * (-1) = 1 := by
    rw [pow_one, hodd.neg_one_pow]
    simp
  fin_cases i
  · exact hm
  · exact hm
  · simp

theorem card_SU4_int :
    (Nat.card (SU4 p) : ℤ) = (p : ℤ) ^ 6 * (((p : ℤ) ^ 2 - 1) * (((p : ℤ) ^ 3 + 1) *
      ((p : ℤ) ^ 4 - 1))) := by
  have h := CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV.card_statedSU_eq_int
    (unitaryFieldData_galoisField p 1 le_rfl) (n := 4) (by norm_num)
  have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [e] at h
  rw [h]
  simp

theorem card_SU4_eq {a m : ℕ} (hm : ¬ 3 ∣ m) (hpm : p + 1 = 3 ^ (a + 1) * m) :
    ∃ k, ¬ 3 ∣ k ∧ Nat.card (SU4 p) = 3 ^ (3 * (a + 1) + 1) * k := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ a * m := ⟨_, rfl⟩
  have hpB : p + 1 = 3 * B := by rw [hpm, hB, pow_succ]; ring
  have hB1 : 1 ≤ B := by omega
  have hp3 : p % 3 = 2 := by omega
  refine ⟨m ^ 3 * (p ^ 6 * (p - 1) ^ 2 * (p ^ 2 + 1) * (3 * B * (B - 1) + 1)), ?_, ?_⟩
  · refine not_three_dvd_mul (not_three_dvd_pow 3 hm) (not_three_dvd_mul
      (not_three_dvd_mul (not_three_dvd_mul (not_three_dvd_pow 6 (by omega))
        (not_three_dvd_pow 2 (by omega))) ?_) (by rw [mul_assoc]; omega))
    intro h
    have : (p ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, hp3]
    omega
  · rw [← mul_assoc, three_pow_mul_cube, ← hB]
    have h := card_SU4_int (p := p)
    have hZ : (p : ℤ) = 3 * (B : ℤ) - 1 := by
      have : ((p + 1 : ℕ) : ℤ) = ((3 * B : ℕ) : ℤ) := by rw [hpB]
      push_cast at this
      linear_combination this
    have key : (Nat.card (SU4 p) : ℤ) = ((81 * B ^ 3 * (p ^ 6 * (p - 1) ^ 2 * (p ^ 2 + 1) *
        (3 * B * (B - 1) + 1)) : ℕ) : ℤ) := by
      rw [h]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub hB1]
      rw [hZ]
      ring
    exact_mod_cast key

theorem torus_mem_SU4 {a m : ℕ} (hpm : p + 1 = 3 ^ (a + 1) * m) (t : Fin 3 → (FU p)ˣ)
    (ht : ∀ i, t i ^ (3 ^ (a + 1)) = 1) : emb4G (TauCeti.diagGL t) ∈ SU4 p := by
  refine emb4G_mem_SU4 (unitary_diagGL_FU _ fun i => ?_)
  rw [← pow_succ, pow_one, hpm, pow_mul, ht i, one_pow]

@[expose] noncomputable def projEquivSU4 (p : ℕ) [Fact p.Prime] :
    CFSG.Assembly.RankThreeEven.projSU 4 p 1 ≃* CFSG.Assembly.RankThreeEven.projImage (SU4 p) :=
  MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 p 1).symm

theorem e27Move_projSU4 (hp : p % 3 = 2) :
    E27Move (CFSG.Assembly.RankThreeEven.projSU 4 p 1) := by
  obtain ⟨a, m, hm, hpm⟩ := exists_three_pow_succ (n := p + 1) (by omega) (by omega)
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd (F := FU p) (d := 3 ^ (a + 1)) (by
    rw [card_FU, show p ^ 2 - 1 = (p - 1) * (p + 1) by
      have : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
      zify [this, Nat.one_le_pow 2 p (by omega)]
      ring, hpm]
    exact Dvd.dvd.mul_left (Dvd.intro m rfl) (p - 1))
  obtain ⟨k, hk, hcard⟩ := card_SU4_eq hm hpm
  refine E27Move.of_mulEquiv (projEquivSU4 p) (e27Move_projImage
    (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (p ^ 1) (FU p)) ?_)
  exact e27Move_of_torus4 hζ (torus_mem_SU4 hpm)
    (emb4G_mem_SU4 unitary_permGL3_FU) exists_permMat_SU4 hcard hk

theorem two_ne_zero_FU (hp2 : p ≠ 2) : (2 : FU p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : FU p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (FU p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

theorem exists_omega_FU (hp : p % 3 = 2) : ∃ ω : (FU p)ˣ, orderOf ω = 3 := by
  refine exists_orderOf_eq_of_dvd ?_
  rw [card_FU]
  have hsq : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hp]
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  exact Nat.dvd_of_mod_eq_zero (by omega)

theorem exists_e27_projSU4 (hp : p % 3 = 2) :
    ∃ E : Subgroup (CFSG.Assembly.RankThreeEven.projSU 4 p 1), Late.IsE27 E := by
  obtain ⟨a, m, -, hpm⟩ := exists_three_pow_succ (n := p + 1) (by omega) (by omega)
  obtain ⟨ω, hω⟩ := exists_omega_FU hp
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨E, hE⟩ := exists_e27_projImage hω3
    (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (p ^ 1) (FU p)) hω
    (τ4_mem_of (torus_mem_SU4 hpm) hω3)
  exact ⟨E.map (projEquivSU4 p).symm.toMonoidHom, isElemAbelian_map _ hE.1, by
    rw [Subgroup.card_map_of_injective (projEquivSU4 p).symm.injective, hE.2]⟩

theorem invE9_projSU4 (hp : p % 3 = 2) (hp2 : p ≠ 2) :
    InvE9 (CFSG.Assembly.RankThreeEven.projSU 4 p 1) := by
  obtain ⟨a, m, -, hpm⟩ := exists_three_pow_succ (n := p + 1) (by omega) (by omega)
  obtain ⟨ω, hω⟩ := exists_omega_FU hp
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  exact InvE9.of_mulEquiv (projEquivSU4 p) (invE9_projImage hω3
    (CFSG.Open.StatedAPI.statedSU_le_statedSL 4 (p ^ 1) (FU p)) hω
    (τ4_mem_of (torus_mem_SU4 hpm) hω3) (neg_mem_SU4 hp2) (two_ne_zero_FU hp2))

theorem noThreeCover_projSU4
    (hp : 3 < p) :
    NoThreeCover (CFSG.Assembly.RankThreeEven.projSU 4 p 1) := by
  have e₀ : CFSG.Assembly.RankThreeEven.projSU 4 p 1 ≃* StatedProj (SU4 p) :=
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 p 1))).symm
  have hSU : StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSU 4 p 1) .PSU 4 p 1 :=
    ⟨⟨Fact.out, le_rfl, by norm_num, by simp⟩, FU p, inferInstance, inferInstance,
      by rw [card_FU, pow_one], ⟨e₀⟩⟩
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row hSU
    (by decide) (Or.inl (by rw [pow_one]; omega))
  have hexc : exceptionalOrders .PSU 4 p 1 = (1, 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 4 := ⟨p - 4, by omega⟩
    rfl
  have hcard : Nat.card (generic .PSU 4 p 1 × exceptional .PSU 4 p 1) =
      Nat.gcd 4 (p ^ 1 + 1) := by
    simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod, hexc]
    simp [genericOrders]
  have hg : 0 < Nat.gcd 4 (p ^ 1 + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  haveI : Finite (generic .PSU 4 p 1 × exceptional .PSU 4 p 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  refine noThreeCover_of_hopf e ?_
  rw [hcard]
  intro h
  have := h.trans (Nat.gcd_dvd_left 4 (p ^ 1 + 1))
  omega

end SU

section SL

variable {p : ℕ} [Fact p.Prime]

abbrev FL (p : ℕ) [Fact p.Prime] : Type := GaloisField p 1

noncomputable abbrev SL4 (p : ℕ) [Fact p.Prime] : Subgroup (GL (Fin 4) (FL p)) :=
  StatedSL 4 (FL p)

theorem card_FL : Nat.card (FL p) = p := by
  have h := GaloisField.card p 1 (by norm_num)
  simpa using h

theorem emb4G_mem_SL4 (A : GL (Fin 3) (FL p)) : emb4G A ∈ SL4 p :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det (det_blk4G A)

theorem exists_permMat_SL4 (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1) :
    ∃ n ∈ SL4 p, (n : Matrix (Fin 4) (Fin 4) (FL p)) = σ.toPEquiv.toMatrix := by
  have hPP' : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FL p)) *
      σ.symm.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hP'P : (σ.symm.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FL p)) *
      σ.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let g : GL (Fin 4) (FL p) := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, hPP', hP'P⟩
  have hdet : (σ.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) (FL p)).det = 1 := by
    have h := Matrix.det_permutation (R := FL p) σ
    rw [Equiv.Perm.permMatrix] at h
    rw [h, hσ]
    simp
  exact ⟨g, CFSG.Open.StatedAPI.mem_statedSL_of_det hdet, rfl⟩

theorem card_statedSL_four' (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSL 4 K) =
      Nat.card K ^ 6 * ((Nat.card K ^ 2 - 1) * ((Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1))) := by
  let := Fintype.ofFinite K
  rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, ← Nat.card_eq_fintype_card,
    Fin.prod_univ_four]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h3, pow_zero, pow_one]
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have h1 : 1 ≤ q := by omega
  have hprod : (q ^ 4 - 1) * (q ^ 4 - q) * (q ^ 4 - q ^ 2) * (q ^ 4 - q ^ 3) =
      (q - 1) * (q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)))) := by
    have e1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have e2 : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
    have e3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have e4 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have e5 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e6 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [e1, e2, e3, e4, e5, e6, h1]
    ring
  rw [hprod, Nat.mul_div_cancel_left _ (by omega)]

theorem card_SL4_eq {a m : ℕ} (hm : ¬ 3 ∣ m) (hpm : p - 1 = 3 ^ (a + 1) * m) :
    ∃ k, ¬ 3 ∣ k ∧ Nat.card (SL4 p) = 3 ^ (3 * (a + 1) + 1) * k := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨B, hB⟩ : ∃ B, B = 3 ^ a * m := ⟨_, rfl⟩
  have hpB : p = 3 * B + 1 := by
    have : p - 1 = 3 * B := by rw [hpm, hB, pow_succ]; ring
    omega
  have hp3 : p % 3 = 1 := by omega
  refine ⟨m ^ 3 * (p ^ 6 * (p + 1) ^ 2 * (p ^ 2 + 1) * (3 * B * (B + 1) + 1)), ?_, ?_⟩
  · refine not_three_dvd_mul (not_three_dvd_pow 3 hm) (not_three_dvd_mul
      (not_three_dvd_mul (not_three_dvd_mul (not_three_dvd_pow 6 (by omega))
        (not_three_dvd_pow 2 (by omega))) ?_) (by rw [mul_assoc]; omega))
    intro h
    have : (p ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, hp3]
    omega
  · rw [← mul_assoc, three_pow_mul_cube, ← hB, card_statedSL_four', card_FL]
    have hZ : (p : ℤ) = 3 * (B : ℤ) + 1 := by rw [hpB]; push_cast; ring
    have key : ((p ^ 6 * ((p ^ 2 - 1) * ((p ^ 3 - 1) * (p ^ 4 - 1))) : ℕ) : ℤ) =
        ((81 * B ^ 3 * (p ^ 6 * (p + 1) ^ 2 * (p ^ 2 + 1) * (3 * B * (B + 1) + 1)) : ℕ) : ℤ) := by
      have e2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      have e3 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
      have e4 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4]
      rw [hZ]
      ring
    exact_mod_cast key

@[expose] noncomputable def projEquivSL4 (p : ℕ) [Fact p.Prime] :
    CFSG.Assembly.RankThreeEven.projSL 4 (FL p) ≃*
      CFSG.Assembly.RankThreeEven.projImage (SL4 p) :=
  MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 (FL p)).symm

theorem e27Move_projSL4 (hp : p % 3 = 1) :
    E27Move (CFSG.Assembly.RankThreeEven.projSL 4 (FL p)) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨a, m, hm, hpm⟩ := exists_three_pow_succ (n := p - 1) (by omega) (by omega)
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd (F := FL p) (d := 3 ^ (a + 1)) (by
    rw [card_FL, hpm]
    exact Dvd.intro m rfl)
  obtain ⟨k, hk, hcard⟩ := card_SL4_eq hm hpm
  refine E27Move.of_mulEquiv (projEquivSL4 p) (e27Move_projImage le_rfl ?_)
  exact e27Move_of_torus4 hζ (fun t _ => emb4G_mem_SL4 _) (emb4G_mem_SL4 _)
    exists_permMat_SL4 hcard hk

theorem exists_omega_FL (hp : p % 3 = 1) : ∃ ω : (FL p)ˣ, orderOf ω = 3 :=
  exists_orderOf_eq_of_dvd (by rw [card_FL]; exact Nat.dvd_of_mod_eq_zero (by omega))

theorem exists_e27_projSL4 (hp : p % 3 = 1) :
    ∃ E : Subgroup (CFSG.Assembly.RankThreeEven.projSL 4 (FL p)), Late.IsE27 E := by
  obtain ⟨ω, hω⟩ := exists_omega_FL hp
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨E, hE⟩ := exists_e27_projImage hω3 (le_refl (SL4 p)) hω
    (fun v => emb4G_mem_SL4 _)
  exact ⟨E.map (projEquivSL4 p).symm.toMonoidHom, isElemAbelian_map _ hE.1, by
    rw [Subgroup.card_map_of_injective (projEquivSL4 p).symm.injective, hE.2]⟩

theorem two_ne_zero_FL (hp2 : p ≠ 2) : (2 : FL p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : FL p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (FL p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

theorem invE9_projSL4 (hp : p % 3 = 1) :
    InvE9 (CFSG.Assembly.RankThreeEven.projSL 4 (FL p)) := by
  obtain ⟨ω, hω⟩ := exists_omega_FL hp
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  exact InvE9.of_mulEquiv (projEquivSL4 p) (invE9_projImage hω3 (le_refl (SL4 p)) hω
    (fun v => emb4G_mem_SL4 _) (emb4G_mem_SL4 _) (two_ne_zero_FL (by omega)))

theorem not_three_dvd_card_outer_projSL4p :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Assembly.RankThreeEven.projSL 4 (FL p))) := by
  have hd := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
    (k := FL p) (p := p) (f := 1) (n := 4) Fact.out le_rfl (by norm_num)
    (by rw [card_FL, pow_one])
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (projSLEquivProjectiveSL 4 (FL p))).toEquiv] at hd
  intro h3
  have h8 : 2 * 1 * Nat.gcd 4 (p ^ 1 - 1) ∣ 2 * 1 * 4 :=
    Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left 4 _)
  have := (h3.trans hd).trans h8
  omega

theorem noThreeCover_projSL4
    (hp : 3 < p) :
    NoThreeCover (CFSG.Assembly.RankThreeEven.projSL 4 (FL p)) := by
  have e₀ : CFSG.Assembly.RankThreeEven.projSL 4 (FL p) ≃* StatedProj (SL4 p) :=
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 4 (FL p)))).symm
  have hSL : StatedClassicalModel (CFSG.Assembly.RankThreeEven.projSL 4 (FL p)) .PSL 4 p 1 :=
    ⟨⟨Fact.out, le_rfl, by norm_num, by simp, by simp⟩, FL p, inferInstance, inferInstance,
      by rw [card_FL, pow_one], ⟨e₀⟩⟩
  obtain ⟨e⟩ := (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hSL).2
  have hexc : exceptionalOrders .PSL 4 p 1 = (1, 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 4 := ⟨p - 4, by omega⟩
    rfl
  have hcard : Nat.card (generic .PSL 4 p 1 × exceptional .PSL 4 p 1) =
      Nat.gcd 4 (p ^ 1 - 1) := by
    simp only [generic, exceptional, Nat.card_prod, card_multiplicative_zmod, hexc]
    simp [genericOrders]
  have hg : 0 < Nat.gcd 4 (p ^ 1 - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  haveI : Finite (generic .PSL 4 p 1 × exceptional .PSL 4 p 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  refine noThreeCover_of_hopf e ?_
  rw [hcard]
  intro h
  have := h.trans (Nat.gcd_dvd_left 4 (p ^ 1 - 1))
  omega

end SL

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
