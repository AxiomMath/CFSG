module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.LieType.Universal

private lemma dpcPSU_antidiag_map {F : Type} [Field F] (σ : F →+* F) (n : ℕ) :
    (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).map σ = Unitary.antidiag n := by
  ext i j
  simp only [Unitary.antidiag, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · exact map_one σ
  · exact map_zero σ

private lemma dpcPSU_transpose_antidiag {F : Type} [Field F] (n : ℕ) :
    Matrix.transpose (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
  ext i j
  simp only [Matrix.transpose_apply, Unitary.antidiag, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h']
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h']

private lemma dpcPSU_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
  rintro x ⟨s, hs, rfl⟩
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
  rintro y ⟨s', hs', rfl⟩
  exact (hS s hs s' hs').units_val

private lemma dpcPSU_block_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e = 1) {a : Matrix ι ι F}
    (ha : a ∈ A) : ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have hMdeg : Module.finrank F M = 1 := hdeg
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hene : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  have haM : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, heM⟩ : M) hene).mp hMdeg
    (⟨a * e, haM⟩ : M)
  exact ⟨c, by simpa using congrArg Subtype.val hc.symm⟩

private lemma dpcPSU_blockDegree_eq_one {F : Type} [Field F] {n : ℕ}
    {A : Subalgebra F (Matrix (Fin n) (Fin n) F)} {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e < 2) : blockDegree A e = 1 := by
  let M : Submodule F (Matrix (Fin n) (Fin n) F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
  have hlt : Module.finrank F M < 2 := hdeg
  change Module.finrank F M = 1
  omega

private lemma dpcPSU_formAdj_idem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {e : Matrix ι ι F}
    (he : IsIdempotentElem e) : IsIdempotentElem (formAdj σ G e) := by
  rw [isIdempotentElem_iff] at he ⊢
  rw [← Geo.formAdj_mul σ hG, he]

private lemma dpcPSU_formAdj_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G : Matrix ι ι F) : formAdj σ G 0 = 0 := by
  unfold formAdj
  rw [Matrix.map_zero σ (map_zero σ), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

private lemma dpcPSU_formAdj_ne_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {a : Matrix ι ι F} (ha : a ≠ 0) :
    formAdj σ G a ≠ 0 := by
  intro h0
  have : a = 0 := by
    rw [← Geo.formAdj_formAdj σ hσ hG hGh a, h0, dpcPSU_formAdj_zero σ G]
  exact ha this

private lemma dpcPSU_formAdj_of_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    {s : GL ι F} (hs : s ∈ S) :
    formAdj σ G (s : Matrix ι ι F) = ((s⁻¹ : GL ι F) : Matrix ι ι F) :=
  Geo.formAdj_eq_inv_of_isometry σ hG s (hSU s hs)

private lemma dpcPSU_formAdj_char {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {s : GL ι F} (hs : s ∈ S) {c : F} (hce : (s : Matrix ι ι F) * e = c • e) :
    (s : Matrix ι ι F) * formAdj σ G e = (σ c)⁻¹ • formAdj σ G e := by
  have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have heStar_mem : formAdj σ G e ∈ Algebra.adjoin F (Units.val '' S) :=
    Geo.formAdj_mem_adjoin σ hG hSU he.1
  have hcomm : (s : Matrix ι ι F) * formAdj σ G e =
      formAdj σ G e * (s : Matrix ι ι F) :=
    (dpcPSU_adjoin_comm hS (s : Matrix ι ι F) hsA (formAdj σ G e) heStar_mem).eq
  have hs_inv : formAdj σ G (s : Matrix ι ι F) = ((s⁻¹ : GL ι F) : Matrix ι ι F) :=
    dpcPSU_formAdj_of_mem σ hG hSU hs
  have h1 : σ c • formAdj σ G e =
      formAdj σ G e * ((s⁻¹ : GL ι F) : Matrix ι ι F) := by
    have h := Geo.formAdj_mul σ hG (s : Matrix ι ι F) e
    rw [hce, Geo.formAdj_smul, hs_inv] at h
    exact h
  have hss : ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : formAdj σ G e = σ c • ((s : Matrix ι ι F) * formAdj σ G e) := by
    have key : (σ c • formAdj σ G e) * (s : Matrix ι ι F) = formAdj σ G e := by
      rw [h1, Matrix.mul_assoc, hss, Matrix.mul_one]
    rw [Matrix.smul_mul, ← hcomm] at key
    exact key.symm
  have hσc : σ c ≠ 0 := by
    intro h0
    exact dpcPSU_formAdj_ne_zero σ hσ hG hGh he.2.2.1 (by rw [h2, h0, zero_smul])
  have h3 := congrArg (fun x => (σ c)⁻¹ • x) h2
  rw [smul_smul, inv_mul_cancel₀ hσc, one_smul] at h3
  exact h3.symm

private lemma dpcPSU_scalar_eq_smul_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Semiring F]
    (d : F) : Matrix.scalar ι d = d • (1 : Matrix ι ι F) := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private lemma dpcPSU_scalar_map {ι F : Type} [Fintype ι] [DecidableEq ι] [Semiring F]
    (σ : F →+* F) (d : F) : (Matrix.scalar ι d).map σ = Matrix.scalar ι (σ d) := by
  rw [dpcPSU_scalar_eq_smul_one d, dpcPSU_scalar_eq_smul_one (σ d),
    Matrix.map_smul' σ d 1 (map_mul σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

private lemma dpcPSU_transpose_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Semiring F]
    (d : F) : Matrix.transpose (Matrix.scalar ι d) = Matrix.scalar ι d := by
  rw [dpcPSU_scalar_eq_smul_one d, Matrix.transpose_smul, Matrix.transpose_one,
    ← dpcPSU_scalar_eq_smul_one d]

private lemma dpcPSU_scalar_mul_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (a b : F) (G : Matrix ι ι F) :
    Matrix.scalar ι a * G * Matrix.scalar ι b = (a * b) • G := by
  rw [dpcPSU_scalar_eq_smul_one a, dpcPSU_scalar_eq_smul_one b, Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]

private lemma dpcPSU_pow_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a e : Matrix ι ι F} {c : F} (h : a * e = c • e) (k : ℕ) : a ^ k * e = c ^ k • e := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, Matrix.mul_smul, ih, smul_smul, pow_succ']

private lemma dpcPSU_conjTr_pow {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G a : Matrix ι ι F}
    (h : Matrix.transpose (a.map σ) * G * a = G) (k : ℕ) :
    Matrix.transpose ((a ^ k).map σ) * G * a ^ k = G := by
  induction k with
  | zero => simp [Matrix.map_one σ (map_zero σ) (map_one σ)]
  | succ k ih =>
      rw [pow_succ, Matrix.map_mul, Matrix.transpose_mul]
      rw [show (Matrix.transpose (a.map σ) * Matrix.transpose ((a ^ k).map σ)) * G *
              (a ^ k * a) =
            Matrix.transpose (a.map σ) *
              (Matrix.transpose ((a ^ k).map σ) * G * a ^ k) * a by
            simp only [Matrix.mul_assoc]]
      rw [ih, h]

theorem exists_dualPair_char_ne_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e) :
    ∃ s ∈ S, ∃ c : F, (s : Matrix (Fin n) (Fin n) F) * e = c • e ∧ c ^ (2 ^ f + 1) ≠ 1 := by
  let σe : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
  let σ : F →+* F := σe.toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  let A : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F (Units.val '' S)
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    simpa [σ, σe] using
      CFSG.LieType.BorelTits.unitaryInvolution_involutive (K := F) (p := 2) (f := f) hc x
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    exact Unitary.det_antidiag_ne_zero n
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [dpcPSU_antidiag_map σ n, dpcPSU_transpose_antidiag n]
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G *
      (s : Matrix (Fin n) (Fin n) F) = G := by
    intro s hs
    simpa [Unitary.conjTr, G, σ, σe] using hSU s hs
  have hpair' : formAdj σ G e ≠ e := by
    change formAdj σe.toRingHom (Unitary.antidiag n) e ≠ e
    exact hpair
  have hdeg1 : blockDegree A e = 1 := dpcPSU_blockDegree_eq_one he hdeg
  have heA : e ∈ A := he.1
  have heStarA : formAdj σ G e ∈ A := Geo.formAdj_mem_adjoin σ hG hSU' he.1
  have heStarne : formAdj σ G e ≠ 0 := dpcPSU_formAdj_ne_zero σ hσ hG hGh he.2.2.1
  have heStaridem : IsIdempotentElem (formAdj σ G e) := dpcPSU_formAdj_idem σ hG he.2.1
  by_contra hcon
  push Not at hcon
  have hclaim : ∀ a ∈ A, ∃ χ : F,
      a * e = χ • e ∧ a * formAdj σ G e = χ • formAdj σ G e := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => ∃ χ : F, x * e = χ • e ∧ x * formAdj σ G e = χ • formAdj σ G e)
      ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      obtain ⟨c, hce⟩ := dpcPSU_block_scalar he hdeg1 (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
      have hσc : σ c = c ^ (2 ^ f) := by
        simpa [σ, σe] using
          CFSG.LieType.BorelTits.unitaryInvolution_apply (K := F) (p := 2) (f := f) c
      have hcc : σ c * c = 1 := by
        rw [hσc, ← pow_succ]
        exact hcon s hs c hce
      have hcinv : (σ c)⁻¹ = c := (eq_inv_of_mul_eq_one_right hcc).symm
      have hstar : (s : Matrix (Fin n) (Fin n) F) * formAdj σ G e = c • formAdj σ G e := by
        rw [dpcPSU_formAdj_char σ hσ hG hGh hSU' hS he hs hce, hcinv]
      exact ⟨c, hce, hstar⟩
    · intro r
      exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul],
        by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]⟩
    · rintro x y hx hy ⟨χx, hxe, hxe'⟩ ⟨χy, hye, hye'⟩
      exact ⟨χx + χy, by rw [Matrix.add_mul, hxe, hye, add_smul],
        by rw [Matrix.add_mul, hxe', hye', add_smul]⟩
    · rintro x y hx hy ⟨χx, hxe, hxe'⟩ ⟨χy, hye, hye'⟩
      exact ⟨χy * χx, by rw [Matrix.mul_assoc, hye, Matrix.mul_smul, hxe, smul_smul],
        by rw [Matrix.mul_assoc, hye', Matrix.mul_smul, hxe', smul_smul]⟩
  obtain ⟨χe, hχe, hχe'⟩ := hclaim e heA
  obtain ⟨χs, hχs, hχs'⟩ := hclaim (formAdj σ G e) heStarA
  have hcomm : formAdj σ G e * e = e * formAdj σ G e :=
    (dpcPSU_adjoin_comm hS (formAdj σ G e) heStarA e heA).eq
  have hχe1 : χe = 1 := by
    have h : χe • e = 1 • e := by rw [← hχe, he.2.1.eq, one_smul]
    exact smul_left_injective F he.2.2.1 (by simpa using h)
  have heStare : formAdj σ G e * e = formAdj σ G e := by
    rw [hcomm, hχe', hχe1, one_smul]
  have hχs1 : χs = 1 := by
    have h : χs • formAdj σ G e = 1 • formAdj σ G e := by
      rw [← hχs', heStaridem.eq, one_smul]
    exact smul_left_injective F heStarne (by simpa using h)
  have heStareq : formAdj σ G e = e := by
    have h2 : formAdj σ G e = χs • e := by
      rw [← heStare]
      exact hχs
    rw [hχs1, one_smul] at h2
    exact h2
  exact hpair' heStareq

theorem dvd_two_pow_sub_one_of_dualPair_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (S : Set (GL (Fin n) F))
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    (hpair : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e ≠ e)
    {p : ℕ} (hp : p.Prime)
    (hsp : ∀ s ∈ S, ∃ c : F, (s : Matrix (Fin n) (Fin n) F) ^ p = Matrix.scalar (Fin n) c) :
    p ∣ 2 ^ f - 1 := by
  let σe : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
  let σ : F →+* F := σe.toRingHom
  let G : Matrix (Fin n) (Fin n) F := Unitary.antidiag n
  haveI : Fintype F := Fintype.ofFinite F
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    exact Unitary.det_antidiag_ne_zero n
  have hGh : Matrix.transpose (G.map σ) = G := by
    show Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n
    rw [dpcPSU_antidiag_map σ n, dpcPSU_transpose_antidiag n]
  have hSU' : ∀ s ∈ S, Matrix.transpose ((s : Matrix (Fin n) (Fin n) F).map σ) * G *
      (s : Matrix (Fin n) (Fin n) F) = G := by
    intro s hs
    simpa [Unitary.conjTr, G, σ, σe] using hSU s hs
  have hn : n ≠ 0 := by
    rintro rfl
    exact he.2.2.1 (by ext i j; exact Fin.elim0 i)
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hGne : G ≠ 0 := by
    intro h0
    have hdet0 : G.det = 0 := by rw [h0, Matrix.det_zero]
    exact Unitary.det_antidiag_ne_zero n hdet0
  obtain ⟨s, hs, c, hce, hζne⟩ := exists_dualPair_char_ne_PSU hc n S hSU hS he hdeg hpair
  obtain ⟨z, hz⟩ := hsp s hs
  have hcne : c ≠ 0 := by
    intro hc0
    have hs_e0 : (s : Matrix (Fin n) (Fin n) F) * e = 0 := by rw [hce, hc0, zero_smul]
    have he0 : e = 0 := by
      calc e = 1 * e := (Matrix.one_mul e).symm
        _ = (((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (s : Matrix (Fin n) (Fin n) F)) * e := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = ((s⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              ((s : Matrix (Fin n) (Fin n) F) * e) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hs_e0, Matrix.mul_zero]
    exact he.2.2.1 he0
  have hcp : c ^ p = z := by
    have h1 : (s : Matrix (Fin n) (Fin n) F) ^ p * e = c ^ p • e := dpcPSU_pow_mul hce p
    have h2 : Matrix.scalar (Fin n) z * e = z • e := by
      rw [dpcPSU_scalar_eq_smul_one z, Matrix.smul_mul, Matrix.one_mul]
    have h3 : c ^ p • e = z • e := by rw [← h1, hz, h2]
    exact smul_left_injective F he.2.2.1 h3
  have hσz : σ z * z = 1 := by
    have hiso : Matrix.transpose (((s : Matrix (Fin n) (Fin n) F) ^ p).map σ) * G *
        (s : Matrix (Fin n) (Fin n) F) ^ p = G := dpcPSU_conjTr_pow σ (hSU' s hs) p
    rw [hz] at hiso
    rw [dpcPSU_scalar_map σ z, dpcPSU_transpose_scalar (σ z),
      dpcPSU_scalar_mul_smul (σ z) z G] at hiso
    exact smul_left_injective F hGne (by
      show (σ z * z) • G = 1 • G
      rw [hiso, one_smul])
  have hzζ : z ^ (2 ^ f + 1) = 1 := by
    have hσz' : σ z = z ^ (2 ^ f) := by
      simpa [σ, σe] using
        CFSG.LieType.BorelTits.unitaryInvolution_apply (K := F) (p := 2) (f := f) z
    rw [hσz', ← pow_succ] at hσz
    exact hσz
  let q : ℕ := 2 ^ f
  have hζp : (c ^ (q + 1)) ^ p = 1 := by
    have h : (c ^ (q + 1)) ^ p = (c ^ p) ^ (q + 1) := by
      rw [← pow_mul, mul_comm (q + 1) p, pow_mul]
    rw [h, hcp]
    simpa [q] using hzζ
  have hc_pow : c ^ (q ^ 2 - 1) = 1 := by
    have hcard : Fintype.card F = q ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hc
    rw [← hcard]
    exact FiniteField.pow_card_sub_one_eq_one c hcne
  have hmul : (q + 1) * (q - 1) = q ^ 2 - 1 := by
    have hq : 1 ≤ q := by
      dsimp [q]
      exact Nat.one_le_two_pow
    have h : 1 + (q + 1) * (q - 1) = q ^ 2 := by nlinarith [Nat.sub_add_cancel hq]
    omega
  have hζq : (c ^ (q + 1)) ^ (q - 1) = 1 := by
    rw [← pow_mul, hmul]
    exact hc_pow
  have hord : orderOf (c ^ (q + 1)) = p := by
    have hdvd_p : orderOf (c ^ (q + 1)) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr hζp
    rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf (c ^ (q + 1))) hdvd_p with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hζne
    · exact hp'
  have hdvd_q : p ∣ q - 1 := by
    have := orderOf_dvd_iff_pow_eq_one.mpr hζq
    rwa [hord] at this
  simpa [q] using hdvd_q

end CFSG.StandardType.ClassicalPosition
