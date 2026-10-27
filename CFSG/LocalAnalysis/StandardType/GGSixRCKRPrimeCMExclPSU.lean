module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMExclusion
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Perm

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes

open scoped Matrix

private lemma rckPSU_exists_normOne_ne_one {E : Type} [Field E] [Finite E] {Q : ℕ}
    (hE : Nat.card E = Q ^ 2) :
    ∃ ζ : E, ζ ^ (Q + 1) = 1 ∧ ζ ≠ 1 := by
  have hQ2 : 2 ≤ Q := by
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    nlinarith [hE]
  have hsq : (Q + 1) * (Q - 1) = Q ^ 2 - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
    have h2 : (n + 1 : ℕ) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have h4 : (n + 1) - 1 = n := by omega
    have h3 : (n + 1 + 1 : ℕ) * n = n ^ 2 + 2 * n := by ring
    rw [h2, h4, h3]
    omega
  have hdvd : Q + 1 ∣ Nat.card Eˣ := by
    rw [Nat.card_units (α := E), hE, ← hsq]
    exact Nat.dvd_mul_right (Q + 1) (Q - 1)
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : Q + 1 ≠ 1)
  haveI : Fact r.Prime := ⟨hrprime⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' r (G := Eˣ) (hrdvd.trans hdvd)
  have hpow : u ^ (Q + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hu]
    exact hrdvd
  refine ⟨(u : E), ?_, ?_⟩
  · simpa using congrArg Units.val hpow
  · intro h
    have hu1 : u = 1 := Units.ext h
    have hord : orderOf u = 1 := by rw [hu1, orderOf_one]
    rw [hu] at hord
    exact hrprime.ne_one hord

private lemma rckPSU_diagonal_mem_GUFull {m Q : ℕ} {E : Type} [Field E] (hQ : 0 < Q)
    (d : Fin m → E) (hd : ∀ i, d i ^ (Q + 1) = 1) :
    ∃ D : GL (Fin m) E, (D : Matrix (Fin m) (Fin m) E) = Matrix.diagonal d ∧
      D ∈ ClassicalBlocks.GUFull m Q E := by
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h
    have h1 := hd i
    rw [h, zero_pow (by omega : Q + 1 ≠ 0)] at h1
    exact zero_ne_one h1
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i)
  let D : GL (Fin m) E := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) hdet
  have hDval : (D : Matrix (Fin m) (Fin m) E) = Matrix.diagonal d := by
    simp [D]
  refine ⟨D, hDval, ?_⟩
  apply Subgroup.subset_closure
  show ((D : Matrix (Fin m) (Fin m) E).map (· ^ Q))ᵀ * (D : Matrix (Fin m) (Fin m) E) = 1
  rw [hDval]
  have hmap : (Matrix.diagonal d).map (· ^ Q) = Matrix.diagonal (fun i => d i ^ Q) :=
    Matrix.diagonal_map (f := fun x : E => x ^ Q) (zero_pow (by omega : Q ≠ 0))
  have htr : (Matrix.diagonal (fun i => d i ^ Q) : Matrix (Fin m) (Fin m) E)ᵀ =
      Matrix.diagonal (fun i => d i ^ Q) := by
    ext i j
    rw [Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]
  rw [hmap, htr, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, ← pow_succ]
    exact hd i
  · rw [if_neg hij, if_neg hij]

private lemma rckPSU_perm_mem_GUFull {m Q : ℕ} {E : Type} [Field E] (hQ : 0 < Q)
    (σ : Equiv.Perm (Fin m)) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.permGL m E σ ∈
      ClassicalBlocks.GUFull m Q E := by
  let P : GL (Fin m) E := CFSG.HardMathSupport.Timmesfeld.Tables.Census.permGL m E σ
  apply Subgroup.subset_closure
  change ((P : Matrix (Fin m) (Fin m) E).map (· ^ Q))ᵀ * (P : Matrix (Fin m) (Fin m) E) = 1
  have hPval : (P : Matrix (Fin m) (Fin m) E) = (σ⁻¹).toPEquiv.toMatrix := by
    rw [show P = CFSG.HardMathSupport.Timmesfeld.Tables.Census.permGL m E σ from rfl,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.coe_permGL]
  have hmap : ((P : Matrix (Fin m) (Fin m) E).map (· ^ Q)) =
      (P : Matrix (Fin m) (Fin m) E) := by
    rw [hPval]
    ext i j
    rw [Matrix.map_apply]
    change (((σ⁻¹).toPEquiv.toMatrix : Matrix (Fin m) (Fin m) E) i j) ^ Q =
      ((σ⁻¹).toPEquiv.toMatrix : Matrix (Fin m) (Fin m) E) i j
    rw [PEquiv.toMatrix_apply]
    split_ifs <;> simp [hQ.ne']
  rw [hmap, hPval]
  change ((σ⁻¹).permMatrix E)ᵀ * ((σ⁻¹).permMatrix E) = 1
  rw [Matrix.transpose_permMatrix, inv_inv]
  have hPP : σ.permMatrix E * (σ⁻¹).permMatrix E = 1 := by
    simpa using (Matrix.permMatrix_mul (σ := σ⁻¹) (τ := σ) (R := E)).symm
  exact hPP

private lemma rckPSU_center_offdiag {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) {z : ↥(ClassicalBlocks.GUFull m Q E)}
    (hz : z ∈ Subgroup.center ↥(ClassicalBlocks.GUFull m Q E)) {i k : Fin m} (hik : k ≠ i) :
    (z.1 : Matrix (Fin m) (Fin m) E) i k = 0 := by
  have hQ : 0 < Q := by
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    nlinarith [hE]
  obtain ⟨ζ, hζpow, hζne⟩ := rckPSU_exists_normOne_ne_one hE
  let d : Fin m → E := Function.update (fun _ => 1) i ζ
  have hd : ∀ j, d j ^ (Q + 1) = 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [d, hζpow]
    · simp [d, Function.update_of_ne hj]
  obtain ⟨D, hDval, hDmem⟩ := rckPSU_diagonal_mem_GUFull hQ d hd
  have hcomm := congrArg (fun u : ↥(ClassicalBlocks.GUFull m Q E) =>
    (u.1 : Matrix (Fin m) (Fin m) E))
    (Subgroup.mem_center_iff.mp hz ⟨D, hDmem⟩)
  simp only [Subgroup.coe_mul, Units.val_mul, hDval] at hcomm
  have hentry := congrArg (fun M : Matrix (Fin m) (Fin m) E => M i k) hcomm
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  have hdi : d i = ζ := by simp [d]
  have hdk : d k = 1 := by simp [d, Function.update_of_ne hik]
  rw [hdi, hdk, mul_one] at hentry
  have hzero : (ζ - 1) * (z.1 : Matrix (Fin m) (Fin m) E) i k = 0 := by
    rw [sub_mul, one_mul, hentry, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hζne)

private lemma rckPSU_center_diag_eq {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) {z : ↥(ClassicalBlocks.GUFull m Q E)}
    (hz : z ∈ Subgroup.center ↥(ClassicalBlocks.GUFull m Q E))
    (hoff : ∀ i j : Fin m, i ≠ j → (z.1 : Matrix (Fin m) (Fin m) E) i j = 0)
    {i j : Fin m} (hij : i ≠ j) :
    (z.1 : Matrix (Fin m) (Fin m) E) i i = (z.1 : Matrix (Fin m) (Fin m) E) j j := by
  have hQ : 0 < Q := by
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    nlinarith [hE]
  let σ : Equiv.Perm (Fin m) := Equiv.swap i j
  let P : GL (Fin m) E := CFSG.HardMathSupport.Timmesfeld.Tables.Census.permGL m E σ
  have hPmem : P ∈ ClassicalBlocks.GUFull m Q E := rckPSU_perm_mem_GUFull hQ σ
  have hcomm := congrArg (fun u : ↥(ClassicalBlocks.GUFull m Q E) =>
    (u.1 : Matrix (Fin m) (Fin m) E)) (Subgroup.mem_center_iff.mp hz ⟨P, hPmem⟩)
  simp only [Subgroup.coe_mul, Units.val_mul] at hcomm
  have hPval : (P : Matrix (Fin m) (Fin m) E) = (σ⁻¹).toPEquiv.toMatrix := by
    rw [show P = CFSG.HardMathSupport.Timmesfeld.Tables.Census.permGL m E σ from rfl,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.coe_permGL]
  rw [hPval] at hcomm
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv] at hcomm
  have hentry := congrArg (fun M : Matrix (Fin m) (Fin m) E => M i j) hcomm
  simp only [Matrix.submatrix_apply, id_eq] at hentry
  have h1 : (σ⁻¹) i = j := by simp [σ, Equiv.swap_apply_left]
  have h2 : (σ⁻¹).symm j = i := by simp [σ, Equiv.swap_apply_right]
  rw [h1, h2] at hentry
  exact hentry.symm

theorem center_GUFull_le_statedScalars {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) :
    Subgroup.center ↥(ClassicalBlocks.GUFull m Q E) ≤
      (CFSG.Open.StatedScalars (Fin m) E).subgroupOf (ClassicalBlocks.GUFull m Q E) := by
  intro z hz
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst m
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine ⟨1, ?_⟩
    apply Units.ext
    ext i j
    exact Fin.elim0 i
  · have hoff : ∀ i j : Fin m, i ≠ j → (z.1 : Matrix (Fin m) (Fin m) E) i j = 0 :=
      fun i j hij => rckPSU_center_offdiag hE hz hij.symm
    let i0 : Fin m := ⟨0, hmpos⟩
    have hdiag : ∀ i, (z.1 : Matrix (Fin m) (Fin m) E) i i =
        (z.1 : Matrix (Fin m) (Fin m) E) i0 i0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; rfl
      · exact rckPSU_center_diag_eq hE hz hoff hi
    let c : E := (z.1 : Matrix (Fin m) (Fin m) E) i0 i0
    have hzdiag : (z.1 : Matrix (Fin m) (Fin m) E) = Matrix.diagonal (fun _ => c) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [hdiag i, Matrix.diagonal_apply_eq]
      · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
    have hc : c ≠ 0 := by
      intro hc0
      have hdet := Matrix.GeneralLinearGroup.det_ne_zero (z : GL (Fin m) E)
      rw [hzdiag, Matrix.det_diagonal] at hdet
      exact hdet (Finset.prod_eq_zero (Finset.mem_univ i0) hc0)
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine ⟨Units.mk0 c hc, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, hzdiag]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]

private noncomputable abbrev rckPSU_Gt {n g : ℕ} (s : GL (Fin n) (PSUF g))
    (ε : Matrix (Fin n) (Fin n) (PSUF g)) : Subgroup (GL (Fin n) (PSUF g)) :=
  Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓ GUsub (PSUσ g) n

private lemma rckPSU_block_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (hε : IsIdempotentElem ε) {x y : Matrix ι ι F}
    (hx : x * ε = ε * x) (hy : y * ε = ε * y) :
    (x * ε + (1 - ε)) * (y * ε + (1 - ε)) = (x * y) * ε + (1 - ε) := by
  have hε' : ε * ε = ε := hε.eq
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε']
    abel
  have hx0 : x * ε * (1 - ε) = 0 := by
    rw [mul_assoc, hε.mul_one_sub_self, mul_zero]
  have hy0 : (1 - ε) * (y * ε) = 0 := by
    rw [hy, ← mul_assoc, hε.one_sub_mul_self, zero_mul]
  calc
    (x * ε + (1 - ε)) * (y * ε + (1 - ε))
        = x * ε * (y * ε) + x * ε * (1 - ε) + (1 - ε) * (y * ε) +
            (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * ε * (y * ε) + (1 - ε) * (1 - ε) := by simp [hx0, hy0]
    _ = x * (ε * y) * ε + (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * (y * ε) * ε + (1 - ε) * (1 - ε) := by rw [hy]
    _ = x * y * ε + (1 - ε) := by
      rw [mul_assoc x (y * ε) ε, mul_assoc y ε ε, hε', ← mul_assoc x y ε, h1]

private lemma rckPSU_blockRestrict_exists {n g : ℕ} {s : GL (Fin n) (PSUF g)}
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (t : GL (Fin n) (PSUF g)) (htU : t ∈ GUsub (PSUσ g) n) (hcomm : Commute t s) :
    ∃ s₁ : GL (Fin n) (PSUF g),
      s₁ ∈ rckPSU_Gt s ε ∧
      (s₁ : Matrix (Fin n) (Fin n) (PSUF g)) =
        (t : Matrix (Fin n) (Fin n) (PSUF g)) * ε + (1 - ε) ∧
      (t : Matrix (Fin n) (Fin n) (PSUF g)) * ε =
        ε * (t : Matrix (Fin n) (Fin n) (PSUF g)) ∧
      ∀ u ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε),
        t * u * t⁻¹ = s₁ * u * s₁⁻¹ := by
  have hS : ∀ u ∈ ({s} : Set (GL (Fin n) (PSUF g))),
      ∀ v ∈ ({s} : Set (GL (Fin n) (PSUF g))), Commute u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u; subst v
    exact Commute.refl s
  obtain ⟨hcommε, s₁, hval, hmem, -, hconj⟩ :=
    rckGLBlock_restrict (S := ({s} : Set (GL (Fin n) (PSUF g)))) hS hε.1 hε.2.1 t (fun u hu => by
      rw [Set.mem_singleton_iff] at hu
      subst u
      exact hcomm)
  refine ⟨s₁, ?_, hval, hcommε, hconj⟩
  refine Subgroup.mem_inf.mpr ⟨hmem, ?_⟩
  exact mem_GUsub_iff.mpr (rckGLBlock_restrict_isometry (σ := (PSUσ g).toRingHom)
    (G := Unitary.antidiag n) (PSUantidiag_isUnit_det n g) hε.2.2.2.1 hε.2.1
    (mem_GUsub_iff.mp htU) hcommε hval)

private theorem rckPSU_commute_lifts {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    (t : ↥(psuE ψ A)) : Commute (t.1 : GL (Fin n) (PSUF g)) s := by
  obtain ⟨-, b, hb, hlift⟩ := mem_psuE.mp t.2
  exact hH.commute_lifts hb heA hlift hs

private noncomputable def rckPSU_restrictFun {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (t : ↥(psuE ψ A)) : GL (Fin n) (PSUF g) :=
  Classical.choose (rckPSU_blockRestrict_exists hε t.1 (mem_psuE.mp t.2).1
    (rckPSU_commute_lifts hH heA hs t))

private theorem rckPSU_restrictFun_spec {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (t : ↥(psuE ψ A)) :
    rckPSU_restrictFun hH heA hs hε t ∈ rckPSU_Gt s ε ∧
      (rckPSU_restrictFun hH heA hs hε t : Matrix (Fin n) (Fin n) (PSUF g)) =
        (t.1 : Matrix (Fin n) (Fin n) (PSUF g)) * ε + (1 - ε) ∧
      (t.1 : Matrix (Fin n) (Fin n) (PSUF g)) * ε =
        ε * (t.1 : Matrix (Fin n) (Fin n) (PSUF g)) ∧
      ∀ u ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε),
        t.1 * u * t.1⁻¹ = rckPSU_restrictFun hH heA hs hε t * u *
          (rckPSU_restrictFun hH heA hs hε t)⁻¹ := by
  unfold rckPSU_restrictFun
  exact Classical.choose_spec (rckPSU_blockRestrict_exists hε t.1 (mem_psuE.mp t.2).1
    (rckPSU_commute_lifts hH heA hs t))

private theorem rckPSU_restrictFun_one {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε) :
    rckPSU_restrictFun hH heA hs hε (1 : ↥(psuE ψ A)) = 1 := by
  apply Units.ext
  rw [(rckPSU_restrictFun_spec hH heA hs hε (1 : ↥(psuE ψ A))).2.1]
  rw [Subgroup.coe_one, Units.val_one, Matrix.one_mul]
  abel

private theorem rckPSU_restrictFun_mul {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (a b : ↥(psuE ψ A)) :
    rckPSU_restrictFun hH heA hs hε (a * b) =
      rckPSU_restrictFun hH heA hs hε a * rckPSU_restrictFun hH heA hs hε b := by
  apply Units.ext
  rw [(rckPSU_restrictFun_spec hH heA hs hε (a * b)).2.1]
  rw [Units.val_mul]
  rw [(rckPSU_restrictFun_spec hH heA hs hε a).2.1,
    (rckPSU_restrictFun_spec hH heA hs hε b).2.1]
  rw [Subgroup.coe_mul]
  exact (rckPSU_block_mul hε.2.1
    (rckPSU_restrictFun_spec hH heA hs hε a).2.2.1
    (rckPSU_restrictFun_spec hH heA hs hε b).2.2.1).symm

private noncomputable def rckPSU_restrictHom {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε) :
    ↥(psuE ψ A) →* rckPSU_Gt s ε where
  toFun t := ⟨rckPSU_restrictFun hH heA hs hε t,
    (rckPSU_restrictFun_spec hH heA hs hε t).1⟩
  map_one' := Subtype.ext (rckPSU_restrictFun_one hH heA hs hε)
  map_mul' a b := Subtype.ext (rckPSU_restrictFun_mul hH heA hs hε a b)

private theorem rckPSU_restrictHom_conj {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (t : ↥(psuE ψ A)) {u : GL (Fin n) (PSUF g)}
    (hu : u ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε)) :
    t.1 * u * t.1⁻¹ =
      ((rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) : GL (Fin n) (PSUF g)) * u *
        (((rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) :
          GL (Fin n) (PSUF g)))⁻¹ :=
  (rckPSU_restrictFun_spec hH heA hs hε t).2.2.2 u hu

private lemma rckPSU_unitary_range_card_le {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B₁ : Subgroup X} (hB₁ : IsElemAbelian p B₁)
    {m Q : ℕ} (hm : m ≤ 3) {E : Type} [Field E] [Finite E] [CharP E 2]
    (β' : ↥B₁ →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E)) :
    Nat.card β'.range ≤ p ^ 2 := by
  have htop : IsElemAbelian p (⊤ : Subgroup ↥B₁) := by
    simpa using hB₁.subgroupOf B₁
  have hE : IsElemAbelian p β'.range := by
    simpa [MonoidHom.range_eq_map] using htop.map β'
  have hpE : (p : E) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff E 2]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst m
    haveI : Subsingleton (GL (Fin 0) E) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Subsingleton (CFSG.Open.StatedProj (ClassicalBlocks.GUFull 0 Q E)) := inferInstance
    have hle1 : Nat.card β'.range ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    exact hle1.trans (Nat.one_le_pow 2 p hp.pos)
  · have hle := CFSG.LocalAnalysis.GLTheoremA.card_le_pow_statedProj hp hp2 hpE hmpos
        (ClassicalBlocks.GUFull m Q E) β'.range hE
    have hm2 : m - 1 ≤ 2 := by omega
    exact hle.trans (pow_le_pow_right₀ hp.one_le hm2)

private theorem rckPSU_restrictHom_center_of_scalar {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    (t : ↥(psuE ψ A)) {c : PSUF g}
    (hc : (t.1 : Matrix (Fin n) (Fin n) (PSUF g)) = Matrix.scalar (Fin n) c) :
    (rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) ∈
      Subgroup.center (rckPSU_Gt s ε) := by
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  have hu : (u : GL (Fin n) (PSUF g)) ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) :=
    (Subgroup.mem_inf.mp u.2).1
  have hconj := rckPSU_restrictHom_conj hH heA hs hε t hu
  have htcenter : (t.1 : GL (Fin n) (PSUF g)) ∈
      Subgroup.center (GL (Fin n) (PSUF g)) := mem_center_GL_of_scalar hc
  have htu : (u : GL (Fin n) (PSUF g)) * t.1 = t.1 * (u : GL (Fin n) (PSUF g)) :=
    Subgroup.mem_center_iff.mp htcenter (u : GL (Fin n) (PSUF g))
  have hleft : t.1 * (u : GL (Fin n) (PSUF g)) * t.1⁻¹ = (u : GL (Fin n) (PSUF g)) := by
    rw [← htu]
    group
  rw [hleft] at hconj
  have h := congrArg (fun x : GL (Fin n) (PSUF g) =>
    x * ((rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) : GL (Fin n) (PSUF g))) hconj
  simpa [mul_assoc] using h

private theorem rckPSU_betaTilde_ker {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A : Subgroup X}
    (hH : PSULiftHyp n g ψ p A) {e : X} (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (Φ : rckPSU_Gt s ε ≃* ↥(ClassicalBlocks.GUFull m Q E)) :
    hH.phi.ker ≤ ((QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp
        (rckPSU_restrictHom hH heA hs hε))).ker := by
  intro t ht
  have hphi : hH.phi t = 1 := MonoidHom.mem_ker.mp ht
  obtain ⟨c, hc⟩ := hH.scalar_of_phi_eq_one hphi
  have hcenterGt := rckPSU_restrictHom_center_of_scalar hH heA hs hε t hc
  have hcenterGU : Φ (rckPSU_restrictHom hH heA hs hε t) ∈
      Subgroup.center ↥(ClassicalBlocks.GUFull m Q E) :=
    (MulEquivClass.apply_mem_center_iff Φ).mpr hcenterGt
  have hmem : Φ (rckPSU_restrictHom hH heA hs hε t) ∈
      (CFSG.Open.StatedScalars (Fin m) E).subgroupOf (ClassicalBlocks.GUFull m Q E) :=
    center_GUFull_le_statedScalars (m := m) (Q := Q) (E := E) hE hcenterGU
  have hq : (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E))) (Φ (rckPSU_restrictHom hH heA hs hε t)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hq

private noncomputable def rckPSU_beta {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A B₁ : Subgroup X} {e : X}
    (hH : PSULiftHyp n g ψ p A) (hB₁A : B₁ ≤ A) (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (Φ : rckPSU_Gt s ε ≃* ↥(ClassicalBlocks.GUFull m Q E)) :
    ↥B₁ →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E) :=
  let βtilde : ↥(psuE ψ A) →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E))).comp (Φ.toMonoidHom.comp
        (rckPSU_restrictHom hH heA hs hε))
  let βA : ↥A →* CFSG.Open.StatedProj (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.lift hH.phi.ker βtilde
      (rckPSU_betaTilde_ker hH heA hs hε hE Φ)).comp
      (QuotientGroup.quotientKerEquivOfSurjective hH.phi hH.phi_surjective).symm.toMonoidHom
  βA.comp (Subgroup.inclusion hB₁A)

private theorem rckPSU_beta_apply {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A B₁ : Subgroup X} {e : X}
    (hH : PSULiftHyp n g ψ p A) (hB₁A : B₁ ≤ A) (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (Φ : rckPSU_Gt s ε ≃* ↥(ClassicalBlocks.GUFull m Q E))
    {b : ↥B₁} {t : ↥(psuE ψ A)} (ht : hH.phi t = (⟨b, hB₁A b.2⟩ : ↥A)) :
    rckPSU_beta hH hB₁A heA hs hε hE Φ b =
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
        (ClassicalBlocks.GUFull m Q E))) (Φ (rckPSU_restrictHom hH heA hs hε t)) := by
  have hker : (QuotientGroup.quotientKerEquivOfSurjective hH.phi hH.phi_surjective)
      (QuotientGroup.mk' hH.phi.ker t) = (⟨b, hB₁A b.2⟩ : ↥A) := by
    change hH.phi t = (⟨b, hB₁A b.2⟩ : ↥A)
    exact ht
  have heq : (QuotientGroup.quotientKerEquivOfSurjective hH.phi hH.phi_surjective).symm
      (⟨b, hB₁A b.2⟩ : ↥A) = QuotientGroup.mk' hH.phi.ker t := by
    rw [← hker, MulEquiv.symm_apply_apply]
  unfold rckPSU_beta
  dsimp only
  simp only [MonoidHom.comp_apply, Subgroup.coe_inclusion, MulEquiv.coe_toMonoidHom]
  rw [show (Subgroup.inclusion hB₁A) b = (⟨b, hB₁A b.2⟩ : ↥A) from rfl]
  rw [heq]
  rfl

private theorem rckPSU_beta_ker {X : Type} [Group X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {A B₁ K : Subgroup X} {e : X}
    (hH : PSULiftHyp n g ψ p A) (hB₁A : B₁ ≤ A) (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (Φ : rckPSU_Gt s ε ≃* ↥(ClassicalBlocks.GUFull m Q E))
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'G : J' ≤ glBlockCentralizer (PSUj n g) {s} ε) (hJ'K : J'.map ψ = K) :
    ∀ b : ↥B₁, rckPSU_beta hH hB₁A heA hs hε hE Φ b = 1 →
      (b : X) ∈ Subgroup.centralizer (K : Set X) := by
  intro b hb
  let bA : ↥A := ⟨b, hB₁A b.2⟩
  let t : ↥(psuE ψ A) := Function.surjInv hH.phi_surjective bA
  have ht : hH.phi t = bA := Function.surjInv_eq hH.phi_surjective bA
  have hβt : (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin m) E).subgroupOf
      (ClassicalBlocks.GUFull m Q E)))
      (Φ (rckPSU_restrictHom hH heA hs hε t)) = 1 := by
    rw [← rckPSU_beta_apply hH hB₁A heA hs hε hE Φ ht]
    exact hb
  have hmem : Φ (rckPSU_restrictHom hH heA hs hε t) ∈
      (CFSG.Open.StatedScalars (Fin m) E).subgroupOf (ClassicalBlocks.GUFull m Q E) :=
    (QuotientGroup.eq_one_iff _).mp hβt
  have hcenterGU : Φ (rckPSU_restrictHom hH heA hs hε t) ∈
      Subgroup.center ↥(ClassicalBlocks.GUFull m Q E) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hscalar : (Φ (rckPSU_restrictHom hH heA hs hε t) : GL (Fin m) E) ∈
        CFSG.Open.StatedScalars (Fin m) E := Subgroup.mem_subgroupOf.mp hmem
    have hgl : (Φ (rckPSU_restrictHom hH heA hs hε t) : GL (Fin m) E) ∈
        Subgroup.center (GL (Fin m) E) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hscalar
    exact Subgroup.mem_center_iff.mp hgl (z : GL (Fin m) E)
  have hcenterGt : (rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) ∈
      Subgroup.center (rckPSU_Gt s ε) :=
    (MulEquivClass.apply_mem_center_iff Φ).mp hcenterGU
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨y, hyJ', hyk⟩ := Subgroup.mem_map.mp (by rwa [← hJ'K] at hk)
  rw [← hyk]
  have hyGF : (PSUj n g y : GL (Fin n) (PSUF g)) ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) :=
    Subgroup.mem_comap.mp (hJ'G hyJ')
  have hyU : (PSUj n g y : GL (Fin n) (PSUF g)) ∈ GUsub (PSUσ g) n := by
    rw [mem_GUsub_iff]
    simpa [Unitary.conjTr] using (Unitary.mem_SU.mp y.2).2
  let yT : rckPSU_Gt s ε := ⟨(PSUj n g y : GL (Fin n) (PSUF g)), ⟨hyGF, hyU⟩⟩
  have hcentral : ((rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) * yT *
      (rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε)⁻¹) = yT := by
    have hcomm := Subgroup.mem_center_iff.mp hcenterGt yT
    rw [← hcomm]
    group
  have hcentralGL : ((rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) :
      GL (Fin n) (PSUF g)) * (PSUj n g y : GL (Fin n) (PSUF g)) *
      (((rckPSU_restrictHom hH heA hs hε t : rckPSU_Gt s ε) :
        GL (Fin n) (PSUF g)))⁻¹ = (PSUj n g y : GL (Fin n) (PSUF g)) := by
    have h := congrArg (fun z : rckPSU_Gt s ε => (z : GL (Fin n) (PSUF g))) hcentral
    simpa [yT, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hconj := rckPSU_restrictHom_conj hH heA hs hε t hyGF
  rw [hcentralGL] at hconj
  obtain ⟨u', hj, hψ⟩ := hH.isGLLift_phi t y
  have hj' : PSUj n g u' = PSUj n g y := by rw [hj, hconj]
  have hu' : u' = y := Subtype.ext hj'
  rw [hu', ht] at hψ
  have hψ' : (b : X)⁻¹ * ψ y * (b : X) = ψ y := by simpa [bA] using hψ
  exact (calc (b : X) * ψ y =
      (b : X) * ((b : X)⁻¹ * ψ y * (b : X)) := by rw [hψ']
    _ = ψ y * (b : X) := by group).symm

theorem rckEq_of_block_unitarySmall_PSU {n g : ℕ} {X : Type} [Group X] [Finite X] {p : ℕ}
    {A B₁ D J K : Subgroup X} {d e : X} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X}
    (hH : PSULiftHyp n g ψ p A) (hB₁A : B₁ ≤ A) (hDcard : Nat.card D = p ^ 2)
    (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hp4 : p ^ 4 ≤ Nat.card B₁)
    (hJK : J ≤ K) (hK : IsQuasisimple ↥K) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) (heA : e ∈ A)
    {s : GL (Fin n) (PSUF g)} (hs : IsGLLift (PSUj n g) ψ s e)
    {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'G : J' ≤ glBlockCentralizer (PSUj n g) {s} ε) (hJ'K : J'.map ψ = K)
    {m Q : ℕ} (hm : m ≤ 3) {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (Φ : ↥(Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
        GUsub (PSUσ g) n) ≃* ↥(ClassicalBlocks.GUFull m Q E)) :
    K = J := by
  refine rckEq_of_blockAction hH.prime hDcard hB₁J hp4 hJK hK hdD hJ
    (rckPSU_beta hH hB₁A heA hs hε hE Φ) ?_ ?_
  · exact rckPSU_beta_ker hH hB₁A heA hs hε hE Φ hJ'G hJ'K
  · exact rckPSU_unitary_range_card_le hH.prime hH.ne_two (hH.elem.mono hB₁A) hm
      (rckPSU_beta hH hB₁A heA hs hε hE Φ)

end CFSG.StandardType.RCKRP
