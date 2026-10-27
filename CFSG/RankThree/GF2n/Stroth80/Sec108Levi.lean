module

public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GF2n.Smith81.TiD2Alg
public import TauCeti.Algebra.GroupAction.TypeTags

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open Matrix
open scoped commutatorElement

variable {𝓜 : Type} [Group 𝓜]

abbrev NL (L : Subgroup 𝓜) : Subgroup 𝓜 := Subgroup.normalizer (L : Set 𝓜)

abbrev GG (L : Subgroup 𝓜) : Type := ↥(NL L) ⧸ L.subgroupOf (NL L)

abbrev mkG (L : Subgroup 𝓜) : ↥(NL L) →* GG L := QuotientGroup.mk' (L.subgroupOf (NL L))

@[expose] def Yhat (L N : Subgroup 𝓜) : Subgroup (GG L) := (N.subgroupOf (NL L)).map (mkG L)

@[expose] def Pfrak (L R : Subgroup 𝓜) : Subgroup (GG L) := (R.subgroupOf (NL L)).map (mkG L)

@[expose] def Nfrak (L Y : Subgroup 𝓜) : Subgroup (GG L) :=
  ((Subgroup.normalizer (Y : Set 𝓜)).subgroupOf (NL L)).map (mkG L)

@[expose] def P0frak (L R : Subgroup 𝓜) : Subgroup (GG L) := ⁅Pfrak L R, Pfrak L R⁆

@[expose] def Xlevi (L R : Subgroup 𝓜) : Subgroup (GG L) := ⁅P0frak L R, P0frak L R⁆

@[expose] def Kfrak (L R : Subgroup 𝓜) : Subgroup (GG L) :=
  Subgroup.centralizer (Xlevi L R : Set (GG L))

abbrev NLY (L Y : Subgroup 𝓜) : Subgroup 𝓜 :=
  Subgroup.normalizer (L : Set 𝓜) ⊓ Subgroup.normalizer (Y : Set 𝓜)

abbrev e₀ (K : Type) [Field K] : Fin 3 → K := Pi.single 0 1

structure Levi108 (K : Type) [Field K] [Finite K] [CharP K 2] (L R N Y : Subgroup 𝓜)
    (ρ : ↥R →* GL (Fin 3) K) (μ : ↥N →* Multiplicative (Fin 3 → K))
    (T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)) : Prop where
  four_le_card : 4 ≤ Nat.card K
  elemAb_L : IsElemAbelian 2 L
  elemAb_N : IsElemAbelian 2 N
  L_le_R : L ≤ R
  N_le_R : N ≤ R
  Y_le_N : Y ≤ N
  Y_le_centralizer : Y ≤ Subgroup.centralizer (R : Set 𝓜)
  range_rho : ρ.range = StatedSL 3 K
  ker_rho : ρ.ker = N.subgroupOf R
  rho_L : ∀ l (hl : l ∈ L), ∃ u : Fin 3 → K, u 0 = 0 ∧
    (ρ ⟨l, L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec (e₀ K) u
  exists_L : ∀ u : Fin 3 → K, u 0 = 0 → ∃ l, ∃ hl : l ∈ L,
    (ρ ⟨l, L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec (e₀ K) u
  mem_normalizer_iff : ∀ r (hr : r ∈ R), r ∈ Subgroup.normalizer (L : Set 𝓜) ↔
    (ρ ⟨r, hr⟩ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (ρ ⟨r, hr⟩ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0
  surjective_mu : Function.Surjective μ
  ker_mu : μ.ker = Y.subgroupOf N
  mu_conj : ∀ r (hr : r ∈ R) n (hn : n ∈ N) n' (hn' : n' ∈ N), n' = r * n * r⁻¹ →
    Multiplicative.toAdd (μ ⟨n', hn'⟩) =
      (((ρ ⟨r, hr⟩)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ
        Multiplicative.toAdd (μ ⟨n, hn⟩)
  mem_L_iff_mu : ∀ n (hn : n ∈ N), n ∈ L ↔ Multiplicative.toAdd (μ ⟨n, hn⟩) 0 = 0
  normalizer_Y_le : Subgroup.normalizer (Y : Set 𝓜) ≤ Subgroup.normalizer (R : Set 𝓜)
  normalizer_inf_le :
    Subgroup.normalizer ((L ⊓ N : Subgroup 𝓜) : Set 𝓜) ≤ Subgroup.normalizer (Y : Set 𝓜)
  T_semilinear : ∀ g : ↥(NLY L Y), ∃ σ : K ≃+* K, ∀ (c : K) (v : Fin 3 → K),
    T g (c • v) = σ c • T g v
  T_line : ∀ g : ↥(NLY L Y), ∃ c : K, T g (e₀ K) = c • e₀ K
  T_rho : ∀ (g : ↥(NLY L Y)) (hg : (g : 𝓜) ∈ R) (v : Fin 3 → K),
    T g v = (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ v
  T_ker_comm : ⁅⁅T.ker, T.ker⁆, ⁅T.ker, T.ker⁆⁆ ≤ N.subgroupOf (NLY L Y)
  T_ker_two : ∀ g : ↥(NLY L Y), T g = 1 → ∀ k : ℕ, (g : 𝓜) ^ 2 ^ k ∈ N → (g : 𝓜) ∈ N

section LeviFactor

variable {K : Type} [Field K] [Finite K] [CharP K 2] {L R N Y : Subgroup 𝓜}
  {ρ : ↥R →* GL (Fin 3) K} {μ : ↥N →* Multiplicative (Fin 3 → K)}
  {T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)}

private abbrev Psub (L R : Subgroup 𝓜) : Subgroup 𝓜 := R ⊓ NL L

private abbrev qP (L R : Subgroup 𝓜) : ↥(Psub L R) →* GG L :=
  (mkG L).comp (Subgroup.inclusion inf_le_right)

private noncomputable def rhoP (ρ : ↥R →* GL (Fin 3) K) (L : Subgroup 𝓜) :
    ↥(Psub L R) →* GL (Fin 3) K where
  toFun p := ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
  map_one' := by
    change ρ (1 : ↥R) = 1
    exact map_one ρ
  map_mul' p q := by
    change ρ (⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ * ⟨q.1, (Subgroup.mem_inf.mp q.2).1⟩) =
      ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ * ρ ⟨q.1, (Subgroup.mem_inf.mp q.2).1⟩
    rw [map_mul]

@[simp] private lemma rhoP_apply (p : ↥(Psub L R)) :
    rhoP ρ L p = ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ := rfl

private lemma range_qP (L R : Subgroup 𝓜) : (qP L R).range = Pfrak L R := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p.1, p.2.2⟩, p.2.1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, hy, y.2⟩, rfl⟩

private lemma det_rho_eq_one (hC : Levi108 K L R N Y ρ μ T) (r : ↥R) :
    ((ρ r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have hmem : ρ r ∈ StatedSL 3 K := by
    rw [← hC.range_rho]
    exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
  exact CFSG.Open.StatedAPI.mem_statedSL_iff.mp hmem

private lemma rhoP_lower (hC : Levi108 K L R N Y ρ μ T) (p : ↥(Psub L R)) :
    (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  simpa using (hC.mem_normalizer_iff p.1 (Subgroup.mem_inf.mp p.2).1).mp
    (Subgroup.mem_inf.mp p.2).2

private lemma rhoP_00_ne_zero (hC : Levi108 K L R N Y ρ μ T) (p : ↥(Psub L R)) :
    (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
  intro h0
  have hdet : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 :=
    det_rho_eq_one hC ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
  have hlow := rhoP_lower hC p
  have hcol : ∀ i, (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) i 0 = 0 := by
    intro i
    fin_cases i
    · exact h0
    · exact hlow.1
    · exact hlow.2
  have hzero : (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero 0 hcol
  have hzero' : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 0 := by
    simpa using hzero
  rw [hdet] at hzero'
  exact one_ne_zero hzero'

private noncomputable def chi (hC : Levi108 K L R N Y ρ μ T) : ↥(Psub L R) →* Kˣ where
  toFun p := Units.mk0 ((rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) 0 0) (rhoP_00_ne_zero hC p)
  map_one' := by
    apply Units.ext
    change ((ρ (1 : ↥R) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1
    simp
  map_mul' p q := by
    apply Units.ext
    have hlow := rhoP_lower hC q
    simp only [rhoP_apply] at hlow
    simp only [Units.val_mk0, Units.val_mul, map_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_three, hlow.1, hlow.2, mul_zero, add_zero, rhoP_apply]

private lemma chi_eq_one_of_mem_L (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L) :
    chi hC ⟨l, Subgroup.mem_inf.mpr ⟨hC.L_le_R hl, Subgroup.le_normalizer hl⟩⟩ = 1 := by
  apply Units.ext
  change ((ρ ⟨l, hC.L_le_R hl⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1
  obtain ⟨u, hu0, hu⟩ := hC.rho_L l hl
  rw [hu]
  simp [Matrix.vecMulVec, e₀, hu0]

private lemma chi_eq_one_of_mem_commutator (hC : Levi108 K L R N Y ρ μ T) {p : ↥(Psub L R)}
    (hp : p ∈ ⁅(⊤ : Subgroup ↥(Psub L R)), (⊤ : Subgroup ↥(Psub L R))⁆) :
    chi hC p = 1 := by
  have hle : ⁅(⊤ : Subgroup ↥(Psub L R)), (⊤ : Subgroup ↥(Psub L R))⁆ ≤ (chi hC).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact MonoidHom.mem_ker.mp (hle hp)

private lemma P0_eq_map_commutator :
    P0frak L R = Subgroup.map (qP L R) ⁅(⊤ : Subgroup ↥(Psub L R)),
      (⊤ : Subgroup ↥(Psub L R))⁆ := by
  rw [P0frak, ← range_qP L R, MonoidHom.range_eq_map (qP L R), Subgroup.map_commutator]

private noncomputable def diagGL (A : Matrix.SpecialLinearGroup (Fin 2) K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.reindex (finSumFinEquiv (m := 1) (n := 2)) (finSumFinEquiv (m := 1) (n := 2))
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 0 (A : Matrix (Fin 2) (Fin 2) K)))
    (by
      rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, A.2, one_mul]
      exact one_ne_zero)

private lemma diagGL_val (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (diagGL A : Matrix (Fin 3) (Fin 3) K) =
      Matrix.reindex (finSumFinEquiv (m := 1) (n := 2)) (finSumFinEquiv (m := 1) (n := 2))
        (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 0
          (A : Matrix (Fin 2) (Fin 2) K)) := rfl

private lemma diagGL_det (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (diagGL A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [diagGL_val, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one,
    A.2, one_mul]

private lemma diagGL_succ_succ (A : Matrix.SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    (diagGL A : Matrix (Fin 3) (Fin 3) K) i.succ j.succ = A i j := by
  have hsymm (i : Fin 2) : (finSumFinEquiv (m := 1) (n := 2)).symm i.succ = Sum.inr i := by
    rw [show (i.succ : Fin 3) = Fin.natAdd 1 i from by
      ext
      simp [Fin.val_succ, Fin.val_natAdd, Nat.add_comm]]
    exact finSumFinEquiv_symm_apply_natAdd (m := 1) (n := 2) i
  rw [diagGL_val]
  change (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 0
    (A : Matrix (Fin 2) (Fin 2) K))
      ((finSumFinEquiv (m := 1) (n := 2)).symm i.succ)
      ((finSumFinEquiv (m := 1) (n := 2)).symm j.succ) = A i j
  rw [hsymm i, hsymm j]
  simp [Matrix.fromBlocks]

private lemma diagGL_succ_zero (A : Matrix.SpecialLinearGroup (Fin 2) K) (i : Fin 2) :
    (diagGL A : Matrix (Fin 3) (Fin 3) K) i.succ 0 = 0 := by
  have h0e : (finSumFinEquiv (m := 1) (n := 2)) (Sum.inl (0 : Fin 1)) = 0 := by
    rw [finSumFinEquiv_apply_left]
    simp
  have h0 : (finSumFinEquiv (m := 1) (n := 2)).symm (0 : Fin 3) = Sum.inl 0 := by
    rw [← h0e]
    exact Equiv.symm_apply_apply _ _
  have hsymm (i : Fin 2) : (finSumFinEquiv (m := 1) (n := 2)).symm i.succ = Sum.inr i := by
    rw [show (i.succ : Fin 3) = Fin.natAdd 1 i from by
      ext
      simp [Fin.val_succ, Fin.val_natAdd, Nat.add_comm]]
    exact finSumFinEquiv_symm_apply_natAdd (m := 1) (n := 2) i
  rw [diagGL_val]
  change (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 0
    (A : Matrix (Fin 2) (Fin 2) K))
      ((finSumFinEquiv (m := 1) (n := 2)).symm i.succ)
      ((finSumFinEquiv (m := 1) (n := 2)).symm (0 : Fin 3)) = 0
  rw [hsymm i, h0]
  simp [Matrix.fromBlocks]

private lemma diagGL_mem_statedSL (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    diagGL A ∈ StatedSL 3 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  exact diagGL_det A

private lemma block_mul_apply (A B : Matrix (Fin 3) (Fin 3) K)
    (hA1 : A 1 0 = 0) (hA2 : A 2 0 = 0) (hB1 : B 1 0 = 0) (hB2 : B 2 0 = 0)
    (i j : Fin 2) :
    (A * B) i.succ j.succ = ∑ k : Fin 2, A i.succ k.succ * B k.succ j.succ := by
  rw [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> simp [Fin.succ_zero_eq_one, hA1, hA2]

private lemma block_det_ne_zero (hC : Levi108 K L R N Y ρ μ T) (p : ↥(Psub L R)) :
    ((rhoP ρ L p : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ).det ≠ 0 := by
  have hlow := rhoP_lower hC p
  have hlow1 : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by simpa [rhoP_apply] using hlow.1
  have hlow2 : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by simpa [rhoP_apply] using hlow.2
  have hdet : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 :=
    det_rho_eq_one hC ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
  have h := Matrix.det_succ_column_zero
    ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [Fin.sum_univ_three] at h
  simp [hlow1, hlow2] at h
  intro hzero
  have hzero' : (((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ).det = 0 := by
    simpa [rhoP_apply] using hzero
  rw [hdet, hzero', mul_zero] at h
  exact one_ne_zero h

private lemma block_mul (hC : Levi108 K L R N Y ρ μ T) (p q : ↥(Psub L R)) :
    ((rhoP ρ L (p * q) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).submatrix
        Fin.succ Fin.succ =
      ((rhoP ρ L p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ *
        ((rhoP ρ L q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).submatrix
          Fin.succ Fin.succ := by
  rw [map_mul, Matrix.GeneralLinearGroup.coe_mul]
  ext i j
  rw [Matrix.submatrix_apply]
  rw [block_mul_apply (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K)
    (rhoP ρ L q : Matrix (Fin 3) (Fin 3) K) (rhoP_lower hC p).1 (rhoP_lower hC p).2
    (rhoP_lower hC q).1 (rhoP_lower hC q).2 i j]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Fin.sum_univ_two]

private noncomputable def blk (hC : Levi108 K L R N Y ρ μ T) :
    ↥(Psub L R) →* GL (Fin 2) K where
  toFun p := Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((rhoP ρ L p : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ) (block_det_ne_zero hC p)
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have h : ((rhoP ρ L (1 : ↥(Psub L R)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [map_one]
      rfl
    have h2 : ((rhoP ρ L (1 : ↥(Psub L R)) : Matrix (Fin 3) (Fin 3) K).submatrix
        Fin.succ Fin.succ) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      rw [h]
      simp [Matrix.one_apply]
    simpa [Matrix.GeneralLinearGroup.mkOfDetNeZero] using h2
  map_mul' p q := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have h := congrFun (congrFun (block_mul hC p q) i) j
    simpa [Matrix.GeneralLinearGroup.mkOfDetNeZero] using h

private lemma toGL_range_le_blk_range (hC : Levi108 K L R N Y ρ μ T) :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range ≤
      (blk hC).range := by
  intro X hX
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hX
  have hmem : diagGL A ∈ ρ.range := by
    rw [hC.range_rho]
    exact diagGL_mem_statedSL A
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hmem
  have hrNL : (r : 𝓜) ∈ NL L := by
    refine (hC.mem_normalizer_iff r.1 r.2).mpr ⟨?_, ?_⟩
    · rw [hr]
      simpa using diagGL_succ_zero A 0
    · rw [hr]
      simpa using diagGL_succ_zero A 1
  let p : ↥(Psub L R) := ⟨r.1, Subgroup.mem_inf.mpr ⟨r.2, hrNL⟩⟩
  refine ⟨p, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((rhoP ρ L p : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ) i j =
    (A : Matrix (Fin 2) (Fin 2) K) i j
  have hp : (⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : ↥R) = r := Subtype.ext rfl
  rw [rhoP_apply, hp, hr]
  exact diagGL_succ_succ A i j

private lemma mem_N_conj (hC : Levi108 K L R N Y ρ μ T) {r : 𝓜} (hr : r ∈ R) {n : 𝓜}
    (hn : n ∈ N) : r * n * r⁻¹ ∈ N := by
  have hmem : (⟨r * n * r⁻¹, R.mul_mem (R.mul_mem hr (hC.N_le_R hn)) (R.inv_mem hr)⟩ : ↥R) ∈
      ρ.ker := by
    rw [MonoidHom.mem_ker]
    have hnker : (⟨n, hC.N_le_R hn⟩ : ↥R) ∈ ρ.ker := by
      rw [hC.ker_rho]
      exact hn
    have hn1 : ρ ⟨n, hC.N_le_R hn⟩ = 1 := MonoidHom.mem_ker.mp hnker
    change ρ (⟨r, hr⟩ * ⟨n, hC.N_le_R hn⟩ * ⟨r, hr⟩⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hn1]
    simp
  rw [hC.ker_rho] at hmem
  exact hmem

private lemma diag_inv_transpose_mulVec_zero (β : K) (hβ0 : β ≠ 0) (v : Fin 3 → K) :
    (((Matrix.diagonal (![β, β⁻¹, 1] : Fin 3 → K))⁻¹)ᵀ *ᵥ v) 0 = β⁻¹ * v 0 := by
  have hDM : (Matrix.diagonal (![β⁻¹, β, 1] : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal (![β, β⁻¹, 1] : Fin 3 → K) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hβ0]
  have hMinv : (Matrix.diagonal (![β, β⁻¹, 1] : Fin 3 → K) :
      Matrix (Fin 3) (Fin 3) K)⁻¹ = Matrix.diagonal (![β⁻¹, β, 1] : Fin 3 → K) :=
    Matrix.inv_eq_left_inv hDM
  rw [hMinv, Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
  change (![β⁻¹, β, 1] : Fin 3 → K) 0 * v 0 = β⁻¹ * v 0
  simp

private lemma exists_diag_rho (hC : Levi108 K L R N Y ρ μ T) {β : K} (hβ0 : β ≠ 0) :
    ∃ r : ↥R, (ρ r : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![β, β⁻¹, 1] ∧
      (r : 𝓜) ∈ NL L := by
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![β, β⁻¹, 1]
  have hdetM : M.det = 1 := by
    simp [M, Matrix.det_diagonal, Fin.prod_univ_three, hβ0]
  let A : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdetM]; exact one_ne_zero)
  have hA : A ∈ StatedSL 3 K := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    simpa [A] using hdetM
  have hmem : A ∈ ρ.range := by
    rw [hC.range_rho]
    exact hA
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨r, ?_, ?_⟩
  · rw [hr]
    simp [A, M]
  · refine (hC.mem_normalizer_iff r.1 r.2).mpr ⟨?_, ?_⟩
    · rw [hr]
      simp [A, M]
    · rw [hr]
      simp [A, M]

private lemma vecMulVec_e0_mul_self (u : Fin 3 → K) (hu0 : u 0 = 0) :
    Matrix.vecMulVec (e₀ K) u * Matrix.vecMulVec (e₀ K) u = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have h : (u ⬝ᵥ e₀ K) = 0 := by
    simp [dotProduct_single, e₀, hu0]
  rw [h, zero_smul, Matrix.vecMulVec_zero]

private lemma one_sub_vecMulVec_mul_one_add (u : Fin 3 → K) (hu0 : u 0 = 0) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - Matrix.vecMulVec (e₀ K) u) *
      (1 + Matrix.vecMulVec (e₀ K) u) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, vecMulVec_e0_mul_self u hu0]
  abel

private lemma inv_one_add_vecMulVec (u : Fin 3 → K) (hu0 : u 0 = 0) :
    ((1 : Matrix (Fin 3) (Fin 3) K) + Matrix.vecMulVec (e₀ K) u)⁻¹ =
      1 - Matrix.vecMulVec (e₀ K) u :=
  Matrix.inv_eq_left_inv (one_sub_vecMulVec_mul_one_add u hu0)

private lemma transpose_inv_one_add_vecMulVec (u : Fin 3 → K) (hu0 : u 0 = 0) :
    (((1 : Matrix (Fin 3) (Fin 3) K) + Matrix.vecMulVec (e₀ K) u)⁻¹)ᵀ =
      1 - Matrix.vecMulVec u (e₀ K) := by
  rw [inv_one_add_vecMulVec u hu0, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

private lemma one_sub_vecMulVec_mulVec (u v : Fin 3 → K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - Matrix.vecMulVec u (e₀ K)) *ᵥ v = v - v 0 • u := by
  ext i
  simp [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_single,
    e₀, MulOpposite.op_smul]

private theorem mu_conj_of_mem_L (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L) {u : Fin 3 → K}
    (hu0 : u 0 = 0)
    (hu : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec (e₀ K) u)
    {n : 𝓜} (hn : n ∈ N) (hn' : l * n * l⁻¹ ∈ N) :
    Multiplicative.toAdd (μ ⟨l * n * l⁻¹, hn'⟩) =
      Multiplicative.toAdd (μ ⟨n, hn⟩) - Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u := by
  have hmu := hC.mu_conj l (hC.L_le_R hl) n hn (l * n * l⁻¹) hn' rfl
  rw [Matrix.GeneralLinearGroup.coe_inv, hu, transpose_inv_one_add_vecMulVec u hu0,
    one_sub_vecMulVec_mulVec] at hmu
  exact hmu

private lemma conj_mem_L (hC : Levi108 K L R N Y ρ μ T) {n : 𝓜} (hn : n ∈ N) {l : 𝓜}
    (hl : l ∈ L) : n * l * n⁻¹ ∈ L := by
  obtain ⟨u, hu0, hu⟩ := hC.rho_L l hl
  have hlnN : l * n * l⁻¹ ∈ N := mem_N_conj hC (hC.L_le_R hl) hn
  have hmu := mu_conj_of_mem_L hC hl hu0 hu (n := n) hn hlnN
  have hyN : l * n * l⁻¹ * n⁻¹ ∈ N := N.mul_mem hlnN (N.inv_mem hn)
  have hmapy : μ ⟨l * n * l⁻¹ * n⁻¹, hyN⟩ =
      μ ⟨l * n * l⁻¹, hlnN⟩ * (μ ⟨n, hn⟩)⁻¹ := by
    have h1 : (⟨l * n * l⁻¹ * n⁻¹, hyN⟩ : ↥N) =
        ⟨l * n * l⁻¹, hlnN⟩ * ⟨n, hn⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_inv]
  have hycoord : Multiplicative.toAdd (μ ⟨l * n * l⁻¹ * n⁻¹, hyN⟩) 0 = 0 := by
    rw [hmapy, toAdd_mul, toAdd_inv, hmu]
    simp [hu0]
  have hzN : n * (l * n⁻¹ * l⁻¹) ∈ N := by
    exact N.mul_mem hn (mem_N_conj hC (hC.L_le_R hl) (N.inv_mem hn))
  have hz_eq : (⟨n * (l * n⁻¹ * l⁻¹), hzN⟩ : ↥N) =
      (⟨l * n * l⁻¹ * n⁻¹, hyN⟩ : ↥N)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv]
    group
  have hzcoord : Multiplicative.toAdd (μ ⟨n * (l * n⁻¹ * l⁻¹), hzN⟩) 0 = 0 := by
    rw [hz_eq, map_inv, toAdd_inv, Pi.neg_apply, hycoord, neg_zero]
  have hzL : n * (l * n⁻¹ * l⁻¹) ∈ L := (hC.mem_L_iff_mu _ hzN).mpr hzcoord
  have : n * l * n⁻¹ = (n * (l * n⁻¹ * l⁻¹)) * l := by group
  rw [this]
  exact L.mul_mem hzL hl

private lemma N_le_normalizer (hC : Levi108 K L R N Y ρ μ T) : N ≤ NL L := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · exact conj_mem_L hC hn
  · intro h
    have h2 : n⁻¹ * (n * l * n⁻¹) * (n⁻¹)⁻¹ = l := by group
    have := conj_mem_L hC (N.inv_mem hn) h
    rwa [h2] at this

private lemma R_le_normalizer_Y_subgroup (hC : Levi108 K L R N Y ρ μ T) :
    R ≤ Subgroup.normalizer (Y : Set 𝓜) :=
  (Subgroup.le_centralizer_iff.mpr hC.Y_le_centralizer).trans
    (Subgroup.centralizer_le_normalizer (Y : Set 𝓜))

private lemma P_le_N (hC : Levi108 K L R N Y ρ μ T) : Pfrak L R ≤ Nfrak L Y := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr
    ⟨y, Subgroup.subgroupOf_mono (NL L) (R_le_normalizer_Y_subgroup hC) hy, rfl⟩

private lemma isElemAbelian_Yhat_subgroup (hC : Levi108 K L R N Y ρ μ T) :
    IsElemAbelian 2 (Yhat L N) := by
  simpa [Yhat] using (hC.elemAb_N.subgroupOf (NL L)).map (mkG L)

private lemma mem_R_of_mem_P (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NL L)}
    (hg : mkG L g ∈ Pfrak L R) : (g : 𝓜) ∈ R := by
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp hg
  obtain ⟨z, hz, hzr⟩ :=
    (QuotientGroup.mk'_eq_mk' (L.subgroupOf (NL L))).mp hrg
  have hcoe : (r : 𝓜) * (z : 𝓜) = (g : 𝓜) := congrArg Subtype.val hzr
  rw [← hcoe]
  exact R.mul_mem hr (hC.L_le_R hz)

private lemma card_Yhat_eq (hC : Levi108 K L R N Y ρ μ T) [Finite 𝓜] :
    Nat.card (Yhat L N) = Nat.card K := by
  let φ : ↥N →* Multiplicative K :=
    { toFun := fun n => Multiplicative.ofAdd (Multiplicative.toAdd (μ n) 0)
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul, toAdd_mul] }
  have hφker : φ.ker = (L ⊓ N).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h0 : Multiplicative.toAdd (μ n) 0 = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa [φ] using this
      exact ⟨(hC.mem_L_iff_mu n.1 n.2).mpr h0, n.2⟩
    · intro h
      have h0 : Multiplicative.toAdd (μ n) 0 = 0 :=
        (hC.mem_L_iff_mu n.1 n.2).mp h.1
      simp [φ, h0]
  have hφsurj : Function.Surjective φ := by
    intro c
    obtain ⟨n, hn⟩ := hC.surjective_mu (Multiplicative.ofAdd (c.toAdd • e₀ K))
    refine ⟨n, ?_⟩
    simp [φ, hn, e₀]
  let q : ↥N →* GG L := (mkG L).comp (Subgroup.inclusion (N_le_normalizer hC))
  have hqrange : q.range = Yhat L N := by
    change ((mkG L).comp (Subgroup.inclusion (N_le_normalizer hC))).range = Yhat L N
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, Yhat]
  have hqker : q.ker = (L ⊓ N).subgroupOf N := by
    change ((mkG L).comp (Subgroup.inclusion (N_le_normalizer hC))).ker = (L ⊓ N).subgroupOf N
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (((Subgroup.inclusion (N_le_normalizer hC) n : ↥(NL L)) : GG L) = 1) ↔ n.1 ∈ L ⊓ N
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, n.2⟩, fun h => h.1⟩
  have h1 : Nat.card (Yhat L N) = Nat.card (↥N ⧸ q.ker) := by
    rw [← hqrange]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv).symm
  have h2 : Nat.card (↥N ⧸ φ.ker) = Nat.card K := by
    have e := QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
    calc Nat.card (↥N ⧸ φ.ker) = Nat.card (Multiplicative K) :=
        Nat.card_congr e.toEquiv
      _ = Nat.card K := rfl
  calc Nat.card (Yhat L N) = Nat.card (↥N ⧸ q.ker) := h1
    _ = Nat.card (↥N ⧸ φ.ker) := by rw [hqker, hφker]
    _ = Nat.card K := h2

private lemma exists_commutator_coord (hC : Levi108 K L R N Y ρ μ T) {β : K}
    (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) {r : ↥R}
    (hr : (ρ r : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![β, β⁻¹, 1])
    (n0 : ↥N) :
    ∃ (n1 : ↥N) (comm : ↥N), comm.1 = ⁅r.1, n1.1⁆ ∧
      Multiplicative.toAdd (μ comm) 0 = Multiplicative.toAdd (μ n0) 0 := by
  have hden : β⁻¹ - 1 ≠ 0 := by
    intro h
    apply hβ1
    have h1 : β⁻¹ = 1 := sub_eq_zero.mp h
    simpa using congrArg (fun x : K => x⁻¹) h1
  let c : K := Multiplicative.toAdd (μ n0) 0 / (β⁻¹ - 1)
  let v : Fin 3 → K := c • e₀ K
  obtain ⟨n1, hn1⟩ := hC.surjective_mu (Multiplicative.ofAdd v)
  have hn1v : Multiplicative.toAdd (μ n1) = v := by rw [hn1]; simp
  let n' : ↥N := ⟨r.1 * n1.1 * r.1⁻¹, mem_N_conj hC r.2 n1.2⟩
  have hmu := hC.mu_conj r.1 r.2 n1.1 n1.2 n'.1 n'.2 rfl
  have hcoord : Multiplicative.toAdd (μ n') 0 = β⁻¹ * c := by
    have h0 := congrArg (fun w : Fin 3 → K => w 0) hmu
    have hcoe : (((ρ r)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Matrix.diagonal ![β, β⁻¹, 1] : Matrix (Fin 3) (Fin 3) K)⁻¹ := by
      rw [Matrix.GeneralLinearGroup.coe_inv, hr]
    rw [hcoe, diag_inv_transpose_mulVec_zero β hβ0, hn1v] at h0
    simpa [v, e₀] using h0
  let comm : ↥N := ⟨⁅r.1, n1.1⁆, by
    rw [commutatorElement_def]
    exact N.mul_mem n'.2 (N.inv_mem n1.2)⟩
  have hcomm_eq : comm = n' * n1⁻¹ := by
    apply Subtype.ext
    simp only [comm, n', Subgroup.coe_mul, Subgroup.coe_inv]
    rw [commutatorElement_def]
  have hcomm_coord : Multiplicative.toAdd (μ comm) 0 =
      Multiplicative.toAdd (μ n0) 0 := by
    rw [hcomm_eq, map_mul, map_inv, toAdd_mul, toAdd_inv]
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [hcoord, hn1v]
    simp only [v, Pi.smul_apply, e₀, Pi.single_eq_same, smul_eq_mul, mul_one]
    change β⁻¹ * c + -c = Multiplicative.toAdd (μ n0) 0
    have hc : (β⁻¹ - 1) * c = Multiplicative.toAdd (μ n0) 0 := by
      simp only [c, div_eq_mul_inv]
      field_simp
    calc β⁻¹ * c + -c = (β⁻¹ - 1) * c := by ring
      _ = Multiplicative.toAdd (μ n0) 0 := hc
  exact ⟨n1, comm, rfl, hcomm_coord⟩

private lemma exists_commutator_data (hC : Levi108 K L R N Y ρ μ T) {β : K}
    (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) {r : ↥R}
    (hr : (ρ r : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![β, β⁻¹, 1])
    (n0 : ↥N) :
    ∃ (n1 : ↥N) (comm : ↥N) (l : ↥N), comm.1 = ⁅r.1, n1.1⁆ ∧
      (l : 𝓜) ∈ L ∧ comm * l = n0 := by
  obtain ⟨n1, comm, hcomm, hcoord⟩ := exists_commutator_coord hC hβ0 hβ1 hr n0
  let l : ↥N := comm⁻¹ * n0
  have hlL : (l : 𝓜) ∈ L := by
    refine (hC.mem_L_iff_mu l.1 l.2).mpr ?_
    have hzero : Multiplicative.toAdd (μ l) 0 = 0 := by
      rw [show l = comm⁻¹ * n0 from rfl, map_mul, map_inv, toAdd_mul, toAdd_inv]
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [hcoord]
      simp
    simpa using hzero
  refine ⟨n1, comm, l, hcomm, hlL, ?_⟩
  show comm * l = n0
  rw [show l = comm⁻¹ * n0 from rfl]
  group

private lemma Yhat_le_P0frak (hC : Levi108 K L R N Y ρ μ T) :
    Yhat L N ≤ P0frak L R := by
  obtain ⟨β, hβ0, hβ1⟩ :=
    CFSG.RankThree.GF2n.Smith81.D2.exists_ne_zero_ne_one hC.four_le_card
  obtain ⟨r, hr, hrNL⟩ := exists_diag_rho hC hβ0
  intro n hn
  obtain ⟨n0, hn0N, hn0eq⟩ := Subgroup.mem_map.mp hn
  let n0N : ↥N := ⟨n0.1, hn0N⟩
  obtain ⟨n1, comm, l, hcomm_eq, hlL, hcomm_l⟩ :=
    exists_commutator_data hC hβ0 hβ1 hr n0N
  let rP : ↥(Psub L R) := ⟨r.1, Subgroup.mem_inf.mpr ⟨r.2, hrNL⟩⟩
  let n1P : ↥(Psub L R) :=
    ⟨n1.1, Subgroup.mem_inf.mpr ⟨hC.N_le_R n1.2, N_le_normalizer hC n1.2⟩⟩
  let commP : ↥(Psub L R) := ⁅rP, n1P⁆
  have hcommP_mem : commP ∈ ⁅(⊤ : Subgroup ↥(Psub L R)),
      (⊤ : Subgroup ↥(Psub L R))⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hqcomm : qP L R commP ∈ P0frak L R := by
    rw [P0_eq_map_commutator]
    exact Subgroup.mem_map.mpr ⟨commP, hcommP_mem, rfl⟩
  have hcommP_val : commP.1 = comm.1 := by
    simp [commP, rP, n1P, hcomm_eq, commutatorElement_def]
  have hlNL : (l : 𝓜) ∈ NL L := Subgroup.le_normalizer hlL
  have hn0_eq : mkG L n0 = qP L R commP := by
    have hprod : (n0 : ↥(NL L)) = ⟨commP.1, (Subgroup.mem_inf.mp commP.2).2⟩ *
        ⟨l.1, Subgroup.le_normalizer hlL⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hcommP_val]
      have hcoe : (n0 : 𝓜) = (comm : 𝓜) * (l : 𝓜) := by
        simpa [n0N] using (congrArg Subtype.val hcomm_l).symm
      simpa using hcoe
    rw [hprod, map_mul]
    have hl1 : mkG L ⟨l.1, Subgroup.le_normalizer hlL⟩ = 1 := by
      have hmem : (⟨l.1, Subgroup.le_normalizer hlL⟩ : ↥(NL L)) ∈ L.subgroupOf (NL L) := by
        rw [Subgroup.mem_subgroupOf]
        exact hlL
      simpa [mkG] using (QuotientGroup.eq_one_iff
        (⟨l.1, Subgroup.le_normalizer hlL⟩ : ↥(NL L))).mpr hmem
    rw [hl1, mul_one]
    rfl
  rw [← hn0eq, hn0_eq]
  exact hqcomm

private lemma conj_mem_Pfrak_of_normalizes (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NL L)}
    (hgY : (g : 𝓜) ∈ Subgroup.normalizer (Y : Set 𝓜)) {r : ↥(NL L)}
    (hr : (r : 𝓜) ∈ R) :
    mkG L g * mkG L r * (mkG L g)⁻¹ ∈ Pfrak L R := by
  have hgR : (g : 𝓜) ∈ Subgroup.normalizer (R : Set 𝓜) := hC.normalizer_Y_le hgY
  have hconjR : (g : 𝓜) * (r : 𝓜) * (g : 𝓜)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hgR (r : 𝓜)).mp hr
  have hconjNL : (g : 𝓜) * (r : 𝓜) * (g : 𝓜)⁻¹ ∈ NL L :=
    (NL L).mul_mem ((NL L).mul_mem g.2 r.2) ((NL L).inv_mem g.2)
  change mkG L (g * r * g⁻¹) ∈ Pfrak L R
  exact Subgroup.mem_map.mpr
    ⟨⟨(g : 𝓜) * (r : 𝓜) * (g : 𝓜)⁻¹, hconjNL⟩, hconjR, rfl⟩

private lemma N_normalizes_P (hC : Levi108 K L R N Y ρ μ T) :
    Nfrak L Y ≤ Subgroup.normalizer (Pfrak L R : Set (GG L)) := by
  intro k hk
  obtain ⟨g, hgY, rfl⟩ := Subgroup.mem_map.mp hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hh
    exact conj_mem_Pfrak_of_normalizes hC hgY hr
  · intro hh
    obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.mp hh
    have hgR : (g : 𝓜) ∈ Subgroup.normalizer (R : Set 𝓜) := hC.normalizer_Y_le hgY
    have hgRinv : (g : 𝓜)⁻¹ ∈ Subgroup.normalizer (R : Set 𝓜) :=
      (Subgroup.normalizer (R : Set 𝓜)).inv_mem hgR
    have hyR : (g : 𝓜)⁻¹ * (y : 𝓜) * (g : 𝓜) ∈ R := by
      simpa using (Subgroup.mem_normalizer_iff.mp hgRinv (y : 𝓜)).mp hy
    have hyNL : (g : 𝓜)⁻¹ * (y : 𝓜) * (g : 𝓜) ∈ NL L :=
      (NL L).mul_mem ((NL L).mul_mem ((NL L).inv_mem g.2) y.2) g.2
    have h1 : h = (mkG L g)⁻¹ * mkG L y * mkG L g := by
      rw [hyh]
      group
    rw [h1]
    change mkG L (g⁻¹ * y * g) ∈ Pfrak L R
    exact Subgroup.mem_map.mpr ⟨⟨_, hyNL⟩, hyR, rfl⟩

private lemma inv_block_properties (A : Matrix (Fin 3) (Fin 3) K)
    (hA1 : A 1 0 = 0) (hA2 : A 2 0 = 0) (hdet : A.det = 1) :
    (A⁻¹) 1 0 = 0 ∧ (A⁻¹) 2 0 = 0 ∧ (A⁻¹) 0 0 = (A 0 0)⁻¹ := by
  have hD : (A.submatrix Fin.succ Fin.succ).det ≠ 0 := by
    have h := Matrix.det_succ_column_zero A
    rw [Fin.sum_univ_three] at h
    simp [hA1, hA2] at h
    intro hzero
    rw [hdet, hzero, mul_zero] at h
    exact one_ne_zero h
  have hmul : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr (by rw [hdet]; exact one_ne_zero))
  have h00 : ((A * A⁻¹) 0 0) = 1 := by rw [hmul]; simp
  have hv : (A.submatrix Fin.succ Fin.succ) *ᵥ (![A⁻¹ 1 0, A⁻¹ 2 0] : Fin 2 → K) = 0 := by
    ext i
    have hi : ((A * A⁻¹) i.succ 0) = 0 := by
      rw [hmul]; fin_cases i <;> simp
    rw [Matrix.mul_apply, Fin.sum_univ_three] at hi
    fin_cases i <;> simpa [Fin.succ_zero_eq_one, hA1, hA2, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using hi
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hD hv
  have hB1 : A⁻¹ 1 0 = 0 := by simpa using congrFun hz 0
  have hB2 : A⁻¹ 2 0 = 0 := by simpa using congrFun hz 1
  rw [Matrix.mul_apply, Fin.sum_univ_three] at h00
  rw [hB1, hB2] at h00
  simp only [mul_zero, add_zero] at h00
  exact ⟨hB1, hB2, eq_inv_of_mul_eq_one_right h00⟩

private lemma inv_transpose_mulVec_zero (A : Matrix (Fin 3) (Fin 3) K)
    (hA1 : A 1 0 = 0) (hA2 : A 2 0 = 0) (hdet : A.det = 1) (h00 : A 0 0 = 1)
    (v : Fin 3 → K) : ((A⁻¹)ᵀ *ᵥ v) 0 = v 0 := by
  obtain ⟨hB1, hB2, hB00⟩ := inv_block_properties A hA1 hA2 hdet
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp [hB1, hB2, hB00, h00]

private lemma commutator_mem_L_of_mem_commutator (hC : Levi108 K L R N Y ρ μ T)
    {p : ↥(Psub L R)} (hp : p ∈ ⁅(⊤ : Subgroup ↥(Psub L R)),
      (⊤ : Subgroup ↥(Psub L R))⁆) {n0 : ↥N} : ⁅p.1, n0.1⁆ ∈ L := by
  have h00 : (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    have hchi := chi_eq_one_of_mem_commutator hC hp
    have := congrArg (fun u : Kˣ => (u : K)) hchi
    simpa [chi] using this
  have hn' : p.1 * n0.1 * p.1⁻¹ ∈ N := mem_N_conj hC p.2.1 n0.2
  have hmu := hC.mu_conj p.1 p.2.1 n0.1 n0.2 (p.1 * n0.1 * p.1⁻¹) hn' rfl
  have h0 : Multiplicative.toAdd (μ ⟨p.1 * n0.1 * p.1⁻¹, hn'⟩) 0 =
      Multiplicative.toAdd (μ n0) 0 := by
    have hA1 : (((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) 1 0 = 0 := by
      simpa [rhoP_apply] using (rhoP_lower hC p).1
    have hA2 : (((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) 2 0 = 0 := by
      simpa [rhoP_apply] using (rhoP_lower hC p).2
    have hdet : (((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)).det = 1 :=
      det_rho_eq_one hC ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
    have h00' : (((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) 0 0 = 1 := by
      simpa [rhoP_apply] using h00
    have h0' := congrArg (fun w : Fin 3 → K => w 0) hmu
    rw [Matrix.GeneralLinearGroup.coe_inv] at h0'
    rw [inv_transpose_mulVec_zero
      (((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) hA1 hA2 hdet h00'] at h0'
    exact h0'
  have hcommN : ⁅p.1, n0.1⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem hn' (N.inv_mem n0.2)
  let commN : ↥N := ⟨⁅p.1, n0.1⁆, hcommN⟩
  have hcomm_coord : Multiplicative.toAdd (μ commN) 0 = 0 := by
    have heq : commN = (⟨p.1 * n0.1 * p.1⁻¹, hn'⟩ : ↥N) * n0⁻¹ := by
      apply Subtype.ext
      simp only [commN, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [commutatorElement_def]
    rw [heq, map_mul, map_inv, toAdd_mul, toAdd_inv]
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [h0]
    simp
  exact (hC.mem_L_iff_mu commN.1 commN.2).mpr hcomm_coord

private lemma Yhat_le_centralizer_P0 (hC : Levi108 K L R N Y ρ μ T) :
    Yhat L N ≤ Subgroup.centralizer (P0frak L R : Set (GG L)) := by
  intro n hn
  obtain ⟨n0, hn0N, rfl⟩ := Subgroup.mem_map.mp hn
  let n0N : ↥N := ⟨n0.1, hn0N⟩
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
  intro h hh
  rw [P0_eq_map_commutator] at hh
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hh
  have hcommL : ⁅p.1, n0N.1⁆ ∈ L :=
    commutator_mem_L_of_mem_commutator hC hp (n0 := n0N)
  change ⁅mkG L ⟨p.1, (Subgroup.mem_inf.mp p.2).2⟩, mkG L n0⁆ = 1
  rw [← map_commutatorElement (mkG L)]
  change mkG L (⟨⁅p.1, n0.1⁆, Subgroup.le_normalizer hcommL⟩ : ↥(NL L)) = 1
  exact (QuotientGroup.eq_one_iff
    (⟨⁅p.1, n0.1⁆, Subgroup.le_normalizer hcommL⟩ : ↥(NL L))).mpr hcommL

private lemma normalizes_commutator_of_normalizes {H : Subgroup (GG L)} {k : GG L}
    (hk : k ∈ Subgroup.normalizer H) :
    k ∈ Subgroup.normalizer ((⁅H, H⁆ : Subgroup (GG L)) : Set (GG L)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hk ⊢
  rw [Subgroup.map_commutator, hk]

private lemma N_normalizes_P0 (hC : Levi108 K L R N Y ρ μ T) :
    Nfrak L Y ≤ Subgroup.normalizer (P0frak L R : Set (GG L)) :=
  fun k hk => normalizes_commutator_of_normalizes (N_normalizes_P hC hk)

private lemma N_normalizes_X (hC : Levi108 K L R N Y ρ μ T) :
    Nfrak L Y ≤ Subgroup.normalizer (Xlevi L R : Set (GG L)) :=
  fun k hk => normalizes_commutator_of_normalizes (N_normalizes_P0 hC hk)

private lemma X_le_N (hC : Levi108 K L R N Y ρ μ T) : Xlevi L R ≤ Nfrak L Y :=
  (Subgroup.commutator_le_self (P0frak L R)).trans
    ((Subgroup.commutator_le_self (Pfrak L R)).trans (P_le_N hC))

private lemma Yhat_le_K (hC : Levi108 K L R N Y ρ μ T) : Yhat L N ≤ Kfrak L R := by
  refine (Yhat_le_centralizer_P0 hC).trans (Subgroup.centralizer_le ?_)
  intro x hx
  exact Subgroup.commutator_le_self _ hx

private lemma rho_00_eq_one_of_mem_P0frak (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hg : (g : 𝓜) ∈ R) (hx : mkG L g ∈ P0frak L R) :
    (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  rw [P0_eq_map_commutator] at hx
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hx
  have hchi : chi hC p = 1 := chi_eq_one_of_mem_commutator hC hp
  let gp : ↥(Psub L R) := ⟨g.1, Subgroup.mem_inf.mpr ⟨hg, g.2⟩⟩
  have hq : mkG L (⟨p.1, (Subgroup.mem_inf.mp p.2).2⟩ : ↥(NL L)) = mkG L g := by
    have hp_eq : (⟨p.1, (Subgroup.mem_inf.mp p.2).2⟩ : ↥(NL L)) =
        Subgroup.inclusion inf_le_right p := Subtype.ext rfl
    rw [hp_eq]
    simpa [qP] using hpx
  obtain ⟨z, hz, hzr⟩ := (QuotientGroup.mk'_eq_mk' (L.subgroupOf (NL L))).mp hq
  let zp : ↥(Psub L R) := ⟨z.1, Subgroup.mem_inf.mpr ⟨hC.L_le_R hz, z.2⟩⟩
  have hgp : p * zp = gp := by
    apply Subtype.ext
    simpa [zp, gp] using congrArg Subtype.val hzr
  have hchi_gp : chi hC gp = 1 := by
    have hzp : chi hC zp = 1 := by
      simpa [zp] using chi_eq_one_of_mem_L hC hz
    rw [← hgp, map_mul, hchi, hzp, mul_one]
  have hval := congrArg (fun u : Kˣ => (u : K)) hchi_gp
  simpa [chi, gp, rhoP_apply] using hval

private lemma upper_unipotent_of_block_one (M : Matrix (Fin 3) (Fin 3) K)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h00 : M 0 0 = 1)
    (hblock : M.submatrix Fin.succ Fin.succ = 1) :
    ∃ u : Fin 3 → K, u 0 = 0 ∧ M = 1 + Matrix.vecMulVec (e₀ K) u := by
  refine ⟨![0, M 0 1, M 0 2], by simp, ?_⟩
  have h11 : M 1 1 = 1 := by
    have := congrFun (congrFun hblock 0) 0
    simpa using this
  have h12 : M 1 2 = 0 := by
    have := congrFun (congrFun hblock 0) 1
    simpa using this
  have h21 : M 2 1 = 0 := by
    have := congrFun (congrFun hblock 1) 0
    simpa using this
  have h22 : M 2 2 = 1 := by
    have := congrFun (congrFun hblock 1) 1
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₀, Matrix.vecMulVec, h00, h10, h20, h11, h12, h21, h22]

private lemma toGL_range_le_commutator_blk (hC : Levi108 K L R N Y ρ μ T) :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range ≤
      ⁅(blk hC).range, (blk hC).range⁆ := by
  have hperf : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))⁆ = ⊤ :=
    CFSG.RankThree.GF2n.Smith81.D2.sl2_commutator_eq_top hC.four_le_card
  have hmap : ⁅(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range,
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range⁆ =
      (⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))⁆).map
        (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K) := by
    rw [Subgroup.map_commutator]
    rw [MonoidHom.range_eq_map]
  calc (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range =
      ⁅(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range,
        (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range⁆ := by
        rw [hmap, hperf, ← MonoidHom.range_eq_map]
    _ ≤ ⁅(blk hC).range, (blk hC).range⁆ :=
      Subgroup.commutator_mono (toGL_range_le_blk_range hC) (toGL_range_le_blk_range hC)

private lemma block_det_eq_one_of_rho_00_eq_one (hC : Levi108 K L R N Y ρ μ T)
    (p : ↥(Psub L R)) (h00 : (rhoP ρ L p : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) :
    ((rhoP ρ L p : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ).det = 1 := by
  have hlow := rhoP_lower hC p
  have hlow1 : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by simpa [rhoP_apply] using hlow.1
  have hlow2 : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by simpa [rhoP_apply] using hlow.2
  have h00' : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by simpa [rhoP_apply] using h00
  have hdet : ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 :=
    det_rho_eq_one hC ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
  have h := Matrix.det_succ_column_zero
    ((ρ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [Fin.sum_univ_three] at h
  simp [hlow1, hlow2] at h
  rw [hdet, h00', one_mul] at h
  exact h.symm

private lemma exists_commutator_preimage (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hg : (g : 𝓜) ∈ R)
    (h00 : (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) :
    ∃ h : ↥(Psub L R), h ∈ ⁅(⊤ : Subgroup ↥(Psub L R)),
      (⊤ : Subgroup ↥(Psub L R))⁆ ∧
      ((rhoP ρ L (h⁻¹ * ⟨g.1, Subgroup.mem_inf.mpr ⟨hg, g.2⟩⟩) :
          Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ = 1 ∧
       (rhoP ρ L (h⁻¹ * ⟨g.1, Subgroup.mem_inf.mpr ⟨hg, g.2⟩⟩) :
          Matrix (Fin 3) (Fin 3) K) 0 0 = 1) := by
  let gp : ↥(Psub L R) := ⟨g.1, Subgroup.mem_inf.mpr ⟨hg, g.2⟩⟩
  have h00p : (rhoP ρ L gp : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simpa [rhoP_apply, gp] using h00
  let A : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨(rhoP ρ L gp : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ,
      block_det_eq_one_of_rho_00_eq_one hC gp h00p⟩
  have hAcomm : (A : GL (Fin 2) K) ∈ ⁅(blk hC).range, (blk hC).range⁆ :=
    toGL_range_le_commutator_blk hC (MonoidHom.mem_range.mpr ⟨A, rfl⟩)
  have hmap : ⁅(blk hC).range, (blk hC).range⁆ =
      ((⁅(⊤ : Subgroup ↥(Psub L R)), (⊤ : Subgroup ↥(Psub L R))⁆).map (blk hC)) := by
    rw [Subgroup.map_commutator, MonoidHom.range_eq_map]
  rw [hmap] at hAcomm
  obtain ⟨h, hh, hhA⟩ := Subgroup.mem_map.mp hAcomm
  have hchi_h : chi hC h = 1 := chi_eq_one_of_mem_commutator hC hh
  have hchi_gp : chi hC gp = 1 := by
    apply Units.ext
    change (rhoP ρ L gp : Matrix (Fin 3) (Fin 3) K) 0 0 = 1
    exact h00p
  have hblk_gp : blk hC gp = (A : GL (Fin 2) K) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((rhoP ρ L gp : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ) i j =
      (A : Matrix (Fin 2) (Fin 2) K) i j
    rfl
  have hblk_x : blk hC (h⁻¹ * gp) = 1 := by
    rw [map_mul, map_inv, hhA, hblk_gp, inv_mul_cancel]
  have hblock : ((rhoP ρ L (h⁻¹ * gp) : Matrix (Fin 3) (Fin 3) K).submatrix
      Fin.succ Fin.succ) = 1 := by
    have := congrArg (fun z : GL (Fin 2) K => (z : Matrix (Fin 2) (Fin 2) K)) hblk_x
    simpa [blk, Matrix.GeneralLinearGroup.mkOfDetNeZero] using this
  have hchi_x : chi hC (h⁻¹ * gp) = 1 := by
    rw [map_mul, map_inv, hchi_h, hchi_gp, inv_one, one_mul]
  have h00x : (rhoP ρ L (h⁻¹ * gp) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hchi_x
    simpa [chi] using this
  exact ⟨h, hh, by simpa [gp] using hblock, by simpa [gp] using h00x⟩

private lemma exists_l_of_upper (hC : Levi108 K L R N Y ρ μ T) {x : ↥(Psub L R)}
    (hblock : ((rhoP ρ L x : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ) = 1)
    (h00x : (rhoP ρ L x : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) :
    ∃ l : 𝓜, l ∈ L ∧ x.1 * l⁻¹ ∈ N := by
  obtain ⟨u, hu0, huM⟩ := upper_unipotent_of_block_one (rhoP ρ L x : Matrix (Fin 3) (Fin 3) K)
    (rhoP_lower hC x).1 (rhoP_lower hC x).2 h00x hblock
  obtain ⟨l, hlL, hlρ⟩ := hC.exists_L u hu0
  refine ⟨l, hlL, ?_⟩
  have hlρ' : ((ρ ⟨l, hC.L_le_R hlL⟩ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (rhoP ρ L x : Matrix (Fin 3) (Fin 3) K) := by
    rw [hlρ, huM]
  have hmem : (⟨x.1 * l⁻¹, R.mul_mem x.2.1 (R.inv_mem (hC.L_le_R hlL))⟩ : ↥R) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    change (ρ (⟨x.1, x.2.1⟩ * ⟨l, hC.L_le_R hlL⟩⁻¹) : GL (Fin 3) K) = 1
    rw [map_mul, map_inv]
    have hxρ : ρ ⟨x.1, x.2.1⟩ = (rhoP ρ L x : GL (Fin 3) K) := rfl
    have hlρG : ρ ⟨l, hC.L_le_R hlL⟩ = (rhoP ρ L x : GL (Fin 3) K) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact congrFun (congrFun hlρ' i) j
    rw [hxρ, hlρG, mul_inv_cancel]
  rw [hC.ker_rho] at hmem
  exact hmem

private lemma mem_P0frak_of_rho_00_eq_one (hC : Levi108 K L R N Y ρ μ T)
    {g : ↥(NL L)} (hg : (g : 𝓜) ∈ R)
    (h00 : (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1) :
    mkG L g ∈ P0frak L R := by
  obtain ⟨h, hh, hblock, h00x⟩ := exists_commutator_preimage hC hg h00
  let gp : ↥(Psub L R) := ⟨g.1, Subgroup.mem_inf.mpr ⟨hg, g.2⟩⟩
  let x : ↥(Psub L R) := h⁻¹ * gp
  have hblock' : ((rhoP ρ L x : Matrix (Fin 3) (Fin 3) K).submatrix Fin.succ Fin.succ) = 1 := by
    simpa [x, gp] using hblock
  have h00x' : (rhoP ρ L x : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simpa [x, gp] using h00x
  obtain ⟨l, hlL, hxlN⟩ := exists_l_of_upper hC hblock' h00x'
  let hNL : ↥(NL L) := ⟨h.1, (Subgroup.mem_inf.mp h.2).2⟩
  let nNL : ↥(NL L) := ⟨x.1 * l⁻¹, N_le_normalizer hC hxlN⟩
  let lNL : ↥(NL L) := ⟨l, Subgroup.le_normalizer hlL⟩
  have hlNL : mkG L lNL = 1 := by
    have hl1 : lNL ∈ L.subgroupOf (NL L) := by
      rw [Subgroup.mem_subgroupOf]
      exact hlL
    simpa [mkG] using (QuotientGroup.eq_one_iff lNL).mpr hl1
  have hprod : g = hNL * nNL * lNL := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hNL, nNL, lNL]
    have hx_val : (x : 𝓜) = h.1⁻¹ * g.1 := by simp [x, gp]
    rw [hx_val]
    group
  have hhP0 : mkG L hNL ∈ P0frak L R := by
    rw [P0_eq_map_commutator]
    exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
  have hnP0 : mkG L nNL ∈ P0frak L R := by
    exact Yhat_le_P0frak hC (Subgroup.mem_map.mpr ⟨nNL, hxlN, rfl⟩)
  rw [hprod, map_mul, map_mul, hlNL, mul_one]
  exact (P0frak L R).mul_mem hhP0 hnP0

theorem Levi108.N_le_NL (hC : Levi108 K L R N Y ρ μ T) : N ≤ NL L :=
  N_le_normalizer hC

theorem Levi108.mu_conj_L (hC : Levi108 K L R N Y ρ μ T) {l : 𝓜} (hl : l ∈ L) {u : Fin 3 → K}
    (hu0 : u 0 = 0)
    (hu : (ρ ⟨l, hC.L_le_R hl⟩ : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.vecMulVec (e₀ K) u)
    {n : 𝓜} (hn : n ∈ N) (hn' : l * n * l⁻¹ ∈ N) :
    Multiplicative.toAdd (μ ⟨l * n * l⁻¹, hn'⟩) =
      Multiplicative.toAdd (μ ⟨n, hn⟩) - Multiplicative.toAdd (μ ⟨n, hn⟩) 0 • u :=
  mu_conj_of_mem_L hC hl hu0 hu hn hn' 

theorem Levi108.mem_R_of_mem_Pfrak (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NL L)}
    (hg : mkG L g ∈ Pfrak L R) : (g : 𝓜) ∈ R :=
  mem_R_of_mem_P hC hg

theorem Levi108.R_le_normalizer_Y (hC : Levi108 K L R N Y ρ μ T) :
    R ≤ Subgroup.normalizer (Y : Set 𝓜) :=
  R_le_normalizer_Y_subgroup hC

theorem Levi108.card_Yhat (hC : Levi108 K L R N Y ρ μ T) [Finite 𝓜] :
    Nat.card (Yhat L N) = Nat.card K :=
  card_Yhat_eq hC

theorem Levi108.isElemAbelian_Yhat (hC : Levi108 K L R N Y ρ μ T) :
    IsElemAbelian 2 (Yhat L N) :=
  isElemAbelian_Yhat_subgroup hC

theorem Levi108.Pfrak_le_Nfrak (hC : Levi108 K L R N Y ρ μ T) : Pfrak L R ≤ Nfrak L Y :=
  P_le_N hC

theorem Levi108.mem_P0frak_iff (hC : Levi108 K L R N Y ρ μ T) [Finite 𝓜] (g : ↥(NL L))
    (hg : (g : 𝓜) ∈ R) :
    mkG L g ∈ P0frak L R ↔ (ρ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
  ⟨rho_00_eq_one_of_mem_P0frak hC hg, mem_P0frak_of_rho_00_eq_one hC hg⟩

theorem Levi108.Yhat_le_centralizer_P0frak (hC : Levi108 K L R N Y ρ μ T) [Finite 𝓜] :
    Yhat L N ≤ Subgroup.centralizer (P0frak L R : Set (GG L)) :=
  Yhat_le_centralizer_P0 hC

theorem Xlevi_le_P0frak (L R : Subgroup 𝓜) : Xlevi L R ≤ P0frak L R :=
  Subgroup.commutator_le_self _

theorem P0frak_le_Pfrak (L R : Subgroup 𝓜) : P0frak L R ≤ Pfrak L R :=
  Subgroup.commutator_le_self _

theorem Levi108.Yhat_le_Kfrak (hC : Levi108 K L R N Y ρ μ T) [Finite 𝓜] :
    Yhat L N ≤ Kfrak L R :=
  Yhat_le_K hC

theorem Levi108.Nfrak_le_normalizer_P0frak (hC : Levi108 K L R N Y ρ μ T) :
    Nfrak L Y ≤ Subgroup.normalizer (P0frak L R : Set (GG L)) :=
  N_normalizes_P0 hC

theorem Levi108.Nfrak_le_normalizer_Xlevi (hC : Levi108 K L R N Y ρ μ T) :
    Nfrak L Y ≤ Subgroup.normalizer (Xlevi L R : Set (GG L)) :=
  N_normalizes_X hC

theorem Levi108.Xlevi_le_Nfrak (hC : Levi108 K L R N Y ρ μ T) : Xlevi L R ≤ Nfrak L Y :=
  X_le_N hC

end LeviFactor

end CFSG.RankThree.GF2n.Stroth80.Sec108
