module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNC
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag4
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQCat.SL3Sect

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

section TwoByTwo

variable {K : Type} [Field K] [CharP K 2]

theorem sq_eq_one_of_pow_two_pow {M : Matrix (Fin 2) (Fin 2) K} {s : ℕ} (h : M ^ 2 ^ s = 1) :
    M ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, rfl⟩ : ∃ N : Matrix (Fin 2) (Fin 2) K, M = N + 1 :=
    ⟨M + 1, by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩
  have hN0 : N ^ 2 ^ s = 0 := by
    have h1 := add_pow_char_pow_of_commute 2 s (Commute.one_right N)
    rw [h, one_pow] at h1
    have h2 : N ^ 2 ^ s = 1 - 1 := eq_sub_of_add_eq h1.symm
    rwa [sub_self] at h2
  have hCH : N * N = N.trace • N - N.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
  have hdet : N.det = 0 := by
    have := congrArg Matrix.det hN0
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff (by positivity) |>.1 this
  rw [hdet, zero_smul, sub_zero] at hCH
  have hpow : ∀ k : ℕ, N ^ (k + 1) = N.trace ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_assoc, hCH, smul_smul, pow_succ]
  have hN2 : N * N = 0 := by
    by_cases ht : N.trace = 0
    · rw [hCH, ht, zero_smul]
    · have h1 := hpow (2 ^ s - 1)
      rw [Nat.sub_add_cancel Nat.one_le_two_pow, hN0] at h1
      have hN' : N = 0 := (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ ht)
      rw [hN', mul_zero]
  have e : (N + 1) ^ 2 = N * N + (N + N) + 1 := by
    rw [sq]
    noncomm_ring
  rw [e, hN2, CharTwo.add_self_eq_zero, zero_add, zero_add]

end TwoByTwo

section Small

theorem false_of_normal {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hN2 : IsPGroup 2 N) {g σ : G} (hσ : σ * σ = 1) (hx3 : (g ^ 2 * (σ * g ^ 2 * σ)) ^ 3 = 1)
    (hx1 : g ^ 2 * (σ * g ^ 2 * σ) ≠ 1) (hg : g ^ 2 ∈ N) : False := by
  have hσ' : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hc : σ * g ^ 2 * σ ∈ N := by
    have := hN.conj_mem _ hg σ
    rwa [hσ'] at this
  obtain ⟨k, hk⟩ := hN2 ⟨_, N.mul_mem hg hc⟩
  have hk' : (g ^ 2 * (σ * g ^ 2 * σ)) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hgcd := (pow_gcd_eq_one).2 ⟨hx3, hk'⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at hgcd
  exact hx1 hgcd

@[expose] def g3 : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def s3 : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩

@[expose] def g4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

@[expose] def s4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1], by decide⟩

theorem g3_data : g3 ^ 4 = 1 ∧ s3 * s3 = 1 ∧ (g3 ^ 2 * (s3 * g3 ^ 2 * s3)) ^ 3 = 1 ∧
    g3 ^ 2 * (s3 * g3 ^ 2 * s3) ≠ 1 := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, fun h => ?_⟩
  · decide
  · decide
  · decide
  · have := congrArg Subtype.val h
    revert this
    decide

theorem g4_data : g4 ^ 4 = 1 ∧ s4 * s4 = 1 ∧ (g4 ^ 2 * (s4 * g4 ^ 2 * s4)) ^ 3 = 1 ∧
    g4 ^ 2 * (s4 * g4 ^ 2 * s4) ≠ 1 := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, fun h => ?_⟩
  · decide
  · decide
  · decide
  · have := congrArg Subtype.val h
    revert this
    decide

theorem exists_data {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∃ g σ : SpecialLinearGroup (Fin m) (ZMod 2), g ^ 4 = 1 ∧ σ * σ = 1 ∧
      (g ^ 2 * (σ * g ^ 2 * σ)) ^ 3 = 1 ∧ g ^ 2 * (σ * g ^ 2 * σ) ≠ 1 := by
  rcases hm with rfl | rfl
  · exact ⟨g3, s3, g3_data⟩
  · exact ⟨g4, s4, g4_data⟩

end Small

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem core (j : Fin 2) {D : Subgroup (SpecialLinearGroup (Fin 3) K)} (hDQ : D ≤ Q3 K j)
    {m : ℕ} (hm : m = 3 ∨ m = 4) (π : ↥D →* SpecialLinearGroup (Fin m) (ZMod 2))
    (hπ : Function.Surjective π) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, σ, hg4, hσ, hx3, hx1⟩ := exists_data hm
  let ℓ : ↥D →* Matrix (Fin 2) (Fin 2) K :=
    (blkMon (Q3 K j) (1 - (j : ℕ)) 2 (q3_blk_le j) (q3_blockLeft j) (q3_blockRight j)).comp
      (Subgroup.inclusion hDQ)
  have hR2 : IsPGroup 2 ℓ.ker := by
    intro r
    have hr : (r : ↥D) ∈ ℓ.ker := r.2
    have hu : ((r : ↥D) : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
      refine blk3_ker_aux j _ (hDQ (r : ↥D).2) fun i k => ?_
      have h1 : ℓ r = 1 := hr
      exact congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i k) h1
    obtain ⟨n, hn⟩ := isPGroup_unitriangular_charTwo (K := K) (n := 3) (by norm_num) ⟨_, hu⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hN : (ℓ.ker.map π).Normal := (MonoidHom.normal_ker ℓ).map π hπ
  have hN2 : IsPGroup 2 (ℓ.ker.map π) := hR2.map π
  obtain ⟨a₀, ha₀⟩ := hπ g
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a₀).ne'
  have ha2 : (a₀ ^ t) ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hst, pow_orderOf_eq_one]
  have hπa : π ((a₀ ^ t) ^ 2) = g ^ 2 := by
    obtain ⟨u, rfl⟩ := ht
    rw [map_pow, map_pow, ha₀, ← pow_mul, show (2 * u + 1) * 2 = 4 * u + 2 by ring, pow_add,
      pow_mul, hg4, one_pow, one_mul]
  have hℓa : ℓ ((a₀ ^ t) ^ 2) = 1 := by
    rw [map_pow]
    refine sq_eq_one_of_pow_two_pow (s := s) ?_
    rw [← map_pow, ha2, map_one]
  exact false_of_normal hN hN2 hσ hx3 hx1 ⟨_, hℓa, hπa⟩

end Core

section Main

theorem charP_two_of_card {F : Type} [Field F] [Fintype F] {k : ℕ}
    (hF : Fintype.card F = 2 ^ k) : CharP F 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hn0 : (n : ℕ) ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn
    have := Fintype.one_lt_card (α := F)
    omega
  have h2 : ringChar F = 2 := by
    have h1 : ringChar F ∣ 2 ^ k := by
      rw [← hF, hn]
      exact dvd_pow_self _ hn0
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
  rw [← h2]
  exact ringChar.charP F

theorem lem1211NNSL3_holds : Lem1211NNSL3 := by
  intro Y _ _ X P D F _ _ k m _ hF hX hP hDP hm π hπ _
  have : CharP F 2 := charP_two_of_card hF
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨k, by rw [Nat.card_eq_fintype_card, hF]⟩
  obtain ⟨e₀⟩ := hX
  let e : ↥X ≃* SpecialLinearGroup (Fin 3) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  obtain ⟨⟨hPX, S, hS, hSP⟩, hPne, -⟩ := hP
  set P' := (P.subgroupOf X).map e.toMonoidHom with hP'
  set S' := (S.subgroupOf X).map e.toMonoidHom with hS'
  have hS'syl : IsSylowTwoOf S' ⊤ := by
    have hU := Setup.X6.isSylowTwoOf_subgroupOf_top hS
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    have h1 := hU.2.2
    rw [show ((S.subgroupOf X).subgroupOf ⊤).index = (S.subgroupOf X).index from
      Subgroup.relIndex_top_right _] at h1
    rw [show (S'.subgroupOf ⊤).index = S'.index from Subgroup.relIndex_top_right _, hS',
      MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact h1
  have hSP' : S' ≤ P' := Subgroup.map_mono fun x hx =>
    hSP ⟨x.2, Subgroup.le_normalizer hx⟩
  have hP'top : P' ≠ ⊤ := by
    intro h
    apply hPne
    refine le_antisymm hPX fun x hx => ?_
    have h1 : e ⟨x, hx⟩ ∈ P' := h ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hx⟩ := e.injective hyx
    rw [this] at hy
    exact hy
  obtain ⟨φ, -, hres⟩ := (SzN2.sl3_residualOvergroupsAt hK).exists_iso_of_isSylow
    (MulEquiv.refl _) (SzN2.isSylowTwoOf_unitriangular (by norm_num)) hS'syl
  obtain ⟨A, hA, hPA⟩ := (eq_top_or_exists_le_coatom P').resolve_left hP'top
  obtain ⟨j, rfl⟩ := (hres.2.2.1 A (hSP'.trans hPA)).1 hA.covBy_top
  have hDX : D ≤ X := hDP.trans hPX
  let D'' : Subgroup (SpecialLinearGroup (Fin 3) F) :=
    ((D.subgroupOf X).map e.toMonoidHom).map φ.toMonoidHom
  have hDQ : D'' ≤ Q3 F j := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h1 : e x ∈ (Q3 F j).map φ.symm.toMonoidHom :=
      hPA ⟨x, (show (x : Y) ∈ P from hDP hx), rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : φ (e x) = y := by
      rw [← hyx]
      simp
    change φ (e x) ∈ Q3 F j
    rw [this]
    exact hy
  let ψ : ↥D ≃* ↥D'' :=
    (((Subgroup.subgroupOfEquivOfLe hDX).symm.trans
      ((D.subgroupOf X).equivMapOfInjective e.toMonoidHom e.injective)).trans
      (((D.subgroupOf X).map e.toMonoidHom).equivMapOfInjective φ.toMonoidHom φ.injective))
  exact core j hDQ hm (π.comp ψ.symm.toMonoidHom) (hπ.comp ψ.symm.surjective)

end Main

end CFSG.Quasithin.H13.NQCat.SL3Sect
