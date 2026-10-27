module

public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.R3cRankTwo
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.RankThree.SubgroupLists.FieldThreeFamilies
public import CFSG.LieType.Classical.SteinbergBLSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.R3c3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.SectionRank.OddCover

section Scalars

variable {K : Type} [Field K]

theorem pow_eq_one_of_scalar_mem_statedSL {n : ℕ} {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K) : c ^ n = 1 := by
  have h1 := det_of_mem_statedSL h
  have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = (c : K) ^ n := by
    simp [Matrix.GeneralLinearGroup.scalar]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one])

noncomputable def statedProjStatedSLEquiv {n : ℕ} (h : ∀ c : Kˣ, c ^ n = 1 → c = 1) :
    StatedProj (StatedSL n K) ≃* ↥(StatedSL n K) :=
  have hbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    have hc1 : c = 1 := h c (pow_eq_one_of_scalar_mem_statedSL (hc ▸ x.2))
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot

theorem eq_one_of_sq_eq_one_charTwo [CharP K 2] {c : Kˣ} (hc : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hc' : ((c : Kˣ) : K) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have h0 : (((c : Kˣ) : K) - 1) ^ 2 = 0 := by
    linear_combination hc' + (1 - ((c : Kˣ) : K)) * h2
  have : ((c : Kˣ) : K) - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h0
  exact Units.ext (by simpa [sub_eq_zero] using this)

theorem eq_one_of_cube_eq_one_of_not_dvd [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) {c : Kˣ}
    (hc : c ^ 3 = 1) : c = 1 := by
  have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  have hdvd : orderOf c ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard c
  rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ hdvd) h3

end Scalars

theorem two_le_pRank_three_isPSL_three_three {X : Type} [Group X] [Finite X] (h : IsPSL 3 3 1 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have hch : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  obtain ⟨e₁, e₂, g, h, he₁, he₂, he₁₂, he₁1, hg₁, hg₂, hh₁, hh₂⟩ :=
    CFSG.RankThree.SubgroupLists.exists_three_square_psl33 (F := K) h3
  have hnot : ∀ k : ℤ, e₁ ^ k ≠ e₂ := by
    intro k hk
    have hc : h * e₁ ^ k * h⁻¹ = e₁ ^ k := by
      have := map_zpow (MulAut.conj h) e₁ k
      simp only [MulAut.conj_apply] at this
      rw [this, hh₁]
    rw [hk, hh₂] at hc
    exact he₁1 (mul_eq_left.1 hc)
  have hr := R3c.two_le_pRank_three_of_commuting he₁ he₂ he₁₂ he₁1 hnot
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm)]
  exact hr

theorem two_le_pRank_three_isPSL_three_two_even {n : ℕ} (hn : Even n) {X : Type} [Group X]
    [Finite X] (h : IsPSL 3 2 n X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  obtain ⟨ω, h3, h1⟩ := R3c.exists_cube_root_of_card_two_pow hn hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact R3c.two_le_pRank_three_statedProj_statedSL_three h3 h1

section Monomial

variable {K : Type} [Field K]

private noncomputable def diagOmega (ω : Kˣ) : GL (Fin 3) K :=
  diagHom 3 ![1, ω, ω⁻¹]

private theorem diagOmega_pow_three {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    (diagOmega ω : GL (Fin 3) K) ^ 3 = 1 := by
  rw [diagOmega, ← map_pow, ← map_one (diagHom (K := K) 3)]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using h3
  · simp [inv_pow, h3]

private theorem cyc_conj_diagOmega {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    (cycGL : GL (Fin 3) K) * diagOmega ω * cycGL⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * diagOmega ω := by
  rw [diagOmega, cycGL_conj_diagHom, scalar_eq_diagHom, ← map_mul]
  congr 1
  funext i
  have h2 : ω⁻¹ * ω⁻¹ = ω := by
    have : ω * ω * ω = 1 := by rw [← pow_three']; exact h3
    calc ω⁻¹ * ω⁻¹ = ω⁻¹ * ω⁻¹ * (ω * ω * ω) := by rw [this, mul_one]
      _ = ω := by group
  fin_cases i
  · simp
  · simp
  · simp [h2]

private theorem scalar_mem_center (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem two_le_pRank_three_statedProj_of_monomialData [Finite K] {H : Subgroup (GL (Fin 3) K)}
    {M : Subgroup Kˣ} (hH : MonomialData H M) {ω : Kˣ} (hωM : ω ∈ M) (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) := by
  have hdH : (diagOmega ω : GL (Fin 3) K) ∈ H :=
    hH.diag_mem _ (fun i => by
      fin_cases i
      · simp
      · simpa using hωM
      · simpa using M.inv_mem hωM) (by simp)
  let dH : ↥H := ⟨diagOmega ω, hdH⟩
  let cH : ↥H := ⟨cycGL, hH.cyc_mem⟩
  have hdH3 : dH ^ 3 = 1 := Subtype.ext (diagOmega_pow_three h3)
  have hcH3 : cH ^ 3 = 1 := Subtype.ext cycGL_pow_three
  have hD : ∀ x : ↥H, (QuotientGroup.mk x : StatedProj H) = 1 →
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = (x : GL (Fin 3) K) := by
    intro x hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    exact hx
  refine R3c.two_le_pRank_three_of_commuting (a := (QuotientGroup.mk dH : StatedProj H))
    (b := (QuotientGroup.mk cH : StatedProj H)) ?_ ?_ ?_ ?_ ?_
  · rw [← QuotientGroup.mk_pow, hdH3]
    rfl
  · rw [← QuotientGroup.mk_pow, hcH3]
    rfl
  · show _ * _ = _ * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨ω⁻¹, ?_⟩
    have hconj := cyc_conj_diagOmega (K := K) h3
    have hcd : (cycGL : GL (Fin 3) K) * diagOmega ω =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * diagOmega ω * cycGL := by
      rw [← hconj]
      group
    have hs := Subgroup.mem_center_iff.1 (scalar_mem_center (K := K) ω⁻¹)
      (diagOmega ω * cycGL)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, dH, cH]
    rw [hcd, mul_assoc, ← hs, inv_mul_cancel_left]
  · intro h
    obtain ⟨c, hc⟩ := hD dH h
    have hc' : diagHom 3 (fun _ => c) = diagHom (K := K) 3 ![1, ω, ω⁻¹] := by
      rw [← scalar_eq_diagHom]
      exact hc
    have := diagHom_injective 3 hc'
    have h0 := congrFun this 0
    have h1' := congrFun this 1
    simp at h0 h1'
    exact h1 (h1'.symm.trans h0)
  · intro k hk
    have hk' : (QuotientGroup.mk (dH ^ k) : StatedProj H) = QuotientGroup.mk cH := by
      rw [QuotientGroup.mk_zpow]
      exact hk
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hk'
    obtain ⟨c, hc⟩ := hk'
    have hdiag : (cycGL : GL (Fin 3) K) = diagHom 3 (![1, ω, ω⁻¹] ^ k * fun _ => c) := by
      rw [map_mul, ← scalar_eq_diagHom, map_zpow, hc]
      simp [dH, cH, diagOmega]
    generalize ![1, ω, ω⁻¹] ^ k * (fun _ => c) = w at hdiag
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hdiag) 1) 0
    rw [coe_cycGL, coe_diagHom] at this
    simp [cycMat] at this

end Monomial

theorem two_le_pRank_three_isPSU_two_odd {n : ℕ} (hn : Odd n) {X : Type} [Group X] [Finite X]
    (h : IsPSU 3 2 n X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hch : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω, h3, h1⟩ := R3c.exists_cube_root_of_card_two_pow (n := 2 * n) ⟨n, by ring⟩ hK2
  have hdvd : 3 ∣ 2 ^ n + 1 := by
    have := R3c.two_pow_mod_three_of_odd hn
    omega
  have hωM : ω ∈ normOne K (2 ^ n) := by
    rw [mem_normOne]
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, h3, one_pow]
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact two_le_pRank_three_statedProj_of_monomialData
    (monomialData_statedSU (K := K) (p := 2) (f := n)) hωM h3 h1

theorem isPGroup_two_scalarKernel_statedSp {K : Type} [Field K] (n : ℕ) (hn : 1 ≤ n) :
    IsPGroup 2 ↥((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨⟨A, hA⟩, hg⟩ := g
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c = A := hc
  have hc2 : c ^ 2 = 1 := (CFSG.LieType.Classical.scalar_mem_statedSp_iff hn c).1 (hc' ▸ hA)
  apply Subtype.ext
  apply Subtype.ext
  change A ^ (2 ^ 1) = 1
  rw [← hc', pow_one, ← map_pow, hc2, map_one]

theorem two_le_pRank_three_statedProj_statedSp_two {K : Type} [Field K] [Finite K] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_quotient_eq _
    (R3c.not_three_dvd_card_of_isPGroup_two (isPGroup_two_scalarKernel_statedSp 2 (by norm_num)))]
  exact FFC.threeRank2_statedSp.pRank_two_le

theorem two_le_pRank_three_isPSp_two {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .PSp 2 2 n) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact two_le_pRank_three_statedProj_statedSp_two

theorem two_le_pRank_three_isPSL_two_one {n : ℕ} (hn : n = 4 ∨ n = 5) {X : Type} [Group X] [Finite X]
    (h : IsPSL n 2 1 X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let φ : X ≃* GL (Fin n) (ZMod 2) :=
    (e.trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hK2 n)).trans
      (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK2 n)
  let ψ : GL (Fin n) (ZMod 2) ≃* ↥(StatedSL n (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
      (CFSG.GH74.Exceptional.statedSL_eq_top_of_card_two (Nat.card_zmod 2) n).symm)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) (φ.trans ψ)]
  rcases hn with rfl | rfl
  · exact R3c.two_le_pRank_three_statedSL_four_two
  · exact R3c.two_le_pRank_three_statedSL_five_two

theorem two_le_pRank_three_alt {n : ℕ} (hn : 6 ≤ n) {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin n)) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact (FFC.threeRank2_alt hn).pRank_two_le

end CFSG.Quasithin.R3c3
