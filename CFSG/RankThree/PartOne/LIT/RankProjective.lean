module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix Module CFSG.Assembly.RankThreeEven

universe u v

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]

instance instFiniteProjGenLinGroup [Finite K] : Finite (ProjGenLinGroup ι K) :=
  inferInstanceAs (Finite (GL ι K ⧸ Subgroup.center (GL ι K)))

@[expose] noncomputable def projEquiv (H : Subgroup (GL ι K)) :
    (H ⧸ (Subgroup.center (GL ι K)).subgroupOf H) ≃* projImage H := by
  let φ : H →* ProjGenLinGroup ι K := (ProjGenLinGroup.mk : GL ι K →* _).comp H.subtype
  have hker : φ.ker = (Subgroup.center (GL ι K)).subgroupOf H := by
    ext h
    simp [φ, MonoidHom.mem_ker, ProjGenLinGroup.mk_eq_one, Subgroup.mem_subgroupOf]
  have hrange : φ.range = projImage H := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))

theorem pRank_projImage_eq [Finite K] {r : ℕ} [Fact r.Prime] (H : Subgroup (GL ι K))
    (hN : ¬ r ∣ Nat.card ((Subgroup.center (GL ι K)).subgroupOf H)) :
    CFSG.Open.pRank r (⊤ : Subgroup (projImage H)) = CFSG.Open.pRank r (⊤ : Subgroup H) :=
  (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : r.Prime).one_lt (projEquiv H).symm).trans
    (CFSG.SectionRank.pRank_quotient_eq _ hN)

theorem not_dvd_card_scalars {m r : ℕ} (hr : r.Prime) (hrm : ¬ r ∣ m) [Finite K]
    (H : Subgroup (GL ι K))
    (h : ∀ g ∈ H, g ∈ Subgroup.center (GL ι K) → g ^ m = 1) :
    ¬ r ∣ Nat.card ((Subgroup.center (GL ι K)).subgroupOf H) := by
  intro hdvd
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hxm : x ^ m = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have := h x.1.1 x.1.2 (Subgroup.mem_subgroupOf.mp x.2)
    exact this
  exact hrm (hx ▸ orderOf_dvd_of_pow_eq_one hxm)

theorem pow_card_eq_one_of_det (g : GL ι K) (hg : g ∈ Subgroup.center (GL ι K))
    (hdet : (g : Matrix ι ι K).det = 1) : g ^ Fintype.card ι = 1 := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, rfl⟩ := hg
  have hc : (c : K) ^ Fintype.card ι = 1 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  rw [← map_pow]
  have : c ^ Fintype.card ι = 1 := Units.ext (by simpa using hc)
  rw [this, map_one]

theorem sq_eq_one_of_form (J : Matrix ι ι K) (hJ : J.det ≠ 0) [Nonempty ι] (g : GL ι K)
    (hg : g ∈ Subgroup.center (GL ι K))
    (hpres : (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J) : g ^ 2 = 1 := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, rfl⟩ := hg
  have hJne : ∃ i j, J i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hJ
    have : J = 0 := by ext i j; exact hcon i j
    rw [this, Matrix.det_zero]
  obtain ⟨i, j, hij⟩ := hJne
  have h1 := congrFun (congrFun hpres i) j
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal] at h1
  have hcc : (c : K) * c = 1 := by
    have : ((c : K) * c - 1) * J i j = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hij
  rw [← map_pow]
  have : c ^ 2 = 1 := Units.ext (by simpa [sq] using hcc)
  rw [this, map_one]

theorem not_dvd_two {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 2 := fun h =>
  hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)

theorem pRank_projSL_two_le [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : (r : K) ≠ 0) :
    CFSG.Open.pRank r (⊤ : Subgroup (projSL 2 K)) ≤ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  let H : Subgroup (GL (Fin 2) K) := (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker
  have hH : ∀ h ∈ H, (h : Matrix (Fin 2) (Fin 2) K).det = 1 := fun h hh => by
    have := MonoidHom.mem_ker.mp hh
    simpa [Units.ext_iff] using this
  have hN : ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin 2) K)).subgroupOf H) :=
    not_dvd_card_scalars (m := Fintype.card (Fin 2)) hr (by simpa using not_dvd_two hr hr2) H
      fun g hg hc => pow_card_eq_one_of_det g hc (hH g hg)
  have h1 : CFSG.Open.pRank r (⊤ : Subgroup (projImage H)) =
      CFSG.Open.pRank r (⊤ : Subgroup H) := pRank_projImage_eq H hN
  have h2 := pRank_le_card_gl hr hrK H
  have h3 : CFSG.Open.pRank r (⊤ : Subgroup (projSL 2 K)) ≤ Fintype.card (Fin 2) := by
    show CFSG.Open.pRank r (⊤ : Subgroup (projImage H)) ≤ _
    rw [h1]
    exact h2
  simpa using h3

theorem sympForm_alt (n : ℕ) (v : Fin n ⊕ Fin n → K) : v ⬝ᵥ (sympForm n K *ᵥ v) = 0 := by
  simp only [sympForm, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  simp [Matrix.neg_mulVec, mul_comm]

theorem sympForm_det (n : ℕ) : (sympForm n K).det ≠ 0 := by
  have h : sympForm n K * (-sympForm n K) = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [sympForm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact left_ne_zero_of_mul_eq_one this

theorem pRank_projSp_two_le [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : (r : K) ≠ 0) :
    CFSG.Open.pRank r (⊤ : Subgroup (projSp 2 K)) ≤ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  let S : Set (GL (Fin 2 ⊕ Fin 2) K) := {A | (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      sympForm 2 K * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sympForm 2 K}
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := Subgroup.closure S
  have hH : ∀ h ∈ H, (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * sympForm 2 K *
      (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sympForm 2 K :=
    mem_closure_form fun g hg => hg
  have hN : ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin 2 ⊕ Fin 2) K)).subgroupOf H) :=
    not_dvd_card_scalars (m := 2) hr (not_dvd_two hr hr2) H
      fun g hg hc => sq_eq_one_of_form (sympForm 2 K) (sympForm_det 2) g hc (hH g hg)
  have h1 : CFSG.Open.pRank r (⊤ : Subgroup (projImage H)) =
      CFSG.Open.pRank r (⊤ : Subgroup H) := pRank_projImage_eq H hN
  have h2 := pRank_le_half_of_form_gl hr hrK (sympForm 2 K) (sympForm_det 2) (sympForm_alt 2) H hH
  have h3 : CFSG.Open.pRank r (⊤ : Subgroup (projSp 2 K)) ≤
      Fintype.card (Fin 2 ⊕ Fin 2) / 2 := by
    show CFSG.Open.pRank r (⊤ : Subgroup (projImage H)) ≤ _
    rw [h1]
    exact h2
  simpa using h3

theorem projSU_le_projSL (n p f : ℕ) [Fact p.Prime] :
    projSU n p f ≤ projSL n (GaloisField p (2 * f)) := by
  apply Subgroup.map_mono
  rw [Subgroup.closure_le]
  intro A hA
  exact MonoidHom.mem_ker.mpr hA.1

theorem pRank_projSU_le_projSL (n p f : ℕ) [Fact p.Prime] {r : ℕ} (hr : 1 < r) :
    CFSG.Open.pRank r (⊤ : Subgroup (projSU n p f)) ≤
      CFSG.Open.pRank r (⊤ : Subgroup (projSL n (GaloisField p (2 * f)))) :=
  CFSG.SectionRank.pRank_top_le_of_injective hr (Subgroup.inclusion (projSU_le_projSL n p f))
    (Subgroup.inclusion_injective _)

end CFSG.RankThree.PartOne.LIT
