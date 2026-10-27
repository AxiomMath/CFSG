module

public import CFSG.RankThree.PartOne.K133.ProjUnip3
public import CFSG.RankThree.PartOne.K133.InnerRed
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.RankThree.PartOne.CTP.SeitzToral
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree.GroupTheory CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem statedProj_card_le_sq_of_sl3 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) (hp3 : p ≠ 3) (M : Subgroup (GL (Fin 3) K)) (hM : M ≤ StatedSL 3 K)
    (A : Subgroup (StatedProj M)) (hA : IsElementaryAbelian p A) : Nat.card A ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup M := (StatedScalars (Fin 3) K).subgroupOf M with hZ
  let π : M →* StatedProj M := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hdet : ∀ g ∈ M, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro g hg
    have h1 : g ∈ StatedSL 3 K := hM hg
    rw [LIT.statedSL_eq_det_ker] at h1
    have := MonoidHom.mem_ker.1 h1
    have h2 := congrArg (fun u : Kˣ => (u : K)) this
    simpa using h2
  have hker : ¬ p ∣ Nat.card π.ker := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzK : (z : M) ∈ Z := by
      have h1 : π (z : M) = 1 := MonoidHom.mem_ker.1 z.2
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = ((z : M) : GL (Fin 3) K) :=
      hzK
    have hc3 : (c : K) ^ 3 = 1 := by
      have h1 := hdet (z : M) (z : M).2
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one', Matrix.det_smul,
        Matrix.det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have hz3 : (z : M) ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
      have : (Matrix.scalar (Fin 3) (c : K)) ^ 3 = Matrix.scalar (Fin 3) ((c : K) ^ 3) := by
        rw [map_pow]
      rw [this, hc3, map_one]
      rfl
    have hzo : orderOf (z : M) = p := by rw [Subgroup.orderOf_coe, hz]
    have : p ∣ 3 := hzo ▸ orderOf_dvd_of_pow_eq_one hz3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
  obtain ⟨E', hE'map, hE'dis⟩ := CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hker A
    (IsElementaryAbelian.isPGroup p A)
  have hE'mem : ∀ x ∈ E', π x ∈ A := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have hcm : π a * π b = π b * π a :=
        congrArg Subtype.val (hA.is_comm.comm ⟨π a, hE'mem a ha⟩ ⟨π b, hE'mem b hb⟩)
      rw [hcm]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (π a) (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  have hEle : Nat.card (E'.map M.subtype) ≤ p ^ 2 := by
    refine LIT.card_le_sq_of_det_gl hp hpK (by simp) (E'.map M.subtype) ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hE'comm a ha b hb
      simpa using congrArg M.subtype this
    · rintro _ ⟨a, ha, rfl⟩
      have := hE'exp a ha
      rw [← map_pow, this, map_one]
    · rintro _ ⟨a, ha, rfl⟩
      exact hdet a a.2
  rw [Subgroup.card_map_of_injective M.subtype_injective] at hEle
  have hsurj : Function.Surjective (fun x : E' => (⟨π x, hE'mem x x.2⟩ : A)) := by
    intro a
    have : (a : StatedProj M) ∈ E'.map π := hE'map ▸ a.2
    obtain ⟨x, hx, hxa⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hEle

theorem goodRes_statedProj_three {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (M : Subgroup (GL (Fin 3) K)) (hM : M ≤ StatedSL 3 K) [IsSimpleGroup (StatedProj M)]
    (hne : ∃ a b : StatedProj M, a * b ≠ b * a)
    (hOut : ¬ p ∣ Nat.card (Outer (StatedProj M))) : GoodRes p (StatedProj M) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center (StatedProj M) = ⊥ := center_eq_bot_of_simple_nonabelian hne
  have hin : ∀ E : Subgroup (MulAut (StatedProj M)), IsPGroup p E → E ≤ inner (StatedProj M) :=
    fun E hE => le_inner_of_isPGroup_of_not_dvd_outer hp hOut hE
  by_cases hpK : (p : K) = 0
  ·
    have hcharp : CharP K p := (CharP.charP_iff_prime_eq_zero hp).2 hpK
    refine goodRes_of_inner_noConfig hp hZ hin ?_
    intro C hC hCc Kb hKs hKn hpKb hcomm
    have : Nontrivial C := by
      have : Finite C := inferInstance
      apply Finite.one_lt_card_iff_nontrivial.1
      rw [hCc]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    obtain ⟨x, hx1⟩ := exists_ne (1 : C)
    refine statedProj_three_no_config (K := K) (p := p) (by omega) M (x : StatedProj M) ?_ ?_ Kb hKn
      (fun k hk => hcomm x x.2 k hk)
    · intro h
      exact hx1 (Subtype.ext h)
    · have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := C) (x : StatedProj M) x.2
      exact this
  ·
    have hno : NoRankThree p (StatedProj M) := by
      refine noRankThree_of_inner_rank hp hZ hin ?_
      intro A hA hcard
      have hle := statedProj_card_le_sq_of_sl3 hp hpK (by omega) M hM A hA
      rw [hcard] at hle
      have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    exact hno.dead.good.goodRes

end CFSG.RankThree.PartOne.K133
