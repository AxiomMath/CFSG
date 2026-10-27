module

public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.RankThree.PartOne.KC.LinearThreeFourInnerDefining

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut SemiGL)
open CFSG.RankThree.RegularUnipotent (conj_injective_projectiveSL)

variable {n : ℕ} {K : Type} [Field K]

theorem not_dvd_card_ker_proj {p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1) [Finite K] :
    ¬ p ∣ Nat.card (proj n K).ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzs : (z : SpecialLinearGroup (Fin n) K) ∈ scalars n K := proj_eq_one_iff.mp z.2
  obtain ⟨c, hcn, hzc⟩ := hzs
  have hzp : (z : SpecialLinearGroup (Fin n) K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg Subtype.val this
  have hcp : c ^ p = 1 := by
    have h1 : (((z : SpecialLinearGroup (Fin n) K) ^ p : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hzp]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow] at h1
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0, hn⟩ ⟨0, hn⟩) h1
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hc1 : c = 1 := hZp c hcp hcn
  have hz1 : (z : SpecialLinearGroup (Fin n) K) = 1 := by
    apply Subtype.ext
    rw [hzc, hc1, Units.val_one, map_one]
    rfl
  have hz1' : z = 1 := Subtype.ext hz1
  rw [hz1', orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem exists_special_lift [Finite K] {p : ℕ} (hp : p.Prime) (hn : 3 ≤ n)
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1) {t : MulAut (projectiveSL n K)}
    (ht : t ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (htp : orderOf t = p) :
    ∃ x : SpecialLinearGroup (Fin n) K, orderOf x = p ∧ MulAut.conj (proj n K x) = t := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, rfl⟩ := ht
  have hinj := conj_injective_projectiveSL (k := K) hn
  have hy : y ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact htp ▸ pow_orderOf_eq_one _
  obtain ⟨x, hxy, hxp⟩ := exists_lift_pow_eq_one (proj n K) hp
    (not_dvd_card_ker_proj hp (by omega) hZp) (MonoidHom.mem_range.mpr (proj_surjective n K y)) hy
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at htp
    exact hp.one_lt.ne htp
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hy1 (by rw [← hxy, map_one])
  exact ⟨x, orderOf_eq_prime hxp hx1, by rw [hxy]⟩

theorem centralizer_conjAut_eq_map [Finite K] {p : ℕ} (hn : 3 ≤ n)
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1) {a : GL (Fin n) K} (hap : a ^ p = 1)
    (hdet : (a : Matrix (Fin n) (Fin n) K).det = 1) :
    (conjAut n K).range ⊓ Subgroup.centralizer ({conjAut n K a} : Set (MulAut (projectiveSL n K))) =
      (Subgroup.centralizer ({a} : Set (GL (Fin n) K))).map (conjAut n K) := by
  ext y
  constructor
  · rintro ⟨⟨Y, rfl⟩, hy⟩
    refine ⟨Y, ?_, rfl⟩
    have hy' : conjAut n K Y ∈ Subgroup.centralizer ({conjAut n K a} :
        Set (MulAut (projectiveSL n K))) := hy
    have hcomm : conjAut n K Y * conjAut n K a = conjAut n K a * conjAut n K Y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy'
    have hg : semilinPsi n K ⟨Y, 1⟩ * conjAut n K a * (semilinPsi n K ⟨Y, 1⟩)⁻¹ =
        conjAut n K a := by
      rw [semilinPsi_mk, map_one, mul_one, hcomm, mul_inv_cancel_right]
    have h := semilin_conj_eq_self hn hZp hap hdet ⟨Y, 1⟩ hg
    change Y * glAut 1 a * Y⁻¹ = a at h
    rw [map_one, MulAut.one_apply] at h
    show Y ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp h
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨⟨Y, rfl⟩, ?_⟩
    have hY' : Y ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := hY
    show conjAut n K Y ∈ Subgroup.centralizer ({conjAut n K a} :
      Set (MulAut (projectiveSL n K)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hY']

end CFSG.RankThree.PartOne.KCLinComm
