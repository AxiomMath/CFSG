module

public import CFSG.RankThree.PartOne.S11d.PSpGood
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut fieldSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem exists_fieldAut_model_PSp {T : Type} [Group T] [Finite T] {p f₀ r : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .PSp r 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    2 ≤ r ∧ ∃ (K : Type) (_ : Field K), Finite K ∧ Nat.card K = 2 ^ (p * f₀) ∧
      ∃ (φ : T ≃* StatedProj (StatedSp r K)) (σ : K ≃+* K), orderOf σ = p ∧
        MulAut.congr φ α = fieldAut r K σ := by
  have hC : StatedClassicalModel T .PSp r 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ r := hC.1.2.2.1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp r K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p :=
    orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ (innerAut _).one_mem))
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup r K := by
    have hidx' : (spSemilinearAutGroup r K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup r K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ (p * f₀) - 1) = 1 := by
      have h1 : (2 : ℕ) ^ (p * f₀) % 2 = 0 := by
        obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hf
        rw [hg, pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ (p * f₀) := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hα'inn (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨hpf, σ, hσord, -, h, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  have : Finite K := inferInstance
  refine ⟨hn, K, inferInstance, inferInstance, hK,
    e.trans (h⁻¹ : MulAut (StatedProj (StatedSp r K))), σ, hσord, ?_⟩
  have : MulAut.congr (e.trans (h⁻¹ : MulAut (StatedProj (StatedSp r K)))) α =
      h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ := rfl
  rw [this, hαh]
  group


theorem lieGoodComponentFixT_PSp : LieGoodComponentFixT .PSp := by
  intro T _ _ p hp hp5 _ hrank n f₀ hf₀ hM α hαp hαinn _ _ x hxp hx1 hαx y hy2 hy1 hxy
  obtain ⟨hn, K, _, _, hK, φ, σ, hσord, hφα⟩ :=
    exists_fieldAut_model_PSp hp hp5 hM hf₀ α hαp hαinn
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 := charP_two_of_card_eq_pow hK
  have : NeZero n := ⟨by omega⟩
  have hr : 1 ≤ n := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (proj n K) := proj_injective_sp hK hf hr
  let ψ : StatedSp n K ≃* StatedProj (StatedSp n K) :=
    MulEquiv.ofBijective (proj n K)
      ⟨hinj, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩
  let e : T ≃* StatedSp n K := φ.trans ψ.symm
  have hψe : ∀ t, ψ (e t) = φ t := fun t => ψ.apply_symm_apply (φ t)
  have hcongr : MulAut.congr e α = fieldSp n K σ := by
    refine MulEquiv.ext fun g => ?_
    apply ψ.injective
    have h1 : (MulAut.congr φ α) (ψ g) = fieldAut n K σ (ψ g) := by rw [hφα]
    have h2 : fieldAut n K σ (ψ g) = ψ (fieldSp n K σ g) :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj σ g
    have h3 : e.symm g = φ.symm (ψ g) := rfl
    have h4 : ψ ((MulAut.congr e α) g) = (MulAut.congr φ α) (ψ g) := by
      show ψ (e (α (e.symm g))) = φ (α (φ.symm (ψ g)))
      rw [hψe, h3]
    rw [h4, h1, h2]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσord
    exact hp.one_lt.ne hσord
  have hrankG : CFSG.pRank p (StatedSp n K) ≤ 1 := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
    exact hrank.le
  have hap : (e x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have ha1 : e x ≠ 1 := fun h => hx1 (e.injective (by rw [h, map_one]))
  have hxo : orderOf (proj n K (e x)) = p :=
    orderOf_eq_prime (by rw [← map_pow, hap, map_one])
      (fun h => ha1 (hinj (by rw [h, map_one])))
  have hσa : fieldSp n K σ (e x) = e x := by
    rw [← hcongr]
    simp [MulAut.congr_apply, hαx]
  have key := sp_good_conclusion hp hp5 hf₀ hK hrankG hσ1 (a := e x) (S := e y) hap ha1 hxo hσa
    (by rw [← map_pow, hy2, map_one]) (fun h => hy1 (e.injective (by rw [h, map_one])))
    (by rw [← map_mul, ← map_mul, hxy])
  rw [← hcongr] at key
  exact GoodConclusion.of_mulEquiv e α x key

end CFSG.RankThree.PartOne
