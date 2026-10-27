module

public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartOne.K1214

open Matrix Subgroup

variable {K : Type} [Field K]

@[expose] noncomputable def diagSL : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun t := ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by
    rw [det_fin_two_of]
    simp⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    apply Subtype.ext
    show (!![((s * t : Kˣ) : K), 0; 0, (((s * t)⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) =
      !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] * !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem diagSL_apply (t : Kˣ) :
    (diagSL t : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

theorem diagSL_injective : Function.Injective (diagSL (K := K)) := by
  intro s t h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [diagSL_apply] at this
  exact Units.ext (by simpa using this)

theorem sylowShape_SL2 [Finite K] {p e m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he1 : 1 ≤ e)
    (hN : Nat.card K - 1 = p ^ e * m) (hm : ¬ p ∣ m) :
    SylowShape p 1 e (SpecialLinearGroup (Fin 2) K) := by
  classical
  have hpe : (p ^ e) ∣ Nat.card K - 1 := ⟨m, hN⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard := CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := K) hpe
  set μ : Subgroup Kˣ := rootsOfUnity (p ^ e) K with hμ
  set T : Subgroup (SpecialLinearGroup (Fin 2) K) := μ.map diagSL with hT
  have hTcard : Nat.card T = p ^ e := by
    rw [hT, Subgroup.card_map_of_injective diagSL_injective, hcard]
  have hTp : IsPGroup p ↥T := IsPGroup.of_card hTcard
  have hidx : ¬ p ∣ T.index := by
    have h1 := Subgroup.card_mul_index T
    rw [hTcard, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K] at h1
    set N := Nat.card K with hNdef
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    have hsq : N ^ 2 - 1 = (N - 1) * (N + 1) := by
      obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      rw [hn]
      have : (n + 1) ^ 2 = n * (n + 1 + 1) + 1 := by ring
      simp only [Nat.add_sub_cancel]
      exact Nat.sub_eq_of_eq_add this
    have hpe0 : 0 < p ^ e := pow_pos hp.pos _
    have h2 : T.index = N * (m * (N + 1)) := by
      refine Nat.eq_of_mul_eq_mul_left hpe0 ?_
      rw [h1, hsq, hN]
      ring
    have hpdvd : p ∣ p ^ e * m := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m
    have hpN : ¬ p ∣ N := fun h => by
      have h' : p ∣ N - (N - 1) := Nat.dvd_sub h (hN ▸ hpdvd)
      rw [Nat.sub_sub_self hN1] at h'
      exact hp.one_lt.ne' (Nat.dvd_one.1 h')
    have hpN1 : ¬ p ∣ N + 1 := fun h => by
      have h' : p ∣ (N + 1) - (N - 1) := Nat.dvd_sub h (hN ▸ hpdvd)
      have h3 : (N + 1) - (N - 1) = 2 := by omega
      rw [h3] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
    rw [h2]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpN h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hm h
      · exact hpN1 h
  have hcyc : IsCyclic ↥μ := inferInstance
  let φ1 : ↥T ≃* ↥μ := (Subgroup.equivMapOfInjective μ diagSL diagSL_injective).symm
  let φ2 : Multiplicative (ZMod (p ^ e)) ≃* ↥μ :=
    (((ZMod.ringEquivCongr hcard.symm).toAddEquiv).toMultiplicative).trans (zmodCyclicMulEquiv hcyc)
  exact SylowShape.of_witness hp hTp hidx (φ1.trans (φ2.symm.trans (MulEquiv.piUnique (fun _ : Fin 1 => Multiplicative (ZMod (p ^ e)))).symm))

theorem center_SL2_eq_bot [CharP K 2] : center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by
      rw [CharTwo.sub_eq_add, CharTwo.add_sq, h2, one_pow, one_add_one_eq_two]
      exact CharTwo.two_eq_zero
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

theorem sylowShape_PSL2 [Finite K] [CharP K 2] {p e m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he1 : 1 ≤ e) (hN : Nat.card K - 1 = p ^ e * m) (hm : ¬ p ∣ m) :
    SylowShape p 1 e (ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have h := center_SL2_eq_bot (K := K)
  exact SylowShape.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot)
    (sylowShape_SL2 hp hp2 he1 hN hm)

open CFSG.Assembly.LowTwoRank in
theorem sylowShape_of_psl2Model {X : Type} [Group X] [Finite X] {p e m f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he1 : 1 ≤ e) (hN : 2 ^ f - 1 = p ^ e * m) (hm : ¬ p ∣ m)
    (hX : StatedClassicalModel X .PSL 2 2 f) : SylowShape p 1 e X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact SylowShape.of_mulEquiv (φ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    (sylowShape_PSL2 hp hp2 he1 (by rw [hK]; exact hN) hm)

end CFSG.RankThree.PartOne.K1214
