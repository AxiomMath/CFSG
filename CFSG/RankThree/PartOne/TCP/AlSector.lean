module

public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartOne.S11d.PSpGood
public import CFSG.RankThree.PartOne.TCP.Concrete
public import CFSG.RankThree.PartOne.TCP.Config

public section

namespace CFSG.RankThree.PartOne.TCP

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCX
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp fieldAut spLinearAutGroup
  spSemilinearAutGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem psp_sector {T : Type} [Group T] [Finite T] {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrank : LocalRankLeTwo p T) (h2 : 2 ≤ CFSG.pRank p T) (hf₀ : 1 ≤ f₀)
    (hM : LieModel T .PSp n 2 (p * f₀)) (hLow : n ≤ 3) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) (hLR : LocalRankAut p T α) (hFix : FixModel .PSp n f₀ α) :
    n = 2 ∧ orderOf (((2 ^ (p * f₀) : ℕ)) : ZMod p) = 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, k₀, _, _, hn2, hK, hk₀, ⟨eT⟩, ⟨eF⟩⟩ :=
    psp_concrete hp hp5 hrank hf₀ hM hαp hαinn hLR hFix
  have hp2 : p ≠ 2 := by omega
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  have : CharP k₀ 2 := K128.charP_two_of_card_eq_two_pow hk₀
  have hpK : ¬ p ∣ Nat.card K := not_dvd_card_of_charTwo hp hp2
  have hpk : ¬ p ∣ Nat.card k₀ := not_dvd_card_of_charTwo hp hp2
  have hQ : Nat.card K = Nat.card k₀ ^ p := by rw [hK, hk₀, ← pow_mul, mul_comm]
  have hord : orderOf (Nat.card K : ZMod p) = orderOf (Nat.card k₀ : ZMod p) :=
    orderOf_natCast_pow_prime hp hQ
  have hrk : 2 ≤ CFSG.pRank p ↥(StatedSp n K) := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT]
    exact h2
  have hbd := blockDim_le_of_two_le_pRank hp hp2 hpK hrk
  rw [hord] at hbd
  by_cases hcond : Even (orderOf (Nat.card k₀ : ZMod p)) → orderOf (Nat.card k₀ : ZMod p) < n
  · exfalso
    obtain ⟨R, hRe, hRc, hU⟩ := exists_psp_config hp hpk hbd
    obtain ⟨U, hU1, hU2, hUN⟩ := hU hcond
    let ψ : StatedSp n k₀ →* T := (fixRes α).subtype.comp eF.symm.toMonoidHom
    have hψ : Function.Injective ψ := (fixRes α).subtype_injective.comp eF.symm.injective
    have hfix : ∀ y, α (ψ y) = ψ y := fun y =>
      mem_fixSub.mp (fixRes_le_fixSub α (eF.symm y).2)
    exact false_of_rank_two_in_fixSub hαp hαinn hLR ψ hψ hfix hRe hRc hU1 hU2 hUN
  · have hcond' : Even (orderOf (Nat.card k₀ : ZMod p)) ∧
        n ≤ orderOf (Nat.card k₀ : ZMod p) := by
      by_contra hc
      exact hcond fun hev => by
        by_contra hge
        exact hc ⟨hev, by omega⟩
    obtain ⟨hev, hne⟩ := hcond'
    have hbde : blockDim (orderOf (Nat.card k₀ : ZMod p)) = orderOf (Nat.card k₀ : ZMod p) :=
      ite_eq_left_iff.mpr fun h => absurd hev h
    rw [hbde] at hbd
    have hne' : orderOf (Nat.card k₀ : ZMod p) = n := le_antisymm hbd hne
    have hn2' : n = 2 := by
      obtain ⟨m, hm⟩ := hev
      omega
    refine ⟨hn2', ?_⟩
    have he2 : orderOf (Nat.card K : ZMod p) = 2 := by rw [hord, hne', hn2']
    rwa [hK] at he2

theorem psp_model {T : Type} [Group T] [Finite T] {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : LieModel T .PSp n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ (p * f₀) ∧ ∃ (e : T ≃* StatedSp n K) (σ : K ≃+* K), orderOf σ = p ∧
        Nat.card (descentField σ) = 2 ^ f₀ ∧ MulAut.congr e α = fieldSp n K σ := by
  have hC : StatedClassicalModel T .PSp n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ n := hC.1.2.2.1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (StatedProj (StatedSp n K)) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p :=
    orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ (innerAut _).one_mem))
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup n K := by
    have hidx' : (spSemilinearAutGroup n K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ spLinearAutGroup n K := by
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
  obtain ⟨hpf, σ, hσord, hkcard, h, -, hαh⟩ := hdesc p hp _ hE hD hα'ord
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hkcard
  have hcharK : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
  have hfinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hr : 1 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have hinj : Function.Injective (proj n K) := proj_injective_sp hK hf hr
  let ψ : StatedSp n K ≃* StatedProj (StatedSp n K) :=
    MulEquiv.ofBijective (proj n K)
      ⟨hinj, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩
  let φ : T ≃* StatedProj (StatedSp n K) := e.trans (h⁻¹ : MulAut (StatedProj (StatedSp n K)))
  have hφα : MulAut.congr φ α = fieldAut n K σ := by
    have : MulAut.congr φ α = h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  let e' : T ≃* StatedSp n K := φ.trans ψ.symm
  have hψe : ∀ t, ψ (e' t) = φ t := fun t => ψ.apply_symm_apply (φ t)
  have hcongr : MulAut.congr e' α = fieldSp n K σ := by
    refine MulEquiv.ext fun g => ?_
    apply ψ.injective
    have h1 : (MulAut.congr φ α) (ψ g) = fieldAut n K σ (ψ g) := by rw [hφα]
    have h2 : fieldAut n K σ (ψ g) = ψ (fieldSp n K σ g) :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj σ g
    have h3 : e'.symm g = φ.symm (ψ g) := rfl
    have h4 : ψ ((MulAut.congr e' α) g) = (MulAut.congr φ α) (ψ g) := by
      show ψ (e' (α (e'.symm g))) = φ (α (φ.symm (ψ g)))
      rw [hψe, h3]
    rw [h4, h1, h2]
  exact ⟨hn, K, inferInstance, hfinK, hcharK, hK, e', σ, hσord, hkcard, hcongr⟩

end CFSG.RankThree.PartOne.TCP
