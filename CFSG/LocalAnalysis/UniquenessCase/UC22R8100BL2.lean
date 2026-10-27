module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.LocalAnalysis.EvenBN.Common Subgroup
open scoped MatrixGroups

theorem uc22r8100b_torus_frame {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n) {q : ℕ}
    [Fact q.Prime] (hq : q ∣ 2 ^ n - 1) (Q : Sylow q X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (e : X ≃* SL(2, K)),
      Nat.card K = 2 ^ n ∧
      (∃ μ : Kˣ, μ ≠ 1 ∧ diagSL μ ∈ Subgroup.map e.toMonoidHom (Q : Subgroup X)) ∧
      Subgroup.map e.toMonoidHom (Q : Subgroup X) ≤ torusSL K ∧
      ∀ g : SL(2, K), (∀ s ∈ Subgroup.map e.toMonoidHom (Q : Subgroup X), g * s = s * g) →
        g ∈ torusSL K := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ := LieModel.statedClassicalModel h (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  let e₀ : X ≃* SL(2, K) := e₁.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K))
  have hqX : q ∣ Nat.card X := by
    have h1 : q ∣ Nat.card (torusSL K) := by rw [card_torusSL, hK]; exact hq
    rw [Nat.card_congr e₀.toEquiv]
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  have hQq : q ∣ Nat.card Q := Q.dvd_card_of_dvd_card hqX
  haveI : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le (Fact.out : q.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hQq)
  have hQp : IsPGroup q Q := Q.isPGroup'
  haveI := hQp.center_nontrivial
  have hZq : q ∣ Nat.card (Subgroup.center Q) := by
    rcases (hQp.to_subgroup (Subgroup.center Q)).card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Nat.ne_of_gt Finite.one_lt_card)
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) q hZq
  have hz0o : orderOf (((z : Q)) : X) = q := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz0c : ∀ s ∈ (Q : Subgroup X), s * ((z : Q) : X) = ((z : Q) : X) * s := fun s hs =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨s, hs⟩)
  have hq1 : (q : ℕ) ≠ 1 := (Fact.out : q.Prime).one_lt.ne'
  have hz1 : e₀ ((z : Q) : X) ≠ 1 := by
    intro h1
    rw [← orderOf_eq_one_iff, MulEquiv.orderOf_eq, hz0o] at h1
    exact hq1 h1
  have hzK : e₀ ((z : Q) : X) ^ (Nat.card K - 1) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [MulEquiv.orderOf_eq, hz0o, hK]
    exact hq
  obtain ⟨x, μ, hμ, hx⟩ := exists_conj_eq_diagSL hz1 hzK
  let e : X ≃* SL(2, K) := e₀.trans (MulAut.conj x)
  have hez : e ((z : Q) : X) = diagSL μ := hx
  have hS : ∀ s ∈ (Q : Subgroup X), e s ∈ torusSL K := by
    intro s hs
    rw [← centralizer_diagSL hμ, Subgroup.mem_centralizer_singleton_iff, ← hez, ← map_mul,
      ← map_mul, hz0c s hs]
  refine ⟨K, hKf, hKfin, inferInstance, e, hK, ⟨μ, hμ, ⟨_, ((z : Q)).2, hez⟩⟩, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hS s hs
  · intro g hg
    rw [← centralizer_diagSL hμ, Subgroup.mem_centralizer_singleton_iff]
    exact hg _ ⟨_, ((z : Q)).2, hez⟩

theorem uc22r8100b_normalizer_le {G : Type*} [Group G] {S T : Subgroup G} (hST : S ≤ T)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hC : ∀ g : G, (∀ s ∈ S, g * s = s * g) → g ∈ T)
    {y : G} (hy : y ∈ normalizer (S : Set G)) : y ∈ normalizer (T : Set G) := by
  have key : ∀ y ∈ normalizer (S : Set G), ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro y hy t ht
    refine hC _ fun s hs => ?_
    have hs' : y⁻¹ * s * y ∈ S := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) s).1 hs
    have h1 := hT t ht _ (hST hs')
    calc y * t * y⁻¹ * s = y * (t * (y⁻¹ * s * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * s * y) * t) * y⁻¹ := by rw [h1]
      _ = s * (y * t * y⁻¹) := by group
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨key y hy t, fun ht => ?_⟩
  simpa [mul_assoc] using key y⁻¹ (Subgroup.inv_mem _ hy) _ ht

theorem uc22r8100b_normalizer_torus {K : Type} [Field K] [Finite K] [CharP K 2] {μ : Kˣ}
    (hμ : μ ≠ 1) {y : SL(2, K)} (hy : y ∈ normalizer (torusSL K : Set SL(2, K))) :
    y ∈ torusSL K ∨ y * y = 1 := by
  obtain ⟨ν, hν⟩ := mem_torusSL_iff.1
    ((Subgroup.mem_normalizer_iff.1 hy (diagSL μ)).1 (diagSL_mem_torusSL μ))
  have hyν : y * diagSL μ = diagSL ν * y := by rw [hν]; group
  obtain ⟨a, b, c, d, hdet, rfl⟩ := exists_eq_mkSL y
  have e00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hyν
  have e01 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hyν
  have e10 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 1 0) hyν
  have e11 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 1 1) hyν
  simp [coe_mkSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases hνμ : ν = μ
  · subst hνμ
    have hne : (ν : K) - (ν : K)⁻¹ ≠ 0 := sub_ne_zero.2 (units_inv_ne_self hμ).symm
    have hb : b = 0 := by
      have : b * ((ν : K) - (ν : K)⁻¹) = 0 := by linear_combination -e01
      exact (mul_eq_zero.1 this).resolve_right hne
    have hc : c = 0 := by
      have : c * ((ν : K) - (ν : K)⁻¹) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hne
    subst hb hc
    exact Or.inl (mkSL_mem_torusSL a d hdet)
  · have hne : (μ : K) - (ν : K) ≠ 0 := sub_ne_zero.2 fun h1 => hνμ (Units.ext h1).symm
    have hne' : (μ : K)⁻¹ - (ν : K)⁻¹ ≠ 0 := sub_ne_zero.2 fun h1 =>
      hνμ (Units.ext (inv_injective h1)).symm
    have ha : a = 0 := by
      have : a * ((μ : K) - (ν : K)) = 0 := by linear_combination e00
      exact (mul_eq_zero.1 this).resolve_right hne
    have hd : d = 0 := by
      have : d * ((μ : K)⁻¹ - (ν : K)⁻¹) = 0 := by linear_combination e11
      exact (mul_eq_zero.1 this).resolve_right hne'
    subst ha hd
    exact Or.inr (mkSL_mul_self_eq_one hdet (add_zero 0))

theorem uc22r8100b_not_dvd_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n)
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) [Fact q.Prime]
    (hq : q ∣ 2 ^ n - 1) (Q : Sylow q X) {y : X} (hy : y ∈ normalizer ((Q : Subgroup X) : Set X)) :
    orderOf y ≠ p := by
  obtain ⟨K, hKf, hKfin, hKc, e, hK, ⟨μ, hμ, -⟩, hST, hC⟩ := uc22r8100b_torus_frame h hq Q
  intro hord
  have hyS : e y ∈ normalizer ((Subgroup.map e.toMonoidHom (Q : Subgroup X) : Subgroup SL(2, K)) :
      Set SL(2, K)) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  have hyT := uc22r8100b_normalizer_le hST
    (fun a ha b hb => mul_comm_of_mem_isMulCommutative (torusSL K) ha hb) hC hyS
  have hp2' : p ∣ 2 → False := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  rcases uc22r8100b_normalizer_torus hμ hyT with hT | hsq
  · have h1 : p ∣ 2 ^ n - 1 := by
      rw [← hord, ← MulEquiv.orderOf_eq e y, ← hK, ← card_torusSL (k := K)]
      exact Subgroup.orderOf_dvd_natCard _ hT
    have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpn h1
    have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    exact hp2' (h3 ▸ h2)
  · have h1 : orderOf (e y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [MulEquiv.orderOf_eq, hord] at h1
    exact hp2' h1

theorem uc22r8100b_not_dvd_normalizer_of_le {Γ : Type} [Group Γ] [Finite Γ] {K S : Subgroup Γ}
    {n : ℕ} (hK : IsL2 K n) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1)
    (hq : q.Prime) (hqn : q ∣ 2 ^ n - 1) (hS : IsSylowOf q S K) :
    ∀ y ∈ K, y ∈ normalizer (S : Set Γ) → orderOf y ≠ p := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, rfl⟩ := hS
  intro y hyK hyN
  have hmem : ∀ s : K, s ∈ (Q : Subgroup K) ↔ (s : Γ) ∈ (Q : Subgroup K).map K.subtype :=
    fun s => (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hyQ : (⟨y, hyK⟩ : K) ∈ normalizer ((Q : Subgroup K) : Set K) := by
    refine Subgroup.mem_normalizer_iff.2 fun s => ?_
    rw [hmem s, hmem (⟨y, hyK⟩ * s * ⟨y, hyK⟩⁻¹)]
    exact Subgroup.mem_normalizer_iff.1 hyN s
  have h1 := uc22r8100b_not_dvd_normalizer hK hp hp2 hpn hqn Q hyQ
  have h2 : orderOf y = orderOf (⟨y, hyK⟩ : K) := Subgroup.orderOf_coe (⟨y, hyK⟩ : K)
  rwa [h2]

end CFSG.LocalAnalysis.UniquenessCase.UC22
