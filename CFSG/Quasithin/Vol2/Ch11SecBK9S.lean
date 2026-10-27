module

public import CFSG.Quasithin.Vol2.Ch11SecBK9R
public import CFSG.Quasithin.Vol2.Ch11SecBK9O

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L V U T : Subgroup G} [IsMulCommutative ↥V]
  {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 4)
  (hLV : L ≤ Subgroup.normalizer (V : Set G)) {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
  (hπ : Function.Bijective π) (C : CovData K ↥V)
  (hCpi : ∀ γ, C.pi' γ = ((π γ : ↥(autOn L V)) : MulAut ↥V))
  {Ψ : (Fin 2 ⊕ Fin 2 → K) ≃ (Fin 2 ⊕ Fin 2 → K)}
  (hΨ : ∀ γ a, Ψ (mat 2 K γ *ᵥ a + C.kappa hK γ) = mat 2 K γ *ᵥ Ψ a + bm hK γ)
  (hUV : U ≤ V) (hCU : C.U₀ = U.subgroupOf V)

include hK hLV hπ hCpi hΨ hUV hCU in
theorem isMaxSubgroupIn_of_cov (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hxz : ∀ x ∈ L ⊔ T, x⁻¹ * (C.z : G) * x = C.z) :
    CFSG.Quasithin.IsMaxSubgroupIn (L ⊔ T) ((L ⊔ T) ⊓ Subgroup.normalizer (U : Set G)) := by
  have hU0 : U.subgroupOf V = C.compl 0 := by rw [C.compl_zero, hCU]
  have hNU := mem_normalizer_iff_rho hK hLV hπ C hCpi hΨ hUV hU0
  have hLT : ∀ x ∈ L ⊔ T, x ∈ Subgroup.normalizer (V : Set G) ∧
      x ∈ Subgroup.normalizer (L : Set G) := fun x hx =>
    ⟨sup_le hLV hTV hx, sup_le Subgroup.le_normalizer hTL hx⟩
  have horbit : ∀ x ∈ L ⊔ T, ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.normalizer (U : Set G) :=
    fun x hx => exists_inv_mul_mem_normalizer hK hLV hπ C hCpi hΨ hUV hCU (hLT x hx).1
      (hLT x hx).2 (hxz x hx)
  refine ⟨lt_of_le_of_ne inf_le_left fun h => ?_, fun X hNX hXLT => ?_⟩
  · obtain ⟨γ, hγ⟩ := exists_not_mem_stabQ hK (Ψ 0)
    obtain ⟨l, rfl⟩ := rhoL_surjective hLV hπ γ
    have hl : (l : G) ∈ (L ⊔ T) ⊓ Subgroup.normalizer (U : Set G) := by
      rw [h]
      exact Subgroup.mem_sup_left l.2
    exact hγ ((hNU l).mp hl.2)
  obtain ⟨x, hxX, hxN⟩ := IsConcreteLE.exists_of_lt hNX
  obtain ⟨l, hlL, hlx⟩ := horbit x (hXLT hxX)
  have hlLT : l ∈ L ⊔ T := Subgroup.mem_sup_left hlL
  have hn : l⁻¹ * x ∈ X :=
    hNX.le ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem hlLT) (hXLT hxX), hlx⟩
  have hlX : l ∈ X := by
    have h := X.mul_mem hxX (X.inv_mem hn)
    rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
  have hlU : l ∉ Subgroup.normalizer (U : Set G) := fun h => hxN ⟨hXLT hxX, by
    have h' := (Subgroup.normalizer (U : Set G)).mul_mem h hlx
    rwa [mul_inv_cancel_left] at h'⟩
  have hPS : stabQ (qOf (Ψ 0)) ≤ (X.subgroupOf L).map (rhoL hLV hπ) := fun γ hγ => by
    obtain ⟨m, rfl⟩ := rhoL_surjective hLV hπ γ
    exact ⟨m, hNX.le ⟨Subgroup.mem_sup_left m.2, (hNU m).mpr hγ⟩, rfl⟩
  have hSP : ¬ (X.subgroupOf L).map (rhoL hLV hπ) ≤ stabQ (qOf (Ψ 0)) := fun h =>
    hlU ((hNU ⟨l, hlL⟩).mpr (h ⟨⟨l, hlL⟩, hlX, rfl⟩))
  have hS := eq_top_of_stabQ_lt hK (Ψ 0) hPS hSP
  have hLX : L ≤ X := fun m hm => by
    obtain ⟨m', hm'X, hm'ρ⟩ : rhoL hLV hπ ⟨m, hm⟩ ∈ (X.subgroupOf L).map (rhoL hLV hπ) :=
      hS ▸ Subgroup.mem_top _
    have hk : rhoL hLV hπ (m'⁻¹ * ⟨m, hm⟩) = 1 := by
      rw [map_mul, map_inv, hm'ρ, inv_mul_cancel]
    have hc := (rhoL_eq_one_iff hLV hπ _).mp hk
    have hnU := mem_normalizer_of_mem_centralizer hUV hc
    have hm'X' : (m' : G) ∈ X := hm'X
    have h := X.mul_mem hm'X' (hNX.le ⟨Subgroup.mem_sup_left (m'⁻¹ * ⟨m, hm⟩).2, hnU⟩)
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h
  have hTX : T ≤ X := fun t ht => by
    obtain ⟨l', hl'L, hl't⟩ := horbit t (Subgroup.mem_sup_right ht)
    have h1 : l'⁻¹ * t ∈ X := hNX.le
      ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hl'L))
        (Subgroup.mem_sup_right ht), hl't⟩
    have h := X.mul_mem (hLX hl'L) h1
    rwa [mul_inv_cancel_left] at h
  exact le_antisymm hXLT (sup_le hLX hTX)

include hK hLV hπ hCpi hΨ hUV hCU in
theorem relIndex_ne_two_of_cov :
    ((L ⊔ T) ⊓ Subgroup.normalizer (U : Set G)).relIndex (L ⊔ T) ≠ 2 := by
  have hU0 : U.subgroupOf V = C.compl 0 := by rw [C.compl_zero, hCU]
  have hNU := mem_normalizer_iff_rho hK hLV hπ C hCpi hΨ hUV hU0
  intro h2
  have hnorm := Subgroup.normal_of_index_eq_two h2
  apply not_normal_stabQ hK (Ψ 0)
  refine ⟨fun δ hδ γ => ?_⟩
  obtain ⟨n, rfl⟩ := rhoL_surjective hLV hπ δ
  obtain ⟨m, rfl⟩ := rhoL_surjective hLV hπ γ
  rw [← map_inv, ← map_mul, ← map_mul, ← hNU]
  have hn : (n : G) ∈ (L ⊔ T) ⊓ Subgroup.normalizer (U : Set G) :=
    ⟨Subgroup.mem_sup_left n.2, (hNU n).mpr hδ⟩
  have h := hnorm.conj_mem ⟨n, hn.1⟩ hn ⟨m, Subgroup.mem_sup_left m.2⟩
  exact (Subgroup.mem_inf.mp h).2

include hK hLV hπ hCpi hΨ hUV hCU in
theorem exists_three_of_cov (hCzL : ((C.z : ↥V) : G) ∈ Subgroup.centralizer (L : Set G))
    (hCL : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    ∃ Y : Subgroup G, Y ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card Y = 3 ∧
      Y ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU0 : U.subgroupOf V = C.compl 0 := by rw [C.compl_zero, hCU]
  have hNU := mem_normalizer_iff_rho hK hLV hπ C hCpi hΨ hUV hU0
  obtain ⟨γ₃, hγ₃P, hγ₃⟩ := exists_orderOf_eq_three hK (Ψ 0)
  obtain ⟨l₃, rfl⟩ := rhoL_surjective hLV hπ γ₃
  have hk3 : rhoL hLV hπ (l₃ ^ 3) = 1 := by rw [map_pow, ← hγ₃, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := hCL ⟨((l₃ ^ 3 : ↥L) : G), (l₃ ^ 3).2, (rhoL_eq_one_iff hLV hπ _).mp hk3⟩
  have hk' : (l₃ ^ 3) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have h := congrArg (fun w : ↥(L ⊓ Subgroup.centralizer (V : Set G)) => (w : G)) hk
    simpa using h
  obtain ⟨y, hy⟩ : ∃ y : ↥L, y = l₃ ^ (2 ^ k) := ⟨_, rfl⟩
  have hy3 : y ^ 3 = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, hk']
  have hρy : rhoL hLV hπ y ≠ 1 := by
    rw [hy, map_pow]
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hγ₃] at h3
    have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hyP : rhoL hLV hπ y ∈ stabQ (qOf (Ψ 0)) := by
    rw [hy, map_pow]
    exact Subgroup.pow_mem _ hγ₃P _
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hord : orderOf (y : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hy3 hy1
  have hyU : (y : G) ∉ Subgroup.centralizer (U : Set G) := by
    intro hyC
    apply hρy
    rw [rhoL_eq_one_iff, Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hvU : v ∈ U
    · exact Subgroup.mem_centralizer_iff.mp hyC v hvU
    have hidx : (U.subgroupOf V).index = 2 := by
      rw [← hCU]
      exact C.index₀
    have hz : C.z ∉ U.subgroupOf V := by
      rw [← hCU]
      exact C.z_not_mem₀
    have hzv : C.z * ⟨v, hv⟩ ∈ U.subgroupOf V :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hz hvU)
    have h1 := Subgroup.mem_centralizer_iff.mp hyC ((C.z : G) * v) hzv
    have h2 := Subgroup.mem_centralizer_iff.mp hCzL y y.2
    change ((C.z : ↥V) : G) * v * y = y * ((C.z : G) * v) at h1
    calc v * (y : G) = ((C.z : G))⁻¹ * ((C.z : G) * v * y) := by group
      _ = ((C.z : G))⁻¹ * (y * (C.z : G) * v) := by rw [h1]; group
      _ = ((C.z : G))⁻¹ * ((C.z : G) * y * v) := by rw [h2]
      _ = y * v := by group
  refine ⟨Subgroup.zpowers (y : G), ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨y.2, (hNU y).mpr hyP⟩
  · rw [Nat.card_zpowers, hord]
  · rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwY, hwC⟩ := Subgroup.mem_inf.mp hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    have hw3 : orderOf w = 3 := by
      have h := orderOf_dvd_of_mem_zpowers hwY
      rw [hord] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hw1
      · exact h1
    have heq : Subgroup.zpowers w = Subgroup.zpowers (y : G) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwY)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hw3])
    apply hyU
    have hyw : (y : G) ∈ Subgroup.zpowers w := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    exact Subgroup.zpowers_le.mpr hwC hyw

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
