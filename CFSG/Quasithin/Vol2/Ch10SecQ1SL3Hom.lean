module

public import CFSG.Quasithin.Vol2.Ch10SecQ1SL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Big
public import CFSG.Quasithin.Vol2.Ch10SecQ1Base

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open Matrix CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Bridge.Alt57Model
open scoped commutatorElement

variable {K : Type} [Field K]

theorem false_of_ker_le_center
    [CharP K 2] [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (hn2 : 2 ≤ n)
    {X : Type} [Group X] (hX : IsShapeGroup X) (φ : SL3 K →* X)
    (hkZ : ∀ k ∈ φ.ker, k ∈ Subgroup.center (SL3 K)) : False := by
  have hne : ∀ A : SL3 K, A ∉ Subgroup.center (SL3 K) → φ A ≠ 1 := fun A hA h1 => hA (hkZ A h1)
  rcases hX with ⟨m, hm, F, _, _, hF, ⟨e⟩⟩ | ⟨m, -, a, -, F, _, _, hf, hF, ⟨e⟩⟩ | he
  ·
    have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hF
    have hJ4 : e (φ (jMat3 K)) ^ 4 = 1 := by
      rw [← map_pow, ← map_pow, jMat3_pow_four, map_one, map_one]
    apply hne (jMat3 K ^ 2) jMat3_sq_not_mem_center
    apply e.injective
    rw [map_pow, map_pow, sq_eq_one_of_pow_four_SL2 _ hJ4, map_one]
  ·
    subst hf
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf (φ (pMat3 K)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, pMat3_pow_three, map_one]) (hne _ pMat3_not_mem_center)
    have h3 : 3 ∣ Nat.card X := hord ▸ orderOf_dvd_natCard _
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF] at h3
    exact three_not_dvd_card_suzuki a h3
  ·
    obtain ⟨e⟩ := he
    let Q : Multiplicative (K × K) →* SL3 K :=
      { toFun := fun p => qMat3 (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2
        map_one' := qMat3_zero
        map_mul' := fun p q => by
          simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
          exact (qMat3_mul _ _ _ _).symm }
    have hinj : Function.Injective (φ.comp Q) := by
      rw [injective_iff_map_eq_one]
      intro p hp
      have hmem : Q p ∈ φ.ker := hp
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hkZ _ hmem)
      have h01 := congrFun (congrFun hr 0) 1
      have h02 := congrFun (congrFun hr 0) 2
      simp [Q, qMat3_coe] at h01 h02
      apply Multiplicative.toAdd.injective
      exact Prod.ext h01.symm h02.symm
    have hdvd := Subgroup.card_dvd_of_injective (φ.comp Q) hinj
    have hc : Nat.card (Multiplicative (K × K)) = Nat.card K ^ 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, sq]
    rw [hc, hn, ← pow_mul, Nat.card_congr e.toEquiv, card_SL_three_zmod_two] at hdvd
    have h16 : 16 ∣ 2 ^ (n * 2) :=
      (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    omega

theorem sl3_hom_trivial
    [CharP K 2] [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (hn2 : 2 ≤ n)
    {X : Type} [Group X] (hX : IsShapeGroup X) (φ : SL3 K →* X) : ∀ A : SL3 K, φ A = 1 := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one h4
  have hperf : commutator (SL3 K) = ⊤ := sl3_commutator_eq_top hc0 (sq_ne_one hc1)
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) K) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 3) (K := K) (by norm_num)
      (Or.inl le_rfl)).2.1
  set Z := Subgroup.center (SL3 K) with hZ
  set π : SL3 K →* ProjectiveSpecialLinearGroup (Fin 3) K := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hN : (φ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map π) with h | h
  · exfalso
    refine false_of_ker_le_center hn hn2 hX φ fun k hk => ?_
    have : π k ∈ φ.ker.map π := ⟨k, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).1 this
  · have hcen : ∀ s : SL3 K, ∃ z ∈ Z, φ s = φ z := by
      intro s
      have : π s ∈ φ.ker.map π := by rw [h]; trivial
      obtain ⟨k, hk, hks⟩ := this
      have hz : k⁻¹ * s ∈ Z := QuotientGroup.eq.1 hks
      refine ⟨k⁻¹ * s, hz, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    have hker : commutator (SL3 K) ≤ φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨z₁, hz₁, ha⟩ := hcen a
      obtain ⟨z₂, hz₂, hb⟩ := hcen b
      have hcomm : ⁅z₁, z₂⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hz₁ z₂).symm
      rw [MonoidHom.mem_ker, map_commutatorElement, ha, hb, ← map_commutatorElement, hcomm,
        map_one]
    intro A
    exact MonoidHom.mem_ker.1 (hker (hperf ▸ Subgroup.mem_top A))

end C10P01

open C10P01

theorem factB4aNineTensor_holds :
    FactB4aNineTensor := by
  intro K _ _ a ha hK X _ hX π hπ
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have := nontrivial_of_isShapeGroup hX
  have htriv := sl3_hom_trivial hK (by omega) hX
    (π.comp (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨g, rfl⟩ := hπ x
  obtain ⟨A, rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).surjective g
  exact hx (htriv A)

end CFSG.Quasithin.Vol2.Ch10.SecA
