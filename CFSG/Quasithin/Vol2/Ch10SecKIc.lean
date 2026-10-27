module

public import CFSG.Quasithin.Vol2.Ch10SecKIb
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin Matrix CFSG.Quasithin.JonesParshall
open CFSG.QuasithinUnique.Bridge.Alt57Model
open scoped commutatorElement

theorem false_of_simple_surj {Γ X : Type} [Group Γ] [Group X] (hΓ : IsSimpleGroup Γ)
    (hc : ¬ TargetCard (Nat.card Γ)) (hX : TargetCard (Nat.card X)) (π : Γ →* X)
    (hπ : Function.Surjective π) : False := by
  have hX1 : 1 < Nat.card X := by
    have := le_of_targetCard hX
    omega
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hX1
  obtain ⟨e⟩ := SecA.nonempty_mulEquiv_of_surjective hΓ π hπ
  exact hc (by rw [Nat.card_congr e.toEquiv]; exact hX)

variable {K : Type} [Field K]

theorem false_of_ker_le_center [CharP K 2] [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n)
    (hn2 : 2 ≤ n) {X : Type} [Group X] (h16 : ¬ 16 ∣ Nat.card X) (φ : SL3 K →* X)
    (hkZ : ∀ k ∈ φ.ker, k ∈ Subgroup.center (SL3 K)) : False := by
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
  rw [hc, hn, ← pow_mul] at hdvd
  have h16' : 16 ∣ 2 ^ (n * 2) :=
    (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)
  exact h16 (h16'.trans hdvd)

theorem sl3_hom_trivial [CharP K 2] [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (hn2 : 2 ≤ n)
    {X : Type} [Group X] (h16 : ¬ 16 ∣ Nat.card X) (φ : SL3 K →* X) : ∀ A : SL3 K, φ A = 1 := by
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
    refine false_of_ker_le_center hn hn2 h16 φ fun k hk => ?_
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

theorem false_of_g2_surj [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {X : Type}
    [Group X] [Nontrivial X] (h16 : ¬ 16 ∣ Nat.card X) (π : ↥(quasithinG2 K) →* X)
    (hπ : Function.Surjective π) : False := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let e : ↥(Explicit.cayleyGroup K) ≃* ↥(CFSG.Open.quasithinG2 K) :=
    MulEquiv.subgroupCongr CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup.symm
  let ψ : ↥(Explicit.cayleyGroup K) →* X := π.comp e.toMonoidHom
  have hA := sl3_hom_trivial hK hn h16 (ψ.comp JonesParshall.g2A)
  have hall := SecA.C10P01.cayley_hom_trivial h4 ψ hA
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨g, rfl⟩ := hπ x
  apply hx
  have h1 := hall (e.symm g)
  simpa [ψ] using h1

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
