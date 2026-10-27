module

public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Sporadic.Schreier.J1QT

public section

namespace CFSG.Quasithin

namespace P1469Two

open CFSG.Blueprint CFSG.Sporadic.Schreier

theorem center_eq_bot_of_simple_of_noncomm {K : Type*} [Group K] [IsSimpleGroup K] {x y : K}
    (hxy : x * y ≠ y * x) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hx : x ∈ Subgroup.center K := by rw [h]; trivial
    exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem sq_eq_one_of_index_two_simple {M : Type*} [Group M] {K : Subgroup M} [K.Normal]
    [IsSimpleGroup K] {x y : K} (hxy : x * y ≠ y * x) (hidx : K.index = 2) {c : M}
    (hc : ∀ m : M, m * c ^ 2 = c ^ 2 * m) : c ^ 2 = 1 := by
  have hfin : Finite (M ⧸ K) := Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_eq_card, hidx]; omega)
  have h1 : Nat.card (M ⧸ K) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  have h2 := pow_card_eq_one' (G := M ⧸ K) (x := (c : M ⧸ K))
  rw [h1] at h2
  have hτ : c ^ 2 ∈ K := (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact h2)
  have hcenter : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_of_noncomm hxy
  have hτc : (⟨c ^ 2, hτ⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k)
  rw [hcenter, Subgroup.mem_bot] at hτc
  exact congrArg Subtype.val hτc

theorem noOrderFour_J1
    {X : Type} [Group X] [Finite X] (hJ : IsSporadic .J1 X) :
    ∀ g : X, g ^ 4 = 1 → g ^ 2 = 1 := by
  classical
  intro g hg4
  by_contra hg2
  obtain ⟨e₀⟩ := hJ
  let e : X ≃* NativeSporadic.J1 := e₀
  have : Finite NativeSporadic.J1 := Finite.of_equiv X e.toEquiv
  have ha4 : e g ^ 4 = 1 := by rw [← map_pow, hg4, map_one]
  have ha2 : e g ^ 2 ≠ 1 := fun h => hg2 (e.injective (by rw [map_pow, h, map_one]))
  have ht : orderOf (e g ^ 2) = 2 :=
    orderOf_eq_prime (by rw [← pow_mul]; exact ha4) ha2
  obtain ⟨K, hKn, hKs, hK60, ⟨x, y, hxy⟩, -⟩ :=
    qt_unique_j1_involution_centralizer_normal_simple_subgroup (e g ^ 2) ht
  have hC : Nat.card (Subgroup.centralizer ({e g ^ 2} : Set NativeSporadic.J1)) = 120 :=
    (ctugs_j1_involution_centralizer_odd_core_free ⟨MulEquiv.refl _⟩ (e g ^ 2) ht).1
  have hidx : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    rw [hK60, hC] at h
    omega
  have haC : e g ∈ Subgroup.centralizer ({e g ^ 2} : Set NativeSporadic.J1) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← pow_succ, ← pow_succ']
  have := hKn
  have := hKs
  have key := sq_eq_one_of_index_two_simple hxy hidx
    (c := (⟨e g, haC⟩ : Subgroup.centralizer ({e g ^ 2} : Set NativeSporadic.J1)))
    (fun m => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2))
  exact ha2 (congrArg Subtype.val key)

theorem exists_central_involution {B X : Type*} [Group B] [Group X] [Finite X] (ψ : B →* X) {N : Subgroup B}
    (hN2 : IsPGroup 2 ↥N) (hcent : ∀ q ∈ N, ∀ g : B, ψ q * ψ g = ψ g * ψ q) {q : B} (hq : q ∈ N)
    (hq1 : ψ q ≠ 1) :
    ∃ b : B, orderOf (ψ b) = 2 ∧ ∀ g : B, ψ b * ψ g = ψ g * ψ b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hN2 ⟨q, hq⟩
  have hqk : q ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hyk : ψ q ^ 2 ^ k = 1 := by rw [← map_pow, hqk, map_one]
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.zpowers (ψ q)) := by
    rw [Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyk)
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hj, h0, pow_zero])) hq1
    · rw [hj]
      exact dvd_pow_self 2 h0.ne'
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers (ψ q))) 2 hdvd
  have heo : orderOf (e : X) = 2 := by rw [Subgroup.orderOf_coe]; exact he
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp e.2
  refine ⟨q ^ m, ?_, fun g => ?_⟩
  · rw [map_zpow, hm, heo]
  · rw [map_zpow]
    exact ((Commute.zpow_left (show Commute (ψ q) (ψ g) from hcent q hq g) m)).eq

theorem not_isSolvable_range {B X : Type*} [Group B] [Finite B] [Group X] (hns : ¬ Group.IsSolvable B)
    (ψ : B →* X) (hker : IsPGroup 2 ↥ψ.ker) : ¬ Group.IsSolvable ↥ψ.range := by
  intro hrange
  have : Group.IsNilpotent ↥ψ.ker := hker.isNilpotent
  have : Group.IsSolvable ↥ψ.ker := inferInstance
  exact hns (Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]))

theorem isSolvable_of_isCyclic'' {H : Type*} [Group H] (h : IsCyclic H) : Group.IsSolvable H := by
  let _ : CommGroup H := IsCyclic.commGroup
  exact Group.isSolvable_of_comm fun a b => mul_comm a b

theorem mem_center_of_mulEquiv' {H Q : Type*} [Group H] [Group Q] (f : H ≃* Q) {x : H}
    (hx : ∀ h : H, h * x = x * h) : f x ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨h, rfl⟩ := f.surjective q
  rw [← map_mul, ← map_mul, hx h]

theorem perm_four_eq_one' : ∀ x : Equiv.Perm (Fin 4),
    x * Equiv.swap 0 1 = Equiv.swap 0 1 * x →
    x * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) =
      (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) * x → x = 1 := by
  decide

theorem noSL25_psl2_odd {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hX : IsPSL 2 p 1 X) {B : Type} [Group B] [Finite B]
    (_hper : Group.IsPerfect B) (hns : ¬ Group.IsSolvable B) (ψ : B →* X)
    (α : B →* alternatingGroup (Fin 5)) (_hα : Function.Surjective α) (hψα : ψ.ker ≤ α.ker)
    (hα2 : IsPGroup 2 ↥α.ker) (hcent : ∀ q ∈ α.ker, ∀ g : B, ψ q * ψ g = ψ g * ψ q) :
    ∀ q ∈ α.ker, ψ q = 1 := by
  classical
  intro q hq
  by_contra hq1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hbo, hbc⟩ := exists_central_involution ψ hα2 hcent hq hq1
  obtain ⟨K, _, _, _, ε, hcard, -, -⟩ :=
    CFSG.QuasithinUnique.K1.psl2_model_data (by omega : p ≠ 2) hX
  have hF : Nat.card K = p ^ 1 := by rw [Nat.card_eq_fintype_card]; exact hcard
  set H' : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) := ψ.range.map ε.toMonoidHom
    with hH'
  let eH : ↥ψ.range ≃* ↥H' := Subgroup.equivMapOfInjective ψ.range ε.toMonoidHom ε.injective
  have hbR : ψ b ∈ ψ.range := ⟨b, rfl⟩
  set x : ↥H' := eH ⟨ψ b, hbR⟩ with hx
  have hxc : ∀ h : ↥H', h * x = x * h := by
    intro h
    obtain ⟨⟨_, g, rfl⟩, rfl⟩ := eH.surjective h
    rw [hx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbc g).symm
  have hox : orderOf x = 2 := by rw [hx, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hbo
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hox; omega
  have hnsH : ¬ Group.IsSolvable ↥H' := fun h =>
    not_isSolvable_range hns ψ (hα2.to_le hψα)
      (Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective)
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list (F := K) hF H' with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ |
      ⟨-, ⟨eA5⟩⟩ | ⟨m, t, -, -, -, -, E, C, hEn, hEel, -, -, -, -, hEC, hfaith, -⟩ |
      ⟨m, hm, ⟨eL⟩⟩ | ⟨m, hm, -⟩
  ·
    exact hnsH (Group.isSolvable_of_comm fun a b => hel.toIsMulCommutative.is_comm.comm a b)
  ·
    exact hnsH (isSolvable_of_isCyclic'' hcyc)
  ·
    have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact hnsH (Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective)
  ·
    have h := mem_center_of_mulEquiv' eA hxc
    rw [alternatingGroup.center_eq_bot (le_of_eq (Nat.card_fin 4).symm), Subgroup.mem_bot] at h
    exact hx1 (eA.injective (by rw [h, map_one]))
  ·
    have h := Subgroup.mem_center_iff.mp (mem_center_of_mulEquiv' eS hxc)
    have h1 := perm_four_eq_one' (eS x) (h _).symm (h _).symm
    exact hx1 (eS.injective (by rw [h1, map_one]))
  ·
    have h := mem_center_of_mulEquiv' eA5 hxc
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot] at h
    exact hx1 (eA5.injective (by rw [h, map_one]))
  ·
    have : E.Normal := hEn
    have hxEC : x ∈ ((E ⊔ C : Subgroup ↥H') : Set ↥H') := by rw [hEC]; exact Subgroup.mem_top x
    rw [Subgroup.normal_mul] at hxEC
    obtain ⟨e₀, he₀, c₀, hc₀, hec⟩ := Set.mem_mul.mp hxEC
    have hcomm := isMulCommutative_iff.mp hEel.toIsMulCommutative
    have hc₁ : c₀ = 1 := by
      refine hfaith c₀ hc₀ fun e' he' => ?_
      have hc' : c₀ = e₀⁻¹ * x := by rw [← hec]; group
      have h1 : e₀⁻¹ * e' = e' * e₀⁻¹ :=
        congrArg Subtype.val (hcomm ⟨e₀⁻¹, E.inv_mem he₀⟩ ⟨e', he'⟩)
      rw [hc', mul_assoc, ← hxc e', ← mul_assoc, h1, mul_assoc]
    rw [hc₁, mul_one] at hec
    have hxp : x ^ p = 1 := by rw [← hec]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian e₀ he₀
    have h2 := orderOf_dvd_of_pow_eq_one hxp
    rw [hox] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega
  ·
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hm
    subst hm1
    have h := mem_center_of_mulEquiv' eL hxc
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p 1), Subgroup.mem_bot] at h
    exact hx1 (eL.injective (by rw [h, map_one]))
  ·
    have := Nat.eq_one_of_dvd_one hm
    omega

end P1469Two

end CFSG.Quasithin
