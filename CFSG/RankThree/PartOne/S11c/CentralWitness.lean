module

public import CFSG.RankThree.GroupTheory.SteinbergCDCentralElementaryRank
public import CFSG.RankThree.Classical.UnitaryRankWitness
public import CFSG.RankThree.PartOne.S11c.PlaneLift

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory

theorem isElementaryAbelian_bot' {p : ℕ} {H : Type*} [Group H] :
    IsElementaryAbelian p (⊥ : Subgroup H) := by
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2,
      Subgroup.mem_bot.1 b.2])
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.mem_bot.1 x.2, one_pow]; rfl)

theorem exists_isElementaryAbelian_card_pRank {p : ℕ} (hp : 1 < p) {H : Type*} [Group H]
    [Finite H] : ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ pRank p H := by
  classical
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧
      Nat.card A = p ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro r ⟨A, -, hA⟩
    have h1 : r < p ^ r := Nat.lt_pow_self hp
    have h2 : Nat.card A ≤ Nat.card H := Subgroup.card_le_card_group A
    omega
  exact Nat.sSup_mem (s := {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧
    Nat.card A = p ^ r}) ⟨0, ⊥, isElementaryAbelian_bot', by simp⟩ hbdd

theorem exists_rank_four_of_central_witness {Y X : Type*} [Group Y] [Finite Y] [Group X]
    (φ : Y →* X) (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup X} {k : ℕ} (hU : IsElementaryAbelian p U)
    (hUcard : Nat.card U = p ^ k) (hk : 6 ≤ k) {s : X} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1)
    (hsU : ∀ u ∈ U, s * u = u * s) :
    ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y, V ≤ Subgroup.centralizer {z} ∧
      IsElementaryAbelian p V ∧ ∃ r : ℕ, 4 ≤ r ∧ Nat.card V = p ^ r := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hUp : IsPGroup p U := IsElementaryAbelian.isPGroup p U
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; exact (pow_pos hp.pos k).ne')
  set F : Subgroup Y := U.comap φ with hF
  have hnil : Group.IsNilpotent F := by
    let f : F →* U := (φ.comp F.subtype).codRestrict U fun x => x.2
    have : Group.IsNilpotent U := hUp.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro x hx
    have hxk : (x : Y) ∈ φ.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hxk) y)
  obtain ⟨P⟩ : Nonempty (Sylow p F) := inferInstance
  have hPc : (P : Subgroup F).Characteristic := Sylow.characteristic_of_normal P inferInstance
  set S : Subgroup Y := (P : Subgroup F).map F.subtype with hS
  have hSp : IsPGroup p S := P.2.map F.subtype
  have hSU : S.map φ = U := map_sylow_comap φ hφ hUp P
  have hSF : S ≤ F := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  obtain ⟨y, hy⟩ := hφ s
  have h2dvd : 2 ∣ orderOf y := by
    have : orderOf s ∣ orderOf y := by rw [← hy]; exact orderOf_map_dvd φ y
    rwa [orderOf_eq_prime hs2 hs1] at this
  set z : Y := y ^ (orderOf y / 2) with hzdef
  have hz : orderOf z = 2 := orderOf_pow_orderOf_div (orderOf_pos y).ne' h2dvd
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    omega
  have hzU : ∀ u ∈ U, φ z * u = u * φ z := by
    intro u hu
    have hzs : φ z ∈ Subgroup.zpowers s := by
      rw [hzdef, map_pow, hy]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hzs
    rw [← hm]
    exact ((Commute.zpow_left (show Commute s u from hsU u hu) m)).eq
  have hFz : ∀ x ∈ F, z * x * z⁻¹ ∈ F := fun x hx => by
    change φ (z * x * z⁻¹) ∈ U
    have hx' : φ x ∈ U := hx
    rw [map_mul, map_mul, map_inv, hzU _ hx', mul_inv_cancel_right]
    exact hx'
  have hFz' : ∀ x ∈ F, z⁻¹ * x * z ∈ F := fun x hx => by
    change φ (z⁻¹ * x * z) ∈ U
    have hx' : φ x ∈ U := hx
    rw [map_mul, map_mul, map_inv, mul_assoc, ← hzU _ hx', inv_mul_cancel_left]
    exact hx'
  let ψz : F ≃* F :=
    { toFun := fun x => ⟨z * x * z⁻¹, hFz x x.2⟩
      invFun := fun x => ⟨z⁻¹ * x * z, hFz' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x w => Subtype.ext (by simp [mul_assoc]) }
  have hψ : (P : Subgroup F).comap ψz.toMonoidHom = P := hPc.fixed ψz
  have hSz : ∀ x ∈ S, z * x * z⁻¹ ∈ S := by
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ (P : Subgroup F).comap ψz.toMonoidHom := by rw [hψ]; exact hx
    exact ⟨ψz x, this, rfl⟩
  have hSc : ∀ x ∈ S, z * x = x * z := by
    intro x hx
    obtain ⟨c, hcdef⟩ : ∃ c : Y, c = z * x * z⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hcS : c ∈ S := hcdef ▸ S.mul_mem (hSz x hx) (S.inv_mem hx)
    have hcker : c ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv,
        hzU _ (hSU ▸ Subgroup.mem_map_of_mem φ hx)]
      group
    have hcc : c ∈ Subgroup.center Y := hZ hcker
    have hzc : z * c * z⁻¹ = c := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.1 hcc z
    have hzx : z * x * z⁻¹ = c * x := by
      rw [hcdef]
      exact (inv_mul_cancel_right _ _).symm
    have hx2 : x = c * c * x := by
      calc x = (z * z) * x * (z * z)⁻¹ := by rw [← sq, hz2]; simp
        _ = z * (z * x * z⁻¹) * z⁻¹ := by group
        _ = z * (c * x) * z⁻¹ := by rw [hzx]
        _ = (z * c * z⁻¹) * (z * x * z⁻¹) := by group
        _ = c * (c * x) := by rw [hzc, hzx]
        _ = c * c * x := by rw [mul_assoc]
    have hc2 : c ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_right.1 hx2.symm
    obtain ⟨m, hm⟩ := hSp ⟨c, hcS⟩
    have hcm : c ^ p ^ m = 1 := congrArg Subtype.val hm
    have hcop : Nat.Coprime (p ^ m) 2 :=
      Nat.Coprime.pow_left m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hord : orderOf c = 1 := by
      have h1 : orderOf c ∣ p ^ m := orderOf_dvd_of_pow_eq_one hcm
      have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
      exact (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
    have hc1 : c = 1 := orderOf_eq_one_iff.1 hord
    have hzx1 : z * x * z⁻¹ = x := by rw [hzx, hc1, one_mul]
    calc z * x = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [hzx1]
  let ψ : S →* U := (φ.comp S.subtype).codRestrict U fun x => hSU ▸ Subgroup.mem_map_of_mem φ x.2
  have hψs : Function.Surjective ψ := fun u => by
    have hu : (u : X) ∈ S.map φ := by rw [hSU]; exact u.2
    obtain ⟨x, hx, hxu⟩ := hu
    exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
  have hker' : ψ.ker ≤ Subgroup.center S := fun x hx => by
    have hxk : ((x : S) : Y) ∈ φ.ker := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ hxk) w)
  have e := QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  have hel : IsElementaryAbelian p (S ⧸ ψ.ker) :=
    isElementaryAbelian_of_mulEquiv_lift e.symm hU
  have hcard : Nat.card (S ⧸ ψ.ker) = p ^ k := by rw [Nat.card_congr e.toEquiv]; exact hUcard
  have hrank4 : 4 ≤ pRank p S := by
    by_contra hlt
    have h5 := central_elementary_odd_quotient_rank_three_bound hp hp2 (F := S)
      (by omega) ψ.ker hker' k hel hcard
    omega
  obtain ⟨A, hA, hAcard⟩ := exists_isElementaryAbelian_card_pRank (p := p) hp.one_lt (H := S)
  refine ⟨z, hz2, hz1, A.map S.subtype, ?_, ?_, pRank p S, hrank4, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hSc x x.2).symm
  · exact IsElementaryAbelian.map_subtype (H := A)
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hAcard]

theorem le_localRank_of_rank_four_witness {G : Type*} [Group G] [Finite G] {Y : Subgroup G}
    {p : ℕ} (hp : 1 < p) (hw : ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.centralizer {z} ∧ IsElementaryAbelian p V ∧ ∃ r : ℕ, 4 ≤ r ∧
        Nat.card V = p ^ r) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
  obtain ⟨z, hz2, hz1, V, hVz, hV, r, hr, hcard⟩ := hw
  exact hr.trans (CFSG.RankThree.Classical.le_localRank_of_witness hp ⟨z, hz2, hz1, V, hVz,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p V).1 hV, hcard⟩)

end CFSG.RankThree.PartOne
