module

public import CFSG.Quasithin.EmptyFaithful.E22PL2PglA
public import CFSG.Quasithin.Background.E1Defs
import CFSG.GroupTheory.SolvableTransport
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.EmptyFaithful.E22PTor

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.GorensteinWalter
open scoped Pointwise commutatorElement
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange outerTorusOrder
  outerTorusOrder_mod_four six_le_outerTorusOrder outer_involution_centralizer
  zpowers_le_normalizer_of_inverting odd_card_of_isOddPrimePower)

theorem e22pl2pgl_mem_zpowers_involution {G : Type*} [Group G] {w x : G} (hw : w * w = 1)
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, hw2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, hw2, one_zpow, one_mul, zpow_one]

theorem e22pl2pgl_involution_unique {G : Type*} [Group G] {U : Subgroup G} [Finite U]
    (hU : IsCyclic ↥U) {x y : G} (hx : x ∈ U) (hy : y ∈ U) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have := Fintype.ofFinite ↥U
  have h2 := hU.card_pow_eq_one_le (n := 2) (by norm_num)
  have hsub : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset ↥U) ⊆ Finset.univ.filter fun a : ↥U => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simpa using hx2)
    · exact Subtype.ext (by simpa using hy2)
  have h3 := Finset.card_le_card hsub
  have hne1 : (1 : ↥U) ≠ ⟨x, hx⟩ := fun h => hx1 (congrArg Subtype.val h).symm
  have hne2 : (1 : ↥U) ≠ ⟨y, hy⟩ := fun h => hy1 (congrArg Subtype.val h).symm
  have hne3 : (⟨x, hx⟩ : ↥U) ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
  rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
    Finset.card_insert_of_notMem (by simpa using hne3), Finset.card_singleton] at h3
  omega

theorem e22pl2pgl_exists_odd_prime {n : ℕ} (h4 : n % 4 = 2) (h6 : 6 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ n := by
  obtain ⟨c, rfl⟩ : ∃ c, n = 2 * c := ⟨n / 2, by omega⟩
  obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  refine ⟨r, hr, ?_, Dvd.dvd.mul_left hrc 2⟩
  rintro rfl
  omega

theorem e22pl2pgl_outer_member_eOne {K : Type} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {T A : Subgroup (PGL2 K)}
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 4)
    (hO2 : pCoreOf 2 (⊤ : Subgroup (PGL2 K)) = ⊥) {z : PGL2 K} (hzA : z ∈ A)
    (hz2 : orderOf z = 2) (hzJ : z ∈ pslRange K) (hAJ : ¬ A ≤ pslRange K) :
    ∃ I : Subgroup (PGL2 K), IsE 1 ⊤ T A I ∧ EOne ↥I (A.subgroupOf I) ∧
      ¬ I ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
  haveI := e22pl2pgl_finite K
  obtain ⟨b, hbA, hbJ⟩ : ∃ b ∈ A, b ∉ pslRange K := by
    by_contra h
    push Not at h
    exact hAJ h
  have hb2' : b ^ 2 = 1 := hA.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbJ (h ▸ (pslRange K).one_mem)
  have hb2 : orderOf b = 2 := orderOf_eq_prime hb2' hb1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  obtain ⟨U, w, hUc, hUcard, hbU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hodd hcard hb2' hbJ
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set (PGL2 K)) :=
    zpowers_le_normalizer_of_inverting hww hwinv
  have hzb : b * z = z * b := by
    have := hA.1.is_comm.comm (⟨b, hbA⟩ : ↥A) ⟨z, hzA⟩
    exact congrArg Subtype.val this
  have hzC : z ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact hzb.symm
  have hzmul : z ∈ (U : Set (PGL2 K)) * (Subgroup.zpowers w : Set (PGL2 K)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U _ hnorm]
    exact hzC
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hzmul
  have hzU : z ∉ U := by
    intro hzU
    exact hbJ ((e22pl2pgl_involution_unique hUc hzU hbU hz2' hb2' hz1 hb1) ▸ hzJ)
  have hvw : v = w := by
    rcases e22pl2pgl_mem_zpowers_involution hww hv with h | h
    · exfalso
      apply hzU
      rw [← huv, h, mul_one]
      exact hu
    · exact h
  subst hvw
  have hzinv : ∀ x ∈ U, z * x * z⁻¹ = x⁻¹ := by
    intro x hx
    rw [← huv]
    have h1 : u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
    rw [h1, hwinv x hx]
    have h2 := hUcomm u hu x⁻¹ (U.inv_mem hx)
    calc u * x⁻¹ * u⁻¹ = x⁻¹ * u * u⁻¹ := by rw [h2]
      _ = x⁻¹ := by group
  have hbU' : ∀ x ∈ U, b * x = x * b := fun x hx => hUcomm b hbU x hx
  have hab : z ∉ Subgroup.zpowers b := by
    intro hzb'
    rcases e22pl2pgl_mem_zpowers_involution (by rw [← sq]; exact hb2') hzb' with h | h
    · exact hz1 h
    · exact hbJ (h ▸ hzJ)
  have hτ : tauOf ⊤ T A ≤ Subgroup.normalizer (U : Set (PGL2 K)) := by
    intro t ht
    have hcomm : ⁅t, b⁆ = 1 := by
      have := ht.2.2 b hbA
      rwa [hO2, Subgroup.mem_bot] at this
    have htb : t * b = b * t := by
      have h1 : t * b * t⁻¹ * b⁻¹ = 1 := hcomm
      calc t * b = (t * b * t⁻¹ * b⁻¹) * (b * t) := by group
        _ = b * t := by rw [h1, one_mul]
    have htC : t ∈ Subgroup.centralizer ({b} : Set (PGL2 K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr htb
    rw [hC] at htC
    exact (sup_le Subgroup.le_normalizer hnorm) htC
  have hqodd := odd_card_of_isOddPrimePower hodd
  have h5 : 5 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  obtain ⟨r, hr, hr2, hrU⟩ := e22pl2pgl_exists_odd_prime (n := Nat.card U)
    (by rw [hUcard]; exact outerTorusOrder_mod_four hqodd)
    (by rw [hUcard]; exact six_le_outerTorusOrder hqodd h5)
  obtain ⟨P₀, hP₀U, -, -, hP₀, hnc⟩ := isE_one_of_odd_torus hT hAT hA hAcard hbA hzA hb2 hab hUc hbU'
    hzinv hτ hr hr2 hrU
  have hUsolv : Group.IsSolvable ↥U :=
    Group.isSolvable_of_comm fun x y => Subtype.ext (hUcomm x x.2 y y.2)
  have hUτsolv : Group.IsSolvable ↥(U ⊔ tauOf ⊤ T A) :=
    CFSG.GroupTheory.isSolvable_sup_of_isPGroup_of_le_normalizer hUsolv
      (hT.isPGroup.to_le (tauOf_le ⊤ T A)) hτ
  haveI : Group.IsSolvable ↥(U ⊔ tauOf ⊤ T A) := hUτsolv
  have hP₀τle : P₀ ⊔ tauOf ⊤ T A ≤ U ⊔ tauOf ⊤ T A :=
    sup_le (hP₀U.trans le_sup_left) le_sup_right
  haveI : Group.IsSolvable ↥((P₀ ⊔ tauOf ⊤ T A).subgroupOf (U ⊔ tauOf ⊤ T A)) :=
    inferInstance
  have hsolv : Group.IsSolvable ↥(P₀ ⊔ tauOf ⊤ T A) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hP₀τle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hP₀τle).symm.injective
  have hE : EOne ↥(P₀ ⊔ tauOf ⊤ T A) (A.subgroupOf (P₀ ⊔ tauOf ⊤ T A)) :=
    (CFSG.Quasithin.E1.isE_eOne_of_isSolvable hP₀ hsolv).1
  exact ⟨P₀ ⊔ tauOf ⊤ T A, hP₀, hE, fun h => hnc (le_sup_left.trans h)⟩

theorem e22pl2pgl_outer_member {K : Type} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {T A : Subgroup (PGL2 K)}
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 4)
    (hO2 : pCoreOf 2 (⊤ : Subgroup (PGL2 K)) = ⊥) {z : PGL2 K} (hzA : z ∈ A)
    (hz2 : orderOf z = 2) (hzJ : z ∈ pslRange K) (hAJ : ¬ A ≤ pslRange K) :
    ∃ P : Subgroup (PGL2 K), IsE 1 ⊤ T A P ∧ ¬ P ≤ Subgroup.centralizer ({z} : Set (PGL2 K)) := by
  obtain ⟨P, hP, -, hnc⟩ :=
    e22pl2pgl_outer_member_eOne hodd hcard hT hAT hA hAcard hO2 hzA hz2 hzJ hAJ
  exact ⟨P, hP, hnc⟩

end CFSG.Quasithin.E22L2
