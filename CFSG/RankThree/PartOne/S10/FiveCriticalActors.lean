module

public import CFSG.RankThree.PartOne.S10.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem card_eq_sq_of_relIndex_eq_prime [Finite G] {p : ℕ} (hp : p.Prime) {A E : Subgroup G}
    (hAcard : Nat.card A = p ^ 3) (hEA : E ≤ A) (hrel : E.relIndex A = p) :
    Nat.card E = p ^ 2 := by
  have h1 := (E.subgroupOf A).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hAcard] at h1
  change E.relIndex A * Nat.card E = p ^ 3 at h1
  rw [hrel] at h1
  have h2 : p * (p ^ 2) = p * Nat.card E := by rw [h1]; ring
  exact (Nat.eq_of_mul_eq_mul_left hp.pos h2).symm

theorem exists_mul_of_mem_of_relIndex_eq_prime [Finite G] {p : ℕ} (hp : p.Prime)
    {A E : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hEA : E ≤ A)
    (hrel : E.relIndex A = p) {a : G} (ha : a ∈ A) (haE : a ∉ E) :
    A ≤ E ⊔ zpowers a ∧ ∀ x ∈ A, ∃ e ∈ E, ∃ y ∈ zpowers a, x = e * y := by
  have hAK : A ≤ E ⊔ zpowers a := by
    set K := E ⊔ zpowers a with hK
    have hEK : E ≤ K := le_sup_left
    have hKA : K ≤ A := sup_le hEA (Subgroup.zpowers_le.mpr ha)
    have hmul := Subgroup.relIndex_mul_relIndex E K A hEK hKA
    rw [hrel] at hmul
    have hdvd : E.relIndex K ∣ p := ⟨K.relIndex A, hmul.symm⟩
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      exact haE ((Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
    · rw [h1] at hmul
      have h2 : K.relIndex A = 1 := by
        have := hp.pos
        nlinarith
      exact Subgroup.relIndex_eq_one.mp h2
  refine ⟨hAK, fun x hx => ?_⟩
  have hnorm : E ≤ normalizer (zpowers a : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute a e from hcomm a ha e (hEA he)) n).eq)
  have hx' : x ∈ (E : Set G) * (zpowers a : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E (zpowers a) hnorm]
    exact hAK hx
  obtain ⟨e, he, y, hy, hxy⟩ := hx'
  exact ⟨e, he, y, hy, hxy.symm⟩

theorem five_actors [Finite G] {A E R D : Subgroup G} (hAe : IsElementaryAbelian 5 A)
    (hEA : E ≤ A) (hrel : E.relIndex A = 5) (hker : A ⊓ centralizer (R : Set G) = E)
    (hAR : A ≤ normalizer (R : Set G)) (hAD : A ≤ normalizer (D : Set G)) (hRA : ⁅R, A⁆ = R)
    {a b : G} (ha : a ∈ A) (haE : a ∉ E) (hbE : b ∈ E) (hb1 : b ≠ 1) :
    Nat.card (zpowers a) = 5 ∧ Nat.card ↥(fiveActorPlane a b) = 25 ∧
    zpowers a ≤ fiveActorPlane a b ∧ fiveActorPlane a b ≤ A ∧
    fiveActorPlane a b ≤ normalizer (R : Set G) ⊓ normalizer (D : Set G) ∧
    ⁅R, zpowers a⁆ = R ∧ ⁅R, fiveActorPlane a b⁆ = R ∧
    fiveActorPlane a b ⊓ centralizer (R : Set G) = zpowers b ∧
    ∀ U : Subgroup G, U ≤ R →
      (A ≤ normalizer (U : Set G) ↔ fiveActorPlane a b ≤ normalizer (U : Set G)) ∧
      (A ≤ normalizer (U : Set G) ↔ zpowers a ≤ normalizer (U : Set G)) ∧
      (A ≤ normalizer (U : Set G) →
        ⁅U, A⁆ = ⁅U, fiveActorPlane a b⁆ ∧ ⁅U, A⁆ = ⁅U, zpowers a⁆) := by
  classical
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have ha1 : a ≠ 1 := fun h => haE (h ▸ E.one_mem)
  have ha5 : orderOf a = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hacard : Nat.card (zpowers a) = 5 := by rw [Nat.card_zpowers, ha5]
  have hbA : b ∈ A := hEA hbE
  have hb5 : orderOf b = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hbA) hb1
  have hbcard : Nat.card (zpowers b) = 5 := by rw [Nat.card_zpowers, hb5]
  have hbleE : zpowers b ≤ E := Subgroup.zpowers_le.mpr hbE
  have hEa : E ⊓ zpowers a = ⊥ :=
    GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card E (zpowers a)
      (by rw [hacard]; exact hp5) (fun h => haE (h (Subgroup.mem_zpowers a)))
  have hab : Commute a b := hcomm a ha b hbA
  have hbnorm : zpowers b ≤ normalizer (zpowers a : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hab.zpow_zpow m n).eq)
  have hdisj : Disjoint (zpowers a) (zpowers b) := by
    rw [Subgroup.disjoint_def]
    intro x hxa hxb
    have hx : x ∈ E ⊓ zpowers a := ⟨hbleE hxb, hxa⟩
    rw [hEa] at hx
    exact Subgroup.mem_bot.mp hx
  have hFcard : Nat.card ↥(fiveActorPlane a b) = 25 := by
    unfold fiveActorPlane
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hbnorm hdisj, hacard,
      hbcard]
  have hFA : fiveActorPlane a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hbA)
  have hCE : ∀ e ∈ E, e ∈ centralizer (R : Set G) := fun e he => by
    rw [← hker] at he
    exact he.2
  have hEact : ∀ e ∈ E, ∀ r ∈ R, r * e = e * r := fun e he r hr =>
    Subgroup.mem_centralizer_iff.mp (hCE e he) r hr
  obtain ⟨hAK, hdecomp⟩ := exists_mul_of_mem_of_relIndex_eq_prime hp5 hcomm hEA hrel ha haE
  have hzA : zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hUA : ∀ U : Subgroup G, U ≤ R → A ≤ normalizer (U : Set G) →
      ⁅U, A⁆ ≤ ⁅U, zpowers a⁆ := by
    intro U hUR hAU
    rw [Subgroup.commutator_le]
    intro u hu x hx
    obtain ⟨e, he, y, hy, rfl⟩ := hdecomp x hx
    have hyA : y ∈ A := hzA hy
    have hw : y * u⁻¹ * y⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hAU hyA) u⁻¹).mp (U.inv_mem hu)
    have h1 : e * u = u * e := (hEact e he u (hUR hu)).symm
    have h2 : e * (y * u⁻¹ * y⁻¹) = (y * u⁻¹ * y⁻¹) * e := (hEact e he _ (hUR hw)).symm
    have hc : e * (u * (y * u⁻¹ * y⁻¹)) = (u * (y * u⁻¹ * y⁻¹)) * e :=
      (Commute.mul_right (show Commute e u from h1) (show Commute e (y * u⁻¹ * y⁻¹) from h2)).eq
    have e3 : ⁅u, e * y⁆ = ⁅u, y⁆ := by
      simp only [commutatorElement_def]
      calc u * (e * y) * u⁻¹ * (e * y)⁻¹ = (u * e) * (y * u⁻¹ * y⁻¹) * e⁻¹ := by group
        _ = e * (u * (y * u⁻¹ * y⁻¹)) * e⁻¹ := by rw [← h1]; group
        _ = u * (y * u⁻¹ * y⁻¹) := by rw [mul_inv_eq_iff_eq_mul, hc]
        _ = u * y * u⁻¹ * y⁻¹ := by group
    rw [e3]
    exact Subgroup.commutator_mem_commutator hu hy
  have hUA' : ∀ U : Subgroup G, U ≤ R → A ≤ normalizer (U : Set G) →
      ⁅U, A⁆ = ⁅U, zpowers a⁆ := fun U hUR hAU =>
    le_antisymm (hUA U hUR hAU) (Subgroup.commutator_mono le_rfl hzA)
  have hUF : ∀ U : Subgroup G, U ≤ R → A ≤ normalizer (U : Set G) →
      ⁅U, A⁆ = ⁅U, fiveActorPlane a b⁆ := fun U hUR hAU =>
    le_antisymm ((hUA U hUR hAU).trans (Subgroup.commutator_mono le_rfl le_sup_left))
      (Subgroup.commutator_mono le_rfl hFA)
  have hNU : ∀ U : Subgroup G, U ≤ R → zpowers a ≤ normalizer (U : Set G) →
      A ≤ normalizer (U : Set G) := by
    intro U hUR hau
    refine hAK.trans (sup_le ?_ hau)
    intro e he
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun u hu => hEact e he u (hUR hu))
  have hFzF : zpowers a ≤ fiveActorPlane a b := le_sup_left
  refine ⟨hacard, hFcard, hFzF, hFA, le_inf (hFA.trans hAR) (hFA.trans hAD), ?_, ?_, ?_,
    fun U hUR => ⟨⟨fun h => hFA.trans h, fun h => hNU U hUR (hFzF.trans h)⟩,
      ⟨fun h => hzA.trans h, hNU U hUR⟩, fun h => ⟨hUF U hUR h, hUA' U hUR h⟩⟩⟩
  · rw [← hUA' R le_rfl hAR, hRA]
  · rw [← hUF R le_rfl hAR, hRA]
  · apply le_antisymm
    · rintro x ⟨hxF, hxC⟩
      have hxE : x ∈ E := by
        rw [← hker]
        exact ⟨hFA hxF, hxC⟩
      have hx' : x ∈ (zpowers a : Set G) * (zpowers b : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (zpowers a) (zpowers b) hbnorm]
        exact hxF
      obtain ⟨y, hy, z, hz, rfl⟩ := hx'
      have hyE : y ∈ E := by
        have h := E.mul_mem hxE (E.inv_mem (hbleE hz))
        rwa [mul_inv_cancel_right] at h
      have hy1 : y = 1 := by
        have h : y ∈ E ⊓ zpowers a := ⟨hyE, hy⟩
        rw [hEa] at h
        exact Subgroup.mem_bot.mp h
      show y * z ∈ zpowers b
      rw [hy1, one_mul]
      exact hz
    · exact le_inf le_sup_right (Subgroup.zpowers_le.mpr (hCE b hbE))

end CFSG.RankThree.PartOne.FiveCritical
