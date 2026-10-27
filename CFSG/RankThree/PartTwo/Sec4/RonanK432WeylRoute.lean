module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Subgroup
open scoped Pointwise

theorem notMem_or_notMem_zpowers {S : Type} [Group S] [Finite S] {a b z : S} (ha : orderOf a = 3)
    (hz : orderOf z = 3) (hb : b ∉ zpowers a) : a ∉ zpowers z ∨ b ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨haz, hbz⟩ := hcon
  have hle : zpowers a ≤ zpowers z := zpowers_le.mpr haz
  have hcard : Nat.card (zpowers z) ≤ Nat.card (zpowers a) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hz, ha]
  have heq : zpowers a = zpowers z := Subgroup.eq_of_le_of_card_ge hle hcard
  exact hb (heq ▸ hbz)

theorem exists_commute_of_E9 {S : Type} [Group S] [Finite S] {x0 y0 : S} (hx0 : orderOf x0 = 3)
    (hy0 : y0 ^ 3 = 1) (hc0 : x0 * y0 = y0 * x0) (hn0 : y0 ∉ zpowers x0) {z : S}
    (hz : orderOf z = 3) : ∃ y : S, y ^ 3 = 1 ∧ z * y = y * z ∧ y ∉ zpowers z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy01 : y0 ≠ 1 := fun h => hn0 (h ▸ one_mem _)
  have hy0o : orderOf y0 = 3 := orderOf_eq_prime hy0 hy01
  have hx03 : x0 ^ 3 = 1 := by rw [← hx0]; exact pow_orderOf_eq_one x0
  have hEcard : Nat.card (zpowers x0 ⊔ zpowers y0 : Subgroup S) = 9 := by
    have hxe : CFSG.Assembly.IsElemAbelian 3 (zpowers x0) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx03, one_zpow]
    have hcomm : ∀ a ∈ zpowers x0, a * y0 = y0 * a := by
      intro a ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute x0 y0 from hc0) k).eq
    obtain ⟨-, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hxe hn0 hy0 hcomm
    rw [hcard, Nat.card_zpowers, hx0]
  have hEp : IsPGroup 3 (zpowers x0 ⊔ zpowers y0 : Subgroup S) :=
    IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hzp : IsPGroup 3 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; simp)
  obtain ⟨P, hzP⟩ := hzp.exists_le_sylow
  obtain ⟨P1, hEP1⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P1 P
  have hconj : ∀ x ∈ (P1 : Subgroup S), g * x * g⁻¹ ∈ (P : Subgroup S) := by
    intro x hx
    have h1 : (P : Subgroup S) = (g • P1 : Sylow 3 S) := by rw [hg]
    rw [h1, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
  have hx0P : g * x0 * g⁻¹ ∈ (P : Subgroup S) :=
    hconj x0 (hEP1 (mem_sup_left (mem_zpowers x0)))
  have hy0P : g * y0 * g⁻¹ ∈ (P : Subgroup S) :=
    hconj y0 (hEP1 (mem_sup_right (mem_zpowers y0)))
  have hzmem : z ∈ (P : Subgroup S) := hzP (mem_zpowers z)
  have hx0'o : orderOf (g * x0 * g⁻¹) = 3 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x0
    rw [hx0] at this
    simpa using this
  have hy0'3 : (g * y0 * g⁻¹) ^ 3 = 1 := by
    rw [show (g * y0 * g⁻¹) ^ 3 = g * y0 ^ 3 * g⁻¹ by simp [conj_pow], hy0]; group
  have hx0'3 : (g * x0 * g⁻¹) ^ 3 = 1 := by
    rw [show (g * x0 * g⁻¹) ^ 3 = g * x0 ^ 3 * g⁻¹ by simp [conj_pow], hx03]; group
  have hn0' : g * y0 * g⁻¹ ∉ zpowers (g * x0 * g⁻¹) := by
    intro hmem
    apply hn0
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : (g * x0 * g⁻¹) ^ k = g * x0 ^ k * g⁻¹ := by simp [conj_zpow]
    rw [h1] at hk
    have := congrArg (fun t => g⁻¹ * t * g) hk
    simpa [mul_assoc] using this
  by_cases hzc : ∀ q ∈ (P : Subgroup S), q * z = z * q
  ·
    rcases notMem_or_notMem_zpowers hx0'o hz hn0' with h | h
    · exact ⟨g * x0 * g⁻¹, hx0'3, (hzc _ hx0P).symm, h⟩
    · exact ⟨g * y0 * g⁻¹, hy0'3, (hzc _ hy0P).symm, h⟩
  ·
    haveI : Nontrivial (P : Subgroup S) := ⟨⟨⟨z, hzmem⟩, 1, fun h => by
      have : z = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hz; omega⟩⟩
    haveI : Finite (P : Subgroup S) := inferInstance
    haveI := (P.isPGroup').center_nontrivial
    have hZp : IsPGroup 3 (Subgroup.center (P : Subgroup S)) := (P.isPGroup').to_subgroup _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : 1 < Nat.card (Subgroup.center (P : Subgroup S)) := Finite.one_lt_card
      rw [hn] at h1
      simp at h1
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (P : Subgroup S)) 3
      (by rw [hn]; exact dvd_pow_self 3 hn0)
    have hcP : ((c : (P : Subgroup S)) : S) ∈ (P : Subgroup S) := (c : (P : Subgroup S)).2
    have hcc : ∀ q ∈ (P : Subgroup S), q * ((c : (P : Subgroup S)) : S) =
        ((c : (P : Subgroup S)) : S) * q := by
      intro q hq
      have := Subgroup.mem_center_iff.mp c.2 ⟨q, hq⟩
      exact congrArg Subtype.val this
    have hco : orderOf ((c : (P : Subgroup S)) : S) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hc
    refine ⟨((c : (P : Subgroup S)) : S), ?_, ?_, ?_⟩
    · have := pow_orderOf_eq_one ((c : (P : Subgroup S)) : S)
      rwa [hco] at this
    · exact hcc z hzmem
    · intro hmem
      apply hzc
      have hz_in : z ∈ zpowers ((c : (P : Subgroup S)) : S) := by
        have hle : zpowers ((c : (P : Subgroup S)) : S) ≤ zpowers z := zpowers_le.mpr hmem
        have hcard : Nat.card (zpowers z) ≤ Nat.card (zpowers ((c : (P : Subgroup S)) : S)) := by
          rw [Nat.card_zpowers, Nat.card_zpowers, hz, hco]
        exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ mem_zpowers z
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz_in
      intro q hq
      rw [← hk]
      exact (Commute.zpow_right (show Commute q ((c : (P : Subgroup S)) : S) from hcc q hq) k).eq

open CFSG.RankThree.PartTwo.Sec4.Item424Res5 in
theorem exists_weyl_of_cover {X : Type*} [Group X] {Y : Type*} [Group Y] [Finite Y] (π : Y →* X)
    (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, z ^ 4 = 1)
    (hY : ∀ E : Subgroup Y, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → ∃ g : Y, (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
        ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹)
    {D : Subgroup X} (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) :
    ∃ g : X, (∀ x ∈ D, g * x * g⁻¹ ∈ D) ∧ ∀ x ∈ D, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop := not_three_dvd_card_ker π hker
  have hDp : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hDexp x x.2)⟩
  obtain ⟨E, hEmap, hEdis⟩ :=
    CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hcop D hDp
  have hEmem : ∀ x ∈ E, π x ∈ D := fun x hx => hEmap ▸ ⟨x, hx, rfl⟩
  have hDE : ∀ x ∈ D, ∃ e ∈ E, π e = x := fun x hx => by
    rw [← hEmap] at hx
    exact hx
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hDcomm _ (hEmem a ha) _ (hEmem b hb)]
      group
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.disjoint_def.mp hEdis hc hk)
  have hEexp : ∀ a ∈ E, a ^ 3 = 1 := by
    intro a ha
    have hk : a ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hDexp _ (hEmem a ha)
    exact Subgroup.disjoint_def.mp hEdis (E.pow_mem ha 3) hk
  have hEcard : Nat.card E = 9 := by
    let fπ : E →* D := (π.comp E.subtype).codRestrict D (fun x => hEmem x.1 x.2)
    have hfπsurj : Function.Surjective fπ := by
      intro e
      obtain ⟨x, hx, hxe⟩ := hDE e e.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have hfπinj : Function.Injective fπ := by
      intro x y hxy
      have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
      have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3' : x.1⁻¹ * y.1 = 1 :=
        Subgroup.disjoint_def.mp hEdis (E.mul_mem (E.inv_mem x.2) y.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3')
    rw [← hD9]
    exact Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  obtain ⟨g, hgE, hg2⟩ := hY E hEcomm hEexp hEcard
  refine ⟨π g, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hDE x hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hEmem _ (hgE e he)
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hDE x hx
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, hg2 e he, map_inv]

theorem not_weaklyClosed_of_weyl {X : Type} [Group X] {D : Subgroup X}
    (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {g z : X} (hz : orderOf z = 3) (hzD : z ∈ D)
    (hg : ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hg2 : ∀ x ∈ D, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹) :
    ¬ WeaklyClosed (zpowers z) := by
  refine not_weaklyClosed_of_commute_conj (g := g) (hDcomm _ (hg z hzD) z hzD) ?_
  intro hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hcalc : g ^ 2 * z * (g ^ 2)⁻¹ = z ^ (k * k) := by
    have e1 : g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    have e2 : g * (z ^ k) * g⁻¹ = (g * z * g⁻¹) ^ k := conj_zpow.symm
    rw [e1, ← hk, e2, ← hk, ← zpow_mul]
  have h2 : z ^ (k * k) = z⁻¹ := hcalc.symm.trans (hg2 z hzD)
  have h3 : z ^ (k * k + 1) = 1 := by
    rw [zpow_add_one, h2, inv_mul_cancel]
  have h4 : (orderOf z : ℤ) ∣ k * k + 1 := orderOf_dvd_iff_zpow_eq_one.mpr h3
  rw [hz] at h4
  have h5 : (((k * k + 1 : ℤ)) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h4)
  push_cast at h5
  have h6 : ∀ x : ZMod 3, x * x + 1 ≠ 0 := by decide
  exact h6 _ h5

theorem listRow_of_cover_weyl {X : Type} [Group X] [Finite X] {Y : Type*} [Group Y] [Finite Y]
    (π : Y →* X) (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, z ^ 4 = 1)
    (hY : ∀ E : Subgroup Y, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → ∃ g : Y, (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
        ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹)
    {x0 y0 : X} (hx0 : orderOf x0 = 3) (hy0 : y0 ^ 3 = 1) (hc0 : x0 * y0 = y0 * x0)
    (hn0 : y0 ∉ zpowers x0) : ListRow X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  obtain ⟨y, hy3, hzy, hyn⟩ := exists_commute_of_E9 hx0 hy0 hc0 hn0 hz
  have hz3 : z ^ 3 = 1 := by have := pow_orderOf_eq_one z; rwa [hz] at this
  have hze : CFSG.Assembly.IsElemAbelian 3 (zpowers z) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hcomm : ∀ a ∈ zpowers z, a * y = y * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (show Commute z y from hzy) k).eq
  obtain ⟨hDab, hDcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hze hyn hy3 hcomm
  have hD9 : Nat.card (zpowers z ⊔ zpowers y : Subgroup X) = 9 := by
    rw [hDcard, Nat.card_zpowers, hz]
  haveI : IsMulCommutative (zpowers z ⊔ zpowers y : Subgroup X) := hDab.1
  have hDcomm : ∀ x ∈ (zpowers z ⊔ zpowers y : Subgroup X), ∀ w ∈ (zpowers z ⊔ zpowers y : Subgroup X),
      x * w = w * x := fun x hx w hw =>
    Subgroup.mul_comm_of_mem_isMulCommutative _ hx hw
  obtain ⟨g, hg, hg2⟩ := exists_weyl_of_cover π hπ hker hY hDcomm hDab.2 hD9
  exact not_weaklyClosed_of_weyl hDcomm hz (mem_sup_left (mem_zpowers z)) hg hg2

end CFSG.RankThree.PartTwo.Sec4.RonanK432
