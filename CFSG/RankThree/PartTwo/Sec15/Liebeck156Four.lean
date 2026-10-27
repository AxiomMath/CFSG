module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Quasithin.Recognition.HSTypeModels
import CFSG.RankThree.PartTwo.Sec21.Hering233iQ8D8
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwo
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfect_subgroup_le_perfectResidualOf perfectResidualOf_normalizer_contains)

section ModelFacts

private def ExtFacts (B : Type) [Group B] : Prop :=
  (∀ u v : B, u ∈ Subgroup.center B → v ∈ Subgroup.center B → u * u = 1 → v * v = 1 →
      u ≠ 1 → v ≠ 1 → u = v) ∧
    (∀ S : Subgroup B, S ⊓ Subgroup.center B = ⊥ → Nat.card S ≤ 4)

private theorem mem_zpowers_iff_of_mul_self_eq_one {G : Type*} [Group G] {z : G}
    (hz2 : z * z = 1) {n : G} : n ∈ Subgroup.zpowers z ↔ n = 1 ∨ n = z := by
  refine ⟨fun hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [zpow_eq_zpow_emod k (show z ^ (2 : ℤ) = 1 by rw [zpow_two, hz2])]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private theorem not_mem_of_inf_center {B : Type} [Group B] {S : Subgroup B} {z : B}
    (hz : z ∈ Subgroup.center B) (hz1 : z ≠ 1) (hS : S ⊓ Subgroup.center B = ⊥) : z ∉ S :=
  fun h => hz1 (Subgroup.mem_bot.mp (hS ▸ Subgroup.mem_inf.mpr ⟨h, hz⟩))

private theorem mem_of_mul_eq_mul_mul {B : Type} [Group B] {S : Subgroup B} {x y z : B}
    (hx : x ∈ S) (hy : y ∈ S) (h : x * y = y * x * z) : z ∈ S := by
  have : z = (y * x)⁻¹ * (x * y) := by rw [h, inv_mul_cancel_left]
  exact this ▸ S.mul_mem (S.inv_mem (S.mul_mem hy hx)) (S.mul_mem hx hy)

private theorem sq_eq_one_of_inf_center {B : Type} [Group B] {z : B}
    (hz : z ∈ Subgroup.center B) (hz1 : z ≠ 1) (hsq : ∀ x : B, x * x = 1 ∨ x * x = z)
    {S : Subgroup B} (hS : S ⊓ Subgroup.center B = ⊥) : ∀ x ∈ S, x * x = 1 :=
  fun x hx => (hsq x).resolve_right fun h =>
    not_mem_of_inf_center hz hz1 hS (h ▸ S.mul_mem hx hx)

private theorem comm_of_inf_center {B : Type} [Group B] {z : B}
    (hz : z ∈ Subgroup.center B) (hz1 : z ≠ 1)
    (hcomm : ∀ x y : B, x * y = y * x ∨ x * y = y * x * z) {S : Subgroup B}
    (hS : S ⊓ Subgroup.center B = ⊥) : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x :=
  fun _ hx _ hy => (hcomm _ _).resolve_right fun h =>
    not_mem_of_inf_center hz hz1 hS (mem_of_mul_eq_mul_mul hx hy h)

private theorem card_le_two {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ 1 → b ≠ 1 → a = b) : Nat.card S ≤ 2 := by
  classical
  have := Nat.card_le_card_of_injective (fun a : S => decide ((a : G) ≠ 1)) fun a b hab => ?_
  · simpa using this
  · by_cases ha : (a : G) = 1
    · have hb : (b : G) = 1 := by
        by_contra hb
        simp [ha, hb] at hab
      exact Subtype.ext (ha.trans hb.symm)
    · have hb : (b : G) ≠ 1 := by
        intro hb
        simp [ha, hb] at hab
      exact Subtype.ext (h a a.2 b b.2 ha hb)

private theorem two_mul_card_le {B : Type} [Group B] [Finite B] {z : B}
    (hz : z ∈ Subgroup.center B) (hz2 : z * z = 1) {S : Subgroup B} (hzS : z ∉ S)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) {m : ℕ}
    (hm : ∀ E : Subgroup B, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ m) : 2 * Nat.card S ≤ m := by
  have hzc : ∀ g : B, g * z = z * g := Subgroup.mem_center_iff.mp hz
  haveI : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
  have hcen : ∀ n : B, (n = 1 ∨ n = z) → ∀ g : B, Commute n g := by
    rintro n (rfl | rfl) g
    · exact Commute.one_left g
    · exact (hzc g).symm
  have hmem : ∀ x ∈ S ⊔ Subgroup.zpowers z, ∃ s ∈ S, ∃ n, (n = 1 ∨ n = z) ∧ s * n = x := by
    intro x hx
    obtain ⟨s, hs, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    exact ⟨s, hs, n, (mem_zpowers_iff_of_mul_self_eq_one hz2).mp hn, rfl⟩
  have hTc : ∀ x ∈ S ⊔ Subgroup.zpowers z, ∀ y ∈ S ⊔ Subgroup.zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨s, hs, n, hn, rfl⟩ := hmem x hx
    obtain ⟨t, ht, k, hk, rfl⟩ := hmem y hy
    exact (Commute.mul_right (hcomm s hs t ht) (hcen k hk s).symm).mul_left
      ((hcen n hn t).mul_right (hcen n hn k))
  have hTsq : ∀ x ∈ S ⊔ Subgroup.zpowers z, x * x = 1 := by
    intro x hx
    obtain ⟨s, hs, n, hn, rfl⟩ := hmem x hx
    have hn2 : n * n = 1 := by
      rcases hn with rfl | rfl
      · exact one_mul 1
      · exact hz2
    calc s * n * (s * n) = s * (n * s) * n := by group
      _ = s * (s * n) * n := by rw [(hcen n hn s).eq]
      _ = s * s * (n * n) := by group
      _ = 1 := by rw [hsq s hs, hn2, one_mul]
  have hzT : z ∈ S ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have h1 := Subgroup.relIndex_mul_card S (S ⊔ Subgroup.zpowers z)
  rw [inf_of_le_left le_sup_left] at h1
  have h2 : S.relIndex (S ⊔ Subgroup.zpowers z) ≠ 1 := fun h =>
    hzS (Subgroup.relIndex_eq_one.mp h hzT)
  have h3 : S.relIndex (S ⊔ Subgroup.zpowers z) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact (Nat.card_pos (α := ↥(S ⊔ Subgroup.zpowers z))).ne' h1.symm
  calc 2 * Nat.card S ≤ S.relIndex (S ⊔ Subgroup.zpowers z) * Nat.card S :=
        Nat.mul_le_mul_right _ (by omega)
    _ = Nat.card ↥(S ⊔ Subgroup.zpowers z) := h1
    _ ≤ m := hm _ hTc hTsq

private abbrev Pre := QuaternionGroup 2 × DihedralGroup 4

private abbrev κ : Pre := (QuaternionGroup.a 2, DihedralGroup.r 2)

private abbrev zq : Pre := (QuaternionGroup.a 2, 1)

private def inK (x : Pre) : Prop := x = 1 ∨ x = κ

private instance (x : Pre) : Decidable (inK x) := inferInstanceAs (Decidable (x = 1 ∨ x = κ))

private abbrev zb : Sec4.Q8D8 := QuotientGroup.mk zq

private theorem mem_q8D8Kernel_iff (x : Pre) : x ∈ Sec4.q8D8Kernel ↔ inK x :=
  mem_zpowers_iff_of_mul_self_eq_one (by decide)

private theorem mk_eq_mk_iff {a b : Pre} :
    (QuotientGroup.mk a : Sec4.Q8D8) = QuotientGroup.mk b ↔ inK (a⁻¹ * b) := by
  rw [QuotientGroup.eq, mem_q8D8Kernel_iff]

private theorem mk_eq_one_iff {a : Pre} : (QuotientGroup.mk a : Sec4.Q8D8) = 1 ↔ inK a := by
  rw [QuotientGroup.eq_one_iff, mem_q8D8Kernel_iff]

private theorem sq_lift : ∀ p : Pre, inK (p * p) ∨ inK ((p * p)⁻¹ * zq) := by decide

private theorem central_lift : ∀ p : Pre, (∀ q : Pre, inK ((q * p)⁻¹ * (p * q))) →
    inK p ∨ inK (zq⁻¹ * p) := by
  decide

private theorem zq_lift : ∀ q : Pre, inK ((q * zq)⁻¹ * (zq * q)) := by decide

private theorem invol_lift : ∀ p : Pre, inK (p * p) → ¬ inK p → ¬ inK (p⁻¹ * zq) →
    ∀ q : Pre, inK (q * q) → ¬ inK q → ¬ inK (q⁻¹ * zq) →
      inK (p * q) ∨ inK ((p * q)⁻¹ * zq) ∨ inK ((p * q)⁻¹ * (q * p * zq)) := by
  simp only [Prod.forall]
  decide

private theorem q8D8_sq (x : Sec4.Q8D8) : x * x = 1 ∨ x * x = zb := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_mul, mk_eq_one_iff, mk_eq_mk_iff]
  exact sq_lift p

private theorem q8D8_central {u : Sec4.Q8D8} (hu : u ∈ Subgroup.center Sec4.Q8D8) :
    u = 1 ∨ u = zb := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective u
  rw [Subgroup.mem_center_iff] at hu
  have h : ∀ q : Pre, inK ((q * p)⁻¹ * (p * q)) := fun q => by
    rw [← mk_eq_mk_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hu q
  rcases central_lift p h with h1 | h1
  · exact Or.inl (mk_eq_one_iff.mpr h1)
  · exact Or.inr (mk_eq_mk_iff.mpr h1).symm

private theorem zb_mem_center : zb ∈ Subgroup.center Sec4.Q8D8 := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff]
  exact zq_lift q

private theorem zb_ne_one : zb ≠ 1 := by
  rw [ne_eq, mk_eq_one_iff]
  decide

private theorem q8D8_invol (a b : Sec4.Q8D8) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (haz : a ≠ zb) (hb1 : b ≠ 1) (hbz : b ≠ zb) :
    a * b = 1 ∨ a * b = zb ∨ a * b = b * a * zb := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, mk_eq_one_iff] at ha2 hb2
  rw [ne_eq, mk_eq_one_iff] at ha1 hb1
  rw [ne_eq, mk_eq_mk_iff] at haz hbz
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_one_iff,
    mk_eq_mk_iff, mk_eq_mk_iff]
  exact invol_lift p ha2 ha1 haz q hb2 hb1 hbz

private theorem extFacts_q8D8 : ExtFacts Sec4.Q8D8 := by
  refine ⟨fun u v hu hv _ _ hu1 hv1 => ?_, fun S hS => ?_⟩
  · rw [(q8D8_central hu).resolve_left hu1, (q8D8_central hv).resolve_left hv1]
  · have hS2 := sq_eq_one_of_inf_center zb_mem_center zb_ne_one q8D8_sq hS
    have hzS := not_mem_of_inf_center zb_mem_center zb_ne_one hS
    have key : ∀ a ∈ S, ∀ b ∈ S, a ≠ 1 → b ≠ 1 → a = b := by
      intro a ha b hb ha1 hb1
      rcases q8D8_invol a b (hS2 a ha) (hS2 b hb) ha1 (fun h => hzS (h ▸ ha)) hb1
        (fun h => hzS (h ▸ hb)) with h | h | h
      · exact (mul_left_cancel (h.trans (hS2 a ha).symm)).symm
      · exact absurd (h ▸ S.mul_mem ha hb) hzS
      · exact absurd (mem_of_mul_eq_mul_mul ha hb h) hzS
    have := card_le_two S key
    omega

open CFSG.Quasithin.HSType (IsZ4Q8Q8 card_center_of_isZ4Q8Q8 card_le_eight_of_isZ4Q8Q8
  eq_of_central_of_isZ4Q8Q8 mul_comm_or_of_isZ4Q8Q8 sq_eq_of_isZ4Q8Q8)

private theorem isZ4Q8Q8 : IsZ4Q8Q8 Sec4.Z4Q8Q8 := ⟨MulEquiv.refl _⟩

private theorem extFacts_z4Q8Q8 : ExtFacts Sec4.Z4Q8Q8 := by
  refine ⟨fun u v hu hv hu2 hv2 hu1 hv1 => ?_, fun S hS => ?_⟩
  · exact eq_of_central_of_isZ4Q8Q8 isZ4Q8Q8 (fun w => (Subgroup.mem_center_iff.mp hu w).symm)
      hu2 hu1 (fun w => (Subgroup.mem_center_iff.mp hv w).symm) hv2 hv1
  · obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Sec4.Z4Q8Q8) 2
      (by rw [card_center_of_isZ4Q8Q8 isZ4Q8Q8]; norm_num)
    have hz2 : (c : Sec4.Z4Q8Q8) * c = 1 := by
      have h : c * c = 1 := by
        rw [← sq]
        exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hc)
      simpa using congrArg Subtype.val h
    have hz1 : (c : Sec4.Z4Q8Q8) ≠ 1 := fun h => by
      have : c = 1 := Subtype.ext h
      simp [this] at hc
    have hzc : ∀ g : Sec4.Z4Q8Q8, (c : Sec4.Z4Q8Q8) * g = g * c := fun g =>
      (Subgroup.mem_center_iff.mp c.2 g).symm
    have := two_mul_card_le c.2 hz2 (not_mem_of_inf_center c.2 hz1 hS)
      (comm_of_inf_center c.2 hz1 (mul_comm_or_of_isZ4Q8Q8 isZ4Q8Q8 hzc hz2 hz1) hS)
      (sq_eq_one_of_inf_center c.2 hz1 (sq_eq_of_isZ4Q8Q8 isZ4Q8Q8 hzc hz2 hz1) hS) (m := 8)
      fun E hE hE2 => card_le_eight_of_isZ4Q8Q8 isZ4Q8Q8 E hE hE2
    omega

end ModelFacts

section YInternal

variable {Y : Type} [Group Y]

private theorem le_center_of_card_le_four [Finite Y] (hYp : Group.IsPerfect Y)
    (N : Subgroup Y) [N.Normal] (h4 : Nat.card N ≤ 4) : N ≤ Subgroup.center Y := by
  let φ : Y →* Equiv.Perm N := (MulAut.toPerm N).comp (MulAut.conjNormal : Y →* MulAut N)
  haveI : Group.IsSolvable (Equiv.Perm N) := Equiv.Perm.isSolvable h4
  haveI : Group.IsSolvable (Y ⧸ φ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective φ)
  haveI := hYp
  have hker : φ.ker = ⊤ := Sec4.Census.eq_top_of_isSolvable_quotient inferInstance
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : φ g = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    trivial
  have h2 := congrArg (fun π : Equiv.Perm N => ((π ⟨n, hn⟩ : N) : Y)) h1
  have h3 : g * n * g⁻¹ = n := h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

private theorem mem_pCore_two_of_equiv (τ : Y ≃* Y) {y : Y} (hy : y ∈ CFSG.pCore 2 Y) :
    τ y ∈ CFSG.pCore 2 Y := by
  have hc := CFSG.LieType.BorelTits.pCore_characteristic (G := Y) 2
  have h : y ∈ (CFSG.pCore 2 Y).comap τ.toMonoidHom := by
    rw [hc.fixed τ]
    exact hy
  exact h

private theorem exists_inner_of_pow_three {ψ : MulAut (alternatingGroup (Fin 5))}
    (h3 : ∀ a, ψ (ψ (ψ a)) = a) : ∃ g : alternatingGroup (Fin 5), ∀ a, ψ a = g * a * g⁻¹ := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  obtain ⟨g, rfl⟩ := hb.2 ψ
  have hg3 : g ^ 3 = 1 := by
    apply hb.1
    rw [map_pow, map_one]
    refine MulEquiv.ext fun a => ?_
    exact h3 a
  have hsign : Equiv.Perm.sign g = 1 := by
    have h := congrArg Equiv.Perm.sign hg3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, fun a => ?_⟩
  apply Subtype.ext
  exact MulAut.conjNormal_apply g a

private theorem false_of_pCore_le_center (hYp : Group.IsPerfect Y)
    (eY : Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) (hR1 : CFSG.pCore 2 Y ≠ ⊥)
    (τ : Y ≃* Y) (hτ3 : ∀ y, τ (τ (τ y)) = y)
    (hfix : ∀ y ∈ CFSG.pCore 2 Y, τ y = y → y = 1)
    (hc : CFSG.pCore 2 Y ≤ Subgroup.center Y) : False := by
  haveI := hYp
  set R := CFSG.pCore 2 Y with hR
  have hRτ : R.map τ.toMonoidHom = R := by
    have hch := CFSG.LieType.BorelTits.pCore_characteristic (G := Y) 2
    exact Subgroup.characteristic_iff_map_eq.mp hch τ
  let τbar : Y ⧸ R ≃* Y ⧸ R := QuotientGroup.congr R R τ hRτ
  let π : Y →* alternatingGroup (Fin 5) := eY.toMonoidHom.comp (QuotientGroup.mk' R)
  have hπs : Function.Surjective π := eY.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : ∀ y, π y = 1 → y ∈ R := fun y h =>
    (QuotientGroup.eq_one_iff y).mp (eY.map_eq_one_iff.mp h)
  let ψ : MulAut (alternatingGroup (Fin 5)) := eY.symm.trans (τbar.trans eY)
  have hψπ : ∀ y, ψ (π y) = π (τ y) := by
    intro y
    simp only [ψ, π, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply]
    rfl
  have hψ3 : ∀ a, ψ (ψ (ψ a)) = a := by
    intro a
    obtain ⟨y, rfl⟩ := hπs a
    rw [hψπ, hψπ, hψπ, hτ3]
  obtain ⟨g, hg⟩ := exists_inner_of_pow_three hψ3
  obtain ⟨y₀, hy₀⟩ := hπs g
  have hδR : ∀ y, y⁻¹ * (y₀⁻¹ * τ y * y₀) ∈ R := by
    intro y
    apply hπker
    have h1 : π (τ y) = g * π y * g⁻¹ := by rw [← hψπ, hg]
    simp only [map_mul, map_inv, hy₀, h1]
    group
  have hδ : ∀ y z, (y * z)⁻¹ * (y₀⁻¹ * τ (y * z) * y₀) =
      (y⁻¹ * (y₀⁻¹ * τ y * y₀)) * (z⁻¹ * (y₀⁻¹ * τ z * y₀)) := by
    intro y z
    have hcen := Subgroup.mem_center_iff.mp (hc (hδR y)) z⁻¹
    rw [map_mul]
    calc (y * z)⁻¹ * (y₀⁻¹ * (τ y * τ z) * y₀)
        = z⁻¹ * (y⁻¹ * (y₀⁻¹ * τ y * y₀)) * (y₀⁻¹ * τ z * y₀) := by group
      _ = (y⁻¹ * (y₀⁻¹ * τ y * y₀)) * z⁻¹ * (y₀⁻¹ * τ z * y₀) := by rw [hcen]
      _ = _ := by group
  let δ : Y →* Subgroup.center Y :=
    { toFun := fun y => ⟨y⁻¹ * (y₀⁻¹ * τ y * y₀), hc (hδR y)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y z => Subtype.ext (hδ y z) }
  haveI : Group.IsSolvable (Y ⧸ δ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective δ)
  have hker : δ.ker = ⊤ := Sec4.Census.eq_top_of_isSolvable_quotient inferInstance
  have hτy : ∀ y, τ y = y₀ * y * y₀⁻¹ := by
    intro y
    have h1 : δ y = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      trivial
    have h2 : y⁻¹ * (y₀⁻¹ * τ y * y₀) = 1 := congrArg Subtype.val h1
    have h3 : y₀⁻¹ * τ y * y₀ = y := by
      calc y₀⁻¹ * τ y * y₀ = y * (y⁻¹ * (y₀⁻¹ * τ y * y₀)) := by group
        _ = y := by rw [h2, mul_one]
    calc τ y = y₀ * (y₀⁻¹ * τ y * y₀) * y₀⁻¹ := by group
      _ = y₀ * y * y₀⁻¹ := by rw [h3]
  obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR1
  have hrfix : τ r = r := by
    rw [hτy]
    have := Subgroup.mem_center_iff.mp (hc r.2) y₀
    calc y₀ * (r : Y) * y₀⁻¹ = (r : Y) * y₀ * y₀⁻¹ := by rw [this]
      _ = r := by group
  exact hr1 (Subtype.ext (hfix r r.2 hrfix))

private theorem false_of_card_pCore_le_four [Finite Y]
    (hYp : Group.IsPerfect Y) (eY : Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5))
    (hR1 : CFSG.pCore 2 Y ≠ ⊥) (τ : Y ≃* Y) (hτ3 : ∀ y, τ (τ (τ y)) = y)
    (hfix : ∀ y ∈ CFSG.pCore 2 Y, τ y = y → y = 1)
    (h4 : Nat.card (CFSG.pCore 2 Y) ≤ 4) : False :=
  false_of_pCore_le_center hYp eY hR1 τ hτ3 hfix (le_center_of_card_le_four hYp _ h4)

end YInternal

section PLevel

private structure Dat (P Y : Type) [Group P] [Finite P] [Group Y] [Finite Y] where
  K : Subgroup P
  [normal : K.Normal]
  hperf : Group.IsPerfect P
  hKs : Group.IsSolvable K
  hK3 : ¬ 3 ∣ Nat.card K
  eK : P ⧸ K ≃* alternatingGroup (Fin 5)
  hYp : Group.IsPerfect Y
  eY : Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)
  hR1 : CFSG.pCore 2 Y ≠ ⊥
  j : Y →* P
  hj : Function.Injective j
  hRK : ∀ y ∈ CFSG.pCore 2 Y, j y ∈ K
  σ : P ≃* P
  τ : Y ≃* Y
  hτ3 : ∀ y, τ (τ (τ y)) = y
  hστ : ∀ y, σ (j y) = j (τ y)
  hσK : ∀ x, σ x ∈ K ↔ x ∈ K
  hfix : ∀ y ∈ CFSG.pCore 2 Y, τ y = y → y = 1
  hO2 : CFSG.pCore 2 P = ⊥

attribute [local instance] Dat.normal

private theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem oddCore_characteristic (G : Type*) [Group G] :
    (CFSG.oddCore G).Characteristic := by
  refine Subgroup.characteristic_iff_le_comap.2 fun φ => sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map _ φ.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hN.2

namespace Dat

variable {P Y : Type} [Group P] [Finite P] [Group Y] [Finite Y]

private theorem simple (D : Dat P Y) : IsSimpleGroup (P ⧸ D.K) :=
  D.eK.isSimpleGroup

private theorem card_quotient (D : Dat P Y) : Nat.card (P ⧸ D.K) = 60 := by
  rw [Nat.card_congr D.eK.toEquiv, card_alternatingGroup_five]

private theorem eq_one_of_mem_oddCore (D : Dat P Y) {y : Y} (hy : y ∈ CFSG.pCore 2 Y)
    (hyO : D.j y ∈ CFSG.oddCore P) : y = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR2 ⟨y, hy⟩
  have h1 : orderOf y = 2 ^ k := by rw [← Subgroup.orderOf_mk y hy, hk]
  have h2 : orderOf (D.j y) = orderOf y := orderOf_injective D.j D.hj y
  have h3 : orderOf (D.j y) ∣ Nat.card (CFSG.oddCore P) := by
    rw [← Subgroup.orderOf_mk (D.j y) hyO]
    exact orderOf_dvd_natCard _
  have hodd : Odd (Nat.card (CFSG.oddCore P)) := CFSG.ABGLocalTools.odd_card_oddCore
  rw [h2, h1] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    have : 2 ∣ Nat.card (CFSG.oddCore P) := (dvd_pow_self 2 hk0).trans h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

private theorem pCore_le_center_of_map_central (D : Dat P Y) {Q : Type*} [Group Q] (f : P →* Q)
    (hf : ∀ y ∈ CFSG.pCore 2 Y, f (D.j y) = 1 → y = 1)
    (hcen : ∀ y ∈ CFSG.pCore 2 Y, f (D.j y) ∈ Subgroup.center Q) :
    CFSG.pCore 2 Y ≤ Subgroup.center Y := by
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro g
  have hn : g * y * g⁻¹ * y⁻¹ ∈ CFSG.pCore 2 Y :=
    (CFSG.pCore 2 Y).mul_mem
      ((inferInstance : (CFSG.pCore 2 Y).Normal).conj_mem y hy g) ((CFSG.pCore 2 Y).inv_mem hy)
  have hc := Subgroup.mem_center_iff.mp (hcen y hy) (f (D.j g))
  have h1 : f (D.j (g * y * g⁻¹ * y⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have h2 : ⁅g, y⁆ = 1 := hf _ hn h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

private theorem case_one (D : Dat P Y) (hq : IsQuasisimple (P ⧸ CFSG.pCore 2 P)) :
    CFSG.pCore 2 Y ≤ Subgroup.center Y := by
  haveI := D.hperf
  haveI := D.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : P →* P ⧸ CFSG.pCore 2 P := QuotientGroup.mk' (CFSG.pCore 2 P)
  have hfK : f.ker ≤ D.K := by
    rw [QuotientGroup.ker_mk']
    exact Sec4.Census.pCore_le 2
  have hmap := Sec4.Census.map_eq_center D.hKs hq f (QuotientGroup.mk'_surjective _) hfK
  refine D.pCore_le_center_of_map_central f ?_ ?_
  · intro y _ h1
    have h2 : D.j y ∈ CFSG.pCore 2 P := (QuotientGroup.eq_one_iff _).mp h1
    rw [D.hO2, Subgroup.mem_bot] at h2
    exact D.hj (h2.trans (map_one D.j).symm)
  · intro y hy
    rw [← hmap]
    exact ⟨D.j y, D.hRK y hy, rfl⟩

private theorem card_le_two_of_sl2 (D : Dat P Y) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {N : Subgroup P} [N.Normal] (hNO : N ≤ CFSG.oddCore P) (hNK : N ≤ D.K)
    (e : P ⧸ N ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    Nat.card (CFSG.pCore 2 Y) ≤ 2 := by
  haveI := D.hperf
  haveI := D.simple
  have hJ : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    Sec4.Census.isQuasisimple_SL2 hp5
  let f : P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : f.ker = N := by
    ext x
    simp [f]
  have hmap := Sec4.Census.map_eq_center D.hKs hJ f hf (by rw [hker]; exact hNK)
  have hc2 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = 2 :=
    Sec4.Census.card_center_SL2 (by omega)
  let g : CFSG.pCore 2 Y →* Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    ((f.comp D.j).comp (CFSG.pCore 2 Y).subtype).codRestrict _
      (fun y => hmap ▸ ⟨D.j y, D.hRK y y.2, rfl⟩)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : f (D.j y) = 1 := congrArg Subtype.val hy
    have h2 : D.j y ∈ N := by rw [← hker]; exact h1
    exact Subtype.ext (D.eq_one_of_mem_oddCore y.2 (hNO h2))
  calc Nat.card (CFSG.pCore 2 Y)
      ≤ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :=
        Nat.card_le_card_of_injective g hg
    _ = 2 := hc2

private theorem case_two (D : Dat P Y)
    (e : Nonempty (P ⧸ Sec4.oTwoFitting P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) :
    Nat.card (CFSG.pCore 2 Y) ≤ 2 := by
  obtain ⟨e⟩ := e
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := D.hperf
  haveI := D.simple
  have hNK : Sec4.oTwoFitting P ≤ D.K :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance Sec4.isSolvable_oTwoFitting
  have hNO : Sec4.oTwoFitting P ≤ CFSG.oddCore P := by
    rw [Sec4.Census.oTwoFitting_eq_of_pCore_two_eq_bot D.hO2]
    exact Sec4.Census.fittingSubgroup_le_oddCore D.hO2
  exact D.card_le_two_of_sl2 (le_refl 5) hNO hNK e

private theorem case_three (D : Dat P Y) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (e : Nonempty (P ⧸ Sec4.oTwoP p P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :
    Nat.card (CFSG.pCore 2 Y) ≤ 2 := by
  obtain ⟨e⟩ := e
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := D.hperf
  haveI := D.simple
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    omega
  have hNK : Sec4.oTwoP p P ≤ D.K :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance (Sec4.isSolvable_oTwoP p)
  have hNO : Sec4.oTwoP p P ≤ CFSG.oddCore P := by
    rw [Sec4.Census.oTwoP_eq_of_pCore_two_eq_bot p D.hO2]
    refine le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal p, ?_⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := P) p).exists_card_eq
    rw [hk]
    exact Odd.pow (hp.odd_of_ne_two hp2)
  exact D.card_le_two_of_sl2 hp5 hNO hNK e

private theorem false_of_case_four_a (D : Dat P Y)
    (e : Nonempty (P ⧸ Sec4.oTwoP 3 P ≃* projSL 3 (GaloisField 3 1))) : False := by
  obtain ⟨e⟩ := e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := D.hperf
  haveI := D.simple
  have hNK : Sec4.oTwoP 3 P ≤ D.K :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance (Sec4.isSolvable_oTwoP 3)
  have hdiv : Nat.card (P ⧸ D.K) ∣ Nat.card (P ⧸ Sec4.oTwoP 3 P) :=
    Subgroup.index_dvd_of_le hNK
  rw [D.card_quotient, Nat.card_congr e.toEquiv,
    ← Nat.card_congr Sec4.Census.sl3EquivProjSL.toEquiv, Sec4.Census.card_SL3_three] at hdiv
  norm_num at hdiv

private theorem isPGroup_two_q8D8 : IsPGroup 2 Sec4.Q8D8 := by
  have h64 : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 2 ^ 6 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card,
      DihedralGroup.nat_card]
    norm_num
  exact (IsPGroup.of_card h64).to_quotient _

private theorem false_of_case_four_b (D : Dat P Y)
    (h : Sec4.IsExtOf (P ⧸ Sec4.oTwoP 3 P) (alternatingGroup (Fin 5)) Sec4.Q8D8) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := D.hperf
  haveI := D.simple
  obtain ⟨B, hBn, ⟨eB⟩, -⟩ := h
  haveI := hBn
  have hN3 : Sec4.oTwoP 3 P = ⊥ := by
    have h1 : Sec4.oTwoP 3 P = CFSG.pCore 3 P :=
      Sec4.Census.oTwoP_eq_of_pCore_two_eq_bot 3 D.hO2
    have h2 : CFSG.pCore 3 P ≤ D.K := Sec4.Census.pCore_le 3
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := P) 3).exists_card_eq
    have h3 : 3 ^ k ∣ Nat.card D.K := hk ▸ Subgroup.card_dvd_of_le h2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero] at hk
      rw [h1]
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exact absurd ((dvd_pow_self 3 hk0.ne').trans h3) D.hK3
  let f : P →* P ⧸ Sec4.oTwoP 3 P := QuotientGroup.mk' (Sec4.oTwoP 3 P)
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN3]
  have hmapBt : (B.comap f).map f = B :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) B
  have hBtB : B.comap f ≃* B :=
    ((B.comap f).equivMapOfInjective f hfinj).trans (MulEquiv.subgroupCongr hmapBt)
  have hB2 : IsPGroup 2 B := isPGroup_two_q8D8.of_equiv eB.symm
  have hBt2 : IsPGroup 2 (B.comap f) := hB2.of_equiv hBtB.symm
  have hBtle : B.comap f ≤ CFSG.pCore 2 P :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hBt2
  rw [D.hO2, le_bot_iff] at hBtle
  have hmap1 : B = ⊥ := by
    rw [← hmapBt, hBtle, Subgroup.map_bot]
  obtain ⟨a, b, hab⟩ := Sec21.Hering233i.exists_not_commute_Q8D8
  have hnt : Nontrivial B := by
    haveI : Nontrivial Sec4.Q8D8 := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    exact eB.surjective.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot B).1 hnt hmap1

private theorem comap_eq_K (D : Dat P Y) {B' : Subgroup (P ⧸ CFSG.oddCore P)} [B'.Normal]
    (eA : (P ⧸ CFSG.oddCore P) ⧸ B' ≃* alternatingGroup (Fin 5)) :
    B'.comap (QuotientGroup.mk' (CFSG.oddCore P)) = D.K := by
  haveI := D.hperf
  haveI := D.simple
  haveI : (B'.comap (QuotientGroup.mk' (CFSG.oddCore P))).Normal := inferInstance
  let eT : P ⧸ B'.comap (QuotientGroup.mk' (CFSG.oddCore P)) ≃* alternatingGroup (Fin 5) :=
    (Sec4.Census.quotientComapEquiv (CFSG.oddCore P) B').trans eA
  haveI : Nontrivial (P ⧸ B'.comap (QuotientGroup.mk' (CFSG.oddCore P))) :=
    eT.surjective.nontrivial
  have hle : B'.comap (QuotientGroup.mk' (CFSG.oddCore P)) ≤ D.K :=
    Sec4.Census.le_of_nontrivial_quotient D.hKs inferInstance
  have hcard : Nat.card (P ⧸ B'.comap (QuotientGroup.mk' (CFSG.oddCore P))) =
      Nat.card (P ⧸ D.K) := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_congr D.eK.toEquiv]
  have h1 := Subgroup.card_mul_index (B'.comap (QuotientGroup.mk' (CFSG.oddCore P)))
  have h2 := Subgroup.card_mul_index D.K
  have hpos : 0 < Nat.card (P ⧸ D.K) := Nat.card_pos
  have h3 : Nat.card (B'.comap (QuotientGroup.mk' (CFSG.oddCore P))) = Nat.card D.K := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have e1 : (B'.comap (QuotientGroup.mk' (CFSG.oddCore P))).index =
        Nat.card (P ⧸ B'.comap (QuotientGroup.mk' (CFSG.oddCore P))) := rfl
    have e2 : D.K.index = Nat.card (P ⧸ D.K) := rfl
    rw [e1, hcard] at h1
    rw [e2] at h2
    rw [h1, h2]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq h3.symm)

private theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem false_of_case_A6 (D : Dat P Y) {B' : Subgroup (P ⧸ CFSG.oddCore P)} [B'.Normal]
    (eA : (P ⧸ CFSG.oddCore P) ⧸ B' ≃* alternatingGroup (Fin 6)) : False := by
  haveI := D.hperf
  haveI := D.simple
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : (B'.comap (QuotientGroup.mk' (CFSG.oddCore P))).Normal := inferInstance
  set Bt := B'.comap (QuotientGroup.mk' (CFSG.oddCore P)) with hBt
  let eT : P ⧸ Bt ≃* alternatingGroup (Fin 6) :=
    (Sec4.Census.quotientComapEquiv (CFSG.oddCore P) B').trans eA
  haveI : Nontrivial (P ⧸ Bt) := eT.surjective.nontrivial
  haveI : IsSimpleGroup (P ⧸ Bt) := eT.isSimpleGroup
  have hle : Bt ≤ D.K := Sec4.Census.le_of_nontrivial_quotient D.hKs inferInstance
  have hM : (D.K.map (QuotientGroup.mk' Bt)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Bt)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.K.map (QuotientGroup.mk' Bt)) with h | h
  · have hKle : D.K ≤ Bt := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hKB : Bt = D.K := le_antisymm hle hKle
    have hc : Nat.card (P ⧸ Bt) = 360 := by
      rw [Nat.card_congr eT.toEquiv, card_alternatingGroup_six]
    have hc' : Nat.card (P ⧸ Bt) = 60 := by
      rw [hKB, D.card_quotient]
    omega
  · have h1 : D.K ⊔ (QuotientGroup.mk' Bt).ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, h, Subgroup.comap_top]
    rw [QuotientGroup.ker_mk', sup_eq_left.mpr hle] at h1
    have h2 : Nat.card (P ⧸ D.K) = 1 := by
      rw [h1]
      exact Subgroup.index_top
    rw [D.card_quotient] at h2
    omega

end Dat

private theorem exists_pow_orderOf_eq_two {A : Type*} [Group A] (hA : IsPGroup 2 A) {a : A}
    (ha : a ≠ 1) : ∃ n : ℕ, orderOf (a ^ n) = 2 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA a
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk)) ha
    · exact ⟨k - 1, by omega⟩
  refine ⟨2 ^ m, ?_⟩
  have hdvd : 2 ^ m ∣ orderOf a := by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.le_succ m)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hk, pow_succ,
    Nat.mul_div_cancel_left _ (by positivity)]

namespace Dat

variable {P Y : Type} [Group P] [Finite P] [Group Y] [Finite Y]

private theorem card_le_four_of_ext (D : Dat P Y) {B : Type} [Group B] (hB : ExtFacts B)
    {B' : Subgroup (P ⧸ CFSG.oddCore P)} [B'.Normal] (eB : B' ≃* B)
    (hBK : B'.comap (QuotientGroup.mk' (CFSG.oddCore P)) = D.K) :
    Nat.card (CFSG.pCore 2 Y) ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := CFSG.oddCore P
  let f : P →* P ⧸ O := QuotientGroup.mk' O
  have hKB : D.K.map f = B' := by
    rw [← hBK]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) B'
  have hmem : ∀ y ∈ CFSG.pCore 2 Y, f (D.j y) ∈ B' := fun y hy =>
    hKB ▸ ⟨D.j y, D.hRK y hy, rfl⟩
  have hσO : ∀ x, D.σ x ∈ O ↔ x ∈ O := by
    intro x
    have hc := (oddCore_characteristic P).fixed D.σ
    have : x ∈ O.comap D.σ.toMonoidHom ↔ x ∈ O := by rw [hc]
    exact this
  have hfσ : ∀ a b, f a = f b → f (D.σ a) = f (D.σ b) := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ O := QuotientGroup.eq.mp hab
    have h2 : (D.σ a)⁻¹ * D.σ b ∈ O := by
      have : (D.σ a)⁻¹ * D.σ b = D.σ (a⁻¹ * b) := by simp
      rw [this, hσO]
      exact h1
    exact QuotientGroup.eq.mpr h2
  let Cen : Y → Prop := fun y => ∀ k ∈ D.K, f (D.j y) * f k = f (k) * f (D.j y)
  have hCen_τ : ∀ y, Cen y → Cen (D.τ y) := by
    intro y hy k hk
    have hk' : D.σ.symm k ∈ D.K := by
      rw [← D.hσK]
      simpa using hk
    have h1 := hy _ hk'
    have h2 : f (D.j y * D.σ.symm k) = f (D.σ.symm k * D.j y) := by
      rw [map_mul, map_mul]
      exact h1
    have h3 := hfσ _ _ h2
    rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    rw [← D.hστ]
    exact h3
  let ρ : CFSG.pCore 2 Y →* B := eB.toMonoidHom.comp
    (((f.comp D.j).comp (CFSG.pCore 2 Y).subtype).codRestrict B' (fun y => hmem y y.2))
  have hρ_symm : ∀ y : CFSG.pCore 2 Y, eB.symm (ρ y) = ⟨f (D.j y), hmem y y.2⟩ := by
    intro y
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : eB.symm (ρ y) = 1 := by rw [hy, map_one]
    rw [hρ_symm] at h1
    have h2 : f (D.j y) = 1 := congrArg Subtype.val h1
    exact Subtype.ext (D.eq_one_of_mem_oddCore y.2 ((QuotientGroup.eq_one_iff _).mp h2))
  have hCenOfCentral : ∀ y : CFSG.pCore 2 Y, ρ y ∈ Subgroup.center B → Cen y := by
    intro y hy k hk
    have hkB : f k ∈ B' := hKB ▸ ⟨k, hk, rfl⟩
    have hc := Subgroup.mem_center_iff.mp hy (eB ⟨f k, hkB⟩)
    have h1 : eB.symm (eB ⟨f k, hkB⟩ * ρ y) = eB.symm (ρ y * eB ⟨f k, hkB⟩) := by rw [hc]
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply, hρ_symm] at h1
    exact (congrArg Subtype.val h1).symm
  have hCentralOfCen : ∀ y : CFSG.pCore 2 Y, Cen y → ρ y ∈ Subgroup.center B := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨b', rfl⟩ := eB.surjective b
    obtain ⟨k, hk, hkb⟩ := (hKB ▸ b'.2 : (b' : P ⧸ O) ∈ D.K.map f)
    apply eB.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply, hρ_symm]
    apply Subtype.ext
    change (b' : P ⧸ O) * f (D.j y) = f (D.j y) * (b' : P ⧸ O)
    rw [← hkb]
    exact (hy k hk).symm
  have hS : ρ.range ⊓ Subgroup.center B = ⊥ := by
    by_contra hne
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨r, hr⟩ := x.2.1
    have hr1 : r ≠ 1 := by
      intro h
      apply hx1
      apply Subtype.ext
      rw [← hr, h, map_one]
      rfl
    have hR2 : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hR2 hr1
    have hρc : ρ r ∈ Subgroup.center B := by rw [hr]; exact x.2.2
    have hρ0c : ρ (r ^ n) ∈ Subgroup.center B := by
      rw [map_pow]
      exact Subgroup.pow_mem _ hρc n
    have hr0sq : r ^ n * r ^ n = 1 := by
      have h := pow_orderOf_eq_one (r ^ n)
      rw [hn, sq] at h
      exact h
    have hr0one : r ^ n ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hn
      omega
    set r₀ := r ^ n with hr₀
    let r₁ : CFSG.pCore 2 Y := ⟨D.τ r₀, mem_pCore_two_of_equiv D.τ r₀.2⟩
    have hρ1c : ρ r₁ ∈ Subgroup.center B :=
      hCentralOfCen r₁ (hCen_τ (r₀ : Y) (hCenOfCentral r₀ hρ0c))
    have hr1one : r₁ ≠ 1 := by
      intro h
      apply hr0one
      have h' : D.τ r₀ = 1 := congrArg Subtype.val h
      exact Subtype.ext (D.τ.injective (h'.trans (map_one D.τ).symm))
    have hr1sq : r₁ * r₁ = 1 := by
      apply Subtype.ext
      change D.τ r₀ * D.τ r₀ = 1
      rw [← map_mul]
      have := congrArg Subtype.val hr0sq
      change (r₀ : Y) * r₀ = 1 at this
      rw [this, map_one]
    have hρeq : ρ r₀ = ρ r₁ :=
      hB.1 _ _ hρ0c hρ1c (by rw [← map_mul, hr0sq, map_one]) (by rw [← map_mul, hr1sq, map_one])
        (fun h => hr0one (hρinj (h.trans (map_one ρ).symm)))
        (fun h => hr1one (hρinj (h.trans (map_one ρ).symm)))
    have hr01 : r₀ = r₁ := hρinj hρeq
    have hfixr : D.τ r₀ = r₀ := (congrArg Subtype.val hr01).symm
    exact hr0one (Subtype.ext (D.hfix r₀ r₀.2 hfixr))
  calc Nat.card (CFSG.pCore 2 Y) = Nat.card ρ.range :=
        Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    _ ≤ 4 := hB.2 _ hS

end Dat

namespace Dat

variable {P Y : Type} [Group P] [Finite P] [Group Y] [Finite Y]

private theorem case_five_q (D : Dat P Y) (hq : IsQuasisimple (P ⧸ CFSG.oddCore P)) :
    CFSG.pCore 2 Y ≤ Subgroup.center Y := by
  haveI := D.hperf
  haveI := D.simple
  haveI : Nontrivial (P ⧸ CFSG.oddCore P) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hOK : CFSG.oddCore P ≤ D.K := Sec4.Census.le_of_nontrivial_quotient D.hKs inferInstance
  let f : P →* P ⧸ CFSG.oddCore P := QuotientGroup.mk' (CFSG.oddCore P)
  have hfK : f.ker ≤ D.K := by
    rw [QuotientGroup.ker_mk']
    exact hOK
  have hmap := Sec4.Census.map_eq_center D.hKs hq f (QuotientGroup.mk'_surjective _) hfK
  refine D.pCore_le_center_of_map_central f ?_ ?_
  · intro y hy h1
    exact D.eq_one_of_mem_oddCore hy ((QuotientGroup.eq_one_iff _).mp h1)
  · intro y hy
    rw [← hmap]
    exact ⟨D.j y, D.hRK y hy, rfl⟩

end Dat

private theorem false_of_dat (h44 : Sec4.Item4_4)
    {P Y : Type} [Group P] [Finite P] [Group Y] [Finite Y] (hS : SectionFourHyp P)
    (D : Dat P Y) : False := by
  haveI := D.hperf
  haveI := D.simple
  have hcen : CFSG.pCore 2 Y ≤ Subgroup.center Y → False := fun hc =>
    false_of_pCore_le_center D.hYp D.eY D.hR1 D.τ D.hτ3 D.hfix hc
  have hle4 : Nat.card (CFSG.pCore 2 Y) ≤ 4 → False := fun h4 =>
    false_of_card_pCore_le_four D.hYp D.eY D.hR1 D.τ D.hτ3 D.hfix h4
  rcases h44 P hS D.hperf D.K D.hKs D.simple with
    h1 | h2 | ⟨p, hp, hp3, h3⟩ | (h4a | h4b) | ⟨-, h5⟩
  · exact hcen (D.case_one h1)
  · exact hle4 ((D.case_two h2).trans (by norm_num))
  · exact hle4 ((D.case_three hp hp3 h3).trans (by norm_num))
  · exact D.false_of_case_four_a h4a
  · exact D.false_of_case_four_b h4b
  · rcases h5 D.hK3 with ⟨-, hq | hext⟩ | ⟨-, hext1 | hext2 | hext3⟩
    · exact hcen (D.case_five_q hq)
    · obtain ⟨B', hB'n, ⟨eB⟩, ⟨eA⟩⟩ := hext
      haveI := hB'n
      exact hle4 (D.card_le_four_of_ext extFacts_q8D8 eB (D.comap_eq_K eA))
    · obtain ⟨B', hB'n, ⟨eB⟩, ⟨eA⟩⟩ := hext1
      haveI := hB'n
      exact hle4 (D.card_le_four_of_ext extFacts_q8D8 eB (D.comap_eq_K eA))
    · obtain ⟨B', hB'n, ⟨eB⟩, ⟨eA⟩⟩ := hext2
      haveI := hB'n
      exact hle4 (D.card_le_four_of_ext extFacts_z4Q8Q8 eB (D.comap_eq_K eA))
    · obtain ⟨B', hB'n, -, ⟨eA⟩⟩ := hext3
      haveI := hB'n
      exact D.false_of_case_A6 eA

end PLevel

private theorem false_of_data (h44 : Sec4.Item4_4)
    {P : Type} [Group P] [Finite P] (hS : SectionFourHyp P) (hperf : Group.IsPerfect P)
    (K : Subgroup P) [K.Normal] (hKs : Group.IsSolvable K) (hK3 : ¬ 3 ∣ Nat.card K)
    (eK : P ⧸ K ≃* alternatingGroup (Fin 5))
    {Y : Type} [Group Y] [Finite Y] (hYp : Group.IsPerfect Y)
    (eY : Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) (hR1 : CFSG.pCore 2 Y ≠ ⊥)
    (j : Y →* P) (hj : Function.Injective j) (hRK : ∀ y ∈ CFSG.pCore 2 Y, j y ∈ K)
    (σ : P ≃* P) (τ : Y ≃* Y) (hτ3 : ∀ y, τ (τ (τ y)) = y)
    (hστ : ∀ y, σ (j y) = j (τ y)) (hσK : ∀ x, σ x ∈ K ↔ x ∈ K)
    (hfix : ∀ y ∈ CFSG.pCore 2 Y, τ y = y → y = 1)
    (hO2 : CFSG.pCore 2 P = ⊥) : False :=
  false_of_dat h44 hS
    ⟨K, hperf, hKs, hK3, eK, hYp, eY, hR1, j, hj, hRK, σ, τ, hτ3, hστ, hσK, hfix, hO2⟩

section Helpers

private theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem le_of_normal_of_not_three_dvd {Y : Type} [Group Y] {R N : Subgroup Y}
    [R.Normal] [N.Normal] (e : Y ⧸ R ≃* alternatingGroup (Fin 5)) (hN : ¬ 3 ∣ Nat.card N) :
    N ≤ R := by
  haveI : IsSimpleGroup (Y ⧸ R) := e.isSimpleGroup
  haveI : (N.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective R)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' R)) with h | h
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · exfalso
    apply hN
    have h1 : Nat.card (N.map (QuotientGroup.mk' R)) ∣ Nat.card N := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Y ⧸ R) = 60 := by rw [Nat.card_congr e.toEquiv, card_alt5]
    have h3 : Nat.card (N.map (QuotientGroup.mk' R)) = 60 := by
      rw [h, Subgroup.card_top, h2]
    exact (show 3 ∣ 60 by norm_num).trans (h3 ▸ h1)

variable {G : Type} [Group G]

private theorem normal_subgroupOf_of_le_normalizer {T G₀ : Subgroup G}
    (h : G₀ ≤ Subgroup.normalizer (T : Set G)) : (T.subgroupOf G₀).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (h g.2) x).mp hx⟩

private theorem exists_injective_subgroupOf (T G₀ : Subgroup G) :
    ∃ f : ↥(T.subgroupOf G₀) →* ↥T, Function.Injective f :=
  ⟨(G₀.subtype.comp (T.subgroupOf G₀).subtype).codRestrict T fun x => x.2,
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥T → G) h))⟩

private theorem exists_isoA5 {T Y G₀ : Subgroup G} [(T.subgroupOf G₀).Normal]
    (hT3 : ¬ 3 ∣ Nat.card T) (hYT : Y ≤ Subgroup.normalizer (T : Set G)) (hYG₀ : Y ≤ G₀)
    (hG₀ : G₀ ≤ T ⊔ Y) (hRT : CFSG.Open.pCoreOf 2 Y ≤ T)
    (hY5 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5))) :
    Nonempty (↥G₀ ⧸ T.subgroupOf G₀ ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hY5
  let c₁ : ↥Y →* ↥G₀ ⧸ T.subgroupOf G₀ :=
    (QuotientGroup.mk' (T.subgroupOf G₀)).comp (Subgroup.inclusion hYG₀)
  have hsurj : Function.Surjective c₁ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hg : (g : G) ∈ ((Y ⊔ T : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hG₀ g.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Y T hYT] at hg
      obtain ⟨y, hy, t, ht, hyt⟩ := hg
      refine ⟨⟨y, hy⟩, ?_⟩
      show QuotientGroup.mk' (T.subgroupOf G₀) (Subgroup.inclusion hYG₀ ⟨y, hy⟩) =
        QuotientGroup.mk' (T.subgroupOf G₀) g
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simpa [← hyt] using ht
  have hmem : ∀ y : ↥Y, y ∈ c₁.ker ↔ (y : G) ∈ T := by
    intro y
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (T.subgroupOf G₀) (Subgroup.inclusion hYG₀ y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hker : c₁.ker = CFSG.pCore 2 ↥Y := by
    refine le_antisymm (le_of_normal_of_not_three_dvd e fun h3 => hT3 (h3.trans ?_)) ?_
    · rw [← Subgroup.card_map_of_injective Y.subtype_injective]
      exact Subgroup.card_dvd_of_le (by
        rintro _ ⟨y, hy, rfl⟩
        exact (hmem y).mp hy)
    · intro y hy
      exact (hmem y).mpr (hRT ⟨y, hy, rfl⟩)
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective c₁ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans e⟩

variable [Finite G]

private theorem exists_perfect_core {T Y : Subgroup G} {c : G} (hYp : Group.IsPerfect ↥Y)
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (hcT : c ∈ Subgroup.normalizer (T : Set G)) :
    ∃ G₀ : Subgroup G, G₀ ≤ T ⊔ Y ∧ Y ≤ G₀ ∧ Group.IsPerfect ↥G₀ ∧
      T ≤ Subgroup.normalizer (G₀ : Set G) ∧ c ∈ Subgroup.normalizer (G₀ : Set G) :=
  ⟨perfectResidualOf (T ⊔ Y), Subgroup.map_subtype_le _,
    perfect_subgroup_le_perfectResidualOf Y _ hYp le_sup_right,
    finite_perfectResidualOf_isPerfect _,
    le_sup_left.trans (Subgroup.le_normalizer.trans (perfectResidualOf_normalizer_contains _)),
    perfectResidualOf_normalizer_contains _
      (Subgroup.inf_normalizer_le_normalizer_sup T Y ⟨hcT, hcY⟩)⟩

private theorem pCore_eq_bot_of_pCoreOf_eq_bot {T G₀ : Subgroup G} [Group.IsPerfect ↥G₀]
    [(T.subgroupOf G₀).Normal] [IsSimpleGroup (↥G₀ ⧸ T.subgroupOf G₀)]
    (hTG₀ : T ≤ Subgroup.normalizer (G₀ : Set G)) (hbot : CFSG.Open.pCoreOf 2 T = ⊥) :
    CFSG.pCore 2 ↥G₀ = ⊥ := by
  have hle : CFSG.pCore 2 ↥G₀ ≤ T.subgroupOf G₀ := Sec4.Census.pCore_le 2
  have h1 : CFSG.Open.pCoreOf 2 G₀ ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hle hx)
  have h2 : CFSG.Open.pCoreOf 2 G₀ ≤ CFSG.Open.pCoreOf 2 T :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h1
      (hTG₀.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 G₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀)
  rw [hbot, le_bot_iff] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ G₀.subtype_injective).mp h2

end Helpers

theorem pCoreOf_ne_bot_of_item44 (h44 : Sec4.Item4_4)
    {G : Type} [Group G] [Finite G] {T Y : Subgroup G} {c : G}
    (hS : ∀ H : Subgroup G, H ≤ T ⊔ Y → SectionFourHyp ↥H)
    (hTs : Group.IsSolvable ↥T) (hT3 : ¬ 3 ∣ Nat.card T)
    (hYT : Y ≤ Subgroup.normalizer (T : Set G))
    (hYp : Group.IsPerfect ↥Y)
    (hY5 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)))
    (hRT : CFSG.Open.pCoreOf 2 Y ≤ T) (hR1 : CFSG.Open.pCoreOf 2 Y ≠ ⊥)
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (hcT : c ∈ Subgroup.normalizer (T : Set G))
    (hc3 : c ^ 3 = 1)
    (hcfix : CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    CFSG.Open.pCoreOf 2 T ≠ ⊥ := by
  intro hbot
  obtain ⟨G₀, hG₀H, hYG₀, hperf, hTG₀, hcG₀⟩ := exists_perfect_core (T := T) hYp hcY hcT
  have hG₀T : G₀ ≤ Subgroup.normalizer (T : Set G) :=
    hG₀H.trans (sup_le Subgroup.le_normalizer hYT)
  haveI : (T.subgroupOf G₀).Normal := normal_subgroupOf_of_le_normalizer hG₀T
  obtain ⟨eK⟩ := exists_isoA5 hT3 hYT hYG₀ hG₀H hRT hY5
  obtain ⟨f, hf⟩ := exists_injective_subgroupOf T G₀
  haveI := hperf
  haveI : IsSimpleGroup (↥G₀ ⧸ T.subgroupOf G₀) := eK.isSimpleGroup
  have hKs : Group.IsSolvable ↥(T.subgroupOf G₀) := Group.isSolvable_of_isSolvable_injective hf
  have hK3 : ¬ 3 ∣ Nat.card ↥(T.subgroupOf G₀) := fun h =>
    hT3 (h.trans (Subgroup.card_dvd_of_injective f hf))
  have hR1' : CFSG.pCore 2 ↥Y ≠ ⊥ := fun h => hR1 (by simp [CFSG.Open.pCoreOf, h])
  refine false_of_data h44 (hS G₀ hG₀H) hperf (T.subgroupOf G₀) hKs hK3 eK hYp hY5.some hR1'
    (Subgroup.inclusion hYG₀) (Subgroup.inclusion_injective hYG₀) ?_
    (G₀.normalizerMonoidHom ⟨c, hcG₀⟩) (Y.normalizerMonoidHom ⟨c, hcY⟩) ?_ ?_ ?_ ?_
    (pCore_eq_bot_of_pCoreOf_eq_bot hTG₀ hbot)
  · intro y hy
    exact hRT ⟨y, hy, rfl⟩
  · intro y
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have h3 : c * c * c = 1 := by
      calc c * c * c = c ^ 3 := by rw [pow_succ, sq]
        _ = 1 := hc3
    calc c * (c * (c * (y : G) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * y * (c * c * c)⁻¹ := by group
      _ = y := by rw [h3]; group
  · intro y
    exact Subtype.ext (by simp [Subgroup.normalizerMonoidHom_apply_apply_coe])
  · intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hcT x).symm
  · intro y hy hτ
    have hcomm : c * (y : G) = (y : G) * c := by
      have h := congrArg Subtype.val hτ
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      calc c * (y : G) = c * (y : G) * c⁻¹ * c := by group
        _ = (y : G) * c := by rw [h]
    have hy' : (y : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({c} : Set G) :=
      ⟨⟨y, hy, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [hcfix] at hy'
    exact Subtype.ext (Subgroup.mem_bot.mp hy')

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
