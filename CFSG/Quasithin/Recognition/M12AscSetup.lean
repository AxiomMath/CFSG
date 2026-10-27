module

public import CFSG.Quasithin.Recognition.M12AscModel
public import CFSG.Quasithin.Recognition.M12AscLocalCore

public section

namespace CFSG.Quasithin

open CFSG.GH74.M12 (Asc03Hyp q8Subgroups)
open Subgroup

variable {G : Type*} [Group G] {z : G}

theorem q32Data_pCore (hyp : Asc03Hyp G z) :
    Q32Data (⟨z, z_mem_ascH z⟩ : ↥(ascH z)) (CFSG.pCore 2 ↥(ascH z)) := by
  obtain ⟨hcard, hsq, hcomm⟩ := isExtraspecial_facts hyp.extraspecial
  set P := CFSG.pCore 2 ↥(ascH z) with hP
  set zH : ↥(ascH z) := ⟨z, z_mem_ascH z⟩ with hzH
  have hzP : zH ∈ P := z_mem_pCore hyp
  have hz1 : zH ≠ 1 := fun h => asc_z_ne_one hyp (by simpa [zH] using congrArg Subtype.val h)
  have hz2 : zH * zH = 1 := Subtype.ext (by simpa [zH] using asc_z_sq hyp)
  let zP : ↥P := ⟨zH, hzP⟩
  have hzPc : zP ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 y.1.2
  have hzP1 : zP ≠ 1 := fun h => hz1 (congrArg (fun w : ↥P => (w : ↥(ascH z))) h)
  have hcen : ∀ w ∈ Subgroup.center ↥P, w = 1 ∨ w = zP := by
    intro w hw
    have := eq_one_or_eq_of_card_two hcard (a := (⟨zP, hzPc⟩ : ↥(Subgroup.center ↥P)))
      (by intro h; exact hzP1 (congrArg Subtype.val h)) ⟨w, hw⟩
    rcases this with h | h
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  refine ⟨hyp.card_core, hzP, hz1, hz2, fun h => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 h.2),
    ?_, ?_, ?_⟩
  · intro q hq hc
    have hqc : (⟨q, hq⟩ : ↥P) ∈ Subgroup.center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hc y.1 y.2).symm
    rcases hcen _ hqc with h | h
    · left; exact congrArg (fun w : ↥P => (w : ↥(ascH z))) h
    · right; exact congrArg (fun w : ↥P => (w : ↥(ascH z))) h
  · intro q hq
    have h1 := hcen _ (hsq (⟨q, hq⟩ : ↥P))
    rcases h1 with h | h
    · left; simpa [pow_two] using congrArg (fun w : ↥P => (w : ↥(ascH z))) h
    · right; simpa [pow_two, zP] using congrArg (fun w : ↥P => (w : ↥(ascH z))) h
  · intro q hq y hy
    have h1 := hcen _ (hcomm (⟨q, hq⟩ : ↥P) (⟨y, hy⟩ : ↥P))
    rcases h1 with h | h
    · left; simpa using congrArg (fun w : ↥P => (w : ↥(ascH z))) h
    · right; simpa [zP] using congrArg (fun w : ↥P => (w : ↥(ascH z))) h

theorem asc_centralizer_order_three [Finite G] (hyp : Asc03Hyp G z) {x : ↥(ascH z)} (hx1 : x ≠ 1)
    (hx3 : x * x * x = 1) :
    ∀ q ∈ CFSG.pCore 2 ↥(ascH z), q * x = x * q → q = 1 ∨ q = (⟨z, z_mem_ascH z⟩ : ↥(ascH z)) := by
  intro q hq hqx
  have hord : orderOf x = 3 := by
    refine orderOf_eq_prime ?_ hx1
    simpa [pow_succ, mul_assoc] using hx3
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨X, hX⟩ := hxp.exists_le_sylow
  have hXcard : Nat.card ↥(X : Subgroup ↥(ascH z)) = 3 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 X.isPGroup'
    have hdvd : 3 ^ k ∣ 192 := by
      rw [← AscModel.card_ascH hyp, ← hk]
      exact Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have : 3 ^ 2 ∣ 192 := (pow_dvd_pow 3 hk2).trans hdvd
      norm_num at this
    have hge : 3 ≤ Nat.card ↥(X : Subgroup ↥(ascH z)) := by
      have := Subgroup.card_le_of_le hX
      rwa [Nat.card_zpowers, hord] at this
    rw [hk] at hge ⊢
    interval_cases k <;> simp_all
  have hXeq : Subgroup.zpowers x = (X : Subgroup ↥(ascH z)) :=
    Subgroup.eq_of_le_of_card_ge hX (by rw [hXcard, Nat.card_zpowers, hord])
  have hcomm : ∀ y ∈ (X : Subgroup ↥(ascH z)), y * q = q * y := by
    intro y hy
    rw [← hXeq] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute x q from hqx.symm) k)).eq
  have hz := hyp.centralizer_X X q hq hcomm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hz2 : z ^ k = 1 ∨ z ^ k = z := by
    rw [← zpow_mod_orderOf, hyp.orderTwo]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; simp [h]
    · right; simp [h]
  rcases hz2 with h | h
  · left
    apply Subtype.ext
    rw [← hk, h]; rfl
  · right
    apply Subtype.ext
    rw [← hk, h]

theorem asc_q8_facts (hyp : Asc03Hyp G z) {K : Subgroup ↥(ascH z)}
    (hK : K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z))) :
    Nat.card K = 8 ∧ ∃ a ∈ K, a * a = (⟨z, z_mem_ascH z⟩ : ↥(ascH z)) := by
  obtain ⟨hKQ, ⟨ψ⟩⟩ := hK
  have hQ := q32Data_pCore hyp
  have hQ8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  refine ⟨(Nat.card_congr ψ.toEquiv).trans hQ8, ?_⟩
  set zH : ↥(ascH z) := ⟨z, z_mem_ascH z⟩ with hzH
  have hnc : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  have hinv : ∀ g : QuaternionGroup 2, g * g = 1 → g ≠ 1 → g = QuaternionGroup.a 2 := by decide
  have hsq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide
  set k1 : K := ψ.symm (QuaternionGroup.a 1) with hk1
  set k2 : K := ψ.symm (QuaternionGroup.xa 0) with hk2
  have hk12 : (k1 : ↥(ascH z)) * k2 ≠ k2 * k1 := by
    intro h
    apply hnc
    have h' : k1 * k2 = k2 * k1 := Subtype.ext h
    have := congrArg ψ h'
    simpa [hk1, hk2] using this
  have hzK : zH ∈ K := by
    have hc : (k1 : ↥(ascH z)) * k2 * (k1 : ↥(ascH z))⁻¹ * (k2 : ↥(ascH z))⁻¹ = 1 ∨
        (k1 : ↥(ascH z)) * k2 * (k1 : ↥(ascH z))⁻¹ * (k2 : ↥(ascH z))⁻¹ = zH :=
      hQ.comm_mem _ (hKQ k1.2) _ (hKQ k2.2)
    rcases hc with h | h
    · exfalso
      apply hk12
      calc (k1 : ↥(ascH z)) * k2 = ((k1 : ↥(ascH z)) * k2 * (k1 : ↥(ascH z))⁻¹ * (k2 : ↥(ascH z))⁻¹) *
            (k2 * k1) := by group
        _ = k2 * k1 := by rw [h, one_mul]
    · rw [← h]
      exact K.mul_mem (K.mul_mem (K.mul_mem k1.2 k2.2) (K.inv_mem k1.2)) (K.inv_mem k2.2)
  have hψz : ψ ⟨zH, hzK⟩ = QuaternionGroup.a 2 := by
    apply hinv
    · rw [← map_mul]
      have : (⟨zH, hzK⟩ : K) * ⟨zH, hzK⟩ = 1 := Subtype.ext hQ.z_sq
      rw [this, map_one]
    · intro h
      have := ψ.injective (h.trans ψ.map_one.symm)
      exact hQ.z_ne_one (congrArg Subtype.val this)
  refine ⟨ψ.symm (QuaternionGroup.a 1), (ψ.symm _).2, ?_⟩
  have : ψ.symm (QuaternionGroup.a 1) * ψ.symm (QuaternionGroup.a 1) = ⟨zH, hzK⟩ := by
    rw [← map_mul, hsq, ← hψz]
    exact ψ.symm_apply_apply _
  exact congrArg Subtype.val this

theorem exists_ascModel_of_asc03_normal_q8
    [Finite G] (hyp : Asc03Hyp G z)
    (hK : ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)), K.Normal) : Nonempty (AscModel z) := by
  obtain ⟨K, hKmem, hKn⟩ := hK
  obtain ⟨hK8, hKa⟩ := asc_q8_facts hyp hKmem
  obtain ⟨e⟩ := hyp.quotient_S3
  set P := CFSG.pCore 2 ↥(ascH z) with hP
  let ρ : ↥(ascH z) →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' P)
  have hρs : Function.Surjective ρ :=
    e.surjective.comp (QuotientGroup.mk'_surjective P)
  have hρk : ∀ h : ↥(ascH z), ρ h = 1 ↔ h ∈ P := by
    intro h
    constructor
    · intro h1
      have : (QuotientGroup.mk' P) h = 1 := by
        apply e.injective
        simpa [ρ] using h1
      exact (QuotientGroup.eq_one_iff _).1 this
    · intro h1
      have : (QuotientGroup.mk' P) h = 1 := (QuotientGroup.eq_one_iff _).2 h1
      show e ((QuotientGroup.mk' P) h) = 1
      rw [this, map_one]
  obtain ⟨g, -, -, -, -, -, -, v₀, hv₀, hv₀o, hv₀Q⟩ := exists_config_of_asc03 hyp
  have hv₀2 : v₀ * v₀ = 1 := by
    have := pow_orderOf_eq_one v₀
    rwa [hv₀o, pow_two] at this
  set v : ↥(ascH z) := ⟨v₀, hv₀.1⟩ with hv
  have hv2 : v * v = 1 := Subtype.ext hv₀2
  have hvQ : v ∉ P := fun h => hv₀Q ((mem_ascQ_iff z v₀).2 ⟨hv₀.1, h⟩)
  obtain ⟨a, b, x, u, hPres, ha2, hgen⟩ := exists_hPres_of_core (q32Data_pCore hyp) hρs hρk
    (fun x hx1 hx3 => asc_centralizer_order_three hyp hx1 hx3) hKmem.1 hKn hK8 hKa hv2 hvQ
  obtain ⟨φ, hφa, -, -, -⟩ := exists_mulEquiv_ascHModel (AscModel.card_ascH hyp) hPres hgen
  refine ⟨⟨φ, ?_⟩⟩
  rw [← ha2, map_mul]
  show ((φ a * φ a : ascHModel) : Equiv.Perm (Fin 12)) = _
  rw [Subgroup.coe_mul, hφa]

end CFSG.Quasithin
