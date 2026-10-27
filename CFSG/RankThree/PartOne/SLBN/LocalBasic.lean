module

public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG
open scoped commutatorElement

section Perfect

theorem commute_of_commutator_commutator_eq_bot {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (hperf : ⁅H₁, H₁⁆ = H₁) (hc : ⁅⁅H₁, H₂⁆, H₁⁆ = ⊥) :
    ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x := by
  have h2 : ⁅⁅H₂, H₁⁆, H₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm H₂ H₁]
    exact hc
  have h3 : ⁅⁅H₁, H₁⁆, H₂⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hc h2
  rw [hperf] at h3
  intro x hx y hy
  have : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := h3 ▸ Subgroup.commutator_mem_commutator hx hy
  rw [Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem commute_of_commutator_le_center {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (hperf : ⁅H₁, H₁⁆ = H₁) (hc : ⁅H₁, H₂⁆ ≤ Subgroup.center G) :
    ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x := by
  refine commute_of_commutator_commutator_eq_bot hperf ?_
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro c hc' h _
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp (hc hc') h).symm)

theorem mem_center_of_forall_commutator_mem_center {G : Type*} [Group G] [Group.IsPerfect G]
    {x : G} (h : ∀ w : G, ⁅x, w⁆ ∈ Subgroup.center G) : x ∈ Subgroup.center G := by
  have hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊤ : Subgroup G) := by
    have := Group.IsPerfect.commutator_eq_top (G := G)
    rwa [_root_.commutator_def] at this
  have hc : ⁅(⊤ : Subgroup G), Subgroup.zpowers x⁆ ≤ Subgroup.center G := by
    rw [Subgroup.commutator_le]
    intro g _ k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hgx : ⁅g, x⁆ ∈ Subgroup.center G := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (h g)
    have hcen : Commute ⁅g, x⁆ x := ((Subgroup.mem_center_iff.mp hgx) x).symm
    have hz : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
    have hm : g * x ^ m * g⁻¹ = ⁅g, x⁆ ^ m * x ^ m := by
      rw [← conj_zpow, hz, Commute.mul_zpow hcen]
    have : ⁅g, x ^ m⁆ = ⁅g, x⁆ ^ m := by
      rw [commutatorElement_def, hm]
      group
    rw [this]
    exact Subgroup.zpow_mem _ hgx m
  rw [Subgroup.mem_center_iff]
  intro w
  exact (commute_of_commutator_le_center hperf hc w (Subgroup.mem_top w) x
    (Subgroup.mem_zpowers x))

end Perfect

section Comp

structure Comp (G : Type*) [Group G] (W : Subgroup G) : Prop where
  perfect : Group.IsPerfect W
  normal : ∀ N : Subgroup W, N.Normal → N ≤ Subgroup.center W ∨ N = ⊤
  five : ∃ h : W, orderOf h = 5 ∧ h ∉ Subgroup.center W

variable {G : Type*} [Group G] {W : Subgroup G}

theorem Comp.eq_top_of_forall_coprime (hW : Comp G W) (N : Subgroup W) [N.Normal]
    (hN : ∀ g : W, Nat.Coprime (orderOf g) 3 → g ∈ N) : N = ⊤ := by
  obtain ⟨h, h5, hc⟩ := hW.five
  rcases hW.normal N inferInstance with hle | htop
  · exact absurd (hle (hN h (by rw [h5]; norm_num))) hc
  · exact htop

end Comp

section Zpowers

theorem mem_zpowers_of_commute_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {a b : G} (ha : orderOf a = p) (hb : orderOf b = p) (hab : Commute a b)
    (hcard : ¬ p ^ 2 ∣ Nat.card G) : b ∈ Subgroup.zpowers a := by
  by_contra hnot
  have hdisj : ∀ x ∈ Subgroup.zpowers a, x ∈ Subgroup.zpowers b → x = 1 := by
    intro x hxa hxb
    by_contra hx1
    have hxord : orderOf x = p := by
      have hd : orderOf x ∣ p := by rw [← hb]; exact orderOf_dvd_of_mem_zpowers hxb
      exact ((Nat.dvd_prime Fact.out).mp hd).resolve_left
        (fun h => hx1 (orderOf_eq_one_iff.mp h))
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hxb
    have heq : Subgroup.zpowers x = Subgroup.zpowers b := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hb]
    apply hnot
    have : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
    exact (Subgroup.zpowers_le.2 hxa) this
  have hcomm : ∀ (m : Subgroup.zpowers a) (n : Subgroup.zpowers b),
      Commute ((Subgroup.zpowers a).subtype m) ((Subgroup.zpowers b).subtype n) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact hab.zpow_zpow i j
  let f : Subgroup.zpowers a × Subgroup.zpowers b →* G :=
    (Subgroup.zpowers a).subtype.noncommCoprod (Subgroup.zpowers b).subtype hcomm
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ hmn
    have h1 : (m : G) * n = 1 := hmn
    have hm1 : (m : G) = (n : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hm : (m : G) = 1 := hdisj m m.2 (hm1 ▸ Subgroup.inv_mem _ n.2)
    have hn : (n : G) = 1 := by rw [hm, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hm) (Subtype.ext hn)
  have hdvd : Nat.card f.range ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, Nat.card_zpowers,
    Nat.card_zpowers, ha, hb, ← sq] at hdvd
  exact hcard hdvd

end Zpowers

section Cube

theorem cube_formula {G : Type*} [Group G] {u v c : G} (hc : ∀ g : G, c * g = g * c)
    (huv : u * v = c * (v * u)) (hc3 : c ^ 3 = 1) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  obtain ⟨P, hP⟩ : ∃ P : G, P = c⁻¹ := ⟨_, rfl⟩
  have hci : ∀ g : G, P * g = g * P := fun g => by
    rw [hP]
    exact (Commute.inv_left (show Commute c g from hc g)).eq
  have hl : ∀ g X : G, g * (P * X) = P * (g * X) := fun g X => by
    rw [← mul_assoc, ← hci g, mul_assoc]
  have e1 : v * u = P * (u * v) := by rw [hP, huv]; group
  have e2 : ∀ X : G, v * (u * X) = P * (u * (v * X)) := fun X => by
    rw [← mul_assoc, e1, mul_assoc, mul_assoc]
  have hPPP : P * (P * P) = 1 := by
    have : P ^ 3 = 1 := by rw [hP, inv_pow, hc3, inv_one]
    rw [pow_succ, pow_succ, pow_one] at this
    simpa [mul_assoc] using this
  have key : (u * v) ^ 3 = P * (P * (P * (u * (u * (u * (v * (v * v))))))) := by
    calc (u * v) ^ 3 = u * (v * (u * (v * (u * v)))) := by
          rw [pow_succ, pow_succ, pow_one]; group
      _ = u * (P * (u * (v * (v * (u * v))))) := by rw [e2 (v * (u * v))]
      _ = P * (u * (u * (v * (v * (u * v))))) := by rw [hl]
      _ = P * (u * (u * (v * (P * (u * (v * v)))))) := by rw [e2 v]
      _ = P * (u * (u * (P * (v * (u * (v * v)))))) := by rw [hl v]
      _ = P * (u * (P * (u * (v * (u * (v * v)))))) := by rw [hl u]
      _ = P * (P * (u * (u * (v * (u * (v * v)))))) := by rw [hl u]
      _ = P * (P * (u * (u * (P * (u * (v * (v * v))))))) := by rw [e2 (v * v)]
      _ = P * (P * (u * (P * (u * (u * (v * (v * v))))))) := by rw [hl u]
      _ = P * (P * (P * (u * (u * (u * (v * (v * v))))))) := by rw [hl u]
  rw [key]
  calc P * (P * (P * (u * (u * (u * (v * (v * v))))))) =
        (P * (P * P)) * (u * (u * (u * (v * (v * v))))) := by simp only [mul_assoc]
    _ = u * (u * (u * (v * (v * v)))) := by rw [hPPP, one_mul]
    _ = u ^ 3 * v ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem cube_mul_eq {G : Type*} [Group G] {C : Subgroup G} (hC : C ≤ Subgroup.center G)
    (hC3 : ∀ c ∈ C, c ^ 3 = 1) {u v : G} (h : ⁅u, v⁆ ∈ C) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  refine cube_formula (c := ⁅u, v⁆) (fun g => ?_) ?_ (hC3 _ h)
  · exact (Subgroup.mem_center_iff.mp (hC h) g).symm
  · rw [commutatorElement_def]; group

end Cube

section Product

theorem exists_isElementaryAbelian_sup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A B : Subgroup G} (hA : IsElementaryAbelian p A) (hB : IsElementaryAbelian p B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : ∀ x ∈ A, x ∈ B → x = 1) :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Nat.card E = Nat.card A * Nat.card B ∧
      (∀ x ∈ E, ∃ a ∈ A, ∃ b ∈ B, x = a * b) ∧ A ≤ E ∧ B ≤ E := by
  have hc : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n => hcomm m m.2 n n.2
  let f : A × B →* G := A.subtype.noncommCoprod B.subtype hc
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ hmn
    have h1 : (m : G) * n = 1 := hmn
    have hm1 : (m : G) = (n : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hm : (m : G) = 1 := hdisj m m.2 (hm1 ▸ Subgroup.inv_mem _ n.2)
    have hn : (n : G) = 1 := by rw [hm, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hm) (Subtype.ext hn)
  have hAc : ∀ a a' : A, a * a' = a' * a := hA.toIsMulCommutative.is_comm.comm
  have hBc : ∀ b b' : B, b * b' = b' * b := hB.toIsMulCommutative.is_comm.comm
  have hAp : ∀ a : A, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A)
  have hBp : ∀ b : B, b ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B)
  refine ⟨f.range, { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }, ?_, ?_, ?_,
    ?_⟩
  · obtain ⟨⟨a, b⟩, ha⟩ := x.2
    obtain ⟨⟨a', b'⟩, hb⟩ := y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (hAc a a') (hBc b b')
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
    obtain ⟨⟨a, b⟩, ha⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ha, ← map_pow]
    have : (a, b) ^ p = 1 := Prod.ext (hAp a) (hBp b)
    rw [this, map_one]
    rfl
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod]
  · rintro x ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, a.2, b, b.2, rfl⟩
  · intro a ha
    exact ⟨(⟨a, ha⟩, 1), by simp [f]⟩
  · intro b hb
    exact ⟨(1, ⟨b, hb⟩), by simp [f]⟩

end Product

end CFSG.RankThree.PartOne.SLBN
