module

public import CFSG.RankThree.PartOne.SLBN.LocalBasic
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.RankThree.PartOne.SLBN

open Subgroup CFSG
open scoped commutatorElement

theorem eq_one_of_perfect_of_range_isPGroup {W A : Type*} [Group W] [Finite W]
    [Group.IsPerfect W] [Group A] {p : ℕ} [Fact p.Prime] (α : W →* A) (P : Subgroup A)
    (hP : IsPGroup p P) (hα : ∀ w, α w ∈ P) : α = 1 := by
  have hker : α.ker = ⊤ := by
    let β : W ⧸ α.ker →* P := (QuotientGroup.kerLift α).codRestrict P (fun q => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      exact hα w)
    have hβ : Function.Injective β := fun x y h =>
      QuotientGroup.kerLift_injective α (congrArg Subtype.val h)
    have hpg : IsPGroup p (W ⧸ α.ker) := hP.of_injective β hβ
    exact CFSG.RankThree.PartOne.SRC.eq_top_of_perfect_pgroup_quotient α.ker hpg
  ext w
  have : w ∈ α.ker := hker ▸ Subgroup.mem_top w
  simpa using this

theorem normal_centralizer_of_normal {G : Type*} [Group G] (R : Subgroup G) [R.Normal] :
    (Subgroup.centralizer (R : Set G)).Normal := by
  refine ⟨fun x hx w => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : w⁻¹ * y * w ∈ R := by
    have := (inferInstance : R.Normal).conj_mem y hy w⁻¹
    simpa using this
  have hx' := Subgroup.mem_centralizer_iff.mp hx _ hy'
  calc y * (w * x * w⁻¹) = w * ((w⁻¹ * y * w) * x) * w⁻¹ := by group
    _ = w * (x * (w⁻¹ * y * w)) * w⁻¹ := by rw [hx']
    _ = w * x * w⁻¹ * y := by group

theorem eq_one_of_mem_zpowers_of_map_eq_one {G S : Type*} [Group G] [Group S] [Finite G]
    (φ : G →* S) {p : ℕ} [Fact p.Prime] {e : G} (he : e ^ p = 1) (hφ : φ e ≠ 1) {x : G}
    (hx : x ∈ Subgroup.zpowers e) (h1 : φ x = 1) : x = 1 := by
  by_contra hx1
  have he1 : e ≠ 1 := fun h => hφ (by rw [h, map_one])
  have heord : orderOf e = p := by
    have hd : orderOf e ∣ p := orderOf_dvd_of_pow_eq_one he
    exact ((Nat.dvd_prime Fact.out).mp hd).resolve_left (fun h => he1 (orderOf_eq_one_iff.mp h))
  have hxord : orderOf x = p := by
    have hd : orderOf x ∣ p := by rw [← heord]; exact orderOf_dvd_of_mem_zpowers hx
    exact ((Nat.dvd_prime Fact.out).mp hd).resolve_left (fun h => hx1 (orderOf_eq_one_iff.mp h))
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers e := Subgroup.zpowers_le.2 hx
  have heq : Subgroup.zpowers x = Subgroup.zpowers e := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hxord, heord]
  have : e ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers e
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp this
  apply hφ
  rw [← hm, map_zpow, h1, one_zpow]

section Both

variable {G A : Type*} [Group G] [Group A]

theorem Comp.ker_le_center {W : Subgroup G} (hW : Comp G W) (ψ : G →* A)
    (hnt : ¬ ∀ w ∈ W, ψ w = 1) (w : W) (hw : ψ (w : G) = 1) : w ∈ Subgroup.center W := by
  have hN : (ψ.comp W.subtype).ker.Normal := MonoidHom.normal_ker _
  rcases hW.normal (ψ.comp W.subtype).ker hN with hle | htop
  · exact hle hw
  · exfalso
    apply hnt
    intro x hx
    have : (⟨x, hx⟩ : W) ∈ (ψ.comp W.subtype).ker := htop ▸ Subgroup.mem_top _
    exact this

theorem Comp.exists_five_map_ne_one {W : Subgroup G} (hW : Comp G W) (ψ : G →* A)
    (hnt : ¬ ∀ w ∈ W, ψ w = 1) :
    ∃ h : W, orderOf h = 5 ∧ ψ (h : G) ≠ 1 ∧ h ∉ Subgroup.center W := by
  obtain ⟨h, h5, hc⟩ := hW.five
  exact ⟨h, h5, fun h1 => hc (hW.ker_le_center ψ hnt h h1), hc⟩

theorem false_of_both_nontrivial [Finite G] [Finite A] (ψ : G →* A) {W₁ W₂ : Subgroup G}
    (h₁ : Comp G W₁) (h₂ : Comp G W₂) (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x)
    (hnt₁ : ¬ ∀ w ∈ W₁, ψ w = 1) (hnt₂ : ¬ ∀ w ∈ W₂, ψ w = 1) (hA : ¬ 25 ∣ Nat.card A) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := h₁.perfect
  obtain ⟨a, ha5, haψ, hac⟩ := h₁.exists_five_map_ne_one ψ hnt₁
  obtain ⟨b, hb5, hbψ, hbc⟩ := h₂.exists_five_map_ne_one ψ hnt₂
  have hord : ∀ g : G, g ^ 5 = 1 → ψ g ≠ 1 → orderOf (ψ g) = 5 := by
    intro g hg hψg
    have hd : orderOf (ψ g) ∣ 5 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one])
    exact ((Nat.dvd_prime Fact.out).mp hd).resolve_left (fun h => hψg (orderOf_eq_one_iff.mp h))
  have ha5' : (a : G) ^ 5 = 1 := by
    have := pow_orderOf_eq_one a
    rw [ha5] at this
    exact congrArg Subtype.val this
  have hb5' : (b : G) ^ 5 = 1 := by
    have := pow_orderOf_eq_one b
    rw [hb5] at this
    exact congrArg Subtype.val this
  have hoa := hord a ha5' haψ
  have hob := hord b hb5' hbψ
  have hcab : Commute (ψ (a : G)) (ψ (b : G)) :=
    (Commute.map (show Commute (a : G) (b : G) from hcomm a a.2 b b.2) ψ)
  have hmem := mem_zpowers_of_commute_of_not_sq_dvd hoa hob hcab hA
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  set u : W₁ := (a ^ j)⁻¹ with hu
  have hy : ψ ((b : G) * (u : G)) = 1 := by
    have : ψ (u : G) = (ψ (a : G) ^ j)⁻¹ := by
      rw [hu, Subgroup.coe_inv, Subgroup.coe_zpow, map_inv, map_zpow]
    rw [map_mul, this, hj, mul_inv_cancel]
  have hkerN : (ψ.ker).Normal := MonoidHom.normal_ker ψ
  have hcom_u : ∀ w : W₁, ⁅u, w⁆ ∈ Subgroup.center W₁ := by
    intro w
    have hyk : (b : G) * (u : G) ∈ ψ.ker := hy
    have h1 : ⁅(b : G) * (u : G), (w : G)⁆ ∈ ψ.ker := by
      rw [commutatorElement_def]
      have := hkerN.conj_mem _ hyk (w : G)
      have h2 := Subgroup.mul_mem _ this (Subgroup.inv_mem _ hyk)
      have h3 := Subgroup.inv_mem _ h2
      have h4 : ((w : G) * ((b : G) * (u : G)) * (w : G)⁻¹ * ((b : G) * (u : G))⁻¹)⁻¹ =
          (b : G) * (u : G) * (w : G) * ((b : G) * (u : G))⁻¹ * (w : G)⁻¹ := by group
      rwa [h4] at h3
    have h5 : ⁅(b : G) * (u : G), (w : G)⁆ = ⁅(u : G), (w : G)⁆ := by
      have hbc' : ∀ x : W₁, (b : G) * (x : G) = (x : G) * (b : G) := fun x =>
        (hcomm x x.2 b b.2).symm
      have e1 : (b : G) * ((u : G) * (w : G) * (u : G)⁻¹) =
          ((u : G) * (w : G) * (u : G)⁻¹) * (b : G) :=
        hbc' (u * w * u⁻¹)
      rw [commutatorElement_def, commutatorElement_def]
      calc (b : G) * (u : G) * (w : G) * ((b : G) * (u : G))⁻¹ * (w : G)⁻¹
          = (b : G) * ((u : G) * (w : G) * (u : G)⁻¹) * (b : G)⁻¹ * (w : G)⁻¹ := by group
        _ = ((u : G) * (w : G) * (u : G)⁻¹) * (b : G) * (b : G)⁻¹ * (w : G)⁻¹ := by rw [e1]
        _ = (u : G) * (w : G) * (u : G)⁻¹ * (w : G)⁻¹ := by group
    rw [h5] at h1
    exact h₁.ker_le_center ψ hnt₁ ⁅u, w⁆ (by
      change ψ ⁅(u : G), (w : G)⁆ = 1
      exact h1)
  have huc : u ∈ Subgroup.center W₁ := mem_center_of_forall_commutator_mem_center hcom_u
  have hne : ψ ((a ^ j : W₁) : G) ≠ 1 := by
    rw [Subgroup.coe_zpow, map_zpow, hj]
    exact hbψ
  have hajc : a ^ j ∈ Subgroup.center W₁ := by
    have := Subgroup.inv_mem _ huc
    simpa [hu] using this
  have hpa : a ^ 5 = 1 := by rw [← ha5]; exact pow_orderOf_eq_one a
  have hne1 : a ^ j ≠ 1 := fun h => hne (by rw [h]; exact map_one ψ)
  have h5' : (a ^ j) ^ 5 = 1 := by
    rw [← zpow_natCast (a ^ j) 5, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpa, one_zpow]
  have hord_aj : orderOf (a ^ j) = 5 := orderOf_eq_prime h5' hne1
  have hle : Subgroup.zpowers (a ^ j) ≤ Subgroup.zpowers a :=
    Subgroup.zpowers_le.2 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j)
  have heq : Subgroup.zpowers (a ^ j) = Subgroup.zpowers a := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hord_aj, ha5]
  have : a ∈ Subgroup.zpowers (a ^ j) := heq ▸ Subgroup.mem_zpowers a
  exact hac (Subgroup.zpowers_le.2 hajc this)

end Both

end CFSG.RankThree.PartOne.SLBN
