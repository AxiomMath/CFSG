module

public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

structure CentralData (Z : Subgroup Γ) : Prop where
  central : Z ≤ Subgroup.center Γ
  card_Z : Nat.card Z = 3
  comm_mem : ∀ x y : Γ, ⁅x, y⁆ ∈ Z
  cube_mem : ∀ x : Γ, x ^ 3 ∈ Z

namespace CentralData

variable {Z : Subgroup Γ} (hZ : CentralData Z)

include hZ

theorem finite_Z : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ.card_Z]; norm_num)

theorem pow_three_eq_one {z : Γ} (hz : z ∈ Z) : z ^ 3 = 1 := by
  have := hZ.finite_Z
  have h : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
  rw [hZ.card_Z] at h
  exact congrArg Subtype.val h

theorem mul_central {z : Γ} (hz : z ∈ Z) (g : Γ) : g * z = z * g :=
  Subgroup.mem_center_iff.mp (hZ.central hz) g

theorem cube_mul (x y : Γ) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hdZ : ⁅y, x⁆ ∈ Z := hZ.comm_mem y x
  have hd3 : ⁅y, x⁆ ^ 3 = 1 := hZ.pow_three_eq_one hdZ
  have hdc : ∀ g : Γ, g * ⁅y, x⁆ = ⁅y, x⁆ * g := hZ.mul_central hdZ
  have hyx : y * x = ⁅y, x⁆ * (x * y) := by
    rw [commutatorElement_def]
    group
  have hL : ∀ g h : Γ, g * (⁅y, x⁆ * h) = ⁅y, x⁆ * (g * h) := fun g h => by
    rw [← mul_assoc, hdc g, mul_assoc]
  have hyx' : ∀ w : Γ, y * (x * w) = ⁅y, x⁆ * (x * (y * w)) := fun w => by
    rw [← mul_assoc, hyx, mul_assoc, mul_assoc]
  have h : (x * y) ^ 3 = ⁅y, x⁆ ^ 3 * (x ^ 3 * y ^ 3) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    simp only [hyx', hL]
  rw [h, hd3, one_mul]

@[expose] def commHom (a : Γ) : Γ →* Z where
  toFun y := ⟨⁅a, y⁆, hZ.comm_mem a y⟩
  map_one' := Subtype.ext (commutatorElement_one_right a)
  map_mul' y w := Subtype.ext (by
    have hcen : y * ⁅a, w⁆ * y⁻¹ = ⁅a, w⁆ := by
      rw [hZ.mul_central (hZ.comm_mem a w) y]
      group
    change ⁅a, y * w⁆ = ⁅a, y⁆ * ⁅a, w⁆
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc, mul_assoc, ← mul_assoc y, hcen])

theorem ker_commHom (a : Γ) : (hZ.commHom a).ker = Subgroup.centralizer ({a} : Set Γ) := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
  change (⟨⁅a, y⁆, hZ.comm_mem a y⟩ : Z) = 1 ↔ y * a = a * y
  rw [Subtype.ext_iff, Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm, eq_comm]

theorem card_centralizer_ge (hΓ : Nat.card Γ = 81) (a : Γ) :
    27 ≤ Nat.card (Subgroup.centralizer ({a} : Set Γ)) := by
  have := hZ.finite_Z
  have : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  have h1 := Subgroup.card_ker_mul_card_range (hZ.commHom a)
  have h2 : Nat.card (hZ.commHom a).range ≤ 3 := by
    have := Subgroup.card_le_of_le (le_top : (hZ.commHom a).range ≤ ⊤)
    rw [Subgroup.card_top, hZ.card_Z] at this
    exact this
  rw [hZ.ker_commHom a, hΓ] at h1
  have hpos : 0 < Nat.card (Subgroup.centralizer ({a} : Set Γ)) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card (Subgroup.centralizer ({a} : Set Γ)) *
      Nat.card (hZ.commHom a).range < 81 := by
    calc _ ≤ 26 * 3 := Nat.mul_le_mul (by omega) h2
      _ < 81 := by norm_num
  omega

@[expose] def cubeHom : Γ →* Z where
  toFun x := ⟨x ^ 3, hZ.cube_mem x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (hZ.cube_mul x y)

theorem mem_ker_cubeHom {x : Γ} : x ∈ (hZ.cubeHom).ker ↔ x ^ 3 = 1 := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  rfl

theorem card_ker_cubeHom_ge (hΓ : Nat.card Γ = 81) : 27 ≤ Nat.card (hZ.cubeHom).ker := by
  have := hZ.finite_Z
  have h1 := Subgroup.card_ker_mul_card_range (hZ.cubeHom)
  have h2 : Nat.card (hZ.cubeHom).range ≤ 3 := by
    have := Subgroup.card_le_of_le (le_top : (hZ.cubeHom).range ≤ ⊤)
    rw [Subgroup.card_top, hZ.card_Z] at this
    exact this
  rw [hΓ] at h1
  by_contra hlt
  push Not at hlt
  have : Nat.card (hZ.cubeHom).ker * Nat.card (hZ.cubeHom).range < 81 := by
    calc _ ≤ 26 * 3 := Nat.mul_le_mul (by omega) h2
      _ < 81 := by norm_num
  omega

theorem exists_abelian_exp_three (hΓ : Nat.card Γ = 81)
    (hR : ∀ a b r : Γ, a ^ 3 = 1 → a * b ≠ b * a → r * a = a * r → r ^ 3 = 1) :
    ∃ B : Subgroup Γ, Z ≤ B ∧ 27 ≤ Nat.card B ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      ∀ x ∈ B, x ^ 3 = 1 := by
  classical
  have hfin : Finite Z := hZ.finite_Z
  have : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  set Γ₀ : Subgroup Γ := hZ.cubeHom.ker with hΓ₀
  have hZΓ₀ : Z ≤ Γ₀ := fun z hz => (hZ.mem_ker_cubeHom).2 (hZ.pow_three_eq_one hz)
  have hΓ₀card : 27 ≤ Nat.card Γ₀ := hZ.card_ker_cubeHom_ge hΓ
  by_cases hab : ∀ x ∈ Γ₀, ∀ y ∈ Γ₀, x * y = y * x
  · exact ⟨Γ₀, hZΓ₀, hΓ₀card, hab, fun x hx => (hZ.mem_ker_cubeHom).1 hx⟩
  · push Not at hab
    obtain ⟨a, ha, b, hb, hne⟩ := hab
    have ha3 : a ^ 3 = 1 := (hZ.mem_ker_cubeHom).1 ha
    have hbC : b ∉ Subgroup.centralizer ({a} : Set Γ) := fun h =>
      hne (Subgroup.mem_centralizer_singleton_iff.mp h).symm
    have hCcard : 27 ≤ Nat.card (Subgroup.centralizer ({a} : Set Γ)) :=
      hZ.card_centralizer_ge hΓ a
    by_cases htop : Γ₀ = ⊤
    ·
      set C : Subgroup Γ := Subgroup.centralizer ({a} : Set Γ) with hC
      have hC81 : Nat.card C ≠ 81 := by
        intro h
        apply hbC
        have : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [h, hΓ])
        rw [this]
        exact Subgroup.mem_top _
      have hC27 : Nat.card C = 27 := by
        have hdvd : Nat.card C ∣ 81 := hΓ ▸ Subgroup.card_subgroup_dvd_card C
        have hle : Nat.card C ≤ 81 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases hn : Nat.card C <;> omega
      have hZC : Z ≤ C := fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.2 (hZ.mul_central hz a).symm
      have hall : ∀ x : Γ, x ^ 3 = 1 := fun x =>
        (hZ.mem_ker_cubeHom).1 (by rw [← hΓ₀, htop]; exact Subgroup.mem_top x)
      refine ⟨C, hZC, hC27.ge, ?_, fun x _ => hall x⟩
      have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
      let a' : C := ⟨a, haC⟩
      have ha'c : a' ∈ Subgroup.center C := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have hZ'le : Z.subgroupOf C ≤ Subgroup.center C := by
        intro g hg
        rw [Subgroup.mem_center_iff]
        intro g'
        exact Subtype.ext (hZ.mul_central hg g')
      have hZ'card : Nat.card (Z.subgroupOf C) = 3 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZ.card_Z]
      have ha'Z' : a' ∉ Z.subgroupOf C := by
        intro h
        apply hne
        exact (hZ.mul_central h b).symm
      have hcen9 : 9 ≤ Nat.card (Subgroup.center C) := by
        have hdvd1 : 3 ∣ Nat.card (Subgroup.center C) :=
          hZ'card ▸ Subgroup.card_dvd_of_le hZ'le
        have hdvd2 : Nat.card (Subgroup.center C) ∣ 27 :=
          hC27 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center C)
        have hne3 : Nat.card (Subgroup.center C) ≠ 3 := by
          intro h3
          have : Z.subgroupOf C = Subgroup.center C :=
            Subgroup.eq_of_le_of_card_ge hZ'le (by rw [h3, hZ'card])
          exact ha'Z' (this ▸ ha'c)
        have hle : Nat.card (Subgroup.center C) ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd2
        have hpos : 0 < Nat.card (Subgroup.center C) := Nat.card_pos
        interval_cases hn : Nat.card (Subgroup.center C) <;> omega
      have hcyc : IsCyclic (C ⧸ Subgroup.center C) := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        refine isCyclic_of_card_dvd_prime (p := 3) ?_
        have h1 := Subgroup.card_mul_index (Subgroup.center C)
        rw [hC27] at h1
        have h2 : Nat.card (C ⧸ Subgroup.center C) = (Subgroup.center C).index := rfl
        rw [h2]
        have hle : (Subgroup.center C).index ≤ 3 := by
          by_contra hlt
          push Not at hlt
          have : 9 * 4 ≤ Nat.card (Subgroup.center C) * (Subgroup.center C).index :=
            Nat.mul_le_mul hcen9 hlt
          omega
        have hdvd : (Subgroup.center C).index ∣ 27 := Dvd.intro_left _ h1
        interval_cases hn : (Subgroup.center C).index <;> omega
      intro x hx y hy
      have := hcyc
      have := (isMulCommutative_of_isCyclic_quotient_center_self C).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    · exfalso
      have hΓ₀27 : Nat.card Γ₀ = 27 := by
        have hdvd : Nat.card Γ₀ ∣ 81 := hΓ ▸ Subgroup.card_subgroup_dvd_card Γ₀
        have hle : Nat.card Γ₀ ≤ 81 := Nat.le_of_dvd (by norm_num) hdvd
        have hne81 : Nat.card Γ₀ ≠ 81 := fun h =>
          htop (Subgroup.eq_top_of_card_eq Γ₀ (by rw [h, hΓ]))
        interval_cases hn : Nat.card Γ₀ <;> omega
      have hCnot : ¬ Subgroup.centralizer ({a} : Set Γ) ≤ Γ₀ := by
        intro hle
        have heq : Subgroup.centralizer ({a} : Set Γ) = Γ₀ :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hΓ₀27]; exact hCcard)
        exact hbC (heq ▸ hb)
      obtain ⟨r, hrC, hrΓ₀⟩ := Set.not_subset.mp hCnot
      have hr3 := hR a b r ha3 hne (Subgroup.mem_centralizer_singleton_iff.mp hrC)
      exact hrΓ₀ ((hZ.mem_ker_cubeHom).2 hr3)

end CentralData

theorem card_comap_eq {U W : Type*} [Group U] [Group W] (ρ : U →* W) {S : Subgroup W}
    (hS : S ≤ ρ.range) : Nat.card (S.comap ρ) = Nat.card ρ.ker * Nat.card S := by
  set Γ : Subgroup U := S.comap ρ with hΓ
  set f' : Γ →* W := ρ.comp Γ.subtype with hf'
  have hrange : f'.range = S := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hw
      obtain ⟨u, rfl⟩ := hS hw
      exact ⟨⟨u, hw⟩, rfl⟩
  have hker : f'.ker = ρ.ker.subgroupOf Γ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hle : ρ.ker ≤ Γ := fun z hz => by
    rw [hΓ, Subgroup.mem_comap, (MonoidHom.mem_ker).1 hz]
    exact S.one_mem
  have hcard : Nat.card f'.ker = Nat.card ρ.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← Subgroup.card_ker_mul_card_range f', hrange, hcard]

theorem card_eq_card_ker_mul_card_map {U W : Type*} [Group U] [Group W] (ρ : U →* W)
    {B : Subgroup U} (hB : ρ.ker ≤ B) :
    Nat.card B = Nat.card ρ.ker * Nat.card (B.map ρ) := by
  set f' : B →* W := ρ.comp B.subtype with hf'
  have hrange : f'.range = B.map ρ := by
    rw [hf', MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f'.ker = ρ.ker.subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hcard : Nat.card f'.ker = Nat.card ρ.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  rw [← Subgroup.card_ker_mul_card_range f', hrange, hcard]

theorem exists_abelian_exp_three_of_comap {U W : Type*} [Group U] [Group W] (ρ : U →* W)
    (S : Subgroup W) (hker : ρ.ker ≤ Subgroup.center U) (hZ : Nat.card ρ.ker = 3)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS3 : ∀ x ∈ S, x ^ 3 = 1)
    (hSr : S ≤ ρ.range) (hS27 : Nat.card S = 27)
    (hR : ∀ a b r : U, ρ a ∈ S → ρ b ∈ S → ρ r ∈ S → a ^ 3 = 1 → a * b ≠ b * a →
      r * a = a * r → r ^ 3 = 1) :
    ∃ B : Subgroup U, ρ.ker ≤ B ∧ (∀ x ∈ B, ρ x ∈ S) ∧ 27 ≤ Nat.card B ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ∀ x ∈ B, x ^ 3 = 1 := by
  set Γ : Subgroup U := S.comap ρ with hΓ
  have hkerΓ : ρ.ker ≤ Γ := fun z hz => by
    rw [hΓ, Subgroup.mem_comap, (MonoidHom.mem_ker).1 hz]
    exact S.one_mem
  have hΓcard : Nat.card Γ = 81 := by
    rw [hΓ, card_comap_eq ρ hSr, hZ, hS27]
  set Z : Subgroup Γ := ρ.ker.subgroupOf Γ with hZdef
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerΓ).toEquiv, hZ]
  have hcd : CentralData Z := by
    refine ⟨?_, hZcard, ?_, ?_⟩
    · intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.1 (hker hz)) g)
    · intro x y
      rw [hZdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      have hc := hSc _ x.2 _ y.2
      have h1 : ρ ⁅(x : U), (y : U)⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hc
      simpa [commutatorElement_def] using h1
    · intro x
      rw [hZdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow]
      exact hS3 _ x.2
  obtain ⟨B', hZB', hB'27, hB'c, hB'3⟩ := hcd.exists_abelian_exp_three hΓcard
    (fun a b r ha3 hab hra => by
      apply Subtype.ext
      have := hR a b r a.2 b.2 r.2 (congrArg Subtype.val ha3) (fun h => hab (Subtype.ext h))
        (congrArg Subtype.val hra)
      simpa using this)
  refine ⟨B'.map Γ.subtype, fun z hz => ⟨⟨z, hkerΓ hz⟩, hZB' hz, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, -, rfl⟩
    exact b.2
  · rw [Subgroup.card_map_of_injective Γ.subtype_injective]
    exact hB'27
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    exact congrArg Subtype.val (hB'c b hb b' hb')
  · rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hB'3 b hb)

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
