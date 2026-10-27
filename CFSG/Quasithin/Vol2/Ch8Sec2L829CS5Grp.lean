module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

theorem mem_of_normalizes_sylowTwo_cs5 {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y}
    (hS : IsSylowTwoOf S X) {x : Y} (hx : x ∈ X) (hxN : x ∈ Subgroup.normalizer (S : Set Y))
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ S := by
  obtain ⟨hSX, hS2, hodd⟩ := hS
  obtain ⟨k, hk⟩ := hx2
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := k)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hk)
  have hK2 : IsPGroup 2 (Subgroup.zpowers x ⊔ S : Subgroup Y) :=
    IsPGroup.to_sup_of_normal_right' hzp hS2 (Subgroup.zpowers_le.mpr hxN)
  have hKX : (Subgroup.zpowers x ⊔ S : Subgroup Y) ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr hx) hSX
  have hSK : S ≤ (Subgroup.zpowers x ⊔ S : Subgroup Y) := le_sup_right
  have hodd0 : ¬ 2 ∣ S.relIndex X := hodd
  have h1 : S.relIndex (Subgroup.zpowers x ⊔ S) * (Subgroup.zpowers x ⊔ S).relIndex X
      = S.relIndex X :=
    Subgroup.relIndex_mul_relIndex S _ X hSK hKX
  have hodd1 : ¬ 2 ∣ S.relIndex (Subgroup.zpowers x ⊔ S) :=
    fun h => hodd0 (by rw [← h1]; exact h.mul_right _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hK2.index (S.subgroupOf (Subgroup.zpowers x ⊔ S))
  have hm' : S.relIndex (Subgroup.zpowers x ⊔ S) = 2 ^ m := hm
  have hm0 : m = 0 := by
    by_contra hm0
    exact hodd1 (by rw [hm']; exact dvd_pow_self 2 hm0)
  have hle : (Subgroup.zpowers x ⊔ S : Subgroup Y) ≤ S :=
    Subgroup.relIndex_eq_one.mp (by rw [hm', hm0, pow_zero])
  exact hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem card_mul_le_card_sup_cs5 {Y : Type} [Group Y] [Finite Y] {A B : Subgroup Y}
    (h : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun ab : A × B => (⟨(ab.1 : Y) * ab.2, mul_mem (Subgroup.mem_sup_left ab.1.2)
      (Subgroup.mem_sup_right ab.2.2)⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have hab' : (a : Y) * b = a' * b' := congrArg Subtype.val hab
  have hmem : (a' : Y)⁻¹ * a ∈ A ⊓ B := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    have heq : (a' : Y)⁻¹ * a = (b' : Y) * (b : Y)⁻¹ := by
      calc (a' : Y)⁻¹ * a = (a' : Y)⁻¹ * ((a : Y) * b) * (b : Y)⁻¹ := by group
        _ = (a' : Y)⁻¹ * ((a' : Y) * b') * (b : Y)⁻¹ := by rw [hab']
        _ = (b' : Y) * (b : Y)⁻¹ := by group
    rw [heq]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [h, Subgroup.mem_bot] at hmem
  have ha : (a : Y) = a' := (inv_mul_eq_one.mp hmem).symm
  have hb : (b : Y) = b' := by
    rw [ha] at hab'
    exact mul_left_cancel hab'
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem eq_top_of_simple_card_sixty_cs5 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) {W : Subgroup X} (hW : 16 ≤ Nat.card W) : W = ⊤ := by
  by_contra hWtop
  have hidx : W.index ≤ 3 := by
    have h1 := W.card_mul_index
    rw [hX] at h1
    by_contra hlt
    have h4 : 4 ≤ W.index := by omega
    have h2 := Nat.mul_le_mul hW h4
    rw [h1] at h2
    omega
  rcases Subgroup.Normal.eq_bot_or_eq_top (MulAction.toPermHom X (X ⧸ W)).ker with hker | hker
  · have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ W)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm] at hcard
    have hc : Nat.card (X ⧸ W) = W.index := rfl
    rw [hc, hX] at hcard
    have h6 := Nat.factorial_le hidx
    have h3 : Nat.factorial 3 = 6 := rfl
    omega
  · apply hWtop
    have hnc : W.normalCore = ⊤ := by
      rw [Subgroup.normalCore_eq_ker]
      exact hker
    have hle : (⊤ : Subgroup X) ≤ W := by
      rw [← hnc]
      exact W.normalCore_le
    exact eq_top_iff.mpr hle

theorem isSolvable_normalizer_of_borel_cs5 {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y}
    [X.Normal] (hSX : S ≤ X) (hYX : IsPGroup 2 (Y ⧸ X))
    (hB : Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (S : Set Y))) :
    Group.IsSolvable ↥(Subgroup.normalizer (S : Set Y)) := by
  clear hSX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : Group.IsSolvable (Y ⧸ X) := by
    have := hYX.isNilpotent
    infer_instance
  let f : ↥(X ⊓ Subgroup.normalizer (S : Set Y)) →* ↥(Subgroup.normalizer (S : Set Y)) :=
    Subgroup.inclusion inf_le_right
  let g : ↥(Subgroup.normalizer (S : Set Y)) →* (Y ⧸ X) :=
    (QuotientGroup.mk' X).comp (Subgroup.normalizer (S : Set Y)).subtype
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro n hn
  rw [MonoidHom.mem_ker] at hn
  have hnX : (n : Y) ∈ X := (QuotientGroup.eq_one_iff (n : Y)).mp hn
  exact MonoidHom.mem_range.mpr ⟨⟨(n : Y), Subgroup.mem_inf.mpr ⟨hnX, n.2⟩⟩, rfl⟩

theorem eq_one_of_centralizes_normal_cs5 {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y}
    [X.Normal] (hZ : Subgroup.center ↥X = ⊥) (hYX : IsPGroup 2 (Y ⧸ X))
    (hO : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∀ y : Y, (∀ x ∈ X, y * x = x * y) → y = 1 := by
  intro y hy
  have hCn : (Subgroup.centralizer (X : Set Y)).Normal := Subgroup.normal_centralizer
  have hCX : Subgroup.centralizer (X : Set Y) ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcC, hcX⟩ := Subgroup.mem_inf.mp hc
    have hcZ : (⟨c, hcX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC (g : Y) g.2)
    rw [hZ, Subgroup.mem_bot] at hcZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcZ
  have hCp : IsPGroup 2 (Subgroup.centralizer (X : Set Y)) := by
    let f : ↥(Subgroup.centralizer (X : Set Y)) →* (Y ⧸ X) :=
      (QuotientGroup.mk' X).comp (Subgroup.centralizer (X : Set Y)).subtype
    refine hYX.of_injective f ?_
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcX : (c : Y) ∈ X := (QuotientGroup.eq_one_iff (c : Y)).mp hc
    have hcb : (c : Y) ∈ Subgroup.centralizer (X : Set Y) ⊓ X :=
      Subgroup.mem_inf.mpr ⟨c.2, hcX⟩
    rw [hCX, Subgroup.mem_bot] at hcb
    exact Subtype.ext hcb
  have hCbot := hO _ hCn hCp
  have hyC : y ∈ Subgroup.centralizer (X : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr (fun x hx => (hy x hx).symm)
  rw [hCbot, Subgroup.mem_bot] at hyC
  exact hyC

theorem exists_fixed_mem_coset_cs5 {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {x : Y} (hx : ∃ k : ℕ, x ^ p ^ k = 1) {P : Subgroup Y} (hP : IsPGroup 2 P)
    (hxP : x ∈ Subgroup.normalizer (P : Set Y)) {i : Y} (hi : x * i * x⁻¹ * i⁻¹ ∈ P) :
    ∃ q ∈ P, x * (q * i) * x⁻¹ = q * i := by
  have hpp : Nat.Prime p := Fact.out
  have hconj : ∀ r ∈ P, x * r * x⁻¹ ∈ P := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hxP r).mp hr
  have hconj' : ∀ r ∈ P, x⁻¹ * r * x ∈ P := by
    intro r hr
    have hxi : x⁻¹ ∈ Subgroup.normalizer (P : Set Y) :=
      (Subgroup.normalizer (P : Set Y)).inv_mem hxP
    have h := (Subgroup.mem_normalizer_iff.mp hxi r).mp hr
    rwa [inv_inv] at h
  have hi' : x⁻¹ * i * x * i⁻¹ ∈ P := by
    have e : x⁻¹ * i * x * i⁻¹ = x⁻¹ * (x * i * x⁻¹ * i⁻¹)⁻¹ * x := by group
    rw [e]
    exact hconj' _ (P.inv_mem hi)
  set Ω : Set Y := {ω | ω * i⁻¹ ∈ P}
  have hΩ : ∀ ω : Y, ω ∈ Ω ↔ ω * i⁻¹ ∈ P := fun ω => Iff.rfl
  have hxN : x ∈ Subgroup.normalizer Ω := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    rw [hΩ, hΩ]
    constructor
    · intro hh
      have e : x * h * x⁻¹ * i⁻¹ = (x * (h * i⁻¹) * x⁻¹) * (x * i * x⁻¹ * i⁻¹) := by group
      rw [e]
      exact P.mul_mem (hconj _ hh) hi
    · intro hh
      have e : h * i⁻¹ = (x⁻¹ * (x * h * x⁻¹ * i⁻¹) * x) * (x⁻¹ * i * x * i⁻¹) := by group
      rw [e]
      exact P.mul_mem (hconj' _ hh) hi'
  have hH : Subgroup.zpowers x ≤ Subgroup.normalizer Ω := Subgroup.zpowers_le.mpr hxN
  have hact : ∀ (h : Subgroup.zpowers x) (ω : ↥Ω), (h : Y) * (ω : Y) * (h : Y)⁻¹ ∈ Ω :=
    fun h ω => (Subgroup.mem_set_normalizer_iff.mp (hH h.2) (ω : Y)).mp ω.2
  letI act : MulAction (Subgroup.zpowers x) ↥Ω :=
    { smul := fun h ω => ⟨(h : Y) * (ω : Y) * (h : Y)⁻¹, hact h ω⟩
      one_smul := fun ω => Subtype.ext (by
        show ((1 : Subgroup.zpowers x) : Y) * (ω : Y) * ((1 : Subgroup.zpowers x) : Y)⁻¹ = (ω : Y)
        simp)
      mul_smul := fun a b ω => Subtype.ext (by
        show ((a * b : Subgroup.zpowers x) : Y) * (ω : Y) * ((a * b : Subgroup.zpowers x) : Y)⁻¹
          = (a : Y) * ((b : Y) * (ω : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨k, hk⟩ := hx
  have hHp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := k)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hk)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  let eP : ↥P ≃ ↥Ω :=
    { toFun := fun q => ⟨(q : Y) * i, (hΩ _).mpr (by rw [mul_inv_cancel_right]; exact q.2)⟩
      invFun := fun ω => ⟨(ω : Y) * i⁻¹, (hΩ _).mp ω.2⟩
      left_inv := fun q => Subtype.ext (by simp)
      right_inv := fun ω => Subtype.ext (by simp) }
  have hmod := hHp.card_modEq_card_fixedPoints ↥Ω
  rw [← Nat.card_congr eP, hn] at hmod
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) ↥Ω) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have hdvd : p ∣ 2 ^ n := Nat.modEq_zero_iff_dvd.mp hmod
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))
  obtain ⟨⟨a⟩, -⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hfix)
  have hfixa := MulAction.mem_fixedPoints.mp a.2 ⟨x, Subgroup.mem_zpowers x⟩
  have hxa : x * ((a : ↥Ω) : Y) * x⁻¹ = ((a : ↥Ω) : Y) := congrArg Subtype.val hfixa
  refine ⟨((a : ↥Ω) : Y) * i⁻¹, (hΩ _).mp (a : ↥Ω).2, ?_⟩
  rw [inv_mul_cancel_right]
  exact hxa

end CFSG.Quasithin.H13

end
