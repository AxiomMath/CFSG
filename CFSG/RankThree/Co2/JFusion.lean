module

public import Mathlib.GroupTheory.Nilpotent

public section

open scoped Pointwise

namespace CFSG.RankThree.Co2

variable {G : Type*} [Group G]

@[expose] def ElemTwo (A : Subgroup G) : Prop :=
  (∀ a ∈ A, a * a = 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

theorem ElemTwo.conj {A : Subgroup G} (h : ElemTwo A) (y : G) :
    ElemTwo (A.map (MulAut.conj y).toMonoidHom) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [h.1 a ha]; group
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * a * y⁻¹ * (y * b * y⁻¹) = y * (a * b) * y⁻¹ := by group
      _ = y * (b * a) * y⁻¹ := by rw [h.2 a ha b hb]
      _ = y * b * y⁻¹ * (y * a * y⁻¹) := by group

theorem card_subgroupOf_eq {T C : Subgroup G} (hTC : T ≤ C) :
    Nat.card (T.subgroupOf C) = Nat.card T :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv

@[expose, instance_reducible] def conjActOn (V K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (V : Set G)) : MulAction K V where
  smul k v := ⟨(k : G) * v * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hK k.2) v).1 v.2⟩
  one_smul v := by apply Subtype.ext; change (1 : G) * v * 1⁻¹ = v; group
  mul_smul k l v := by
    apply Subtype.ext
    change ((k : G) * l) * v * ((k : G) * l)⁻¹ = k * (l * v * (l : G)⁻¹) * (k : G)⁻¹
    group

theorem map_conj_mul (J : Subgroup G) (g h : G) :
    (J.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      J.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mem_normalizer_of_map_eq {J : Subgroup G} {n : G}
    (h : J.map (MulAut.conj n).toMonoidHom = J) : n ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    rw [← h]
    exact ⟨j, hj, rfl⟩
  · intro hj
    rw [← h] at hj
    obtain ⟨k, hk, e⟩ := hj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have : k = j := by
      have := congrArg (fun x => n⁻¹ * x * n) e
      simpa [mul_assoc] using this
    rwa [← this]

theorem exists_normalizer_conj_of_class {z : G} {J : Subgroup G} (hJ : ElemTwo J)
    (hcls : ∀ A : Subgroup G, A ≤ Subgroup.centralizer {z} → ElemTwo A →
      Nat.card A = Nat.card J →
        ∃ h ∈ Subgroup.centralizer {z}, A = J.map (MulAut.conj h).toMonoidHom)
    {t : G} (htJ : t ∈ J) (hzt : IsConj z t) :
    ∃ n ∈ Subgroup.normalizer (J : Set G), n * z * n⁻¹ = t := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hzt
  set A := J.map (MulAut.conj g⁻¹).toMonoidHom with hAdef
  have hAH : A ≤ Subgroup.centralizer {z} := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hjt := hJ.2 j hj t htJ
    rw [← hg] at hjt
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * j * g * z = g⁻¹ * (j * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * j) * g := by rw [hjt]
      _ = z * (g⁻¹ * j * g) := by group
  obtain ⟨h, hh, hA⟩ := hcls A hAH (hJ.conj g⁻¹)
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective)
  refine ⟨g * h, mem_normalizer_of_map_eq ?_, ?_⟩
  · rw [← map_conj_mul, ← hA, hAdef, map_conj_mul, mul_inv_cancel]
    ext x
    simp
  · rw [Subgroup.mem_centralizer_singleton_iff] at hh
    calc g * h * z * (g * h)⁻¹ = g * (h * z) * h⁻¹ * g⁻¹ := by group
      _ = g * (z * h) * h⁻¹ * g⁻¹ := by rw [hh]
      _ = t := by rw [← hg]; group

theorem elemTwo_closure {S : Set G} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hs : ∀ a ∈ S, a * a = 1) : ElemTwo (Subgroup.closure S) := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hc b hb a ha
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.1 (h1 hb)) a ha).symm
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (h2 hb)) a ha
  refine ⟨fun a ha => ?_, hcomm⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← hcomm x hx y hy, mul_assoc, mul_assoc]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem mem_normalizer_of_conj_mem {J : Subgroup G} [Finite J] {g : G}
    (h : ∀ j ∈ J, g * j * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  apply mem_normalizer_of_map_eq
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨j, hj, rfl⟩
    exact h j hj
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

variable [Finite G]

theorem centralizes_of_prime_order {V : Subgroup G} {s : G} {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hs : orderOf s = p) (hsN : s ∈ Subgroup.normalizer (V : Set G)) {a : ℕ}
    (hV : Nat.card V = 2 ^ a) (hpa : ∀ c, 1 ≤ c → c ≤ a → ¬ p ∣ 2 ^ c - 1) :
    ∀ v ∈ V, s * v = v * s := by
  set K := Subgroup.zpowers s
  have hK : K ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le]; exact hsN
  let _ := conjActOn V K hK
  have hKp : IsPGroup p K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hmod := hKp.card_modEq_card_fixedPoints V
  let F : Subgroup V :=
    { carrier := MulAction.fixedPoints K V
      one_mem' := fun k => by apply Subtype.ext; change (k : G) * 1 * (k : G)⁻¹ = 1; group
      mul_mem' := fun {x y} hx hy k => by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hx k)
        have h2 := congrArg Subtype.val (hy k)
        change (k : G) * x * (k : G)⁻¹ = x at h1
        change (k : G) * y * (k : G)⁻¹ = y at h2
        change (k : G) * (x * y) * (k : G)⁻¹ = x * y
        calc (k : G) * (x * y) * (k : G)⁻¹ =
            ((k : G) * x * (k : G)⁻¹) * ((k : G) * y * (k : G)⁻¹) := by group
          _ = x * y := by rw [h1, h2]
      inv_mem' := fun {x} hx k => by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hx k)
        change (k : G) * x * (k : G)⁻¹ = x at h1
        change (k : G) * (x : G)⁻¹ * (k : G)⁻¹ = (x : G)⁻¹
        calc (k : G) * (x : G)⁻¹ * (k : G)⁻¹ = ((k : G) * x * (k : G)⁻¹)⁻¹ := by group
          _ = (x : G)⁻¹ := by rw [h1] }
  have hFcard : Nat.card (MulAction.fixedPoints K V) = Nat.card F := rfl
  obtain ⟨b, hb, hFb⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (hV ▸ Subgroup.card_subgroup_dvd_card F)
  have hba : b = a := by
    by_contra hne
    have hlt : b < a := lt_of_le_of_ne hb hne
    rw [hV, hFcard, hFb] at hmod
    have hdvd : p ∣ 2 ^ a - 2 ^ b :=
      (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hb)).1 hmod.symm
    have hfac : 2 ^ a - 2 ^ b = 2 ^ b * (2 ^ (a - b) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hb]
    rw [hfac] at hdvd
    have hcop : Nat.Coprime p (2 ^ b) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
    exact hpa (a - b) (by omega) (by omega) (hcop.dvd_of_dvd_mul_left hdvd)
  have htop : F = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hFb, hba, hV]
  intro v hv
  have hfix : (⟨v, hv⟩ : V) ∈ F := by rw [htop]; exact Subgroup.mem_top _
  have := congrArg Subtype.val (hfix ⟨s, Subgroup.mem_zpowers s⟩)
  change s * v * s⁻¹ = v at this
  calc s * v = s * v * s⁻¹ * s := by group
    _ = v * s := by rw [this]

theorem centralizes_or_fixed_trivial {V : Subgroup G} {s : G} {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hs : orderOf s = p) (hsN : s ∈ Subgroup.normalizer (V : Set G)) {a : ℕ}
    (hV : Nat.card V = 2 ^ a) (hpa : ∀ c, 1 ≤ c → c < a → ¬ p ∣ 2 ^ c - 1) :
    (∀ v ∈ V, s * v = v * s) ∨ (∀ v ∈ V, s * v = v * s → v = 1) := by
  set K := Subgroup.zpowers s
  have hK : K ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le]; exact hsN
  let _ := conjActOn V K hK
  have hKp : IsPGroup p K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hmod := hKp.card_modEq_card_fixedPoints V
  let F : Subgroup V :=
    { carrier := MulAction.fixedPoints K V
      one_mem' := fun k => by apply Subtype.ext; change (k : G) * 1 * (k : G)⁻¹ = 1; group
      mul_mem' := fun {x y} hx hy k => by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hx k)
        have h2 := congrArg Subtype.val (hy k)
        change (k : G) * x * (k : G)⁻¹ = x at h1
        change (k : G) * y * (k : G)⁻¹ = y at h2
        change (k : G) * (x * y) * (k : G)⁻¹ = x * y
        calc (k : G) * (x * y) * (k : G)⁻¹ =
            ((k : G) * x * (k : G)⁻¹) * ((k : G) * y * (k : G)⁻¹) := by group
          _ = x * y := by rw [h1, h2]
      inv_mem' := fun {x} hx k => by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hx k)
        change (k : G) * x * (k : G)⁻¹ = x at h1
        change (k : G) * (x : G)⁻¹ * (k : G)⁻¹ = (x : G)⁻¹
        calc (k : G) * (x : G)⁻¹ * (k : G)⁻¹ = ((k : G) * x * (k : G)⁻¹)⁻¹ := by group
          _ = (x : G)⁻¹ := by rw [h1] }
  have hFcard : Nat.card (MulAction.fixedPoints K V) = Nat.card F := rfl
  obtain ⟨b, hb, hFb⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (hV ▸ Subgroup.card_subgroup_dvd_card F)
  have hmem : ∀ v (hv : v ∈ V), s * v = v * s → (⟨v, hv⟩ : V) ∈ F := by
    intro v hv hsv k
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 k.2
    apply Subtype.ext
    change (k : G) * v * (k : G)⁻¹ = v
    have hc : Commute s v := hsv
    rw [← hn, (hc.zpow_left n).eq, mul_inv_cancel_right]
  by_cases hba : b = a
  · left
    have htop : F = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hFb, hba, hV]
    intro v hv
    have hfix : (⟨v, hv⟩ : V) ∈ F := by rw [htop]; exact Subgroup.mem_top _
    have := congrArg Subtype.val (hfix ⟨s, Subgroup.mem_zpowers s⟩)
    change s * v * s⁻¹ = v at this
    calc s * v = s * v * s⁻¹ * s := by group
      _ = v * s := by rw [this]
  · right
    rw [hV, hFcard, hFb] at hmod
    have hdvd : p ∣ 2 ^ a - 2 ^ b :=
      (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hb)).1 hmod.symm
    have hfac : 2 ^ a - 2 ^ b = 2 ^ b * (2 ^ (a - b) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hb]
    rw [hfac] at hdvd
    have hcop : Nat.Coprime p (2 ^ b) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
    have hd := hcop.dvd_of_dvd_mul_left hdvd
    have hb0 : b = 0 := by
      by_contra hb0
      exact hpa (a - b) (by omega) (by omega) hd
    intro v hv hsv
    have hvF := hmem v hv hsv
    have hF1 : Nat.card F = 1 := by rw [hFb, hb0, pow_zero]
    rw [Subgroup.card_eq_one.1 hF1] at hvF
    exact congrArg Subtype.val ((Subgroup.mem_bot).1 hvF)

theorem dvd_card_of_no_fixed {K X : Type*} [Group K] [MulAction K X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hK : IsPGroup p K) (hfix : ∀ x : X, ∃ k : K, k • x ≠ x) :
    p ∣ Nat.card X := by
  have hmod := hK.card_modEq_card_fixedPoints X
  have h0 : Nat.card (MulAction.fixedPoints K X) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hfix x
    exact hk (hx k)
  rw [h0] at hmod
  exact Nat.modEq_zero_iff_dvd.1 hmod

theorem exists_sylow_eq_of_normalizer_le {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {T : Subgroup C} (hT : IsPGroup p T) (hN : Subgroup.normalizer (T : Set C) ≤ T) :
    ∃ P : Sylow p C, (P : Subgroup C) = T := by
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  refine ⟨P, ?_⟩
  by_contra hne
  have hlt : T.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm _ hP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ T.subgroupOf P := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := P)
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  apply hxT
  rw [Subgroup.mem_subgroupOf]
  apply hN
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have hwP : w ∈ (P : Subgroup C) := hP hw
    have := (Subgroup.mem_normalizer_iff.1 hxN ⟨w, hwP⟩).1 (Subgroup.mem_subgroupOf.2 hw)
    exact Subgroup.mem_subgroupOf.1 this
  · intro hw
    have hwP : (x : C) * w * (x : C)⁻¹ ∈ (P : Subgroup C) := hP hw
    have hw' : w ∈ (P : Subgroup C) := by
      have := (P : Subgroup C).mul_mem
        ((P : Subgroup C).mul_mem ((P : Subgroup C).inv_mem x.2) hwP) x.2
      simpa [mul_assoc] using this
    have := (Subgroup.mem_normalizer_iff.1 hxN ⟨w, hw'⟩).2 (Subgroup.mem_subgroupOf.2 hw)
    exact Subgroup.mem_subgroupOf.1 this

theorem exists_swap_normalizing {p : ℕ} [Fact p.Prime]
    {z t y : G} (hy1 : y * z * y⁻¹ = t) (hy2 : y * t * y⁻¹ = z) {Q : Subgroup G}
    (hQ : Q ≤ Subgroup.centralizer {z} ⊓ Subgroup.centralizer {t})
    (hQp : Nat.card Q =
      p ^ (Nat.card ↥(Subgroup.centralizer {z} ⊓ Subgroup.centralizer {t})).factorization p) :
    ∃ y' : G, y' * z * y'⁻¹ = t ∧ y' * t * y'⁻¹ = z ∧
      Q.map (MulAut.conj y').toMonoidHom = Q := by
  set D := Subgroup.centralizer {z} ⊓ Subgroup.centralizer {t} with hD
  have hyD : ∀ x ∈ D, y * x * y⁻¹ ∈ D := by
    intro x hx
    obtain ⟨hxz, hxt⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxz hxt
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · rw [← hy2]
      calc y * x * y⁻¹ * (y * t * y⁻¹) = y * (x * t) * y⁻¹ := by group
        _ = y * (t * x) * y⁻¹ := by rw [hxt]
        _ = y * t * y⁻¹ * (y * x * y⁻¹) := by group
    · rw [← hy1]
      calc y * x * y⁻¹ * (y * z * y⁻¹) = y * (x * z) * y⁻¹ := by group
        _ = y * (z * x) * y⁻¹ := by rw [hxz]
        _ = y * z * y⁻¹ * (y * x * y⁻¹) := by group
  set Q₂ := Q.map (MulAut.conj y).toMonoidHom
  have hQ₂ : Q₂ ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hyD x (hQ hx)
  have hc1 : Nat.card (Q.subgroupOf D) = p ^ (Nat.card D).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv, hQp]
  have hc2 : Nat.card (Q₂.subgroupOf D) = p ^ (Nat.card D).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₂).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj y).injective, hQp]
  set P₁ : Sylow p D := Sylow.ofCard _ hc1
  set P₂ : Sylow p D := Sylow.ofCard _ hc2
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D P₁ P₂
  have hdQ : Q.map (MulAut.conj (d : G)).toMonoidHom = Q₂ := by
    ext x
    have key : ∀ w : D, (w ∈ (P₂ : Subgroup D)) ↔ (w : G) ∈ Q₂ := fun w => Iff.rfl
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqD : q ∈ D := hQ hq
      have : d * ⟨q, hqD⟩ * d⁻¹ ∈ (P₂ : Subgroup D) := by
        rw [← hd, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj d) _
          (show (⟨q, hqD⟩ : D) ∈ (P₁ : Subgroup D) from hq)
      exact (key _).1 this
    · intro hx
      have hxD : x ∈ D := hQ₂ hx
      have : (⟨x, hxD⟩ : D) ∈ (P₂ : Subgroup D) := hx
      rw [← hd, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
      refine ⟨(d : G)⁻¹ * x * d, this, ?_⟩
      simp [mul_assoc]
  refine ⟨(d : G)⁻¹ * y, ?_, ?_, ?_⟩
  · have hdt : (d : G) * t = t * d :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 d.2).2
    calc (d : G)⁻¹ * y * z * ((d : G)⁻¹ * y)⁻¹ = (d : G)⁻¹ * (y * z * y⁻¹) * d := by group
      _ = (d : G)⁻¹ * (t * d) := by rw [hy1, mul_assoc]
      _ = t := by rw [← hdt]; group
  · have hdz : (d : G) * z = z * d :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 d.2).1
    calc (d : G)⁻¹ * y * t * ((d : G)⁻¹ * y)⁻¹ = (d : G)⁻¹ * (y * t * y⁻¹) * d := by group
      _ = (d : G)⁻¹ * (z * d) := by rw [hy2, mul_assoc]
      _ = z := by rw [← hdz]; group
  · rw [← map_conj_mul, show Q.map (MulAut.conj y).toMonoidHom = Q₂ from rfl, ← hdQ,
      map_conj_mul, inv_mul_cancel]
    ext x
    simp

omit [Finite G] in
theorem card_swap_eq {z t y : G} (hy1 : y * z * y⁻¹ = t)
    (hy2 : y * t * y⁻¹ = z) {Q : Subgroup G} (hQ : Q.map (MulAut.conj y).toMonoidHom = Q)
    (L₁ L₂ L₃ : G → Prop) (h₁ : ∀ x, L₁ (y * x * y⁻¹) ↔ L₁ x)
    (h₂ : ∀ x, L₂ (y * x * y⁻¹) ↔ L₂ x) (h₃ : ∀ x, L₃ (y * x * y⁻¹) ↔ L₃ x) :
    Nat.card {x : Q // L₁ x ∧ L₂ (x * z) ∧ L₃ (x * t)} =
      Nat.card {x : Q // L₁ x ∧ L₂ (x * t) ∧ L₃ (x * z)} := by
  have hmem : ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun x hx => by
    rw [← hQ]; exact ⟨x, hx, rfl⟩
  have hmem' : ∀ x ∈ Q, y⁻¹ * x * y ∈ Q := fun x hx => by
    rw [← hQ] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    simpa [mul_assoc] using hw
  have k1 : ∀ w : G, y * w * y⁻¹ * t = y * (w * z) * y⁻¹ := fun w => by rw [← hy1]; group
  have k2 : ∀ w : G, y * w * y⁻¹ * z = y * (w * t) * y⁻¹ := fun w => by rw [← hy2]; group
  have k3 : ∀ w : G, y * ((y⁻¹ * w * y) * z) * y⁻¹ = w * t := fun w => by rw [← hy1]; group
  have k4 : ∀ w : G, y * ((y⁻¹ * w * y) * t) * y⁻¹ = w * z := fun w => by rw [← hy2]; group
  have k5 : ∀ w : G, y * (y⁻¹ * w * y) * y⁻¹ = w := fun w => by group
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨y * x * y⁻¹, hmem _ x.1.2⟩, ?_⟩
      invFun := fun x => ⟨⟨y⁻¹ * x * y, hmem' _ x.1.2⟩, ?_⟩
      left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
      right_inv := fun x => by apply Subtype.ext; apply Subtype.ext; simp [mul_assoc] }
  · obtain ⟨a, b, c⟩ := x.2
    exact ⟨(h₁ _).2 a, by rw [k1, h₂]; exact b, by rw [k2, h₃]; exact c⟩
  · obtain ⟨a, b, c⟩ := x.2
    refine ⟨?_, ?_, ?_⟩
    · rw [← h₁, k5]; exact a
    · rw [← h₂, k3]; exact b
    · rw [← h₃, k4]; exact c

end CFSG.RankThree.Co2
