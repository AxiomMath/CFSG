module

public import CFSG.RankThree.PartTwo.Sec13.Item13GL
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.KFacts.K74Plane

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Plane

variable {G : Type} [Group G]

theorem eq_bot_or_eq_of_isIrreducibleOn {K B V : Subgroup G}
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B)) (hVB : V ≤ B)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) : V = ⊥ ∨ V = B := by
  have hinv : ∀ φ ∈ Sec4.autIn K B,
      (V.subgroupOf B).map φ.toMonoidHom = V.subgroupOf B := by
    intro φ hφ
    obtain ⟨k, hkN, hkK, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    have hkV := hKV hkK
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨⟨y, hy⟩, hyV, hyx⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hyV
      rw [Subgroup.mem_subgroupOf]
      have : k * y * k⁻¹ = x := congrArg Subtype.val hyx
      show x ∈ V
      rw [← this]
      exact (Subgroup.mem_normalizer_iff.mp hkV y).mp hyV
    · intro hxV
      rw [Subgroup.mem_subgroupOf] at hxV
      have hxB : k⁻¹ * x * k⁻¹⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) x).mp hx
      refine ⟨⟨k⁻¹ * x * k⁻¹⁻¹, hxB⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkV) x).mp hxV
      · apply Subtype.ext
        show k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ = x
        group
  rcases hirr _ hinv with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact (disjoint_iff.mp h ▸ (inf_eq_left.mpr hVB)).symm
  · right
    exact le_antisymm hVB (Subgroup.subgroupOf_eq_top.mp h)

variable {A B : Subgroup G} {a : G}

theorem exists_pow_mul_of_mem (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) {x : G} (hx : x ∈ A) :
    ∃ i : ℕ, i < 3 ∧ ∃ b ∈ B, x = a ^ i * b := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hcomm a haA b (hBA hb), mul_inv_cancel_right]
      exact hb
    · intro hb
      have : a * b * a⁻¹ = b := by
        by_cases hbA : b ∈ A
        · rw [hcomm a haA b hbA, mul_inv_cancel_right]
        · exact absurd (hBA hb) (by
            intro h
            apply hbA
            have := A.mul_mem (A.mul_mem (A.inv_mem haA) h) haA
            simpa [mul_assoc] using this)
      rwa [this] at hb
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hx' : x ∈ ((Subgroup.zpowers a ⊔ B : Subgroup G) : Set G) := by rw [← hAa]; exact hx
  rw [hmul] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := hx'
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  rcases eq_of_mem_zpowers_of_pow_three ha3 hy with h | h | h
  · exact ⟨0, by norm_num, b, hb, by rw [h, pow_zero]⟩
  · exact ⟨1, by norm_num, b, hb, by rw [h, pow_one]⟩
  · exact ⟨2, by norm_num, b, hb, by rw [h]⟩

theorem eq_of_le_of_le_normalizer [Finite G] {K V : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B)) (hVA : V ≤ A)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G)) :
    V = ⊥ ∨ V = Subgroup.zpowers a ∨ V = B ∨ V = A := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hKVB : K ≤ Subgroup.normalizer ((V ⊓ B : Subgroup G) : Set G) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp (hKV hk) x,
      ← Subgroup.mem_normalizer_iff.mp (hKB hk) x]
  rcases eq_bot_or_eq_of_isIrreducibleOn hirr inf_le_right hKVB with h | h
  ·
    by_cases hV1 : V = ⊥
    · exact Or.inl hV1
    right; left
    obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
    have hv1' : v ≠ 1 := fun h' => hv1 (Subtype.ext h')
    have ha3 : a ^ 3 = 1 := hA.2 a haA
    have hcard : Nat.card V * 9 ≤ 27 := by
      have hinj : Function.Injective (fun p : V × B =>
          (⟨(p.1 : G) * p.2, A.mul_mem (hVA p.1.2) (hBA p.2.2)⟩ : A)) := by
        rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
        have e : x * y = x' * y' := congrArg Subtype.val hxy
        have hm : x'⁻¹ * x ∈ V ⊓ B := ⟨V.mul_mem (V.inv_mem hx') hx, by
          have : x'⁻¹ * x = y' * y⁻¹ := by
            calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
              _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [e]
              _ = y' * y⁻¹ := by group
          rw [this]
          exact B.mul_mem hy' (B.inv_mem hy)⟩
        rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hm
        subst hm
        have : y = y' := mul_left_cancel e
        subst this
        rfl
      have := Nat.card_le_card_of_injective _ hinj
      rwa [Nat.card_prod, hB9, h27] at this
    have hVcard : Nat.card V = 3 := by
      have hdvd : Nat.card V ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hVA
      have h1 : Nat.card V ≠ 1 := fun h' => hV1 (Subgroup.card_eq_one.mp h')
      have hle : Nat.card V ≤ 3 := by omega
      interval_cases h' : Nat.card V <;> first | rfl | omega
    have hVv : V = Subgroup.zpowers v := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvV)
      rw [hVcard, Nat.card_zpowers]
      have := orderOf_dvd_of_pow_eq_one (hA.2 v (hVA hvV))
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ this with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hv1'
      · rw [h']
    obtain ⟨i, hi, b, hb, hvab⟩ := exists_pow_mul_of_mem hA haA hAa (hVA hvV)
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hvab
      have : v ∈ V ⊓ B := ⟨hvV, hvab ▸ hb⟩
      rw [h, Subgroup.mem_bot] at this
      exact hv1' this
    have haiB : a ^ i ∉ B := by
      intro hai
      apply haB
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · simpa using hai
      · have : a = (a ^ 2) ^ 2 * (a ^ 3)⁻¹ := by group
        rw [this, ha3, inv_one, mul_one]
        exact B.pow_mem hai 2
    have hKb : ∀ k ∈ K, k * b * k⁻¹ = b := by
      intro k hk
      have hkv : k * v * k⁻¹ ∈ Subgroup.zpowers v := by
        rw [← hVv]
        exact (Subgroup.mem_normalizer_iff.mp (hKV hk) v).mp hvV
      have hkai : k * a ^ i * k⁻¹ = a ^ i := by
        rw [(Commute.pow_right (hKa k hk) i).eq, mul_inv_cancel_right]
      have hkbB : k * b * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hKB hk) b).mp hb
      have hexp : k * v * k⁻¹ = a ^ i * (k * b * k⁻¹) := by
        rw [hvab]
        calc k * (a ^ i * b) * k⁻¹ = (k * a ^ i * k⁻¹) * (k * b * k⁻¹) := by group
          _ = a ^ i * (k * b * k⁻¹) := by rw [hkai]
      rcases eq_of_mem_zpowers_of_pow_three (hA.2 v (hVA hvV)) hkv with h1 | h1 | h1
      · exfalso
        apply hv1'
        have : v = k⁻¹ * (k * v * k⁻¹) * k := by group
        rw [this, h1]
        group
      · rw [hexp, hvab] at h1
        exact mul_left_cancel h1
      · exfalso
        rw [hexp, hvab] at h1
        apply haiB
        have hbA : b ∈ A := hBA hb
        have hkbA : k * b * k⁻¹ ∈ A := hBA hkbB
        have e2 : a ^ i * (k * b * k⁻¹) = a ^ i * a ^ i * (b * b) := by
          rw [h1, pow_two, mul_assoc (a ^ i) b, ← mul_assoc b (a ^ i) b,
            hcomm b hbA (a ^ i) (A.pow_mem haA i)]
          group
        have e3 : a ^ i = (k * b * k⁻¹) * (b * b)⁻¹ := by
          have := mul_left_cancel (e2.trans (mul_assoc _ _ _))
          rw [this]
          group
        rw [e3]
        exact B.mul_mem hkbB (B.inv_mem (B.mul_mem hb hb))
    have hb1 : b = 1 := by
      have hKbn : K ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := fun k hk => by
        have hkC : k ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := hKb k hk
          calc k * b = (k * b * k⁻¹) * k := by group
            _ = b * k := by rw [this]
        exact Subgroup.centralizer_le_normalizer _ hkC
      rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr hb) hKbn with h1 | h1
      · exact Subgroup.zpowers_eq_bot.mp h1
      · exfalso
        have : Nat.card (Subgroup.zpowers b) ≤ 3 := by
          rw [Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.2 b (hBA hb)))
        rw [h1, hB9] at this
        omega
    rw [hb1, mul_one] at hvab
    rw [hVv, hvab]
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · rw [pow_one]
    · apply le_antisymm
      · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2)
      · apply Subgroup.zpowers_le.mpr
        have e : (a ^ 2) ^ 2 = a := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ha3, one_mul]
        have h2 := Subgroup.pow_mem (Subgroup.zpowers (a ^ 2)) (Subgroup.mem_zpowers (a ^ 2)) 2
        rwa [e] at h2
  · right; right
    have hBV : B ≤ V := h ▸ inf_le_left
    have hdvd : Nat.card V ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hVA
    have h9 : 9 ∣ Nat.card V := hB9 ▸ Subgroup.card_dvd_of_le hBV
    have hle : Nat.card V ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
    have : Nat.card V = 9 ∨ Nat.card V = 27 := by
      interval_cases h' : Nat.card V <;> omega
    rcases this with h9' | h27'
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hBV (by rw [h9', hB9])).symm
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hVA (by rw [h27', h27]))

theorem isIrreducibleOn_wStar_of [Finite G] {K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKW : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    (hWB : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G)) :
    Sec21.IsIrreducibleOn (wStar A) := by
  intro V' hV'
  set V := V'.map A.subtype with hVdef
  have hVA : V ≤ A := Subgroup.map_subtype_le V'
  have hWV : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro w hw
    have hφ : ∀ w' (hw' : w' ∈ Subgroup.normalizer (A : Set G)), ∀ x ∈ V,
        w' * x * w'⁻¹ ∈ V := by
      intro w' hw' x hx
      obtain ⟨v, hv, rfl⟩ := hx
      have hmem : A.normalizerMonoidHom ⟨w', hw'⟩ ∈ wStar A :=
        Sec4.mem_autIn_iff.mpr ⟨w', hw', Subgroup.mem_top _, rfl⟩
      have h1 := hV' _ hmem
      have h2 : A.normalizerMonoidHom ⟨w', hw'⟩ v ∈ V' := by
        rw [← h1]
        exact ⟨v, hv, rfl⟩
      exact ⟨_, h2, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hφ w hw x
    · intro hx
      have := hφ w⁻¹ (Subgroup.inv_mem _ hw) _ hx
      simpa [mul_assoc] using this
  rcases eq_of_le_of_le_normalizer hA h27 haA hAa haB hB9 hKa hirr hVA (hKW.trans hWV) hKB with
    h | h | h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).mp h
  · exact absurd (h ▸ hWV) hWa
  · exact absurd (h ▸ hWV) hWB
  · right
    rw [eq_top_iff]
    rintro x -
    have : (x : G) ∈ V := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := this
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy

@[expose] def transvAxis (A B : Subgroup G) : Subgroup (MulAut A) where
  carrier := {σ | (∀ x : A, (x : G) ∈ B → σ x = x) ∧ ∀ x : A, ((σ x : A) : G) * (x : G)⁻¹ ∈ B}
  mul_mem' {σ τ} hσ hτ := by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · rw [MulAut.mul_apply, hτ.1 x hx, hσ.1 x hx]
    · rw [MulAut.mul_apply]
      have e : (((σ (τ x)) : A) : G) * (x : G)⁻¹ =
          ((((σ (τ x)) : A) : G) * ((τ x : A) : G)⁻¹) * (((τ x : A) : G) * (x : G)⁻¹) := by
        group
      rw [e]
      exact B.mul_mem (hσ.2 (τ x)) (hτ.2 x)
  one_mem' := ⟨fun x _ => rfl, fun x => by simp [B.one_mem]⟩
  inv_mem' {σ} hσ := by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · have h1 : σ x = x := hσ.1 x hx
      calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [h1]
        _ = x := by simp
    · have h := hσ.2 (σ⁻¹ x)
      have e1 : σ (σ⁻¹ x) = x := by simp
      rw [e1] at h
      have e2 : (((σ⁻¹ x) : A) : G) * (x : G)⁻¹ = ((x : G) * ((σ⁻¹ x : A) : G)⁻¹)⁻¹ := by group
      rw [e2]
      exact B.inv_mem h

theorem mem_transvAxis_of (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) {σ : MulAut A} (h1 : ∀ x : A, (x : G) ∈ B → σ x = x)
    (h2 : ((σ ⟨a, haA⟩ : A) : G) * a⁻¹ ∈ B) : σ ∈ transvAxis A B := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨i, -, b, hb, hx⟩ := exists_pow_mul_of_mem hA haA hAa x.2
  have hxe : x = ⟨a, haA⟩ ^ i * ⟨b, hBA hb⟩ := Subtype.ext (by simp [hx])
  rw [hxe, map_mul, map_pow, h1 ⟨b, hBA hb⟩ hb]
  have hcomm : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
  set β : A := σ ⟨a, haA⟩ * ⟨a, haA⟩⁻¹ with hβ
  have hσa : σ ⟨a, haA⟩ = β * ⟨a, haA⟩ := by rw [hβ, inv_mul_cancel_right]
  have hpow : ∀ n : ℕ, (β * ⟨a, haA⟩) ^ n = β ^ n * ⟨a, haA⟩ ^ n := fun n =>
    (Commute.mul_pow (hcomm β ⟨a, haA⟩) n)
  rw [hσa, hpow]
  have e : ((β ^ i * ⟨a, haA⟩ ^ i * ⟨b, hBA hb⟩ : A) : G) * ((⟨a, haA⟩ ^ i * ⟨b, hBA hb⟩ : A) :
      G)⁻¹ = ((β ^ i : A) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    group
  rw [e, Subgroup.coe_pow]
  exact B.pow_mem h2 i

theorem transvAxis_ext (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) {σ τ : MulAut A} (hσ : σ ∈ transvAxis A B)
    (hτ : τ ∈ transvAxis A B) (h : σ ⟨a, haA⟩ = τ ⟨a, haA⟩) : σ = τ := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  ext x
  obtain ⟨i, -, b, hb, hx⟩ := exists_pow_mul_of_mem hA haA hAa x.2
  have hxe : x = ⟨a, haA⟩ ^ i * ⟨b, hBA hb⟩ := Subtype.ext (by simp [hx])
  rw [hxe, map_mul, map_mul, map_pow, map_pow, h, hσ.1 ⟨b, hBA hb⟩ hb, hτ.1 ⟨b, hBA hb⟩ hb]

theorem transvAxis_pow_three (hA : CFSG.Assembly.IsElemAbelian 3 A) {σ : MulAut A}
    (hσ : σ ∈ transvAxis A B) : σ ^ 3 = 1 := by
  ext x
  have hcomm : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
  set β : A := σ x * x⁻¹ with hβ
  have hβB : (β : G) ∈ B := by simpa [hβ] using hσ.2 x
  have hσx : σ x = β * x := by rw [hβ, inv_mul_cancel_right]
  have hσβ : σ β = β := hσ.1 β hβB
  have hβ3 : β ^ 3 = 1 := Subtype.ext (by simpa using hA.2 _ β.2)
  have e : (σ ^ 3) x = β ^ 3 * x := by
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, hσx, map_mul, hσβ]
    group
  rw [e, hβ3, one_mul, MulAut.one_apply]

theorem card_transvAxis_le [Finite G] (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) : Nat.card (transvAxis A B) ≤ Nat.card B := by
  let f : transvAxis A B → B := fun σ =>
    ⟨((σ.1 ⟨a, haA⟩ : A) : G) * a⁻¹, σ.2.2 ⟨a, haA⟩⟩
  have hf : Function.Injective f := by
    intro σ τ hστ
    have h1 : ((σ.1 ⟨a, haA⟩ : A) : G) = ((τ.1 ⟨a, haA⟩ : A) : G) := by
      have := congrArg Subtype.val hστ
      simpa [f] using this
    exact Subtype.ext (transvAxis_ext hA haA hAa σ.2 τ.2 (Subtype.ext h1))
  exact Nat.card_le_card_of_injective f hf

theorem conj_mem_transvAxis {ρ σ : MulAut A}
    (hρ : ∀ x : A, (x : G) ∈ B ↔ ((ρ x : A) : G) ∈ B) (hσ : σ ∈ transvAxis A B) :
    ρ * σ * ρ⁻¹ ∈ transvAxis A B := by
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · have hy : ((ρ⁻¹ x : A) : G) ∈ B := by
      rw [hρ]
      simpa using hx
    simp only [MulAut.mul_apply, hσ.1 _ hy, MulAut.apply_inv_self]
  · have h := hσ.2 (ρ⁻¹ x)
    have hmem : (((ρ (σ (ρ⁻¹ x) * (ρ⁻¹ x)⁻¹)) : A) : G) ∈ B :=
      (hρ _).mp (by simpa using h)
    simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self] at hmem ⊢
    simpa using hmem

theorem commutator_mem_transvAxis [Finite G] (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (hAa : A = Subgroup.zpowers a ⊔ B) {w k : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwB : w ∈ Subgroup.normalizer (B : Set G))
    (hkA : k ∈ Subgroup.normalizer (A : Set G)) (hka : k * a = a * k)
    (hkB : ∀ b ∈ B, k * b * k⁻¹ = b⁻¹) :
    A.normalizerMonoidHom ⟨w * k * w⁻¹ * k⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hwA hkA) (Subgroup.inv_mem _ hwA)) (Subgroup.inv_mem _ hkA)⟩ ∈
        transvAxis A B ∧
      (w * k * w⁻¹ * k⁻¹ * a * (w * k * w⁻¹ * k⁻¹)⁻¹ = a →
        w ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G)) := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hkB' : ∀ b ∈ B, k⁻¹ * b * k = b⁻¹ := by
    intro b hb
    have h1 := hkB b⁻¹ (B.inv_mem hb)
    rw [inv_inv] at h1
    calc k⁻¹ * b * k = k⁻¹ * (k * b⁻¹ * k⁻¹) * k := by rw [h1]
      _ = b⁻¹ := by group
  have hka' : k⁻¹ * a * k = a := by
    calc k⁻¹ * a * k = k⁻¹ * (a * k) := by group
      _ = k⁻¹ * (k * a) := by rw [hka]
      _ = a := by group
  set t := w * k * w⁻¹ * k⁻¹ with ht
  have htB : ∀ b ∈ B, t * b * t⁻¹ = b := by
    intro b hb
    have hb1 : w⁻¹ * b⁻¹ * w ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwB) b⁻¹).mp (B.inv_mem hb)
      simpa using this
    calc t * b * t⁻¹ = w * (k * (w⁻¹ * (k⁻¹ * b * k) * w) * k⁻¹) * w⁻¹ := by rw [ht]; group
      _ = w * (k * (w⁻¹ * b⁻¹ * w) * k⁻¹) * w⁻¹ := by rw [hkB' b hb]
      _ = w * (w⁻¹ * b⁻¹ * w)⁻¹ * w⁻¹ := by rw [hkB _ hb1]
      _ = b := by group
  have hwa : w⁻¹ * a * w ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwA) a).mp haA
    simpa using this
  obtain ⟨i, hi, b₀, hb₀, hab⟩ := exists_pow_mul_of_mem hA haA hAa hwa
  have hb₀3 : b₀ ^ 3 = 1 := hA.2 b₀ (hBA hb₀)
  have hwb₀ : w * b₀ * w⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hwB b₀).mp hb₀
  have hta : t * a * t⁻¹ = a * (w * b₀ * w⁻¹) := by
    have h1 : w * a ^ i * w⁻¹ = a * (w * b₀ * w⁻¹)⁻¹ := by
      calc w * a ^ i * w⁻¹ = w * (a ^ i * b₀) * w⁻¹ * (w * b₀ * w⁻¹)⁻¹ := by group
        _ = w * (w⁻¹ * a * w) * w⁻¹ * (w * b₀ * w⁻¹)⁻¹ := by rw [hab]
        _ = a * (w * b₀ * w⁻¹)⁻¹ := by group
    have hka_i : k * a ^ i * k⁻¹ = a ^ i := by
      rw [(Commute.pow_right hka i).eq, mul_inv_cancel_right]
    have hb₀inv : (w * b₀ * w⁻¹)⁻¹ * (w * b₀ * w⁻¹)⁻¹ = w * b₀ * w⁻¹ := by
      have hb : b₀⁻¹ * b₀⁻¹ = b₀ := by
        calc b₀⁻¹ * b₀⁻¹ = b₀⁻¹ * b₀⁻¹ * b₀ ^ 3 := by rw [hb₀3, mul_one]
          _ = b₀ := by group
      calc (w * b₀ * w⁻¹)⁻¹ * (w * b₀ * w⁻¹)⁻¹ = w * (b₀⁻¹ * b₀⁻¹) * w⁻¹ := by group
        _ = w * b₀ * w⁻¹ := by rw [hb]
    calc t * a * t⁻¹ = w * (k * (w⁻¹ * (k⁻¹ * a * k) * w) * k⁻¹) * w⁻¹ := by rw [ht]; group
      _ = w * (k * (a ^ i * b₀) * k⁻¹) * w⁻¹ := by rw [hka', hab]
      _ = w * ((k * a ^ i * k⁻¹) * (k * b₀ * k⁻¹)) * w⁻¹ := by group
      _ = w * (a ^ i * b₀⁻¹) * w⁻¹ := by rw [hka_i, hkB b₀ hb₀]
      _ = (w * a ^ i * w⁻¹) * (w * b₀ * w⁻¹)⁻¹ := by group
      _ = a * ((w * b₀ * w⁻¹)⁻¹ * (w * b₀ * w⁻¹)⁻¹) := by rw [h1]; group
      _ = a * (w * b₀ * w⁻¹) := by rw [hb₀inv]
  refine ⟨mem_transvAxis_of hA haA hAa (fun x hx => Subtype.ext (htB x hx)) ?_, fun h => ?_⟩
  · show t * a * t⁻¹ * a⁻¹ ∈ B
    rw [hta, hcomm a haA _ (hBA hwb₀), mul_inv_cancel_right]
    exact hwb₀
  ·
    rw [hta, mul_eq_left] at h
    have hb₀1 : b₀ = 1 := by
      have : b₀ = w⁻¹ * (w * b₀ * w⁻¹) * w := by group
      rw [this, h]
      group
    rw [hb₀1, mul_one] at hab
    have hmem : w⁻¹ * a * w⁻¹⁻¹ ∈ Subgroup.zpowers a := by
      rw [inv_inv, hab]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i
    have hle : (Subgroup.zpowers a).map (MulAut.conj w⁻¹).toMonoidHom ≤ Subgroup.zpowers a := by
      rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hmem
    have heq : (Subgroup.zpowers a).map (MulAut.conj w⁻¹).toMonoidHom = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective])
    have : w⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    simpa using Subgroup.inv_mem _ this

@[expose] def transvValue (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A) :
    transvAxis A B →* A where
  toFun σ := σ.1 ⟨a, haA⟩ * ⟨a, haA⟩⁻¹
  map_one' := by simp
  map_mul' σ τ := by
    have hcomm : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
    set βτ : A := τ.1 ⟨a, haA⟩ * ⟨a, haA⟩⁻¹ with hβτ
    have hβτB : (βτ : G) ∈ B := by simpa [hβτ] using τ.2.2 ⟨a, haA⟩
    have hτa : τ.1 ⟨a, haA⟩ = βτ * ⟨a, haA⟩ := by rw [hβτ, inv_mul_cancel_right]
    show (σ.1 * τ.1) ⟨a, haA⟩ * ⟨a, haA⟩⁻¹ = σ.1 ⟨a, haA⟩ * ⟨a, haA⟩⁻¹ * βτ
    rw [MulAut.mul_apply, hτa, map_mul, σ.2.1 βτ hβτB, mul_assoc]
    exact hcomm _ _

theorem exists_transv_of_irreducible [Finite G] {K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    {b : G} (hb : b ∈ B) : ∃ (w : G) (hw : w ∈ Subgroup.normalizer (A : Set G)),
      A.normalizerMonoidHom ⟨w, hw⟩ ∈ transvAxis A B ∧ w * a * w⁻¹ = a * b := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x (hBA x.2) y (hBA y.2))⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
  obtain ⟨ι, hιS, hι⟩ := exists_inv_mem_of_four_dvd hBe hB9
    (KFacts.four_dvd_card_of_isIrreducibleOn hBe hB9 hirr)
  obtain ⟨k, hkN, hkK, rfl⟩ := Sec4.mem_autIn_iff.mp hιS
  have hkB : ∀ x ∈ B, k * x * k⁻¹ = x⁻¹ := fun x hx => congrArg Subtype.val (hι ⟨x, hx⟩)
  set V : Subgroup G := (((wStar A).subgroupOf (transvAxis A B)).map
    (transvValue hA haA)).map A.subtype with hVdef
  have hVmem : ∀ x : G, x ∈ V ↔ ∃ σ ∈ transvAxis A B, σ ∈ wStar A ∧
      ((σ ⟨a, haA⟩ : A) : G) * a⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
      exact ⟨σ.1, σ.2, Subgroup.mem_subgroupOf.mp hσ, rfl⟩
    · rintro ⟨σ, hσT, hσW, rfl⟩
      exact ⟨_, ⟨⟨σ, hσT⟩, Subgroup.mem_subgroupOf.mpr hσW, rfl⟩, rfl⟩
  have hVB : V ≤ B := fun x hx => by
    obtain ⟨σ, hσT, -, rfl⟩ := (hVmem x).mp hx
    exact hσT.2 ⟨a, haA⟩
  have hKV1 : ∀ k' ∈ K, ∀ x ∈ V, k' * x * k'⁻¹ ∈ V := by
    intro k' hk' x hx
    obtain ⟨σ, hσT, hσW, rfl⟩ := (hVmem x).mp hx
    set ρ := A.normalizerMonoidHom ⟨k', hKA hk'⟩
    have hρB : ∀ y : A, (y : G) ∈ B ↔ ((ρ y : A) : G) ∈ B := fun y =>
      Subgroup.mem_normalizer_iff.mp (hKB hk') y
    have hρW : ρ ∈ wStar A := Sec4.mem_autIn_iff.mpr ⟨k', hKA hk', Subgroup.mem_top _, rfl⟩
    refine (hVmem _).mpr ⟨ρ * σ * ρ⁻¹, conj_mem_transvAxis hρB hσT,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hρW hσW) (Subgroup.inv_mem _ hρW), ?_⟩
    have hρa : ρ⁻¹ ⟨a, haA⟩ = ⟨a, haA⟩ := by
      apply (MulEquiv.apply_eq_iff_eq ρ).mp
      rw [MulAut.apply_inv_self]
      apply Subtype.ext
      show a = k' * a * k'⁻¹
      rw [hKa k' hk', mul_inv_cancel_right]
    rw [MulAut.mul_apply, MulAut.mul_apply, hρa]
    show k' * ((σ ⟨a, haA⟩ : A) : G) * k'⁻¹ * a⁻¹ =
      k' * (((σ ⟨a, haA⟩ : A) : G) * a⁻¹) * k'⁻¹
    have : k' * a⁻¹ * k'⁻¹ = a⁻¹ := by
      rw [(Commute.inv_right (hKa k' hk')).eq, mul_inv_cancel_right]
    calc k' * ((σ ⟨a, haA⟩ : A) : G) * k'⁻¹ * a⁻¹ =
        k' * ((σ ⟨a, haA⟩ : A) : G) * k'⁻¹ * (k' * a⁻¹ * k'⁻¹) := by rw [this]
      _ = k' * (((σ ⟨a, haA⟩ : A) : G) * a⁻¹) * k'⁻¹ := by group
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := fun k' hk' => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hKV1 k' hk' x, fun hx => ?_⟩
    have := hKV1 k'⁻¹ (K.inv_mem hk') _ hx
    simpa [mul_assoc] using this
  have hV1 : V ≠ ⊥ := by
    obtain ⟨w, hwA, hwa⟩ := Set.not_subset.mp hWa
    obtain ⟨hT, hfix⟩ := commutator_mem_transvAxis hA haA hAa hwA (hWB hwA) (hKA hkK)
      (hKa k hkK) hkB
    intro hbot
    apply hwa
    apply hfix
    have hmem : (((A.normalizerMonoidHom ⟨_, _⟩ ⟨a, haA⟩ : A) : G) * a⁻¹) ∈ V :=
      (hVmem _).mpr ⟨_, hT, Sec4.mem_autIn_iff.mpr ⟨_, _, Subgroup.mem_top _, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hVeq : V = B := (eq_bot_or_eq_of_isIrreducibleOn hirr hVB hKV).resolve_left hV1
  obtain ⟨σ, hσT, hσW, hσb⟩ := (hVmem b).mp (hVeq ▸ hb)
  obtain ⟨w, hwA, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσW
  refine ⟨w, hwA, hσT, ?_⟩
  have : w * a * w⁻¹ * a⁻¹ = b := hσb
  rw [← this, hcomm _ ((Subgroup.mem_normalizer_iff.mp hwA a).mp haA) a⁻¹ (A.inv_mem haA)]
  group

theorem transvAxis_le_wStar_and_card [Finite G] {K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    transvAxis A B ≤ wStar A ∧ Nat.card (transvAxis A B) = 9 := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hex := fun {b : G} (hb : b ∈ B) =>
    exists_transv_of_irreducible hA haA hAa hB9 hKa hirr hKA hKB hWB hWa hb
  refine ⟨fun τ hτ => ?_, le_antisymm ((card_transvAxis_le hA haA hAa).trans hB9.le) ?_⟩
  · have hb : ((τ ⟨a, haA⟩ : A) : G) * a⁻¹ ∈ B := hτ.2 ⟨a, haA⟩
    obtain ⟨w, hwA, hT, hwa⟩ := hex hb
    have : A.normalizerMonoidHom ⟨w, hwA⟩ = τ := by
      refine transvAxis_ext hA haA hAa hT hτ (Subtype.ext ?_)
      show w * a * w⁻¹ = ((τ ⟨a, haA⟩ : A) : G)
      rw [hwa, hcomm a haA _ (hBA hb), inv_mul_cancel_right]
    exact this ▸ Sec4.mem_autIn_iff.mpr ⟨w, hwA, Subgroup.mem_top _, rfl⟩
  · rw [← hB9]
    choose w hwA hT hwa using fun b : B => hex b.2
    refine Nat.card_le_card_of_injective (fun b : B =>
      (⟨A.normalizerMonoidHom ⟨w b, hwA b⟩, hT b⟩ : transvAxis A B)) ?_
    intro b b' hbb'
    have h1 := congrArg (fun σ : transvAxis A B => ((σ.1 ⟨a, haA⟩ : A) : G)) hbb'
    simp only at h1
    change w b * a * (w b)⁻¹ = w b' * a * (w b')⁻¹ at h1
    rw [hwa b, hwa b'] at h1
    exact Subtype.ext (mul_left_cancel h1)

theorem normalizerMonoidHom_apply_val (w : G) (hw : w ∈ Subgroup.normalizer (A : Set G))
    (x : A) : ((A.normalizerMonoidHom ⟨w, hw⟩ x : A) : G) = w * x * w⁻¹ :=
  rfl

theorem oThreeWStar_eq_transvAxis [Finite G] {K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    oThreeWStar A = transvAxis A B := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x (hBA x.2) y (hBA y.2))⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
  obtain ⟨hTW, hT9⟩ := transvAxis_le_wStar_and_card hA haA hAa hB9 hKa hirr hKA hKB hWB hWa
  have hpres : ∀ g ∈ wStar A, ∀ x : A, (x : G) ∈ B ↔ ((g x : A) : G) ∈ B := by
    intro g hg x
    obtain ⟨w, hwA, -, rfl⟩ := Sec4.mem_autIn_iff.mp hg
    exact Subgroup.mem_normalizer_iff.mp (hWB hwA) x
  have hO3p : ∀ ρ ∈ oThreeWStar A, ∃ n : ℕ, ρ ^ 3 ^ n = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := wStar A)) ⟨g, hg⟩
    have h1 : g ^ 3 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
    have h2 : (g : MulAut A) ^ 3 ^ n = 1 := by
      have := congrArg Subtype.val h1
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
    exact ⟨n, h2⟩
  have hO3W : oThreeWStar A ≤ wStar A := Subgroup.map_subtype_le _
  have hO3n : ∀ g ∈ wStar A, ∀ ρ ∈ oThreeWStar A, g * ρ * g⁻¹ ∈ oThreeWStar A := by
    rintro g hg _ ⟨r, hr, rfl⟩
    have := (pCore_normal (p := 3) (G := wStar A)).conj_mem r hr ⟨g, hg⟩
    exact ⟨_, this, rfl⟩
  apply le_antisymm
  ·
    set P : Subgroup G := oThreeWPre A with hP
    have hPmem : ∀ p : G, p ∈ P ↔ ∃ hp : p ∈ Subgroup.normalizer (A : Set G),
        A.normalizerMonoidHom ⟨p, hp⟩ ∈ oThreeWStar A := by
      intro p
      constructor
      · rintro ⟨⟨p', hp'⟩, hmem, rfl⟩
        exact ⟨hp', hmem⟩
      · rintro ⟨hp, hmem⟩
        exact ⟨⟨p, hp⟩, hmem, rfl⟩
    set C : Subgroup G :=
      { carrier := {b | b ∈ B ∧ ∀ p ∈ P, p * b * p⁻¹ = b}
        mul_mem' := fun {x y} hx hy => ⟨B.mul_mem hx.1 hy.1, fun p hp => by
          rw [show p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) by group, hx.2 p hp,
            hy.2 p hp]⟩
        one_mem' := ⟨B.one_mem, fun p _ => by group⟩
        inv_mem' := fun {x} hx => ⟨B.inv_mem hx.1, fun p hp => by
          rw [show p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ by group, hx.2 p hp]⟩ } with hC
    have hCB : C ≤ B := fun x hx => hx.1
    have hRB : IsPGroup 3 (Sec4.autIn P B) := by
      rintro ⟨τ, hτ⟩
      obtain ⟨p, hpN, hpP, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
      obtain ⟨hpA, hmem⟩ := (hPmem p).mp hpP
      obtain ⟨n, hn⟩ := hO3p _ hmem
      refine ⟨n, Subtype.ext (MulEquiv.ext fun b => Subtype.ext ?_)⟩
      have h1 := congrArg (fun σ : MulAut A => ((σ ⟨(b : G), hBA b.2⟩ : A) : G)) hn
      simp only [← map_pow, MulAut.one_apply] at h1
      simpa [← map_pow] using h1
    obtain ⟨b₁, hb₁, hfix⟩ := exists_fixed_of_isPGroup hB9 hRB
    have hC1 : C ≠ ⊥ := by
      intro hbot
      apply hb₁
      have hmem : (b₁ : G) ∈ C := ⟨b₁.2, fun p hp => by
        have hpN : p ∈ Subgroup.normalizer (B : Set G) := hWB ((hPmem p).mp hp).1
        have := hfix _ (Sec4.mem_autIn_iff.mpr ⟨p, hpN, hp, rfl⟩)
        exact congrArg Subtype.val this⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hKC1 : ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
      intro k hk x hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hKB hk) x).mp hx.1, fun p hp => ?_⟩
      have hkA := hKA hk
      have hpk : k⁻¹ * p * k ∈ P := by
        obtain ⟨hpA, hmem⟩ := (hPmem p).mp hp
        have hkpk : k⁻¹ * p * k ∈ Subgroup.normalizer (A : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkA) hpA) hkA
        refine (hPmem _).mpr ⟨hkpk, ?_⟩
        have hkW : A.normalizerMonoidHom ⟨k⁻¹, Subgroup.inv_mem _ hkA⟩ ∈ wStar A :=
          Sec4.mem_autIn_iff.mpr ⟨_, _, Subgroup.mem_top _, rfl⟩
        have := hO3n _ hkW _ hmem
        convert this using 1
        ext y
        simp [mul_assoc]
      calc p * (k * x * k⁻¹) * p⁻¹ = k * ((k⁻¹ * p * k) * x * (k⁻¹ * p * k)⁻¹) * k⁻¹ := by group
        _ = k * x * k⁻¹ := by rw [hx.2 _ hpk]
    have hKC : K ≤ Subgroup.normalizer (C : Set G) := fun k hk => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hKC1 k hk x, fun hx => ?_⟩
      have := hKC1 k⁻¹ (K.inv_mem hk) _ hx
      simpa [mul_assoc] using this
    have hCeq : C = B := (eq_bot_or_eq_of_isIrreducibleOn hirr hCB hKC).resolve_left hC1
    intro ρ hρ
    obtain ⟨w, hwA, -, hwρ⟩ := Sec4.mem_autIn_iff.mp (hO3W hρ)
    have hwP : w ∈ P := (hPmem w).mpr ⟨hwA, hwρ ▸ hρ⟩
    have hρB : ∀ x : A, (x : G) ∈ B → ρ x = x := by
      intro x hx
      rw [← hwρ]
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_val]
      exact ((hCeq ▸ hx : (x : G) ∈ C)).2 w hwP
    refine mem_transvAxis_of hA haA hAa hρB ?_
    have hρa : ((ρ ⟨a, haA⟩ : A) : G) ∈ A := (ρ ⟨a, haA⟩).2
    obtain ⟨i, hi, b, hb, hab⟩ := exists_pow_mul_of_mem hA haA hAa hρa
    have ha3 : a ^ 3 = 1 := hA.2 a haA
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hab
      apply haB
      have := (hpres ρ (hO3W hρ) ⟨a, haA⟩).mpr (hab ▸ hb)
      exact this
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · rw [hab, pow_one, hcomm a haA b (hBA hb), mul_inv_cancel_right]
      exact hb
    · exfalso
      have hb3 : b ^ 3 = 1 := hA.2 b (hBA hb)
      have e1 : ρ ⟨a, haA⟩ = ⟨a, haA⟩ ^ 2 * ⟨b, hBA hb⟩ := Subtype.ext (by simp [hab])
      have hρ2a : (ρ * ρ) ⟨a, haA⟩ = ⟨a, haA⟩ := by
        apply Subtype.ext
        rw [MulAut.mul_apply, e1, map_mul, map_pow, e1, hρB ⟨b, hBA hb⟩ hb]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        have hab' : Commute (a ^ 2) b := Commute.pow_left (hcomm a haA b (hBA hb)) 2
        rw [hab'.mul_pow, ← pow_mul, mul_assoc, ← pow_succ, hb3, mul_one,
          show 2 * 2 = 3 + 1 by norm_num, pow_succ, ha3, one_mul]
      have hρ2 : ρ * ρ = 1 := by
        ext x
        obtain ⟨j, -, b', hb', hx⟩ := exists_pow_mul_of_mem hA haA hAa x.2
        have hxe : x = ⟨a, haA⟩ ^ j * ⟨b', hBA hb'⟩ := Subtype.ext (by simp [hx])
        rw [hxe, map_mul, map_pow, hρ2a, MulAut.mul_apply,
          hρB ⟨b', hBA hb'⟩ hb', hρB ⟨b', hBA hb'⟩ hb', MulAut.one_apply]
      obtain ⟨n, hn⟩ := hO3p ρ hρ
      obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
      have hρ1 : ρ = 1 := by
        have : ρ ^ 3 ^ n = ρ := by
          rw [hm, pow_succ, pow_mul, sq, hρ2, one_pow, one_mul]
        rw [← this, hn]
      have : ρ ⟨a, haA⟩ = ⟨a, haA⟩ := by rw [hρ1, MulAut.one_apply]
      rw [e1] at this
      apply haB
      have h2 : (a : G) ^ 2 * b = a := by simpa using congrArg Subtype.val this
      have : b = a⁻¹ := by
        calc b = (a ^ 2)⁻¹ * (a ^ 2 * b) := by group
          _ = (a ^ 2)⁻¹ * a := by rw [h2]
          _ = a⁻¹ := by group
      have hainv : a⁻¹ ∈ B := this ▸ hb
      simpa using B.inv_mem hainv
  ·
    intro τ hτ
    have hτW := hTW hτ
    have hnorm : ((transvAxis A B).subgroupOf (wStar A)).Normal :=
      ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr
        (conj_mem_transvAxis (hpres g g.2) (Subgroup.mem_subgroupOf.mp hx))⟩
    have hp : IsPGroup 3 ((transvAxis A B).subgroupOf (wStar A)) := by
      rintro ⟨x, hx⟩
      have h3 := transvAxis_pow_three hA (Subgroup.mem_subgroupOf.mp hx)
      exact ⟨1, Subtype.ext (Subtype.ext (by simpa using h3))⟩
    have hle : (transvAxis A B).subgroupOf (wStar A) ≤ CFSG.pCore 3 (wStar A) :=
      le_sSup ⟨hnorm, hp⟩
    exact ⟨⟨τ, hτW⟩, hle (Subgroup.mem_subgroupOf.mpr hτ), rfl⟩

@[expose] def pointsOff (A B : Subgroup G) : Set (Subgroup G) :=
  {F | F ≤ A ∧ Nat.card F = 3 ∧ ¬ F ≤ B}

theorem mem_pointsOff_iff [Finite G] (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) {F : Subgroup G} :
    F ∈ pointsOff A B ↔ ∃ b ∈ B, F = Subgroup.zpowers (a * b) := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hcard3 : ∀ x ∈ A, x ≠ 1 → Nat.card (Subgroup.zpowers x) = 3 := fun x hx hx1 => by
    rw [Nat.card_zpowers]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hA.2 x hx)) with
      h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  constructor
  · rintro ⟨hFA, hF3, hFB⟩
    obtain ⟨x, hxF, hxB⟩ := Set.not_subset.mp hFB
    have hx1 : x ≠ 1 := fun h => hxB (h ▸ B.one_mem)
    have hFx : F = Subgroup.zpowers x := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxF)
      rw [hF3, hcard3 x (hFA hxF) hx1]
    obtain ⟨i, hi, b, hb, hx⟩ := exists_pow_mul_of_mem hA haA hAa (hFA hxF)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact absurd (by rw [hx, pow_zero, one_mul]; exact hb) hxB
    · exact ⟨b, hb, by rw [hFx, hx, pow_one]⟩
    ·
      refine ⟨b ^ 2, B.pow_mem hb 2, ?_⟩
      rw [hFx]
      have hx2 : x ^ 2 = a * b ^ 2 := by
        have hab' : Commute (a ^ 2) b := Commute.pow_left (hcomm a haA b (hBA hb)) 2
        rw [hx, hab'.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ha3,
          one_mul]
      rw [← hx2]
      have hx3 : x ^ 3 = 1 := hA.2 x (hFA hxF)
      apply le_antisymm
      · apply Subgroup.zpowers_le.mpr
        have e : (x ^ 2) ^ 2 = x := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hx3, one_mul]
        have h2 := Subgroup.pow_mem (Subgroup.zpowers (x ^ 2)) (Subgroup.mem_zpowers (x ^ 2)) 2
        rwa [e] at h2
      · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)
  · rintro ⟨b, hb, rfl⟩
    have habA : a * b ∈ A := A.mul_mem haA (hBA hb)
    have hab1 : a * b ∉ B := fun h => haB (by
      have := B.mul_mem h (B.inv_mem hb)
      simpa using this)
    refine ⟨Subgroup.zpowers_le.mpr habA, hcard3 _ habA (fun h => hab1 (h ▸ B.one_mem)),
      fun h => hab1 (h (Subgroup.mem_zpowers _))⟩

theorem zpowers_mul_injOn [Finite G] (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B)
    (h : Subgroup.zpowers (a * b) = Subgroup.zpowers (a * b')) : b = b' := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hmem : a * b ∈ Subgroup.zpowers (a * b') := h ▸ Subgroup.mem_zpowers _
  have hab3 : (a * b') ^ 3 = 1 := hA.2 _ (A.mul_mem haA (hBA hb'))
  rcases eq_of_mem_zpowers_of_pow_three hab3 hmem with h1 | h1 | h1
  · exfalso
    apply haB
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact B.inv_mem hb
  · exact mul_left_cancel h1
  · exfalso
    have hc : Commute a b' := hcomm a haA b' (hBA hb')
    rw [hc.mul_pow] at h1
    apply haB
    have h2 : b = a * b' ^ 2 := by
      calc b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ * (a ^ 2 * b' ^ 2) := by rw [h1]
        _ = a * b' ^ 2 := by group
    have : a = b * (b' ^ 2)⁻¹ := by rw [h2]; group
    rw [this]
    exact B.mul_mem hb (B.inv_mem (B.pow_mem hb' 2))

theorem ncard_pointsOff [Finite G] (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) (hB9 : Nat.card B = 9) :
    (pointsOff A B).ncard = 9 := by
  have heq : pointsOff A B = (fun b : B => Subgroup.zpowers (a * b)) '' Set.univ := by
    ext F
    rw [mem_pointsOff_iff hA haA hAa haB]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
  rw [heq, Set.ncard_image_of_injective _ (fun b b' h => Subtype.ext
    (zpowers_mul_injOn hA haA hAa haB b.2 b'.2 h)), Set.ncard_univ, hB9]

theorem exists_conj_pointsOff [Finite G] {K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (A : Set G)),
      A.normalizerMonoidHom ⟨w, hw⟩ ∈ transvAxis A B ∧
      (Subgroup.zpowers (a * b)).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (a * b') := by
  have hBA : B ≤ A := hAa ▸ le_sup_right
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨w, hwA, hT, hwa⟩ := exists_transv_of_irreducible hA haA hAa hB9 hKa hirr hKA hKB
    hWB hWa (B.mul_mem hb' (B.inv_mem hb))
  refine ⟨w, hwA, hT, ?_⟩
  rw [MonoidHom.map_zpowers]
  congr 1
  have hwb : w * b * w⁻¹ = b := congrArg Subtype.val (hT.1 ⟨b, hBA hb⟩ hb)
  show w * (a * b) * w⁻¹ = a * b'
  calc w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
    _ = a * (b' * b⁻¹) * b := by rw [hwa, hwb]
    _ = a * b' := by group

theorem map_conj_mem_pointsOff {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwB : w ∈ Subgroup.normalizer (B : Set G)) {F : Subgroup G} (hF : F ∈ pointsOff A B) :
    F.map (MulAut.conj w).toMonoidHom ∈ pointsOff A B := by
  obtain ⟨hFA, hF3, hFB⟩ := hF
  refine ⟨?_, ?_, fun h => hFB ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hwA x).mp (hFA hx)
  · rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hF3]
  · intro x hx
    have : w * x * w⁻¹ ∈ B := h ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hwB x).mpr this

theorem wStar_eq_sup [Finite G] {K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A)
    (hAa : A = Subgroup.zpowers a ⊔ B) (haB : a ∉ B) (hB9 : Nat.card B = 9)
    (hKa : ∀ k ∈ K, k * a = a * k) (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (hWa : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    {c : G} (hcA : c ∈ A) (hcB : c ∉ B) (hc1 : c ≠ 1) :
    wStar A = oThreeWStar A ⊔
      Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A := by
  have hO3 := oThreeWStar_eq_transvAxis hA haA hAa haB hB9 hKa hirr hKA hKB hWB hWa
  apply le_antisymm
  · intro φ hφ
    obtain ⟨w, hwA, -, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    have hc : Subgroup.zpowers c ∈ pointsOff A B := by
      refine ⟨Subgroup.zpowers_le.mpr hcA, ?_, fun h => hcB (h (Subgroup.mem_zpowers c))⟩
      rw [Nat.card_zpowers]
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hA.2 c hcA))
        with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc1
      · exact h
    obtain ⟨b₀, hb₀, hcb₀⟩ := (mem_pointsOff_iff hA haA hAa haB).mp hc
    obtain ⟨b₁, hb₁, hwc⟩ := (mem_pointsOff_iff hA haA hAa haB).mp
      (map_conj_mem_pointsOff hwA (hWB hwA) hc)
    obtain ⟨w', hw'A, hT, hw'⟩ :=
      exists_conj_pointsOff hA haA hAa hB9 hKa hirr hKA hKB hWB hWa hb₀ hb₁
    have hmm : ∀ (F : Subgroup G) (x y : G),
        (F.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
          F.map (MulAut.conj (y * x)).toMonoidHom := by
      intro F x y
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hn : w'⁻¹ * w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show (Subgroup.zpowers c).map (MulAut.conj (w'⁻¹ * w)).toMonoidHom = Subgroup.zpowers c
      rw [← hmm, hwc, ← hw', hmm, inv_mul_cancel, ← hcb₀]
      ext z
      simp
    have hw'' : w'⁻¹ * w ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hw'A) hwA
    have hsplit : A.normalizerMonoidHom ⟨w, hwA⟩ = A.normalizerMonoidHom ⟨w', hw'A⟩ *
        A.normalizerMonoidHom ⟨w'⁻¹ * w, hw''⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [hsplit]
    refine Subgroup.mul_mem_sup ?_ (Sec4.mem_autIn_iff.mpr ⟨_, hw'', hn, rfl⟩)
    rw [hO3]
    exact hT
  · exact sup_le (Subgroup.map_subtype_le _) (fun φ hφ => by
      obtain ⟨w, hwA, -, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
      exact Sec4.mem_autIn_iff.mpr ⟨w, hwA, Subgroup.mem_top _, rfl⟩)

end Plane

end CFSG.RankThree.PartTwo.Sec13
