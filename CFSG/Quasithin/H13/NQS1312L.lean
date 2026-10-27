module

public import CFSG.Quasithin.H13.NQS1312J

public section

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup

variable {G : Type} [Group G]

@[expose] def fixSub (A B : Subgroup G) (k : G) (hAB : A ≤ normalizer (B : Set G)) :
    Subgroup G where
  carrier := {a | a ∈ A ∧ a⁻¹ * (k * a * k⁻¹) ∈ B}
  one_mem' := ⟨A.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hka⟩ ⟨hb, hkb⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (a * b)⁻¹ * (k * (a * b) * k⁻¹) =
        (b⁻¹ * (a⁻¹ * (k * a * k⁻¹)) * b) * (b⁻¹ * (k * b * k⁻¹)) := by group
    rw [e]
    refine B.mul_mem ?_ hkb
    have := (mem_normalizer_iff.1 (hAB (A.inv_mem hb)) _).1 hka
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, hka⟩
    refine ⟨A.inv_mem ha, ?_⟩
    have e : a⁻¹⁻¹ * (k * a⁻¹ * k⁻¹) = a * (a⁻¹ * (k * a * k⁻¹))⁻¹ * a⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hAB ha) _).1 (B.inv_mem hka)

theorem mem_fixSub {A B : Subgroup G} {k : G} {hAB : A ≤ normalizer (B : Set G)} {a : G} :
    a ∈ fixSub A B k hAB ↔ a ∈ A ∧ a⁻¹ * (k * a * k⁻¹) ∈ B := Iff.rfl

theorem fixSub_le {A B : Subgroup G} {k : G} (hAB : A ≤ normalizer (B : Set G)) :
    fixSub A B k hAB ≤ A := fun _ ha => ha.1

theorem le_fixSub {A B : Subgroup G} {k : G} (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ A)
    (hkB : k ∈ normalizer (B : Set G)) : B ≤ fixSub A B k hAB :=
  fun b hb => ⟨hBA hb, B.mul_mem (B.inv_mem hb) ((mem_normalizer_iff.1 hkB b).1 hb)⟩

theorem fixSub_eq_self {A B : Subgroup G} {k : G} (hAB : A ≤ normalizer (B : Set G))
    (h : ∀ a ∈ A, a⁻¹ * (k * a * k⁻¹) ∈ B) : fixSub A B k hAB = A :=
  le_antisymm (fixSub_le hAB) fun a ha => ⟨ha, h a ha⟩

theorem relIndex_fixSub_eq_one {A B : Subgroup G} {k : G} (hAB : A ≤ normalizer (B : Set G))
    (h : ∀ a ∈ A, a⁻¹ * (k * a * k⁻¹) ∈ B) : (fixSub A B k hAB).relIndex A = 1 := by
  rw [fixSub_eq_self hAB h, Subgroup.relIndex_self]

theorem exists_commute_of_mem_fixSub [Finite G] {C : Subgroup G} {k : G} (hk3 : k ^ 3 = 1)
    (hkC : k ∈ normalizer (C : Set G)) (hC3 : ¬ 3 ∣ Nat.card C) {a : G}
    (ha : a⁻¹ * (k * a * k⁻¹) ∈ C) : ∃ c ∈ C, k * (a * c) * k⁻¹ = a * c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d := a⁻¹ * (k * a * k⁻¹) with hd
  let φ : Function.End ↥C := fun c => ⟨d * (k * (c : G) * k⁻¹),
    C.mul_mem ha ((mem_normalizer_iff.1 hkC c).1 c.2)⟩
  have hφ : ∀ c : ↥C, a * ((φ c : ↥C) : G) = k * (a * c) * k⁻¹ := by
    intro c
    show a * (a⁻¹ * (k * a * k⁻¹) * (k * (c : G) * k⁻¹)) = k * (a * c) * k⁻¹
    group
  have hkkk : k * k * k = 1 := by rw [mul_assoc, ← pow_three, hk3]
  have hφ3 : φ ^ 3 = 1 := by
    funext c
    apply Subtype.ext
    have h1 : a * ((φ (φ (φ c)) : ↥C) : G) = a * c := by
      rw [hφ, hφ, hφ]
      calc k * (k * (k * (a * c) * k⁻¹) * k⁻¹) * k⁻¹ =
          (k * k * k) * (a * c) * (k * k * k)⁻¹ := by group
        _ = a * c := by rw [hkkk]; group
    exact mul_left_cancel h1
  have : Fintype ↥C := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := φ) (by simpa using hφ3)
  have hmod' : Nat.card ↥C ≡ Nat.card (Function.fixedPoints φ) [MOD 3] := by
    convert hmod using 1 <;> exact Nat.card_eq_fintype_card
  have hne : Nat.card (Function.fixedPoints φ) ≠ 0 := by
    intro h0
    rw [h0] at hmod'
    exact hC3 (Nat.modEq_zero_iff_dvd.1 hmod')
  obtain ⟨⟨c, hc⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  refine ⟨c, c.2, ?_⟩
  rw [← hφ c]
  exact congrArg (fun x : ↥C => a * (x : G)) hc

theorem relIndex_fixSub_mul [Finite G] {A B C : Subgroup G} {k : G} (hk3 : k ^ 3 = 1)
    (hBC : B ≤ C) (hCA : C ≤ A) (hAB : A ≤ normalizer (B : Set G))
    (hAC : A ≤ normalizer (C : Set G)) (hkC : k ∈ normalizer (C : Set G))
    (hC3 : ¬ 3 ∣ Nat.card C) :
    (fixSub A B k hAB).relIndex A =
      (fixSub A C k hAC).relIndex A * (fixSub C B k (hCA.trans hAB)).relIndex C := by
  set FB := fixSub A B k hAB with hFB
  set FC := fixSub A C k hAC with hFC
  set F' := fixSub C B k (hCA.trans hAB) with hF'
  have hsup : FC = FB ⊔ C := by
    refine le_antisymm (fun a ha => ?_) (sup_le (fun a ha => ⟨ha.1, hBC ha.2⟩)
      (le_fixSub hAC hCA hkC))
    obtain ⟨c, hc, hac⟩ := exists_commute_of_mem_fixSub hk3 hkC hC3 ha.2
    have hacB : a * c ∈ FB := by
      refine ⟨A.mul_mem ha.1 (hCA hc), ?_⟩
      rw [hac, inv_mul_cancel]
      exact B.one_mem
    have e : a = (a * c) * c⁻¹ := by group
    rw [e]
    exact mul_mem_sup hacB (C.inv_mem hc)
  have hinf : F' = FB ⊓ C := by
    ext c
    constructor
    · rintro ⟨hcC, hcB⟩
      exact ⟨⟨hCA hcC, hcB⟩, hcC⟩
    · rintro ⟨⟨-, hcB⟩, hcC⟩
      exact ⟨hcC, hcB⟩
  have hprod : Nat.card (FB ⊔ C : Subgroup G) * Nat.card (FB ⊓ C : Subgroup G) =
      Nat.card FB * Nat.card C := by
    have h := card_sup_mul_card_inf_line (A := C) (B := FB) ((fixSub_le hAB).trans hAC)
    rw [sup_comm, inf_comm] at h
    rw [h, mul_comm]
  have h1 : Nat.card FB * FB.relIndex A = Nat.card A := by
    rw [mul_comm, ← Subgroup.relIndex_mul_card (H := FB) (K := A),
      inf_of_le_left (fixSub_le hAB)]
  have h2 : Nat.card FC * FC.relIndex A = Nat.card A := by
    rw [mul_comm, ← Subgroup.relIndex_mul_card (H := FC) (K := A),
      inf_of_le_left (fixSub_le hAC)]
  have h3 : Nat.card F' * F'.relIndex C = Nat.card C := by
    rw [mul_comm, ← Subgroup.relIndex_mul_card (H := F') (K := C),
      inf_of_le_left (fixSub_le (hCA.trans hAB))]
  rw [← hsup] at hprod
  rw [← hinf] at hprod
  have hpos : 0 < Nat.card FB * Nat.card C := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc FB.relIndex A * (Nat.card FB * Nat.card C) = (Nat.card FB * FB.relIndex A) * Nat.card C :=
        by ring
    _ = Nat.card A * Nat.card C := by rw [h1]
    _ = (Nat.card FC * FC.relIndex A) * (Nat.card F' * F'.relIndex C) := by rw [h2, h3]
    _ = FC.relIndex A * F'.relIndex C * (Nat.card FC * Nat.card F') := by ring
    _ = FC.relIndex A * F'.relIndex C * (Nat.card FB * Nat.card C) := by rw [hprod]

theorem relIndex_pos_line [Finite G] (H K : Subgroup G) : 0 < H.relIndex K := by
  have h := Subgroup.relIndex_mul_card (H := H) (K := K)
  rcases Nat.eq_zero_or_pos (H.relIndex K) with h0 | h0
  · rw [h0, zero_mul] at h
    exact absurd h.symm (Nat.card_pos (α := ↥K)).ne'
  · exact h0

theorem le_normalizer_bot_line (A : Subgroup G) : A ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
  intro a _
  rw [mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl
    group
  · intro h
    have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [this, h]
    group

theorem mem_fixSub_bot {A : Subgroup G} {k a : G} :
    a ∈ fixSub A ⊥ k (le_normalizer_bot_line A) ↔ a ∈ A ∧ k * a * k⁻¹ = a := by
  rw [mem_fixSub, Subgroup.mem_bot, inv_mul_eq_one]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

theorem card_fixSub_bot_modEq [Finite G] {A : Subgroup G} {k : G} (hk3 : k ^ 3 = 1)
    (hkA : k ∈ normalizer (A : Set G)) :
    Nat.card (fixSub A ⊥ k (le_normalizer_bot_line A)) ≡ Nat.card A [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : Function.End ↥A := fun a => ⟨k * (a : G) * k⁻¹, (mem_normalizer_iff.1 hkA a).1 a.2⟩
  have hkkk : k * k * k = 1 := by rw [mul_assoc, ← pow_three, hk3]
  have hφ3 : φ ^ 3 = 1 := by
    funext a
    apply Subtype.ext
    show k * (k * (k * (a : G) * k⁻¹) * k⁻¹) * k⁻¹ = a
    calc k * (k * (k * (a : G) * k⁻¹) * k⁻¹) * k⁻¹ = (k * k * k) * a * (k * k * k)⁻¹ := by group
      _ = a := by rw [hkkk]; group
  have : Fintype ↥A := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := φ) (by simpa using hφ3)
  have hmod' : Nat.card ↥A ≡ Nat.card (Function.fixedPoints φ) [MOD 3] := by
    convert hmod using 1 <;> exact Nat.card_eq_fintype_card
  have he : Nat.card (Function.fixedPoints φ) =
      Nat.card (fixSub A ⊥ k (le_normalizer_bot_line A)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1, mem_fixSub_bot.2 ⟨x.1.2, congrArg Subtype.val x.2⟩⟩
        invFun := fun y => ⟨⟨y, (mem_fixSub_bot.1 y.2).1⟩,
          Subtype.ext (mem_fixSub_bot.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [he] at hmod'
  exact hmod'.symm

theorem relIndex_fixSub_bot_modEq [Finite G] {A : Subgroup G} {k : G} (hk3 : k ^ 3 = 1)
    (hkA : k ∈ normalizer (A : Set G)) (hA3 : ¬ 3 ∣ Nat.card A) :
    (fixSub A ⊥ k (le_normalizer_bot_line A)).relIndex A ≡ 1 [MOD 3] := by
  set F := fixSub A ⊥ k (le_normalizer_bot_line A)
  have h1 : F.relIndex A * Nat.card F = Nat.card A := by
    rw [← Subgroup.relIndex_mul_card (H := F) (K := A), inf_of_le_left (fixSub_le _)]
  have hF3 : Nat.Coprime 3 (Nat.card F) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => hA3 ?_
    rw [← h1]
    exact dvd_mul_of_dvd_right h3 _
  have h2 := card_fixSub_bot_modEq hk3 hkA
  refine Nat.ModEq.cancel_right_of_coprime (c := Nat.card F) hF3 ?_
  rw [h1, one_mul]
  exact h2.symm

theorem relIndex_fixSub_le_four [Finite G] {A B : Subgroup G} {k : G} (hk3 : k ^ 3 = 1)
    (hBA : B ≤ A) (hAB : A ≤ normalizer (B : Set G)) (hkA : k ∈ normalizer (A : Set G))
    (hkB : k ∈ normalizer (B : Set G)) (hA : IsPGroup 2 A) (h8 : B.relIndex A ≤ 8) :
    (fixSub A B k hAB).relIndex A ≤ 4 := by
  have hA3 : ∀ C : Subgroup G, C ≤ A → ¬ 3 ∣ Nat.card C := by
    intro C hCA h3
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (hA.to_le hCA)
    rw [hm] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmul := relIndex_fixSub_mul hk3 (bot_le : (⊥ : Subgroup G) ≤ B) hBA
    (le_normalizer_bot_line A) hAB hkB (hA3 B hBA)
  have h1 := relIndex_fixSub_bot_modEq hk3 hkA (hA3 A le_rfl)
  have h2 := relIndex_fixSub_bot_modEq hk3 hkB (hA3 B hBA)
  have hcop : Nat.gcd 3 ((fixSub B ⊥ k (hBA.trans (le_normalizer_bot_line A))).relIndex B) = 1 := by
    have h3 : (fixSub B ⊥ k (hBA.trans (le_normalizer_bot_line A))).relIndex B % 3 = 1 := h2
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => ?_
    have := Nat.mod_eq_zero_of_dvd h
    omega
  have hi1 : (fixSub A B k hAB).relIndex A ≡ 1 [MOD 3] := by
    refine Nat.ModEq.cancel_right_of_coprime hcop ?_
    rw [one_mul, ← hmul]
    exact h1.trans h2.symm
  have hdvd : (fixSub A B k hAB).relIndex A ∣ B.relIndex A :=
    Subgroup.relIndex_dvd_of_le_left A (le_fixSub hAB hBA hkB)
  have hdvdA : (fixSub A B k hAB).relIndex A ∣ Nat.card A := Subgroup.relIndex_dvd_card _ _
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hA
  rw [hm] at hdvdA
  obtain ⟨e, -, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvdA
  have hle : (fixSub A B k hAB).relIndex A ≤ 8 :=
    (Nat.le_of_dvd (relIndex_pos_line B A) hdvd).trans h8
  rw [hie] at hle hi1 ⊢
  have he3 : e ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases e <;> simp_all [Nat.ModEq]

@[expose] def centerPre (A B : Subgroup G) (hAB : A ≤ normalizer (B : Set G)) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B}
  one_mem' := ⟨A.one_mem, fun a' _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨A.mul_mem ha hb, fun a' ha' => ?_⟩
    have e : a * b * a' * (a * b)⁻¹ * a'⁻¹ =
        (a * (b * a' * b⁻¹ * a'⁻¹) * a⁻¹) * (a * a' * a⁻¹ * a'⁻¹) := by group
    rw [e]
    exact B.mul_mem ((mem_normalizer_iff.1 (hAB ha) _).1 (hcb a' ha')) (hca a' ha')
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨A.inv_mem ha, fun a' ha' => ?_⟩
    have e : a⁻¹ * a' * a⁻¹⁻¹ * a'⁻¹ = a⁻¹ * (a * a' * a⁻¹ * a'⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hAB (A.inv_mem ha)) _).1 (B.inv_mem (hca a' ha'))

@[expose] def sqPre (A B : Subgroup G) (hAB : A ≤ normalizer (B : Set G))
    (hab : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) : Subgroup G where
  carrier := {a | a ∈ A ∧ a ^ 2 ∈ B}
  one_mem' := ⟨A.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (a * b) ^ 2 = (a * (b * a * b⁻¹ * a⁻¹) * a⁻¹) * a ^ 2 * b ^ 2 := by
      simp only [pow_two]
      group
    rw [e]
    exact B.mul_mem (B.mul_mem ((mem_normalizer_iff.1 (hAB ha) _).1 (hab b hb a ha)) ha2) hb2
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨A.inv_mem ha, ?_⟩
    rw [inv_pow]
    exact B.inv_mem ha2

theorem mem_normalizer_centerPre {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer (centerPre A B hAB : Set G) := by
  have key : ∀ h : G, h ∈ normalizer (A : Set G) → h ∈ normalizer (B : Set G) →
      ∀ a ∈ centerPre A B hAB, h * a * h⁻¹ ∈ centerPre A B hAB := by
    rintro h hhA hhB a ⟨ha, hca⟩
    refine ⟨(mem_normalizer_iff.1 hhA a).1 ha, fun a' ha' => ?_⟩
    have ha'' : h⁻¹ * a' * h ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hhA) a').1 ha'
      simpa using this
    have e : h * a * h⁻¹ * a' * (h * a * h⁻¹)⁻¹ * a'⁻¹ =
        h * (a * (h⁻¹ * a' * h) * a⁻¹ * (h⁻¹ * a' * h)⁻¹) * h⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hhB _).1 (hca _ ha'')
  rw [mem_normalizer_iff]
  intro a
  refine ⟨key g hgA hgB a, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hgA) (inv_mem hgB) _ h
  simpa [mul_assoc] using this

theorem mem_normalizer_sqPre {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hab : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer (sqPre A B hAB hab : Set G) := by
  have key : ∀ h : G, h ∈ normalizer (A : Set G) → h ∈ normalizer (B : Set G) →
      ∀ a ∈ sqPre A B hAB hab, h * a * h⁻¹ ∈ sqPre A B hAB hab := by
    rintro h hhA hhB a ⟨ha, ha2⟩
    refine ⟨(mem_normalizer_iff.1 hhA a).1 ha, ?_⟩
    have e : (h * a * h⁻¹) ^ 2 = h * a ^ 2 * h⁻¹ := by
      simp only [pow_two]
      group
    rw [e]
    exact (mem_normalizer_iff.1 hhB _).1 ha2
  rw [mem_normalizer_iff]
  intro a
  refine ⟨key g hgA hgB a, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hgA) (inv_mem hgB) _ h
  simpa [mul_assoc] using this

theorem exists_mem_centerPre [Finite G] {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hlt : B < A) (hA : IsPGroup 2 A) : ∃ a ∈ centerPre A B hAB, a ∉ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  obtain ⟨a₀, ha₀A, ha₀B⟩ := Set.exists_of_ssubset hlt
  have hnt : Nontrivial (↥A ⧸ B.subgroupOf A) := by
    refine ⟨⟨QuotientGroup.mk ⟨a₀, ha₀A⟩, 1, fun h => ha₀B ?_⟩⟩
    have := (QuotientGroup.eq_one_iff _).1 h
    exact this
  have hp : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := hA.to_quotient _
  have : Nontrivial ↥(Subgroup.center (↥A ⧸ B.subgroupOf A)) := hp.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center (↥A ⧸ B.subgroupOf A)))
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (z : ↥A ⧸ B.subgroupOf A)
  refine ⟨x, ⟨x.2, fun a' ha' => ?_⟩, fun hxB => hz1 (Subtype.ext ?_)⟩
  · have h1 := Subgroup.mem_center_iff.1 z.2 (QuotientGroup.mk ⟨a', ha'⟩)
    rw [← hx] at h1
    have h2 : (QuotientGroup.mk (x * ⟨a', ha'⟩ * x⁻¹ * ⟨a', ha'⟩⁻¹) :
        ↥A ⧸ B.subgroupOf A) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← h1]
      group
    have h3 := (QuotientGroup.eq_one_iff _).1 h2
    simpa [Subgroup.mem_subgroupOf] using h3
  · rw [← hx]
    exact (QuotientGroup.eq_one_iff _).2 hxB

theorem exists_mem_sqPre [Finite G] {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hab : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) (hlt : B < A) (hA : IsPGroup 2 A) :
    ∃ a ∈ sqPre A B hAB hab, a ∉ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  obtain ⟨a₀, ha₀A, ha₀B⟩ := Set.exists_of_ssubset hlt
  have hp : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := hA.to_quotient _
  have hne1 : (QuotientGroup.mk ⟨a₀, ha₀A⟩ : ↥A ⧸ B.subgroupOf A) ≠ 1 := fun h =>
    ha₀B (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (⟨a₀, ha₀A⟩ : ↥A)).1 h))
  have h2 : 2 ∣ Nat.card (↥A ⧸ B.subgroupOf A) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact hne1 (Nat.card_eq_one_iff_unique.1 hm |>.1.elim _ _)
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective w
  refine ⟨x, ⟨x.2, ?_⟩, fun hxB => ?_⟩
  · have h1 : (QuotientGroup.mk (x ^ 2) : ↥A ⧸ B.subgroupOf A) = 1 := by
      rw [QuotientGroup.mk_pow, hx, ← hw, pow_orderOf_eq_one]
    have h3 := (QuotientGroup.eq_one_iff _).1 h1
    simpa [Subgroup.mem_subgroupOf] using h3
  · have h1 : w = 1 := by
      rw [← hx]
      exact (QuotientGroup.eq_one_iff _).2 hxB
    rw [h1, orderOf_one] at hw
    omega

theorem le_normalizer_of_comm_mod {A B C : Subgroup G} (hBC : B ≤ C)
    (hab : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) (hCA : C ≤ A) :
    A ≤ normalizer (C : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    have e : a * c * a⁻¹ = (a * c * a⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact C.mul_mem (hBC (hab a ha c (hCA hc))) hc
  · intro hc
    have hc' : c = (a⁻¹ * (a * c * a⁻¹) * a⁻¹⁻¹ * (a * c * a⁻¹)⁻¹) * (a * c * a⁻¹) := by group
    rw [hc']
    exact C.mul_mem (hBC (hab _ (A.inv_mem ha) _ (hCA hc))) hc

theorem two_le_relIndex_of_lt [Finite G] {H K : Subgroup G} (h : H < K) : 2 ≤ H.relIndex K := by
  have h1 := relIndex_pos_line H K
  have h2 : H.relIndex K ≠ 1 := fun h1' => (not_le_of_gt h) (Subgroup.relIndex_eq_one.1 h1')
  omega

theorem fixSub_good [Finite G] {L : Subgroup G} {k : G} (hkL : k ∈ L) (hk3 : k ^ 3 = 1)
    (hbase : ∀ (A B : Subgroup G) (hAB : A ≤ normalizer (B : Set G)), B < A → IsPGroup 2 A →
      L ≤ normalizer (A : Set G) → L ≤ normalizer (B : Set G) →
      (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) → (∀ a ∈ A, a ^ 2 ∈ B) →
      (∀ C : Subgroup G, B ≤ C → C ≤ A → L ≤ normalizer (C : Set G) → C = B ∨ C = A) →
      (fixSub A B k hAB).relIndex A = 1 ∨ 16 ≤ (fixSub A B k hAB).relIndex A) :
    ∀ (n : ℕ) (A B : Subgroup G) (hAB : A ≤ normalizer (B : Set G)), B.relIndex A ≤ n →
      B ≤ A → IsPGroup 2 A → L ≤ normalizer (A : Set G) → L ≤ normalizer (B : Set G) →
      (fixSub A B k hAB).relIndex A = 1 ∨ 16 ≤ (fixSub A B k hAB).relIndex A := by
  intro n
  induction n with
  | zero =>
    intro A B hAB hn _ _ _ _
    have := relIndex_pos_line B A
    omega
  | succ n ih =>
    intro A B hAB hn hBA hA hLA hLB
    have hkA : k ∈ normalizer (A : Set G) := hLA hkL
    have hkB : k ∈ normalizer (B : Set G) := hLB hkL
    by_cases hEq : B = A
    · subst hEq
      left
      refine relIndex_fixSub_eq_one hAB fun a ha => B.mul_mem (B.inv_mem ha) ?_
      exact (mem_normalizer_iff.1 hkA a).1 ha
    have hlt : B < A := lt_of_le_of_ne hBA hEq
    have hC3 : ∀ C : Subgroup G, C ≤ A → ¬ 3 ∣ Nat.card C := by
      intro C hCA h3
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (hA.to_le hCA)
      rw [hm] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    by_cases hsplit : ∃ C : Subgroup G, B < C ∧ C < A ∧ A ≤ normalizer (C : Set G) ∧
        L ≤ normalizer (C : Set G)
    · obtain ⟨C, hBC, hCA, hAC, hLC⟩ := hsplit
      rw [relIndex_fixSub_mul hk3 hBC.le hCA.le hAB hAC (hLC hkL) (hC3 C hCA.le)]
      have hr := Subgroup.relIndex_mul_relIndex B C A hBC.le hCA.le
      have h1 := two_le_relIndex_of_lt hBC
      have h2 := two_le_relIndex_of_lt hCA
      have hIA := ih A C hAC (by nlinarith) hCA.le hA hLA hLC
      have hIC := ih C B (hCA.le.trans hAB) (by nlinarith) hBC.le (hA.to_le hCA.le) hLC hLB
      rcases hIA with h | h <;> rcases hIC with h' | h'
      · left; rw [h, h']
      · right; rw [h, one_mul]; exact h'
      · right; rw [h', mul_one]; exact h
      · right; nlinarith
    · push Not at hsplit
      have hZ : centerPre A B hAB = A := by
        have hBZ : B ≤ centerPre A B hAB := fun b hb => ⟨hBA hb, fun a' ha' => by
          have e : b * a' * b⁻¹ * a'⁻¹ = b * (a' * b⁻¹ * a'⁻¹) := by group
          rw [e]
          exact B.mul_mem hb ((mem_normalizer_iff.1 (hAB ha') _).1 (B.inv_mem hb))⟩
        obtain ⟨a, haZ, haB⟩ := exists_mem_centerPre hAB hlt hA
        have hBlt : B < centerPre A B hAB := lt_of_le_of_ne hBZ fun h => haB (h ▸ haZ)
        rcases lt_or_eq_of_le (show centerPre A B hAB ≤ A from fun x hx => hx.1) with h | h
        · exact absurd (fun g hg => mem_normalizer_centerPre hAB (hLA hg) (hLB hg))
            (hsplit _ hBlt h (fun g hg => mem_normalizer_centerPre hAB
              (Subgroup.le_normalizer hg) (hAB hg)))
        · exact h
      have hab : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B := by
        intro a ha
        have h : a ∈ centerPre A B hAB := by rw [hZ]; exact ha
        exact h.2
      have hS : sqPre A B hAB hab = A := by
        have hBS : B ≤ sqPre A B hAB hab := fun b hb => ⟨hBA hb, B.pow_mem hb 2⟩
        obtain ⟨a, haS, haB⟩ := exists_mem_sqPre hAB hab hlt hA
        have hBlt : B < sqPre A B hAB hab := lt_of_le_of_ne hBS fun h => haB (h ▸ haS)
        rcases lt_or_eq_of_le (show sqPre A B hAB hab ≤ A from fun x hx => hx.1) with h | h
        · exact absurd (fun g hg => mem_normalizer_sqPre hAB hab (hLA hg) (hLB hg))
            (hsplit _ hBlt h (le_normalizer_of_comm_mod hBS hab (fun x hx => hx.1)))
        · exact h
      have hsq : ∀ a ∈ A, a ^ 2 ∈ B := by
        intro a ha
        have h : a ∈ sqPre A B hAB hab := by rw [hS]; exact ha
        exact h.2
      have hirr : ∀ C : Subgroup G, B ≤ C → C ≤ A → L ≤ normalizer (C : Set G) →
          C = B ∨ C = A := by
        intro C hBC hCA hLC
        rcases lt_or_eq_of_le hBC with h1 | h1
        · rcases lt_or_eq_of_le hCA with h2 | h2
          · exact absurd hLC (hsplit C h1 h2 (le_normalizer_of_comm_mod hBC hab hCA))
          · exact Or.inr h2
        · exact Or.inl h1.symm
      exact hbase A B hAB hlt hA hLA hLB hab hsq hirr

end CFSG.Quasithin.H13.U3.NLine
