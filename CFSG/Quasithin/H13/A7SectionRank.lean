module

public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open

theorem card_le_pow_of_fixes {α : Type*} [DecidableEq α] [Fintype α] {p : ℕ}
    [hp : Fact p.Prime] (m : ℕ) : ∀ (X : Finset α), X.card = m → ∀ (E : Subgroup (Perm α)),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ p = 1) →
      (∀ e ∈ E, ∀ x ∉ X, e x = x) → Nat.card E ≤ p ^ (m / p) := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X hX E hcomm hpow hfix
  by_cases hE : E = ⊥
  · rw [hE, card_bot]
    exact Nat.one_le_pow _ _ hp.out.pos
  obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
  obtain ⟨x, hx⟩ : ∃ x, (e : Perm α) x ≠ x := by
    by_contra h
    push Not at h
    exact he1 (Subtype.ext (Equiv.ext h))
  have hxX : x ∈ X := by
    by_contra h
    exact hx (hfix e e.2 x h)
  have hE2 : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hpow g g.2)⟩
  set O := MulAction.orbit E x with hO
  obtain ⟨a, ha⟩ := hE2.card_orbit x
  rw [← hO] at ha
  have hsm : ∀ (g : E) (y : α), g • y = (g : Perm α) y := fun _ _ => rfl
  have hOX : ∀ y ∈ O, y ∈ X := by
    rintro _ ⟨g, rfl⟩
    by_contra h
    have h1 := hfix (g⁻¹ : E) (g⁻¹).2 _ h
    have h2 : ((g⁻¹ : E) : Perm α) (g • x) = x := by
      rw [hsm]
      simp
    have h3 : g • x = x := h1.symm.trans h2
    apply h
    show g • x ∈ X
    rw [h3]
    exact hxX
  have hO2 : 2 ≤ Nat.card O := by
    have hxO : x ∈ O := MulAction.mem_orbit_self x
    have hexO : (e : Perm α) x ∈ O := ⟨e, rfl⟩
    have : ({x, (e : Perm α) x} : Set α) ⊆ O := by
      intro y hy
      rcases hy with rfl | rfl
      · exact hxO
      · exact hexO
    have h := Set.ncard_le_ncard this (Set.toFinite O)
    rw [Set.ncard_pair hx.symm] at h
    rwa [Nat.card_coe_set_eq]
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero] at ha
      omega
    · exact h
  set K := (MulAction.stabilizer E x).map E.subtype with hK
  have hKfix : ∀ k ∈ K, ∀ y ∉ X \ (Set.toFinite O).toFinset, k y = y := by
    rintro _ ⟨k, hk, rfl⟩ y hy
    rw [Finset.mem_sdiff, not_and_or, not_not, Set.Finite.mem_toFinset] at hy
    rcases hy with hy | ⟨g, rfl⟩
    · exact hfix k k.2 y hy
    · have hkx : (k : Perm α) x = x := hk
      show (k : Perm α) ((g : Perm α) x) = (g : Perm α) x
      rw [← Perm.mul_apply, hcomm k k.2 g g.2, Perm.mul_apply, hkx]
  have hOcard : (Set.toFinite O).toFinset.card = p ^ a := by
    rw [← Set.ncard_eq_toFinset_card O, ← Nat.card_coe_set_eq, ha]
  have hsub : (Set.toFinite O).toFinset ⊆ X :=
    fun y hy => hOX y ((Set.Finite.mem_toFinset _).1 hy)
  have hcardX' : (X \ (Set.toFinite O).toFinset).card = m - p ^ a := by
    rw [Finset.card_sdiff_of_subset hsub, hX, hOcard]
  have hpa : p ^ a ≤ m := by
    have h := Finset.card_le_card hsub
    rwa [hX, hOcard] at h
  have hlt : m - p ^ a < m := by
    have : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp.out.pos
    omega
  have hK' := ih _ hlt _ hcardX' K
    (by rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩; exact hcomm u u.2 v v.2)
    (by rintro _ ⟨u, -, rfl⟩; exact hpow u u.2) hKfix
  have hKcard : Nat.card K = Nat.card (MulAction.stabilizer E x) :=
    card_map_of_injective E.subtype_injective
  have hEcard : Nat.card E = Nat.card (MulAction.stabilizer E x) * p ^ a := by
    rw [← card_mul_index (MulAction.stabilizer E x), MulAction.index_stabilizer,
      ← hO, ← Nat.card_coe_set_eq, ha]
  rw [hEcard, ← hKcard]
  calc Nat.card K * p ^ a ≤ p ^ ((m - p ^ a) / p) * p ^ a := Nat.mul_le_mul_right _ hK'
    _ = p ^ ((m - p ^ a) / p + a) := by rw [pow_add]
    _ ≤ p ^ (m / p) := by
      apply Nat.pow_le_pow_right hp.out.pos
      have hpa' : p ^ a = p * p ^ (a - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h1 : (m - p ^ a) / p = m / p - p ^ (a - 1) := by
        rw [hpa', Nat.sub_mul_div]
      have h2 : a - 1 < p ^ (a - 1) := Nat.lt_pow_self hp.out.one_lt
      have h3 : p ^ (a - 1) ≤ m / p := by
        rw [Nat.le_div_iff_mul_le hp.out.pos, mul_comm, ← hpa']
        exact hpa
      omega

theorem finRotate_pow_self {p : ℕ} (hp : 2 ≤ p) : finRotate p ^ p = 1 := by
  have h := (isCycle_finRotate_of_le hp).orderOf
  rw [support_finRotate_of_le hp, Finset.card_univ, Fintype.card_fin] at h
  rw [← pow_orderOf_eq_one (finRotate p), h]

@[expose] def blockEquiv {n p : ℕ} (k : ℕ) (hk : (k + 1) * p ≤ n) :
    Fin p ≃ {x : Fin n // k * p ≤ x.val ∧ x.val < k * p + p} where
  toFun i := ⟨⟨k * p + i, by have := i.2; nlinarith⟩, by simp, by simp [i.2]⟩
  invFun x := ⟨x.1.val - k * p, by have := x.2; omega⟩
  left_inv i := by ext; simp
  right_inv x := by
    ext
    simp only
    have := x.2.1
    omega

theorem blockCycle_spec {n p : ℕ} (k : ℕ) (hk : (k + 1) * p ≤ n) (hp : 2 ≤ p) :
    ((finRotate p).extendDomain (blockEquiv k hk)) ^ p = 1 ∧
      (∀ x : Fin n, x.val < k * p ∨ k * p + p ≤ x.val →
        (finRotate p).extendDomain (blockEquiv k hk) x = x) ∧
      (finRotate p).extendDomain (blockEquiv k hk) ⟨k * p, by nlinarith⟩ ≠
        ⟨k * p, by nlinarith⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · show (extendDomainHom (blockEquiv k hk)) (finRotate p) ^ p = 1
    rw [← map_pow, finRotate_pow_self hp, map_one]
  · intro x hx
    apply extendDomain_apply_not_subtype
    omega
  · intro h
    have : NeZero p := ⟨by omega⟩
    have h0 : (blockEquiv k hk ⟨0, by omega⟩ : Fin n) = ⟨k * p, by nlinarith⟩ := by
      ext
      simp [blockEquiv]
    have h1 := extendDomain_apply_image (finRotate p) (blockEquiv k hk) ⟨0, by omega⟩
    rw [h0] at h1
    rw [h1] at h
    have h2 := congrArg Fin.val h
    simp [blockEquiv, finRotate_apply] at h2
    omega

theorem exists_elementary_alternating {n p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ k : ℕ, k * p ≤ n → ∃ (B : Type) (_ : Group B), (∀ a b : B, a * b = b * a) ∧
      (∀ a : B, a ^ p = 1) ∧ Nat.card B = p ^ k ∧
      ∃ F : B →* alternatingGroup (Fin n), Function.Injective F ∧
        ∀ b (x : Fin n), k * p ≤ x.val →
          ((F b : alternatingGroup (Fin n)) : Perm (Fin n)) x = x := by
  classical
  have hp2' : 2 ≤ p := hp.out.two_le
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Unit, inferInstance, fun _ _ => rfl, fun _ => rfl, by simp, 1,
      fun _ _ _ => Subsingleton.elim _ _, fun _ x _ => by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨B, _, hcomm, hpow, hB, F, hF, hfix⟩ := ih (by nlinarith)
    have hsign : sign (finRotate p) = 1 := by
      obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have hodd : Odd p := hp.out.odd_of_ne_two hp2
      rw [hq, sign_finRotate]
      have hq2 : Even q := by
        rcases hodd with ⟨r, hr⟩
        exact ⟨r, by omega⟩
      exact hq2.neg_one_pow
    obtain ⟨hy5, hyfix, hymove⟩ := blockCycle_spec k hk hp2'
    set y : alternatingGroup (Fin n) := ⟨(finRotate p).extendDomain (blockEquiv k hk),
      mem_alternatingGroup.2 (by rw [sign_extendDomain, hsign])⟩ with hydef
    have hy : y ^ p = 1 := Subtype.ext (by simpa [hydef] using hy5)
    have hy1 : y ∉ F.range := by
      rintro ⟨b, hb⟩
      apply hymove
      have h1 := hfix b ⟨k * p, by nlinarith⟩ le_rfl
      rw [hb] at h1
      exact h1
    have hyc : ∀ b, Commute (F b) y := by
      intro b
      have hd : Disjoint ((F b : alternatingGroup (Fin n)) : Perm (Fin n)) (y : Perm (Fin n)) := by
        intro x
        by_cases hx : k * p ≤ x.val
        · exact Or.inl (hfix b x hx)
        · exact Or.inr (hyfix x (Or.inl (by omega)))
      exact Subtype.ext hd.commute
    obtain ⟨F', hF', hc', hp', hcard', hform⟩ :=
      CFSG.SectionRank.exists_extend hcomm hpow hB F hF hy hy1 hyc
    refine ⟨B × Subgroup.zpowers y, inferInstance, hc', hp', hcard', F', hF', fun a x hx => ?_⟩
    obtain ⟨b, m, hm⟩ := hform a
    rw [hm, Subgroup.coe_mul, Perm.mul_apply, SubgroupClass.coe_pow]
    have hyx : (y : Perm (Fin n)) x = x := hyfix x (Or.inr (by nlinarith))
    rw [pow_apply_eq_self_of_apply_eq_self hyx]
    exact hfix b x (by nlinarith)

theorem section_rank_alternating_odd_prime_rank :
    (∀ n p : ℕ, p.Prime → p ≠ 2 → pRank p (⊤ : Subgroup (alternatingGroup (Fin n))) = n / p) ∧
      pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) = 2 ∧
      pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 7))) = 2 ∧
      pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 9))) = 3 ∧
      pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 10))) = 3 := by
  classical
  have hmain : ∀ n p : ℕ, p.Prime → p ≠ 2 →
      pRank p (⊤ : Subgroup (alternatingGroup (Fin n))) = n / p := by
    intro n p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    apply le_antisymm
    · refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
      have h := card_le_pow_of_fixes (α := Fin n) (p := p) n Finset.univ (by simp)
        (E.map (alternatingGroup (Fin n)).subtype)
        (by
          rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
          exact congrArg Subtype.val
            (congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)))
        (by
          rintro _ ⟨u, hu, rfl⟩
          simpa using congrArg Subtype.val (hE.2 u hu))
        (fun _ _ x hx => absurd (Finset.mem_univ x) hx)
      rwa [card_map_of_injective (alternatingGroup (Fin n)).subtype_injective] at h
    · obtain ⟨B, _, hcomm, hpow, hB, F, hF, -⟩ :=
        exists_elementary_alternating (n := n) hp2 (n / p) (Nat.div_mul_le_self n p)
      exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hB F hF le_top
  refine ⟨hmain, ?_, ?_, ?_, ?_⟩
  · exact hmain 6 3 Nat.prime_three (by norm_num)
  · exact hmain 7 3 Nat.prime_three (by norm_num)
  · exact hmain 9 3 Nat.prime_three (by norm_num)
  · exact hmain 10 3 Nat.prime_three (by norm_num)

end CFSG.Quasithin.H13.A7
