module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.F126

open Equiv

abbrev S53 : Type := Perm (Fin 5) × Perm (Fin 3)

@[expose] def c3 : Perm (Fin 3) := swap 0 1 * swap 1 2

@[expose] def s3 : Perm (Fin 3) := swap 0 1

theorem c3_pow_three : c3 ^ 3 = 1 := by decide

theorem c3_ne_one : c3 ≠ 1 := by decide

theorem s3_sq : s3 ^ 2 = 1 := by decide

theorem s3_conj : s3 * c3 * s3⁻¹ = c3 ^ 2 := by decide

theorem conj_c3 : ∀ s : Perm (Fin 3), s * c3 * s⁻¹ = c3 ∨ s * c3 * s⁻¹ = c3 ^ 2 := by decide

theorem eq_one_of_comm_c3 : ∀ s : Perm (Fin 3), s ^ 2 = 1 → s * c3 = c3 * s → s = 1 := by decide

theorem mem_c3 : ∀ s : Perm (Fin 3), s ^ 3 = 1 → s = 1 ∨ s = c3 ∨ s = c3 ^ 2 := by decide

theorem pow_nine : ∀ q : S53, q ^ 9 = 1 → q ^ 3 = 1 := by decide +kernel

theorem card_S53 : Nat.card S53 = 720 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin]
  rfl

theorem s5_klein : ∀ a : Perm (Fin 5), a ≠ 1 ∧ a ^ 2 = 1 → ∀ b : Perm (Fin 5),
    b ≠ 1 ∧ b ^ 2 = 1 ∧ a ≠ b ∧ a * b = b * a → ∀ y : Perm (Fin 5),
    (y ≠ 1 ∧ y ^ 3 = 1 ∧ (y * a * y⁻¹ = a ∨ y * a * y⁻¹ = b ∨ y * a * y⁻¹ = a * b) ∧
      (y * b * y⁻¹ = a ∨ y * b * y⁻¹ = b ∨ y * b * y⁻¹ = a * b)) →
    Perm.sign a = 1 ∧ Perm.sign b = 1 := by
  decide +kernel

variable {Q : Type*} [Group Q] (e : Q ≃* S53)

@[expose] def xQ : Q := e.symm (1, c3)

@[expose] def tQ : Q := e.symm (1, s3)

@[expose] def ιA5 : ↥(alternatingGroup (Fin 5)) →* Q :=
  e.symm.toMonoidHom.comp ((MonoidHom.inl (Perm (Fin 5)) (Perm (Fin 3))).comp
    (alternatingGroup (Fin 5)).subtype)

theorem ιA5_apply (a : ↥(alternatingGroup (Fin 5))) : ιA5 e a = e.symm ((a : Perm (Fin 5)), 1) :=
  rfl

theorem ιA5_injective : Function.Injective (ιA5 e) := by
  intro a b h
  rw [ιA5_apply, ιA5_apply] at h
  have := congrArg Prod.fst (e.symm.injective h)
  exact Subtype.ext this

theorem xQ_pow_three : xQ e ^ 3 = 1 := by
  rw [xQ, ← map_pow, Prod.pow_mk, one_pow, c3_pow_three]
  exact map_one e.symm

theorem xQ_ne_one : xQ e ≠ 1 := by
  intro h
  have := congrArg e h
  rw [xQ, MulEquiv.apply_symm_apply, map_one] at this
  exact c3_ne_one (congrArg Prod.snd this)

theorem tQ_sq : tQ e ^ 2 = 1 := by
  rw [tQ, ← map_pow, Prod.pow_mk, one_pow, s3_sq]
  exact map_one e.symm

theorem tQ_conj : tQ e * xQ e * (tQ e)⁻¹ = xQ e ^ 2 := by
  rw [tQ, xQ, ← map_inv, ← map_mul, ← map_mul, ← map_pow, Prod.inv_mk, Prod.mk_mul_mk,
    Prod.mk_mul_mk, Prod.pow_mk, one_pow, inv_one, mul_one, mul_one, s3_conj]

theorem conj_xQ (q : Q) : q * xQ e * q⁻¹ = xQ e ∨ q * xQ e * q⁻¹ = xQ e ^ 2 := by
  obtain ⟨⟨g, s⟩, rfl⟩ := e.symm.surjective q
  rw [xQ, ← map_inv, ← map_mul, ← map_mul, ← map_pow, Prod.inv_mk, Prod.mk_mul_mk,
    Prod.mk_mul_mk, Prod.pow_mk, one_pow, mul_one, mul_inv_cancel]
  rcases conj_c3 s with h | h
  · left; rw [h]
  · right; rw [h]

theorem ιA5_comm_xQ (a : ↥(alternatingGroup (Fin 5))) : ιA5 e a * xQ e = xQ e * ιA5 e a := by
  rw [ιA5_apply, xQ, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one,
    mul_one, one_mul]

theorem ιA5_comm_tQ (a : ↥(alternatingGroup (Fin 5))) : ιA5 e a * tQ e = tQ e * ιA5 e a := by
  rw [ιA5_apply, tQ, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one,
    mul_one, one_mul]

theorem zpowers_xQ_normal : (Subgroup.zpowers (xQ e)).Normal := by
  refine ⟨fun n hn q => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← conj_zpow]
  rcases conj_xQ e q with h | h
  · rw [h]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  · rw [h]; exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) _

theorem card_zpowers_xQ : Nat.card (Subgroup.zpowers (xQ e)) = 3 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (xQ_pow_three e) (xQ_ne_one e)

theorem mem_zpowers_of_fst {q : Q} (hq3 : q ^ 3 = 1) (h1 : (e q).1 = 1) :
    q ∈ Subgroup.zpowers (xQ e) := by
  have h3 : (e q).2 ^ 3 = 1 := by
    have := congrArg (fun r => (e r).2) hq3
    simpa [map_pow] using this
  have hq : q = e.symm (1, (e q).2) := by
    rw [← h1, Prod.mk.eta, MulEquiv.symm_apply_apply]
  have he1 : (e.symm (1, 1) : Q) = 1 := map_one e.symm
  rcases mem_c3 _ h3 with h | h | h
  · rw [hq, h, he1]
    exact Subgroup.one_mem _
  · rw [hq, h]
    exact Subgroup.mem_zpowers _
  · rw [hq, h, ← one_pow 2, ← Prod.pow_mk, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

variable [Finite Q]

include e in
omit [Finite Q] in
theorem card_Q : Nat.card Q = 720 := by rw [Nat.card_congr e.toEquiv, card_S53]

theorem zpowers_le_of_dvd {N : Subgroup Q} (hN : 9 ∣ Nat.card N) :
    Subgroup.zpowers (xQ e) ≤ N := by
  have := zpowers_xQ_normal e
  by_contra hle
  have hinf : Subgroup.zpowers (xQ e) ⊓ N = ⊥ := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers (xQ e) ⊓ N ≤ _)
    rw [card_zpowers_xQ] at h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hle
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Subgroup.zpowers (xQ e) ⊓ N ≤ _)
        (by rw [h, card_zpowers_xQ])
      rw [← this]
      exact inf_le_right
  have h1 := Subgroup.relIndex_sup_left N (Subgroup.zpowers (xQ e))
  have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers (xQ e)) N
  rw [hinf, Subgroup.card_bot, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card (Subgroup.zpowers (xQ e))
    (Subgroup.zpowers (xQ e) ⊔ N)
  rw [inf_eq_left.2 le_sup_left, card_zpowers_xQ, h1, h2] at h3
  have h4 := Subgroup.card_dvd_of_le (le_top : Subgroup.zpowers (xQ e) ⊔ N ≤ ⊤)
  rw [Subgroup.card_top, card_Q e, ← h3] at h4
  obtain ⟨k, hk⟩ := hN
  rw [hk] at h4
  have : 27 ∣ 720 := Dvd.dvd.trans ⟨k, by ring⟩ h4
  norm_num at this

theorem le_range_ιA5 {N P : Subgroup Q} (hPN : P ≤ N)
    (hNP : N ≤ Subgroup.normalizer (P : Set Q)) (hP4 : Nat.card P = 4)
    (hP2 : ∀ p ∈ P, p ^ 2 = 1) (hN : 9 ∣ Nat.card N) : P ≤ (ιA5 e).range := by
  have hXN := zpowers_le_of_dvd e hN
  have hxN : xQ e ∈ N := hXN (Subgroup.mem_zpowers _)
  have hPX : P ⊓ Subgroup.zpowers (xQ e) = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (by rw [hP4, card_zpowers_xQ]; norm_num))
  have hcomm : ∀ p ∈ P, p * xQ e = xQ e * p := by
    intro p hp
    have hn := zpowers_xQ_normal e
    have h1 : p * xQ e * p⁻¹ * (xQ e)⁻¹ ∈ Subgroup.zpowers (xQ e) :=
      Subgroup.mul_mem _ (hn.conj_mem _ (Subgroup.mem_zpowers _) p)
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
    have h2 : p * xQ e * p⁻¹ * (xQ e)⁻¹ ∈ P := by
      have : xQ e * p⁻¹ * (xQ e)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.1 (hNP hxN) p⁻¹).1 (P.inv_mem hp)
      have e1 : p * xQ e * p⁻¹ * (xQ e)⁻¹ = p * (xQ e * p⁻¹ * (xQ e)⁻¹) := by group
      rw [e1]
      exact P.mul_mem hp this
    have h3 : p * xQ e * p⁻¹ * (xQ e)⁻¹ ∈ P ⊓ Subgroup.zpowers (xQ e) := ⟨h2, h1⟩
    rw [hPX, Subgroup.mem_bot] at h3
    calc p * xQ e = (p * xQ e * p⁻¹ * (xQ e)⁻¹) * (xQ e * p) := by group
      _ = xQ e * p := by rw [h3, one_mul]
  have hsnd : ∀ p ∈ P, (e p).2 = 1 := by
    intro p hp
    have h2 := congrArg (fun r => (e r).2) (hP2 p hp)
    have hc := congrArg (fun r => (e r).2) (hcomm p hp)
    simp only [map_pow, Prod.pow_snd, map_one, Prod.snd_one, map_mul, Prod.snd_mul, xQ,
      MulEquiv.apply_symm_apply] at h2 hc
    exact eq_one_of_comm_c3 _ h2 hc
  obtain ⟨y, hyN, hy3, hy1⟩ : ∃ y ∈ N, y ^ 3 = 1 ∧ (e y).1 ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) 3 (n := 2) hN
    have hSX : S.map N.subtype ≤ Subgroup.zpowers (xQ e) := by
      rintro _ ⟨s, hs, rfl⟩
      have hs9 : (s : Q) ^ 9 = 1 := by
        have := pow_card_eq_one' (G := S) (x := ⟨s, hs⟩)
        rw [hS] at this
        have := congrArg (fun z : ↥S => ((z : ↥N) : Q)) this
        simpa using this
      have hs3 : (s : Q) ^ 3 = 1 := by
        have := pow_nine (e s) (by rw [← map_pow, hs9, map_one])
        rw [← map_pow] at this
        exact e.injective (this.trans (map_one e).symm)
      exact mem_zpowers_of_fst e hs3 (hno s s.2 hs3)
    have h1 := Subgroup.card_le_of_le hSX
    rw [Subgroup.card_map_of_injective N.subtype_injective, hS, card_zpowers_xQ] at h1
    norm_num at h1
  classical
  have hPn : (P : Set Q).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hP4
  obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra h
    push Not at h
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 h
    rw [this, Subgroup.card_bot] at hP4
    norm_num at hP4
  obtain ⟨b, hbP, hb1, hba⟩ : ∃ b ∈ P, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (P : Set Q) ⊆ {1, a} := fun p hp => by
      by_cases hp1 : p = 1
      · exact Or.inl hp1
      · exact Or.inr (h p hp hp1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hPn] at this
    have h2 := Set.ncard_insert_le (1 : Q) {a}
    rw [Set.ncard_singleton] at h2
    omega
  have habc : a * b = b * a := by
    have h := hP2 (a * b) (P.mul_mem haP hbP)
    have ha := hP2 a haP
    have hb := hP2 b hbP
    rw [pow_two] at h ha hb
    calc a * b = a * (a * b * (a * b)) * b := by rw [h, mul_one]
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [ha, hb, one_mul, mul_one]
  have hab1 : a * b ≠ 1 := fun h' => hba (by
    have h2 := hP2 b hbP
    rw [pow_two] at h2
    calc b = a * b * b := by rw [h', one_mul]
      _ = a := by rw [mul_assoc, h2, mul_one])
  have haba : a * b ≠ a := fun h' => hb1 (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h', inv_mul_cancel])
  have habb : a * b ≠ b := fun h' => ha1 (by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [h', mul_inv_cancel])
  have hs : ({1, a, b, a * b} : Finset Q).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair habb.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hba.symm, haba.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  have hsub : (({1, a, b, a * b} : Finset Q) : Set Q) ⊆ P := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact haP
    · exact hbP
    · exact P.mul_mem haP hbP
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Set.ncard_coe_finset, hs, hPn]) (Set.toFinite _)
  have hall : ∀ p ∈ P, p = 1 ∨ p = a ∨ p = b ∨ p = a * b := fun p hp => by
    have : p ∈ (({1, a, b, a * b} : Finset Q) : Set Q) := heq ▸ hp
    simpa using this
  have hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P := fun p hp =>
    (Subgroup.mem_normalizer_iff.1 (hNP hyN) p).1 hp
  have hfst : ∀ p, (e p).1 = 1 → (e p).2 = 1 → p = 1 := fun p h1 h2 => by
    apply e.injective
    rw [map_one]
    exact Prod.ext h1 h2
  have ha1' : (e a).1 ≠ 1 := fun h => ha1 (hfst a h (hsnd a haP))
  have hb1' : (e b).1 ≠ 1 := fun h => hb1 (hfst b h (hsnd b hbP))
  have hab' : (e a).1 ≠ (e b).1 := fun h => hba (by
    apply e.injective
    exact Prod.ext h.symm ((hsnd b hbP).trans (hsnd a haP).symm))
  have hconj : ∀ p ∈ P, (e (y * p * y⁻¹)).1 = (e y).1 * (e p).1 * ((e y).1)⁻¹ := fun p _ => by
    simp [map_mul, map_inv]
  have hcase : ∀ p ∈ P, p ≠ 1 → ((e (y * p * y⁻¹)).1 = (e a).1 ∨
      (e (y * p * y⁻¹)).1 = (e b).1 ∨ (e (y * p * y⁻¹)).1 = (e a).1 * (e b).1) := by
    intro p hp hp1
    have hne : y * p * y⁻¹ ≠ 1 := fun h => hp1 (by
      have := congrArg (fun z => y⁻¹ * z * y) h
      simpa [mul_assoc] using this)
    rcases hall _ (hyP p hp) with h | h | h | h
    · exact absurd h hne
    · left; rw [h]
    · right; left; rw [h]
    · right; right; rw [h, map_mul, Prod.fst_mul]
  have hsign := s5_klein (e a).1 ⟨ha1', by
      have := congrArg (fun r => (e r).1) (hP2 a haP); simpa [map_pow] using this⟩
    (e b).1 ⟨hb1', by
      have := congrArg (fun r => (e r).1) (hP2 b hbP); simpa [map_pow] using this, hab', by
      have := congrArg (fun r => (e r).1) habc; simpa [map_mul] using this⟩
    (e y).1 ⟨hy1, by
      have := congrArg (fun r => (e r).1) hy3; simpa [map_pow] using this,
      by rw [← hconj a haP]; exact hcase a haP ha1, by rw [← hconj b hbP]; exact hcase b hbP hb1⟩
  intro p hp
  have hpA : (e p).1 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases hall p hp with rfl | rfl | rfl | rfl
    · simp
    · exact hsign.1
    · exact hsign.2
    · rw [map_mul, Prod.fst_mul, Perm.sign_mul, hsign.1, hsign.2, mul_one]
  refine ⟨⟨(e p).1, hpA⟩, ?_⟩
  rw [ιA5_apply]
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  exact Prod.ext rfl (hsnd p hp).symm

end CFSG.Quasithin.H13.F126
