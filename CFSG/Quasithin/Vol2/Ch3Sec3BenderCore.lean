module

public import CFSG.Quasithin.Vol2.Ch3Sec3BenderL2
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.H13.BenC

open Subgroup CFSG.Quasithin.H13.BenL2
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {Q : Type*} [Group Q] [Finite Q]

section Prod

variable {A A' : Subgroup Q}

omit [Finite Q] in
theorem le_normalizer_of_comm (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) :
    A' ≤ normalizer (A : Set Q) := fun b hb =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)

omit [Finite Q] in
theorem mem_sup_iff (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) {z : Q} :
    z ∈ A ⊔ A' ↔ ∃ a ∈ A, ∃ a' ∈ A', z = a * a' :=
  B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)

omit [Finite Q] in
theorem eq_of_mul_eq (hi : A ⊓ A' = ⊥) {a b a' b' : Q} (ha : a ∈ A) (hb : b ∈ A)
    (ha' : a' ∈ A') (hb' : b' ∈ A') (h : a * a' = b * b') : a = b ∧ a' = b' := by
  have h1 : b⁻¹ * a = b' * a'⁻¹ := by
    calc b⁻¹ * a = b⁻¹ * (a * a') * a'⁻¹ := by group
      _ = b⁻¹ * (b * b') * a'⁻¹ := by rw [h]
      _ = b' * a'⁻¹ := by group
  have h2 : b⁻¹ * a ∈ A ⊓ A' := ⟨A.mul_mem (A.inv_mem hb) ha, h1 ▸ A'.mul_mem hb' (A'.inv_mem ha')⟩
  rw [hi, mem_bot] at h2
  have hab : a = b := by
    have := congrArg (b * ·) h2
    simpa using this
  refine ⟨hab, ?_⟩
  subst hab
  exact mul_left_cancel h

omit [Finite Q] in
theorem mul_mem_normalizer (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) {S : Subgroup Q} (hSA : S ≤ A)
    {a a' : Q} (ha' : a' ∈ A') (haN : a ∈ normalizer (S : Set Q)) :
    a * a' ∈ normalizer (S : Set Q) := by
  refine Subgroup.mul_mem _ haN ?_
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
  exact hc s (hSA hs) a' ha'

omit [Finite Q] in
theorem mem_normalizer_of_mul (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) {S : Subgroup Q}
    (hSA : S ≤ A) {a a' : Q} (ha' : a' ∈ A') (h : a * a' ∈ normalizer (S : Set Q)) :
    a ∈ normalizer (S : Set Q) := by
  have h1 : a'⁻¹ ∈ normalizer (S : Set Q) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun s hs =>
      hc s (hSA hs) _ (A'.inv_mem ha'))
  have := Subgroup.mul_mem _ h h1
  rwa [mul_inv_cancel_right] at this

end Prod

theorem eq_of_isSylowTwoOf {A S X : Subgroup Q} (hS : IsSylowTwoOf S A) (hSX : S ≤ X)
    (hXA : X ≤ A) (hX : IsPGroup 2 X) : X = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (le_antisymm hSX ?_).symm
  have h1 : ¬ 2 ∣ S.relIndex X := fun h2 =>
    hS.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex S X A hSX hXA)))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  have h2 : S.relIndex X ∣ 2 ^ n := by
    rw [← hn]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := S) (K := X))
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hm0 : m = 0 := by
    by_contra hm0
    exact h1 (hm' ▸ dvd_pow_self 2 hm0)
  rw [hm0, pow_zero] at hm'
  exact Subgroup.relIndex_eq_one.mp hm'

omit [Finite Q] in
theorem isSylowTwoOf_conj {A S : Subgroup Q} (hS : IsSylowTwoOf S A) {b : Q} (hb : b ∈ A) :
    IsSylowTwoOf (S.map (MulAut.conj b).toMonoidHom) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, hS.2.1.map _, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact A.mul_mem (A.mul_mem hb (hS.1 hs)) (A.inv_mem hb)
  · have e : (S.map (MulAut.conj b).toMonoidHom).subgroupOf A =
        (S.subgroupOf A).map (MulAut.conj (⟨b, hb⟩ : ↥A)).toMonoidHom := by
      ext x
      simp only [mem_subgroupOf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨s, hs, hsx⟩
        refine ⟨⟨s, hS.1 hs⟩, hs, Subtype.ext ?_⟩
        simpa using hsx
      · rintro ⟨s, hs, hsx⟩
        refine ⟨s, hs, ?_⟩
        rw [← hsx]
        simp
    rw [e, Subgroup.index_map_of_bijective (MulAut.conj _).bijective]
    exact hS.2.2

section Core

variable {A A' T U Y P D : Subgroup Q} {q : ℕ} {t : Q}

theorem inf_sup_le (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    (hS : IsSylowTwoOf (T ⊓ A) A) (hS' : IsSylowTwoOf (T ⊓ A') A') (hT : IsPGroup 2 T) :
    T ⊓ (A ⊔ A') ≤ T ⊓ A ⊔ T ⊓ A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup Q :=
    { carrier := {a | a ∈ A ∧ ∃ a' ∈ A', a * a' ∈ T}
      one_mem' := ⟨A.one_mem, 1, A'.one_mem, by simp [T.one_mem]⟩
      mul_mem' := fun {a b} ⟨ha, a', ha', hT1⟩ ⟨hb, b', hb', hT2⟩ => ⟨A.mul_mem ha hb, a' * b',
        A'.mul_mem ha' hb', by
          have e : a * b * (a' * b') = a * a' * (b * b') := by
            calc a * b * (a' * b') = a * (b * a') * b' := by group
              _ = a * (a' * b) * b' := by rw [hc b hb a' ha']
              _ = a * a' * (b * b') := by group
          rw [e]
          exact T.mul_mem hT1 hT2⟩
      inv_mem' := fun {a} ⟨ha, a', ha', hT1⟩ => ⟨A.inv_mem ha, a'⁻¹, A'.inv_mem ha', by
          have e : a⁻¹ * a'⁻¹ = (a * a')⁻¹ := by
            rw [mul_inv_rev, (hc _ (A.inv_mem ha) _ (A'.inv_mem ha'))]
          rw [e]
          exact T.inv_mem hT1⟩ }
  let X' : Subgroup Q :=
    { carrier := {a' | a' ∈ A' ∧ ∃ a ∈ A, a * a' ∈ T}
      one_mem' := ⟨A'.one_mem, 1, A.one_mem, by simp [T.one_mem]⟩
      mul_mem' := fun {a' b'} ⟨ha', a, ha, hT1⟩ ⟨hb', b, hb, hT2⟩ => ⟨A'.mul_mem ha' hb', a * b,
        A.mul_mem ha hb, by
          have e : a * b * (a' * b') = a * a' * (b * b') := by
            calc a * b * (a' * b') = a * (b * a') * b' := by group
              _ = a * (a' * b) * b' := by rw [hc b hb a' ha']
              _ = a * a' * (b * b') := by group
          rw [e]
          exact T.mul_mem hT1 hT2⟩
      inv_mem' := fun {a'} ⟨ha', a, ha, hT1⟩ => ⟨A'.inv_mem ha', a⁻¹, A.inv_mem ha, by
          have e : a⁻¹ * a'⁻¹ = (a * a')⁻¹ := by
            rw [mul_inv_rev, (hc _ (A.inv_mem ha) _ (A'.inv_mem ha'))]
          rw [e]
          exact T.inv_mem hT1⟩ }
  have hpow : ∀ {a a' : Q}, a ∈ A → a' ∈ A' → ∀ n : ℕ, (a * a') ^ n = a ^ n * a' ^ n := by
    intro a a' ha ha' n
    exact (Commute.mul_pow (hc a ha a' ha') n)
  have hX2 : IsPGroup 2 X := by
    rintro ⟨a, ha, a', ha', haT⟩
    obtain ⟨k, hk⟩ := hT ⟨_, haT⟩
    have hk' : (a * a') ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hpow ha ha'] at hk'
    have h1 := (eq_of_mul_eq hi (A.pow_mem ha _) A.one_mem (A'.pow_mem ha' _) A'.one_mem
      (by rw [hk', one_mul])).1
    exact ⟨k, Subtype.ext (by simpa using h1)⟩
  have hX'2 : IsPGroup 2 X' := by
    rintro ⟨a', ha', a, ha, haT⟩
    obtain ⟨k, hk⟩ := hT ⟨_, haT⟩
    have hk' : (a * a') ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hpow ha ha'] at hk'
    have h1 := (eq_of_mul_eq hi (A.pow_mem ha _) A.one_mem (A'.pow_mem ha' _) A'.one_mem
      (by rw [hk', one_mul])).2
    exact ⟨k, Subtype.ext (by simpa using h1)⟩
  have hXS : X = T ⊓ A := eq_of_isSylowTwoOf hS (fun a ha => ⟨ha.2, 1, A'.one_mem, by
    simpa using ha.1⟩) (fun a ha => ha.1) hX2
  have hX'S : X' = T ⊓ A' := eq_of_isSylowTwoOf hS' (fun a ha => ⟨ha.2, 1, A.one_mem, by
    simpa using ha.1⟩) (fun a ha => ha.1) hX'2
  rintro z ⟨hzT, hzA⟩
  obtain ⟨a, ha, a', ha', rfl⟩ := (mem_sup_iff hc).mp hzA
  have h1 : a ∈ X := ⟨ha, a', ha', hzT⟩
  have h2 : a' ∈ X' := ⟨ha', a, ha, hzT⟩
  rw [hXS] at h1
  rw [hX'S] at h2
  exact Subgroup.mul_mem_sup h1 h2

theorem le_normalizer_sylow (hA : BorelL2 A q) (hq : 4 ≤ q)
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    (hS : IsSylowTwoOf (T ⊓ A) A) (hS' : IsSylowTwoOf (T ⊓ A') A') (hT : IsPGroup 2 T)
    (hA'q : Nat.card ↥(T ⊓ A') = q)
    (ht : t ∈ T) (htA : ∀ a, a ∈ A ↔ t * a * t⁻¹ ∈ A')
    (hUT : U ≤ T) (hU8 : U.relIndex T ≤ 8) (hTU : T ≤ normalizer (U : Set Q))
    (hYU : Y ≤ normalizer (U : Set Q)) :
    ∀ y ∈ Y, ∀ b ∈ A, ∀ b' ∈ A', y = b * b' → b ∈ normalizer ((T ⊓ A : Subgroup Q) : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := T ⊓ A with hSdef
  set S' := T ⊓ A' with hS'def
  have hSS : S' ≤ normalizer (S : Set Q) := fun s hs =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx.2 s hs.2)
  have hcard : Nat.card ↥(S ⊔ S') = q * q := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hSS
    have h2 : S ⊓ S' = ⊥ := eq_bot_iff.mpr fun x hx => by
      have : x ∈ A ⊓ A' := ⟨hx.1.2, hx.2.2⟩
      rwa [hi] at this
    rw [h2, Subgroup.card_bot, mul_one, hA.card S hS, hA'q] at h1
    exact h1
  have hSST : S ⊔ S' ≤ T := sup_le inf_le_left inf_le_left
  have hne : U ⊓ (S ⊔ S') ≠ ⊥ := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card U (S ⊔ S')
    rw [h0, Subgroup.card_bot, mul_one, hcard] at h1
    have h2 : U.relIndex (S ⊔ S') ≤ U.relIndex T :=
      Subgroup.relIndex_le_of_le_right hSST Subgroup.index_ne_zero_of_finite
    nlinarith
  obtain ⟨⟨x, hxU, hxS⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨s, hs, s', hs', rfl⟩ := (mem_sup_iff (A := S) (A' := S')
    (fun a ha b hb => hc a ha.2 b hb.2)).mp hxS
  obtain ⟨w, hwS, hw1, w', hw', hwU⟩ : ∃ w ∈ S, w ≠ 1 ∧ ∃ w' ∈ A', w * w' ∈ U := by
    by_cases hs1 : s = 1
    · subst hs1
      rw [one_mul] at hxU hx1'
      refine ⟨t⁻¹ * s' * t, ⟨?_, ?_⟩, ?_, 1, A'.one_mem, ?_⟩
      · exact T.mul_mem (T.mul_mem (T.inv_mem ht) hs'.1) ht
      · refine (htA _).mpr ?_
        have e : t * (t⁻¹ * s' * t) * t⁻¹ = s' := by group
        rw [e]
        exact hs'.2
      · intro h
        apply hx1'
        have := congrArg (fun z => t * z * t⁻¹) h
        simpa [mul_assoc] using this
      · rw [mul_one]
        have := (mem_normalizer_iff.mp (hTU (T.inv_mem ht)) s').mp hxU
        simpa using this
    · exact ⟨s, hs, hs1, s', hs'.2, hxU⟩
  intro y hy b hb b' hb' hyb
  have hyU : y * (w * w') * y⁻¹ ∈ U := (mem_normalizer_iff.mp (hYU hy) _).mp hwU
  have e : y * (w * w') * y⁻¹ = (b * w * b⁻¹) * (b' * w' * b'⁻¹) := by
    rw [hyb]
    have h1 : b' * w = w * b' := (hc w hwS.2 b' hb').symm
    have h2 : b * w' = w' * b := hc b hb w' hw'
    calc b * b' * (w * w') * (b * b')⁻¹ = b * (b' * w) * w' * b'⁻¹ * b⁻¹ := by group
      _ = b * (w * b') * w' * b'⁻¹ * b⁻¹ := by rw [h1]
      _ = (b * w * b⁻¹) * (b * (b' * w' * b'⁻¹) * b⁻¹) := by group
      _ = (b * w * b⁻¹) * (b' * w' * b'⁻¹) := by
          rw [hc b hb _ (A'.mul_mem (A'.mul_mem hb' hw') (A'.inv_mem hb'))]
          group
  rw [e] at hyU
  have hbwA : b * w * b⁻¹ ∈ A := A.mul_mem (A.mul_mem hb hwS.2) (A.inv_mem hb)
  have hbwA' : b' * w' * b'⁻¹ ∈ A' := A'.mul_mem (A'.mul_mem hb' hw') (A'.inv_mem hb')
  have hmem := inf_sup_le hc hi hS hS' hT ⟨hUT hyU, Subgroup.mul_mem_sup hbwA hbwA'⟩
  obtain ⟨u, hu, u', hu', hu''⟩ := (mem_sup_iff (A := S) (A' := S')
    (fun a ha b hb => hc a ha.2 b hb.2)).mp hmem
  have hbw : b * w * b⁻¹ = u := (eq_of_mul_eq hi hbwA hu.2 hbwA' hu'.2 hu'').1
  have hconj := isSylowTwoOf_conj hS hb
  have hSc : S.map (MulAut.conj b).toMonoidHom = S := by
    refine hA.ti _ _ hconj hS ?_
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨b * w * b⁻¹, ⟨w, hwS, rfl⟩, hbw ▸ hu⟩, fun h => hw1 ?_⟩
    have h1 : b * w * b⁻¹ = 1 := congrArg Subtype.val h
    have := congrArg (fun z => b⁻¹ * z * b) h1
    simpa [mul_assoc] using this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hSc

theorem le_normalizer_core (hA : BorelL2 A q) (hA' : BorelL2 A' q) (hq : 4 ≤ q)
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    (hS : IsSylowTwoOf (T ⊓ A) A) (hS' : IsSylowTwoOf (T ⊓ A') A') (hT : IsPGroup 2 T)
    (ht : t ∈ T) (htA : ∀ a, a ∈ A ↔ t * a * t⁻¹ ∈ A')
    (hUT : U ≤ T) (hU8 : U.relIndex T ≤ 8) (hTU : T ≤ normalizer (U : Set Q))
    (hYA : Y ≤ A ⊔ A') (hYU : Y ≤ normalizer (U : Set Q)) (hTY : T ≤ normalizer (Y : Set Q))
    (hPY : P ≤ Y) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9) (hY3 : ∀ y ∈ Y, y ^ 3 ∈ T)
    (hDA : D ≤ normalizer (A : Set Q)) (hDA' : D ≤ normalizer (A' : Set Q))
    (hDT : D ≤ normalizer (T : Set Q)) :
    D ≤ normalizer ((Y ⊔ (T ⊓ A ⊔ T ⊓ A') : Subgroup Q) : Set Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := T ⊓ A with hSdef
  set S' := T ⊓ A' with hS'def
  set W := S ⊔ S' with hWdef
  have hc' : ∀ a ∈ A', ∀ b ∈ A, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hi' : A' ⊓ A = ⊥ := by rw [inf_comm]; exact hi
  have htA' : ∀ a, a ∈ A' ↔ t⁻¹ * a * t⁻¹⁻¹ ∈ A := by
    intro a
    rw [htA]
    simp [mul_assoc]
  have hSW : ∀ s ∈ S, ∀ s' ∈ S', s * s' ∈ W := fun s hs s' hs' => Subgroup.mul_mem_sup hs hs'
  have hWm : ∀ {w : Q}, w ∈ W ↔ ∃ s ∈ S, ∃ s' ∈ S', w = s * s' := by
    intro w
    exact mem_sup_iff (A := S) (A' := S') (fun a ha b hb => hc a ha.2 b hb.2)
  have hWT : W ≤ T := sup_le inf_le_left inf_le_left
  have hWA : W ≤ A ⊔ A' := sup_le_sup inf_le_right inf_le_right
  have hYN : ∀ y ∈ Y, y ∈ normalizer (S : Set Q) ∧ y ∈ normalizer (S' : Set Q) := by
    intro y hy
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_sup_iff hc).mp (hYA hy)
    have h1 := le_normalizer_sylow hA hq hc hi hS hS' hT (hA'.card _ hS') ht htA hUT hU8 hTU hYU
      _ hy b hb b' hb' rfl
    have h2 := le_normalizer_sylow (A := A') (A' := A) hA' hq hc' hi' hS' hS hT (hA.card _ hS)
      (T.inv_mem ht) htA' hUT hU8 hTU hYU _ hy b' hb' b hb (hc b hb b' hb')
    exact ⟨mul_mem_normalizer hc inf_le_right hb' h1,
      by rw [hc b hb b' hb']; exact mul_mem_normalizer hc' inf_le_right hb h2⟩
  have hWN : ∀ w ∈ W, w ∈ normalizer (S : Set Q) ∧ w ∈ normalizer (S' : Set Q) := by
    intro w hw
    obtain ⟨s, hs, s', hs', rfl⟩ := hWm.mp hw
    refine ⟨mul_mem_normalizer hc inf_le_right hs'.2 (Subgroup.le_normalizer hs), ?_⟩
    rw [hc s hs.2 s' hs'.2]
    exact mul_mem_normalizer hc' inf_le_right hs.2 (Subgroup.le_normalizer hs')
  let E : Q → Prop := fun z => z ∈ A ⊔ A' ∧ z ∈ normalizer (S : Set Q) ∧
    z ∈ normalizer (S' : Set Q) ∧ z ^ 3 ∈ W
  have hYW : W ≤ normalizer (Y : Set Q) := hWT.trans hTY
  have hY3W : ∀ y ∈ Y, y ^ 3 ∈ W := fun y hy =>
    inf_sup_le hc hi hS hS' hT ⟨hY3 y hy, (A ⊔ A').pow_mem (hYA hy) 3⟩
  have hYWE : ∀ z ∈ Y ⊔ W, E z := by
    intro z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hYW).mp hz
    have hyN := hYN y hy
    have hwN := hWN w hw
    refine ⟨Subgroup.mul_mem _ (hYA hy) (hWA hw), Subgroup.mul_mem _ hyN.1 hwN.1,
      Subgroup.mul_mem _ hyN.2 hwN.2, ?_⟩
    have hWy : ∀ x ∈ W, y * x * y⁻¹ ∈ W ∧ y⁻¹ * x * y ∈ W := by
      intro x hx
      obtain ⟨s, hs, s', hs', rfl⟩ := hWm.mp hx
      have h1 := (mem_normalizer_iff.mp hyN.1 s).mp hs
      have h2 := (mem_normalizer_iff.mp hyN.2 s').mp hs'
      have hyi : y⁻¹ ∈ Y := Y.inv_mem hy
      have h3 := (mem_normalizer_iff.mp (hYN _ hyi).1 s).mp hs
      have h4 := (mem_normalizer_iff.mp (hYN _ hyi).2 s').mp hs'
      refine ⟨?_, ?_⟩
      · have e : y * (s * s') * y⁻¹ = (y * s * y⁻¹) * (y * s' * y⁻¹) := by group
        rw [e]
        exact hSW _ h1 _ h2
      · have e : y⁻¹ * (s * s') * y = (y⁻¹ * s * y⁻¹⁻¹) * (y⁻¹ * s' * y⁻¹⁻¹) := by group
        rw [e]
        exact hSW _ h3 _ h4
    have e : (y * w) ^ 3 = y ^ 3 * (y⁻¹ * (y⁻¹ * w * y) * y) * (y⁻¹ * w * y) * w := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e]
    have hw1 := (hWy w hw).2
    have hw2 := (hWy _ hw1).2
    exact W.mul_mem (W.mul_mem (W.mul_mem (hY3W y hy) hw2) hw1) hw
  obtain ⟨c, hcA, hcN, hcx⟩ := hA.cube S hS
  obtain ⟨c', hcA', hcN', hcx'⟩ := hA'.cube S' hS'
  have hEc : ∀ z, E z → ∃ j < 3, ∃ k < 3, z * (c ^ j * c' ^ k)⁻¹ ∈ W := by
    rintro z ⟨hzA, hzN, hzN', hz3⟩
    obtain ⟨a, ha, a', ha', rfl⟩ := (mem_sup_iff hc).mp hzA
    have haN : a ∈ normalizer (S : Set Q) := mem_normalizer_of_mul hc inf_le_right ha' hzN
    have haN' : a' ∈ normalizer (S' : Set Q) := by
      have h1 : a' * a ∈ normalizer (S' : Set Q) := by rw [← hc a ha a' ha']; exact hzN'
      exact mem_normalizer_of_mul hc' inf_le_right ha h1
    have hz3' : a ^ 3 * a' ^ 3 ∈ W := by
      rw [← (Commute.mul_pow (hc a ha a' ha') 3)]
      exact hz3
    obtain ⟨s, hs, s', hs', hss⟩ := hWm.mp hz3'
    obtain ⟨ha3, ha3'⟩ := eq_of_mul_eq hi (A.pow_mem ha 3) hs.2 (A'.pow_mem ha' 3) hs'.2 hss
    obtain ⟨j, hj, hjS⟩ := hcx a ha haN (by rw [ha3]; exact hs)
    obtain ⟨k, hk, hkS⟩ := hcx' a' ha' haN' (by rw [ha3']; exact hs')
    refine ⟨j, hj, k, hk, ?_⟩
    have e : a * a' * (c ^ j * c' ^ k)⁻¹ = (a * (c ^ j)⁻¹) * (a' * (c' ^ k)⁻¹) := by
      have h1 : a' * (c' ^ k)⁻¹ * (c ^ j)⁻¹ = (c ^ j)⁻¹ * (a' * (c' ^ k)⁻¹) :=
        (hc _ (A.inv_mem (A.pow_mem hcA j)) _
          (A'.mul_mem ha' (A'.inv_mem (A'.pow_mem hcA' k)))).symm
      calc a * a' * (c ^ j * c' ^ k)⁻¹ = a * (a' * (c' ^ k)⁻¹ * (c ^ j)⁻¹) := by group
        _ = a * ((c ^ j)⁻¹ * (a' * (c' ^ k)⁻¹)) := by rw [h1]
        _ = (a * (c ^ j)⁻¹) * (a' * (c' ^ k)⁻¹) := by group
    rw [e]
    exact hSW _ hjS _ hkS
  have hcardE : Nat.card {z // E z} ≤ 9 * Nat.card W := by
    choose! j hj k hk hjk using hEc
    let f : {z // E z} → Fin 3 × Fin 3 × ↥W := fun z =>
      (⟨j z, hj z z.2⟩, ⟨k z, hk z z.2⟩, ⟨z * (c ^ j z * c' ^ k z)⁻¹, hjk z z.2⟩)
    have hf : Function.Injective f := by
      intro z z' h
      simp only [f, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have h4 : (z : Q) * (c ^ j z * c' ^ k z)⁻¹ = z' * (c ^ j z' * c' ^ k z')⁻¹ :=
        congrArg Subtype.val h3
      rw [h1, h2] at h4
      exact Subtype.ext (mul_right_cancel h4)
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_prod, Nat.card_fin] at h1
    linarith
  have hcardYW : 9 * Nat.card W ≤ Nat.card ↥(Y ⊔ W) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hPW : P ⊓ W = ⊥ := (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P W hP3
      (hT.to_le hWT)).eq_bot
    let f : ↥P × ↥W → ↥(Y ⊔ W) := fun x =>
      ⟨(x.1 : Q) * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left (hPY x.1.2))
        (Subgroup.mem_sup_right x.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨p, w⟩ ⟨p', w'⟩ h
      have h1 : (p : Q) * w = p' * w' := congrArg Subtype.val h
      have h2 : (p' : Q)⁻¹ * p = w' * (w : Q)⁻¹ := by
        calc (p' : Q)⁻¹ * p = (p' : Q)⁻¹ * (p * w) * (w : Q)⁻¹ := by group
          _ = (p' : Q)⁻¹ * (p' * w') * (w : Q)⁻¹ := by rw [h1]
          _ = w' * (w : Q)⁻¹ := by group
      have h3 : (p' : Q)⁻¹ * p ∈ P ⊓ W :=
        ⟨P.mul_mem (P.inv_mem p'.2) p.2, h2 ▸ W.mul_mem w'.2 (W.inv_mem w.2)⟩
      rw [hPW, Subgroup.mem_bot] at h3
      have hp : (p : Q) = p' := by
        have := congrArg ((p' : Q) * ·) h3
        simpa using this
      have hw : (w : Q) = w' := by
        rw [hp] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hp) (Subtype.ext hw)
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hP9] at h1
    exact h1
  have hconjN : ∀ {d : Q} {X₁ X₂ : Subgroup Q}, d ∈ normalizer (X₁ : Set Q) →
      d ∈ normalizer (X₂ : Set Q) → d ∈ normalizer ((X₁ ⊔ X₂ : Subgroup Q) : Set Q) := by
    intro d X₁ X₂ h1 h2
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hconjI : ∀ {d : Q} {X₁ X₂ : Subgroup Q}, d ∈ normalizer (X₁ : Set Q) →
      d ∈ normalizer (X₂ : Set Q) → d ∈ normalizer ((X₁ ⊓ X₂ : Subgroup Q) : Set Q) := by
    intro d X₁ X₂ h1 h2
    rw [mem_normalizer_iff] at h1 h2 ⊢
    intro x
    exact and_congr (h1 x) (h2 x)
  have hDE : ∀ d ∈ D, ∀ z, E z → E (d * z * d⁻¹) := by
    rintro d hd z ⟨hzA, hzN, hzN', hz3⟩
    have hdS : d ∈ normalizer (S : Set Q) := hconjI (hDT hd) (hDA hd)
    have hdS' : d ∈ normalizer (S' : Set Q) := hconjI (hDT hd) (hDA' hd)
    have hdAA := hconjN (hDA hd) (hDA' hd)
    have hdW : d ∈ normalizer (W : Set Q) := hconjN hdS hdS'
    refine ⟨(mem_normalizer_iff.mp hdAA z).mp hzA,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hdS hzN) (Subgroup.inv_mem _ hdS),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hdS' hzN') (Subgroup.inv_mem _ hdS'), ?_⟩
    rw [conj_pow]
    exact (mem_normalizer_iff.mp hdW _).mp hz3
  have hmain : ∀ d ∈ D, ∀ z ∈ Y ⊔ W, d * z * d⁻¹ ∈ Y ⊔ W := by
    intro d hd z hz
    have hE : E (d * z * d⁻¹) := hDE d hd z (hYWE z hz)
    by_contra hnot
    let g : Option ↥(Y ⊔ W) → {z // E z} := fun o => match o with
      | none => ⟨d * z * d⁻¹, hE⟩
      | some w => ⟨w, hYWE w w.2⟩
    have hg : Function.Injective g := by
      rintro (_ | w) (_ | w') h
      · rfl
      · exfalso
        have h2 : d * z * d⁻¹ = (w' : Q) := congrArg Subtype.val h
        exact hnot (h2 ▸ w'.2)
      · exfalso
        have h2 : (w : Q) = d * z * d⁻¹ := congrArg Subtype.val h
        exact hnot (h2 ▸ w.2)
      · have h2 : (w : Q) = w' := congrArg (fun x : {z // E z} => (x : Q)) h
        exact congrArg some (Subtype.ext h2)
    have h1 := Nat.card_le_card_of_injective g hg
    rw [Finite.card_option] at h1
    omega
  intro d hd
  rw [mem_normalizer_iff]
  intro z
  refine ⟨hmain d hd z, fun h => ?_⟩
  have := hmain d⁻¹ (D.inv_mem hd) _ h
  simpa [mul_assoc] using this

end Core

end CFSG.Quasithin.H13.BenC
