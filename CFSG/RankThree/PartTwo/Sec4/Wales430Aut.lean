module

public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Proof430

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_fix_of_fix {A D : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) (hDA : D ≤ A) (hD9 : Nat.card D = 9) {y : G} (hyA : y ∈ A)
    (hyD : y ∉ D) {τ : MulAut A} (hτD : ∀ z : A, (z : G) ∈ D → τ z = z)
    (hτy : τ ⟨y, hyA⟩ = ⟨y, hyA⟩) : τ = 1 := by
  have hAy : A = Subgroup.zpowers y ⊔ D :=
    (Sec12.eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hyA) hDA) le_sup_right hD9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hyD).symm
  have hτ : τ ∈ Sec13.transvAxis A D :=
    Sec13.mem_transvAxis_of hA hyA hAy hτD (by rw [hτy, mul_inv_cancel]; exact D.one_mem)
  exact Sec13.transvAxis_ext hA hyA hAy hτ (Sec13.transvAxis A D).one_mem
    (by rw [hτy, MulAut.one_apply])

theorem sq_eq_one_or_pow_three_eq_one_of_fix {A D : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hDA : D ≤ A)
    (hD9 : Nat.card D = 9) {σ : MulAut A} (hσD : ∀ z : A, (z : G) ∈ D → σ z = z) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  have hcommA : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
  obtain ⟨y, hyA, hyD⟩ : ∃ y ∈ A, y ∉ D := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ≤ D from hcon)
    omega
  have hAy : A = Subgroup.zpowers y ⊔ D :=
    (Sec12.eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hyA) hDA) le_sup_right hD9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hyD).symm
  set y' : A := ⟨y, hyA⟩ with hy'
  obtain ⟨i, hi3, d, hdD, hσy⟩ := Sec13.exists_pow_mul_of_mem hA hyA hAy (σ y').2
  have hdA : d ∈ A := hDA hdD
  set d' : A := ⟨d, hdA⟩ with hd'
  have hσy' : σ y' = y' ^ i * d' := Subtype.ext (by simp [hσy, y', d'])
  have hσd : σ d' = d' := hσD d' hdD
  have hd3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 d hdA)
  have hy3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 y hyA)
  interval_cases i
  ·
    exfalso
    apply hyD
    have h1 : σ y' = σ d' := by rw [hσy', pow_zero, one_mul, hσd]
    have h2 : y' = d' := σ.injective h1
    have h3 : y = d := congrArg Subtype.val h2
    rw [h3]
    exact hdD
  ·
    right
    refine Sec13.transvAxis_pow_three hA (Sec13.mem_transvAxis_of hA hyA hAy hσD ?_)
    have e : ((σ y' : A) : G) * y⁻¹ = d := by
      rw [hσy', pow_one, hcommA y' d']
      simp [y', d']
    rw [e]
    exact hdD
  ·
    left
    refine eq_one_of_fix_of_fix hA h27 hDA hD9 hyA hyD (fun z hz => ?_) ?_
    · rw [pow_two, MulAut.mul_apply, hσD z hz, hσD z hz]
    · have h1 : (y' ^ 2 * d') ^ 2 * d' = y' := by
        rw [Commute.mul_pow (hcommA _ _) 2, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add,
          hy3, one_mul, pow_one, mul_assoc, ← pow_succ, hd3, mul_one]
      rw [pow_two, MulAut.mul_apply, hσy', map_mul, map_pow, hσy', hσd, h1]

theorem sq_eq_one_or_pow_three_eq_one_core {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A)
    (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hca : c ∉ Subgroup.zpowers a) {B : Subgroup G}
    (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hcB : c ∉ B) {σ : MulAut A}
    (hσa : σ ⟨a, haA⟩ = ⟨a, haA⟩) (hσc : ((σ ⟨c, hcA⟩ : A) : G) ∈ Subgroup.zpowers c)
    (hσB : ∀ z : A, (z : G) ∈ B → ((σ z : A) : G) ∈ B)
    (hmemB : a ∈ B → ∃ x : A, (x : G) ∈ B ∧ (x : G) ∉ Subgroup.zpowers a ∧ (σ ^ 2) x = x) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcommA : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  set c' : A := ⟨c, hcA⟩ with hc'
  set a' : A := ⟨a, haA⟩ with ha'
  set D := Subgroup.zpowers c ⊔ Subgroup.zpowers a with hD
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr haA)
  have hcommD : ∀ u ∈ Subgroup.zpowers c, ∀ v ∈ Subgroup.zpowers a, u * v = v * u :=
    fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr hcA hu) v (Subgroup.zpowers_le.mpr haA hv)
  have hD9 : Nat.card D = 9 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommD
    rw [Sec13.zpowers_inf_eq_bot hc3 hca, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hc3 hc1, Sec13.card_zpowers_of_pow_three ha3 ha1] at hcard
    exact hcard
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from hcomm _ (hDA u.2) _ (hDA v.2))⟩⟩,
      fun u hu => hA.2 u (hDA hu)⟩
  have hone : ∀ x : A, x ^ 2 = 1 → x ^ 3 = 1 → x = 1 := fun x h2 h3 => by
    have e : x = x ^ 3 * (x ^ 2)⁻¹ := by group
    rw [e, h3, h2, inv_one, one_mul]
  have hσc' : σ c' = c' ∨ σ c' = c'⁻¹ := by
    rcases Sec12.Proof128.eq_one_or_eq_or_eq_inv_of_mem_zpowers hc3 hσc with h | h | h
    · exfalso
      have h1 : σ c' = 1 := Subtype.ext h
      rw [map_eq_one_iff _ σ.injective] at h1
      exact hc1 (congrArg Subtype.val h1)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hmeet : ∀ X Y : Subgroup G, X ≤ A → Nat.card X = 9 → Y ≤ A → Nat.card Y = 9 →
      ∀ x ∈ Y, x ∉ X → Nat.card (X ⊓ Y : Subgroup G) = 3 := by
    intro X Y hXA hX9 hYA hY9 x hxY hxX
    have hXY : X ⊔ Y = A := Sec12.eq_of_card_nine_lt h27 (sup_le hXA hYA) le_sup_left hX9
      (Subgroup.mem_sup_right hxY) hxX
    have hc : ∀ u ∈ X, ∀ v ∈ Y, u * v = v * u := fun u hu v hv => hcomm u (hXA hu) v (hYA hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
    rw [hXY, h27, hX9, hY9] at hcard
    omega
  have hline : ∀ X : Subgroup G, Nat.card X = 3 → ∀ x ∈ X, x ≠ 1 →
      X = Subgroup.zpowers x := by
    intro X hX3 x hxX hx1
    have : Fact (Nat.card X).Prime := ⟨hX3 ▸ Nat.prime_three⟩
    refine (le_antisymm (Subgroup.zpowers_le.mpr hxX) ?_).symm
    rcases ((Subgroup.zpowers x).subgroupOf X).eq_bot_or_eq_top_of_prime_card with h | h
    · exfalso
      apply hx1
      have hmem : (⟨x, hxX⟩ : X) ∈ (Subgroup.zpowers x).subgroupOf X :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x)
      rw [h] at hmem
      exact congrArg Subtype.val ((Subgroup.mem_bot).mp hmem)
    · intro y hy
      have hmem : (⟨y, hy⟩ : X) ∈ (Subgroup.zpowers x).subgroupOf X := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
  have hexists : ∀ X : Subgroup G, Nat.card X = 3 → ∃ x ∈ X, x ≠ 1 := by
    intro X hX3
    by_contra hcon
    push Not at hcon
    have hX : X = ⊥ := (Subgroup.eq_bot_iff_forall X).mpr hcon
    rw [hX, Subgroup.card_bot] at hX3
    omega
  have hfixD : ∀ τ : MulAut A, τ a' = a' → τ c' = c' → ∀ z : A, (z : G) ∈ D → τ z = z := by
    intro τ hτa hτc z hz
    obtain ⟨i, -, b, hb, hzb⟩ := Sec13.exists_pow_mul_of_mem hDe
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) rfl hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hz' : z = c' ^ i * a' ^ j := Subtype.ext (by simp [hzb, c', a'])
    rw [hz', map_mul, map_pow, map_zpow, hτc, hτa]
  have hσ2a : (σ ^ 2) a' = a' := by rw [pow_two, MulAut.mul_apply, hσa, hσa]
  have hσ2c : (σ ^ 2) c' = c' := by
    rw [pow_two, MulAut.mul_apply]
    rcases hσc' with h | h
    · rw [h, h]
    · rw [h, map_inv, h, inv_inv]
  have hBD3 : Nat.card (B ⊓ D : Subgroup G) = 3 :=
    hmeet B D hBA hB9 hDA hD9 c (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) hcB
  by_cases haB : a ∈ B
  ·
    left
    have hBDa : B ⊓ D = Subgroup.zpowers a :=
      hline _ hBD3 a ⟨haB, Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩ ha1
    obtain ⟨x, hxB, hxa, hσ2x⟩ := hmemB haB
    have hxD : (x : G) ∉ D := fun hxD => hxa (hBDa ▸ (show (x : G) ∈ B ⊓ D from ⟨hxB, hxD⟩))
    exact eq_one_of_fix_of_fix hA h27 hDA hD9 x.2 hxD (hfixD _ hσ2a hσ2c) hσ2x
  ·
    obtain ⟨d, hdBD, hd1⟩ := hexists _ hBD3
    have hdB : d ∈ B := hdBD.1
    have hdD : d ∈ D := hdBD.2
    have hdA : d ∈ A := hDA hdD
    have hBDd : B ⊓ D = Subgroup.zpowers d := hline _ hBD3 d hdBD hd1
    have hd3 : d ^ 3 = 1 := hA.2 d hdA
    obtain ⟨i, hi3, b, hb, hdb⟩ := Sec13.exists_pow_mul_of_mem hDe
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) rfl hdD
    have hbA : b ∈ A := Subgroup.zpowers_le.mpr haA hb
    set b' : A := ⟨b, hbA⟩ with hb'
    set d' : A := ⟨d, hdA⟩ with hd'
    have hd'eq : d' = c' ^ i * b' := Subtype.ext (by simp [hdb, c', b', d'])
    have hσb : σ b' = b' := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
      have e : b' = a' ^ j := Subtype.ext (by simp [a', b', hj])
      rw [e, map_zpow, hσa]
    have hb3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 b hbA)
    have hc3' : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    have hb1 : b' ≠ 1 := by
      intro h1
      apply hcB
      have hdi : d = c ^ i := by
        have e := congrArg Subtype.val hd'eq
        rw [h1, mul_one] at e
        simpa [c', d'] using e
      interval_cases i
      · exact absurd (by simpa using hdi) hd1
      · rw [hdi, pow_one] at hdB
        exact hdB
      · have e : c = (c ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
        rw [e, ← hdi]
        exact B.pow_mem hdB 2
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply haB
      have hdb' : d = b := by simpa using hdb
      have hda : d ∈ Subgroup.zpowers a := hdb' ▸ hb
      have e : Subgroup.zpowers a = Subgroup.zpowers d :=
        hline _ (Sec13.card_zpowers_of_pow_three ha3 ha1) d hda hd1
      have haz : a ∈ Subgroup.zpowers d := e ▸ Subgroup.mem_zpowers a
      exact Subgroup.zpowers_le.mpr hdB haz
    have hσd : ((σ d' : A) : G) ∈ Subgroup.zpowers d := by
      rw [← hBDd]
      refine ⟨hσB d' hdB, ?_⟩
      rw [hd'eq, map_mul, map_pow, hσb]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      exact D.mul_mem (D.pow_mem (Subgroup.mem_sup_left hσc) i) (Subgroup.mem_sup_right hb)
    have hσc'' : σ c' = c' := by
      rcases hσc' with h | h
      · exact h
      · exfalso
        have hσd' : σ d' = (c' ^ i)⁻¹ * b' := by
          rw [hd'eq, map_mul, map_pow, h, hσb, inv_pow]
        rcases Sec12.Proof128.eq_one_or_eq_or_eq_inv_of_mem_zpowers hd3 hσd with h1 | h1 | h1
        · have h2 : σ d' = 1 := Subtype.ext h1
          rw [map_eq_one_iff _ σ.injective] at h2
          exact hd1 (congrArg Subtype.val h2)
        ·
          have h2 : σ d' = d' := Subtype.ext h1
          rw [hσd', hd'eq] at h2
          have h3 : (c' ^ i)⁻¹ = c' ^ i := mul_right_cancel h2
          have h4 : c' ^ i * c' ^ i = 1 := by
            nth_rewrite 2 [← h3]
            exact mul_inv_cancel _
          apply hc1
          have hc1' : c' = 1 := by
            interval_cases i
            · exact absurd rfl hi0
            · exact hone c' (by rw [pow_two]; simpa using h4) hc3'
            · have h5 : c' ^ 4 = 1 := by rw [show 4 = 2 + 2 by norm_num, pow_add, h4]
              have e : c' = c' ^ 4 * (c' ^ 3)⁻¹ := by group
              rw [e, h5, hc3', inv_one, one_mul]
          exact congrArg Subtype.val hc1'
        ·
          have h2 : σ d' = d'⁻¹ := Subtype.ext h1
          rw [hσd', hd'eq, mul_inv_rev, hcommA b'⁻¹ (c' ^ i)⁻¹] at h2
          have h3 : b' = b'⁻¹ := mul_left_cancel h2
          have h4 : b' ^ 2 = 1 := by
            rw [pow_two]
            nth_rewrite 2 [h3]
            exact mul_inv_cancel _
          exact hb1 (hone b' h4 hb3)
    exact sq_eq_one_or_pow_three_eq_one_of_fix hA h27 hDA hD9 (hfixD σ hσa hσc'')

theorem sq_eq_one_or_pow_three_eq_one_of_le {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A)
    (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hca : c ∉ Subgroup.zpowers a) {B L : Subgroup G}
    (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hcB : c ∉ B) (haL : a ∉ L) {σ : MulAut A}
    (hσa : σ ⟨a, haA⟩ = ⟨a, haA⟩) (hσc : ((σ ⟨c, hcA⟩ : A) : G) ∈ Subgroup.zpowers c)
    (hσB : ∀ z : A, (z : G) ∈ B → ((σ z : A) : G) ∈ B)
    (hσL : ∀ z : A, ((σ z : A) : G) * (z : G)⁻¹ ∈ L) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  refine sq_eq_one_or_pow_three_eq_one_core hA h27 haA hcA ha1 hc1 hca hBA hB9 hcB hσa hσc hσB ?_
  intro haB
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcommA : ∀ y z : A, y * z = z * y := fun y z => hA.1.is_comm.comm y z
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  obtain ⟨x, hxB, hxa⟩ : ∃ x ∈ B, x ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers a from hcon)
    rw [Sec13.card_zpowers_of_pow_three ha3 ha1] at this
    omega
  have hxA : x ∈ A := hBA hxB
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hx1 : x ≠ 1 := fun h => hxa (h ▸ Subgroup.one_mem _)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from hcomm _ (hBA u.2) _ (hBA v.2))⟩⟩,
      fun u hu => hA.2 u (hBA hu)⟩
  have hxaB : Subgroup.zpowers x ⊔ Subgroup.zpowers a ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr haB)
  have hcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers a : Subgroup G) = 9 := by
    have hc : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers a, u * v = v * u :=
      fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr hxA hu) v (Subgroup.zpowers_le.mpr haA hv)
    obtain ⟨h, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
    rw [Sec13.zpowers_inf_eq_bot hx3 hxa, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hx3 hx1, Sec13.card_zpowers_of_pow_three ha3 ha1] at h
    exact h
  have hBxa : B = Subgroup.zpowers x ⊔ Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge hxaB (by rw [hB9, hcard])).symm
  set x' : A := ⟨x, hxA⟩ with hx'
  obtain ⟨k, hk3, b, hb, hσx⟩ := Sec13.exists_pow_mul_of_mem hBe hxB hBxa (hσB x' hxB)
  have hbA : b ∈ A := Subgroup.zpowers_le.mpr haA hb
  set b' : A := ⟨b, hbA⟩ with hb'
  have hσx' : σ x' = x' ^ k * b' := Subtype.ext (by simp [hσx, x', b'])
  have hσb : σ b' = b' := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    have e : b' = ⟨a, haA⟩ ^ j := Subtype.ext (by simp [b', hj])
    rw [e, map_zpow, hσa]
  have hb3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 b hbA)
  have hx3' : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  refine ⟨x', hxB, hxa, ?_⟩
  interval_cases k
  · exfalso
    apply hxa
    have h1 : σ x' = σ b' := by rw [hσx', pow_zero, one_mul, hσb]
    have h2 : x' = b' := σ.injective h1
    have h3 : x = b := congrArg Subtype.val h2
    rw [h3]
    exact hb
  ·
    have hbL : b ∈ L := by
      have h := hσL x'
      rw [hσx', pow_one] at h
      have e : ((x' * b' : A) : G) * (x' : G)⁻¹ = b := by
        rw [hcommA x' b']
        simp [x', b']
      rwa [e] at h
    have hb1 : b = 1 := by
      have hmem : b ∈ Subgroup.zpowers a ⊓ L := ⟨hb, hbL⟩
      rw [Sec13.zpowers_inf_eq_bot ha3 haL] at hmem
      exact (Subgroup.mem_bot).mp hmem
    have hb1' : b' = 1 := Subtype.ext hb1
    have hσx1 : σ x' = x' := by rw [hσx', pow_one, hb1', mul_one]
    rw [pow_two, MulAut.mul_apply, hσx1, hσx1]
  · have h1 : (x' ^ 2 * b') ^ 2 * b' = x' := by
      rw [Commute.mul_pow (hcommA _ _) 2, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add,
        hx3', one_mul, pow_one, mul_assoc, ← pow_succ, hb3, mul_one]
    rw [pow_two, MulAut.mul_apply, hσx', map_mul, map_pow, hσx', hσb, h1]

theorem false_of_autIn_dihedral {A L B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a c : G} (haA : a ∈ A) (hcA : c ∈ A) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
    (hca : c ∉ Subgroup.zpowers a) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLa : L ≤ Subgroup.centralizer ({a} : Set G))
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hWB : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hcB : c ∉ B) (haL : a ∉ L) (e : autIn L A ≃* DihedralGroup 6) :
    False := by
  set σ : MulAut A := (e.symm (DihedralGroup.r 1) : MulAut A) with hσdef
  obtain ⟨g, hgN, hgL, hgσ⟩ := mem_autIn_iff.mp (e.symm (DihedralGroup.r 1)).2
  have happ : ∀ x : A, ((σ x : A) : G) = g * x * g⁻¹ := fun x => by
    rw [hσdef, ← hgσ, normalizerMonoidHom_apply_coe]
  have hσa : σ ⟨a, haA⟩ = ⟨a, haA⟩ := by
    apply Subtype.ext
    rw [happ]
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp (hLa hgL)
    rw [hga, mul_inv_cancel_right]
  have hσc : ((σ ⟨c, hcA⟩ : A) : G) ∈ Subgroup.zpowers c := by
    rw [happ]
    exact (Subgroup.mem_normalizer_iff.mp (hW hgN) c).mp (Subgroup.mem_zpowers c)
  have hσB : ∀ z : A, (z : G) ∈ B → ((σ z : A) : G) ∈ B := fun z hz => by
    rw [happ]
    exact (Subgroup.mem_normalizer_iff.mp (hWB hgN) z).mp hz
  have hσL : ∀ z : A, ((σ z : A) : G) * (z : G)⁻¹ ∈ L := fun z => by
    rw [happ]
    have hz : (z : G) * g⁻¹ * (z : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL z.2) g⁻¹).mp (L.inv_mem hgL)
    have e' : g * (z : G) * g⁻¹ * (z : G)⁻¹ = g * ((z : G) * g⁻¹ * (z : G)⁻¹) := by group
    rw [e']
    exact L.mul_mem hgL hz
  have hor := sq_eq_one_or_pow_three_eq_one_of_le hA h27 haA hcA ha1 hc1 hca hBA hB9 hcB haL
    hσa hσc hσB hσL
  have hk : ∀ k : ℕ, σ ^ k = 1 → (DihedralGroup.r 1 : DihedralGroup 6) ^ k = 1 := by
    intro k hk
    have h1 : (e.symm (DihedralGroup.r 1)) ^ k = 1 := Subtype.ext (by simpa [hσdef] using hk)
    have h2 := congrArg e h1
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
  rcases hor with h | h
  · have := hk 2 h
    rw [DihedralGroup.r_one_pow] at this
    exact absurd this (by decide)
  · have := hk 3 h
    rw [DihedralGroup.r_one_pow] at this
    exact absurd this (by decide)

end CFSG.RankThree.PartTwo.Sec4.Proof430
