module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

@[expose] def CenterOrderTwo (P : Type*) [Group P] : Prop :=
  ∃ w : P, w ≠ 1 ∧ (∀ y : P, w * y = y * w) ∧ ∀ x : P, (∀ y : P, x * y = y * x) → x = 1 ∨ x = w

@[expose] def UniqueCentralInvolution (P : Type*) [Group P] : Prop :=
  ∃ w : P, w ≠ 1 ∧ w ^ 2 = 1 ∧ (∀ y : P, w * y = y * w) ∧
    ∀ x : P, (∀ y : P, x * y = y * x) → x ^ 2 = 1 → x = 1 ∨ x = w

theorem CenterOrderTwo.sq_eq_one {P : Type*} [Group P] {w : P} (hw1 : w ≠ 1)
    (hwc : ∀ y : P, w * y = y * w) (hu : ∀ x : P, (∀ y : P, x * y = y * x) → x = 1 ∨ x = w) :
    w ^ 2 = 1 := by
  have hc : ∀ y : P, w ^ 2 * y = y * w ^ 2 := by
    intro y
    rw [pow_two, mul_assoc, hwc y, ← mul_assoc, hwc y, mul_assoc]
  rcases hu (w ^ 2) hc with h | h
  · exact h
  · exfalso
    apply hw1
    have : w * w = w * 1 := by rw [mul_one, ← pow_two, h]
    exact mul_left_cancel this

theorem CenterOrderTwo.uci {P : Type*} [Group P] (h : CenterOrderTwo P) :
    UniqueCentralInvolution P := by
  obtain ⟨w, hw1, hwc, hu⟩ := h
  exact ⟨w, hw1, CenterOrderTwo.sq_eq_one hw1 hwc hu, hwc, fun x hx _ => hu x hx⟩

theorem CenterOrderTwo.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : CenterOrderTwo P) : CenterOrderTwo Q := by
  obtain ⟨w, hw1, hwc, hu⟩ := h
  refine ⟨e w, fun h1 => hw1 (e.injective (by simpa using h1)), fun y => ?_, fun x hx => ?_⟩
  · have := hwc (e.symm y)
    have h2 := congrArg e this
    simpa using h2
  · have hx' : ∀ y : P, e.symm x * y = y * e.symm x := by
      intro y
      have := hx (e y)
      have h2 := congrArg e.symm this
      simpa using h2
    rcases hu _ hx' with h | h
    · left
      have := congrArg e h
      simpa using this
    · right
      have := congrArg e h
      simpa using this

theorem UniqueCentralInvolution.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : UniqueCentralInvolution P) : UniqueCentralInvolution Q := by
  obtain ⟨w, hw1, hw2, hwc, hu⟩ := h
  refine ⟨e w, fun h1 => hw1 (e.injective (by simpa using h1)), by rw [← map_pow, hw2, map_one],
    fun y => ?_, fun x hx hx2 => ?_⟩
  · have := hwc (e.symm y)
    have h2 := congrArg e this
    simpa using h2
  · have hx' : ∀ y : P, e.symm x * y = y * e.symm x := by
      intro y
      have := hx (e y)
      have h2 := congrArg e.symm this
      simpa using h2
    have hx2' : e.symm x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    rcases hu _ hx' hx2' with h | h
    · left
      have := congrArg e h
      simpa using this
    · right
      have := congrArg e h
      simpa using this

theorem centerOrderTwo_quaternion : CenterOrderTwo (QuaternionGroup 2) :=
  ⟨QuaternionGroup.a 2, by decide, by decide, by decide⟩

theorem centerOrderTwo_of_card_center_two {P : Type*} [Group P]
    (h : Nat.card (Subgroup.center P) = 2) : CenterOrderTwo P := by
  obtain ⟨w, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center P)).mp h
  obtain ⟨hw1, hwu⟩ := hw
  refine ⟨(w : P), fun h1 => hw1 (Subtype.ext h1), fun y => ?_, fun x hx => ?_⟩
  · exact (Subgroup.mem_center_iff.mp w.2 y).symm
  · by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have hxc : x ∈ Subgroup.center P := Subgroup.mem_center_iff.mpr fun y => (hx y).symm
      have := hwu ⟨x, hxc⟩ (fun h1 => hx1 (congrArg Subtype.val h1))
      have h2 := congrArg Subtype.val this
      exact h2

section Commuting

variable {P : Type*} [Group P] {A B : Subgroup P}

theorem mem_sup_of_commute (h : A ≤ Subgroup.centralizer (B : Set P)) {x : P} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm
  let S : Subgroup P :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have : b * a' = a' * b := (hcomm a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
          have := hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
          exact this.symm
        rw [mul_inv_rev, this] }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩) (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem card_sup_mul_card_inf_of_le_centralizer (h : A ≤ Subgroup.centralizer (B : Set P)) [Finite P] :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (Subgroup.mem_centralizer_iff.mp (h a.2) b b.2).symm
  let φ : A × B →* P := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : P), x.1.1.2, ?_⟩
        invFun := fun u => ⟨(⟨u.1, u.2.1⟩, ⟨u.1⁻¹, B.inv_mem u.2.2⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have h1 : (x.1.1 : P) * (x.1.2 : P) = 1 := hx
      have h2 : (x.1.1 : P) = (x.1.2 : P)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact B.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker]
      show u.1 * u.1⁻¹ = 1
      simp
    · rintro ⟨⟨a, b⟩, hx⟩
      rw [MonoidHom.mem_ker] at hx
      have h1 : (a : P) * (b : P) = 1 := hx
      have h2 : (a : P) = (b : P)⁻¹ := eq_inv_of_mul_eq_one_left h1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        show (a : P)⁻¹ = b
        rw [h2]; simp
    · intro u
      rfl
  have h1 : Nat.card (A × B) = Nat.card φ.range * Nat.card φ.ker := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have e2 : Nat.card ((A × B) ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [e2] at e1
    exact e1
  rw [Nat.card_prod] at h1
  rw [hrange, hker] at h1
  exact h1.symm

theorem central_factor_right (h : A ≤ Subgroup.centralizer (B : Set P)) {a b : P} (ha : a ∈ A)
    (hx : ∀ y : P, a * b * y = y * (a * b)) : ∀ b' ∈ B, b * b' = b' * b := by
  intro b' hb'
  have hcomm : b' * a = a * b' := (Subgroup.mem_centralizer_iff.mp (h ha) b' hb')
  have h1 := hx b'
  have h2 : a * (b * b') = a * (b' * b) := by
    calc a * (b * b') = a * b * b' := by group
      _ = b' * (a * b) := h1
      _ = (b' * a) * b := by group
      _ = (a * b') * b := by rw [hcomm]
      _ = a * (b' * b) := by group
  exact mul_left_cancel h2

theorem central_factor_left (h : A ≤ Subgroup.centralizer (B : Set P)) {a b : P} (hb : b ∈ B)
    (hx : ∀ y : P, a * b * y = y * (a * b)) : ∀ a' ∈ A, a * a' = a' * a := by
  intro a' ha'
  have hcomm : b * a' = a' * b := Subgroup.mem_centralizer_iff.mp (h ha') b hb
  have h1 := hx a'
  have h2 : (a * a') * b = (a' * a) * b := by
    calc (a * a') * b = a * (a' * b) := by group
      _ = a * (b * a') := by rw [hcomm]
      _ = a * b * a' := by group
      _ = a' * (a * b) := h1
      _ = (a' * a) * b := by group
  exact mul_right_cancel h2

theorem central_of_commutes (h : A ≤ Subgroup.centralizer (B : Set P)) (hgen : A ⊔ B = ⊤) {w : P}
    (hA : ∀ a ∈ A, w * a = a * w) (hB : ∀ b ∈ B, w * b = b * w) : ∀ y : P, w * y = y * w := by
  intro y
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h (hgen ▸ Subgroup.mem_top y)
  calc w * (a * b) = (w * a) * b := by group
    _ = (a * w) * b := by rw [hA a ha]
    _ = a * (w * b) := by group
    _ = a * (b * w) := by rw [hB b hb]
    _ = a * b * w := by group

theorem inf_central (h : A ≤ Subgroup.centralizer (B : Set P)) {u : P} (hu : u ∈ A ⊓ B) :
    (∀ a ∈ A, u * a = a * u) ∧ (∀ b ∈ B, u * b = b * u) := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hBA : B ≤ Subgroup.centralizer (A : Set P) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (h ha) y hy).symm
    exact (Subgroup.mem_centralizer_iff.mp (hBA hu.2) a ha).symm
  · have := Subgroup.mem_centralizer_iff.mp (h hu.1) b hb
    exact this.symm

theorem exists_ne_one_of_card_two {X : Subgroup P} (h : Nat.card X = 2) : ∃ u ∈ X, u ≠ 1 := by
  obtain ⟨w, hw⟩ := (Nat.card_eq_two_iff' (1 : X)).mp h
  exact ⟨w, w.2, fun h1 => hw.1 (Subtype.ext h1)⟩

theorem centerOrderTwo_of_commuting_two (h : A ≤ Subgroup.centralizer (B : Set P))
    (hgen : A ⊔ B = ⊤) (hA : CenterOrderTwo ↥A) (hB : CenterOrderTwo ↥B)
    (hAB : Nat.card ↥(A ⊓ B) = 2) : CenterOrderTwo P := by
  obtain ⟨wa, hwa1, hwac, hwau⟩ := hA
  obtain ⟨wb, hwb1, hwbc, hwbu⟩ := hB
  have hwa2 : (wa : ↥A) ^ 2 = 1 := CenterOrderTwo.sq_eq_one hwa1 hwac hwau
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hAB
  obtain ⟨huA, huB⟩ := inf_central h hu
  have hua : u = (wa : P) := by
    have hc : ∀ y : A, (⟨u, hu.1⟩ : A) * y = y * ⟨u, hu.1⟩ := fun y =>
      Subtype.ext (huA y y.2)
    rcases hwau _ hc with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hu1
    · exact congrArg Subtype.val h1
  have hub : u = (wb : P) := by
    have hc : ∀ y : B, (⟨u, hu.2⟩ : B) * y = y * ⟨u, hu.2⟩ := fun y =>
      Subtype.ext (huB y y.2)
    rcases hwbu _ hc with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hu1
    · exact congrArg Subtype.val h1
  refine ⟨u, hu1, central_of_commutes h hgen huA huB, fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h (hgen ▸ Subgroup.mem_top x)
  have hca := central_factor_left h hb hx
  have hcb := central_factor_right h ha hx
  have ha' : (⟨a, ha⟩ : A) = 1 ∨ (⟨a, ha⟩ : A) = wa :=
    hwau _ (fun y => Subtype.ext (hca y y.2))
  have hb' : (⟨b, hb⟩ : B) = 1 ∨ (⟨b, hb⟩ : B) = wb :=
    hwbu _ (fun y => Subtype.ext (hcb y y.2))
  have hu2 : u * u = 1 := by
    have := congrArg Subtype.val hwa2
    rw [pow_two] at this
    simpa [hua] using this
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
  · left
    have e1 : a = 1 := congrArg Subtype.val h1
    have e2 : b = 1 := congrArg Subtype.val h2
    simp [e1, e2]
  · right
    have e1 : a = 1 := congrArg Subtype.val h1
    have e2 : b = u := (congrArg Subtype.val h2).trans hub.symm
    simp [e1, e2]
  · right
    have e1 : a = u := (congrArg Subtype.val h1).trans hua.symm
    have e2 : b = 1 := congrArg Subtype.val h2
    simp [e1, e2]
  · left
    have e1 : a = u := (congrArg Subtype.val h1).trans hua.symm
    have e2 : b = u := (congrArg Subtype.val h2).trans hub.symm
    rw [e1, e2, hu2]

theorem cyclic_four_involution {A : Type*} [Group A] (hc : IsCyclic A) (h4 : Nat.card A = 4)
    {x y : A} (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) (hy1 : y ≠ 1) (hy2 : y ^ 2 = 1) : x = y := by
  have e : Multiplicative (ZMod 4) ≃* A := by
    have := zmodCyclicMulEquiv hc
    rw [h4] at this
    exact this
  have key : ∀ z : Multiplicative (ZMod 4), z ^ 2 = 1 → z = 1 ∨ z = Multiplicative.ofAdd 2 := by
    decide
  have hx := key (e.symm x) (by rw [← map_pow, hx2, map_one])
  have hy := key (e.symm y) (by rw [← map_pow, hy2, map_one])
  rcases hx with hx | hx
  · exact absurd (by simpa using hx) hx1
  · rcases hy with hy | hy
    · exact absurd (by simpa using hy) hy1
    · exact e.symm.injective (hx.trans hy.symm)

theorem uci_of_cyclic_commuting (h : A ≤ Subgroup.centralizer (B : Set P)) (hgen : A ⊔ B = ⊤)
    (hAc : IsCyclic ↥A) (hA4 : Nat.card ↥A = 4) (hB : CenterOrderTwo ↥B)
    (hAB : Nat.card ↥(A ⊓ B) = 2) : UniqueCentralInvolution P := by
  obtain ⟨wb, hwb1, hwbc, hwbu⟩ := hB
  have hwb2 : (wb : ↥B) ^ 2 = 1 := CenterOrderTwo.sq_eq_one hwb1 hwbc hwbu
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hAB
  obtain ⟨huA, huB⟩ := inf_central h hu
  have hub : u = (wb : P) := by
    have hc : ∀ y : B, (⟨u, hu.2⟩ : B) * y = y * ⟨u, hu.2⟩ := fun y =>
      Subtype.ext (huB y y.2)
    rcases hwbu _ hc with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hu1
    · exact congrArg Subtype.val h1
  have hu2 : u ^ 2 = 1 := by
    have := congrArg Subtype.val hwb2
    rw [hub]
    simpa using this
  refine ⟨u, hu1, hu2, central_of_commutes h hgen huA huB, fun x hx hx2 => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h (hgen ▸ Subgroup.mem_top x)
  have hcb := central_factor_right h ha hx
  have hb' : (⟨b, hb⟩ : B) = 1 ∨ (⟨b, hb⟩ : B) = wb :=
    hwbu _ (fun y => Subtype.ext (hcb y y.2))
  have hbA : b ∈ A := by
    rcases hb' with h1 | h1
    · have : b = 1 := congrArg Subtype.val h1
      rw [this]; exact A.one_mem
    · have : b = u := (congrArg Subtype.val h1).trans hub.symm
      rw [this]; exact hu.1
  have hxA : a * b ∈ A := A.mul_mem ha hbA
  by_cases hx1 : a * b = 1
  · exact Or.inl hx1
  · right
    exact congrArg Subtype.val (cyclic_four_involution hAc hA4
      (x := (⟨a * b, hxA⟩ : A)) (y := (⟨u, hu.1⟩ : A))
      (fun h1 => hx1 (congrArg Subtype.val h1)) (Subtype.ext hx2)
      (fun h1 => hu1 (congrArg Subtype.val h1)) (Subtype.ext hu2))

theorem card_quaternion_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem uci_of_isZ4StarQ8 {P : Type*} [Group P] [Finite P] (h : IsZ4StarQ8 P) :
    UniqueCentralInvolution P := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, hA4, hAc, ⟨eB⟩⟩ := h
  have hB8 : Nat.card B = 8 := by rw [Nat.card_congr eB.toEquiv, card_quaternion_two]
  have hprod := card_sup_mul_card_inf_of_le_centralizer hAB
  rw [hgen, Subgroup.card_top, hcard, hA4, hB8] at hprod
  have hAB2 : Nat.card ↥(A ⊓ B) = 2 := by omega
  exact uci_of_cyclic_commuting hAB hgen hAc hA4 (centerOrderTwo_quaternion.of_mulEquiv eB.symm) hAB2

theorem centerOrderTwo_of_isQ8Sq {P : Type*} [Group P] [Finite P] (h : IsQ8Sq P) :
    CenterOrderTwo P := by
  obtain ⟨hcard, A, B, ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  have hA8 : Nat.card A = 8 := by rw [Nat.card_congr eA.toEquiv, card_quaternion_two]
  have hB8 : Nat.card B = 8 := by rw [Nat.card_congr eB.toEquiv, card_quaternion_two]
  have hprod := card_sup_mul_card_inf_of_le_centralizer hAB
  rw [hgen, Subgroup.card_top, hcard, hA8, hB8] at hprod
  have hAB2 : Nat.card ↥(A ⊓ B) = 2 := by omega
  exact centerOrderTwo_of_commuting_two hAB hgen (centerOrderTwo_quaternion.of_mulEquiv eA.symm)
    (centerOrderTwo_quaternion.of_mulEquiv eB.symm) hAB2

theorem uci_of_isSpecialPow {P : Type*} [Group P] {w : ℕ} (h : IsSpecialPow 2 2 w P) :
    UniqueCentralInvolution P :=
  (centerOrderTwo_of_card_center_two h.2.2).uci

end Commuting

theorem card_centerOf_eq_card_center {G : Type*} [Group G] (R : Subgroup G) :
    Nat.card ↥(centerOf R) = Nat.card ↥(Subgroup.center ↥R) := by
  have h : (Subgroup.center ↥R).map R.subtype = centerOf R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2), rfl⟩
  rw [← h]
  exact Nat.card_congr ((Subgroup.center ↥R).equivMapOfInjective _ R.subtype_injective).symm

theorem uci_of_isAutM12Vertex {G : Type*} [Group G] {L : Subgroup G} (h : IsAutM12Vertex L) :
    UniqueCentralInvolution ↥(CFSG.Open.pCoreOf 2 L) :=
  (centerOrderTwo_of_card_center_two
    ((card_centerOf_eq_card_center (CFSG.Open.pCoreOf 2 L)).symm.trans h.2.2)).uci

theorem exists_central_of_uci {G : Type*} [Group G] {K R : Subgroup G} (hn : K ≤ Subgroup.normalizer (R : Set G))
    (h : UniqueCentralInvolution ↥R) : ∃ w ∈ R, w ≠ 1 ∧ ∀ k ∈ K, k * w = w * k := by
  obtain ⟨w, hw1, hw2, hwc, hu⟩ := h
  refine ⟨w, w.2, fun h1 => hw1 (Subtype.ext h1), fun k hk => ?_⟩
  let φ : ↥R ≃* ↥R := R.normalizerMonoidHom ⟨k, hn hk⟩
  have hφ : ∀ x : ↥R, ((φ x : ↥R) : G) = k * x * k⁻¹ := fun x =>
    R.normalizerMonoidHom_apply_apply_coe ⟨k, hn hk⟩ x
  have hcen : ∀ y : ↥R, φ w * y = y * φ w := by
    intro y
    apply φ.symm.injective
    simp only [map_mul, MulEquiv.symm_apply_apply]
    exact hwc (φ.symm y)
  have hsq : φ w ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
  rcases hu (φ w) hcen hsq with h1 | h1
  · exfalso
    exact hw1 (φ.injective (by rw [h1, map_one]))
  · have h2 := hφ w
    rw [h1] at h2
    have : (w : G) * k = k * w := by
      calc (w : G) * k = (k * w * k⁻¹) * k := by rw [← h2]
        _ = k * w := by group
    exact this.symm

end CFSG.Quasithin
