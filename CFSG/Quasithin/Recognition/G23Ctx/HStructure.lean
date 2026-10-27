module

public import CFSG.Quasithin.Recognition.G23Ctx.SL23
public import CFSG.GH74.QTGen4.Recog.G23.HLettersD

public section

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
open scoped MatrixGroups

variable {G : Type} [Group G] {H H₁ H₂ : Subgroup G}

structure IsZ (H₁ H₂ : Subgroup G) (z : G) : Prop where
  mem : z ∈ H₁ ⊓ H₂
  ne_one : z ≠ 1
  uniq : ∀ y ∈ H₁ ⊓ H₂, y = 1 ∨ y = z

theorem g23One_symm (hH : G23One H H₁ H₂) : G23One H H₂ H₁ where
  le_one := hH.le_two
  le_two := hH.le_one
  normal_one := hH.normal_two
  normal_two := hH.normal_one
  iso_one := hH.iso_two
  iso_two := hH.iso_one
  index := by rw [sup_comm]; exact hH.index
  card_inf := by rw [inf_comm]; exact hH.card_inf
  eq_centralizer := by rw [inf_comm]; exact hH.eq_centralizer

theorem IsZ.symm {z : G} (hz : IsZ H₁ H₂ z) : IsZ H₂ H₁ z where
  mem := by rw [inf_comm]; exact hz.mem
  ne_one := hz.ne_one
  uniq := fun y hy => hz.uniq y (by rw [inf_comm]; exact hy)

theorem exists_isZ (hH : G23One H H₁ H₂) : ∃ z, IsZ H₁ H₂ z := by
  obtain ⟨z, hzmem, hz1, huniq⟩ := G23One.exists_unique_inf hH
  exact ⟨z, hzmem, hz1, huniq⟩

theorem IsZ.mem_left {z : G} (hz : IsZ H₁ H₂ z) : z ∈ H₁ := (Subgroup.mem_inf.mp hz.mem).1

theorem IsZ.mem_right {z : G} (hz : IsZ H₁ H₂ z) : z ∈ H₂ := (Subgroup.mem_inf.mp hz.mem).2

theorem IsZ.mul_self {z : G} (hz : IsZ H₁ H₂ z) : z * z = 1 := by
  have hz2 : z * z ∈ H₁ ⊓ H₂ := (H₁ ⊓ H₂).mul_mem hz.mem hz.mem
  rcases hz.uniq (z * z) hz2 with h | h
  · exact h
  · exact absurd (mul_left_cancel (a := z) (b := z) (c := 1) (by rw [mul_one]; exact h)) hz.ne_one

theorem IsZ.sq {z : G} (hz : IsZ H₁ H₂ z) : z ^ 2 = 1 := by
  rw [pow_two]; exact hz.mul_self

theorem IsZ.comm (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {h : G} (hh : h ∈ H) :
    h * z = z * h :=
  G23One.mul_comm_of_mem_inf hH hh hz.mem

theorem mem_H_of_comm (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {x : G}
    (hx : x * z = z * x) : x ∈ H := by
  rw [hH.eq_centralizer, Subgroup.mem_centralizer_iff]
  intro t ht
  rcases hz.uniq t ht with rfl | rfl
  · simp
  · exact hx.symm

theorem invol_mem_left (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {x : G} (hx : x ∈ H₁)
    (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  have hz2 : (⟨z, hz.mem_left⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hz.mul_self)
  have hz1 : (⟨z, hz.mem_left⟩ : ↥H₁) ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have hx2' : (⟨x, hx⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hx2)
  rcases sl23_unique_invol hH.iso_one hz2 hz1 ⟨x, hx⟩ hx2' with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem invol_mem_right (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {x : G} (hx : x ∈ H₂)
    (hx2 : x * x = 1) : x = 1 ∨ x = z := by
  have hz2 : (⟨z, hz.mem_right⟩ : ↥H₂) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hz.mul_self)
  have hz1 : (⟨z, hz.mem_right⟩ : ↥H₂) ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have hx2' : (⟨x, hx⟩ : ↥H₂) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hx2)
  rcases sl23_unique_invol hH.iso_two hz2 hz1 ⟨x, hx⟩ hx2' with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem sq_mem_sup (hH : G23One H H₁ H₂) {x : G} (hx : x ∈ H) : x * x ∈ H₁ ⊔ H₂ := by
  have hidx : ((H₁ ⊔ H₂).subgroupOf H).index = 2 := hH.index
  have key : ∀ g : H, g * g ∈ (H₁ ⊔ H₂).subgroupOf H :=
    fun g => (Subgroup.mul_mem_iff_of_index_two hidx).mpr Iff.rfl
  exact Subgroup.mem_subgroupOf.mp (key ⟨x, hx⟩)

theorem mem_sup_of_odd (hH : G23One H H₁ H₂) {x : G} (hx : x ∈ H) {n : ℕ} (hn : Odd n)
    (hxn : x ^ n = 1) : x ∈ H₁ ⊔ H₂ := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : x ^ (k + 1) * x ^ (k + 1) = x := by
    rw [← pow_add]
    have e : k + 1 + (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e, pow_succ, hxn, one_mul]
  have hxk : x ^ (k + 1) ∈ H := H.pow_mem hx _
  have hsq := sq_mem_sup hH hxk
  rw [h1] at hsq
  exact hsq

theorem commutator_mem_sup (hH : G23One H H₁ H₂) {s t : G} (hs : s ∈ H) (ht : t ∈ H) :
    s * t * s⁻¹ * t⁻¹ ∈ H₁ ⊔ H₂ := by
  have hidx : ((H₁ ⊔ H₂).subgroupOf H).index = 2 := hH.index
  have key : ∀ g h : H, g * h * g⁻¹ * h⁻¹ ∈ (H₁ ⊔ H₂).subgroupOf H := by
    intro g h
    simp only [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
    tauto
  exact Subgroup.mem_subgroupOf.mp (key ⟨s, hs⟩ ⟨t, ht⟩)

theorem mul_inv_mem_sup (hH : G23One H H₁ H₂) {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (hx' : x ∉ H₁ ⊔ H₂) (hy' : y ∉ H₁ ⊔ H₂) : x * y⁻¹ ∈ H₁ ⊔ H₂ := by
  have hidx : ((H₁ ⊔ H₂).subgroupOf H).index = 2 := hH.index
  have key : ∀ g g' : H, g ∉ (H₁ ⊔ H₂).subgroupOf H → g' ∉ (H₁ ⊔ H₂).subgroupOf H →
      g * g'⁻¹ ∈ (H₁ ⊔ H₂).subgroupOf H := by
    intro g g' hg hg'
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
    exact iff_of_false hg hg'
  exact Subgroup.mem_subgroupOf.mp
    (key ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hx' (Subgroup.mem_subgroupOf.mp h))
      (fun h => hy' (Subgroup.mem_subgroupOf.mp h)))

theorem conj_mem_pow4 (hH : G23One H H₁ H₂) {w x : G} (hw : w ∈ H) (hx : x ∈ H₁)
    (hx4 : x ^ 4 = 1) : w * x * w⁻¹ ∈ H₁ ∧ (w * x * w⁻¹) ^ 4 = 1 := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hH.normal_one hw) x).mp hx, ?_⟩
  rw [conj_pow, hx4, mul_one, mul_inv_cancel]

def dq1Sub (hX : Nonempty (↥H₁ ≃* SL(2, ZMod 3))) : Subgroup G where
  carrier := {x | x ∈ H₁ ∧ x ^ 4 = 1}
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hx, hx4⟩ := hx
    obtain ⟨hy, hy4⟩ := hy
    show x * y ∈ H₁ ∧ (x * y) ^ 4 = 1
    refine ⟨H₁.mul_mem hx hy, ?_⟩
    have h := sl23_pow4_mul hX ⟨x, hx⟩ ⟨y, hy⟩
      (Subtype.ext (by simpa using hx4)) (Subtype.ext (by simpa using hy4))
    simpa using congrArg Subtype.val h
  one_mem' := ⟨H₁.one_mem, by simp⟩
  inv_mem' := by
    intro x hx
    obtain ⟨hx, hx4⟩ := hx
    exact ⟨H₁.inv_mem hx, by rw [inv_pow, hx4, inv_one]⟩

theorem mem_dq1Sub {hX : Nonempty (↥H₁ ≃* SL(2, ZMod 3))} {x : G} :
    x ∈ dq1Sub hX ↔ x ∈ H₁ ∧ x ^ 4 = 1 :=
  Iff.rfl

theorem dq1_normal (hH : G23One H H₁ H₂) : ((dq1Sub hH.iso_one).subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hn1, hn4⟩ := mem_dq1Sub.mp hn
  have hc := conj_mem_pow4 hH g.2 hn1 hn4
  have hgn : ((g * n * g⁻¹ : ↥H) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by simp
  rw [mem_dq1Sub, hgn]
  exact hc

theorem dq1_isPGroup (hH : G23One H H₁ H₂) :
    IsPGroup 2 ((dq1Sub hH.iso_one).subgroupOf H) := by
  intro g
  refine ⟨2, ?_⟩
  have hg : ((g : ↥H) : G) ^ 4 = 1 := (mem_dq1Sub.mp (Subgroup.mem_subgroupOf.mp g.2)).2
  apply Subtype.ext
  apply Subtype.ext
  simpa using hg

theorem hsq_one_of_mem_inf {z : G} (hz : IsZ H₁ H₂ z) {y : G} (hy : y ∈ H₁ ⊓ H₂) :
    y ^ 2 = 1 := by
  rcases hz.uniq y hy with h | h
  · rw [h, one_pow]
  · rw [h, hz.sq]

theorem pow4_mem_sylow (hH : G23One H H₁ H₂) {T : Subgroup G} (hTH : T ≤ H)
    (hT : quasithinIsSylowTwo (T.subgroupOf H)) {x : G} (hx : x ∈ H₁) (hx4 : x ^ 4 = 1) :
    x ∈ T := by
  haveI hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnorm : ((dq1Sub hH.iso_one).subgroupOf H).Normal := dq1_normal hH
  obtain ⟨hT2, hTidx⟩ := hT
  have hQT : (dq1Sub hH.iso_one).subgroupOf H ≤ T.subgroupOf H := by
    have hle := IsPGroup.le_sylow_of_normal (dq1_isPGroup hH) (hT2.toSylow hTidx)
    rwa [IsPGroup.toSylow_coe] at hle
  have hmem : (⟨x, hH.le_one hx⟩ : ↥H) ∈ (dq1Sub hH.iso_one).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (mem_dq1Sub.mpr ⟨hx, hx4⟩)
  exact Subgroup.mem_subgroupOf.mp (hQT hmem)

theorem pow4_mem_pCoreOf (hH : G23One H H₁ H₂) {x : G} (hx : x ∈ H₁) (hx4 : x ^ 4 = 1) :
    x ∈ pCoreOf 2 H := by
  haveI hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemS : (dq1Sub hH.iso_one).subgroupOf H ∈ {K : Subgroup H | K.Normal ∧ IsPGroup 2 K} :=
    ⟨dq1_normal hH, dq1_isPGroup hH⟩
  have hle : (dq1Sub hH.iso_one).subgroupOf H ≤ CFSG.pCore 2 H := le_sSup hmemS
  have hxH : x ∈ H := hH.le_one hx
  have hmem : (⟨x, hxH⟩ : ↥H) ∈ CFSG.pCore 2 H :=
    hle (Subgroup.mem_subgroupOf.mpr (mem_dq1Sub.mpr ⟨hx, hx4⟩))
  unfold CFSG.Open.pCoreOf
  exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hmem, rfl⟩

theorem eq_of_centralizes (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {k : G}
    (hk : k ∈ H₁ ⊔ H₂) (h₁ : ∀ q ∈ H₁, q ^ 4 = 1 → k * q = q * k)
    (h₂ : ∀ q ∈ H₂, q ^ 4 = 1 → k * q = q * k) : k = 1 ∨ k = z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (G23One.mem_sup_iff hH).mp hk
  have hA : ∀ q : G, q ∈ H₁ → q ^ 4 = 1 → a * q = q * a := by
    intro q hq hq4
    have hbq : b * q = q * b := (G23One.comm_one_two hH hq hb).symm
    have h' : a * q * b = q * a * b := by
      calc a * q * b = a * (q * b) := mul_assoc _ _ _
        _ = a * (b * q) := by rw [hbq]
        _ = a * b * q := (mul_assoc _ _ _).symm
        _ = q * (a * b) := h₁ q hq hq4
        _ = q * a * b := (mul_assoc _ _ _).symm
    exact mul_right_cancel h'
  have hB : ∀ q : G, q ∈ H₂ → q ^ 4 = 1 → b * q = q * b := by
    intro q hq hq4
    have haq : a * q = q * a := G23One.comm_one_two hH ha hq
    have h' : a * (b * q) = a * (q * b) := by
      calc a * (b * q) = a * b * q := (mul_assoc _ _ _).symm
        _ = q * (a * b) := h₂ q hq hq4
        _ = q * a * b := (mul_assoc _ _ _).symm
        _ = a * q * b := by rw [haq]
        _ = a * (q * b) := mul_assoc _ _ _
    exact mul_left_cancel h'
  have hz2 : (⟨z, hz.mem_left⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa using hz.sq)
  have hz1 : (⟨z, hz.mem_left⟩ : ↥H₁) ≠ 1 :=
    fun h => hz.ne_one (by simpa using congrArg Subtype.val h)
  have hz2' : (⟨z, hz.mem_right⟩ : ↥H₂) ^ 2 = 1 := Subtype.ext (by simpa using hz.sq)
  have hz1' : (⟨z, hz.mem_right⟩ : ↥H₂) ≠ 1 :=
    fun h => hz.ne_one (by simpa using congrArg Subtype.val h)
  have hak : a = 1 ∨ a = z := by
    have hc : ∀ q : ↥H₁, q ^ 4 = 1 → (⟨a, ha⟩ : ↥H₁) * q = q * ⟨a, ha⟩ := fun q hq =>
      Subtype.ext (by simpa using hA q.1 q.2 (by simpa using congrArg Subtype.val hq))
    rcases sl23_centralizer_pow4 hH.iso_one hz2 hz1 ⟨a, ha⟩ hc with h | h
    · exact Or.inl (by simpa using congrArg Subtype.val h)
    · exact Or.inr (by simpa using congrArg Subtype.val h)
  have hbk : b = 1 ∨ b = z := by
    have hc : ∀ q : ↥H₂, q ^ 4 = 1 → (⟨b, hb⟩ : ↥H₂) * q = q * ⟨b, hb⟩ := fun q hq =>
      Subtype.ext (by simpa using hB q.1 q.2 (by simpa using congrArg Subtype.val hq))
    rcases sl23_centralizer_pow4 hH.iso_two hz2' hz1' ⟨b, hb⟩ hc with h | h
    · exact Or.inl (by simpa using congrArg Subtype.val h)
    · exact Or.inr (by simpa using congrArg Subtype.val h)
  rcases hak with h | h <;> rcases hbk with h' | h' <;> rw [h, h'] <;> simp [hz.mul_self]

theorem split_invol (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {u : G}
    (hu : u ∈ H₁ ⊔ H₂) (hu2 : u * u = 1) :
    ∃ a ∈ H₁, ∃ b ∈ H₂, u = a * b ∧ a ^ 4 = 1 ∧ b ^ 4 = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (G23One.mem_sup_iff hH).mp hu
  have hc : a * b = b * a := G23One.comm_one_two hH ha hb
  have e : a * b * (a * b) = a * a * (b * b) := by
    calc a * b * (a * b) = a * (b * (a * b)) := mul_assoc _ _ _
      _ = a * ((b * a) * b) := by simp only [mul_assoc]
      _ = a * ((a * b) * b) := by rw [← hc]
      _ = a * a * (b * b) := by simp only [mul_assoc]
  have key : a * a * (b * b) = 1 := by rw [← e]; exact hu2
  have haa : a * a ∈ H₁ ⊓ H₂ := by
    refine Subgroup.mem_inf.mpr ⟨H₁.mul_mem ha ha, ?_⟩
    rw [eq_inv_of_mul_eq_one_left key]
    exact H₂.inv_mem (H₂.mul_mem hb hb)
  have hbb : b * b ∈ H₁ ⊓ H₂ := by
    rw [eq_inv_of_mul_eq_one_right key]
    exact (H₁ ⊓ H₂).inv_mem haa
  refine ⟨a, ha, b, hb, rfl, ?_, ?_⟩
  · have h4 : a ^ 4 = (a * a) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq a]
    rw [h4, hsq_one_of_mem_inf hz haa]
  · have h4 : b ^ 4 = (b * b) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq b]
    rw [h4, hsq_one_of_mem_inf hz hbb]

theorem exists_comm_z (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) :
    ∃ s ∈ H₁, ∃ t ∈ H₁, s ^ 4 = 1 ∧ t ^ 4 = 1 ∧ s * t * s⁻¹ * t⁻¹ = z := by
  have hz2 : (⟨z, hz.mem_left⟩ : ↥H₁) ^ 2 = 1 := Subtype.ext (by simpa using hz.sq)
  have hz1 : (⟨z, hz.mem_left⟩ : ↥H₁) ≠ 1 :=
    fun h => hz.ne_one (by simpa using congrArg Subtype.val h)
  obtain ⟨s, t, hs, ht, hst⟩ := sl23_exists_comm hH.iso_one hz2 hz1
  refine ⟨s.1, s.2, t.1, t.2, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hs
  · simpa using congrArg Subtype.val ht
  · simpa using congrArg Subtype.val hst

theorem exists_order_three (hH : G23One H H₁ H₂) : ∃ a ∈ H₁, a ^ 3 = 1 ∧ a ≠ 1 := by
  obtain ⟨a, ha3, ha1⟩ := sl23_exists_order_three hH.iso_one
  refine ⟨a.1, a.2, ?_, fun h => ha1 (Subtype.ext (by simpa using h))⟩
  simpa using congrArg Subtype.val ha3

theorem mem_sylow_z (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {T : Subgroup G}
    (hTH : T ≤ H) (hT : quasithinIsSylowTwo (T.subgroupOf H)) : z ∈ T := by
  have hz4 : z ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hz.sq, one_pow]
  exact pow4_mem_sylow hH hTH hT hz.mem_left hz4

theorem card_sylow_H (hH : G23One H H₁ H₂) {T : Subgroup G} (hTH : T ≤ H)
    (hT : quasithinIsSylowTwo (T.subgroupOf H)) : Nat.card T = 64 := by
  obtain ⟨hp, hodd⟩ := hT
  haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [card_H_of_G23One hH]; norm_num)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hc := Subgroup.card_mul_index (T.subgroupOf H)
  have hTcard : Nat.card ↥(T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  rw [hn, card_H_of_G23One hH] at hc
  rw [hTcard] at hn
  have hle : 2 ^ n ≤ 576 := Nat.le_of_dvd (by norm_num) ⟨(T.subgroupOf H).index, hc.symm⟩
  have hn10 : n < 10 := by
    by_contra h
    have h1 : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    omega
  have h64 : 2 ^ n = 64 := by
    interval_cases n
    all_goals first
      | rfl
      | (norm_num at hc <;> omega)
  rw [hn]
  exact h64

theorem exists_mem_sylow_not_mem_sup (hH : G23One H H₁ H₂) {T : Subgroup G} (hTH : T ≤ H)
    (hT : quasithinIsSylowTwo (T.subgroupOf H)) : ∃ w ∈ T, w ∉ H₁ ⊔ H₂ := by
  by_contra hcon
  have hle : T ≤ H₁ ⊔ H₂ := fun w hw => not_not.mp (fun hw' => hcon ⟨w, hw, hw'⟩)
  have hd : Nat.card T ∣ Nat.card ↥(H₁ ⊔ H₂) := Subgroup.card_dvd_of_le hle
  rw [card_sylow_H hH hTH hT] at hd
  have h1 := card_sup_mul_two_of_G23One hH
  have h2 := card_H_of_G23One hH
  omega

end CFSG.Quasithin.G23Type.Ctx
