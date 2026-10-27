module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206q
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.CardLeOfSylowConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

@[expose] def ForceRealPair (Q : Type) [Group Q] : Prop :=
  ∃ a b g k : Q, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * (b * a * b⁻¹) = b * a * b⁻¹ * a ∧ a * b ≠ b * a ∧
    g * a * g⁻¹ = a⁻¹ ∧ k * b * k⁻¹ = b⁻¹

theorem ForceRealPair.of_hom {G Q : Type} [Group G] [Group Q] (f : G →* Q) {a b g k : G}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hw : a * (b * a * b⁻¹) = b * a * b⁻¹ * a)
    (hab : f (a * b) ≠ f (b * a)) (hg : g * a * g⁻¹ = a⁻¹) (hk : k * b * k⁻¹ = b⁻¹) :
    ForceRealPair Q :=
  ⟨f a, f b, f g, f k, by rw [← map_pow, ha, map_one], by rw [← map_pow, hb, map_one],
    by simpa only [map_mul, map_inv] using congrArg f hw,
    by simpa only [map_mul] using hab,
    by simpa only [map_mul, map_inv] using congrArg f hg,
    by simpa only [map_mul, map_inv] using congrArg f hk⟩

theorem ForceRealPair.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : ForceRealPair Q') : ForceRealPair Q := by
  obtain ⟨a, b, g, k, ha, hb, hw, hab, hg, hk⟩ := h
  refine ForceRealPair.of_hom e.symm.toMonoidHom ha hb hw ?_ hg hk
  intro h
  exact hab (e.symm.injective (by simpa using h))

theorem ForceRealPair.of_mem {G : Type} [Group G] (H : Subgroup G) {a b g k : G} (haH : a ∈ H)
    (hbH : b ∈ H) (hgH : g ∈ H) (hkH : k ∈ H) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hw : a * (b * a * b⁻¹) = b * a * b⁻¹ * a) (hab : a * b ≠ b * a) (hg : g * a * g⁻¹ = a⁻¹)
    (hk : k * b * k⁻¹ = b⁻¹) : ForceRealPair H :=
  ⟨⟨a, haH⟩, ⟨b, hbH⟩, ⟨g, hgH⟩, ⟨k, hkH⟩, Subtype.ext ha, Subtype.ext hb, Subtype.ext hw,
    fun h => hab (congrArg Subtype.val h), Subtype.ext hg, Subtype.ext hk⟩

theorem forceRealPair_facts_of_matrix {n R : Type} [Fintype n] [DecidableEq n] [CommRing R]
    (a b g k : GL n R)
    (ha : (a : Matrix n n R) * a * a = 1) (hb : (b : Matrix n n R) * b * b = 1)
    (hw : (a : Matrix n n R) * (b * a * (b⁻¹ : GL n R)) = b * a * (b⁻¹ : GL n R) * a)
    (hab : (a : Matrix n n R) * b ≠ b * a)
    (hg : (g : Matrix n n R) * a * (g⁻¹ : GL n R) = (a⁻¹ : GL n R))
    (hk : (k : Matrix n n R) * b * (k⁻¹ : GL n R) = (b⁻¹ : GL n R)) :
    a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * (b * a * b⁻¹) = b * a * b⁻¹ * a ∧ a * b ≠ b * a ∧
      g * a * g⁻¹ = a⁻¹ ∧ k * b * k⁻¹ = b⁻¹ := by
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_, fun h => hab ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [Units.val_pow_eq_pow_val, pow_three, ← mul_assoc]; exact ha
  · rw [Units.val_pow_eq_pow_val, pow_three, ← mul_assoc]; exact hb
  · simpa only [Units.val_mul] using hw
  · simpa only [Units.val_mul] using congrArg Units.val h
  · simpa only [Units.val_mul] using hg
  · simpa only [Units.val_mul] using hk

theorem isPGroup_three_of_wreath {Q : Type} [Group Q] {a b : Q} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hw : a * (b * a * b⁻¹) = b * a * b⁻¹ * a) :
    IsPGroup 3 ↥(zpowers b ⊔ closure ({a, b * a * b⁻¹, b⁻¹ * a * b} : Set Q)) := by
  set s : Set Q := {a, b * a * b⁻¹, b⁻¹ * a * b} with hs
  have hbinv : b⁻¹ = b * b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, hb]
  have hbb : b * b = b⁻¹ := hbinv.symm
  have hbb' : b⁻¹ * b⁻¹ = b := by rw [← mul_inv_rev, hbb, inv_inv]
  have h12 : Commute a (b * a * b⁻¹) := hw
  have h23 : Commute (b * a * b⁻¹) (b⁻¹ * a * b) := by
    show b * a * b⁻¹ * (b⁻¹ * a * b) = b⁻¹ * a * b * (b * a * b⁻¹)
    have e1 : b⁻¹ * a * b = b * (b * a * b⁻¹) * b⁻¹ := by
      calc b⁻¹ * a * b = b⁻¹ * a * (b⁻¹ * b⁻¹) := by rw [hbb']
        _ = b * b * a * (b⁻¹ * b⁻¹) := by rw [hbb]
        _ = b * (b * a * b⁻¹) * b⁻¹ := by group
    rw [e1]
    calc b * a * b⁻¹ * (b * (b * a * b⁻¹) * b⁻¹) = b * (a * (b * a * b⁻¹)) * b⁻¹ := by group
      _ = b * (b * a * b⁻¹ * a) * b⁻¹ := by rw [hw]
      _ = b * (b * a * b⁻¹) * b⁻¹ * (b * a * b⁻¹) := by group
  have h13 : Commute a (b⁻¹ * a * b) := by
    show a * (b⁻¹ * a * b) = b⁻¹ * a * b * a
    calc a * (b⁻¹ * a * b) = b⁻¹ * (b * a * b⁻¹ * a) * b := by group
      _ = b⁻¹ * (a * (b * a * b⁻¹)) * b := by rw [hw]
      _ = b⁻¹ * a * b * a := by group
  have hpair : s.Pairwise Commute := by
    intro x hx y hy _
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact h12 | exact h12.symm | exact h23 | exact h23.symm | exact h13 | exact h13.symm
  have hcube : ∀ x ∈ s, x ^ 3 = 1 := by
    intro x hx
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · rw [conj_pow, ha]; group
    · rw [show b⁻¹ * a * b = b⁻¹ * a * b⁻¹⁻¹ by group, conj_pow, ha]; group
  have hK : IsPGroup 3 ↥(closure s) := by
    have hc : ∀ x ∈ closure s, ∀ y ∈ closure s, Commute x y := by
      let _ := Subgroup.closureCommGroupOfComm hpair
      intro x hx y hy
      have := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(closure s)) ⟨y, hy⟩)
      exact this
    have h3 : ∀ x ∈ closure s, x ^ 3 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact hcube x hx
      | one => exact one_pow 3
      | mul x y hx hy ihx ihy => rw [(hc x hx y hy).mul_pow, ihx, ihy, one_mul]
      | inv x hx ih => rw [inv_pow, ih, inv_one]
    intro x
    exact ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hB : IsPGroup 3 ↥(zpowers b) := CFSG.GroupTheory.isPGroup_zpowers_of_pow_three hb
  have hconj : ∀ x ∈ s, b * x * b⁻¹ ∈ s ∧ b⁻¹ * x * b ∈ s := by
    intro x hx
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    · refine ⟨Or.inr (Or.inr ?_), Or.inl (by group)⟩
      calc b * (b * a * b⁻¹) * b⁻¹ = b * b * a * (b⁻¹ * b⁻¹) := by group
        _ = b⁻¹ * a * b := by rw [hbb, hbb']
    · refine ⟨Or.inl (by group), Or.inr (Or.inl ?_)⟩
      calc b⁻¹ * (b⁻¹ * a * b) * b = b⁻¹ * b⁻¹ * a * (b * b) := by group
        _ = b * a * b⁻¹ := by rw [hbb, hbb']
  have hnorm : zpowers b ≤ normalizer (closure s : Set Q) := by
    rw [zpowers_le, mem_normalizer_iff]
    have hle : ∀ g : Q, (∀ x ∈ s, g * x * g⁻¹ ∈ s) → ∀ y ∈ closure s, g * y * g⁻¹ ∈ closure s := by
      intro g hg y hy
      have : closure s ≤ (closure s).comap (MulAut.conj g).toMonoidHom := by
        rw [closure_le]
        intro x hx
        exact subset_closure (hg x hx)
      exact this hy
    intro y
    constructor
    · exact hle b (fun x hx => (hconj x hx).1) y
    · intro hy
      have := hle b⁻¹ (fun x hx => by simpa using (hconj x hx).2) _ hy
      simpa [mul_assoc] using this
  exact hB.to_sup_of_normal_right' hK hnorm

theorem not_cubesCommute_of_cover {X Q : Type} [Group X] [Finite X] [Group Q]
    (hQ : Nonempty (Q ≃* X ⧸ center X)) (h : ForceRealPair Q) :
    ¬ ∀ P : Subgroup X, IsPGroup 3 P → ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x := by
  intro hT1
  obtain ⟨e⟩ := hQ
  obtain ⟨π, hπ, hker⟩ := CFSG.AGLEmbedding.exists_surjective_ker_eq_center e.symm
  obtain ⟨a, b, g, k, ha, hb, hw, hab, hg, hk⟩ := h
  obtain ⟨w, hw3, hwa⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s206q_lift π hπ hker ha hg
  obtain ⟨v, hv3, hvb⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s206q_lift π hπ hker hb hk
  set Sb : Subgroup Q := zpowers b ⊔ closure ({a, b * a * b⁻¹, b⁻¹ * a * b} : Set Q) with hSb
  have hSp : IsPGroup 3 Sb := isPGroup_three_of_wreath ha hb hw
  have haS : a ∈ Sb := mem_sup_right (subset_closure (Set.mem_insert _ _))
  have hbS : b ∈ Sb := mem_sup_left (mem_zpowers b)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Finite.of_surjective π hπ
  set L : Subgroup X := Sb.comap π with hL
  have hLnil : Group.IsNilpotent L := by
    have : Group.IsNilpotent Sb := hSp.isNilpotent
    refine _root_.isNilpotent_of_ker_le_center (π.subgroupComap Sb) ?_
    intro y hy
    rw [mem_center_iff]
    intro z
    have hy' : (y : X) ∈ center X := hker ▸
      (show π (y : X) = 1 from congrArg Subtype.val ((MonoidHom.mem_ker).mp hy))
    exact Subtype.ext ((mem_center_iff.mp hy') z)
  obtain ⟨P⟩ : Nonempty (Sylow 3 L) := inferInstance
  have : (P : Subgroup L).Normal := inferInstance
  have := Sylow.unique_of_normal P inferInstance
  have hmem : ∀ y : L, y ^ 3 = 1 → y ∈ (P : Subgroup L) := by
    intro y hy
    obtain ⟨Q₁, hQ₁⟩ := (CFSG.GroupTheory.isPGroup_zpowers_of_pow_three hy).exists_le_sylow
    have hQP : Q₁ = P := Subsingleton.elim _ _
    exact hQP ▸ hQ₁ (mem_zpowers y)
  have hwL : w ∈ L := by rw [hL, mem_comap, hwa]; exact haS
  have hvL : v ∈ L := by rw [hL, mem_comap, hvb]; exact hbS
  have hwP := hmem ⟨w, hwL⟩ (Subtype.ext (by simpa using hw3))
  have hvP := hmem ⟨v, hvL⟩ (Subtype.ext (by simpa using hv3))
  have hc := hT1 ((P : Subgroup L).map L.subtype) (P.isPGroup'.map _) w ⟨⟨w, hwL⟩, hwP, rfl⟩
    v ⟨⟨v, hvL⟩, hvP, rfl⟩ hw3 hv3
  apply hab
  rw [← hwa, ← hvb, ← map_mul, ← map_mul, hc]

theorem exists_sylow_three_normalizer_le {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    (hT2 : (∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range) →
      center X = ⊥ →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ normalizer (S : Set X) ≤ Y)
    (hA : ∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range)
    (hZ : center X = ⊥) : ∃ S : Sylow 3 X, normalizer ((S : Subgroup X) : Set X) ≤ Y := by
  obtain ⟨S, hS, hN⟩ := hT2 hA hZ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at hS
  exact ⟨hS.2.1.toSylow hS.2.2, hN⟩

theorem exists_sylow_two_le_of_isNontrivialParabolic {X : Type} [Group X] {Y : Subgroup X}
    (h : S19.IsNontrivialParabolic X Y) : ∃ T : Sylow 2 X, (T : Subgroup X) ≤ Y := by
  obtain ⟨⟨T, hT⟩, -, -⟩ := h
  exact ⟨T, le_normalizer.trans hT⟩

theorem index_dvd_of_sylow_le {X : Type} [Group X] [Finite X] {p k m : ℕ} [hp : Fact p.Prime]
    (hX : Nat.card X = p ^ k * m) (hm : ¬ p ∣ m) (P : Sylow p X) {Y : Subgroup X}
    (hPY : (P : Subgroup X) ≤ Y) : Y.index ∣ m := by
  have hP := CFSG.GroupTheory.GL52.card_sylow_of_card_eq_pow_mul hX hm P
  have h1 := (P : Subgroup X).card_mul_index
  rw [hP, hX] at h1
  have hidx : (P : Subgroup X).index = m :=
    Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos k) h1
  exact hidx ▸ Subgroup.index_dvd_of_le hPY

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
