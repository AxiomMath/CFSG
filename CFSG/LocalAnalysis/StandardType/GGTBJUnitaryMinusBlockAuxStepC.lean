module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxStepA
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.ComponentClassification
open CFSG.RankThree.CALinearPlane

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}

@[expose] noncomputable def zeroCoordsEmb (S : Finset (Fin m)) :
    HypIndex S.card ε → HypIndex m ε :=
  hypMap (fun i => S.orderEmbOfFin rfl i) id

theorem zeroCoordsEmb_injective (S : Finset (Fin m)) :
    Function.Injective (zeroCoordsEmb (ε := ε) S) :=
  hypMap_injective (S.orderEmbOfFin rfl).injective (fun _ _ h => h)

theorem zeroCoordsEmb_partner (S : Finset (Fin m)) (a : HypIndex S.card ε) :
    zeroCoordsEmb (ε := ε) S (hypPartner a) = hypPartner (zeroCoordsEmb S a) :=
  hypMap_partner _ _ a

theorem range_zeroCoordsEmb (S : Finset (Fin m)) :
    Set.range (zeroCoordsEmb (ε := ε) S) = zeroCoords S := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with i | k | i
    · exact Or.inl ⟨_, Finset.orderEmbOfFin_mem S rfl i, rfl⟩
    · exact Or.inr (Or.inl ⟨k, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, Finset.orderEmbOfFin_mem S rfl i, rfl⟩)
  · intro ha
    rcases ha with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩ | ⟨i, hi, rfl⟩
    · have hi' : i ∈ Set.range (S.orderEmbOfFin rfl : Fin S.card → Fin m) := by
        rw [Finset.range_orderEmbOfFin]
        exact hi
      obtain ⟨j, hj⟩ := Set.mem_range.mp hi'
      exact ⟨.inl j, by
        change (Sum.inl (S.orderEmbOfFin rfl j) : HypIndex m ε) = Sum.inl i
        rw [hj]⟩
    · exact ⟨.inr (.inl k), rfl⟩
    · have hi' : i ∈ Set.range (S.orderEmbOfFin rfl : Fin S.card → Fin m) := by
        rw [Finset.range_orderEmbOfFin]
        exact hi
      obtain ⟨j, hj⟩ := Set.mem_range.mp hi'
      exact ⟨.inr (.inr j), by
        change (Sum.inr (Sum.inr (S.orderEmbOfFin rfl j)) : HypIndex m ε) =
          Sum.inr (Sum.inr i)
        rw [hj]⟩

theorem hypGram_zeroCoordsEmb (S : Finset (Fin m)) (i j : HypIndex S.card ε) :
    hypGram m ε F (zeroCoordsEmb (ε := ε) S i) (zeroCoordsEmb (ε := ε) S j) =
      hypGram S.card ε F i j := by
  rw [hypGram_apply, hypGram_apply]
  by_cases h : j = hypPartner i
  · have h' : zeroCoordsEmb (ε := ε) S j = hypPartner (zeroCoordsEmb (ε := ε) S i) := by
      rw [h, zeroCoordsEmb_partner]
    rw [if_pos h, if_pos h']
  · have h' : zeroCoordsEmb (ε := ε) S j ≠ hypPartner (zeroCoordsEmb (ε := ε) S i) := by
      intro hh
      rw [← zeroCoordsEmb_partner] at hh
      exact h ((zeroCoordsEmb_injective S) hh)
    rw [if_neg h, if_neg h']

theorem extHyp_zeroCoords_range (S : Finset (Fin m)) :
    (extHyp h (zeroCoordsEmb (ε := ε) S) (zeroCoordsEmb_injective S)
      (zeroCoordsEmb_partner S)).range = hypBlock h (zeroCoords S) := by
  have hrange := range_zeroCoordsEmb (ε := ε) (m := m) S
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [mem_hypBlock]
    intro a b hab
    rw [coe_extHyp]
    rcases hab with ha | hb
    · have ha' : a ∉ Set.range (zeroCoordsEmb (ε := ε) S) := fun hh => ha (hrange ▸ hh)
      rw [extId_apply_of_not_left _ _ _ ha' b]
    · have hb' : b ∉ Set.range (zeroCoordsEmb (ε := ε) S) := fun hh => hb (hrange ▸ hh)
      rw [extId_apply_of_not_right _ _ _ a hb']
  · intro g hg
    let θ : HypIndex S.card ε → HypIndex m ε := zeroCoordsEmb (ε := ε) S
    have hθ : Function.Injective θ := zeroCoordsEmb_injective S
    have hpθ : ∀ a, θ (hypPartner a) = hypPartner (θ a) := zeroCoordsEmb_partner S
    let G : Matrix (HypIndex m ε) (HypIndex m ε) F :=
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F)
    let G' : Matrix (HypIndex S.card ε) (HypIndex S.card ε) F := fun i j => G (θ i) (θ j)
    have hGblock : IsHypBlockOn (zeroCoords S) G := hg
    have hGunit : ((G.map h.bar)ᵀ * hypGram m ε F * G) = hypGram m ε F :=
      (mem_hypSU.mp g.2).1
    have hGdet : G.det = 1 := (mem_hypSU.mp g.2).2
    have hGext : G = extId θ hθ G' := by
      ext a b
      by_cases ha : a ∈ Set.range θ
      · obtain ⟨i, rfl⟩ := ha
        by_cases hb : b ∈ Set.range θ
        · obtain ⟨j, rfl⟩ := hb
          rw [extId_apply_map]
        · rw [extId_apply_of_not_right _ _ _ (θ i) hb]
          exact hGblock (θ i) b (Or.inr (fun h' => hb (hrange.symm ▸ h')))
      · rw [extId_apply_of_not_left _ _ _ ha b]
        exact hGblock a b (Or.inl (fun h' => ha (hrange.symm ▸ h')))
    have hsum_eq : ∀ i j, ((G.map h.bar)ᵀ * hypGram m ε F * G) (θ i) (θ j) =
        ((G'.map h.bar)ᵀ * hypGram S.card ε F * G') i j := by
      intro i j
      have houter : ∀ a : HypIndex m ε, a ∉ Set.range θ →
          (∑ y, h.bar (G y (θ i)) * hypGram m ε F y a) * G a (θ j) = 0 := by
        intro a ha
        rw [hGblock a (θ j) (Or.inl (fun h' => ha (hrange.symm ▸ h')))]
        rw [Matrix.one_apply_ne (fun h' : a = θ j => ha (h' ▸ ⟨j, rfl⟩)), mul_zero]
      have hinner : ∀ a, ∀ b : HypIndex m ε, b ∉ Set.range θ →
          h.bar (G b (θ i)) * hypGram m ε F b a = 0 := by
        intro a b hb
        rw [hGblock b (θ i) (Or.inl (fun h' => hb (hrange.symm ▸ h')))]
        rw [Matrix.one_apply_ne (fun h' : b = θ i => hb (h' ▸ ⟨i, rfl⟩)), map_zero, zero_mul]
      calc ((G.map h.bar)ᵀ * hypGram m ε F * G) (θ i) (θ j)
          = ∑ a, (∑ y, h.bar (G y (θ i)) * hypGram m ε F y a) * G a (θ j) := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
        _ = ∑ a, (∑ b, h.bar (G (θ b) (θ i)) *
              hypGram m ε F (θ b) (θ a)) * G (θ a) (θ j) := by
            rw [← Fintype.sum_of_injective θ hθ _
              (fun a => (∑ y, h.bar (G y (θ i)) * hypGram m ε F y a) * G a (θ j)) houter
              fun _ => rfl]
            refine Finset.sum_congr rfl fun a _ => ?_
            exact congrArg (fun z => z * G (θ a) (θ j))
              (Fintype.sum_of_injective θ hθ _
                (fun b => h.bar (G b (θ i)) * hypGram m ε F b (θ a)) (hinner (θ a))
                fun _ => rfl).symm
        _ = ∑ a, (∑ b, h.bar (G' b i) * hypGram S.card ε F b a) * G' a j := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have h1 : (∑ b, h.bar (G (θ b) (θ i)) * hypGram m ε F (θ b) (θ a)) =
                ∑ b, h.bar (G' b i) * hypGram S.card ε F b a := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [hypGram_zeroCoordsEmb S b a]
            rw [h1]
        _ = ((G'.map h.bar)ᵀ * hypGram S.card ε F * G') i j := by
            simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    have hunit : ((G'.map h.bar)ᵀ * hypGram S.card ε F * G') = hypGram S.card ε F := by
      ext i j
      rw [← hsum_eq i j, hGunit, hypGram_zeroCoordsEmb S i j]
    have hdet : G'.det = 1 := by
      rw [← det_extId θ hθ G', ← hGext]
      exact hGdet
    have hdetne : G'.det ≠ 0 := by
      rw [hdet]
      exact one_ne_zero
    let g' : GL (HypIndex S.card ε) F := Matrix.GeneralLinearGroup.mkOfDetNeZero G' hdetne
    have hG'mem : g' ∈ hypSU h S.card ε := mem_hypSU.mpr ⟨hunit, hdet⟩
    refine ⟨⟨g', hG'mem⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_extHyp]
    exact hGext.symm

theorem nonempty_hypBlock_zeroCoords_mulEquiv (S : Finset (Fin m)) :
    Nonempty (hypBlock h (zeroCoords (ε := ε) S) ≃* hypSU h S.card ε) :=
  ⟨((MonoidHom.ofInjective (extHyp_injective h _ _ _)).trans
    (MulEquiv.subgroupCongr (extHyp_zeroCoords_range (ε := ε) S))).symm⟩


theorem two_le_of_dvd_sub_one {f p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1)
    (hf : 1 ≤ f) : 2 ≤ f := by
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · have hf1 : f = 1 := by omega
    subst hf1
    have hp1 : p ∣ 1 := by simpa using hpq
    exact absurd (Nat.le_of_dvd one_pos hp1) (by have := hp.two_le; omega)
  · exact hge

theorem isQuasisimple_hypBlock_zeroCoords (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1)
    (hε : ε ≤ 1) {S : Finset (Fin m)} (hS : S.Nonempty) :
    CFSG.Assembly.IsQuasisimple (hypBlock h (zeroCoords (ε := ε) S)) := by
  have hn2 : 2 ≤ f := two_le_of_dvd_sub_one hp hpq h.one_le
  obtain ⟨e⟩ := nonempty_hypBlock_zeroCoords_mulEquiv (h := h) (ε := ε) S
  have hmq : (2 * S.card + ε, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 := (Prod.ext_iff.mp h).2
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hqSU : CFSG.Open.IsQuasisimple (hypSU h S.card ε) := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · exact absurd hS (by simp [Finset.card_eq_zero.mp h0])
    have h1 : 1 ≤ S.card := hpos
    rcases Nat.eq_or_lt_of_le h1 with h1' | h2
    ·
      have hSc : S.card = 1 := h1'.symm
      rw [hSc] at hmq ⊢
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with hε0 | hε1
      · rw [hε0]
        exact (CFSG.AGLEmbedding.LeviBlock.hypSU_facts_two h hn2).1
      · rw [hε1] at hmq ⊢
        exact (CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le (s := 1) (ε := 1) h
          (by norm_num) hmq).1
    ·
      have hle : 3 ≤ 2 * S.card + ε := by
        have h4 : 2 * 2 ≤ 2 * S.card := Nat.mul_le_mul_left 2 h2
        omega
      exact (CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le h hle hmq).1
  exact hqSU.of_mulEquiv e

theorem splitEntries_eq_one_of_mem_zeroCoords {ζ : F} {t : Fin m → ZMod p}
    {S : Finset (Fin m)} (ht : ∀ i ∈ S, t i = 0) {a : HypIndex m ε}
    (ha : a ∈ zeroCoords S) : splitEntries ζ t a = 1 := by
  rcases ha with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩ | ⟨i, hi, rfl⟩
  · rw [splitEntries, ht i hi, ZMod.val_zero, pow_zero]
  · rfl
  · rw [splitEntries, ht i hi, ZMod.val_zero, pow_zero, inv_one]

theorem hypBlock_zeroCoords_le_centralizer {ζ : F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε} (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))} {S : Finset (Fin m)}
    (hS : ∀ i ∈ S, ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0) :
    hypBlock h (zeroCoords (ε := ε) S) ≤ Subgroup.centralizer (τ '' E) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨t, ht, rfl⟩
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hτt : (((τ t : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) =
      diagonal (splitEntries ζ (Multiplicative.toAdd t)) := hτ (Multiplicative.toAdd t)
  rw [hτt]
  have hentry : ∀ x ∈ zeroCoords (ε := ε) S,
      splitEntries ζ (Multiplicative.toAdd t) x = 1 :=
    fun x hx => splitEntries_eq_one_of_mem_zeroCoords
      (fun i hi => hS i hi (Multiplicative.toAdd t) ht) hx
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hD : splitEntries ζ (Multiplicative.toAdd t) a =
      splitEntries ζ (Multiplicative.toAdd t) b
  · rw [hD, mul_comm]
  · have hne : a ≠ b := fun hab => hD (by rw [hab])
    have hgab : (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0 := by
      by_cases ha : a ∈ zeroCoords (ε := ε) S
      · by_cases hb : b ∈ zeroCoords (ε := ε) S
        · exact absurd (by rw [hentry a ha, hentry b hb]) hD
        · rw [mem_hypBlock.mp hg a b (Or.inr hb), Matrix.one_apply_ne hne]
      · rw [mem_hypBlock.mp hg a b (Or.inl ha), Matrix.one_apply_ne hne]
    rw [hgab, zero_mul, mul_zero]

theorem hypBlock_zeroCoords_eq_one_of_empty (hε : ε ≤ 1) {S : Finset (Fin m)} (hS : S = ∅)
    {g : hypSU h m ε} (hg : g ∈ hypBlock h (zeroCoords (ε := ε) S)) {a b : HypIndex m ε}
    (hab : a ≠ b) :
    (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0 := by
  subst hS
  have hsub : ∀ x ∈ zeroCoords (ε := ε) (∅ : Finset (Fin m)), ∃ k : Fin ε, x = .inr (.inl k) := by
    rintro x (⟨i, hi, -⟩ | ⟨k, rfl⟩ | ⟨i, hi, -⟩)
    · exact absurd hi (by simp)
    · exact ⟨k, rfl⟩
    · exact absurd hi (by simp)
  have hpair : ¬ (a ∈ zeroCoords (ε := ε) (∅ : Finset (Fin m)) ∧
      b ∈ zeroCoords (ε := ε) (∅ : Finset (Fin m))) := by
    rintro ⟨ha, hb⟩
    obtain ⟨k, rfl⟩ := hsub a ha
    obtain ⟨l, rfl⟩ := hsub b hb
    have : Subsingleton (Fin ε) := Fin.subsingleton_iff_le_one.mpr hε
    exact hab (by rw [Subsingleton.elim k l])
  rw [mem_hypBlock.mp hg a b]
  · rw [Matrix.one_apply_ne hab]
  · by_cases ha : a ∈ zeroCoords (ε := ε) (∅ : Finset (Fin m))
    · exact Or.inr fun hb => hpair ⟨ha, hb⟩
    · exact Or.inl ha


open scoped commutatorElement

@[expose] noncomputable def zeroSet (E : Set (Multiplicative (Fin m → ZMod p))) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0)

theorem mem_zeroSet {E : Set (Multiplicative (Fin m → ZMod p))} {i : Fin m} :
    i ∈ zeroSet E ↔ ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0 := by
  classical
  simp [zeroSet]

theorem weightClass_zero_eq_zeroCoords {E : Set (Multiplicative (Fin m → ZMod p))}
    {a : HypIndex m ε} (hz : ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E →
      splitWeight a t = 0) :
    weightClass E a ∪ weightClassPartner E a = zeroCoords (ε := ε) (zeroSet E) := by
  classical
  ext x
  rcases x with i | k | i
  · simp only [Set.mem_union, weightClass, weightClassPartner, Set.mem_setOf_eq, zeroCoords,
      Set.mem_setOf_eq, splitWeight_inl]
    have hA : (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = splitWeight a t) ↔
        (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0) := by
      constructor <;> intro h t ht
      · rw [h t ht, hz t ht]
      · rw [h t ht, hz t ht]
    have hB : (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = -splitWeight a t) ↔
        (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0) := by
      constructor <;> intro h t ht
      · have h' := h t ht
        rw [hz t ht] at h'
        simpa using h'
      · rw [h t ht, hz t ht]
        simp
    rw [hA, hB]
    simp [mem_zeroSet]
  · simp only [Set.mem_union, weightClass, weightClassPartner, Set.mem_setOf_eq, zeroCoords,
      Set.mem_setOf_eq, splitWeight_z]
    have hA : (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → (0 : ZMod p) = splitWeight a t) :=
      fun t ht => (hz t ht).symm
    have hB : (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E →
        splitWeight a t = 0) := fun t ht => hz t ht
    exact ⟨fun _ => Or.inr (Or.inl ⟨k, rfl⟩), fun _ => Or.inl hA⟩
  · simp only [Set.mem_union, weightClass, weightClassPartner, Set.mem_setOf_eq, zeroCoords,
      Set.mem_setOf_eq, splitWeight_inr]
    have hA : (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → -t i = splitWeight a t) ↔
        (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0) := by
      constructor <;> intro h t ht
      · have h' := h t ht
        rw [hz t ht] at h'
        simpa using h'
      · rw [h t ht, hz t ht]
        simp
    have hB : (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → -t i = -splitWeight a t) ↔
        (∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0) := by
      constructor <;> intro h t ht
      · have h' := h t ht
        rw [hz t ht] at h'
        simpa using h'
      · rw [h t ht, hz t ht]
    rw [hA, hB]
    simp [mem_zeroSet]

theorem mul_comm_of_offDiag_eq_zero {u v : hypSU h m ε}
    (hu : ∀ a b : HypIndex m ε, a ≠ b →
      (((u : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0)
    (hv : ∀ a b : HypIndex m ε, a ≠ b →
      (((v : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F) a b = 0) :
    u * v = v * u := by
  have hA : ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F)).IsDiag := hu
  have hB : ((((v : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F)).IsDiag := hv
  have hcomm : ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F)) *
      ((((v : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F)) =
      ((((v : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F)) *
      ((((u : hypSU h m ε) : GL (HypIndex m ε) F) :
        Matrix (HypIndex m ε) (HypIndex m ε) F)) := by
    rw [← hA.diagonal_diag, ← hB.diagonal_diag]
    exact (Matrix.commute_diagonal _ _).eq
  apply Subtype.ext
  apply Units.ext
  simpa only [Subgroup.coe_mul, Units.val_mul] using hcomm

theorem exists_eq_zeroBlock_of_isComponentOf
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) (hε : ε ≤ 1) {ζ : F}
    {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε}
    (hτ : IsSplitTorus h ζ τ) {E : Set (Multiplicative (Fin m → ZMod p))}
    {J : Subgroup (hypSU h m ε)}
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer (τ '' E)))
    {a : HypIndex m ε}
    (hJle : J ≤ Subgroup.centralizer (τ '' E) ⊓
      hypBlock h (weightClass E a ∪ weightClassPartner E a))
    (hz : ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → splitWeight a t = 0) :
    ∃ S : Finset (Fin m), S.Nonempty ∧
      J = (hypBlock h (zeroCoords (ε := ε) S)).map
        (MulAut.conj (1 : hypSU h m ε)).toMonoidHom := by
  classical
  let S : Finset (Fin m) := zeroSet E
  have hpair : weightClass E a ∪ weightClassPartner E a = zeroCoords (ε := ε) S :=
    weightClass_zero_eq_zeroCoords (ε := ε) hz
  have hJle' : J ≤ Subgroup.centralizer (τ '' E) ⊓ hypBlock h (zeroCoords (ε := ε) S) := by
    rwa [hpair] at hJle
  have hSdef : ∀ i ∈ S, ∀ t : Fin m → ZMod p, Multiplicative.ofAdd t ∈ E → t i = 0 :=
    fun i hi => (mem_zeroSet).mp hi
  have hQle : hypBlock h (zeroCoords (ε := ε) S) ≤ Subgroup.centralizer (τ '' E) :=
    hypBlock_zeroCoords_le_centralizer (ε := ε) hτ hSdef
  have hSne : S.Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have hcomm : ∀ u ∈ J, ∀ v ∈ J, u * v = v * u := by
      intro u hu v hv
      exact mul_comm_of_offDiag_eq_zero
        (fun x y hxy => hypBlock_zeroCoords_eq_one_of_empty (ε := ε) hε hS (hJle' hu).2 hxy)
        (fun x y hxy => hypBlock_zeroCoords_eq_one_of_empty (ε := ε) hε hS (hJle' hv).2 hxy)
    exact LinSemisimple.false_of_isQuasisimple_of_commute hJ.2.2 hcomm
  refine ⟨S, hSne, ?_⟩
  have hQ := isQuasisimple_hypBlock_zeroCoords (h := h) hp hpq hε hSne
  have hJeq : J = hypBlock h (zeroCoords (ε := ε) S) :=
    eq_of_isComponentOf_le_of_isQuasisimple hJ (fun x hx => (hJle' hx).2) hQle hQ
  rw [hJeq]
  rw [show (MulAut.conj (1 : hypSU h m ε)).toMonoidHom = MonoidHom.id _ from by
    ext x
    simp, Subgroup.map_id]

end CFSG.StandardType.SuSplitRootGen

