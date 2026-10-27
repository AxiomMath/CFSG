module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesL44
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.L44
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesL44
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

section Perfect

theorem map_eq_one_of_isPerfect {P A : Type*} [Group P] [CommMonoid A]
    (hP : Group.IsPerfect P) (f : P →* A) (x : P) : f x = 1 := by
  have h1 : commutator P ≤ (f.toHomUnits).ker := Abelianization.commutator_subset_ker _
  rw [hP.commutator_eq_top] at h1
  have h2 := MonoidHom.mem_ker.mp (h1 (Subgroup.mem_top x))
  simpa using congrArg Units.val h2

theorem entry_eq_one_of_isPerfect {H : Type*} [Group H] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (m : H →* Matrix ι ι K) {P : Subgroup H} (hP : Group.IsPerfect P)
    (k : ι) (hrow : ∀ g ∈ P, ∀ l, l ≠ k → m g k l = 0) : ∀ g ∈ P, m g k k = 1 := by
  let f : P →* K :=
    { toFun := fun g => m g k k
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, map_mul, Matrix.mul_apply]
        rw [Finset.sum_eq_single k]
        · intro l _ hl
          rw [hrow g g.2 l hl, zero_mul]
        · simp }
  intro g hg
  exact map_eq_one_of_isPerfect hP f ⟨g, hg⟩

end Perfect

theorem card_le_of_model {G M' : Type*} [Group G] [Group M'] {I A B P : Subgroup G}
    (φ : I ≃* M') {A0' : Subgroup M'} (hφA : (A.subgroupOf I).map φ.toMonoidHom = A0')
    (hBA : B ≤ A) (hAI : A ≤ I) (hPI : P ≤ I) (hPB : P ≤ Subgroup.centralizer (B : Set G))
    (hP : Group.IsPerfect P) (hB9 : Nat.card B = 9) {n : ℕ}
    (h : ∀ B' P' : Subgroup M', B' ≤ A0' → Nat.card B' = 9 →
      P' ≤ Subgroup.centralizer (B' : Set M') → Group.IsPerfect P' → Nat.card P' ≤ n) :
    Nat.card P ≤ n := by
  set B' := (B.subgroupOf I).map φ.toMonoidHom with hB'
  set P' := (P.subgroupOf I).map φ.toMonoidHom with hP'
  have hB'A : B' ≤ A0' := by
    rw [← hφA]
    exact Subgroup.map_mono (fun x hx => hBA hx)
  have hB'9 : Nat.card B' = 9 := by
    rw [hB', Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBA.trans hAI)).toEquiv, hB9]
  have hP'C : P' ≤ Subgroup.centralizer (B' : Set M') := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hpb : (b : G) * p = p * b :=
      Subgroup.mem_centralizer_iff.mp (hPB (Subgroup.mem_subgroupOf.mp hp)) b
        (Subgroup.mem_subgroupOf.mp hb)
    have hpb' : b * p = p * b := Subtype.ext hpb
    change φ b * φ p = φ p * φ b
    rw [← map_mul, ← map_mul, hpb']
  let e : P ≃* P' := (Subgroup.subgroupOfEquivOfLe hPI).symm.trans
    (Subgroup.equivMapOfInjective _ _ φ.injective)
  have hP'p : Group.IsPerfect P' := by
    have := hP
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rw [Nat.card_congr e.toEquiv]
  exact h B' P' hB'A hB'9 hP'C hP'p

theorem exists_basis_of_card_nine {M' : Type*} [Group M']
    (δ' : Multiplicative (Fin 3 → ZMod 3) →* M') {B : Subgroup M'} (hBδ : B ≤ δ'.range)
    (hB9 : Nat.card B = 9) :
    ∃ x y : Fin 3 → ZMod 3, δ' (Multiplicative.ofAdd x) ∈ B ∧ δ' (Multiplicative.ofAdd y) ∈ B ∧
      x ≠ 0 ∧ y ≠ 0 ∧ y ≠ x ∧ y ≠ x + x := by
  have hB1 : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB9
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun e => hb' (Subtype.ext e)
  obtain ⟨x', rfl⟩ := hBδ hbB
  obtain ⟨c, hcB, hc⟩ : ∃ c ∈ B, c ≠ 1 ∧ c ≠ δ' x' ∧ c ≠ δ' x' ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hsub : (B : Set M') ⊆ {1, δ' x', δ' x' ^ 2} := by
      intro c hc
      by_cases h1 : c = 1
      · exact Or.inl h1
      · by_cases h2 : c = δ' x'
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (hcon c hc h1 h2))
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, δ' x', δ' x' ^ 2} : Set M').ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
      rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hB9] at h1
    omega
  obtain ⟨y', rfl⟩ := hBδ hcB
  refine ⟨Multiplicative.toAdd x', Multiplicative.toAdd y', hbB, hcB, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hb1
    rw [show x' = 1 from Multiplicative.toAdd.injective h, map_one]
  · intro h
    apply hc.1
    rw [show y' = 1 from Multiplicative.toAdd.injective h, map_one]
  · intro h
    apply hc.2.1
    rw [show y' = x' from Multiplicative.toAdd.injective h]
  · intro h
    apply hc.2.2
    rw [show y' = x' ^ 2 from Multiplicative.toAdd.injective (by rw [h, toAdd_pow, two_nsmul]),
      map_pow]

@[expose] def matL : M →* Matrix (Fin 4) (Fin 4) F4 where
  toFun g := g
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' := Matrix.SpecialLinearGroup.coe_mul

@[expose] def TwoZero (w : Fin 3 → ZMod 3) : Prop :=
  (Finset.univ.filter fun i => ext w i = 0).card = 2

instance : DecidablePred TwoZero := fun w => by unfold TwoZero; infer_instance

theorem exists_twoZero : ∀ x y : Fin 3 → ZMod 3, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ x + x →
    ∃ a b : Fin 3, TwoZero ((a : ℕ) • x + (b : ℕ) • y) := by
  decide +kernel

theorem exists_perm_twoZero : ∀ w : Fin 3 → ZMod 3, TwoZero w → ∃ σ : Equiv.Perm (Fin 4),
    ext w (σ 2) = 0 ∧ ext w (σ 3) = 0 ∧ ext w (σ 0) ≠ 0 ∧ ext w (σ 1) ≠ 0 ∧
      ext w (σ 0) ≠ ext w (σ 1) := by
  decide +kernel

theorem card_le_sixty_of_std {u : Fin 3 → ZMod 3} (h2 : ext u 2 = 0) (h3 : ext u 3 = 0)
    (h0 : ext u 0 ≠ 0) (h1 : ext u 1 ≠ 0) (h01 : ext u 0 ≠ ext u 1) {P : Subgroup M}
    (hPC : P ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd u)} : Set M))
    (hP : Group.IsPerfect P) : Nat.card P ≤ 60 := by
  have hbd : ∀ g ∈ P, IsBlockDiag (ext u) (g : Matrix (Fin 4) (Fin 4) F4) :=
    fun g hg => isBlockDiag_of_mem_centralizer (hPC hg)
  have hne0 : ∀ l : Fin 4, l ≠ 0 → ext u 0 ≠ ext u l := by
    intro l hl
    fin_cases l
    · exact absurd rfl hl
    · exact h01
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [h2]
      exact h0
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [h3]
      exact h0
  have hne1 : ∀ l : Fin 4, l ≠ 1 → ext u 1 ≠ ext u l := by
    intro l hl
    fin_cases l
    · exact fun h => h01 h.symm
    · exact absurd rfl hl
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [h2]
      exact h1
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [h3]
      exact h1
  have he0 := entry_eq_one_of_isPerfect matL hP 0 fun g hg l hl => hbd g hg 0 l (hne0 l hl)
  have he1 := entry_eq_one_of_isPerfect matL hP 1 fun g hg l hl => hbd g hg 1 l (hne1 l hl)
  have hle : P ≤ ι23.range := by
    intro g hg
    rw [mem_range_ι23_iff]
    intro i j hij
    by_cases hij' : i = j
    · subst hij'
      have hi : i = 0 ∨ i = 1 := by
        rcases hij with hi | hi <;> fin_cases i <;> simp_all
      rw [Matrix.one_apply_eq]
      rcases hi with rfl | rfl
      · exact he0 g hg
      · exact he1 g hg
    · rw [Matrix.one_apply_ne hij']
      apply hbd g hg i j
      intro he
      rcases hij with hi | hj
      · have hi' : i = 0 ∨ i = 1 := by fin_cases i <;> simp_all
        rcases hi' with rfl | rfl
        · exact hne0 j (Ne.symm hij') he
        · exact hne1 j (Ne.symm hij') he
      · have hj' : j = 0 ∨ j = 1 := by fin_cases j <;> simp_all
        rcases hj' with rfl | rfl
        · exact hne0 i hij' he.symm
        · exact hne1 i hij' he.symm
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) F4) = 60 := by
    have := Fintype.ofFinite F4
    rw [Matrix.card_SL_field, Fintype.card_eq_nat_card, card_F4]
    norm_num [Fin.prod_univ_two]
  calc Nat.card P ≤ Nat.card ι23.range := Subgroup.card_le_of_le hle
    _ = Nat.card (SpecialLinearGroup (Fin 2) F4) :=
      (Nat.card_congr (MonoidHom.ofInjective ι23_injective).toEquiv).symm
    _ = 60 := hcard

theorem card_le_sixty_L44 {B P : Subgroup M} (hBA : B ≤ A0) (hB9 : Nat.card B = 9)
    (hPC : P ≤ Subgroup.centralizer (B : Set M)) (hP : Group.IsPerfect P) : Nat.card P ≤ 60 := by
  obtain ⟨x, y, hxB, hyB, hx0, hy0, hyx, hyxx⟩ := exists_basis_of_card_nine δ hBA hB9
  obtain ⟨a, b, hab⟩ := exists_twoZero x y hx0 hy0 hyx hyxx
  set w := (a : ℕ) • x + (b : ℕ) • y with hw
  have hwB : δ (Multiplicative.ofAdd w) ∈ B := by
    rw [hw, ofAdd_add, map_mul, δ_nsmul, δ_nsmul]
    exact B.mul_mem (B.pow_mem hxB _) (B.pow_mem hyB _)
  obtain ⟨σ, hσ2, hσ3, hσ0, hσ1, hσ01⟩ := exists_perm_twoZero w hab
  set φ := reindexSL (K := F4) σ
  have hsum : ∑ i, (ext w ∘ σ) i = 0 := by
    change ∑ i, ext w (σ i) = 0
    rw [Equiv.sum_comp σ (ext w)]
    exact sum_ext w
  set u := res (ext w ∘ σ) with hu
  have hext : ext u = ext w ∘ σ := ext_res hsum
  have hφw : φ (δ (Multiplicative.ofAdd w)) = δ (Multiplicative.ofAdd u) := reindexSL_δ σ w
  have hPC' : P.map φ.toMonoidHom ≤
      Subgroup.centralizer ({δ (Multiplicative.ofAdd u)} : Set M) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgw : δ (Multiplicative.ofAdd w) * g = g * δ (Multiplicative.ofAdd w) :=
      Subgroup.mem_centralizer_iff.mp (hPC hg) _ hwB
    change φ g * δ (Multiplicative.ofAdd u) = δ (Multiplicative.ofAdd u) * φ g
    rw [← hφw, ← map_mul, ← map_mul, hgw]
  let e : P ≃* P.map φ.toMonoidHom := Subgroup.equivMapOfInjective _ _ φ.injective
  have hP' : Group.IsPerfect (P.map φ.toMonoidHom) := by
    have := hP
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rw [Nat.card_congr e.toEquiv]
  refine card_le_sixty_of_std ?_ ?_ ?_ ?_ ?_ hPC' hP'
  · rw [hext]
    exact hσ2
  · rw [hext]
    exact hσ3
  · rw [hext]
    exact hσ0
  · rw [hext]
    exact hσ1
  · rw [hext]
    exact hσ01

theorem terminalRootSmallL44 {G : Type} [Group G] [Finite G] {I A B P : Subgroup G}
    (hAI : A ≤ I) (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 3 ^ 3)
    (eI : I ≃* projSL 4 (GaloisField 2 2)) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hPI : P ≤ I)
    (hPB : P ≤ Subgroup.centralizer (B : Set G)) (hP : Group.IsPerfect P) :
    Nat.card P ≤ 60 := by
  set e' : I ≃* M := eI.trans equivSL
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA27]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  set φ : I ≃* M := e'.trans (MulAut.conj x)
  have hφA : (A.subgroupOf I).map φ.toMonoidHom = A0 := by
    rw [← hx, Subgroup.map_map]
    rfl
  exact card_le_of_model φ hφA hBA hAI hPI hPB hP hB9
    fun B' P' hB' hB'9 hP'C hP' => card_le_sixty_L44 hB' hB'9 hP'C hP'

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof
