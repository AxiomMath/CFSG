module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.AllRootWeylSignsDefs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rootChar_mul_left {L : Type} [Field L]
    (a b : Fin Tag.E6.rank → Lˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one_left {L : Type} [Field L] (v : Fin Tag.E6.rank → ℤ) :
    rootChar (1 : Fin Tag.E6.rank → Lˣ) v = 1 := by
  simp [rootChar]

theorem rootChar_pow_left {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) (v : Fin Tag.E6.rank → ℤ) (n : ℕ) :
    rootChar (a ^ n) v = (rootChar a v) ^ n := by
  induction n with
  | zero => simp [rootChar_one_left]
  | succ n ih => rw [pow_succ, rootChar_mul_left, ih, pow_succ]

theorem rootChar_neg_left {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

@[expose] def charHom {L : Type} [Field L] (α : Fin Tag.E6.rank → ℤ) :
    (Fin Tag.E6.rank → Lˣ) →* Lˣ where
  toFun t := rootChar t α
  map_one' := rootChar_one_left α
  map_mul' a b := rootChar_mul_left a b α

@[expose] def charHomPair {L : Type} [Field L] (α β : Fin Tag.E6.rank → ℤ) :
    (Fin Tag.E6.rank → Lˣ) →* Lˣ × Lˣ where
  toFun t := (rootChar t α, rootChar t β)
  map_one' := by ext <;> simp [rootChar_one_left]
  map_mul' a b := by ext <;> simp [rootChar_mul_left]

theorem a1roots_char_eq_one {L : Type} [Field L]
    (t : Fin Tag.E6.rank → Lˣ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (hγ1 : rootChar t γ = 1) :
    ∀ δ ∈ ({γ, -γ} : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 δ ∧ rootChar t δ = 1 := by
  intro δ hδ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl
  · exact ⟨hγ, hγ1⟩
  · exact ⟨IsRoot.neg hγ, by rw [rootChar_neg_left, hγ1, inv_one]⟩

theorem a2roots_char_eq_one {L : Type} [Field L]
    (t : Fin Tag.E6.rank → Lˣ) {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hαβ : IsRoot .E6 (α + β))
    (hα1 : rootChar t α = 1) (hβ1 : rootChar t β = 1) :
    ∀ δ ∈ a2roots α β, IsRoot .E6 δ ∧ rootChar t δ = 1 := by
  intro δ hδ
  simp only [a2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hα, hα1⟩
  · exact ⟨IsRoot.neg hα, by rw [rootChar_neg_left, hα1, inv_one]⟩
  · exact ⟨hβ, hβ1⟩
  · exact ⟨IsRoot.neg hβ, by rw [rootChar_neg_left, hβ1, inv_one]⟩
  · exact ⟨hαβ, by rw [rootChar_add, hα1, hβ1, one_mul]⟩
  · exact ⟨IsRoot.neg hαβ,
      by rw [rootChar_neg_left, rootChar_add, hα1, hβ1, one_mul, inv_one]⟩

theorem findIdx_witnesses_eq_length
    {α : Fin Tag.E6.rank → ℤ} (hα : ¬ IsRoot .E6 α) :
    Tag.E6.witnesses.roots.findIdx (fun c => decide (decodeVec (τ := .E6) c = α)) =
      Tag.E6.witnesses.roots.length := by
  rw [List.findIdx_eq_length]
  intro c hc
  rw [decide_eq_false_iff_not]
  intro hdec
  obtain ⟨b, hb, hbc⟩ := List.getElem_of_mem hc
  rw [← hbc] at hdec
  have hroot := isRoot_decodeVec_witness (τ := .E6) (b := b) (by simpa using hb)
  rw [List.getD_eq_getElem _ _ hb] at hroot
  exact hα (hdec ▸ hroot)

theorem pinnedData_eq_default
    {α : Fin Tag.E6.rank → ℤ} (hα : ¬ IsRoot .E6 α) :
    pinnedData .E6 α = (0, [], 1) := by
  have hn1 : ¬ ∃ j, α = Pi.single j 1 := fun ⟨j, hj⟩ => hα (hj ▸ IsRoot.basis j)
  have hn2 : ¬ ∃ j, α = -Pi.single j 1 := fun ⟨j, hj⟩ => hα (hj ▸ IsRoot.neg (IsRoot.basis j))
  rw [pinnedData, dite_eq_right_of_eq_false (eq_false hn1),
    dite_eq_right_of_eq_false (eq_false hn2)]
  have hlen : Tag.E6.witnesses.roots.length = 72 := rfl
  have hseeds : Tag.E6.witnesses.seeds.length = 72 := rfl
  have hwords : Tag.E6.witnesses.words.length = 72 := rfl
  rw [findIdx_witnesses_eq_length hα]
  dsimp only
  have hs : Tag.E6.witnesses.seeds.getD Tag.E6.witnesses.roots.length 0 = 0 := by
    apply List.getD_eq_default
    rw [hseeds, hlen]
  have hw : Tag.E6.witnesses.words.getD Tag.E6.witnesses.roots.length 0 = 0 := by
    apply List.getD_eq_default
    rw [hwords, hlen]
  rw [hs, hw]
  simp [decodeWord, Tag.idx]

theorem pinnedX_eq_xUnit_zero
    {L : Type} [Field L] {α : Fin Tag.E6.rank → ℤ} (hα : ¬ IsRoot .E6 α) (c : L) :
    pinnedX .E6 L α c = xUnit .E6 L 0 c := by
  have hpd := pinnedData_eq_default hα
  rw [pinnedX, hpd]
  simp [pinnedWeyl, hpd]

theorem rootSubgroup_eq_of_not_isRoot
    {L : Type} [Field L] {α : Fin Tag.E6.rank → ℤ} (hα : ¬ IsRoot .E6 α) :
    rootSubgroup .E6 L α = rootSubgroup .E6 L (Pi.single (0 : Fin Tag.E6.rank) 1) := by
  have hf : pinnedX .E6 L α = pinnedX .E6 L (Pi.single (0 : Fin Tag.E6.rank) 1) := by
    funext c
    rw [pinnedX_eq_xUnit_zero hα c, pinnedX_single]
  rw [rootSubgroup, rootSubgroup, hf]

theorem rootSpan_pair_le_of_not_isRoot
    {L : Type} [Field L] {α : Fin Tag.E6.rank → ℤ} (hα : ¬ IsRoot .E6 α) :
    rootSpan .E6 L ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) ≤
      rootSpan .E6 L
        ({(Pi.single (0 : Fin Tag.E6.rank) 1), -(Pi.single (0 : Fin Tag.E6.rank) 1)} :
          Set (Fin Tag.E6.rank → ℤ)) := by
  rw [rootSpan, rootSpan]
  refine iSup₂_le fun δ hδ => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl
  · rw [rootSubgroup_eq_of_not_isRoot hα]
    exact le_iSup₂ (f := fun β (_ : β ∈
      ({(Pi.single (0 : Fin Tag.E6.rank) 1), -(Pi.single (0 : Fin Tag.E6.rank) 1)} : Set _)) =>
        rootSubgroup .E6 L β) _ (by simp)
  · rw [rootSubgroup_eq_of_not_isRoot (fun h => hα (by simpa using IsRoot.neg h))]
    exact le_iSup₂ (f := fun β (_ : β ∈
      ({(Pi.single (0 : Fin Tag.E6.rank) 1), -(Pi.single (0 : Fin Tag.E6.rank) 1)} : Set _)) =>
        rootSubgroup .E6 L β) _ (by simp)

theorem rootDiagUnit_mem_centralizer_of_char
    {L : Type} [Field L] {t : Fin Tag.E6.rank → Lˣ}
    {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E6 γ ∧ rootChar t γ = 1) :
    rootDiagUnit .E6 t ∈
      Subgroup.centralizer (rootSpan .E6 L S : Set (ModGL .E6 L)) := by
  have h : rootSpan .E6 L S ≤
      Subgroup.centralizer ({rootDiagUnit .E6 t} : Set (ModGL .E6 L)) :=
    rootSpan_le_centralizer t hS
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (h hy)

theorem comap_pow_three_eq_one
    {L : Type} [Field L]
    (B : Subgroup (ModGL .E6 L)) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (t : B.comap (rootDiagUnitHom .E6 L)) :
    (t : Fin Tag.E6.rank → Lˣ) ^ 3 = 1 := by
  have h : rootDiagUnitHom .E6 L ((t : Fin Tag.E6.rank → Lˣ) ^ 3) = 1 := by
    rw [map_pow]
    exact hB3 _ t.2
  exact rootDiagUnit_injective (h.trans (map_one (rootDiagUnitHom .E6 L)).symm)

theorem charHom_pow_three {L : Type} [Field L] (γ : Fin Tag.E6.rank → ℤ)
    {T : Subgroup (Fin Tag.E6.rank → Lˣ)}
    (hT3 : ∀ t : T, (t : Fin Tag.E6.rank → Lˣ) ^ 3 = 1) (t : T) :
    (charHom γ (t : Fin Tag.E6.rank → Lˣ)) ^ 3 = 1 := by
  show (rootChar (t : Fin Tag.E6.rank → Lˣ) γ) ^ 3 = 1
  rw [← rootChar_pow_left, hT3 t, rootChar_one_left]

theorem finite_inf_centralizer {L : Type} [Field L]
    (B J : Subgroup (ModGL .E6 L)) [Finite B] :
    Finite ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) :=
  Finite.of_injective
    (fun x : ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) =>
      (⟨x.1, x.2.1⟩ : B))
    (fun x y h => Subtype.ext (congrArg (fun z : B => (z : ModGL .E6 L)) h))

theorem card_le_mul_card_inf_centralizer
    {L : Type} [Field L] {G' : Type} [Group G']
    (B J : Subgroup (ModGL .E6 L)) [Finite B]
    (hBT : B ≤ torusGroup .E6 L)
    (T : Subgroup (Fin Tag.E6.rank → Lˣ))
    (hT : T = B.comap (rootDiagUnitHom .E6 L))
    (χ : T →* G')
    (n : ℕ) (hn : Nat.card χ.range ≤ n)
    (hker : ∀ t : T, χ t = 1 →
      rootDiagUnitHom .E6 L (t : Fin Tag.E6.rank → Lˣ) ∈
        B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) :
    Nat.card B ≤ n * Nat.card
      (B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) : Subgroup (ModGL .E6 L)) := by
  let f : (Fin Tag.E6.rank → Lˣ) →* ModGL .E6 L := rootDiagUnitHom .E6 L
  have hf : Function.Injective f := rootDiagUnit_injective
  have hTmap : T.map f = B := by
    rw [hT]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      obtain ⟨t, ht⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hBT hx)
      refine ⟨t, ?_, ht.symm⟩
      change rootDiagUnit .E6 t ∈ B
      rw [← ht]
      exact hx
  have hcardT : Nat.card T = Nat.card B := by
    rw [← hTmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective T f hf).toEquiv
  have hsplit : Nat.card χ.ker * Nat.card χ.range = Nat.card T :=
    Subgroup.card_ker_mul_card_range χ
  haveI : Finite ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) :=
    finite_inf_centralizer B J
  have hker' : Nat.card χ.ker ≤
      Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) := by
    have hinj : Function.Injective
        (fun t : χ.ker => (⟨f (t.1 : Fin Tag.E6.rank → Lˣ), hker t.1 t.2⟩ :
          ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))))) := by
      intro x y h
      have h' : f (x.1 : Fin Tag.E6.rank → Lˣ) = f (y.1 : Fin Tag.E6.rank → Lˣ) :=
        congrArg (fun z : ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) =>
          (z : ModGL .E6 L)) h
      exact Subtype.ext (Subtype.ext (hf h'))
    exact Nat.card_le_card_of_injective _ hinj
  calc Nat.card B = Nat.card T := hcardT.symm
    _ = Nat.card χ.ker * Nat.card χ.range := hsplit.symm
    _ ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) * n :=
        Nat.mul_le_mul hker' hn
    _ = n * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) := Nat.mul_comm _ _

theorem rank_one_bound
    {L : Type} [Field L] (B : Subgroup (ModGL .E6 L)) [Finite B]
    (hBT : B ≤ torusGroup .E6 L) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (γ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) :
    Nat.card B ≤ 3 * Nat.card
      (B ⊓ Subgroup.centralizer
        (rootSpan .E6 L ({γ, -γ} : Set (Fin Tag.E6.rank → ℤ)) : Set (ModGL .E6 L)) :
          Subgroup (ModGL .E6 L)) := by
  let f : (Fin Tag.E6.rank → Lˣ) →* ModGL .E6 L := rootDiagUnitHom .E6 L
  let T : Subgroup (Fin Tag.E6.rank → Lˣ) := B.comap f
  let χ : T →* Lˣ := (charHom γ).comp T.subtype
  have hT3 : ∀ t : T, (t : Fin Tag.E6.rank → Lˣ) ^ 3 = 1 :=
    fun t => comap_pow_three_eq_one B hB3 t
  have hrange : Nat.card χ.range ≤ 3 := by
    have hle : χ.range ≤ rootsOfUnity 3 L := by
      intro x hx
      obtain ⟨t, rfl⟩ := hx
      rw [mem_rootsOfUnity]
      exact charHom_pow_three γ hT3 t
    calc Nat.card χ.range ≤ Nat.card (rootsOfUnity 3 L) := Subgroup.card_le_of_le hle
      _ ≤ 3 := card_rootsOfUnity L 3
  have hker : ∀ t : T, χ t = 1 →
      rootDiagUnitHom .E6 L (t : Fin Tag.E6.rank → Lˣ) ∈
        B ⊓ Subgroup.centralizer
          (rootSpan .E6 L ({γ, -γ} : Set (Fin Tag.E6.rank → ℤ)) : Set (ModGL .E6 L)) := by
    intro t ht
    rw [Subgroup.mem_inf]
    refine ⟨t.2, ?_⟩
    have ht1 : rootChar (t : Fin Tag.E6.rank → Lˣ) γ = 1 := by
      simpa [χ, charHom] using ht
    exact rootDiagUnit_mem_centralizer_of_char
      (a1roots_char_eq_one (t : Fin Tag.E6.rank → Lˣ) hγ ht1)
  exact card_le_mul_card_inf_centralizer B
    (rootSpan .E6 L ({γ, -γ} : Set (Fin Tag.E6.rank → ℤ))) hBT T rfl χ 3 hrange hker

theorem rank_two_bound
    {L : Type} [Field L] (B : Subgroup (ModGL .E6 L)) [Finite B]
    (hBT : B ≤ torusGroup .E6 L) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (α β : Fin Tag.E6.rank → ℤ) (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hαβ : IsRoot .E6 (α + β)) :
    Nat.card B ≤ 9 * Nat.card
      (B ⊓ Subgroup.centralizer
        (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) :
          Subgroup (ModGL .E6 L)) := by
  let f : (Fin Tag.E6.rank → Lˣ) →* ModGL .E6 L := rootDiagUnitHom .E6 L
  let T : Subgroup (Fin Tag.E6.rank → Lˣ) := B.comap f
  let χ : T →* Lˣ × Lˣ := (charHomPair α β).comp T.subtype
  have hT3 : ∀ t : T, (t : Fin Tag.E6.rank → Lˣ) ^ 3 = 1 :=
    fun t => comap_pow_three_eq_one B hB3 t
  have hrange : Nat.card χ.range ≤ 9 := by
    have hle : χ.range ≤ (rootsOfUnity 3 L).prod (rootsOfUnity 3 L) := by
      intro x hx
      rw [Subgroup.mem_prod]
      obtain ⟨t, rfl⟩ := hx
      exact ⟨by rw [mem_rootsOfUnity]; exact charHom_pow_three α hT3 t,
        by rw [mem_rootsOfUnity]; exact charHom_pow_three β hT3 t⟩
    have hinj : Function.Injective (fun x : χ.range =>
        (Prod.mk (⟨x.1.1, (Subgroup.mem_prod.1 (hle x.2)).1⟩ : rootsOfUnity 3 L)
          (⟨x.1.2, (Subgroup.mem_prod.1 (hle x.2)).2⟩ : rootsOfUnity 3 L))) := by
      intro x y h
      have h1 : x.1.1 = y.1.1 := congrArg (fun z => (z.1 : Lˣ)) h
      have h2 : x.1.2 = y.1.2 := congrArg (fun z => (z.2 : Lˣ)) h
      exact Subtype.ext (Prod.ext h1 h2)
    have hcard : Nat.card χ.range ≤
        Nat.card (rootsOfUnity 3 L × rootsOfUnity 3 L) :=
      Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod] at hcard
    calc Nat.card χ.range
        ≤ Nat.card (rootsOfUnity 3 L) * Nat.card (rootsOfUnity 3 L) := hcard
      _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity L 3) (card_rootsOfUnity L 3)
      _ = 9 := rfl
  have hker : ∀ t : T, χ t = 1 →
      rootDiagUnitHom .E6 L (t : Fin Tag.E6.rank → Lˣ) ∈
        B ⊓ Subgroup.centralizer
          (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) := by
    intro t ht
    rw [Subgroup.mem_inf]
    refine ⟨t.2, ?_⟩
    have ht1 : rootChar (t : Fin Tag.E6.rank → Lˣ) α = 1 := by
      have h := congrArg Prod.fst ht
      simpa [χ, charHomPair] using h
    have ht2 : rootChar (t : Fin Tag.E6.rank → Lˣ) β = 1 := by
      have h := congrArg Prod.snd ht
      simpa [χ, charHomPair] using h
    exact rootDiagUnit_mem_centralizer_of_char
      (a2roots_char_eq_one (t : Fin Tag.E6.rank → Lˣ) hα hβ hαβ ht1 ht2)
  exact card_le_mul_card_inf_centralizer B
    (rootSpan .E6 L (a2roots α β)) hBT T rfl χ 9 hrange hker

end CFSG.StandardType
