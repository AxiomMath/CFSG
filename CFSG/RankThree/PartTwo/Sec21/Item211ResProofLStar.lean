module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofLStarAlg
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
public import Certificates.Certificate3169
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.LieType.CurtisTits.Recognition
import CFSG.Sporadic.J3
import CFSG.CharacterTheory.Semidihedral.NormalForm
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

open CFSG.Blueprint
open Item2130SplitProof Item2130LStarProof

variable {G : Type} [Group G]

@[expose] def Case2130 (A L : Subgroup G) : Prop :=
  (Nonempty (lBar L ≃* NativeSporadic.M22) ∧ Nat.card A = 3 ^ 3 ∧
    Nonempty (starOf A L ≃* QuaternionGroup 2)) ∨
  ((Nonempty (lBar L ≃* NativeSporadic.M23) ∨ Nonempty (lBar L ≃* NativeSporadic.HS)) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* CFSG.Open.SemidihedralGroup 4)) ∨
  (((∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (lBar L ≃* projSU 4 2 n))) ∨
      Nonempty (lBar L ≃* projSU 5 2 2)) ∧
    Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
  ((∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n)) ∧ Nat.card A = 3 ^ 4 ∧
    Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)))

section Certs


@[expose] def Item2130LStarInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    Case2130 A L → c ∉ L ∧ Nat.card A = 3 * Nat.card (A ⊓ L : Subgroup G)

end Certs

namespace Item2130LStarProof

theorem exists_lift {A X : Subgroup G} {φ : MulAut A} (hφ : φ ∈ starOf A X) :
    ∃ x : Subgroup.normalizer (A : Set G), (x : G) ∈ X ∧ A.normalizerMonoidHom x = φ := by
  obtain ⟨x, hx, rfl⟩ := hφ
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

theorem sameOn_of_eq {A : Subgroup G} {x y : Subgroup.normalizer (A : Set G)}
    (h : A.normalizerMonoidHom x = A.normalizerMonoidHom y) : SameOn A x y := fun a ha =>
  congrArg Subtype.val (congrArg (fun φ : MulAut A => φ ⟨a, ha⟩) h)

theorem eq_of_sameOn {A : Subgroup G} {x y : Subgroup.normalizer (A : Set G)}
    (h : SameOn A x y) : A.normalizerMonoidHom x = A.normalizerMonoidHom y :=
  MulEquiv.ext fun a => Subtype.ext (h a a.2)

theorem sameOn_one_of_sup {A B : Subgroup G} {c ℓ : G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hcA : c ∈ A) (hAB : A = Subgroup.zpowers c ⊔ B) (hℓc : ℓ * c * ℓ⁻¹ = c)
    (hℓB : SameOn B ℓ 1) : SameOn A ℓ 1 := by
  rw [sameOn_one_iff] at hℓB ⊢
  intro a ha
  obtain ⟨i, -, b, hb, rfl⟩ := Sec13.exists_pow_mul_of_mem hA hcA hAB ha
  have hci : ℓ * c ^ i * ℓ⁻¹ = c ^ i := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hℓc]
  calc ℓ * (c ^ i * b) * ℓ⁻¹ = (ℓ * c ^ i * ℓ⁻¹) * (ℓ * b * ℓ⁻¹) := by group
    _ = c ^ i * b := by rw [hci, hℓB b hb]

end Item2130LStarProof

open Item2130LStarProof

theorem center_eq_bot_of_isSimpleGroup' {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Y :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hY (Group.is_simple_iff_prime_card.mp inferInstance)

theorem false_of_J3 {L : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (hJ3 : IsEmpty (L ⧸ Subgroup.center L ≃* NativeSporadic.J3))
    (hJ : Nonempty (lBar L ≃* NativeSporadic.J3) ∨
      Sec4.IsTripleCover (lBar L) NativeSporadic.J3) : False := by
  have hJnt : Nontrivial NativeSporadic.J3 := CFSG.Sporadic.J3.fam_j3_simplicity.2.1
  set φ : L →* lBar L := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hnt : Nontrivial (lBar L) := by
    rcases hJ with e | ⟨-, e⟩
    · obtain ⟨e⟩ := e
      exact e.toEquiv.nontrivial
    · obtain ⟨e⟩ := e
      have : Nontrivial (lBar L ⧸ Subgroup.center (lBar L)) := e.toEquiv.nontrivial
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      have := hcon
      have := (QuotientGroup.mk'_surjective (Subgroup.center (lBar L))).subsingleton
      exact not_subsingleton _ this
  have hφ : ∃ k, φ k ≠ 1 := by
    obtain ⟨y, hy⟩ := exists_ne (1 : lBar L)
    obtain ⟨k, rfl⟩ := hsurj y
    exact ⟨k, hy⟩
  have hker := LieType.CurtisTits.ker_le_center_of_isQuasisimple hL hφ
  let e₁ := LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hL hsurj hker
  rcases hJ with e | ⟨-, e⟩
  · obtain ⟨e⟩ := e
    have := CFSG.Sporadic.J3.isSimpleGroup_J3
    have hcenJ : Subgroup.center NativeSporadic.J3 = ⊥ := center_eq_bot_of_isSimpleGroup' (by
      rw [CFSG.Sporadic.J3.card_J3]
      norm_num)
    have hcen : Subgroup.center (lBar L) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ Subgroup.center NativeSporadic.J3 := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
      rw [hcenJ, Subgroup.mem_bot] at hz'
      rw [Subgroup.mem_bot]
      exact e.injective (by rw [hz', map_one])
    exact hJ3.false (e₁.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot.trans e)))
  · obtain ⟨e⟩ := e
    exact hJ3.false (e₁.trans e)

theorem case2130_of (h211 : Item211) (h213 : Item213)
    (h217 : Item217) (h218 : Item218) (h2116 : Item2116) (h2117 : Item2117) (h2118 : Item2118)
    (h2119 : Item2119) {G : Type} [Group G] [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hred : ¬ IsIrreducibleOn (wStar A)) : Case2130 A L := by
  obtain ⟨hM24, hHe, hJ2, hRu, hJ4, hG2, hD4⟩ := h218 G A E U c L hpair
  rcases h211 G A E U c L hpair with ⟨-, hT, -⟩ | ⟨hM, h27, hQ⟩ | ⟨hM, h27, hSD⟩ |
      ⟨hM, -, -⟩ | ⟨hJ, -, -⟩ | ⟨hM, -, -⟩ | ⟨⟨n, -, -, h7⟩, -, -⟩ | ⟨⟨n, -, -, h8⟩, -, -⟩ |
      ⟨h9, h27, hD8⟩ | ⟨h10, h81, hS4⟩ | ⟨hJ, -, -⟩ | ⟨h12, -, -⟩ | ⟨h13, -, -⟩
  · exact absurd hT (h2117 G A E U c L hpair)
  · exact Or.inl ⟨hM, h27, hQ⟩
  · exact Or.inr (Or.inl ⟨hM, h27, hSD⟩)
  · rcases hM with e | e
    · exact (e.elim hM24.false).elim
    · exact (e.elim hHe.false).elim
  · exact (hJ.elim hJ2.false).elim
  · rcases hM with e | e
    · exact (e.elim hRu.false).elim
    · exact (e.elim hJ4.false).elim
  · rcases h7 with ⟨hL3, -⟩ | ⟨hSL3, -⟩
    · exact absurd (h2119 G A E U c L hpair ⟨n, hL3⟩) hred
    · exact absurd (h2118 G A E U c L hpair ⟨n, hSL3⟩) hred
  · rcases h8 with h | h
    · exact absurd h (hG2 n)
    · exact absurd h (hD4 n)
  · exact Or.inr (Or.inr (Or.inl ⟨h9, h27, hD8⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h10, h81, hS4⟩))
  · exact (false_of_J3 (h213 G A E U c L hpair) (h217 G A E U c L hpair) hJ).elim
  · exact absurd (h12.elim Or.inl (fun h => Or.inr (Or.inl h))) (h2116 G A E U c L hpair)
  · exact absurd (Or.inr (Or.inr h13)) (h2116 G A E U c L hpair)

namespace Item2130LStarProof

theorem elemAbelian_of_le {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) : CFSG.Assembly.IsElemAbelian 3 B := CFSG.Open.IsElemAbelian.mono hA hBA

@[expose] def permS : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def permT : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def permG : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem perm_relations : permS * permS = 1 ∧ permT * permT = 1 ∧ permS * permT = permT * permS ∧
    permS ≠ 1 ∧ permT ≠ 1 ∧ permS * permT ≠ 1 ∧ permG * permG * permG = 1 ∧
    permG * permS * permG⁻¹ = permT ∧ permG * permT * permG⁻¹ = permS * permT := by
  decide

theorem eq_bot_or_eq_of_order_four [Finite G] {A B L X : Subgroup G} {c : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hAB : A = Subgroup.zpowers c ⊔ B)
    (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hLc : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ = c)
    (hKB : L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    {φ : MulAut A} (hφ : φ ∈ starOf A L) (h4 : φ ^ 4 = 1) (h2 : φ ^ 2 ≠ 1) (hXB : X ≤ B)
    (hKX : L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = ⊥ ∨ X = B := by
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := elemAbelian_of_le hA hBA
  obtain ⟨ℓ', hℓL, hℓφ⟩ := exists_lift hφ
  have hℓK : (ℓ' : G) ∈ L ⊓ Subgroup.normalizer (A : Set G) := ⟨hℓL, ℓ'.2⟩
  have hpowK : ∀ n : ℕ, (ℓ' : G) ^ n ∈ L ⊓ Subgroup.normalizer (A : Set G) := fun n =>
    Subgroup.pow_mem _ hℓK n
  set τ : MulAut B := B.normalizerMonoidHom ⟨ℓ', hKB hℓK⟩ with hτ
  have hτpow : ∀ n : ℕ, τ ^ n = B.normalizerMonoidHom ⟨(ℓ' : G) ^ n, hKB (hpowK n)⟩ := by
    intro n
    rw [hτ, ← map_pow]
    rfl
  have hφpow : ∀ n : ℕ, φ ^ n = A.normalizerMonoidHom (ℓ' ^ n) := by
    intro n
    rw [← hℓφ, map_pow]
  have h4' : τ ^ 4 = 1 := by
    rw [hτpow, ← map_one B.normalizerMonoidHom]
    apply eq_of_sameOn
    have := sameOn_of_eq (x := ℓ' ^ 4) (y := 1) (by rw [← hφpow, h4, map_one])
    exact this.mono hBA
  have h2' : τ ^ 2 ≠ 1 := by
    intro h
    apply h2
    rw [hφpow, ← map_one A.normalizerMonoidHom]
    apply eq_of_sameOn
    have hB : SameOn B ((ℓ' : G) ^ 2) 1 :=
      sameOn_of_eq (x := ⟨(ℓ' : G) ^ 2, hKB (hpowK 2)⟩) (y := 1) (by rw [← hτpow, h, map_one])
    exact sameOn_one_of_sup hA hcA hAB (hLc _ (hpowK 2).1) hB
  set T : Subgroup (MulAut B) :=
    ((L ⊓ Subgroup.normalizer (A : Set G)).subgroupOf (Subgroup.normalizer (B : Set G))).map
      B.normalizerMonoidHom
  have hτT : τ ∈ T := ⟨⟨ℓ', hKB hℓK⟩, hℓK, rfl⟩
  have hirr := Sec13.isIrreducibleOn_of_order_four hBe hB9 hτT h4' h2'
  have hinv : ∀ ψ ∈ T, (X.subgroupOf B).map ψ.toMonoidHom = X.subgroupOf B := by
    rintro _ ⟨⟨k, hkB⟩, hk, rfl⟩
    have hkX := hKX (Subgroup.mem_subgroupOf.mp hk)
    have hkX' := hKX (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp hk))
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨z, hz⟩, hzX, hzy⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hzX
      rw [Subgroup.mem_subgroupOf]
      have : k * z * k⁻¹ = y := congrArg Subtype.val hzy
      change y ∈ X
      rw [← this]
      exact (Subgroup.mem_normalizer_iff.mp hkX z).mp hzX
    · intro hyX
      rw [Subgroup.mem_subgroupOf] at hyX
      have hyB' : k⁻¹ * y * k⁻¹⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ hkB) y).mp hy
      refine ⟨⟨k⁻¹ * y * k⁻¹⁻¹, hyB'⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_normalizer_iff.mp hkX' y).mp hyX
      · apply Subtype.ext
        change k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y
        group
  rcases hirr _ hinv with h0 | ht
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact (disjoint_iff.mp h0 ▸ (inf_eq_left.mpr hXB)).symm
  · right
    exact le_antisymm hXB (Subgroup.subgroupOf_eq_top.mp ht)

theorem eq_bot_or_eq_of_perm [Finite G] {A B L X : Subgroup G} {c : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hAB : A = Subgroup.zpowers c ⊔ B)
    (hBA : B ≤ A) (hB27 : Nat.card B = 27) (hLc : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ = c)
    (hKB : L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G))
    (e : starOf A L ≃* Equiv.Perm (Fin 4)) (hXB : X ≤ B)
    (hKX : L ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = ⊥ ∨ X = B := by
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := elemAbelian_of_le hA hBA
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := perm_relations
  set φ : Equiv.Perm (Fin 4) →* MulAut A := (starOf A L).subtype.comp e.symm.toMonoidHom
  have hφinj : Function.Injective φ := (starOf A L).subtype_injective.comp e.symm.injective
  have hφmem : ∀ x, φ x ∈ starOf A L := fun x => (e.symm x).2
  obtain ⟨ls, hlsL, hls⟩ := exists_lift (hφmem permS)
  obtain ⟨lt, hltL, hlt⟩ := exists_lift (hφmem permT)
  obtain ⟨lg, hlgL, hlg⟩ := exists_lift (hφmem permG)
  set nmh := A.normalizerMonoidHom
  have rel : ∀ (x y : Subgroup.normalizer (A : Set G)), nmh x = nmh y → SameOn B x y :=
    fun x y h => (sameOn_of_eq h).mono hBA
  have hK : ∀ x : Subgroup.normalizer (A : Set G), (x : G) ∈ L →
      (x : G) ∈ L ⊓ Subgroup.normalizer (A : Set G) := fun x hx => ⟨hx, x.2⟩
  have nontriv : ∀ (x : Subgroup.normalizer (A : Set G)), (x : G) ∈ L → nmh x ≠ 1 →
      ¬ SameOn B x 1 := by
    intro x hxL hx h
    apply hx
    rw [← map_one nmh]
    exact eq_of_sameOn (x := x) (y := 1) (sameOn_one_of_sup hA hcA hAB (hLc _ hxL) h)
  have hA4 : A4On B ls lt lg := by
    refine
      { hs := hKB (hK ls hlsL), ht := hKB (hK lt hltL), hg := hKB (hK lg hlgL)
        s2 := rel (ls * ls) 1 ?_, t2 := rel (lt * lt) 1 ?_, st := rel (ls * lt) (lt * ls) ?_
        s1 := nontriv ls hlsL ?_, t1 := nontriv lt hltL ?_
        st1 := nontriv (ls * lt) (L.mul_mem hlsL hltL) ?_
        g3 := rel (lg * lg * lg) 1 ?_, gs := rel (lg * ls * lg⁻¹) lt ?_
        gt := rel (lg * lt * lg⁻¹) (ls * lt) ?_ }
    · rw [map_mul, hls, ← map_mul, r1, map_one, map_one]
    · rw [map_mul, hlt, ← map_mul, r2, map_one, map_one]
    · rw [map_mul, map_mul, hls, hlt, ← map_mul, ← map_mul, r3]
    · rw [hls, ← map_one φ]
      exact fun h => r4 (hφinj h)
    · rw [hlt, ← map_one φ]
      exact fun h => r5 (hφinj h)
    · rw [map_mul, hls, hlt, ← map_mul, ← map_one φ]
      exact fun h => r6 (hφinj h)
    · rw [map_mul, map_mul, hlg, ← map_mul, ← map_mul, r7, map_one, map_one]
    · rw [map_mul, map_mul, map_inv, hlg, hls, hlt, ← map_inv, ← map_mul, ← map_mul, r8]
    · rw [map_mul, map_mul, map_inv, map_mul, hlg, hls, hlt, ← map_inv, ← map_mul, ← map_mul,
        ← map_mul, r9]
  exact hA4.eq_bot_or_eq hBe hB27 hXB (hKX (hK ls hlsL)) (hKX (hK lt hltL)) (hKX (hK lg hlgL))

end Item2130LStarProof

section Certs


theorem item2130LStar_of (h211 : Item211) (h213 : Item213)
    (h217 : Item217) (h218 : Item218) (h2116 : Item2116) (h2117 : Item2117) (h2118 : Item2118)
    (h2119 : Item2119) (hNF : Item211NoField) (hInner : Item2130LStarInner) :
    Item2130LStar := by
  intro G _ _ A E U c L hpair hred
  have hcase := case2130_of h211 h213 h217 h218 h2116 h2117 h2118 h2119 hpair hred
  have hA2781 : Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4 := by
    rcases hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hcL, hcard⟩ := hInner G A E U c L hpair (hNF G A E U c L hpair hA2781) hcase
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := hpairs.2.2.1.1
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hLc : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ = c := fun ℓ hℓ => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hℓ), mul_inv_cancel_right]
  have hBA : A ⊓ L ≤ A := inf_le_left
  have hcB : c ∉ A ⊓ L := fun h => hcL h.2
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA hBA hcB hcard
  have hKB : L ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hk.2 x]
    constructor
    · rintro ⟨hxA, hxL⟩
      exact ⟨hxA, L.mul_mem (L.mul_mem hk.1 hxL) (L.inv_mem hk.1)⟩
    · rintro ⟨hxA, hxL⟩
      refine ⟨hxA, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hk.1) hxL) hk.1
      simpa [mul_assoc] using this
  refine ⟨hcL, hcard, ?_, ?_, fun X hXB hKX => ?_⟩
  · rcases hA2781 with h | h <;> omega
  · rcases hA2781 with h | h <;> omega
  ·
    have h4Q : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 :=
      QuaternionGroup.orderOf_a_one
    have h4D : orderOf (DihedralGroup.r 1 : DihedralGroup 4) = 4 := DihedralGroup.orderOf_r_one
    have h8 : orderOf (CFSG.Semidihedral.r 4) = 8 := by
      rw [CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
      rfl
    have h4S : orderOf (CFSG.Semidihedral.r 4 ^ 2) = 4 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [h8]; norm_num), h8]
    have use4 : ∀ {H : Type} [Group H] (e : starOf A L ≃* H) (x : H), orderOf x = 4 →
        Nat.card (A ⊓ L : Subgroup G) = 9 → X = ⊥ ∨ X = A ⊓ L := by
      intro H _ e x hx h9
      have hφ : ((e.symm x : starOf A L) : MulAut A) ∈ starOf A L := (e.symm x).2
      have hord : orderOf ((e.symm x : starOf A L) : MulAut A) = 4 := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
      refine eq_bot_or_eq_of_order_four hA hcA hAB hBA h9 hLc hKB hφ ?_ ?_ hXB hKX
      · rw [← hord]
        exact pow_orderOf_eq_one _
      · intro h2
        have := orderOf_dvd_of_pow_eq_one h2
        rw [hord] at this
        norm_num at this
    rcases hcase with ⟨-, h27, he⟩ | ⟨-, h27, he⟩ | ⟨-, h27, he⟩ | ⟨-, h81, he⟩
    · obtain ⟨e⟩ := he
      exact use4 e _ h4Q (by rw [h27] at hcard; omega)
    · obtain ⟨e⟩ := he
      exact use4 e _ h4S (by rw [h27] at hcard; omega)
    · obtain ⟨e⟩ := he
      exact use4 e _ h4D (by rw [h27] at hcard; omega)
    · obtain ⟨e⟩ := he
      exact eq_bot_or_eq_of_perm hA hcA hAB hBA (by rw [h81] at hcard; omega) hLc hKB e hXB hKX

end Certs

end CFSG.RankThree.PartTwo.Sec21
