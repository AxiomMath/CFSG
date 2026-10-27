module

public import CFSG.Quasithin.MS93.S34
import CFSG.Quasithin.MS93.S33SpCoord
import CFSG.Quasithin.MS93.RedHyp
import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.MS93.Sec2Gen

public section

namespace CFSG.Quasithin.MS93.S34R

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ Matrix
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

section Generic

variable {V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {β : ↥V →* Multiplicative (Fin 1 → ι → F)}

theorem exists_gl_of_linear (hβ : Function.Surjective β) (hβker : β.ker = Z.subgroupOf V)
    {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) {f : (ι → F) →+ (ι → F)}
    (hf : IsCoordAct β g f) (hlin : ∀ (c : F) (x : ι → F), f (c • x) = c • f x) :
    ∃ γ : GL ι F, IsCoordAct β g (γ : Matrix ι ι F).mulVec := by
  obtain ⟨f', hf'⟩ := exists_isCoordAct hβ hβker (inv_mem hgV) (inv_mem hgZ)
  have hinv := S33.coordMap_inv_comp' hβ hgV hf hf'
  have hlin' : ∀ (c : F) (x : ι → F), f' (c • x) = c • f' x := by
    intro c x
    have h1 : f (f' (c • x)) = f (c • f' x) := by rw [(hinv _).1, hlin, (hinv x).1]
    rw [← (hinv (f' (c • x))).2, h1, (hinv _).2]
  obtain ⟨A, hA⟩ := exists_matrix_of_linear hf hlin
  obtain ⟨B, hB⟩ := exists_matrix_of_linear hf' hlin'
  exact exists_gl_of_isCoordAct hβ hgV hA hB

variable [Nonempty ι]

end Generic

section Reduce

variable [Finite G] {M T L T₁ : Subgroup G}

theorem le_normalizer_sup_of_normal (h : PUHyp M T L)
    (hn : T ≤ Subgroup.normalizer (T₁ : Set G)) :
    M ≤ Subgroup.normalizer ((L ⊔ T₁ : Subgroup G) : Set G) := by
  rw [h.eq_sup]
  exact sup_le (le_sup_left.trans Subgroup.le_normalizer)
    (le_normalizer_sup (h.le.trans h.le_normalizer) hn)

theorem puHyp_sup_of_normal (h : PUHyp M T L) (hT₁ : T₁ ≤ T)
    (hn : T ≤ Subgroup.normalizer (T₁ : Set G)) (hQ : pCoreOf 2 M ≤ T₁)
    (hP : ∀ C : Subgroup G, C ≤ T₁ → C ≠ ⊥ → (C.subgroupOf T₁).Characteristic →
      ¬ L ⊔ T₁ ≤ Subgroup.normalizer (C : Set G)) : PUHyp (L ⊔ T₁) T₁ L where
  le := le_sup_right
  isPGroup := h.isPGroup.to_le hT₁
  ne_bot := h.ne_bot_of_inf_le (inf_le_right.trans hQ)
  noChar := hP
  pCore_le := (le_inf (pCoreOf_le' _) (pCoreOf_le_pCoreOf_of_le_normalizer (h.reduce_le hT₁)
    (le_normalizer_sup_of_normal h hn))).trans (inf_le_right.trans hQ)
  charTwo := CharTwo.of_normal h.charTwo (h.reduce_le hT₁)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (h.reduce_le hT₁)).2
      (le_normalizer_sup_of_normal h hn))
  L_le := le_sup_left
  le_normalizer := sup_le Subgroup.le_normalizer ((hT₁.trans h.le).trans h.le_normalizer)
  eq_sup := rfl
  perfect := h.perfect
  quasisimple := h.quasisimple
  rankTwo := h.rankTwo
  sqtk := B5.sqtk_of_le h.sqtk (h.reduce_le hT₁)

end Reduce

section LinPart

variable [Finite G] {M T L : Subgroup G}

abbrev linPart (h : PUHyp M T L) {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (β : ↥(Uq M T L) →* Multiplicative (Fin 1 → ι → F)) : Subgroup G :=
  coordGroup β ⊤ T (h.le.trans (le_normalizer_Uq h.le_normalizer))

theorem pCoreOf_le_linPart (h : PUHyp M T L) {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] (β : ↥(Uq M T L) →* Multiplicative (Fin 1 → ι → F)) :
    pCoreOf 2 M ≤ linPart h β := by
  intro q hq
  refine ⟨h.pCore_le hq, 1, fun u v huv => ?_⟩
  have hu : (u : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ (h.Uq_le_Xq u.2))
  have hvu : v = u := by
    apply Subtype.ext
    rw [huv, Subgroup.mem_centralizer_iff.1 hu q hq]
    group
  simp [hvu]

theorem sl3Full_of_le_linPart (h : PUHyp M T L) {n : ℕ} {F : Type} [Field F] [Fintype F]
    {α : ↥L →* ↥(StatedSL 3 F)} (hcard : Fintype.card F = 2 ^ n) (hα : Function.Surjective α)
    (hX : Xq M = Zq M L ⊔ Uq M T L) (hZU : Zq M L ⊓ Uq M T L = ⊥)
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)} (hβ : Function.Surjective β)
    (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (a : ↥L) (u v : ↥(Uq M T L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    (hT : T ≤ linPart h β) : IsSL3Full M T L :=
  h.sl3Full_of_gl hcard hα hX hZU hβ hβker hβα fun t ht => by
    obtain ⟨-, γ, hγ⟩ := hT ht
    exact ⟨γ, hγ⟩

theorem le_linPart_of_card_two (h : PUHyp M T L) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) {Z : Subgroup G}
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → ι → F)} (hβ : Function.Surjective β)
    (hβker : β.ker = Z.subgroupOf (Uq M T L))
    (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) : T ≤ linPart h β := by
  intro t ht
  obtain ⟨γ, hγ⟩ := exists_gl_of_card_two hF hβ hβker
    ((h.le.trans (le_normalizer_Uq h.le_normalizer)) ht) (hTZ ht)
  exact ⟨ht, ⟨γ, Subgroup.mem_top _⟩, hγ⟩

theorem card_eq_two_of_lt {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hcard : Fintype.card F = 2 ^ n) (hn : n < 2) : Fintype.card F = 2 := by
  rcases Nat.lt_succ_iff.1 hn |>.eq_or_lt with h1 | h0
  · rw [hcard, h1, pow_one]
  · have : n = 0 := by omega
    subst this
    have := Fintype.one_lt_card (α := F)
    omega

theorem sp4Full_of_le_linPart (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {α : ↥L →* ↥(StatedSp 2 F)} (hk : 2 ≤ k) (hcard : Fintype.card F = 2 ^ k)
    (hα : Function.Surjective α) (hLV : L ≤ Subgroup.normalizer (Uq M T L : Set G))
    (hZV : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ Uq M T L)
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)} (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L))
    (hβα : ∀ (a : ↥L) (u v : ↥(Uq M T L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i))
    (hT : T ≤ linPart h β) : IsSp4Full M T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hβα' : ∀ a : ↥L, IsCoordAct β a ((α a : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec := by
    intro a u v huv
    simpa [moduleAct] using hβα a u v huv 0
  have hTsp : ∀ t ∈ T, ∃ γ : ↥(StatedSp 2 F), IsCoordAct β t ((γ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec := by
    intro t ht
    obtain ⟨-, γ, hγ⟩ := hT ht
    obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
    have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    exact exists_sp4_of_gl hα hLV hβ hβα' (hTV ht) (h.le_normalizer (h.le ht)) he' hγ
  obtain ⟨α', hα', hnat⟩ := exists_natural_of_coordAct h.eq_sup hα hLV hZV hβ hβker hβα hTV hTsp
  exact ⟨k, F, inferInstance, inferInstance, α', by omega, hcard, hα', hnat⟩

end LinPart

end CFSG.Quasithin.MS93.S34R
