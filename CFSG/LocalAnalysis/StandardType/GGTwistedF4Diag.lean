module

public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagCore
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open TableB (markDiag largeEvenDiagMap_eq_markDiag)

namespace TwistedF4Diag

section RootSet

variable (K : Type) [Field K] (a : ℕ)

@[expose] def TwF4DiagRealizedOn (S : (Fin 4 → ℤ) → Prop) : Prop :=
  ∀ b : Fin 4 → Kˣ,
    (∀ h ∈ MarkChev.twF4H S a K, ∃ h' ∈ MarkChev.twF4H S a K,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K b = markDiag S K b * h) →
    ∃ g ∈ MarkChev.twF4H S a K, (g : Module.End K (MarkChev.Space S K)) = markDiag S K b

variable {K a}

theorem ggDiagRealizedInput_of_twF4DiagRealizedOn
    (h : TwF4DiagRealizedOn K a (LargeEvenIsRoot LargeEvenCartanF4)) :
    GGDiagRealizedInput LargeEvenCartanF4 K (LargeEvenTwF4H a K) := by
  rw [largeEvenTwF4H_eq]
  have hd : ∀ b, (TableB.diagHom LargeEvenCartanF4 K b :
      Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        markDiag (LargeEvenIsRoot LargeEvenCartanF4) K b := fun b => by
    rw [TableB.coe_diagHom, largeEvenDiagMap_eq_markDiag]
  have hrel : ∀ b, (∀ x ∈ MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K,
      TableB.diagHom LargeEvenCartanF4 K b * x * (TableB.diagHom LargeEvenCartanF4 K b)⁻¹ ∈
        MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K) →
      ∀ x ∈ MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K,
        ∃ x' ∈ MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K,
          (x' : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) *
              markDiag (LargeEvenIsRoot LargeEvenCartanF4) K b =
            markDiag (LargeEvenIsRoot LargeEvenCartanF4) K b * x := by
    intro b hb x hx
    refine ⟨_, hb x hx, ?_⟩
    rw [← largeEvenDiagMap_eq_markDiag]
    exact (TableB.diag_rel_iff b x _).2 rfl
  have hmem : ∀ {b} {g : LargeEvenChevGL LargeEvenCartanF4 K},
      (g : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        markDiag (LargeEvenIsRoot LargeEvenCartanF4) K b →
          g = TableB.diagHom LargeEvenCartanF4 K b := fun hg => Units.ext (by rw [hg, hd])
  intro b hb
  obtain ⟨g, hg, hgd⟩ := h b (hrel b hb)
  rw [← hmem hgd]
  exact hg

theorem TwF4DiagRealizedOn.of_eq {S S' : (Fin 4 → ℤ) → Prop} (hS : S = S')
    (h : TwF4DiagRealizedOn K a S) : TwF4DiagRealizedOn K a S' :=
  hS ▸ h

theorem markDiag_isRoot_F4 (b : Fin 4 → Kˣ) :
    markDiag (r := 4) (IsRoot .F4) K b = rootDiag (τ := ReeTag.F4.tag) b :=
  TableB.TwE6.markDiag_isRoot (τ := Tag.F4) b

end RootSet


section Ree

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem twF4H_isRoot_eq_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    MarkChev.twF4H (IsRoot .F4) a K = ReeTag.F4.reeGamma K a := by
  have h2 : ReeTag.F4.reeGamma K a = reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) :=
    ReeTag.reeGamma_eq_reeFixedGroup
  have h3 := RecipeExcLang.commutator_self_eq_of_commutator_eq_top
    (ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) ha hK)
  have h4 : ⁅reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)), reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆ =
      ⁅ReeTag.F4.reeGamma K a, ReeTag.F4.reeGamma K a⁆ := by
    rw [h2]
    rfl
  exact (twF4H_eq_commutator K a).trans (h4.trans h3)

theorem twF4DiagRealizedOn_isRoot (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    TwF4DiagRealizedOn K a (IsRoot .F4) := by
  intro b hb
  rw [twF4H_isRoot_eq_reeGamma ha hK] at hb ⊢
  have hconj : ∀ g ∈ ReeTag.F4.reeGamma K a, rootDiagUnit ReeTag.F4.tag b * g *
      (rootDiagUnit ReeTag.F4.tag b)⁻¹ ∈ ReeTag.F4.reeGamma K a := by
    intro g hg
    obtain ⟨h', hh', e⟩ := hb g hg
    rw [markDiag_isRoot_F4] at e
    rw [← TableB.TwE6.eq_conj_of_mul_rootDiag (τ := ReeTag.F4.tag) e]
    exact hh'
  exact ⟨_, rootDiagUnit_mem_reeGamma_of_forall_conj_mem hK hconj, (markDiag_isRoot_F4 b).symm⟩

end Ree

end TwistedF4Diag

open TwistedF4Diag

section Main


theorem ggDiagRealizedInput_twF4 {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGDiagRealizedInput LargeEvenCartanF4 K (LargeEvenTwF4H a K) := by
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  exact ggDiagRealizedInput_of_twF4DiagRealizedOn
    ((twF4DiagRealizedOn_isRoot ha hK).of_eq (largeEvenIsRoot_eq_isRoot .F4).symm)

theorem ggTwistedF4DiagInput_holds : GGTwistedF4DiagInput :=
  fun _ ha K _ _ hK _ => ggDiagRealizedInput_twF4 ha K hK

theorem chevIDImage_subset_inn_twF4 {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H a K) →*
        MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))).range :=
  chevIDImage_subset_inn (ggDiagRealizedInput_twF4 ha K hK)

theorem largeEvenLabelAll_subset_inn_twF4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, h3⟩ := hl
  intro Q hQ
  exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)
    (fun K _ _ hK _ _ φ hφ => chevIDImage_subset_inn_twF4 (by omega) K hK hφ) hQ

end Main

end CFSG.StandardType
