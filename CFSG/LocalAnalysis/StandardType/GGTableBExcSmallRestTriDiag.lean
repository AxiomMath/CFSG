module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestBasic
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open TableB (markDiag largeEvenDiagMap_eq_markDiag)

namespace TableBExcSmallRest

section RootSet

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ) (K : Type)
  [Field K]

@[expose] def DiagRealizedOn (S : (Fin r → ℤ) → Prop) : Prop :=
  ∀ a : Fin r → Kˣ,
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K a = markDiag S K a * h) →
    ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K a

variable {A ρ n K}

theorem ggDiagRealizedInput_of_diagRealizedOn (h : DiagRealizedOn A ρ n K (LargeEvenIsRoot A)) :
    GGDiagRealizedInput A K (LargeEvenTwistedH A K ρ n) := by
  rw [largeEvenTwistedH_eq]
  have hd : ∀ b, (TableB.diagHom A K b : Module.End K (LargeEvenChevModule A K)) =
      markDiag (LargeEvenIsRoot A) K b := fun b => by
    rw [TableB.coe_diagHom, largeEvenDiagMap_eq_markDiag]
  have hrel : ∀ b, (∀ x ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n,
      TableB.diagHom A K b * x * (TableB.diagHom A K b)⁻¹ ∈
        MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n) →
      ∀ x ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n,
        ∃ x' ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n,
          (x' : Module.End K (LargeEvenChevModule A K)) * markDiag (LargeEvenIsRoot A) K b =
            markDiag (LargeEvenIsRoot A) K b * x := by
    intro b hb x hx
    refine ⟨_, hb x hx, ?_⟩
    rw [← largeEvenDiagMap_eq_markDiag]
    exact (TableB.diag_rel_iff b x _).2 rfl
  have hmem : ∀ {b} {g : LargeEvenChevGL A K},
      (g : Module.End K (LargeEvenChevModule A K)) = markDiag (LargeEvenIsRoot A) K b →
        g = TableB.diagHom A K b := fun hg => Units.ext (by rw [hg, hd])
  intro a ha
  obtain ⟨g, hg, hgd⟩ := h a (hrel a ha)
  rw [← hmem hgd]
  exact hg

theorem DiagRealizedOn.of_eq {S S' : (Fin r → ℤ) → Prop} (hS : S = S')
    (h : DiagRealizedOn A ρ n K S) : DiagRealizedOn A ρ n K S' :=
  hS ▸ h

end RootSet

theorem rootDiagUnit_mem_graphFixedRootGroup_D4 {K : Type} [Field K] [Finite K]
    (hchar : ringChar K = 2) (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {b : Fin TwistTag.D4.tag.rank → Kˣ}
    (h : ∀ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      rootDiagUnit TwistTag.D4.tag b * g * (rootDiagUnit TwistTag.D4.tag b)⁻¹ ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    rootDiagUnit TwistTag.D4.tag b ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hc : ∀ i, b (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (b i) :=
    fun i => TableB.TwE6.compat_of_forall_conj_mem h i
  have hF : twistHom TwistTag.D4 K σ.toRingHom (rootDiagUnit TwistTag.D4.tag b) =
      rootDiagUnit TwistTag.D4.tag b := by
    rw [twistHom_rootDiagUnit_eq]
    congr 1
    funext i
    rw [← hc (TwistTag.D4.perm.symm i), Equiv.apply_symm_apply]
  have hT := (even_power_two_Cartan_root_diagonals_inner Tag.D4 (Or.inr (Or.inr (Or.inl rfl)))
    K hchar).1 b
  have hle : torusGroup TwistTag.D4.tag K ≤ adjointGroup TwistTag.D4.tag K :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  have hadj : rootDiagUnit TwistTag.D4.tag b ∈ adjointGroup TwistTag.D4.tag K := hle hT
  have hΓ : rootDiagUnit TwistTag.D4.tag b ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).2 ⟨hadj, hF⟩
  rwa [(even_triality_fixed_group_eq_root_group K hchar σ hσ3).1] at hΓ

theorem diagRealizedOn_isRoot_D4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    DiagRealizedOn TwistTag.D4.tag.cartan TwistTag.D4.perm n K (IsRoot TwistTag.D4.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, hcomm, -, -⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have hC : MarkChev.twistedH TwistTag.D4.tag.cartan (IsRoot TwistTag.D4.tag) K TwistTag.D4.perm
      n = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [twistedH_eq_commutator K .D4 n σ.toRingHom hσ]
    exact hcomm
  intro a ha
  rw [hC] at ha ⊢
  have hconj : ∀ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      rootDiagUnit TwistTag.D4.tag a * g * (rootDiagUnit TwistTag.D4.tag a)⁻¹ ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro g hg
    obtain ⟨h', hh', e⟩ := ha g hg
    rw [TableB.TwE6.markDiag_isRoot] at e
    rw [← TableB.TwE6.eq_conj_of_mul_rootDiag e]
    exact hh'
  exact ⟨_, rootDiagUnit_mem_graphFixedRootGroup_D4 (K := K) (ringChar.eq K 2) σ
    (ringEquiv_cube_apply_eq hK hσ) hconj, (TableB.TwE6.markDiag_isRoot a).symm⟩

theorem ggTwistedD4DiagInput_holds : GGTwistedD4DiagInput := by
  intro n hn K _ _ hK _
  exact ggDiagRealizedInput_of_diagRealizedOn
    ((diagRealizedOn_isRoot_D4 hn hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag).symm)

theorem chevIDImage_subset_inn_triD4 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    LargeEvenChevIDImage LargeEvenCartanD4 K (LargeEvenTwistedH LargeEvenCartanD4 K
        LargeEvenRhoD4 n) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)
        →* MulAut (LargeEvenCenterQuot
          (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))).range :=
  chevIDImage_subset_inn (ggDiagRealizedInput_of_diagRealizedOn
    ((diagRealizedOn_isRoot_D4 hn hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag).symm))

theorem largeEvenLabelAll_subset_inn_triD4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R)
    (fun K _ _ hK _ _ φ hφ => chevIDImage_subset_inn_triD4 hn K hK hφ) hQ

end TableBExcSmallRest

end CFSG.StandardType
