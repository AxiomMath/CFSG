module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagRee

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableB.TwE6

section RootSet

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ) (K : Type)
  [Field K]

@[expose] def DiagCyclicOn (S : (Fin r → ℤ) → Prop) : Prop :=
  ∀ a a' : Fin r → Kˣ,
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K a = markDiag S K a * h) →
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K a' = markDiag S K a' * h) →
    (¬ ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K a') →
    ∃ k : ℕ, ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K (a * (a' ^ k)⁻¹)

variable {A ρ n K}

theorem ggDiagCyclicInput_of_diagCyclicOn (h : DiagCyclicOn A ρ n K (LargeEvenIsRoot A)) :
    GGDiagCyclicInput A K (LargeEvenTwistedH A K ρ n) := by
  rw [largeEvenTwistedH_eq]
  have hd : ∀ b, (diagHom A K b : Module.End K (LargeEvenChevModule A K)) =
      markDiag (LargeEvenIsRoot A) K b := fun b => by
    rw [coe_diagHom, largeEvenDiagMap_eq_markDiag]
  have hrel : ∀ b, (∀ x ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n,
      diagHom A K b * x * (diagHom A K b)⁻¹ ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n) →
      ∀ x ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n,
        ∃ x' ∈ MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n,
          (x' : Module.End K (LargeEvenChevModule A K)) * markDiag (LargeEvenIsRoot A) K b =
            markDiag (LargeEvenIsRoot A) K b * x := by
    intro b hb x hx
    refine ⟨_, hb x hx, ?_⟩
    rw [← largeEvenDiagMap_eq_markDiag]
    exact (diag_rel_iff b x _).2 rfl
  have hmem : ∀ {b} {g : LargeEvenChevGL A K},
      (g : Module.End K (LargeEvenChevModule A K)) = markDiag (LargeEvenIsRoot A) K b →
        g = diagHom A K b := fun hg => Units.ext (by rw [hg, hd])
  intro a a' ha ha' hn
  obtain ⟨k, g, hg, hgd⟩ := h a a' (hrel a ha) (hrel a' ha') fun ⟨g, hg, hgd⟩ => by
    rw [hmem hgd] at hg
    exact hn hg
  refine ⟨k, ?_⟩
  rw [← hmem hgd]
  exact hg

theorem DiagCyclicOn.of_eq {S S' : (Fin r → ℤ) → Prop} (hS : S = S')
    (h : DiagCyclicOn A ρ n K S) : DiagCyclicOn A ρ n K S' :=
  hS ▸ h

end RootSet

theorem markDiag_isRoot {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) :
    markDiag (IsRoot τ) K b = rootDiag b := by
  unfold markDiag rootDiag
  congr 1
  funext l
  cases l <;> rfl

theorem eq_conj_of_mul_rootDiag {τ : Tag} {K : Type} [Field K] {b : Fin τ.rank → Kˣ}
    {g h' : ModGL τ K}
    (e : (h' : Module.End K (RootModule τ K)) * rootDiag b = rootDiag b * g) :
    h' = rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹ := by
  have e' : h' * rootDiagUnit τ b = rootDiagUnit τ b * g := Units.ext e
  rw [← e', mul_inv_cancel_right]


theorem diagCyclicOn_isRoot {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    DiagCyclicOn TwistTag.E6.tag.cartan TwistTag.E6.perm n K (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := iterateFrobenius_def 2 n
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = graphFixedRootGroup TwistTag.E6 K σ := by
    rw [twistedH_eq_commutator K .E6 n σ hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  intro a a' ha ha' hn'
  rw [hC] at ha ha' hn' ⊢
  have hconj : ∀ {b : Fin TwistTag.E6.tag.rank → Kˣ},
      (∀ h ∈ graphFixedRootGroup TwistTag.E6 K σ, ∃ h' ∈ graphFixedRootGroup TwistTag.E6 K σ,
        (h' : Module.End K (RootModule TwistTag.E6.tag K)) *
            markDiag (IsRoot TwistTag.E6.tag) K b = markDiag (IsRoot TwistTag.E6.tag) K b * h) →
      ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag b * g *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro b hb g hg
    obtain ⟨h', hh', e⟩ := hb g hg
    rw [markDiag_isRoot] at e
    rw [← eq_conj_of_mul_rootDiag e]
    exact hh'
  have hn2 : rootDiagUnit TwistTag.E6.tag a' ∉ graphFixedRootGroup TwistTag.E6 K σ := fun h =>
    hn' ⟨_, h, (markDiag_isRoot a').symm⟩
  obtain ⟨k, hk⟩ := twE6_rootDiag_cyclic hq hK hσ (hconj ha) (hconj ha') hn2
  exact ⟨k, _, hk, (markDiag_isRoot _).symm⟩

end TableB.TwE6

section Main


theorem ggTwistedE6DiagInput_holds : GGTwistedE6DiagInput := by
  intro n hn K _ _ hK _
  exact TableB.TwE6.ggDiagCyclicInput_of_diagCyclicOn
    ((TableB.TwE6.diagCyclicOn_isRoot hn hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm)

theorem ggLNoncyclicInput_holds : GGLNoncyclicInput :=
  ggLNoncyclicInput_of_twE6Diag ggTwistedE6DiagInput_holds

theorem ggTableBInputs_of_split
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I) :
    GGLNoncyclicInput ∧ GGBstarInput ∧ GGStdSubPreInput :=
  ggTableBInputs_of_twE6
    (fun _ hlab ht => largeEvenLabelAll_outdiag_twE6 ggTwistedE6DiagInput_holds hlab ht) h

end Main

end CFSG.StandardType
