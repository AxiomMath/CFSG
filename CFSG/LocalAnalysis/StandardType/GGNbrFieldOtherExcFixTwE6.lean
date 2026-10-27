module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GTwE6Model
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RecipeExcLang

theorem twE6Fix_fixOn
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop}
    (hS : S = IsRoot TwistTag.E6.tag) {H : Subgroup (MarkChev.GLS S K)}
    (hH : H = MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)
    {f : MulAut (LargeEvenCenterQuot H)} (hf : f ∈ RecipeFieldExcInn.markFieldImage S K H)
    (hord : orderOf f = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = (2 ^ (n / p)) ^ 2 ∧
      ∀ H₀ : Subgroup (MarkChev.GLS S k),
        H₀ = MarkChev.twistedH TwistTag.E6.tag.cartan S k TwistTag.E6.perm (n / p) →
          IsSimpleGroup (LargeEvenCenterQuot H₀) ∧
            (∃ a b : LargeEvenCenterQuot H₀, a * b ≠ b * a) ∧
            ∃ θ₀ : ggFixDer f ≃* LargeEvenCenterQuot H₀,
              GGFixGeom (markIDImage S K H) f (markIDImage S k H₀) θ₀ := by
  subst hS
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hH' : H = graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    hH.trans ((twistedH_eq_commutator K TwistTag.E6 n σ.toRingHom hσ).trans
      (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ).2.2.1)
  subst hH'
  obtain ⟨hpn, κ, σ₀, hk, hσ₀, hs, hna, θ₀, hθ₀⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T156.twE6_fixGeom_model hn hK σ hσ hp hp2 hf hord
  refine ⟨fixSubfield κ, inferInstance, inferInstance, hk, fun H₀ hH₀ => ?_⟩
  have hd : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hH₀' : H₀ = graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom :=
    hH₀.trans ((twistedH_eq_commutator (fixSubfield κ) TwistTag.E6 (n / p) σ₀.toRingHom
      hσ₀).trans (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hd (fixSubfield κ)
        hk σ₀.toRingHom hσ₀).2.2.1)
  subst hH₀'
  exact ⟨hs, hna, θ₀, hθ₀⟩

theorem twE6Fix_fixStd
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))}
    (hf : f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
    (hord : orderOf f = p) :
    LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 (n / p) fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom (LargeEvenChevIDImage (LargeEvenCartanE 6) K
          (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) f I₀ θ₀ := by
  obtain ⟨k, _, _, hk, hconcl⟩ := twE6Fix_fixOn hn hK hp hp2
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag) (largeEvenTwistedH_eq _ K _ n) hf hord
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  obtain ⟨hs, hna, θ₀, hg⟩ := hconcl _ (largeEvenTwistedH_eq _ k _ (n / p))
  refine ⟨hs, hna, θ₀, ?_⟩
  rw [largeEvenChevIDImage_eq, largeEvenChevIDImage_eq]
  exact hg

theorem ggFieldFixKnown_twE6_all :
    GGFieldFixKnown fun _ lab => lab.tag = .twE6 := by
  intro p lab hp hp2 hlab ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeTwisted_and (fun K _ _ hK _ _ f hf hord =>
    twE6Fix_fixStd hn hK hp hp2 hf hord) hQ

theorem ggFieldFixKnown_twE6 :
    GGFieldFixKnown fun p lab => lab.tag = .twE6 ∧ p ≠ 3 :=
  fun p lab hp hp2 hlab hS => ggFieldFixKnown_twE6_all p lab hp hp2 hlab hS.1

end CFSG.StandardType

end
