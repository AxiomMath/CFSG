module

public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidModels
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj

public section

namespace CFSG.StandardType.TwE6EltSmall

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical2 CFSG.RankThree.Chevalley CFSG.StandardType.LangRat

set_option linter.unusedSectionVars false

theorem rootSL2_HSL_eq_rootDiagUnit_corootTuple
    {L : Type} [Field L]
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (t : Lˣ) :
    rootSL2 TwistTag.E6.tag L γ (HSL t) =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ t) := by
  have h2 : iform γ γ = 2 := SimplyLacedCover.iform_self_eq_two (τ := TwistTag.E6.tag)
    (fun i => Matrix.one_apply_eq i) hγ
  refine CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hγ _ (fun δ _ => ?_) t
  rw [h2, Int.mul_ediv_cancel_left _ two_ne_zero, iform_comm]
  simp only [iform, TwE6RootKill.symmetrizedCartan_twE6, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring


theorem mem_Γ_of_mem_model_of_mul_self {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {L : Type}
    [Field L] [Algebra K L] {Fr : L →+* L} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L]
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (D : LangDatum TwistTag.E6.tag L)
    (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) {x : ModGL TwistTag.E6.tag L} (hx : x ∈ D.model)
    (hxx : x * x = 1) : x ∈ D.Γ := by
  obtain ⟨-, -, hder, ⟨k, hk⟩, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  haveI : (((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
      (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 L Fr)).Normal :=
    Subgroup.Normal.of_commutator_le _ fun z hz => by
      rw [Subgroup.mem_subgroupOf, ← hder, ← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map_of_mem _ hz
  rw [model_eq_map_twistedFixedGroup D hΦ] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyy : y * y = 1 := (MulAut.conj D.g0⁻¹).injective (by rw [map_mul, map_one]; exact hxx)
  have hmem := Subgroup.pow_index_mem (((twistedE6RootGroup K σ).map
    (baseChangeGL (algebraMap K L))).subgroupOf
      (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 L Fr)) ⟨y, hy⟩
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hyy' : (⟨y, hy⟩ : CFSG.Blueprint.twistedFixedGroup TwistTag.E6 L Fr) * ⟨y, hy⟩ = 1 :=
    Subtype.ext hyy
  rw [hk, hm, pow_succ, pow_mul, sq, hyy', one_pow, one_mul] at hmem
  rw [Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ]
  exact ⟨y, Subgroup.mem_subgroupOf.1 hmem, rfl⟩

variable {K : Type} [Field K] [Finite K] {n : ℕ} {σ : K ≃+* K}
  {A : Subgroup (ModGL TwistTag.E6.tag K)}

theorem exists_ennolaSetup (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (D : CFSG.LieType.SeitzGeneration.ExcWideThree.TwLangData K σ (2 ^ n) A) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) :
    ∃ S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p,
      S.D = LangDatum.ofTwist TwistTag.E6 D.Fr (2 ^ n) D.hFr D.v D.hg0C D.hg0 := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved _ _
    (LangDatum.ofTwist TwistTag.E6 D.Fr (2 ^ n) D.hFr D.v D.hg0C D.hg0)
  refine ⟨LangDatum.toSetup _ p ρ hρ hp (Or.inl hp5)
    ⟨Nat.prime_two.isPrimePow.pow (by omega), ?_⟩ ?_
    (finite_model_twistedE6 Nat.prime_two hn hK hσ D.hFr _ rfl), rfl⟩
  · change ((2 ^ n : ℕ) : AlgebraicClosure K) = 0
    rw [Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow (by omega)]
  · exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpq))

variable (D : CFSG.LieType.SeitzGeneration.ExcWideThree.TwLangData K σ (2 ^ n) A)
  (hv : ∀ γ, D.v • permLattice TwistTag.E6.perm γ = -γ) {p : ℕ}
  (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p)
  (hSD : S.D = LangDatum.ofTwist TwistTag.E6 D.Fr (2 ^ n) D.hFr D.v D.hg0C D.hg0)

include hv hSD in
theorem ennola_rho_eq_neg {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    S.ρ γ = -γ := by
  have hF := S.frob
  rw [hSD] at hF
  rw [frobRootMap_ofTwist_apply (by positivity) D.hFr D.hg0C D.hg0 hF hγ, hv]

include hv in
theorem ennola_step_pinnedX (hK : Nat.card K = (2 ^ n) ^ 2) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (c : AlgebraicClosure K) :
    (LangDatum.ofTwist TwistTag.E6 D.Fr (2 ^ n) D.hFr D.v D.hg0C D.hg0).step
        (pinnedX TwistTag.E6.tag (AlgebraicClosure K) γ c) =
      pinnedX TwistTag.E6.tag (AlgebraicClosure K) (-γ) (D.Fr c) := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨e, he, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv (AlgebraicClosure K) D.v
    (hγ.permLattice TwistTag.E6.cartan_perm)
  change canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v *
      twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr
        (pinnedX TwistTag.E6.tag (AlgebraicClosure K) γ c) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)⁻¹ = _
  rw [CFSG.SeitzReduction.twistHom_pinnedX_eq_of_charTwo (t := TwistTag.E6)
    (CharTwo.two_eq_zero (R := AlgebraicClosure K)) D.Fr hγ, hconj, hv,
    eq_one_of_mul_self_eq_one_of_charTwo he, one_mul]

include hv hSD in
theorem ennola_rootSL2_WSL_mem_Γ (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) : rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ WSL ∈ S.Γ := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h₁ := ennola_step_pinnedX D hv hK hγ 1
  have h₂ := ennola_step_pinnedX D hv hK (IsRoot.neg hγ) 1
  rw [map_one] at h₁ h₂
  rw [neg_neg] at h₂
  change _ ∈ S.D.Γ
  rw [hSD]
  exact mem_Γ_of_mem_model_of_mul_self Nat.prime_two hn hK hσ D.hFr _ rfl
    (rootSL2_WSL_mem_model _ hγ h₁ h₂) (rootSL2_WSL_mul_self γ)

include hSD in
theorem ennola_range_eq_Γ (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ((MulAut.conj D.g0⁻¹).toMonoidHom.comp ((baseChangeGL
      (algebraMap K (AlgebraicClosure K))).comp (twistedE6RootGroup K σ).subtype)).range = S.Γ := by
  change _ = S.D.Γ
  rw [hSD, Γ_eq_map_twistedE6RootGroup Nat.prime_two hn hK hσ D.hFr
    (LangDatum.ofTwist TwistTag.E6 D.Fr (2 ^ n) D.hFr D.v D.hg0C D.hg0) rfl, MonoidHom.range_comp,
    MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

end CFSG.StandardType.TwE6EltSmall

end
