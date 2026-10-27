module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeOddIndex
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidTwE6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.StraightenTw
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextRankAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

theorem no_weyl_neg_one_E6
    (w : WeylGroup .E6) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ ∧ w • γ ≠ -γ := by
  by_contra h
  push Not at h
  have h1 : twNeg * w = 1 := by
    apply CFSG.LieType.Chevalley.eq_one_of_forall_height_pos
    intro i
    rw [mul_smul, h (Pi.single i 1) (isRoot_single .E6 i), smul_neg, twNeg_smul, neg_neg,
      permLattice_single, height_single]
    norm_num
  have hw : w = twNeg⁻¹ := by
    have := congrArg (fun x => twNeg⁻¹ * x) h1
    simpa [mul_assoc] using this
  have h0 := h (Pi.single 0 1) (isRoot_single .E6 0)
  rw [hw, twNeg_inv_smul, permLattice_single] at h0
  have hval := congrFun h0 0
  simp only [Pi.neg_apply] at hval
  rw [Pi.single_eq_same] at hval
  have hne : (0 : Fin Tag.E6.rank) ≠ twE6Rho 0 := by decide
  rw [Pi.single_eq_of_ne hne] at hval
  norm_num at hval

theorem twisted_descend_torus
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5)
    (hΦ : ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom .E6 Ω Fr)
    (hd : S.DescendsTwE6) (hAlg : S.IsAlgebraic)
    (A₀ : Subgroup (ModGL .E6 Ω)) (hA₀ : A₀ ≤ S.D.model) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra K Ω) (σ : K ≃+* K)
      (e : twistedE6RootGroup K σ ≃* S.Γ) (A : Subgroup (ModGL TwistTag.E6.tag K)),
      Nat.card K = S.D.q ^ 2 ∧
      (∀ c : K, algebraMap K Ω (σ c) = (algebraMap K Ω c) ^ S.D.q) ∧
      Nonempty (IsAlgClosure K Ω) ∧
      A ≤ twistedE6InndiagGL K σ ∧ Nat.card A = Nat.card A₀ ∧
      A.map ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp
        (baseChangeGL (algebraMap K Ω) : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 Ω)) = A₀ ∧
      (∀ h : twistedE6RootGroup K σ, (e h : ModGL Tag.E6 Ω) =
        S.D.g0⁻¹ *
          (baseChangeGL (algebraMap K Ω) (h : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 Ω) *
          S.D.g0) := by
  obtain ⟨K, hF, hFin, hAlgΩ, σ, e, hK, hσ, he⟩ := hd
  obtain ⟨Fr, hFr, hΦeq⟩ := hΦ
  obtain ⟨ℓ, f, hℓ, hf, hqf⟩ := S.hqpow.1
  haveI : IsAlgClosure K Ω := ⟨inferInstance, ⟨fun c => by
    obtain ⟨n, hn, hc⟩ := hAlg c
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X, ?_, ?_⟩
    · have hq1 : 1 < S.D.q ^ n := Nat.one_lt_pow hn.ne' S.hqpow.1.one_lt
      exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hc, sub_self]⟩⟩
  have hK' : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hqf]; exact hK
  have hσ' : ∀ c : K, σ c = c ^ (ℓ ^ f) := by
    intro c
    apply (algebraMap K Ω).injective
    rw [map_pow, hqf]
    exact hσ c
  have hFr' : ∀ c : Ω, Fr c = c ^ (ℓ ^ f) := by intro c; rw [hqf]; exact hFr c
  have hmodel : S.D.model = (twistedFixedGroup TwistTag.E6 Ω Fr).map
      (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    model_eq_map_twistedFixedGroup S.D hΦeq
  have hA₀' : A₀.map (MulAut.conj S.D.g0).toMonoidHom ≤
      twistedFixedGroup TwistTag.E6 Ω Fr := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have ha' : a ∈ (twistedFixedGroup TwistTag.E6 Ω Fr).map
        (MulAut.conj S.D.g0⁻¹).toMonoidHom := hmodel ▸ hA₀ ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha'
    rw [← hba]
    simpa [MulAut.conj_apply, mul_assoc] using hb
  have hA₀'' : A₀.map (MulAut.conj S.D.g0).toMonoidHom ≤
      (twistedE6InndiagGL K σ).map (baseChangeGL (algebraMap K Ω)) :=
    hA₀'.trans (twistedFixedGroup_le_map_inndiag_alg (Nat.prime_iff.mpr hℓ) hf hK' σ hσ' Fr hFr')
  have hmap : ((A₀.map (MulAut.conj S.D.g0).toMonoidHom).comap
        (baseChangeGL (algebraMap K Ω))).map (baseChangeGL (algebraMap K Ω)) =
        A₀.map (MulAut.conj S.D.g0).toMonoidHom :=
      Subgroup.map_comap_eq_self (hA₀''.trans
        (Subgroup.map_le_range (baseChangeGL (algebraMap K Ω)) (twistedE6InndiagGL K σ)))
  refine ⟨K, hF, hFin, hAlgΩ, σ, e,
    (A₀.map (MulAut.conj S.D.g0).toMonoidHom).comap (baseChangeGL (algebraMap K Ω)),
    hK, hσ, ⟨inferInstance⟩, ?_, ?_, ?_, he⟩
  · intro x hx
    have hx' : baseChangeGL (algebraMap K Ω) x ∈
        (twistedE6InndiagGL K σ).map (baseChangeGL (algebraMap K Ω)) := hA₀'' hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    rwa [baseChangeGL_injective (algebraMap K Ω) hyx] at hy
  · calc Nat.card ((A₀.map (MulAut.conj S.D.g0).toMonoidHom).comap
          (baseChangeGL (algebraMap K Ω)))
        = Nat.card (((A₀.map (MulAut.conj S.D.g0).toMonoidHom).comap
            (baseChangeGL (algebraMap K Ω))).map (baseChangeGL (algebraMap K Ω))) :=
          (Subgroup.card_map_of_injective (baseChangeGL_injective (algebraMap K Ω))).symm
      _ = Nat.card (A₀.map (MulAut.conj S.D.g0).toMonoidHom) := by rw [hmap]
      _ = Nat.card A₀ := Subgroup.card_map_of_injective (MulAut.conj S.D.g0).injective
  · calc ((A₀.map (MulAut.conj S.D.g0).toMonoidHom).comap
          (baseChangeGL (algebraMap K Ω))).map
          ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K Ω)))
        = (((A₀.map (MulAut.conj S.D.g0).toMonoidHom).comap
            (baseChangeGL (algebraMap K Ω))).map (baseChangeGL (algebraMap K Ω))).map
            (MulAut.conj S.D.g0⁻¹).toMonoidHom := by rw [Subgroup.map_map]
      _ = (A₀.map (MulAut.conj S.D.g0).toMonoidHom).map
            (MulAut.conj S.D.g0⁻¹).toMonoidHom := by rw [hmap]
      _ = A₀ := by
          rw [Subgroup.map_map]
          convert Subgroup.map_id A₀ using 2
          ext x
          simp [MulAut.conj_apply, mul_assoc]

theorem twisted_twNormTwo
    {K : Type} [Field K] (σ : K ≃+* K)
    (A : Subgroup (ModGL TwistTag.E6.tag K))
    (U : Subgroup (ModGL TwistTag.E6.tag K)) (hUroot : U ≤ twistedE6RootGroup K σ)
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hAU : A ≤ Subgroup.normalizer (U : Set (ModGL TwistTag.E6.tag K))) :
    TwE6RootKill.TwNormTwo K σ A := by
  refine ⟨U, hUroot, hU, hU2, fun x hx u hu => ?_⟩
  exact (Subgroup.mem_set_normalizer_iff.mp (hAU hx) u).mp hu

theorem twisted_kill_translate
    {Ω : Type} [Field Ω]
    (A₀ : Subgroup (ModGL .E6 Ω))
    (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot .E6 α)
    (hkill : ∀ x ∈ A₀, ∃ a : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit .E6 a = x ∧ rootChar a α = 1) :
    ∃ α, IsRoot .E6 α ∧ ∀ u : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit .E6 u ∈ A₀ → rootChar u α = 1 := by
  refine ⟨α, hα, fun u hu => ?_⟩
  obtain ⟨a, ha, hαa⟩ := hkill (rootDiagUnit .E6 u) hu
  have hau : a = u := CFSG.LieType.Chevalley.rootDiagUnit_injective ha
  rwa [hau] at hαa

theorem langSetup_isAlgebraic_of_halg
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (S : LangSetup .E6 Ω 5)
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) : S.IsAlgebraic := by
  obtain ⟨ℓ, f0, hℓ, hf0, hqf⟩ := S.hqpow.1
  have hℓ2 : ℓ = 2 := by
    have h0 : ((S.D.q : ℕ) : Ω) = 0 := S.hqpow.2
    rw [← hqf, Nat.cast_pow] at h0
    have hz : ((ℓ : ℕ) : Ω) = 0 := (pow_eq_zero_iff hf0.ne').1 h0
    have h2dvd : 2 ∣ ℓ := (CharP.cast_eq_zero_iff Ω 2 ℓ).1 hz
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_iff.mpr hℓ)).1 h2dvd).symm
  subst hℓ2
  letI : Algebra (ZMod 2) Ω := ZMod.algebra Ω 2
  haveI : Algebra.IsAlgebraic (ZMod 2) Ω := halg
  intro c
  have hint : IsIntegral (ZMod 2) c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have hfd : FiniteDimensional (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : Finite (IntermediateField.adjoin (ZMod 2) {c}) := Module.finite_of_finite (ZMod 2)
  letI : Fintype (IntermediateField.adjoin (ZMod 2) {c}) := Fintype.ofFinite _
  set m := Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2) {c}) with hm
  have hmpos : 0 < m := Module.finrank_pos
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod 2) {c}) = 2 ^ m := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2)
      (V := IntermediateField.adjoin (ZMod 2) {c})
    rw [← hm] at h
    rw [h, ZMod.card]
  have hcm : c ^ (2 ^ m) = c := by
    have h1 := FiniteField.pow_card
      (⟨c, IntermediateField.mem_adjoin_simple_self (ZMod 2) c⟩ :
        IntermediateField.adjoin (ZMod 2) {c})
    rw [hcard] at h1
    have h2 := congrArg (fun x : IntermediateField.adjoin (ZMod 2) {c} => (x : Ω)) h1
    simpa using h2
  have hiter : ∀ k : ℕ, c ^ ((2 ^ m) ^ k) = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hcm]
  refine ⟨m, hmpos, ?_⟩
  rw [show S.D.q = 2 ^ f0 from hqf.symm, ← pow_mul, mul_comm, pow_mul]
  exact hiter f0

end CFSG.StandardType
