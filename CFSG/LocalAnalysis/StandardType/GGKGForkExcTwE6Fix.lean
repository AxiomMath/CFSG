module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkWeylFive
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public section

namespace CFSG.StandardType

namespace ExcTwE6Nons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.RankThree.Chevalley.EvenF4QPlus
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix_apply)

private theorem ggKGTf_weylTuple_eq_mactC {τ : Tag} (w : WeylGroup τ) {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) : weylTuple w a = mactC (Atw w) a := by
  funext i
  rw [weylTuple_eq_zpowMatrix, zpowMatrix_apply]
  simp [mactC, Atw]

private theorem ggKGTf_mactC_subtype_coe {G : Type} [CommGroup G] {r : ℕ} (H : Subgroup G)
    (M : Matrix (Fin r) (Fin r) ℤ) (a : Fin r → H) :
    mactC M (fun i => (a i : G)) = fun i => ((mactC M a i : H) : G) := by
  funext i
  simp only [mactC]
  rw [Subgroup.val_finset_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [Subgroup.coe_zpow]

private theorem ggKGTf_canonicalRep_pow_charTwo
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (v : WeylGroup τ) (k : ℕ) :
    canonicalRep (coxeterSystem τ) L (v ^ k) = (canonicalRep (coxeterSystem τ) L v) ^ k := by
  induction k with
  | zero => simp [canonicalRep_one]
  | succ k ih => rw [pow_succ, canonicalRep_mul_of_charTwo, ih, pow_succ]

private theorem ggKGTf_pow_conj
    {K : Type} [Field K]
    {σ : K ≃+* K} {ET : Subgroup (twistedE6RootGroup K σ)} {u : twistedE6RootGroup K σ}
    (hu : u ∈ Subgroup.normalizer (ET : Set (twistedE6RootGroup K σ)))
    {g0 c : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hstep : ∀ e ∈ ET,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((u * e * u⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) * g0 =
        c * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) * c⁻¹) :
    ∀ k : ℕ, ∀ e ∈ ET,
      ((u ^ k) * e * (u ^ k)⁻¹ ∈ ET) ∧
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((((u ^ k) * e * (u ^ k)⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) * g0 =
        c ^ k * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) * (c ^ k)⁻¹ := by
  intro k
  induction k with
  | zero =>
    intro e he
    refine ⟨by simpa using he, ?_⟩
    simp
  | succ k ih =>
    intro e he
    obtain ⟨hmem, hval⟩ := ih e he
    have hmem' : u * ((u ^ k) * e * (u ^ k)⁻¹) * u⁻¹ ∈ ET :=
      (Subgroup.mem_normalizer_iff.1 hu ((u ^ k) * e * (u ^ k)⁻¹)).1 hmem
    have heq : (u ^ (k + 1)) * e * (u ^ (k + 1))⁻¹ =
        u * ((u ^ k) * e * (u ^ k)⁻¹) * u⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact hmem'
    · rw [heq, hstep _ hmem, hval, pow_succ]
      group

theorem card_fixed_le_five_cube_tw
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (h5 : 5 ∣ 2 ^ n + 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (w : WeylGroup TwistTag.E6.tag) (hw : ExcIsLongest TwistTag.E6.tag w)
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 = g0 * canonicalRep
      (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {ET : Subgroup (twistedE6RootGroup K σ)}
    (hET : ∀ x : twistedE6RootGroup K σ, x ∈ ET ↔ x ^ 5 = 1 ∧
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 ∈
        twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr))
    {u : twistedE6RootGroup K σ}
    (hu : u ∈ Subgroup.normalizer (ET : Set (twistedE6RootGroup K σ)))
    (hu5 : u ^ 5 ∈ Subgroup.centralizer (ET : Set (twistedE6RootGroup K σ)))
    (hnc : u ∉ Subgroup.centralizer (ET : Set (twistedE6RootGroup K σ))) :
    Nat.card {e : twistedE6RootGroup K σ // e ∈ ET ∧ u * e = e * u} ≤ 5 ^ 3 := by
  let F : TwE6Frame K σ n 5 ET :=
    { Fr := Fr, v := w, g0 := g0, fr_eq := hFr, g0_mem := hg0, lang := hlang, mem_iff := hET }
  have hvW : (5 ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (5 ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v) :=
    Or.inr ⟨h5, hw⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨v, _hvW, hweyl_raw⟩ :=
    ggKGTwE6_normalizer_weyl hK hσ Nat.prime_five (by norm_num) F hvW hu
  set c : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v with hc
  have hweyl : ∀ e ∈ ET,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((u * e * u⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        c * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) * c⁻¹ := by
    intro e he
    have h := hweyl_raw e he
    simpa [hc, F] using h
  have hpow := ggKGTf_pow_conj (K := K) (ET := ET) (u := u) hu (c := c) hweyl
  have hcpow : c ^ 5 = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
    (v ^ 5) := by
    rw [hc]
    exact (ggKGTf_canonicalRep_pow_charTwo (L := AlgebraicClosure K) v 5).symm
  have hv5 : v ^ 5 = 1 := by
    apply ggKGTwE6_normalizer_faithful (u := v ^ 5) hK hσ Nat.prime_five (by norm_num) F hvW
    intro e he
    have hcent : (u ^ 5) * e * (u ^ 5)⁻¹ = e := by
      have hc5 := (Subgroup.mem_centralizer_iff.1 hu5) e he
      rw [← hc5]
      group
    have hB : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        c ^ 5 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) * (c ^ 5)⁻¹ := by
      have h := (hpow 5 e he).2
      rw [hcent] at h
      exact h
    have hgoal : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (v ^ 5) *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (v ^ 5))⁻¹ =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
      rw [← hcpow]
      exact hB.symm
    simpa [F] using hgoal
  have hv1 : v ≠ 1 := by
    intro hv
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hfixg : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((u * e * u⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
      have h := hweyl e he
      rw [hc, hv] at h
      simpa [canonicalRep_one] using h
    have hfix : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((u * e * u⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
      have h := congrArg (fun z => g0 * z * g0⁻¹) hfixg
      simpa [mul_assoc] using h
    have hconj : u * e * u⁻¹ = e := by
      apply Subtype.ext
      exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hfix
    calc e * u = (u * e * u⁻¹) * u := by rw [hconj]
      _ = u * e := by group
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have horder : orderOf v = 5 := orderOf_eq_prime hv5 hv1
  have hex : ∀ e : {e : twistedE6RootGroup K σ // e ∈ ET ∧ u * e = e * u},
      ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
          rootDiagUnit TwistTag.E6.tag a ∧
        (∀ i, a i ^ 5 = 1) ∧ mactC (Atw v) a = a := by
    intro e
    obtain ⟨heET, hef⟩ := e.2
    have hmemT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      (mem_twistedTorusOf.1 ((hET e.1).1 heET).2).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmemT
    have he5 : e.1 ^ 5 = 1 := ((hET e.1).1 heET).1
    have hB5 : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) ^ 5 = 1 := by
      have hB : (baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) ^ 5 = 1 := by
        rw [← map_pow, ← Subgroup.coe_pow, he5, Subgroup.coe_one, map_one]
      have h := map_pow (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) 5
      rw [hB] at h
      simpa [MulAut.conj_apply] using h.symm
    have ha5 : ∀ i, a i ^ 5 = 1 := by
      have h1 : rootDiagUnit TwistTag.E6.tag (a ^ 5) = 1 := by
        rw [← rootDiagUnit_pow, ← ha, hB5]
      have h2 : a ^ 5 = 1 :=
        rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
      intro i
      simpa using congrFun h2 i
    have hfix : mactC (Atw v) a = a := by
      have hef' : u * e.1 * u⁻¹ = e.1 := by
        calc u * e.1 * u⁻¹ = (u * e.1) * u⁻¹ := rfl
          _ = (e.1 * u) * u⁻¹ := by rw [hef]
          _ = e.1 := by group
      have hEq : c * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0) * c⁻¹ =
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((e.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
        have h := hweyl e.1 heET
        rw [hef'] at h
        exact h.symm
      have hconj : rootDiagUnit TwistTag.E6.tag (weylTuple v a) = rootDiagUnit
        TwistTag.E6.tag a := by
        rw [← canonicalRep_conj_rootDiagUnit v a, ← ha, ← hc]
        exact hEq
      have hwt : weylTuple v a = a := rootDiagUnit_injective hconj
      calc mactC (Atw v) a = weylTuple v a := (ggKGTf_weylTuple_eq_mactC v a).symm
        _ = a := hwt
    exact ⟨a, ha, ha5, hfix⟩
  let f : {e : twistedE6RootGroup K σ // e ∈ ET ∧ u * e = e * u} →
      {a : Fin TwistTag.E6.tag.rank → rootsOfUnity 5 (AlgebraicClosure K) //
        mactC (Atw v) a = a} :=
    fun e =>
      let a := Classical.choose (hex e)
      have hspec := Classical.choose_spec (hex e)
      ⟨fun i => ⟨a i, (mem_rootsOfUnity 5 (a i)).2 (hspec.2.1 i)⟩, by
        have hcoe := ggKGTf_mactC_subtype_coe (rootsOfUnity 5 (AlgebraicClosure K)) (Atw v)
          (fun i => (⟨a i, (mem_rootsOfUnity 5 (a i)).2 (hspec.2.1 i)⟩ :
            rootsOfUnity 5 (AlgebraicClosure K)))
        funext i
        apply Subtype.ext
        have hthis := congrFun hcoe i
        change mactC (Atw v) a i = _ at hthis
        exact hthis.symm.trans (congrFun hspec.2.2 i)⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 heq
    have hchoose : Classical.choose (hex e1) = Classical.choose (hex e2) := by
      have h := congrArg (fun g : {a : Fin TwistTag.E6.tag.rank →
            rootsOfUnity 5 (AlgebraicClosure K) // mactC (Atw v) a = a} =>
          fun i => ((g.1 i : rootsOfUnity 5 (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)) heq
      simpa [f] using h
    have hBeqg : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e1.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e2.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
      rw [(Classical.choose_spec (hex e1)).1, (Classical.choose_spec (hex e2)).1, hchoose]
    have hBeq : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e1.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e2.1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
      have h := congrArg (fun z => g0 * z * g0⁻¹) hBeqg
      simpa [mul_assoc] using h
    exact Subtype.ext
      (Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hBeq))
  have hCcard : Nat.card (rootsOfUnity 5 (AlgebraicClosure K)) = 5 := by
    haveI : NeZero (5 : AlgebraicClosure K) := ⟨by
      intro h
      have h' : ((5 : ℕ) : AlgebraicClosure K) = 0 := h
      rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 5] at h'
      norm_num at h'⟩
    haveI : IsSepClosed (AlgebraicClosure K) := inferInstance
    haveI : HasEnoughRootsOfUnity (AlgebraicClosure K) 5 :=
      IsSepClosed.hasEnoughRootsOfUnity (AlgebraicClosure K) 5
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 5
    exact hζ.card_rootsOfUnity
  calc Nat.card {e : twistedE6RootGroup K σ // e ∈ ET ∧ u * e = e * u}
      ≤ Nat.card {a : Fin TwistTag.E6.tag.rank → rootsOfUnity 5 (AlgebraicClosure K) //
          mactC (Atw v) a = a} := Nat.card_le_card_of_injective f hf_inj
    _ ≤ 5 ^ 3 := weylE6_five_fixed (C := rootsOfUnity 5 (AlgebraicClosure K)) hCcard horder

end ExcTwE6Nons

end CFSG.StandardType

end
