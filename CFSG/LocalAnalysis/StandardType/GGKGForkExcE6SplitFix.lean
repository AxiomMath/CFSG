module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkWeylFive

public section

namespace CFSG.StandardType

namespace ExcE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.RankThree.Chevalley.EvenF4QPlus

open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix_apply)

private theorem ggKGSf_weylTuple_eq_mactC {τ : Tag} (w : WeylGroup τ) {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) : weylTuple w a = mactC (Atw w) a := by
  funext i
  rw [weylTuple_eq_zpowMatrix, zpowMatrix_apply]
  simp [mactC, Atw]

private theorem ggKGSf_mactC_subtype_coe {G : Type} [CommGroup G] {r : ℕ} (H : Subgroup G)
    (M : Matrix (Fin r) (Fin r) ℤ) (a : Fin r → H) :
    mactC M (fun i => (a i : G)) = fun i => ((mactC M a i : H) : G) := by
  funext i
  simp only [mactC]
  rw [Subgroup.val_finset_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [Subgroup.coe_zpow]

private theorem ggKGSf_canonicalRep_pow_charTwo
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (v : WeylGroup τ) (k : ℕ) :
    canonicalRep (coxeterSystem τ) L (v ^ k) = (canonicalRep (coxeterSystem τ) L v) ^ k := by
  induction k with
  | zero => simp [canonicalRep_one]
  | succ k ih => rw [pow_succ, canonicalRep_mul_of_charTwo, ih, pow_succ]

private theorem ggKGSf_pow_conj
    {K : Type} [Field K]
    {ET : Subgroup (adjointGroup .E6 K)} {u : adjointGroup .E6 K}
    (hu : u ∈ Subgroup.normalizer (ET : Set (adjointGroup .E6 K)))
    {c : ModGL .E6 (AlgebraicClosure K)}
    (hstep : ∀ e ∈ ET,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((u * e * u⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) =
        c * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) * c⁻¹) :
    ∀ k : ℕ, ∀ e ∈ ET,
      ((u ^ k) * e * (u ^ k)⁻¹ ∈ ET) ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((u ^ k) * e * (u ^ k)⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) =
        c ^ k * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) * (c ^ k)⁻¹ := by
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

theorem card_fixed_le_five_cube
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (h5 : 5 ∣ Nat.card K - 1)
    {ET : Subgroup (adjointGroup .E6 K)}
    (hET : ∀ x : adjointGroup .E6 K, x ∈ ET ↔ x ^ 5 = 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) ∈
          twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)))
    {u : adjointGroup .E6 K} (hu : u ∈ Subgroup.normalizer (ET : Set (adjointGroup .E6 K)))
    (hu5 : u ^ 5 ∈ Subgroup.centralizer (ET : Set (adjointGroup .E6 K)))
    (hnc : u ∉ Subgroup.centralizer (ET : Set (adjointGroup .E6 K))) :
    Nat.card {e : adjointGroup .E6 K // e ∈ ET ∧ u * e = e * u} ≤ 5 ^ 3 := by
  obtain ⟨F, hw, hg0, _hn⟩ :=
    exists_splitFrame (K := K) (p := 5) Fr hFr hET
  have hw' : (5 ∣ Nat.card K - 1 ∧ F.w = 1) ∨
      (5 ∣ Nat.card K + 1 ∧ ExcIsLongest .E6 F.w) := Or.inl ⟨h5, hw⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨v, _hvW, hweyl_raw⟩ :=
    ggKGExc_normalizer_weyl (τ := .E6) (K := K) (p := 5)
      (Or.inl rfl) Nat.prime_five (by norm_num) (fun _ => le_rfl) F hw' hu
  set c : ModGL .E6 (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) v with hc
  have hweyl : ∀ e ∈ ET,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((u * e * u⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) =
        c * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) * c⁻¹ := by
    intro e he
    have h := hweyl_raw e he
    simpa [hg0] using h
  have hpow := ggKGSf_pow_conj (K := K) (ET := ET) (u := u) hu (c := c) hweyl
  have hcpow : c ^ 5 = canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) (v ^ 5) := by
    rw [hc]
    exact (ggKGSf_canonicalRep_pow_charTwo (L := AlgebraicClosure K) v 5).symm
  have hv5 : v ^ 5 = 1 := by
    apply ggKGExc_normalizer_faithful (v := v ^ 5) (τ := .E6) (K := K) (p := 5)
      (Or.inl rfl) Nat.prime_five (by norm_num) (fun _ => le_rfl) F hw'
    intro e he
    have hcent : (u ^ 5) * e * (u ^ 5)⁻¹ = e := by
      have hc5 := (Subgroup.mem_centralizer_iff.1 hu5) e he
      rw [← hc5]
      group
    have hB : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) =
        c ^ 5 * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) *
          (c ^ 5)⁻¹ := by
      have h := (hpow 5 e he).2
      rw [hcent] at h
      exact h
    have hgoal : canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) (v ^ 5) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) *
        (canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) (v ^ 5))⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) := by
      rw [← hcpow]
      exact hB.symm
    simpa [hg0] using hgoal
  have hv1 : v ≠ 1 := by
    intro hv
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hfix : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((u * e * u⁻¹ : adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) := by
      have h := hweyl e he
      rw [hc, hv] at h
      simpa [canonicalRep_one] using h
    have hconj : u * e * u⁻¹ = e := by
      apply Subtype.ext
      exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hfix
    calc e * u = (u * e * u⁻¹) * u := by rw [hconj]
      _ = u * e := by group
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have horder : orderOf v = 5 := orderOf_eq_prime hv5 hv1
  have hex : ∀ e : {e : adjointGroup .E6 K // e ∈ ET ∧ u * e = e * u},
      ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL .E6 K) = rootDiagUnit .E6 a ∧
        (∀ i, a i ^ 5 = 1) ∧ mactC (Atw v) a = a := by
    intro e
    obtain ⟨heET, hef⟩ := e.2
    have hmemT : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL .E6 K) ∈
        torusGroup .E6 (AlgebraicClosure K) :=
      (mem_twistedTorusOf.1 ((hET e.1).1 heET).2).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmemT
    have he5 : e.1 ^ 5 = 1 := ((hET e.1).1 heET).1
    have hB5 : (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL .E6 K)) ^ 5 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, he5, Subgroup.coe_one, map_one]
    have ha5 : ∀ i, a i ^ 5 = 1 := by
      have h1 : rootDiagUnit .E6 (a ^ 5) = 1 := by
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
      have hEq : c * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL .E6 K) * c⁻¹ =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL .E6 K) := by
        have h := hweyl e.1 heET
        rw [hef'] at h
        exact h.symm
      have hconj : rootDiagUnit .E6 (weylTuple v a) = rootDiagUnit .E6 a := by
        rw [← canonicalRep_conj_rootDiagUnit v a, ← ha, ← hc]
        exact hEq
      have hwt : weylTuple v a = a := rootDiagUnit_injective hconj
      calc mactC (Atw v) a = weylTuple v a := (ggKGSf_weylTuple_eq_mactC v a).symm
        _ = a := hwt
    exact ⟨a, ha, ha5, hfix⟩
  let f : {e : adjointGroup .E6 K // e ∈ ET ∧ u * e = e * u} →
      {a : Fin Tag.E6.rank → rootsOfUnity 5 (AlgebraicClosure K) // mactC (Atw v) a = a} :=
    fun e =>
      let a := Classical.choose (hex e)
      have hspec := Classical.choose_spec (hex e)
      ⟨fun i => ⟨a i, (mem_rootsOfUnity 5 (a i)).2 (hspec.2.1 i)⟩, by
        have hcoe := ggKGSf_mactC_subtype_coe (rootsOfUnity 5 (AlgebraicClosure K)) (Atw v)
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
      have h := congrArg (fun g : {a : Fin Tag.E6.rank → rootsOfUnity 5 (AlgebraicClosure K) //
          mactC (Atw v) a = a} =>
          fun i => ((g.1 i : rootsOfUnity 5 (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)) heq
      simpa [f] using h
    have hBeq : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e1.1 : ModGL .E6 K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e2.1 : ModGL .E6 K) := by
      rw [(Classical.choose_spec (hex e1)).1, (Classical.choose_spec (hex e2)).1, hchoose]
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
  calc Nat.card {e : adjointGroup .E6 K // e ∈ ET ∧ u * e = e * u}
      ≤ Nat.card {a : Fin Tag.E6.rank → rootsOfUnity 5 (AlgebraicClosure K) //
          mactC (Atw v) a = a} := Nat.card_le_card_of_injective f hf_inj
    _ ≤ 5 ^ 3 := weylE6_five_fixed (C := rootsOfUnity 5 (AlgebraicClosure K)) hCcard horder

end ExcE6Split

end CFSG.StandardType

end
