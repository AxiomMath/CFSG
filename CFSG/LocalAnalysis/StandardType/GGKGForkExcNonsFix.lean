module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkWeylSeven
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

namespace ExcNons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

private theorem ggKGNf_weylTuple_eq_mactC {τ : Tag} (w : WeylGroup τ) {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) : weylTuple w a = mactC (Atw w) a := by
  funext i
  rw [weylTuple_eq_zpowMatrix, CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_apply]
  simp [mactC, Atw]

private theorem ggKGNf_mactC_subtype_coe {G : Type} [CommGroup G] {r : ℕ} (H : Subgroup G)
    (M : Matrix (Fin r) (Fin r) ℤ) (a : Fin r → H) :
    mactC M (fun i => (a i : G)) = fun i => ((mactC M a i : H) : G) := by
  funext i
  simp only [mactC]
  rw [Subgroup.val_finset_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [Subgroup.coe_zpow]

private theorem ggKGNf_canonicalRep_pow_charTwo
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (v : WeylGroup τ) (k : ℕ) :
    canonicalRep (coxeterSystem τ) L (v ^ k) = (canonicalRep (coxeterSystem τ) L v) ^ k := by
  induction k with
  | zero => simp [canonicalRep_one]
  | succ k ih =>
    rw [pow_succ, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, ih, pow_succ]

private theorem ggKGNf_conj_pow {G : Type} [Group G] (a b : G) (n : ℕ) :
    (a * b * a⁻¹) ^ n = a * b ^ n * a⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

private theorem ggKGNf_pow_conj
    {τ : Tag} {K : Type} [Field K]
    {ET : Subgroup (adjointGroup τ K)} {u : adjointGroup τ K}
    (hu : u ∈ Subgroup.normalizer (ET : Set (adjointGroup τ K)))
    {g0 : ModGL τ (AlgebraicClosure K)} {c : ModGL τ (AlgebraicClosure K)}
    (hstep : ∀ e ∈ ET,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((u * e * u⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 =
        c * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) * c⁻¹) :
    ∀ k : ℕ, ∀ e ∈ ET,
      ((u ^ k) * e * (u ^ k)⁻¹ ∈ ET) ∧
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((u ^ k) * e * (u ^ k)⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 =
        c ^ k * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) *
          (c ^ k)⁻¹ := by
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
    · rw [heq]; exact hmem'
    · rw [heq, hstep _ hmem, hval, pow_succ]; group

theorem card_fixed_le_pow_nons {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {m : ℕ}
    (hW : ∀ {C : Type} [CommGroup C], Nat.card C = p → ∀ {w : WeylGroup τ}, orderOf w = p →
      Nat.card {a : Fin τ.rank → C // mactC (Atw w) a = a} ≤ p ^ m)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g0 : ModGL τ (AlgebraicClosure K)) (hg0 : g0 ∈ adjointGroup τ (AlgebraicClosure K))
      (w : WeylGroup τ) (hw : ExcIsLongest τ w)
    (hlang : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ)
      (AlgebraicClosure K) w)
    {ET : Subgroup (adjointGroup τ K)}
    (hET : ∀ x : adjointGroup τ K, x ∈ ET ↔ x ^ p = 1 ∧
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) * g0 ∈
        twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
          (Units.map (entrywiseHom Fr)))
    {u : adjointGroup τ K} (hu : u ∈ Subgroup.normalizer (ET : Set (adjointGroup τ K)))
    (hup : u ^ p ∈ Subgroup.centralizer (ET : Set (adjointGroup τ K)))
    (hnc : u ∉ Subgroup.centralizer (ET : Set (adjointGroup τ K))) :
    Nat.card {e : adjointGroup τ K // e ∈ ET ∧ u * e = e * u} ≤ p ^ m := by
  classical
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let D : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0 hlang
  let F : ExcFrame τ K p ET :=
    { D := D
      w := w
      q_eq := rfl
      frob := ⟨Fr, hFr, fun g => rfl⟩
      n_eq := rfl
      mem_iff := hET }
  have hg0F : F.D.g0 = g0 := rfl
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hw' : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w) :=
    Or.inr ⟨hpq, hw⟩
  obtain ⟨v, _hvW, hweyl_raw⟩ :=
    ggKGExc_normalizer_weyl (τ := τ) (K := K) (p := p) hτ' hp (by omega) (fun _ => hp5) F hw' hu
  set c : ModGL τ (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v with hc
  have hweyl : ∀ e ∈ ET,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((u * e * u⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 =
        c * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) *
          c⁻¹ := by
    intro e he
    have h := hweyl_raw e he
    rw [hg0F] at h
    exact h
  have hpow :=
    ggKGNf_pow_conj (τ := τ) (K := K) (ET := ET) (u := u) hu (g0 := g0) (c := c) hweyl
  have hcpow : c ^ p = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v ^ p) := by
    rw [hc]
    exact (ggKGNf_canonicalRep_pow_charTwo (L := AlgebraicClosure K) v p).symm
  have hvp : v ^ p = 1 := by
    apply ggKGExc_normalizer_faithful (v := v ^ p) (τ := τ) (K := K) (p := p) hτ' hp (by omega)
      (fun _ => hp5) F hw'
    intro e he
    have hcent : (u ^ p) * e * (u ^ p)⁻¹ = e := by
      have hcu := (Subgroup.mem_centralizer_iff.1 hup) e he
      rw [← hcu]
      group
    have hY : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0 =
        c ^ p * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) *
          (c ^ p)⁻¹ := by
      have h := (hpow p e he).2
      rw [hcent] at h
      exact h
    have hgoal : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v ^ p) *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v ^ p))⁻¹ =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0 := by
      rw [← hcpow]
      exact hY.symm
    simpa only [hg0F] using hgoal
  have hv1 : v ≠ 1 := by
    intro hv
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hYfix : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((u * e * u⁻¹ : adjointGroup τ K) : ModGL τ K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0 := by
      have h := hweyl e he
      rw [hc, hv] at h
      simpa [canonicalRep_one] using h
    have hfix : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((u * e * u⁻¹ : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) := by
      calc baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((u * e * u⁻¹ : adjointGroup τ K) : ModGL τ K)
          = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((u * e * u⁻¹ : adjointGroup τ K) : ModGL τ K) * g0) * g0⁻¹ := by group
        _ = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * g0) *
          g0⁻¹ := by
              rw [hYfix]
        _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) := by group
    have hconj : u * e * u⁻¹ = e := by
      apply Subtype.ext
      exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hfix
    calc e * u = (u * e * u⁻¹) * u := by rw [hconj]
      _ = u * e := by group
  have hex : ∀ e : {e : adjointGroup τ K // e ∈ ET ∧ u * e = e * u},
      ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K) * g0 =
            rootDiagUnit τ a ∧
        (∀ i, a i ^ p = 1) ∧ mactC (Atw v) a = a := by
    intro e
    obtain ⟨heET, hef⟩ := e.2
    have hmemT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K) * g0 ∈
        torusGroup τ (AlgebraicClosure K) :=
      (mem_twistedTorusOf.1 ((hET e.1).1 heET).2).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmemT
    have hep : e.1 ^ p = 1 := ((hET e.1).1 heET).1
    have hBp : (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K)) ^ p = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hep, Subgroup.coe_one, map_one]
    have hYp : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K) * g0) ^ p
      = 1 := by
      have hconj :=
        ggKGNf_conj_pow g0⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K)) p
      simpa [hBp] using hconj
    have hap : ∀ i, a i ^ p = 1 := by
      have h1 : rootDiagUnit τ (a ^ p) = 1 := by
        rw [← rootDiagUnit_pow, ← ha]
        exact hYp
      have h2 : a ^ p = 1 := rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
      intro i
      simpa using congrFun h2 i
    have hfix : mactC (Atw v) a = a := by
      have hef' : u * e.1 * u⁻¹ = e.1 := by
        calc u * e.1 * u⁻¹ = (u * e.1) * u⁻¹ := rfl
          _ = (e.1 * u) * u⁻¹ := by rw [hef]
          _ = e.1 := by group
      have hEq : c *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K) * g0) * c⁻¹ =
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e.1 : ModGL τ K) * g0 := by
        have h := hweyl e.1 heET
        rw [hef'] at h
        exact h.symm
      have hconj : rootDiagUnit τ (weylTuple v a) = rootDiagUnit τ a := by
        rw [← canonicalRep_conj_rootDiagUnit v a, ← ha, ← hc]
        exact hEq
      have hwt : weylTuple v a = a := rootDiagUnit_injective hconj
      calc mactC (Atw v) a = weylTuple v a := (ggKGNf_weylTuple_eq_mactC v a).symm
        _ = a := hwt
    exact ⟨a, ha, hap, hfix⟩
  let f : {e : adjointGroup τ K // e ∈ ET ∧ u * e = e * u} →
      {a : Fin τ.rank → rootsOfUnity p (AlgebraicClosure K) // mactC (Atw v) a = a} :=
    fun e =>
      let a := Classical.choose (hex e)
      have hspec := Classical.choose_spec (hex e)
      ⟨fun i => ⟨a i, (mem_rootsOfUnity p (a i)).2 (hspec.2.1 i)⟩, by
        have hcoe := ggKGNf_mactC_subtype_coe (rootsOfUnity p (AlgebraicClosure K)) (Atw v)
          (fun i => (⟨a i, (mem_rootsOfUnity p (a i)).2 (hspec.2.1 i)⟩ :
            rootsOfUnity p (AlgebraicClosure K)))
        funext i
        apply Subtype.ext
        have hthis := congrFun hcoe i
        change mactC (Atw v) a i = _ at hthis
        exact hthis.symm.trans (congrFun hspec.2.2 i)⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 heq
    have hchoose : Classical.choose (hex e1) = Classical.choose (hex e2) := by
      have h := congrArg (fun g : {a : Fin τ.rank → rootsOfUnity p (AlgebraicClosure K) //
          mactC (Atw v) a = a} =>
          fun i => ((g.1 i : rootsOfUnity p (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)) heq
      simpa [f] using h
    have hYeq : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e1.1 : ModGL τ K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e2.1 : ModGL τ K) * g0 := by
      rw [(Classical.choose_spec (hex e1)).1, (Classical.choose_spec (hex e2)).1, hchoose]
    have hBeq : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e1.1 : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e2.1 : ModGL τ K) := by
      calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (e1.1 : ModGL τ K)
          = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e1.1 : ModGL τ K) * g0) *
            g0⁻¹ := by
              group
        _ = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e2.1 : ModGL τ K) * g0) *
          g0⁻¹ := by
              rw [hYeq]
        _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (e2.1 : ModGL τ K) := by group
    exact Subtype.ext
      (Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hBeq))
  have hCcard : Nat.card (rootsOfUnity p (AlgebraicClosure K)) = p := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p : AlgebraicClosure K) := ⟨by
      intro h
      have h' : ((p : ℕ) : AlgebraicClosure K) = 0 := h
      rw [CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p] at h'
      rcases (Nat.dvd_prime hp).1 h' with h1 | h2
      · norm_num at h1
      · omega⟩
    haveI : IsSepClosed (AlgebraicClosure K) := inferInstance
    haveI : HasEnoughRootsOfUnity (AlgebraicClosure K) p :=
      IsSepClosed.hasEnoughRootsOfUnity (AlgebraicClosure K) p
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
    exact hζ.card_rootsOfUnity
  haveI : Fact p.Prime := ⟨hp⟩
  have horder : orderOf v = p := orderOf_eq_prime hvp hv1
  calc Nat.card {e : adjointGroup τ K // e ∈ ET ∧ u * e = e * u}
      ≤ Nat.card {a : Fin τ.rank → rootsOfUnity p (AlgebraicClosure K) //
          mactC (Atw v) a = a} := Nat.card_le_card_of_injective f hf_inj
    _ ≤ p ^ m := hW (C := rootsOfUnity p (AlgebraicClosure K)) hCcard horder

end ExcNons

end CFSG.StandardType

end
