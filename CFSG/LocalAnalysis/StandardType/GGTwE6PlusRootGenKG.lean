module

public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidReflFamily
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCenterPrime
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Sylow
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LieType.SeitzGeneration.ExcTorusCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem TwE6PlusRootGen.ggTorusModelAt_twE6Plus_of_frame
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) :
    GGTorusModelAt p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two hp hp2
  have hζ : ζ ^ p = 1 := hζp.pow_eq_one
  obtain ⟨T, hTinj, hTE, hT⟩ :=
    exists_twE6PlusTorus hK hσ hp5 hpq F hv hζp.eq_orderOf.symm hζ
  have hweyl : ∀ i : {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}, ∃ r ∈ ggKGTwJ F i.1,
      ggKGTwY F r = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
        (rootReflection i.1) := fun i => ggKGTwJ_weyl hK hσ F hv i.2
  choose w hwJ hwY using hweyl
  haveI : Nonempty {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ} :=
    ⟨⟨Pi.single 0 1, isRoot_single Tag.E6 0⟩⟩
  rw [← hTE]
  refine ggTorusModelAt_of_reflFamily hTinj w (fun i => ExcSplitRootGen.excRefl (τ := Tag.E6) i.1)
    (fun i => ggKGTwJ F i.1) ?_ ?_ ?_ hwJ ?_ ?_ ?_ ?_
  · intro i t
    exact conj_twE6PlusTorus F hζ hT (hwY i) t
  · intro i t
    exact ExcSplitRootGen.excRefl_excRefl i.2 t
  · intro i
    exact ExcSplitRootGen.card_fix_excRefl hp2 i.2
  · intro i
    rw [torusFix_excRefl_eq_ggKGTwHyp F hζ hTinj hTE hT]
    exact isComponentOf_ggKGTwJ hK hσ hp hp5 hpq hq F hv i.2
  · intro i
    exact ggKGTwJ_dvd_card hK hσ F hv i.2 hpq
  · intro i j hij
    rcases PhiTwoRootGen.eq_or_eq_neg_of_excRefl_eq_excRefl (Or.inl rfl) hp2 i.2 j.2 hij with h | h
    · simp only [h]
    · simp only [h, ggKGTwJ_neg F i.2]
  · intro j
    exact iSup_ggKGTwJ_ne hGen hp2 hn hK hσ F hv j

private theorem selfCentralizing_map_mulEquiv_twE6Plus {p : ℕ} {G G' : Type} [Group G]
    [Group G'] (e : G ≃* G') {E : Subgroup G}
    (h : ∀ x : G, (∀ a ∈ E, x * a = a * x) → x ^ p = 1 → x ∈ E) :
    ∀ x : G', (∀ b ∈ E.map e.toMonoidHom, x * b = b * x) → x ^ p = 1 →
      x ∈ E.map e.toMonoidHom := by
  intro x hx hxp
  obtain ⟨y, rfl⟩ : ∃ y, e y = x := ⟨e.symm x, e.apply_symm_apply x⟩
  refine Subgroup.mem_map_of_mem e.toMonoidHom (h y (fun a ha => ?_) ?_)
  · have h1 := hx (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)
    exact e.injective (by rw [map_mul, map_mul]; exact h1)
  · exact e.injective (by rw [map_pow, hxp, map_one])

theorem TwE6PlusRootGen.ggTorusModelAt_recipeR_twE6Plus
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1)
    {E : Subgroup (TwE6Delta.RecipeR K n)} (hE : IsElemAbelian p E) (hcard : p ^ 5 ≤ Nat.card E)
    (hsc : ∀ g : TwE6Delta.RecipeR K n, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    GGTorusModelAt p E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ n := fun c => hσ c
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (by omega : 1 ≤ n) hK σ.toRingHom hσ'
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := hE.map e.toMonoidHom
  have hcard' : p ^ 5 ≤ Nat.card (E.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  have h3 : p ^ 3 ≤ Nat.card (E.map e.toMonoidHom) :=
    le_trans (Nat.pow_le_pow_right (by have h2 := hp.two_le; omega) (by norm_num : 3 ≤ 5))
      hcard'
  have hsc' : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (∀ b ∈ E.map e.toMonoidHom, x * b = b * x) → x ^ p = 1 →
        x ∈ E.map e.toMonoidHom :=
    selfCentralizing_map_mulEquiv_twE6Plus e hsc
  obtain ⟨F, -, hv⟩ := ExcTwE6Nons.twE6SCTorusInput_nonsplit σ hp hp5 hK hσ hpn
    (E.map e.toMonoidHom) hE' h3 hcard' hsc'
  have hmodel : GGTorusModelAt p (E.map e.toMonoidHom) :=
    TwE6PlusRootGen.ggTorusModelAt_twE6Plus_of_frame hGen hn hK hσ hp hp5 hpn F (hv hpn)
  have hback : GGTorusModelAt p ((E.map e.toMonoidHom).map e.symm.toMonoidHom) :=
    GGTorusModelAt.map hmodel e.symm
  have hmap : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id (TwE6Delta.RecipeR K n) := by
      ext x
      exact e.symm_apply_apply x
    rw [hcomp, Subgroup.map_id]
  rwa [hmap] at hback

theorem ggTorusRootGenAvoidKG_twE6Plus_of_lss92
    (hGen : PhiTwoTwE6GenInput) {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGTorusRootGenAvoidKG p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n)
      (TwE6Delta.RecipeI K n) := by
  have hn1 : 1 ≤ n := by omega
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI := TwE6Delta.finite_recipeR (K := K) (n := n) hK
  refine ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime hp
    (TwE6Delta.center_recipeR_eq_bot hn1 hK) (TwE6Delta.ggOutdiagPrime_twE6 hn1 hK hp hp3)
    (TwE6Delta.ggCenterPrime_twE6 hn1 hK hp hp2 hp3) ?_
  intro E hE hr _ hsc
  rw [TwE6Delta.liftRank_of_ne hp3] at hr
  exact TwE6PlusRootGen.ggTorusModelAt_recipeR_twE6Plus hGen hn hK hp hp5 hpn hE hr hsc

end CFSG.StandardType

end
