module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.GroupTheory.GroupAction.OfQuotient
import Mathlib.GroupTheory.IndexNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise TensorProduct commutatorElement IsMulCommutative

public theorem CFSG.theorem_3_7_elementCentralizer_eq_bot {G : Type*} [Group G] [Finite G]
    (K R : Subgroup G) (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) :
    ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ := by
  intro x hx
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hycent⟩
  have hz_top : Subgroup.zpowers x = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hR_prime hx
  have hycentR : y ∈ subgroupCentralizerIn K R := by
    refine ⟨hyK, ?_⟩
    change y ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hrR
    have hrz : (⟨r, hrR⟩ : R) ∈ Subgroup.zpowers x := by
      have : (⟨r, hrR⟩ : R) ∈ (⊤ : Subgroup R) := by simp
      rwa [← hz_top] at this
    rcases Subgroup.mem_zpowers_iff.mp hrz with ⟨n, hn⟩
    have hycommx : Commute y (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hycent
    have hnG : (x : G) ^ n = (r : G) := by
      simpa using congrArg Subtype.val hn
    simpa [hnG, Commute] using (hycommx.zpow_right n).eq.symm
  have hybot : y ∈ (⊥ : Subgroup G) := by
    rw [← hfix]
    exact hycentR
  simpa using hybot

public theorem CFSG.theorem_3_7_frobenius {G : Type*} [Group G] [Finite G]
    (K R : Subgroup G) (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hK_ne : K ≠ ⊥) (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) :
    IsFrobeniusGroupWithKernelComplement K R := by
  have hR_ne : R ≠ ⊥ := by
    intro hR_bot
    exact hR_prime.ne_one ((Subgroup.eq_bot_iff_card (H := R)).1 hR_bot)
  exact
    (lemma_3_1 (K := K) (R := R) hK_ne hR_ne hK_normal hKR).2
      (theorem_3_7_elementCentralizer_eq_bot K R hR_prime hfix)

public theorem CFSG.theorem_3_7_coprime_card {G : Type*} [Group G] [Finite G]
    (K R : Subgroup G) (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hR_prime : Nat.Prime (Nat.card R)) (hfix : subgroupCentralizerIn K R = ⊥) :
    Nat.Coprime (Nat.card K) (Nat.card R) := by
  by_cases hK_bot : K = ⊥
  · rw [(Subgroup.eq_bot_iff_card (H := K)).1 hK_bot]
    exact Nat.coprime_one_left (Nat.card R)
  · exact
      theorem_3_5_coprime_card_of_prime_complement K R
        (theorem_3_7_frobenius K R hK_normal hKR hK_bot hR_prime hfix) hR_prime


public theorem CFSG.theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot
    {A V : Type*} [Group A] [Group V] {q : ℕ} [Fact q.Prime]
    [IsElementaryAbelian q V] [MulDistribMulAction A V] (R : Subgroup A) :
    letI : MulDistribMulAction (↥R) V := MulDistribMulAction.compHom V R.subtype
    fixedPointSubgroup (↥R) V = ⊥ →
      (Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := q) :
        Representation (ZMod q) A (Additive V)).fixedSubspace R =
        ⊥ := by
  classical
  let : MulDistribMulAction (↥R) V := MulDistribMulAction.compHom V R.subtype
  intro hfix
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply Additive.toMul.injective
  have hxfix : Additive.toMul x ∈ fixedPointSubgroup (↥R) V := by
    rw [FixedPoints.mem_subgroup]
    intro r
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hx
    have hxr := hx r
    change (r : A) • Additive.toMul x = Additive.toMul x
    exact Additive.ofMul.injective (by simpa using hxr)
  have hxbot : Additive.toMul x ∈ (⊥ : Subgroup V) := by
    simpa [hfix] using hxfix
  simpa using hxbot

public theorem CFSG.theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn
    {A V : Type*} [Group A] [Group V] {q : ℕ} [Fact q.Prime]
    [IsElementaryAbelian q V] [MulDistribMulAction A V] (H : Subgroup A)
    (hcent :
      H ≤
        (Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := q) :
          Representation (ZMod q) A (Additive V)).centralizerIn
          H) :
    letI : MulDistribMulAction (↥H) V := MulDistribMulAction.compHom V H.subtype
    fixedPointSubgroup (↥H) V = ⊤ := by
  classical
  let : MulDistribMulAction (↥H) V := MulDistribMulAction.compHom V H.subtype
  apply top_unique
  intro x _hx
  rw [FixedPoints.mem_subgroup]
  intro h
  have hhker :
      (h : A) ∈
        (Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := q) :
          Representation (ZMod q) A (Additive V)).ker :=
    (hcent h.property).2
  rw [MonoidHom.mem_ker] at hhker
  have hlin :=
    congrArg (fun f : Module.End (ZMod q) (Additive V) => f (Additive.ofMul x)) hhker
  change (h : A) • x = x
  exact Additive.ofMul.injective (by simpa using hlin)

public theorem CFSG.theorem_3_7_quotient_card_prime {G : Type*} [Group G] [Finite G]
    (K R : Subgroup G) (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hR_prime : Nat.Prime (Nat.card R)) :
    Nat.Prime (Nat.card (G ⧸ K)) := by
  have : K.Normal := hK_normal
  let e : G ⧸ K ≃* R := hKR.symm.QuotientMulEquiv
  have hcard : Nat.card (G ⧸ K) = Nat.card R := Nat.card_congr e.toEquiv
  rwa [hcard]

public theorem CFSG.theorem_3_7_map_mk'_eq_top_of_not_le_kernel
    {G : Type*} [Group G] [Finite G] (K N : Subgroup G) [K.Normal]
    (hquot_prime : Nat.Prime (Nat.card (G ⧸ K))) (hN_not_le_K : ¬ N ≤ K) :
    N.map (QuotientGroup.mk' K) = ⊤ := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have : Fact (Nat.Prime (Nat.card (G ⧸ K))) := ⟨hquot_prime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (N.map q) with hbot | htop
  · have hleker : N ≤ q.ker := (Subgroup.map_eq_bot_iff (H := N) (f := q)).1 hbot
    have hleK : N ≤ K := by
      simpa [q] using hleker
    exact False.elim (hN_not_le_K hleK)
  · simpa [q] using htop

public theorem CFSG.theorem_3_7_sup_eq_top_of_map_mk'_eq_top
    {G : Type*} [Group G] (K N : Subgroup G) [K.Normal]
    (hmap : N.map (QuotientGroup.mk' K) = ⊤) :
    N ⊔ K = ⊤ := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hmap' : N.map q = ⊤ := by
    simpa [q] using hmap
  have hcomap : Subgroup.comap q (N.map q) = K ⊔ N := by
    simp [q, QuotientGroup.comap_map_mk']
  have hKN : K ⊔ N = ⊤ := by
    rw [← hcomap, hmap']
    simp
  simpa [sup_comm] using hKN

public theorem CFSG.theorem_3_7_sup_eq_top_of_not_le_kernel
    {G : Type*} [Group G] [Finite G] (K N : Subgroup G) [K.Normal]
    (hquot_prime : Nat.Prime (Nat.card (G ⧸ K))) (hN_not_le_K : ¬ N ≤ K) :
    N ⊔ K = ⊤ :=
  theorem_3_7_sup_eq_top_of_map_mk'_eq_top K N
    (theorem_3_7_map_mk'_eq_top_of_not_le_kernel K N hquot_prime hN_not_le_K)

public theorem CFSG.theorem_3_7_normal_eq_top_of_not_le_kernel
    {G : Type*} [Group G] [Finite G] (K R N : Subgroup G) [N.Normal]
    (hsolvK : Group.IsSolvable K) (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hK_ne : K ≠ ⊥)
    (hR_prime : Nat.Prime (Nat.card R)) (hN_not_le_K : ¬ N ≤ K) :
    N = ⊤ := by
  let _ : Nontrivial ↥K := K.nontrivial_iff_ne_bot.mpr hK_ne
  have : K.Normal := hfrob.normal
  have hquot_prime : Nat.Prime (Nat.card (G ⧸ K)) :=
    theorem_3_7_quotient_card_prime K R hfrob.normal hfrob.isComplement' hR_prime
  have hN_sup_K : N ⊔ K = ⊤ :=
    theorem_3_7_sup_eq_top_of_not_le_kernel K N hquot_prime hN_not_le_K
  have hK_le_N : K ≤ N := by
    by_contra hK_not_le_N
    have hN_le_K : N ≤ K :=
      lemma_3_2_a (K := K) (R := R) (N := N) hfrob hsolvK hK_not_le_N
    exact hN_not_le_K hN_le_K
  calc
    N = N ⊔ K := (sup_eq_left.mpr hK_le_N).symm
    _ = ⊤ := hN_sup_K

public theorem CFSG.theorem_3_7_chiefFactor_lower_le_kernel
    {G : Type*} [Group G] [Finite G] (K R : Subgroup G) (hsolvG : Group.IsSolvable G)
    (hK_normal : K.Normal) (hKR : K.IsComplement' R) (hK_ne : K ≠ ⊥)
    (hR_prime : Nat.Prime (Nat.card R)) (hfix : subgroupCentralizerIn K R = ⊥)
    (cf : ChiefFactor G) :
    cf.V ≤ K := by
  by_contra hV_not_le_K
  have : cf.V.Normal := cf.isChief.normal_K
  have hsolvK : Group.IsSolvable K := by
    infer_instance
  have hfrob : IsFrobeniusGroupWithKernelComplement K R :=
    theorem_3_7_frobenius K R hK_normal hKR hK_ne hR_prime hfix
  have hV_top : cf.V = ⊤ :=
    theorem_3_7_normal_eq_top_of_not_le_kernel K R cf.V hsolvK hfrob hK_ne hR_prime
      hV_not_le_K
  have hV_ne_top : cf.V ≠ ⊤ := by
    intro htop
    exact (not_le_of_gt cf.isChief.lt) (by simp [htop])
  exact hV_ne_top hV_top

public theorem CFSG.theorem_3_7_chief_factor_bridge_of_upper_le
    {G : Type*} [Group G] [Finite G] (K R : Subgroup G) (hsolvG : Group.IsSolvable G)
    (hK_normal : K.Normal) (hKR : K.IsComplement' R) (hK_ne : K ≠ ⊥)
    (hR_prime : Nat.Prime (Nat.card R)) (hfix : subgroupCentralizerIn K R = ⊥)
    (hupper :
      ∀ cf : ChiefFactor G, cf.U ≤ K → K ≤ centralizerOfChiefFactor (G := G) K cf) :
    ∀ cf : ChiefFactor G, K ≤ centralizerOfChiefFactor (G := G) K cf := by
  intro cf
  by_cases hU_le_K : cf.U ≤ K
  · exact hupper cf hU_le_K
  · have hV_le_K : cf.V ≤ K :=
      theorem_3_7_chiefFactor_lower_le_kernel K R hsolvG hK_normal hKR hK_ne hR_prime hfix cf
    exact
      le_centralizerOfChiefFactor_of_lower_le_of_not_upper_le hK_normal cf hV_le_K
        hU_le_K

public theorem CFSG.theorem_3_7_le_centralizerOfChiefFactor_of_quotient_conj_fixed
    {G : Type*} [Group G] (K : Subgroup G) (cf : ChiefFactor G) [cf.V.Normal]
    (hfixed :
      ∀ k : K, ∀ u : cf.U.map (QuotientGroup.mk' cf.V),
        (QuotientGroup.mk' cf.V) (k : G) * u *
            ((QuotientGroup.mk' cf.V) (k : G))⁻¹ = u) :
    K ≤ centralizerOfChiefFactor (G := G) K cf := by
  refine (le_centralizerOfChiefFactor_iff (G := G) (H := K) (N := K) (cf := cf)).2 ?_
  refine ⟨le_rfl, ?_⟩
  rw [Subgroup.commutator_le]
  intro k hk u hu
  let q : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  have huq : q u ∈ cf.U.map q := ⟨u, hu, rfl⟩
  have hfix := hfixed ⟨k, hk⟩ ⟨q u, huq⟩
  have hqcomm : q ⁅k, u⁆ = 1 := by
    change q (k * u * k⁻¹ * u⁻¹) = 1
    have hfix' : q k * q u * (q k)⁻¹ = q u := by
      simpa [q] using hfix
    calc
      q (k * u * k⁻¹ * u⁻¹) = q k * q u * (q k)⁻¹ * (q u)⁻¹ := by simp [q, mul_assoc]
      _ = q u * (q u)⁻¹ := by rw [hfix']
      _ = 1 := by simp
  exact (QuotientGroup.eq_one_iff (N := cf.V) ⁅k, u⁆).1 hqcomm

public theorem CFSG.theorem_3_7_chief_quotient_map_le_normalizer
    {G : Type*} [Group G] (H : Subgroup G) (cf : ChiefFactor G) [cf.V.Normal] :
    H.map (QuotientGroup.mk' cf.V) ≤
      Subgroup.normalizer (cf.U.map (QuotientGroup.mk' cf.V)) := by
  have : (cf.U.map (QuotientGroup.mk' cf.V)).Normal :=
    cf.isChief.normal_H.map (QuotientGroup.mk' cf.V) (QuotientGroup.mk'_surjective cf.V)
  exact Subgroup.le_normalizer_of_normal (H := cf.U.map (QuotientGroup.mk' cf.V))

public theorem CFSG.theorem_3_7_chief_quotient_R_fixedPointSubgroup_eq_bot
    {G : Type*} [Group G] [Finite G] (K R : Subgroup G) (hsolvG : Group.IsSolvable G)
    (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hR_prime : Nat.Prime (Nat.card R)) (hfix : subgroupCentralizerIn K R = ⊥)
    (cf : ChiefFactor G) (hU_le_K : cf.U ≤ K) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let q : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let hRnormUq :
      R.map q ≤ Subgroup.normalizer (cf.U.map q) :=
        theorem_3_7_chief_quotient_map_le_normalizer R cf
    have : Subgroup.Normalizes (R.map q) (cf.U.map q) := ⟨hRnormUq⟩
    fixedPointSubgroup (↥(R.map q)) (↥(cf.U.map q)) = ⊥ := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let q : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map q
  let Rq : Subgroup (G ⧸ cf.V) := R.map q
  have hRnormUq : Rq ≤ Subgroup.normalizer Uq :=
    theorem_3_7_chief_quotient_map_le_normalizer R cf
  have : Subgroup.Normalizes Rq Uq := ⟨hRnormUq⟩
  have hfixed_eq :
      fixedPointSubgroup (↥Rq) (↥Uq) = (subgroupCentralizerIn Uq Rq).subgroupOf Uq := by
    simpa [Uq, Rq] using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Uq Rq hRnormUq
  have hcent_quot : subgroupCentralizerIn Uq Rq = ⊥ := by
    have : cf.U.Normal := cf.isChief.normal_H
    have hRnormU : R ≤ Subgroup.normalizer cf.U :=
      Subgroup.le_normalizer_of_normal (H := cf.U)
    have hsolvU : Group.IsSolvable ↥cf.U := by
      let : Group.IsSolvable G := hsolvG
      infer_instance
    have hcopKR : Nat.Coprime (Nat.card K) (Nat.card R) :=
      theorem_3_7_coprime_card K R hK_normal hKR hR_prime hfix
    have hcopUR : Nat.Coprime (Nat.card cf.U) (Nat.card R) :=
      Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hU_le_K) hcopKR
    have hVinv : ∀ r : R, ∀ x ∈ cf.V, (r : G) * x * (r : G)⁻¹ ∈ cf.V := by
      intro r x hx
      exact cf.isChief.normal_K.conj_mem x hx (r : G)
    have hcent_map :
        subgroupCentralizerIn (cf.U.map q) (R.map q) =
          (subgroupCentralizerIn cf.U R).map q :=
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime cf.U R cf.V hRnormU
        hsolvU hcopUR hVinv
    have hcentU_bot : subgroupCentralizerIn cf.U R = ⊥ := by
      apply bot_unique
      intro x hx
      have hxK : x ∈ subgroupCentralizerIn K R := ⟨hU_le_K hx.1, hx.2⟩
      simpa [hfix] using hxK
    simp [Uq, Rq, hcent_map, hcentU_bot, q]
  change fixedPointSubgroup (↥Rq) (↥Uq) = ⊥
  rw [hfixed_eq, hcent_quot]
  simp

public theorem CFSG.theorem_3_7_le_centralizerOfChiefFactor_of_fixedPointSubgroup_top
    {G : Type*} [Group G] (K : Subgroup G) (cf : ChiefFactor G) [cf.V.Normal]
    (hKnorm :
      K.map (QuotientGroup.mk' cf.V) ≤
        Subgroup.normalizer (cf.U.map (QuotientGroup.mk' cf.V))) :
    letI : Subgroup.Normalizes (K.map (QuotientGroup.mk' cf.V))
        (cf.U.map (QuotientGroup.mk' cf.V)) := ⟨hKnorm⟩
    fixedPointSubgroup (↥(K.map (QuotientGroup.mk' cf.V)))
        (↥(cf.U.map (QuotientGroup.mk' cf.V))) = ⊤ →
      K ≤ centralizerOfChiefFactor (G := G) K cf := by
  classical
  let q : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  have : Subgroup.Normalizes (K.map q) (cf.U.map q) := ⟨hKnorm⟩
  intro hfix_top
  refine theorem_3_7_le_centralizerOfChiefFactor_of_quotient_conj_fixed K cf ?_
  intro k u
  let kq : K.map q := ⟨q (k : G), ⟨(k : G), k.property, rfl⟩⟩
  have hu_fix : u ∈ fixedPointSubgroup (↥(K.map q)) (↥(cf.U.map q)) := by
    rw [hfix_top]
    simp
  have hfix_u : kq • u = u := by
    rw [FixedPoints.mem_subgroup] at hu_fix
    exact hu_fix kq
  simpa [q, kq, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hKnorm] using
    congrArg Subtype.val hfix_u


universe u37

public abbrev CFSG.Theorem37IndHyp {G : Type u37} [Group G] [Finite G] (_K : Subgroup G) : Prop :=
  ∀ {G' : Type u37} [Group G'] [Finite G'] (K' R' : Subgroup G'),
    Nat.card G' < Nat.card G →
    Group.IsSolvable G' →
    Odd (Nat.card G') →
    K'.Normal →
    K'.IsComplement' R' →
    Nat.Prime (Nat.card R') →
    subgroupCentralizerIn K' R' = ⊥ →
    Group.IsNilpotent K'

public theorem CFSG.theorem_3_7_subgroupCentralizerIn_eq_bot_of_le
    {G : Type*} [Group G] (K R L : Subgroup G) (hL_le_K : L ≤ K)
    (hfix : subgroupCentralizerIn K R = ⊥) :
    subgroupCentralizerIn L R = ⊥ := by
  apply bot_unique
  intro x hx
  have hxK : x ∈ subgroupCentralizerIn K R := ⟨hL_le_K hx.1, hx.2⟩
  simpa [hfix] using hxK

public theorem CFSG.theorem_3_7_exists_maximal_normal_subgroup_of_ne_bot
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (hK_ne_bot : K ≠ ⊥) :
    ∃ L : Subgroup G,
      L.Normal ∧
        L < K ∧
          ∀ N : Subgroup G, N.Normal → L ≤ N → N ≤ K → N = L ∨ N = K := by
  classical
  let s : Set (Subgroup G) := {L | L.Normal ∧ L < K}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    constructor
    · infer_instance
    · exact bot_lt_iff_ne_bot.mpr hK_ne_bot
  obtain ⟨L, hL, hLmax⟩ := hsfin.exists_maximal hsne
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro N hN_normal hLN hNK
  by_cases hNK_eq : N = K
  · exact Or.inr hNK_eq
  · have hN_mem : N ∈ s := ⟨hN_normal, lt_of_le_of_ne hNK hNK_eq⟩
    exact Or.inl (le_antisymm (hLmax hN_mem hLN) hLN)

public theorem CFSG.theorem_3_7_subambient_card_lt_of_lt
    {G : Type*} [Group G] [Finite G] (K R L : Subgroup G) [L.Normal]
    (hKR : K.IsComplement' R) (hLK : L < K) :
    Nat.card ↥(L ⊔ R) < Nat.card G := by
  let S : Subgroup G := L ⊔ R
  have hdisj : Disjoint L R := hKR.disjoint.mono_left hLK.1
  have hcompS : (L.subgroupOf S).IsComplement' (R.subgroupOf S) :=
    isComplement'_subgroupOf_sup_of_disjoint L R hdisj
  have hcardS_eq : Nat.card ↥L * Nat.card ↥R = Nat.card ↥S := by
    simpa [S, natCard_subgroupOf_eq L S le_sup_left,
      natCard_subgroupOf_eq R S le_sup_right] using hcompS.card_mul_card
  have hcardG_eq : Nat.card ↥K * Nat.card ↥R = Nat.card G := by
    simpa using hKR.card_mul_card
  have hL_lt_K : Nat.card ↥L < Nat.card ↥K := natCard_lt_of_subgroup_lt hLK
  have hlt_mul : Nat.card ↥L * Nat.card ↥R < Nat.card ↥K * Nat.card ↥R := by
    exact Nat.mul_lt_mul_of_pos_right hL_lt_K (Nat.card_pos (α := ↥R))
  calc
    Nat.card ↥(L ⊔ R) = Nat.card ↥S := rfl
    _ = Nat.card ↥L * Nat.card ↥R := hcardS_eq.symm
    _ < Nat.card ↥K * Nat.card ↥R := hlt_mul
    _ = Nat.card G := hcardG_eq


public theorem CFSG.theorem_3_7_quotient_odd_of_normal
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hodd : Odd (Nat.card G)) :
    Odd (Nat.card (G ⧸ L)) := by
  exact odd_of_card_dvd hodd (Subgroup.card_quotient_dvd_card (s := L))


public theorem CFSG.theorem_3_7_le_fitting_of_nilpotent_normal
    {G : Type*} [Group G] [Finite G] (K L : Subgroup G) (hL_le_K : L ≤ K)
    (hL_normal : L.Normal) (hL_nil : Group.IsNilpotent L) :
    L ≤ fittingSubgroupOf (G := G) K := by
  let Lsub : Subgroup K := L.subgroupOf K
  have hLsub_normal : Lsub.Normal :=
    Subgroup.Normal.subgroupOf (G := G) (hH := hL_normal) K
  have : Group.IsNilpotent Lsub := by
    let e := (Subgroup.subgroupOfEquivOfLe (G := G) (H := L) (K := K) hL_le_K).symm
    have : Group.IsNilpotent (↥L) := hL_nil
    exact Group.nilpotent_of_mulEquiv (G := L) (G' := Lsub) e
  have hLsub_le : Lsub ≤ fittingSubgroup (↥K) :=
    le_sSup ⟨hLsub_normal, inferInstance⟩
  have hmap_le : Lsub.map K.subtype ≤ fittingSubgroupOf (G := G) K :=
    Subgroup.map_mono hLsub_le
  simpa [Lsub, fittingSubgroupOf, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hL_le_K] using
    hmap_le

public theorem CFSG.theorem_3_7_le_centralizerOfChiefFactor_of_le_fitting
    {G : Type*} [Group G] [Finite G] (K L : Subgroup G) (hsolvG : Group.IsSolvable G)
    (hK_normal : K.Normal)
    (hL_le_fit : L ≤ fittingSubgroupOf (G := G) K) (cf : ChiefFactor G) :
    L ≤ centralizerOfChiefFactor (G := G) K cf := by
  have hfit_le_K : fittingSubgroupOf (G := G) K ≤ K := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hfit_normal : (fittingSubgroupOf (G := G) K).Normal :=
    fittingSubgroupOf_normal (G := G) K hK_normal
  have hfit_nil : Group.IsNilpotent (fittingSubgroupOf (G := G) K) :=
    fittingSubgroupOf_isNilpotent (G := G) K
  have hfit_le_top :
      fittingSubgroupOf (G := G) K ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf :=
    normal_nilpotent_le_centralizerOfChiefFactor_top (G := G) hsolvG
      (fittingSubgroupOf (G := G) K) hfit_normal hfit_nil cf
  have hcomm_le :
      ⁅fittingSubgroupOf (G := G) K, cf.U⁆ ≤ cf.V :=
    (le_centralizerOfChiefFactor_iff (G := G) (H := (⊤ : Subgroup G))
      (N := fittingSubgroupOf (G := G) K) (cf := cf)).1 hfit_le_top |>.2
  have hfit_le_Kcf : fittingSubgroupOf (G := G) K ≤ centralizerOfChiefFactor (G := G) K cf := by
    exact
      (le_centralizerOfChiefFactor_iff (G := G) (H := K)
        (N := fittingSubgroupOf (G := G) K) (cf := cf)).2 ⟨hfit_le_K, hcomm_le⟩
  exact hL_le_fit.trans hfit_le_Kcf

public theorem CFSG.theorem_3_7_nilpotent_of_lt_of_induction
    {G : Type*} [Group G] [Finite G] (K R L : Subgroup G) (hind : Theorem37IndHyp K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) (hL_normal : L.Normal) (hLK : L < K) :
    Group.IsNilpotent L := by
  let S : Subgroup G := L ⊔ R
  have hcardS_dvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  have hcardS_lt : Nat.card S < Nat.card G :=
    theorem_3_7_subambient_card_lt_of_lt K R L hKR hLK
  have hdisj : Disjoint L R := hKR.disjoint.mono_left hLK.1
  have hsolvS : Group.IsSolvable S := by
    let : Group.IsSolvable G := hsolvG
    infer_instance
  have hoddS : Odd (Nat.card S) := odd_of_card_dvd hodd hcardS_dvd
  have hLsub_normal : (L.subgroupOf S).Normal :=
    Subgroup.Normal.subgroupOf (G := G) (hH := hL_normal) S
  have hcompS : (L.subgroupOf S).IsComplement' (R.subgroupOf S) :=
    isComplement'_subgroupOf_sup_of_disjoint L R hdisj
  have hRsub_prime : Nat.Prime (Nat.card (R.subgroupOf S)) := by
    rw [natCard_subgroupOf_eq R S le_sup_right]
    exact hR_prime
  have hfixL : subgroupCentralizerIn L R = ⊥ :=
    theorem_3_7_subgroupCentralizerIn_eq_bot_of_le K R L hLK.1 hfix
  have hfixS : subgroupCentralizerIn (L.subgroupOf S) (R.subgroupOf S) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq S L R le_sup_right, hfixL]
    simp
  have hnil_sub : Group.IsNilpotent (L.subgroupOf S) :=
    hind (L.subgroupOf S) (R.subgroupOf S) hcardS_lt hsolvS hoddS hLsub_normal hcompS
      hRsub_prime hfixS
  let e : ↥(L.subgroupOf S) ≃* ↥L :=
    Subgroup.subgroupOfEquivOfLe (G := G) (H := L) (K := S) le_sup_left
  exact Group.nilpotent_of_mulEquiv (G := L.subgroupOf S) (G' := L) e

public theorem CFSG.theorem_3_7_le_fitting_of_lt_of_induction
    {G : Type*} [Group G] [Finite G] (K R L : Subgroup G) (hind : Theorem37IndHyp K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) (hL_normal : L.Normal) (hLK : L < K) :
    L ≤ fittingSubgroupOf (G := G) K := by
  exact
    theorem_3_7_le_fitting_of_nilpotent_normal K L hLK.1 hL_normal
      (theorem_3_7_nilpotent_of_lt_of_induction K R L hind hsolvG hodd hKR
        hR_prime hfix hL_normal hLK)

public theorem CFSG.theorem_3_7_le_centralizerOfChiefFactor_of_lt_of_induction
    {G : Type*} [Group G] [Finite G] (K R L : Subgroup G) (hind : Theorem37IndHyp K)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) (hL_normal : L.Normal) (hLK : L < K)
    (cf : ChiefFactor G) :
    L ≤ centralizerOfChiefFactor (G := G) K cf := by
  exact
    theorem_3_7_le_centralizerOfChiefFactor_of_le_fitting K L hsolvG hK_normal
      (theorem_3_7_le_fitting_of_lt_of_induction K R L hind hsolvG hodd hKR
        hR_prime hfix hL_normal hLK)
      cf

private theorem CFSG.theorem_3_7_le_centralizerOfChiefFactor_of_sup_eq_lower
    {G : Type*} [Group G] (K L : Subgroup G) [L.Normal] (cf : ChiefFactor G)
    (hLcent : L ≤ centralizerOfChiefFactor (G := G) K cf)
    (hKV : L ⊔ cf.V = K) :
    K ≤ centralizerOfChiefFactor (G := G) K cf := by
  let : cf.V.Normal := cf.isChief.normal_K
  refine (le_centralizerOfChiefFactor_iff (G := G) (H := K) (N := K) (cf := cf)).2 ?_
  constructor
  · exact le_rfl
  · rw [Subgroup.commutator_le]
    intro x hx u hu
    have hxKV : x ∈ L ⊔ cf.V := by simpa [hKV] using hx
    rcases (Subgroup.mem_sup_of_normal_left (s := L) (t := cf.V) (x := x)).1 hxKV with
      ⟨l, hlL, v, hvV, hmul⟩
    have hlcomm : ⁅l, u⁆ ∈ cf.V := by
      have hcomm_le : ⁅L, cf.U⁆ ≤ cf.V :=
        (le_centralizerOfChiefFactor_iff (G := G) (H := K) (N := L) (cf := cf)).1 hLcent |>.2
      exact hcomm_le (Subgroup.commutator_mem_commutator hlL hu)
    have hvcomm : ⁅v, u⁆ ∈ cf.V := by
      have hcomm_le : ⁅cf.V, cf.U⁆ ≤ cf.V :=
        Subgroup.commutator_le_left (H₁ := cf.V) (H₂ := cf.U)
      exact hcomm_le (Subgroup.commutator_mem_commutator hvV hu)
    have hmulV : l * ⁅v, u⁆ * l⁻¹ ∈ cf.V :=
      cf.isChief.normal_K.conj_mem _ hvcomm l
    have hxu : ⁅x, u⁆ = l * ⁅v, u⁆ * l⁻¹ * ⁅l, u⁆ := by
      simpa [hmul] using (commutator_mul_left l v u)
    rw [hxu]
    exact cf.V.mul_mem hmulV hlcomm

private theorem CFSG.theorem_3_7_le_centralizerOfChiefFactor_of_commutator_le_of_inf_eq_lower
    {G : Type*} [Group G] (K L : Subgroup G) (cf : ChiefFactor G)
    (hU_le_K : cf.U ≤ K) (hcommKK_L : ⁅K, K⁆ ≤ L) (hinf : cf.U ⊓ L = cf.V) :
    K ≤ centralizerOfChiefFactor (G := G) K cf := by
  let : cf.U.Normal := cf.isChief.normal_H
  refine (le_centralizerOfChiefFactor_iff (G := G) (H := K) (N := K) (cf := cf)).2 ?_
  constructor
  · exact le_rfl
  · have hcommKU_KK : ⁅K, cf.U⁆ ≤ ⁅K, K⁆ := Subgroup.commutator_mono le_rfl hU_le_K
    have hcommKU_L : ⁅K, cf.U⁆ ≤ L := hcommKU_KK.trans hcommKK_L
    have hcommKU_U : ⁅K, cf.U⁆ ≤ cf.U := Subgroup.commutator_le_right (H₁ := K) (H₂ := cf.U)
    have hcommKU_inf : ⁅K, cf.U⁆ ≤ cf.U ⊓ L := le_inf hcommKU_U hcommKU_L
    simpa [hinf] using hcommKU_inf

private theorem CFSG.theorem_3_7_chiefFactor_inf_eq_lower_of_lower_le_of_not_upper_le
    {G : Type*} [Group G] (cf : ChiefFactor G) (L : Subgroup G) [L.Normal]
    (hV_le_L : cf.V ≤ L) (hU_not_le_L : ¬ cf.U ≤ L) :
    cf.U ⊓ L = cf.V := by
  let : cf.U.Normal := cf.isChief.normal_H
  have hInf_normal : (cf.U ⊓ L).Normal := by infer_instance
  have hV_le_inf : cf.V ≤ cf.U ⊓ L := le_inf cf.isChief.lt.le hV_le_L
  have hInf_le_U : cf.U ⊓ L ≤ cf.U := inf_le_left
  rcases cf.isChief.is_maximal (cf.U ⊓ L) hInf_normal hV_le_inf hInf_le_U with hInf | hInf
  · exact hInf
  · exfalso
    exact hU_not_le_L (by
      simpa [hInf] using (inf_le_right : cf.U ⊓ L ≤ L))

private theorem CFSG.theorem_3_7_sup_eq_of_not_le_maximal
    {G : Type*} [Group G] (K L N : Subgroup G) [L.Normal] [N.Normal]
    (hL_le_K : L ≤ K)
    (hLmax : ∀ M : Subgroup G, M.Normal → L ≤ M → M ≤ K → M = L ∨ M = K)
    (hN_le_K : N ≤ K) (hN_not_le_L : ¬ N ≤ L) :
    L ⊔ N = K := by
  have hsup_le_K : L ⊔ N ≤ K := sup_le hL_le_K hN_le_K
  rcases hLmax (L ⊔ N) (by infer_instance) le_sup_left hsup_le_K with hEq | hEq
  · exfalso
    exact hN_not_le_L (by simpa [hEq] using (le_sup_right : N ≤ L ⊔ N))
  · exact hEq

private theorem CFSG.theorem_3_7_commutator_le_of_maximal_normal_solvable
    {G : Type*} [Group G] [Finite G] (hsolvG : Group.IsSolvable G)
    (K L : Subgroup G) (hL_normal : L.Normal) (hK_normal : K.Normal)
    (hLK : L < K)
    (hLmax : ∀ N : Subgroup G, N.Normal → L ≤ N → N ≤ K → N = L ∨ N = K) :
    ⁅K, K⁆ ≤ L := by
  let cfLK : ChiefFactor G := ⟨L, K, {
    normal_K := hL_normal
    normal_H := hK_normal
    lt := hLK
    is_maximal := hLmax
  }⟩
  let π : G →* G ⧸ L := QuotientGroup.mk' L
  let KL : Subgroup (G ⧸ L) := K.map π
  have hKL_min : IsMinimalNormal KL := by
    simpa [cfLK, π, KL] using chiefFactor_quotient_isMinimalNormal (G := G) cfLK
  have hKL_comm : IsMulCommutative ↥KL := by
    let : KL.Normal := cfLK.isChief.normal_H.map π (QuotientGroup.mk'_surjective L)
    let : IsMinimalNormal KL := hKL_min
    have : Group.IsSolvable (G ⧸ L) := by
      let : Group.IsSolvable G := hsolvG
      infer_instance
    have : Group.IsSolvable ↥KL := by infer_instance
    exact minimalNormal_solvable_isMulCommutative KL
  let : IsMulCommutative ↥KL := hKL_comm
  let e : K ⧸ L.subgroupOf K ≃* KL := quotientSubgroupRangeEquiv K L
  have hquot_comm' : ∀ a b : K ⧸ L.subgroupOf K, a * b = b * a := by
    intro a b
    apply e.injective
    simpa only [map_mul] using IsMulCommutative.is_comm.comm (e a) (e b)
  have hquot_comm : IsMulCommutative (K ⧸ L.subgroupOf K) :=
    IsMulCommutative.mk ⟨hquot_comm'⟩
  have hcomm_sub : _root_.commutator K ≤ L.subgroupOf K :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (G := K) (N := L.subgroupOf K)).1 hquot_comm
  have hmap_le :
      (_root_.commutator K).map K.subtype ≤ (L.subgroupOf K).map K.subtype :=
    Subgroup.map_mono hcomm_sub
  simpa [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hLK.le] using hmap_le

private theorem CFSG.theorem_3_7_coprime_card_of_fixedPointSubgroup_eq_bot
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V] {q : ℕ} [Fact q.Prime]
    [IsElementaryAbelian q V] [MulDistribMulAction A V] [Nontrivial V]
    (R : Subgroup A) (hR_prime : Nat.Prime (Nat.card R))
    (hfix : fixedPointSubgroup (↥R) V = ⊥) :
    Nat.Coprime q (Nat.card R) := by
  have hV_p : IsPGroup q V := IsElementaryAbelian.isPGroup q V
  have hq_dvd_cardV : q ∣ Nat.card V := by
    rcases hV_p.card_eq_or_dvd with h1 | hdiv
    · exfalso
      have hV_card : 1 < Nat.card V := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      exact (ne_of_gt hV_card) (by simp [h1])
    · exact hdiv
  refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ?_
  intro hq_dvd_cardR
  rcases (Nat.dvd_prime hR_prime).1 hq_dvd_cardR with h1 | hqeq
  · exact (Fact.out : Nat.Prime q).ne_one h1
  · have hR_p : IsPGroup q ↥R := by
      exact IsPGroup.of_card (G := ↥R) (p := q) (n := 1) (by simp [hqeq])
    have hone_fix : (1 : V) ∈ MulAction.fixedPoints (↥R) V := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨v, hv_fix, hv_ne_one'⟩ :=
      hR_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := V) hq_dvd_cardV hone_fix
    have hv_mem : v ∈ fixedPointSubgroup (↥R) V := by
      simpa [FixedPoints.mem_subgroup] using
        MulAction.mem_fixedPoints.mp hv_fix
    have hv_bot : v ∈ (⊥ : Subgroup V) := by
      simpa [hfix] using hv_mem
    exact hv_ne_one' (Subgroup.mem_bot.mp hv_bot).symm

private theorem CFSG.theorem_3_7_chief_factor_maximal_quotient_exists_pgroup
    {G : Type*} [Group G] [Finite G] (hsolvG : Group.IsSolvable G)
    (K L V : Subgroup G) [V.Normal] [L.Normal]
    (hV_le_L : V ≤ L) (hK_normal : K.Normal) (hLK : L < K)
    (hLmax : ∀ N : Subgroup G, N.Normal → L ≤ N → N ≤ K → N = L ∨ N = K) :
    ∃ p : ℕ, p.Prime ∧
      let πV : G →* G ⧸ V := QuotientGroup.mk' V
      let Lq : Subgroup (G ⧸ V) := L.map πV
      let qLq : G ⧸ V →* (G ⧸ V) ⧸ Lq := QuotientGroup.mk' Lq
      IsPGroup p (↥((K.map πV).map qLq)) := by
  classical
  let cfLK : ChiefFactor G := ⟨L, K, {
    normal_K := inferInstance
    normal_H := hK_normal
    lt := hLK
    is_maximal := hLmax
  }⟩
  obtain ⟨p, hp, hKL_elem⟩ :=
    chiefFactor_quotient_exists_isElementaryAbelian (G := G) hsolvG cfLK
  refine ⟨p, hp, ?_⟩
  let πV : G →* G ⧸ V := QuotientGroup.mk' V
  let Lq : Subgroup (G ⧸ V) := L.map πV
  let qLq : G ⧸ V →* (G ⧸ V) ⧸ Lq := QuotientGroup.mk' Lq
  let e : (G ⧸ V) ⧸ Lq ≃* G ⧸ L :=
    QuotientGroup.quotientQuotientEquivQuotient (N := V) (M := L) hV_le_L
  have hmap_eq :
      ((K.map πV).map qLq).map e.toMonoidHom = K.map (QuotientGroup.mk' L) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨kq, hkqK, hkqy⟩
      rcases Subgroup.mem_map.mp hkqK with ⟨k, hkK, hkqk⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨k, hkK, ?_⟩
      subst y
      subst kq
      change QuotientGroup.mk k =
        QuotientGroup.quotientQuotientEquivQuotient (N := V) (M := L) hV_le_L
          ((QuotientGroup.mk ((QuotientGroup.mk k : G ⧸ V)) :
            (G ⧸ V) ⧸ L.map (QuotientGroup.mk' V)))
      exact
        (QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
          (N := V) (M := L) (h := hV_le_L) k).symm
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨qLq (πV k), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨πV k, Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩, rfl⟩
      · rw [← hkx]
        exact
          QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
            (N := V) (M := L) (h := hV_le_L) k
  let eK : ((K.map πV).map qLq) ≃* (K.map (QuotientGroup.mk' L)) :=
    (Subgroup.equivMapOfInjective ((K.map πV).map qLq) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap_eq)
  exact (IsElementaryAbelian.isPGroup p ↥(K.map (QuotientGroup.mk' L))).of_equiv eK.symm

private theorem CFSG.theorem_3_7_chief_quotient_map_le_ker_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (K L : Subgroup G) (cf : ChiefFactor G)
    (hUq_elem :
      letI : cf.V.Normal := cf.isChief.normal_K
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      IsElementaryAbelian q (↥Uq))
    (hLcent : L ≤ centralizerOfChiefFactor (G := G) K cf) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    letI : IsElementaryAbelian q (↥Uq) := by simpa using hUq_elem
    letI : MulDistribMulAction (G ⧸ cf.V) Uq :=
      MulDistribMulAction.compHom Uq (MulAut.conjNormal (G := G ⧸ cf.V) (H := Uq))
    let ρ : Representation (ZMod q) (G ⧸ cf.V) (Additive Uq) :=
      Theory.Representation.ofElementaryAbelianAction (A := G ⧸ cf.V) (G := Uq) (p := q)
    L.map π ≤ ρ.ker := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  let : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
  let : IsElementaryAbelian q (↥Uq) := by simpa using hUq_elem
  let : MulDistribMulAction (G ⧸ cf.V) Uq :=
    MulDistribMulAction.compHom Uq (MulAut.conjNormal (G := G ⧸ cf.V) (H := Uq))
  let ρ : Representation (ZMod q) (G ⧸ cf.V) (Additive Uq) :=
    Theory.Representation.ofElementaryAbelianAction (A := G ⧸ cf.V) (G := Uq) (p := q)
  change ∀ x ∈ L.map π, x ∈ ρ.ker
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨l, hlL, rfl⟩
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro u
  simp [ρ]
  apply Subtype.ext
  rcases Subgroup.mem_map.mp (Additive.toMul u).2 with ⟨y, hyU, hyu⟩
  have hcomm_le : ⁅L, cf.U⁆ ≤ cf.V :=
    (le_centralizerOfChiefFactor_iff (G := G) (H := K) (N := L) (cf := cf)).1 hLcent |>.2
  have hcommV : ⁅l, y⁆ ∈ cf.V := hcomm_le (Subgroup.commutator_mem_commutator hlL hyU)
  have hq : π ⁅l, y⁆ = 1 := (QuotientGroup.eq_one_iff (N := cf.V) (x := ⁅l, y⁆)).2 hcommV
  have hconj : π l * π y * (π l)⁻¹ = π y := by
    have hcomm :
        π l * π y * (π l)⁻¹ * (π y)⁻¹ = 1 := by
      simpa [π, map_commutatorElement, commutatorElement_def, mul_assoc] using hq
    have := congrArg (fun t => t * π y) hcomm
    simpa [mul_assoc] using this
  calc
    π l * Additive.toMul u * (π l)⁻¹ = π l * π y * (π l)⁻¹ := by rw [← hyu]
    _ = π y := hconj
    _ = Additive.toMul u := hyu


private theorem CFSG.theorem_3_7_chief_conj_range_pCore_eq_bot
    {G : Type*} [Group G] [Finite G] (cf : ChiefFactor G) [cf.V.Normal]
    {q : ℕ} [Fact q.Prime]
    (hUq_elem :
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      IsElementaryAbelian q (↥Uq)) :
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
    pCore q φ.range = ⊥ := by
  classical
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
  let : Uq.Normal := hmin.1
  let : IsElementaryAbelian q (↥Uq) := by simpa using hUq_elem
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  let A : Subgroup (MulAut Uq) := φ.range
  have hUq_p : IsPGroup q Uq := IsElementaryAbelian.isPGroup q Uq
  let P : Subgroup A := pCore q A
  have hP_p : IsPGroup q P := by
    dsimp [P]
    exact pCore_isPGroup (G := A) (p := q)
  have hUq_dvd : q ∣ Nat.card Uq := by
    have hUq_nontrivial : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hmin.2.1
    rcases (IsPGroup.nontrivial_iff_card (p := q) (G := Uq) (hG := hUq_p)).1 hUq_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self q (Nat.pos_iff_ne_zero.mp hn)
  let F : Subgroup Uq := fixedPointSubgroup P Uq
  have hF_ne_bot : F ≠ ⊥ := by
    have hone_fix : (1 : Uq) ∈ MulAction.fixedPoints P Uq := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨u, hu_fix, hu_ne_one'⟩ :=
      hP_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (α := Uq) hUq_dvd hone_fix
    have hu_ne_one : u ≠ 1 := by
      intro hu
      exact hu_ne_one' hu.symm
    intro hbot
    have hu_mem : u ∈ F := by
      change u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup]
      exact MulAction.mem_fixedPoints.mp hu_fix
    have hu_bot : u ∈ (⊥ : Subgroup Uq) := by
      simpa [hbot] using hu_mem
    exact hu_ne_one (Subgroup.mem_bot.mp hu_bot)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have hF_inv : IsInvariant A Uq F := by
    refine ⟨?_⟩
    intro a u
    constructor
    · intro hu
      change u ∈ fixedPointSubgroup P Uq at hu
      change a • u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup] at hu ⊢
      exact smul_mem_fixedPoints_of_normal (H := P) a hu
    · intro hu
      change a • u ∈ fixedPointSubgroup P Uq at hu
      change u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup] at hu ⊢
      have hsmul := smul_mem_fixedPoints_of_normal (H := P) a⁻¹ hu
      intro p
      simpa [mul_smul] using hsmul p
  let Fmap : Subgroup (G ⧸ cf.V) := F.map Uq.subtype
  have hFmap_normal : Fmap.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases Subgroup.mem_map.mp hx with ⟨u, huF, rfl⟩
    let ag : A := ⟨φ g, ⟨g, rfl⟩⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨ag • u, (hF_inv.invariant ag u).1 huF, ?_⟩
    change (((φ g) u : Uq) : G ⧸ cf.V) = g * (u : G ⧸ cf.V) * g⁻¹
    simp [φ, MulAut.conjNormal_apply]
  have hFmap_le_Uq : Fmap ≤ Uq := by
    exact Subgroup.map_subtype_le F
  have hFmap_ne_bot : Fmap ≠ ⊥ := by
    intro hbot
    have : F = ⊥ := by
      exact
        (Subgroup.map_eq_bot_iff_of_injective (H := F) (f := Uq.subtype)
          Uq.subtype_injective).1 (by simpa [Fmap] using hbot)
    exact hF_ne_bot this
  have hFmap_eq_Uq : Fmap = Uq :=
    hmin.2.2 Fmap hFmap_normal hFmap_le_Uq hFmap_ne_bot
  have htop_map_Uq : (⊤ : Subgroup Uq).map Uq.subtype = Uq := by
    simpa [MonoidHom.range_eq_map] using
      (Uq.range_subtype : Uq.subtype.range = Uq)
  have hF_top : F = ⊤ := by
    have hinj : Function.Injective (Subgroup.map Uq.subtype) :=
      Subgroup.map_injective (f := Uq.subtype) Uq.subtype_injective
    apply hinj
    simpa [Fmap, htop_map_Uq] using hFmap_eq_Uq
  have htriv : ActsTrivially (A := P) (G := Uq) := by
    intro a u
    have huF : u ∈ F := by
      simp [F, hF_top]
    exact (FixedPoints.mem_subgroup (M := P) (a := u)).mp huF a
  have hsub : Subsingleton P := by
    refine ⟨?_⟩
    intro a b
    apply Subtype.ext
    ext u
    exact congrArg (fun z : Uq => (z : G ⧸ cf.V))
      ((htriv a u).trans (htriv b u).symm)
  have hcard_one : Nat.card P = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  change P = ⊥
  exact (Subgroup.card_eq_one (H := P)).1 hcard_one

public theorem CFSG.theorem_3_7_chief_factor_bridge {G : Type u37} [Group G] [Finite G]
    (K R : Subgroup G) (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hK_normal : K.Normal) (hKR : K.IsComplement' R)
    (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) :
    ∀ cf : ChiefFactor G, K ≤ centralizerOfChiefFactor (G := G) K cf := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type u37) [Group G'] [Finite G'] (K' R' : Subgroup G'),
      Nat.card G' = n →
      Group.IsSolvable G' →
      Odd (Nat.card G') →
      K'.Normal →
      K'.IsComplement' R' →
      Nat.Prime (Nat.card R') →
      subgroupCentralizerIn K' R' = ⊥ →
      ∀ cf : ChiefFactor G', K' ≤ centralizerOfChiefFactor (G := G') K' cf
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ K' R' hcard hsolvG' hodd' hK'_normal hK'R' hR'_prime hfix' cf0
    by_cases hK'_bot : K' = ⊥
    · simp [hK'_bot]
    have hK'_ne_bot : K' ≠ ⊥ := hK'_bot
    refine
      theorem_3_7_chief_factor_bridge_of_upper_le (G := G') (K := K') (R := R') hsolvG'
        hK'_normal hK'R' hK'_ne_bot hR'_prime hfix' ?_ cf0
    intro cf hU_le_K
    obtain ⟨L, hL_normal, hLK, hLmax⟩ :=
      theorem_3_7_exists_maximal_normal_subgroup_of_ne_bot K' hK'_ne_bot
    have hind : Theorem37IndHyp K' := by
      intro G'' _ _ K'' R'' hlt hsolvG'' hodd'' hK''_normal hK''R'' hR''_prime hfix''
      have hlt' : Nat.card G'' < n := by simpa [hcard] using hlt
      have hbridge :
          ∀ cf : ChiefFactor G'', K'' ≤ centralizerOfChiefFactor (G := G'') K'' cf :=
        ih (Nat.card G'') hlt' G'' K'' R'' rfl hsolvG'' hodd'' hK''_normal hK''R''
          hR''_prime hfix''
      exact
        isNilpotent_of_le_centralizerOfChiefFactor (G := G'') hsolvG'' K'' hK''_normal
          hbridge
    have hLcent :
        L ≤ centralizerOfChiefFactor (G := G') K' cf :=
      theorem_3_7_le_centralizerOfChiefFactor_of_lt_of_induction K' R' L hind hsolvG' hodd'
        hK'_normal hK'R' hR'_prime hfix' hL_normal hLK cf
    by_cases hU_le_L : cf.U ≤ L
    · have hV_le_L : cf.V ≤ L := cf.isChief.lt.le.trans hU_le_L
      have hV_le_K' : cf.V ≤ K' := hV_le_L.trans hLK.1
      let : cf.V.Normal := cf.isChief.normal_K
      let π : G' →* G' ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G' ⧸ cf.V) := cf.U.map π
      let Kq : Subgroup (G' ⧸ cf.V) := K'.map π
      let Lq : Subgroup (G' ⧸ cf.V) := L.map π
      let Rq : Subgroup (G' ⧸ cf.V) := R'.map π
      have hUq_normal : Uq.Normal :=
        cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      let : Uq.Normal := hUq_normal
      have hKq_normal : Kq.Normal := hK'_normal.map π (QuotientGroup.mk'_surjective cf.V)
      have hLq_normal : Lq.Normal := hL_normal.map π (QuotientGroup.mk'_surjective cf.V)
      have hRq_normKq : Rq ≤ Subgroup.normalizer Kq :=
        Subgroup.le_normalizer_of_normal (H := Kq)
      have hKq_normUq : Kq ≤ Subgroup.normalizer Uq := by
        simpa [Kq, Uq, π] using theorem_3_7_chief_quotient_map_le_normalizer K' cf
      have hRq_normUq : Rq ≤ Subgroup.normalizer Uq := by
        simpa [Rq, Uq, π] using theorem_3_7_chief_quotient_map_le_normalizer R' cf
      obtain ⟨q, hq, hUq_elem⟩ :=
        chiefFactor_quotient_exists_isElementaryAbelian (G := G') hsolvG' cf
      let : Fact q.Prime := ⟨hq⟩
      let : IsElementaryAbelian q (↥Uq) := by simpa [π, Uq] using hUq_elem
      let φ : (G' ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
      let : MulDistribMulAction (G' ⧸ cf.V) Uq := MulDistribMulAction.compHom Uq φ
      let ρ : Representation (ZMod q) (G' ⧸ cf.V) (Additive Uq) :=
        Theory.Representation.ofElementaryAbelianAction (A := G' ⧸ cf.V) (G := Uq) (p := q)
      have hρker_eq : ρ.ker = φ.ker := by
        rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
        rw [fixingSubgroupOf_univ_eq_ker_toMulAut]
        rfl
      have hLq_ker : Lq ≤ ρ.ker := by
        simpa [Lq, π, Uq, ρ] using
          theorem_3_7_chief_quotient_map_le_ker_of_le_centralizer
            (K := K') (L := L) (cf := cf) hUq_elem hLcent
      have hLq_kerφ : Lq ≤ φ.ker := by
        simpa [hρker_eq] using hLq_ker
      let : Representation.IsTrivial (ρ.comp Lq.subtype) :=
        isTrivialCompSubtypeOfLeKer (ρ := ρ) (N := Lq) hLq_ker
      let qLq : (G' ⧸ cf.V) →* (G' ⧸ cf.V) ⧸ Lq := QuotientGroup.mk' Lq
      let Kbar : Subgroup ((G' ⧸ cf.V) ⧸ Lq) := Kq.map qLq
      let Rbar : Subgroup ((G' ⧸ cf.V) ⧸ Lq) := Rq.map qLq
      let ρbar : Representation (ZMod q) ((G' ⧸ cf.V) ⧸ Lq) (Additive Uq) :=
        Representation.ofQuotient ρ Lq
      have hcopKR : Nat.Coprime (Nat.card K') (Nat.card R') :=
        theorem_3_7_coprime_card K' R' hK'_normal hK'R' hR'_prime hfix'
      have hKqRq : Kq.IsComplement' Rq := by
        simpa [Kq, Rq, π] using
          isComplement'_map_mk'_of_le_isComplement' K' R' cf.V hV_le_K' hK'R'
      have hRq_prime : Nat.Prime (Nat.card Rq) := by
        simpa [Rq, π] using
          prime_card_map_mk'_of_le_isComplement' K' R' cf.V hV_le_K' hK'R' hR'_prime
      have hcopKqRq : Nat.Coprime (Nat.card Kq) (Nat.card Rq) := by
        simpa [Kq, Rq, π] using
          coprime_card_map_mk'_of_le_isComplement' K' R' cf.V hV_le_K' hK'R' hcopKR
      have hLq_le_Kq : Lq ≤ Kq := by
        exact Subgroup.map_mono hLK.1
      have hKbar_normal : Kbar.Normal := hKq_normal.map qLq (QuotientGroup.mk'_surjective Lq)
      have hKbarRbar : Kbar.IsComplement' Rbar := by
        simpa [Kbar, Rbar, qLq] using
          isComplement'_map_mk'_of_le_isComplement' Kq Rq Lq hLq_le_Kq hKqRq
      have hRbar_prime : Nat.Prime (Nat.card Rbar) := by
        simpa [Kbar, Rbar, qLq] using
          prime_card_map_mk'_of_le_isComplement' Kq Rq Lq hLq_le_Kq hKqRq hRq_prime
      have hsolvK' : Group.IsSolvable K' := by
        let : Group.IsSolvable G' := hsolvG'
        infer_instance
      have hfixKqRq : subgroupCentralizerIn Kq Rq = ⊥ := by
        have hRnormK' : R' ≤ Subgroup.normalizer K' := Subgroup.le_normalizer_of_normal (H := K')
        have hVinv : ∀ r : R', ∀ x ∈ cf.V, (r : G') * x * (r : G')⁻¹ ∈ cf.V := by
          intro r x hx
          exact cf.isChief.normal_K.conj_mem x hx (r : G')
        have hmap :
            subgroupCentralizerIn Kq Rq =
              (subgroupCentralizerIn K' R').map π := by
          simpa [Kq, Rq, π] using
            subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
              K' R' cf.V hRnormK' hsolvK' hcopKR hVinv
        simpa [hfix'] using hmap
      have hsolvKq : Group.IsSolvable Kq := by
        let : Group.IsSolvable G' := hsolvG'
        infer_instance
      have hfixbar : subgroupCentralizerIn Kbar Rbar = ⊥ := by
        have hLqinv : ∀ r : Rq, ∀ x ∈ Lq, (r : G' ⧸ cf.V) * x * (r : G' ⧸ cf.V)⁻¹ ∈ Lq := by
          intro r x hx
          exact hLq_normal.conj_mem x hx (r : G' ⧸ cf.V)
        have hmap :
            subgroupCentralizerIn Kbar Rbar =
              (subgroupCentralizerIn Kq Rq).map qLq := by
          simpa [Kbar, Rbar, qLq] using
            subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
              Kq Rq Lq hRq_normKq hsolvKq hcopKqRq hLqinv
        simpa [hfixKqRq] using hmap
      have hfixRq_fp : fixedPointSubgroup (↥Rq) Uq = ⊥ := by
        simpa [Rq, Uq, π] using
          theorem_3_7_chief_quotient_R_fixedPointSubgroup_eq_bot
            K' R' hsolvG' hK'_normal hK'R' hR'_prime hfix' cf hU_le_K
      have hfixRq_subspace : ρ.fixedSubspace Rq = ⊥ := by
        simpa [ρ] using
          theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot
            (A := G' ⧸ cf.V) (V := Uq) (q := q) Rq hfixRq_fp
      have hfixRbar_subspace : ρbar.fixedSubspace Rbar = ⊥ := by
        rw [show Rbar = Rq.map qLq by rfl]
        rw [show ρbar = Representation.ofQuotient ρ Lq by rfl]
        rw [fixedSubspace_map_mk'_ofQuotient_eq (ρ := ρ) (N := Lq) (R := Rq)]
        exact hfixRq_subspace
      obtain ⟨p, hp, hKbar_p⟩ :=
        theorem_3_7_chief_factor_maximal_quotient_exists_pgroup
          hsolvG' K' L cf.V hV_le_L hK'_normal hLK hLmax
      have hKbar_p' : IsPGroup p Kbar := by
        simpa [Kbar, Kq, Lq, π, qLq] using hKbar_p
      have hKq_ker : Kq ≤ ρ.ker := by
        by_cases hpq : p = q
        · have hKbar_q : IsPGroup q Kbar := by simpa [hpq] using hKbar_p'
          have hpcore_bot : pCore q φ.range = ⊥ := by
            simpa [π, Uq, φ] using theorem_3_7_chief_conj_range_pCore_eq_bot (cf := cf) hUq_elem
          let φK : Kq →* φ.range := φ.rangeRestrict.comp Kq.subtype
          have hLqsub_kerφK : Lq.subgroupOf Kq ≤ φK.ker := by
            intro x hx
            rw [MonoidHom.mem_ker]
            apply Subtype.ext
            change φ ((x : Kq) : G' ⧸ cf.V) = 1
            exact hLq_kerφ hx
          let φKquot : Kq ⧸ Lq.subgroupOf Kq →* φ.range :=
            QuotientGroup.lift (Lq.subgroupOf Kq) φK (by
              intro x hx
              apply Subtype.ext
              change φ ((x : Kq) : G' ⧸ cf.V) = 1
              exact hLq_kerφ hx)
          let eKL : Kq ⧸ Lq.subgroupOf Kq ≃* Kbar := quotientSubgroupRangeEquiv Kq Lq
          let ψ : Kbar →* φ.range := φKquot.comp eKL.symm.toMonoidHom
          have hφK_range : φK.range = Kq.map φ.rangeRestrict := by
            ext x
            constructor
            · rintro ⟨k, rfl⟩
              exact Subgroup.mem_map_of_mem φ.rangeRestrict k.2
            · rintro ⟨k, hk, rfl⟩
              exact ⟨⟨k, hk⟩, rfl⟩
          have hφKquot_range : φKquot.range = φK.range := by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (N := Lq.subgroupOf Kq) y
              exact ⟨k, rfl⟩
            · rintro ⟨k, rfl⟩
              exact ⟨QuotientGroup.mk k, rfl⟩
          have hψ_range : ψ.range = φKquot.range := by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              exact ⟨eKL.symm y, rfl⟩
            · rintro ⟨y, rfl⟩
              refine ⟨eKL y, ?_⟩
              simp [ψ]
          have hψrange_q : IsPGroup q ψ.range := by
            have htop_q : IsPGroup q (⊤ : Subgroup Kbar) := by
              simpa using hKbar_q.to_subgroup (⊤ : Subgroup Kbar)
            have hmap_q : IsPGroup q ((⊤ : Subgroup Kbar).map ψ) :=
              IsPGroup.map (p := q) (H := (⊤ : Subgroup Kbar)) htop_q ψ
            rw [← MonoidHom.range_eq_map] at hmap_q
            exact hmap_q
          have hKimg_q : IsPGroup q (Kq.map φ.rangeRestrict) := by
            rw [← hφK_range, ← hφKquot_range, ← hψ_range]
            exact hψrange_q
          have hKimg_normal : (Kq.map φ.rangeRestrict).Normal := by
            exact hKq_normal.map φ.rangeRestrict φ.rangeRestrict_surjective
          have hKimg_le : Kq.map φ.rangeRestrict ≤ pCore q φ.range := by
            exact le_sSup ⟨hKimg_normal, hKimg_q⟩
          have hKimg_bot_le : Kq.map φ.rangeRestrict ≤ (⊥ : Subgroup φ.range) := by
            simpa [hpcore_bot] using hKimg_le
          have hKimg_bot : Kq.map φ.rangeRestrict = ⊥ := le_antisymm hKimg_bot_le bot_le
          have hKmap_phi_bot : Kq.map φ = ⊥ := by
            have hmap :
                (Kq.map φ.rangeRestrict).map φ.range.subtype = Kq.map φ := by
              ext x
              constructor
              · rintro ⟨y, hy, rfl⟩
                rcases Subgroup.mem_map.mp hy with ⟨k, hk, rfl⟩
                exact Subgroup.mem_map_of_mem φ hk
              · rintro ⟨k, hk, rfl⟩
                refine Subgroup.mem_map.mpr ?_
                exact ⟨⟨φ k, ⟨k, rfl⟩⟩,
                  Subgroup.mem_map_of_mem φ.rangeRestrict hk, rfl⟩
            rw [← hmap, hKimg_bot]
            simp
          have hKq_kerφ : Kq ≤ φ.ker :=
            (Subgroup.map_eq_bot_iff (H := Kq) (f := φ)).1 hKmap_phi_bot
          simpa [hρker_eq] using hKq_kerφ
        · have hq_not_dvd_p : ¬ q ∣ p := by
            intro hqdvd
            rcases (Nat.dvd_prime hp).1 hqdvd with hq1 | hqp
            · exact hq.ne_one hq1
            · exact hpq hqp.symm
          have hp_not_dvd_q : ¬ p ∣ q := by
            intro hpdvd
            rcases (Nat.dvd_prime hq).1 hpdvd with hp1 | hpq'
            · exact hp.ne_one hp1
            · exact hpq hpq'
          have hq_cop_Kbar : Nat.Coprime q (Nat.card Kbar) := by
            have : Fact p.Prime := ⟨hp⟩
            rcases hKbar_p'.exists_card_eq with ⟨n, hcard⟩
            rw [hcard]
            exact Nat.Coprime.pow_right n (((Nat.Prime.coprime_iff_not_dvd hp).2 hp_not_dvd_q).symm)
          have hcharbar : ringChar (ZMod q) = 0 ∨
              (Nat.Prime (ringChar (ZMod q)) ∧ Nat.Coprime (ringChar (ZMod q)) (Nat.card Kbar)) := by
            right
            rw [ZMod.ringChar_zmod_n]
            exact ⟨hq, hq_cop_Kbar⟩
          have hKbar_ker : Kbar ≤ ρbar.ker := by
            by_cases hKbar_bot : Kbar = ⊥
            · rw [hKbar_bot]
              exact bot_le
            · have hfrobbar : IsFrobeniusGroupWithKernelComplement Kbar Rbar :=
                theorem_3_7_frobenius Kbar Rbar hKbar_normal hKbarRbar hKbar_bot hRbar_prime
                  hfixbar
              by_contra hKbar_not_le
              exact (lemma_3_3 Kbar Rbar ρbar hfrobbar hcharbar hKbar_not_le) hfixRbar_subspace
          by_contra hKq_not_le
          have hKbar_not_le :
              ¬ Kbar ≤ ρbar.ker :=
            not_map_le_ker_of_not_le_ker_of_quotient
              (ρ := ρ) (N := Lq) (K := Kq) hKq_not_le
          exact hKbar_not_le hKbar_ker
      have hKq_cent : Kq ≤ ρ.centralizerIn Kq := by
        intro x hx
        exact ⟨hx, hKq_ker hx⟩
      let : MulDistribMulAction Kq Uq := MulDistribMulAction.compHom Uq Kq.subtype
      have hfixKq_top : fixedPointSubgroup (↥Kq) Uq = ⊤ := by
        exact theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn
          (A := G' ⧸ cf.V) (V := Uq) (q := q) Kq hKq_cent
      exact
        theorem_3_7_le_centralizerOfChiefFactor_of_fixedPointSubgroup_top
          K' cf hKq_normUq hfixKq_top
    · have hV_le_K : cf.V ≤ K' :=
        theorem_3_7_chiefFactor_lower_le_kernel K' R' hsolvG' hK'_normal hK'R' hK'_ne_bot hR'_prime
          hfix' cf
      let : cf.V.Normal := cf.isChief.normal_K
      by_cases hV_le_L : cf.V ≤ L
      · exact
          theorem_3_7_le_centralizerOfChiefFactor_of_commutator_le_of_inf_eq_lower K' L cf
            hU_le_K
            (theorem_3_7_commutator_le_of_maximal_normal_solvable hsolvG' K' L hL_normal
              hK'_normal hLK hLmax)
            (theorem_3_7_chiefFactor_inf_eq_lower_of_lower_le_of_not_upper_le cf L hV_le_L
              hU_le_L)
      · exact
          theorem_3_7_le_centralizerOfChiefFactor_of_sup_eq_lower K' L cf hLcent
            (theorem_3_7_sup_eq_of_not_le_maximal K' L cf.V hLK.1 hLmax hV_le_K hV_le_L)
  exact hP (Nat.card G) G K R rfl hsolvG hodd hK_normal hKR hR_prime hfix

public theorem CFSG.theorem_3_7 {G : Type u37} [Group G] [Finite G] (K R : Subgroup G)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hKR : K.IsComplement' R) (hR_prime : Nat.Prime (Nat.card R))
    (hfix : subgroupCentralizerIn K R = ⊥) :
    Group.IsNilpotent K := by
  exact
    isNilpotent_of_le_centralizerOfChiefFactor (G := G) hsolvG K hK_normal
      (theorem_3_7_chief_factor_bridge K R hsolvG hodd hK_normal hKR hR_prime hfix)

/-- Helper lemma extracted from `faithful_on_fitting_of_coprime`:
If a group element `a` acts trivially on the Fitting subgroup of `G`,
and its order is coprime to `|G|`, then it acts trivially on all of `G`. -/
private theorem CFSG.element_actsTrivially_of_centralizes_fitting_of_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (a : A) (ha_fitting : ∀ f : fittingSubgroup G, a • (f : G) = (f : G)) :
    ∀ g : G, a • g = g := by
  classical
  have hcop_a : Nat.Coprime (orderOf a) (Nat.card G) :=
    Nat.Coprime.of_dvd_left (orderOf_dvd_natCard a) hcoprime
  intro g
  set x : G := g⁻¹ * (a • g) with hx_def
  have hx_centralizer :
      x ∈ Subgroup.centralizer (fittingSubgroup G : Set G) := by
    refine (Subgroup.mem_centralizer_iff (g := x) (s := (fittingSubgroup G : Set G))).2 ?_
    intro f hf
    have hf_fix : a • (f : G) = f := ha_fitting ⟨f, hf⟩
    have hconj : g * f * g⁻¹ ∈ fittingSubgroup G :=
      Subgroup.Normal.conj_mem (inferInstance : (fittingSubgroup G).Normal) f hf g
    have hconj_fix : a • (g * f * g⁻¹) = g * f * g⁻¹ :=
      ha_fitting ⟨g * f * g⁻¹, hconj⟩
    have hconj_eq : g * f * g⁻¹ = (a • g) * f * (a • g)⁻¹ := by
      have : (a • g) * f * (a • g)⁻¹ = g * f * g⁻¹ := by
        simpa [smul_mul', smul_inv', hf_fix, mul_assoc] using hconj_fix
      simpa using this.symm
    have h1 : g * f * g⁻¹ * (a • g) = (a • g) * f := by
      calc
        g * f * g⁻¹ * (a • g) = ((a • g) * f * (a • g)⁻¹) * (a • g) := by
          simpa [mul_assoc] using congrArg (fun t => t * (a • g)) hconj_eq
        _ = (a • g) * f := by simp [mul_assoc]
    have h2 : f * g⁻¹ * (a • g) = g⁻¹ * (a • g) * f := by
      have := congrArg (fun t : G => g⁻¹ * t) h1
      simpa [mul_assoc] using this
    simpa [hx_def, mul_assoc] using h2
  have hx_mem_F : x ∈ fittingSubgroup G :=
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := G) hsolv) hx_centralizer
  have hx_fix : a • x = x := by
    have := ha_fitting ⟨x, hx_mem_F⟩
    simpa using this
  have hx_fix_pow : ∀ n : ℕ, (a ^ n) • x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, mul_smul, hx_fix, ih]
  have ha_g : a • g = g * x := by simp [hx_def]
  have hpow : ∀ n : ℕ, (a ^ n) • g = g * x ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (a ^ (n + 1)) • g = (a ^ n) • (a • g) := by simp [pow_succ, mul_smul]
        _ = (a ^ n) • (g * x) := by simp [ha_g]
        _ = ((a ^ n) • g) * ((a ^ n) • x) := by simp [smul_mul']
        _ = (g * x ^ n) * x := by simp [ih, hx_fix_pow n]
        _ = g * x ^ (n + 1) := by simp [pow_succ, mul_assoc]
  have hx_pow_order : x ^ orderOf a = 1 := by
    have ha_pow : a ^ orderOf a = (1 : A) := pow_orderOf_eq_one a
    have : g = g * x ^ orderOf a := by
      calc
        g = (1 : A) • g := by simp
        _ = (a ^ orderOf a) • g := by simp [ha_pow]
        _ = g * x ^ orderOf a := hpow (orderOf a)
    have := congrArg (fun t : G => g⁻¹ * t) this
    simpa [mul_assoc] using this.symm
  have h_order_dvd : orderOf x ∣ orderOf a :=
    (orderOf_dvd_iff_pow_eq_one).2 hx_pow_order
  have h_order_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_a h_order_dvd (orderOf_dvd_natCard x)
  have hx_one : x = 1 := (orderOf_eq_one_iff).1 h_order_one
  simp [hx_one, ha_g]

/-- If an element `r` centralizes the Fitting subgroup of `K` via conjugation,
and `orderOf r` is coprime to `|K|`, then `r` centralizes all of `K`. -/
private theorem CFSG.conjugatesTrivially_of_conjugatesTriviallyFitting_of_coprime
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (hsolvK : Group.IsSolvable K) (r : G) (hr_cop : Nat.Coprime (orderOf r) (Nat.card K))
    (hr_fit : ∀ f : fittingSubgroupOf (G := G) K, r * (f : G) * r⁻¹ = (f : G)) :
    ∀ k : K, r * (k : G) * r⁻¹ = (k : G) := by
  -- Convert the conjugation action of r on K into a MulDistribMulAction
  have h_r_norm : Subgroup.zpowers r ≤ Subgroup.normalizer K := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    simp [Subgroup.normalizer_eq_top (H := K)]
  have : Subgroup.Normalizes (Subgroup.zpowers r) K := ⟨h_r_norm⟩
  have hsolvK' : Group.IsSolvable (↥K) := hsolvK
  have hcop' : Nat.Coprime (Nat.card (↥(Subgroup.zpowers r))) (Nat.card (↥K)) := by
    have hcard_zp : Nat.card (↥(Subgroup.zpowers r)) = orderOf r := by
      simp
    rw [hcard_zp]
    exact hr_cop
  -- The hypothesis on the Fitting subgroup: the action of r on F(K) is trivial
  let r' : (↥(Subgroup.zpowers r)) := ⟨r, Subgroup.mem_zpowers r⟩
  have ha_fitting : ∀ f : fittingSubgroup (↥K), r' • (f : ↥K) = (f : ↥K) := by
    intro f
    apply Subtype.ext
    have h_f_mem : (f : ↥K) ∈ fittingSubgroup (↥K) := f.property
    have h_img_mem : K.subtype (f : ↥K) ∈ fittingSubgroupOf (G := G) K := by
      rw [fittingSubgroupOf]
      exact Subgroup.mem_map.mpr ⟨f, h_f_mem, rfl⟩
    have h_fit := hr_fit ⟨K.subtype (f : ↥K), h_img_mem⟩
    -- Now use the smul lemma
    simpa [r'] using h_fit
  -- Apply the general lemma
  intro k
  have h_act :=
    element_actsTrivially_of_centralizes_fitting_of_coprime
      (G := ↥K) (A := ↥(Subgroup.zpowers r)) hsolvK' hcop' r' ha_fitting k
  -- Translate back to G
  simpa [r'] using congrArg Subtype.val h_act


private theorem CFSG.theorem_3_8_elementCentralizerIn_eq_subgroupCentralizerIn_of_le
    {G : Type*} [Group G] (K L R : Subgroup G) (hL_le_K : L ≤ K)
    (hcentralizer :
      ∀ x : R, x ≠ 1 →
        elementCentralizerIn K (x : G) = subgroupCentralizerIn K R)
    (x : R) (hx_ne : x ≠ 1) :
    elementCentralizerIn L (x : G) = subgroupCentralizerIn L R := by
  ext y
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    have hyK : y ∈ K := hL_le_K hy.1
    have hyxK : y ∈ elementCentralizerIn K (x : G) := ⟨hyK, hy.2⟩
    rw [hcentralizer x hx_ne] at hyxK
    exact hyxK.2
  · intro hy
    refine ⟨hy.1, ?_⟩
    have hycentR : y ∈ Subgroup.centralizer (R : Set G) := hy.2
    change y ∈ Subgroup.centralizer ({(x : G)} : Set G)
    rw [Subgroup.mem_centralizer_iff] at hycentR ⊢
    intro z hz
    have hz_eq : z = (x : G) := by simpa using hz
    simpa [hz_eq] using hycentR (x : G) x.property

private theorem CFSG.theorem_3_8_elementCentralizerIn_eq_subgroupCentralizerIn_of_zpowers_eq_top
    {G : Type*} [Group G] (K R₀ : Subgroup G) (v : R₀)
    (hvgen : Subgroup.zpowers v = ⊤) :
    elementCentralizerIn K (v : G) = subgroupCentralizerIn K R₀ := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer (R₀ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hrR₀
    have hrmem : (⟨r, hrR₀⟩ : R₀) ∈ Subgroup.zpowers v := by
      simp [hvgen]
    rcases Subgroup.mem_zpowers_iff.mp hrmem with ⟨m, hm⟩
    have hv_comm : (v : G) * x = x * (v : G) := by
      exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    have hcomm : Commute (v : G) x := by
      exact commutatorElement_eq_one_iff_commute.mp
        (commutatorElement_eq_one_iff_mul_comm.mpr hv_comm)
    have hr_comm : ((v : G) ^ m) * x = x * ((v : G) ^ m) := by
      exact (Commute.zpow_left hcomm m).eq
    have hrv : r = (v : G) ^ m := by
      simpa using congrArg Subtype.val hm.symm
    simpa [hrv] using hr_comm
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer ({(v : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx.2) (v : G) v.2).symm

private theorem CFSG.theorem_3_8_elementCentralizerIn_subgroupOf_eq
    {G : Type*} [Group G] (S H : Subgroup G) (x : G) (hx : x ∈ S) :
    elementCentralizerIn (H.subgroupOf S) (⟨x, hx⟩ : S) =
      (elementCentralizerIn H x).subgroupOf S := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyH, hyC⟩
    change (y : G) ∈ H ∧ (y : G) ∈ Subgroup.centralizer ({x} : Set G)
    refine ⟨hyH, ?_⟩
    change y ∈ Subgroup.centralizer ({(⟨x, hx⟩ : S)} : Set S) at hyC
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hyx : (⟨x, hx⟩ : S) * y = y * (⟨x, hx⟩ : S) :=
      (Subgroup.mem_centralizer_iff.mp hyC) (⟨x, hx⟩) (by simp)
    have hz_eq : z = x := by simpa using hz
    simpa [hz_eq] using congrArg Subtype.val hyx
  · intro hy
    change (y : G) ∈ H ∧ (y : G) ∈ Subgroup.centralizer ({x} : Set G) at hy
    rcases hy with ⟨hyH, hyC⟩
    refine ⟨hyH, ?_⟩
    change y ∈ Subgroup.centralizer ({(⟨x, hx⟩ : S)} : Set S)
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hyx : (x : G) * (y : G) = (y : G) * x := hyC x (by simp)
    have hz_eq : z = (⟨x, hx⟩ : S) := by simpa using hz
    apply Subtype.ext
    simpa [hz_eq] using hyx

private theorem CFSG.theorem_3_8_centralizerOfChiefFactorIn_eq_subgroupOf
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (cf : ChiefFactor G) :
    centralizerOfChiefFactorIn (G := G) H cf =
      (centralizerOfChiefFactor (G := G) H cf).subgroupOf H := by
  ext y
  simp [centralizerOfChiefFactorIn, Subgroup.mem_subgroupOf]

private theorem CFSG.theorem_3_8_subambient_card_lt_of_right_lt
    {G : Type*} [Group G] [Finite G] (K R R₀ : Subgroup G) [K.Normal]
    (hgen : K ⊔ R = ⊤) (hcop : Nat.Coprime (Nat.card R) (Nat.card K)) (hR₀R : R₀ < R) :
    Nat.card ↥(K ⊔ R₀) < Nat.card G := by
  let S : Subgroup G := K ⊔ R₀
  have hKR_inf : K ⊓ R = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop.symm).eq_bot
  have hKR_disj : Disjoint K R := by
    rw [disjoint_iff_inf_le, hKR_inf]
  have hmul_eq_univ : (K : Set G) * (R : Set G) = Set.univ := by
    have h_coe_sup : (↑(K ⊔ R) : Set G) = (K : Set G) * (R : Set G) :=
      Subgroup.normal_mul K R
    rw [← h_coe_sup, hgen]
    simp
  have hKR : K.IsComplement' R :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKR_disj hmul_eq_univ
  have hdisj0 : Disjoint K R₀ := hKR.disjoint.mono_right hR₀R.1
  have hcompS : (K.subgroupOf S).IsComplement' (R₀.subgroupOf S) :=
    isComplement'_subgroupOf_sup_of_disjoint K R₀ hdisj0
  have hcardS_eq : Nat.card ↥K * Nat.card ↥R₀ = Nat.card ↥S := by
    simpa [S, natCard_subgroupOf_eq K S le_sup_left,
      natCard_subgroupOf_eq R₀ S le_sup_right] using hcompS.card_mul_card
  have hcardG_eq : Nat.card ↥K * Nat.card ↥R = Nat.card G := by
    simpa using hKR.card_mul_card
  have hR₀_lt_R : Nat.card ↥R₀ < Nat.card ↥R := natCard_lt_of_subgroup_lt hR₀R
  have hlt_mul : Nat.card ↥K * Nat.card ↥R₀ < Nat.card ↥K * Nat.card ↥R := by
    exact Nat.mul_lt_mul_of_pos_left hR₀_lt_R (Nat.card_pos (α := ↥K))
  calc
    Nat.card ↥(K ⊔ R₀) = Nat.card ↥S := rfl
    _ = Nat.card ↥K * Nat.card ↥R₀ := hcardS_eq.symm
    _ < Nat.card ↥K * Nat.card ↥R := hlt_mul
    _ = Nat.card G := hcardG_eq

private theorem CFSG.theorem_3_8_map_fittingSubgroupOf_subambient_le_fitting
    {G : Type*} [Group G] [Finite G] (L R : Subgroup G) :
    let S : Subgroup G := L ⊔ R
    (fittingSubgroupOf (G := S) (L.subgroupOf S)).map S.subtype ≤ fittingSubgroupOf (G := G) L := by
  classical
  let S : Subgroup G := L ⊔ R
  let Lsub : Subgroup S := L.subgroupOf S
  let Fsub : Subgroup S := fittingSubgroupOf (G := S) Lsub
  let e : ↥Lsub ≃* ↥L :=
    Subgroup.subgroupOfEquivOfLe (G := G) (H := L) (K := S) le_sup_left
  let F1 : Subgroup L := (fittingSubgroup (↥Lsub)).map e.toMonoidHom
  have hF1_normal : F1.Normal := by
    exact Subgroup.Normal.map (H := fittingSubgroup (↥Lsub))
      (inferInstance : (fittingSubgroup (↥Lsub)).Normal) e.toMonoidHom e.surjective
  have hF1_nil : Group.IsNilpotent ↥F1 := by
    let ψ : fittingSubgroup (↥Lsub) →* F1 :=
      { toFun := fun x => ⟨e x, ⟨x, x.2, rfl⟩⟩
        map_one' := rfl
        map_mul' := by intro a b; rfl }
    have hψ_surj : Function.Surjective ψ := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact Group.nilpotent_of_surjective (G := ↥(fittingSubgroup (↥Lsub))) (G' := ↥F1) ψ hψ_surj
  have hF1_le_fit : F1 ≤ fittingSubgroup (↥L) := le_sSup ⟨hF1_normal, hF1_nil⟩
  have hcomp :
      L.subtype.comp e.toMonoidHom = S.subtype.comp Lsub.subtype := by
    ext x
    rfl
  have hmap_eq : Fsub.map S.subtype = F1.map L.subtype := by
    calc
      Fsub.map S.subtype
          = ((fittingSubgroup (↥Lsub)).map Lsub.subtype).map S.subtype := by
              simp [Fsub, fittingSubgroupOf]
      _ = (fittingSubgroup (↥Lsub)).map (S.subtype.comp Lsub.subtype) := by
            rw [Subgroup.map_map]
      _ = (fittingSubgroup (↥Lsub)).map (L.subtype.comp e.toMonoidHom) := by rw [hcomp.symm]
      _ = ((fittingSubgroup (↥Lsub)).map e.toMonoidHom).map L.subtype := by
            rw [Subgroup.map_map]
      _ = F1.map L.subtype := rfl
  calc
    (fittingSubgroupOf (G := S) (L.subgroupOf S)).map S.subtype = F1.map L.subtype := hmap_eq
    _ ≤ (fittingSubgroup (↥L)).map L.subtype := Subgroup.map_mono hF1_le_fit
    _ = fittingSubgroupOf (G := G) L := rfl

private theorem CFSG.theorem_3_8_subgroupCentralizerIn_eq_bot_of_element_eq_bot
    {G : Type*} [Group G] (K R : Subgroup G) (r : R)
    (hcent_r : elementCentralizerIn K (r : G) = ⊥) :
    subgroupCentralizerIn K R = ⊥ := by
  apply bot_unique
  intro x hx
  have hx_r : x ∈ elementCentralizerIn K (r : G) := by
    rcases hx with ⟨hxK, hxC⟩
    refine ⟨hxK, ?_⟩
    have hxC' : x ∈ Subgroup.centralizer (R : Set G) := hxC
    change x ∈ Subgroup.centralizer ({(r : G)} : Set G)
    rw [Subgroup.mem_centralizer_iff] at hxC' ⊢
    intro h hh
    have hh_eq : h = (r : G) := by simpa using hh
    simpa [hh_eq] using hxC' (r : G) r.property
  simpa [hcent_r] using hx_r


universe u38

set_option maxHeartbeats 800000 in
public theorem CFSG.theorem_3_8 {G : Type u38} [Group G] [Finite G] (K R : Subgroup G)
    (hsolvG : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hK_normal : K.Normal)
    (hgen : K ⊔ R = ⊤) (hcop : Nat.Coprime (Nat.card R) (Nat.card K))
    (hcentralizer :
      ∀ x : R, x ≠ 1 →
        elementCentralizerIn K (x : G) = subgroupCentralizerIn K R)
    (hfit_fix : subgroupCentralizerIn (fittingSubgroupOf (G := G) K) R = ⊥) :
    ⁅K, R⁆ ≤ fittingSubgroupOf (G := G) K := by
  let F := fittingSubgroupOf (G := G) K
  have hF_le_K : F ≤ K := by
    simpa [F, fittingSubgroupOf] using
      (Subgroup.map_subtype_le (H := K) (K := fittingSubgroup (↥K)))
  have hsolvK : Group.IsSolvable K := by
    have : Group.IsSolvable G := hsolvG
    infer_instance
  -- We prove the result by strong induction on Nat.card G
  -- The induction predicate: for all groups G' with |G'| = n, the theorem holds
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type u38) [Group G'] [Finite G'] (K' R' : Subgroup G'),
      Nat.card G' = n →
      Group.IsSolvable G' →
      Odd (Nat.card G') →
      K'.Normal →
      K' ⊔ R' = ⊤ →
      Nat.Coprime (Nat.card R') (Nat.card K') →
      (∀ x : R', x ≠ 1 → elementCentralizerIn K' (x : G') = subgroupCentralizerIn K' R') →
      subgroupCentralizerIn (fittingSubgroupOf (G := G') K') R' = ⊥ →
      ⁅K', R'⁆ ≤ fittingSubgroupOf (G := G') K'
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ K' R' hn_card hsolvG' hodd' hK'_normal hgen' hcop' hcent' hfit_fix'
    let F' := fittingSubgroupOf (G := G') K'
    have hF'_le_K' : F' ≤ K' := by
      simpa [F', fittingSubgroupOf] using
        (Subgroup.map_subtype_le (H := K') (K := fittingSubgroup (↥K')))
    -- Key lemma: if R' centralizes F', then [K',R'] = ⊥ ≤ F'
    -- This follows from `conjugatesTrivially_of_conjugatesTriviallyFitting_of_coprime`
    -- which is Proposition 1.4: if r (with order coprime to |K'|) centralizes F(K'),
    -- then r centralizes all of K'
    have h_centralizes_F'_implies_done :
        (∀ r : R', ∀ f : F', (r : G') * (f : G') * (r : G')⁻¹ = (f : G')) →
        ⁅K', R'⁆ ≤ F' := by
      intro h_cent
      have hsolvK' : Group.IsSolvable K' := by
        have : Group.IsSolvable G' := hsolvG'
        infer_instance
      -- For each r ∈ R', orderOf r ∣ Nat.card R', and Nat.card R' is coprime to Nat.card K'
      -- So orderOf r is coprime to Nat.card K'
      have h_coprime_each (r : R') : Nat.Coprime (orderOf (r : G')) (Nat.card K') :=
        Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard R' r.property) hcop'
      -- By the private lemma, each r centralizes all of K'
      have h_each_r_cent_K' : ∀ r : R', ∀ k : K', (r : G') * (k : G') * (r : G')⁻¹ = (k : G') := by
        intro r
        have hr_cop := h_coprime_each r
        have hr_fit : ∀ f : fittingSubgroupOf (G := G') K', (r : G') * (f : G') * (r : G')⁻¹ = (f : G') := by
          intro f
          simpa [F'] using h_cent r ⟨f, f.property⟩
        have : K'.Normal := hK'_normal
        exact conjugatesTrivially_of_conjugatesTriviallyFitting_of_coprime
          K' hsolvK' (r : G') hr_cop hr_fit
      -- Now [K',R'] = ⊥ because every element of K' commutes with every element of R'
      have h_comm_eq_bot : ⁅K', R'⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have h := h_each_r_cent_K' ⟨r, hr⟩ ⟨k, hk⟩
        apply mul_inv_eq_iff_eq_mul.mp
        simpa [mul_assoc] using h
      rw [h_comm_eq_bot]
      simp
    -- Case split: does R' centralize F'?
    by_cases hR_cent_F' : ∀ r : R', ∀ f : F', (r : G') * (f : G') * (r : G')⁻¹ = (f : G')
    · -- R' centralizes F', done by the lemma above
      exact h_centralizes_F'_implies_done hR_cent_F'
    · -- R' does not centralize F'
      rcases Classical.not_forall.mp hR_cent_F' with ⟨r, hr⟩
      rcases Classical.not_forall.mp hr with ⟨f, hf⟩
      have h_ne : (r : G') * (f : G') * (r : G')⁻¹ ≠ (f : G') := hf
      -- From coprime condition, K' and R' have trivial intersection
      have h_disjoint_inf : K' ⊓ R' = ⊥ :=
        (Subgroup.disjoint_of_coprime_natCard hcop'.symm).eq_bot
      have h_disjoint : Disjoint K' R' :=
        disjoint_iff_inf_le.mpr (h_disjoint_inf.symm ▸ le_rfl)
      -- Since K' is normal, the set product equals the supremum
      have h_mul_eq_top : (K' : Set G') * (R' : Set G') = Set.univ := by
        have h_coe_sup : (↑(K' ⊔ R') : Set G') = (K' : Set G') * (R' : Set G') :=
          Subgroup.normal_mul K' R'
        rw [← h_coe_sup, hgen']
        simp
      -- So K' and R' are complements in G'
      have h_KR_complement : K'.IsComplement' R' :=
        Subgroup.isComplement'_of_disjoint_and_mul_eq_univ h_disjoint h_mul_eq_top
      have hcomm_le_F : ⁅K', R'⁆ ≤ F' := by
        have hsolvK' : Group.IsSolvable K' := by
          have : Group.IsSolvable G' := hsolvG'
          infer_instance
        have hF'_normal : F'.Normal := fittingSubgroupOf_normal (G := G') K' hK'_normal
        have hF'_nil : Group.IsNilpotent F' := fittingSubgroupOf_isNilpotent (G := G') K'
        let : F'.Normal := hF'_normal
        let qF : G' →* G' ⧸ F' := QuotientGroup.mk' F'
        let Kbar : Subgroup (G' ⧸ F') := K'.map qF
        let Rbar : Subgroup (G' ⧸ F') := R'.map qF
        have hKbar_normal : Kbar.Normal :=
          hK'_normal.map qF (QuotientGroup.mk'_surjective F')
        have hRbar_le_normKbar : Rbar ≤ Subgroup.normalizer Kbar :=
          Subgroup.le_normalizer_of_normal (H := Kbar)
        have hcopKbarRbar : Nat.Coprime (Nat.card Kbar) (Nat.card Rbar) := by
          have hcopKbarR' : Nat.Coprime (Nat.card Kbar) (Nat.card R') :=
            Nat.Coprime.of_dvd_left (Subgroup.card_map_dvd (H := K') (f := qF)) hcop'.symm
          exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := R') (f := qF)) hcopKbarR'
        by_cases h_all_pCore_cent :
            ∀ p : (Nat.card Kbar).primeFactors.attach, ∀ r : R',
              ∀ x : pCore p.1.1 Kbar,
                qF (r : G') * ((Kbar.subtype x : G' ⧸ F')) * (qF (r : G'))⁻¹ =
                  (Kbar.subtype x : G' ⧸ F')
        · have h_cent_fit_bar :
              ∀ r : R', ∀ f : fittingSubgroupOf (G := G' ⧸ F') Kbar,
                qF (r : G') * (f : G' ⧸ F') * (qF (r : G'))⁻¹ = (f : G' ⧸ F') := by
            intro r f
            rcases Subgroup.mem_map.mp f.property with ⟨f0, hf0, hf_eq⟩
            rw [← hf_eq]
            have hpCore_le_cent :
                ∀ p : (Nat.card Kbar).primeFactors.attach,
                  pCore p.1.1 Kbar ≤
                    (Subgroup.centralizer ({qF (r : G')} : Set (G' ⧸ F'))).comap Kbar.subtype := by
              intro p x hx
              change Kbar.subtype x ∈ Subgroup.centralizer ({qF (r : G')} : Set (G' ⧸ F'))
              rw [Subgroup.mem_centralizer_iff]
              intro z hz
              rcases Set.mem_singleton_iff.mp hz with rfl
              have hx' := h_all_pCore_cent p r ⟨x, hx⟩
              apply mul_inv_eq_iff_eq_mul.mp
              simpa [mul_assoc] using hx'
            have hfit_le_sup :
                fittingSubgroup ↥Kbar ≤ ⨆ p : (Nat.card Kbar).primeFactors.attach, pCore p.1.1 Kbar :=
              normal_nilpotent_le_sup_pCore (G := ↥Kbar) (N := fittingSubgroup ↥Kbar)
                (hN := inferInstance) (by infer_instance)
            have hsup_le_cent :
                (⨆ p : (Nat.card Kbar).primeFactors.attach, pCore p.1.1 Kbar) ≤
                  (Subgroup.centralizer ({qF (r : G')} : Set (G' ⧸ F'))).comap Kbar.subtype := by
              refine iSup_le hpCore_le_cent
            have hf0cent :
                f0 ∈ (Subgroup.centralizer ({qF (r : G')} : Set (G' ⧸ F'))).comap Kbar.subtype :=
              (hfit_le_sup.trans hsup_le_cent) hf0
            change Kbar.subtype f0 ∈ Subgroup.centralizer ({qF (r : G')} : Set (G' ⧸ F')) at hf0cent
            rw [Subgroup.mem_centralizer_iff] at hf0cent
            have hmul : qF (r : G') * Kbar.subtype f0 = Kbar.subtype f0 * qF (r : G') :=
              hf0cent (qF (r : G')) (by simp)
            calc
              qF (r : G') * Kbar.subtype f0 * (qF (r : G'))⁻¹
                  = Kbar.subtype f0 * qF (r : G') * (qF (r : G'))⁻¹ := by rw [hmul]
              _ = Kbar.subtype f0 := by simp [mul_assoc]
          have h_each_r_cent_Kbar :
              ∀ r : R', ∀ k : Kbar,
                qF (r : G') * (k : G' ⧸ F') * (qF (r : G'))⁻¹ = (k : G' ⧸ F') := by
            intro r
            have hr_cop :
                Nat.Coprime (orderOf (qF (r : G'))) (Nat.card Kbar) := by
              have hrbar_mem : qF (r : G') ∈ Rbar := Subgroup.mem_map_of_mem qF r.property
              exact Nat.Coprime.of_dvd_left
                (Subgroup.orderOf_dvd_natCard Rbar hrbar_mem) hcopKbarRbar.symm
            have hr_fit :
                ∀ f : fittingSubgroupOf (G := G' ⧸ F') Kbar,
                  qF (r : G') * (f : G' ⧸ F') * (qF (r : G'))⁻¹ = (f : G' ⧸ F') := by
              intro f
              exact h_cent_fit_bar r f
            exact
              conjugatesTrivially_of_conjugatesTriviallyFitting_of_coprime
                Kbar (by infer_instance) (qF (r : G')) hr_cop hr_fit
          have hcomm_bar_eq_bot : ⁅Kbar, Rbar⁆ = ⊥ := by
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
            intro k hk
            rw [Subgroup.mem_centralizer_iff]
            intro rbar hrbar
            rcases Subgroup.mem_map.mp hrbar with ⟨r, hrR, rfl⟩
            have h := h_each_r_cent_Kbar ⟨r, hrR⟩ ⟨k, hk⟩
            apply mul_inv_eq_iff_eq_mul.mp
            simpa [mul_assoc] using h
          have hmap_bot : (⁅K', R'⁆).map qF = ⊥ := by
            rw [Subgroup.map_commutator]
            simpa [Kbar, Rbar] using hcomm_bar_eq_bot
          simpa [qF] using
            (Subgroup.map_eq_bot_iff (H := ⁅K', R'⁆) (f := qF)).mp hmap_bot
        · rcases Classical.not_forall.mp h_all_pCore_cent with ⟨pbar, hpbar⟩
          rcases Classical.not_forall.mp hpbar with ⟨rbar, hrbar⟩
          rcases Classical.not_forall.mp hrbar with ⟨xbar, hxbar⟩
          let p : ℕ := pbar.1
          have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors pbar.1.2
          let Pbar0 : Subgroup Kbar := pCore p Kbar
          let Pbar : Subgroup (G' ⧸ F') := Pbar0.map Kbar.subtype
          have : Pbar0.Characteristic := pCore_characteristic (p := p)
          have hPbar_normal : Pbar.Normal := by infer_instance
          let P : Subgroup G' := Pbar.comap qF
          have hPbar_le_Kbar : Pbar ≤ Kbar := by
            intro z hz
            rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
            exact w.property
          have hP_le_K' : P ≤ K' := by
            intro y hy
            have hybar : qF y ∈ Kbar := hPbar_le_Kbar hy
            have hycomap : y ∈ Subgroup.comap qF Kbar := hybar
            simpa [Kbar, qF, QuotientGroup.comap_map_mk', hF'_le_K'] using hycomap
          have hF'_le_P : F' ≤ P := by
            intro y hyF
            change qF y ∈ Pbar
            have hyq : qF y = 1 := (QuotientGroup.eq_one_iff (N := F') y).2 hyF
            rw [hyq]
            exact Pbar.one_mem
          have hP_normal : P.Normal := by
            exact hPbar_normal.comap qF
          have hFP_eq : fittingSubgroupOf (G := G') P = F' := by
            apply le_antisymm
            · exact
                theorem_3_7_le_fitting_of_nilpotent_normal K' (fittingSubgroupOf (G := G') P)
                  ((fittingSubgroupOf_le (G := G') P).trans hP_le_K')
                  (fittingSubgroupOf_normal (G := G') P hP_normal)
                  (fittingSubgroupOf_isNilpotent (G := G') P)
            · exact
                theorem_3_7_le_fitting_of_nilpotent_normal P F' hF'_le_P hF'_normal hF'_nil
          obtain ⟨pKbar, hpKbar, hKbar_pgroup⟩ :
              ∃ pKbar : ℕ, pKbar.Prime ∧ IsPGroup pKbar Kbar := by
            by_cases hP_eq_K' : P = K'
            · refine ⟨p, hp, ?_⟩
              have hPbar_eq_Kbar : Pbar = Kbar := by
                calc
                  Pbar = P.map qF := by
                    symm
                    simpa [P] using Subgroup.map_comap_eq_self_of_surjective
                      (f := qF) (QuotientGroup.mk'_surjective F') Pbar
                  _ = Kbar := by simp [hP_eq_K', Kbar]
              rw [← hPbar_eq_Kbar]
              exact (pCore_isPGroup (G := Kbar) (p := p)).map Kbar.subtype
            · have hP_lt_K' : P < K' := lt_of_le_of_ne hP_le_K' hP_eq_K'
              let S : Subgroup G' := P ⊔ R'
              have hcardS_lt : Nat.card S < Nat.card G' :=
                theorem_3_7_subambient_card_lt_of_lt K' R' P h_KR_complement hP_lt_K'
              have hsolvS : Group.IsSolvable S := by
                let : Group.IsSolvable G' := hsolvG'
                infer_instance
              have hoddS : Odd (Nat.card S) :=
                odd_of_card_dvd hodd' (Subgroup.card_subgroup_dvd_card S)
              have hPsub_normal : (P.subgroupOf S).Normal :=
                Subgroup.Normal.subgroupOf (G := G') (hH := hP_normal) S
              have hdisjPS : Disjoint P R' := h_KR_complement.disjoint.mono_left hP_lt_K'.1
              have hcompS : (P.subgroupOf S).IsComplement' (R'.subgroupOf S) :=
                isComplement'_subgroupOf_sup_of_disjoint P R' hdisjPS
              have hgenS : P.subgroupOf S ⊔ R'.subgroupOf S = ⊤ := by
                simpa [S] using hcompS.sup_eq_top
              have hcopS :
                  Nat.Coprime (Nat.card (R'.subgroupOf S)) (Nat.card (P.subgroupOf S)) := by
                simpa [Nat.Coprime, S] using
                  (coprime_card_subgroupOf_sup_of_le P K' R' hP_lt_K'.1 hcop'.symm).symm
              have hcentP :
                  ∀ x : R', x ≠ 1 →
                    elementCentralizerIn P (x : G') = subgroupCentralizerIn P R' := by
                intro x hx
                exact
                  theorem_3_8_elementCentralizerIn_eq_subgroupCentralizerIn_of_le
                    K' P R' hP_le_K' hcent' x hx
              have hcentS :
                  ∀ x : R'.subgroupOf S, x ≠ 1 →
                    elementCentralizerIn (P.subgroupOf S) (x : S) =
                      subgroupCentralizerIn (P.subgroupOf S) (R'.subgroupOf S) := by
                intro x hx
                have hx_ne' : (⟨(x : G'), x.2⟩ : R') ≠ 1 := by
                  intro hx1
                  apply hx
                  ext
                  simpa using congrArg Subtype.val hx1
                have hxS : (x : G') ∈ S := (x : S).2
                calc
                  elementCentralizerIn (P.subgroupOf S) (x : S)
                      = (elementCentralizerIn P (x : G')).subgroupOf S := by
                          simpa using
                            theorem_3_8_elementCentralizerIn_subgroupOf_eq S P (x : G') hxS
                  _ = (subgroupCentralizerIn P R').subgroupOf S := by
                        rw [hcentP ⟨(x : G'), x.2⟩ hx_ne']
                  _ = subgroupCentralizerIn (P.subgroupOf S) (R'.subgroupOf S) := by
                        symm
                        exact subgroupCentralizerIn_subgroupOf_eq S P R' le_sup_right
              have hfitP_fix : subgroupCentralizerIn (fittingSubgroupOf (G := G') P) R' = ⊥ := by
                simpa [hFP_eq] using hfit_fix'
              have hfitS :
                  subgroupCentralizerIn (fittingSubgroupOf (G := S) (P.subgroupOf S))
                    (R'.subgroupOf S) = ⊥ := by
                let FPsub : Subgroup S := fittingSubgroupOf (G := S) (P.subgroupOf S)
                have hmap_le :
                    FPsub.map S.subtype ≤ fittingSubgroupOf (G := G') P := by
                  simpa [S] using theorem_3_8_map_fittingSubgroupOf_subambient_le_fitting P R'
                have hmap_fix :
                    subgroupCentralizerIn (FPsub.map S.subtype) R' = ⊥ :=
                  theorem_3_7_subgroupCentralizerIn_eq_bot_of_le
                    (fittingSubgroupOf (G := G') P) R' (FPsub.map S.subtype) hmap_le hfitP_fix
                have hsub_eq : ((FPsub.map S.subtype).subgroupOf S) = FPsub := by
                  ext x
                  constructor
                  · intro hx
                    change (x : G') ∈ FPsub.map S.subtype at hx
                    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
                    have hy_eq : y = x := Subtype.ext hyx
                    simpa [hy_eq] using hy
                  · intro hx
                    change (x : G') ∈ FPsub.map S.subtype
                    exact Subgroup.mem_map_of_mem S.subtype hx
                have hsub_fix :
                    subgroupCentralizerIn ((FPsub.map S.subtype).subgroupOf S) (R'.subgroupOf S) = ⊥ := by
                  calc
                    subgroupCentralizerIn ((FPsub.map S.subtype).subgroupOf S) (R'.subgroupOf S)
                        = (subgroupCentralizerIn (FPsub.map S.subtype) R').subgroupOf S := by
                            exact subgroupCentralizerIn_subgroupOf_eq S (FPsub.map S.subtype) R' le_sup_right
                    _ = (⊥ : Subgroup S) := by simp [hmap_fix]
                simpa [hsub_eq] using hsub_fix
              have hlt' : Nat.card S < n := by simpa [hn_card] using hcardS_lt
              have hcomm_sub :
                  ⁅P.subgroupOf S, R'.subgroupOf S⁆ ≤ fittingSubgroupOf (G := S) (P.subgroupOf S) :=
                ih (Nat.card S) hlt' S (P.subgroupOf S) (R'.subgroupOf S) rfl hsolvS hoddS
                  hPsub_normal hgenS hcopS hcentS hfitS
              have hcommP_le_F : ⁅P, R'⁆ ≤ F' := by
                calc
                  ⁅P, R'⁆ = (⁅P.subgroupOf S, R'.subgroupOf S⁆).map S.subtype := by
                    symm
                    simpa [S] using commutator_subgroupOf_map_eq S R' P le_sup_right le_sup_left
                  _ ≤ (fittingSubgroupOf (G := S) (P.subgroupOf S)).map S.subtype :=
                    Subgroup.map_mono hcomm_sub
                  _ ≤ fittingSubgroupOf (G := G') P := by
                    simpa [S] using theorem_3_8_map_fittingSubgroupOf_subambient_le_fitting P R'
                  _ = F' := hFP_eq
              have hPbar_eq : P.map qF = Pbar := by
                simpa [P] using Subgroup.map_comap_eq_self_of_surjective
                  (f := qF) (QuotientGroup.mk'_surjective F') Pbar
              have hcommPbar_eq_bot : ⁅Pbar, Rbar⁆ = ⊥ := by
                have hmap_bot : (⁅P, R'⁆).map qF = ⊥ := by
                  exact (Subgroup.map_eq_bot_iff (H := ⁅P, R'⁆) (f := qF)).2 (by simpa [qF] using hcommP_le_F)
                calc
                  ⁅Pbar, Rbar⁆ = (⁅P, R'⁆).map qF := by
                    rw [Subgroup.map_commutator, hPbar_eq]
                  _ = ⊥ := hmap_bot
              have hx_fix :
                  qF (rbar : G') * ((Kbar.subtype xbar : G' ⧸ F')) * (qF (rbar : G'))⁻¹ =
                    (Kbar.subtype xbar : G' ⧸ F') := by
                have hPbar_le_cent :
                    Pbar ≤ Subgroup.centralizer (Rbar : Set (G' ⧸ F')) := by
                  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcommPbar_eq_bot
                  exact hcommPbar_eq_bot
                have hxPbar : (Kbar.subtype xbar : G' ⧸ F') ∈ Pbar :=
                  Subgroup.mem_map_of_mem Kbar.subtype xbar.2
                have hxcent := hPbar_le_cent hxPbar
                rw [Subgroup.mem_centralizer_iff] at hxcent
                have hrbar_mem : qF (rbar : G') ∈ Rbar := Subgroup.mem_map_of_mem qF rbar.property
                calc
                  qF (rbar : G') * (Kbar.subtype xbar : G' ⧸ F') * (qF (rbar : G'))⁻¹
                      = (Kbar.subtype xbar : G' ⧸ F') * qF (rbar : G') * (qF (rbar : G'))⁻¹ := by
                          rw [hxcent (qF (rbar : G')) hrbar_mem]
                  _ = (Kbar.subtype xbar : G' ⧸ F') := by simp [mul_assoc]
              exact False.elim (hxbar hx_fix)
          by_cases hR_prime : Nat.Prime (Nat.card R')
          · have h_restricted_chief :
                ∀ cf : ChiefFactor G', cf.U ≤ F' →
                  ⁅K', R'⁆ ≤ centralizerOfChiefFactor (G := G') K' cf := by
              intro cf hU_le_F
              have hV_le_F : cf.V ≤ F' := cf.isChief.lt.le.trans hU_le_F
              have hV_le_K' : cf.V ≤ K' := hV_le_F.trans hF'_le_K'
              let : cf.V.Normal := cf.isChief.normal_K
              let π : G' →* G' ⧸ cf.V := QuotientGroup.mk' cf.V
              let Uq : Subgroup (G' ⧸ cf.V) := cf.U.map π
              let Kq : Subgroup (G' ⧸ cf.V) := K'.map π
              let Fq : Subgroup (G' ⧸ cf.V) := F'.map π
              let Rq : Subgroup (G' ⧸ cf.V) := R'.map π
              have hUq_normal : Uq.Normal :=
                cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
              let : Uq.Normal := hUq_normal
              have hKq_normal : Kq.Normal :=
                hK'_normal.map π (QuotientGroup.mk'_surjective cf.V)
              have hFq_normal : Fq.Normal :=
                hF'_normal.map π (QuotientGroup.mk'_surjective cf.V)
              have hKq_normUq : Kq ≤ Subgroup.normalizer Uq := by
                simpa [Kq, Uq, π] using theorem_3_7_chief_quotient_map_le_normalizer K' cf
              have hRq_normUq : Rq ≤ Subgroup.normalizer Uq := by
                simpa [Rq, Uq, π] using theorem_3_7_chief_quotient_map_le_normalizer R' cf
              obtain ⟨q, hq, hUq_elem⟩ :=
                chiefFactor_quotient_exists_isElementaryAbelian (G := G') hsolvG' cf
              let : Fact q.Prime := ⟨hq⟩
              let : IsElementaryAbelian q (↥Uq) := by simpa [π, Uq] using hUq_elem
              have hUq_min :
                  Uq.Normal ∧ Uq ≠ ⊥ ∧
                    (∀ K : Subgroup (G' ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
                simpa [π, Uq] using chiefFactor_quotient_minimal (G := G') cf
              have hUq_ne_bot : Uq ≠ ⊥ := hUq_min.2.1
              have : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hUq_ne_bot
              let φ : (G' ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
              let : MulDistribMulAction (G' ⧸ cf.V) Uq := MulDistribMulAction.compHom Uq φ
              let ρ : Representation (ZMod q) (G' ⧸ cf.V) (Additive Uq) :=
                Theory.Representation.ofElementaryAbelianAction (A := G' ⧸ cf.V) (G := Uq) (p := q)
              have hρker_eq : ρ.ker = φ.ker := by
                rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
                rw [fixingSubgroupOf_univ_eq_ker_toMulAut]
                rfl
              have hFcent :
                  F' ≤ centralizerOfChiefFactor (G := G') K' cf :=
                theorem_3_7_le_centralizerOfChiefFactor_of_le_fitting
                  K' F' hsolvG' hK'_normal le_rfl cf
              have hFq_ker : Fq ≤ ρ.ker := by
                simpa [Fq, π, Uq, ρ] using
                  theorem_3_7_chief_quotient_map_le_ker_of_le_centralizer
                    (K := K') (L := F') (cf := cf) hUq_elem hFcent
              have hFq_kerφ : Fq ≤ φ.ker := by simpa [hρker_eq] using hFq_ker
              let : Representation.IsTrivial (ρ.comp Fq.subtype) :=
                isTrivialCompSubtypeOfLeKer (ρ := ρ) (N := Fq) hFq_ker
              let qFq : G' ⧸ cf.V →* (G' ⧸ cf.V) ⧸ Fq := QuotientGroup.mk' Fq
              let Kbarcf : Subgroup ((G' ⧸ cf.V) ⧸ Fq) := Kq.map qFq
              let Rbarcf : Subgroup ((G' ⧸ cf.V) ⧸ Fq) := Rq.map qFq
              let ρbar : Representation (ZMod q) ((G' ⧸ cf.V) ⧸ Fq) (Additive Uq) :=
                Representation.ofQuotient ρ Fq
              have hKqRq : Kq.IsComplement' Rq := by
                simpa [Kq, Rq, π] using
                  isComplement'_map_mk'_of_le_isComplement' K' R' cf.V hV_le_K' h_KR_complement
              have hRq_prime : Nat.Prime (Nat.card Rq) := by
                simpa [Rq, π] using
                  prime_card_map_mk'_of_le_isComplement' K' R' cf.V hV_le_K' h_KR_complement hR_prime
              have hcopKqRq : Nat.Coprime (Nat.card Kq) (Nat.card Rq) := by
                simpa [Kq, Rq, π] using
                  coprime_card_map_mk'_of_le_isComplement' K' R' cf.V hV_le_K' h_KR_complement hcop'.symm
              have hFq_le_Kq : Fq ≤ Kq := Subgroup.map_mono hF'_le_K'
              have hKbarcf_normal : Kbarcf.Normal :=
                hKq_normal.map qFq (QuotientGroup.mk'_surjective Fq)
              have hKbarcfRbarcf : Kbarcf.IsComplement' Rbarcf := by
                simpa [Kbarcf, Rbarcf, qFq] using
                  isComplement'_map_mk'_of_le_isComplement' Kq Rq Fq hFq_le_Kq hKqRq
              have hRbarcf_prime : Nat.Prime (Nat.card Rbarcf) := by
                simpa [Kbarcf, Rbarcf, qFq] using
                  prime_card_map_mk'_of_le_isComplement' Kq Rq Fq hFq_le_Kq hKqRq hRq_prime
              have hfixRq_fp : fixedPointSubgroup (↥Rq) Uq = ⊥ := by
                have hfixed_eq :
                    fixedPointSubgroup (↥Rq) (↥Uq) = (subgroupCentralizerIn Uq Rq).subgroupOf Uq := by
                  simpa [Uq, Rq] using
                    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Uq Rq hRq_normUq
                have hcent_quot : subgroupCentralizerIn Uq Rq = ⊥ := by
                  have : cf.U.Normal := cf.isChief.normal_H
                  have hRnormU : R' ≤ Subgroup.normalizer cf.U :=
                    Subgroup.le_normalizer_of_normal (H := cf.U)
                  have hsolvU : Group.IsSolvable ↥cf.U := by
                    let : Group.IsSolvable G' := hsolvG'
                    infer_instance
                  have hcopUR : Nat.Coprime (Nat.card cf.U) (Nat.card R') :=
                    Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le (hU_le_F.trans hF'_le_K')) hcop'.symm
                  have hVinv : ∀ r : R', ∀ x ∈ cf.V, (r : G') * x * (r : G')⁻¹ ∈ cf.V := by
                    intro r x hx
                    exact cf.isChief.normal_K.conj_mem x hx (r : G')
                  have hcent_map :
                      subgroupCentralizerIn (cf.U.map π) (R'.map π) =
                        (subgroupCentralizerIn cf.U R').map π :=
                    subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
                      cf.U R' cf.V hRnormU hsolvU hcopUR hVinv
                  have hcentU_bot : subgroupCentralizerIn cf.U R' = ⊥ :=
                    theorem_3_7_subgroupCentralizerIn_eq_bot_of_le F' R' cf.U hU_le_F hfit_fix'
                  simp [Uq, Rq, π, hcent_map, hcentU_bot]
                change fixedPointSubgroup (↥Rq) (↥Uq) = ⊥
                rw [hfixed_eq, hcent_quot]
                simp
              have hfixRq_subspace : ρ.fixedSubspace Rq = ⊥ := by
                simpa [ρ] using
                  theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot
                    (A := G' ⧸ cf.V) (V := Uq) (q := q) Rq hfixRq_fp
              have hfixRbar_subspace : ρbar.fixedSubspace Rbarcf = ⊥ := by
                rw [show Rbarcf = Rq.map qFq by rfl]
                rw [show ρbar = Representation.ofQuotient ρ Fq by rfl]
                rw [fixedSubspace_map_mk'_ofQuotient_eq (ρ := ρ) (N := Fq) (R := Rq)]
                exact hfixRq_subspace
              let eQQ : ((G' ⧸ cf.V) ⧸ Fq) ≃* (G' ⧸ F') :=
                QuotientGroup.quotientQuotientEquivQuotient (N := cf.V) (M := F') hV_le_F
              have hmap_eq :
                  ((K'.map π).map qFq).map eQQ.toMonoidHom = Kbar := by
                ext x
                constructor
                · rintro ⟨y, hy, rfl⟩
                  rcases Subgroup.mem_map.mp hy with ⟨kq, hkqK, hkqy⟩
                  rcases Subgroup.mem_map.mp hkqK with ⟨k, hkK, hkqk⟩
                  refine Subgroup.mem_map.mpr ?_
                  refine ⟨k, hkK, ?_⟩
                  subst y
                  subst kq
                  change QuotientGroup.mk k =
                    QuotientGroup.quotientQuotientEquivQuotient (N := cf.V) (M := F') hV_le_F
                      ((QuotientGroup.mk ((QuotientGroup.mk k : G' ⧸ cf.V)) :
                        (G' ⧸ cf.V) ⧸ F'.map (QuotientGroup.mk' cf.V)))
                  exact
                    (QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
                      (N := cf.V) (M := F') (h := hV_le_F) k).symm
                · intro hx
                  rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
                  refine Subgroup.mem_map.mpr ?_
                  refine ⟨qFq (π k), ?_, ?_⟩
                  · exact Subgroup.mem_map.mpr ⟨π k, Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩, rfl⟩
                  · rw [← hkx]
                    exact
                      QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
                        (N := cf.V) (M := F') (h := hV_le_F) k
              let eK : Kbarcf ≃* Kbar :=
                (Subgroup.equivMapOfInjective Kbarcf eQQ.toMonoidHom eQQ.injective).trans
                  (MulEquiv.subgroupCongr hmap_eq)
              have hKbarcf_p : IsPGroup pKbar Kbarcf := hKbar_pgroup.of_equiv eK.symm
              by_cases hpq : pKbar = q
              · have hKq_ker : Kq ≤ ρ.ker := by
                  have hKbarcf_q : IsPGroup q Kbarcf := by simpa [hpq] using hKbarcf_p
                  have hpcore_bot : pCore q φ.range = ⊥ := by
                    simpa [π, Uq, φ] using theorem_3_7_chief_conj_range_pCore_eq_bot (cf := cf) hUq_elem
                  let φK : Kq →* φ.range := φ.rangeRestrict.comp Kq.subtype
                  let φKquot : Kq ⧸ Fq.subgroupOf Kq →* φ.range :=
                    QuotientGroup.lift (Fq.subgroupOf Kq) φK (by
                      intro x hx
                      apply Subtype.ext
                      change φ ((x : Kq) : G' ⧸ cf.V) = 1
                      exact hFq_kerφ hx)
                  let eKF : Kq ⧸ Fq.subgroupOf Kq ≃* Kbarcf := quotientSubgroupRangeEquiv Kq Fq
                  let ψ : Kbarcf →* φ.range := φKquot.comp eKF.symm.toMonoidHom
                  have hφK_range : φK.range = Kq.map φ.rangeRestrict := by
                    ext x
                    constructor
                    · rintro ⟨k, rfl⟩
                      exact Subgroup.mem_map_of_mem φ.rangeRestrict k.2
                    · rintro ⟨k, hk, rfl⟩
                      exact ⟨⟨k, hk⟩, rfl⟩
                  have hφKquot_range : φKquot.range = φK.range := by
                    ext x
                    constructor
                    · rintro ⟨y, rfl⟩
                      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (N := Fq.subgroupOf Kq) y
                      exact ⟨k, rfl⟩
                    · rintro ⟨k, rfl⟩
                      exact ⟨QuotientGroup.mk k, rfl⟩
                  have hψ_range : ψ.range = φKquot.range := by
                    ext x
                    constructor
                    · rintro ⟨y, rfl⟩
                      exact ⟨eKF.symm y, rfl⟩
                    · rintro ⟨y, rfl⟩
                      refine ⟨eKF y, ?_⟩
                      simp [ψ]
                  have hψrange_q : IsPGroup q ψ.range := by
                    have htop_q : IsPGroup q (⊤ : Subgroup Kbarcf) := by
                      simpa using hKbarcf_q.to_subgroup (⊤ : Subgroup Kbarcf)
                    have hmap_q : IsPGroup q ((⊤ : Subgroup Kbarcf).map ψ) :=
                      IsPGroup.map (p := q) (H := (⊤ : Subgroup Kbarcf)) htop_q ψ
                    rw [← MonoidHom.range_eq_map] at hmap_q
                    exact hmap_q
                  have hKimg_q : IsPGroup q (Kq.map φ.rangeRestrict) := by
                    rw [← hφK_range, ← hφKquot_range, ← hψ_range]
                    exact hψrange_q
                  have hKimg_normal : (Kq.map φ.rangeRestrict).Normal := by
                    exact hKq_normal.map φ.rangeRestrict φ.rangeRestrict_surjective
                  have hKimg_le : Kq.map φ.rangeRestrict ≤ pCore q φ.range := by
                    exact le_sSup ⟨hKimg_normal, hKimg_q⟩
                  have hKimg_bot : Kq.map φ.rangeRestrict = ⊥ := by
                    exact le_antisymm (by simpa [hpcore_bot] using hKimg_le) bot_le
                  have hKmap_phi_bot : Kq.map φ = ⊥ := by
                    have hmap :
                        (Kq.map φ.rangeRestrict).map φ.range.subtype = Kq.map φ := by
                      ext x
                      constructor
                      · rintro ⟨y, hy, rfl⟩
                        rcases Subgroup.mem_map.mp hy with ⟨k, hk, rfl⟩
                        exact Subgroup.mem_map_of_mem φ hk
                      · rintro ⟨k, hk, rfl⟩
                        refine Subgroup.mem_map.mpr ?_
                        exact ⟨⟨φ k, ⟨k, rfl⟩⟩,
                          Subgroup.mem_map_of_mem φ.rangeRestrict hk, rfl⟩
                    rw [← hmap, hKimg_bot]
                    simp
                  have hKq_kerφ : Kq ≤ φ.ker :=
                    (Subgroup.map_eq_bot_iff (H := Kq) (f := φ)).1 hKmap_phi_bot
                  simpa [hρker_eq] using hKq_kerφ
                have hKq_cent : Kq ≤ ρ.centralizerIn Kq := by
                  intro x hx
                  exact ⟨hx, hKq_ker hx⟩
                let : MulDistribMulAction Kq Uq := MulDistribMulAction.compHom Uq Kq.subtype
                have hfixKq_top : fixedPointSubgroup (↥Kq) Uq = ⊤ := by
                  exact theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn
                    (A := G' ⧸ cf.V) (V := Uq) (q := q) Kq hKq_cent
                exact
                  (Subgroup.commutator_le_left (H₁ := K') (H₂ := R')).trans
                    (theorem_3_7_le_centralizerOfChiefFactor_of_fixedPointSubgroup_top
                      K' cf hKq_normUq hfixKq_top)
              · have hp_not_dvd_q : ¬ pKbar ∣ q := by
                  intro hpdvd
                  rcases (Nat.dvd_prime hq).1 hpdvd with hp1 | hpq'
                  · exact hpKbar.ne_one hp1
                  · exact hpq hpq'
                have hq_cop_Kbarcf : Nat.Coprime q (Nat.card Kbarcf) := by
                  have : Fact pKbar.Prime := ⟨hpKbar⟩
                  rcases hKbarcf_p.exists_card_eq with ⟨n, hcard⟩
                  rw [hcard]
                  exact
                    Nat.Coprime.pow_right n
                      ((Nat.Prime.coprime_iff_not_dvd hpKbar).2 hp_not_dvd_q).symm
                have hq_cop_Rq : Nat.Coprime q (Nat.card Rq) :=
                  theorem_3_7_coprime_card_of_fixedPointSubgroup_eq_bot Rq hRq_prime hfixRq_fp
                have hq_cop_Rbarcf : Nat.Coprime q (Nat.card Rbarcf) := by
                  exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := Rq) (f := qFq)) hq_cop_Rq
                have hq_cop_ambient :
                    Nat.Coprime q (Nat.card (((G' ⧸ cf.V) ⧸ Fq))) := by
                  rw [← hKbarcfRbarcf.card_mul_card]
                  exact hq_cop_Kbarcf.mul_right hq_cop_Rbarcf
                have hcharbar : ringChar (ZMod q) = 0 ∨
                    (Nat.Prime (ringChar (ZMod q)) ∧
                      Nat.Coprime (ringChar (ZMod q)) (Nat.card (((G' ⧸ cf.V) ⧸ Fq)))) := by
                  right
                  rw [ZMod.ringChar_zmod_n]
                  exact ⟨hq, hq_cop_ambient⟩
                have hsolvbar : Group.IsSolvable (((G' ⧸ cf.V) ⧸ Fq)) := by
                  let : Group.IsSolvable G' := hsolvG'
                  infer_instance
                have hoddbar : Odd (Nat.card (((G' ⧸ cf.V) ⧸ Fq))) := by
                  have hdvd1 : Nat.card (G' ⧸ cf.V) ∣ Nat.card G' :=
                    Subgroup.card_quotient_dvd_card (s := cf.V)
                  have hdvd2 : Nat.card (((G' ⧸ cf.V) ⧸ Fq)) ∣ Nat.card (G' ⧸ cf.V) :=
                    Subgroup.card_quotient_dvd_card (s := Fq)
                  exact odd_of_card_dvd hodd' (dvd_trans hdvd2 hdvd1)
                have hcopKbarcfRbarcf :
                    Nat.Coprime (Nat.card Kbarcf) (Nat.card Rbarcf) := by
                  simpa [Kbarcf, Rbarcf, qFq] using
                    coprime_card_map_mk'_of_le_isComplement' Kq Rq Fq hFq_le_Kq hKqRq hcopKqRq
                have hcomm_bar_le :
                    ⁅Rbarcf, Kbarcf⁆ ≤ ρbar.centralizerIn Kbarcf := by
                  exact
                    theorem_3_4 (G := ((G' ⧸ cf.V) ⧸ Fq)) (F := ZMod q) (V := Additive ↥Uq)
                      (K := Kbarcf) (R := Rbarcf) (ρ := ρbar) hsolvbar hoddbar hKbarcf_normal
                      hKbarcfRbarcf hcopKbarcfRbarcf hRbarcf_prime hcharbar hfixRbar_subspace
                have hcomm_q_le : ⁅Rq, Kq⁆ ≤ ρ.centralizerIn Kq := by
                  simpa [Kbarcf, Rbarcf, qFq] using
                    commutator_le_centralizerIn_of_map_le_centralizerIn_ofQuotient
                      (N := Fq) (K := Kq) (R := Rq) (ρ := ρ) hKq_normal hcomm_bar_le
                have hcomm_map_le :
                    (⁅K', R'⁆).map π ≤ ρ.centralizerIn Kq := by
                  rw [Subgroup.map_commutator]
                  simpa [Kq, Rq, π, Subgroup.commutator_comm] using hcomm_q_le
                have hcomm_fixed :
                    ∀ c : ↥(⁅K', R'⁆), ∀ u : Uq,
                      π (c : G') * u * (π (c : G'))⁻¹ = u := by
                  intro c u
                  have hc_map : π (c : G') ∈ (⁅K', R'⁆).map π :=
                    Subgroup.mem_map_of_mem π c.property
                  have hc_cent : π (c : G') ∈ ρ.centralizerIn Kq := hcomm_map_le hc_map
                  rw [Representation.centralizerIn] at hc_cent
                  have hcKer : π (c : G') ∈ ρ.ker := hc_cent.2
                  rw [MonoidHom.mem_ker] at hcKer
                  have hlin := congrArg
                    (fun f : Module.End (ZMod q) (Additive Uq) => f (Additive.ofMul u)) hcKer
                  have hsmul : π (c : G') • u = u := by
                    dsimp [ρ] at hlin
                    rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul] at hlin
                    exact Additive.ofMul.injective hlin
                  have hval : ((π (c : G')) • u : Uq) = u := hsmul
                  have hconj : (((π (c : G')) • u : Uq) : G' ⧸ cf.V) = u := congrArg Subtype.val hval
                  rw [MulAction.compHom_smul_def] at hconj
                  dsimp [φ] at hconj
                  exact hconj
                have hcomm_cent_self :
                    ⁅K', R'⁆ ≤ centralizerOfChiefFactor (G := G') ⁅K', R'⁆ cf :=
                  theorem_3_7_le_centralizerOfChiefFactor_of_quotient_conj_fixed
                    (⁅K', R'⁆) cf hcomm_fixed
                intro x hx
                have hxself :
                    x ∈ centralizerOfChiefFactor (G := G') ⁅K', R'⁆ cf := hcomm_cent_self hx
                rcases (mem_centralizerOfChiefFactor (H := ⁅K', R'⁆) (cf := cf) (g := x)).1 hxself with
                  ⟨hxcomm, hxcent⟩
                exact
                  (mem_centralizerOfChiefFactor (H := K') (cf := cf) (g := x)).2
                    ⟨(Subgroup.commutator_le_left (H₁ := K') (H₂ := R')) hxcomm, hxcent⟩
            have hF_eq_restricted :
                F' =
                  (sInf (centralizerOfChiefFactorIn (G := G') K' ''
                    {cf : ChiefFactor G' | cf.U ≤ F'})).map K'.subtype :=
              (proposition_1_2 (G := G') hsolvG' K' hK'_normal).2
            unfold centralizerOfChiefFactorIn at hF_eq_restricted
            rw [hF_eq_restricted]
            intro x hx
            have hxK : x ∈ K' := (Subgroup.commutator_le_left (H₁ := K') (H₂ := R')) hx
            refine Subgroup.mem_map.mpr ?_
            refine ⟨⟨x, hxK⟩, ?_, rfl⟩
            rw [Subgroup.mem_sInf]
            intro Y hY
            rcases hY with ⟨cf, hcf, hYeq⟩
            subst hYeq
            have hgoal :
                (⟨x, hxK⟩ : K') ∈ (centralizerOfChiefFactor (G := G') K' cf).subgroupOf K' := by
              simpa [Subgroup.mem_subgroupOf] using h_restricted_chief cf hcf hx
            simpa [theorem_3_8_centralizerOfChiefFactorIn_eq_subgroupOf (G := G') K' cf] using hgoal
          · have hr_ne_one : r ≠ 1 := by
              intro hr1
              exact h_ne (by simp [hr1])
            have hcardR_gt_one : 1 < Nat.card R' := by
              exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨r, 1, hr_ne_one⟩⟩
            obtain ⟨p0, hp0, hp0dvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hcardR_gt_one)
            have : Fact p0.Prime := ⟨hp0⟩
            obtain ⟨y0, hy0_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥R') p0 hp0dvd
            let R₀ : Subgroup G' := Subgroup.zpowers (y0 : G')
            have hR₀_card : Nat.card R₀ = p0 := by
              calc
                Nat.card R₀ = orderOf (y0 : G') := by
                  dsimp [R₀]
                  exact Nat.card_zpowers (y0 : G')
                _ = orderOf y0 := by rw [Subgroup.orderOf_coe]
                _ = p0 := hy0_order
            have hR₀_prime : Nat.Prime (Nat.card R₀) := by simpa [hR₀_card] using hp0
            have hR₀_le_R' : R₀ ≤ R' := by
              exact (Subgroup.zpowers_le).2 y0.property
            have hR₀_lt_R' : R₀ < R' := by
              refine lt_of_le_of_ne hR₀_le_R' ?_
              intro hEq
              have hcard_eq : Nat.card R' = p0 := by simpa [hEq] using hR₀_card
              have hR'_prime : Nat.Prime (Nat.card R') := by simpa [hcard_eq] using hp0
              exact hR_prime hR'_prime
            let S : Subgroup G' := K' ⊔ R₀
            have hcardS_lt : Nat.card S < Nat.card G' :=
              theorem_3_8_subambient_card_lt_of_right_lt K' R' R₀ hgen' hcop' hR₀_lt_R'
            have hsolvS : Group.IsSolvable S := by
              let : Group.IsSolvable G' := hsolvG'
              infer_instance
            have hoddS : Odd (Nat.card S) :=
              odd_of_card_dvd hodd' (Subgroup.card_subgroup_dvd_card S)
            have hKsub_normal : (K'.subgroupOf S).Normal :=
              Subgroup.Normal.subgroupOf (G := G') (hH := hK'_normal) S
            have hdisj0 : Disjoint K' R₀ := h_KR_complement.disjoint.mono_right hR₀_lt_R'.1
            have hcompS : (K'.subgroupOf S).IsComplement' (R₀.subgroupOf S) :=
              isComplement'_subgroupOf_sup_of_disjoint K' R₀ hdisj0
            have hgenS : K'.subgroupOf S ⊔ R₀.subgroupOf S = ⊤ := by
              simpa [S] using hcompS.sup_eq_top
            have hcopS :
                Nat.Coprime (Nat.card (R₀.subgroupOf S)) (Nat.card (K'.subgroupOf S)) := by
              have hcopR0K : Nat.Coprime (Nat.card R₀) (Nat.card K') :=
                Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hR₀_le_R') hcop'
              simpa [S, natCard_subgroupOf_eq K' S le_sup_left,
                natCard_subgroupOf_eq R₀ S le_sup_right] using hcopR0K
            let x0 : R₀ := ⟨(y0 : G'), Subgroup.mem_zpowers (y0 : G')⟩
            have hx0_ne : x0 ≠ 1 := by
              intro hx1
              have hy0_eq_one : (y0 : G') = 1 := by
                simpa [x0] using congrArg Subtype.val hx1
              have hy0_eq_one_sub : y0 = 1 := Subtype.ext hy0_eq_one
              have hp0_eq_one : p0 = 1 := by
                simpa [hy0_eq_one_sub] using hy0_order.symm
              exact hp0.ne_one hp0_eq_one
            have hx0_gen : Subgroup.zpowers x0 = ⊤ :=
              zpowers_eq_top_of_prime_card_of_ne_one hR₀_prime hx0_ne
            have hcentS :
                ∀ x : R₀.subgroupOf S, x ≠ 1 →
                  elementCentralizerIn (K'.subgroupOf S) (x : S) =
                    subgroupCentralizerIn (K'.subgroupOf S) (R₀.subgroupOf S) := by
              intro x hx
              have hx_ne' : (⟨(x : G'), x.2⟩ : R₀) ≠ 1 := by
                intro hx1
                apply hx
                ext
                simpa using congrArg Subtype.val hx1
              have hxS : (x : G') ∈ S := (x : S).2
              calc
                elementCentralizerIn (K'.subgroupOf S) (x : S)
                    = (elementCentralizerIn K' (x : G')).subgroupOf S := by
                        simpa using theorem_3_8_elementCentralizerIn_subgroupOf_eq S K' (x : G') hxS
                _ = (subgroupCentralizerIn K' R₀).subgroupOf S := by
                      rw [theorem_3_8_elementCentralizerIn_eq_subgroupCentralizerIn_of_zpowers_eq_top
                        K' R₀ ⟨(x : G'), x.2⟩
                          (zpowers_eq_top_of_prime_card_of_ne_one hR₀_prime hx_ne')]
                _ = subgroupCentralizerIn (K'.subgroupOf S) (R₀.subgroupOf S) := by
                      symm
                      exact subgroupCentralizerIn_subgroupOf_eq S K' R₀ le_sup_right
            have hfitS :
                subgroupCentralizerIn (fittingSubgroupOf (G := S) (K'.subgroupOf S))
                  (R₀.subgroupOf S) = ⊥ := by
              let FKsub : Subgroup S := fittingSubgroupOf (G := S) (K'.subgroupOf S)
              have hmap_le : FKsub.map S.subtype ≤ F' := by
                simpa [S] using theorem_3_8_map_fittingSubgroupOf_subambient_le_fitting K' R₀
              have hmap_fix :
                  subgroupCentralizerIn (FKsub.map S.subtype) R' = ⊥ :=
                theorem_3_7_subgroupCentralizerIn_eq_bot_of_le F' R' (FKsub.map S.subtype) hmap_le hfit_fix'
              have hmap_le_K' : FKsub.map S.subtype ≤ K' := hmap_le.trans hF'_le_K'
              have hmap_fix₀_elem :
                  elementCentralizerIn (FKsub.map S.subtype) (x0 : G') = ⊥ := by
                have hx0R' : (⟨(x0 : G'), hR₀_le_R' x0.property⟩ : R') ≠ 1 := by
                  intro hx1
                  apply hx0_ne
                  ext
                  simpa using congrArg Subtype.val hx1
                calc
                  elementCentralizerIn (FKsub.map S.subtype) (x0 : G')
                      = subgroupCentralizerIn (FKsub.map S.subtype) R' := by
                          exact
                            theorem_3_8_elementCentralizerIn_eq_subgroupCentralizerIn_of_le
                              K' (FKsub.map S.subtype) R' hmap_le_K' hcent'
                                ⟨(x0 : G'), hR₀_le_R' x0.property⟩ hx0R'
                  _ = ⊥ := hmap_fix
              have hmap_fix₀ :
                  subgroupCentralizerIn (FKsub.map S.subtype) R₀ = ⊥ :=
                theorem_3_8_subgroupCentralizerIn_eq_bot_of_element_eq_bot
                  (FKsub.map S.subtype) R₀ x0 hmap_fix₀_elem
              have hsub_eq : ((FKsub.map S.subtype).subgroupOf S) = FKsub := by
                ext x
                constructor
                · intro hx
                  change (x : G') ∈ FKsub.map S.subtype at hx
                  rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
                  have hy_eq : y = x := Subtype.ext hyx
                  simpa [hy_eq] using hy
                · intro hx
                  change (x : G') ∈ FKsub.map S.subtype
                  exact Subgroup.mem_map_of_mem S.subtype hx
              have hsub_fix :
                  subgroupCentralizerIn ((FKsub.map S.subtype).subgroupOf S)
                    (R₀.subgroupOf S) = ⊥ := by
                calc
                  subgroupCentralizerIn ((FKsub.map S.subtype).subgroupOf S) (R₀.subgroupOf S)
                      = (subgroupCentralizerIn (FKsub.map S.subtype) R₀).subgroupOf S := by
                          exact subgroupCentralizerIn_subgroupOf_eq S (FKsub.map S.subtype) R₀
                            le_sup_right
                  _ = (⊥ : Subgroup S) := by simp [hmap_fix₀]
              simpa [hsub_eq] using hsub_fix
            have hlt' : Nat.card S < n := by simpa [hn_card] using hcardS_lt
            have hcomm_sub :
                ⁅K'.subgroupOf S, R₀.subgroupOf S⁆ ≤ fittingSubgroupOf (G := S) (K'.subgroupOf S) :=
              ih (Nat.card S) hlt' S (K'.subgroupOf S) (R₀.subgroupOf S) rfl hsolvS hoddS
                hKsub_normal hgenS hcopS hcentS hfitS
            have hcommR₀_le_F : ⁅K', R₀⁆ ≤ F' := by
              calc
                ⁅K', R₀⁆ = (⁅K'.subgroupOf S, R₀.subgroupOf S⁆).map S.subtype := by
                  symm
                  simpa [S] using commutator_subgroupOf_map_eq S R₀ K' le_sup_right le_sup_left
                _ ≤ (fittingSubgroupOf (G := S) (K'.subgroupOf S)).map S.subtype :=
                  Subgroup.map_mono hcomm_sub
                _ ≤ F' := by
                  simpa [S] using theorem_3_8_map_fittingSubgroupOf_subambient_le_fitting K' R₀
            have hq_cent₀ : ⁅Kbar, R₀.map qF⁆ = ⊥ := by
              have hmap_bot :
                  (⁅K', R₀⁆).map qF = ⊥ := by
                exact
                  (Subgroup.map_eq_bot_iff (H := ⁅K', R₀⁆) (f := qF)).2
                    (by simpa [qF] using hcommR₀_le_F)
              rw [Subgroup.map_commutator] at hmap_bot
              simpa [qF, Kbar] using hmap_bot
            have hR0bar_cent : subgroupCentralizerIn Kbar (R₀.map qF) = Kbar := by
              rw [subgroupCentralizerIn, inf_eq_left]
              exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hq_cent₀)
            have hRnormK' : R' ≤ Subgroup.normalizer K' := Subgroup.le_normalizer_of_normal (H := K')
            have hFinv : ∀ r : R', ∀ x ∈ F', (r : G') * x * (r : G')⁻¹ ∈ F' := by
              intro r x hx
              exact hF'_normal.conj_mem x hx (r : G')
            have hcent_map_R :
                subgroupCentralizerIn Kbar Rbar = (subgroupCentralizerIn K' R').map qF := by
              simpa [Kbar, Rbar, qF] using
                subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
                  K' R' F' hRnormK' hsolvK' hcop'.symm hFinv
            have hcent_map_R₀ :
                subgroupCentralizerIn Kbar (R₀.map qF) = (subgroupCentralizerIn K' R₀).map qF := by
              have hcopR0K : Nat.Coprime (Nat.card R₀) (Nat.card K') :=
                Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hR₀_le_R') hcop'
              have hR₀normK' : R₀ ≤ Subgroup.normalizer K' :=
                hR₀_le_R'.trans hRnormK'
              have hFinv₀ : ∀ r : R₀, ∀ x ∈ F', (r : G') * x * (r : G')⁻¹ ∈ F' := by
                intro r x hx
                exact hF'_normal.conj_mem x hx (r : G')
              simpa [Kbar, qF] using
                subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
                  K' R₀ F' hR₀normK' hsolvK' hcopR0K.symm hFinv₀
            have hcentR0_eq_R :
                subgroupCentralizerIn K' R₀ = subgroupCentralizerIn K' R' := by
              rw [← theorem_3_8_elementCentralizerIn_eq_subgroupCentralizerIn_of_zpowers_eq_top
                K' R₀ x0 hx0_gen]
              exact hcent' ⟨(x0 : G'), hR₀_le_R' x0.property⟩ (by simpa using hx0_ne)
            have hRbar_cent : subgroupCentralizerIn Kbar Rbar = Kbar := by
              rw [hcent_map_R, ← hcentR0_eq_R, ← hcent_map_R₀]
              exact hR0bar_cent
            have hq_cent : ⁅Kbar, Rbar⁆ = ⊥ := by
              rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
              intro x hx
              have hx_cent : x ∈ subgroupCentralizerIn Kbar Rbar := by
                rw [hRbar_cent]
                exact hx
              exact hx_cent.2
            have hmap_bot : (⁅K', R'⁆).map qF = ⊥ := by
              rw [Subgroup.map_commutator]
              simpa [Kbar, Rbar, qF] using hq_cent
            simpa [qF] using
              (Subgroup.map_eq_bot_iff (H := ⁅K', R'⁆) (f := qF)).mp hmap_bot
      exact hcomm_le_F
  -- Apply the induction to our original group
  exact hP (Nat.card G) G K R rfl hsolvG hodd hK_normal hgen hcop hcentralizer hfit_fix

private theorem CFSG.proposition_3_9_pow_mul_swap_of_relation
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_y : Commute c y) :
    ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
        _ = y * (c ^ n * x * y ^ n) := by
              rw [proposition_3_9_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = y * c ^ n * x * y ^ n := by simp [mul_assoc]
        _ = c ^ n * y * x * y ^ n := by
              have hycn : Commute (c ^ n) y := hc_y.pow_left n
              rw [hycn.eq]
        _ = c ^ n * (y * x) * y ^ n := by simp [mul_assoc]
        _ = c ^ n * (c * x * y) * y ^ n := by rw [hrel]
        _ = (c ^ n * c) * x * (y * y ^ n) := by simp [mul_assoc]
        _ = (c ^ n * c) * x * (y ^ n * y) := by
              have hy_pow_comm : y * y ^ n = y ^ n * y := by
                calc
                  y * y ^ n = y ^ (n + 1) := (pow_succ' y n).symm
                  _ = y ^ n * y := pow_succ y n
              rw [hy_pow_comm]
        _ = c ^ (n + 1) * x * y ^ (n + 1) := by
              simp [pow_succ, mul_assoc]

private theorem CFSG.proposition_3_9_pow_mul_eq_cpow_mul_pow_mul_pow
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_x : Commute c x)
    (hc_y : Commute c y) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (Nat.choose n 2) * x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
        _ = (c ^ (Nat.choose n 2) * x ^ n * y ^ n) * (x * y) := by
              rw [proposition_3_9_pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y n]
        _ = c ^ (Nat.choose n 2) * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * x ^ n * (c ^ n * x * y ^ n) * y := by
              rw [proposition_3_9_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = c ^ (Nat.choose n 2) * (x ^ n * c ^ n) * x * y ^ n * y := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * (c ^ n * x ^ n) * x * y ^ n * y := by
              have hcxnn : Commute (c ^ n) (x ^ n) := (hc_x.pow_left n).pow_right n
              rw [hcxnn.symm.eq]
        _ = (c ^ (Nat.choose n 2) * c ^ n) * (x ^ n * x) * (y ^ n * y) := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose (n + 1) 2) * x ^ (n + 1) * y ^ (n + 1) := by
              have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
                simpa [Nat.choose_one_right, Nat.add_comm] using
                  (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
              rw [hchoose, pow_add, pow_succ, pow_succ]

private theorem CFSG.proposition_3_9_prime_dvd_choose_two {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) :
    p ∣ Nat.choose p 2 := by
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hpodd)
  exact Nat.Prime.dvd_choose_self (Fact.out : Nat.Prime p) (k := 2) (by decide) hlt

private theorem CFSG.proposition_3_9_choose_two_pow_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] {M : Type*} [Group M] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) :
    c ^ Nat.choose p 2 = 1 := by
  rcases proposition_3_9_prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ Nat.choose p 2 = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]

private theorem CFSG.proposition_3_9_pth_mul_eq_mul_pows_of_class2
    {T : Type*} [Group T] {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) (hclass2 : NilpotencyClassLe 2 T)
    (hder_pow : ∀ {x : T}, x ∈ derivedSubgroup T → x ^ p = 1) {u v : T} :
    (u * v) ^ p = u ^ p * v ^ p := by
  have hcomm_le :
      ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ ≤ Subgroup.center T :=
    commutator_le_center_of_le_upperCentralSeries_two (G := T) (⊤ : Subgroup T)
      (by simpa [hclass2])
  have hcomm_mem : ⁅v, u⁆ ∈ Subgroup.center T := by
    exact hcomm_le (Subgroup.commutator_mem_commutator (by simp) (by simp))
  have hc_der : ⁅v, u⁆ ∈ derivedSubgroup T := by
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using
      (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup T)) (H₂ := (⊤ : Subgroup T))
        (by simp) (by simp))
  have hc_choose : ⁅v, u⁆ ^ Nat.choose p 2 = 1 := by
    exact proposition_3_9_choose_two_pow_eq_one (p := p) hpodd (hder_pow hc_der)
  calc
    (u * v) ^ p = ⁅v, u⁆ ^ Nat.choose p 2 * u ^ p * v ^ p := by
      simpa using
        proposition_3_9_pow_mul_eq_cpow_mul_pow_mul_pow u v ⁅v, u⁆
          (by simp [commutatorElement_def, mul_assoc])
          (by
            show Commute ⁅v, u⁆ u
            rw [commute_iff_eq]
            exact (Subgroup.mem_center_iff.mp hcomm_mem u).symm)
          (by
            show Commute ⁅v, u⁆ v
            rw [commute_iff_eq]
            exact (Subgroup.mem_center_iff.mp hcomm_mem v).symm) p
    _ = u ^ p * v ^ p * ⁅v, u⁆ ^ Nat.choose p 2 := by
      have hc_center : ⁅v, u⁆ ^ Nat.choose p 2 ∈ Subgroup.center T :=
        (Subgroup.center T).pow_mem hcomm_mem (Nat.choose p 2)
      have hcomm_uv : Commute (⁅v, u⁆ ^ Nat.choose p 2) (u ^ p * v ^ p) := by
        show Commute (⁅v, u⁆ ^ Nat.choose p 2) (u ^ p * v ^ p)
        rw [commute_iff_eq]
        exact (Subgroup.mem_center_iff.mp hc_center (u ^ p * v ^ p)).symm
      simpa [Commute, mul_assoc] using hcomm_uv.eq
    _ = u ^ p * v ^ p := by simp [hc_choose]

private theorem CFSG.proposition_3_9_exists_elementaryAbelian_p2_preimage_case
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (Z : Subgroup R) [Z.Normal]
    (hZ_le_center : Z ≤ Subgroup.center R) (hZcard : Nat.card Z = p ^ 1)
    (Sbar : Subgroup (R ⧸ Z)) [Sbar.Normal] (hSbar_card : Nat.card Sbar = p ^ 2)
    (hSbar_elem : IsElementaryAbelian p Sbar) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let T : Subgroup R := Sbar.comap q
  have hT_normal : T.Normal := by
    simpa [T, q] using (inferInstance : (Sbar.comap (QuotientGroup.mk' Z)).Normal)
  let : T.Normal := hT_normal
  have hker_le_T : q.ker ≤ T := by
    simpa [T] using (Subgroup.ker_le_comap (f := q) (H := Sbar))
  let ZT : Subgroup T := q.ker.subgroupOf T
  have hZT_card : Nat.card ZT = p ^ 1 := by
    calc
      Nat.card ZT = Nat.card q.ker := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_T).toEquiv
      _ = Nat.card Z := by simp [q, QuotientGroup.ker_mk']
      _ = p ^ 1 := hZcard
  have hT_card : Nat.card T = p ^ 3 := by
    have hquot_card : Nat.card (T ⧸ ZT) = p ^ 2 := by
      simpa [T, ZT, q] using
        (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z)
          (H := Sbar)).trans hSbar_card
    calc
      Nat.card T = Nat.card (T ⧸ ZT) * Nat.card ZT := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := ZT))
      _ = p ^ 2 * p ^ 1 := by rw [hquot_card, hZT_card]
      _ = p ^ 3 := by ring_nf
  let qT : T →* T.map q := q.subgroupMap T
  have hTmap_eq : T.map q = Sbar := by
    simpa [T] using
      (Subgroup.map_comap_eq_self_of_surjective (f := q)
        (h := QuotientGroup.mk'_surjective Z) Sbar)
  have hTmap_comm : IsMulCommutative (T.map q) := by
    rw [hTmap_eq]
    exact hSbar_elem.toIsMulCommutative
  have hder_le_ZT : _root_.commutator T ≤ ZT := by
    let : IsMulCommutative (T.map q) := hTmap_comm
    let : CommGroup ↥qT.range := by infer_instance
    have hquot_comm' : Std.Commutative (· * · : T ⧸ qT.ker → _ → _) := by
      let e : T ⧸ qT.ker ≃* qT.range := QuotientGroup.quotientKerEquivRange qT
      let : CommGroup (T ⧸ qT.ker) := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
      infer_instance
    have hquot_comm : IsMulCommutative (T ⧸ qT.ker) := ⟨hquot_comm'⟩
    have hder_le_ker : _root_.commutator T ≤ qT.ker := by
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := qT.ker)).1 hquot_comm
    simpa [qT, ZT, Subgroup.ker_subgroupMap] using hder_le_ker
  have hZT_le_centerT : ZT ≤ Subgroup.center T := by
    intro z hz
    have hzZ : ((z : T) : R) ∈ Z := by
      change ((z : T) : R) ∈ q.ker at hz
      simpa [q, QuotientGroup.ker_mk'] using hz
    have hzcenter : ((z : T) : R) ∈ Subgroup.center R := hZ_le_center hzZ
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hzcenter) (t : R)
  have hclassT : NilpotencyClassLe 2 T := by
    have hcomm_sub : _root_.commutator T ≤ Subgroup.center T := hder_le_ZT.trans hZT_le_centerT
    have hL1_le_center :
        (⊤ : Subgroup T).lowerCentralSeries 1 ≤ Subgroup.center T := by
      simpa [Subgroup.top_lowerCentralSeries_one, _root_.commutator_def] using hcomm_sub
    have hL2_bot : (⊤ : Subgroup T).lowerCentralSeries 2 = ⊥ := by
      simpa [Nat.succ_eq_add_one] using
        (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup T) hL1_le_center)
    have hnil : Group.IsNilpotent T :=
      (Subgroup.nilpotent_iff_lowerCentralSeries (G := T)).2 ⟨2, hL2_bot⟩
    let : Group.IsNilpotent T := hnil
    have hclass : Group.nilpotencyClass T ≤ 2 :=
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := T)).1 hL2_bot
    unfold NilpotencyClassLe
    exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := T)).2 hclass
  let φ : T →* ZT :=
    { toFun := fun x =>
        ⟨x ^ p, by
          let xbar : Sbar := ⟨q x, show q (x : R) ∈ Sbar from x.2⟩
          have hxbar_pow : xbar ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p Sbar) xbar
          have hxpow_one : (qT x) ^ p = 1 := by
            apply Subtype.ext
            simpa [qT] using congrArg Subtype.val hxbar_pow
          have hxker : x ^ p ∈ qT.ker := by
            rw [MonoidHom.mem_ker]
            simpa [MonoidHom.map_pow] using hxpow_one
          simpa [ZT, q, qT, QuotientGroup.ker_mk', Subgroup.ker_subgroupMap] using hxker⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        have hder_pow : ∀ {z : T}, z ∈ derivedSubgroup T → z ^ p = 1 := by
          intro z hz
          have hzZT : z ∈ ZT := hder_le_ZT hz
          have : (⟨z, hzZT⟩ : ZT) ^ Nat.card ZT = 1 := by
            simp
          simpa [hZT_card] using congrArg Subtype.val this
        ext
        simpa using
          congrArg Subtype.val
            (proposition_3_9_pth_mul_eq_mul_pows_of_class2
              (p := p) hpodd hclassT hder_pow (u := x) (v := y)) }
  let ΩT : Subgroup T := omega₁ (G := T) (p := p)
  have hOmega_eq_ker : ΩT = φ.ker := by
    apply le_antisymm
    · intro x hx
      change φ x = 1
      refine Subgroup.closure_induction (k := {z : T | z ^ (p ^ 1) = 1}) (x := x) ?_ ?_ ?_ ?_ hx
      · intro z hz
        ext
        have hz' : (z : T) ^ p = 1 := by
          simpa [pow_one] using hz
        simpa [φ] using congrArg Subtype.val hz'
      · simp [φ]
      · intro a b _ _ ha hb
        simp [MonoidHom.map_mul, ha, hb]
      · intro a _ ha
        simp [MonoidHom.map_inv, ha]
    · intro x hx
      refine Subgroup.subset_closure ?_
      change φ x = 1 at hx
      have hxpow : x ^ p = 1 := by
        simpa [φ] using congrArg Subtype.val hx
      simpa [omega₁, omega, pow_one] using hxpow
  have hOmegaT_card_eq_ker : Nat.card ΩT = Nat.card φ.ker := by
    simp [hOmega_eq_ker]
  have hphi_range_le_p : Nat.card φ.range ≤ p ^ 1 := by
    calc
      Nat.card φ.range ≤ Nat.card (⊤ : Subgroup ZT) := Subgroup.card_le_of_le le_top
      _ = Nat.card ZT := by simp
      _ = p ^ 1 := hZT_card
  have hT_card_expr : Nat.card T = Nat.card φ.range * Nat.card φ.ker := by
    have hquot_card : Nat.card (T ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    calc
      Nat.card T = Nat.card (T ⧸ φ.ker) * Nat.card φ.ker := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker))
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hquot_card]
  have hOmegaT_big : p ^ 2 ≤ Nat.card ΩT := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hmul : p ^ 3 ≤ p ^ 1 * Nat.card φ.ker := by
      calc
        p ^ 3 = Nat.card φ.range * Nat.card φ.ker := by rw [← hT_card, hT_card_expr]
        _ ≤ p ^ 1 * Nat.card φ.ker := Nat.mul_le_mul_right _ hphi_range_le_p
    have hcancel : p ^ 2 ≤ Nat.card φ.ker := by
      have hmul' : p * p ^ 2 ≤ p * Nat.card φ.ker := by
        simpa [pow_succ, pow_one, mul_assoc] using hmul
      exact Nat.le_of_mul_le_mul_left hmul' hp_pos
    simpa [hOmegaT_card_eq_ker] using hcancel
  let Ω : Subgroup R := ΩT.map T.subtype
  have hΩ_normal : Ω.Normal := by
    let : ΩT.Characteristic := omega₁_characteristic T
    simpa [Ω] using (inferInstance : (ΩT.map T.subtype).Normal)
  let : Ω.Normal := hΩ_normal
  have hΩ_card_eq : Nat.card Ω = Nat.card ΩT := by
    exact Subgroup.card_map_of_injective (f := T.subtype) Subtype.coe_injective
  have hΩ_p : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := IsPGroup.iff_card.mp hΩ_p
  have hm_ge_two : 2 ≤ m := by
    have hΩ_big : p ^ 2 ≤ Nat.card Ω := by simpa [hΩ_card_eq] using hOmegaT_big
    have hpow : p ^ 2 ≤ p ^ m := by simpa [hmΩ] using hΩ_big
    exact (Nat.pow_le_pow_iff_right (show 1 < p from (Fact.out : Nat.Prime p).one_lt)).1 hpow
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) Ω inferInstance hmΩ 2 hm_ge_two
  let : K.Normal := hK_normal
  have hOmegaT_pow : ∀ x : ΩT, ((x : T) : R) ^ p = 1 := by
    intro x
    have hxker : (x : T) ∈ φ.ker := by simpa [hOmega_eq_ker] using x.2
    have hxpowT : (x : T) ^ p = 1 := by
      change φ (x : T) = 1 at hxker
      simpa [φ] using congrArg Subtype.val hxker
    simpa using congrArg Subtype.val hxpowT
  have hKpow : ∀ y : K, y ^ p = 1 := by
    intro y
    apply Subtype.ext
    change ((y : R) ^ p = 1)
    have hyΩ : (y : R) ∈ Ω := hK_le_Ω y.2
    rcases Subgroup.mem_map.mp hyΩ with ⟨x, hxΩT, hxy⟩
    simpa [← hxy] using hOmegaT_pow ⟨x, hxΩT⟩
  have hKcyc : IsCyclic (K ⧸ Subgroup.center K) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := K) hKcard
  let : IsCyclic (↥K ⧸ Subgroup.center ↥K) := hKcyc
  let : CommGroup ↥K :=
    commGroupOfCyclicCenterQuotient (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.ker_mk' (Subgroup.center ↥K)).le
  let : IsMulCommutative ↥K :=
    { is_comm := by infer_instance }
  refine ⟨K, hK_normal, hKcard, ?_⟩
  refine {
    toIsMulCommutative := by infer_instance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hKpow

private theorem CFSG.proposition_3_9_exists_elementaryAbelian_p2_cyclic_case
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact (Nat.Prime p)]
    [Fact (IsPGroup p R)] (Z : Subgroup R) [Z.Normal] (hZ_le_center : Z ≤ Subgroup.center R)
    (hZcard : Nat.card Z = p ^ 1) (hQcyc : IsCyclic (R ⧸ Z)) (hncyc : ¬ IsCyclic R) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  obtain ⟨q0, hq0⟩ := (isCyclic_iff_exists_zpowers_eq_top).1 hQcyc
  obtain ⟨x, hxq0⟩ := Quotient.exists_rep q0
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let C : Subgroup R := Subgroup.zpowers x
  have hxq0' : q x = q0 := by simpa [q] using hxq0
  have hq0x : Subgroup.zpowers (q x) = ⊤ := by
    rw [hxq0']
    exact hq0
  have hCmap_top : C.map q = ⊤ := by
    calc
      C.map q = Subgroup.zpowers (q x) := by
        simp [C, q]
      _ = ⊤ := hq0x
  have hCZ_top : C ⊔ Z = ⊤ := by
    apply (Subgroup.eq_top_iff' (H := C ⊔ Z)).2
    intro r
    have hqr : q r ∈ C.map q := by simp [hCmap_top]
    rcases Subgroup.mem_map.mp hqr with ⟨c, hcC, hqc⟩
    have hker : c⁻¹ * r ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) (x := c⁻¹ * r)).1
      have : (q c)⁻¹ * q r = 1 := by
        simpa using congrArg (fun t => t⁻¹ * q r) hqc
      simpa [q, MonoidHom.map_mul] using this
    exact (Subgroup.mem_sup_of_normal_right).2 ⟨c, hcC, c⁻¹ * r, hker, by simp⟩
  have hZ_not_le_C : ¬ Z ≤ C := by
    intro hZleC
    have hC_top : C = ⊤ := by
      simpa [sup_eq_left.mpr hZleC] using hCZ_top
    exact hncyc <|
      (isCyclic_iff_exists_zpowers_eq_top).2 ⟨x, by simpa [C] using hC_top⟩
  let π : R ⧸ Z →* R ⧸ Subgroup.center R :=
    QuotientGroup.map Z (Subgroup.center R) (MonoidHom.id R) hZ_le_center
  have hπ_surj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn y ?_
    intro r
    exact ⟨QuotientGroup.mk' Z r, rfl⟩
  have hQcenter_cyc : IsCyclic (R ⧸ Subgroup.center R) :=
    isCyclic_of_surjective π hπ_surj
  let : IsCyclic (R ⧸ Subgroup.center R) := hQcenter_cyc
  let : CommGroup R :=
    commGroupOfCyclicCenterQuotient (QuotientGroup.mk' (Subgroup.center R))
      (QuotientGroup.ker_mk' (Subgroup.center R)).le
  let C' : Subgroup R := C
  let : C'.Normal := Subgroup.normal_of_isMulCommutative C'
  have hx_ne : x ≠ 1 := by
    intro hx1
    have hCbot : C' = ⊥ := by simp [C', C, hx1]
    have hZ_top : Z = ⊤ := by
      have hCbot' : C = ⊥ := by simpa [C'] using hCbot
      simpa [hCbot'] using hCZ_top
    have hR_card : Nat.card R = p := by simpa [hZ_top] using hZcard
    exact hncyc (isCyclic_of_prime_card (α := R) hR_card)
  have hC_nontriv : Nontrivial C' := by
    have hxC : x ∈ C := Subgroup.mem_zpowers x
    refine ⟨⟨1, ⟨⟨x, by simpa [C'] using hxC⟩, ?_⟩⟩⟩
    intro hEq
    exact hx_ne (Subtype.ext_iff.mp hEq).symm
  have hCp : IsPGroup p C' := (Fact.out : IsPGroup p R).to_subgroup C'
  obtain ⟨mC, hmC⟩ := IsPGroup.iff_card.mp hCp
  have hmC_pos : 0 < mC := by
    by_contra hmC0
    have hmC_eq_zero : mC = 0 := Nat.eq_zero_of_not_pos hmC0
    have hC_card_one : Nat.card C' = 1 := by simpa [hmC_eq_zero] using hmC
    have hC_sub : Subsingleton C' := (Nat.card_eq_one_iff_unique.mp hC_card_one).1
    exact (not_subsingleton_iff_nontrivial.mpr hC_nontriv) hC_sub
  obtain ⟨U, hU_normal, hU_le_C, hUcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p)
      (N := C') inferInstance hmC 1 (Nat.succ_le_of_lt hmC_pos)
  let : U.Normal := hU_normal
  have hU_ne_Z : U ≠ Z := by
    intro hUZ
    exact hZ_not_le_C (hUZ ▸ hU_le_C)
  let Ω : Subgroup R := U ⊔ Z
  let : Ω.Normal := Subgroup.normal_of_isMulCommutative Ω
  have hOmega_pow : ∀ y : Ω, y ^ p = 1 := by
    intro y
    rcases (Subgroup.mem_sup_of_normal_right).1 y.2 with ⟨u, huU, z, hzZ, huz⟩
    have hu_pow : u ^ p = 1 := by
      have : (⟨u, huU⟩ : U) ^ Nat.card U = 1 := by
        simp
      simpa [hUcard] using congrArg Subtype.val this
    have hz_pow : z ^ p = 1 := by
      have : (⟨z, hzZ⟩ : Z) ^ Nat.card Z = 1 := by
        simp
      simpa [hZcard] using congrArg Subtype.val this
    apply Subtype.ext
    change ((y : R) ^ p = 1)
    rw [← huz]
    simp [mul_pow, hu_pow, hz_pow]
  have hU_le_Ω : U ≤ Ω := le_sup_left
  have hZ_le_Ω : Z ≤ Ω := le_sup_right
  have hΩ_p : IsPGroup p Ω := (Fact.out : IsPGroup p R).to_subgroup Ω
  obtain ⟨m, hmΩ⟩ := IsPGroup.iff_card.mp hΩ_p
  have hΩ_card_ne_p : Nat.card Ω ≠ p := by
    intro hΩp
    have hU_eq_Ω : U = Ω :=
      Subgroup.eq_of_le_of_card_ge hU_le_Ω (by simp [hUcard, hΩp])
    have hZ_eq_Ω : Z = Ω :=
      Subgroup.eq_of_le_of_card_ge hZ_le_Ω (by simp [hZcard, hΩp])
    exact hU_ne_Z (hU_eq_Ω.trans hZ_eq_Ω.symm)
  have hm_ge_two : 2 ≤ m := by
    have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
    by_contra hm_lt
    have hm_lt_two : m < 2 := lt_of_not_ge hm_lt
    cases m with
    | zero =>
        have hΩ_card_one : Nat.card Ω = 1 := by simpa using hmΩ
        have hp_le_one : p ≤ 1 := by
          have := Subgroup.card_le_of_le hZ_le_Ω
          simpa [hZcard, hΩ_card_one] using this
        exact (not_le_of_gt hp_one_lt) hp_le_one
    | succ m' =>
        cases m' with
        | zero =>
            exact hΩ_card_ne_p (by simpa using hmΩ)
        | succ m'' =>
            exact False.elim (by omega)
  obtain ⟨K, hK_normal, hK_le_Ω, hKcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) Ω inferInstance hmΩ 2 hm_ge_two
  let : K.Normal := hK_normal
  have hKpow : ∀ y : K, y ^ p = 1 := by
    intro y
    apply Subtype.ext
    simpa using hOmega_pow ⟨(y : R), hK_le_Ω y.2⟩
  have hKcyc : IsCyclic (K ⧸ Subgroup.center K) :=
    IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq (p := p) (G := K) hKcard
  let : IsCyclic (↥K ⧸ Subgroup.center ↥K) := hKcyc
  let : CommGroup ↥K :=
    commGroupOfCyclicCenterQuotient (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.ker_mk' (Subgroup.center ↥K)).le
  let : IsMulCommutative ↥K :=
    { is_comm := by infer_instance }
  refine ⟨K, hK_normal, hKcard, ?_⟩
  refine {
    toIsMulCommutative := by infer_instance
    exponent_dvd_p := ?_
  }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hKpow

universe u

private theorem CFSG.proposition_3_9_exists_elementaryAbelian_p2
    {p : ℕ} {R : Type u} [Group R] [Finite R]
    (hp : Nat.Prime p) (hpodd : p ≠ 2) (hRp : IsPGroup p R) (hncyc : ¬ IsCyclic R) :
    ∃ S : Subgroup R, S.Normal ∧ Nat.card S = p ^ 2 ∧ IsElementaryAbelian p S := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let rec aux {S : Type u} [Group S] [Finite S] [Fact (IsPGroup p S)]
      (hSncyc : ¬ IsCyclic S) :
      ∃ A : Subgroup S, A.Normal ∧ Nat.card A = p ^ 2 ∧ IsElementaryAbelian p A := by
    have hSp : IsPGroup p S := Fact.out
    obtain ⟨nS, hSpow⟩ := IsPGroup.iff_card.mp hSp
    have hnS_pos : 0 < nS := by
      by_contra hnS
      have hnS0 : nS = 0 := Nat.eq_zero_of_not_pos hnS
      have hS_card_one : Nat.card S = 1 := by simpa [hnS0] using hSpow
      let : Subsingleton S := (Nat.card_eq_one_iff_unique.mp hS_card_one).1
      exact hSncyc (isCyclic_of_subsingleton (α := S))
    obtain ⟨k, hk_pos, hcenter_card⟩ :=
      IsPGroup.card_center_eq_prime_pow (G := S) (p := p) hSpow hnS_pos
    obtain ⟨Z, hZ_normal, hZ_le_center, hZcard⟩ :=
      exists_normal_subgroup_card_pow_of_normal (G := S) (p := p)
        (N := Subgroup.center S) inferInstance hcenter_card 1 (Nat.succ_le_of_lt hk_pos)
    let : Z.Normal := hZ_normal
    by_cases hQcyc : IsCyclic (S ⧸ Z)
    · exact
        proposition_3_9_exists_elementaryAbelian_p2_cyclic_case
          (R := S) (p := p) Z hZ_le_center hZcard hQcyc hSncyc
    · have hQp : IsPGroup p (S ⧸ Z) := (Fact.out : IsPGroup p S).to_quotient Z
      have hQ_card : Nat.card S = Nat.card (S ⧸ Z) * p := by
        calc
          Nat.card S = Nat.card (S ⧸ Z) * Nat.card Z := by
            simpa using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := S) (s := Z))
          _ = Nat.card (S ⧸ Z) * p := by simp [hZcard]
      have hQ_lt : Nat.card (S ⧸ Z) < Nat.card S := by
        rw [hQ_card]
        simpa [one_mul] using
          (Nat.mul_lt_mul_of_pos_left ((Fact.out : Nat.Prime p).one_lt)
            (Nat.card_pos (α := S ⧸ Z)))
      let : Fact (IsPGroup p (S ⧸ Z)) := ⟨hQp⟩
      obtain ⟨Sbar, hSbar_normal, hSbar_card, hSbar_elem⟩ := aux (S := S ⧸ Z) hQcyc
      let : Sbar.Normal := hSbar_normal
      exact
        proposition_3_9_exists_elementaryAbelian_p2_preimage_case
          (R := S) (p := p) hpodd Z hZ_le_center hZcard Sbar hSbar_card hSbar_elem
  termination_by Nat.card S
  decreasing_by
    exact hQ_lt
  let : Fact (IsPGroup p R) := ⟨hRp⟩
  exact aux (S := R) hncyc

public theorem CFSG.proposition_3_9 {p : ℕ} {H R : Type*} [Group H] [Finite H] [Nontrivial H]
    [Group R] [Finite R] [MulDistribMulAction R H] (hp : Nat.Prime p) (hp_odd : Odd p)
    (hH_coprime : Nat.Coprime p (Nat.card H)) (hR_pgroup : IsPGroup p R)
    (hregular : ActsRegularly R H) :
    IsCyclic R := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hR_cyc : IsCyclic R
  · exact hR_cyc
  · have hpodd : p ≠ 2 := by
      intro hp2
      have : ¬ Odd (2 : ℕ) := by decide
      exact this (hp2 ▸ hp_odd)
    let : Fact (IsPGroup p R) := ⟨hR_pgroup⟩
    have hH_card_gt_one : 1 < Nat.card H := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    obtain ⟨q, hq_prime, hq_dvd_H⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp (Nat.ne_of_gt hH_card_gt_one)
    let : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨Q₀, hQinv⟩ :=
      exists_invariant_sylow (G := H) (A := R) (p := p) (q := q) hH_coprime
    let Q : Subgroup H := Q₀
    have hQ_ne_bot : Q ≠ ⊥ := Sylow.ne_bot_of_dvd_card (G := H) (p := q) Q₀ hq_dvd_H
    let : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hQ_ne_bot
    have hQ_coprime : Nat.Coprime p (Nat.card Q) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card Q) hH_coprime
    have hQregular : ActsRegularly R Q := by
      intro a ha
      have : IsInvariant (↥(Subgroup.zpowers a)) H Q :=
        { invariant := fun b x => hQinv.invariant (b : R) x }
      simpa [hregular a ha] using
        (fixedPointSubgroup_subtype_eq_local (A := ↥(Subgroup.zpowers a)) (G := H) Q)
    obtain ⟨S, hS_normal, hS_card, hS_elem⟩ :=
      proposition_3_9_exists_elementaryAbelian_p2 (p := p) (R := R) hp hpodd hR_pgroup hR_cyc
    let : IsMulCommutative S := hS_elem.toIsMulCommutative
    let : CommGroup S := IsMulCommutative.instCommGroup
    let : Fact (IsPGroup p S) := ⟨IsElementaryAbelian.isPGroup p S⟩
    have hS_card_gt_one : 1 < Nat.card S := by
      simpa [hS_card] using one_lt_pow₀ hp.one_lt (by decide : 2 ≠ 0)
    let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp hS_card_gt_one
    have hS_exp_eq_p : Monoid.exponent S = p := by
      have hExp_dvd : Monoid.exponent S ∣ p := IsElementaryAbelian.exponent_dvd_p p S
      exact (hp.eq_one_or_self_of_dvd (Monoid.exponent S) hExp_dvd).resolve_left
        (Nat.ne_of_gt Monoid.one_lt_exponent)
    have hS_noncyc : ¬ IsCyclic S := by
      exact (not_isCyclic_iff_exponent_eq_prime hp hS_card).2 hS_exp_eq_p
    let : MulDistribMulAction S Q := MulDistribMulAction.compHom Q S.subtype
    have hfix_top :
        (⨆ (a : S) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) Q) = ⊤ := by
      simpa using proposition_1_16_a (G := Q) (A := S) p hQ_coprime hS_noncyc
    have hall_bot : ∀ a : S, ∀ ha : a ≠ 1, fixedPointSubgroup (↥(Subgroup.zpowers a)) Q = ⊥ := by
      intro a ha
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      let a1 : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
      have hax : (a • x : Q) = x := hx a1
      have haxR : ((a : R) • x : Q) = x := by
        change ((a : R) • x : Q) = x at hax
        exact hax
      have hxR : x ∈ fixedPointSubgroup (↥(Subgroup.zpowers (a : R))) Q := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro y
        exact smul_eq_self_of_mem_zpowers y.2 haxR
      have hfixR_bot : fixedPointSubgroup (↥(Subgroup.zpowers (a : R))) Q = ⊥ :=
        hQregular (a : R) (by
          intro hEq
          exact ha (Subtype.ext hEq))
      simpa [hfixR_bot] using hxR
    have hfix_bot :
        (⨆ (a : S) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) Q) = ⊥ := by
      apply le_antisymm
      · refine iSup_le ?_
        intro a
        refine iSup_le ?_
        intro ha
        simp [hall_bot a ha]
      · exact bot_le
    exact False.elim (top_ne_bot (hfix_top.symm.trans hfix_bot))

section Theorem310

universe u310G u310M

variable {G : Type u310G} [Group G] [Finite G] (K R : Subgroup G)
variable {M : Type u310M} [Group M] [Finite M] [MulDistribMulAction G M] [Nontrivial M]

omit [Finite G] [Finite M] in
private theorem CFSG.theorem_3_10_K_ne_bot
    (hfixK : fixedPointSubgroup (↥K) M = ⊥) :
    K ≠ ⊥ := by
  intro hK_bot
  have hfix_top : fixedPointSubgroup (↥K) M = ⊤ := by
    subst hK_bot
    ext x
    simp [fixedPointSubgroup, FixedPoints.mem_subgroup]
  exact top_ne_bot (hfix_top.symm.trans hfixK)

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_eq_of_nontrivial_le
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M)
    {R₀ : Subgroup G} (hR₀_le : R₀ ≤ R) (hR₀_ne_bot : R₀ ≠ ⊥) :
    letI : MulDistribMulAction (↥R₀) M := MulDistribMulAction.compHom M R₀.subtype
    fixedPointSubgroup (↥R₀) M = fixedPointSubgroup (↥R) M := by
  let : MulDistribMulAction (↥R₀) M := MulDistribMulAction.compHom M R₀.subtype
  let : Nontrivial ↥R₀ := R₀.nontrivial_iff_ne_bot.mpr hR₀_ne_bot
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : R₀)
  have hxR_ne : (⟨(x : G), hR₀_le x.2⟩ : R) ≠ 1 := by
    intro hx1
    apply hx_ne
    ext
    simpa using congrArg Subtype.val hx1
  have hx_fix :
      fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M :=
    hfixR ⟨(x : G), hR₀_le x.2⟩ hxR_ne
  have hfixR_le :
      fixedPointSubgroup (↥R) M ≤ fixedPointSubgroup (↥R₀) M := by
    intro y hy
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy ⊢
    intro r₀
    exact hy ⟨(r₀ : G), hR₀_le r₀.2⟩
  have hzpow_le : Subgroup.zpowers (x : G) ≤ R₀ := (Subgroup.zpowers_le).2 x.2
  have hfixR₀_le :
      fixedPointSubgroup (↥R₀) M ≤ fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M := by
    intro y hy
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy ⊢
    intro z
    exact hy ⟨(z : G), hzpow_le z.2⟩
  exact le_antisymm (le_trans hfixR₀_le hx_fix.le) hfixR_le

private theorem CFSG.theorem_3_10_regular_conj_action
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    letI : K.Normal := hfrob.normal
    letI : MulDistribMulAction (↥R) (↥K) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R K
        (Subgroup.le_normalizer_of_normal (H := K))
    ActsRegularly (↥R) (↥K) := by
  let : K.Normal := hfrob.normal
  let hRnormK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  let : MulDistribMulAction (↥R) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R K hRnormK
  intro x hx
  have hcentx_bot :
      elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hfrob.kernel_ne_bot hfrob.complement_ne_bot
      hfrob.normal hfrob.isComplement').1 hfrob x hx
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyx : x • y = y := hy ⟨x, Subgroup.mem_zpowers x⟩
  have hycomm : (y : G) * (x : G) = (x : G) * (y : G) := by
    have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = (y : G) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRnormK] using
        congrArg Subtype.val hyx
    have := congrArg (fun t : G => t * (x : G)) hyconj
    simpa [mul_assoc] using this.symm
  have hycent : (y : G) ∈ elementCentralizerIn K (x : G) := by
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hycomm⟩
  have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
    simpa [hcentx_bot] using hycent
  simpa using hybot

public theorem CFSG.IsFrobeniusGroupWithKernelComplement.regular_conj_action
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    letI : K.Normal := hfrob.normal
    letI : MulDistribMulAction (↥R) (↥K) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R K
        (Subgroup.le_normalizer_of_normal (H := K))
    ActsRegularly (↥R) (↥K) :=
  theorem_3_10_regular_conj_action (K := K) (R := R) hfrob

public theorem CFSG.ActsRegularly.subgroup {H R : Type*} [Group H] [Group R]
    [MulDistribMulAction R H] (hregular : ActsRegularly R H) (S : Subgroup R) :
    letI : MulDistribMulAction S H := MulDistribMulAction.compHom H S.subtype
    ActsRegularly S H := by
  let : MulDistribMulAction S H := MulDistribMulAction.compHom H S.subtype
  intro a ha
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hax : (a • x : H) = x := hx ⟨a, Subgroup.mem_zpowers a⟩
  have haR : (a : R) ≠ 1 := by
    intro hEq
    exact ha (Subtype.ext hEq)
  have haxR : ((a : R) • x : H) = x := by
    change ((a : R) • x : H) = x at hax
    exact hax
  have hxR : x ∈ fixedPointSubgroup (↥(Subgroup.zpowers (a : R))) H := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro y
    exact smul_eq_self_of_mem_zpowers y.2 haxR
  have hfixR_bot : fixedPointSubgroup (↥(Subgroup.zpowers (a : R))) H = ⊥ :=
    hregular (a : R) haR
  simpa [hfixR_bot] using hxR

public theorem CFSG.ActsRegularly.invariantSubgroup {H R : Type*} [Group H] [Group R]
    [MulDistribMulAction R H] (hregular : ActsRegularly R H) (E : Subgroup H)
    [IsInvariant R H E] :
    ActsRegularly R E := by
  intro a ha
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxH : (x : H) ∈ fixedPointSubgroup (↥(Subgroup.zpowers a)) H := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro y
    have hxy : y • x = x := by
      simpa [fixedPointSubgroup, FixedPoints.mem_subgroup] using hx y
    exact congrArg Subtype.val hxy
  have hfixH : fixedPointSubgroup (↥(Subgroup.zpowers a)) H = ⊥ :=
    hregular a ha
  have hxHbot : (x : H) ∈ (⊥ : Subgroup H) := by
    simpa [hfixH] using hxH
  exact Subtype.ext (Subgroup.mem_bot.mp hxHbot)

public theorem CFSG.isCyclic_of_odd_regular_pSubgroup {p : ℕ} {H R : Type*}
    [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hp : Nat.Prime p) (hoddR : Odd (Nat.card R))
    (hregular : ActsRegularly R H) {P : Subgroup R} (hP_p : IsPGroup p P) :
    IsCyclic P := by
  classical
  by_cases hPbot : P = ⊥
  · rw [hPbot]
    infer_instance
  · let : Fact p.Prime := ⟨hp⟩
    let : MulDistribMulAction P H := MulDistribMulAction.compHom H P.subtype
    have hp_dvd_R : p ∣ Nat.card R := by
      obtain ⟨n, hP_card⟩ := hP_p.exists_card_eq
      have hP_card_ne_one : Nat.card P ≠ 1 := by
        intro hcard
        exact hPbot ((Subgroup.eq_bot_iff_card (H := P)).2 hcard)
      have hn_ne_zero : n ≠ 0 := by
        intro hn
        apply hP_card_ne_one
        simp [hP_card, hn]
      have hp_dvd_P : p ∣ Nat.card P := by
        rw [hP_card]
        exact dvd_pow_self p hn_ne_zero
      exact hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card P)
    have hp_odd : Odd p := odd_of_card_dvd hoddR hp_dvd_R
    have hregularP : ActsRegularly P H := by
      intro a ha
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      let a1 : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
      have hax : (a • x : H) = x := hx a1
      have haR : (a : R) ≠ 1 := by
        intro hEq
        exact ha (Subtype.ext hEq)
      have haxR : ((a : R) • x : H) = x := by
        change ((a : R) • x : H) = x at hax
        exact hax
      have hxR : x ∈ fixedPointSubgroup (↥(Subgroup.zpowers (a : R))) H := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro y
        exact smul_eq_self_of_mem_zpowers y.2 haxR
      have hfixR_bot : fixedPointSubgroup (↥(Subgroup.zpowers (a : R))) H = ⊥ :=
        hregular (a : R) haR
      simpa [hfixR_bot] using hxR
    have hfixP_bot : fixedPointSubgroup P H = ⊥ := by
      let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPbot
      obtain ⟨x, hx_ne⟩ := exists_ne (1 : P)
      have hx_fix_bot : fixedPointSubgroup (↥(Subgroup.zpowers x)) H = ⊥ :=
        hregularP x hx_ne
      apply le_antisymm
      · intro y hy
        have hyz : y ∈ fixedPointSubgroup (↥(Subgroup.zpowers x)) H := by
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy ⊢
          intro z
          exact hy z.1
        simpa [hx_fix_bot] using hyz
      · exact bot_le
    have hcop_p_H : Nat.Coprime p (Nat.card H) := by
      refine (hp.coprime_iff_not_dvd).2 ?_
      intro hpdvdH
      have hone_fix : (1 : H) ∈ MulAction.fixedPoints P H := by
        simp [MulAction.mem_fixedPoints]
      obtain ⟨y, hy_fix, hy_ne_one⟩ :=
        hP_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point
          (α := H) hpdvdH hone_fix
      have hy_mem : y ∈ fixedPointSubgroup P H := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        exact MulAction.mem_fixedPoints.mp hy_fix
      have hy_bot : y ∈ (⊥ : Subgroup H) := by
        simpa [hfixP_bot] using hy_mem
      exact hy_ne_one (Subgroup.mem_bot.mp hy_bot).symm
    exact proposition_3_9 (H := H) (R := P) (p := p)
      hp hp_odd hcop_p_H hP_p hregularP

public theorem CFSG.natCard_omega₁_cyclic_pGroup_eq_prime
    {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] [Fact (IsPGroup p H)] (hcyc : IsCyclic H) [Nontrivial H] :
    Nat.card (omega₁ (G := H) (p := p)) = p := by
  classical
  let : IsCyclic H := hcyc
  let : CommGroup H := hcyc.commGroup
  have hOmega_eq_ker : omega₁ (G := H) (p := p) =
      (powMonoidHom p : H →* H).ker := by
    apply le_antisymm
    · rw [omega₁, omega]
      refine (Subgroup.closure_le (K := (powMonoidHom p : H →* H).ker)).2 ?_
      intro x hx
      change x ^ (p ^ 1) = 1 at hx
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
    · intro x hx
      change x ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
  obtain ⟨n, hn_pos, hcardH⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := H) (hG := Fact.out)).mp
      inferInstance
  calc
    Nat.card (omega₁ (G := H) (p := p))
        = Nat.card ((powMonoidHom p : H →* H).ker) := by rw [hOmega_eq_ker]
    _ = (Nat.card H).gcd p := IsCyclic.card_powMonoidHom_ker (G := H) p
    _ = p := by
      rw [hcardH]
      exact Nat.gcd_eq_right_iff_dvd.mpr
        (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn_pos))

public theorem CFSG.omega₁_map_subtype_normal_of_normal
    {R : Type*} [Group R] {p : ℕ} {A : Subgroup R} [A.Normal] :
    ((omega₁ (G := A) (p := p)).map A.subtype).Normal := by
  let Ωsub : Subgroup A := omega₁ (G := A) (p := p)
  have : Ωsub.Characteristic := by
    simpa [Ωsub] using (omega₁_characteristic (G := A) (p := p))
  simpa [Ωsub] using (inferInstance : (Ωsub.map A.subtype).Normal)


public theorem CFSG.minimalInvariantNormal_solvable_exists_isElementaryAbelian
    {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]
    (M : Subgroup G) [M.Normal] [IsInvariant A G M] [Group.IsSolvable (↥M)]
    (hM_ne_bot : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → IsInvariant A G K → K ≠ ⊥ → K ≤ M → K = M) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p (↥M) := by
  classical
  have : Nontrivial (↥M) := (Subgroup.nontrivial_iff_ne_bot M).2 hM_ne_bot
  have hcomm_lt : ⁅M, M⁆ < M := by
    have hlt : commutator (↥M) < (⊤ : Subgroup (↥M)) :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial (G := (↥M))
    have hlt' : (commutator (↥M)).map M.subtype <
        (⊤ : Subgroup (↥M)).map M.subtype :=
      (Subgroup.map_subtype_lt_map_subtype (G' := M) (H := commutator (↥M))
        (K := (⊤ : Subgroup (↥M)))).mpr hlt
    have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
      simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
    simpa [Subgroup.map_subtype_commutator, htop_map] using hlt'
  have hcomm_inv : IsInvariant A G ⁅M, M⁆ :=
    isInvariant_commutator (A := A) (G := G) M M
  have hcomm_eq_bot : ⁅M, M⁆ = ⊥ := by
    by_contra hne
    have hcomm_eq : ⁅M, M⁆ = M :=
      hmin ⁅M, M⁆ (inferInstance : (⁅M, M⁆).Normal) hcomm_inv hne
        (Subgroup.commutator_le_left (H₁ := M) (H₂ := M))
    exact (ne_of_lt hcomm_lt) hcomm_eq
  have hM_le_centralizer : M ≤ Subgroup.centralizer (M : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := M) (H₂ := M)).mp
      hcomm_eq_bot
  have : IsMulCommutative (↥M) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := M)).mp hM_le_centralizer
  have hcard_ne_one : Nat.card (↥M) ≠ 1 := by
    have : 1 < Nat.card (↥M) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := M)).2 hM_ne_bot
    exact ne_of_gt this
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (↥M)) hcard_ne_one
  have : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p (↥M) := default
  have hP_ne_bot : (P : Subgroup (↥M)) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := (↥M)) (p := p) P hp_dvd
  have hP_normal : (P : Subgroup (↥M)).Normal := by infer_instance
  have : (P : Subgroup (↥M)).Characteristic :=
    Sylow.characteristic_of_normal (G := (↥M)) (p := p) P hP_normal
  have : ((P : Subgroup (↥M)).map M.subtype).Normal := by infer_instance
  have : IsInvariant A (↥M) (P : Subgroup (↥M)) :=
    isInvariant_of_characteristic (A := A) (G := ↥M) (P : Subgroup (↥M))
  have hPmap_inv : IsInvariant A G ((P : Subgroup (↥M)).map M.subtype) :=
    isInvariant_map_subtype (A := A) (G := G) M (P : Subgroup (↥M))
  have hPmap_ne_bot : (P : Subgroup (↥M)).map M.subtype ≠ ⊥ := by
    intro hbot
    have : (P : Subgroup (↥M)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup (↥M))) (f := M.subtype)
        M.subtype_injective).1 hbot
    exact hP_ne_bot this
  have hPmap_eq_M : (P : Subgroup (↥M)).map M.subtype = M :=
    hmin ((P : Subgroup (↥M)).map M.subtype)
      (inferInstance : ((P : Subgroup (↥M)).map M.subtype).Normal)
      hPmap_inv hPmap_ne_bot (Subgroup.map_subtype_le (H := M) (K := (P : Subgroup (↥M))))
  have hMpgroup : IsPGroup p (↥M) := by
    have h : IsPGroup p (↥((P : Subgroup (↥M)).map M.subtype)) :=
      P.isPGroup'.map M.subtype
    simpa using (hPmap_eq_M ▸ h)
  have : Fact (IsPGroup p (↥M)) := ⟨hMpgroup⟩
  let Ω : Subgroup (↥M) := omega₁ (G := (↥M)) (p := p)
  have hΩ_char : Ω.Characteristic := by
    simpa [Ω] using (omega₁_characteristic (G := (↥M)) (p := p))
  have : Ω.Characteristic := hΩ_char
  have : (Ω.map M.subtype).Normal := by infer_instance
  have : IsInvariant A (↥M) Ω :=
    isInvariant_of_characteristic (A := A) (G := ↥M) Ω
  have hΩmap_inv : IsInvariant A G (Ω.map M.subtype) :=
    isInvariant_map_subtype (A := A) (G := G) M Ω
  have hΩmap_ne_bot : Ω.map M.subtype ≠ ⊥ := by
    simpa [Ω] using omega₁_map_subtype_ne_bot (M := M) (p := p) hp_dvd
  have hΩmap_eq_M : Ω.map M.subtype = M :=
    hmin (Ω.map M.subtype) (inferInstance : (Ω.map M.subtype).Normal)
      hΩmap_inv hΩmap_ne_bot (Subgroup.map_subtype_le (H := M) (K := Ω))
  have hΩ_top : Ω = ⊤ := by
    have hinj : Function.Injective (Subgroup.map M.subtype) :=
      Subgroup.map_injective (f := M.subtype) M.subtype_injective
    have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
      simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
    apply hinj
    simpa [htop_map] using hΩmap_eq_M
  have hpow : ∀ x : ↥M, x ^ p = 1 := by
    intro x
    have hxΩ : x ∈ Ω := by simp [hΩ_top]
    have hx' : x ∈ Subgroup.closure {y : ↥M | y ^ (p ^ 1) = 1} := by
      simpa [Ω, omega₁, omega] using hxΩ
    refine
      Subgroup.closure_induction (k := {y : ↥M | y ^ (p ^ 1) = 1})
        (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simpa [pow_one] using hy
    · simp
    · intro a b _ha _hb ha hb
      calc
        (a * b) ^ p = a ^ p * b ^ p := by simpa using mul_pow a b p
        _ = 1 := by simp [ha, hb]
    · intro a _ha ha
      simp [ha]
  have hExp : Monoid.exponent (↥M) ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow
  exact ⟨p, hp_prime, ⟨hExp⟩⟩


public theorem CFSG.exists_regular_elementaryAbelian_invariant_subgroup_of_invariant_solvable_subgroup
    {H R : Type*} [Group H] [Finite H] [Group R] [MulDistribMulAction R H]
    (hregular : ActsRegularly R H) {S : Subgroup H} [IsInvariant R H S]
    (hS_ne_bot : S ≠ ⊥) (hSsolv : Group.IsSolvable (↥S)) :
    ∃ (E : Subgroup H) (r : ℕ) (hE_inv : IsInvariant R H E),
      r.Prime ∧ E ≠ ⊥ ∧ IsElementaryAbelian r (↥E) ∧
        letI : IsInvariant R H E := hE_inv
        ActsRegularly R E := by
  classical
  have : Nontrivial (↥S) := (Subgroup.nontrivial_iff_ne_bot S).2 hS_ne_bot
  obtain ⟨M, hMnorm, hMinv, hM_ne_bot, hMmin⟩ :=
    exists_minimal_normal_isInvariant (G := S) (A := R)
  have : M.Normal := hMnorm
  have : IsInvariant R S M := hMinv
  have : Group.IsSolvable (↥S) := hSsolv
  have : Group.IsSolvable (↥M) := by infer_instance
  obtain ⟨r, hr, hMelem⟩ :=
    minimalInvariantNormal_solvable_exists_isElementaryAbelian
      (G := S) (A := R) M hM_ne_bot
      (fun K hKnorm hKinv hKne hKle => hMmin K hKnorm hKinv hKne hKle)
  let E : Subgroup H := M.map S.subtype
  have hE_inv : IsInvariant R H E := by
    simpa [E] using isInvariant_map_subtype (A := R) (G := H) S M
  have hE_ne_bot : E ≠ ⊥ := by
    intro hbot
    have hM_bot : M = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := M) (f := S.subtype) S.subtype_injective).1
        hbot
    exact hM_ne_bot hM_bot
  have : Fact r.Prime := ⟨hr⟩
  have : IsElementaryAbelian r (↥M) := hMelem
  have hEelem : IsElementaryAbelian r (↥E) := by
    simpa [E] using (IsElementaryAbelian.map_subtype (p := r) (K := S) (H := M))
  refine ⟨E, r, hE_inv, hr, hE_ne_bot, hEelem, ?_⟩
  let : IsInvariant R H E := hE_inv
  exact ActsRegularly.invariantSubgroup hregular E


/-- Prime-power operator nonabelian `H¹` base: a `1`-cocycle for a coprime finite
`r`-group action is principal.  The proof uses the standard twisted action on the
underlying finite set and the fixed-point theorem for `p`-groups. -/
private theorem CFSG.exists_principal_cocycle_of_pgroup_operator_coprime_bg3
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] {r : ℕ} [Fact r.Prime] [Fact (IsPGroup r A)]
    (hcoprime : Nat.Coprime r (Nat.card G))
    (c : A → G) (hc : ∀ a b : A, c (a * b) = c a * (a • c b)) :
    ∃ x : G, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let smul0 : A → G → G := fun a x => a • x
  have hc_one : c 1 = 1 := by
    have h' : c 1 = c 1 * c 1 := by simpa using hc 1 1
    calc
      c 1 = (c 1)⁻¹ * (c 1 * c 1) := by simp
      _ = (c 1)⁻¹ * c 1 := by rw [← h']
      _ = 1 := by simp
  let : MulAction A G :=
    { smul := fun a x => c a * smul0 a x
      one_smul := by
        intro x
        change c 1 * smul0 1 x = x
        dsimp [smul0]
        simp [hc_one]
      mul_smul := by
        intro a b x
        change c (a * b) * smul0 (a * b) x = c a * smul0 a (c b * smul0 b x)
        dsimp [smul0]
        rw [hc a b]
        simp [smul_mul', smul_smul, mul_assoc] }
  have hr_not_dvd : ¬ r ∣ Nat.card G :=
    ((Fact.out : Nat.Prime r).coprime_iff_not_dvd).1 hcoprime
  rcases (Fact.out : IsPGroup r A).nonempty_fixed_point_of_prime_not_dvd_card
      G hr_not_dvd with
    ⟨x, hxfix⟩
  refine ⟨x, ?_⟩
  intro a
  have hx : c a * smul0 a x = x := by
    have := (MulAction.mem_fixedPoints.mp hxfix) a
    change c a * smul0 a x = x at this
    exact this
  show c a = x * (smul0 a x)⁻¹
  calc
    c a = (c a * smul0 a x) * (smul0 a x)⁻¹ := by simp
    _ = x * (smul0 a x)⁻¹ := by rw [hx]

universe u_h1 v_h1

/-- Nonabelian `H¹` vanishing in the form needed for the solvable operator
Schur-Zassenhaus step: a `1`-cocycle for a finite solvable coprime operator
group is principal. -/
private theorem CFSG.exists_principal_cocycle_of_solvable_operator_coprime_bg3
    {G : Type u_h1} {A : Type v_h1}
    [Group G] [Finite G] [Group A] [Finite A] [Group.IsSolvable A]
    [MulDistribMulAction A G] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (c : A → G) (hc : ∀ a b : A, c (a * b) = c a * (a • c b)) :
    ∃ x : G, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (A' : Type v_h1) (G' : Type u_h1) [Group A'] [Finite A'] [Group.IsSolvable A']
      [Group G'] [Finite G'] [MulDistribMulAction A' G'],
      Nat.card A' = n →
      Nat.Coprime (Nat.card A') (Nat.card G') →
      ∀ c' : A' → G', (∀ a b : A', c' (a * b) = c' a * (a • c' b)) →
        ∃ x : G', ∀ a : A', c' a = x * (a • x)⁻¹
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A' G' _ _ _ _ _ _ hcardA hcop c' hc'
    by_cases hA_one : Nat.card A' = 1
    · let : Subsingleton A' := (Nat.card_eq_one_iff_unique.mp hA_one).1
      have hc_one : c' 1 = 1 := by
        have h' : c' 1 = c' 1 * c' 1 := by simpa using hc' 1 1
        calc
          c' 1 = (c' 1)⁻¹ * (c' 1 * c' 1) := by simp
          _ = (c' 1)⁻¹ * c' 1 := by rw [← h']
          _ = 1 := by simp
      refine ⟨1, ?_⟩
      intro a
      have ha : a = 1 := Subsingleton.elim a 1
      simp [ha, hc_one]
    · have hA_nontrivial : Nontrivial A' := by
        exact (not_subsingleton_iff_nontrivial.mp fun hsub => by
          have hcard_one : Nat.card A' = 1 := by
            exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
          exact hA_one hcard_one)
      let : Nontrivial A' := hA_nontrivial
      obtain ⟨B, hBnorm, hBne, hBmin⟩ :=
        exists_minimal_normal (G := A') (inferInstance : Group.IsSolvable A') hA_nontrivial
      let : B.Normal := hBnorm
      let : IsMinimalNormal B := by
        refine ⟨?_⟩
        intro K hKnorm hKle
        by_cases hKbot : K = ⊥
        · exact Or.inl hKbot
        · exact Or.inr (hBmin K hKnorm hKle hKbot)
      have hBsolv : Group.IsSolvable B := by infer_instance
      let : Group.IsSolvable B := hBsolv
      obtain ⟨r, hrprime, hBel⟩ :=
        minimalNormal_solvable_exists_isElementaryAbelian (G := A') B
      let : Fact r.Prime := ⟨hrprime⟩
      let : IsElementaryAbelian r B := hBel
      let : Fact (IsPGroup r B) :=
        ⟨IsElementaryAbelian.isPGroup r B⟩
      have hr_dvd_A : r ∣ Nat.card A' := by
        have hBp : IsPGroup r B := IsElementaryAbelian.isPGroup r B
        rcases hBp.exists_card_eq with ⟨k, hk⟩
        have hBcard_ne_one : Nat.card B ≠ 1 := by
          intro hcard
          exact hBne ((Subgroup.eq_bot_iff_card (H := B)).2 hcard)
        have hk_ne_zero : k ≠ 0 := by
          intro hk0
          apply hBcard_ne_one
          simp [hk, hk0]
        have hr_dvd_B : r ∣ Nat.card B := by
          rw [hk]
          exact dvd_pow_self r hk_ne_zero
        exact hr_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)
      have hcop_r_G : Nat.Coprime r (Nat.card G') :=
        Nat.Coprime.of_dvd_left hr_dvd_A hcop
      let cB : B → G' := fun b => c' b
      have hcB : ∀ a b : B, cB (a * b) = cB a * (a • cB b) := by
        intro a b
        change c' ((a : A') * (b : A')) = c' a * ((a : A') • c' b)
        exact hc' (a : A') (b : A')
      obtain ⟨x0, hx0⟩ :=
        exists_principal_cocycle_of_pgroup_operator_coprime_bg3
          (G := G') (A := B) hcop_r_G cB hcB
      let c1 : A' → G' := fun a => x0⁻¹ * c' a * (a • x0)
      have hc1_def : ∀ a : A', c1 a = x0⁻¹ * c' a * (a • x0) := fun _ => rfl
      have hc1 : ∀ a b : A', c1 (a * b) = c1 a * (a • c1 b) := by
        intro a b
        dsimp [c1]
        rw [hc' a b]
        simp [smul_mul', smul_smul, mul_assoc]
      have hc1B : ∀ b : B, c1 b = 1 := by
        intro b
        dsimp [c1]
        change x0⁻¹ * cB b * (b • x0) = 1
        rw [hx0 b]
        simp
      have hc1_fixed : ∀ a : A', c1 a ∈ fixedPointSubgroup B G' := by
        intro a
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro b
        have hconj_mem : a⁻¹ * (b : A') * a ∈ B :=
          by simpa using (inferInstance : B.Normal).conj_mem (b : A') b.property a⁻¹
        let b' : B := ⟨a⁻¹ * (b : A') * a, hconj_mem⟩
        have hba : (b : A') * a = a * (b' : A') := by
          simp [b', mul_assoc]
        have h1 : c1 ((b : A') * a) = (b : A') • c1 a := by
          simpa [hc1B b] using hc1 (b : A') a
        have h2 : c1 (a * (b' : A')) = c1 a := by
          simpa [hc1B b'] using hc1 a (b' : A')
        have : (b : A') • c1 a = c1 a := by
          calc
            (b : A') • c1 a = c1 ((b : A') * a) := h1.symm
            _ = c1 (a * (b' : A')) := by rw [hba]
            _ = c1 a := h2
        change (b : A') • c1 a = c1 a
        exact this
      let F : Subgroup G' := fixedPointSubgroup B G'
      have hcop_Q_F : Nat.Coprime (Nat.card (A' ⧸ B)) (Nat.card F) := by
        have hquot_dvd : Nat.card (A' ⧸ B) ∣ Nat.card A' :=
          Subgroup.card_quotient_dvd_card (s := B)
        have hcop_Q_G : Nat.Coprime (Nat.card (A' ⧸ B)) (Nat.card G') :=
          Nat.Coprime.of_dvd_left hquot_dvd hcop
        exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card F) hcop_Q_G
      have hquot_lt : Nat.card (A' ⧸ B) < n := by
        simpa [hcardA] using card_quotient_lt_of_ne_bot (G := A') B hBne
      have hsolv_quot : Group.IsSolvable (A' ⧸ B) := by infer_instance
      let : Group.IsSolvable (A' ⧸ B) := hsolv_quot
      let : MulDistribMulAction (A' ⧸ B) F := by
        dsimp [F]
        infer_instance
      have hc1_eq_of_mk_eq {a b : A'} (h : (a : A' ⧸ B) = b) : c1 a = c1 b := by
        rcases (QuotientGroup.mk'_eq_mk' (N := B)).mp h with ⟨z, hzB, haz⟩
        have hz : c1 z = 1 := hc1B ⟨z, hzB⟩
        calc
          c1 a = c1 (a * z) := by simpa [hz] using (hc1 a z).symm
          _ = c1 b := by rw [haz]
      let cQ : A' ⧸ B → F := fun q => ⟨c1 q.out, hc1_fixed q.out⟩
      have hcQ_mk : ∀ a : A', cQ (a : A' ⧸ B) = ⟨c1 a, hc1_fixed a⟩ := by
        intro a
        ext
        dsimp [cQ]
        exact hc1_eq_of_mk_eq
          (by exact Quotient.out_eq (s := QuotientGroup.leftRel B) (a : A' ⧸ B))
      have hcQ : ∀ q s : A' ⧸ B, cQ (q * s) = cQ q * (q • cQ s) := by
        intro q s
        refine Quotient.inductionOn₂' q s ?_
        intro a b
        ext
        rw [← QuotientGroup.mk_mul (N := B) a b]
        simp only [hcQ_mk, Subgroup.coe_mul]
        have hsmul :
            ↑(((a : A' ⧸ B) • (⟨c1 b, hc1_fixed b⟩ : F)) : F) = a • c1 b := by
          rfl
        rw [hsmul]
        exact hc1 a b
      obtain ⟨y, hy⟩ :=
        ih (Nat.card (A' ⧸ B)) hquot_lt (A' ⧸ B) F rfl hcop_Q_F cQ hcQ
      refine ⟨x0 * (y : G'), ?_⟩
      intro a
      have hy_a : c1 a = (y : G') * (a • (y : G'))⁻¹ := by
        have h := congrArg Subtype.val (hy (a : A' ⧸ B))
        rw [hcQ_mk] at h
        change c1 a = (y : G') * (a • (y : G'))⁻¹ at h
        exact h
      have hc_rearr : c' a = x0 * c1 a * (a • x0)⁻¹ := by
        have hdef := hc1_def a
        calc
          c' a = x0 * (x0⁻¹ * c' a * (a • x0)) * (a • x0)⁻¹ := by
                  simp [mul_assoc]
          _ = x0 * c1 a * (a • x0)⁻¹ := by rw [← hdef]
      rw [hc_rearr, hy_a]
      simp [smul_mul', mul_assoc]
  exact hP (Nat.card A) A G rfl hcoprime c hc

/-- In the action semidirect product `G ⋊ A`, the two standard copies of `G` and `A`
are complementary subgroups. -/
private theorem CFSG.semidirect_range_inl_isComplement_range_inr
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G] :
    let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
    let inl : G →* G ⋊[φ] A := SemidirectProduct.inl (φ := φ)
    let inr : A →* G ⋊[φ] A := SemidirectProduct.inr (φ := φ)
    ((⊤ : Subgroup G).map inl).IsComplement' ((⊤ : Subgroup A).map inr) := by
  classical
  intro φ inl inr
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases hx with ⟨hxG, hxA⟩
    rcases Subgroup.mem_map.mp hxG with ⟨g, _hg, hgx⟩
    rcases Subgroup.mem_map.mp hxA with ⟨a, _ha, hax⟩
    have hright : a = 1 := by
      have := congrArg (SemidirectProduct.right : G ⋊[φ] A → A) (hax.trans hgx.symm)
      simpa [inl, inr, φ] using this
    have hx_one : x = 1 := by
      rw [← hax, hright]
      simp [inr]
    simp [hx_one]
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨inl x.left, ?_, inr x.right, ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem inl (by simp)
      · exact Subgroup.mem_map_of_mem inr (by simp)
      · exact SemidirectProduct.inl_left_mul_inr_right x


/-- If the standard copy of `A` normalizes the embedded Sylow subgroup in `G ⋊ A`, then the
original Sylow subgroup of `G` is `A`-invariant. -/
private theorem CFSG.isInvariant_of_inr_le_normalizer_map_inl_sylow
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
    let inl : G →* G ⋊[φ] A := SemidirectProduct.inl (φ := φ)
    let inr : A →* G ⋊[φ] A := SemidirectProduct.inr (φ := φ)
    let Pembed : Subgroup (G ⋊[φ] A) := (P : Subgroup G).map inl
    ((⊤ : Subgroup A).map inr) ≤ Subgroup.normalizer Pembed →
      IsInvariant A G (P : Subgroup G) := by
  classical
  intro φ inl inr Pembed hle
  have hinl_inj : Function.Injective inl := by
    simpa [inl, φ] using
      (SemidirectProduct.inl_injective (N := G) (G := A) (φ := φ) :
        Function.Injective (SemidirectProduct.inl (φ := φ) : G → G ⋊[φ] A))
  constructor
  intro a g
  constructor
  · intro hg
    have hnorm : (inr a : G ⋊[φ] A) ∈ Subgroup.normalizer Pembed := by
      exact hle (Subgroup.mem_map_of_mem inr (by simp))
    have hg_embed : (inl g : G ⋊[φ] A) ∈ Pembed :=
      Subgroup.mem_map_of_mem inl hg
    have hconj_mem : (inr a : G ⋊[φ] A) * inl g * (inr a)⁻¹ ∈ Pembed :=
      ((Subgroup.mem_normalizer_iff.mp hnorm) (inl g)).1 hg_embed
    have hconj_eq : (inr a : G ⋊[φ] A) * inl g * (inr a)⁻¹ = inl (a • g) := by
      simpa [inl, inr, φ] using (SemidirectProduct.inl_aut (φ := φ) a g).symm
    have ha_embed : inl (a • g) ∈ Pembed := by
      simpa [hconj_eq] using hconj_mem
    rcases Subgroup.mem_map.mp ha_embed with ⟨y, hy, hy_eq⟩
    have hy_eq' : y = a • g := hinl_inj hy_eq
    simpa [← hy_eq'] using hy
  · intro hg
    have hnorm : (inr a⁻¹ : G ⋊[φ] A) ∈ Subgroup.normalizer Pembed := by
      exact hle (Subgroup.mem_map_of_mem inr (by simp))
    have hg_embed : (inl (a • g) : G ⋊[φ] A) ∈ Pembed :=
      Subgroup.mem_map_of_mem inl hg
    have hconj_mem : (inr a⁻¹ : G ⋊[φ] A) * inl (a • g) * (inr a⁻¹)⁻¹ ∈ Pembed :=
      ((Subgroup.mem_normalizer_iff.mp hnorm) (inl (a • g))).1 hg_embed
    have hconj_eq : (inr a : G ⋊[φ] A)⁻¹ * inl (a • g) * inr a = inl g := by
      calc
        (inr a : G ⋊[φ] A)⁻¹ * inl (a • g) * inr a
            = (inr a⁻¹ : G ⋊[φ] A) * inl (a • g) * (inr a⁻¹)⁻¹ := by simp
        _ = inl (a⁻¹ • (a • g)) := by
                simpa [inl, inr, φ] using
                  (SemidirectProduct.inl_aut (φ := φ) a⁻¹ (a • g)).symm
        _ = inl g := by simp [smul_smul]
    have hg_embed' : inl g ∈ Pembed := by
      simpa [hconj_eq] using hconj_mem
    rcases Subgroup.mem_map.mp hg_embed' with ⟨y, hy, hy_eq⟩
    have hy_eq' : y = g := hinl_inj hy_eq
    simpa [← hy_eq'] using hy


private theorem CFSG.exists_conj_eq_of_isComplement'_solvable_complement_bg3
    {E : Type*} [Group E] [Finite E] {N C D : Subgroup E} [N.Normal]
    (hNC : N.IsComplement' C) (hND : N.IsComplement' D)
    (hcopNC : Nat.Coprime (Nat.card N) (Nat.card C))
    [Group.IsSolvable C] :
    ∃ n : N, D = C.map (MulAut.conj (n : E)).toMonoidHom := by
  classical
  have hC_norm_N : C ≤ Subgroup.normalizer (N : Set E) :=
    Subgroup.le_normalizer_of_normal (H := N)
  let : MulDistribMulAction C N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := E) C N hC_norm_N
  let q : E →* E ⧸ N := QuotientGroup.mk' N
  let eD : E ⧸ N ≃* D := hND.symm.QuotientMulEquiv
  let sectD : C → D := fun c => eD (q (c : E))
  have hsectD_q : ∀ c : C, q (sectD c : E) = q (c : E) := by
    intro c
    dsimp [sectD, eD, q]
    exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hND.symm
      (QuotientGroup.mk' N (c : E))
  let z : C → N := fun c =>
    ⟨(sectD c : E) * (c : E)⁻¹, by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q ((sectD c : E) * (c : E)⁻¹) = 1
      rw [map_mul, map_inv, hsectD_q c]
      simp⟩
  have hsectD_mul : ∀ a b : C, sectD (a * b) = sectD a * sectD b := by
    intro a b
    dsimp [sectD]
    exact eD.map_mul (q (a : E)) (q (b : E))
  have hsectD_eq : ∀ c : C, (sectD c : E) = (z c : E) * (c : E) := by
    intro c
    dsimp [z]
    simp [mul_assoc]
  have hz_cocycle : ∀ a b : C, z (a * b) = z a * (a • z b) := by
    intro a b
    ext
    have hsE : (sectD (a * b) : E) = (sectD a : E) * (sectD b : E) :=
      congrArg Subtype.val (hsectD_mul a b)
    dsimp [z]
    rw [hsE]
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  obtain ⟨x, hx⟩ :=
    exists_principal_cocycle_of_solvable_operator_coprime_bg3
      (G := N) (A := C) hcopNC.symm z hz_cocycle
  have hCx_le_D : C.map (MulAut.conj (x : E)).toMonoidHom ≤ D := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨c, hcC, rfl⟩
    let cC : C := ⟨c, hcC⟩
    have hzE :
        (z cC : E) = (x : E) * (((cC : C) • x : N) : E)⁻¹ := by
      simpa using congrArg Subtype.val (hx cC)
    have hsect_eq : (sectD cC : E) = (x : E) * c * (x : E)⁻¹ := by
      calc
        (sectD cC : E) = (z cC : E) * (cC : E) := hsectD_eq cC
        _ = ((x : E) * (((cC : C) • x : N) : E)⁻¹) * (cC : E) := by rw [hzE]
        _ = (x : E) * c * (x : E)⁻¹ := by
              simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, cC, mul_assoc]
    simpa [MulAut.conj_apply, cC, hsect_eq] using (sectD cC).property
  have hcardD : Nat.card D = Nat.card C :=
    hND.symm.index_eq_card.symm.trans hNC.symm.index_eq_card
  have hcardCx : Nat.card (C.map (MulAut.conj (x : E)).toMonoidHom) = Nat.card C := by
    exact Subgroup.card_map_of_injective
      (K := C) (f := (MulAut.conj (x : E)).toMonoidHom) (MulAut.conj (x : E)).injective
  have hcard_le : Nat.card D ≤ Nat.card (C.map (MulAut.conj (x : E)).toMonoidHom) := by
    rw [hcardD, hcardCx]
  exact ⟨x, (Subgroup.eq_of_le_of_card_ge hCx_le_D hcard_le).symm⟩


private theorem CFSG.exists_sylow_normalized_by_solvable_complement_of_normal_hall_bg3
    {E : Type*} [Group E] [Finite E] {N C : Subgroup E} [N.Normal]
    (hNC : N.IsComplement' C) (hcopNC : Nat.Coprime (Nat.card N) (Nat.card C))
    [Group.IsSolvable C] {p : ℕ} [Fact p.Prime] :
    ∃ P : Sylow p N, C ≤ Subgroup.normalizer ((P : Subgroup N).map N.subtype : Subgroup E) := by
  classical
  let P₀ : Sylow p N := default
  let Pembed : Subgroup E := (P₀ : Subgroup N).map N.subtype
  let M : Subgroup E := Subgroup.normalizer Pembed
  let NM : Subgroup M := N.comap M.subtype
  have hfrat : M ⊔ N = ⊤ := by
    simpa [M, Pembed] using (Sylow.normalizer_sup_eq_top (G := E) (N := N) (P := P₀))
  have hq_surj : Function.Surjective ((QuotientGroup.mk' N).comp M.subtype) := by
    intro y
    rcases QuotientGroup.mk'_surjective N y with ⟨x, rfl⟩
    have hx_sup : x ∈ M ⊔ N := by simp [hfrat]
    have hx_mul : x ∈ (M : Set E) * (N : Set E) := by
      simpa [hfrat] using
        ((show (↑(M ⊔ N) : Set E) = (M : Set E) * (N : Set E) from
          Subgroup.mul_normal M N) ▸ hx_sup)
    rcases Set.mem_mul.mp hx_mul with ⟨m, hmM, n, hnN, hmn⟩
    refine ⟨⟨m, hmM⟩, ?_⟩
    rw [← hmn]
    simpa using hnN
  have hker : ((QuotientGroup.mk' N).comp M.subtype).ker = NM := by
    ext x
    change ((x : E) : E ⧸ N) = 1 ↔ (x : E) ∈ N
    exact QuotientGroup.eq_one_iff (N := N) (x := (x : E))
  have hquot_card_C : Nat.card (E ⧸ N) = Nat.card C := by
    have hidxC : N.index = Nat.card C := hNC.symm.index_eq_card
    have hidxQ : N.index = Nat.card (E ⧸ N) := by
      simp [Subgroup.index_eq_card]
    exact hidxQ.symm.trans hidxC
  have hNM_index_C : NM.index = Nat.card C := by
    calc
      NM.index = ((QuotientGroup.mk' N).comp M.subtype).ker.index := by rw [hker]
      _ = Nat.card (((QuotientGroup.mk' N).comp M.subtype).range) := by
            rw [Subgroup.index_ker]
      _ = Nat.card (⊤ : Subgroup (E ⧸ N)) := by
            rw [MonoidHom.range_eq_top_of_surjective _ hq_surj]
      _ = Nat.card (E ⧸ N) := by simp
      _ = Nat.card C := hquot_card_C
  have hNM_card_dvd_N : Nat.card NM ∣ Nat.card N := by
    let NMmap : Subgroup E := NM.map M.subtype
    have hNMmap_le_N : NMmap ≤ N := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact hy
    have hcard_map : Nat.card NMmap = Nat.card NM := by
      simpa [NMmap] using
        (Subgroup.card_map_of_injective (K := NM) (f := M.subtype) M.subtype_injective)
    rw [← hcard_map]
    exact Subgroup.card_dvd_of_le hNMmap_le_N
  have hNM_coprime_index : Nat.Coprime (Nat.card NM) NM.index := by
    exact Nat.Coprime.of_dvd_left hNM_card_dvd_N (by simpa [hNM_index_C] using hcopNC)
  have : NM.Normal := by
    dsimp [NM]
    infer_instance
  obtain ⟨Dloc, hNM_Dloc⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := NM) hNM_coprime_index
  let D : Subgroup E := Dloc.map M.subtype
  have hD_le_M : D ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hNMmap_le_N : NM.map M.subtype ≤ N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hy
  have hM_le_N_sup_D : M ≤ N ⊔ D := by
    intro x hx
    let xM : M := ⟨x, hx⟩
    have hxM_top : xM ∈ (⊤ : Subgroup M) := by simp
    have hxM_sup : xM ∈ NM ⊔ Dloc := by
      simp [hNM_Dloc.sup_eq_top]
    have hx_map : (xM : E) ∈ (NM ⊔ Dloc).map M.subtype :=
      Subgroup.mem_map_of_mem M.subtype hxM_sup
    have hmap_sup : (NM ⊔ Dloc).map M.subtype = NM.map M.subtype ⊔ D := by
      simp [D, Subgroup.map_sup]
    have hx_ND : x ∈ NM.map M.subtype ⊔ D := by
      simpa [xM, hmap_sup] using hx_map
    exact (sup_le_sup hNMmap_le_N le_rfl) hx_ND
  have hN_sup_D : N ⊔ D = ⊤ := by
    apply top_le_iff.mp
    rw [← hfrat]
    exact sup_le hM_le_N_sup_D le_sup_left
  have hN_disj_D : Disjoint N D := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨hxN, hxD⟩
    rcases Subgroup.mem_map.mp hxD with ⟨d, hdD, hd_eq⟩
    have hdNM : d ∈ NM := by
      change (d : E) ∈ N
      simpa [← hd_eq] using hxN
    have hd_bot : d ∈ (⊥ : Subgroup M) := by
      have hd_inf : d ∈ NM ⊓ Dloc := ⟨hdNM, hdD⟩
      simpa [hNM_Dloc.disjoint.eq_bot] using hd_inf
    have hx_one : x = 1 := by
      have hd_one : d = 1 := by simpa using hd_bot
      rw [← hd_eq, hd_one]
      rfl
    simp [hx_one]
  have hND : N.IsComplement' D := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hN_disj_D ?_
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ N ⊔ D := by simp [hN_sup_D]
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := N) (t := D)).1 hx with
      ⟨n, hnN, d, hdD, hmul⟩
    exact Set.mem_mul.mpr ⟨n, hnN, d, hdD, hmul⟩
  obtain ⟨n, hnD⟩ :=
    exists_conj_eq_of_isComplement'_solvable_complement_bg3
      (N := N) (C := C) (D := D) hNC hND hcopNC
  let P : Sylow p N := (n⁻¹ : N) • P₀
  refine ⟨P, ?_⟩
  let Pmap : Subgroup E := ((P : Subgroup N).map N.subtype : Subgroup E)
  have hPmap_eq : Pmap = Pembed.map (MulAut.conj ((n : E)⁻¹)).toMonoidHom := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyP, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨((MulAut.conj (n : N)) y), ?_, ?_⟩
      · have hyP' : y ∈ ((MulAut.conj (n : N))⁻¹ • (P₀ : Subgroup N)) := by
          simpa [P, Sylow.pointwise_smul_def, Sylow.smul_def] using hyP
        have hyP0 : (MulAut.conj (n : N)) y ∈ (P₀ : Subgroup N) :=
          Subgroup.mem_inv_pointwise_smul_iff.mp hyP'
        exact Subgroup.mem_map_of_mem N.subtype hyP0
      · simp [MulAut.conj_apply, mul_assoc]
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyPembed, hxy⟩
      rcases Subgroup.mem_map.mp hyPembed with ⟨z, hzP₀, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨((MulAut.conj (n : N))⁻¹) z, ?_, ?_⟩
      · have hzP : ((MulAut.conj (n : N))⁻¹) z ∈ ((P : Subgroup N)) := by
          have hzP' : ((MulAut.conj (n : N))⁻¹) z ∈
              ((MulAut.conj (n : N))⁻¹ • (P₀ : Subgroup N)) :=
            Subgroup.smul_mem_pointwise_smul z ((MulAut.conj (n : N))⁻¹)
              (P₀ : Subgroup N) hzP₀
          simpa [P, Sylow.pointwise_smul_def, Sylow.smul_def]
            using hzP'
        exact hzP
      · simpa [MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc] using hxy
  have hconj_mem :
      ∀ {c x : E}, c ∈ C → x ∈ Pmap → c * x * c⁻¹ ∈ Pmap := by
    intro c x hc hx
    have hd : (n : E) * c * (n : E)⁻¹ ∈ D := by
      rw [hnD]
      exact Subgroup.mem_map.mpr ⟨c, hc, by simp [MulAut.conj_apply]⟩
    have hdnorm : (n : E) * c * (n : E)⁻¹ ∈ M := hD_le_M hd
    rw [hPmap_eq] at hx ⊢
    rcases Subgroup.mem_map.mp hx with ⟨y, hyP, hxy⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨((n : E) * c * (n : E)⁻¹) * y * ((n : E) * c * (n : E)⁻¹)⁻¹,
      ?_, ?_⟩
    · exact ((Subgroup.mem_normalizer_iff.mp hdnorm) y).1 hyP
    · rw [← hxy]
      simp [mul_assoc]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hconj_mem hc hx
  · intro hx
    have hx' : c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ ∈ Pmap :=
      hconj_mem (C.inv_mem hc) hx
    simpa [Pmap, mul_assoc] using hx'


private theorem CFSG.exists_sylow_normalized_by_semidirect_right_of_solvable_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [Group.IsSolvable A]
    [MulDistribMulAction A G] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    {p : ℕ} [Fact p.Prime] :
    let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
    ∃ P : Sylow p G,
      let inl : G →* G ⋊[φ] A := SemidirectProduct.inl (φ := φ)
      let inr : A →* G ⋊[φ] A := SemidirectProduct.inr (φ := φ)
    let Pembed : Subgroup (G ⋊[φ] A) := (P : Subgroup G).map inl
    ((⊤ : Subgroup A).map inr) ≤ Subgroup.normalizer Pembed := by
  classical
  intro φ
  let : Finite (G ⋊[φ] A) :=
    Finite.of_equiv (G × A) (SemidirectProduct.equivProd (N := G) (G := A) (φ := φ)).symm
  let inl : G →* G ⋊[φ] A := SemidirectProduct.inl (φ := φ)
  let inr : A →* G ⋊[φ] A := SemidirectProduct.inr (φ := φ)
  let rightHom : G ⋊[φ] A →* A :=
    SemidirectProduct.rightHom (N := G) (G := A) (φ := φ)
  let N : Subgroup (G ⋊[φ] A) := inl.range
  let C : Subgroup (G ⋊[φ] A) := inr.range
  have hC_map : C = (⊤ : Subgroup A).map inr := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map_of_mem inr trivial
    · rintro ⟨a, _ha, rfl⟩
      exact ⟨a, rfl⟩
  have hN_eq_ker : N = rightHom.ker := by
    simpa [N, inl, rightHom, φ] using
      (SemidirectProduct.range_inl_eq_ker_rightHom (N := G) (G := A) (φ := φ))
  let : rightHom.ker.Normal := rightHom.normal_ker
  let : N.Normal := hN_eq_ker.symm ▸ (inferInstance : rightHom.ker.Normal)
  have hNC : N.IsComplement' C := by
    have hNmap : N = (⊤ : Subgroup G).map inl := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact Subgroup.mem_map_of_mem inl trivial
      · rintro ⟨g, _hg, rfl⟩
        exact ⟨g, rfl⟩
    have hCmap : C = (⊤ : Subgroup A).map inr := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact Subgroup.mem_map_of_mem inr trivial
      · rintro ⟨a, _ha, rfl⟩
        exact ⟨a, rfl⟩
    rw [hNmap, hCmap]
    simpa [inl, inr, φ] using
      (semidirect_range_inl_isComplement_range_inr (G := G) (A := A))
  have hinl_inj : Function.Injective inl := by
    simpa [inl, φ] using
      (SemidirectProduct.inl_injective (N := G) (G := A) (φ := φ) :
        Function.Injective (SemidirectProduct.inl (φ := φ) : G → G ⋊[φ] A))
  have hinr_inj : Function.Injective inr := by
    simpa [inr, φ] using
      (SemidirectProduct.inr_injective (N := G) (G := A) (φ := φ) :
        Function.Injective (SemidirectProduct.inr (φ := φ) : A → G ⋊[φ] A))
  have hcardN : Nat.card N = Nat.card G := by
    simpa [N] using
      (Subgroup.card_map_of_injective (K := (⊤ : Subgroup G)) (f := inl) hinl_inj)
  have hcardC : Nat.card C = Nat.card A := by
    simpa [C] using
      (Subgroup.card_map_of_injective (K := (⊤ : Subgroup A)) (f := inr) hinr_inj)
  have hcopNC : Nat.Coprime (Nat.card N) (Nat.card C) := by
    simpa [hcardN, hcardC] using hcoprime.symm
  have hC_solvable : Group.IsSolvable C := by
    dsimp [C]
    exact Group.isSolvable_of_surjective (f := inr.rangeRestrict) inr.rangeRestrict_surjective
  let : Group.IsSolvable C := hC_solvable
  obtain ⟨PN, hCnorm⟩ :=
    exists_sylow_normalized_by_solvable_complement_of_normal_hall_bg3
      (E := G ⋊[φ] A) (N := N) (C := C) hNC hcopNC (p := p)
  let inlN : G →* N := inl.rangeRestrict
  have hinlN_inj : Function.Injective inlN := by
    intro x y hxy
    exact hinl_inj (congrArg Subtype.val hxy)
  have hinlN_surj : Function.Surjective inlN := inl.rangeRestrict_surjective
  have hPN_le_range : (PN : Subgroup N) ≤ inlN.range := by
    intro x _hx
    rcases hinlN_surj x with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  let P : Sylow p G := PN.comapOfInjective inlN hinlN_inj hPN_le_range
  have hPembed :
      ((P : Subgroup G).map inl : Subgroup (G ⋊[φ] A)) =
        ((PN : Subgroup N).map N.subtype : Subgroup (G ⋊[φ] A)) := by
    ext x
    constructor
    · rintro ⟨g, hgP, rfl⟩
      refine ⟨inlN g, ?_, rfl⟩
      simpa [P, inlN] using hgP
    · rintro ⟨y, hyPN, rfl⟩
      rcases hinlN_surj y with ⟨g, hg⟩
      refine ⟨g, ?_, ?_⟩
      · have hgPN : inlN g ∈ (PN : Subgroup N) := by
          rw [hg]
          exact hyPN
        change inlN g ∈ (PN : Subgroup N)
        exact hgPN
      · exact congrArg Subtype.val hg
  refine ⟨P, ?_⟩
  change (⊤ : Subgroup A).map inr ≤ Subgroup.normalizer ((P : Subgroup G).map inl)
  rw [← hC_map]
  simpa [hPembed] using hCnorm

private theorem CFSG.isCyclic_of_prime_order_subgroups_centralize_of_card_mul
    {R : Type*} [Group R] [Finite R] {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    {P Q : Subgroup R} (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q)
    (hcent : P ≤ Subgroup.centralizer (Q : Set R))
    (hcardR : Nat.card R = p * q) :
    IsCyclic R := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hPcyc : IsCyclic P := isCyclic_of_prime_card (α := P) (p := p) hPcard
  have hQcyc : IsCyclic Q := isCyclic_of_prime_card (α := Q) (p := q) hQcard
  let : IsCyclic P := hPcyc
  let : IsCyclic Q := hQcyc
  obtain ⟨x, hx_order⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  obtain ⟨y, hy_order⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have hx_order_R : orderOf (x : R) = p := by
    rw [Subgroup.orderOf_coe, hx_order, hPcard]
  have hy_order_R : orderOf (y : R) = q := by
    rw [Subgroup.orderOf_coe, hy_order, hQcard]
  have hxy_comm : Commute (x : R) (y : R) := by
    exact (Subgroup.mem_centralizer_iff.mp (hcent x.2) (y : R) y.2).symm
  have horders_coprime : Nat.Coprime (orderOf (x : R)) (orderOf (y : R)) := by
    rw [hx_order_R, hy_order_R]
    exact (Nat.coprime_primes hp hq).2 hpq
  have hxy_order : orderOf ((x : R) * (y : R)) = p * q := by
    rw [hxy_comm.orderOf_mul_eq_mul_orderOf_of_coprime horders_coprime,
      hx_order_R, hy_order_R]
  exact isCyclic_of_orderOf_eq_card ((x : R) * (y : R)) (by rw [hxy_order, hcardR])

private theorem CFSG.fixedPointSubgroup_subgroup_eq_bot_of_regular_of_prime_card
    {H R : Type*} [Group H] [Finite H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hregular : ActsRegularly R H)
    {P : Subgroup R} (hPprime : Nat.Prime (Nat.card P)) :
    letI : MulDistribMulAction P H := MulDistribMulAction.compHom H P.subtype
    fixedPointSubgroup (↥P) H = ⊥ := by
  classical
  let : MulDistribMulAction P H := MulDistribMulAction.compHom H P.subtype
  have hP_ne_bot : P ≠ ⊥ := by
    intro hPbot
    exact hPprime.ne_one (by simp [hPbot])
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hP_ne_bot
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : P)
  apply le_antisymm
  · intro y hy
    have hxR_ne : (x : R) ≠ 1 := by
      intro hxR
      exact hx_ne (Subtype.ext hxR)
    have hy_z :
        y ∈ fixedPointSubgroup (↥(Subgroup.zpowers (x : R))) H := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy ⊢
      intro z
      have hzP : (z : R) ∈ P := (Subgroup.zpowers_le).2 x.2 z.2
      have hyP := hy ⟨(z : R), hzP⟩
      change (z : R) • y = y at hyP
      exact hyP
    simpa [hregular (x : R) hxR_ne] using hy_z
  · exact bot_le

private theorem CFSG.coprime_card_of_regular_action
    {H R : Type*} [Group H] [Finite H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hregular : ActsRegularly R H) :
    Nat.Coprime (Nat.card H) (Nat.card R) := by
  classical
  refine Nat.coprime_of_dvd ?_
  intro r hr_prime hr_dvd_H hr_dvd_R
  let : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨P, hPcard_pow⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := R) r (n := 1) (by
      simpa using hr_dvd_R)
  have hPcard : Nat.card P = r := by
    simpa using hPcard_pow
  have hPprime : Nat.Prime (Nat.card P) := by
    simpa [hPcard] using hr_prime
  let : MulDistribMulAction P H := MulDistribMulAction.compHom H P.subtype
  have hfix : fixedPointSubgroup (↥P) H = ⊥ :=
    fixedPointSubgroup_subgroup_eq_bot_of_regular_of_prime_card hregular hPprime
  have hPp : IsPGroup r P :=
    IsPGroup.of_card (G := P) (p := r) (n := 1) (by simp [hPcard])
  have hone_fix : (1 : H) ∈ MulAction.fixedPoints (↥P) H := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hx_fix, hx_ne_one⟩ :=
    hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := H) hr_dvd_H hone_fix
  have hx_mem : x ∈ fixedPointSubgroup (↥P) H := by
    rw [FixedPoints.mem_subgroup]
    exact MulAction.mem_fixedPoints.mp hx_fix
  have hx_bot : x ∈ (⊥ : Subgroup H) := by
    simpa [hfix] using hx_mem
  exact hx_ne_one (Subgroup.mem_bot.mp hx_bot).symm


public theorem CFSG.exists_invariant_sylow_of_solvable_operator_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [Group.IsSolvable A]
    [MulDistribMulAction A G] (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    {p : ℕ} [Fact p.Prime] :
    ∃ P : Sylow p G, IsInvariant A G (P : Subgroup G) := by
  classical
  by_cases hA_card_one : Nat.card A = 1
  · let : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA_card_one).1
    refine ⟨(default : Sylow p G), ?_⟩
    constructor
    intro a g
    have ha : a = 1 := Subsingleton.elim a 1
    constructor
    · intro hg
      simpa [ha] using hg
    · intro hg
      simpa [ha] using hg
  · -- Remaining source step: extend the proved prime-power operator case through a
    obtain ⟨P, hPnorm⟩ :=
      exists_sylow_normalized_by_semidirect_right_of_solvable_coprime
        (G := G) (A := A) hcoprime (p := p)
    exact ⟨P, isInvariant_of_inr_le_normalizer_map_inl_sylow (G := G) (A := A) P hPnorm⟩


private theorem CFSG.exists_regular_elementaryAbelian_invariant_subgroup_of_solvable_operator_regular_action_source
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [Group.IsSolvable R] [MulDistribMulAction R H] (hregular : ActsRegularly R H) :
    ∃ (E : Subgroup H) (r : ℕ) (hE_inv : IsInvariant R H E),
      r.Prime ∧ E ≠ ⊥ ∧ IsElementaryAbelian r (↥E) ∧
        letI : IsInvariant R H E := hE_inv
        ActsRegularly R E := by
  classical
  have hH_card_gt_one : 1 < Nat.card H :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨r, hr_prime, hr_dvd_H⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card H) (Nat.ne_of_gt hH_card_gt_one)
  let : Fact r.Prime := ⟨hr_prime⟩
  have hcopRH : Nat.Coprime (Nat.card R) (Nat.card H) :=
    (coprime_card_of_regular_action (H := H) (R := R) hregular).symm
  obtain ⟨S₀, hS₀_inv⟩ :=
    exists_invariant_sylow_of_solvable_operator_coprime
      (G := H) (A := R) hcopRH (p := r)
  let S : Subgroup H := S₀
  have : IsInvariant R H S := hS₀_inv
  have hS_ne_bot : S ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := H) (p := r) S₀ hr_dvd_H
  have hSsolv : Group.IsSolvable (↥S) := by
    have hSp : IsPGroup r S := S₀.isPGroup'
    have hSnil : Group.IsNilpotent S :=
      IsPGroup.isNilpotent (p := r) (G := S) (h := hSp)
    let : Group.IsNilpotent S := hSnil
    infer_instance
  exact
    exists_regular_elementaryAbelian_invariant_subgroup_of_invariant_solvable_subgroup
      (H := H) (R := R) hregular hS_ne_bot hSsolv

private theorem CFSG.subgroupCentralizerIn_eq_bot_of_not_le_centralizer_of_prime_card
    {R : Type*} [Group R] [Finite R] {P Q : Subgroup R}
    (hQprime : Nat.Prime (Nat.card Q))
    (hnot : ¬ P ≤ Subgroup.centralizer (Q : Set R)) :
    subgroupCentralizerIn Q P = ⊥ := by
  classical
  let C : Subgroup Q := (subgroupCentralizerIn Q P).subgroupOf Q
  have : Fact (Nat.Prime (Nat.card Q)) := ⟨hQprime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card C with hCbot | hCtop
  · apply (Subgroup.eq_bot_iff_card (H := subgroupCentralizerIn Q P)).2
    have hcardC : Nat.card C = 1 := by simp [C, hCbot]
    simpa [C, natCard_subgroupOf_eq (subgroupCentralizerIn Q P) Q inf_le_left] using hcardC
  · exfalso
    apply hnot
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyQ
    have hyC : (⟨y, hyQ⟩ : Q) ∈ C := by
      simp [C, hCtop]
    have hy_cent : y ∈ Subgroup.centralizer (P : Set R) := by
      exact (show y ∈ subgroupCentralizerIn Q P from hyC).2
    exact (Subgroup.mem_centralizer_iff.mp hy_cent x hxP).symm

private theorem CFSG.regular_pq_complement_centralizes_of_elementaryAbelian
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] {r p q : ℕ} [Fact r.Prime] [IsElementaryAbelian r H]
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hregular : ActsRegularly R H)
    {P Q : Subgroup R} (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q)
    (hQ_normal : Q.Normal) (hQP : Q.IsComplement' P) :
    P ≤ Subgroup.centralizer (Q : Set R) := by
  classical
  by_contra hnot
  have hPprime_card : Nat.Prime (Nat.card P) := by simpa [hPcard] using hp
  have hQprime_card : Nat.Prime (Nat.card Q) := by simpa [hQcard] using hq
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro hQbot
    exact hQprime_card.ne_one (by simp [hQbot])
  have hcent_bot : subgroupCentralizerIn Q P = ⊥ :=
    subgroupCentralizerIn_eq_bot_of_not_le_centralizer_of_prime_card hQprime_card hnot
  have hfrob : IsFrobeniusGroupWithKernelComplement Q P :=
    theorem_3_7_frobenius Q P hQ_normal hQP hQ_ne_bot hPprime_card hcent_bot
  let ρ : Representation (ZMod r) R (Additive H) :=
    Theory.Representation.ofElementaryAbelianAction (A := R) (G := H) (p := r)
  have hfixP : fixedPointSubgroup (↥P) H = ⊥ := by
    let : MulDistribMulAction P H := MulDistribMulAction.compHom H P.subtype
    exact fixedPointSubgroup_subgroup_eq_bot_of_regular_of_prime_card hregular hPprime_card
  have hρfixP : ρ.fixedSubspace P = ⊥ :=
    theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot
      (A := R) (V := H) (q := r) P hfixP
  have hfixQ : fixedPointSubgroup (↥Q) H = ⊥ := by
    let : MulDistribMulAction Q H := MulDistribMulAction.compHom H Q.subtype
    exact fixedPointSubgroup_subgroup_eq_bot_of_regular_of_prime_card hregular hQprime_card
  have hcop_r_Q : Nat.Coprime r (Nat.card Q) :=
    theorem_3_7_coprime_card_of_fixedPointSubgroup_eq_bot
      (A := R) (V := H) (q := r) Q hQprime_card hfixQ
  have hQ_not_le_ker : ¬ Q ≤ ρ.ker := by
    intro hQker
    have hQcent : Q ≤ ρ.centralizerIn Q := by
      intro x hx
      exact ⟨hx, hQker hx⟩
    have hfixQ_top : fixedPointSubgroup (↥Q) H = ⊤ :=
      theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn
        (A := R) (V := H) (q := r) Q hQcent
    exact top_ne_bot (hfixQ_top.symm.trans hfixQ)
  have hρfixP_ne : ρ.fixedSubspace P ≠ ⊥ :=
    lemma_3_3 Q P ρ hfrob
      (Or.inr ⟨by simpa [ZMod.ringChar_zmod_n] using (Fact.out : Nat.Prime r),
        by simpa [ZMod.ringChar_zmod_n] using hcop_r_Q⟩)
      hQ_not_le_ker
  exact hρfixP_ne hρfixP


public theorem CFSG.regular_pq_complement_centralizes_of_odd_regular_action_source
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcardR : Nat.card R = p * q) (hpq_lt : p < q)
    (hoddR : Odd (Nat.card R)) (hregular : ActsRegularly R H)
    {P Q : Subgroup R} (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q)
    (hQ_normal : Q.Normal) (hQP : Q.IsComplement' P)
    (hP_cyclic : IsCyclic P) (hQ_cyclic : IsCyclic Q) :
    P ≤ Subgroup.centralizer (Q : Set R) := by
  classical
  let _ := hpq
  let _ := hcardR
  let _ := hpq_lt
  let _ := hoddR
  have hQsolv : Group.IsSolvable Q := by
    let : IsCyclic Q := hQ_cyclic
    let : CommGroup Q := IsCyclic.commGroup
    infer_instance
  have hquot_cyclic : IsCyclic (R ⧸ Q) := by
    exact (hQP.symm.QuotientMulEquiv).isCyclic.mpr hP_cyclic
  have hquot_solv : Group.IsSolvable (R ⧸ Q) := by
    let : IsCyclic (R ⧸ Q) := hquot_cyclic
    let : CommGroup (R ⧸ Q) := IsCyclic.commGroup
    infer_instance
  have hsolvR : Group.IsSolvable R := by
    have : Group.IsSolvable Q := hQsolv
    have : Group.IsSolvable (R ⧸ Q) := hquot_solv
    refine Group.isSolvable_of_ker_le_range Q.subtype (QuotientGroup.mk' Q) ?_
    rw [QuotientGroup.ker_mk']
    simpa [MonoidHom.range_eq_map] using (Q.range_subtype : Q.subtype.range = Q).symm.le
  let : Group.IsSolvable R := hsolvR
  obtain ⟨E, r, hE_inv, hr, hE_ne_bot, hE_elem, hE_regular⟩ :=
    exists_regular_elementaryAbelian_invariant_subgroup_of_solvable_operator_regular_action_source
      (H := H) (R := R) hregular
  let : IsInvariant R H E := hE_inv
  let : Fact r.Prime := ⟨hr⟩
  have : IsElementaryAbelian r (↥E) := hE_elem
  have : Nontrivial (↥E) := (Subgroup.nontrivial_iff_ne_bot E).2 hE_ne_bot
  exact
    regular_pq_complement_centralizes_of_elementaryAbelian
      (H := E) (R := R) (r := r) hp hq hE_regular
      hPcard hQcard hQ_normal hQP


public theorem CFSG.regular_pq_prime_order_subgroups_centralize_of_odd_regular_action
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcardR : Nat.card R = p * q) (hpq_lt : p < q)
    (hoddR : Odd (Nat.card R)) (hregular : ActsRegularly R H)
    {P Q : Subgroup R} (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q) :
    P ≤ Subgroup.centralizer (Q : Set R) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q Q := by
    refine IsPGroup.of_card (p := q) (G := Q) (n := 1) ?_
    simpa using hQcard
  have hQindex : Q.index = p := by
    have hmul : q * Q.index = q * p := by
      calc
        q * Q.index = Nat.card Q * Q.index := by rw [hQcard]
        _ = Nat.card R := Q.card_mul_index
        _ = p * q := hcardR
        _ = q * p := by rw [mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hq.pos hmul
  have hq_not_dvd_Qindex : ¬ q ∣ Q.index := by
    rw [hQindex]
    intro hdiv
    exact (Nat.le_of_dvd hp.pos hdiv).not_gt hpq_lt
  let Qsyl : Sylow q R := hQp.toSylow hq_not_dvd_Qindex
  have hcardSyl_dvd_p : Nat.card (Sylow q R) ∣ p := by
    have h := Sylow.card_dvd_index Qsyl
    simpa [Qsyl, IsPGroup.toSylow_coe, hQindex] using h
  have hcardSyl_eq_one : Nat.card (Sylow q R) = 1 := by
    have hcardSyl_le_p : Nat.card (Sylow q R) ≤ p :=
      Nat.le_of_dvd hp.pos hcardSyl_dvd_p
    have hcardSyl_lt_q : Nat.card (Sylow q R) < q :=
      lt_of_le_of_lt hcardSyl_le_p hpq_lt
    have hcardSyl_mod : Nat.card (Sylow q R) % q = Nat.card (Sylow q R) :=
      Nat.mod_eq_of_lt hcardSyl_lt_q
    have hOne_mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
    have hmod : Nat.card (Sylow q R) % q = 1 % q :=
      (card_sylow_modEq_one q R : Nat.card (Sylow q R) ≡ 1 [MOD q])
    omega
  have : Subsingleton (Sylow q R) :=
    (Nat.card_eq_one_iff_unique.mp hcardSyl_eq_one).1
  have hQ_normal : Q.Normal := by
    have hQsyl_normal : (Qsyl : Subgroup R).Normal := Sylow.normal_of_subsingleton Qsyl
    simpa [Qsyl, IsPGroup.toSylow_coe] using hQsyl_normal
  have hcop_QP : Nat.Coprime (Nat.card Q) (Nat.card P) := by
    simpa [hQcard, hPcard] using ((Nat.coprime_primes hq hp).2 (Ne.symm hpq))
  have hQP_disj : Disjoint Q P := Subgroup.disjoint_of_coprime_natCard hcop_QP
  have hQP_card : Nat.card Q * Nat.card P = Nat.card R := by
    rw [hQcard, hPcard, hcardR, mul_comm]
  have hQP : Q.IsComplement' P :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hQP_card hQP_disj
  have hP_cyclic : IsCyclic P :=
    isCyclic_of_prime_card (α := P) (p := p) hPcard
  have hQ_cyclic : IsCyclic Q :=
    isCyclic_of_prime_card (α := Q) (p := q) hQcard
  exact
    regular_pq_complement_centralizes_of_odd_regular_action_source
      (H := H) (R := R) hp hq hpq hcardR hpq_lt hoddR hregular
      hPcard hQcard hQ_normal hQP hP_cyclic hQ_cyclic

private theorem CFSG.regular_pq_group_cyclic_of_odd_regular_action_ordered
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcardR : Nat.card R = p * q) (hpq_lt : p < q)
    (hoddR : Odd (Nat.card R)) (hregular : ActsRegularly R H) :
    IsCyclic R := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPcard_pow⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := R) p (n := 1) (by
      rw [hcardR]
      simp)
  obtain ⟨Q, hQcard_pow⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := R) q (n := 1) (by
      rw [hcardR]
      simp)
  have hPcard : Nat.card P = p := by simpa using hPcard_pow
  have hQcard : Nat.card Q = q := by simpa using hQcard_pow
  exact isCyclic_of_prime_order_subgroups_centralize_of_card_mul
    (R := R) hp hq hpq hPcard hQcard
    (regular_pq_prime_order_subgroups_centralize_of_odd_regular_action
      (H := H) (R := R) hp hq hpq hcardR hpq_lt hoddR hregular hPcard hQcard)
    hcardR

public theorem CFSG.prime_order_subgroup_le_centralizer_pCore_of_omega₁_join_commutative
    {R : Type*} [Group R] [Finite R] (hoddR : Odd (Nat.card R))
    {P : Subgroup R} (hPprime : Nat.Prime (Nat.card P)) {q : ℕ}
    [Fact q.Prime] (hq_ne : q ≠ Nat.card P)
    (hcomm :
      IsMulCommutative
        ↥(P ⊔ ((omega₁ (G := ↥(pCore q R)) (p := q)).map (pCore q R).subtype))) :
    P ≤ Subgroup.centralizer (pCore q R : Set R) := by
  classical
  by_cases hQbot : pCore q R = ⊥
  · intro a _ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx_one : x = 1 := by
      have hxbot : x ∈ (⊥ : Subgroup R) := by
        rw [← hQbot]
        exact hx
      exact Subgroup.mem_bot.mp hxbot
    simp [hx_one]
  · let Q : Subgroup R := pCore q R
    let ΩQ : Subgroup R := (omega₁ (G := ↥Q) (p := q)).map Q.subtype
    let S : Subgroup R := P ⊔ ΩQ
    have hQp : IsPGroup q Q := by
      simpa [Q] using (pCore_isPGroup (p := q) (G := R))
    have : Fact (IsPGroup q Q) := ⟨hQp⟩
    have hq_dvd_Q : q ∣ Nat.card Q := by
      obtain ⟨n, hQ_card⟩ := hQp.exists_card_eq
      have hQ_card_ne_one : Nat.card Q ≠ 1 := by
        intro hcard
        exact hQbot (by
          simpa [Q] using (Subgroup.eq_bot_iff_card (H := Q)).2 hcard)
      have hn_ne_zero : n ≠ 0 := by
        intro hn
        apply hQ_card_ne_one
        simp [hQ_card, hn]
      rw [hQ_card]
      exact dvd_pow_self q hn_ne_zero
    have hq_dvd_R : q ∣ Nat.card R :=
      hq_dvd_Q.trans (Subgroup.card_subgroup_dvd_card Q)
    have hq_odd : Odd q := odd_of_card_dvd hoddR hq_dvd_R
    have hq_ne_two : q ≠ 2 := by
      intro hq_eq
      rcases hq_odd with ⟨k, hk⟩
      omega
    have : Fact (Nat.Prime (Nat.card P)) := ⟨hPprime⟩
    have hPp : IsPGroup (Nat.card P) P := by
      exact IsPGroup.of_card (p := Nat.card P) (G := P) (n := 1) (by simp)
    have hcop_PQ : Nat.Coprime (Nat.card P) (Nat.card Q) := by
      exact
        IsPGroup.coprime_card_of_ne (Nat.card P) q (Ne.symm hq_ne) P Q hPp hQp
    have hPnormQ : P ≤ Subgroup.normalizer (Q : Set R) := by
      simpa [Q] using (Subgroup.le_normalizer_of_normal (H := pCore q R) : P ≤
        Subgroup.normalizer (pCore q R : Set R))
    let : Subgroup.Normalizes P Q := ⟨hPnormQ⟩
    let : MulDistribMulAction P Q :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (G := R) P Q hPnormQ
    have hcommS : IsMulCommutative S := by
      simpa [S, ΩQ, Q] using hcomm
    let : IsMulCommutative S := hcommS
    have hΩ_trivial :
        ActsTriviallyOnSubgroup (A := P) (G := Q) (omega₁ (G := ↥Q) (p := q)) := by
      intro a x hx
      apply Subtype.ext
      have hxΩQ : (x : R) ∈ ΩQ := by
        exact Subgroup.mem_map_of_mem Q.subtype hx
      have haS : (a : R) ∈ S := by
        exact (show P ≤ S from le_sup_left) a.2
      have hxS : (x : R) ∈ S := by
        exact (show ΩQ ≤ S from le_sup_right) hxΩQ
      have hmul : (a : R) * (x : R) = (x : R) * (a : R) := by
        exact setLike_mul_comm (s := S) haS hxS
      have hconj : (a : R) * (x : R) * (a : R)⁻¹ = (x : R) := by
        calc
          (a : R) * (x : R) * (a : R)⁻¹ = ((x : R) * (a : R)) * (a : R)⁻¹ := by
            rw [hmul]
          _ = (x : R) := by simp [mul_assoc]
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPnormQ] using hconj
    have htrivQ : ActsTrivially (A := P) (G := Q) :=
      theorem_1_11 (G := Q) (A := P) (p := q) hq_ne_two hcop_PQ hΩ_trivial
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfix : ((⟨a, ha⟩ : P) • (⟨x, hx⟩ : Q) : Q) = ⟨x, hx⟩ :=
      htrivQ ⟨a, ha⟩ ⟨x, hx⟩
    have hconj : a * x * a⁻¹ = x := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPnormQ] using
        congrArg Subtype.val hfix
    have hmul : a * x = x * a := by
      have := congrArg (fun t : R => t * a) hconj
      simpa [mul_assoc] using this
    exact hmul.symm

public theorem CFSG.isCyclic_of_isComplement'_of_cyclic_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
    (hKR : K.IsComplement' R) (hKcyc : IsCyclic K) (hRcyc : IsCyclic R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hcent : R ≤ Subgroup.centralizer (K : Set G)) :
    IsCyclic G := by
  classical
  let μ : K × R →* G :=
    { toFun := fun x => (x.1 : G) * (x.2 : G)
      map_one' := by simp
      map_mul' := by
        intro x y
        have hcomm : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) := by
          have hxcent : (x.2 : G) ∈ Subgroup.centralizer (K : Set G) := hcent x.2.2
          rw [Subgroup.mem_centralizer_iff] at hxcent
          exact hxcent (y.1 : G) y.1.2
        calc
          ((x.1 * y.1 : K) : G) * ((x.2 * y.2 : R) : G)
              = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
                simp [mul_assoc]
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
                rw [hcomm]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by
                simp [mul_assoc] }
  have hμ_bij : Function.Bijective μ := by
    simpa [μ] using
      (Subgroup.isComplement_iff_bijective (s := K) (t := R)).1
        ((Subgroup.isComplement'_def).1 hKR)
  let eG : K × R ≃* G := MulEquiv.ofBijective μ hμ_bij
  have hprod_cyclic : IsCyclic (K × R) := by
    exact (Group.isCyclic_prod_iff (M := K) (N := R)).2 ⟨hKcyc, hRcyc, hcop⟩
  exact eG.isCyclic.mp hprod_cyclic

public theorem CFSG.regular_pq_group_cyclic_of_odd_regular_action
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcardR : Nat.card R = p * q)
    (hoddR : Odd (Nat.card R))
    (hregular : ActsRegularly R H) :
    IsCyclic R := by
  by_cases hp_lt_q : p < q
  · exact regular_pq_group_cyclic_of_odd_regular_action_ordered
      (H := H) (R := R) hp hq hpq hcardR hp_lt_q hoddR hregular
  · have hq_lt_p : q < p :=
      lt_of_le_of_ne (Nat.le_of_not_gt hp_lt_q) (Ne.symm hpq)
    have hcardR' : Nat.card R = q * p := by
      rw [hcardR, mul_comm]
    exact regular_pq_group_cyclic_of_odd_regular_action_ordered
      (H := H) (R := R) hq hp (Ne.symm hpq) hcardR' hq_lt_p hoddR hregular


public theorem CFSG.prime_order_subgroup_omega₁_pCore_join_commutative_of_odd_regular_action
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hoddR : Odd (Nat.card R))
    (hregular : ActsRegularly R H) {P : Subgroup R}
    (hPprime : Nat.Prime (Nat.card P)) {q : ℕ} [Fact q.Prime]
    (hq_ne : q ≠ Nat.card P) (hQ_ne_bot : pCore q R ≠ ⊥) :
    IsMulCommutative
      ↥(P ⊔ ((omega₁ (G := ↥(pCore q R)) (p := q)).map (pCore q R).subtype)) := by
  classical
  let Q : Subgroup R := pCore q R
  let ΩQ : Subgroup R := (omega₁ (G := Q) (p := q)).map Q.subtype
  let S : Subgroup R := P ⊔ ΩQ
  have hQp : IsPGroup q Q := by
    simpa [Q] using (pCore_isPGroup (p := q) (G := R))
  have : Fact (IsPGroup q Q) := ⟨hQp⟩
  have hQ_ne : Q ≠ ⊥ := by
    simpa [Q] using hQ_ne_bot
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ_ne
  have hQcyc : IsCyclic Q :=
    isCyclic_of_odd_regular_pSubgroup (H := H) (R := R) (P := Q) (p := q)
      (Fact.out : Nat.Prime q) hoddR hregular hQp
  have hΩQ_card : Nat.card ΩQ = q := by
    calc
      Nat.card ΩQ = Nat.card (omega₁ (G := Q) (p := q)) := by
        exact Subgroup.card_map_of_injective
          (K := omega₁ (G := Q) (p := q)) (f := Q.subtype) Q.subtype_injective
      _ = q := natCard_omega₁_cyclic_pGroup_eq_prime (H := Q) (p := q) hQcyc
  have hp_ne_q : Nat.card P ≠ q := by
    intro hpq
    exact hq_ne hpq.symm
  have hPΩ_coprime : Nat.Coprime (Nat.card P) (Nat.card ΩQ) := by
    simpa [hΩQ_card] using
      ((Nat.coprime_primes hPprime (Fact.out : Nat.Prime q)).2 hp_ne_q)
  have hP_inf_ΩQ : P ⊓ ΩQ = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hPΩ_coprime).eq_bot
  have hΩQ_inf_P : ΩQ ⊓ P = ⊥ := by
    simpa [inf_comm] using hP_inf_ΩQ
  have hΩQ_disj_P : Disjoint ΩQ P :=
    disjoint_iff.mpr hΩQ_inf_P
  have : Q.Normal := by
    simpa [Q] using (pCore_normal (p := q) (G := R))
  have hΩQ_normal : ΩQ.Normal := by
    simpa [ΩQ, Q] using
      (omega₁_map_subtype_normal_of_normal (R := R) (p := q) (A := Q))
  let : ΩQ.Normal := hΩQ_normal
  have hcard_ΩQ_sup_P : Nat.card ↥(ΩQ ⊔ P : Subgroup R) = q * Nat.card P := by
    have hcomp :
        (ΩQ.subgroupOf (ΩQ ⊔ P)).IsComplement' (P.subgroupOf (ΩQ ⊔ P)) :=
      isComplement'_subgroupOf_sup_of_disjoint ΩQ P hΩQ_disj_P
    calc
      Nat.card ↥(ΩQ ⊔ P : Subgroup R)
          = Nat.card (ΩQ.subgroupOf (ΩQ ⊔ P)) *
              Nat.card (P.subgroupOf (ΩQ ⊔ P)) := by
            exact hcomp.card_mul_card.symm
      _ = Nat.card ΩQ * Nat.card P := by
        rw [natCard_subgroupOf_eq ΩQ (ΩQ ⊔ P) le_sup_left,
          natCard_subgroupOf_eq P (ΩQ ⊔ P) le_sup_right]
      _ = q * Nat.card P := by rw [hΩQ_card]
  have hcardS : Nat.card S = Nat.card P * q := by
    change Nat.card ↥(P ⊔ ΩQ : Subgroup R) = Nat.card P * q
    calc
      Nat.card ↥(P ⊔ ΩQ : Subgroup R) = Nat.card ↥(ΩQ ⊔ P : Subgroup R) := by
        rw [sup_comm]
      _ = q * Nat.card P := hcard_ΩQ_sup_P
      _ = Nat.card P * q := by rw [mul_comm]
  let : MulDistribMulAction S H := MulDistribMulAction.compHom H S.subtype
  have hregularS : ActsRegularly S H :=
    ActsRegularly.subgroup (H := H) (R := R) hregular S
  have hoddS : Odd (Nat.card S) :=
    odd_of_card_dvd hoddR (Subgroup.card_subgroup_dvd_card S)
  have hcycS : IsCyclic S :=
    regular_pq_group_cyclic_of_odd_regular_action (H := H) (R := S)
      (p := Nat.card P) (q := q) hPprime (Fact.out : Nat.Prime q) hp_ne_q hcardS
      hoddS hregularS
  let : CommGroup S := hcycS.commGroup
  simpa [S, ΩQ, Q] using (inferInstance : IsMulCommutative S)


public theorem CFSG.prime_order_subgroup_le_centralizer_fitting_of_odd_regular_action
    {H R : Type*} [Group H] [Finite H] [Nontrivial H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hoddR : Odd (Nat.card R))
    (hregular : ActsRegularly R H) {P : Subgroup R}
    (hPprime : Nat.Prime (Nat.card P)) :
    P ≤ Subgroup.centralizer (fittingSubgroup R : Set R) := by
  classical
  refine subgroup_le_centralizer_fitting_of_le_centralizer_pCores (G := R) (P := P) ?_
  intro q
  let qNat : ℕ := q.1.1
  have hqprime : Nat.Prime qNat := Nat.prime_of_mem_primeFactors q.1.2
  let : Fact qNat.Prime := ⟨hqprime⟩
  by_cases hq_eq : qNat = Nat.card P
  · have hPq : IsPGroup qNat P := by
      exact IsPGroup.of_card (p := qNat) (G := P) (n := 1) (by simp [hq_eq])
    have hcycSylow : ∀ S : Sylow qNat R, IsCyclic (S : Subgroup R) := by
      intro S
      exact isCyclic_of_odd_regular_pSubgroup (H := H) (R := R) (p := qNat)
        hqprime hoddR hregular (P := (S : Subgroup R)) S.isPGroup'
    exact pSubgroup_le_centralizer_pCore_of_cyclic_sylow_fitting
      (G := R) (p := qNat) (P := P) hPq hcycSylow
  · by_cases hQbot : pCore qNat R = ⊥
    · intro a _ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx_one : x = 1 := by
        have hxbot : x ∈ (⊥ : Subgroup R) := by simpa [qNat, hQbot] using hx
        exact Subgroup.mem_bot.mp hxbot
      simp [hx_one]
    · have hcomm :
          IsMulCommutative
            ↥(P ⊔ ((omega₁ (G := ↥(pCore qNat R)) (p := qNat)).map
              (pCore qNat R).subtype)) :=
        prime_order_subgroup_omega₁_pCore_join_commutative_of_odd_regular_action
          (H := H) (R := R) hoddR hregular hPprime hq_eq hQbot
      exact prime_order_subgroup_le_centralizer_pCore_of_omega₁_join_commutative
        (R := R) hoddR hPprime hq_eq hcomm

public theorem CFSG.isZGroup_of_frobenius_complement_of_odd
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hoddR : Odd (Nat.card R)) :
    IsZGroup R := by
  classical
  rw [isZGroup_iff]
  intro p hp P
  let : K.Normal := hfrob.normal
  have hregularR :
      let : MulDistribMulAction (↥R) (↥K) :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R K
          (Subgroup.le_normalizer_of_normal (H := K))
      ActsRegularly (↥R) (↥K) :=
    hfrob.regular_conj_action
  let : MulDistribMulAction (↥R) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R K
      (Subgroup.le_normalizer_of_normal (H := K))
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hfrob.kernel_ne_bot
  exact isCyclic_of_odd_regular_pSubgroup (H := K) (R := R) (P := (P : Subgroup R))
    hp hoddR hregularR P.isPGroup'

private theorem CFSG.theorem_3_10_subambient_frobenius
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    {R₀ : Subgroup G} (hR₀_le : R₀ ≤ R) (hR₀_ne_bot : R₀ ≠ ⊥) :
    IsFrobeniusGroupWithKernelComplement (K.subgroupOf (K ⊔ R₀)) (R₀.subgroupOf (K ⊔ R₀)) := by
  let : K.Normal := hfrob.normal
  let S : Subgroup G := K ⊔ R₀
  have hKsub_ne_bot : K.subgroupOf S ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card K = 1 := by
      calc
        Nat.card K = Nat.card (K.subgroupOf S) := by
          symm
          exact natCard_subgroupOf_eq K S le_sup_left
        _ = 1 := by simp [hbot]
    exact hfrob.kernel_ne_bot ((Subgroup.eq_bot_iff_card (H := K)).2 hcard)
  have hR₀sub_ne_bot : R₀.subgroupOf S ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card R₀ = 1 := by
      calc
        Nat.card R₀ = Nat.card (R₀.subgroupOf S) := by
          symm
          exact natCard_subgroupOf_eq R₀ S le_sup_right
        _ = 1 := by simp [hbot]
    exact hR₀_ne_bot ((Subgroup.eq_bot_iff_card (H := R₀)).2 hcard)
  have hcompS : (K.subgroupOf S).IsComplement' (R₀.subgroupOf S) := by
    have hdisj0 : Disjoint K R₀ := hfrob.isComplement'.disjoint.mono_right hR₀_le
    exact isComplement'_subgroupOf_sup_of_disjoint K R₀ hdisj0
  have hcent :
      ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hfrob.kernel_ne_bot hfrob.complement_ne_bot
      hfrob.normal hfrob.isComplement').1 hfrob
  have hcentS :
      ∀ x : R₀.subgroupOf S, x ≠ 1 →
        elementCentralizerIn (K.subgroupOf S) (x : S) = ⊥ := by
    intro x hx
    have hxR : (⟨(x : G), hR₀_le x.2⟩ : R) ≠ 1 := by
      intro hx1
      apply hx
      ext
      simpa using congrArg Subtype.val hx1
    calc
      elementCentralizerIn (K.subgroupOf S) (x : S)
          = (elementCentralizerIn K (x : G)).subgroupOf S := by
              simpa [S] using
                theorem_3_8_elementCentralizerIn_subgroupOf_eq S K (x : G) ((x : S).2)
      _ = (⊥ : Subgroup S) := by
            rw [hcent ⟨(x : G), hR₀_le x.2⟩ hxR]
            simp
  exact
    (lemma_3_1 (K := K.subgroupOf S) (R := R₀.subgroupOf S) hKsub_ne_bot hR₀sub_ne_bot
      (Subgroup.Normal.subgroupOf (G := G) (hH := hfrob.normal) S) hcompS).2 hcentS

private theorem CFSG.theorem_3_10_subambient_card_lt_of_right_lt
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    {R₀ : Subgroup G} (hR₀_lt_R : R₀ < R) :
    Nat.card ↥(K ⊔ R₀) < Nat.card G := by
  let : K.Normal := hfrob.normal
  let S : Subgroup G := K ⊔ R₀
  have hdisj0 : Disjoint K R₀ := hfrob.isComplement'.disjoint.mono_right hR₀_lt_R.1
  have hcompS : (K.subgroupOf S).IsComplement' (R₀.subgroupOf S) :=
    isComplement'_subgroupOf_sup_of_disjoint K R₀ hdisj0
  have hcardS_eq : Nat.card ↥K * Nat.card ↥R₀ = Nat.card ↥S := by
    simpa [S, natCard_subgroupOf_eq K S le_sup_left,
      natCard_subgroupOf_eq R₀ S le_sup_right] using hcompS.card_mul_card
  have hcardG_eq : Nat.card ↥K * Nat.card ↥R = Nat.card G := by
    simpa using hfrob.isComplement'.card_mul_card
  have hcardR₀_lt_R : Nat.card ↥R₀ < Nat.card ↥R := natCard_lt_of_subgroup_lt hR₀_lt_R
  have hlt_mul : Nat.card ↥K * Nat.card ↥R₀ < Nat.card ↥K * Nat.card ↥R := by
    exact Nat.mul_lt_mul_of_pos_left hcardR₀_lt_R (Nat.card_pos (α := ↥K))
  calc
    Nat.card ↥(K ⊔ R₀) = Nat.card ↥K * Nat.card ↥R₀ := hcardS_eq.symm
    _ < Nat.card ↥K * Nat.card ↥R := hlt_mul
    _ = Nat.card G := hcardG_eq

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_subgroupOf_eq
    {S A : Subgroup G} (hA_le : A ≤ S) :
    letI : MulDistribMulAction S M := MulDistribMulAction.compHom M S.subtype
    fixedPointSubgroup (↥(A.subgroupOf S)) M = fixedPointSubgroup (↥A) M := by
  let : MulDistribMulAction S M := MulDistribMulAction.compHom M S.subtype
  ext x
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hx a
    have ha :
        (⟨⟨(a : G), hA_le a.2⟩, by
          show ((⟨(a : G), hA_le a.2⟩ : S) : G) ∈ A
          exact a.2⟩ : A.subgroupOf S) • x = x :=
      hx ⟨⟨(a : G), hA_le a.2⟩, by
        show ((⟨(a : G), hA_le a.2⟩ : S) : G) ∈ A
        exact a.2⟩
    change (a : G) • x = x at ha
    exact ha
  · intro hx a
    have hx' : ((⟨(a : S), by
      show ((a : S) : G) ∈ A
      exact a.2⟩ : A) : G) • x = x := by
      exact hx ⟨(a : S), by
        show ((a : S) : G) ∈ A
        exact a.2⟩
    change (a : G) • x = x at hx'
    exact hx'

omit [Finite G] in
private theorem CFSG.theorem_3_10_zpowers_subgroupOf_eq
    {S : Subgroup G} (x : S) :
    (Subgroup.zpowers (x : G)).subgroupOf S = Subgroup.zpowers x := by
  ext y
  constructor
  · intro hy
    have hyz : ((y : S) : G) ∈ Subgroup.zpowers (x : G) := by
      simpa [Subgroup.mem_subgroupOf] using hy
    rcases Subgroup.mem_zpowers_iff.mp hyz with ⟨n, hn⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
      apply Subtype.ext
      simpa using hn⟩
  · intro hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, hn⟩
    have hyz : ((y : S) : G) ∈ Subgroup.zpowers (x : G) := by
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    simpa [Subgroup.mem_subgroupOf] using hyz

omit [Finite G] in
private theorem CFSG.theorem_3_10_case2_elementaryAbelian
    (hnilM : Group.IsNilpotent M)
    (hminv :
      ∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p M := by
  classical
  have hM_card_gt_one : 1 < Nat.card M := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨p, hp_prime, hp_dvd_cardM⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card M) (Nat.ne_of_gt hM_card_gt_one)
  let : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p M := default
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) (p := p) P hp_dvd_cardM
  have hP_normal : (P : Subgroup M).Normal := Group.IsNilpotent.sylow_normal hnilM p P
  let : (P : Subgroup M).Characteristic := Sylow.characteristic_of_normal P hP_normal
  have hP_inv : IsInvariant G M (P : Subgroup M) :=
    isInvariant_of_characteristic (A := G) (G := M) (P : Subgroup M)
  have hP_top : (P : Subgroup M) = ⊤ :=
    hminv (P : Subgroup M) hP_normal hP_inv hP_ne_bot
  have htop_p : IsPGroup p (⊤ : Subgroup M) :=
    P.isPGroup'.of_equiv (MulEquiv.subgroupCongr hP_top)
  have hMpgroup : IsPGroup p M := htop_p.of_equiv Subgroup.topEquiv
  let : Fact (IsPGroup p M) := ⟨hMpgroup⟩
  have hcenter_ne_bot : Subgroup.center M ≠ ⊥ := by
    let : Nontrivial (Subgroup.center M) := IsPGroup.center_nontrivial (p := p) (G := M) hMpgroup
    exact (Subgroup.nontrivial_iff_ne_bot (H := Subgroup.center M)).1 inferInstance
  let : (Subgroup.center M).Characteristic := Subgroup.centerCharacteristic
  have hcenter_inv : IsInvariant G M (Subgroup.center M) :=
    isInvariant_of_characteristic (A := G) (G := M) (Subgroup.center M)
  have hcenter_top : Subgroup.center M = ⊤ :=
    hminv (Subgroup.center M) inferInstance hcenter_inv hcenter_ne_bot
  have hcommM : IsMulCommutative M := by
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b ↦ ?_
    have ha_center : a ∈ Subgroup.center M := by
      simp [hcenter_top]
    exact ((Subgroup.mem_center_iff.mp ha_center) b).symm
  let : IsMulCommutative M := hcommM

  let Ω : Subgroup M := omega₁ (G := M) (p := p)
  let : Ω.Characteristic := by simpa [Ω] using omega₁_characteristic (G := M) (p := p)
  have hΩ_inv : IsInvariant G M Ω := isInvariant_of_characteristic (A := G) (G := M) Ω
  have hΩ_ne_bot : Ω ≠ ⊥ := by
    let : Fintype M := Fintype.ofFinite M
    obtain ⟨x, hx_order⟩ := _root_.exists_prime_orderOf_dvd_card (G := M) p <| by
      simpa [Nat.card_eq_fintype_card] using hp_dvd_cardM
    have hx_ne_one : x ≠ (1 : M) := by
      intro hx
      have : 1 = p := by simpa [hx] using hx_order
      exact hp_prime.ne_one this.symm
    have hx_pow : x ^ p = 1 := by
      simpa [hx_order] using pow_orderOf_eq_one x
    have hx_mem : x ∈ Ω := by
      change x ∈ Subgroup.closure {y : M | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [Ω, omega₁, omega, pow_one] using hx_pow
    intro hΩ_bot
    have hx_bot : x ∈ (⊥ : Subgroup M) := by
      simpa [hΩ_bot] using hx_mem
    exact hx_ne_one (by simpa using hx_bot)
  have hΩ_top : Ω = ⊤ := hminv Ω inferInstance hΩ_inv hΩ_ne_bot

  have hpow : ∀ x : M, x ^ p = 1 := by
    intro x
    have hxΩ : x ∈ Ω := by simp [hΩ_top]
    have hx' : x ∈ Subgroup.closure {y : M | y ^ (p ^ 1) = 1} := by
      simpa [Ω, omega₁, omega] using hxΩ
    refine
      Subgroup.closure_induction (k := {y : M | y ^ (p ^ 1) = 1})
        (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simpa [pow_one] using hy
    · simp
    · intro a b _ha _hb ha hb
      calc
        (a * b) ^ p = a ^ p * b ^ p := by simpa using mul_pow a b p
        _ = 1 := by simp [ha, hb]
    · intro a _ha ha
      simp [ha]
  refine ⟨p, hp_prime, ?_⟩
  exact
    { toIsMulCommutative := hcommM
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow }

omit [Finite G] [Finite M] in
private theorem CFSG.theorem_3_10_case2_irreducible
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hminv :
      ∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤) :
    Representation.IsIrreducible
      (Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := p) :
        Representation (ZMod p) G (Additive M)) := by
  let ρ : Representation (ZMod p) G (Additive M) :=
    Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := p)
  refine
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := ?_ }
  intro S
  let N : Subgroup M := S.toSubmodule.toAddSubgroup.toSubgroup'
  have hN_inv : IsInvariant G M N := by
    have hmap_mem (g : G) {x : M} (hx : x ∈ N) : g • x ∈ N := by
      change Additive.ofMul (g • x) ∈ S.toSubmodule
      have hx' : Additive.ofMul x ∈ S.toSubmodule := by
        change Additive.ofMul x ∈ S.toSubmodule at hx
        exact hx
      have hx'' := S.apply_mem_toSubmodule g hx'
      simpa [ρ, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
    refine { invariant := ?_ }
    intro g x
    constructor
    · intro hx
      exact hmap_mem g hx
    · intro hx
      have hx' : (g : G)⁻¹ • ((g : G) • x) ∈ N := hmap_mem (g : G)⁻¹ hx
      simpa [smul_smul] using hx'
  by_cases hN_bot : N = ⊥
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_bot]
    constructor
    · intro hx
      simpa [hx]
    · intro hx
      have hx' : x ∈ (⊥ : Submodule (ZMod p) (Additive M)) := by
        let Z : Subrepresentation
            (Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := p) :
              Representation (ZMod p) G (Additive M)) :=
          { toSubmodule := ⊥
            apply_mem_toSubmodule := by simp }
        have hxZ : x ∈ Z :=
          (show (⊥ : Subrepresentation
            (Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := p) :
              Representation (ZMod p) G (Additive M))) ≤ Z from bot_le) hx
        exact hxZ
      simpa using hx'
  · right
    have hN_top : N = ⊤ := hminv N inferInstance hN_inv hN_bot
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_top]
    constructor
    · intro _hx
      exact Submodule.mem_top
    · intro _hx
      simp

private theorem CFSG.theorem_3_10_case2_fixedPointSubgroup_ne_bot
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥) :
    fixedPointSubgroup (↥R) M ≠ ⊥ := by
  let ρ : Representation (ZMod p) G (Additive M) :=
    Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := p)
  have hp_cop_G : Nat.Coprime p (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p M).exists_card_eq
    have hn_pos : 0 < n := by
      have hM_card_gt_one : 1 < Nat.card M := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rw [hn] at hM_card_gt_one
      cases n with
      | zero =>
          simp at hM_card_gt_one
      | succ n =>
          exact Nat.succ_pos _
    have hp_cop_pow : Nat.Coprime (Nat.card G) (p ^ n) := by simpa [hn] using hcop
    exact hp_cop_pow.symm.of_dvd_left (dvd_pow_self p (Nat.ne_of_gt hn_pos))
  have hp_cop_K : Nat.Coprime p (Nat.card K) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card K) hp_cop_G
  have hK_nontrivial : ¬ K ≤ ρ.ker := by
    intro hKker
    have hKcent : K ≤ ρ.centralizerIn K := by
      exact (le_centralizerIn_iff_le_ker (ρ := ρ) (H := K) (K := K) le_rfl).2 hKker
    have hfix_top : fixedPointSubgroup (↥K) M = ⊤ :=
      theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn (A := G) (V := M) (q := p) K
        hKcent
    exact top_ne_bot (hfix_top.symm.trans hfixK)
  have hfixR_sub_ne : ρ.fixedSubspace R ≠ ⊥ :=
    lemma_3_3 K R ρ hfrob
      (Or.inr ⟨by simpa [ZMod.ringChar_zmod_n] using (Fact.out : Nat.Prime p),
        by simpa [ZMod.ringChar_zmod_n] using hp_cop_K⟩)
      hK_nontrivial
  intro hfixR
  exact hfixR_sub_ne <|
    theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot (A := G) (V := M) (q := p) R
      hfixR

omit [Finite M] in
private theorem CFSG.theorem_3_10_case2_faithful_action
    (hK_min : ∀ N : Subgroup G, N.Normal → N ≤ K → N ≠ ⊥ → N = K)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hfixK : fixedPointSubgroup (↥K) M = ⊥) :
    actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G) = ⊥ := by
  let C := actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G)
  have hC_normal : C.Normal := by
    have hC_eq_ker : C = (MulDistribMulAction.toMulAut G M).ker := by
      calc
        C = actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G) := rfl
        _ = (⊤ : Subgroup G) ⊓ fixingSubgroupOf G M Set.univ := rfl
        _ = fixingSubgroupOf G M Set.univ := by simp
        _ = (MulDistribMulAction.toMulAut G M).ker :=
          fixingSubgroupOf_univ_eq_ker_toMulAut
    rw [hC_eq_ker]
    infer_instance
  have hK_not_le_C : ¬ K ≤ C := by
    intro hK_le_C
    have hfix_top : fixedPointSubgroup (↥K) M = ⊤ := by
      refine le_antisymm le_top ?_
      intro m hm
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro k
      have hkC : (k : G) ∈ C := hK_le_C k.2
      dsimp [C, actionCentralizerIn] at hkC
      have hk_fix : (k : G) ∈ fixingSubgroupOf G M Set.univ := hkC.2
      rw [mem_fixingSubgroup_iff] at hk_fix
      exact hk_fix m (Set.mem_univ m)
    rw [hfixK] at hfix_top
    exact top_ne_bot hfix_top.symm
  have hC_le_K : C ≤ K :=
    lemma_3_2_a_no_solv (K := K) (R := R) (N := C) hfrob hK_not_le_C
  by_cases hC_bot : C = ⊥
  · exact hC_bot
  · have hC_eq_K : C = K := hK_min C hC_normal hC_le_K hC_bot
    exfalso
    exact hK_not_le_C (hC_eq_K ▸ le_refl K)


private noncomputable def CFSG.theorem_3_10_ofElementaryAbelianActionFixedSubspaceEquiv
    {A V : Type*} [Group A] [Group V] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p V] [MulDistribMulAction A V] (H : Subgroup A) :
    ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p) :
      Representation (ZMod p) A (Additive V)).fixedSubspace H) ≃
      Additive ↥(fixedPointSubgroup (↥H) V) := by
  refine
    { toFun := fun x =>
        Additive.ofMul ⟨Additive.toMul x.1, by
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
          intro h
          exact Additive.ofMul.injective (by
            change Additive.ofMul ((h : A) • Additive.toMul x.1) = x.1
            have hx := x.2 h
            change
              (Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p) :
                Representation (ZMod p) A (Additive V)) (h : A) x.1 = x.1 at hx
            rw [Theory.Representation.ofElementaryAbelianAction_apply] at hx
            exact hx)⟩
      invFun := fun y =>
        ⟨Additive.ofMul ((Additive.toMul y : ↥(fixedPointSubgroup (↥H) V)) : V), by
          intro h
          let yH : fixedPointSubgroup (↥H) V := Additive.toMul y
          have hy := yH.2 h
          change (h : A) • (yH : V) = (yH : V) at hy
          change
            (Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p) :
              Representation (ZMod p) A (Additive V)) (h : A) (Additive.ofMul (yH : V)) =
                Additive.ofMul (yH : V)
          rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
          exact congrArg Additive.ofMul hy⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl }

private theorem CFSG.theorem_3_10_natCard_eq_prime_of_cyclic_elementaryAbelian
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Nontrivial G]
    [IsElementaryAbelian p G] (hcyc : IsCyclic G) :
    Nat.card G = p := by
  have hcard_dvd : Nat.card G ∣ p := by
    rw [← hcyc.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p p G
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hcard_dvd with hcard_one | hcard_p
  · exact False.elim <|
      (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial G)).ne' hcard_one
  · exact hcard_p

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_eq_bot_of_invariant_subgroup
    {A : Subgroup G} {N : Subgroup M} [IsInvariant G M N]
    (hfixA : fixedPointSubgroup (↥A) M = ⊥) :
    fixedPointSubgroup (↥A) N = ⊥ := by
  let : IsInvariant A M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact IsInvariant.invariant (A := G) (G := M) (H := N) (a : G) g }
  apply
    (Subgroup.map_eq_bot_iff_of_injective
      (H := fixedPointSubgroup (↥A) N) (f := N.subtype) N.subtype_injective).1
  rw [fixedPointSubgroup_map_subtype_eq_inf]
  simp [hfixA]

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_eq_of_invariant_subgroup
    {N : Subgroup M} [IsInvariant G M N]
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    ∀ x : R, x ≠ 1 →
      fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) N = fixedPointSubgroup (↥R) N := by
  let : IsInvariant (↥R) M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact IsInvariant.invariant (A := G) (G := M) (H := N) (a : G) g }
  intro x hx
  let : IsInvariant (↥(Subgroup.zpowers (x : G))) M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact IsInvariant.invariant (A := G) (G := M) (H := N) (a : G) g }
  apply (Subgroup.map_injective (f := N.subtype) N.subtype_injective)
  rw [fixedPointSubgroup_map_subtype_eq_inf, fixedPointSubgroup_map_subtype_eq_inf, hfixR x hx]

omit [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_eq_bot_of_quotient
    {A : Subgroup G} {N : Subgroup M} [N.Normal] (hNinv : IsInvariant G M N)
    (hsolvM : Group.IsSolvable M) (hcopA : Nat.Coprime (Nat.card A) (Nat.card M))
    (hfixA : fixedPointSubgroup (↥A) M = ⊥) :
    letI : MulDistribMulAction G (M ⧸ N) :=
      quotientMulDistribMulAction (A := G) (G := M) N hNinv
    fixedPointSubgroup (↥A) (M ⧸ N) = ⊥ := by
  let : MulDistribMulAction G (M ⧸ N) :=
    quotientMulDistribMulAction (A := G) (G := M) N hNinv
  let : MulAction.QuotientAction G N := quotientAction_of_isInvariant (A := G) N hNinv
  let : IsInvariant A M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact hNinv.invariant (a : G) g }
  rw [fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
    (G := M) (A := ↥A) hsolvM hcopA (π := ∅) (H := N) inferInstance]
  simp [hfixA]

omit [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_eq_of_quotient
    {N : Subgroup M} [N.Normal] (hNinv : IsInvariant G M N)
    (hsolvM : Group.IsSolvable M) (hcopR : Nat.Coprime (Nat.card R) (Nat.card M))
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    letI : MulDistribMulAction G (M ⧸ N) :=
      quotientMulDistribMulAction (A := G) (G := M) N hNinv
    ∀ x : R, x ≠ 1 →
      fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) (M ⧸ N) =
        fixedPointSubgroup (↥R) (M ⧸ N) := by
  let : MulDistribMulAction G (M ⧸ N) :=
    quotientMulDistribMulAction (A := G) (G := M) N hNinv
  let : MulAction.QuotientAction G N := quotientAction_of_isInvariant (A := G) N hNinv
  let : IsInvariant (↥R) M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact hNinv.invariant (a : G) g }
  intro x hx
  have hz_dvd : Nat.card (Subgroup.zpowers (x : G)) ∣ Nat.card R := by
    rw [← natCard_subgroupOf_eq (Subgroup.zpowers (x : G)) R (Subgroup.zpowers_le.2 x.2)]
    exact Subgroup.card_subgroup_dvd_card ((Subgroup.zpowers (x : G)).subgroupOf R)
  have hz_cop : Nat.Coprime (Nat.card (Subgroup.zpowers (x : G))) (Nat.card M) := by
    exact Nat.Coprime.of_dvd_left hz_dvd hcopR
  let : IsInvariant (↥(Subgroup.zpowers (x : G))) M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact hNinv.invariant (a : G) g }
  calc
    fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) (M ⧸ N)
        = (fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M).map (QuotientGroup.mk' N) := by
            rw [fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
              (G := M) (A := ↥(Subgroup.zpowers (x : G))) hsolvM hz_cop (π := ∅) (H := N)
              inferInstance]
    _ = (fixedPointSubgroup (↥R) M).map (QuotientGroup.mk' N) := by rw [hfixR x hx]
    _ = fixedPointSubgroup (↥R) (M ⧸ N) := by
          rw [fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
            (G := M) (A := ↥R) hsolvM hcopR (π := ∅) (H := N) inferInstance]

omit [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_card_factor
    {N : Subgroup M} [N.Normal] (hNinv : IsInvariant G M N)
    (hsolvM : Group.IsSolvable M) (hcopR : Nat.Coprime (Nat.card R) (Nat.card M)) :
    letI : MulDistribMulAction G (M ⧸ N) :=
      quotientMulDistribMulAction (A := G) (G := M) N hNinv
    Nat.card (fixedPointSubgroup (↥R) M) =
      Nat.card (fixedPointSubgroup (↥R) N) *
        Nat.card (fixedPointSubgroup (↥R) (M ⧸ N)) := by
  let : MulDistribMulAction G (M ⧸ N) :=
    quotientMulDistribMulAction (A := G) (G := M) N hNinv
  let : IsInvariant G M N := hNinv
  let : MulAction.QuotientAction G N := quotientAction_of_isInvariant (A := G) N hNinv
  let : IsInvariant (↥R) M N :=
    { invariant := fun a g => by
        change g ∈ N ↔ (a : G) • g ∈ N
        exact hNinv.invariant (a : G) g }
  let C : Subgroup M := fixedPointSubgroup (↥R) M
  let q : M →* M ⧸ N := QuotientGroup.mk' N
  have hCN_card : Nat.card (fixedPointSubgroup (↥R) N) = Nat.card (C.subgroupOf N) := by
    simpa [C] using
      congrArg (fun H : Subgroup N => Nat.card H)
        (fixedPointSubgroup_subtype_eq_local (A := ↥R) (G := M) N)
  have hNC_eq : N.subgroupOf C = (N ⊓ C).subgroupOf C := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hCN_eq : C.subgroupOf N = (C ⊓ N).subgroupOf N := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hNC_card : Nat.card (N.subgroupOf C) = Nat.card (C.subgroupOf N) := by
    rw [hNC_eq, hCN_eq,
      natCard_subgroupOf_eq (N ⊓ C) C inf_le_right,
      natCard_subgroupOf_eq (C ⊓ N) N inf_le_right,
      inf_comm]
  have hCQ_card : Nat.card (fixedPointSubgroup (↥R) (M ⧸ N)) = Nat.card (C.map q) := by
    change Nat.card (fixedPointSubgroup (↥R) (M ⧸ N)) =
      Nat.card ((fixedPointSubgroup (↥R) M).map (QuotientGroup.mk' N))
    exact congrArg (fun H : Subgroup (M ⧸ N) => Nat.card H)
      (fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := M) (A := ↥R) hsolvM hcopR (π := ∅) (H := N) inferInstance)
  have hcard_mul : Nat.card C = Nat.card (C.map q) * Nat.card (N.subgroupOf C) := by
    calc
      Nat.card C = Nat.card (C ⧸ N.subgroupOf C) * Nat.card (N.subgroupOf C) := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := C) (s := N.subgroupOf C))
      _ = Nat.card (C.map q) * Nat.card (N.subgroupOf C) := by
        rw [natCard_map_mk'_eq C N]
  calc
    Nat.card (fixedPointSubgroup (↥R) M) = Nat.card C := rfl
    _ = Nat.card (C.map q) * Nat.card (N.subgroupOf C) := hcard_mul
    _ = Nat.card (fixedPointSubgroup (↥R) (M ⧸ N)) * Nat.card (fixedPointSubgroup (↥R) N) := by
      rw [← hCQ_card, hNC_card, hCN_card]
    _ = Nat.card (fixedPointSubgroup (↥R) N) *
        Nat.card (fixedPointSubgroup (↥R) (M ⧸ N)) := by
          rw [Nat.mul_comm]

omit [Nontrivial M] in
public theorem CFSG.fixedPointSubgroup_card_eq_mul_quotient_of_solvable_coprime
    {N : Subgroup M} [N.Normal] (hNinv : IsInvariant G M N)
    (hsolvM : Group.IsSolvable M) (hcopR : Nat.Coprime (Nat.card R) (Nat.card M)) :
    letI : MulDistribMulAction G (M ⧸ N) :=
      quotientMulDistribMulAction (A := G) (G := M) N hNinv
    Nat.card (fixedPointSubgroup (↥R) M) =
      Nat.card (fixedPointSubgroup (↥R) N) *
        Nat.card (fixedPointSubgroup (↥R) (M ⧸ N)) :=
  theorem_3_10_fixedPointSubgroup_card_factor
    (G := G) (M := M) (R := R) (N := N) hNinv hsolvM hcopR

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_invariant_of_normal
    {A : Subgroup G} [A.Normal] :
    IsInvariant G M (fixedPointSubgroup (↥A) M) := by
  refine ⟨?_⟩
  intro g x
  constructor
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro a
    have hxfix :
        ((⟨g⁻¹ * (a : G) * g, by
          simpa using (inferInstance : A.Normal).conj_mem (a : G) a.2 g⁻¹⟩ : A) : G) • x = x :=
      hx ⟨g⁻¹ * (a : G) * g, by
        simpa using (inferInstance : A.Normal).conj_mem (a : G) a.2 g⁻¹⟩
    calc
      (a : G) • (g • x) = g • (((g⁻¹ * (a : G) * g) : G) • x) := by
        simp [mul_smul, mul_assoc]
      _ = g • x := by rw [hxfix]
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro a
    have hxfix :
        ((⟨g * (a : G) * g⁻¹, by
          exact (inferInstance : A.Normal).conj_mem (a : G) a.2 g⟩ : A) : G) • (g • x) = g • x :=
      hx ⟨g * (a : G) * g⁻¹, by
        exact (inferInstance : A.Normal).conj_mem (a : G) a.2 g⟩
    calc
      (a : G) • x = g⁻¹ • (((g * (a : G) * g⁻¹) : G) • (g • x)) := by
        simp [mul_smul, mul_assoc]
      _ = g⁻¹ • (g • x) := by rw [hxfix]
      _ = x := by simp

omit [Finite G] [Finite M] in
private noncomputable abbrev CFSG.theorem_3_10_quotientMulDistribMulActionOfTrivial
    {N : Subgroup G} [N.Normal]
    (hNfix : N ≤ actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G)) :
    MulDistribMulAction (G ⧸ N) M := by
  let φ : G →* MulAut M := MulDistribMulAction.toMulAut G M
  have hNker : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext m
    have hfixn : n ∈ fixingSubgroupOf G M (Set.univ : Set M) := (hNfix hn).2
    exact
      (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set M))).1 hfixn m (by trivial)
  let φq : G ⧸ N →* MulAut M :=
    (QuotientGroup.mk' N).liftOfSurjective (QuotientGroup.mk'_surjective (N := N)) ⟨φ, by
      simpa [QuotientGroup.ker_mk'] using hNker⟩
  exact
    { smul := fun q m => φq q m
      one_smul := by
        intro m
        change (φq 1) m = m
        simp [φq]
      mul_smul := by
        intro a b m
        change (φq (a * b)) m = (φq a) ((φq b) m)
        simp [φq]
      smul_mul := by
        intro a m₁ m₂
        exact (φq a).map_mul m₁ m₂
      smul_one := by
        intro a
        exact (φq a).map_one }

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_quotientMulDistribMulActionOfTrivial_smul_mk'
    {N : Subgroup G} [N.Normal]
    (hNfix : N ≤ actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G))
    (g : G) (m : M) :
    let :
        MulDistribMulAction (G ⧸ N) M :=
      theorem_3_10_quotientMulDistribMulActionOfTrivial (G := G) (M := M) hNfix
    (QuotientGroup.mk' N g : G ⧸ N) • m = g • m := by
  let φ : G →* MulAut M := MulDistribMulAction.toMulAut G M
  have hNker : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext x
    have hfixn : n ∈ fixingSubgroupOf G M (Set.univ : Set M) := (hNfix hn).2
    exact
      (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set M))).1 hfixn x (by trivial)
  let φq : G ⧸ N →* MulAut M :=
    (QuotientGroup.mk' N).liftOfSurjective (QuotientGroup.mk'_surjective (N := N)) ⟨φ, by
      simpa [QuotientGroup.ker_mk'] using hNker⟩
  have hcomp : φq.comp (QuotientGroup.mk' N) = φ := by
    have hNker' : (QuotientGroup.mk' N).ker ≤ φ.ker := by
      simpa [QuotientGroup.ker_mk'] using hNker
    exact congrArg Subtype.val
      (((QuotientGroup.mk' N).liftOfSurjective
        (QuotientGroup.mk'_surjective (N := N))).left_inv ⟨φ, hNker'⟩)
  change φq (QuotientGroup.mk' N g) m = φ g m
  have hqg : φq (QuotientGroup.mk' N g) = φ g := by
    exact congrArg (fun f : G →* MulAut M => f g) hcomp
  simpa [φ] using congrArg (fun f : MulAut M => f m) hqg

omit [Finite G] [Finite M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_fixedPointSubgroup_map_mk'_eq_of_trivial
    {N A : Subgroup G} [N.Normal]
    (hNfix : N ≤ actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G)) :
    let :
        MulDistribMulAction (G ⧸ N) M :=
      theorem_3_10_quotientMulDistribMulActionOfTrivial (G := G) (M := M) hNfix
    fixedPointSubgroup (↥(A.map (QuotientGroup.mk' N))) M = fixedPointSubgroup (↥A) M := by
  let :
      MulDistribMulAction (G ⧸ N) M :=
    theorem_3_10_quotientMulDistribMulActionOfTrivial (G := G) (M := M) hNfix
  ext m
  constructor
  · intro hm
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hm ⊢
    intro a
    have hmq :
        (⟨QuotientGroup.mk' N (a : G), ⟨(a : G), a.2, rfl⟩⟩ : A.map (QuotientGroup.mk' N)) • m = m :=
      hm ⟨QuotientGroup.mk' N (a : G), ⟨(a : G), a.2, rfl⟩⟩
    calc
      (a : G) • m = (⟨QuotientGroup.mk' N (a : G), ⟨(a : G), a.2, rfl⟩⟩ :
          A.map (QuotientGroup.mk' N)) • m := by
            simpa using
              (theorem_3_10_quotientMulDistribMulActionOfTrivial_smul_mk'
                (G := G) (M := M) hNfix (g := (a : G)) (m := m)).symm
      _ = m := hmq
  · intro hm
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hm ⊢
    intro aq
    rcases Subgroup.mem_map.mp aq.2 with ⟨a, haA, haq⟩
    have hma : (a : G) • m = m := hm ⟨a, haA⟩
    calc
      aq • m = (a : G) • m := by
        change (aq : G ⧸ N) • m = (a : G) • m
        rw [← haq]
        exact theorem_3_10_quotientMulDistribMulActionOfTrivial_smul_mk'
          (G := G) (M := M) hNfix (g := a) (m := m)
      _ = m := hma


private noncomputable def CFSG.theorem_3_10_endFieldRepFixedSubspaceEquiv
    {F : Type*} [Field F] [Finite F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [Representation.IsIrreducible ρ]
    (A : Subgroup G) :
    ↥(@Representation.fixedSubspace
      (Module.End (MonoidAlgebra F G) ρ.asModule)
      G
      ρ.asModule
      (endField_field ρ)
      inferInstance
      inferInstance
      (endFieldModule ρ)
      (endFieldRep ρ)
      A) ≃ ↥(ρ.fixedSubspace A) := by
  let := endField_field ρ
  let := endFieldModule ρ
  let ρK := endFieldRep ρ
  refine
    { toFun := fun x => ⟨ρ.asModuleEquiv x.1, by
          have hx := x.2
          change x.1 ∈ @Representation.fixedSubspace
            (Module.End (MonoidAlgebra F G) ρ.asModule)
            G
            ρ.asModule
            (endField_field ρ)
            inferInstance
            inferInstance
            (endFieldModule ρ)
            (endFieldRep ρ)
            A at hx
          change ∀ a : A, (ρK.comp A.subtype) a x.1 = x.1 at hx
          change ∀ a : A, (ρ.comp A.subtype) a (ρ.asModuleEquiv x.1) = ρ.asModuleEquiv x.1
          intro a
          calc
            ρ (a : G) (ρ.asModuleEquiv x.1) =
                ρ.asModuleEquiv ((endFieldRep ρ) (a : G) x.1) :=
              (endFieldRep_apply' ρ (a : G) x.1).symm
            _ = ρ.asModuleEquiv x.1 := congrArg ρ.asModuleEquiv (hx a)⟩
      invFun := fun x => ⟨ρ.asModuleEquiv.symm x.1, by
          change ∀ a : A, (ρK.comp A.subtype) a (ρ.asModuleEquiv.symm x.1) =
            ρ.asModuleEquiv.symm x.1
          intro a
          apply ρ.asModuleEquiv.injective
          calc
            ρ.asModuleEquiv ((endFieldRep ρ) (a : G) (ρ.asModuleEquiv.symm x.1)) =
                ρ (a : G) x.1 := by
              rw [endFieldRep_apply', ρ.asModuleEquiv.apply_symm_apply]
            _ = x.1 := x.2 a
            _ = ρ.asModuleEquiv (ρ.asModuleEquiv.symm x.1) :=
              (ρ.asModuleEquiv.apply_symm_apply x.1).symm⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }

private theorem CFSG.theorem_3_10_endFieldRep_ker_le
    {F : Type*} [Field F] [Finite F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [Representation.IsIrreducible ρ] :
    let := endFieldModule ρ
    (endFieldRep ρ).ker ≤ ρ.ker := by
  let := endFieldModule ρ
  change ∀ g, g ∈ (endFieldRep ρ).ker → g ∈ ρ.ker
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  ext v
  let m : ρ.asModule := ρ.asModuleEquiv.symm v
  have hgm : ((endFieldRep ρ) g) m = m := by
    exact DFunLike.congr_fun hg m
  calc
    ρ g v = ρ.asModuleEquiv (((endFieldRep ρ) g) m) := by
      rw [endFieldRep_apply']
      simp [m]
    _ = ρ.asModuleEquiv m := congrArg ρ.asModuleEquiv hgm
    _ = v := by simp [m]

private noncomputable def CFSG.theorem_3_10_scalarValFinrankOne
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hfin : Module.finrank F V = 1) (f : Module.End F V) : F :=
  Classical.choose
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one (R := F) (M := V) hfin f)

private theorem CFSG.theorem_3_10_scalarValFinrankOne_spec
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hfin : Module.finrank F V = 1) (f : Module.End F V) :
    f = theorem_3_10_scalarValFinrankOne hfin f • (1 : Module.End F V) :=
  (Classical.choose_spec
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one (R := F) (M := V) hfin f)).1

private theorem CFSG.theorem_3_10_scalarValFinrankOne_eq
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hfin : Module.finrank F V = 1) (f : Module.End F V) {a : F}
    (ha : f = a • (1 : Module.End F V)) :
    theorem_3_10_scalarValFinrankOne hfin f = a :=
  ((Classical.choose_spec
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one (R := F) (M := V) hfin f)).2 a ha).symm

private noncomputable def CFSG.theorem_3_10_scalarHomFinrankOne
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hfin : Module.finrank F V = 1) : G →* F where
  toFun g := theorem_3_10_scalarValFinrankOne hfin (ρ g)
  map_one' := by
    exact theorem_3_10_scalarValFinrankOne_eq (hfin := hfin) (f := ρ 1) <| by
      simp
  map_mul' g h := by
    have hg' := theorem_3_10_scalarValFinrankOne_spec (hfin := hfin) (f := ρ g)
    have hh' := theorem_3_10_scalarValFinrankOne_spec (hfin := hfin) (f := ρ h)
    have hmul :
        ρ (g * h) =
          (theorem_3_10_scalarValFinrankOne hfin (ρ g) *
              theorem_3_10_scalarValFinrankOne hfin (ρ h)) •
            (1 : Module.End F V) := by
      calc
        ρ (g * h) = ρ g * ρ h := by simp
        _ =
            (theorem_3_10_scalarValFinrankOne hfin (ρ g) • (1 : Module.End F V)) *
              (theorem_3_10_scalarValFinrankOne hfin (ρ h) • (1 : Module.End F V)) := by
                conv_lhs =>
                  rw [hg', hh']
        _ =
            (theorem_3_10_scalarValFinrankOne hfin (ρ g) *
                theorem_3_10_scalarValFinrankOne hfin (ρ h)) •
              (1 : Module.End F V) := by
                ext v
                simp [smul_smul, mul_comm]
    exact theorem_3_10_scalarValFinrankOne_eq (hfin := hfin) (f := ρ (g * h)) hmul

private theorem CFSG.theorem_3_10_scalarHomFinrankOne_spec
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hfin : Module.finrank F V = 1) (g : G) :
    ρ g =
      theorem_3_10_scalarHomFinrankOne ρ hfin g • (1 : Module.End F V) :=
  by
    show ρ g = theorem_3_10_scalarValFinrankOne hfin (ρ g) • (1 : Module.End F V)
    exact theorem_3_10_scalarValFinrankOne_spec (hfin := hfin) (f := ρ g)

private theorem CFSG.theorem_3_10_scalarHomFinrankOne_apply
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hfin : Module.finrank F V = 1) (g : G) (v : V) :
    ρ g v = theorem_3_10_scalarHomFinrankOne ρ hfin g • v := by
  simpa using
    congrArg (fun f : Module.End F V => f v)
      (theorem_3_10_scalarHomFinrankOne_spec (ρ := ρ) hfin g)

private theorem CFSG.theorem_3_10_scalarHomFinrankOne_ker_eq
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hfin : Module.finrank F V = 1) :
    (theorem_3_10_scalarHomFinrankOne ρ hfin).ker = ρ.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    calc
      ρ g = theorem_3_10_scalarHomFinrankOne ρ hfin g • (1 : Module.End F V) :=
        theorem_3_10_scalarHomFinrankOne_spec (ρ := ρ) hfin g
      _ = 1 := by simp [hg]
  · intro hg
    show theorem_3_10_scalarValFinrankOne hfin (ρ g) = 1
    apply theorem_3_10_scalarValFinrankOne_eq (hfin := hfin) (f := ρ g)
    simp [hg]

private theorem CFSG.theorem_3_10_scalarHomFinrankOne_eq_of_conj_equiv
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (ρ : Representation F H V) (hfin : Module.finrank F V = 1) {x : G}
    (e : ρ ≃ₗ Theory.Representation.conjugateRep ρ x) (h : H) :
    theorem_3_10_scalarHomFinrankOne ρ hfin
        ⟨x * (h : G) * x⁻¹, Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 x⟩ =
      theorem_3_10_scalarHomFinrankOne ρ hfin h := by
  classical
  obtain ⟨v, hv_ne⟩ := exists_ne (0 : V)
  have hev_ne : e v ≠ 0 := by
    intro hev
    apply hv_ne
    calc
      v = e.symm (e v) := by simp
      _ = e.symm 0 := by rw [hev]
      _ = 0 := e.symm.toLinearEquiv.map_zero
  have hintertwine := e.isIntertwining h v
  have hscalar :
      theorem_3_10_scalarHomFinrankOne ρ hfin h • e v =
        theorem_3_10_scalarHomFinrankOne ρ hfin
          ⟨x * (h : G) * x⁻¹, Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 x⟩ • e v := by
    calc
      theorem_3_10_scalarHomFinrankOne ρ hfin h • e v
          = e (theorem_3_10_scalarHomFinrankOne ρ hfin h • v) := by
              exact (e.toLinearEquiv.map_smul
                (theorem_3_10_scalarHomFinrankOne ρ hfin h) v).symm
      _ = e (ρ h v) := by
              rw [theorem_3_10_scalarHomFinrankOne_apply (ρ := ρ) hfin h v]
      _ = (Theory.Representation.conjugateRep ρ x) h (e v) := hintertwine
      _ =
          theorem_3_10_scalarHomFinrankOne ρ hfin
            ⟨x * (h : G) * x⁻¹, Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 x⟩ • e v := by
              rw [Theory.Representation.conjugateRep_apply]
              exact theorem_3_10_scalarHomFinrankOne_apply
                (ρ := ρ) hfin
                ⟨x * (h : G) * x⁻¹,
                  Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 x⟩ (e v)
  have hzero :
      (theorem_3_10_scalarHomFinrankOne ρ hfin h -
        theorem_3_10_scalarHomFinrankOne ρ hfin
          ⟨x * (h : G) * x⁻¹, Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 x⟩) • e v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hscalar
  have hsub :
      theorem_3_10_scalarHomFinrankOne ρ hfin h -
        theorem_3_10_scalarHomFinrankOne ρ hfin
          ⟨x * (h : G) * x⁻¹, Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 x⟩ = 0 :=
    (smul_eq_zero.mp hzero).resolve_right hev_ne
  exact (sub_eq_zero.mp hsub).symm

private theorem CFSG.theorem_3_10_commutes_of_conj_commutator_eq
    {G : Type*} [Group G] {K : Subgroup G} [IsMulCommutative K]
    (x : G) (a b : K)
    (h : x * (a : G) * x⁻¹ * (a : G)⁻¹ =
      x * (b : G) * x⁻¹ * (b : G)⁻¹) :
    (b : G)⁻¹ * (a : G) * x = x * ((b : G)⁻¹ * (a : G)) := by
  have h1 : (a : G) * x⁻¹ * (a : G)⁻¹ * (b : G) = (b : G) * x⁻¹ := by
    calc
      (a : G) * x⁻¹ * (a : G)⁻¹ * (b : G)
          = x⁻¹ * (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (b : G) := by group
      _ = x⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (b : G) := by rw [h]
      _ = (b : G) * x⁻¹ := by group
  have h2 : x⁻¹ * ((a : G)⁻¹ * (b : G)) = ((a : G)⁻¹ * (b : G)) * x⁻¹ := by
    calc
      x⁻¹ * ((a : G)⁻¹ * (b : G)) =
          (a : G)⁻¹ * ((a : G) * x⁻¹ * (a : G)⁻¹ * (b : G)) := by group
      _ = (a : G)⁻¹ * ((b : G) * x⁻¹) := by rw [h1]
      _ = ((a : G)⁻¹ * (b : G)) * x⁻¹ := by group
  have h2inv := congrArg Inv.inv h2
  simpa [mul_assoc] using h2inv

private theorem CFSG.theorem_3_10_conj_commutator_mem
    {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (x : G) (a : K) :
    x * (a : G) * x⁻¹ * (a : G)⁻¹ ∈ K :=
  K.mul_mem ((inferInstance : K.Normal).conj_mem (a : G) a.2 x) (K.inv_mem a.2)

private theorem CFSG.theorem_3_10_conj_commutator_surjective
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal] [IsMulCommutative K]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) {x : G}
    (hxq : (x : G ⧸ K) ≠ 1) :
    Function.Surjective fun a : K =>
      (⟨x * (a : G) * x⁻¹ * (a : G)⁻¹,
        theorem_3_10_conj_commutator_mem (K := K) x a⟩ : K) := by
  classical
  let f : K → K := fun a =>
    ⟨x * (a : G) * x⁻¹ * (a : G)⁻¹,
      theorem_3_10_conj_commutator_mem (K := K) x a⟩
  have hreg : ActsRegularly (↥R) (↥K) :=
    theorem_3_10_regular_conj_action (G := G) (K := K) (R := R) hfrob
  have hx_mem_top : x ∈ (⊤ : Subgroup G) := by simp
  rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := K) (t := R)).1
      (by simp [hfrob.isComplement'.sup_eq_top]) with
    ⟨k₀, hk₀K, r, hrR, hxr⟩
  let k₀K : K := ⟨k₀, hk₀K⟩
  let rR : R := ⟨r, hrR⟩
  have hr_ne : rR ≠ 1 := by
    intro hr1
    apply hxq
    have hxK : x ∈ K := by
      rw [← hxr]
      have hr_eq : r = 1 := by simpa [rR] using congrArg Subtype.val hr1
      simp [hr_eq, hk₀K]
    simpa [QuotientGroup.eq_one_iff] using hxK
  have hf_inj : Function.Injective f := by
    intro a b hab
    have habG :
        x * (a : G) * x⁻¹ * (a : G)⁻¹ =
          x * (b : G) * x⁻¹ * (b : G)⁻¹ := congrArg Subtype.val hab
    let c : K := b⁻¹ * a
    have hc_x : (c : G) * x = x * (c : G) := by
      simpa [c] using theorem_3_10_commutes_of_conj_commutator_eq
        (K := K) x a b habG
    have hc_r : (c : G) * (rR : G) = (rR : G) * (c : G) := by
      have hc_x' : (c : G) * ((k₀K : G) * (rR : G)) =
          ((k₀K : G) * (rR : G)) * (c : G) := by
        simpa [k₀K, rR, ← hxr] using hc_x
      have hck : (c : G) * (k₀K : G) = (k₀K : G) * (c : G) := by
        exact congrArg Subtype.val (mul_comm c k₀K)
      apply mul_left_cancel (a := (k₀K : G))
      calc
        (k₀K : G) * ((c : G) * (rR : G))
            = ((k₀K : G) * (c : G)) * (rR : G) := by group
        _ = ((c : G) * (k₀K : G)) * (rR : G) := by rw [← hck]
        _ = (c : G) * ((k₀K : G) * (rR : G)) := by group
        _ = ((k₀K : G) * (rR : G)) * (c : G) := hc_x'
        _ = (k₀K : G) * ((rR : G) * (c : G)) := by group
    have hc_r_smul : rR • c = c := by
      ext
      have hconj : (rR : G) * (c : G) * (rR : G)⁻¹ = (c : G) := by
        calc
          (rR : G) * (c : G) * (rR : G)⁻¹
              = (c : G) * (rR : G) * (rR : G)⁻¹ := by rw [← hc_r]
          _ = (c : G) := by group
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        Subgroup.le_normalizer_of_normal (H := K)] using hconj
    have hc_fix : c ∈ fixedPointSubgroup (↥(Subgroup.zpowers rR)) K := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro y
      exact smul_eq_self_of_mem_zpowers y.2 hc_r_smul
    have hc_bot : c ∈ (⊥ : Subgroup K) := by
      simpa [hreg rR hr_ne] using hc_fix
    have hc_one : c = 1 := by
      simpa using (Subgroup.mem_bot.mp hc_bot)
    have hba : (b : G)⁻¹ * (a : G) = 1 := by simpa [c] using congrArg Subtype.val hc_one
    exact Subtype.ext (inv_mul_eq_one.mp hba).symm
  simpa [f] using Finite.surjective_of_injective hf_inj

private noncomputable def CFSG.theorem_3_10_fixedSubrepresentation_of_normal
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal] :
    Subrepresentation ρ where
  toSubmodule := ρ.fixedSubspace H
  apply_mem_toSubmodule := by
    intro g v hv
    change ∀ h : H, ρ h (ρ g v) = ρ g v
    intro h
    have hh' : (g : G)⁻¹ * h * g ∈ H := by
      simpa using Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 ((g : G)⁻¹)
    let h' : H := ⟨(g : G)⁻¹ * h * g, hh'⟩
    have hvh' : ρ h' v = v := hv h'
    calc
      ρ h (ρ g v) = ((ρ h) * (ρ g)) v := rfl
      _ = ρ ((h : G) * g) v := by rw [← ρ.map_mul]
      _ = ρ (g * (h' : H)) v := by
            congr 1
            simp [h', mul_assoc]
      _ = ((ρ g) * (ρ h')) v := by rw [ρ.map_mul]
      _ = ρ g (ρ h' v) := rfl
      _ = ρ g v := by rw [hvh']

private theorem CFSG.theorem_3_10_toSubmodule_bot
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (rho : Representation F G V) :
    (⊥ : Subrepresentation rho).toSubmodule = ⊥ := by
  apply le_antisymm
  · intro x hx
    let Z : Subrepresentation rho :=
      { toSubmodule := ⊥
        apply_mem_toSubmodule := by simp }
    have hxZ : x ∈ Z := (show (⊥ : Subrepresentation rho) ≤ Z from bot_le) hx
    exact hxZ
  · exact bot_le

private theorem CFSG.theorem_3_10_toSubmodule_top
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (rho : Representation F G V) :
    (⊤ : Subrepresentation rho).toSubmodule = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x _hx
    let T : Subrepresentation rho :=
      { toSubmodule := ⊤
        apply_mem_toSubmodule := by simp }
    have hxT : x ∈ T := by
      change x ∈ (⊤ : Submodule F V)
      exact Submodule.mem_top
    exact (show T ≤ (⊤ : Subrepresentation rho) from le_top) hxT

private theorem CFSG.theorem_3_10_le_ker_of_normal_fixedSubspace_ne_bot
    {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal] [Representation.IsIrreducible ρ]
    (hfix : ρ.fixedSubspace H ≠ ⊥) :
    H ≤ ρ.ker := by
  let S : Subrepresentation ρ := theorem_3_10_fixedSubrepresentation_of_normal ρ H
  have hS_ne : S ≠ ⊥ := by
    intro hS
    apply hfix
    have hsub := congrArg Subrepresentation.toSubmodule hS
    change ρ.fixedSubspace H = (⊥ : Subrepresentation ρ).toSubmodule at hsub
    calc
      ρ.fixedSubspace H = (⊥ : Subrepresentation ρ).toSubmodule := hsub
      _ = ⊥ := theorem_3_10_toSubmodule_bot ρ
  have hS_top : S = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top S with hbot | htop
    · exact False.elim (hS_ne hbot)
    · exact htop
  have htop_sub : ρ.fixedSubspace H = ⊤ := by
    have hsub := congrArg Subrepresentation.toSubmodule hS_top
    change ρ.fixedSubspace H = (⊤ : Subrepresentation ρ).toSubmodule at hsub
    calc
      ρ.fixedSubspace H = (⊤ : Subrepresentation ρ).toSubmodule := hsub
      _ = ⊤ := theorem_3_10_toSubmodule_top ρ
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  have hv : v ∈ ρ.fixedSubspace H := by simp [htop_sub]
  exact hv ⟨h, hh⟩

private theorem CFSG.theorem_3_10_le_ker_of_extendScalars
    {G : Type*} [Group G] {F : Type*} [Field F] {F' : Type*} [Field F']
    [Algebra F F'] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) {H : Subgroup G}
    (hH : H ≤ (Theory.Representation.extendScalars F' ρ).ker) :
    H ≤ ρ.ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  have hh' : h ∈ (Theory.Representation.extendScalars F' ρ).ker := hH hh
  have hfix :
      Theory.Representation.extendScalars F' ρ h (1 ⊗ₜ[F] v) = (1 : F') ⊗ₜ[F] v := by
    simpa using
      DFunLike.congr_fun (show Theory.Representation.extendScalars F' ρ h = 1 by simpa using hh')
        ((1 : F') ⊗ₜ[F] v)
  have hfix' : (1 : F') ⊗ₜ[F] (ρ h v) = (1 : F') ⊗ₜ[F] v := by
    simpa [Theory.Representation.extendScalars_apply] using hfix
  exact (Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := F') V) hfix'

private noncomputable def CFSG.theorem_3_10_fixedSubspace_equiv_of_equiv
    {G : Type*} [Group G] {F : Type*} [Field F] {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : ρ ≃ₗ σ) (R : Subgroup G) :
    ρ.fixedSubspace R ≃ₗ[F] σ.fixedSubspace R := by
  refine
    { toFun := fun v => ⟨e v, ?_⟩
      invFun := fun w => ⟨e.symm w, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := by
        intro v w
        ext1
        exact e.map_add v w
      map_smul' := by
        intro a v
        ext1
        exact e.map_smul a v }
  · change ∀ r : R, σ r (e v) = e v
    intro r
    simpa using (e.isIntertwining r v).symm.trans (congrArg e (v.2 r))
  · change ∀ r : R, ρ r (e.symm w) = e.symm w
    intro r
    simpa using (e.symm.isIntertwining r w).symm.trans (congrArg e.symm (w.2 r))
  · intro v
    ext1
    simp
  · intro w
    ext1
    simp


private theorem CFSG.theorem_3_10_invariants_extendScalars_eq_baseChange
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {L : Type*} [Field L] [Algebra F L] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hF : (Nat.card G : F) ≠ 0) (hL : (Nat.card G : L) ≠ 0) :
    Representation.invariants (Theory.Representation.extendScalars L ρ) =
      (Representation.invariants ρ).baseChange L := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : F) := by
    simpa [Nat.card_eq_fintype_card] using invertibleOfNonzero hF
  let : Invertible (Fintype.card G : L) := by
    simpa [Nat.card_eq_fintype_card] using invertibleOfNonzero hL
  let S : Submodule F V := Representation.invariants ρ
  let Sext : Submodule L (L ⊗[F] V) :=
    Representation.invariants (Theory.Representation.extendScalars L ρ)
  let avg : V →ₗ[F] V := Representation.averageMap ρ
  let avgS : V →ₗ[F] ↥S :=
    avg.codRestrict S (Representation.averageMap_invariant (ρ := ρ))
  let avgExt : L ⊗[F] V →ₗ[L] L ⊗[F] V :=
    Representation.averageMap (Theory.Representation.extendScalars L ρ)
  let avgSext : L ⊗[F] V →ₗ[L] ↥Sext :=
    avgExt.codRestrict Sext
      (Representation.averageMap_invariant (ρ := Theory.Representation.extendScalars L ρ))
  have havg_eq : avgExt = LinearMap.baseChange L avg := by
    ext a
    simp [avgExt, avg, Representation.averageMap, GroupAlgebra.average,
      Theory.Representation.extendScalars_apply, map_sum, TensorProduct.AlgebraTensorModule.curry_apply]
    rw [Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul']
    rw [TensorProduct.tmul_sum]
    simp [Algebra.smul_def]
  have havgS_subtype : S.subtype.comp avgS = avg := by
    ext v
    rfl
  have havgS_proj_apply (v : S) : avgS (S.subtype v) = v := by
    apply Subtype.ext
    change avg (S.subtype v) = S.subtype v
    exact Representation.averageMap_id (ρ := ρ) v v.2
  have havgSext_subtype : Sext.subtype.comp avgSext = avgExt := by
    ext v
    rfl
  have havgSext_proj_apply (v : Sext) : avgSext (Sext.subtype v) = v := by
    apply Subtype.ext
    change avgExt (Sext.subtype v) = Sext.subtype v
    exact Representation.averageMap_id (ρ := Theory.Representation.extendScalars L ρ) v v.2
  have hrange_avg : LinearMap.range avg = S := by
    rw [← havgS_subtype, LinearMap.range_comp]
    rw [LinearMap.range_eq_of_proj havgS_proj_apply, Submodule.map_top, Submodule.range_subtype]
  have hrange_avgExt : LinearMap.range avgExt = Sext := by
    rw [← havgSext_subtype, LinearMap.range_comp]
    rw [LinearMap.range_eq_of_proj havgSext_proj_apply, Submodule.map_top,
      Submodule.range_subtype]
  have hbc_comp :
      (LinearMap.baseChange L S.subtype).comp (LinearMap.baseChange L avgS) =
        LinearMap.baseChange L avg := by
    rw [← LinearMap.baseChange_comp, havgS_subtype]
  have hbc_proj_eq :
      (LinearMap.baseChange L avgS).comp (LinearMap.baseChange L S.subtype) =
        LinearMap.id := by
    ext c
    exact congrArg (fun x => (1 : L) ⊗ₜ[F] x) (havgS_proj_apply c)
  have hbc_surj : Function.Surjective (LinearMap.baseChange L avgS) := by
    intro a
    refine ⟨(LinearMap.baseChange L S.subtype) a, ?_⟩
    simpa using DFunLike.congr_fun hbc_proj_eq a
  have hrange_avg_bc :
      LinearMap.range (LinearMap.baseChange L avg) = S.baseChange L := by
    rw [← hbc_comp, LinearMap.range_comp]
    rw [LinearMap.range_eq_top.2 hbc_surj, Submodule.map_top, Submodule.baseChange]
  calc
    Sext = LinearMap.range avgExt := hrange_avgExt.symm
    _ = LinearMap.range (LinearMap.baseChange L avg) := by rw [havg_eq]
    _ = S.baseChange L := hrange_avg_bc

private theorem CFSG.theorem_3_10_fixedSubspace_extendScalars_eq_baseChange
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {L : Type*} [Field L] [Algebra F L] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G)
    (hF : (Nat.card H : F) ≠ 0) (hL : (Nat.card H : L) ≠ 0) :
    (Theory.Representation.extendScalars L ρ).fixedSubspace H =
      (ρ.fixedSubspace H).baseChange L := by
  dsimp [Representation.fixedSubspace]
  have hrep :
      (Theory.Representation.extendScalars L ρ).comp H.subtype =
        Theory.Representation.extendScalars L (ρ.comp H.subtype) := by
    ext h
    rfl
  rw [hrep]
  exact theorem_3_10_invariants_extendScalars_eq_baseChange
    (ρ := ρ.comp H.subtype) hF hL

private theorem CFSG.theorem_3_10_noNontrivialConj_of_faithful
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal]
    [IsMulCommutative K] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F G V) [Representation.IsIrreducible ρ]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hK_not_le_ker : ¬ K ≤ ρ.ker)
    (W : Subrepresentation (ρ.comp K.subtype)) [Representation.IsIrreducible W.toRepresentation] :
    ∀ x : G, (x : G ⧸ K) ≠ 1 →
      ¬ Nonempty (W.toRepresentation ≃ₗ Theory.Representation.conjugateRep W.toRepresentation x) := by
  classical
  let : FiniteDimensional F W.toSubmodule :=
    FiniteDimensional.of_injective W.toSubmodule.subtype Subtype.val_injective
  let : Nontrivial W.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial W.toRepresentation
  have hWfin : Module.finrank F W.toSubmodule = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      (ρ := W.toRepresentation)
  intro x hxq hnon
  let e : W.toRepresentation ≃ₗ Theory.Representation.conjugateRep W.toRepresentation x :=
    Classical.choice hnon
  let χ := theorem_3_10_scalarHomFinrankOne W.toRepresentation hWfin
  have hsurj := theorem_3_10_conj_commutator_surjective (G := G) (K := K) (R := R)
    hfrob (x := x) hxq
  have hWker : ∀ y : K, y ∈ W.toRepresentation.ker := by
    intro y
    rcases hsurj y with ⟨a, ha⟩
    rw [← ha]
    let c : K :=
      ⟨x * (a : G) * x⁻¹ * (a : G)⁻¹,
        theorem_3_10_conj_commutator_mem (K := K) x a⟩
    let xax : K :=
      ⟨x * (a : G) * x⁻¹,
        (inferInstance : K.Normal).conj_mem (a : G) a.2 x⟩
    have hχ_conj : χ xax = χ a :=
      theorem_3_10_scalarHomFinrankOne_eq_of_conj_equiv
        (ρ := W.toRepresentation) hWfin e a
    have hc_mul : c * a = xax := by
      ext
      simp [c, xax]
    have hχa_ne : χ a ≠ 0 := by
      have hmul : χ a * χ a⁻¹ = 1 := by
        simpa using (χ.map_mul a a⁻¹).symm
      exact left_ne_zero_of_mul_eq_one hmul
    have hχc : χ c = 1 := by
      have hmap := congrArg χ hc_mul
      rw [map_mul, hχ_conj] at hmap
      have hmap' : χ c * χ a = 1 * χ a := by simpa using hmap
      exact (mul_left_injective₀ hχa_ne) hmap'
    rw [← theorem_3_10_scalarHomFinrankOne_ker_eq (ρ := W.toRepresentation) hWfin]
    exact MonoidHom.mem_ker.mpr hχc
  have hfix_ne : ρ.fixedSubspace K ≠ ⊥ := by
    obtain ⟨w, hw_ne⟩ := exists_ne (0 : W.toSubmodule)
    have hw_mem : (w : V) ∈ ρ.fixedSubspace K := by
      change ∀ k : K, (ρ.comp K.subtype) k (w : V) = (w : V)
      intro k
      have hkw : W.toRepresentation k w = w := by
        have hk := hWker k
        exact DFunLike.congr_fun (show W.toRepresentation k = 1 by simpa [MonoidHom.mem_ker] using hk) w
      exact congrArg Subtype.val hkw
    intro hbot
    have hw_bot : (w : V) ∈ (⊥ : Submodule F V) := by
      simpa [hbot] using hw_mem
    exact hw_ne (Subtype.ext (by simpa using hw_bot))
  exact hK_not_le_ker (theorem_3_10_le_ker_of_normal_fixedSubspace_ne_bot (ρ := ρ) K hfix_ne)


private noncomputable def CFSG.theorem_3_10_coindMap
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] {W : Type*}
    [AddCommGroup W] [Module F W] (σ : Representation F G W)
    (ρ : Representation F H V) (π : σ.comp H.subtype →ₗ ρ) :
    σ →ₗ coindRep ρ := by
  refine Theory.Representation.RepMap.mk ?_ ?_
  · refine
      { toFun := fun w => ⟨fun g => π (σ g w), ?_⟩
        map_add' := by
          intro w1 w2
          apply Subtype.ext
          ext g
          simp
        map_smul' := by
          intro a w
          apply Subtype.ext
          ext g
          simp }
    intro h g
    have hinter := Representation.IntertwiningMap.isIntertwining
      (ρ := σ.comp H.subtype) (σ := ρ) π h (σ g w)
    calc
      π (σ ((h : G) * g) w) = π (σ (h : G) (σ g w)) := by
        rw [map_mul]
        rfl
      _ = ρ h (π (σ g w)) := hinter
  · intro g
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext x
    change π (σ x (σ g w)) = π (σ (x * g) w)
    rw [map_mul]
    rfl

private noncomputable def CFSG.theorem_3_10_coindMapOfSubrep
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (σ : Representation F G V)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (σ.comp H.subtype)) :
    σ →ₗ coindRep M.toRepresentation := by
  let σH : Representation F H V := σ.comp H.subtype
  have hσHcr : σH.IsCompletelyReducible := by
    exact Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (ρ := σH) hchar
  let : ComplementedLattice (Subrepresentation σH) := by
    exact
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
        (ρ := σH)).2 hσHcr
  let ψ : Subrepresentation σH := Classical.choose (exists_isCompl M)
  have hcompl : IsCompl M ψ := Classical.choose_spec (exists_isCompl M)
  have hcompl_sub : IsCompl M.toSubmodule ψ.toSubmodule := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      calc
        M.toSubmodule ⊓ ψ.toSubmodule =
            (⊥ : Subrepresentation σH).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
        _ = ⊥ := theorem_3_10_toSubmodule_bot σH
    · rw [codisjoint_iff]
      calc
        M.toSubmodule ⊔ ψ.toSubmodule =
            (⊤ : Subrepresentation σH).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
        _ = ⊤ := theorem_3_10_toSubmodule_top σH
  let proj : V →ₗ[F] M.toSubmodule :=
    Submodule.projectionOnto M.toSubmodule ψ.toSubmodule hcompl_sub
  have hproj_intertwining (h : H) :
      proj.comp (σH h) = (M.toRepresentation h).comp proj := by
    apply LinearMap.ext
    intro v
    rcases Submodule.existsUnique_add_of_isCompl hcompl_sub v with ⟨u, w, huw, huniq⟩
    have hu_mem : (σH h) u ∈ M.toSubmodule := M.apply_mem_toSubmodule h u.2
    have hw_mem : (σH h) w ∈ ψ.toSubmodule := ψ.apply_mem_toSubmodule h w.2
    let projψ : V →ₗ[F] ψ.toSubmodule :=
      Submodule.projectionOnto ψ.toSubmodule M.toSubmodule hcompl_sub.symm
    have hdecomp : (proj v : V) + (projψ v : V) = v := by
      simpa [proj, projψ] using
        Submodule.projection_add_projection_eq_self hcompl_sub v
    have hproj_v : proj v = u := by
      exact huniq (proj v) (projψ v) hdecomp |>.1
    have hproj_hu : proj ((σH h) u) = ⟨(σH h) u, hu_mem⟩ := by
      simpa [proj] using
        Submodule.projectionOnto_apply_left hcompl_sub ⟨(σH h) u, hu_mem⟩
    have hproj_hw : proj ((σH h) w) = 0 := by
      simpa [proj] using
        Submodule.projectionOnto_apply_right hcompl_sub ⟨(σH h) w, hw_mem⟩
    apply Subtype.ext
    calc
      (((proj.comp (σH h)) v : M.toSubmodule) : V) =
          ((proj ((σH h) u + (σH h) w) : M.toSubmodule) : V) := by
            rw [LinearMap.comp_apply, ← huw, map_add]
      _ = ((proj ((σH h) u) : M.toSubmodule) : V) + ((proj ((σH h) w) : M.toSubmodule) : V) := by
            simp [map_add]
      _ = (σH h) u + 0 := by
            rw [hproj_hu, hproj_hw]
            simp
      _ = (σH h) u := by simp
      _ = (σH h) (proj v) := by rw [congrArg Subtype.val hproj_v.symm]
      _ = (((M.toRepresentation h).comp proj v : M.toSubmodule) : V) := by rfl
  exact
    theorem_3_10_coindMap σ M.toRepresentation
      (Theory.Representation.RepMap.mk proj hproj_intertwining)

private theorem CFSG.theorem_3_10_coindMapOfSubrep_eval_one
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (σ : Representation F G V)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (σ.comp H.subtype)) (m : M.toSubmodule) :
    coindEval (ρ := M.toRepresentation) (1 : G)
      (theorem_3_10_coindMapOfSubrep σ hchar M m) = m := by
  classical
  unfold theorem_3_10_coindMapOfSubrep theorem_3_10_coindMap coindEval
  simp

private theorem CFSG.theorem_3_10_coind_apply_baseFunctionAt
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F H V)
    (g x : G) (v : V) :
    coindRep (ρ := ρ) x (coindBaseFunctionAt (ρ := ρ) g v) =
      coindBaseFunctionAt (ρ := ρ) (g * x⁻¹) v := by
  classical
  ext y
  change (coindBaseFunctionAt (ρ := ρ) g v).1 (y * x) =
    (coindBaseFunctionAt (ρ := ρ) (g * x⁻¹) v).1 y
  unfold coindBaseFunctionAt
  change (if hx : y * x * g⁻¹ ∈ H then ρ ⟨y * x * g⁻¹, hx⟩ v else 0) =
    (if hx : y * (g * x⁻¹)⁻¹ ∈ H then ρ ⟨y * (g * x⁻¹)⁻¹, hx⟩ v else 0)
  by_cases h1 : y * x * g⁻¹ ∈ H
  · by_cases h2 : y * (g * x⁻¹)⁻¹ ∈ H
    · simp [mul_assoc, mul_inv_rev]
    · exfalso
      exact h2 (by simpa [mul_assoc, mul_inv_rev] using h1)
  · by_cases h2 : y * (g * x⁻¹)⁻¹ ∈ H
    · exfalso
      exact h1 (by simpa [mul_assoc, mul_inv_rev] using h2)
    · simp [mul_assoc, mul_inv_rev]

private theorem CFSG.theorem_3_10_coind_sumBase_mem_fixedSubspace
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H R : Subgroup G}
    [H.Normal] [Fintype R] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (v : V) :
    (∑ r : R, coindBaseFunctionAt (ρ := ρ) (r : G) v) ∈
      (coindRep (ρ := ρ)).fixedSubspace R := by
  classical
  change ∀ r : R,
      coindRep (ρ := ρ) r (∑ s : R, coindBaseFunctionAt (ρ := ρ) (s : G) v) =
        ∑ s : R, coindBaseFunctionAt (ρ := ρ) (s : G) v
  intro r
  rw [map_sum]
  calc
    ∑ s : R, coindRep (ρ := ρ) r (coindBaseFunctionAt (ρ := ρ) (s : G) v) =
        ∑ s : R, coindBaseFunctionAt (ρ := ρ) ((s : G) * (r : G)⁻¹) v := by
          apply Fintype.sum_congr
          intro s
          simpa using
            theorem_3_10_coind_apply_baseFunctionAt (ρ := ρ) (g := (s : G)) (x := (r : G)) v
    _ = ∑ s : R, coindBaseFunctionAt (ρ := ρ) (s : G) v := by
          let e : R → R := fun s => s * r⁻¹
          have he : Function.Bijective e := Group.mulRight_bijective r⁻¹
          simpa [e] using
            (Fintype.sum_bijective e he
              (fun s : R => coindBaseFunctionAt (ρ := ρ) ((s : G) * (r : G)⁻¹) v)
              (fun s : R => coindBaseFunctionAt (ρ := ρ) (s : G) v)
              (fun s => rfl))

private theorem CFSG.theorem_3_10_coindEval_surjective_fixedSubspace
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H R : Subgroup G}
    [H.Normal] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (hHR : H.IsComplement' R) :
    Function.Surjective
      ((coindEval (ρ := ρ) (1 : G)).toLinearMap.comp
        ((coindRep (ρ := ρ)).fixedSubspace R).subtype) := by
  classical
  let : Fintype R := Fintype.ofFinite R
  intro v
  refine ⟨⟨∑ r : R, coindBaseFunctionAt (ρ := ρ) (r : G) v, ?_⟩, ?_⟩
  · exact theorem_3_10_coind_sumBase_mem_fixedSubspace (ρ := ρ) v
  · change (coindEval (ρ := ρ) (1 : G)).toLinearMap
      (∑ r : R, coindBaseFunctionAt (ρ := ρ) (r : G) v) = v
    rw [map_sum]
    rw [Finset.sum_eq_single (1 : R)]
    · exact coindEval_base (ρ := ρ) (1 : G) v
    · intro r _ hr
      have hrq :
          ((r : G) : G ⧸ H) ≠ 1 := by
        intro hq
        have hrH : (r : G) ∈ H := (QuotientGroup.eq_one_iff _).mp hq
        have hr1 : (r : G) = 1 := by
          exact (Subgroup.disjoint_def.mp hHR.disjoint) hrH r.2
        exact hr (Subtype.ext hr1)
      have hrq' : ((1 : G) : G ⧸ H) ≠ ((r : G) : G ⧸ H) := by
        intro hq
        apply hrq
        simpa using hq.symm
      change coindEval (ρ := ρ) (1 : G)
        (coindBaseFunctionAt (ρ := ρ) (r : G) v) = 0
      exact coindEval_of_ne_coset (ρ := ρ) (x := (1 : G)) (g := (r : G)) hrq' v
    · intro hr
      exact False.elim (hr (Finset.mem_univ _))

private noncomputable def CFSG.theorem_3_10_conj_diff_equiv
    {F : Type*} [Field F]
    {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] {g x : G}
    (ρ : Representation F H V)
    (e : Theory.Representation.conjugateRep ρ g ≃ₗ Theory.Representation.conjugateRep ρ x) :
    ρ ≃ₗ Theory.Representation.conjugateRep ρ (x * g⁻¹) := by
  exact conj_diff_equiv (ρ := ρ) e

private theorem CFSG.theorem_3_10_coindRep_irreducible_of_noNontrivialConj
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) [FiniteDimensional F V] [Representation.IsIrreducible ρ]
    (hnconj :
      ∀ x : G, (x : G ⧸ H) ≠ 1 →
        ¬ Nonempty (ρ ≃ₗ Theory.Representation.conjugateRep ρ x)) :
    IsSimpleOrder (Subrepresentation (coindRep (ρ := ρ))) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let v0 : V := Classical.choose (exists_ne (0 : V))
  have hv0_ne : v0 ≠ 0 := Classical.choose_spec (exists_ne (0 : V))
  let f0 := coindBaseFunctionAt (ρ := ρ) (1 : G) v0
  have hf0_ne : f0 ≠ 0 := by
    intro hf0
    apply hv0_ne
    have h0 := congrArg (coindEval (ρ := ρ) (1 : G)) hf0
    simpa [f0] using h0
  let : Nontrivial (Representation.coindV H.subtype ρ) := ⟨f0, 0, hf0_ne⟩
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    have hSsub_ne : S.toSubmodule ≠ ⊥ := by
      intro hbot
      apply hS
      exact Subrepresentation.toSubmodule_injective hbot
    let SH : Subrepresentation ((coindRep (ρ := ρ)).comp H.subtype) := {
      toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro h f hf
        exact S.apply_mem_toSubmodule h.1 hf
    }
    obtain ⟨fS, hfS, hfS_ne⟩ := SH.toSubmodule.ne_bot_iff.mp hSsub_ne
    let : Nontrivial SH.toSubmodule := ⟨⟨fS, hfS⟩, 0, by simpa using hfS_ne⟩
    let iS : SH.toRepresentation →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := subrepInclusion SH
    obtain ⟨N, hNirr⟩ :=
      @Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
        F ↥H ↥SH.toSubmodule inferInstance inferInstance inferInstance inferInstance inferInstance
        SH.toRepresentation inferInstance
    let : Representation.IsIrreducible N.toRepresentation := hNirr
    let iNS : N.toRepresentation →ₗ SH.toRepresentation := subrepInclusion N
    let iN : N.toRepresentation →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := iS.comp iNS
    have hiN_injective : Function.Injective iN := by
      intro a b hab
      simpa [iN, iS, iNS, subrepInclusion] using hab
    let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
    let n0 : N.toSubmodule := Classical.choose (exists_ne (0 : N.toSubmodule))
    have hn0_ne : n0 ≠ 0 := Classical.choose_spec (exists_ne (0 : N.toSubmodule))
    have hiNn0_ne : iN n0 ≠ 0 := by
      intro h0
      apply hn0_ne
      exact hiN_injective (by simpa using h0)
    obtain ⟨g, hg_ne⟩ : ∃ g : G, (iN n0).1 g ≠ 0 := by
      by_contra hnone
      apply hiNn0_ne
      ext x
      by_cases hx : (iN n0).1 x = 0
      · exact hx
      · exact False.elim (hnone ⟨x, hx⟩)
    let q : G ⧸ H := g
    let P (q' : G ⧸ H) :
        N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation :=
      (coindProjToCoset (ρ := ρ) q').comp iN
    have hPq_ne : P q ≠ 0 := by
      intro hP0
      apply hg_ne
      have h0 := congrArg
        (fun f => (((f n0).1 : Representation.coindV H.subtype ρ).1 g)) hP0
      simpa [P, q, coindProjToCoset, coindProj_apply] using h0
    have hP_unique (q' : G ⧸ H) (hq' : q' ≠ q) : P q' = 0 := by
      by_contra hPq'_ne
      let x : G := Classical.choose (QuotientGroup.mk_surjective q')
      have hx : (x : G ⧸ H) = q' := Classical.choose_spec (QuotientGroup.mk_surjective q')
      have :
          IsSimpleOrder
            (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) (g : G ⧸ H)
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) := by
        simpa [q] using
          (coindCosetSubrep_irreducible (ρ := ρ) (g : G ⧸ H) :
            IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)))
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q').toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) q'
      let eNq :
          N.toRepresentation ≃ₗ
            (coindCosetSubrep (ρ := ρ) q).toRepresentation := by
          let fq : N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation := P q
          have hfq_ne : fq ≠ 0 := by simpa [fq] using hPq_ne
          exact
            (show N.toRepresentation ≃ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation from
              repEquivOfNeZeroOfSimple
                (V₁ := N.toSubmodule)
                (V₂ := (coindCosetSubrep (ρ := ρ) q).toSubmodule)
                (ρ₁ := N.toRepresentation)
                (ρ₂ := (coindCosetSubrep (ρ := ρ) q).toRepresentation)
                (hρ₂ := coindCosetSubrep_irreducible (ρ := ρ) q)
                (f := fq)
                hfq_ne)
      let eNq' :
          N.toRepresentation ≃ₗ
            (coindCosetSubrep (ρ := ρ) q').toRepresentation := by
          let fq' : N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation := P q'
          have hfq'_ne : fq' ≠ 0 := by simpa [fq'] using hPq'_ne
          exact
            (show N.toRepresentation ≃ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation from
              repEquivOfNeZeroOfSimple
                (V₁ := N.toSubmodule)
                (V₂ := (coindCosetSubrep (ρ := ρ) q').toSubmodule)
                (ρ₁ := N.toRepresentation)
                (ρ₂ := (coindCosetSubrep (ρ := ρ) q').toRepresentation)
                (hρ₂ := coindCosetSubrep_irreducible (ρ := ρ) q')
                (f := fq')
                hfq'_ne)
      let eCg :
          (coindCosetSubrep (ρ := ρ) q).toRepresentation ≃ₗ
            Theory.Representation.conjugateRep ρ g := by
        simpa [q] using (coindCosetEquiv (ρ := ρ) g)
      let eCx :
          (coindCosetSubrep (ρ := ρ) q').toRepresentation ≃ₗ
            Theory.Representation.conjugateRep ρ x := by
        rw [← hx]
        exact coindCosetEquiv (ρ := ρ) x
      let eNg : N.toRepresentation ≃ₗ Theory.Representation.conjugateRep ρ g := eNq.trans eCg
      let eNx : N.toRepresentation ≃ₗ Theory.Representation.conjugateRep ρ x := eNq'.trans eCx
      have hneqone : ((x * g⁻¹ : G) : G ⧸ H) ≠ 1 := by
        intro h1
        apply hq'
        calc
          q' = (x : G ⧸ H) := hx.symm
          _ = (g : G ⧸ H) := by
                have hxg' : (x : G ⧸ H) * (g : G ⧸ H)⁻¹ = 1 := by
                  simpa [div_eq_mul_inv] using h1
                calc
                  (x : G ⧸ H) = ((x : G ⧸ H) * (g : G ⧸ H)⁻¹) * (g : G ⧸ H) := by
                    simp [mul_assoc]
                  _ = (g : G ⧸ H) := by simp [hxg']
          _ = q := by rfl
      exact False.elim <|
        hnconj (x * g⁻¹) hneqone
          ⟨theorem_3_10_conj_diff_equiv (ρ := ρ) (e := eNg.symm.trans eNx)⟩
    have hmem_q (n : N.toSubmodule) : iN n ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := by
      have hzero_proj (q' : G ⧸ H) (hq' : q' ≠ q) : coindProj (ρ := ρ) q' (iN n) = 0 := by
        have h0 := congrArg (fun f => ((f n).1 : Representation.coindV H.subtype ρ))
          (hP_unique q' hq')
        simpa [P, coindProjToCoset] using h0
      have h_eq : iN n = coindProj (ρ := ρ) q (iN n) := by
        ext x
        by_cases hx : (x : G ⧸ H) = q
        · simp [coindProj_apply, hx]
        · have hxproj : coindProj (ρ := ρ) (x : G ⧸ H) (iN n) = 0 := hzero_proj (x : G ⧸ H) hx
          have hxzero : (iN n).1 x = 0 := by
            have h0 := congrArg (fun f : Representation.coindV H.subtype ρ => f.1 x) hxproj
            simpa [coindProj_apply] using h0
          simp [coindProj_apply, hx, hxzero]
      rw [h_eq]
      exact coindProj_mem_coset (ρ := ρ) q (iN n)
    have hw0_q : iN n0 ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := hmem_q n0
    have hw0_SH : iN n0 ∈ SH.toSubmodule := by
      change (((iS (iNS n0)) : Representation.coindV H.subtype ρ)) ∈ SH.toSubmodule
      exact (iNS n0).2
    have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) :=
      coindCosetSubrep_irreducible (ρ := ρ) q
    have hCq_le : (coindCosetSubrep (ρ := ρ) q).toSubmodule ≤ SH.toSubmodule := by
      exact subrep_le_of_nonzero_mem
        (ρ' := ((coindRep (ρ := ρ)).comp H.subtype))
        (S := coindCosetSubrep (ρ := ρ) q) (T := SH) hw0_q hw0_SH hiNn0_ne
    have hCr_le (r : G ⧸ H) : (coindCosetSubrep (ρ := ρ) r).toSubmodule ≤ SH.toSubmodule := by
      let y : G := Classical.choose (QuotientGroup.mk_surjective (r⁻¹ * q))
      have hy : (y : G ⧸ H) = r⁻¹ * q := Classical.choose_spec (QuotientGroup.mk_surjective (r⁻¹ * q))
      have hy_mem : coindRep (ρ := ρ) y (iN n0) ∈ (coindCosetSubrep (ρ := ρ) r).toSubmodule := by
        have hy_mem' := coind_apply_mem_coset_shift (ρ := ρ) y (iN n0) hw0_q
        simpa [hy, div_eq_mul_inv, mul_assoc] using hy_mem'
      have hy_SH : coindRep (ρ := ρ) y (iN n0) ∈ SH.toSubmodule := by
        exact S.apply_mem_toSubmodule y hw0_SH
      have hy_ne : coindRep (ρ := ρ) y (iN n0) ≠ 0 := by
        intro h0
        apply hiNn0_ne
        exact (Representation.apply_bijective (coindRep (ρ := ρ)) y).1 h0
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) r).toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) r
      exact subrep_le_of_nonzero_mem
        (ρ' := ((coindRep (ρ := ρ)).comp H.subtype))
        (S := coindCosetSubrep (ρ := ρ) r) (T := SH) hy_mem hy_SH hy_ne
    have hsup_le : (⨆ r : G ⧸ H, (coindCosetSubrep (ρ := ρ) r).toSubmodule) ≤ S.toSubmodule := by
      refine iSup_le ?_
      intro r
      exact hCr_le r
    have htop_le : (⊤ : Submodule F (Representation.coindV H.subtype ρ)) ≤ S.toSubmodule := by
      simpa [iSup_coindCosetSubrep_eq_top (ρ := ρ)] using hsup_le
    apply Subrepresentation.toSubmodule_injective
    exact le_antisymm le_top htop_le

set_option backward.isDefEq.respectTransparency false in
private noncomputable def CFSG.theorem_3_10_coindEquivOfNoNontrivialConj
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) [Representation.IsIrreducible ρ]
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (ρ.comp H.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    (hnconj : ∀ x : G, (x : G ⧸ H) ≠ 1 →
      ¬ Nonempty (M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x)) :
    ρ ≃ₗ coindRep M.toRepresentation := by
  let : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let : FiniteDimensional F M.toSubmodule := FiniteDimensional.of_injective M.toSubmodule.subtype
    Subtype.val_injective
  let f : ρ →ₗ coindRep M.toRepresentation := theorem_3_10_coindMapOfSubrep ρ hchar M
  let : Nontrivial M.toSubmodule := Subrepresentation.irreducible_module_nontrivial M.toRepresentation
  have hf_ne : f ≠ 0 := by
    obtain ⟨m0, hm0_ne⟩ := exists_ne (0 : M.toSubmodule)
    intro hf0
    have h_eval :
        coindEval (ρ := M.toRepresentation) (1 : G) (f m0) = m0 :=
      theorem_3_10_coindMapOfSubrep_eval_one ρ hchar M m0
    have h_zero :
        coindEval (ρ := M.toRepresentation) (1 : G) (f m0) = 0 := by
      simp [f, hf0]
    exact hm0_ne (h_eval.symm.trans h_zero)
  have hsimple_coind :
      IsSimpleOrder (Subrepresentation (coindRep (ρ := M.toRepresentation))) :=
    theorem_3_10_coindRep_irreducible_of_noNontrivialConj (ρ := M.toRepresentation) hnconj
  let : Representation.IsIrreducible (coindRep (ρ := M.toRepresentation)) := hsimple_coind
  have hfinj : Function.Injective f := by
    rcases (Representation.IsIrreducible.injective_or_eq_zero
      (ρ := ρ) (σ := coindRep (ρ := M.toRepresentation)) (f := f)) with hfinj | hf0
    · exact hfinj
    · exact False.elim (hf_ne hf0)
  have hrange_ne : f.range ≠ ⊥ := by
    intro hbot
    apply hf_ne
    apply Theory.Representation.RepMap.toLinearMap_injective
    apply LinearMap.range_eq_bot.mp
    have hsub := congrArg Subrepresentation.toSubmodule hbot
    change f.range.toSubmodule = (⊥ : Subrepresentation (coindRep M.toRepresentation)).toSubmodule at hsub
    calc
      LinearMap.range f.toLinearMap = f.range.toSubmodule := rfl
      _ = (⊥ : Subrepresentation (coindRep M.toRepresentation)).toSubmodule := hsub
      _ = ⊥ := theorem_3_10_toSubmodule_bot (coindRep M.toRepresentation)
  have hrange_top : f.range = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible (coindRep (ρ := M.toRepresentation))).eq_bot_or_eq_top f.range with
      hbot | htop
    · exact False.elim (hrange_ne hbot)
    · exact htop
  have hfsurj : Function.Surjective f := by
    exact LinearMap.range_eq_top.mp (by
      have hsub := congrArg Subrepresentation.toSubmodule hrange_top
      change f.range.toSubmodule = (⊤ : Subrepresentation (coindRep M.toRepresentation)).toSubmodule at hsub
      calc
        LinearMap.range f.toLinearMap = f.range.toSubmodule := rfl
        _ = (⊤ : Subrepresentation (coindRep M.toRepresentation)).toSubmodule := hsub
        _ = ⊤ := theorem_3_10_toSubmodule_top (coindRep M.toRepresentation))
  let eLin : V ≃ₗ[F] Representation.coindV H.subtype M.toRepresentation :=
    LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsurj⟩
  refine Theory.Representation.RepEquiv.mk eLin ?_
  intro g
  ext v x
  simpa [LinearMap.comp_apply, eLin] using congrArg
    (fun z : Representation.coindV H.subtype M.toRepresentation => z.1 x)
    (Representation.IntertwiningMap.isIntertwining
      (ρ := ρ) (σ := coindRep (ρ := M.toRepresentation)) f g v)


set_option backward.isDefEq.respectTransparency false in
private noncomputable def CFSG.theorem_3_10_coindFixedSubspaceEquiv
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H R : Subgroup G}
    [H.Normal] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (hHR : H.IsComplement' R) :
    (coindRep (ρ := ρ)).fixedSubspace R ≃ₗ[F] V := by
  classical
  let eval :
      ↥((coindRep (ρ := ρ)).fixedSubspace R) →ₗ[F] V :=
    (coindEval (ρ := ρ) (1 : G)).toLinearMap.comp
      ((coindRep (ρ := ρ)).fixedSubspace R).subtype
  have hsurj : Function.Surjective eval := by
    simpa [eval] using theorem_3_10_coindEval_surjective_fixedSubspace (ρ := ρ) hHR
  have hinj : Function.Injective eval := by
    intro f g hfg
    have hsub : eval (f - g) = 0 := by
      apply sub_eq_zero.mp
      simpa [eval, map_sub] using congrArg (fun z => z - eval g) hfg
    have hzero :
        ∀ x : G, ((f - g : (coindRep (ρ := ρ)).fixedSubspace R) : Representation.coindV H.subtype ρ).1 x = 0 := by
      intro x
      have hx_top : x ∈ H ⊔ R := by
        simp [hHR.sup_eq_top]
      rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := H) (t := R)).1 hx_top with
        ⟨h, hhH, r, hrR, hhr⟩
      let hH : H := ⟨h, hhH⟩
      let rR : R := ⟨r, hrR⟩
      have hfixr :
          (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ).1 (rR : G)) = 0 := by
        have hfg_r :
            coindRep (ρ := ρ) rR
              ((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
                Representation.coindV H.subtype ρ) =
              ((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
                Representation.coindV H.subtype ρ) :=
          (f - g).2 rR
        have h1 := congrArg
          (fun z : Representation.coindV H.subtype ρ => z.1 (1 : G)) hfg_r
        have h_eval_one :
            (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
                Representation.coindV H.subtype ρ).1 (1 : G)) = 0 := by
          change coindEval (ρ := ρ) (1 : G)
            (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ)) = 0
          change coindEval (ρ := ρ) (1 : G)
            (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ)) = 0 at hsub
          exact hsub
        calc
          (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ).1 (rR : G))
              =
            (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ).1 (1 : G)) := by
                simpa [Representation.coind_apply] using h1
          _ = 0 := h_eval_one
      have hcoind :
          (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ).1 ((h : G) * (r : G))) =
            ρ hH
              (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
                Representation.coindV H.subtype ρ).1 (rR : G)) := by
        simpa using
          (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
            Representation.coindV H.subtype ρ).2 hH rR)
      have hcoind' :
          (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ).1 x) =
            ρ hH
              (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
                Representation.coindV H.subtype ρ).1 (rR : G)) := by
        simpa [hhr] using hcoind
      calc
        (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
            Representation.coindV H.subtype ρ).1 x)
            =
          ρ hH
            (((f - g : (coindRep (ρ := ρ)).fixedSubspace R) :
              Representation.coindV H.subtype ρ).1 (rR : G)) := hcoind'
        _ = ρ hH 0 := by rw [hfixr]
        _ = 0 := by simp
    apply Subtype.ext
    ext x
    exact sub_eq_zero.mp (hzero x)
  exact LinearEquiv.ofBijective eval ⟨hinj, hsurj⟩


/- Retired route: the former prime-cardinality coinduction endpoint was replaced by
the endomorphism-field argument in `theorem_3_10_case2_card_formula_rep_theory`. -/
/-
set_option maxHeartbeats 800000 in
/-- Step 3b: Prove ρ ≅ coindRep(W) via the dichotomy:
  - Case B: no nontrivial conjugate of W is isomorphic to W → use theorem_3_10_coindEquivOfNoNontrivialConj.
  - Case A: some nontrivial conjugate is isomorphic → then all are (by all_conjugates_of_prime_quotient),
    and the orbit argument (m = p case) gives ρ ≅ coindRep(W). The m = 1 subcase leads to a
    contradiction via scalar R-action (contradicts hreg/hfaith). -/
private noncomputable def theorem_3_10_case2_rho_iso_coind
    {q : ℕ} [Fact q.Prime] [Finite G] [Finite M] [Nontrivial M]
    [IsElementaryAbelian q M] [MulDistribMulAction G M]
    (hK_min : ∀ N : Subgroup G, N.Normal → N ≤ K → N ≠ ⊥ → N = K)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (hR_cyclic : IsCyclic R)
    (hR_prime : Nat.Prime (Nat.card R))
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤)
    (ρ : Representation (ZMod q) G (Additive M))
    (hirred : Representation.IsIrreducible ρ)
    (hfaith : actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G) = ⊥)
    (hchar : ringChar (ZMod q) = 0 ∨
      (Nat.Prime (ringChar (ZMod q)) ∧ Nat.Coprime (ringChar (ZMod q)) (Nat.card K)))
    (W : Subrepresentation (ρ.comp K.subtype))
    [Representation.IsIrreducible W.toRepresentation] :
    ρ ≃ₗ coindRep W.toRepresentation := by
  classical
  let : K.Normal := hfrob.normal
  have hR_ne_bot : R ≠ ⊥ := hfrob.complement_ne_bot
  have hcard_quot : Nat.card (G ⧸ K) = Nat.card R := by
    let e : G ⧸ K ≃* R := hfrob.isComplement'.symm.QuotientMulEquiv
    simpa using Nat.card_congr e.toEquiv
  have hreg : ActsRegularly (↥R) (↥K) :=
    theorem_3_10_regular_conj_action (G := G) (K := K) (R := R) hfrob
  have hR_nontrivial : Nontrivial R := R.nontrivial_iff_ne_bot.mpr hR_ne_bot
  have : Fintype R := Fintype.ofFinite (↥R)
  -- Pick any nontrivial r ∈ R (R has prime order, so any r≠1 generates it)
  have h_exists_nonone : ∃ (r : R), r ≠ 1 := by
    have hcard_gt_one : 1 < Fintype.card R := by
      have hcard_ne_one : Fintype.card R ≠ 1 := by
        intro hcard_one
        apply hR_ne_bot
        have : Nat.card R = 1 := by simpa [Nat.card_eq_fintype_card] using hcard_one
        exact (Subgroup.eq_bot_iff_card (H := R)).mpr this
      have hpos : 0 < Fintype.card R := Fintype.card_pos
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hpos.ne', hcard_ne_one⟩
    have h_exists := Fintype.exists_ne_of_one_lt_card hcard_gt_one
    rcases h_exists 1 with ⟨r, hr_ne⟩
    exact ⟨r, hr_ne⟩
  let r : R := Classical.choose h_exists_nonone
  have hr_ne_one : r ≠ 1 := Classical.choose_spec h_exists_nonone
  have hx_ne_one : ((r : G) : G ⧸ K) ≠ 1 := by
    intro h_eq
    have h_mem : (r : G) ∈ K := by
      simpa [QuotientGroup.eq_one_iff] using h_eq
    have h_disjoint : Disjoint K R := hfrob.isComplement'.disjoint
    have h_inf_le : K ⊓ R ≤ ⊥ := disjoint_iff_inf_le.mp h_disjoint
    have h_inf_eq_bot : K ⊓ R = ⊥ := le_antisymm h_inf_le bot_le
    have h_mem_inf : (r : G) ∈ (K ⊓ R : Subgroup G) := Subgroup.mem_inf.mpr ⟨h_mem, r.2⟩
    have h_mem_bot : (r : G) ∈ (⊥ : Subgroup G) := by
      rw [← h_inf_eq_bot]
      exact h_mem_inf
    have h_one : (r : G) = 1 := by simpa using h_mem_bot
    exact hr_ne_one (Subtype.ext h_one)
  by_cases h_no_conj : ¬ Nonempty (W.toRepresentation ≃ₗ
    Theory.Representation.conjugateRep W.toRepresentation (r : G))
  · -- Case B: W ≇ W^r for a generator r. Then no nontrivial conjugate is isomorphic.
    have hnconj : ∀ x : G, (x : G ⧸ K) ≠ 1 → ¬ Nonempty (W.toRepresentation ≃ₗ
      Theory.Representation.conjugateRep W.toRepresentation x) := by
      intro x hx_ne
      intro h_nonempty
      let e : W.toRepresentation ≃ₗ Theory.Representation.conjugateRep W.toRepresentation x :=
        Classical.choice h_nonempty
      have hall := all_conjugates_of_prime_quotient (ρ := W.toRepresentation)
        hcard_quot hR_prime hx_ne e
      exact h_no_conj ⟨hall (r : G)⟩
    exact theorem_3_10_coindEquivOfNoNontrivialConj ρ hchar W hnconj
  · -- Case A: W ≅ W^r. Then all conjugates are isomorphic.
    have h_conj : Nonempty (W.toRepresentation ≃ₗ
      Theory.Representation.conjugateRep W.toRepresentation (r : G)) := by
      exact not_not.mp h_no_conj
    let e : W.toRepresentation ≃ₗ Theory.Representation.conjugateRep W.toRepresentation (r : G) :=
      Classical.choice h_conj
    have hall : ∀ x : G, W.toRepresentation ≃ₗ Theory.Representation.conjugateRep W.toRepresentation x :=
      all_conjugates_of_prime_quotient (ρ := W.toRepresentation) hcard_quot hR_prime hx_ne_one e
    have hall_conj : ∀ x : G, Nonempty (W.toRepresentation ≃ₗ
      Theory.Representation.conjugateRep W.toRepresentation x) :=
      λ x => ⟨hall x⟩
    -- Step 2: Construct φ and prove injectivity
    let φ : ρ →ₗ coindRep W.toRepresentation := theorem_3_10_coindMapOfSubrep ρ hchar W
    let : Nontrivial W.toSubmodule :=
      Subrepresentation.irreducible_module_nontrivial W.toRepresentation
    have hφ_ne_zero : φ ≠ 0 := by
      obtain ⟨m0, hm0_ne⟩ := exists_ne (0 : W.toSubmodule)
      intro hφ0
      have h_eval : coindEval (ρ := W.toRepresentation) (1 : G) (φ m0) = m0 :=
        theorem_3_10_coindMapOfSubrep_eval_one ρ hchar W m0
      have h_zero : coindEval (ρ := W.toRepresentation) (1 : G) (φ m0) = 0 := by
        simp [φ, hφ0]
      exact hm0_ne (h_eval.symm.trans h_zero)
    have hφ_inj : Function.Injective φ := by
      let σ : Representation (ZMod q) G (Representation.coindV K.subtype W.toRepresentation) :=
        Representation.coind K.subtype W.toRepresentation
      rcases (Representation.IsIrreducible.injective_or_eq_zero
        (ρ := ρ) (σ := σ) (f := φ)) with hφ_inj' | hφ0
      · exact hφ_inj'
      · exact False.elim (hφ_ne_zero hφ0)
    -- Step 4: ρ|_K is W-isotypic with multiplicity m ≤ p
    let V_coind := Representation.coindV K.subtype W.toRepresentation
    have : Fintype (G ⧸ K) := Fintype.ofFinite (G ⧸ K)
    have : FiniteDimensional (ZMod q) (Additive M) :=
      finiteDimensional_of_irreducible_finite_group ρ hirred
    have : FiniteDimensional (ZMod q) (W.toSubmodule) :=
      finiteDimensional_of_irreducible_finite_group W.toRepresentation inferInstance
    have h_card_quot_fintype : Fintype.card (G ⧸ K) = Nat.card R := by
      rw [← Nat.card_eq_fintype_card, hcard_quot]
    have h_finrank_rhoK_le : Module.finrank (ZMod q) (Additive M) ≤
        (Nat.card R) * Module.finrank (ZMod q) (W.toSubmodule) := by
      have h_finrank_inj : Module.finrank (ZMod q) (Additive M) ≤ Module.finrank (ZMod q) V_coind :=
        LinearMap.finrank_le_finrank_of_injective (hφ_inj : Function.Injective φ.toLinearMap)
      have h_finrank_coind : Module.finrank (ZMod q) V_coind =
          Fintype.card (G ⧸ K) * Module.finrank (ZMod q) (W.toSubmodule) :=
        finrank_coindRep_eq_card_mul (ρ := W.toRepresentation)
      calc
        Module.finrank (ZMod q) (Additive M) ≤ Module.finrank (ZMod q) V_coind := h_finrank_inj
        _ = Fintype.card (G ⧸ K) * Module.finrank (ZMod q) (W.toSubmodule) := h_finrank_coind
        _ = (Nat.card R) * Module.finrank (ZMod q) (W.toSubmodule) := by rw [h_card_quot_fintype]
    -- Step 5-7: Multiplicity dichotomy and conclusion.
    -- By the plan, either m = 1 (contradiction) or m = p (φ is an isomorphism).
    let p := Nat.card R
    have hp_prime : Nat.Prime p := hR_prime
    have hp_gt_one : 1 < p := Nat.Prime.one_lt hp_prime
    let U := W.toSubmodule
    have h_card_quot_fintype' : Fintype.card (G ⧸ K) = p := by
      rw [h_card_quot_fintype]
    have h_finrank_coind : Module.finrank (ZMod q) V_coind = p * Module.finrank (ZMod q) U := by
      calc
        Module.finrank (ZMod q) V_coind = Fintype.card (G ⧸ K) * Module.finrank (ZMod q) U :=
          finrank_coindRep_eq_card_mul (ρ := W.toRepresentation)
        _ = p * Module.finrank (ZMod q) U := by rw [h_card_quot_fintype']
    have : FiniteDimensional (ZMod q) V_coind := by
      have h_equiv : V_coind ≃ₗ[ZMod q] ((G ⧸ K) → W.toSubmodule) :=
        coindPiEquiv (ρ := W.toRepresentation)
      have : FiniteDimensional (ZMod q) ((G ⧸ K) → W.toSubmodule) := by infer_instance
      exact FiniteDimensional.of_injective (h_equiv : V_coind →ₗ[ZMod q] ((G ⧸ K) → W.toSubmodule))
        h_equiv.injective
    -- The finrank equality: either finrank(ρ) = finrank(W) (m = 1) or finrank(ρ) = p * finrank(W) (m = p).
    -- If finrank(ρ) < p * finrank(W), then ρ|_K has multiplicity m < p.
    -- The orbit argument shows that m must be 1 or p, so finrank(ρ) = finrank(W) in this case.
    -- The plan (Step 6) shows the m = 1 case leads to a contradiction via the regular action.
    -- Therefore finrank(ρ) = p * finrank(W) and φ is an isomorphism.
    by_cases h_finrank_eq_p : Module.finrank (ZMod q) (Additive M) = p * Module.finrank (ZMod q) U
    · -- Case m = p: finrank matches, so φ is an isomorphism.
      have h_dim_eq : Module.finrank (ZMod q) (Additive M) = Module.finrank (ZMod q) V_coind := by
        rw [h_finrank_coind, h_finrank_eq_p]
      have h_φ_surj : Function.Surjective φ := by
        have h_surj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim_eq
          (f := φ.toLinearMap)).mp hφ_inj
        exact h_surj
      let e := LinearEquiv.ofBijective φ.toLinearMap ⟨hφ_inj, h_φ_surj⟩
      refine Theory.Representation.RepEquiv.mk e ?_
      intro g
      apply LinearMap.ext
      intro v
      calc
        e (ρ g v) = φ.toLinearMap (ρ g v) := by simp [e]
        _ = φ (ρ g v) := rfl
        _ = (coindRep W.toRepresentation g) (φ v) :=
          Representation.IntertwiningMap.isIntertwining (ρ := ρ)
            (σ := coindRep W.toRepresentation) φ g v
        _ = (coindRep W.toRepresentation g) (φ.toLinearMap v) := rfl
        _ = (coindRep W.toRepresentation g) (e v) := by simp [e]
    · -- Case finrank(ρ) < p * finrank(W): orbit argument gives contradiction.
      -- Step 7: Using coindProj_coindRep_comm and the R-transitivity on G/K,
      -- one shows that the projection of im(φ) onto each coset summand C_q
      -- is nonzero, hence all of C_q (by K-irreducibility).  Then im(φ) = V_coind,
      -- giving finrank(ρ) = p·finrank(W), contradicting the case assumption.
      -- The key lemmas coindProj_coindRep_comm and coindRep_restriction_decomp
      -- are already in place above.  The remaining representation-theoretic
      -- argument (showing that a G-submodule of V_coind projecting onto all
      -- C_q must be the whole space) requires a detailed analysis of the
      -- R-module structure of F[R] which is not yet formalized.
      omitted

-/

set_option synthInstance.maxHeartbeats 100000 in
omit [Finite G] [Finite M] [MulDistribMulAction G M] [Nontrivial M] in
private theorem CFSG.theorem_3_10_case2_card_formula_rep_theory
    {q : ℕ} [Fact q.Prime] [Finite G] [Finite M] [Nontrivial M]
    [IsElementaryAbelian q M] [MulDistribMulAction G M]
    (hK_min : ∀ N : Subgroup G, N.Normal → N ≤ K → N ≠ ⊥ → N = K)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hsolvG : Group.IsSolvable G)
    (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (_hfixR : ∀ x : R, x ≠ 1 →
      fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M)
    (_hR_cyclic : IsCyclic R)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤) :
    Nat.card M = Nat.card (fixedPointSubgroup (↥R) M) ^ Nat.card R := by
  classical
  let : K.Normal := hfrob.normal
  let ρ : Representation (ZMod q) G (Additive M) :=
    Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := q)
  have hirred :=
    theorem_3_10_case2_irreducible (G := G) (M := M) (p := q) hminv
  let : Representation.IsIrreducible ρ := hirred
  let : FiniteDimensional (ZMod q) (Additive M) :=
    finiteDimensional_of_irreducible_finite_group ρ hirred
  let instNontrivρas : Nontrivial ρ.asModule :=
    Function.Injective.nontrivial (f := ρ.asModuleEquiv.symm)
      (LinearEquiv.injective ρ.asModuleEquiv.symm)
  let instFiniteρas : Finite ρ.asModule :=
    Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective
  have hfaith : actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G) = ⊥ :=
    theorem_3_10_case2_faithful_action (G := G) (M := M) (K := K) (R := R)
      hK_min hfrob hfixK
  have hcard_quot : Nat.card (G ⧸ K) = Nat.card R := by
    let e : G ⧸ K ≃* R := hfrob.isComplement'.symm.QuotientMulEquiv
    simpa using Nat.card_congr e.toEquiv
  have hq_prime : Nat.Prime q := Fact.out
  have hq_cop_G : Nat.Coprime q (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup q M).exists_card_eq
    have hn_pos : 0 < n := by
      have hcard_gt_one : 1 < Nat.card M := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rw [hn] at hcard_gt_one
      cases n with
      | zero => simp at hcard_gt_one
      | succ n => exact Nat.succ_pos _
    have hq_cop_pow : Nat.Coprime (Nat.card G) (q ^ n) := by simpa [hn] using hcop
    exact hq_cop_pow.symm.of_dvd_left (dvd_pow_self q (Nat.ne_of_gt hn_pos))
  have hq_cop_K : Nat.Coprime q (Nat.card K) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card K) hq_cop_G
  have hq_cop_R : Nat.Coprime q (Nat.card R) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card R) hq_cop_G
  have : IsMinimalNormal K := {
    minimal := fun N hN hNK => by
      by_cases hNbot : N = ⊥
      · exact Or.inl hNbot
      · exact Or.inr (hK_min N hN hNK hNbot) }
  let : Group.IsSolvable G := hsolvG
  have : Group.IsSolvable K := by infer_instance
  have : IsMulCommutative K := minimalNormal_solvable_isMulCommutative K
  let E := Module.End (MonoidAlgebra (ZMod q) G) ρ.asModule
  let instSemiringE : Semiring E :=
    @Ring.toSemiring E (@DivisionRing.toRing E (@Field.toDivisionRing E (endField_field ρ)))
  let instModuleE : @Module E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule :=
    endFieldModule ρ
  let : Field E := endField_field ρ
  let : Semiring E := instSemiringE
  let : AddCommGroup ρ.asModule := ρ.instAddCommGroupAsModule
  let : AddCommMonoid ρ.asModule := ρ.instAddCommMonoidAsModule
  have : @Module E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule := instModuleE
  let instModuleEStd : Module E ρ.asModule := endFieldModule ρ
  let : Module E ρ.asModule := instModuleEStd
  let κ : @Representation E G ρ.asModule instSemiringE inferInstance
      ρ.instAddCommMonoidAsModule instModuleE :=
    endFieldRep ρ
  have hρasFinite : Finite ρ.asModule := instFiniteρas
  let instFiniteE :
      @Module.Finite E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule instModuleE :=
    @Module.Finite.of_finite E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule
      instModuleE hρasFinite
  have :
      @Module.Finite E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule instModuleE :=
    instFiniteE
  have hfdE :
      @FiniteDimensional E ρ.asModule (@Field.toDivisionRing E (endField_field ρ))
        ρ.instAddCommGroupAsModule instModuleE := instFiniteE
  have :
      @FiniteDimensional E ρ.asModule (@Field.toDivisionRing E (endField_field ρ))
        ρ.instAddCommGroupAsModule instModuleE := hfdE
  have :
      @Module.Free E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule instModuleE :=
    @Module.Free.of_divisionRing E ρ.asModule (@Field.toDivisionRing E (endField_field ρ))
      ρ.instAddCommGroupAsModule instModuleE
  have : Module.Flat E ρ.asModule := Module.Flat.of_free
  have hκirr :
      @Representation.IsIrreducible G E ρ.asModule inferInstance (endField_field ρ)
        ρ.instAddCommGroupAsModule instModuleE κ := by
    dsimp [κ]
    exact endFieldRep_isIrreducible ρ
  have :
      @Representation.IsIrreducible G E ρ.asModule inferInstance (endField_field ρ)
        ρ.instAddCommGroupAsModule instModuleE κ := hκirr
  have hκabs :
      @Theory.Representation.IsAbsolutelyIrreducible E G ρ.asModule inferInstance (endField_field ρ)
        ρ.instAddCommGroupAsModule instModuleE κ := by
    dsimp [κ]
    exact endFieldRep_isAbsolutelyIrreducible ρ
  have :
      @Theory.Representation.IsAbsolutelyIrreducible E G ρ.asModule inferInstance (endField_field ρ)
        ρ.instAddCommGroupAsModule instModuleE κ := hκabs
  let Falg := AlgebraicClosure E
  let instFieldFalg : Field Falg := inferInstance
  let instAlgebraEFalg : Algebra E Falg := inferInstance
  let : Field Falg := instFieldFalg
  let : Algebra E Falg := instAlgebraEFalg
  let κ' : Representation Falg G (Falg ⊗[E] ρ.asModule) :=
    @Theory.Representation.extendScalars E G ρ.asModule inferInstance (endField_field ρ)
      ρ.instAddCommGroupAsModule
      instModuleE Falg instFieldFalg instAlgebraEFalg κ
  have hκ'irr : Representation.IsIrreducible κ' := by
    dsimp [κ']
    exact
      @Theory.Representation.IsAbsolutelyIrreducible.irreducible_of_extension
        E G ρ.asModule inferInstance (endField_field ρ) ρ.instAddCommGroupAsModule
        instModuleE
        κ hfdE Falg instFieldFalg instAlgebraEFalg hκabs
  let : Representation.IsIrreducible κ' := hκ'irr
  let instFDFalg : FiniteDimensional Falg (Falg ⊗[E] ρ.asModule) := by
    exact @Theory.Representation.extendScalars_finite_dimensional
      E G ρ.asModule inferInstance (endField_field ρ) ρ.instAddCommGroupAsModule
      instModuleE Falg instFieldFalg instAlgebraEFalg κ hfdE
  have : FiniteDimensional Falg (Falg ⊗[E] ρ.asModule) := instFDFalg
  let instNontrivFalg : Nontrivial (Falg ⊗[E] ρ.asModule) := by
    exact @Theory.Representation.extendScalars_nontrivial
      E G ρ.asModule inferInstance (endField_field ρ) ρ.instAddCommGroupAsModule
      instModuleE Falg instFieldFalg instAlgebraEFalg κ instNontrivρas
  have : Nontrivial (Falg ⊗[E] ρ.asModule) := instNontrivFalg
  have hringCharE : ringChar E = q := by
    let : Algebra (ZMod q) E :=
      Module.End.instAlgebra (ZMod q) (MonoidAlgebra (ZMod q) G) ρ.asModule
    have hEZ : ringChar E = ringChar (ZMod q) := by
      simpa [E] using (Algebra.ringChar_eq (K := ZMod q) (L := E)).symm
    simpa [ZMod.ringChar_zmod_n] using hEZ
  have hringCharFalg : ringChar Falg = q := by
    have hFE : ringChar Falg = ringChar E := by
      simpa [Falg] using (Algebra.ringChar_eq (K := E) (L := Falg)).symm
    exact hFE.trans hringCharE
  have hcharK_Falg :
      ringChar Falg = 0 ∨
        (Nat.Prime (ringChar Falg) ∧ Nat.Coprime (ringChar Falg) (Nat.card K)) := by
    right
    exact ⟨by simpa [hringCharFalg] using hq_prime,
      by simpa [hringCharFalg] using hq_cop_K⟩
  have hcharR_E :
      ringChar E = 0 ∨
        (Nat.Prime (ringChar E) ∧ Nat.Coprime (ringChar E) (Nat.card R)) := by
    right
    exact ⟨by simpa [hringCharE] using hq_prime,
      by simpa [hringCharE] using hq_cop_R⟩
  have hcharR_Falg :
      ringChar Falg = 0 ∨
        (Nat.Prime (ringChar Falg) ∧ Nat.Coprime (ringChar Falg) (Nat.card R)) := by
    right
    exact ⟨by simpa [hringCharFalg] using hq_prime,
      by simpa [hringCharFalg] using hq_cop_R⟩
  have hcardR_E_ne : (Nat.card R : E) ≠ 0 :=
    card_ne_zero_of_char_condition (G := R) (F := E) hcharR_E
  have hcardR_Falg_ne : (Nat.card R : Falg) ≠ 0 :=
    card_ne_zero_of_char_condition (G := R) (F := Falg) hcharR_Falg
  have hK_not_le_κ'_ker : ¬ K ≤ κ'.ker := by
    intro hKker'
    have hKkerκ : K ≤ κ.ker :=
      @theorem_3_10_le_ker_of_extendScalars
        G inferInstance E (endField_field ρ) Falg instFieldFalg instAlgebraEFalg
        ρ.asModule ρ.instAddCommGroupAsModule instModuleE κ K
        (by simpa [κ'] using hKker')
    have hKkerρ : K ≤ ρ.ker := by
      intro k hk
      have hkκ : k ∈ (endFieldRep ρ).ker := by
        simpa [κ] using hKkerκ hk
      exact (theorem_3_10_endFieldRep_ker_le ρ) hkκ
    have hK_le_action : K ≤ actionCentralizerIn (A := G) (G := M) (⊤ : Subgroup G) := by
      intro k hk
      rw [actionCentralizerIn]
      constructor
      · exact Subgroup.mem_top k
      · change k ∈ fixingSubgroupOf G M Set.univ
        have hkρ : k ∈
            (Theory.Representation.ofElementaryAbelianAction (A := G) (G := M) (p := q) :
              Representation (ZMod q) G (Additive M)).ker := by
          simpa [ρ] using hKkerρ hk
        simpa [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup] using hkρ
    have hKbot : K = ⊥ :=
      le_antisymm (by simpa [hfaith] using hK_le_action) bot_le
    exact hfrob.kernel_ne_bot hKbot
  let σ : Representation Falg K (Falg ⊗[E] ρ.asModule) := κ'.comp K.subtype
  obtain ⟨W, hWirr⟩ :=
    @Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      Falg K (Falg ⊗[E] ρ.asModule) inferInstance inferInstance inferInstance
      inferInstance instFDFalg σ instNontrivFalg
  have : Representation.IsIrreducible W.toRepresentation := hWirr
  have : FiniteDimensional Falg W.toSubmodule :=
    @FiniteDimensional.of_injective
      Falg W.toSubmodule instFieldFalg.toDivisionRing inferInstance inferInstance
      (Falg ⊗[E] ρ.asModule) inferInstance inferInstance W.toSubmodule.subtype
      Subtype.val_injective instFDFalg
  have hnconj :
      ∀ x : G, (x : G ⧸ K) ≠ 1 →
        ¬ Nonempty (W.toRepresentation ≃ₗ Theory.Representation.conjugateRep W.toRepresentation x) :=
    @theorem_3_10_noNontrivialConj_of_faithful
      Falg instFieldFalg inferInstance G inferInstance inferInstance K R inferInstance
      inferInstance (Falg ⊗[E] ρ.asModule) inferInstance inferInstance instFDFalg
      κ' hκ'irr hfrob hK_not_le_κ'_ker W hWirr
  let Vco := Representation.coindV K.subtype W.toRepresentation
  let ρco : Representation Falg G Vco := coindRep (ρ := W.toRepresentation)
  have h_equiv : κ' ≃ₗ ρco := by
    dsimp [ρco]
    exact theorem_3_10_coindEquivOfNoNontrivialConj κ' hcharK_Falg W hnconj
  have : Fintype (G ⧸ K) := Fintype.ofFinite (G ⧸ K)
  have h_card_quot_fintype : Fintype.card (G ⧸ K) = Nat.card R := by
    rw [← Nat.card_eq_fintype_card, hcard_quot]
  have hcoind_fix_fin :
      Module.finrank Falg
          ↥(@Representation.fixedSubspace Falg G Vco instFieldFalg inferInstance
            Vco.addCommGroup Vco.module ρco R) =
        Module.finrank Falg W.toSubmodule := by
    simpa [ρco] using
      LinearEquiv.finrank_eq
        (theorem_3_10_coindFixedSubspaceEquiv (ρ := W.toRepresentation) hfrob.isComplement')
  have hκ'_fix_fin :
      Module.finrank Falg ↥(κ'.fixedSubspace R) =
        Module.finrank Falg
          ↥(@Representation.fixedSubspace Falg G Vco instFieldFalg inferInstance
            Vco.addCommGroup Vco.module ρco R) := by
    exact LinearEquiv.finrank_eq (theorem_3_10_fixedSubspace_equiv_of_equiv h_equiv R)
  have hdimFalg :
      Module.finrank Falg (Falg ⊗[E] ρ.asModule) =
        Nat.card R * Module.finrank Falg ↥(κ'.fixedSubspace R) := by
    calc
      Module.finrank Falg (Falg ⊗[E] ρ.asModule) =
          Module.finrank Falg Vco := LinearEquiv.finrank_eq h_equiv.toLinearEquiv
      _ = Fintype.card (G ⧸ K) * Module.finrank Falg W.toSubmodule :=
          finrank_coindRep_eq_card_mul (ρ := W.toRepresentation)
      _ = Nat.card R * Module.finrank Falg W.toSubmodule := by rw [h_card_quot_fintype]
      _ = Nat.card R *
          Module.finrank Falg
            ↥(@Representation.fixedSubspace Falg G Vco instFieldFalg inferInstance
              Vco.addCommGroup Vco.module ρco R) := by
            rw [hcoind_fix_fin]
      _ = Nat.card R * Module.finrank Falg ↥(κ'.fixedSubspace R) := by
            rw [← hκ'_fix_fin]
  let κfix : @Submodule E ρ.asModule instSemiringE ρ.instAddCommMonoidAsModule instModuleE :=
    @Representation.fixedSubspace E G ρ.asModule (endField_field ρ) inferInstance
      ρ.instAddCommGroupAsModule instModuleE κ R
  have hκfix_base :
      κ'.fixedSubspace R = κfix.baseChange Falg := by
    simpa [κ', κfix] using
      (@theorem_3_10_fixedSubspace_extendScalars_eq_baseChange
        G inferInstance inferInstance E (endField_field ρ) Falg instFieldFalg
        instAlgebraEFalg ρ.asModule ρ.instAddCommGroupAsModule instModuleE κ R
        hcardR_E_ne hcardR_Falg_ne)
  have hκfix_finrank_base :
      Module.finrank Falg ↥(κ'.fixedSubspace R) =
        Module.finrank E ↥κfix := by
    let p := κfix
    have : Module.Free E p := Module.Free.of_divisionRing E p
    have hbase_inj : Function.Injective (p.subtype.baseChange Falg) := by
      simp [LinearMap.baseChange_eq_ltensor]
    have hto_inj : Function.Injective (p.toBaseChange Falg) := by
      intro x y hxy
      apply hbase_inj
      have hx :
          (p.toBaseChange Falg x : p.baseChange Falg).1 = (p.subtype.baseChange Falg) x := rfl
      have hy :
          (p.toBaseChange Falg y : p.baseChange Falg).1 = (p.subtype.baseChange Falg) y := rfl
      rw [← hx, ← hy]
      exact congrArg (fun z : p.baseChange Falg => z.1) hxy
    let ebc : Falg ⊗[E] p ≃ₗ[Falg] p.baseChange Falg :=
      LinearEquiv.ofBijective (p.toBaseChange Falg)
        ⟨hto_inj, Submodule.toBaseChange_surjective Falg p⟩
    calc
      Module.finrank Falg ↥(κ'.fixedSubspace R) =
          Module.finrank Falg ↥(p.baseChange Falg) := by
            rw [hκfix_base]
      _ = Module.finrank Falg (Falg ⊗[E] p) := (LinearEquiv.finrank_eq ebc.symm)
      _ = Module.finrank E p := Module.finrank_baseChange
  have hdimE :
      Module.finrank E ρ.asModule =
        Nat.card R * Module.finrank E ↥κfix := by
    calc
      Module.finrank E ρ.asModule =
          Module.finrank Falg (Falg ⊗[E] ρ.asModule) :=
            (Module.finrank_baseChange (R := Falg) (S := E) (M' := ρ.asModule)).symm
      _ = Nat.card R * Module.finrank Falg ↥(κ'.fixedSubspace R) := hdimFalg
      _ = Nat.card R * Module.finrank E ↥κfix := by rw [hκfix_finrank_base]
  have hcardM :
      Nat.card M = (Nat.card E) ^ Module.finrank E ρ.asModule := by
    let eM : Additive M ≃ M :=
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have h_as : Nat.card ρ.asModule = Nat.card (Additive M) :=
      Nat.card_congr ρ.asModuleEquiv.toEquiv
    have h_add : Nat.card (Additive M) = Nat.card M := Nat.card_congr eM
    calc
      Nat.card M = Nat.card ρ.asModule := by rw [← h_add, ← h_as]
      _ = (Nat.card E) ^ Module.finrank E ρ.asModule :=
          @Module.natCard_eq_pow_finrank E ρ.asModule
            (@Field.toDivisionRing E (endField_field ρ)) ρ.instAddCommGroupAsModule
            instModuleE instFiniteE
  have hcardFix :
      Nat.card (fixedPointSubgroup (↥R) M) =
        (Nat.card E) ^ Module.finrank E ↥κfix := by
    have h_end :
        Nat.card ↥κfix = Nat.card ↥(ρ.fixedSubspace R) := by
      simpa [κfix, κ] using
        Nat.card_congr (theorem_3_10_endFieldRepFixedSubspaceEquiv (ρ := ρ) R)
    have h_elem :
        Nat.card ↥(ρ.fixedSubspace R) =
          Nat.card (Additive ↥(fixedPointSubgroup (↥R) M)) := by
      exact Nat.card_congr
        (theorem_3_10_ofElementaryAbelianActionFixedSubspaceEquiv
          (A := G) (V := M) (p := q) (H := R))
    let eFix : Additive ↥(fixedPointSubgroup (↥R) M) ≃
        ↥(fixedPointSubgroup (↥R) M) :=
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have h_add :
        Nat.card (Additive ↥(fixedPointSubgroup (↥R) M)) =
          Nat.card (fixedPointSubgroup (↥R) M) := Nat.card_congr eFix
    calc
      Nat.card (fixedPointSubgroup (↥R) M) =
          Nat.card ↥κfix := by rw [← h_add, ← h_elem, ← h_end]
      _ = (Nat.card E) ^ Module.finrank E ↥κfix :=
          Module.natCard_eq_pow_finrank (K := E) (V := ↥κfix)
  calc
    Nat.card M = (Nat.card E) ^ Module.finrank E ρ.asModule := hcardM
    _ = (Nat.card E) ^
        (Nat.card R * Module.finrank E ↥κfix) := by rw [hdimE]
    _ = ((Nat.card E) ^ Module.finrank E ↥κfix) ^ Nat.card R := by
      rw [mul_comm, pow_mul]
    _ = (Nat.card (fixedPointSubgroup (↥R) M)) ^ Nat.card R := by rw [hcardFix]

set_option maxHeartbeats 1000000 in
public theorem CFSG.theorem_3_10
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvG : Group.IsSolvable G)
    (hnilM : Group.IsNilpotent M) (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    IsCyclic R ∧
      Nat.Prime (Nat.card R) ∧
      Nat.card M = Nat.card (fixedPointSubgroup (↥R) M) ^ Nat.card R ∧
      (IsCyclic (fixedPointSubgroup (↥R) M) →
        ⁅K, K⁆ ≤ actionCentralizerIn (A := G) (G := M) K) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type u310G) [Group G'] [Finite G'] (K' R' : Subgroup G')
      (M' : Type u310M) [Group M'] [Finite M'] [MulDistribMulAction G' M'] [Nontrivial M'],
      Nat.card G' + Nat.card M' = n →
      IsFrobeniusGroupWithKernelComplement K' R' →
      Group.IsSolvable G' →
      Group.IsNilpotent M' →
      Nat.Coprime (Nat.card G') (Nat.card M') →
      fixedPointSubgroup (↥K') M' = ⊥ →
      (∀ x : R', x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G'))) M' = fixedPointSubgroup (↥R') M') →
      IsCyclic R' ∧
        Nat.Prime (Nat.card R') ∧
        Nat.card M' = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R' ∧
        (IsCyclic (fixedPointSubgroup (↥R') M') →
          ⁅K', K'⁆ ≤ actionCentralizerIn (A := G') (G := M') K')
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ K' R' M' _ _ _ _ hn hfrob' hsolvG' hnilM' hcop' hfixK' hfixR'
    have hK_ne_bot : K' ≠ ⊥ := theorem_3_10_K_ne_bot (K := K') (M := M') hfixK'
    have hR_ne_bot : R' ≠ ⊥ := hfrob'.complement_ne_bot
    let : K'.Normal := hfrob'.normal
    have hsolvM' : Group.IsSolvable M' := by infer_instance
    have hcopR' : Nat.Coprime (Nat.card R') (Nat.card M') := by
      exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card R') hcop'
    have hregular :
        let : MulDistribMulAction (↥R') (↥K') :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G') R' K'
            (Subgroup.le_normalizer_of_normal (H := K'))
        ActsRegularly (↥R') (↥K') :=
      theorem_3_10_regular_conj_action (K := K') (R := R') hfrob'
    have hind :
        ∀ (G'' : Type u310G) [Group G''] [Finite G''] (K'' R'' : Subgroup G'')
          (M'' : Type u310M) [Group M''] [Finite M''] [MulDistribMulAction G'' M'']
          [Nontrivial M''],
          Nat.card G'' + Nat.card M'' < Nat.card G' + Nat.card M' →
          IsFrobeniusGroupWithKernelComplement K'' R'' →
          Group.IsSolvable G'' →
          Group.IsNilpotent M'' →
          Nat.Coprime (Nat.card G'') (Nat.card M'') →
          fixedPointSubgroup (↥K'') M'' = ⊥ →
          (∀ x : R'', x ≠ 1 →
            fixedPointSubgroup (↥(Subgroup.zpowers (x : G''))) M'' =
              fixedPointSubgroup (↥R'') M'') →
          IsCyclic R'' ∧
            Nat.Prime (Nat.card R'') ∧
            Nat.card M'' = Nat.card (fixedPointSubgroup (↥R'') M'') ^ Nat.card R'' ∧
            (IsCyclic (fixedPointSubgroup (↥R'') M'') →
              ⁅K'', K''⁆ ≤ actionCentralizerIn (A := G'') (G := M'') K'') := by
      intro G'' _ _ K'' R'' M'' _ _ _ _ hlt hfrob'' hsolvG'' hnilM'' hcop'' hfixK'' hfixR''
      have hlt' : Nat.card G'' + Nat.card M'' < n := by
        simpa [hn] using hlt
      exact
        ih (Nat.card G'' + Nat.card M'') hlt' G'' K'' R'' M'' rfl hfrob'' hsolvG'' hnilM''
          hcop'' hfixK'' hfixR''
    have hproper :
        ∀ {R₀ : Subgroup G'}, R₀ < R' → R₀ ≠ ⊥ →
          IsCyclic R₀ ∧
            Nat.Prime (Nat.card R₀) ∧
            Nat.card M' = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R₀ := by
      intro R₀ hR₀_lt hR₀_ne_bot
      let S : Subgroup G' := K' ⊔ R₀
      let : MulDistribMulAction S M' := MulDistribMulAction.compHom M' S.subtype
      have hltS : Nat.card S + Nat.card M' < Nat.card G' + Nat.card M' := by
        exact Nat.add_lt_add_right
          (theorem_3_10_subambient_card_lt_of_right_lt (K := K') (R := R') hfrob' hR₀_lt) _
      have hcopS : Nat.Coprime (Nat.card S) (Nat.card M') := by
        exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card S) hcop'
      have hfixKsub : fixedPointSubgroup (↥(K'.subgroupOf S)) M' = ⊥ := by
        rw [theorem_3_10_fixedPointSubgroup_subgroupOf_eq (M := M') (S := S) (A := K') le_sup_left]
        exact hfixK'
      have hfixRsub_eq :
          fixedPointSubgroup (↥(R₀.subgroupOf S)) M' = fixedPointSubgroup (↥R') M' := by
        rw [theorem_3_10_fixedPointSubgroup_subgroupOf_eq (M := M') (S := S) (A := R₀)
          le_sup_right]
        exact
          theorem_3_10_fixedPointSubgroup_eq_of_nontrivial_le (R := R') (M := M') hfixR'
            hR₀_lt.1 hR₀_ne_bot
      have hfixRsub :
          ∀ x : R₀.subgroupOf S, x ≠ 1 →
            fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) M' =
              fixedPointSubgroup (↥(R₀.subgroupOf S)) M' := by
        intro x hx
        have hxR0 : ((x : S) : G') ∈ R₀ := by
          exact x.2
        have hxR : (⟨(x : G'), hR₀_lt.1 hxR0⟩ : R') ≠ 1 := by
          intro hx1
          apply hx
          ext
          simpa using congrArg Subtype.val hx1
        calc
          fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) M'
              = fixedPointSubgroup (↥((Subgroup.zpowers (x : G')).subgroupOf S)) M' := by
                  rw [← theorem_3_10_zpowers_subgroupOf_eq (S := S) x]
          _ = fixedPointSubgroup (↥(Subgroup.zpowers (x : G'))) M' := by
                rw [theorem_3_10_fixedPointSubgroup_subgroupOf_eq (M := M') (S := S)
                  (A := Subgroup.zpowers (x : G')) (Subgroup.zpowers_le.2 x.1.2)]
          _ = fixedPointSubgroup (↥R') M' := hfixR' ⟨(x : G'), hR₀_lt.1 hxR0⟩ hxR
          _ = fixedPointSubgroup (↥(R₀.subgroupOf S)) M' := hfixRsub_eq.symm
      have hmainS :=
        hind S (K'.subgroupOf S) (R₀.subgroupOf S) M' hltS
          (theorem_3_10_subambient_frobenius (K := K') (R := R') hfrob' hR₀_lt.1 hR₀_ne_bot)
          (by infer_instance) hnilM' hcopS hfixKsub hfixRsub
      refine ⟨?_, ?_, ?_⟩
      · exact (Subgroup.subgroupOfEquivOfLe (H := R₀) (K := S) le_sup_right).isCyclic.1 hmainS.1
      · simpa [natCard_subgroupOf_eq R₀ S le_sup_right] using hmainS.2.1
      · calc
          Nat.card M' =
              Nat.card (fixedPointSubgroup (↥(R₀.subgroupOf S)) M') ^ Nat.card (R₀.subgroupOf S) :=
                hmainS.2.2.1
          _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card (R₀.subgroupOf S) := by
                rw [hfixRsub_eq]
          _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R₀ := by
                rw [natCard_subgroupOf_eq R₀ S le_sup_right]
    have hsame_prime :
        ∀ {p q : ℕ}, p.Prime → q.Prime → p ∣ Nat.card R' → q ∣ Nat.card R' → p = q := by
      intro p q hp hq hpdvd hqdvd
      by_cases hpq : p = q
      · exact hpq
      let : Fact p.Prime := ⟨hp⟩
      let : Fact q.Prime := ⟨hq⟩
      obtain ⟨P, hP_card⟩ := Sylow.exists_subgroup_card_pow_prime (G := R') p (n := 1) (by
        simpa using hpdvd)
      obtain ⟨Q, hQ_card⟩ := Sylow.exists_subgroup_card_pow_prime (G := R') q (n := 1) (by
        simpa using hqdvd)
      let PG : Subgroup G' := P.map R'.subtype
      let QG : Subgroup G' := Q.map R'.subtype
      have hPG_card : Nat.card PG = p := by
        simpa [PG, hP_card] using
          (Subgroup.card_map_of_injective (K := P) (f := R'.subtype) R'.subtype_injective)
      have hQG_card : Nat.card QG = q := by
        simpa [QG, hQ_card] using
          (Subgroup.card_map_of_injective (K := Q) (f := R'.subtype) R'.subtype_injective)
      have hPG_ne_bot : PG ≠ ⊥ := by
        intro hbot
        have : Nat.card PG = 1 := by simp [hbot]
        have hp_one : p = 1 := by simpa [hPG_card] using this
        exact hp.ne_one hp_one
      have hQG_ne_bot : QG ≠ ⊥ := by
        intro hbot
        have : Nat.card QG = 1 := by simp [hbot]
        have hq_one : q = 1 := by simpa [hQG_card] using this
        exact hq.ne_one hq_one
      have hPG_lt : PG < R' := by
        refine lt_of_le_of_ne ?_ ?_
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact y.2
        · intro hEq
          have hcard_eq : Nat.card R' = p := by simpa [hEq] using hPG_card
          have hq_dvd_p : q ∣ p := hcard_eq ▸ hqdvd
          rcases (Nat.dvd_prime hp).1 hq_dvd_p with hq_one | hq_eq
          · exact False.elim (hq.ne_one hq_one)
          · exact hpq hq_eq.symm
      have hQG_lt : QG < R' := by
        refine lt_of_le_of_ne ?_ ?_
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact y.2
        · intro hEq
          have hcard_eq : Nat.card R' = q := by simpa [hEq] using hQG_card
          have hp_dvd_q : p ∣ q := hcard_eq ▸ hpdvd
          rcases (Nat.dvd_prime hq).1 hp_dvd_q with hp_one | hp_eq
          · exact False.elim (hp.ne_one hp_one)
          · exact hpq hp_eq
      have hMP :
          Nat.card M' = Nat.card (fixedPointSubgroup (↥R') M') ^ p :=
        by simpa [hPG_card] using (hproper hPG_lt hPG_ne_bot).2.2
      have hMQ :
          Nat.card M' = Nat.card (fixedPointSubgroup (↥R') M') ^ q :=
        by simpa [hQG_card] using (hproper hQG_lt hQG_ne_bot).2.2
      have hfix_card_gt_one : 1 < Nat.card (fixedPointSubgroup (↥R') M') := by
        have hfix_ne_one : Nat.card (fixedPointSubgroup (↥R') M') ≠ 1 := by
          intro hfix_one
          have hM_one : Nat.card M' = 1 := by
            rw [hMP, hfix_one]
            simp
          exact
            (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial M')).ne'
              hM_one
        exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
          ⟨(Nat.card_pos (α := ↥(fixedPointSubgroup (↥R') M'))).ne', hfix_ne_one⟩
      have hpow_eq : Nat.card (fixedPointSubgroup (↥R') M') ^ p =
          Nat.card (fixedPointSubgroup (↥R') M') ^ q := hMP.symm.trans hMQ
      exact (Nat.pow_right_injective hfix_card_gt_one hpow_eq)
    have hR_prime_dvd : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card R' := by
      have hcard_ne_one : Nat.card R' ≠ 1 := by
        intro hcard_one
        exact hR_ne_bot ((Subgroup.eq_bot_iff_card (H := R')).2 hcard_one)
      exact Nat.exists_prime_and_dvd (n := Nat.card R') hcard_ne_one
    obtain ⟨p, hp, hpdvd⟩ := hR_prime_dvd
    let : Fact p.Prime := ⟨hp⟩
    have hR_pgroup : IsPGroup p R' := by
      refine (IsPGroup.iff_card (p := p) (G := R')).2 ?_
      refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := R')).ne' ?_⟩
      intro q hq hqdvd
      exact (hsame_prime (p := p) (q := q) hp hq hpdvd hqdvd).symm
    have hfixKreg : fixedPointSubgroup (↥R') (↥K') = ⊥ := by
      have hRK : R' ≤ Subgroup.normalizer K' := Subgroup.le_normalizer_of_normal (H := K')
      have hfix_eq :
          fixedPointSubgroup (↥R') (↥K') = (subgroupCentralizerIn K' R').subgroupOf K' := by
        simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K' R' hRK
      let : Nontrivial ↥R' := R'.nontrivial_iff_ne_bot.mpr hR_ne_bot
      obtain ⟨x, hx_ne⟩ := exists_ne (1 : R')
      have hx_fix_bot : fixedPointSubgroup (↥(Subgroup.zpowers x)) (↥K') = ⊥ := hregular x hx_ne
      have hx_eq :
          fixedPointSubgroup (↥(Subgroup.zpowers x)) (↥K') =
            (elementCentralizerIn K' (x : G')).subgroupOf K' := by
        simpa [hRK] using
          fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn K' R' hRK x
      have hx_cent_bot : elementCentralizerIn K' (x : G') = ⊥ := by
        apply (Subgroup.eq_bot_iff_card (H := elementCentralizerIn K' (x : G'))).2
        have hx_sub_bot : (elementCentralizerIn K' (x : G')).subgroupOf K' = ⊥ := by
          simpa [hx_eq] using hx_fix_bot
        have hcard_sub : Nat.card ((elementCentralizerIn K' (x : G')).subgroupOf K') = 1 := by
          simp [hx_sub_bot]
        rw [← natCard_subgroupOf_eq (elementCentralizerIn K' (x : G')) K' inf_le_left]
        exact hcard_sub
      have hcent_bot : subgroupCentralizerIn K' R' = ⊥ := by
        apply le_antisymm
        · intro y hy
          have hy' : y ∈ elementCentralizerIn K' (x : G') := by
            have hy_inf : y ∈ K' ⊓ Subgroup.centralizer (R' : Set G') := by
              simpa [subgroupCentralizerIn] using hy
            have hy_cent_x : y ∈ Subgroup.centralizer ({(x : G')} : Set G') := by
              rw [Subgroup.mem_centralizer_iff]
              intro z hz
              have hxy : (x : G') * y = y * (x : G') := by
                exact (Subgroup.mem_centralizer_iff.mp hy_inf.2) x x.2
              simpa [Set.mem_singleton_iff.mp hz] using hxy
            exact by
              show y ∈ K' ⊓ Subgroup.centralizer ({(x : G')} : Set G')
              exact ⟨hy_inf.1, hy_cent_x⟩
          simpa [hx_cent_bot] using hy'
        · exact bot_le
      rw [hfix_eq]
      simp [hcent_bot]
    have hp_cop_K : Nat.Coprime p (Nat.card K') := by
      refine (hp.coprime_iff_not_dvd).2 ?_
      intro hpdvdK
      have hone_fix : (1 : K') ∈ MulAction.fixedPoints R' K' := by
        simp [MulAction.mem_fixedPoints]
      obtain ⟨y, hy_fix, hy_ne_one'⟩ :=
        hR_pgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
          (α := K') hpdvdK hone_fix
      have hy_mem : y ∈ fixedPointSubgroup (↥R') (↥K') := by
        simpa [fixedPointSubgroup, FixedPoints.mem_subgroup] using
          MulAction.mem_fixedPoints.mp hy_fix
      have hy_bot : y ∈ (⊥ : Subgroup K') := by
        simpa [hfixKreg] using hy_mem
      exact hy_ne_one' (Subgroup.mem_bot.mp hy_bot).symm
    have hR_cyclic : IsCyclic R' := by
      obtain ⟨nR, hR_card_eq⟩ := (IsPGroup.iff_card (p := p) (G := R')).1 hR_pgroup
      by_cases hcyc : IsCyclic R'
      · exact hcyc
      have hnR_gt_one : 1 < nR := by
        have hnR_ne_zero : nR ≠ 0 := by
          intro hnR_zero
          have hcard_one : Nat.card R' = 1 := by simp [hR_card_eq, hnR_zero]
          exact hR_ne_bot ((Subgroup.eq_bot_iff_card (H := R')).2 hcard_one)
        have hnR_ne_one : nR ≠ 1 := by
          intro hnR_one
          have hcard_p : Nat.card R' = p := by simp [hR_card_eq, hnR_one]
          have hR_prime : Nat.Prime (Nat.card R') := by simpa [hcard_p] using hp
          exact hcyc (isCyclic_of_prime_card (α := R') hcard_p)
        exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hnR_ne_zero, hnR_ne_one⟩
      have hnR_le_two : nR ≤ 2 := by
        by_contra hnR_gt_two
        have htwo_le_nR : 2 ≤ nR := by omega
        have hpow_le : p ^ 2 ≤ Nat.card R' := by
          rw [hR_card_eq]
          exact Nat.pow_le_pow_right hp.pos htwo_le_nR
        obtain ⟨S, hS_card⟩ :=
          Sylow.exists_subgroup_card_pow_prime_of_le_card (G := R') (n := 2) (p := p) hp hR_pgroup hpow_le
        let SG : Subgroup G' := S.map R'.subtype
        have hSG_card : Nat.card SG = p ^ 2 := by
          simpa [SG, hS_card] using
            (Subgroup.card_map_of_injective (K := S) (f := R'.subtype) R'.subtype_injective)
        have hSG_ne_bot : SG ≠ ⊥ := by
          intro hbot
          have hcard_one : Nat.card SG = 1 := by simp [hbot]
          have hpow_eq_one : p ^ 2 = 1 := by
            rw [← hSG_card]
            exact hcard_one
          exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne' hpow_eq_one
        have hSG_lt : SG < R' := by
          refine lt_of_le_of_ne ?_ ?_
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact y.2
          · intro hEq
            have hcard_eq : Nat.card R' = p ^ 2 := by simpa [hEq] using hSG_card
            have hnR_eq_two : nR = 2 := by
              apply Nat.pow_right_injective hp.two_le
              calc
                p ^ nR = Nat.card R' := hR_card_eq.symm
                _ = p ^ 2 := hcard_eq
            exact hnR_gt_two (by simp [hnR_eq_two])
        have hSG_prime : Nat.Prime (Nat.card SG) := (hproper hSG_lt hSG_ne_bot).2.1
        have : Nat.Prime (p ^ 2) := by simpa [hSG_card] using hSG_prime
        exact Nat.Prime.not_prime_pow (x := p) (n := 2) (by decide : 2 ≤ 2) this
      have hR_card_p2 : Nat.card R' = p ^ 2 := by
        have hnR_eq_two : nR = 2 := by omega
        simp [hR_card_eq, hnR_eq_two]
      have hcommR : IsMulCommutative R' := by
        refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b => ?_
        exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq
          (p := p) (G := R') hR_card_p2).is_comm.comm a b
      let : IsMulCommutative R' := hcommR
      let : CommGroup R' := IsMulCommutative.instCommGroup
      let : Fact (IsPGroup p ↥R') := ⟨hR_pgroup⟩
      have hfix_top :
          (⨆ (a : R') (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥K')) = ⊤ := by
        simpa using proposition_1_16_a (G := ↥K') (A := R') p hp_cop_K hcyc
      have hfix_bot :
          (⨆ (a : R') (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) (↥K')) = ⊥ := by
        apply le_antisymm
        · refine iSup_le ?_
          intro a
          refine iSup_le ?_
          intro ha
          simp [hregular a ha]
        · exact bot_le
      let : Nontrivial ↥K' := (Subgroup.nontrivial_iff_ne_bot K').2 hK_ne_bot
      exact False.elim (top_ne_bot (hfix_top.symm.trans hfix_bot))
    by_cases hminv : ∀ N : Subgroup M', N.Normal → IsInvariant G' M' N → N ≠ ⊥ → N = ⊤
    ·
      obtain ⟨q, hq, hMq⟩ := theorem_3_10_case2_elementaryAbelian
        (G := G') (M := M') hnilM' hminv
      let : Fact q.Prime := ⟨hq⟩
      let : IsElementaryAbelian q M' := hMq
      have hcardM : Nat.card M' = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R' := by
        rcases exists_minimal_normal_le (G := G') K' hfrob'.normal hK_ne_bot with
          ⟨K₀, hK₀_normal, hK₀_le_K', hK₀_ne_bot, hK₀_min⟩
        let : K₀.Normal := hK₀_normal
        have hfixK₀_inv : IsInvariant G' M' (fixedPointSubgroup (↥K₀) M') :=
          theorem_3_10_fixedPointSubgroup_invariant_of_normal (A := K₀)
        have hfixK₀_normal : (fixedPointSubgroup (↥K₀) M').Normal := by
          have : IsMulCommutative M' := inferInstance
          refine { conj_mem := fun h hh g => ?_ }
          have hcomm : g * h * g⁻¹ = h := by
            simp [mul_comm, mul_assoc]
          simpa [hcomm] using hh
        by_cases hfixK₀_bot : fixedPointSubgroup (↥K₀) M' = ⊥
        · by_cases hK₀_eq_K' : K₀ = K'
          · subst hK₀_eq_K'
            have hK_min :
                ∀ N : Subgroup G', N.Normal → N ≤ K₀ → N ≠ ⊥ → N = K₀ := by
              intro N hN hNK hNne
              exact hK₀_min N hN hNK hNne
            exact theorem_3_10_case2_card_formula_rep_theory
              (G := G') (K := K₀) (R := R') (M := M') (q := q)
              hK_min hfrob' hsolvG' hcop' hfixK' hfixR' hR_cyclic hminv
          · have hK₀_lt_K' : K₀ < K' := lt_of_le_of_ne hK₀_le_K' hK₀_eq_K'
            let S : Subgroup G' := K₀ ⊔ R'
            have hdisj : Disjoint K₀ R' :=
              hfrob'.isComplement'.disjoint.mono hK₀_le_K' (le_refl R')
            have hcompS : (K₀.subgroupOf S).IsComplement' (R'.subgroupOf S) :=
              isComplement'_subgroupOf_sup_of_disjoint K₀ R' hdisj
            have hS_normal_K₀ : (K₀.subgroupOf S).Normal :=
              normal_subgroupOf_sup_of_conj_mem K₀ R' (by
                intro r h hH
                exact hK₀_normal.conj_mem h hH (r : G'))
            have hcard_mul_G' : Nat.card K' * Nat.card R' = Nat.card G' :=
              hfrob'.isComplement'.card_mul_card
            have hcardK₀_lt_cardK' : Nat.card K₀ < Nat.card K' :=
              natCard_lt_of_subgroup_lt hK₀_lt_K'
            have hR'_pos : 0 < Nat.card R' := Nat.card_pos (α := ↥R')
            have hS_lt_G' : Nat.card S < Nat.card G' := by
              calc
                Nat.card S = Nat.card K₀ * Nat.card R' := by
                  have hcardS_mul : Nat.card (K₀.subgroupOf S) * Nat.card (R'.subgroupOf S) = Nat.card S :=
                    hcompS.card_mul_card
                  simpa [natCard_subgroupOf_eq K₀ S le_sup_left,
                    natCard_subgroupOf_eq R' S le_sup_right] using hcardS_mul.symm
                _ < Nat.card K' * Nat.card R' :=
                  Nat.mul_lt_mul_of_pos_right hcardK₀_lt_cardK' hR'_pos
                _ = Nat.card G' := hcard_mul_G'
            have hcardS_dvd : Nat.card S ∣ Nat.card G' := Subgroup.card_subgroup_dvd_card S
            have hcopS : Nat.Coprime (Nat.card S) (Nat.card M') :=
              Nat.Coprime.of_dvd_left hcardS_dvd hcop'
            have hfixKsub : fixedPointSubgroup (↥(K₀.subgroupOf S)) M' = ⊥ := by
              calc
                fixedPointSubgroup (↥(K₀.subgroupOf S)) M' = fixedPointSubgroup (↥K₀) M' :=
                  theorem_3_10_fixedPointSubgroup_subgroupOf_eq (M := M') (S := S) (A := K₀) le_sup_left
                _ = ⊥ := hfixK₀_bot
            have hfixRsub_eq : fixedPointSubgroup (↥(R'.subgroupOf S)) M' = fixedPointSubgroup (↥R') M' :=
              theorem_3_10_fixedPointSubgroup_subgroupOf_eq (M := M') (S := S) (A := R') le_sup_right
            have hfixRsub : ∀ x : R'.subgroupOf S, x ≠ 1 →
                fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) M' = fixedPointSubgroup (↥(R'.subgroupOf S)) M' := by
              intro x hx
              have hxR' : ((x : S) : G') ∈ R' := x.2
              have hxR'_ne_one : (⟨(x : S).val, hxR'⟩ : R') ≠ 1 := by
                intro hx1
                apply hx
                ext
                simpa using congrArg Subtype.val hx1
              have hzp_le_S : Subgroup.zpowers ((x : S) : G') ≤ S :=
                (Subgroup.zpowers_le.2 hxR').trans (le_sup_right : R' ≤ S)
              calc
                fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) M'
                    = fixedPointSubgroup (↥((Subgroup.zpowers ((x : S) : G')).subgroupOf S)) M' := by
                      rw [← theorem_3_10_zpowers_subgroupOf_eq (S := S) x]
                _ = fixedPointSubgroup (↥(Subgroup.zpowers ((x : S) : G'))) M' :=
                  theorem_3_10_fixedPointSubgroup_subgroupOf_eq (M := M') (S := S)
                    (A := Subgroup.zpowers ((x : S) : G')) hzp_le_S
                _ = fixedPointSubgroup (↥R') M' := hfixR' ⟨(x : S).val, hxR'⟩ hxR'_ne_one
                _ = fixedPointSubgroup (↥(R'.subgroupOf S)) M' := hfixRsub_eq.symm
            have hcentK' : ∀ x : R', x ≠ 1 → elementCentralizerIn K' (x : G') = ⊥ :=
              (lemma_3_1 (K := K') (R := R') hK_ne_bot hR_ne_bot hfrob'.normal hfrob'.isComplement').mp hfrob'
            have hcentS : ∀ x : R'.subgroupOf S, x ≠ 1 → elementCentralizerIn (K₀.subgroupOf S) (x : S) = ⊥ := by
              intro x hx
              have hxR' : (x : G') ∈ R' := x.2
              have hxR'_ne_one : (⟨(x : G'), hxR'⟩ : R') ≠ 1 := by
                intro hx1; apply hx; ext; simpa using congrArg Subtype.val hx1
              have hcentK'_x : elementCentralizerIn K' ((x : G') : G') = ⊥ :=
                hcentK' ⟨(x : G'), hxR'⟩ hxR'_ne_one
              have hcentK₀_le : elementCentralizerIn K₀ ((x : G') : G') ≤ elementCentralizerIn K' ((x : G') : G') :=
                inf_le_inf hK₀_le_K' (le_refl _)
              have hcentK₀ : elementCentralizerIn K₀ ((x : G') : G') = ⊥ :=
                le_antisymm (hcentK₀_le.trans hcentK'_x.le) bot_le
              have hxS : (x : G') ∈ S := Subgroup.mem_sup_right hxR'
              calc
                elementCentralizerIn (K₀.subgroupOf S) (x : S)
                    = (elementCentralizerIn K₀ ((x : G') : G')).subgroupOf S := by
                      simpa using theorem_3_8_elementCentralizerIn_subgroupOf_eq S K₀ (x : G') hxS
                _ = (⊥ : Subgroup G').subgroupOf S := by rw [hcentK₀]
                _ = ⊥ := by simp
            have hK₀S_ne_bot : K₀.subgroupOf S ≠ ⊥ := by
              intro hbot
              apply hK₀_ne_bot
              have hcard_one : Nat.card K₀ = 1 := by
                calc
                  Nat.card K₀ = Nat.card (K₀.subgroupOf S) :=
                    (natCard_subgroupOf_eq K₀ S le_sup_left).symm
                  _ = 1 := by simp [hbot]
              refine (Subgroup.eq_bot_iff_card (H := K₀)).mpr ?_
              simpa [Nat.card_eq_fintype_card] using hcard_one
            have hR'S_ne_bot : R'.subgroupOf S ≠ ⊥ := by
              intro hbot
              apply hR_ne_bot
              have hcard_one : Nat.card R' = 1 := by
                calc
                  Nat.card R' = Nat.card (R'.subgroupOf S) :=
                    (natCard_subgroupOf_eq R' S le_sup_right).symm
                  _ = 1 := by simp [hbot]
              refine (Subgroup.eq_bot_iff_card (H := R')).mpr ?_
              simpa [Nat.card_eq_fintype_card] using hcard_one
            have hfrobS : IsFrobeniusGroupWithKernelComplement (K₀.subgroupOf S) (R'.subgroupOf S) :=
              ((lemma_3_1 (K := K₀.subgroupOf S) (R := R'.subgroupOf S) hK₀S_ne_bot hR'S_ne_bot
                hS_normal_K₀ hcompS).mpr hcentS)
            obtain ⟨_, _, hcard_eq, _⟩ := hind S (K₀.subgroupOf S) (R'.subgroupOf S) M'
              (by
                have : Nat.card S + Nat.card M' < Nat.card G' + Nat.card M' :=
                  Nat.add_lt_add_right hS_lt_G' (Nat.card M')
                exact this)
              hfrobS (by infer_instance) hnilM' hcopS hfixKsub hfixRsub
            calc
              Nat.card M' = Nat.card (fixedPointSubgroup (↥(R'.subgroupOf S)) M') ^ Nat.card (R'.subgroupOf S) :=
                hcard_eq
              _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card (R'.subgroupOf S) := by rw [hfixRsub_eq]
              _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R' := by
                rw [natCard_subgroupOf_eq R' S le_sup_right]
        · have hfixK₀_top : fixedPointSubgroup (↥K₀) M' = ⊤ := by
            exact hminv (fixedPointSubgroup (↥K₀) M') hfixK₀_normal hfixK₀_inv hfixK₀_bot
          have hK₀_ne_K' : K₀ ≠ K' := by
            intro hEq
            have hfixK'_top : fixedPointSubgroup (↥K') M' = ⊤ := by
              rw [← hEq]
              exact hfixK₀_top
            have htop_bot : (⊤ : Subgroup M') = ⊥ := hfixK'_top.symm.trans hfixK'
            exact (top_ne_bot : (⊤ : Subgroup M') ≠ ⊥) htop_bot
          have hK₀_lt_K' : K₀ < K' := lt_of_le_of_ne hK₀_le_K' hK₀_ne_K'
          have hK₀_fix_all : K₀ ≤ actionCentralizerIn (A := G') (G := M') (⊤ : Subgroup G') := by
            intro k hk
            rw [actionCentralizerIn]
            constructor
            · exact Subgroup.mem_top k
            · change k ∈ fixingSubgroupOf G' M' Set.univ
              rw [mem_fixingSubgroup_iff]
              intro m _hm
              have hmfix : m ∈ fixedPointSubgroup (↥K₀) M' := by
                simp [hfixK₀_top]
              rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hmfix
              exact hmfix ⟨k, hk⟩
          let qG : G' →* G' ⧸ K₀ := QuotientGroup.mk' K₀
          let : MulDistribMulAction (G' ⧸ K₀) M' :=
            theorem_3_10_quotientMulDistribMulActionOfTrivial
              (G := G') (M := M') hK₀_fix_all
          have hfrobQ : IsFrobeniusGroupWithKernelComplement
              (K'.map qG) (R'.map qG) := by
            exact lemma_3_2_b (K := K') (R := R') (N := K₀) hfrob' (by infer_instance)
              (by exact fun hle => hK₀_lt_K'.not_ge hle)
          have hltQG : Nat.card (G' ⧸ K₀) + Nat.card M' < Nat.card G' + Nat.card M' := by
            exact Nat.add_lt_add_right (natCard_quotient_lt_natCard_of_ne_bot K₀ hK₀_ne_bot) _
          have hcopQG : Nat.Coprime (Nat.card (G' ⧸ K₀)) (Nat.card M') := by
            exact Nat.Coprime.of_dvd_left (Subgroup.card_quotient_dvd_card (s := K₀)) hcop'
          have hfixKQ : fixedPointSubgroup (↥(K'.map qG)) M' = ⊥ := by
            calc
              fixedPointSubgroup (↥(K'.map qG)) M' = fixedPointSubgroup (↥K') M' :=
                theorem_3_10_fixedPointSubgroup_map_mk'_eq_of_trivial
                  (G := G') (M := M') (N := K₀) (A := K') hK₀_fix_all
              _ = ⊥ := hfixK'
          have hfixRQ_eq : fixedPointSubgroup (↥(R'.map qG)) M' = fixedPointSubgroup (↥R') M' := by
            exact theorem_3_10_fixedPointSubgroup_map_mk'_eq_of_trivial
              (G := G') (M := M') (N := K₀) (A := R') hK₀_fix_all
          have hfixRQ : ∀ x : R'.map qG, x ≠ 1 →
              fixedPointSubgroup (↥(Subgroup.zpowers (x : G' ⧸ K₀))) M' =
                fixedPointSubgroup (↥(R'.map qG)) M' := by
            intro x hx
            rcases x.2 with ⟨r, hrR, hrx⟩
            have hr_ne : (⟨r, hrR⟩ : R') ≠ 1 := by
              intro hr1
              apply hx
              apply Subtype.ext
              calc
                (x : G' ⧸ K₀) = qG r := hrx.symm
                _ = qG (1 : G') := congrArg qG (congrArg Subtype.val hr1)
                _ = 1 := by simp [qG]
            have hzp_eq : Subgroup.zpowers (x : G' ⧸ K₀) =
                (Subgroup.zpowers r).map qG := by
              ext y
              constructor
              · intro hy
                rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
                refine ⟨r ^ n, ?_, ?_⟩
                · exact Subgroup.zpow_mem_zpowers r n
                · calc
                    qG (r ^ n) = qG r ^ n := by simp [qG]
                    _ = (x : G' ⧸ K₀) ^ n := by rw [hrx]
              · intro hy
                rcases hy with ⟨z, hz, rfl⟩
                rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
                rw [map_zpow]
                rw [hrx]
                exact Subgroup.zpow_mem_zpowers (x : G' ⧸ K₀) n
            calc
              fixedPointSubgroup (↥(Subgroup.zpowers (x : G' ⧸ K₀))) M' =
                  fixedPointSubgroup (↥((Subgroup.zpowers r).map qG)) M' := by rw [hzp_eq]
              _ = fixedPointSubgroup (↥(Subgroup.zpowers r)) M' :=
                theorem_3_10_fixedPointSubgroup_map_mk'_eq_of_trivial
                  (G := G') (M := M') (N := K₀) (A := Subgroup.zpowers r) hK₀_fix_all
              _ = fixedPointSubgroup (↥R') M' := hfixR' ⟨r, hrR⟩ hr_ne
              _ = fixedPointSubgroup (↥(R'.map qG)) M' := hfixRQ_eq.symm
          have hmainQ := hind (G' ⧸ K₀) (K'.map qG) (R'.map qG) M' hltQG
            hfrobQ (by infer_instance) hnilM' hcopQG hfixKQ hfixRQ
          calc
            Nat.card M' = Nat.card (fixedPointSubgroup (↥(R'.map qG)) M') ^
                Nat.card (R'.map qG) := hmainQ.2.2.1
            _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card (R'.map qG) := by
              rw [hfixRQ_eq]
            _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R' := by
              have hcardR : Nat.card (R'.map qG) = Nat.card R' := by
                symm
                let f : R' → R'.map qG := fun r => ⟨qG r, ⟨r, r.2, rfl⟩⟩
                have hf_inj : Function.Injective f := by
                  intro a b hab
                  apply Subtype.ext
                  have habq : qG (a : G') = qG (b : G') := congrArg Subtype.val hab
                  have habK₀ : (a : G')⁻¹ * (b : G') ∈ K₀ := QuotientGroup.eq.mp habq
                  have habK' : (a : G')⁻¹ * (b : G') ∈ K' := hK₀_le_K' habK₀
                  have habR' : (a : G')⁻¹ * (b : G') ∈ R' := R'.mul_mem (R'.inv_mem a.2) b.2
                  have hab_one : (a : G')⁻¹ * (b : G') = 1 :=
                    (Subgroup.disjoint_def.mp hfrob'.isComplement'.disjoint) habK' habR'
                  have := congrArg (fun t : G' => (a : G') * t) hab_one
                  have hb_eq_a : (b : G') = a := by simpa [mul_assoc] using this
                  exact hb_eq_a.symm
                have hf_surj : Function.Surjective f := by
                  rintro ⟨x, hx⟩
                  rcases hx with ⟨r, hrR, rfl⟩
                  exact ⟨⟨r, hrR⟩, rfl⟩
                exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
              rw [hcardR]
      have hR_prime : Nat.Prime (Nat.card R') := by
        obtain ⟨nR, hR_card_eq⟩ := (IsPGroup.iff_card (p := p) (G := R')).1 hR_pgroup
        have hnR_eq_one : nR = 1 := by
          by_contra hnR_ne_one
          obtain ⟨P, hP_card⟩ := Sylow.exists_subgroup_card_pow_prime (G := R') p (n := 1) (by
            simpa using hpdvd)
          let PG : Subgroup G' := P.map R'.subtype
          have hPG_card : Nat.card PG = p := by
            simpa [PG, hP_card] using
              (Subgroup.card_map_of_injective (K := P) (f := R'.subtype) R'.subtype_injective)
          have hPG_ne_bot : PG ≠ ⊥ := by
            intro hbot
            have : Nat.card PG = 1 := by simp [hbot]
            have hp_one : p = 1 := by simpa [hPG_card] using this
            exact hp.ne_one hp_one
          have hPG_lt : PG < R' := by
            refine lt_of_le_of_ne ?_ ?_
            · intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              exact y.2
            · intro hEq
              have hcard_eq : Nat.card R' = p := by simpa [hEq] using hPG_card
              have hnR_eq_one' : nR = 1 := by
                apply Nat.pow_right_injective hp.two_le
                calc
                  p ^ nR = Nat.card R' := hR_card_eq.symm
                  _ = p ^ 1 := by simpa using hcard_eq
              exact hnR_ne_one hnR_eq_one'
          have hMP :
              Nat.card M' = Nat.card (fixedPointSubgroup (↥R') M') ^ p :=
            by simpa [hPG_card] using (hproper hPG_lt hPG_ne_bot).2.2
          have hfix_card_gt_one : 1 < Nat.card (fixedPointSubgroup (↥R') M') := by
            have hfix_ne_one : Nat.card (fixedPointSubgroup (↥R') M') ≠ 1 := by
              intro hfix_one
              have hM_one : Nat.card M' = 1 := by
                rw [hMP, hfix_one]
                simp
              exact
                (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial M')).ne'
                  hM_one
            exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
              ⟨(Nat.card_pos (α := ↥(fixedPointSubgroup (↥R') M'))).ne', hfix_ne_one⟩
          have hpow_eq : Nat.card (fixedPointSubgroup (↥R') M') ^ p =
              Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R' := hMP.symm.trans hcardM
          have hp_eq_card : p = Nat.card R' :=
            Nat.pow_right_injective hfix_card_gt_one hpow_eq
          have hnR_eq_one' : nR = 1 := by
            apply Nat.pow_right_injective hp.two_le
            calc
              p ^ nR = Nat.card R' := hR_card_eq.symm
              _ = p ^ 1 := by simp [hp_eq_card]
          exact hnR_ne_one hnR_eq_one'
        have hR_card_p : Nat.card R' = p := by simp [hR_card_eq, hnR_eq_one]
        simpa [hR_card_p] using hp
      refine ⟨hR_cyclic, hR_prime, hcardM, ?_⟩
      intro hcycFix
      let ρ : Representation (ZMod q) G' (Additive M') :=
        Theory.Representation.ofElementaryAbelianAction (A := G') (G := M') (p := q)
      have hq_cop_G : Nat.Coprime q (Nat.card G') := by
        obtain ⟨nq, hM_card⟩ := (IsElementaryAbelian.isPGroup q M').exists_card_eq
        have hnq_pos : 0 < nq := by
          have hM_gt : 1 < Nat.card M' := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
          rw [hM_card] at hM_gt
          cases nq with
          | zero => simp at hM_gt
          | succ nq => exact Nat.succ_pos _
        have hcop_pow : Nat.Coprime (Nat.card G') (q ^ nq) := by simpa [hM_card] using hcop'
        exact hcop_pow.symm.of_dvd_left (dvd_pow_self q (Nat.ne_of_gt hnq_pos))
      have hchar : ringChar (ZMod q) = 0 ∨
          (Nat.Prime (ringChar (ZMod q)) ∧ Nat.Coprime (ringChar (ZMod q)) (Nat.card G')) := by
        right
        constructor
        · simpa [ZMod.ringChar_zmod_n] using hq
        · simpa [ZMod.ringChar_zmod_n] using hq_cop_G
      have hfixRank : Module.rank (ZMod q) ↥(ρ.fixedSubspace R') = 1 := by
        have hfixEquiv := theorem_3_10_ofElementaryAbelianActionFixedSubspaceEquiv
          (A := G') (V := M') (p := q) R'
        have hfix_ne : fixedPointSubgroup (↥R') M' ≠ ⊥ :=
          theorem_3_10_case2_fixedPointSubgroup_ne_bot
            (G := G') (K := K') (R := R') (M := M') (p := q) hfrob' hcop' hfixK'
        let : Nontrivial ↥(fixedPointSubgroup (↥R') M') :=
          (Subgroup.nontrivial_iff_ne_bot _).2 hfix_ne
        have : IsElementaryAbelian q ↥(fixedPointSubgroup (↥R') M') :=
          { toIsMulCommutative := by infer_instance
            exponent_dvd_p := by
              refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
              intro x
              apply Subtype.ext
              simpa using
                (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (IsElementaryAbelian.exponent_dvd_p q M') x.1) }
        have hcard_fix : Nat.card (fixedPointSubgroup (↥R') M') = q :=
          theorem_3_10_natCard_eq_prime_of_cyclic_elementaryAbelian (p := q) hcycFix
        have hcard_add : Nat.card (Additive ↥(fixedPointSubgroup (↥R') M')) = q := by
          calc
            Nat.card (Additive ↥(fixedPointSubgroup (↥R') M')) =
                Nat.card ↥(fixedPointSubgroup (↥R') M') :=
              Nat.card_congr Additive.toMul
            _ = q := hcard_fix
        have hcard_sub : Nat.card ↥(ρ.fixedSubspace R') = q := by
          calc
            Nat.card ↥(ρ.fixedSubspace R') = Nat.card (Additive ↥(fixedPointSubgroup (↥R') M')) := by
              simpa [ρ] using Nat.card_congr hfixEquiv
            _ = q := hcard_add
        have hfin : Module.finrank (ZMod q) ↥(ρ.fixedSubspace R') = 1 := by
          have hnat := Module.natCard_eq_pow_finrank (K := ZMod q) (V := ↥(ρ.fixedSubspace R'))
          have hqpow : q ^ Module.finrank (ZMod q) ↥(ρ.fixedSubspace R') = q ^ 1 := by
            simpa [hcard_sub] using hnat.symm
          exact Nat.pow_right_injective hq.one_lt hqpow
        exact (Module.rank_eq_one_iff_finrank_eq_one
          (R := ZMod q) (M := ↥(ρ.fixedSubspace R'))).2 hfin
      have hρcent : ⁅K', K'⁆ ≤ ρ.centralizerIn K' :=
        theorem_3_5 K' R' ρ hfrob' (by infer_instance) hR_cyclic hR_prime hchar hfixRank
      intro g hg
      have hgcent : g ∈ ρ.centralizerIn K' := hρcent hg
      rw [actionCentralizerIn]
      constructor
      · exact (Subgroup.commutator_le_right (H₁ := K') (H₂ := K')) hg
      · rw [Representation.centralizerIn, Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup] at hgcent
        exact hgcent.2
    · push Not at hminv
      rcases hminv with ⟨N, hN_normal, hN_inv, hN_ne_bot, hN_ne_top⟩
      let : N.Normal := hN_normal
      let : IsInvariant G' M' N := hN_inv
      let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hN_ne_bot
      have hN_lt_top : N < ⊤ := lt_of_le_of_ne le_top hN_ne_top
      have hcardN_lt : Nat.card N < Nat.card M' := by
        simpa using natCard_lt_of_subgroup_lt hN_lt_top
      have hltN : Nat.card G' + Nat.card N < Nat.card G' + Nat.card M' := by
        exact Nat.add_lt_add_left hcardN_lt _
      have hcopK' : Nat.Coprime (Nat.card K') (Nat.card M') := by
        exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card K') hcop'
      have hcopN : Nat.Coprime (Nat.card G') (Nat.card N) := by
        exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card N) hcop'
      have hfixKN : fixedPointSubgroup (↥K') N = ⊥ :=
        theorem_3_10_fixedPointSubgroup_eq_bot_of_invariant_subgroup
          (G := G') (M := M') (A := K') (N := N) hfixK'
      have hfixRN :
          ∀ x : R', x ≠ 1 →
            fixedPointSubgroup (↥(Subgroup.zpowers (x : G'))) N = fixedPointSubgroup (↥R') N :=
        theorem_3_10_fixedPointSubgroup_eq_of_invariant_subgroup
          (G := G') (M := M') (R := R') (N := N) hfixR'
      have hmainN :=
        hind G' K' R' N hltN hfrob' hsolvG' (by infer_instance) hcopN hfixKN hfixRN
      have hR_prime : Nat.Prime (Nat.card R') := hmainN.2.1
      let : MulDistribMulAction G' (M' ⧸ N) :=
        quotientMulDistribMulAction (A := G') (G := M') N hN_inv
      let : MulAction.QuotientAction G' N := quotientAction_of_isInvariant (A := G') N hN_inv
      have hQ_nontrivial : Nontrivial (M' ⧸ N) :=
        (QuotientGroup.nontrivial_iff (G := M') (N := N)).2 hN_ne_top
      let : Nontrivial (M' ⧸ N) := hQ_nontrivial
      have hltQ : Nat.card G' + Nat.card (M' ⧸ N) < Nat.card G' + Nat.card M' := by
        exact Nat.add_lt_add_left (natCard_quotient_lt_natCard_of_ne_bot N hN_ne_bot) _
      have hcopQ : Nat.Coprime (Nat.card G') (Nat.card (M' ⧸ N)) := by
        exact Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card (s := N)) hcop'
      have hfixKQ : fixedPointSubgroup (↥K') (M' ⧸ N) = ⊥ :=
        theorem_3_10_fixedPointSubgroup_eq_bot_of_quotient
          (G := G') (M := M') (A := K') (N := N) hN_inv hsolvM' hcopK' hfixK'
      have hfixRQ :
          ∀ x : R', x ≠ 1 →
            fixedPointSubgroup (↥(Subgroup.zpowers (x : G'))) (M' ⧸ N) =
              fixedPointSubgroup (↥R') (M' ⧸ N) :=
        theorem_3_10_fixedPointSubgroup_eq_of_quotient
          (G := G') (M := M') (R := R') (N := N) hN_inv hsolvM' hcopR' hfixR'
      have hmainQ :=
        hind G' K' R' (M' ⧸ N) hltQ hfrob' hsolvG' (by infer_instance) hcopQ hfixKQ hfixRQ
      have hfix_card_factor :
          Nat.card (fixedPointSubgroup (↥R') M') =
            Nat.card (fixedPointSubgroup (↥R') N) *
              Nat.card (fixedPointSubgroup (↥R') (M' ⧸ N)) :=
        theorem_3_10_fixedPointSubgroup_card_factor
          (G := G') (M := M') (R := R') (N := N) hN_inv hsolvM' hcopR'
      refine ⟨hR_cyclic, hR_prime, ?_, ?_⟩
      · calc
          Nat.card M' = Nat.card (M' ⧸ N) * Nat.card N := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := M') (s := N))
          _ =
              Nat.card (fixedPointSubgroup (↥R') (M' ⧸ N)) ^ Nat.card R' *
                Nat.card (fixedPointSubgroup (↥R') N) ^ Nat.card R' := by
                  rw [hmainQ.2.2.1, hmainN.2.2.1]
          _ =
              (Nat.card (fixedPointSubgroup (↥R') (M' ⧸ N)) *
                Nat.card (fixedPointSubgroup (↥R') N)) ^ Nat.card R' := by
                  rw [Nat.mul_pow]
          _ =
              (Nat.card (fixedPointSubgroup (↥R') N) *
                Nat.card (fixedPointSubgroup (↥R') (M' ⧸ N))) ^ Nat.card R' := by
                  rw [Nat.mul_comm]
          _ = Nat.card (fixedPointSubgroup (↥R') M') ^ Nat.card R' := by
                rw [hfix_card_factor]
      · intro hcycFix
        let A : Subgroup G' := ⁅K', K'⁆
        let : MulDistribMulAction A M' := MulDistribMulAction.compHom M' A.subtype
        let : IsInvariant (↥R') M' N :=
          { invariant := fun a g => by
              change g ∈ N ↔ (a : G') • g ∈ N
              exact hN_inv.invariant (a : G') g }
        have hcycFixN : IsCyclic (fixedPointSubgroup (↥R') N) := by
          let C : Subgroup M' := fixedPointSubgroup (↥R') M'
          let eCN : (C.subgroupOf N) ≃* (N.subgroupOf C) :=
            { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
              invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
              left_inv := by intro x; rfl
              right_inv := by intro x; rfl
              map_mul' := by intro x y; rfl }
          have hcycNC : IsCyclic (N.subgroupOf C) := by infer_instance
          rw [fixedPointSubgroup_subtype_eq_local (A := ↥R') (G := M') N]
          exact
            isCyclic_of_surjective (f := eCN.symm.toMonoidHom) eCN.symm.surjective
        have hcycFixQ : IsCyclic (fixedPointSubgroup (↥R') (M' ⧸ N)) := by
          let C : Subgroup M' := fixedPointSubgroup (↥R') M'
          let q : M' →* M' ⧸ N := QuotientGroup.mk' N
          have hfixQ_eq : fixedPointSubgroup (↥R') (M' ⧸ N) = C.map q := by
            dsimp [C, q]
            rw [fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
              (G := M') (A := ↥R') hsolvM' hcopR' (π := ∅) (H := N) inferInstance]
          rw [hfixQ_eq]
          exact
            isCyclic_of_surjective (f := q.subgroupMap C)
              (MonoidHom.subgroupMap_surjective q C)
        let Gi : Fin 3 → Subgroup M' := fun i =>
          if hi0 : (i : ℕ) = 0 then
            ⊤
          else if hi1 : (i : ℕ) = 1 then
            N
          else
            ⊥
        let next : Fin 3 → Fin 3 := fun i =>
          if (i : ℕ) = 0 then 1 else 2
        have hseries : StabilizesNormalSeries (G := M') (A := A) Gi next := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · refine ⟨0, 2, ?_, ?_, ?_⟩
            · simp [Gi]
            · simp [Gi]
            · exact ⟨2, rfl⟩
          · intro i
            fin_cases i <;> simp [Gi, next]
          · intro i
            fin_cases i
            · simp [Gi]
            · simpa [Gi] using hN_normal
            · simp [Gi]
          · intro i
            fin_cases i
            · change IsInvariant A M' (⊤ : Subgroup M')
              refine { invariant := ?_ }
              intro a g
              constructor <;> intro _ <;> simp
            · change IsInvariant A M' N
              refine { invariant := ?_ }
              intro a g
              change g ∈ N ↔ (a : G') • g ∈ N
              exact hN_inv.invariant (a : G') g
            · change IsInvariant A M' (⊥ : Subgroup M')
              refine { invariant := ?_ }
              intro a g
              constructor
              · intro hg
                have hg' : g = 1 := by simpa using hg
                subst g
                rw [Subgroup.mem_bot]
                exact smul_one a
              · intro hg
                have hsmul : a • g = 1 := by simpa using hg
                have hg' : g = 1 := by
                  calc
                    g = a⁻¹ • (a • g) := (inv_smul_smul a g).symm
                    _ = 1 := by rw [hsmul]; exact smul_one a⁻¹
                simp [hg']
          · intro i a g hg
            fin_cases i
            ·
              have haFixQ :
                  (a : G') ∈ fixingSubgroupOf G' (M' ⧸ N) (Set.univ : Set (M' ⧸ N)) :=
                ((hmainQ.2.2.2 hcycFixQ) a.2).2
              have hmk_eq : QuotientGroup.mk' N ((a : G') • g) = QuotientGroup.mk' N g := by
                let gQ : M' ⧸ N := QuotientGroup.mk' N g
                have hfix : (a : G') • gQ = gQ :=
                  (mem_fixingSubgroup_iff
                    (M := G') (s := (Set.univ : Set (M' ⧸ N)))).1 haFixQ gQ (by trivial)
                simpa [gQ] using hfix
              have hdiv_mem : ((a : G') • g) / g ∈ N :=
                (QuotientGroup.eq_iff_div_mem (N := N) (x := (a : G') • g) (y := g)).1 hmk_eq
              change ((a : G') • g) * g⁻¹ ∈ N
              simpa only [div_eq_mul_inv] using hdiv_mem
            ·
              have haFixN : (a : G') ∈ fixingSubgroupOf G' N (Set.univ : Set N) :=
                ((hmainN.2.2.2 hcycFixN) a.2).2
              let gN : N := ⟨g, by simpa [Gi] using hg⟩
              have hfix : (a : G') • gN = gN :=
                (mem_fixingSubgroup_iff (M := G') (s := (Set.univ : Set N))).1 haFixN gN
                  (by trivial)
              have hEq : (a : G') • g = g := by
                have hEq' := congrArg Subtype.val hfix
                change (a : G') • g = g at hEq'
                exact hEq'
              have hmem_bot : (((a : G') • g) * g⁻¹) ∈ (⊥ : Subgroup M') := by
                simp [hEq]
              change ((a : G') • g) * g⁻¹ ∈ (⊥ : Subgroup M')
              exact hmem_bot
            ·
              have hg_one : g = 1 := by simpa [Gi] using hg
              subst g
              change ((a : G') • (1 : M')) * 1⁻¹ ∈ (⊥ : Subgroup M')
              simp
        have hker_eq :
            fixingSubgroupOf (↥A) M' (Set.univ : Set M') =
              (MulDistribMulAction.toMulAut (G := ↥A) (M := M')).ker :=
          fixingSubgroupOf_univ_eq_ker_toMulAut (A := ↥A) (G := M')
        have hker_normal : (fixingSubgroupOf (↥A) M' (Set.univ : Set M')).Normal := by
          rw [hker_eq]
          exact MonoidHom.normal_ker (MulDistribMulAction.toMulAut (G := ↥A) (M := M'))
        let π : Set Nat.Primes := {q | q.val ∣ Nat.card M'}
        have hpi : IsPiGroup π M' := by
          rw [IsPiGroup_iff π M']
          intro q hq
          exact hq
        have hquot_pi :
            IsPiGroup π (A ⧸ fixingSubgroupOf (↥A) M' (Set.univ : Set M')) :=
          lemma_1_9 (G := M') (A := A) π hsolvM' hpi (by
            exact ⟨(Fin 3 : Type), Gi, next, hseries⟩) hker_normal
        have hquot_card_one :
            Nat.card (A ⧸ fixingSubgroupOf (↥A) M' (Set.univ : Set M')) = 1 := by
          by_contra hcard_ne_one
          obtain ⟨q, hqprime, hqdvd⟩ :=
            Nat.exists_prime_and_dvd
              (n := Nat.card (A ⧸ fixingSubgroupOf (↥A) M' (Set.univ : Set M')))
              hcard_ne_one
          let q' : Nat.Primes := ⟨q, hqprime⟩
          have hq_dvd_M : q ∣ Nat.card M' :=
            (IsPiGroup_iff π (A ⧸ fixingSubgroupOf (↥A) M' (Set.univ : Set M'))).1 hquot_pi
              q' hqdvd
          have hq_dvd_A : q ∣ Nat.card A := by
            exact dvd_trans hqdvd
              (Subgroup.card_quotient_dvd_card (s := fixingSubgroupOf (↥A) M' Set.univ))
          have hq_dvd_G : q ∣ Nat.card G' := by
            exact dvd_trans hq_dvd_A (Subgroup.card_subgroup_dvd_card A)
          have hq_not_dvd_G : ¬ q ∣ Nat.card G' := by
            have hq_cop : Nat.Coprime q (Nat.card G') :=
              Nat.Coprime.of_dvd_left hq_dvd_M hcop'.symm
            exact (hqprime.coprime_iff_not_dvd).1 hq_cop
          exact hq_not_dvd_G hq_dvd_G
        have hfixA_top : fixingSubgroupOf (↥A) M' (Set.univ : Set M') = ⊤ := by
          exact (Subgroup.index_eq_one).1 (by simpa [Subgroup.index_eq_card] using hquot_card_one)
        intro a ha
        refine ⟨(Subgroup.commutator_le_right (H₁ := K') (H₂ := K')) ha, ?_⟩
        let aA : A := ⟨a, ha⟩
        have haFixA : aA ∈ fixingSubgroupOf (↥A) M' (Set.univ : Set M') := by
          simp [hfixA_top]
        exact (mem_fixingSubgroup_iff (M := G') (s := (Set.univ : Set M'))).2 <| by
          intro g _hg
          exact (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set M'))).1 haFixA g (by trivial)
  exact
    hP (Nat.card G + Nat.card M) G K R M rfl hfrob hsolvG hnilM hcop hfixK hfixR


public theorem CFSG.theorem_3_10_a
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvG : Group.IsSolvable G)
    (hnilM : Group.IsNilpotent M) (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    IsCyclic R ∧ Nat.Prime (Nat.card R) := by
  have hmain := theorem_3_10 (K := K) (R := R) (M := M) hfrob hsolvG hnilM hcop hfixK hfixR
  exact ⟨hmain.1, hmain.2.1⟩

public theorem CFSG.theorem_3_10_b
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvG : Group.IsSolvable G)
    (hnilM : Group.IsNilpotent M) (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    Nat.card M = Nat.card (fixedPointSubgroup (↥R) M) ^ Nat.card R := by
  exact (theorem_3_10 (K := K) (R := R) (M := M) hfrob hsolvG hnilM hcop hfixK hfixR).2.2.1

public theorem CFSG.theorem_3_10_c
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvG : Group.IsSolvable G)
    (hnilM : Group.IsNilpotent M) (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (hfixR :
      ∀ x : R, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    IsCyclic (fixedPointSubgroup (↥R) M) →
      ⁅K, K⁆ ≤ actionCentralizerIn (A := G) (G := M) K := by
  exact (theorem_3_10 (K := K) (R := R) (M := M) hfrob hsolvG hnilM hcop hfixK hfixR).2.2.2

end Theorem310
