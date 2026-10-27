module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenRefl
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Hyp
public import CFSG.LocalAnalysis.StandardType.GGTableBExcAdLinear
public import CFSG.RankThree.PartOne.KE.A1Centralizer
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
public import CFSG.LocalAnalysis.StandardType.GGRk1ConclExSix
import CFSG.RankThree.PartOne.S11c.G2Torus
import CFSG.LieType.Chevalley.CorootCoordinates
import CFSG.LocalAnalysis.StandardType.GGTBJF4RootsAux
import CFSG.LocalAnalysis.AGLEmbedding.SymThreeCentralExt
import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport
import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeOddProduct
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusRankOneNative

public section

namespace CFSG.StandardType

theorem card_ggOTwoPrime_eq_six_of_map_eq {U V : Type} [Group U] [Finite U] [Group V]
    (π : U →* V) (hπ : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {C : Subgroup U} {D : Subgroup V} (hmap : (ggOTwoPrime C).map π = D)
    (hD : Nonempty (↥D ≃* Equiv.Perm (Fin 3))) :
    Nat.card (ggOTwoPrime C) = 6 := by
  classical
  obtain ⟨e⟩ := hD
  let Q : Subgroup U := ggOTwoPrime C
  haveI : Finite ↥Q := Finite.of_injective Q.subtype Q.subtype_injective
  let f₀ : ↥Q →* ↥D := (π.comp Q.subtype).codRestrict D fun x =>
    le_of_eq hmap (Subgroup.mem_map_of_mem (K := ggOTwoPrime C) π x.2)
  have hf₀ : Function.Surjective f₀ := by
    intro d
    obtain ⟨q, hq, hqd⟩ := Subgroup.mem_map.mp (le_of_eq hmap.symm d.2)
    exact ⟨⟨q, hq⟩, Subtype.ext hqd⟩
  let f : ↥Q →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp f₀
  have hf_apply : ∀ q : ↥Q, f q = e (f₀ q) := fun _ => rfl
  have hf : Function.Surjective f := by
    intro σ
    obtain ⟨d, rfl⟩ := e.surjective σ
    obtain ⟨q, rfl⟩ := hf₀ d
    exact ⟨q, hf_apply q⟩
  have hfk : f.ker = π.ker.subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, hf_apply q, MulEquiv.map_eq_one_iff e,
      Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hdvd : Nat.card f.ker ∣ Nat.card π.ker := by
    rw [hfk]
    exact Subgroup.card_comap_dvd_of_injective π.ker Q.subtype Q.subtype_injective
  have hoddker : Odd (Nat.card f.ker) := Odd.of_dvd_nat hodd hdvd
  have hc : ∀ k ∈ f.ker, ∀ q : ↥Q, k * q = q * k := by
    intro k hk q
    have hk0 : f₀ k = 1 := by
      have h : e (f₀ k) = 1 := by
        have hk' := hk
        rw [MonoidHom.mem_ker, hf_apply k] at hk'
        exact hk'
      exact (MulEquiv.map_eq_one_iff e).mp h
    have hkπ : (k : U) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hk0
    have hkc : (k : U) ∈ Subgroup.center U := hπ hkπ
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hkc (q : U)).symm)
  obtain ⟨T, hTn, ⟨eT⟩, hTi⟩ :=
    CFSG.AGLEmbedding.SymThreeCentralExt.exists_normal_symThree f hf hc hoddker
  haveI : T.Normal := hTn
  have hTodd : Odd T.index :=
    Nat.not_even_iff_odd.mp fun he => hTi (even_iff_two_dvd.mp he)
  have hle : ggOTwoPrime C ≤ T.map Q.subtype := by
    change Subgroup.closure {y | y ∈ C ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1} ≤ T.map Q.subtype
    rw [Subgroup.closure_le (T.map Q.subtype)]
    rintro y ⟨hyC, k, hyk⟩
    let q : ↥Q := ⟨y, Subgroup.subset_closure ⟨hyC, k, hyk⟩⟩
    have hqpow : q ^ (2 ^ k) = 1 := Subtype.ext hyk
    have hxpow : (q : ↥Q ⧸ T) ^ (2 ^ k) = 1 := by
      rw [← QuotientGroup.mk_pow, hqpow, QuotientGroup.mk_one]
    have hord1 : orderOf (q : ↥Q ⧸ T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxpow
    have hord2 : orderOf (q : ↥Q ⧸ T) ∣ T.index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hord : orderOf (q : ↥Q ⧸ T) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hTodd))
        hord1 hord2
    have hq1 : (q : ↥Q ⧸ T) = 1 := orderOf_eq_one_iff.mp hord
    have hqT : q ∈ T := (QuotientGroup.eq_one_iff q).mp hq1
    exact Subgroup.mem_map.mpr ⟨q, hqT, rfl⟩
  have htop : T = ⊤ := by
    refine (Subgroup.eq_top_iff' T).mpr fun q => ?_
    obtain ⟨q', hq'T, hq'eq⟩ := Subgroup.mem_map.mp (hle q.2)
    have hq' : q' = q := Subtype.ext hq'eq
    rwa [hq'] at hq'T
  have hcardT : Nat.card ↥Q = Nat.card ↥T := by rw [htop, Subgroup.card_top]
  have hcardS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  calc Nat.card (ggOTwoPrime C) = Nat.card ↥Q := rfl
    _ = Nat.card ↥T := hcardT
    _ = Nat.card (Equiv.Perm (Fin 3)) := Nat.card_congr eT.toEquiv
    _ = 6 := hcardS

namespace TwE6ThreeRootGen

section WeylStab

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

private theorem pow_three_eq_one_of_forall_fix
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {w : WeylGroup Tag.E6}
    (hfix : ∀ x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
      ExcSplitRootGen.excRefl (p := 3) γ x = x → adAct Tag.E6 3 w x = x)
    (hγw : w • γ = γ) : w ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstep : ∀ x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
      adAct Tag.E6 3 w (adAct Tag.E6 3 w x - x) = adAct Tag.E6 3 w x - x := by
    intro x hx
    have hy : adAct Tag.E6 3 w x - x ∈ NoOffRest.hypE6 :=
      AddSubgroup.sub_mem NoOffRest.hypE6 (NoOffRest.adAct_mem_hypE6 w hx) hx
    have hpair := adAct_pairing_smul (p := 3) w x γ
    rw [hγw] at hpair
    have hzero : (∑ j, (γ j : ZMod 3) * (adAct Tag.E6 3 w x - x) j) = 0 := by
      calc (∑ j, (γ j : ZMod 3) * (adAct Tag.E6 3 w x - x) j)
          = ∑ j, ((γ j : ZMod 3) * adAct Tag.E6 3 w x j - (γ j : ZMod 3) * x j) :=
            Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply, mul_sub]
        _ = (∑ j, (γ j : ZMod 3) * adAct Tag.E6 3 w x j) - ∑ j, (γ j : ZMod 3) * x j :=
            Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun j => (γ j : ZMod 3) * adAct Tag.E6 3 w x j)
              (g := fun j => (γ j : ZMod 3) * x j)
        _ = 0 := by rw [hpair, sub_self]
    exact hfix _ hy
      ((ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ _).mpr hzero)
  have hpow : ∀ x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
      adAct Tag.E6 3 (w ^ 3) x = x := fun x hx =>
    NoOffRest.adAct_pow_three_eq (hstep x hx) (by decide)
  refine NoOffRest.hypPerm_injective ?_
  rw [map_one]
  apply Equiv.ext
  intro x
  exact Subtype.ext (by
    show adAct Tag.E6 3 (w ^ 3) x.1 = x.1
    exact hpow x.1 x.2)

private theorem eq_one_of_smul_eq_self
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {w : WeylGroup Tag.E6}
    (hfix : ∀ x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
      ExcSplitRootGen.excRefl (p := 3) γ x = x → adAct Tag.E6 3 w x = x)
    (hγw : w • γ = γ) : w = 1 := by
  have hw3 : w ^ 3 = 1 := pow_three_eq_one_of_forall_fix hγ hfix hγw
  by_contra hw1
  have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hA : IsElemAbelian 3 (Subgroup.zpowers w) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨k, hk⟩ := a.2
      obtain ⟨l, hl⟩ := b.2
      show (a : WeylGroup Tag.E6) * b = b * a
      rw [← hk, ← hl]
      exact zpow_mul_comm w k l
    · obtain ⟨k, rfl⟩ := ha
      calc (w ^ k) ^ 3 = (w ^ 3) ^ k := by
            rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast w 3, ← zpow_mul, mul_comm]
        _ = 1 := by rw [hw3, one_zpow]
  have hA1 : Subgroup.zpowers w ≠ ⊥ := fun h => hw1 (Subgroup.zpowers_eq_bot.mp h)
  have hcardS : Nat.card {x : NoOffRest.hypE6 //
      ExcSplitRootGen.excRefl (p := 3) γ ↑x = ↑x} = 3 ^ 4 := by
    have hmain := card_fix_excRefl_mul_three
      (V := (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) (Or.inr rfl) hγ
    have he : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) ∧
          ExcSplitRootGen.excRefl (p := 3) γ x = x} =
        Nat.card {x : NoOffRest.hypE6 // ExcSplitRootGen.excRefl (p := 3) γ ↑x = ↑x} :=
      Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun x => x ∈ NoOffRest.hypE6)
        (fun x => ExcSplitRootGen.excRefl (p := 3) γ x = x)).symm
    have hcardH : Nat.card (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) = 3 ^ 5 :=
      NoOffRest.card_hypE6
    rw [he, hcardH] at hmain
    have h35 : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by norm_num
    rw [h35] at hmain
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmain
  have hinj : Nat.card {x : NoOffRest.hypE6 //
        ExcSplitRootGen.excRefl (p := 3) γ ↑x = ↑x} ≤
      Nat.card {x : NoOffRest.hypE6 //
        ∀ a ∈ Subgroup.zpowers w, NoOffRest.hypPerm a x = x} := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) (fun x x' hxx => ?_)
    · intro a ha
      obtain ⟨k, rfl⟩ := ha
      rw [map_zpow]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
        (Subtype.ext (hfix x.1.1 x.1.2 x.2)) k
    · exact Subtype.ext (by simpa using hxx)
  have hno := NoOffRest.actNoOffender_hypPerm_E6 (Subgroup.zpowers w) hA hA1
  rw [Nat.card_zpowers, hord, NoOffRest.card_hypE6] at hno
  have hge : (3 : ℕ) ^ 4 ≤ Nat.card {x : NoOffRest.hypE6 //
      ∀ a ∈ Subgroup.zpowers w, NoOffRest.hypPerm a x = x} := hcardS ▸ hinj
  have h35 : (3 : ℕ) ^ 5 = 3 * 3 ^ 4 := by norm_num
  rw [h35] at hno
  exact absurd hno (not_lt.mpr (Nat.mul_le_mul_left 3 hge))

theorem eq_one_or_eq_rootReflection_of_forall_fix
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {w : WeylGroup Tag.E6}
    (hw : ∀ x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
      ExcSplitRootGen.excRefl (p := 3) γ x = x → adAct Tag.E6 3 w x = x) :
    w = 1 ∨ w = rootReflection γ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpm : w • γ = γ ∨ w • γ = -γ := by
    refine eq_or_eq_neg_of_forall_mem_sum_eq_zero (Or.inr rfl) hγ (IsRoot.smul hγ w) ?_
    intro x hx hxγ
    have hfx : adAct Tag.E6 3 w x = x :=
      hw x hx ((ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x).mpr hxγ)
    have hpair := adAct_pairing_smul (p := 3) w x γ
    rw [hfx, hxγ] at hpair
    exact hpair
  rcases hpm with hγw | hγw
  · exact Or.inl (eq_one_of_smul_eq_self hγ hw hγw)
  · refine Or.inr ?_
    have hfix' : ∀ x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
        ExcSplitRootGen.excRefl (p := 3) γ x = x →
          adAct Tag.E6 3 (w * rootReflection γ) x = x := by
      intro x hx hxr
      rw [adAct_mul]
      rw [show adAct Tag.E6 3 (rootReflection γ) x = x from hxr]
      exact hw x hx hxr
    have hsm : (w * rootReflection γ) • γ = γ := by
      rw [mul_smul, rootReflection_smul_self hγ, smul_neg, hγw, neg_neg]
    have h1 : w * rootReflection γ = 1 := eq_one_of_smul_eq_self hγ hfix' hsm
    calc w = w * rootReflection γ * rootReflection γ := by
          rw [mul_assoc, rootReflection_mul_self hγ, mul_one]
      _ = rootReflection γ := by rw [h1, one_mul]

theorem eq_one_or_eq_rootReflection_of_forall_fix_of_V
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) {w : WeylGroup Tag.E6}
    (hw : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) γ x = x → adAct Tag.E6 3 w x = x) :
    w = 1 ∨ w = rootReflection γ := by
  rcases hV with rfl | rfl
  · exact eq_one_or_eq_rootReflection_of_forall_fix hγ fun x _ hx => hw x (Set.mem_univ x) hx
  · exact eq_one_or_eq_rootReflection_of_forall_fix hγ hw

end WeylStab

section TorusTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE

theorem mem_rootRankOneGroup_of_pow_two_pow_eq_one
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootRankOneGroup τ L γ) {k : ℕ}
    (hk : y ^ 2 ^ k = 1) : y ∈ rootRankOneGroup τ L γ := by
  classical
  change y ∈ ((torusGroup τ L ⊔ rootRankOneGroup τ L γ : Subgroup (ModGL τ L)) :
    Set (ModGL τ L)) at hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
    (rootRankOneGroup τ L γ) (torusGroup_le_normalizer_rootRankOneGroup hγ)] at hy
  rcases hy with ⟨t, ht, d, hd, rfl⟩
  obtain ⟨u, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  change rootDiagUnit τ u * d ∈ rootRankOneGroup τ L γ
  change (rootDiagUnit τ u * d) ^ 2 ^ k = 1 at hk
  obtain ⟨μ, hμ⟩ : ∃ μ : Lˣ, μ ^ 2 = rootChar u γ := by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (rootChar u γ : L) (n := 2) (by norm_num)
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, zero_pow (by norm_num)] at hx
      exact (rootChar u γ).ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx])⟩
  set m : Fin τ.rank → ℤ := fun i => corootPair γ (Pi.single i 1) with hm
  set h : ModGL τ L := rootSL2 τ L γ (HSL μ) with hh
  have hQ : h ∈ rootRankOneGroup τ L γ := by
    rw [hh]
    exact ⟨HSL μ, rfl⟩
  have hdiag : h = rootDiagUnit τ (fun i => μ ^ m i) := by
    rw [hh]
    exact CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hγ m
      (fun δ hδ => CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum hγ δ) μ
  set b : Fin τ.rank → Lˣ := u * (fun i => μ ^ m i)⁻¹ with hb
  have ht' : rootDiagUnit τ u * h⁻¹ = rootDiagUnit τ b := by
    rw [hdiag, hb, rootDiagUnit_inv, ← rootDiagUnit_mul]
  have hcc : corootPair γ γ = 2 := CFSG.StandardType.ggTBJ_corootPair_self τ hγ
  have hb1val : rootChar b γ = 1 := by
    have hf : rootChar (fun i => μ ^ m i) γ = μ ^ 2 := by
      rw [CFSG.StandardType.LangRat.j4e_rootChar_corootTuple hγ μ γ, hcc]
      rfl
    have hsplit : rootChar b γ =
        rootChar u γ * (rootChar (fun i => μ ^ m i) γ)⁻¹ := by
      simp only [hb, rootChar, Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow,
        Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [hsplit, hf, ← hμ, mul_inv_cancel]
  have hcomm : ∀ x ∈ rootRankOneGroup τ L γ,
      (rootDiagUnit τ u * h⁻¹) * x = x * (rootDiagUnit τ u * h⁻¹) := by
    intro x hx
    obtain ⟨A, rfl⟩ := hx
    have hconj : (rootDiagUnit τ u * h⁻¹) * rootSL2 τ L γ A *
        (rootDiagUnit τ u * h⁻¹)⁻¹ = rootSL2 τ L γ A := by
      rw [ht', rootDiagUnit_conj_rootSL2 b hγ A, hb1val, conjSL_diagUnitOne_one]
    calc (rootDiagUnit τ u * h⁻¹) * rootSL2 τ L γ A
        = ((rootDiagUnit τ u * h⁻¹) * rootSL2 τ L γ A *
            (rootDiagUnit τ u * h⁻¹)⁻¹) * (rootDiagUnit τ u * h⁻¹) := by group
      _ = rootSL2 τ L γ A * (rootDiagUnit τ u * h⁻¹) := by rw [hconj]
  have hydecomp : rootDiagUnit τ u * d = (rootDiagUnit τ u * h⁻¹) * (h * d) := by
    group
  rw [hydecomp] at hk
  have hq : h * d ∈ rootRankOneGroup τ L γ := mul_mem hQ hd
  have hpow : ((rootDiagUnit τ u * h⁻¹) * (h * d)) ^ 2 ^ k =
      (rootDiagUnit τ u * h⁻¹) ^ 2 ^ k * (h * d) ^ 2 ^ k :=
    Commute.mul_pow (show Commute _ _ from hcomm (h * d) hq) (2 ^ k)
  have hzQ : (rootDiagUnit τ u * h⁻¹) ^ 2 ^ k ∈ rootRankOneGroup τ L γ := by
    have h1 : (rootDiagUnit τ u * h⁻¹) ^ 2 ^ k * (h * d) ^ 2 ^ k = 1 := by
      rw [← hpow]
      exact hk
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem hq (2 ^ k))
  obtain ⟨C, hC⟩ := hzQ
  have hzcomm : ∀ x ∈ rootRankOneGroup τ L γ,
      rootSL2 τ L γ C * x = x * rootSL2 τ L γ C := by
    intro x hx
    rw [hC]
    exact Commute.pow_left (show Commute _ _ from hcomm x hx) (2 ^ k)
  have hCcenter : C ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) L) := by
    rw [Subgroup.mem_center_iff]
    intro A
    have h1 : rootSL2 τ L γ (C * A) = rootSL2 τ L γ (A * C) := by
      rw [map_mul, map_mul]
      exact hzcomm (rootSL2 τ L γ A) ⟨A, rfl⟩
    exact (rootSL2_injective_of_field (K := L) γ h1).symm
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hCcenter
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hsq : (r - 1) ^ 2 = 0 := by
    linear_combination hr2 - h2 * (r - 1)
  have hr1 : r = 1 := by
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 hsq)
  have hC1 : C = 1 := by
    apply Subtype.ext
    rw [← hA, hr1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]
  have ht'pow : (rootDiagUnit τ u * h⁻¹) ^ 2 ^ k = 1 := by
    rw [← hC, hC1, map_one]
  have hbpow : b ^ 2 ^ k = 1 := by
    apply rootDiagUnit_injective
    rw [← rootDiagUnit_pow, ← ht', ht'pow, rootDiagUnit_one]
  have hbone : b = 1 := by
    funext i
    apply Units.ext
    have hbi : ((b i : L)) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : Fin τ.rank → Lˣ => ((x i : Lˣ) : L)) hbpow
      simpa using this
    have hsub : ((b i : L) - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, hbi, one_pow, sub_self]
    have hzero : (b i : L) - 1 = 0 :=
      (pow_eq_zero_iff (by positivity : (2 : ℕ) ^ k ≠ 0)).1 hsub
    exact sub_eq_zero.1 hzero
  have ht'1 : rootDiagUnit τ u * h⁻¹ = 1 := by
    rw [ht', hbone, rootDiagUnit_one]
  have ht_eq : rootDiagUnit τ u = h := by
    have h1 : rootDiagUnit τ u * h⁻¹ = 1 := ht'1
    rwa [mul_inv_eq_one] at h1
  rw [ht_eq]
  exact mul_mem hQ hd

end TorusTwo

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
  (nonempty_mulEquiv_perm_three_of_card_two)

theorem adAct_eq_of_mem_rootCharStabilizer {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {x : Fin Tag.E6.rank → ZMod 3} {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizer (zetaVec (τ := Tag.E6) ζ hζ x)) :
    adAct Tag.E6 3 w x = x := by
  have hw' : w⁻¹ ∈ rootCharStabilizer (zetaVec (τ := Tag.E6) ζ hζ x) :=
    (rootCharStabilizerSubgroup (zetaVec (τ := Tag.E6) ζ hζ x)).inv_mem hw
  funext i
  have h := hw' (Pi.single i 1)
  rw [NoOffE8Five.rootChar_zetaVec, NoOffE8Five.rootChar_zetaVec] at h
  have h2 := Multiplicative.ofAdd.injective
    (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ h)
  change ∑ j, (((w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j : ℤ) : ZMod 3) * x j = x i
  rw [h2]
  simp [Pi.single_apply]

section Two


theorem mem_ggKGTwJ_of_pow_two_pow_eq_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {c : twistedE6RootGroup K σ}
    (hc : (c : ModGL TwistTag.E6.tag K) ∈ Subgroup.centralizer
      (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x}))
    {k : ℕ} (hk : c ^ 2 ^ k = 1) : c ∈ ggKGTwJ F γ := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  let a : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
      ExcSplitRootGen.excRefl (p := 3) γ x = x} → Fin TwistTag.E6.tag.rank →
        (AlgebraicClosure K)ˣ := fun x => zetaVec (τ := TwistTag.E6.tag) ζ hζ x.1
  have hfam : ggKGTwY F c ∈ familyCentralizer TwistTag.E6.tag (AlgebraicClosure K) a :=
    ggKGTwJ_mem_familyCentralizer_three F hζ ht hc
  obtain ⟨w, hwstab, m, hm, hc_eq⟩ :=
    familyCentralizer_le_mul TwistTag.E6.tag (AlgebraicClosure K) a hfam
  have hfker : familyKernel a = {γT, -γT} := familyKernel_zetaVec_eq hζ hζo hV hγ
  have hwfix : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) γ x = x →
      adAct Tag.E6 3 w x = x :=
    fun x hx hxr => adAct_eq_of_mem_rootCharStabilizer hζ hζo (hwstab ⟨x, hx, hxr⟩)
  have hQ : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∈
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT := by
    rcases eq_one_or_eq_rootReflection_of_forall_fix_of_V hV hγ hwfix with h | h
    · have h1 : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w = 1 := by
        subst h
        exact canonicalRep_one _ _
      rw [h1]
      exact one_mem _
    · obtain ⟨r, hrJ, hr⟩ := ggKGTwJ_weyl hK hσ F hv hγ
      have h1 : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w =
          ggKGTwY F r := by
        subst h
        exact hr.symm
      rw [h1]
      exact (TwE6PlusRootGen.mem_ggKGTwJ_iff hσ F).1 hrJ
  have hmTQ : m ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) ⊔
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT := by
    rw [familyGroup, hfker] at hm
    have hle : rootSpan TwistTag.E6.tag (AlgebraicClosure K)
        ({γT, -γT} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ≤
          rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT := by
      rw [CFSG.LieType.HighestRoot.rootSpan_pair_eq γT,
        ← (CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_torus_transport
          TwistTag.E6.tag (AlgebraicClosure K) hγT).1]
    exact sup_le_sup_left hle _ hm
  have hyTQ : ggKGTwY F c ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) ⊔
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT := by
    rw [hc_eq]
    exact mul_mem hmTQ (le_sup_right (a := torusGroup TwistTag.E6.tag (AlgebraicClosure K)) hQ)
  have hy2 : (ggKGTwY F c) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  exact (TwE6PlusRootGen.mem_ggKGTwJ_iff hσ F).2
    (mem_rootRankOneGroup_of_pow_two_pow_eq_one hγT hyTQ hy2)

theorem ggOTwoPrime_centralizer_eq_ggKGTwJ
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggOTwoPrime ((Subgroup.centralizer
        (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})).comap
        (twistedE6RootGroup K σ).subtype) = ggKGTwJ F γ := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨e₁⟩ := nonempty_ggKGTwJ_mulEquiv_SL2 hK hσ F hv hγ
  exact OmPlusFrame.ggOTwoPrime_eq_of_le (ggKGTwJ_le_centralizer_three (V := V) F hζ hζo ht hγ)
    (OmPlusFrame.le_closure_two_of_mulEquiv e₁
      (OmPlusFrame.sl2_closure_sq_eq_one CharTwo.two_eq_zero))
    (fun c hc k hk => mem_ggKGTwJ_of_pow_two_pow_eq_one hK hσ F hv hζ hζo ht hV hγ hc hk)

end Two

section TwoCount


theorem exists_map_ggOTwoPrime_ggHypCent_eq_ggKGTwJ {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 ↥(twistedE6RootGroup K σ)
      ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) L' ψ A)
    (hodd : Odd (Nat.card ψ.ker)) {n₀ : L'}
    (hn₀ : MulAut.conj n₀ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hrefl : GGIsReflection 3 (ggConjAut A hn₀)) :
    ∃ (E : Subgroup (twistedE6RootGroup K σ)) (F : TwE6Frame K σ n 3 E)
      (γ : Fin Tag.E6.rank → ℤ), ExcIsLongest TwistTag.E6.tag F.v ∧ IsRoot Tag.E6 γ ∧
      (ggOTwoPrime (ggHypCent A n₀)).map ((twistedE6RootGroup K σ).subtype.comp ψ) =
        (ggKGTwJ F γ).map (twistedE6RootGroup K σ).subtype := by
  classical
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  obtain ⟨ζ, Fr, hζ, hζo, hFr⟩ := exists_zeta_frobenius_twE6Three hK
  obtain ⟨g, κ, t, T, hg, hglang, hκinj, hκrange, ht, hconj, -, -, -, hinner⟩ :=
    exists_frame_torus (L' := L') (ψ₀ := ψ) (A := A) (Fr := Fr) (ζ := ζ)
      hn hK σ hσ h3 hFr hζ hζo hψ hker hperf hA hAI h5 hsc
  obtain ⟨E, F, -, hFv, hFg⟩ :=
    exists_twE6Frame (K := K) (σ := σ) (n := n) (p := 3) (Fr := Fr)
      (v := CFSG.HardMathSupport.Lang.E6Descent.twE6W0) (g₀ := g) hFr hg hglang
  have hv : ExcIsLongest TwistTag.E6.tag F.v := by
    rw [hFv]
    exact excIsLongest_twE6W0
  have htF := baseChange_twE6Three hζ ht hFg
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    coordSet_eq_univ_or_hypE6_twE6Three hκrange
  obtain ⟨⟨γ, hγ⟩, hγact'⟩ := E6ThreeRootGen.exists_root_of_isReflection_frame hκinj hVmem hV
    hinner (ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n₀, rfl⟩) hn₀) hrefl
  have hγact : ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hn₀ a)) =
      ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) := hγact'
  have hcomm : ∀ (a : MulAut L') (ha : a ∈ A), MulAut.conj n₀ * a = a * MulAut.conj n₀ ↔
      ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ ⟨a, ha⟩)) =
        Multiplicative.toAdd (κ ⟨a, ha⟩) := by
    intro a ha
    rw [← hγact ⟨a, ha⟩]
    constructor
    · intro h
      rw [show ggConjAut A hn₀ ⟨a, ha⟩ = ⟨a, ha⟩ from
        Subtype.ext (by rw [ggConjAut_apply, h, mul_inv_cancel_right])]
    · intro h
      have h1 : ggConjAut A hn₀ ⟨a, ha⟩ = ⟨a, ha⟩ := hκinj (Multiplicative.toAdd.injective h)
      have h2 := congrArg Subtype.val h1
      rw [ggConjAut_apply] at h2
      calc MulAut.conj n₀ * a = MulAut.conj n₀ * a * (MulAut.conj n₀)⁻¹ * MulAut.conj n₀ := by
            group
        _ = a * MulAut.conj n₀ := by rw [h2]
  let ι := {a : MulAut L' // a ∈ A ∧ MulAut.conj n₀ * a = a * MulAut.conj n₀}
  let α : ι → MulAut L' := fun i => i.1
  let s : ι → ModGL TwistTag.E6.tag K := fun i => t (Multiplicative.toAdd (κ ⟨i.1, i.2.1⟩))
  let β : ι → MulAut (ModGL TwistTag.E6.tag K) := fun i => MulAut.conj (s i)
  let R := twistedE6RootGroup K σ
  let π : L' →* ModGL TwistTag.E6.tag K := R.subtype.comp ψ
  have hπker : π.ker = ψ.ker := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one]
  have hπc : π.ker ≤ Subgroup.center L' := by rw [hπker]; exact hker
  have hπo : Odd (Nat.card π.ker) := by rw [hπker]; exact hodd
  have hcompat : ∀ i x, π (α i x) = β i (π x) := fun i x => hconj ⟨i.1, i.2.1⟩ x
  have hmap := ggOTwoPrime_map_fixedFamily_of_central_odd_kernel π hπc hπo ⊤ α β hcompat
  have hHyp : ggHypCent A n₀ =
      ⊤ ⊓ ⨅ i, MonoidHom.eqLocus (α i).toMonoidHom (MonoidHom.id L') := by
    ext l
    rw [top_inf_eq, Subgroup.mem_iInf]
    constructor
    · intro h i
      exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp h i.1) i.2
    · intro h
      exact Subgroup.mem_iInf.mpr fun a => Subgroup.mem_iInf.mpr fun ha => h ⟨a, ha⟩
  have hπrange : π.range = R := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hRHS : (⊤ : Subgroup L').map π ⊓
      ⨅ i, MonoidHom.eqLocus (β i).toMonoidHom (MonoidHom.id (ModGL TwistTag.E6.tag K)) =
      ((Subgroup.centralizer (t '' {x | x ∈ V ∧
        ExcSplitRootGen.excRefl (p := 3) γ x = x})).comap R.subtype).map R.subtype := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, ← MonoidHom.range_eq_map, hπrange]
    congr 1
    ext y
    rw [Subgroup.mem_iInf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro h _ ⟨x, ⟨hxV, hxr⟩, rfl⟩
      obtain ⟨a, ha⟩ := hxV
      have hfix : ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ ⟨a.1, a.2⟩)) =
          Multiplicative.toAdd (κ ⟨a.1, a.2⟩) := by
        rw [show (⟨a.1, a.2⟩ : A) = a from rfl, ha]
        exact hxr
      have h1 : t (Multiplicative.toAdd (κ a)) * y * (t (Multiplicative.toAdd (κ a)))⁻¹ = y :=
        h ⟨a.1, a.2, (hcomm a.1 a.2).2 hfix⟩
      rw [ha] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    · intro h i
      have hmem : s i ∈ t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x} :=
        ⟨_, ⟨⟨⟨i.1, i.2.1⟩, rfl⟩, (hcomm i.1 i.2.1).1 i.2.2⟩, rfl⟩
      exact mul_inv_eq_iff_eq_mul.mpr (h (s i) hmem)
  rw [← hHyp, hRHS, ← ggOTwoPrime_map_of_injective R.subtype R.subtype_injective,
    ggOTwoPrime_centralizer_eq_ggKGTwJ hK hσ F hv hζ hζo htF hV hγ] at hmap
  exact ⟨E, F, γ, hv, hγ, hmap⟩

theorem card_ggOTwoPrime_ggHypCent_twE6Two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 ↥(twistedE6RootGroup K σ)
      ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) L' ψ A)
    (hodd : Odd (Nat.card ψ.ker)) {n₀ : L'}
    (hn : MulAut.conj n₀ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hrefl : GGIsReflection 3 (ggConjAut A hn)) :
    Nat.card (ggOTwoPrime (ggHypCent A n₀)) = 6 := by
  obtain ⟨E, F, γ, hv, hγ, hmap⟩ :=
    exists_map_ggOTwoPrime_ggHypCent_eq_ggKGTwJ le_rfl (by norm_num) hK hσ hTB hodd hn hrefl
  let R := twistedE6RootGroup K σ
  let π : L' →* ModGL TwistTag.E6.tag K := R.subtype.comp ψ
  have hπker : π.ker = ψ.ker := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * 1)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcard : Nat.card ↥(ggKGTj_F F.Fr F.fr_eq) = 2 := by
    rw [ggKGTj_card_F hK hσ F.Fr F.fr_eq, pow_one]
  haveI : Finite ↥(ggKGTj_F F.Fr F.fr_eq) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨e₁⟩ := nonempty_ggKGTwJ_mulEquiv_SL2 hK hσ F hv hγ
  obtain ⟨e₂⟩ :=
    nonempty_mulEquiv_perm_three_of_card_two hcard
  exact card_ggOTwoPrime_eq_six_of_map_eq π (by rw [hπker]; exact hTB.2.1)
    (by rw [hπker]; exact hodd) hmap
    ⟨((ggKGTwJ F γ).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
      (e₁.trans e₂)⟩

end TwoCount

@[expose] def GGTorusRk1SixOdd (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A → Odd (Nat.card ψ.ker) →
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGIsReflection p (ggConjAut A hn) → Nat.card (ggOTwoPrime (ggHypCent A n)) = 6

theorem ggTorusRk1SixOdd_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusRk1SixOdd p r R' I') :
    GGTorusRk1SixOdd p r R I := by
  intro L' _ _ ψ A hTB hodd
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  have hk : (e.toMonoidHom.comp ψ).ker = ψ.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  have hTB' : GGTorusTBGroup p r R' I' L' (e.toMonoidHom.comp ψ) A := by
    refine ⟨e.surjective.comp hψ, by rw [hk]; exact hker, hperf, hA, ?_, hr, h3, hsc⟩
    intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa]⟩
  exact h L' (e.toMonoidHom.comp ψ) A hTB' (by rw [hk]; exact hodd)

section Recipe


theorem ggTorusRk1SixOdd_recipeR_twE6Two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGTorusRk1SixOdd 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) := by
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := 1) (by omega) hK
  refine ggTorusRk1SixOdd_of_mulEquiv ε.symm ?_ (fun L' _ _ ψ A hTB hodd n hn hrefl =>
    card_ggOTwoPrime_ggHypCent_twE6Two hK hσ hTB hodd hn hrefl)
  intro α hα
  obtain ⟨w, hw⟩ := (hε α).2 hα
  refine ⟨w, ?_⟩
  apply MulEquiv.ext
  intro x
  rw [← hw]
  change (RecipeExcLang.twConj K σ w) x =
    ε.symm (TwE6Transport.recipeConj σ ε w (ε x))
  rw [TwE6Transport.recipeConj_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end Recipe

end TwE6ThreeRootGen

open CFSG CFSG.Assembly TableB

private theorem innerDiagOnLab_of_twE6Two {G : Type} [Group G] {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) 3 Bs L) :
    GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L := by
  refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hM
  obtain ⟨⟨⟨ht, hpn⟩, -⟩, hBN, hBI⟩ := hP
  refine ⟨⟨ht, rfl, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, hpn⟩), hBN, hBI⟩
  · rw [ht]; exact fun h => h
  · rw [ht]; decide

section Config


theorem card_ggRankOneIn_of_twE6Two_rank {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {X : Subgroup G} (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hr : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range)
    (hodd : Odd (Nat.card (Subgroup.center ↥X))) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs)
    (htr : GGIsReflection p t) : Nat.card (ggRankOneIn X Bs t) = 6 := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, hdvd⟩, hn⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range :=
    (Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 5)).trans hr
  have hmod : ∀ (lab : LargeEvenLabel), LargeEvenInLambda2 lab →
      (lab.tag = .twE6 ∧ lab.n = 1) → LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        TwE6ThreeRootGen.GGTorusRk1SixOdd 3 5 R I) := by
    rintro lab - ⟨ht, hn⟩
    refine fun Q hQ => largeEvenRawDatum_mono (fun _ _ _ _ hP => ⟨hP.1, fun _ _ => hP.2⟩)
      (TwE6Delta.labelAll ht (Q := fun R _ I => TwE6ThreeRootGen.GGTorusRk1SixOdd 3 5 R I)
        (fun K _ _ hK => ?_) Q hQ)
    rw [hn] at hK ⊢
    exact TwE6ThreeRootGen.ggTorusRk1SixOdd_recipeR_twE6Two hK
  have hmark2 := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab.tag = .twE6 ∧ lab.n = 1)
    (P' := fun R _ I _ => TwE6ThreeRootGen.GGTorusRk1SixOdd 3 5 R I) hmod
    (fun _ _ _ _ _ _ hP => ⟨hP.1.1.1, hP.1.2⟩) hmark
  have hXc : commutator ↥X = ⊤ := hmark2.1
  obtain ⟨_, _, hraw2⟩ := hmark2.2
  obtain ⟨_, _, I, _, -, -, θ, hP, hP'⟩ := largeEvenRawDatum_exists hraw2
  obtain ⟨-, -, h3I⟩ := hP
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN h3I hb
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hXc θ hN hBsI hr h3
  have hoddk : Odd (Nat.card (ggQuotHom θ).ker) := by rw [ker_ggQuotHom]; exact hodd
  obtain ⟨g, hgX, hgN, hgact⟩ := mem_ggAutomizer_iff.mp ht
  have htEq : t = ggConjAut Bs hgN :=
    MulEquiv.ext fun b => Subtype.ext (by simpa only [ggConjAut_apply] using hgact b)
  have htI : t ∈ ggInduced X Bs := ⟨g, hgX, hgN, hgact⟩
  obtain ⟨n, hn, hover, hrefl, -⟩ := ggReflection_overGamma_of_induced
    Nat.prime_three (by decide) hBs hN htI htr
  have hcard : Nat.card (ggOTwoPrime (ggHypCent (ggGamma X hN).range n)) = 6 :=
    hP' ↥X (ggQuotHom θ) (ggGamma X hN).range hTB hoddk n hn hrefl
  have hfix : ggFixG Bs (ggConjAut Bs hgN) = ggHyperplane Bs t := by
    rw [← htEq]
    rfl
  have hmapH : (ggHypCent (ggGamma X hN).range n).map X.subtype =
      X ⊓ Subgroup.centralizer (ggHyperplane Bs t : Set G) := by
    simpa only [hfix] using map_ggHypCent_eq Nat.prime_three (by decide) hBs hN hn
      hgX hgN (htEq ▸ htr.1) (htEq ▸ hover)
  rw [ggRankOneIn, ← hmapH, ← ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
    Subgroup.card_map_of_injective X.subtype_injective]
  exact hcard

theorem card_ggRankOneIn_of_twE6Two_marking {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer L Bs)
    (htr : GGIsReflection p t) : Nat.card (ggRankOneIn L Bs t) = 6 := by
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, hdvd⟩, hn⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hcfg.tableB_facts.1 Nat.prime_three).mp hdvd
  subst hp3
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)
  exact card_ggRankOneIn_of_twE6Two_rank hcfg hmark hN
    (ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg (innerDiagOnLab_of_twE6Two hmark) hN)
    hodd ht htr

theorem ggRk1ConclEx_of_twE6Two_L_of_odd (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hnsL : ¬ GGSplitLie p L)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    ∀ r ∈ ggAutomizer L Bs, GGIsReflection p r → GGRk1ConclEx p Bs L r := by
  intro r hrA hrR
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨htag, hdvd⟩, hn⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hcfg.tableB_facts.1 Nat.prime_three).mp hdvd
  refine ggRk1ConclEx_of_card_six hp3 hnsL hrA hrR.1
    (card_ggRankOneIn_of_twE6Two_marking hcfg hmark hodd hrA hrR) ⟨lab, hΛ, hhas⟩
    fun lab' hΛ' hhas' => ?_
  have := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas') (by rw [htag]; decide)
    (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
  omega

theorem ggRk1ConclEx_of_twE6Two_L_of_lt (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hnsL : ¬ GGSplitLie p L)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L)
    (hlt : B < Bs) :
    ∀ r ∈ ggAutomizer L Bs, GGIsReflection p r → GGRk1ConclEx p Bs L r :=
  ggRk1ConclEx_of_twE6Two_L_of_odd hRig hcfg hnsL hmark (hcfg.odd_card_center_of_B_lt_Bs hlt
    (GGDichotomy.marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)))

end Config

end CFSG.StandardType

end
