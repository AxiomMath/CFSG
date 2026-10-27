module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux1
import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
import CFSG.LocalAnalysis.StandardType.GGTBJOmBlock
import CFSG.LocalAnalysis.StandardType.GGTBJOmComp
import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
import CFSG.LocalAnalysis.StandardType.GGTBJOmModelMap
import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthFixOmega
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCoord
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.RankThree.PartOne.FOC.CompCommutator

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

namespace CommonJOmMinusNonsplit


private theorem card_compl_subtype_fin {m : ℕ} {P : Fin m → Prop} :
    Nat.card {i : Fin m // ¬ P i} = m - Nat.card {i : Fin m // P i} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Nat.card_eq_fintype_card,
    Fintype.card_fin]

private theorem card_coord_centralizer {p m : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (τ : (Fin m → Multiplicative (ZMod p)) →* G) (J : Subgroup G)
    (hτ : Function.Injective τ)
    (hcard : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set G)) = p) :
    Nat.card {f : Fin m → Multiplicative (ZMod p) // ∀ j ∈ J, τ f * j = j * τ f} = p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let eτ : (Fin m → Multiplicative (ZMod p)) ≃* ↥τ.range := MonoidHom.ofInjective hτ
  let C := {f : Fin m → Multiplicative (ZMod p) // ∀ j ∈ J, τ f * j = j * τ f}
  let Cτ := ↥(τ.range ⊓ Subgroup.centralizer (J : Set G))
  haveI : Finite C := Subtype.finite
  haveI : Finite Cτ := Subtype.finite
  have h1 : Nat.card C ≤ Nat.card Cτ := by
    refine Nat.card_le_card_of_injective
      (fun f : C => (⟨τ f, ⟨⟨f, rfl⟩, fun j hj => (f.2 j hj).symm⟩⟩ : Cτ)) ?_
    intro f g hfg
    apply Subtype.ext
    exact hτ (congrArg (fun x : Cτ => (x : G)) hfg)
  have h2 : Nat.card Cτ ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective
      (fun x : Cτ => (⟨eτ.symm ⟨x, x.2.1⟩, ?_⟩ : C)) ?_
    · intro j hj
      have hx' : τ (eτ.symm ⟨x, x.2.1⟩) = (x : G) :=
        congrArg Subtype.val (eτ.apply_symm_apply ⟨x, x.2.1⟩)
      simpa only [hx'] using (x.2.2 j hj).symm
    · intro x y hxy
      apply Subtype.ext
      have h := congrArg (fun f : C => τ f) hxy
      have hx' : τ (eτ.symm ⟨x, x.2.1⟩) = (x : G) :=
        congrArg Subtype.val (eτ.apply_symm_apply ⟨x, x.2.1⟩)
      have hy' : τ (eτ.symm ⟨y, y.2.1⟩) = (y : G) :=
        congrArg Subtype.val (eτ.apply_symm_apply ⟨y, y.2.1⟩)
      rw [hx', hy'] at h
      exact h
  exact (le_antisymm h1 h2).trans hcard

private theorem class_card_eq_of_ne_zero {p m : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    (τ : (Fin m → Multiplicative (ZMod p)) →* G)
    (f₀ : Fin m → Multiplicative (ZMod p)) (J : Subgroup G) (P : Fin m → Prop)
    {a : ZMod p} (ha : a ≠ 0)
    (hP : ∀ i, P i → Multiplicative.toAdd (f₀ i) = a ∨ Multiplicative.toAdd (f₀ i) = -a)
    (hcent : ∀ f : Fin m → Multiplicative (ZMod p),
      (∃ c : ZMod p, ∀ i, P i → Multiplicative.toAdd (f i) = c * Multiplicative.toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcard : Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} = p) (hm : 3 ≤ m) :
    Nat.card {i : Fin m // P i} = m := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C := {f : Fin m → Multiplicative (ZMod p) // ∀ j ∈ J, τ f * j = j * τ f}
  haveI : Finite C := Subtype.finite
  have hPne : ∃ i, P i := by
    by_contra h
    push Not at h
    have hS : Nat.card (Fin m → Multiplicative (ZMod p)) ≤ Nat.card C := by
      refine Nat.card_le_card_of_injective (fun f => (⟨f, ?_⟩ : C)) ?_
      · exact hcent f ⟨0, fun i hi => absurd hi (h i)⟩
      · intro a b hab
        exact congrArg Subtype.val hab
    rw [hcard] at hS
    have hdom : Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m := by
      rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
    rw [hdom] at hS
    have hle : p ^ m ≤ p ^ 1 := by simpa using hS
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    omega
  obtain ⟨i₀, hi₀⟩ := hPne
  have hf0 : Multiplicative.toAdd (f₀ i₀) ≠ 0 := by
    rcases hP i₀ hi₀ with h | h
    · rw [h]; exact ha
    · rw [h]; exact neg_ne_zero.mpr ha
  let e : ZMod p × ({i : Fin m // ¬ P i} → Multiplicative (ZMod p)) → C :=
    fun cg => ⟨fun i =>
      if h : P i then Multiplicative.ofAdd (cg.1 * Multiplicative.toAdd (f₀ i)) else cg.2 ⟨i, h⟩,
      hcent _ ⟨cg.1, fun i hi => by rw [dif_pos hi, toAdd_ofAdd]⟩⟩
  have he : Function.Injective e := by
    rintro ⟨c, g⟩ ⟨c', g'⟩ hgg
    have h1 := congrFun (congrArg Subtype.val hgg)
    have hc : c = c' := by
      have h2 := congrArg (fun x => Multiplicative.toAdd x) (h1 i₀)
      simp only [e, dif_pos hi₀, toAdd_ofAdd] at h2
      exact mul_right_cancel₀ hf0 h2
    have hg : g = g' := by
      funext x
      have h2 := h1 x.1
      simpa [e, x.2] using h2
    rw [hc, hg]
  have hS : Nat.card (ZMod p × ({i : Fin m // ¬ P i} → Multiplicative (ZMod p))) ≤
      Nat.card C := Nat.card_le_card_of_injective e he
  rw [hcard] at hS
  have hcarddom : Nat.card (ZMod p × ({i : Fin m // ¬ P i} →
      Multiplicative (ZMod p))) = p ^ (1 + (m - Nat.card {i : Fin m // P i})) := by
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun, card_compl_subtype_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, pow_add, pow_one]
  rw [hcarddom] at hS
  have hle : p ^ (1 + (m - Nat.card {i : Fin m // P i})) ≤ p ^ 1 := by simpa using hS
  have hle' := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hkle : Nat.card {i : Fin m // P i} ≤ m := by
    simpa using (Finite.card_subtype_le (α := Fin m) (fun i => P i))
  omega

private theorem class_card_ge_of_zero {p m : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    (τ : (Fin m → Multiplicative (ZMod p)) →* G)
    (f₀ : Fin m → Multiplicative (ZMod p)) (J : Subgroup G) (P : Fin m → Prop)
    {a : ZMod p} (ha : a = 0)
    (hP : ∀ i, P i → Multiplicative.toAdd (f₀ i) = a ∨ Multiplicative.toAdd (f₀ i) = -a)
    (hcent : ∀ f : Fin m → Multiplicative (ZMod p),
      (∃ c : ZMod p, ∀ i, P i → Multiplicative.toAdd (f i) = c * Multiplicative.toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcard : Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} = p) (hm : 3 ≤ m) :
    m - 1 ≤ Nat.card {i : Fin m // P i} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C := {f : Fin m → Multiplicative (ZMod p) // ∀ j ∈ J, τ f * j = j * τ f}
  haveI : Finite C := Subtype.finite
  let e : ({i : Fin m // ¬ P i} → Multiplicative (ZMod p)) → C :=
    fun g => ⟨fun i => if h : P i then 1 else g ⟨i, h⟩,
      hcent _ ⟨0, fun i hi => by rw [dif_pos hi, toAdd_one, zero_mul]⟩⟩
  have he : Function.Injective e := by
    intro g g' hgg
    funext x
    have h := congrFun (congrArg Subtype.val hgg) x.1
    simpa [e, x.2] using h
  have hS : Nat.card ({i : Fin m // ¬ P i} → Multiplicative (ZMod p)) ≤ Nat.card C :=
    Nat.card_le_card_of_injective e he
  rw [hcard] at hS
  have hcarddom : Nat.card ({i : Fin m // ¬ P i} → Multiplicative (ZMod p)) =
      p ^ (m - Nat.card {i : Fin m // P i}) := by
    rw [Nat.card_fun, card_compl_subtype_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hcarddom] at hS
  have hle : p ^ (m - Nat.card {i : Fin m // P i}) ≤ p ^ 1 := by simpa using hS
  have hle' := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  omega

private theorem eq_one_of_sgnAut_eq_self {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i : Fin m} {f : Fin m → Multiplicative (ZMod p)}
    (h : SpCoord.sgnAut i f = f) : f i = 1 := by
  have hinv : (f i)⁻¹ = f i := by
    simpa [SpCoord.sgnAut_apply] using congrFun h i
  have h2 : (f i) ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hinv.symm
  have hd2 : orderOf (f i) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hdp : orderOf (f i) ∣ p := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rcases (Nat.dvd_prime hp).mp hdp with h1 | hp'
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [hp'] at hd2
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hd2) hp.two_le)

private theorem not_component_of_trivial {K : Type} [Field K] [Finite K] {p m f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hm : 3 ≤ m) (hmo : Odd m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {τ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c}
    (hτ : Function.Injective τ)
    (hsgn : ∀ i : Fin m, ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f))
    (J : Subgroup (OrthRest.RMinus K m b c))
    (hJ : IsComponentOf J
      (Subgroup.centralizer ({(1 : OrthRest.RMinus K m b c)} : Set (OrthRest.RMinus K m b c))))
    (hcard : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c))) = p) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hR : CFSG.IsQuasisimple (OrthRest.RMinus K m b c) := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (OrthTorus.rMinusEquiv K m b c).symm ?_
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (TableBOrth.omegaEquivOrthDerived (TableBOrth.qMinusForm K m b c)) ?_
    rw [TableBOrth.coe_qMinusForm]
    exact TableBOrth.isQuasisimple_omegaMinus (by omega) hirr
  have htop : CFSG.Assembly.IsQuasisimple
      (⊤ : Subgroup (OrthRest.RMinus K m b c)) := by
    rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hR
  have hcent1 : Subgroup.centralizer
      ({(1 : OrthRest.RMinus K m b c)} : Set (OrthRest.RMinus K m b c)) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.one_mem (Subgroup.center (OrthRest.RMinus K m b c))
  have hJtop : J = ⊤ := by
    refine GGHalf.eq_of_isComponentOf_isQuasisimple (J := ⊤) htop ?_
    simpa [hcent1] using hJ
  have hbot : τ.range ⊓ Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c)) = ⊥ := by
    rw [hJtop]
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxrange, hxcent⟩
    obtain ⟨g, rfl⟩ := hxrange
    have hcent : ∀ w : OrthRest.RMinus K m b c, w * τ g = τ g * w :=
      fun w => (Subgroup.mem_centralizer_iff.mp hxcent) w (Subgroup.mem_top w)
    have hg : g = 1 := by
      funext i
      obtain ⟨w, hw⟩ := hsgn i
      have hτg : τ (SpCoord.sgnAut i g) = τ g := by
        rw [← hw g, hcent w]
        exact mul_inv_cancel_right (τ g) w
      exact eq_one_of_sgnAut_eq_self hp hp2 (hτ hτg)
    rw [hg, map_one]
    exact Subgroup.mem_bot.mpr rfl
  have hcard1 : Nat.card ↥(τ.range ⊓
      Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c))) = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  rw [hcard1] at hcard
  exact hp.ne_one hcard.symm

private theorem dense_exceptional {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK2 : Nat.card K = 2) (hpq : p ∣ Nat.card K + 1)
    (hdim : Module.finrank K V = 8) (Δ : OrthTorus.TBJOmData Q p A r)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v)
    (g₀ : Fin r → Multiplicative (ZMod p)) (hg₀ : ∀ i, g₀ i ≠ 1)
    {J : Subgroup ↥(orthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({Δ.τΩ hA g₀} : Set ↥(orthDerived Q))))
    (hnot : ∃ f, ∃ j ∈ J, Δ.τΩ hA f * j ≠ j * Δ.τΩ hA f) : False := by
  classical
  obtain ⟨f, j, hjJ, hfj⟩ := hnot
  have hr : r ≠ 0 := by
    rintro rfl
    have hf1 : f = 1 := funext fun i => i.elim0
    rw [hf1, map_one] at hfj
    simpa using hfj
  have hg1 : g₀ ≠ 1 := by
    intro h
    exact hg₀ ⟨0, Nat.pos_of_ne_zero hr⟩ (congrFun h _)
  have hxne : Δ.τΩ hA g₀ ≠ 1 := by
    intro h
    apply hg1
    apply Δ.τ_inj
    have h1 : Δ.τ g₀ = 1 := by
      simpa using congrArg (fun y : ↥(orthDerived Q) => (y : V ≃ₗ[K] V)) h
    simpa using h1
  have hgp : g₀ ^ p = 1 := by
    funext i
    apply Multiplicative.toAdd.injective
    rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one]
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hxp : (Δ.τΩ hA g₀) ^ p = 1 := by
    rw [← map_pow, hgp, map_one]
  have hx : orderOf (Δ.τΩ hA g₀) = p := orderOf_eq_prime hxp hxne
  have hx' : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q p
      ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V) := by
    simpa using Δ.oddOrderIsometry hp2 hQ hA g₀
  rcases CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.comp_cases_orthDerived_gen hQ Fact.out hp2
    hpq hx hJ with ⟨h, hh, hne, hq, _hLh⟩ | ⟨G, _hGq, hGle, _hGn, _hGdim, hLG⟩
  · obtain ⟨v, hv0, hvA⟩ := hW
    have hxA : ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ A := by
      have h : Δ.τ g₀ ∈ Δ.τ.range := ⟨g₀, rfl⟩
      simpa using le_of_eq Δ.τ_range h
    have hfix : ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = v := hvA _ hxA
    have hm4 : 4 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
        ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h := by
      rcases CFSG.LocalAnalysis.GLTheoremA.I167.i167COrth_hm4 Fact.out hp2 hpq hQ hx hh
        hne hq with h4 | ⟨-, h4⟩
      · exact h4
      · omega
    have hdeg : h.natDegree = 2 :=
      CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx' Fact.out hp2 hpq
        hh hne
    haveI : Fact (Irreducible h) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh⟩
    have hfr : Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h) = 8 := by
      have hge : 8 ≤ Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
          ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h) := by
        have h4 : 4 ≤ Module.finrank (AdjoinRoot h)
            (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
              ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h) := hm4
        rw [CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent, hdeg]
        omega
      have hle : Module.finrank K (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
          ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h) ≤ 8 := by
        rw [← hdim]
        exact Submodule.finrank_le _
      omega
    have htop : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hfr.trans hdim.symm)
    have hvmem : v ∈ CFSG.RankThree.PartOne.KCPrimary.primaryComponent
        ((Δ.τΩ hA g₀ : ↥(orthDerived Q)) : V ≃ₗ[K] V).toLinearMap h := by
      rw [htop]
      exact Submodule.mem_top
    exact hv0 (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.eq_zero_of_mem_primaryComponent_of_apply_eq
      hh hne hvmem hfix)
  · have hf : ∀ i, Multiplicative.toAdd (g₀ i) = 0 → f i = 1 :=
      fun i hi => absurd (by simpa using hi) (hg₀ i)
    have hjG : (j : V ≃ₗ[K] V) ∈ G := by
      have h := hjJ
      rw [hLG, Subgroup.mem_subgroupOf] at h
      exact h
    have hcomm := Δ.blockZ_comm hp2 hQ hA g₀ f hf (j : V ≃ₗ[K] V) (hGle hjG)
    exact hfj (Subtype.ext (by
      simpa only [Subgroup.coe_mul, OrthTorus.tbjA_coe_tauOmega] using hcomm))

private theorem dense_lambda2 {p m f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f + 1) (hm : 3 ≤ m) (hexc : m = 3 → f = 1 → False) :
    LargeEvenInLambda2 ⟨.twA, m - 1, f⟩ := by
  have hf1 : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst hf0
    simp at hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpq)
  have hm2 : 2 ≤ m - 1 := by omega
  have hlast : m - 1 = 2 → 2 ≤ f := by
    intro h
    have hm3 : m = 3 := by omega
    have hfne : f ≠ 1 := fun hf => hexc hm3 hf
    omega
  change 1 ≤ f ∧ 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ f)
  exact ⟨hf1, hm2, hlast⟩

theorem ggCommonJRowOmMinusNonsplit_position {K : Type} [Field K] [Finite K] {p m f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hm : 3 ≤ m) (hmo : Odd m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {τ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c}
    (hτ : Function.Injective τ) (hsign : GGOmMinusNonsplitSignedNormalizer τ)
    (hsgn : ∀ i : Fin m, ∃ w : OrthRest.RMinus K m b c, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f))
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    (g : Fin m → Multiplicative (ZMod p)) (J : Subgroup (OrthRest.RMinus K m b c))
    (hJ : IsComponentOf J (Subgroup.centralizer ({τ g} : Set (OrthRest.RMinus K m b c))))
    (hcard : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c))) = p) :
    (GGCoordDense g ∧ LargeEvenInLambda2 ⟨.twA, m - 1, f⟩) ∨ (GGCoordSparse g ∧ g ≠ 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let Q : QuadraticForm K (LargeEvenMinusIdx m → K) := TableBOrth.qMinusForm K m b c
  let e := OrthTorus.rMinusEquiv K m b c
  let E₀ : Subgroup (OrthRest.RMinus K m b c) := τ.range
  have hE0ab : IsElemAbelian p E₀ := by
    have hexp : ∀ a : Fin m → Multiplicative (ZMod p), a ^ p = 1 := by
      intro a
      funext i
      apply Multiplicative.toAdd.injective
      simp only [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one,
        nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hE := CFSG.StandardType.isElemAbelian_range (p := p)
      (fun a b : Fin m → Multiplicative (ZMod p) => mul_comm a b) hexp τ
    change IsElemAbelian p τ.range
    exact hE
  have hcardE0 : Nat.card E₀ = p ^ m := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_fun,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have h3 : p ^ 3 ≤ Nat.card E₀ := by
    rw [hcardE0]
    exact Nat.pow_le_pow_right hp.one_le hm
  obtain ⟨b₀, hb₀, hb₀1⟩ := CFSG.StandardType.exists_ne_one_of_pow_le_card hp h3
  have hsc0 := CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_sc hK hp hp2 hpq hm hmo
    hirr hE0ab hcardE0
  let E₁ : Subgroup ↥(orthDerived Q) := E₀.map e.toMonoidHom
  have hE1ab : IsElemAbelian p E₁ := by
    change IsElemAbelian p (E₀.map e.toMonoidHom)
    exact hE0ab.map e.toMonoidHom
  have hE1sc := CFSG.StandardType.selfCent_map_mulEquiv e hsc0
  have hcard1 : Nat.card E₁ = p ^ m :=
    (CFSG.StandardType.natCard_map_mulEquiv e E₀).trans hcardE0
  have hne1 : ∃ b ∈ E₁, b ≠ 1 := by
    refine ⟨e b₀, Subgroup.mem_map_of_mem e.toMonoidHom hb₀,
      fun h => hb₀1 (e.injective (by simpa using h))⟩
  obtain ⟨hAΩ, hApow, hAcomm, hmax, hneA⟩ :=
    CFSG.StandardType.map_subtype_hyps E₁ hE1ab hne1 hE1sc
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm m hirr
  have hT : ∃ T : Submodule K (LargeEvenMinusIdx m → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, Q v = 0 := (OrthTorus.charSum_qMinusForm m hirr).2 hm
  have hpq' : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1 := Or.inr (by rw [hK]; exact hpq)
  obtain ⟨r, τ₀, F, D, i₁, i₂, i₃, c', θ, hτF, hinj, hrange, hdim, hcp, hfix, htwist, hroots,
    hθinj, hθrange, hθact, hnorm, hswap, hdinv, hsignMove, hnoFix, hexFix⟩ :=
    OrthTorus.exists_torus_blocks (p := p) hp2 hpq' hQ hT hAΩ hApow hAcomm hmax hneA
  letI := i₁
  letI := i₂
  letI := i₃
  let Δ : OrthTorus.TBJOmData Q p (E₁.map (orthDerived Q).subtype) r :=
    { τ := τ₀, F := F, D := D, c := c', θ := θ, τ_eq := hτF, τ_inj := hinj, τ_range := hrange,
      finrank_D := hdim, c_pow := hcp, c_fix := hfix, c_twist := htwist, c_roots := hroots,
      θ_inj := hθinj, θ_range := hθrange, θ_act := hθact, normalizer := hnorm,
      swapMove := hswap, dinvMove := hdinv, signMove := hsignMove, noFixed := hnoFix,
      exFixed := hexFix }
  have hτΩ : ∀ f, Δ.τ f ∈ orthDerived Q := fun f => by
    have h : Δ.τ f ∈ Δ.τ.range := ⟨f, rfl⟩
    rw [hrange] at h
    exact hAΩ h
  let τ' : (Fin r → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c :=
    e.symm.toMonoidHom.comp (Δ.τ.codRestrict (orthDerived Q) hτΩ)
  have heτ' : ∀ f, e (τ' f) = Δ.τΩ hAΩ f := fun f => by
    show e (e.symm ((Δ.τ.codRestrict (orthDerived Q) hτΩ) f)) = Δ.τΩ hAΩ f
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hτ'inj : Function.Injective τ' := by
    intro f g hfg
    apply hinj
    have h : e (τ' f) = e (τ' g) := congrArg e hfg
    have h' : Δ.τΩ hAΩ f = Δ.τΩ hAΩ g := by simpa only [heτ'] using h
    change (Δ.τ f : (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K)) = Δ.τ g
    exact Subtype.ext_iff.mp h' 
  have hτ'range : τ'.range = E₀ := by
    ext x
    exact (CFSG.StandardType.mem_range_iff_mem_comap_model e E₀ Δ.τ hτΩ hrange x).symm
  have hdom : Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := by
    rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have hpr : p ^ r = p ^ m := by
    rw [← hdom, Nat.card_congr (MonoidHom.ofInjective hτ'inj).toEquiv, hτ'range, hcardE0]
  have hr : r = m := Nat.pow_right_injective hp.two_le hpr
  subst r
  have hsign' : CommonJOmMinusNonsplit.GGOmMinusNonsplitSignedNormalizer τ' := by
    intro w hw
    let g : (LargeEvenMinusIdx m → K) ≃ₗ[K] (LargeEvenMinusIdx m → K) :=
      ((e w : ↥(orthDerived Q)) : (LargeEvenMinusIdx m → K) ≃ₗ[K]
        (LargeEvenMinusIdx m → K))
    have hAnorm : ∀ a ∈ E₁.map (orthDerived Q).subtype, g * a * g⁻¹ ∈
        E₁.map (orthDerived Q).subtype := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨e (w * x * w⁻¹), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem e.toMonoidHom (hτ'range ▸ hw x (hτ'range.symm ▸ hx))
      · have heq : e (w * x * w⁻¹) = e w * e x * e w⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        simpa only [g, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, Subgroup.coe_mul,
          Subgroup.coe_inv, map_inv] using congrArg Subtype.val heq
    obtain ⟨π, ε, hε, hrel⟩ := Δ.normalizer g hAnorm
    let eτ' : (Fin m → Multiplicative (ZMod p)) ≃* ↥τ'.range :=
      MonoidHom.ofInjective hτ'inj
    let u : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p)) :=
      fun f => eτ'.symm ⟨w * τ' f * w⁻¹, hw (τ' f) ⟨f, rfl⟩⟩
    have hu : ∀ f, τ' (u f) = w * τ' f * w⁻¹ := by
      intro f
      have h := eτ'.apply_symm_apply ⟨w * τ' f * w⁻¹, hw (τ' f) ⟨f, rfl⟩⟩
      exact congrArg Subtype.val h
    refine ⟨u, ⟨π, ε, hε, fun f i => ?_⟩, fun f => (hu f).symm⟩
    have hcoe : ∀ f, g * Δ.τ f * g⁻¹ = Δ.τ (u f) := by
      intro f
      have h := congrArg (fun x => e x) (hu f)
      rw [map_mul, map_mul, map_inv] at h
      rw [heτ' f, heτ' (u f)] at h
      have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
      exact h'.symm
    exact hrel f (u f) (hcoe f) i
  have hrange' : τ.range = τ'.range := by rw [hτ'range]
  obtain ⟨φ, hφ, hφnorm⟩ :=
    CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_compareTorus hτ hτ'inj hrange' hsgn hperm
      hsign'
  let g₀ : Fin m → Multiplicative (ZMod p) := φ g
  have hτg : e (τ g) = Δ.τΩ hAΩ g₀ := by
    rw [hφ g, heτ' g₀]
  let J' : Subgroup ↥(orthDerived Q) := J.map e.toMonoidHom
  have hJ'asm : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({Δ.τΩ hAΩ g₀} : Set ↥(orthDerived Q))) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ
      e.toMonoidHom e.injective
    rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e (τ g)] at h
    rwa [hτg] at h
  have hJ' : CFSG.Open.IsComponentOf J'
      (Subgroup.centralizer ({Δ.τΩ hAΩ g₀} : Set ↥(orthDerived Q))) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ'asm
  have hW : ∃ v : LargeEvenMinusIdx m → K, v ≠ 0 ∧ ∀ a ∈ E₁.map (orthDerived Q).subtype,
      a v = v :=
    Δ.exFixed (by
      rw [(OrthTorus.charSum_qMinusForm m hirr).1]
      exact CFSG.StandardType.modEq_neg_one_charSum (Or.inr ⟨hmo, by rw [hK]; exact hpq⟩))
  obtain ⟨a, P, hPval, hPswap, hPmixed, hPsgn, hPcent⟩ :=
    Δ.blockData hp2 hQ hT hAΩ hW g₀ hJ'
  have hcardτ' : Nat.card ↥(τ'.range ⊓ Subgroup.centralizer (J : Set (OrthRest.RMinus K m b c))) =
      p := by
    rwa [hτ'range]
  have hcardC := card_coord_centralizer hp τ' J hτ'inj hcardτ'
  have hcentτ' : ∀ f : Fin m → Multiplicative (ZMod p),
      (∃ c : ZMod p, ∀ i, P i → Multiplicative.toAdd (f i) = c * Multiplicative.toAdd (g₀ i)) →
        ∀ j ∈ J, τ' f * j = j * τ' f := by
    intro f hf j hj
    have h := hPcent f hf (e j) (Subgroup.mem_map_of_mem e.toMonoidHom hj)
    apply e.injective
    simpa only [map_mul, heτ' f] using h
  by_cases ha : a = 0
  · have hk := class_card_ge_of_zero (p := p) (m := m) hp τ' g₀ J P ha hPval hcentτ' hcardC hm
    by_cases hkm : Nat.card {i : Fin m // P i} = m
    · have hPall : ∀ i, P i := by
        have hcompl0 : Nat.card {i : Fin m // ¬ P i} = 0 := by
          rw [card_compl_subtype_fin, hkm, Nat.sub_self]
        intro i
        by_contra hi
        have hpos : 1 ≤ Nat.card {i : Fin m // ¬ P i} := by
          have h := Nat.card_le_card_of_injective
            (fun _ : Unit => (⟨i, hi⟩ : {i : Fin m // ¬ P i}))
            (fun a b _ => Subsingleton.elim a b)
          simpa using h
        omega
      have hg₀1 : g₀ = 1 := by
        funext i
        have hi := hPval i (hPall i)
        rw [ha] at hi
        rcases hi with hi | hi
        · exact Multiplicative.toAdd.injective (by simpa using hi)
        · exact Multiplicative.toAdd.injective (by simpa using hi)
      have hg1 : g = 1 := φ.injective (by
        rw [show φ g = g₀ from rfl, hg₀1, map_one])
      have hJ1 : IsComponentOf J
          (Subgroup.centralizer ({(1 : OrthRest.RMinus K m b c)} :
            Set (OrthRest.RMinus K m b c))) := by
        simpa [hg1] using hJ
      exact (not_component_of_trivial hK hp hp2 hpq hm hmo hirr hτ hsgn J hJ1 hcard).elim
    · have hkcompl : Nat.card {i : Fin m // ¬ P i} = 1 := by
        rw [card_compl_subtype_fin]
        have hkle : Nat.card {i : Fin m // P i} ≤ m := by
          simpa using (Finite.card_subtype_le (α := Fin m) (fun i => P i))
        omega
      obtain ⟨i₀, hi₀⟩ := Nat.card_eq_one_iff_exists.mp hkcompl
      have hsparse0 : GGCoordSparse g₀ := by
        refine ⟨i₀.1, fun j hj => ?_⟩
        have hPj : P j := by
          by_contra hPj
          have hmem : (⟨j, hPj⟩ : {i : Fin m // ¬ P i}) = i₀ := hi₀ ⟨j, hPj⟩
          exact hj (congrArg Subtype.val hmem)
        have hval := hPval j hPj
        rw [ha] at hval
        rcases hval with hval | hval
        · exact Multiplicative.toAdd.injective (by simpa using hval)
        · exact Multiplicative.toAdd.injective (by simpa using hval)
      have hcoord := CommonJ.ggCoord_iff_of_normalizes (p := p) (k := m) hp hp2 hm hφnorm g
      have hgsparse : GGCoordSparse g := hcoord.2.mp hsparse0
      have hgne : g ≠ 1 := by
        intro hg1
        have hg₀1 : g₀ = 1 := by
          rw [show g₀ = φ g from rfl, hg1, map_one]
        have hJ1 : IsComponentOf J
            (Subgroup.centralizer ({(1 : OrthRest.RMinus K m b c)} :
              Set (OrthRest.RMinus K m b c))) := by
          simpa [hg1] using hJ
        exact not_component_of_trivial hK hp hp2 hpq hm hmo hirr hτ hsgn J hJ1 hcard
      exact Or.inr ⟨hgsparse, hgne⟩
  · have hkm := class_card_eq_of_ne_zero (p := p) (m := m) hp τ' g₀ J P ha hPval hcentτ' hcardC hm
    have hPall : ∀ i, P i := by
      have hcompl0 : Nat.card {i : Fin m // ¬ P i} = 0 := by
        rw [card_compl_subtype_fin, hkm, Nat.sub_self]
      intro i
      by_contra hi
      have hpos : 1 ≤ Nat.card {i : Fin m // ¬ P i} := by
        have h := Nat.card_le_card_of_injective
          (fun _ : Unit => (⟨i, hi⟩ : {i : Fin m // ¬ P i}))
          (fun a b _ => Subsingleton.elim a b)
        simpa using h
      omega
    have hdense0 : GGCoordDense g₀ := by
      intro i
      refine ⟨?_, fun j => ?_⟩
      · have hi := hPval i (hPall i)
        intro h1
        rw [h1, toAdd_one] at hi
        rcases hi with hi | hi
        · exact ha hi.symm
        · exact ha (neg_eq_zero.mp hi.symm)
      · have hi := hPval i (hPall i)
        have hj := hPval j (hPall j)
        rcases hi with hi | hi <;> rcases hj with hj | hj
        · left; exact Multiplicative.toAdd.injective (hj.trans hi.symm)
        · right
          apply Multiplicative.toAdd.injective
          simpa [toAdd_inv, hi] using hj
        · right
          apply Multiplicative.toAdd.injective
          simpa [toAdd_inv, hi] using hj
        · left; exact Multiplicative.toAdd.injective (hj.trans hi.symm)
    have hcoord := CommonJ.ggCoord_iff_of_normalizes (p := p) (k := m) hp hp2 hm hφnorm g
    have hgdense : GGCoordDense g := hcoord.1.mp hdense0
    have hg₀ : ∀ i, g₀ i ≠ 1 := fun i => (hdense0 i).1
    have hnot' : ∃ f : Fin m → Multiplicative (ZMod p), ∃ j ∈ J',
        Δ.τΩ hAΩ f * j ≠ j * Δ.τΩ hAΩ f := by
      by_contra hcon
      have hcon' : ∀ f : Fin m → Multiplicative (ZMod p), ∀ j ∈ J',
          Δ.τΩ hAΩ f * j = j * Δ.τΩ hAΩ f := by
        intro f j hj
        by_contra h
        exact hcon ⟨f, j, hj, h⟩
      have hcent : ∀ f : Fin m → Multiplicative (ZMod p), ∀ j ∈ J,
          τ' f * j = j * τ' f := by
        intro f j hj
        have hj' : e j ∈ J' := Subgroup.mem_map_of_mem e.toMonoidHom hj
        have hcomm := hcon' f (e j) hj'
        apply e.injective
        rw [map_mul, map_mul, heτ' f]
        exact hcomm
      have hcardall : Nat.card {f : Fin m → Multiplicative (ZMod p) //
          ∀ j ∈ J, τ' f * j = j * τ' f} = p ^ m := by
        rw [Nat.card_congr (Equiv.subtypeUnivEquiv hcent)]
        rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
      rw [hcardall] at hcardC
      have hm1 : m = 1 := by
        apply Nat.pow_right_injective hp.two_le
        simpa using hcardC
      omega
    have hlam := dense_lambda2 hp hp2 hpq hm (fun hm3 hf1 => by
      have hK2 : Nat.card K = 2 := by rw [hK, hf1]; norm_num
      have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
      have hdim : Module.finrank K (LargeEvenMinusIdx m → K) = 8 := by
        rw [hm3, Module.finrank_fintype_fun_eq_card]
        simp [LargeEvenMinusIdx, Fintype.card_sum]
      exact dense_exceptional hp2 hK2 hpq' hdim Δ hQ hAΩ hW g₀ hg₀ hJ' hnot')
    exact Or.inl ⟨hgdense, hlam⟩


end CommonJOmMinusNonsplit

end CFSG.StandardType

end
