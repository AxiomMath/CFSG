module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwoRankOne
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGResRowOnDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem nonempty_ggOTwoPrime_mulEquiv_sl2_of_map_eq {U V : Type} [Group U] [Finite U] [Group V]
    (π : U →* V) (hπ : π.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card π.ker))
    {C : Subgroup U} {D : Subgroup V} (hmap : (ggOTwoPrime C).map π = D)
    {k : Type} [Field k] [Finite k] (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9)
    (hD : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 2) k)) :
    Nonempty (↥(ggOTwoPrime C) ≃* Matrix.SpecialLinearGroup (Fin 2) k) := by
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
  let f : ↥Q →* Matrix.SpecialLinearGroup (Fin 2) k := e.toMonoidHom.comp f₀
  have hf : Function.Surjective f := e.surjective.comp hf₀
  have hfk : f.ker = π.ker.subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change e (f₀ q) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcen : f.ker ≤ Subgroup.center ↥Q := by
    intro q hq
    rw [hfk, Subgroup.mem_subgroupOf] at hq
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hπ hq) (g : U))
  have hoddk : Odd (Nat.card f.ker) := by
    refine Odd.of_dvd_nat hodd ?_
    rw [hfk]
    exact Subgroup.card_comap_dvd_of_injective π.ker Q.subtype Q.subtype_injective
  obtain ⟨s, hs⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_section_of_central_sl2 hk hk9 hf hcen
  have hgen : ∀ y : ↥Q, ∀ j : ℕ, y ^ 2 ^ j = 1 → s (f y) = y := by
    intro y j hj
    set z := (s (f y))⁻¹ * y with hz
    have hzk : z ∈ f.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hs, inv_mul_cancel]
    have hyz : y = s (f y) * z := by rw [hz, mul_inv_cancel_left]
    have hcomm : Commute (s (f y)) z := Subgroup.mem_center_iff.mp (hcen hzk) (s (f y))
    have hs2 : s (f y) ^ 2 ^ j = 1 := by rw [← map_pow, ← map_pow, hj, map_one, map_one]
    have hz2 : z ^ 2 ^ j = 1 := by
      calc z ^ 2 ^ j = s (f y) ^ 2 ^ j * z ^ 2 ^ j := by rw [hs2, one_mul]
        _ = (s (f y) * z) ^ 2 ^ j := (hcomm.mul_pow _).symm
        _ = 1 := by rw [← hyz, hj]
    have hord : orderOf z = 1 :=
      Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hoddk))
        (orderOf_dvd_of_pow_eq_one hz2) (Subgroup.orderOf_dvd_natCard f.ker hzk)
    calc s (f y) = s (f y) * z := by rw [orderOf_eq_one_iff.mp hord, mul_one]
      _ = y := hyz.symm
  have hall : ∀ u : ↥Q, s (f u) = u := by
    have hle : ggOTwoPrime C ≤ (MonoidHom.eqLocus (s.comp f) (MonoidHom.id ↥Q)).map Q.subtype := by
      change Subgroup.closure {y | y ∈ C ∧ ∃ j : ℕ, y ^ (2 ^ j) = 1} ≤ _
      rw [Subgroup.closure_le]
      rintro y ⟨hyC, j, hyj⟩
      refine Subgroup.mem_map.mpr ⟨⟨y, Subgroup.subset_closure ⟨hyC, j, hyj⟩⟩, ?_, rfl⟩
      exact hgen _ j (Subtype.ext hyj)
    intro u
    obtain ⟨u', hu', hu'u⟩ := Subgroup.mem_map.mp (hle u.2)
    have h : u' = u := Subtype.ext hu'u
    rw [← h]
    exact hu'
  have hinj : Function.Injective f := fun a b hab => by rw [← hall a, ← hall b, hab]
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hf⟩⟩

section Concl

theorem ggRk1ConclEx_of_sl2_rankOne {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (hS : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ggRankOneIn X Bs r))
    (hXns : ¬ GGSplitLie p X) (hdvd : p ∣ 2 ^ f + 1)
    (hle : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n ≤ f)
    (hex : ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧ lab.n = f) :
    GGRk1ConclEx p Bs X r := by
  obtain ⟨σ⟩ := hS
  let θ : Matrix.SpecialLinearGroup (Fin 2) F →* G :=
    (ggRankOneIn X Bs r).subtype.comp σ.toMonoidHom
  have hr2 : r * r = 1 := by simpa [pow_two] using hrR.1
  refine ⟨F, inferInstance, inferInstance, θ, inferInstance, ?_, ?_,
    ggExists_weylElt_of_mem_ggAutomizer hrA hr2, fun hs => absurd hs hXns, fun _ => hF ▸ hdvd,
    ?_, ?_⟩
  · exact (ggRankOneIn X Bs r).subtype_injective.comp σ.injective
  · ext g
    constructor
    · rintro ⟨A, rfl⟩
      exact (σ A).2
    · intro hg
      exact ⟨σ.symm ⟨g, hg⟩, by simp [θ]⟩
  · intro lab hlam hhas
    rw [hF]
    exact Nat.pow_le_pow_right (by norm_num) (hle lab hlam hhas)
  · obtain ⟨lab, hlam, hhas, hn⟩ := hex
    exact ⟨lab, hlam, hhas, by rw [hF, hn]⟩

end Concl

namespace TwE6ThreeRootGen

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Torality

section Map

theorem exists_ggOTwoPrime_ggHypCent_mulEquiv_sl2_twE6Three {n : ℕ} (hn : 3 ≤ n)
    (h3 : 3 ∣ 2 ^ n + 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* ↥(twistedE6RootGroup K σ)} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 ↥(twistedE6RootGroup K σ)
      ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) L' ψ A)
    (hodd : Odd (Nat.card ψ.ker)) {n₀ : L'}
    (hn₀ : MulAut.conj n₀ ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hrefl : GGIsReflection 3 (ggConjAut A hn₀)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), CharP k 2 ∧ Nat.card k = 2 ^ n ∧
      Nonempty (↥(ggOTwoPrime (ggHypCent A n₀)) ≃* Matrix.SpecialLinearGroup (Fin 2) k) := by
  obtain ⟨E, F, γ, hv, hγ, hmap⟩ :=
    exists_map_ggOTwoPrime_ggHypCent_eq_ggKGTwJ (by omega) h3 hK hσ hTB hodd hn₀ hrefl
  let R := twistedE6RootGroup K σ
  let π : L' →* ModGL TwistTag.E6.tag K := R.subtype.comp ψ
  have hπker : π.ker = ψ.ker := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OneMemClass.coe_eq_one]
  have hπc : π.ker ≤ Subgroup.center L' := by rw [hπker]; exact hTB.2.1
  have hπo : Odd (Nat.card π.ker) := by rw [hπker]; exact hodd
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcard : Nat.card ↥(ggKGTj_F F.Fr F.fr_eq) = 2 ^ n := ggKGTj_card_F hK hσ F.Fr F.fr_eq
  haveI : Finite ↥(ggKGTj_F F.Fr F.fr_eq) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨e₁⟩ := nonempty_ggKGTwJ_mulEquiv_SL2 hK hσ F hv hγ
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h9 : 2 ^ n ≠ 9 := fun h => by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    rw [h] at h2
    omega
  refine ⟨↥(ggKGTj_F F.Fr F.fr_eq), inferInstance, inferInstance, inferInstance, hcard, ?_⟩
  exact nonempty_ggOTwoPrime_mulEquiv_sl2_of_map_eq π hπc hπo hmap
    (by rw [hcard]; norm_num at h8; omega) (by rw [hcard]; exact h9)
    ⟨((ggKGTwJ F γ).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e₁⟩

end Map

@[expose] def GGTorusRk1SL (p r m : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGIsReflection p (ggConjAut A hn) →
          ∃ (k : Type) (_ : Field k) (_ : Finite k), CharP k 2 ∧ Nat.card k = 2 ^ m ∧
            Nonempty (↥(ggOTwoPrime (ggHypCent A n)) ≃* Matrix.SpecialLinearGroup (Fin 2) k)

section Recipe

theorem ggTorusRk1SL_recipeR_twE6Three {n : ℕ} (hn : 3 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGTorusRk1SL 3 5 n (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n) (by omega) hK
  intro L' _ _ ψ A hTB n₀ hn₀ hrefl
  have hodd : Odd (Nat.card ψ.ker) :=
    Odd.of_dvd_nat (by decide : Odd 3)
      (TwE6Delta.card_ker_dvd_three_q8 hn hK hTB.1 hTB.2.1 hTB.2.2.1)
  have hI : ∀ α ∈ TwE6Delta.RecipeI K n, MulAut.congr ε.symm α ∈
      ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) := by
    intro α hα
    obtain ⟨w, hw⟩ := (hε α).2 hα
    refine ⟨w, ?_⟩
    apply MulEquiv.ext
    intro x
    rw [← hw]
    change (RecipeExcLang.twConj K σ w) x =
      ε.symm (TwE6Transport.recipeConj σ ε w (ε x))
    rw [TwE6Transport.recipeConj_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact exists_ggOTwoPrime_ggHypCent_mulEquiv_sl2_twE6Three hn h3 hK hσ
    (hTB.mulEquiv ε.symm hI) (by rw [TypeA.ker_comp_mulEquiv]; exact hodd) hn₀ hrefl

end Recipe

end TwE6ThreeRootGen

open CFSG CFSG.Assembly TableB

private theorem innerDiagOnLab_of_twE6Three {G : Type} [Group G] {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) 3 Bs L) :
    GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L := by
  refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hM
  obtain ⟨⟨⟨ht, hpn⟩, -⟩, hBN, hBI⟩ := hP
  refine ⟨⟨ht, rfl, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, hpn⟩), hBN, hBI⟩
  · rw [ht]; exact fun h => h
  · rw [ht]; decide

private theorem three_le_of_dvd_two_pow_add_one {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    3 ≤ n := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    norm_num at h3
  · exact h

section Config

theorem exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_rank {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) 3 Bs X)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hr : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range)
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs) (htr : GGIsReflection 3 t) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
      ggRowP_ETwE6 3 lab ∧ 2 ≤ lab.n ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k), CharP k 2 ∧ Nat.card k = 2 ^ lab.n ∧
        Nonempty (Matrix.SpecialLinearGroup (Fin 2) k ≃* ggRankOneIn X Bs t) := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range :=
    (Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 5)).trans hr
  let S : LargeEvenLabel → Prop := fun lab => lab.tag = .twE6 ∧ 2 ≤ lab.n ∧ 3 ∣ 2 ^ lab.n + 1
  have hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab
      (fun R _ I _ => S lab → TwE6ThreeRootGen.GGTorusRk1SL 3 5 lab.n R I) := by
    intro lab _
    by_cases hS : S lab
    · obtain ⟨htag, hn2, hd⟩ := hS
      exact TwE6Delta.labelAll htag
        (Q := fun R _ I => S lab → TwE6ThreeRootGen.GGTorusRk1SL 3 5 lab.n R I)
        (fun K _ _ hK _ => TwE6ThreeRootGen.ggTorusRk1SL_recipeR_twE6Three
          (three_le_of_dvd_two_pow_add_one hn2 hd) hd hK)
    · intro Q hQ
      exact largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq, fun h => absurd h hS⟩) hQ
  have hmark2 := ggMarking_and_labelAll_dep hall hmark
  have hXc : commutator ↥X = ⊤ := hmark2.1
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨⟨htag, hdvd⟩, hn2⟩, -, h3I⟩, hP'⟩ :=
    largeEvenMarking_exists_hasLabel hmark2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN h3I hb
  have hTB := ggTorusTBGroup_of_marking (p := 3) (r := 5) hp hBs hSC hXc θ hN hBsI hr h3
  obtain ⟨g, hgX, hgN, hgact⟩ := mem_ggAutomizer_iff.mp ht
  have htEq : t = ggConjAut Bs hgN :=
    MulEquiv.ext fun b => Subtype.ext (by simpa only [ggConjAut_apply] using hgact b)
  have htI : t ∈ ggInduced X Bs := ⟨g, hgX, hgN, hgact⟩
  obtain ⟨n, hn, hover, hrefl, -⟩ := ggReflection_overGamma_of_induced
    Nat.prime_three (by decide) hBs hN htI htr
  obtain ⟨k, _, _, hk2, hk, ⟨e⟩⟩ :=
    hP' ⟨htag, hn2, hdvd⟩ ↥X (ggQuotHom θ) (ggGamma X hN).range hTB n hn hrefl
  have hfix : ggFixG Bs (ggConjAut Bs hgN) = ggHyperplane Bs t := by
    rw [← htEq]
    rfl
  have hmapH : (ggHypCent (ggGamma X hN).range n).map X.subtype =
      X ⊓ Subgroup.centralizer (ggHyperplane Bs t : Set G) := by
    simpa only [hfix] using map_ggHypCent_eq Nat.prime_three (by decide) hBs hN hn
      hgX hgN (htEq ▸ htr.1) (htEq ▸ hover)
  have hEq : (ggOTwoPrime (ggHypCent (ggGamma X hN).range n)).map X.subtype =
      ggRankOneIn X Bs t := by
    rw [ggRankOneIn, ← hmapH, ← ggOTwoPrime_map_of_injective X.subtype X.subtype_injective]
  refine ⟨lab, hlab, hhas, ⟨htag, hdvd⟩, hn2, k, inferInstance, inferInstance, hk2, hk, ⟨?_⟩⟩
  exact e.symm.trans (((ggOTwoPrime (ggHypCent (ggGamma X hN).range n)).equivMapOfInjective
    X.subtype X.subtype_injective).trans (MulEquiv.subgroupCongr hEq))

theorem exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hp3 : p = 3)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs L)
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer L Bs) (htr : GGIsReflection p t) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
      ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k), CharP k 2 ∧ Nat.card k = 2 ^ lab.n ∧
        Nonempty (Matrix.SpecialLinearGroup (Fin 2) k ≃* ggRankOneIn L Bs t) := by
  subst hp3
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)
  exact exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_rank hcfg hmark hN
    (ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg (innerDiagOnLab_of_twE6Three hmark) hN)
    ht htr

theorem exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_nbr (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hp3 : p = 3) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X)
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs) (htr : GGIsReflection p t) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧
      ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k), CharP k 2 ∧ Nat.card k = 2 ^ lab.n ∧
        Nonempty (Matrix.SpecialLinearGroup (Fin 2) k ≃* ggRankOneIn X Bs t) := by
  rcases hX with rfl | ⟨y, hnb⟩
  · exact exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_marking hcfg hp3 hmark ht htr
  subst hp3
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) :=
    GGDichotomy.marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)
  exact exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_rank hcfg hmark hN
    (hRk G 3 B Bs x L D J hcfg rfl y X hnb (innerDiagOnLab_of_twE6Three hmark) hN
      (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2)) ht htr

private theorem ggRk1ConclEx_of_twE6Three_iso (hRig : GGLabelRigidInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {Bs X : Subgroup G} (hnsX : ¬ GGSplitLie p X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    (h : ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧ ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k), CharP k 2 ∧ Nat.card k = 2 ^ lab.n ∧
        Nonempty (Matrix.SpecialLinearGroup (Fin 2) k ≃* ggRankOneIn X Bs r)) :
    GGRk1ConclEx p Bs X r := by
  obtain ⟨lab, hΛ, hhas, ⟨htag, hdvd⟩, -, k, _, _, _, hk, hS⟩ := h
  refine ggRk1ConclEx_of_sl2_rankOne hrA hrR hk hS hnsX hdvd (fun lab' hΛ' hhas' => ?_)
    ⟨lab, hΛ, hhas, rfl⟩
  have := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas') (by rw [htag]; decide)
    (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
  omega

theorem ggRk1ConclEx_of_twE6Three_nbr (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hnsX : ¬ GGSplitLie p X) (hp3 : p = 3)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → GGRk1ConclEx p Bs X r := fun r hrA hrR =>
  ggRk1ConclEx_of_twE6Three_iso hRig hnsX hrA hrR
    (exists_ggRankOneIn_mulEquiv_sl2_of_twE6Three_nbr hRk hcfg hp3 hX hmark hrA hrR)

theorem card_ggRankOneIn_of_twE6Two_nbr (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X)
    (hodd : Odd (Nat.card (Subgroup.center ↥X))) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs)
    (htr : GGIsReflection p t) : Nat.card (ggRankOneIn X Bs t) = 6 := by
  rcases hX with rfl | ⟨y, hnb⟩
  · exact card_ggRankOneIn_of_twE6Two_marking hcfg hmark hodd ht htr
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, hdvd⟩, hn⟩, -⟩ := largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hcfg.tableB_facts.1 Nat.prime_three).mp hdvd
  subst hp3
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) :=
    GGDichotomy.marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)
  have hlab : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hmark
    obtain ⟨⟨⟨ht, hpn⟩, -⟩, hBN, hBI⟩ := hP
    refine ⟨⟨ht, rfl, hpn⟩, Or.inr (Or.inl ⟨?_, ?_, hpn⟩), hBN, hBI⟩
    · rw [ht]; exact fun h => h
    · rw [ht]; decide
  exact card_ggRankOneIn_of_twE6Two_rank hcfg hmark hN
    (hRk G 3 B Bs x L D J hcfg rfl y X hnb hlab hN (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2))
    hodd ht htr

theorem ggRk1ConclEx_of_twE6Two_nbr_of_odd (hRig : GGLabelRigidInput)
    (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X)
    (hodd : Odd (Nat.card (Subgroup.center ↥X))) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → GGRk1ConclEx p Bs X r := by
  intro r hrA hrR
  obtain ⟨lab, hΛ, hhas, -, -, -, -, -, ⟨⟨htag, hdvd⟩, hn⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hcfg.tableB_facts.1 Nat.prime_three).mp hdvd
  refine ggRk1ConclEx_of_card_six hp3 hnsX hrA hrR.1
    (card_ggRankOneIn_of_twE6Two_nbr hRk hcfg hX hmark hodd hrA hrR) ⟨lab, hΛ, hhas⟩
    fun lab' hΛ' hhas' => ?_
  have := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hΛ hΛ' hhas hhas') (by rw [htag]; decide)
    (fun ht => by rw [htag] at ht; exact absurd ht (by decide))
  omega

theorem ggRk1ConclEx_of_twE6Two_nbr_of_lt (hRig : GGLabelRigidInput)
    (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X)
    (hlt : B < Bs) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → GGRk1ConclEx p Bs X r :=
  ggRk1ConclEx_of_twE6Two_nbr_of_odd hRig hRk hcfg hX hnsX hmark
    (hcfg.odd_card_center_of_B_lt_Bs hlt
      (GGDichotomy.marking_elim_const (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)))

end Config

end CFSG.StandardType

end
