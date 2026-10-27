module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
import CFSG.GH74.Uniqueness.Section14Tools
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.GroupTheory.LocalCores.FittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped commutatorElement

section Abstract

theorem uc22p22f_isCyclic_fitting_iff (X : Type*) [Group X] [Finite X] :
    IsCyclic ↥(CFSG.fittingSubgroup ↥(_root_.commutator X)) ↔
      IsCyclic ↥(_root_.commutator X ⊓ CFSG.fittingSubgroup X) := by
  have h := CFSG.LocalCores.fitting_normal_intersection (_root_.commutator X)
  let e : ↥(CFSG.fittingSubgroup ↥(_root_.commutator X)) ≃*
      ↥(_root_.commutator X ⊓ CFSG.fittingSubgroup X) :=
    ((CFSG.fittingSubgroup ↥(_root_.commutator X)).equivMapOfInjective (_root_.commutator X).subtype
      (_root_.commutator X).subtype_injective).trans (MulEquiv.subgroupCongr h)
  constructor
  · intro hc
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  · intro hc
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem uc22p22f_cyclic_fitting_of_injective {Q Qb : Type} [Group Q] [Finite Q] [Group Qb]
    [Finite Qb] (f : Q →* Qb) (hf : Function.Surjective f) (h2 : CFSG.pCore 2 Q = ⊥)
    (hinj : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup Q, E ≤ CFSG.pCore q Q →
        CFSG.Open.IsElemAbelian q E → Nat.card E = q ^ 2 → ∀ e ∈ E, f e = 1 → e = 1)
    (hcyc : IsCyclic ↥(_root_.commutator Qb ⊓ CFSG.fittingSubgroup Qb)) :
    IsCyclic ↥(_root_.commutator Q ⊓ CFSG.fittingSubgroup Q) := by
  classical
  set F : Subgroup Q := _root_.commutator Q ⊓ CFSG.fittingSubgroup Q with hF
  haveI hFn : F.Normal := inferInstance
  haveI hFnil : Group.IsNilpotent ↥F := by
    haveI : Group.IsNilpotent ↥(CFSG.fittingSubgroup Q) := inferInstance
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : F ≤ CFSG.fittingSubgroup Q))
  have hFmap : F.map f ≤ _root_.commutator Qb ⊓ CFSG.fittingSubgroup Qb := by
    refine le_inf ?_ ?_
    · calc F.map f ≤ (_root_.commutator Q).map f := Subgroup.map_mono inf_le_left
        _ = _root_.commutator Qb := by
          rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
            Subgroup.map_top_of_surjective f hf]
    · have hn : ((CFSG.fittingSubgroup Q).map f).Normal :=
        (inferInstance : (CFSG.fittingSubgroup Q).Normal).map f hf
      haveI : Group.IsNilpotent ↥((CFSG.fittingSubgroup Q).map f) := by
        haveI : Group.IsNilpotent ↥(CFSG.fittingSubgroup Q) := inferInstance
        exact Group.nilpotent_of_surjective
          (MonoidHom.subgroupMap f (CFSG.fittingSubgroup Q))
          (MonoidHom.subgroupMap_surjective f (CFSG.fittingSubgroup Q))
      have hle : (CFSG.fittingSubgroup Q).map f ≤ CFSG.fittingSubgroup Qb :=
        le_sSup ⟨hn, inferInstance⟩
      exact (Subgroup.map_mono inf_le_right).trans hle
  haveI hcycF : IsCyclic ↥(F.map f) := Subgroup.isCyclic_of_le hFmap
  haveI : IsZGroup ↥F := by
    refine ⟨fun q hq S => ?_⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hle : (S : Subgroup ↥F).map F.subtype ≤ CFSG.pCore q Q :=
      Sylow.map_le_pCore hFn hFnil q S
    by_cases hq2 : q = 2
    · subst hq2
      rw [h2, le_bot_iff] at hle
      have hS : (S : Subgroup ↥F) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : F.subtype x ∈ (S : Subgroup ↥F).map F.subtype := ⟨x, hx, rfl⟩
        rw [hle] at this
        have h1 : (x : Q) = 1 := Subgroup.mem_bot.1 this
        exact Subgroup.mem_bot.2 (Subtype.ext h1)
      rw [hS]
      infer_instance
    · by_contra hnc
      haveI : Fact (IsPGroup q ↥(S : Subgroup ↥F)) := ⟨S.isPGroup'⟩
      obtain ⟨E₀, -, hE₀card, hE₀el⟩ := CFSG.lemma_4_5_a hq2 hnc
      let E₁ : Subgroup ↥F := E₀.map (S : Subgroup ↥F).subtype
      let E : Subgroup Q := E₁.map F.subtype
      have hE₁S : E₁ ≤ (S : Subgroup ↥F) := Subgroup.map_subtype_le _
      have hEle : E ≤ CFSG.pCore q Q := (Subgroup.map_mono hE₁S).trans hle
      have hE₀el' : CFSG.Open.IsElemAbelian q E₀ :=
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q E₀).1 hE₀el
      have hE₁el : CFSG.Open.IsElemAbelian q E₁ := hE₀el'.map _
      have hEel : CFSG.Open.IsElemAbelian q E := hE₁el.map _
      have hE₁card : Nat.card E₁ = q ^ 2 := by
        rw [Subgroup.card_map_of_injective (S : Subgroup ↥F).subtype_injective]
        exact hE₀card
      have hEcard : Nat.card E = q ^ 2 := by
        rw [Subgroup.card_map_of_injective F.subtype_injective]
        exact hE₁card
      have h1 := hinj q hq hq2 E hEle hEel hEcard
      let g : ↥E₁ →* ↥(F.map f) :=
        (f.comp (F.subtype.comp E₁.subtype)).codRestrict (F.map f)
          (fun x => Subgroup.mem_map.2 ⟨((x : ↥E₁) : ↥F), ((x : ↥E₁) : ↥F).2, rfl⟩)
      have hg : Function.Injective g := by
        rw [injective_iff_map_eq_one]
        intro y hy
        have hy' : f ((y : ↥F) : Q) = 1 := by
          have := congrArg (fun z : ↥(F.map f) => (z : Qb)) hy
          simpa [g] using this
        have hyE : (((y : ↥F) : Q)) ∈ E := ⟨(y : ↥F), y.2, rfl⟩
        have := h1 _ hyE hy'
        exact Subtype.ext (Subtype.ext this)
      haveI : IsCyclic ↥E₁ := isCyclic_of_injective g hg
      have hexp : ∀ x : ↥E₁, x ^ q = 1 := by
        intro x
        exact Subtype.ext (by simpa using hE₁el.2 (x : ↥F) x.2)
      have h5 : Monoid.exponent ↥E₁ = Nat.card ↥E₁ := IsCyclic.exponent_eq_card
      have h6 : Monoid.exponent ↥E₁ ∣ q := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
      rw [h5, hE₁card] at h6
      have h7 := Nat.le_of_dvd hq.pos h6
      have h8 : q < q ^ 2 := by nlinarith [hq.one_lt]
      omega
  infer_instance

end Abstract

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_pCore_le_ker {M V : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hred : TwoReduced M V) : CFSG.pCore 2 ↥M ≤ (kerAct M V).normalCore := by
  have h := (uc22br4_pCore_bot_iff M V hV).2 hred
  set ρ : ↥M →* MBar M V := QuotientGroup.mk' (kerAct M V).normalCore with hρ
  have hnorm : ((CFSG.pCore 2 ↥M).map ρ).Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥M)).map ρ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥M).map ρ) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map ρ
  have hle : (CFSG.pCore 2 ↥M).map ρ ≤ CFSG.pCore 2 (MBar M V) := le_sSup ⟨hnorm, hp⟩
  rw [h, le_bot_iff] at hle
  intro x hx
  have hx' : ρ x ∈ (CFSG.pCore 2 ↥M).map ρ := ⟨x, hx, rfl⟩
  rw [hle] at hx'
  exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 hx')

@[expose] noncomputable def uc22p22fRho (M V : Subgroup G)
    (h : CFSG.pCore 2 ↥M ≤ (kerAct M V).normalCore) : Bar2 M →* MBar M V :=
  QuotientGroup.lift (CFSG.pCore 2 ↥M) (QuotientGroup.mk' (kerAct M V).normalCore)
    (by rw [QuotientGroup.ker_mk']; exact h)

theorem uc22p22fRho_mk {M V : Subgroup G} (h : CFSG.pCore 2 ↥M ≤ (kerAct M V).normalCore)
    (x : ↥M) : uc22p22fRho M V h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  QuotientGroup.lift_mk _ _ _

theorem uc22p22fRho_surjective {M V : Subgroup G} (h : CFSG.pCore 2 ↥M ≤ (kerAct M V).normalCore) :
    Function.Surjective (uc22p22fRho M V h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, uc22p22fRho_mk h x⟩

theorem uc22p22fRho_eq_one_iff {M V : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (h : CFSG.pCore 2 ↥M ≤ (kerAct M V).normalCore) (x : ↥M) :
    uc22p22fRho M V h (QuotientGroup.mk x) = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
  rw [uc22p22fRho_mk]
  exact uc22br_gt_mk_eq_one_iff hV x

theorem uc22p22f_pCore_quotient {L : Type*} [Group L] :
    CFSG.pCore 2 (L ⧸ CFSG.pCore 2 L) = ⊥ := by
  set N : Subgroup L := CFSG.pCore 2 L with hN
  set K : Subgroup L := (CFSG.pCore 2 (L ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := L ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := L) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  haveI : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem uc22p22f_exists_lift {p : ℕ} [hp : Fact p.Prime] {X S : Type*} [Group X] [Finite X]
    [Group S] (π : X →* S) (hπ : Function.Surjective π) (hker : p.Coprime (Nat.card π.ker))
    (Q : Subgroup S) (hQ : IsPGroup p Q) :
    ∃ R : Subgroup X, R.map π = Q ∧ Function.Injective (π.comp R.subtype) := by
  set P := Q.comap π
  let πP : P →* Q := (π.comp P.subtype).codRestrict Q (fun x => x.2)
  have hπP : Function.Surjective πP := by
    intro y
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨⟨x, by change π x ∈ Q; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  obtain ⟨T, hT⟩ := CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift p hp.out πP hπP hQ
  set R := (T : Subgroup P).map P.subtype
  have hRp : IsPGroup p R := T.isPGroup'.map P.subtype
  refine ⟨R, ?_, CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup p hp.out
    π hker R hRp⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact x.2
  · intro y hy
    have : (⟨y, hy⟩ : Q) ∈ (T : Subgroup P).map πP := by rw [hT]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩

theorem uc22p22f_rho_inj (M : Subgroup G) {V : Subgroup G} (hV : M ≤ normalizer (V : Set G))
    (hker : CFSG.pCore 2 ↥M ≤ (kerAct M V).normalCore)
    (h10 : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf q Q (barPreimage M (CFSG.pCore q (Bar2 M))) →
      1 < CFSG.Open.pRank q Q → Q ⊓ centralizer (V : Set G) = ⊥)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (E : Subgroup (Bar2 M))
    (hEle : E ≤ CFSG.pCore q (Bar2 M)) (hEel : CFSG.Open.IsElemAbelian q E)
    (hEcard : Nat.card E = q ^ 2) :
    ∀ e ∈ E, uc22p22fRho M V hker e = 1 → e = 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkercop : q.Coprime (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  obtain ⟨R, hRmap, hRinj⟩ := uc22p22f_exists_lift π hπ hkercop E hEel.isPGroup
  let φ : ↥R →* ↥E := (π.comp R.subtype).codRestrict E (fun x => by
    have : π (x : ↥M) ∈ R.map π := ⟨x, x.2, rfl⟩
    rw [hRmap] at this
    exact this)
  have hφinj : Function.Injective φ := fun a b hab => hRinj (congrArg Subtype.val hab)
  have hφsurj : Function.Surjective φ := by
    intro e
    have : (e : Bar2 M) ∈ R.map π := by rw [hRmap]; exact e.2
    obtain ⟨r, hr, hre⟩ := this
    exact ⟨⟨r, hr⟩, Subtype.ext hre⟩
  have hRp : IsPGroup q ↥R := hEel.isPGroup.of_injective φ hφinj
  have hcard : Nat.card ↥R = q ^ 2 := by
    rw [Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)]
    exact hEcard
  have hcomm : ∀ a b : ↥R, a * b = b * a := by
    haveI := hEel.1
    intro a b
    exact hφinj (by rw [map_mul, map_mul]; exact mul_comm' _ _)
  have hpow : ∀ a : ↥R, a ^ q = 1 := by
    intro a
    apply hφinj
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using hEel.2 ((φ a : ↥E) : Bar2 M) (φ a).2)
  set E' : Subgroup G := R.map M.subtype with hE'
  set W : Subgroup G := barPreimage M (CFSG.pCore q (Bar2 M)) with hW
  have hE'W : E' ≤ W := by
    rintro _ ⟨r, hr, rfl⟩
    refine uc22p21c_mem_barPreimage.2 ⟨r.2, ?_⟩
    have : π r ∈ R.map π := ⟨r, hr, rfl⟩
    rw [hRmap] at this
    exact hEle this
  have hE'q : IsPGroup q ↥E' := hRp.map M.subtype
  obtain ⟨S, hS⟩ := (hE'q.comap_subtype : IsPGroup q (E'.subgroupOf W)).exists_le_sylow
  set Q : Subgroup G := (S : Subgroup ↥W).map W.subtype with hQdef
  have hQ : CFSG.ABGLocalTools.IsSylowOf q Q W := ⟨S, rfl⟩
  have hE'Q : E' ≤ Q := by
    intro x hx
    have : (⟨x, hE'W hx⟩ : ↥W) ∈ E'.subgroupOf W := hx
    exact ⟨_, hS this, rfl⟩
  have hrank : 2 ≤ CFSG.Open.pRank q Q := by
    refine CFSG.SectionRank.le_pRank_of_injective hq.one_lt hcomm hpow hcard
      (M.subtype.comp R.subtype) (M.subtype_injective.comp R.subtype_injective) ?_
    rintro _ ⟨r, rfl⟩
    exact hE'Q ⟨r, r.2, rfl⟩
  have hQV := h10 q hq hq2 Q hQ (by omega)
  intro e he hρe
  have he' : e ∈ R.map π := by rw [hRmap]; exact he
  obtain ⟨r, hr, hre⟩ := he'
  have hre' : (QuotientGroup.mk r : Bar2 M) = e := hre
  rw [← hre', uc22p22fRho_eq_one_iff hV hker] at hρe
  have hrQ : (r : G) ∈ Q ⊓ centralizer (V : Set G) := ⟨hE'Q ⟨r, hr, rfl⟩, hρe⟩
  rw [hQV, Subgroup.mem_bot] at hrQ
  have hr1 : r = 1 := Subtype.ext hrQ
  rw [← hre, hr1, map_one]

theorem uc22p22f_fitting_cyclic (D : Data G) (Ch : Choice2011 G) (h10 : S22_10 D Ch)
    (h11 : S22_11 D Ch) (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) :
    IsCyclic ↥(CFSG.fittingSubgroup ↥(_root_.commutator (Bar2 D.M))) := by
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hker := uc22p22f_pCore_le_ker c.hVM hred
  have hcycbar : IsCyclic ↥(_root_.commutator (MBar D.M c.V) ⊓
      CFSG.fittingSubgroup (MBar D.M c.V)) :=
    (uc22p22f_isCyclic_fitting_iff _).1 (h11 h1930 c).1
  rw [uc22p22f_isCyclic_fitting_iff]
  refine uc22p22f_cyclic_fitting_of_injective (uc22p22fRho D.M c.V hker)
    (uc22p22fRho_surjective hker) uc22p22f_pCore_quotient ?_ hcycbar
  intro q hq hq2 E hEle hEel hEcard
  exact uc22p22f_rho_inj D.M c.hVM hker
    (fun q hq hq2 Q hQ hrank => h10 h1930 c q hq hq2 Q hQ hrank) q hq hq2 E hEle hEel hEcard

end Bridge

section YPart

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_normalizer_barPreimage (M : Subgroup G) (Y : Subgroup (Bar2 M)) [Y.Normal] :
    M ≤ normalizer (barPreimage M Y : Set G) := by
  intro m hm
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  obtain ⟨hnM, hnY⟩ := uc22p21c_mem_barPreimage.1 hn
  have hmem : m * n * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hnM) (M.inv_mem hm)
  refine uc22p21c_mem_barPreimage.2 ⟨hmem, ?_⟩
  have e : (⟨m * n * m⁻¹, hmem⟩ : ↥M) = ⟨m, hm⟩ * ⟨n, hnM⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv]
  exact Normal.conj_mem inferInstance _ hnY _

theorem uc22p22f_exists_conj_sylow {p : ℕ} [Fact p.Prime] {K P P' : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hP' : CFSG.ABGLocalTools.IsSylowOf p P' K) :
    ∃ k ∈ K, P' = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) Q Q'
  refine ⟨g, g.2, ?_⟩
  rw [← hg]
  ext x
  simp only [Sylow.coe_subgroup_smul, Subgroup.mem_map,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · refine ⟨g⁻¹ * y * g, ?_, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using hy
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hz
    · simp [MulAut.conj_apply]

theorem uc22p22f_sylow_in_Y {M P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPM : P ≤ M) (hPp : IsPGroup p ↥P) :
    CFSG.ABGLocalTools.IsSylowOf p P (barPreimage M (barImage M P)) ∧
      ∃ n : ℕ, Nat.card (barPreimage M (barImage M P)) = 2 ^ n * Nat.card P := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π : ↥M →* Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set O : Subgroup ↥M := CFSG.pCore 2 ↥M with hO
  set P' : Subgroup ↥M := P.subgroupOf M with hP'
  set Y' : Subgroup ↥M := (barImage M P).comap π with hY'
  have hbarImage : barImage M P = P'.map π := rfl
  have hY'eq : Y' = P' ⊔ O := by
    rw [hY', hbarImage, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hrel : ∃ n : ℕ, P'.relIndex Y' = 2 ^ n := by
    rw [hY'eq, sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal O P']
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).index (P'.subgroupOf O)
  have hSyl' : CFSG.ABGLocalTools.IsSylowOf p P' Y' := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨?_, hPp.comap_subtype, ?_⟩
    · rw [hY'eq]; exact le_sup_left
    · obtain ⟨n, hn⟩ := hrel
      rw [hn]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hPmap : P'.map M.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPM
  have hYmap : Y'.map M.subtype = barPreimage M (barImage M P) := rfl
  refine ⟨?_, ?_⟩
  · have := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M).2 hSyl'
    rw [hPmap, hYmap] at this
    exact this
  · obtain ⟨n, hn⟩ := hrel
    refine ⟨n, ?_⟩
    have hc1 : Nat.card (Y'.map M.subtype) = Nat.card Y' :=
      Subgroup.card_map_of_injective M.subtype_injective
    have hc2 : Nat.card (P'.map M.subtype) = Nat.card P' :=
      Subgroup.card_map_of_injective M.subtype_injective
    have h1 := Subgroup.relIndex_mul_card P' Y'
    rw [inf_eq_left.2 (show P' ≤ Y' by rw [hY'eq]; exact le_sup_left), hn] at h1
    rw [← hYmap, hc1, ← h1, ← hc2, hPmap]

end YPart

section Permutes

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_pCoreOf_le_T (D : Data G) : pCoreOf 2 D.M ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  have h := CFSG.fitting_pCore_le_sylow S
  rw [hS] at h
  exact Subgroup.map_le_iff_le_comap.2 h

theorem uc22p22f_conj_decomp {M R : Subgroup G} (hRM : R ≤ M) (hR : (barImage M R).Normal)
    {m r : G} (hm : m ∈ M) (hr : r ∈ R) :
    ∃ r' ∈ R, (∃ o ∈ pCoreOf 2 M, m * r * m⁻¹ = r' * o) ∧
      (∃ o ∈ pCoreOf 2 M, m * r * m⁻¹ = o * r') := by
  have hx : m * r * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm (hRM hr)) (M.inv_mem hm)
  set x : ↥M := ⟨m * r * m⁻¹, hx⟩ with hxdef
  have hπx : uc22p21cPi M x ∈ barImage M R := by
    have e : x = ⟨m, hm⟩ * ⟨r, hRM hr⟩ * (⟨m, hm⟩ : ↥M)⁻¹ := Subtype.ext rfl
    have hrR : uc22p21cPi M ⟨r, hRM hr⟩ ∈ barImage M R :=
      uc22p21c_mem_barImage.2 ⟨⟨r, hRM hr⟩, hr, rfl⟩
    rw [e, map_mul, map_mul, map_inv]
    exact Normal.conj_mem hR _ hrR _
  obtain ⟨m', hm'R, hm'⟩ := uc22p21c_mem_barImage.1 hπx
  refine ⟨(m' : G), hm'R, ⟨((m')⁻¹ * x : ↥M), ?_, ?_⟩, ⟨(x * m'⁻¹ : ↥M), ?_, ?_⟩⟩
  · refine ⟨(m')⁻¹ * x, ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).1
    show uc22p21cPi M ((m')⁻¹ * x) = 1
    rw [map_mul, map_inv, hm', inv_mul_cancel]
  · simp [hxdef]
  · refine ⟨x * m'⁻¹, ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).1
    show uc22p21cPi M (x * m'⁻¹) = 1
    rw [map_mul, map_inv, hm', mul_inv_cancel]
  · simp [hxdef]

theorem uc22p22f_permutes (D : Data G) {R : Subgroup G} (hRM : R ≤ D.M)
    (hR : (barImage D.M R).Normal) : Permutes R D.T := by
  have hO : ∀ o ∈ pCoreOf 2 D.M, o ∈ D.T := fun o ho => uc22p22f_pCoreOf_le_T D ho
  have hTM : D.T ≤ D.M := D.sylowM.le
  unfold Permutes
  ext z
  rw [Set.mem_mul, Set.mem_mul]
  constructor
  · rintro ⟨r, hr, t, ht, rfl⟩
    obtain ⟨r', hr', -, o, ho, hdec⟩ := uc22p22f_conj_decomp hRM hR (hTM (D.T.inv_mem ht)) hr
    refine ⟨t * o, D.T.mul_mem ht (hO o ho), r', hr', ?_⟩
    have : t⁻¹ * r * t⁻¹⁻¹ = o * r' := hdec
    have e : r * t = t * (t⁻¹ * r * t⁻¹⁻¹) := by group
    calc t * o * r' = t * (o * r') := by group
      _ = t * (t⁻¹ * r * t⁻¹⁻¹) := by rw [this]
      _ = r * t := e.symm
  · rintro ⟨t, ht, r, hr, rfl⟩
    obtain ⟨r', hr', ⟨o, ho, hdec⟩, -⟩ := uc22p22f_conj_decomp hRM hR (hTM ht) hr
    refine ⟨r', hr', o * t, D.T.mul_mem (hO o ho) ht, ?_⟩
    have e : t * r = (t * r * t⁻¹) * t := by group
    calc r' * (o * t) = (r' * o) * t := by group
      _ = (t * r * t⁻¹) * t := by rw [hdec]
      _ = t * r := e.symm

end Permutes

section BLemmas

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_odd_card_B {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) :
    Odd (Nat.card c.B) := by
  by_contra h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card c.B := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B) 2 h2
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB b.2
  rw [Subgroup.orderOf_coe, hb] at hodd
  exact absurd hodd (by decide)

theorem uc22p22f_not_dvd_card_B (D : Data G) (Ch : Choice2011 G) (h8 : S22_8 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) : ¬ p ∣ Nat.card c.B := by
  intro hdvd
  have hps : p ∈ D.sig1 := (h8 h1930 c) ▸ hp
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hsp' := hsp p hps
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B) p hdvd
  set A : Subgroup G := Subgroup.zpowers (b : G) with hA
  have hAB : A ≤ c.B := Subgroup.zpowers_le.2 b.2
  have hAM : A ≤ D.M := hAB.trans (c.hle.trans c.hBM)
  have hAcard : Nat.card A = p := by
    rw [hA, Nat.card_zpowers, Subgroup.orderOf_coe, hb]
  apply s21_2 D Ch h1930 c.toCtx22.toCtx21 A hAB
  intro g hg
  by_contra hgM
  apply hsp'.2.2 g hgM
  have hAle : A ≤ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := by
    refine le_inf hAM ?_
    intro a ha
    have hg' : g⁻¹ ∈ normalizer (A : Set G) := Subgroup.inv_mem _ hg
    have h1 : g⁻¹ * a * g⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg' a).1 ha
    rw [inv_inv] at h1
    exact ⟨g⁻¹ * a * g, hAM h1, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [← hAcard]
  exact Subgroup.card_dvd_of_le hAle

end BLemmas

section Cent

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_P2_cent (D : Data G) (Ch : Choice2011 G) (h11 : S22_11 D Ch) (hV : S22_V D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p.Prime) {P₂ : Subgroup G}
    (hP₂M : P₂ ≤ D.M) (hP₂p : IsPGroup p ↥P₂) (hnorm : (barImage D.M P₂).Normal)
    (hcomm : barImage D.M P₂ ≤ _root_.commutator (Bar2 D.M)) (hPB : ⁅P₂, c.B⁆ = P₂) :
    P₂ ≤ centralizer (c.V : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hker := uc22p22f_pCore_le_ker c.hVM hred
  have hρsurj := uc22p22fRho_surjective hker
  have hBM : c.B ≤ D.M := c.hle.trans c.hBM
  set R : Subgroup (Bar2 D.M) := barImage D.M P₂ with hR
  haveI hRn : R.Normal := hnorm
  have hRp : IsPGroup p ↥R := by
    have : IsPGroup p ↥(P₂.subgroupOf D.M) := hP₂p.comap_subtype
    exact this.map _
  have hRmap : R.map (uc22p22fRho D.M c.V hker) ≤
      _root_.commutator (MBar D.M c.V) ⊓ CFSG.fittingSubgroup (MBar D.M c.V) := by
    refine le_inf ?_ ?_
    · calc R.map (uc22p22fRho D.M c.V hker)
          ≤ (_root_.commutator (Bar2 D.M)).map (uc22p22fRho D.M c.V hker) :=
            Subgroup.map_mono hcomm
        _ = _root_.commutator (MBar D.M c.V) := by
          rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
            Subgroup.map_top_of_surjective _ hρsurj]
    · have hn : (R.map (uc22p22fRho D.M c.V hker)).Normal := hRn.map _ hρsurj
      haveI : Group.IsNilpotent ↥(R.map (uc22p22fRho D.M c.V hker)) :=
        (hRp.map (uc22p22fRho D.M c.V hker)).isNilpotent
      exact le_sSup ⟨hn, inferInstance⟩
  have hcent := (h11 h1930 c).2
  rw [CFSG.LocalCores.fitting_normal_intersection] at hcent
  rw [← hPB]
  refine Subgroup.commutator_le.2 fun x hx b hb => ?_
  have hxM : x ∈ D.M := hP₂M hx
  have hbM : b ∈ D.M := hBM hb
  have hxR : (QuotientGroup.mk ⟨x, hxM⟩ : Bar2 D.M) ∈ R :=
    uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx, rfl⟩
  have hρx : (QuotientGroup.mk ⟨x, hxM⟩ : MBar D.M c.V) ∈
      _root_.commutator (MBar D.M c.V) ⊓ CFSG.fittingSubgroup (MBar D.M c.V) := by
    apply hRmap
    refine ⟨QuotientGroup.mk ⟨x, hxM⟩, hxR, ?_⟩
    exact uc22p22fRho_mk hker ⟨x, hxM⟩
  have hbB : (QuotientGroup.mk ⟨b, hbM⟩ : MBar D.M c.V) ∈ mbarImage D.M c.V c.B :=
    ⟨⟨b, hbM⟩, hb, rfl⟩
  have hcomm' := Subgroup.mem_centralizer_iff.1 (hcent hbB) _ hρx
  have h1 : (QuotientGroup.mk ⁅(⟨x, hxM⟩ : ↥D.M), ⟨b, hbM⟩⁆ : MBar D.M c.V) = 1 := by
    show (QuotientGroup.mk' (kerAct D.M c.V).normalCore) ⁅(⟨x, hxM⟩ : ↥D.M), ⟨b, hbM⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm'
  exact (uc22br_gt_mk_eq_one_iff c.hVM _).1 h1

theorem uc22p22f_cent_U (D : Data G) (Ch : Choice2011 G) (h11 : S22_11 D Ch) (hV : S22_V D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P₂ : Subgroup G}
    (hP₂M : P₂ ≤ D.M) (hP₂p : IsPGroup p ↥P₂) (hnorm : (barImage D.M P₂).Normal)
    (hcomm : barImage D.M P₂ ≤ _root_.commutator (Bar2 D.M)) (hPB : ⁅P₂, c.B⁆ = P₂) :
    P₂ ≤ centralizer (D.U : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : D.U ≤ pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ∧ IsElemAbelian 2 D.U :=
    uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  have hMU : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  have hP₂U : P₂ ≤ normalizer (D.U : Set G) := hP₂M.trans hMU
  set X : Subgroup G := ⁅D.U, P₂⁆ with hX
  have hXU : X ≤ D.U := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hP₂U
  have hXinv : ∀ m ∈ D.M, X.map (MulAut.conj m).toMonoidHom ≤ X := by
    intro m hm
    have hUm : D.U.map (MulAut.conj m).toMonoidHom = D.U := by
      have := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMU hm)
      simpa only [MulEquiv.toMonoidHom_eq_coe] using this
    rw [hX, Subgroup.map_commutator, hUm]
    refine Subgroup.commutator_le.2 fun u hu z hz => ?_
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨x', hx', ⟨o, ho, hdec⟩, -⟩ := uc22p22f_conj_decomp hP₂M hnorm hm hx
    have hdec' : (MulAut.conj m).toMonoidHom x = x' * o := by
      simpa [MulAut.conj_apply] using hdec
    have hou : Commute o u := by
      have := Subgroup.mem_centralizer_iff.1 (hU.1 hu).2 o ho
      exact this
    have e : ⁅u, x' * o⁆ = ⁅u, x'⁆ := by
      have h1 : o * u⁻¹ = u⁻¹ * o := (Commute.inv_right hou).eq
      calc ⁅u, x' * o⁆ = u * x' * (o * u⁻¹) * o⁻¹ * x'⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = u * x' * (u⁻¹ * o) * o⁻¹ * x'⁻¹ := by rw [h1]
        _ = ⁅u, x'⁆ := by simp only [commutatorElement_def]; group
    rw [hdec', e]
    exact Subgroup.commutator_mem_commutator hu hx'
  by_contra hne
  have hX1 : X ≠ ⊥ := by
    intro hX0
    apply hne
    have : ⁅P₂, D.U⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hX0
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨W, ⟨hWne, hWX, hMW⟩, hWmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {W : Subgroup G | W ≠ ⊥ ∧ W ≤ X ∧ D.M ≤ normalizer (W : Set G)} ⟨X, hX1, le_rfl, by
      intro m hm
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine le_antisymm (hXinv m hm) ?_
      intro y hy
      refine ⟨m⁻¹ * y * m, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := hXinv m⁻¹ (D.M.inv_mem hm) ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using this⟩
  have hWirr : IrrOn D.M W := by
    intro W' hW'W hMW'
    by_cases hW'0 : W' = ⊥
    · exact Or.inl hW'0
    · right
      by_contra hne'
      exact hWmin W' ⟨hW'0, hW'W.trans hWX, hMW'⟩ (lt_of_le_of_ne hW'W hne')
  have hWU : W ≤ D.U := hWX.trans hXU
  let c' : Ctx22b D Ch := { c with V := W, hVU := hWU, hVne := hWne, hVM := hMW, hVirr := hWirr }
  have hWc : P₂ ≤ centralizer (W : Set G) :=
    uc22p22f_P2_cent D Ch h11 hV h1930 c' hp hP₂M hP₂p hnorm hcomm hPB
  have hab : ∀ x y : ↥D.U, x * y = y * x := by
    haveI := hU.2.1
    intro x y
    exact mul_comm' x y
  have hcop : Nat.Coprime (Nat.card P₂) (Nat.card D.U) := by
    obtain ⟨k, hk⟩ := hP₂p.exists_card_eq
    obtain ⟨l, hl⟩ := hU.2.isPGroup.exists_card_eq
    rw [hk, hl]
    exact Nat.Coprime.pow k l ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨-, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp D.U P₂ hP₂U hab hcop
  have hW1 : W ≤ D.U ⊓ centralizer (P₂ : Set G) := by
    refine le_inf hWU fun w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.1 (hWc hx) w hw).symm
  exact hWne (eq_bot_iff.2 fun w hw => hdisj.le_bot ⟨hW1 hw, hWX hw⟩)

end Cent

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] def NormL0 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ P : Subgroup G, IsPGroup p ↥P → IsCyclic ↥P →
    P ≤ D.M → P ≤ centralizer (D.U : Set G) → Permutes P D.T → c.B ≤ normalizer (P : Set G) →
    ⁅P, c.B⁆ = P → P ≤ normalizer (c.L0 : Set G)

@[expose] def ConjNormL0 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ P : Subgroup G, IsPGroup p ↥P → IsCyclic ↥P →
    P ≤ D.M → P ≤ centralizer (D.U : Set G) → Permutes P D.T → c.B ≤ normalizer (P : Set G) →
    ⁅P, c.B⁆ = P → ∀ x ∈ P,
      c.L0 ≤ normalizer ((c.L0.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G)

theorem normL0_of_conjNorm (D : Data G) (Ch : Choice2011 G) (h : ConjNormL0 D Ch) :
    NormL0 D Ch := by
  intro h1930 c p hpσ P hPp hPcyc hPM hPU hPperm hBP hPB
  have hBL : c.B ≤ c.L0 := c.hB.1
  have hmem : ∀ {g y : G}, y ∈ c.L0.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ c.L0 := by
    intro g y
    rw [Subgroup.mem_map_equiv]
    simp
  rw [← hPB]
  refine Subgroup.commutator_le.2 fun x hx b hb => ?_
  have hbN : b ∈ normalizer ((c.L0.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) :=
    h h1930 c p hpσ P hPp hPcyc hPM hPU hPperm hBP hPB x hx (hBL hb)
  rw [Subgroup.mem_normalizer_iff] at hbN ⊢
  intro y
  have e : x * b * x⁻¹ * b⁻¹ * y * (x * b * x⁻¹ * b⁻¹)⁻¹ =
      x * (b * (x⁻¹ * (b⁻¹ * y * b) * x) * b⁻¹) * x⁻¹ := by group
  have h1 : y ∈ c.L0 ↔ b⁻¹ * y * b ∈ c.L0 := by
    constructor
    · intro hy
      exact c.L0.mul_mem (c.L0.mul_mem (c.L0.inv_mem (hBL hb)) hy) (hBL hb)
    · intro hy
      have := c.L0.mul_mem (c.L0.mul_mem (hBL hb) hy) (c.L0.inv_mem (hBL hb))
      simpa [mul_assoc] using this
  have h2 : b⁻¹ * y * b ∈ c.L0 ↔ x⁻¹ * (b⁻¹ * y * b) * x ∈ c.L0.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [hmem]
    simp [mul_assoc]
  have h3 := hbN (x⁻¹ * (b⁻¹ * y * b) * x)
  have h4 : b * (x⁻¹ * (b⁻¹ * y * b) * x) * b⁻¹ ∈ c.L0.map (MulAut.conj x⁻¹).toMonoidHom ↔
      x * (b * (x⁻¹ * (b⁻¹ * y * b) * x) * b⁻¹) * x⁻¹ ∈ c.L0 := by
    rw [hmem]
    simp [mul_assoc]
  rw [commutatorElement_def, e, ← h4, ← h3, ← h2, ← h1]

@[expose] def Cent2010 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p ↥P →
    P ≤ c.L0 → P ≤ D.M → c.B ≤ normalizer (P : Set G) → ⁅c.B, P⁆ = ⊥

@[expose] def Last2212 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ P : Subgroup G, IsPGroup p ↥P → IsCyclic ↥P →
    P ≤ D.M → P ≤ centralizer (D.U : Set G) → Permutes P D.T → c.B ≤ normalizer (P : Set G) →
    ⁅P, c.B⁆ = P → P = ⊥

theorem last2212_of (D : Data G) (Ch : Choice2011 G) (hN : NormL0 D Ch) (hC : Cent2010 D Ch) :
    Last2212 D Ch := by
  intro h1930 c p hpσ P hPp hPcyc hPM hPU hPperm hBP hPB
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  have hNL : P ≤ normalizer (c.L0 : Set G) := hN h1930 c p hpσ P hPp hPcyc hPM hPU hPperm hBP hPB
  have hBL : c.B ≤ c.L0 := c.hB.1
  have hcommL : ⁅c.B, P⁆ ≤ c.L0 := by
    refine Subgroup.commutator_le.2 fun b hb x hx => ?_
    have h1 : x * b⁻¹ * x⁻¹ ∈ c.L0 :=
      (Subgroup.mem_normalizer_iff.1 (hNL hx) b⁻¹).1 (c.L0.inv_mem (hBL hb))
    have e : ⁅b, x⁆ = b * (x * b⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact c.L0.mul_mem (hBL hb) h1
  have hPL : P ≤ c.L0 := by
    have : P = ⁅c.B, P⁆ := by rw [Subgroup.commutator_comm]; exact hPB.symm
    rw [this]
    exact hcommL
  have hbot : ⁅c.B, P⁆ = ⊥ := hC h1930 c.toCtx22.toCtx21 p hpp hp2 P hPp hPL hPM hBP
  rw [← hPB, Subgroup.commutator_comm]
  exact hbot

theorem s22_12_of_last (D : Data G) (Ch : Choice2011 G) (h10 : S22_10 D Ch) (h11 : S22_11 D Ch)
    (h2123 : S21_23 D Ch) (hV : S22_V D Ch) (h8 : S22_8 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hL : Last2212 D Ch) : S22_12 D Ch := by
  classical
  intro h1930 c p hpσ P hP
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcyc := uc22p22f_fitting_cyclic D Ch h10 h11 hV h1930 c
  obtain ⟨h1, h2, h3a, h3b, h3c⟩ := h2123 h1930 c.toCtx22.toCtx21 p hpσ P hP hcyc
  refine ⟨⟨h1, h2, h3a, h3b, h3c⟩, ?_⟩
  have hPM : P ≤ D.M := hP.le.trans (uc22p21c_barPreimage_le _ _)
  have hPp : IsPGroup p ↥P := hP.isPGroup
  haveI hbn : (barImage D.M P).Normal := h3b
  haveI hbc : IsCyclic ↥(barImage D.M P) := by
    haveI : IsCyclic ↥(P.subgroupOf D.M) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPM).symm.toMonoidHom
        (MulEquiv.surjective _)
    exact isCyclic_of_surjective
      (MonoidHom.subgroupMap (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) (P.subgroupOf D.M))
      (MonoidHom.subgroupMap_surjective _ _)
  obtain ⟨hPY, n, hYcard⟩ := uc22p22f_sylow_in_Y hpp hp2 hPM hPp
  set Y := barPreimage D.M (barImage D.M P) with hY
  have hYM : Y ≤ D.M := uc22p21c_barPreimage_le _ _
  have hMY : D.M ≤ normalizer (Y : Set G) := uc22p22f_normalizer_barPreimage D.M _
  have hBM : c.B ≤ D.M := c.hle.trans c.hBM
  have hBY : c.B ≤ normalizer (Y : Set G) := hBM.trans hMY
  have hpB : ¬ p ∣ Nat.card c.B := uc22p22f_not_dvd_card_B D Ch h8 hsp h1930 c hpσ
  have hBodd : Odd (Nat.card c.B) := uc22p22f_odd_card_B c.toCtx22.toCtx21
  have hcopP : Nat.Coprime (Nat.card c.B) (Nat.card P) := by
    obtain ⟨m, hm⟩ := hPp.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpB).symm
  have hcopY : Nat.Coprime (Nat.card c.B) (Nat.card Y) := by
    rw [hYcard]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hBodd)) hcopP
  haveI : Group.IsSolvable ↥c.B := by
    haveI := c.hB.2.1
    infer_instance
  obtain ⟨P₁, hP₁Y, hBP₁⟩ := CFSG.GH74.Uniqueness.exists_sylow_normalized_of_coprime hBY hcopY p
  obtain ⟨g, hgY, hP₁eq⟩ := uc22p22f_exists_conj_sylow hPY hP₁Y
  refine ⟨g, hYM hgY, ?_⟩
  rw [← hP₁eq]
  have hP₁p : IsPGroup p ↥P₁ := hP₁Y.isPGroup
  have hP₁M : P₁ ≤ D.M := hP₁Y.le.trans hYM
  have hP₁cyc : IsCyclic ↥P₁ := by
    rw [hP₁eq]
    exact isCyclic_of_surjective
      (P.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom
      (MulEquiv.surjective _)
  haveI := hP₁cyc
  have hP₁comm : ∀ x y : ↥P₁, x * y = y * x := fun x y => mul_comm' x y
  have hcopP₁ : Nat.Coprime (Nat.card c.B) (Nat.card P₁) := by
    rw [hP₁eq, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcopP
  set P₂ : Subgroup G := ⁅P₁, c.B⁆ with hP₂
  have hP₂P₁ : P₂ ≤ P₁ := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hBP₁
  have hBP₂ : c.B ≤ normalizer (P₂ : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hBP₁
  have hP₂B : ⁅P₂, c.B⁆ = P₂ :=
    CFSG.QuasithinUnique.Setup.Layer.commutator_commutator_eq P₁ c.B hBP₁ hP₁comm hcopP₁
  have hP₂p : IsPGroup p ↥P₂ := hP₁p.to_le hP₂P₁
  have hP₂M : P₂ ≤ D.M := hP₂P₁.trans hP₁M
  have hP₂Y : P₂ ≤ Y := hP₂P₁.trans hP₁Y.le
  have hP₂bar : barImage D.M P₂ ≤ barImage D.M P := by
    intro q hq
    obtain ⟨m, hmR, rfl⟩ := uc22p21c_mem_barImage.1 hq
    exact (uc22p21c_mem_barPreimage.1 (hP₂Y hmR)).2
  haveI hP₂norm : (barImage D.M P₂).Normal := uc22p21c_normal_of_le_cyclic_normal hP₂bar
  have hP₂comm : barImage D.M P₂ ≤ _root_.commutator (Bar2 D.M) :=
    hP₂bar.trans (h3a.trans inf_le_right)
  have hP₂U : P₂ ≤ centralizer (D.U : Set G) :=
    uc22p22f_cent_U D Ch h11 hV h1930 c hpp hp2 hP₂M hP₂p hP₂norm hP₂comm hP₂B
  have hP₂perm : Permutes P₂ D.T := uc22p22f_permutes D hP₂M hP₂norm
  have hP₂cyc : IsCyclic ↥P₂ := Subgroup.isCyclic_of_le hP₂P₁
  have hP₂bot : P₂ = ⊥ := hL h1930 c p hpσ P₂ hP₂p hP₂cyc hP₂M hP₂U hP₂perm hBP₂ hP₂B
  intro b hb x hx
  have hx' : ⁅x, b⁆ ∈ P₂ := Subgroup.commutator_mem_commutator hx hb
  rw [hP₂bot, Subgroup.mem_bot] at hx'
  exact (commutatorElement_eq_one_iff_mul_comm.1 hx').symm

theorem s22_12_of (D : Data G) (Ch : Choice2011 G) (h10 : S22_10 D Ch) (h11 : S22_11 D Ch)
    (h2123 : S21_23 D Ch) (hV : S22_V D Ch) (h8 : S22_8 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hN : NormL0 D Ch) (hC : Cent2010 D Ch) : S22_12 D Ch :=
  s22_12_of_last D Ch h10 h11 h2123 hV h8 hsp (last2212_of D Ch hN hC)

end Main

section Card

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_exists_maxTwoLocal_ge {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  set S : Set (Subgroup G) := {M | IsTwoLocal M ∧ H ≤ M} with hS
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ :=
    Set.exists_max_image S (fun M => Nat.card M) (Set.toFinite S) ⟨H, hH, le_rfl⟩
  refine ⟨M, ⟨hM, fun K hK hMK => ?_⟩, hHM⟩
  have hKS : K ∈ S := ⟨hK, hHM.trans hMK⟩
  exact (Subgroup.eq_of_le_of_card_ge hMK (hmax K hKS)).symm

theorem uc22p22f_exists_fixed {V T : Subgroup G} (hV : IsPGroup 2 V) (hVne : V ≠ ⊥)
    (hT : IsPGroup 2 T) (hTV : T ≤ normalizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ t ∈ T, t * v * t⁻¹ = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hVne
  let φ : ↥T →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hTV)
  letI : MulAction ↥T ↥V := MulAction.compHom ↥V φ
  have hdvd : 2 ∣ Nat.card V := by
    obtain ⟨n, hn0, hn⟩ := hV.nontrivial_iff_card.1 inferInstance
    rw [hn]
    exact dvd_pow_self 2 hn0.ne'
  have h1 : (1 : ↥V) ∈ MulAction.fixedPoints ↥T ↥V := fun t => map_one (φ t)
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥V hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun t ht => ?_⟩
  have := hb ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem uc22p22f_exists_z {D : Data G} {Ch : Choice2011 G} (c : Ctx22b D Ch) :
    ∃ z ∈ c.V, z ≠ 1 ∧ z ∈ D.Z ∧ z ^ 2 = 1 := by
  have hU : D.U ≤ pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ∧ IsElemAbelian 2 D.U :=
    uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  have hVT : c.V ≤ D.T := (c.hVU.trans (hU.1.trans inf_le_left)).trans (uc22p22f_pCoreOf_le_T D)
  have hVel : IsElemAbelian 2 c.V :=
    ⟨⟨⟨fun a b => by
      have h := hU.2.1.is_comm.comm (⟨a, c.hVU a.2⟩ : D.U) ⟨b, c.hVU b.2⟩
      have h2 := congrArg Subtype.val h
      exact Subtype.ext h2⟩⟩, fun x hx => hU.2.2 x (c.hVU hx)⟩
  have hVp : IsPGroup 2 c.V := hVel.isPGroup
  have hTM : D.T ≤ normalizer (c.V : Set G) := D.sylowM.le.trans c.hVM
  obtain ⟨v, hvV, hv1, hvT⟩ := uc22p22f_exists_fixed hVp c.hVne D.sylowM.isPGroup hTM
  refine ⟨v, hvV, hv1, ?_, hVel.2 v hvV⟩
  refine CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.2
    ⟨hVT hvV, fun k hk => ?_, hVel.2 v hvV⟩
  have := hvT k hk
  calc k * v = (k * v * k⁻¹) * k := by group
    _ = v * k := by rw [this]

theorem uc22p22f_isTwoLocal_centralizer {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    IsTwoLocal (centralizer ({z} : Set G)) := by
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hmem : ∀ {x : G}, x ∈ Subgroup.zpowers z → x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      have h2 : z ^ (2 : ℤ) = 1 := by simpa using hz2
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      have h2 : z ^ (2 : ℤ) = 1 := by simpa using hz2
      rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  refine ⟨Subgroup.zpowers z, ?_, ?_, ?_⟩
  · intro h
    exact hz1 (Subgroup.zpowers_eq_bot.1 h)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  · ext g
    constructor
    · intro hg
      have hg' : g ∈ centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have : Commute g z := Subgroup.mem_centralizer_singleton_iff.1 hg
        exact ((this.symm.zpow_left k).eq)
      exact Subgroup.centralizer_le_normalizer _ hg'
    · intro hg
      have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z :=
        (Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_zpowers z)
      rcases hmem h1 with h | h
      · exact absurd (by simpa using h) hz1
      · rw [Subgroup.mem_centralizer_iff]
        rintro y rfl
        calc y * g = (g * y * g⁻¹) * g := by rw [h]
          _ = g * y := by group

theorem uc22p22f_card_cent_le (D : Data G) (Ch : Choice2011 G) (h63 : UC6.R6_3 D) (c : Ctx22b D Ch)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {P : Subgroup G} (hPM : P ≤ D.M) (hPq : IsPGroup q ↥P)
    (hPexp : ∀ x ∈ P, x ^ q = 1) (hΓ : rankThreeGamma 1 q P ≤ D.M) :
    Nat.card ↥(P ⊓ centralizer (c.V : Set G)) ≤ q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hlt
  push Not at hlt
  set A : Subgroup G := P ⊓ centralizer (c.V : Set G) with hA
  have hAP : A ≤ P := inf_le_left
  have hApg : IsPGroup q ↥A := hPq.to_le hAP
  have hAnc : ¬ IsCyclic ↥A := by
    intro hcyc
    have h5 : Monoid.exponent ↥A = Nat.card ↥A := IsCyclic.exponent_eq_card
    have hexp : ∀ x : ↥A, x ^ q = 1 := fun x =>
      Subtype.ext (by simpa using hPexp (x : G) (hAP x.2))
    have h6 : Monoid.exponent ↥A ∣ q := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    rw [h5] at h6
    exact absurd (Nat.le_of_dvd hq.pos h6) (not_le.2 hlt)
  haveI : Fact (IsPGroup q ↥A) := ⟨hApg⟩
  obtain ⟨E₀, -, hE₀card, hE₀el⟩ := CFSG.lemma_4_5_a hq2 hAnc
  set E : Subgroup G := E₀.map A.subtype with hE
  have hEA : E ≤ A := Subgroup.map_subtype_le _
  have hEel : IsElemAbelian q E :=
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q E₀).1 hE₀el).map _
  have hEcard : Nat.card E = q ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective A.subtype_injective]
    exact hE₀card
  have hEM : E ≤ D.M := hEA.trans (hAP.trans hPM)
  have hΓE : rankThreeGamma 1 q E ≤ D.M := by
    refine le_trans (sSup_le_sSup ?_) hΓ
    rintro N ⟨Q, hQE, hQ, rfl⟩
    exact ⟨Q, hQE.trans (hEA.trans hAP), hQ, rfl⟩
  have hU := h63 q hq hq2 E hEM hEel hEcard hΓE
  obtain ⟨z, hzV, hz1, hzZ, hz2⟩ := uc22p22f_exists_z c
  have hH2 : IsTwoLocal (centralizer ({z} : Set G)) :=
    uc22p22f_isTwoLocal_centralizer hz1 hz2
  have hEH : E ≤ centralizer ({z} : Set G) := by
    intro e he
    have heC : e ∈ centralizer (c.V : Set G) := (Subgroup.mem_inf.1 (hEA he)).2
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    exact Subgroup.mem_centralizer_iff.1 heC h hzV
  obtain ⟨N, hN, hHN⟩ := uc22p22f_exists_maxTwoLocal_ge hH2
  have hU' : calMOf E = {D.M} := hU
  have hNmem : N ∈ calMOf E := ⟨hN, hEH.trans hHN⟩
  rw [hU'] at hNmem
  have hNM : N = D.M := hNmem
  have hHM : centralizer ({z} : Set G) ≤ D.M := hNM ▸ hHN
  exact c.hC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)).trans hHM)

end Card

section Final

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22f_card_le_of_lt_sq {q : ℕ} (hq : q.Prime) {X : Subgroup G} (hX : IsPGroup q ↥X)
    (h : Nat.card ↥X < q ^ 2) : Nat.card ↥X ≤ q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk] at h ⊢
  by_contra hlt
  push Not at hlt
  have hk2 : 2 ≤ k := by
    by_contra h2
    push Not at h2
    have h2' := hq.two_le
    interval_cases k <;> simp at hlt <;> omega
  exact absurd h (not_lt.2 (Nat.pow_le_pow_right hq.pos hk2))

theorem uc22p22f_exists_E {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup G}
    (hXp : IsPGroup q ↥X) (hXexp : ∀ x ∈ X, x ^ q = 1) (hcard : q ^ 2 ≤ Nat.card ↥X) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian q E ∧ Nat.card ↥E = q ^ 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hlt : q < Nat.card ↥X :=
    lt_of_lt_of_le (by nlinarith [hq.one_lt]) hcard
  have hXnc : ¬ IsCyclic ↥X := by
    intro hcyc
    have h5 : Monoid.exponent ↥X = Nat.card ↥X := IsCyclic.exponent_eq_card
    have hexp : ∀ x : ↥X, x ^ q = 1 := fun x => Subtype.ext (by simpa using hXexp (x : G) x.2)
    have h6 : Monoid.exponent ↥X ∣ q := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    rw [h5] at h6
    exact absurd (Nat.le_of_dvd hq.pos h6) (not_le.2 hlt)
  haveI : Fact (IsPGroup q ↥X) := ⟨hXp⟩
  obtain ⟨E₀, -, hE₀card, hE₀el⟩ := CFSG.lemma_4_5_a hq2 hXnc
  refine ⟨E₀.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q E₀).1 hE₀el).map _
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hE₀card

theorem uc22p22f_two_le (D : Data G) (h63 : UC6.R6_3 D) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {P : Subgroup G} (hPM : P ≤ D.M) (hPq : IsPGroup q ↥P) (hPexp : ∀ x ∈ P, x ^ q = 1)
    (hΓ : rankThreeGamma 1 q P ≤ D.M) {N : Subgroup G} (hN : rankThreeIsMaxTwoLocal N)
    (hcard : q ^ 2 ≤ Nat.card ↥(P ⊓ N)) : N = D.M := by
  obtain ⟨E, hEX, hEel, hEcard⟩ :=
    uc22p22f_exists_E hq hq2 (hPq.to_le inf_le_left) (fun x hx => hPexp x hx.1) hcard
  have hEP : E ≤ P := hEX.trans inf_le_left
  have hEM : E ≤ D.M := hEP.trans hPM
  have hΓE : rankThreeGamma 1 q E ≤ D.M := by
    refine le_trans (sSup_le_sSup ?_) hΓ
    rintro N' ⟨Q, hQE, hQ, rfl⟩
    exact ⟨Q, hQE.trans hEP, hQ, rfl⟩
  have hU : calMOf E = {D.M} := h63 q hq hq2 E hEM hEel hEcard hΓE
  have hNmem : N ∈ calMOf E := ⟨hN, hEX.trans inf_le_right⟩
  rw [hU] at hNmem
  exact hNmem

theorem uc22p22f_card_ge_sq {q : ℕ} (hq : q.Prime) {R B : Subgroup G} (hR : IsPGroup q ↥R)
    (hBR : B ≤ R) (hB : Nat.card ↥B = q) {x : G} (hxR : x ∈ R) (hxB : x ∉ B) :
    q ^ 2 ≤ Nat.card ↥R := by
  by_contra h
  push Not at h
  have h1 : Nat.card ↥R ≤ q := uc22p22f_card_le_of_lt_sq hq hR h
  have h2 : B = R := Subgroup.eq_of_le_of_card_ge hBR (hB ▸ h1)
  exact hxB (h2 ▸ hxR)

theorem uc22p22f_normalizer_grows {q : ℕ} [Fact q.Prime] {W E : Subgroup G}
    (hW : IsPGroup q ↥W) (hEW : E ≤ W) (hne : ¬ W ≤ E) :
    ∃ x ∈ W, x ∈ normalizer (E : Set G) ∧ x ∉ E := by
  haveI : Group.IsNilpotent ↥W := hW.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥W)
  have hlt : E.subgroupOf W < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact hne
  have h := hnc _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hEW] at h
  obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt h
  exact ⟨x.1, x.2, Subgroup.mem_subgroupOf.1 hx1, fun hx => hx2 (Subgroup.mem_subgroupOf.2 hx)⟩

theorem uc22p22f_exists_normalizer_inf {q : ℕ} [Fact q.Prime] {P X E : Subgroup G}
    (hP : IsPGroup q ↥P) (hX : IsPGroup q ↥X) (hXP : X ≤ normalizer (P : Set G))
    (hXE : X ≤ E) (hEW : E ≤ X ⊔ P) (hPE : ¬ P ≤ E) :
    ∃ x ∈ P, x ∈ normalizer (E : Set G) ∧ x ∉ E := by
  have hW : IsPGroup q ↥(X ⊔ P) := hX.to_sup_of_normal_right' hP hXP
  have hne : ¬ (X ⊔ P) ≤ E := fun h => hPE (le_sup_right.trans h)
  obtain ⟨x, hxW, hxN, hxE⟩ := uc22p22f_normalizer_grows hW hEW hne
  have hmul : ((X ⊔ P : Subgroup G) : Set G) = (X : Set G) * P :=
    Subgroup.coe_mul_of_left_le_normalizer_right X P hXP
  have hxm : x ∈ (X : Set G) * (P : Set G) := by
    rw [← hmul]
    exact hxW
  obtain ⟨y, hy, p, hp, hxyp⟩ := Set.mem_mul.1 hxm
  subst hxyp
  refine ⟨p, hp, ?_, ?_⟩
  · have hyN : y⁻¹ ∈ normalizer (E : Set G) :=
      Subgroup.inv_mem _ (Subgroup.le_normalizer (hXE hy))
    have := Subgroup.mul_mem _ hyN hxN
    simpa using this
  · intro hpE
    exact hxE (E.mul_mem (hXE hy) hpE)

theorem uc22p22f_isPGroup_pCoreOf (K : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 K) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype

theorem uc22p22f_le_pCoreOf {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 ↥P)
    (hn : ∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) : P ≤ pCoreOf 2 K := by
  have hN : (P.subgroupOf K).Normal := ⟨fun x hx k => hn (k : G) k.2 x hx⟩
  have hQ : IsPGroup 2 ↥(P.subgroupOf K) := hP.comap_subtype
  have hle : P.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, hQ⟩
  intro x hx
  exact ⟨⟨x, hPK hx⟩, hle hx, rfl⟩

theorem uc22p22f_conj_mem_pCoreOf_self {K : Subgroup G} {k x : G} (hk : k ∈ K)
    (hx : x ∈ pCoreOf 2 K) : k * x * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem y hy ⟨k, hk⟩, rfl⟩

theorem uc22p22f_mem_normalizer_pCoreOf {K : Subgroup G} {n : G}
    (hn : ∀ k ∈ K, n * k * n⁻¹ ∈ K) (hn' : ∀ k ∈ K, n⁻¹ * k * n ∈ K) :
    n ∈ normalizer ((pCoreOf 2 K : Subgroup G) : Set G) := by
  have key : ∀ m : G, (∀ k ∈ K, m * k * m⁻¹ ∈ K) → (∀ k ∈ K, m⁻¹ * k * m ∈ K) →
      ∀ x ∈ pCoreOf 2 K, m * x * m⁻¹ ∈ pCoreOf 2 K := by
    intro m hm hm' x hx
    have hPK : (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hm y (Subgroup.map_subtype_le _ hy)
    have hP2 : IsPGroup 2 ↥((pCoreOf 2 K).map (MulAut.conj m).toMonoidHom) :=
      (uc22p22f_isPGroup_pCoreOf K).map _
    have hPn : ∀ k ∈ K, ∀ y ∈ (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom,
        k * y * k⁻¹ ∈ (pCoreOf 2 K).map (MulAut.conj m).toMonoidHom := by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hk' : m⁻¹ * k * m ∈ K := hm' k hk
      refine ⟨(m⁻¹ * k * m) * y * (m⁻¹ * k * m)⁻¹,
        uc22p22f_conj_mem_pCoreOf_self hk' hy, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      group
    exact uc22p22f_le_pCoreOf hPK hP2 hPn ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key n hn hn' x
  · intro hx
    have := key n⁻¹ (by simpa using hn') (by simpa using hn) _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem uc22p22f_mem_conj (H : Subgroup G) (g x : G) :
    x ∈ uniqueFourConj g H ↔ g * x * g⁻¹ ∈ H := by
  unfold uniqueFourConj
  rw [Subgroup.mem_map_equiv]
  simp

theorem uc22p22f_final_aux (D : Data G) (h63 : UC6.R6_3 D) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {P A P₁ D' M₁ M₂ : Subgroup G} {g z : G} (hPM : P ≤ D.M) (hPq : IsPGroup q ↥P)
    (hPexp : ∀ x ∈ P, x ^ q = 1) (hPcard : q ^ 2 ≤ Nat.card ↥P)
    (hΓ : rankThreeGamma 1 q P ≤ D.M) (hAP : A ≤ P) (hAcard : Nat.card ↥A = q) (hgM : g ∉ D.M)
    (hzO : z ∈ pCoreOf 2 D.M) (hz1 : z ≠ 1) (hzA : A ≤ centralizer ({z} : Set G))
    (hgz : g ∈ centralizer ({z} : Set G))
    (hP₁ : ∀ x, x ∈ P₁ ↔ g * x * g⁻¹ ∈ P) (hD' : ∀ x, x ∈ D' ↔ g * x * g⁻¹ ∈ A)
    (hM₁ : ∀ x, x ∈ M₁ ↔ g * x * g⁻¹ ∈ D.M) (hM₂ : ∀ x, x ∈ M₂ ↔ g⁻¹ * x * g ∈ D.M)
    (hM₁max : rankThreeIsMaxTwoLocal M₁) (hM₂max : rankThreeIsMaxTwoLocal M₂)
    (hP₁q : IsPGroup q ↥P₁) (hD'q : IsPGroup q ↥D') (hP₁card : Nat.card ↥P₁ = Nat.card ↥P)
    (hD'card : Nat.card ↥D' = q) (hD : D' ≤ normalizer (P : Set G))
    (hA : A ≤ normalizer (P₁ : Set G)) : False := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2le := hq.two_le
  have hMmax : rankThreeIsMaxTwoLocal D.M := D.maxLocal
  have hMself : normalizer (D.M : Set G) = D.M :=
    CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M hMmax
  have hgN : g ∉ normalizer (D.M : Set G) := by
    rw [hMself]
    exact hgM
  have hAq : IsPGroup q ↥A := hPq.to_le hAP
  have hrankA : 1 ≤ CFSG.Open.pRank q A := by
    haveI : IsCyclic ↥A := isCyclic_of_prime_card hAcard
    refine CFSG.SectionRank.le_pRank hq.one_lt le_rfl
      ⟨inferInstance, fun x hx => hPexp x (hAP hx)⟩ ?_
    rw [hAcard, pow_one]
  have hNA : normalizer (A : Set G) ≤ D.M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 q P A hAP hrankA).trans hΓ
  have hNP : normalizer (P : Set G) ≤ D.M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 q P P le_rfl
      (hrankA.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono q hq.one_lt hAP))).trans hΓ
  have hnormconj : ∀ (H H' : Subgroup G), (∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H) →
      ∀ x ∈ normalizer (H' : Set G), g * x * g⁻¹ ∈ normalizer (H : Set G) := by
    intro H H' hH' x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro a
    have h := hx (g⁻¹ * a * g)
    rw [hH', hH'] at h
    have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    have e2 : g * (x * (g⁻¹ * a * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ := by group
    rw [e1, e2] at h
    exact h
  have hNP₁ : normalizer (P₁ : Set G) ≤ M₁ := fun x hx => (hM₁ x).2 (hNP (hnormconj P P₁ hP₁ x hx))
  have hDM : D' ≤ D.M := fun d hd => hNP (hD hd)
  have hAM₁ : A ≤ M₁ := fun a ha => hNP₁ (hA ha)
  have hP₁M₁ : P₁ ≤ M₁ := fun x hx => (hM₁ x).2 (hPM ((hP₁ x).1 hx))
  have hD'P₁ : D' ≤ P₁ := fun x hx => (hP₁ x).2 (hAP ((hD' x).1 hx))
  have hbound : ∀ N : Subgroup G, rankThreeIsMaxTwoLocal N → N ≠ D.M →
      Nat.card ↥(P ⊓ N) ≤ q := by
    intro N hN hNM
    refine uc22p22f_card_le_of_lt_sq hq (hPq.to_le inf_le_left) ?_
    by_contra hge
    push Not at hge
    exact hNM (uc22p22f_two_le D h63 hq hq2 hPM hPq hPexp hΓ hN hge)
  have hM₁ne : M₁ ≠ D.M := by
    intro h
    apply hgN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := hM₁ x
    rw [h] at this
    exact this
  have hM₂ne : M₂ ≠ D.M := by
    intro h
    apply hgN
    have hg' : g⁻¹ ∈ normalizer (D.M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have := hM₂ x
      rw [h] at this
      simpa using this
    simpa using Subgroup.inv_mem _ hg'
  have hP₁M : Nat.card ↥(P₁ ⊓ D.M) ≤ q := by
    refine le_trans ?_ (hbound M₂ hM₂max hM₂ne)
    let f : ↥(P₁ ⊓ D.M) → ↥(P ⊓ M₂) := fun x =>
      ⟨g * (x : G) * g⁻¹, (hP₁ _).1 x.2.1, (hM₂ _).2 (by
        have e : g⁻¹ * (g * (x : G) * g⁻¹) * g = x := by group
        rw [e]
        exact x.2.2)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [f] using this
    exact Nat.card_le_card_of_injective f hf
  have hPM₁ : Nat.card ↥(P ⊓ M₁) ≤ q := hbound M₁ hM₁max hM₁ne
  have hAeq : A = P ⊓ M₁ :=
    Subgroup.eq_of_le_of_card_ge (le_inf hAP hAM₁) (hPM₁.trans hAcard.ge)
  have hDeq : D' = P₁ ⊓ D.M :=
    Subgroup.eq_of_le_of_card_ge (le_inf hD'P₁ hDM) (hP₁M.trans hD'card.ge)
  have hAD : A ≠ D' := by
    intro h
    apply hgM
    apply hNA
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := hD' x
    rw [← h] at this
    exact this
  have hAD' : A ⊓ D' = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ D') ∣ q := hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hq).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have h2 : A ⊓ D' = A :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ D' ≤ A) (by omega)
      have h3 : A ≤ D' := by
        rw [← h2]
        exact inf_le_right
      exact hAD (Subgroup.eq_of_le_of_card_ge h3 (by omega))
  have hPP₁ : P ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ P ⊓ M₁ := ⟨hx.1, hP₁M₁ hx.2⟩
    have h2 : x ∈ P₁ ⊓ D.M := ⟨hx.2, hPM hx.1⟩
    rw [← hAeq] at h1
    rw [← hDeq] at h2
    have h3 : x ∈ A ⊓ D' := ⟨h1, h2⟩
    rw [hAD'] at h3
    exact h3
  have hcomm : ∀ a ∈ A, ∀ d ∈ D', a * d = d * a := by
    intro a ha d hd
    have h1 : a * (d * a⁻¹ * d⁻¹) ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (hD hd) a⁻¹).1 (P.inv_mem (hAP ha))
      exact P.mul_mem (hAP ha) this
    have h2 : a * d * a⁻¹ * d⁻¹ ∈ P₁ := by
      have := (Subgroup.mem_normalizer_iff.1 (hA ha) d).1 (hD'P₁ hd)
      exact P₁.mul_mem this (P₁.inv_mem (hD'P₁ hd))
    have h3 : a * d * a⁻¹ * d⁻¹ ∈ P ⊓ P₁ := by
      refine ⟨?_, h2⟩
      have e : a * d * a⁻¹ * d⁻¹ = a * (d * a⁻¹ * d⁻¹) := by group
      rw [e]
      exact h1
    rw [hPP₁] at h3
    have h4 : a * d * a⁻¹ * d⁻¹ = 1 := h3
    have h5 : a * d * a⁻¹ = d := mul_inv_eq_one.1 h4
    calc a * d = a * d * a⁻¹ * a := by group
      _ = d * a := by rw [h5]
  have hAcent : A ≤ centralizer (D' : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hcomm a ha d hd).symm
  have hAnorm : A ≤ normalizer (D' : Set G) :=
    hAcent.trans (Subgroup.centralizer_le_normalizer _)
  have hEmul : ((A ⊔ D' : Subgroup G) : Set G) = (A : Set G) * D' :=
    Subgroup.coe_mul_of_left_le_normalizer_right A D' hAnorm
  have hAE : A ≤ A ⊔ D' := le_sup_left
  have hDE : D' ≤ A ⊔ D' := le_sup_right
  have hPE : ¬ P ≤ A ⊔ D' := by
    intro hle
    have hPA : P ≤ A := by
      intro x hx
      have hx' : x ∈ ((A ⊔ D' : Subgroup G) : Set G) := hle hx
      rw [hEmul] at hx'
      obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hx'
      have hdP : d ∈ P := by
        have := P.mul_mem (P.inv_mem (hAP ha)) hx
        simpa using this
      have h1 : d ∈ P ⊓ P₁ := ⟨hdP, hD'P₁ hd⟩
      rw [hPP₁] at h1
      have hd1 : d = 1 := h1
      rw [hd1, mul_one]
      exact ha
    have h1 : Nat.card ↥P ≤ Nat.card ↥A := Subgroup.card_le_of_le hPA
    have h2 : q ^ 2 ≤ q := hPcard.trans (h1.trans hAcard.le)
    nlinarith
  obtain ⟨x₁, hx₁P, hx₁N, hx₁E⟩ := uc22p22f_exists_normalizer_inf (q := q) (P := P) (X := D')
    (E := A ⊔ D') hPq hD'q hD hDE (sup_le (hAP.trans le_sup_right) le_sup_left) hPE
  have hRcard : q ^ 2 ≤ Nat.card ↥(normalizer ((A ⊔ D' : Subgroup G) : Set G) ⊓ P) :=
    uc22p22f_card_ge_sq hq (hPq.to_le inf_le_right)
      (le_inf (hAE.trans Subgroup.le_normalizer) hAP) hAcard ⟨hx₁N, hx₁P⟩
      (fun h => hx₁E (hAE h))
  have hP₁E : ¬ P₁ ≤ A ⊔ D' := by
    intro hle
    have hP₁D : P₁ ≤ D' := by
      intro x hx
      have hx' : x ∈ ((A ⊔ D' : Subgroup G) : Set G) := hle hx
      rw [hEmul] at hx'
      obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hx'
      have haP₁ : a ∈ P₁ := by
        have := P₁.mul_mem hx (P₁.inv_mem (hD'P₁ hd))
        simpa using this
      have h1 : a ∈ P ⊓ P₁ := ⟨hAP ha, haP₁⟩
      rw [hPP₁] at h1
      have ha1 : a = 1 := h1
      rw [ha1, one_mul]
      exact hd
    have h1 : Nat.card ↥P₁ ≤ Nat.card ↥D' := Subgroup.card_le_of_le hP₁D
    have h2 : q ^ 2 ≤ q := (hPcard.trans hP₁card.ge).trans (h1.trans hD'card.le)
    nlinarith
  obtain ⟨x₂, hx₂P, hx₂N, hx₂E⟩ := uc22p22f_exists_normalizer_inf (q := q) (P := P₁) (X := A)
    (E := A ⊔ D') hP₁q hAq hA hAE (sup_le le_sup_left (hD'P₁.trans le_sup_right)) hP₁E
  have hR'card : q ^ 2 ≤ Nat.card ↥(normalizer ((A ⊔ D' : Subgroup G) : Set G) ⊓ P₁) :=
    uc22p22f_card_ge_sq hq (hP₁q.to_le inf_le_right)
      (le_inf (hDE.trans Subgroup.le_normalizer) hD'P₁) hD'card ⟨hx₂N, hx₂P⟩
      (fun h => hx₂E (hDE h))
  have hzD' : D' ≤ centralizer ({z} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hza : z * (g * d * g⁻¹) = (g * d * g⁻¹) * z :=
      Subgroup.mem_centralizer_iff.1 (hzA ((hD' d).1 hd)) z (Set.mem_singleton z)
    have hzg : z * g = g * z := Subgroup.mem_centralizer_iff.1 hgz z (Set.mem_singleton z)
    have hzg' : g⁻¹ * z * g = z := by
      rw [mul_assoc, hzg]
      group
    calc z * d = (g⁻¹ * z * g) * d := by rw [hzg']
      _ = g⁻¹ * (z * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * d * g⁻¹) * z) * g := by rw [hza]
      _ = d * (g⁻¹ * z * g) := by group
      _ = d * z := by rw [hzg']
  have hEz : A ⊔ D' ≤ centralizer ({z} : Set G) := sup_le hzA hzD'
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = centralizer ((A ⊔ D' : Subgroup G) : Set G) :=
    ⟨_, rfl⟩
  have hzC : z ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.1 (hEz he) z (Set.mem_singleton z)).symm
  have hCM : C ≤ D.M := by
    rw [hCdef]
    exact (Subgroup.centralizer_le (hAE : A ≤ A ⊔ D')).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNA)
  have hOC : pCoreOf 2 D.M ⊓ C ≤ pCoreOf 2 C := by
    refine uc22p22f_le_pCoreOf inf_le_right
      ((uc22p22f_isPGroup_pCoreOf D.M).to_le inf_le_left) ?_
    intro k hk x hx
    exact ⟨uc22p22f_conj_mem_pCoreOf_self (hCM hk) hx.1, C.mul_mem (C.mul_mem hk hx.2) (C.inv_mem hk)⟩
  have hzS : z ∈ pCoreOf 2 C := hOC ⟨hzO, hzC⟩
  have hnormC : ∀ n ∈ normalizer ((A ⊔ D' : Subgroup G) : Set G), ∀ k ∈ C, n * k * n⁻¹ ∈ C := by
    intro n hn k hk
    rw [hCdef] at hk ⊢
    rw [Subgroup.mem_centralizer_iff] at hk ⊢
    intro e he
    have hn' : n⁻¹ ∈ normalizer ((A ⊔ D' : Subgroup G) : Set G) := Subgroup.inv_mem _ hn
    have he' : n⁻¹ * e * n ∈ (A ⊔ D' : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.1 hn' e).1 he
      simpa using this
    have h1 := hk _ he'
    calc e * (n * k * n⁻¹) = n * ((n⁻¹ * e * n) * k) * n⁻¹ := by group
      _ = n * (k * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
      _ = (n * k * n⁻¹) * e := by group
  have hnormS : ∀ r ∈ normalizer ((A ⊔ D' : Subgroup G) : Set G),
      r ∈ normalizer ((pCoreOf 2 C : Subgroup G) : Set G) := by
    intro r hr
    refine uc22p22f_mem_normalizer_pCoreOf (hnormC r hr) ?_
    intro k hk
    have := hnormC r⁻¹ (Subgroup.inv_mem _ hr) k hk
    simpa using this
  have hSne : pCoreOf 2 C ≠ ⊥ := by
    intro h
    apply hz1
    have := hzS
    rw [h] at this
    exact this
  have hloc : IsTwoLocal (normalizer ((pCoreOf 2 C : Subgroup G) : Set G)) :=
    ⟨pCoreOf 2 C, hSne, uc22p22f_isPGroup_pCoreOf C, rfl⟩
  obtain ⟨N, hNmax, hSN⟩ := uc22p22f_exists_maxTwoLocal_ge hloc
  have hNM : N = D.M := by
    refine uc22p22f_two_le D h63 hq hq2 hPM hPq hPexp hΓ hNmax ?_
    refine hRcard.trans (Subgroup.card_le_of_le ?_)
    intro r hr
    exact ⟨hr.2, hSN (hnormS r hr.1)⟩
  have hR'D : normalizer ((A ⊔ D' : Subgroup G) : Set G) ⊓ P₁ ≤ D' := by
    intro r hr
    have hrN : r ∈ N := hSN (hnormS r hr.1)
    rw [hNM] at hrN
    have h1 : r ∈ P₁ ⊓ D.M := ⟨hr.2, hrN⟩
    rw [← hDeq] at h1
    exact h1
  have h1 : q ^ 2 ≤ q := (hR'card.trans (Subgroup.card_le_of_le hR'D)).trans hD'card.le
  nlinarith

theorem uc22p22f_final (D : Data G) (h63 : UC6.R6_3 D) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {P A : Subgroup G} {g z : G} (hPM : P ≤ D.M) (hPq : IsPGroup q ↥P)
    (hPexp : ∀ x ∈ P, x ^ q = 1) (hPcard : q ^ 2 ≤ Nat.card ↥P)
    (hΓ : rankThreeGamma 1 q P ≤ D.M) (hAP : A ≤ P) (hAcard : Nat.card ↥A = q) (hgM : g ∉ D.M)
    (hzO : z ∈ pCoreOf 2 D.M) (hz1 : z ≠ 1) (hzA : A ≤ centralizer ({z} : Set G))
    (hgz : g ∈ centralizer ({z} : Set G)) (hD : uniqueFourConj g A ≤ normalizer (P : Set G))
    (hA : A ≤ normalizer ((uniqueFourConj g P : Subgroup G) : Set G)) : False := by
  have hMmax : rankThreeIsMaxTwoLocal D.M := D.maxLocal
  have hAq : IsPGroup q ↥A := hPq.to_le hAP
  refine uc22p22f_final_aux D h63 hq hq2 (P₁ := uniqueFourConj g P) (D' := uniqueFourConj g A)
    (M₁ := uniqueFourConj g D.M) (M₂ := D.M.map (MulAut.conj g).toMonoidHom) hPM hPq hPexp hPcard hΓ
    hAP hAcard hgM hzO hz1 hzA hgz (uc22p22f_mem_conj P g) (uc22p22f_mem_conj A g)
    (uc22p22f_mem_conj D.M g) ?_
    (CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hMmax (MulAut.conj g⁻¹))
    (CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hMmax (MulAut.conj g))
    (hPq.map _) (hAq.map _) (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective)
    ((Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hAcard) hD hA
  intro x
  rw [Subgroup.mem_map_equiv]
  simp

theorem uc22p22f_V_le_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx22b D Ch) :
    c.V ≤ pCoreOf 2 D.M := by
  have hU : D.U ≤ pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ∧ IsElemAbelian 2 D.U :=
    uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  exact c.hVU.trans (hU.1.trans inf_le_left)

theorem uc22p22f_pCoreOf_le_cent {D : Data G} {Ch : Choice2011 G} (hV : S22_V D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) : pCoreOf 2 D.M ≤ centralizer (c.V : Set G) := by
  have hker := uc22p22f_pCore_le_ker c.hVM (hV h1930 c).1.2.2
  rintro _ ⟨o, ho, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ (hker ho))

theorem uc22p22f_permutes_cent (D : Data G) (Ch : Choice2011 G) (hV : S22_V D Ch) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {P : Subgroup G} (hPM : P ≤ D.M) (hPn : (barImage D.M P).Normal) :
    Permutes (P ⊓ centralizer (c.V : Set G)) D.T := by
  have hAM : P ⊓ centralizer (c.V : Set G) ≤ D.M := inf_le_left.trans hPM
  refine uc22p22f_permutes D hAM ?_
  haveI := hPn
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G,
      K = barPreimage D.M (barImage D.M P) ⊓ centralizer (c.V : Set G) := ⟨_, rfl⟩
  have hYM : barPreimage D.M (barImage D.M P) ≤ D.M := uc22p21c_barPreimage_le _ _
  have hKM : K ≤ D.M := hKdef ▸ inf_le_left.trans hYM
  have hMY : D.M ≤ normalizer ((barPreimage D.M (barImage D.M P) : Subgroup G) : Set G) :=
    uc22p22f_normalizer_barPreimage D.M _
  have hMK : D.M ≤ normalizer (K : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    subst hKdef
    constructor
    · rintro ⟨hxY, hxC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hMY hm) x).1 hxY, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro v hv
      have hv' : m⁻¹ * v * m ∈ c.V := by
        have := (Subgroup.mem_normalizer_iff.1 (c.hVM (D.M.inv_mem hm)) v).1 hv
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hxC _ hv'
      calc v * (m * x * m⁻¹) = m * ((m⁻¹ * v * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
        _ = (m * x * m⁻¹) * v := by group
    · rintro ⟨hxY, hxC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hMY hm) x).2 hxY, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro v hv
      have hv' : m * v * m⁻¹ ∈ c.V := by
        have := (Subgroup.mem_normalizer_iff.1 (c.hVM hm) v).1 hv
        exact this
      have h1 := Subgroup.mem_centralizer_iff.1 hxC _ hv'
      calc v * x = m⁻¹ * ((m * v * m⁻¹) * (m * x * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x * m⁻¹) * (m * v * m⁻¹)) * m := by rw [h1]
        _ = x * v := by group
  have hKn : ((K.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))).Normal := by
    haveI : (K.subgroupOf D.M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMK
    exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hEq : barImage D.M (P ⊓ centralizer (c.V : Set G)) =
      (K.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxA, rfl⟩ := uc22p21c_mem_barImage.1 hy
      refine ⟨x, ?_, rfl⟩
      rw [hKdef]
      refine ⟨uc22p21c_mem_barPreimage.2 ⟨x.2, ?_⟩, hxA.2⟩
      exact uc22p21c_mem_barImage.2 ⟨x, hxA.1, rfl⟩
    · rintro ⟨x, hxK, rfl⟩
      have hxK' : (x : G) ∈ K := hxK
      rw [hKdef] at hxK'
      obtain ⟨hxY, hxC⟩ := hxK'
      obtain ⟨_, hxY'⟩ := uc22p21c_mem_barPreimage.1 hxY
      obtain ⟨p, hpP, hp⟩ := uc22p21c_mem_barImage.1 hxY'
      have hpx : uc22p21cPi D.M p = uc22p21cPi D.M x := hp
      have hker : p⁻¹ * x ∈ CFSG.pCore 2 ↥D.M := by
        have h3 : (QuotientGroup.mk p : Bar2 D.M) = QuotientGroup.mk x := hpx
        rw [← QuotientGroup.eq]
        exact h3
      have hOC : ((p⁻¹ * x : ↥D.M) : G) ∈ centralizer (c.V : Set G) :=
        uc22p22f_pCoreOf_le_cent hV h1930 c ⟨p⁻¹ * x, hker, rfl⟩
      have hpC : (p : G) ∈ centralizer (c.V : Set G) := by
        have h2 : (p : G) = (x : G) * ((p⁻¹ * x : ↥D.M) : G)⁻¹ := by
          simp
        rw [h2]
        exact (centralizer (c.V : Set G)).mul_mem hxC ((centralizer (c.V : Set G)).inv_mem hOC)
      have hpA : (p : G) ∈ P ⊓ centralizer (c.V : Set G) := ⟨hpP, hpC⟩
      have := uc22p21c_mem_barImage.2 ⟨p, hpA, rfl⟩
      rw [hpx] at this
      exact this
  rw [hEq]
  exact hKn

theorem uc22p22f_gamma_of_conj {q : ℕ} (hq : q.Prime) {M P : Subgroup G} {y : G} (hy : y ∈ M)
    (hΓ : rankThreeGamma 1 q (P.map (MulAut.conj y).toMonoidHom) ≤ M) :
    rankThreeGamma 1 q P ≤ M := by
  rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
  intro X hXP hX g hg
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  have hX' : 1 ≤ CFSG.Open.pRank q (X.map (MulAut.conj y).toMonoidHom) := by
    have := CFSG.RankThreeCoreUniqueness.Helpers.pRank_eq_of_subgroup_equiv q hq.one_lt X
      (X.map (MulAut.conj y).toMonoidHom) (X.equivMapOfInjective (MulAut.conj y).toMonoidHom hinj)
    omega
  have hN : normalizer ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) ≤ M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 q _ _ (Subgroup.map_mono hXP)
      hX').trans hΓ
  have key : ∀ a : G, a ∈ X.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * a * y ∈ X := by
    intro a
    rw [Subgroup.mem_map_equiv]
    simp
  have hg' : y * g * y⁻¹ ∈ normalizer ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    rw [key, key]
    have h := (Subgroup.mem_normalizer_iff.1 hg) (y⁻¹ * a * y)
    have e : y⁻¹ * (y * g * y⁻¹ * a * (y * g * y⁻¹)⁻¹) * y = g * (y⁻¹ * a * y) * g⁻¹ := by group
    rw [e]
    exact h
  have h1 := hN hg'
  have e : g = y⁻¹ * (y * g * y⁻¹) * y := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hy) h1) hy

theorem gam2210_of (D : Data G) (Ch : Choice2011 G) (h77 : F07.R77Eq D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h8 : S22_8 D Ch)
    (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M) :
    H1930 D → ∀ c : Ctx22b D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ P : Subgroup G,
      P ≤ D.M → IsPGroup q ↥P → (∀ x ∈ P, x ^ q = 1) → ⁅⁅P, P⁆, P⁆ = ⊥ → ¬ IsCyclic ↥P →
      (barImage D.M P).Normal → rankThreeGamma 1 q P ≤ D.M := by
  classical
  intro h1930 c q hq hq2 P hPM hPq hPexp hPcl hPnc hPY
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hqσ : q ∈ D.sig
  ·
    have hsp' := hsp q ((h8 h1930 c) ▸ hqσ)
    rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
    intro X hXP hX g hg
    by_contra hgM
    obtain ⟨E, hEX, -, hEc⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained q X (by omega)
    have hqE : q ∣ Nat.card ↥E := by
      rw [hEc]
      exact dvd_pow_self q (by omega)
    have hXle : X ≤ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := by
      refine le_inf (hXP.trans hPM) ?_
      intro x hx
      have hg' : g⁻¹ ∈ normalizer (X : Set G) := Subgroup.inv_mem _ hg
      have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hg' x).1 hx
      rw [inv_inv] at h1
      exact ⟨g⁻¹ * x * g, hXP.trans hPM h1, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact hsp'.2.2 g hgM (hqE.trans ((Subgroup.card_dvd_of_le hEX).trans
      (Subgroup.card_dvd_of_le hXle)))
  · obtain ⟨p, hpσ⟩ := hne
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpq : p ≠ q := fun h => hqσ (h ▸ hpσ)
    have hspp := hsp p ((h8 h1930 c) ▸ hpσ)
    have hrkM : 3 ≤ CFSG.Open.pRank p D.M := hrk p hpσ
    obtain ⟨E, hEM, hEel, hEcard⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained p D.M (by omega)
    obtain ⟨hPSyl, n, hYcard⟩ := uc22p22f_sylow_in_Y hq hq2 hPM hPq
    haveI hbn : (barImage D.M P).Normal := hPY
    set Y := barPreimage D.M (barImage D.M P) with hY
    have hYM : Y ≤ D.M := uc22p21c_barPreimage_le _ _
    have hMY : D.M ≤ normalizer (Y : Set G) := uc22p22f_normalizer_barPreimage D.M _
    have hEY : E ≤ normalizer (Y : Set G) := hEM.trans hMY
    obtain ⟨m, hm⟩ := hPq.exists_card_eq
    have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥Y) := by
      rw [hEcard, hYcard, hm]
      exact Nat.Coprime.mul_right
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp Nat.prime_two).2 hp2))
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hq).2 hpq))
    haveI : IsMulCommutative ↥E := hEel.1
    haveI : Group.IsSolvable ↥E := inferInstance
    obtain ⟨P', hP'Syl, hEP'⟩ :=
      CFSG.GH74.Uniqueness.exists_sylow_normalized_of_coprime hEY hcop q
    obtain ⟨y, hyY, hP'eq⟩ := uc22p22f_exists_conj_sylow hPSyl hP'Syl
    have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
    have hP'M : P' ≤ D.M := hP'Syl.le.trans hYM
    have hP'q : IsPGroup q ↥P' := hP'Syl.isPGroup
    have hP'nc : ¬ IsCyclic ↥P' := by
      intro hcyc
      apply hPnc
      rw [hP'eq] at hcyc
      exact isCyclic_of_surjective (P.equivMapOfInjective _ hinj).symm.toMonoidHom
        (MulEquiv.surjective _)
    have hP'exp : ∀ x ∈ P', x ^ q = 1 := by
      intro x hx
      rw [hP'eq] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      rw [conj_pow, hPexp a ha]
      simp
    have hP'cl : ⁅⁅P', P'⁆, P'⁆ = ⊥ := by
      rw [hP'eq, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hPcl, Subgroup.map_bot]
    have hEle : E ≤ D.M ⊓ normalizer (P' : Set G) := le_inf hEM hEP'
    have hrk3 : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (P' : Set G)) :=
      CFSG.SectionRank.le_pRank hpp.one_lt hEle hEel hEcard
    have hΓ' : rankThreeGamma 1 q P' ≤ D.M :=
      h77 (h8 h1930 c).subset p hpσ hp2 hspp q hq hq2 hqσ P' hP'M hP'q hP'nc hP'exp hP'cl
        (by omega) (le_antisymm hrk3
          (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hpp.one_lt inf_le_left))
    exact uc22p22f_gamma_of_conj hq (hYM hyY) (hP'eq ▸ hΓ')

end Final

end CFSG.LocalAnalysis.UniquenessCase.UC22
