module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec13.CritProof

open CFSG Subgroup CFSG.SectionRank.Ccomm
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups commutatorElement

@[expose] def omegaOneCore {X : Type*} [Group X] (p : ℕ) (C : Subgroup (pCore p X)) :
    Subgroup X :=
  (omegaOneIn p C).map (pCore p X).subtype

section CriticalAt

variable {X : Type*} [Group X] [Finite X]

theorem exists_criticalAt_omega {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hP : pCore q X ≠ ⊥) :
    ∃ C : Subgroup (pCore q X), IsThompsonCritical C ∧ C ≠ ⊥ ∧
      Sec4.Census.CriticalAt q (omegaOneCore q C) ∧ (omegaOneCore q C).Characteristic := by
  set P := pCore q X with hPdef
  have : P.Normal := pCore_normal
  have hPq : IsPGroup q P := pCore_isPGroup
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨C, hC, hCne, -, -, hD₀c, hD₀1, hD₀comm, hD₀exp, hD₀fix, -⟩ :=
    exists_isThompsonCritical_omega hq2 hPq
  set D₀ := omegaOneIn q C with hD₀def
  have : D₀.Characteristic := hD₀c
  have hchar : (omegaOneCore q C).Characteristic := by
    change (D₀.map P.subtype).Characteristic
    infer_instance
  refine ⟨C, hC, hCne hnt, ⟨inferInstance, Subgroup.map_subtype_le _, fun h => hD₀1 hnt ?_, ?_,
    ?_, ?_⟩, hchar⟩
  · exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hD₀exp x hx, Subgroup.coe_one]
  · rintro _ ⟨a, ha, rfl⟩ b hb
    have h1 : ⁅a, (⟨b, hb⟩ : P)⁆ ∈ ⁅D₀, (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _)
    obtain ⟨h2, h3⟩ := hD₀comm h1
    refine ⟨⟨_, h2, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have h4 := Subgroup.mem_centralizer_iff.mp h3 d hd
    exact (congrArg Subtype.val h4).symm
  · intro y hy
    set σ : MulAut P := MulAut.conjNormal y with hσ
    have hσfix : σ ∈ fixingSubgroup (MulAut P) (D₀ : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      exact hy _ ⟨d, hd, rfl⟩
    obtain ⟨k, hk⟩ := hD₀fix ⟨σ, hσfix⟩
    refine ⟨k, fun x hx => ?_⟩
    have h1 : σ ^ (q ^ k) = 1 := congrArg Subtype.val hk
    have h2 := congrArg (fun τ : MulAut P => ((τ ⟨x, hx⟩ : P) : X)) h1
    simp only [hσ, ← map_pow, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact h2

end CriticalAt

section Rank

variable {X : Type} [Group X] [Finite X]

theorem false_of_quotient_SL2 {K N : Subgroup X} [K.Normal]
    [N.Normal] (hNK : N ≤ K) {r : ℕ} [Fact r.Prime] (hr3 : 3 < r)
    (e : X ⧸ N ≃* SL(2, ZMod r)) {E : Subgroup (X ⧸ K)} (hE : Monoid.exponent E ∣ 3)
    (hE9 : Nat.card E = 9) : False := by
  set F : SL(2, ZMod r) →* X ⧸ K :=
    (QuotientGroup.map N K (MonoidHom.id X) hNK).comp e.symm.toMonoidHom with hF
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    refine ⟨e (x : X ⧸ N), ?_⟩
    rw [hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Sec4.false_of_surjective_of_isCyclic_sylow F hFs
    (Sec4.Census.isCyclic_sylow_SL2 (p := r) (by norm_num) (by omega)) hE hE9

theorem exists_critical_rank_three [Group.IsPerfect X]
    {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)] (hK : Group.IsSolvable K)
    (hq : ¬ IsQuasisimple X) (hO2 : pCore 2 X = ⊥)
    (hO3 : ∀ y ∈ pCore 3 X, ∀ x : X, y * x = x * y) {E : Subgroup (X ⧸ K)}
    (hE : Monoid.exponent E ∣ 3) (hE9 : Nat.card E = 9) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ (_ : Fact p.Prime) (C : Subgroup (pCore p X)),
      IsThompsonCritical C ∧ C ≠ ⊥ ∧
      Sec4.Census.CriticalAt p (omegaOneCore p C) ∧ (omegaOneCore p C).Characteristic ∧
      (∃ y ∈ pCore p X, ∃ x : X, y * x ≠ x * y) ∧
      centralizer (pCore p X : Set X) ≤ K ∧ 3 ≤ CFSG.pRank p (omegaOneCore p C) := by
  have hKtop : K ≠ ⊤ := fun h => (QuotientGroup.nontrivial_iff.mp inferInstance) h
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hKtop (eq_top_iff.mpr fun x _ => hcon x)
  obtain ⟨s, hs, y, hy, hyx⟩ := L3Proof.exists_pCore_not_commute hK hq hx
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyx (by rw [one_mul, mul_one])
  have hs2 : s ≠ 2 := by
    rintro rfl
    rw [hO2, Subgroup.mem_bot] at hy
    exact hy1 hy
  have hs3 : s ≠ 3 := by
    rintro rfl
    exact hyx (hO3 y hy x)
  have hs3' : 3 < s := by
    have := hs.two_le
    omega
  have : Fact s.Prime := ⟨hs⟩
  have hPne : pCore s X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hy
    exact hy1 hy
  obtain ⟨C, hC, hCne, hD, hDc⟩ := exists_criticalAt_omega hs2 hPne
  have hcen : centralizer (pCore s X : Set X) ≤ K := by
    by_contra hle
    have : (centralizer (pCore s X : Set X)).Normal := by
      have : (pCore s X).Normal := pCore_normal
      infer_instance
    have htop := Sec4.Census.eq_top_of_not_le hK hle
    have hxc : x ∈ centralizer (pCore s X : Set X) := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hyx (Subgroup.mem_centralizer_iff.mp hxc y hy)
  refine ⟨s, hs, hs3', inferInstance, C, hC, hCne, hD, hDc, ⟨y, hy, x, hyx⟩, hcen, ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨N, hN, hlin⟩ :=
    Sec4.Census.linearOutcome_of_criticalAt hK hs3' hcen hD (Nat.lt_succ_iff.mp hlt)
  have hNK : N ≤ K := by
    rcases hlin.2 with ⟨-, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨h3, -⟩
    · have hJ := Sec4.Census.isQuasisimple_SL2 (p := s) (Sec4.Census.five_le_of_prime hs hs3')
      have : Nontrivial (SL(2, ZMod s) ⧸ Subgroup.center SL(2, ZMod s)) := hJ.2.1.toNontrivial
      have : Nontrivial SL(2, ZMod s) :=
        (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ZMod s))).nontrivial
      exact Sec4.Census.le_of_nontrivial_quotient hK e.toEquiv.nontrivial
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hJ := Sec4.Census.isQuasisimple_SL2 (p := 5) le_rfl
      have : Nontrivial (SL(2, ZMod 5) ⧸ Subgroup.center SL(2, ZMod 5)) := hJ.2.1.toNontrivial
      have : Nontrivial SL(2, ZMod 5) :=
        (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ZMod 5))).nontrivial
      exact Sec4.Census.le_of_nontrivial_quotient hK e.toEquiv.nontrivial
    · omega
  rcases hlin.2 with ⟨-, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨h3, -⟩
  · exact false_of_quotient_SL2 hNK hs3' e hE hE9
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact false_of_quotient_SL2 hNK (by norm_num) e hE hE9
  · omega

end Rank

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem odd_card_centralizer_of_three_le_pRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hloc : localRank p G < 3) {D : Subgroup G} (hD : 3 ≤ CFSG.pRank p D) :
    Odd (Nat.card (centralizer (D : Set G))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (D : Set G)) 2
    (even_iff_two_dvd.mp hodd)
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hcomm : ∀ h ∈ D, h * (t : G) = (t : G) * h := fun h hh =>
    Subgroup.mem_centralizer_iff.mp t.2 h hh
  have := Sec4.Census.pRank_le_localRank_of_centralizes hp hp2 ht2 hcomm
  omega

omit [Finite G] in
theorem centralizer_subgroupOf_le_oddCore {D Y : Subgroup G}
    (hY : Y ≤ normalizer (D : Set G)) (hodd : Odd (Nat.card (centralizer (D : Set G)))) :
    (centralizer (D : Set G)).subgroupOf Y ≤ CFSG.oddCore Y := by
  have hN : ((centralizer (D : Set G)).subgroupOf Y).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro d hd
    have hgN := hY g.2
    have hd' : (g : G)⁻¹ * d * (g : G) ∈ D := by
      have := (Subgroup.mem_normalizer_iff''.mp hgN d)
      exact this.mp hd
    have h1 := hn _ hd'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc d * ((g : G) * n * (g : G)⁻¹) = (g : G) * ((g : G)⁻¹ * d * g * n) * (g : G)⁻¹ := by
          group
      _ = (g : G) * (n * ((g : G)⁻¹ * d * g)) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * n * (g : G)⁻¹ * d := by group
  have hcard : Odd (Nat.card ((centralizer (D : Set G)).subgroupOf Y)) := by
    have hle : Nat.card ((centralizer (D : Set G)).subgroupOf Y) ∣
        Nat.card (centralizer (D : Set G)) := by
      refine Subgroup.card_dvd_of_injective
        ((Y.subtype.comp ((centralizer (D : Set G)).subgroupOf Y).subtype).codRestrict _
          fun y => y.2) fun a b hab => ?_
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hodd hle
  exact le_sSup ⟨hN, hcard⟩

theorem card_le_eight_of_isElemAbelian {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {D : Subgroup G} (hDp : IsPGroup p D) (hexp : ∀ x ∈ D, x ^ p = 1)
    (hcl : ∀ a ∈ D, ∀ b ∈ D, ∀ d ∈ D, a * b * a⁻¹ * b⁻¹ * d = d * (a * b * a⁻¹ * b⁻¹))
    (hodd : Odd (Nat.card (centralizer (D : Set G))))
    (hrank : ∀ u : G, u ≠ 1 → (∃ k : ℕ, u ^ 2 ^ k = 1) →
      CFSG.pRank p (D ⊓ centralizer {u} : Subgroup G) ≤ 2)
    {E : Subgroup G} (hEN : E ≤ normalizer (D : Set G)) (hE : CFSG.Assembly.IsElemAbelian 2 E) :
    Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  obtain ⟨eE⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := E)
    (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (hE.2 a a.2)) hn
  set ι : Multiplicative (Fin n → ZMod 2) →* G := E.subtype.comp eE.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp eE.symm.injective
  have hιN : ∀ a, ι a ∈ normalizer (D : Set G) := fun a => hEN (eE.symm a).2
  set κ : Multiplicative (Fin n → ZMod 2) →* normalizer (D : Set G) :=
    (Subgroup.inclusion hEN).comp eE.symm.toMonoidHom with hκ
  let act : MulDistribMulAction (Multiplicative (Fin n → ZMod 2)) D :=
    MulDistribMulAction.compHom D (D.normalizerMonoidHom.comp κ)
  have hsmul : ∀ (a : Multiplicative (Fin n → ZMod 2)) (d : D),
      ((a • d : D) : G) = ι a * d * (ι a)⁻¹ := fun a d => rfl
  have hA2 : ∀ a : Multiplicative (Fin n → ZMod 2), a ^ 2 = 1 := by
    intro a
    obtain ⟨e, rfl⟩ := eE.surjective a
    rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hfaith : FaithfulSMul (Multiplicative (Fin n → ZMod 2)) D := by
    refine ⟨fun {a₁ a₂} h => hι ?_⟩
    set c := (ι a₁)⁻¹ * ι a₂ with hc
    have hcD : c ∈ centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg Subtype.val (h ⟨d, hd⟩)
      rw [hsmul, hsmul] at h1
      calc d * c = (ι a₁)⁻¹ * (ι a₁ * d * (ι a₁)⁻¹) * ι a₂ := by rw [hc]; group
        _ = (ι a₁)⁻¹ * (ι a₂ * d * (ι a₂)⁻¹) * ι a₂ := by rw [h1]
        _ = c * d := by rw [hc]; group
    have hc2 : c ^ 2 = 1 := by
      rw [hc, ← map_inv, ← map_mul, ← map_pow, hA2, map_one]
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have h2 : orderOf c ∣ Nat.card (centralizer (D : Set G)) := by
      rw [← Subgroup.orderOf_mk c hcD]
      exact orderOf_dvd_natCard _
    have h3 : orderOf c = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left).mpr hodd) h1 h2
    rw [orderOf_eq_one_iff, hc, inv_mul_eq_one] at h3
    exact h3
  have hexp' : Monoid.exponent D ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hexp x x.2, Subgroup.coe_one])
  have hclass : (⊤ : Subgroup D).lowerCentralSeries 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top, Subgroup.centralizer_univ]
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have := hcl a a.2 b b.2 d d.2
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this.symm
  have hm : ∀ a : Multiplicative (Fin n → ZMod 2), a ≠ 1 →
      CFSG.pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) D) ≤ 2 := by
    intro a ha
    set C := CFSG.fixedPointSubgroup (Subgroup.zpowers a) D
    have hle : C.map D.subtype ≤ D ⊓ centralizer {ι a} := by
      rintro _ ⟨d, hd, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨d.2, ?_⟩
      have hfix : a • d = d := hd ⟨a, Subgroup.mem_zpowers a⟩
      have h1 := congrArg Subtype.val hfix
      rw [hsmul] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (d : G) * ι a = ι a * d
      calc (d : G) * ι a = ι a * d * (ι a)⁻¹ * ι a := by rw [h1]
        _ = ι a * d := by group
    have hu1 : ι a ≠ 1 := fun h => ha (hι (by rw [h, map_one]))
    have hu2 : ∃ k : ℕ, ι a ^ 2 ^ k = 1 := ⟨1, by rw [pow_one, ← map_pow, hA2, map_one]⟩
    have h1 := hrank (ι a) hu1 hu2
    have h2 : CFSG.pRank p (C.map D.subtype) ≤
        CFSG.pRank p (D ⊓ centralizer {ι a} : Subgroup G) :=
      CFSG.RankThree.PartOne.Quotient36.pRank_le_of_injective' hp.out.one_lt
        (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have h3 : CFSG.pRank p (C.map D.subtype) = CFSG.pRank p C := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt
        (C.equivMapOfInjective _ D.subtype_injective).symm
    omega
  have hA : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
    rw [← Nat.card_congr eE.toEquiv, hn]
  have h2x : ∀ x : Additive (Multiplicative (Fin n → ZMod 2)), 2 • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow]
    exact (congrArg Additive.ofMul (hA2 (Additive.toMul x))).trans ofMul_one
  have hbound := (@CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound p hp
    (hp.out.odd_of_ne_two hp2) D _ _ hDp hexp' hclass
    (Multiplicative (Fin n → ZMod 2)) _ _ (AddCommGroup.zmodModule (n := 2) h2x) n 2 hA act
    hfaith hm).1
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hbound
    _ = 8 := by norm_num

end Ambient

end CFSG.RankThree.PartTwo.Sec13.CritProof
