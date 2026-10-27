module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TwE6Nonsplit

section Centre

theorem center_card_dvd_three (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (Subgroup.center (twistedE6Group 2 f)) ∣ 3 := by
  obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
    (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f) (q := 2 ^ f)
    (TwE6Toral.card_galoisField_two_mul f hf) (frobQ_apply 2 f)
  rw [hcard]
  exact Nat.gcd_dvd_left 3 _

theorem center_pow_three (f : ℕ) (hf : 1 ≤ f) {z : twistedE6Group 2 f}
    (hz : z ∈ Subgroup.center (twistedE6Group 2 f)) : z ^ 3 = 1 := by
  have hzle : Subgroup.zpowers z ≤ Subgroup.center (twistedE6Group 2 f) :=
    Subgroup.zpowers_le.mpr hz
  have horder : orderOf z ∣ Nat.card (Subgroup.center (twistedE6Group 2 f)) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hzle
  exact orderOf_dvd_iff_pow_eq_one.mp (horder.trans (center_card_dvd_three f hf))

theorem ker_pow_three {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hker : π.ker = Subgroup.center (twistedE6Group 2 f)) {z : twistedE6Group 2 f}
    (hz : z ∈ π.ker) : z ^ 3 = 1 := by
  rw [hker] at hz
  exact center_pow_three f hf hz

theorem exists_lift_pow_eq_one {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center (twistedE6Group 2 f))
    {a : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))} {p : ℕ}
    (ha : a ^ p = 1) (hp : p.Prime) (hp3 : p ≠ 3) :
    ∃ s : twistedE6Group 2 f, s ^ p = 1 ∧ π s = a := by
  obtain ⟨s₀, hs₀⟩ := hπ a
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨s₀ ^ (3 * m), ?_, ?_⟩
  · have hz : s₀ ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hs₀, ha]
    have h3 : (s₀ ^ p) ^ 3 = 1 := ker_pow_three hf hker hz
    rw [← pow_mul, mul_comm (3 * m) p, pow_mul, pow_mul, h3, one_pow]
  · rw [map_pow, hs₀, ← Nat.div_add_mod (3 * m) p, pow_add, pow_mul, ha, one_pow, one_mul, hm,
      pow_one]

end Centre

section Bridge

theorem twistedE6RootGroup_bridge (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 ∧
      (∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f)) ∧
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f ∧
      twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) =
        graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  have hring : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f := by
    ext c
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, iterateFrobeniusEquiv_def,
      frobQ_apply]
  refine ⟨TwE6Toral.card_galoisField_two_mul f hf, fun c => iterateFrobeniusEquiv_def _ 2 f c,
    hring, ?_⟩
  rw [twistedE6RootGroup, hring]

end Bridge

section Quotient

theorem nonempty_quotient_center_equiv_derivedCentralQuotient_ad (f : ℕ) (hf : 1 ≤ f) :
    Nonempty (↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⧸
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f)) ≃*
      DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf
    (GaloisField 2 (2 * f)) hK (frobQ 2 f) (frobQ_apply 2 f)).2.2.1
  have hZ := center_graphFixedRootGroup_eq_bot (t := TwistTag.E6)
    (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f)
    (Finite.surjective_of_injective (frobQ 2 f).injective)
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans e.symm)⟩

theorem nonempty_quotient_center_equiv_derivedCentralQuotient_sc (f : ℕ) (hf : 1 ≤ f) :
    Nonempty (twistedE6Group 2 f ⧸ Subgroup.center (twistedE6Group 2 f) ≃*
      DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) := by
  obtain ⟨π, hπ, hker, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf
    (GaloisField 2 (2 * f)) hK (frobQ 2 f) (frobQ_apply 2 f)).2.2.1
  have hZ := center_graphFixedRootGroup_eq_bot (t := TwistTag.E6)
    (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f)
    (Finite.surjective_of_injective (frobQ 2 f).injective)
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).trans e.symm)⟩

end Quotient

end TwE6Nonsplit

section Core

@[expose] def GGTwE6NonsplitCoreInput : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ExcNonsplit.GGNonsplitCoreAt (twistedE6Group 2 f) p ∧
      ExcNonsplit.GGNonsplitCoreAt
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) p

end Core

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LayerFacts LayerSixE

namespace TwE6Nonsplit

section Tag

theorem exists_conj_of_innerDiag_twistedE6 {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπ : Function.Surjective π)
    (hπval : ∀ z, ((π z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f))
          (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {G : Type} [Group G] {ψ : twistedE6Group 2 f →* G}
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f)) (hkπ : ψ.ker ≤ π.ker) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hc : GGPsiInnerDiag (twistedE6Datum 2 f) ψ c) (hcp : c ^ p = 1) :
    ∃ a : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      a ^ p = 1 ∧ GGInduces π ψ c (MulAut.conj a) := by
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hcN hc
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  have hin : α ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range :=
    ggTwE6InndiagOrdPInnerInput_holds f p hf hp hp2 (fun h => hp3 h.1) α hαD hαp
  obtain ⟨a, rfl⟩ := hin
  refine ⟨a, ?_, hα⟩
  have hZ : a ^ p ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : MulAut.conj (a ^ p) g = g := by rw [map_pow, hαp, MulAut.one_apply]
    rw [MulAut.conj_apply] at h2
    calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h2]
      _ = a ^ p * g := by group
  rw [center_graphFixedRootGroup_eq_bot (t := TwistTag.E6)
    (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f)
    (Finite.surjective_of_injective (frobQ 2 f).injective), Subgroup.mem_bot] at hZ
  exact hZ

theorem exists_component_twistedE6_of {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    (hcL : ExcNonsplit.GGNonsplitCoreAt (twistedE6Group 2 f) p)
    (hcC : ExcNonsplit.GGNonsplitCoreAt
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) p)
    {G : Type} [Group G] {ψ : twistedE6Group 2 f →* G}
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hperf : commutator ↥ψ.range = ⊤) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hxN : x ∈ Subgroup.normalizer (ψ.range : Set G))
    (hyN : y ∈ Subgroup.normalizer (ψ.range : Set G))
    (hxD : GGPsiInnerDiag (twistedE6Datum 2 f) ψ x)
    (hyD : GGPsiInnerDiag (twistedE6Datum 2 f) ψ y) {K : Subgroup G}
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x})) (hpK : ¬ p ∣ Nat.card K) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' ∧
      ¬ GGNbrClauseFiveMarking p x K' := by
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hkπ : ψ.ker ≤ π.ker := by rw [hkerπ]; exact hker
  obtain ⟨a, hap, hxa⟩ :=
    exists_conj_of_innerDiag_twistedE6 hf hp hp2 hp3 hπ hπval hker hkπ hxN hxD hx
  obtain ⟨b, hbp, hyb⟩ :=
    exists_conj_of_innerDiag_twistedE6 hf hp hp2 hp3 hπ hπval hker hkπ hyN hyD hy
  have hdvd : Nat.card ψ.ker ∣ 3 :=
    (Subgroup.card_dvd_of_le hker).trans (center_card_dvd_three f hf)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  ·
    have hk1 : ψ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk1
    have hπker : π.ker ≤ Subgroup.center (twistedE6Group 2 f) := le_of_eq hkerπ
    have hkψ : ψ.ker ≤ π.ker := by rw [hk1]; exact bot_le
    obtain ⟨s, hsp, hsa⟩ := exists_lift_pow_eq_one hf hπ hkerπ hap hp hp3
    obtain ⟨t, htp, htb⟩ := exists_lift_pow_eq_one hf hπ hkerπ hbp hp hp3
    have hs : (x, s) ∈ ggConjPairs ψ :=
      ExcNonsplit.mem_ggConjPairs_of_induces_conj hπker hkψ hperf hxN (by rw [hsa]; exact hxa)
    have ht : (y, t) ∈ ggConjPairs ψ :=
      ExcNonsplit.mem_ggConjPairs_of_induces_conj hπker hkψ hperf hyN (by rw [htb]; exact hyb)
    have hz := ExcNonsplit.commutator_mem_center_of_pairs hinj hxy hs ht
    have hst : s * t = t * s :=
      ExcNonsplit.mul_comm_of_commutator_mem_center hp hp3 hsp hz (center_pow_three f hf hz)
    exact ExcNonsplit.exists_component_of_pairs hinj hcL hsp htp hst hs ht hK hpK
  ·
    have hle : ψ.ker ≤ π.ker := hkπ
    have hcπ : Nat.card π.ker = 3 := by
      have hπ3 : Nat.card π.ker ∣ 3 := by rw [hkerπ]; exact center_card_dvd_three f hf
      have hle3 : 3 ≤ Nat.card π.ker := by
        have hdvd : Nat.card ψ.ker ∣ Nat.card π.ker := Subgroup.card_dvd_of_le hle
        rw [h3] at hdvd
        exact Nat.le_of_dvd Nat.card_pos hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hπ3 with h1' | h3'
      · omega
      · exact h3'
    have hkZ : ψ.ker = π.ker := Subgroup.eq_of_le_of_card_ge hle (by rw [hcπ, h3])
    obtain ⟨ψb, hval⟩ :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.exists_factor π hπ ψ (le_of_eq hkZ.symm)
    have hinj : Function.Injective ψb := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro c hc
      obtain ⟨u, rfl⟩ := hπ c
      rw [MonoidHom.mem_ker, hval u] at hc
      have hu : u ∈ ψ.ker := MonoidHom.mem_ker.mpr hc
      rw [hkZ] at hu
      rw [Subgroup.mem_bot]
      exact MonoidHom.mem_ker.mp hu
    have hrange : ψb.range = ψ.range := by
      ext g
      constructor
      · rintro ⟨c, rfl⟩
        obtain ⟨u, rfl⟩ := hπ c
        exact ⟨u, (hval u).symm⟩
      · rintro ⟨u, rfl⟩
        exact ⟨π u, hval u⟩
    have hs := ExcNonsplit.mem_ggConjPairs_of_induces hπ hval hxN hxa
    have ht := ExcNonsplit.mem_ggConjPairs_of_induces hπ hval hyN hyb
    rw [← hrange] at hK ⊢
    exact ExcNonsplit.exists_component_of_core
      (center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (K := GaloisField 2 (2 * f))
        (σ := frobQ 2 f) (Finite.surjective_of_injective (frobQ 2 f).injective))
      hinj hcC hx hy hxy hs ht hK hpK

end Tag

end TwE6Nonsplit

section TagMain

theorem ggNonsplitTag_twistedE6_of_core (h : GGTwE6NonsplitCoreInput) :
    GGNonsplitTag .twistedE6 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy hxN hyN hxD hyD K hK hpK => ?_,
    fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy hxN hyN hxD hyD K K' hK hpK hK' hKK'
      _ => ?_⟩
  all_goals
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, hperf, -⟩ := hpres
    subst hrange
    have hf : 1 ≤ f := hadm.2.1
    obtain ⟨hcL, hcC⟩ := h f p hf hp hp2 hq1 hq2
    obtain ⟨K'', hK'', hKK'', hm⟩ :=
      TwE6Nonsplit.exists_component_twistedE6_of hf hp hp2 hq1 hq2 hcL hcC hker hperf hx hy hxy
        hxN hyN hxD hyD hK hpK
  · exact ⟨K'', hK'', hKK''⟩
  · obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
      hKK' hKK''
    exact hm

end TagMain

end CFSG.StandardType
