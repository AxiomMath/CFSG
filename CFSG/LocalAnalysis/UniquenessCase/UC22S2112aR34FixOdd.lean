module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.GroupTheory.PCore.SolvableRadical
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_fixHom_odd {M L : Subgroup G} (hL : L ∈ calC M) {b : G}
    (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime) (hb2 : orderOf b ≠ 2) :
    ∃ (I : Subgroup (BarInf L)) (φ : ↥(L ⊓ centralizer ({b} : Set G)) →* ↥I),
      I ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) ∧ Function.Surjective φ ∧
      Nat.card φ.ker ∣ Nat.card ↥(CFSG.solvableRadical ↥L) ∧
      ⁅signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩),
        signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)⁆ ≤ I ∧
      ∀ z ∈ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩),
        (orderOf z).Coprime (Nat.card ↥(CFSG.solvableRadical ↥L)) → z ∈ I := by
  classical
  have : Fact (orderOf b).Prime := ⟨hbp⟩
  set θ : MulAut (BarInf L) := inducedBarInfAutHom L ⟨b, hb⟩ with hθdef
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨b, hb⟩ with hαdef
  have hN' : ∀ a : ↥(normalizer (L : Set G)), ∀ n ∈ CFSG.pCore 2 ↥L,
      L.normalizerMonoidHom a n ∈ CFSG.pCore 2 ↥L := by
    intro a n hn
    rw [← Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := 2) (G := ↥L)) (L.normalizerMonoidHom a)]
    exact Subgroup.mem_map_of_mem _ hn
  have hN : ∀ n ∈ CFSG.pCore 2 ↥L, α n ∈ CFSG.pCore 2 ↥L := hN' ⟨b, hb⟩
  set α₂ : MulAut (Bar2 L) :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction L.normalizerMonoidHom
      (CFSG.pCore 2 ↥L) hN' ⟨b, hb⟩ with hα₂def
  have hbpow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ orderOf b = 1 := by
    rw [← Subgroup.orderOf_mk b hb]
    exact pow_orderOf_eq_one _
  have hα : α ^ orderOf b = 1 := by rw [hαdef, ← map_pow, hbpow, map_one]
  have hfix_eq : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup θ =
      signalizerFixedSubgroup θ := Subgroup.ext fun _ => Iff.rfl
  have hα₂q : ∀ k : Bar2 L,
      α₂ k = CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap
        α (CFSG.pCore 2 ↥L) hN k := by
    intro k
    induction k using QuotientGroup.induction_on with
    | H x => rfl
  have hle : CFSG.pCore 2 ↥L ≤ CFSG.solvableRadical ↥L := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.pCore_le_solvableRadical 2 ↥L
  let π : Bar2 L →* BarInf L :=
    QuotientGroup.map (CFSG.pCore 2 ↥L) (CFSG.solvableRadical ↥L) (MonoidHom.id ↥L)
      (by rw [Subgroup.comap_id]; exact hle)
  have hπ : Function.Surjective π :=
    QuotientGroup.map_surjective_of_surjective (CFSG.pCore 2 ↥L) (CFSG.solvableRadical ↥L)
      (MonoidHom.id ↥L) QuotientGroup.mk_surjective (by rw [Subgroup.comap_id]; exact hle)
  have hπker : π.ker = (CFSG.solvableRadical ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    change (QuotientGroup.map (CFSG.pCore 2 ↥L) (CFSG.solvableRadical ↥L) (MonoidHom.id ↥L)
      _).ker = _
    rw [QuotientGroup.ker_map, Subgroup.comap_id]
  have hker : π.ker ≤ Subgroup.center (Bar2 L) := by
    rw [hπker]
    exact (uc22p21k_map_solvableRadical_eq_center hL.2.2).le
  have hkerdvd : Nat.card π.ker ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
    rw [hπker]
    exact Subgroup.card_map_dvd (CFSG.solvableRadical ↥L) (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hαβ : ∀ k : Bar2 L, π (α₂ k) = θ (π k) := by
    intro k
    induction k using QuotientGroup.induction_on with
    | H x => rfl
  have hr : ¬ orderOf b ∣ Nat.card ↥(CFSG.pCore 2 ↥L) := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk] at hd
    have h2 : orderOf b ∣ 2 := hbp.dvd_of_dvd_pow hd
    exact hb2 ((Nat.prime_dvd_prime_iff_eq hbp Nat.prime_two).1 h2)
  let I : Subgroup (BarInf L) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α₂).map π
  let ψ : ↥(L ⊓ centralizer ({b} : Set G)) →* BarInf L :=
    (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp (Subgroup.inclusion inf_le_left)
  have hmem : ∀ x : ↥(L ⊓ centralizer ({b} : Set G)), ψ x ∈ I := by
    intro x
    change π (QuotientGroup.mk (Subgroup.inclusion inf_le_left x)) ∈
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α₂).map π
    refine Subgroup.mem_map_of_mem π ?_
    show α₂ (QuotientGroup.mk (Subgroup.inclusion inf_le_left x)) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_left x)
    rw [hα₂def, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxc := (mem_inf.1 x.2).2
    rw [mem_centralizer_singleton_iff] at hxc
    change b * (x : G) * b⁻¹ = x
    rw [← hxc, mul_inv_cancel_right]
  let φ : ↥(L ⊓ centralizer ({b} : Set G)) →* ↥I := ψ.codRestrict I hmem
  have hφ : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    have hq : CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap
        α (CFSG.pCore 2 ↥L) hN w = w := by
      rw [← hα₂q]
      exact hw
    obtain ⟨y, rfl, hyfix⟩ :=
      (CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_quotient_iff
        α hα (CFSG.pCore 2 ↥L) hN hr w).1 hq
    have hyc : (y : G) ∈ centralizer ({b} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hyfix
      rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      change b * (y : G) * b⁻¹ = y at h1
      calc (y : G) * b = b * y * b⁻¹ * b := by rw [h1]
        _ = b * y := by group
    exact ⟨⟨y, mem_inf.2 ⟨y.2, hyc⟩⟩, rfl⟩
  have hkerφ : Nat.card φ.ker ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
    have hle' : φ.ker.map (Subgroup.inclusion (inf_le_left :
        L ⊓ centralizer ({b} : Set G) ≤ L)) ≤ CFSG.solvableRadical ↥L := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hx))
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective
      (inf_le_left : L ⊓ centralizer ({b} : Set G) ≤ L))]
    exact Subgroup.card_dvd_of_le hle'
  have hIle : I ≤ signalizerFixedSubgroup θ := by
    rw [← hfix_eq]
    exact CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α₂ θ hαβ
  have hcomm : ⁅signalizerFixedSubgroup θ, signalizerFixedSubgroup θ⁆ ≤ I := by
    rw [← hfix_eq]
    exact CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38.commutator_fixSubgroup_le_map
      π hker hπ α₂ θ hαβ
  have hcop : ∀ z ∈ signalizerFixedSubgroup θ,
      (orderOf z).Coprime (Nat.card ↥(CFSG.solvableRadical ↥L)) → z ∈ I := by
    intro z hz hzc
    obtain ⟨w, rfl⟩ := hπ z
    have hz' : π w ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup θ := by
      rw [hfix_eq]
      exact hz
    obtain ⟨z₀, hz₀c, hαw⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.alpha_eq_mul_central π hker α₂ θ hαβ hz'
    have hz₀ker : z₀ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      calc π z₀ = π (w⁻¹ * α₂ w) := by
            rw [show z₀ = w⁻¹ * α₂ w by rw [hαw]; group]
        _ = (π w)⁻¹ * θ (π w) := by rw [map_mul, map_inv, hαβ]
        _ = (π w)⁻¹ * π w := by rw [show θ (π w) = π w from hz']
        _ = 1 := inv_mul_cancel _
    have hz₀dvd : orderOf z₀ ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
      have h1 : orderOf z₀ ∣ Nat.card ↥π.ker := by
        have h2 := orderOf_dvd_natCard (⟨z₀, hz₀ker⟩ : ↥π.ker)
        rwa [Subgroup.orderOf_mk z₀ hz₀ker] at h2
      exact h1.trans hkerdvd
    have hz₀pow : z₀ ^ Nat.card ↥(CFSG.solvableRadical ↥L) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 hz₀dvd
    have hcw : Commute w z₀ := Subgroup.mem_center_iff.1 hz₀c w
    have hfixn : w ^ Nat.card ↥(CFSG.solvableRadical ↥L) ∈
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α₂ := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
      calc α₂ (w ^ Nat.card ↥(CFSG.solvableRadical ↥L))
          = (α₂ w) ^ Nat.card ↥(CFSG.solvableRadical ↥L) := map_pow α₂ w _
        _ = (w * z₀) ^ Nat.card ↥(CFSG.solvableRadical ↥L) := by rw [hαw]
        _ = w ^ Nat.card ↥(CFSG.solvableRadical ↥L) *
            z₀ ^ Nat.card ↥(CFSG.solvableRadical ↥L) := hcw.mul_pow _
        _ = w ^ Nat.card ↥(CFSG.solvableRadical ↥L) := by rw [hz₀pow, mul_one]
    have hzn : (π w) ^ Nat.card ↥(CFSG.solvableRadical ↥L) ∈ I := by
      rw [← map_pow]
      exact Subgroup.mem_map_of_mem π hfixn
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := π w) hzc.symm
    rw [← hm]
    exact I.pow_mem hzn m
  exact ⟨I, φ, hIle, hφ, hkerφ, hcomm, hcop⟩

theorem uc22s2112r34_false_of_fixed_odd {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime) (hb2 : orderOf b ≠ 2)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hrank : 2 ≤ Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)))
    {Y : Subgroup (BarInf L)} (hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩))
    {S : Type} [Group S] [IsSimpleGroup S] (hSns : ¬ Group.IsSolvable S) (g : ↥Y →* S)
    (hg : Function.Surjective g) (hpS : p ∣ Nat.card S) (h5 : p = 5 → ¬ IsAlt S 5) : False := by
  classical
  obtain ⟨hp, -⟩ := D.sig_prime p hpσ
  obtain ⟨I, φ, hIC, hφ, hker, hcomm, hcopI⟩ :=
    uc22s2112r34_exists_fixHom_odd hL hb hbp hb2
  obtain ⟨hHne, hHM, -, hCH⟩ := uc22s2112r2_normalizer hH c hL.1.le hbB hbp
  have hpcop : p.Coprime (Nat.card ↥(CFSG.solvableRadical ↥L)) :=
    (hp.coprime_iff_not_dvd).2 hpN
  have hrankI : 2 ≤ Open.pRank p I := by
    obtain ⟨E, hEC, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hrank
    refine UC6S846.le_pRank' hp (fun x hx => hcopI x (hEC hx) ?_) hEel hEc
    exact hpcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hEel.2 x hx))
  have hrC : 2 ≤ Open.pRank p (L ⊓ centralizer ({b} : Set G)) := by
    have hcop : p.Coprime (Nat.card φ.ker) := hpcop.coprime_dvd_right hker
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel p hp φ hφ hcop,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrankI
  have hrank' : 2 ≤ Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) := by
    obtain ⟨E, hEC, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hrC
    exact UC6S846.le_pRank' hp (hEC.trans hCH) hEel hEc
  have : Group.IsPerfect S := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hbot | htop
    · exact absurd ⟨⟨1, by rw [derivedSeries_one]; exact hbot⟩⟩ hSns
    · exact ⟨htop⟩
  obtain ⟨Y0, hY0Y, hY0perf, f0, hf0⟩ := uc22s2112r2_exists_perfect g hg
  have hY0I : Y0 ≤ I := by
    rw [← hY0perf]
    exact (Subgroup.commutator_mono (hY0Y.trans hY) (hY0Y.trans hY)).trans hcomm
  let Y' : Subgroup ↥I := Y0.subgroupOf I
  let A : Subgroup ↥(L ⊓ centralizer ({b} : Set G)) := Y'.comap φ
  let eA := A.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let g' : ↥(A.map (Subgroup.subtype _)) →* S :=
    ((f0.comp (Subgroup.subgroupOfEquivOfLe hY0I).toMonoidHom).comp (φ.subgroupComap Y')).comp
      eA.symm.toMonoidHom
  have hg' : Function.Surjective g' :=
    ((hf0.comp (Subgroup.subgroupOfEquivOfLe hY0I).surjective).comp
      (φ.subgroupComap_surjective Y' hφ)).comp eA.symm.surjective
  obtain ⟨D0, hD0A, hD0perf, f0', hf0'⟩ := uc22s2112r2_exists_perfect g' hg'
  exact uc22s2112r2_false_of_kf7 hKF7 hpσ hMs hHne hHM hrank'
    ((hD0A.trans (Subgroup.map_subtype_le A)).trans hCH) hD0perf hSns f0' hf0' hpS h5

section Fund


theorem uc22s2112r34_false_of_fund_odd {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf2 : 2 ≤ f) (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M)
    {b : G} (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) (hbp : (orderOf b).Prime)
    (hb2 : orderOf b ≠ 2) (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {K : Subgroup (BarInf L)} (hK : IsFundamentalOver (p ^ f) K)
    (hKb : K ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq9 : 9 ≤ p ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  have hrank : 2 ≤ CFSG.Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) :=
    hf2.trans ((uc22s2112r34_le_pRank_of_isFundamentalOver hp (by omega) hK).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hKb))
  obtain ⟨k, hk, hfk, g, hg⟩ := uc22s2112r34_fund_onto_psl2 (by omega) hK
  obtain ⟨hs, hns, -, hdvd⟩ := uc22s2112r2_psl2_facts hp2 hk (by omega)
  have := hs
  refine uc22s2112r34_false_of_fixed_odd hKF7 hH c hL hpσ hMs hbB hb hbp hb2 hpN hrank hKb hns g hg
    ((dvd_pow_self p (by omega)).trans hdvd) ?_
  rintro rfl ⟨e⟩
  have h9 : 9 ≤ 5 ^ k := hq9.trans hfk
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k
    norm_num at h9
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h25 := (pow_dvd_pow 5 hk2).trans hdvd
  rw [Nat.card_congr e.toEquiv, h60] at h25
  norm_num at h25

end Fund

end CFSG.LocalAnalysis.UniquenessCase.UC22
