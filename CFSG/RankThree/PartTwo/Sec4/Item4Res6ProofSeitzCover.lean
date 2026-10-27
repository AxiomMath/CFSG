module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
import CFSG.LieType.Classical.SteinbergBLSymplectic
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6Seitz

open CFSG CFSG.Assembly.LowTwoRank TauCeti CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

noncomputable def equivOfCenterEqBot {X S : Type} [Group X] [Group S]
    (hZ : Subgroup.center X = ⊥) (θ : X ⧸ Subgroup.center X ≃* S) : X ≃* S :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ

theorem odd_card_of_isPGroup_three {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : IsPGroup 3 H) : Odd (Nat.card H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [hk]
  exact Odd.pow (by decide)

theorem ker_centralQuotient {X S : Type} [Group X] [Group S]
    (θ : X ⧸ Subgroup.center X ≃* S) :
    (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem center_eq_bot_of_cover {X S : Type} [Group X] [Finite X] [Group S]
    (hZ3 : IsPGroup 3 (Subgroup.center X)) (θ : X ⧸ Subgroup.center X ≃* S)
    (hcov : ∀ π : X →* S, Function.Surjective π → π.ker ≤ Subgroup.center X →
      Odd (Nat.card π.ker) → π.ker = ⊥) : Subgroup.center X = ⊥ := by
  have hker := ker_centralQuotient θ
  have h := hcov _ (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le
    (by rw [hker]; exact odd_card_of_isPGroup_three hZ3)
  rwa [hker] at h

theorem center_eq_bot_of_split {H L : Type} [Group H] [Finite H] [Group L] [Finite L]
    [Group.IsPerfect L] {D : Subgroup H} [D.Normal] (e : L ⧸ Subgroup.center L ≃* H ⧸ D)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : H →* E, ∀ g, π (s g) = g)
    (hD : ∀ d ∈ D, d ^ 4 = 1) (hZ3 : IsPGroup 3 (Subgroup.center L)) :
    Subgroup.center L = ⊥ := by
  obtain ⟨hsurj, hcen, -⟩ := CFSG.SectionRank.EvenCover.pullbackFst_centralQuotientMap e
  obtain ⟨s, hs⟩ := hsplit _ _ hsurj hcen
  obtain ⟨φ, -, -, hDφ⟩ := CFSG.SectionRank.EvenCover.perfect_cover_map_of_section e s hs
  rw [← hDφ, eq_bot_iff]
  rintro _ ⟨d, hd, rfl⟩
  have hmem : φ d ∈ Subgroup.center L := hDφ ▸ ⟨d, hd, rfl⟩
  obtain ⟨k, hk⟩ := hZ3 ⟨φ d, hmem⟩
  have h1 : orderOf (φ d) ∣ 4 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hD d hd, map_one])
  have h2 : orderOf (φ d) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have hcop : Nat.gcd (3 ^ k) 4 = 1 := Nat.Coprime.pow_left k (by norm_num)
  have h3 : orderOf (φ d) ∣ 1 := hcop ▸ Nat.dvd_gcd h2 h1
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  exact Nat.dvd_one.mp h3

theorem center_eq_bot_of_cyclic_sylow {X S : Type} [Group X] [Finite X] [Group S] [Finite S]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (θ : X ⧸ Subgroup.center X ≃* S) (hcyc : ∀ Q : Sylow 3 S, IsCyclic (Q : Subgroup S)) :
    Subgroup.center X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect X := hq.1
  set π : X →* S := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := ker_centralQuotient θ
  have hkp : IsPGroup 3 π.ker := by rw [hker]; exact hZ3
  have htp : IsPGroup 3 (⊤ : Subgroup π.ker) := hkp.of_equiv (Subgroup.topEquiv).symm
  obtain ⟨C, hC⟩ := htp.exists_le_sylow
  obtain ⟨Q⟩ : Nonempty (Sylow 3 S) := inferInstance
  have hC1 := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπs
    (by rw [hker]) C Q (hcyc Q)
  rw [← hker, eq_bot_iff]
  intro x hx
  have hxC : (⟨x, hx⟩ : π.ker) ∈ (C : Subgroup π.ker) := hC (Subgroup.mem_top _)
  rw [hC1, Subgroup.mem_bot] at hxC
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxC)

theorem center_eq_bot_of_projSL_three {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) (θ : X ⧸ Subgroup.center X ≃* projSL 3 K) :
    Subgroup.center X = ⊥ := by
  have : Finite (projSL 3 K) := Finite.of_equiv _ θ.toEquiv
  exact center_eq_bot_of_cyclic_sylow hq hZ3 θ
    (fun Q => KFacts.isCyclic_sylow_three_projSL hK Q)

theorem center_eq_bot_of_projSU_three {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0)
    (hq1 : p ^ f % 3 = 1) (θ : X ⧸ Subgroup.center X ≃* projSU 3 p f) :
    Subgroup.center X = ⊥ := by
  have : Finite (projSU 3 p f) := Finite.of_equiv _ θ.toEquiv
  exact center_eq_bot_of_cyclic_sylow hq hZ3 θ
    (fun Q => KFacts.isCyclic_sylow_three_of_mulEquiv_projSU hf hq1 (MulEquiv.refl _) Q)

theorem center_eq_bot_of_projSL_four {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {F : Type} [Field F] [Finite F]
    (hF : 5 ≤ Nat.card F) (θ : X ⧸ Subgroup.center X ≃* projSL 4 F) :
    Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  have : DecidableEq F := Classical.decEq F
  refine center_eq_bot_of_split (H := Matrix.SpecialLinearGroup (Fin 4) F)
    (D := Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F))
    (θ.trans (Sec4.projSLEquivPSLn 4 F)) (fun E _ _ π hπ hcen => ?_) (fun d hd => ?_) hZ3
  · exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (m := 3)
      (by norm_num) hF hπ hcen
  · obtain ⟨r, hr, hrd⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hd
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrd, Matrix.SpecialLinearGroup.coe_one,
      ← map_pow, hr, map_one]

theorem center_eq_bot_of_projSp_two {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {F : Type} [Field F] [Finite F]
    (hF : 5 ≤ Nat.card F) (θ : X ⧸ Subgroup.center X ≃* projSp 2 F) :
    Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  refine center_eq_bot_of_split (θ.trans (Sec4.projSpEquivStatedProj 2 F))
    (fun E _ _ π hπ hcen => ?_) (fun d hd => ?_) hZ3
  · exact CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central (by norm_num) hF
      hπ hcen
  · obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hd
    have hc2 : c ^ 2 = 1 := (CFSG.LieType.Classical.scalar_mem_statedSp_iff (by norm_num) c).mp
      (hc ▸ d.2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, show 4 = 2 * 2 by rfl, pow_mul, hc2, one_pow, map_one,
      Subgroup.coe_one]

theorem center_eq_bot_of_projSU_four
    {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h4 : 4 ≤ p ^ e) (θ : X ⧸ Subgroup.center X ≃* projSU 4 p e) :
    Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  set F := GaloisField p (2 * e)
  have hF : Nat.card F = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  refine center_eq_bot_of_split (θ.trans (Sec4.projSUEquivStatedProj 4 p e))
    (fun E _ _ π hπ hcen => ?_) (fun d hd => ?_) hZ3
  · set ψ := CFSG.LieType.Universal.Unitary.equivStatedSU (p := p) (f := e) hF 4
    have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ ψ.symm.injective]
    obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central
      (p := p) hF (by decide) le_rfl h4 (π := ψ.symm.toMonoidHom.comp π)
      (ψ.symm.surjective.comp hπ) (hker ▸ hcen)
    exact ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective (hs (ψ.symm g))⟩
  · obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hd
    have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU d.2
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hc4 : c ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc4, map_one, Subgroup.coe_one]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem center_eq_bot_of_G2
    {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) {p f : ℕ}
    (hmod : ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 p f) (h5 : 5 ≤ p ^ f) :
    Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hZK := center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let eC : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  set ψ : X →* adjointGroup .G2 K :=
    (e.trans eC).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hψ
  have hψker : ψ.ker = Subgroup.center X := ker_centralQuotient (e.trans eC)
  have hψs : Function.Surjective ψ := (e.trans eC).surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_exists_section_of_central
    (K := K) (by rw [hK]; exact h5) hψs hψker.le
  have h := CFSG.SectionRank.ker_eq_bot_of_section_of_perfect ψ hψker.le σ hσ
  rwa [hψker] at h

theorem center_eq_bot_of_trialityD4
    {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X)) {f : ℕ}
    (hmod : ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .trialityD4 2 f) :
    Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  exact center_eq_bot_of_cover hZ3 (MulEquiv.refl _) fun π hπ hC hodd =>
    CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hmod π hπ hC hodd

theorem center_eq_bot_of_reeF4
    {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X)) {m : ℕ}
    (hm : (LieTypeIndex.reeF4 m).Valid)
    (θ : X ⧸ Subgroup.center X ≃* (CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group) :
    Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  obtain ⟨K, _, _, _, a, ha, hK, ⟨ι⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model
    (Census.bridgeExceptional46.reeF4 m hm)
  exact center_eq_bot_of_cover hZ3 (θ.trans ι) fun π hπ hC hodd =>
    CFSG.SectionRank.LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki
      CFSG.SectionRank.LargeRee.suzukiBlockInputs ha hK π hπ hC hodd

end CFSG.RankThree.PartTwo.Sec4.Res6Seitz
