module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwoMat
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwoType
import CFSG.RankThree.PartTwo.Sec13.Ronan138SRefl
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi zPi PiField ModThree ModNine IsTypeC Type123)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

theorem kf138TypeTwo : KF138TypeTwo := by
  intro G _ _ A c L E hH hPGL e heE he
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d₀, -, hd₀E, hd₀L, hd₀1, -⟩ := exists_inverting_of_hyp138 hH
  obtain ⟨h, -, hcE, hE3, -, hEN, hCE, -, hC⟩ := hH
  obtain ⟨π, p, f, K, _, hK, hq, φ, D, hD, hτD, -⟩ := hC
  have hL := h.mem_thetaComponentsAt
  have hq2 := Item138Proof.two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL)
    hK hq φ
  have h9 := not_modNine_of_typeC h hcE hE3 hEN hPGL hK hq φ hD hτD
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hx : e ∈ Subgroup.normalizer (L : Set G) := hEN heE
  obtain ⟨y, hyD, hy⟩ := hτD _ (Sec4.mem_autThetaQuot_iff.mpr ⟨e, hx, heE, rfl⟩)
  have hy2 := type123_two_of_not_mem h hEN hCE hd₀E hd₀L hd₀1 hK hq h9 φ hD hτD heE he hyD hy
  have : Finite K := hK.finite
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨e₀, he₀3, he₀1, z, hz, g, hg, hD2⟩ := hy2
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  obtain ⟨ζ, -, rfl⟩ := Sec4.exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  set y₀ := g * Sec4.diagE e₀ * g⁻¹ with hy₀
  have hyy₀ : ProjGenLinGroup.mk y = ProjGenLinGroup.mk y₀ := by
    have h1 : y * GeneralLinearGroup.scalar (Fin 3) ζ = y₀ := by rw [hy₀, ← hD2]; group
    rw [← h1, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  have : Finite (GL (Fin 3) K) := inferInstance
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set S : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    fixedSubgroupOf (KFacts.inducedAutHom L φ ⟨e, hx⟩) with hS
  have hSmem : ∀ w : projImage (slPi π 3 (p ^ f) K),
      w ∈ S ↔ KFacts.inducedAutHom L φ ⟨e, hx⟩ w = w :=
    fun w => mem_fixedSubgroupOf _ w
  have hind : ∀ w : projImage (slPi π 3 (p ^ f) K),
      ((KFacts.inducedAutHom L φ ⟨e, hx⟩ w : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk y₀ * (w : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y₀)⁻¹ := by
    intro w
    have h1 := hy (φ.symm w)
    rw [MulEquiv.apply_symm_apply, hyy₀] at h1
    rw [KFacts.inducedAutHom_apply, MulAut.congr_apply]
    exact h1
  set T := (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y₀}).map ProjGenLinGroup.mk with hT
  have hST : S.map (projImage (slPi π 3 (p ^ f) K)).subtype = T := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨N, hN, hNs⟩ := s.2
      have h1 := hind s
      rw [(hSmem s).mp hs] at h1
      refine ⟨N, ⟨hN, ?_⟩, hNs⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (mem_centralizer_of_mk_conj_pi hK he₀3 h3 hg hN (by rw [hNs]; exact h1.symm))
    · rintro ⟨N, ⟨hN, hNc⟩, rfl⟩
      have hNM : ProjGenLinGroup.mk N ∈ projImage (slPi π 3 (p ^ f) K) := ⟨N, hN, rfl⟩
      refine ⟨⟨_, hNM⟩, (hSmem _).mpr ?_, rfl⟩
      apply Subtype.ext
      rw [hind]
      have hNc' : N * y₀ = y₀ * N := Subgroup.mem_centralizer_singleton_iff.mp hNc
      change ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk N * (ProjGenLinGroup.mk y₀)⁻¹ =
        ProjGenLinGroup.mk N
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [← hNc']
      group
  set I := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hI
  have hx3' : ∃ j : ℕ, e ^ 3 ^ j = 1 := ⟨1, by simpa using hE3.2 e heE⟩
  have hĪ := KFacts.imageModTheta_perfectResidual_centralizer_eq hx hx3'
  have hB := KFacts.map_barCentralizer_eq hx φ S hSmem
  set ψ : (L ⧸ aschbacherSolvableCore 3 L) →* ProjGenLinGroup (Fin 3) K :=
    (projImage (slPi π 3 (p ^ f) K)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (slPi π 3 (p ^ f) K)).subtype_injective.comp φ.injective
  set Λ := ((slPi π 2 (p ^ f) K).map Sec4.blockHom).map (MulAut.conj g).toMonoidHom with hΛ
  have hΛ' : (Sec8.imageModTheta L I).map ψ = Λ.map ProjGenLinGroup.mk := by
    rw [hĪ, hψ, ← Subgroup.map_map, CFSG.RankThree.PartTwo.map_inSubgroup_perfectResidual, hB,
      GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
        (projImage (slPi π 3 (p ^ f) K)).subtype_injective,
      hST, hT, ← PartOne.KFU.map_inSubgroup_perfectResidual,
      perfectResidual_centralizer_conj_pi hK hq hq2 he₀1 hg]
  have hmkinj : Function.Injective (ProjGenLinGroup.mk.comp Λ.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro N hN
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hN
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_block_of_mk_eq_one hK N.2 hN)
  have hrange : (ProjGenLinGroup.mk.comp Λ.subtype).range = Λ.map ProjGenLinGroup.mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eΛ : Λ ≃* Λ.map (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) :=
    (MonoidHom.ofInjective hmkinj).trans (MulEquiv.subgroupCongr hrange)
  let eSL : slPi π 2 (p ^ f) K ≃* Λ :=
    ((slPi π 2 (p ^ f) K).equivMapOfInjective _ Sec4.blockHom_injective).trans
      (((slPi π 2 (p ^ f) K).map Sec4.blockHom).equivMapOfInjective _
        (MulAut.conj g).injective)
  let eĪ : Sec8.imageModTheta L I ≃* slPi π 2 (p ^ f) K :=
    ((Sec8.imageModTheta L I).equivMapOfInjective ψ hψinj).trans
      ((MulEquiv.subgroupCongr hΛ').trans (eΛ.symm.trans eSL.symm))
  have hĪq : IsQuasisimple (Sec8.imageModTheta L I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eĪ.symm
      (Sec11.KS11LieProof.isQuasisimple_slPi_two hK hq hq2)
  have hIL : I ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  let ρ : I →* Sec8.imageModTheta L I :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hIL)).codRestrict
      _ (fun i => ⟨Subgroup.inclusion hIL i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨w, l, hl, rfl⟩
    refine ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, ?_⟩
    apply Subtype.ext
    rfl
  obtain ⟨hθs, hθ3⟩ := Sec6.theta_solvable_and_not_dvd L
  obtain ⟨hks, hk3⟩ := Sec13.ker_facts_of_injective ρ I.subtype I.subtype_injective
    (inSubgroup (aschbacherSolvableCore 3) L) (fun i hi => by
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hIL i) = 1 :=
        congrArg Subtype.val hi
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩) hθs hθ3
  have hIq := Sec14.isQuasisimple_quotient_theta_of_surjective hĪq ρ hρ hks hk3
  refine ⟨fun d hd => ?_, hIq⟩
  obtain ⟨hdE, hdL⟩ := Subgroup.mem_inf.mp hd
  have hd3 : d ^ 3 = 1 := hE3.2 d hdE
  have hxd : e * d = d * e := hEc e heE d hdE
  set D' : L ⧸ aschbacherSolvableCore 3 L :=
    ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) with hD'
  have hD'B : D' ∈ Sec8.barCentralizer (Subgroup.zpowers e) L := by
    rw [KFacts.mem_barCentralizer_zpowers_iff hx, hD', Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show e * d * e⁻¹ = d
    rw [hxd, mul_inv_cancel_right]
  have heD'S : φ D' ∈ S := by
    rw [← hB]
    exact ⟨D', hD'B, rfl⟩
  have heD'T : ψ D' ∈ T := by
    rw [← hST]
    exact ⟨_, heD'S, rfl⟩
  obtain ⟨N, hN, hND⟩ := heD'T
  have hD3 : D' ^ 3 = 1 := by
    rw [hD', ← QuotientGroup.mk_pow]
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, QuotientGroup.mk_one]
  have hN3 : ProjGenLinGroup.mk N ^ 3 = 1 := by
    rw [hND, ← map_pow, hD3, map_one]
  obtain ⟨N'', hN''Λ, hN''⟩ := exists_mem_block_of_mk_pow_three hK hq h9 he₀1 hg hN hN3
  have hD'Ī : D' ∈ Sec8.imageModTheta L I := by
    have h1 : ψ D' ∈ (Sec8.imageModTheta L I).map ψ := by
      rw [hΛ']
      exact ⟨N'', hN''Λ, hN''.trans hND⟩
    obtain ⟨w, hw, hwD⟩ := h1
    rwa [hψinj hwD] at hw
  obtain ⟨l, hl, hlD⟩ := hD'Ī
  have hlI : (l : G) ∈ I := Subgroup.mem_subgroupOf.mp hl
  have hθ' : (l : G)⁻¹ * d ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h1 : ((l : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := hlD
    rw [QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  have hdC : d ∈ L ⊓ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hdL, Subgroup.mem_centralizer_singleton_iff.mpr hxd.symm⟩
  have hdNI : d ∈ Subgroup.normalizer (I : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.le_normalizer hdC)
  have hord : Nat.Coprime (orderOf ((l : G)⁻¹ * d)) 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard _ hθ'
    have hcop : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
    exact (hcop.symm.coprime_dvd_left hdvd)
  exact Sec8.Item812Res2.mem_of_mul_mem_of_coprime hd3 hdNI hlI (by group) hord

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
