module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22so
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace P22sp

variable {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod]

theorem mem_centralizer_iff_fix (D : Data G) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ)
    {Y : Subgroup (MBar D.M D.U)} (hY : Y ≤ mbarImage D.M D.U (proofN D)) {x : G} (hx : x ∈ D.M) :
    x ∈ centralizer (proofIi D (preN D Y) : Set G) ↔
      ∀ v ∈ natIi ρ (mbarImage D.M D.U (proofN D)) Y, ρ (QuotientGroup.mk ⟨x, hx⟩) v = v := by
  have hV := uc22p22xf_hV D
  have hb := bsub_proofIi D e ρ hc hY
  constructor
  · intro h v hv
    have hvI : iota e v ∈ proofIi D (preN D Y) := by
      rw [← hb] at hv
      exact mem_bsub.1 hv
    apply iota_injective e
    rw [iota_rho hV e ρ hc ⟨x, hx⟩ v]
    have h1 := Subgroup.mem_centralizer_iff.1 h _ hvI
    calc x * iota e v * x⁻¹ = iota e v * x * x⁻¹ := by rw [← h1]
      _ = iota e v := by group
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyU : y ∈ D.U := proofIi_le D (preN_le_M D Y) hy
    obtain ⟨v, rfl⟩ := exists_iota e hyU
    have hv : v ∈ natIi ρ (mbarImage D.M D.U (proofN D)) Y := by
      rw [← hb]
      exact mem_bsub.2 hy
    have h1 := iota_rho hV e ρ hc ⟨x, hx⟩ v
    rw [h v hv] at h1
    calc iota e v * x = (x * iota e v * x⁻¹) * x := by rw [← h1]
      _ = x * iota e v := by group

theorem inf_centralizer_le_preMbar (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U))
    (hNb : NbarSplit D Nb) (i : Fin m) :
    proofS D ⊓ centralizer (proofIi D (preN D (Nb i)) : Set G) ≤
      preMbar D (centralizer (Nb i : Set (MBar D.M D.U))) := by
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  rintro s ⟨hs, hsc⟩
  have hsM : s ∈ D.M := proofS_le_M D hs
  obtain ⟨-, f, -, hfI, hfN⟩ := P22x.core25 D Ch h2 h3 h51 hH c e ρ hc d i hs hsM
  have hfix := (mem_centralizer_iff_fix D e ρ hc (d.le i) hsM).1 hsc
  have hf1 : ((f i : ↥(Nb i)) : MBar D.M D.U) = 1 := by
    refine d.faithful i (f i).2 fun v hv => ?_
    rw [← d.pi_act f i hv, ← hfI v hv]
    exact hfix v hv
  refine (mem_preMbar D).2 ⟨hsM, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  have h1 := hfN g hg
  rw [d.conj_natPi f i hg, hf1, one_mul, inv_one, mul_one] at h1
  calc g * (QuotientGroup.mk ⟨s, hsM⟩ : MBar D.M D.U)
      = (QuotientGroup.mk ⟨s, hsM⟩ * g * (QuotientGroup.mk ⟨s, hsM⟩)⁻¹) * QuotientGroup.mk ⟨s, hsM⟩ := by
        rw [h1]
    _ = QuotientGroup.mk ⟨s, hsM⟩ * g := by group

theorem relIndex_mul_card_le (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch)
    (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb)
    (i : Fin m) {A : Subgroup G} (hAN : A ≤ proofN D) (hA2 : IsPGroup 2 A) :
    (centralizer (proofIi D (preN D (Nb i)) : Set G)).relIndex A *
        Nat.card ↥(centralizer (A : Set G) ⊓ proofIi D (preN D (Nb i))) ≤
      Nat.card ↥(proofIi D (preN D (Nb i))) := by
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbardef
  set Ii : Subgroup G := proofIi D (preN D (Nb i)) with hIidef
  have hAM : A ≤ D.M := hAN.trans (uc22p22e_jOf_le_self D.M)
  have hAb : mbarImage D.M D.U A ≤ Nbar := mbarImage_mono D.M D.U hAN
  have hAb2 : IsPGroup 2 (mbarImage D.M D.U A) := (hA2.comap_subtype (K := D.M)).map _
  set ι : ↥A →* MBar D.M D.U := (QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion hAM)
    with hιdef
  have hιA : ∀ a : ↥A, ι a ∈ mbarImage D.M D.U A := fun a => ⟨⟨a, hAM a.2⟩, a.2, rfl⟩
  have hιR : ∀ a : ↥A, ι a ∈ d.natPi.range := fun a => by
    rw [d.natPi_range]
    exact hAb (hιA a)
  set ψ := MonoidHom.ofInjective d.natPi_injective with hψdef
  set θ : ↥A →* ↥(Nb i) :=
    (Pi.evalMonoidHom (fun j => ↥(Nb j)) i).comp (ψ.symm.toMonoidHom.comp (ι.codRestrict _ hιR)) with hθdef
  have hθf : ∀ a : ↥A, d.natPi (ψ.symm ⟨ι a, hιR a⟩) = ι a := fun a => by
    have h := congrArg Subtype.val (ψ.apply_symm_apply ⟨ι a, hιR a⟩)
    rw [hψdef, MonoidHom.ofInjective_apply] at h
    exact h
  have hθa : ∀ a : ↥A, (θ a : ↥(Nb i)) = (ψ.symm ⟨ι a, hιR a⟩) i := fun a => rfl
  have hθact : ∀ a : ↥A, ∀ v ∈ natIi ρ Nbar (Nb i), ρ (ι a) v = ρ ((θ a : ↥(Nb i)) : MBar D.M D.U) v := by
    intro a v hv
    rw [hθa a, ← d.pi_act _ i hv, hθf a]
  have hker : θ.ker ≤ (centralizer (Ii : Set G)).subgroupOf A := by
    intro a ha
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff_fix D e ρ hc (d.le i) (hAM a.2)]
    intro v hv
    have h := hθact a v hv
    rw [MonoidHom.mem_ker.1 ha, OneMemClass.coe_one, map_one, Module.End.one_apply] at h
    exact h
  have hrange : Nat.card θ.range ≤ Nat.card (d.proj i (mbarImage D.M D.U A)) := by
    have hle : θ.range.map (Nb i).subtype ≤ d.proj i (mbarImage D.M D.U A) := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      refine (d.mem_proj i).2 ⟨ψ.symm ⟨ι a, hιR a⟩, ?_, rfl⟩
      rw [hθf a]
      exact hιA a
    calc Nat.card θ.range = Nat.card (θ.range.map (Nb i).subtype) :=
          (Subgroup.card_map_of_injective (Nb i).subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hidx : (centralizer (Ii : Set G)).relIndex A ≤ Nat.card θ.range := by
    rw [← Subgroup.index_ker θ]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hker)
  obtain ⟨hloc, -⟩ := d.local_bound i (d.proj_le i _) (d.isPGroup_proj i hAb2)
  rw [d.inf_modFix_proj i hAb] at hloc
  have hfixle : natIi ρ Nbar (Nb i) ⊓ fixSub ρ (mbarImage D.M D.U A) ≤
      natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) (mbarImage D.M D.U A) := by
    rintro v ⟨hv, hvf⟩
    refine ⟨hv, fun a ha => ?_⟩
    rw [hvf a ha, sub_self]
    exact (natC ρ Nbar).zero_mem
  have hIi : Nat.card ↥(natIi ρ Nbar (Nb i)) = Nat.card Ii := by
    rw [← bsub_proofIi D e ρ hc (d.le i), card_bsub e (proofIi_le D (preN_le_M D (Nb i)))]
  have hCI : Nat.card ↥(natIi ρ Nbar (Nb i) ⊓ fixSub ρ (mbarImage D.M D.U A)) =
      Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := by
    rw [← bsub_proofIi D e ρ hc (d.le i), fixSub_mbarImage hV e ρ hc hAM, ← bsub_inf, inf_comm,
      card_bsub e (inf_le_right.trans (proofIi_le D (preN_le_M D (Nb i))))]
  have hpos : 0 < Nat.card ↥(centralizer (A : Set G) ⊓ Ii) := Nat.card_pos
  calc (centralizer (Ii : Set G)).relIndex A * Nat.card ↥(centralizer (A : Set G) ⊓ Ii)
      ≤ Nat.card (d.proj i (mbarImage D.M D.U A)) * Nat.card ↥(centralizer (A : Set G) ⊓ Ii) :=
        Nat.mul_le_mul_right _ (hidx.trans hrange)
    _ = Nat.card (d.proj i (mbarImage D.M D.U A)) *
          Nat.card ↥(natIi ρ Nbar (Nb i) ⊓ fixSub ρ (mbarImage D.M D.U A)) := by rw [hCI]
    _ ≤ Nat.card (d.proj i (mbarImage D.M D.U A)) *
          Nat.card ↥(natIi ρ Nbar (Nb i) ⊓ modFix ρ (natC ρ Nbar) (mbarImage D.M D.U A)) :=
        Nat.mul_le_mul_left _ (Nat.card_mono (Set.toFinite _) hfixle)
    _ ≤ Nat.card ↥(natIi ρ Nbar (Nb i)) := hloc
    _ = Nat.card Ii := hIi

theorem isElemAbelian_omegaZJ22 (R : Subgroup G) : IsElemAbelian 2 (omegaZJ22 R) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => (uc22p22e_mem_omegaZJ.1 hz).2.2⟩
  obtain ⟨haJ, -, -⟩ := uc22p22e_mem_omegaZJ.1 a.2
  obtain ⟨-, hbc, -⟩ := uc22p22e_mem_omegaZJ.1 b.2
  exact hbc a haJ

end P22sp

open P22sp

end CFSG.LocalAnalysis.UniquenessCase.UC22
