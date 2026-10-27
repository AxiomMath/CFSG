module

import CFSG.Yardstones.Mf4cdcdf2e013.StatementCompatibility
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Ctx812
import CFSG.GroupTheory.PRankCommutingPerfect
import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp
import CFSG.Quasithin.Background.RonanD33
import CFSG.Quasithin.Background.A1a
import CFSG.Quasithin.Background.A4Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_asc83CComponent {M L X : Subgroup G}
    (hL : Asc83CComponent M L) (hX : Asc83CComponent M X) (hne : L ≠ X) :
    ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLc : L ∈ CFSG.Quasithin.cComp M :=
    CFSG.Quasithin.mem_cComp_iff.mpr (asc83CComponent_quasithinIsCComponent hL)
  have hXc : X ∈ CFSG.Quasithin.cComp M :=
    CFSG.Quasithin.mem_cComp_iff.mpr (asc83CComponent_quasithinIsCComponent hX)
  let K : Subgroup ↥M := CFSG.pCore 2 ↥M
  haveI hKn : K.Normal := CFSG.pCore_normal
  let π : ↥M →* (↥M ⧸ K) := QuotientGroup.mk' K
  let l : Subgroup ↥M := L.subgroupOf M
  let x : Subgroup ↥M := X.subgroupOf M
  have hlmap : l.map M.subtype = L := Subgroup.map_subgroupOf_eq_of_le hL.1
  have hxmap : x.map M.subtype = X := Subgroup.map_subgroupOf_eq_of_le hX.1
  have hlc : l ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥M) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hLc
  have hxc : x ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥M) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hXc
  have hlne : l ≠ x := by
    intro h
    exact hne (by rw [← hlmap, ← hxmap, h])
  have hK2 : IsPGroup 2 K := CFSG.pCore_isPGroup
  haveI : Group.IsNilpotent ↥K := hK2.isNilpotent
  have hKsolv : Group.IsSolvable ↥K := IsNilpotent.to_isSolvable
  have hbij := CFSG.Quasithin.cComp_quotient_bijOn K hKsolv
  have hlRmem : l.map π ∈ CFSG.Quasithin.cComp (⊤ : Subgroup (↥M ⧸ K)) := hbij.mapsTo hlc
  have hxRmem : x.map π ∈ CFSG.Quasithin.cComp (⊤ : Subgroup (↥M ⧸ K)) := hbij.mapsTo hxc
  have hlRne : l.map π ≠ x.map π := fun h => hlne (hbij.injOn hlc hxc h)
  have hqc : CFSG.Open.pCoreOf 2 l ≤ π.ker := by
    have hsub : CFSG.Open.IsSubnormal l (⊤ : Subgroup ↥M) :=
      CFSG.Quasithin.subnormal_of_mem_cComp hlc
    have hle := CFSG.Quasithin.A4.pCoreOf_le_of_subnormal (p := 2) hsub
    rw [CFSG.Quasithin.pCoreOf_top 2] at hle
    rwa [QuotientGroup.ker_mk' K]
  have hnt : ¬ l ≤ π.ker := by
    intro hle
    rw [QuotientGroup.ker_mk' K] at hle
    have hl2 : IsPGroup 2 ↥l := hK2.to_le hle
    haveI : Group.IsNilpotent ↥l := hl2.isNilpotent
    haveI : Group.IsSolvable ↥l := IsNilpotent.to_isSolvable
    exact CFSG.Quasithin.not_isSolvable_of_mem_cComp hlc inferInstance
  have hlRq : CFSG.IsQuasisimple ↥(l.map π) := by
    refine CFSG.Quasithin.RonanD33.isQuasisimple_map_of_pCore_le_ker (L := l) (ρ := π) ?_ hqc hnt
    obtain ⟨hcore, hq'⟩ :=
      quasisimpleModOTwo_subgroupOf hL.1 hL.2.2.2
    letI := hcore
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq'
  have hxc' : CFSG.Open.pCoreOf 2 x ≤ π.ker := by
    have hsub : CFSG.Open.IsSubnormal x (⊤ : Subgroup ↥M) :=
      CFSG.Quasithin.subnormal_of_mem_cComp hxc
    have hle := CFSG.Quasithin.A4.pCoreOf_le_of_subnormal (p := 2) hsub
    rw [CFSG.Quasithin.pCoreOf_top 2] at hle
    rwa [QuotientGroup.ker_mk' K]
  have hnt' : ¬ x ≤ π.ker := by
    intro hle
    rw [QuotientGroup.ker_mk' K] at hle
    have hx2 : IsPGroup 2 ↥x := hK2.to_le hle
    haveI : Group.IsNilpotent ↥x := hx2.isNilpotent
    haveI : Group.IsSolvable ↥x := IsNilpotent.to_isSolvable
    exact CFSG.Quasithin.not_isSolvable_of_mem_cComp hxc inferInstance
  have hxRq : CFSG.IsQuasisimple ↥(x.map π) := by
    refine CFSG.Quasithin.RonanD33.isQuasisimple_map_of_pCore_le_ker (L := x) (ρ := π) ?_ hxc' hnt'
    obtain ⟨hcore, hq'⟩ :=
      quasisimpleModOTwo_subgroupOf hX.1 hX.2.2.2
    letI := hcore
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq'
  have hcommR : ⁅l.map π, x.map π⁆ = ⊥ := by
    rcases CFSG.Quasithin.H13.cComp_eq_or_commutator_eq_bot_of_isQuasisimple
      hlRmem hxRmem hlRq hxRq with h | h
    · exact absurd h hlRne
    · exact h
  have hcommH : ⁅l, x⁆ ≤ K := by
    have hmapcomm : ⁅l.map π, x.map π⁆ = (⁅l, x⁆).map π :=
      (Subgroup.map_commutator l x π).symm
    rw [hmapcomm, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hcommR
    exact hcommR
  calc ⁅L, X⁆ = (⁅l, x⁆).map M.subtype := by
        rw [Subgroup.map_commutator, hlmap, hxmap]
    _ ≤ K.map M.subtype := Subgroup.map_mono hcommH
    _ = CFSG.Open.pCoreOf 2 M := rfl

theorem asc83CComponent_map_conj {M L : Subgroup G} (hL : Asc83CComponent M L) {m : G}
    (hm : m ∈ M) :
    Asc83CComponent M (L.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨hLM, hsub, hperf, hq⟩ := hL
  let f : G →* G := (MulAut.conj m).toMonoidHom
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hLM hx)) (M.inv_mem hm)
  · have h := CFSG.Quasithin.A3.subnormal_map f hsub
    rw [show Subgroup.map f M = M from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)] at h
    exact h
  · rw [← Subgroup.map_commutator, hperf]
  · obtain ⟨hcore, hq'⟩ := hq
    letI := hcore
    let equivalence := Subgroup.equivMapOfInjective L f (MulAut.conj m).injective
    have coreMap : (CFSG.Open.pCore 2 ↥L).map equivalence.toMonoidHom =
        CFSG.Open.pCore 2 ↥(L.map f) := CFSG.pCore_map_iso 2 equivalence
    let quotientEquivalence := QuotientGroup.congr (CFSG.Open.pCore 2 ↥L)
      (CFSG.Open.pCore 2 ↥(L.map f)) equivalence coreMap
    exact ⟨inferInstance, (CFSG.Open.IsQuasisimple.congr quotientEquivalence).mp hq'⟩

theorem le_normalizer_of_asc83CComponent {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) {M L : Subgroup G}
    (hL : Asc83CComponent M L) (hqL : q ∣ Nat.card L)
    (hrank : CFSG.Open.pRank q M ≤ CFSG.Open.pRank q L) :
    M ≤ Subgroup.normalizer (L : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hL' : Asc83CComponent M (L.map (MulAut.conj m).toMonoidHom) :=
    asc83CComponent_map_conj hL hm
  have hqL' : q ∣ Nat.card (L.map (MulAut.conj m).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact hqL
  have hcomm : ⁅L, L.map (MulAut.conj m).toMonoidHom⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    commutator_le_pCoreOf_of_asc83CComponent hL hL' (Ne.symm hne)
  have hrank' := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := q) hq
    hL.1 hL'.1 hcomm hL'.2.2.1 hqL'
  omega

namespace Ctx812E

theorem map_conj_mem_of_asc83CComponent (c : Ctx812E G) {m : G} (hm : m ∈ c.S.M)
    {L₁ L₂ L₃ Y : Subgroup G} (hLjoin : c.L = L₁ ⊔ L₂ ⊔ L₃)
    (hcomp₁ : Asc83CComponent c.S.M L₁) (hcomp₂ : Asc83CComponent c.S.M L₂)
    (hcomp₃ : Asc83CComponent c.S.M L₃)
    (hY : Asc83CComponent c.S.M Y) (hYrank : CFSG.Open.pRank 3 Y = 1) :
    Y.map (MulAut.conj m).toMonoidHom = L₁ ∨
      Y.map (MulAut.conj m).toMonoidHom = L₂ ∨
        Y.map (MulAut.conj m).toMonoidHom = L₃ := by
  let f : G →* G := (MulAut.conj m).toMonoidHom
  set Y' : Subgroup G := Y.map f with hY'
  have hY'comp : Asc83CComponent c.S.M Y' := asc83CComponent_map_conj hY hm
  have hY'rank : CFSG.Open.pRank 3 Y' = 1 := by
    rw [hY', CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (Y.map f),
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num : (1 : ℕ) < 3)
        (Subgroup.equivMapOfInjective Y f (MulAut.conj m).injective),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Y]
    exact hYrank
  have hY'3 : 3 ∣ Nat.card Y' := by
    obtain ⟨E, hEY', -, hcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num : (1 : ℕ) < 3) Y'
    rw [hY'rank, pow_one] at hcard
    exact hcard ▸ Subgroup.card_dvd_of_le hEY'
  by_contra hnot
  push Not at hnot
  obtain ⟨h1, h2, h3⟩ := hnot
  have hc1 : ⁅Y', L₁⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M :=
    commutator_le_pCoreOf_of_asc83CComponent hY'comp hcomp₁ h1
  have hc2 : ⁅Y', L₂⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M :=
    commutator_le_pCoreOf_of_asc83CComponent hY'comp hcomp₂ h2
  have hc3 : ⁅Y', L₃⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M :=
    commutator_le_pCoreOf_of_asc83CComponent hY'comp hcomp₃ h3
  have hQN : c.S.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hN1 : L₁ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    hcomp₁.1.trans hQN
  have hN2 : L₂ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    hcomp₂.1.trans hQN
  have hN3 : L₃ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    hcomp₃.1.trans hQN
  have h12 : ⁅L₁ ⊔ L₂, Y'⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
    refine CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      L₁ L₂ Y' (CFSG.Open.pCoreOf 2 c.S.M) ?_ ?_ hN1 hN2
    · rw [Subgroup.commutator_comm]; exact hc1
    · rw [Subgroup.commutator_comm]; exact hc2
  have h123 : ⁅L₁ ⊔ L₂ ⊔ L₃, Y'⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
    refine CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      (L₁ ⊔ L₂) L₃ Y' (CFSG.Open.pCoreOf 2 c.S.M) h12 ?_ (sup_le hN1 hN2) hN3
    rw [Subgroup.commutator_comm]; exact hc3
  have hcommL : ⁅c.L, Y'⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
    rw [hLjoin]
    exact h123
  have hcontr := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 3)
    (by norm_num) c.hyp81.1 hY'comp.1 hcommL hY'comp.2.2.1 hY'3
  rw [pRank_three_L c, pRank_three_M c] at hcontr
  omega

theorem le_normalizer_L (c : Ctx812E G) :
    c.S.M ≤ Subgroup.normalizer (c.L : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rcases c.hyp81.2.2.2.2 with hq | ⟨L₁, L₂, L₃, hLjoin, hL₁L, hL₂L, hL₃L,
    hcomp₁, hr₁, hcomp₂, hr₂, hcomp₃, hr₃, -⟩
  ·
    have hAsc : Asc83CComponent c.S.M c.L :=
      ⟨c.hyp81.1, c.hyp81.2.1, c.hyp81.2.2.1, hq⟩
    have hqL : 3 ∣ Nat.card c.L := by
      obtain ⟨E, hEL, -, hcard⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num : (1 : ℕ) < 3) c.L
      rw [pRank_three_L c] at hcard
      have h3 : Nat.card E = 27 := by rw [hcard]; norm_num
      exact (show 3 ∣ Nat.card E by rw [h3]; norm_num).trans (Subgroup.card_dvd_of_le hEL)
    have hrank : CFSG.Open.pRank 3 c.S.M ≤ CFSG.Open.pRank 3 c.L := by
      rw [pRank_three_M c, pRank_three_L c]
    exact le_normalizer_of_asc83CComponent (q := 3) (by norm_num) hAsc hqL hrank
  ·
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    set f : G →* G := (MulAut.conj m).toMonoidHom with hf
    have hconj_mem : ∀ Y : Subgroup G, Asc83CComponent c.S.M Y →
        CFSG.Open.pRank 3 Y = 1 →
        Y.map f = L₁ ∨ Y.map f = L₂ ∨ Y.map f = L₃ :=
      fun Y hYcomp hYrank =>
        map_conj_mem_of_asc83CComponent c hm hLjoin hcomp₁ hcomp₂ hcomp₃ hYcomp hYrank
    have hL₁' : L₁.map f ≤ c.L := by
      rcases hconj_mem L₁ hcomp₁ hr₁ with h | h | h
      · rw [h]; exact hL₁L
      · rw [h]; exact hL₂L
      · rw [h]; exact hL₃L
    have hL₂' : L₂.map f ≤ c.L := by
      rcases hconj_mem L₂ hcomp₂ hr₂ with h | h | h
      · rw [h]; exact hL₁L
      · rw [h]; exact hL₂L
      · rw [h]; exact hL₃L
    have hL₃' : L₃.map f ≤ c.L := by
      rcases hconj_mem L₃ hcomp₃ hr₃ with h | h | h
      · rw [h]; exact hL₁L
      · rw [h]; exact hL₂L
      · rw [h]; exact hL₃L
    have hle : c.L.map f ≤ c.L := by
      conv_lhs => rw [hLjoin]
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le (sup_le hL₁' hL₂') hL₃'
    have hcard : Nat.card (c.L.map f) = Nat.card c.L :=
      Subgroup.card_map_of_injective (MulAut.conj m).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

end Ctx812E

namespace Counterexample4

theorem le_normalizer_L (c : Counterexample4 G) :
    c.S.M ≤ Subgroup.normalizer (c.L : Set G) :=
  Ctx812E.le_normalizer_L c.toCtx812.toCtx812E

end Counterexample4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
