module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem s16c7_quot_isL3 {K : Subgroup G} {Y : Type} [Group Y] (hY : IsL3 Y 1)
    (π : ↥K →* Y) (hπ : Function.Surjective π) (hq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    IsL3 (Bar2 K) 1 ∧ π.ker ≤ CFSG.pCore 2 ↥K := by
  haveI : Finite Y := Finite.of_surjective π hπ
  haveI hs : IsSimpleGroup Y := isSimpleGroup_of_isL3 hY
  have hcard : Nat.card Y = 168 := card_eq_of_isL3 hY
  have h1 : CFSG.pCore 2 ↥K ≤ π.ker := by
    haveI : ((CFSG.pCore 2 ↥K).map π).Normal := Subgroup.Normal.map inferInstance π hπ
    have hNp : IsPGroup 2 ((CFSG.pCore 2 ↥K).map π) := IsPGroup.map CFSG.pCore_isPGroup π
    rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map π) with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      have hY2 : IsPGroup 2 Y := by
        have h2 : IsPGroup 2 (⊤ : Subgroup Y) := h ▸ hNp
        exact h2.of_equiv (Subgroup.topEquiv (G := Y))
      obtain ⟨n, hn⟩ := hY2.exists_card_eq
      rw [hcard] at hn
      have h3 : 3 ∣ 2 ^ n := ⟨56, by omega⟩
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  let π' : Bar2 K →* Y := QuotientGroup.lift (CFSG.pCore 2 ↥K) π h1
  have hπ' : Function.Surjective π' := by
    intro y
    obtain ⟨k, hk⟩ := hπ y
    exact ⟨QuotientGroup.mk k, by simpa [π'] using hk⟩
  have hne : π'.ker ≠ ⊤ := by
    intro htop
    have hone : ∀ y : Y, y = 1 := by
      intro y
      obtain ⟨q, hq'⟩ := hπ' y
      rw [← hq']
      exact MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top q)
    have : Nat.card Y = 1 := by
      haveI : Subsingleton Y := ⟨fun a b => (hone a).trans (hone b).symm⟩
      exact Nat.card_of_subsingleton 1
    omega
  have hcen : π'.ker ≤ Subgroup.center (Bar2 K) :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq π'.ker hne
  have hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup Y, IsPGroup p P → IsCyclic P := by
    intro p hp hp2 P hP
    haveI : Fact p.Prime := ⟨hp⟩
    exact isCyclic_of_card_dvd_prime (card_pGroup_dvd_of_isL3 hY hp hp2 hP)
  have h2 : IsPGroup 2 π'.ker := s16c7_isPGroup_two_ker hq.1 π' hcen hcyc
  have hker : π'.ker = ⊥ := by
    have h3 : π'.ker ≤ CFSG.pCore 2 (Bar2 K) := le_sSup ⟨inferInstance, h2⟩
    rw [TwelveThirteen.pCore_bar2_eq_bot] at h3
    exact le_bot_iff.1 h3
  have hinj : Function.Injective π' := (MonoidHom.ker_eq_bot_iff π').1 hker
  refine ⟨CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.ofBijective π' ⟨hinj, hπ'⟩).symm hY, ?_⟩
  intro x hx
  have h3 : π' (QuotientGroup.mk x) = 1 := by simpa [π'] using hx
  have h4 : (QuotientGroup.mk x : Bar2 K) ∈ π'.ker := h3
  rw [hker, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h4
  exact h4

end Abstract

section Aut

variable {G : Type} [Group G] [Finite G]

theorem s16c7_bar2_of_calC {M V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil ⊥ V) (hKM : K ≤ M) (hK : CFSG.Open.IsQuasisimple (Bar2 K))
    (hKb : IsL3 ↥(barSub ⊥ V hV K) 1) :
    IsL3 (Bar2 K) 1 ∧ K ⊓ centralizer (V : Set G) ≤ pCoreOf 2 K := by
  let ψ : ↥K →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion (hKM.trans hMs))
  have hrange : ψ.range = barSub ⊥ V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion (hKM.trans hMs) k, k.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hY : IsL3 ↥ψ.range 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hrange.symm) hKb
  obtain ⟨h1, h2⟩ := s16c7_quot_isL3 hY ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ) hK
  refine ⟨h1, ?_⟩
  rintro x ⟨hxK, hxc⟩
  have hx : (⟨x, hxK⟩ : ↥K) ∈ ψ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    change actTil ⊥ V hV (Subgroup.inclusion (hKM.trans hMs) ⟨x, hxK⟩) = 1
    rw [actTil_eq_one_iff]
    intro v hv
    have hcomm : v * x = x * v := (Subgroup.mem_centralizer_iff.1 hxc) v hv
    show x * v * x⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G)
    rw [Subgroup.mem_bot, ← hcomm]
    group
  exact ⟨⟨x, hxK⟩, h2 hx, rfl⟩

end Aut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
