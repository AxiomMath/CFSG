module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K326Dichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndNineSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem isSylowOf_top_of_isSylowOf_M (F : A10Frame c) (hF : A10Facts F)
    {P' : Subgroup G} (hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' D.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPGtop : CFSG.ABGLocalTools.IsSylowOf 3 F.P ⊤ := isSylowOf_top F hF.normalizer_A
  refine CFSG.ABGLocalTools.isSylowOf_of_card (P := P') (K := ⊤) le_top ?_
  calc Nat.card P' = 3 ^ (Nat.card D.M).factorization 3 := hP'.card_eq
    _ = Nat.card F.P := F.sylow.card_eq.symm
    _ = 3 ^ (Nat.card (⊤ : Subgroup G)).factorization 3 := hPGtop.card_eq

private theorem centralizer_ne_top (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {B : Subgroup G} (hB : B ≠ ⊥) : Subgroup.centralizer (B : Set G) ≠ ⊤ := by
  intro htop
  have hcenter : Subgroup.center G = ⊥ := by
    haveI : IsSimpleGroup G := hs
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative (G := G) ?_
    rw [isMulCommutative_iff]
    rintro h
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (h x y)
  apply hB
  rw [eq_bot_iff]
  intro b hb
  have hz : b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (B : Set G) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
  rw [hcenter] at hz
  exact hz

private theorem le_centralizer_of_mem_center {B P' : Subgroup G} (hBP' : B ≤ P')
    (hB3 : Nat.card B = 3) (hP'B : P' ≤ Subgroup.centralizer (B : Set G))
    (e : ↥P' ≃* UC326.ZWr 1) {x : G} (hxP' : x ∈ P')
    (hxcent : ∀ g ∈ P', g * x = x * g) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  have hxZ : (⟨x, hxP'⟩ : ↥P') ∈ Subgroup.center ↥P' := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa using hxcent (g : G) g.2
  have hcard_center : Nat.card ↥(Subgroup.center ↥P') = 3 := by
    have h := (UC326.zwr_card_center (n := 1) le_rfl e).2.2
    simpa using h
  have hBsub_le : B.subgroupOf P' ≤ Subgroup.center ↥P' := by
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa using (Subgroup.mem_centralizer_iff.mp (hP'B g.2) (b : G) hb).symm
  have hcard_Bsub : Nat.card ↥(B.subgroupOf P') = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP').toEquiv, hB3]
  have heq : B.subgroupOf P' = Subgroup.center ↥P' :=
    Subgroup.eq_of_le_of_card_ge hBsub_le (by rw [hcard_center, hcard_Bsub])
  have hxB : x ∈ B := by
    have hmem : (⟨x, hxP'⟩ : ↥P') ∈ B.subgroupOf P' := by
      rw [heq]
      exact hxZ
    simpa using Subgroup.mem_subgroupOf.mp hmem
  refine Subgroup.centralizer_le (fun y hy => ?_)
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hxB

private theorem exists_sylow_quotient_zwr {H P' : Subgroup G} (hP'leH : P' ≤ H)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤) (e : ↥P' ≃* UC326.ZWr 1) :
    ∃ S : Sylow 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H),
      Nonempty (↥(S : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) ≃* UC326.ZWr 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOnotdvd : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
  let π : ↥H →* (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker π) := by
    rw [show MonoidHom.ker π = CFSG.pPrimeCore 3 ↥H from QuotientGroup.ker_mk' _]
    exact hOnotdvd
  have hP'H_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (P'.subgroupOf H) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) (K := H)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP'leH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hPG.of_le hP'leH le_top
  have hSsub_sylow : CFSG.ABGLocalTools.IsSylowOf 3 ((P'.subgroupOf H).map π) ⊤ := by
    have h1 := CFSG.isSylowOf_map_of_not_dvd_card_ker π hπsurj (p := 3) Nat.prime_three
      hker hP'H_sylow
    simpa [Subgroup.map_top_of_surjective π hπsurj] using h1
  obtain ⟨-, hPp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hSsub_sylow
  have hdvd' : ¬ 3 ∣ ((P'.subgroupOf H).map π).index := by simpa using hdvd
  have hcoe : (hPp.toSylow hdvd' : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) =
      (P'.subgroupOf H).map π := IsPGroup.toSylow_coe hPp hdvd'
  have hfinj : Function.Injective (π.comp (P'.subgroupOf H).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3)
      (N := CFSG.pPrimeCore 3 ↥H) hOnotdvd hP'H_sylow.isPGroup
  have hrange : (π.comp (P'.subgroupOf H).subtype).range = (P'.subgroupOf H).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨hPp.toSylow hdvd', ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hcoe).trans
    (((MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hP'leH).trans e))

theorem centralizer_le_of_isSylowOf (F : A10Frame c) (hF : A10Facts F) (hK : UC326.K326P2S)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3)
    {P' : Subgroup G} (hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' D.M) (hAP' : F.A ≤ P')
    (hP'B : P' ≤ Subgroup.centralizer (B : Set G)) (e : ↥P' ≃* UC326.ZWr 1)
    {a : G} (haA : a ∈ F.A) (ha3 : F.deg (Subgroup.zpowers a) = 3)
    (haZ : a ∉ UC326.z2Of P') :
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
  classical
  have hBleP' : B ≤ P' := hBA.trans hAP'
  have hBleL : B ≤ c.L := hBA.trans (F.A_le.trans F.P_le_L)
  have hBne : B ≠ ⊥ := by
    rintro rfl
    rw [show Nat.card (⊥ : Subgroup G) = 1 from Subgroup.card_eq_one.mpr rfl] at hB3
    omega
  have hBpg : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB3]; norm_num)
  have hCa : Subgroup.centralizer ({a} : Set G) ≤ D.M := F.centralizer_le_M_of_deg_three hF haA ha3
  have hPG : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ := isSylowOf_top_of_isSylowOf_M F hF hP'
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  have hHne : H ≠ ⊤ :=
    centralizer_ne_top D.standing.simple D.standing.nonab hBne
  have hcent : ∀ x ∈ P', (∀ g ∈ P', g * x = x * g) → x ^ 3 = 1 →
      H ≤ Subgroup.centralizer ({x} : Set G) :=
    fun x hxP' hxcent _ => le_centralizer_of_mem_center hBleP' hB3 hP'B e hxP' hxcent
  rcases k326_dichotomy_of_E27 (G := G) hK c.kProper (M := D.M) (P := P') (A := F.A) (H := H)
      hHne hP'B hPG (le_refl 1) e hAP' F.elemAbelian F.card_A hcent haA haZ
      hF.normalizer_A hCa with h | ⟨-, hex⟩
  · exact h
  ·
    obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_quotient_zwr hP'B hPG e
    have hq : ¬ 5 ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
      A10Five.not_five_dvd_card (X := ↥H ⧸ CFSG.pPrimeCore 3 ↥H)
        (CFSG.pPrimeCore_quotient_eq_bot (G := ↥H) Nat.prime_three) S eS hex.1
    exact A10Five.le_sup_relPPrimeCore_of_five (M := D.M) (H := H)
      (fun R hR hR1 hRM => normalizer_le_of_isPGroup_five F hR hR1 hRM)
      (five_dvd_card_centralizer_inf F (fun x hx h => (a10Hom_eq_one_iff F hx).mp h)
        (three_le_pRank_five F) hBleL hBpg)
      hq

theorem centralizer_le_of_deg_nine (F : A10Frame c) (hF : A10Facts F) (hK : UC326.K326P2S)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
  obtain ⟨P', hP', hAP', hP'B⟩ := F.exists_isSylowOf_le_centralizer hBA hB3 hB9
  obtain ⟨e⟩ := F.nonempty_mulEquiv_zwr hP'
  obtain ⟨a, haA, ha3, haZ⟩ := F.exists_deg_three_not_mem_z2Of hP' hAP'
  exact F.centralizer_le_of_isSylowOf hF hK hBA hB3 hP' hAP' hP'B e haA ha3 haZ

theorem centralizer_le_of_card_eq_three (F : A10Frame c) (hF : A10Facts F)
    (hK : UC326.K326P2S) {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) :
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
  by_cases h9 : F.deg B = 9
  · exact F.centralizer_le_of_deg_nine hF hK hBA hB3 h9
  · exact hF.centralizer_three B hBA hB3 h9

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
