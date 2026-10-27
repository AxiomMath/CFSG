module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Dichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneYLemma
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFive
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (K326P2S ZWr z2Of)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem exists_sylow_quotient_pPrimeCore_zwr {H P : Subgroup G} (hPH : P ≤ H)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) (e : ↥P ≃* ZWr 1) :
    ∃ S : Sylow 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H),
      Nonempty (↥(S : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) ≃* ZWr 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOnotdvd : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
  let π : ↥H →* (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker π) := by
    rw [show MonoidHom.ker π = CFSG.pPrimeCore 3 ↥H from QuotientGroup.ker_mk' _]
    exact hOnotdvd
  have hPH_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf H) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) (K := H)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hPG.of_le hPH le_top
  have hSsub_sylow : CFSG.ABGLocalTools.IsSylowOf 3 ((P.subgroupOf H).map π) ⊤ := by
    have h1 := CFSG.isSylowOf_map_of_not_dvd_card_ker π hπsurj (p := 3) Nat.prime_three
      hker hPH_sylow
    simpa [Subgroup.map_top_of_surjective π hπsurj] using h1
  obtain ⟨-, hPp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hSsub_sylow
  have hdvd' : ¬ 3 ∣ ((P.subgroupOf H).map π).index := by simpa using hdvd
  have hcoe : (hPp.toSylow hdvd' : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) =
      (P.subgroupOf H).map π := IsPGroup.toSylow_coe hPp hdvd'
  have hfinj : Function.Injective (π.comp (P.subgroupOf H).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3)
      (N := CFSG.pPrimeCore 3 ↥H) hOnotdvd hPH_sylow.isPGroup
  have hrange : (π.comp (P.subgroupOf H).subtype).range = (P.subgroupOf H).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨hPp.toSylow hdvd', ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hcoe).trans
    (((MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hPH).trans e))

namespace Case811Sylow

variable {c : Ctx82E3 D}

namespace SignedLift

variable {h : Case811Sylow c}

private theorem dvd_card_inf_centralizer_of_mem_centralizer {p : ℕ} {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p)
    {X : Subgroup G} (hXA : X ≤ h.A) :
    p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  have hle : Subgroup.zpowers y ≤ D.M ⊓ Subgroup.centralizer (X : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hy.1, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hy.2 x (hXA hx)
  have hdvd : p ∣ Nat.card (Subgroup.zpowers y) := by rw [Nat.card_zpowers, hyp]
  exact hdvd.trans (Subgroup.card_dvd_of_le hle)

variable (s : SignedLift h)

private theorem one_le_pRank_inf_centralizer_planeG {p : ℕ} (hp_prime : p.Prime) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p) :
    0 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (s.planeG : Set G)) := by
  have hy_pow : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hycent : y ∈ Subgroup.centralizer (s.planeG : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hy.2 x (s.planeG_le_A hx)
  have hzy : Subgroup.zpowers y ≤ D.M ⊓ Subgroup.centralizer (s.planeG : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hy.1, hycent⟩)
  have hzyab : CFSG.Open.IsElemAbelian p (Subgroup.zpowers y) :=
    CFSG.Open.isElemAbelian_zpowers (p := p) hy_pow
  have h1 := CFSG.SectionRank.le_pRank hp_prime.one_lt hzy hzyab (k := 1)
    (by rw [Nat.card_zpowers, hyp]; norm_num)
  omega

private theorem two_le_pRank_inf_normalizer_planeG {p : ℕ} (hp : p ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p) (hyL : y ∉ c.L)
    (hdvd : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (∃ i, u i = 0) →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt u) : Set G) :
        Subgroup G))
    {X : Subgroup G} (hXE : X ≤ s.planeG) (hX3 : Nat.card X = 3) :
    1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  obtain ⟨w, hw0, rfl⟩ := s.exists_pt_of_card_three (hXE.trans s.planeG_le_A) hX3
  have hw2 : w 2 = 0 := (s.pt_mem_planeG_iff w).mp (hXE (Subgroup.mem_zpowers _))
  obtain ⟨R, hRab, hRcard, hRle⟩ :=
    exists_elemAbelian_sq_le_inf_normalizer h hp_prime hy.1 hy.2 hyp hyL
      (Subgroup.zpowers_le.mpr (s.pt_mem_A w)) (hdvd w hw0 ⟨2, hw2⟩)
  have h2 : 2 ≤ CFSG.Open.pRank p
      (D.M ⊓ Subgroup.normalizer (Subgroup.zpowers (s.pt w) : Set G)) :=
    CFSG.SectionRank.le_pRank hp_prime.one_lt hRle hRab (k := 2) hRcard
  omega

private theorem good_of_mem_plane_of_mem_centralizer {p : ℕ} (hp : p ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p) (hyL : y ∉ c.L)
    (hdvd : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (∃ i, u i = 0) →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt u) : Set G) :
        Subgroup G))
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0) (hv2 : v 2 = 0) : GoodPoint D.M (s.pt v) := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  have hcent := s.one_le_pRank_inf_centralizer_planeG hp_prime hy hyp
  have hN : ∀ X : Subgroup G, X ≤ s.planeG → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) :=
    fun X hXE hX3 => s.two_le_pRank_inf_normalizer_planeG hp hy hyp hyL hdvd hXE hX3
  have hΓ := c.conclusion76 hp 3 Nat.prime_three s.planeG
    (s.planeG_le_L.trans c.hyp81.1) s.elemAbelian_planeG
    (by rw [s.card_planeG]; norm_num) hcent hN
  have hXA : Subgroup.zpowers (s.pt v) ≤ h.A := by
    rw [Subgroup.zpowers_le]; exact s.pt_mem_A v
  have hXE : Subgroup.zpowers (s.pt v) ≤ s.planeG := by
    rw [Subgroup.zpowers_le]; exact (s.pt_mem_planeG_iff v).mpr hv2
  have hXab : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (s.pt v)) :=
    h.elemAbelian.mono hXA
  have h1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers (s.pt v)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl _) hXab
      (by rw [Nat.card_zpowers, s.orderOf_pt hv]; norm_num)
  have hcore := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (p := 3) (k := 1) (P := s.planeG) (Q := Subgroup.zpowers (s.pt v)) hXE h1
  have hle : Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G) ≤
      CFSG.Open.rankThreeGamma 1 3 s.planeG := by
    simpa [CFSG.Open.rankThreeGamma] using hcore
  exact hle.trans hΓ

theorem good_of_weight_le_two_of_mem_centralizer {p : ℕ} (hp : p ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p) (hyL : y ∉ c.L)
    (hdvd : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (∃ i, u i = 0) →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt u) : Set G) :
        Subgroup G))
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0) (hz : ∃ i, v i = 0) : GoodPoint D.M (s.pt v) := by
  obtain ⟨σ, ε, hε, hv'⟩ := exists_perm_signs v hv hz
  obtain ⟨g, -, hg⟩ := s.exists_conj σ ε hε
  have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
  rcases hv' with rfl | rfl
  · have := (s.good_of_mem_plane_of_mem_centralizer hp hy hyp hyL hdvd
      (v := ![1, 0, 0]) (by decide) (by decide)).conj hgM
    rwa [hg] at this
  · have := (s.good_of_mem_plane_of_mem_centralizer hp hy hyp hyL hdvd
      (v := ![1, 1, 0]) (by decide) (by decide)).conj hgM
    rwa [hg] at this

private theorem le_M_of_k326Exceptional {H : Subgroup G} (h5 : 5 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy5 : orderOf y = 5)
    (hPH : h.P ≤ H) (hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤)
    (e : ↥h.P ≃* ZWr 1) (hyH : y ∈ H) (hEH : s.planeG ≤ H)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → v 2 = 0 → GoodPoint D.M (s.pt v))
    (hexc : K326Exceptional (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) : H ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, ⟨eS⟩⟩ := exists_sylow_quotient_pPrimeCore_zwr hPH hPG e
  have hq : ¬ 5 ∣ Nat.card (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
    A10Five.not_five_dvd_card (X := ↥H ⧸ CFSG.pPrimeCore 3 ↥H)
      (CFSG.pPrimeCore_quotient_eq_bot (G := ↥H) Nat.prime_three) S eS hexc.1
  have h5dvd : 5 ∣ Nat.card (H ⊓ D.M : Subgroup G) := by
    have hle : Subgroup.zpowers y ≤ H ⊓ D.M :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hyH, hy.1⟩)
    have hdvd : 5 ∣ Nat.card (Subgroup.zpowers y) := by rw [Nat.card_zpowers, hy5]
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)
  have hN : ∀ R : Subgroup G, IsPGroup 5 R → R ≠ ⊥ → R ≤ D.M →
      Subgroup.normalizer (R : Set G) ≤ D.M :=
    fun R hR hR1 hRM =>
      CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le
        (c.isStronglyPEmbedded_of_mem_sigma h5) hR1 hR hRM
  have hsup := A10Five.le_sup_relPPrimeCore_of_five hN h5dvd hq
  have hR : CFSG.Open.relPPrimeCore 3 H ≤ D.M := s.relPPrimeCore_le_of_good hEH hgood
  exact hsup.trans (sup_le inf_le_right hR)

private theorem mem_centralizer_zpowers_of_mem_centralizer {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) {w : Fin 3 → ZMod 3} :
    y ∈ Subgroup.centralizer (((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (show Commute (s.pt w) y from
    Subgroup.mem_centralizer_iff.mp hy.2 (s.pt w) (s.pt_mem_A w)).zpow_left k

private theorem planeG_le_centralizer_zpowers {w : Fin 3 → ZMod 3} :
    s.planeG ≤ Subgroup.centralizer (((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hcomm : x * s.pt w = s.pt w * x :=
    CFSG.Open.IsElemAbelian.comm h.elemAbelian (s.planeG_le_A hx) (s.pt_mem_A w)
  exact ((show Commute x (s.pt w) from hcomm).zpow_right k).symm

private theorem good_of_five_of_centralizer_le {y : G} (h5 : 5 ∈ D.sig)
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy5 : orderOf y = 5)
    {w : Fin 3 → ZMod 3} (hw0 : w ≠ 0)
    (hH : Subgroup.centralizer (((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)) ≤ D.M) :
    GoodPoint D.M (s.pt w) := by
  have hdvdM : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      5 ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    fun X hXA _ => dvd_card_inf_centralizer_of_mem_centralizer (X := X) hy hy5 hXA
  have hC : Subgroup.centralizer ({s.pt w} : Set G) ≤ D.M := by
    have h' := hH
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h'
  exact h.good_of_centralizer_le_of_dvdM h5 hdvdM (s.pt_mem_A w) (s.orderOf_pt hw0) hC

theorem good_center_of_five (hK : K326P2S) (h5 : 5 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy5 : orderOf y = 5)
    (e : ↥h.P ≃* ZWr 1) (hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) → GoodPoint D.M (s.pt v))
    {v₁ : Fin 3 → ZMod 3} (hv₁ : v₁ ≠ 0) (hv₁z : ∃ i, v₁ i = 0) (hv₁Z : s.pt v₁ ∉ z2Of h.P)
    {w : Fin 3 → ZMod 3} (hw0 : w ≠ 0) (hwc : ∀ g ∈ h.P, g * s.pt w = s.pt w * g)
    (hwΩ : ∀ x ∈ h.P, (∀ g ∈ h.P, g * x = x * g) → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers (s.pt w)) : GoodPoint D.M (s.pt w) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPH : h.P ≤ Subgroup.centralizer
      (((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute g (s.pt w) from hwc g hg).zpow_right k).symm
  let H : Subgroup G := Subgroup.centralizer
    (((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G))
  have hPH' : h.P ≤ H := hPH
  rcases s.center_dichotomy hK le_rfl e hPG hNA hgood hv₁ hv₁z hv₁Z hw0 hwc hwΩ with
    hle | ⟨-, hexc⟩
  · exact s.good_of_five_of_centralizer_le h5 hy hy5 hw0 hle
  · have hyH := s.mem_centralizer_zpowers_of_mem_centralizer hy (w := w)
    have hEH := s.planeG_le_centralizer_zpowers (w := w)
    have hHM : H ≤ D.M :=
      s.le_M_of_k326Exceptional h5 hy hy5 hPH' hPG e hyH hEH
        (fun v hv hv2 => hgood v hv ⟨2, hv2⟩) hexc
    exact s.good_of_five_of_centralizer_le h5 hy hy5 hw0 hHM

private theorem normalizer_le_and_dvd_of_five (h5 : 5 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy5 : orderOf y = 5)
    {w : Fin 3 → ZMod 3} (hgw : GoodPoint D.M (s.pt w)) (hw3 : ∀ i, w i ≠ 0)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) → GoodPoint D.M (s.pt v))
    {X : Subgroup G} (hXA : X ≤ h.A) (hXc : Nat.card X = 3) :
    Subgroup.normalizer (X : Set G) ≤ D.M ∧
      5 ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
  have hdvdN : 5 ∣ Nat.card (Subgroup.normalizer (X : Set G)) :=
    (dvd_card_inf_centralizer_of_mem_centralizer (X := X) hy hy5 hXA).trans
      (Subgroup.card_dvd_of_le (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
  refine ⟨?_, hdvdN⟩
  obtain ⟨v, hv0, rfl⟩ := s.exists_pt_of_card_three hXA hXc
  by_cases hz : ∃ i, v i = 0
  · exact hgood v hv0 hz
  · push Not at hz
    let ε : Fin 3 → ZMod 3 := fun i => v i * (w i)⁻¹
    have hε : ∀ i, ε i ≠ 0 := fun i => mul_ne_zero (hz i) (inv_ne_zero (hw3 i))
    obtain ⟨g, -, hg⟩ := s.exists_conj 1 ε hε
    have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
    have hc := hgw.conj hgM
    rw [hg w] at hc
    have hv : (fun i => ε i * w ((1 : Equiv.Perm (Fin 3)) i)) = v := by
      funext i
      simp [ε, hw3 i]
    rwa [hv] at hc

theorem false_of_five (hK : K326P2S) (h5 : 5 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy5 : orderOf y = 5)
    (e : ↥h.P ≃* ZWr 1)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) → GoodPoint D.M (s.pt v)) :
    False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvdM : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      5 ∣ Nat.card (D.M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    fun X hXA _ => dvd_card_inf_centralizer_of_mem_centralizer (X := X) hy hy5 hXA
  have h100 : (![1, 0, 0] : Fin 3 → ZMod 3) ≠ 0 := by
    intro h
    have := congrFun h 0
    simpa using this
  have hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M :=
    h.normalizer_A_le_of_dvdM h5 hdvdM (s.pt_mem_A ![1, 0, 0]) (s.orderOf_pt h100)
      (hgood _ h100 ⟨1, rfl⟩)
  have hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤ :=
    h.isSylowOf_top (h.normalizer_P_le hNA)
  obtain ⟨w, hw3, hwc, hwΩ⟩ := s.exists_center_weight3 le_rfl e
  obtain ⟨v₁, hv₁, hv₁z, hv₁Z⟩ := s.exists_weight_one_not_mem_z2 le_rfl e
  have hw0 : w ≠ 0 := fun h0 => hw3 0 (by rw [h0]; rfl)
  have hgw : GoodPoint D.M (s.pt w) :=
    s.good_center_of_five hK h5 hy hy5 e hPG hNA hgood hv₁ hv₁z hv₁Z hw0 hwc hwΩ
  have hall : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      Subgroup.normalizer (X : Set G) ≤ D.M ∧
        5 ∣ Nat.card (Subgroup.normalizer (X : Set G)) :=
    fun X hXA hXc => s.normalizer_le_and_dvd_of_five h5 hy hy5 hgw hw3 hgood hXA hXc
  have hΓ : CFSG.Open.rankThreeGamma 1 3 h.A ≤ D.M :=
    CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le (p := 5) (q := 3)
      (M := D.M) (A := h.A) (c.isStronglyPEmbedded_of_mem_sigma h5) h.elemAbelian.isPGroup hall
  exact h.not_rankThreeGamma_le hΓ

end SignedLift

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
