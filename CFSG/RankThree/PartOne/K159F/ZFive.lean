module

public import CFSG.RankThree.PartOne.S12.Sec159FiveDefs
public import CFSG.RankThree.PartOne.S12.Sec159Node
public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot
public import CFSG.RankThree.PartOne.K159F.Sz
public import CFSG.RankThree.PartOne.K159F.CenterRankFive
public import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
import CFSG.RankThree.PartOne.S12.Sec12FusChoice
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.RankThree.PartOne.K159.CenterRankGriess
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartOne.MultRes.Sec68Closed
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import Certificates.Certificate1016Base
public import Certificates.Certificate3085Base
public import Certificates.Certificate8026Base

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP

@[expose] def KF159ZFiveRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    p = 5 → ∀ X ∈ thetaCompE p E, X ∉ thetaCompZeroE p E →
      p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) → E ≤ X → False

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_elemAbelian {p : ℕ} (hp : p.Prime) {X P₁ : Subgroup G}
    (hP₁ : CFSG.ABGLocalTools.IsSylowOf p (P₁ ⊓ X) X)
    (hθ : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X))
    {R : Subgroup (↥X ⧸ aschbacherSolvableCore p ↥X)} (hRexp : ∀ b ∈ R, b ^ p = 1)
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    ∃ R' : Subgroup G, R' ≤ P₁ ⊓ X ∧ (∀ b ∈ R', b ^ p = 1) ∧
      (∀ a ∈ R', ∀ b ∈ R', a * b = b * a) ∧ Nat.card R' = Nat.card R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p ↥X with hθdef
  set π := QuotientGroup.mk' θ with hπ
  set T : Subgroup ↥X := (P₁ ⊓ X).subgroupOf X with hT
  obtain ⟨Qs, hQs⟩ := hP₁.exists_sylow_eq_subgroupOf
  have hQsT : (Qs : Subgroup ↥X) = T := hQs
  have hTsyl : IsSylowOf p T ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hQsT]; exact Qs.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hQsT]; exact Qs.not_dvd_index
  have hTp : IsPGroup p ↥T := hTsyl.2.1
  have hPbar : IsSylowOf p (T.map π) ⊤ := Sec1511.isSylowOf_map_mk' hTsyl
  have hRp : IsPGroup p ↥R := fun b => ⟨1, Subtype.ext (by simpa using hRexp b b.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hPbar hRp
  set R' : Subgroup (↥X ⧸ θ) := conjSub g R with hR'
  have hR'T : R' ≤ T.map π := hg
  have hR'exp : ∀ b ∈ R', b ^ p = 1 := by
    intro b hb
    rw [hR', mem_conjSub_iff] at hb
    have h1 := hRexp _ hb
    have h2 : (g⁻¹ * b * g) ^ p = g⁻¹ * b ^ p * g := by
      have := conj_pow (a := g⁻¹) (b := b) (i := p)
      rwa [inv_inv] at this
    rw [h2] at h1
    have h3 : b ^ p = g * 1 * g⁻¹ := by
      calc b ^ p = g * (g⁻¹ * b ^ p * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h1]
    simpa using h3
  have hR'ab : ∀ a ∈ R', ∀ b ∈ R', a * b = b * a := by
    intro a ha b hb
    rw [hR', mem_conjSub_iff] at ha hb
    have h1 := hRab _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  set R₀ : Subgroup ↥X := T ⊓ R'.comap π with hR₀
  have hR₀T : R₀ ≤ T := inf_le_left
  have hR₀p : IsPGroup p ↥R₀ := hTp.to_le hR₀T
  have hmap : R₀.map π = R' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro r hr
      obtain ⟨t, ht, rfl⟩ := hR'T hr
      exact ⟨t, ⟨ht, hr⟩, rfl⟩
  have hR₀card : Nat.card ↥R₀ = Nat.card ↥R := by
    have h1 := Sec1511.card_map_mk' (O := θ) hR₀p hθ
    rw [← hπ, hmap] at h1
    rw [← h1, hR']
    exact card_conjSub
  have hR₀exp : ∀ b ∈ R₀, b ^ p = 1 := by
    intro b hb
    have hb1 : π b ∈ R' := hb.2
    have h1 : π (b ^ p) = π 1 := by rw [map_pow, hR'exp _ hb1, map_one]
    exact Sec1511.eq_of_mk'_eq hTp hθ (T.pow_mem (hR₀T hb) p) T.one_mem h1
  have hR₀ab : ∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a := by
    intro a ha b hb
    have ha1 : π a ∈ R' := ha.2
    have hb1 : π b ∈ R' := hb.2
    have h1 : π (a * b) = π (b * a) := by
      rw [map_mul, map_mul]
      exact hR'ab _ ha1 _ hb1
    exact Sec1511.eq_of_mk'_eq hTp hθ (T.mul_mem (hR₀T ha) (hR₀T hb))
      (T.mul_mem (hR₀T hb) (hR₀T ha)) h1
  refine ⟨R₀.map X.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hR₀T hx : x ∈ T)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hR₀exp x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hR₀ab x hx y hy]
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hR₀card]

end Lift

section Node

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAb_of_props {p : ℕ} {F : Subgroup G} (hab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hexp : ∀ b ∈ F, b ^ p = 1) : IsElementaryAbelian p ↥F :=
  CFSG.IsElementaryAbelian.of_forall hab hexp

theorem le_E_of_elemAb {p : ℕ} (hp : p.Prime) {A E : Subgroup G} {c : G} {L : Subgroup G}
    (h155 : Node155) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {PW : Subgroup G}
    (hPW : IsSylowOf p PW (torusNormalizer E)) {R : Subgroup G} (hRPW : R ≤ PW)
    (hRexp : ∀ b ∈ R, b ^ p = 1) (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRcard : p ^ 4 ≤ Nat.card R) : R ≤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  rcases h155 G p A c L E h15 hF hout' PW hPW with hΩ | ⟨-, -, hF3, -⟩
  · intro x hx
    have : x ∈ omegaOne p PW := Subgroup.subset_closure ⟨hRPW hx, hRexp x hx⟩
    rwa [hΩ] at this
  · intro g hg
    have hRp : IsPGroup p ↥R := fun b => ⟨1, Subtype.ext (by simpa using hRexp b b.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hRp
    have hk4 : 4 ≤ k := by
      rw [hk] at hRcard
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hRcard
    have hdvdR : p ^ 3 ∣ Nat.card R := by
      rw [hk]; exact pow_dvd_pow p (by omega)
    have hzp : Nat.card ↥(Subgroup.zpowers g) ∣ p ^ 3 := by
      rw [Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one (hRexp g hg)).trans (dvd_pow_self p (by norm_num))
    obtain ⟨F, hFcard, hgF, hFR⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp hzp hdvdR
      (Subgroup.zpowers_le.2 hg)
    have hFel : IsElementaryAbelian p ↥F :=
      isElemAb_of_props (fun a ha b hb => hRab a (hFR ha) b (hFR hb))
        (fun b hb => hRexp b (hFR hb))
    exact hF3 F (hFR.trans hRPW) hFel hFcard (hgF (Subgroup.mem_zpowers g))

end Node

section Main

variable {G : Type} [Group G] [Finite G]

theorem kf159ZFive_of_inputs (h155 : Node155) (hrank : CenterRankFive) (hRes : KF159ZFiveRes) :
    KF159ZFive := by
  classical
  intro G _ _ p A c L E h15 hF hout X hX hX0 hpZ
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h.setup.2.2.2.2.1.le
  have hXcopy := hX
  obtain ⟨B, hB, hXB⟩ := hX
  obtain ⟨x, hxB, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXB
  have hxE : x ∈ E := hB.1 hxB
  have hEX : E ≤ Subgroup.normalizer (X : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hxE hXx
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.1 hXx).1
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hx1
      (eq_top_iff.2 (htop ▸ hXC))
  have hKX : CFSG.IsKGroup ↥X := hKP X hXtop
  have hQq : CFSG.IsQuasisimple (↥X ⧸ aschbacherSolvableCore p ↥X) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) :=
    N143.not_dvd_card_center_theta_quotient (L := ↥X) hp Nat.prime_two (by omega)
  have hodd : Odd (Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))) :=
    Nat.odd_iff.2 (by omega)
  have hrkX : CFSG.twoLocalOddRank ↥X ≤ 3 := by
    have h1 := Sec9A.evenRank_subgroup_le X
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
      CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h1
    exact h1.trans hrk3
  have hθp : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X) :=
    (solvable_prime_complement_core_characterization hp).2.2.1
  obtain ⟨P, hPsyl, hEP, hPW⟩ := exists_sylow_normalizer hp h155 X h15 hF hout
  obtain ⟨PW, hPWsyl, hPPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hPW hPsyl.2.1
  have hP' : CFSG.ABGLocalTools.IsSylowOf p P (X ⊔ E) := CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hPX : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ X) X :=
    hP'.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hEX)
  have key : ∀ R : Subgroup (↥X ⧸ aschbacherSolvableCore p ↥X), (∀ b ∈ R, b ^ p = 1) →
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → p ^ 4 ≤ Nat.card R →
      ∃ R' : Subgroup G, R' ≤ E ∧ R' ≤ P ⊓ X ∧ Nat.card R' = Nat.card R := by
    intro R hRexp hRab hRcard
    obtain ⟨R', hR'P, hR'exp, hR'ab, hR'card⟩ := exists_lift_elemAbelian hp hPX hθp hRexp hRab
    refine ⟨R', ?_, hR'P, hR'card⟩
    refine le_E_of_elemAb hp h155 h15 hF hout hPWsyl (hR'P.trans inf_le_left |>.trans hPPW) hR'exp hR'ab ?_
    rw [hR'card]
    exact hRcard
  rcases hrank ↥X hrkX hKX (aschbacherSolvableCore p ↥X) hQq p hp (by omega) hpZ hodd with
    ⟨R, hRexp, hRab, hRcard⟩ | ⟨hp5eq, R, hRexp, hRab, hRcard⟩
  ·
    obtain ⟨R', hR'E, -, hR'card⟩ := key R hRexp hRab
      (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hRcard)
    have h1 : Nat.card R' ≤ Nat.card E := Subgroup.card_le_of_le hR'E
    rw [hR'card, hEcard] at h1
    have h2 : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  ·
    obtain ⟨R', hR'E, hR'P, hR'card⟩ := key R hRexp hRab hRcard
    have hEeq : R' = E := by
      refine Subgroup.eq_of_le_of_card_ge hR'E ?_
      rw [hR'card, hEcard]
      exact hRcard
    have hEX' : E ≤ X := by
      rw [← hEeq]
      exact hR'P.trans inf_le_right
    exact hRes G p A c L E h15 hF hout hp5eq X hXcopy hX0 hpZ hEX'

end Main

end CFSG.RankThree.PartOne.K159F
