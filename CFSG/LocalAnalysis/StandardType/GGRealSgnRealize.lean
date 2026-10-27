module

public import CFSG.LocalAnalysis.StandardType.GGRealSgnDefs
public import CFSG.LocalAnalysis.StandardType.GGRealKGTorusComponents
public import CFSG.LocalAnalysis.StandardType.GGRealQFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

theorem ggReflRealizedAt_of_torusSgnComponents {G : Type} [Group G] [Finite G] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNT : GGNoTransvection p Bs) (hX : commutator X = ⊤) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : X ⧸ center X ≃* R) (hBsN : Bs ≤ normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range)
    (hT : GGTorusSgnComponents p r R I) {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer X Bs)
    (ht : GGIsReflection p t) (hcomm : ∀ w ∈ ggAutomizer X Bs, Commute (w * t * w⁻¹) t) :
    ∃ Jt : Subgroup G, t ∈ ggInduced Jt Bs ∧
      GLAPComponent p (X ⊓ centralizer (ggFixG Bs t : Set G)) Jt := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have htI : t ∈ ggInduced X Bs := by
    rw [ggAutomizer_eq] at htA
    exact htA
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hX θ hBsN hBsI hr h3
  obtain ⟨n₀, hn₀, hov₀, hrefl₀, hmem₀⟩ := ggReflection_overGamma_of_induced hp hp2 hBs hBsN htI ht
  have hspecial : ∀ (u : X)
      (hu : MulAut.conj u ∈
        Subgroup.normalizer ((ggGamma X hBsN).range : Set (MulAut ↥X))),
      GGTorusWeylElt p (ggGamma X hBsN).range u →
      Commute (ggConjAut (ggGamma X hBsN).range hu * ggConjAut (ggGamma X hBsN).range hn₀ *
          (ggConjAut (ggGamma X hBsN).range hu)⁻¹)
        (ggConjAut (ggGamma X hBsN).range hn₀) := by
    intro u hu hWu
    have hug : (u : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      mem_normalizer_of_ggTorusWeylElt hBsN hSC hWu
    have hw : ggConjAut Bs hug ∈ ggAutomizer X Bs := ggConjAut_mem_ggAutomizer u.2 hug
    have hovw : GGOverGamma hBsN (ggConjAut Bs hug) (ggConjAut (ggGamma X hBsN).range hu) := by
      have h := ggOverGamma_conjAut (hN := hBsN) (g := (u : G)) u.2 hug
      have heq : ggConjAut (ggGamma X hBsN).range
            (conj_mem_normalizer_range_ggGamma hBsN u.2 hug)
          = ggConjAut (ggGamma X hBsN).range hu := by
        apply MulEquiv.ext
        intro b
        apply Subtype.ext
        rfl
      rwa [heq] at h
    have hovt : GGOverGamma hBsN t (ggConjAut (ggGamma X hBsN).range hn₀) := hov₀
    have hov1 : GGOverGamma hBsN (ggConjAut Bs hug * t * (ggConjAut Bs hug)⁻¹)
        (ggConjAut (ggGamma X hBsN).range hu * ggConjAut (ggGamma X hBsN).range hn₀ *
          (ggConjAut (ggGamma X hBsN).range hu)⁻¹) :=
      (hovw.mul hovt).mul hovw.inv
    have hcw : (ggConjAut Bs hug * t * (ggConjAut Bs hug)⁻¹) * t =
        t * (ggConjAut Bs hug * t * (ggConjAut Bs hug)⁻¹) := hcomm (ggConjAut Bs hug) hw
    have h1 : GGOverGamma hBsN (ggConjAut Bs hug * t * (ggConjAut Bs hug)⁻¹ * t)
        (ggConjAut (ggGamma X hBsN).range hu * ggConjAut (ggGamma X hBsN).range hn₀ *
          (ggConjAut (ggGamma X hBsN).range hu)⁻¹ * ggConjAut (ggGamma X hBsN).range hn₀) :=
      hov1.mul hovt
    have h2 : GGOverGamma hBsN (t * (ggConjAut Bs hug * t * (ggConjAut Bs hug)⁻¹))
        (ggConjAut (ggGamma X hBsN).range hn₀ *
          (ggConjAut (ggGamma X hBsN).range hu * ggConjAut (ggGamma X hBsN).range hn₀ *
            (ggConjAut (ggGamma X hBsN).range hu)⁻¹)) :=
      hovt.mul hov1
    rw [hcw] at h1
    exact GGOverGamma.unique h1 h2
  obtain ⟨n, hn, J', hW, hnφ, hnJ', hcomp, hpJ'⟩ :=
    hT X (ggQuotHom θ) (ggGamma X hBsN).range hTB
      (ggConjAut (ggGamma X hBsN).range hn₀) hmem₀ hrefl₀ hspecial
  obtain ⟨m, hg, htr, hover⟩ := exists_pow_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hBsN
    hW hn (hnφ ▸ hrefl₀)
  have hgX : (n : G) ^ m ∈ X := X.pow_mem n.2 m
  have hrt : t = ggConjAut Bs hg := by
    refine ggReflection_eq_of_agree_mod hp2 hBs hNT (Z := centralizer (X : Set G))
      ht htr ?_ ?_ ?_ ?_ ?_
    · obtain ⟨g', -, hg'N, hg'⟩ := htI
      exact ⟨g', trivial, hg'N, hg'⟩
    · exact ⟨(n : G) ^ m, trivial, hg, fun b => rfl⟩
    · obtain ⟨g', hg'X, -, hg'⟩ := htI
      intro b hb
      apply Subtype.ext
      rw [hg' b, mem_centralizer_iff.mp hb g' hg'X]
      group
    · intro b hb
      apply Subtype.ext
      rw [ggConjAut_apply Bs hg, mem_centralizer_iff.mp hb ((n : G) ^ m) hgX]
      group
    · intro b
      have h1 : (ggGamma X hBsN).rangeRestrict ((t b)⁻¹ * (ggConjAut Bs hg) b) = 1 := by
        rw [map_mul, map_inv, hov₀ b, hover b, ← hnφ]
        exact inv_mul_cancel _
      have h2 := (ggGamma_eq_one_iff X hBsN ((t b)⁻¹ * (ggConjAut Bs hg) b)).mp (by
        have := congrArg Subtype.val h1
        simpa using this)
      simpa using h2
  subst hrt
  have hmap := map_ggHypCent_eq hp hp2 hBs hBsN hn hgX hg htr.1 hover
  have hJc : CFSG.Assembly.IsComponentOf (J'.map X.subtype)
      (X ⊓ centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G)) :=
    hmap ▸ isComponentOf_map_of_injective X.subtype X.subtype_injective hcomp
  have hpJ : p ∣ Nat.card (J'.map X.subtype) := by
    rwa [Subgroup.card_map_of_injective X.subtype_injective]
  refine ⟨J'.map X.subtype, ⟨(n : G) ^ m, ⟨n ^ m, J'.pow_mem hnJ' m, by simp⟩, hg, fun b => rfl⟩,
    ?_⟩
  exact (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).mpr
    ⟨hJc.1, isPComponent_subgroupOf_of_isComponentOf_of_dvd hJc hpJ⟩

theorem ggRealized_of_reflRealizedAt {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X : Subgroup G} {z : G} (hzBs : z ∈ Bs)
    (hX : GLAPComponent p (centralizer ({z} : Set G)) X) {t : MulAut ↥Bs}
    (htA : t ∈ ggAutomizer X Bs)
    (hJ : ∃ Jt : Subgroup G, t ∈ ggInduced Jt Bs ∧
      GLAPComponent p (X ⊓ centralizer (ggFixG Bs t : Set G)) Jt) :
    GGRealized p Bs t := by
  obtain ⟨Jt, hind, hJ⟩ := hJ
  have hXz := ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    hp).mp hX).1
  have hzE := mem_ggFixG_of_mem_ggAutomizer hzBs hXz htA
  obtain ⟨hle, hpc⟩ := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    hp).mp (CFSG.LocalAnalysis.GLTheoremA.S9.glaPComponent_centralizer hp hX hzE hJ)
  exact ⟨Jt, hind, hle, hpc⟩

end CFSG.StandardType

end
