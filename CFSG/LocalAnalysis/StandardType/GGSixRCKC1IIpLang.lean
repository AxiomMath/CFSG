module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpToral
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeComp
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RCKRP CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open scoped commutatorElement

theorem rckExc_lang_component_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ D K : Subgroup X} {e : X}
    (ht : GGExcFive t) (hGG : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hDN : D ≤ Subgroup.normalizer (G₀ : Set X))
    (hDC : D ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (heD : e ∈ D) (hene : e ≠ 1)
    (hKcomp : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)))
    (θ : ↥G₀ →* ModGL (langTag t) GGL) (E : Subgroup (ModGL (langTag t) GGL))
    (hθker : θ.ker = Subgroup.center ↥G₀) (hθrange : θ.range = ⁅ggFixGp t f, ggFixGp t f⁆)
    (hEfix : E ≤ ggFixGp t f) (hEel : IsElemAbelian p E) (hEcard : Nat.card E = Nat.card D)
    (hE1 : ∀ d ∈ D, ∃ a ∈ E, GGLiePartner G₀ θ d a)
    (hE2 : ∀ a ∈ E, ∃ d ∈ D, GGLiePartner G₀ θ d a)
    (hT : IsToralSubgroup (langTag t) GGL E) :
    ∃ (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)) (w : WeylGroup (langTag t)),
      η.ker = Subgroup.center ↥G₀ ∧
      η.range = S.Γ ∧
      S.D.q = 2 ^ f ∧
      S.D.Φ = ggPhi t f ∧
      S.D.n = canonicalRep (coxeterSystem (langTag t)) GGL w ∧
      η = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp θ ∧
      E' = E.map (MulAut.conj S.D.g0⁻¹).toMonoidHom ∧
      E' ≤ S.D.torus ∧
      IsElemAbelian p E' ∧
      Nat.card E' = Nat.card D ∧
      (∀ d ∈ D, ∃ a' ∈ E', GGLiePartner G₀ η d a') ∧
      (∀ a' ∈ E', ∃ d ∈ D, GGLiePartner G₀ η d a') ∧
      rootDiagUnit (langTag t) a ∈ E' ∧
      rootDiagUnit (langTag t) a ≠ 1 ∧
      (∀ j, a j ^ p = 1) ∧
      GGLiePartner G₀ η e (rootDiagUnit (langTag t) a) ∧
      ((K.subgroupOf G₀).map η) =
        rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f := hGG.2.2.2
  have hf : 1 ≤ f := (LieModel.admissible hLie).2.1
  have hnotG2 : langTag t ≠ .G2 := by
    intro hG2
    rcases ht with h | h | h | h | h <;>
      (rw [h] at hG2; exact absurd hG2 (by simp [langTag]))
  have hΦ : IsSteinbergEnd (langTag t) GGL (2 ^ f) (ggPhi t f) :=
    isSteinbergEnd_ggPhi ht f
  haveI : CharP GGL 2 := inferInstance
  have hfinΦ : Finite ↥(ratPoints (ggPhi t f)) :=
    finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
  obtain ⟨w, g, hg, hlang, hEtorus0⟩ :=
    ggLieLangPosition_holds (langTag t) (isExcTag (langTag t)) GGL f hf
      (ggPhi t f) (isSteinbergEndZ_of_isSteinbergEnd hΦ) hfinΦ p hp hp2 E hEfix hEel hT
  let c : ModGL (langTag t) GGL →* ModGL (langTag t) GGL :=
    (MulAut.conj g⁻¹).toMonoidHom
  have hc_inj : Function.Injective c := (MulAut.conj g⁻¹).injective
  let D' : LangDatum (langTag t) GGL := langDatumOfPosition hΦ w g hg hlang
  have htransport := langDatumOfPosition_transport hΦ w g hg hlang hEtorus0
  have hmodel : (ratPoints (ggPhi t f)).map c = D'.model := htransport.1
  have hEtorusD : E.map c ≤ D'.torus := htransport.2
  have hfinD : Finite ↥D'.model := by
    haveI : Finite ↥(ratPoints (ggPhi t f)) := hfinΦ
    have hsurj : Function.Surjective (fun x : ↥(ratPoints (ggPhi t f)) =>
        (⟨c x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
          ↥((ratPoints (ggPhi t f)).map c))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfinMap : Finite ↥((ratPoints (ggPhi t f)).map c) :=
      Finite.of_surjective _ hsurj
    rwa [hmodel] at hfinMap
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved (langTag t) GGL D'
  have hDq : D'.q = 2 ^ f := rfl
  obtain ⟨S, hSD, -⟩ := exists_langSetup_of_datum D' ρ hρ hfinD hf hDq
  have hSΓ : S.Γ = D'.Γ := by
    show S.D.Γ = D'.Γ
    rw [hSD]
  have hSq : S.D.q = 2 ^ f := by
    rw [hSD]
    exact hDq
  let E' : Subgroup (ModGL (langTag t) GGL) := E.map c
  let η : ↥G₀ →* ModGL (langTag t) GGL := c.comp θ
  have hηker : η.ker = Subgroup.center ↥G₀ := by
    change (c.comp θ).ker = _
    rw [MonoidHom.ker_comp_of_injective θ c hc_inj, hθker]
  have hηrange : η.range = S.Γ := by
    have hfix : (ggFixGp t f : Subgroup (ModGL (langTag t) GGL)) =
        ratPoints (ggPhi t f) := rfl
    have h1 : η.range = (⁅ggFixGp t f, ggFixGp t f⁆).map c := by
      change (c.comp θ).range = _
      rw [MonoidHom.range_comp, hθrange]
    rw [h1, Subgroup.map_commutator, hfix, hmodel]
    exact hSΓ.symm
  have hE'torus : E' ≤ S.D.torus := by
    change E.map c ≤ S.D.torus
    rw [hSD]
    exact hEtorusD
  have hEel' : CFSG.Open.IsElemAbelian p E := hEel
  have hE'el : CFSG.Open.IsElemAbelian p E' :=
    CFSG.Open.IsElemAbelian.map hEel' c
  have hE'card : Nat.card E' = Nat.card D := by
    change Nat.card (E.map c) = Nat.card D
    rw [Subgroup.card_map_of_injective hc_inj, hEcard]
  have hE'1 : ∀ d ∈ D, ∃ a' ∈ E', GGLiePartner G₀ η d a' := by
    intro d hd
    obtain ⟨a, haE, hpa⟩ := hE1 d hd
    have hpa' : GGLiePartner G₀ θ d a := hpa
    refine ⟨c a, Subgroup.mem_map.mpr ⟨a, haE, rfl⟩, ?_⟩
    simpa [η] using GGLiePartner.comp hpa' c
  have hE'2 : ∀ a' ∈ E', ∃ d ∈ D, GGLiePartner G₀ η d a' := by
    intro a' ha'
    have ha'E : a' ∈ E.map c := ha'
    obtain ⟨a, haE, rfl⟩ := Subgroup.mem_map.mp ha'E
    obtain ⟨d, hdD, hpd⟩ := hE2 a haE
    have hpd' : GGLiePartner G₀ θ d a := hpd
    exact ⟨d, hdD, by simpa [η] using GGLiePartner.comp hpd' c⟩
  obtain ⟨ae, haeE, hparte⟩ := hE1 e heD
  have haeE' : c ae ∈ E' := Subgroup.mem_map.mpr ⟨ae, haeE, rfl⟩
  have haeT : c ae ∈ D'.torus := hEtorusD haeE'
  obtain ⟨a, haeq⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 haeT).1
  have hrootMem : rootDiagUnit (langTag t) a ∈ E' := by
    rw [← haeq]
    exact haeE'
  have hrootT : rootDiagUnit (langTag t) a ∈ S.D.torus := by
    rw [← haeq]
    exact hE'torus haeE'
  have hrd1 : rootDiagUnit (langTag t) a ≠ 1 := by
    intro hroot1
    have hae1 : ae = 1 := by
      apply hc_inj
      rw [haeq, hroot1, map_one]
    have htriv : ∀ x : ↥G₀, ∀ hx : e * (x : X) * e⁻¹ ∈ G₀,
        θ ⟨e * (x : X) * e⁻¹, hx⟩ = θ x := by
      intro x hx
      have h := hparte x hx
      rw [hae1] at h
      simpa using h
    have heN : e ∈ Subgroup.normalizer (G₀ : Set X) := hDN heD
    have hcent := centralizes_of_trivial_bridge_action θ hGG.2.2.1 hθker heN htriv
    have hmem : e ∈ D ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨heD, hcent⟩
    rw [hDC] at hmem
    exact hene (Subgroup.mem_bot.mp hmem)
  have hap : ∀ j, a j ^ p = 1 := by
    have hpow : a ^ p = 1 := by
      apply rootDiagUnit_injective (τ := langTag t)
      rw [← rootDiagUnit_pow, ← haeq, hE'el.2 (c ae) haeE', rootDiagUnit_one]
    intro j
    simpa using congrFun hpow j
  have hpartη : GGLiePartner G₀ η e (rootDiagUnit (langTag t) a) := by
    intro x hx
    have h := congrArg c (hparte x hx)
    simp only [map_mul, map_inv] at h
    rw [haeq] at h
    simpa [η] using h
  have hKcompη : IsComponentOf ((K.subgroupOf G₀).map η)
      (S.Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit (langTag t) a} : Set (ModGL (langTag t) GGL))) :=
    ggLieBridge_component_of_partner G₀ K S.Γ η hηker hηrange
      (hDN heD) hpartη hKcomp
  have hpL : (p : GGL) ≠ 0 := by
    intro h
    have h2 := (CharP.cast_eq_zero_iff GGL 2 p).1 h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    omega
  have hsmall : langTag t = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q :=
    fun h => absurd h hnotG2
  have hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    langSetup_hTame_of_prime S hp hpL hsmall hrootT hap hrd1
  obtain ⟨i, hi_eq, hi_qs⟩ :=
    exists_eq_rationalComponent_of_isComponentOf S hp hrootT hap hrd1 hTame
      (CFSG.Assembly.isComponentOf_iff_open.mp hKcompη)
  have hSΦ : S.D.Φ = ggPhi t f := by
    rw [hSD]
    rfl
  have hSn : S.D.n = canonicalRep (coxeterSystem (langTag t)) GGL w := by
    rw [hSD]
    rfl
  have hSg : S.D.g0 = g := by
    rw [hSD]
    rfl
  have hηc : η = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp θ := by
    rw [hSg]
  have hE'c : E' = E.map (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
    rw [hSg]
  exact ⟨η, E', S, a, i, w, hηker, hηrange, hSq, hSΦ, hSn, hηc, hE'c, hE'torus, hE'el, hE'card,
    hE'1, hE'2, hrootMem, hrd1, hap, hpartη, hi_eq, hi_qs⟩


theorem rckIIpAt_excFive_lang_component
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (ht : GGExcFive t) (hrow : GGSixRCKJRow .IIp J)
    (hcfg : RCKCompConfig t n f ψ p G₀ A B₁ D J L K e) :
    ∃ (η : ↥G₀ →* ModGL (langTag t) GGL)
      (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5)
      (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      η.ker = Subgroup.center ↥G₀ ∧
      η.range = S.Γ ∧
      S.D.q = 2 ^ f ∧
      E' ≤ S.D.torus ∧
      IsElemAbelian p E' ∧
      Nat.card E' = Nat.card D ∧
      (∀ d ∈ D, ∃ a' ∈ E', GGLiePartner G₀ η d a') ∧
      (∀ a' ∈ E', ∃ d ∈ D, GGLiePartner G₀ η d a') ∧
      rootDiagUnit (langTag t) a ∈ E' ∧
      rootDiagUnit (langTag t) a ≠ 1 ∧
      (∀ j, a j ^ p = 1) ∧
      GGLiePartner G₀ η e (rootDiagUnit (langTag t) a) ∧
      ((K.subgroupOf G₀).map η) =
        rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hcfg' := hcfg
  obtain ⟨hGG, hodd, hp, hp2, hAel, hB1A, hDB1, hDc, hAnorm, hMark, hB1J, hB1inf,
    hp4, hA2, hrankA, hbot, hB1L, hMarkL, hJcomp, hoddJ, hLG0, hx, hnotD, hJcompL,
    hA6, heD, hene, hKcomp, hJK, hoddK⟩ := hcfg'
  have hD_le_A : D ≤ A := hDB1.trans hB1A
  have hDC : D ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc D ⊓ Subgroup.centralizer (G₀ : Set X)
        ≤ A ⊓ Subgroup.centralizer (G₀ : Set X) :=
          le_inf (inf_le_left.trans hD_le_A) inf_le_right
      _ = ⊥ := hbot
  obtain ⟨θ, E, hθker, hθrange, hEfix, hEel, hEcard, hE1, hE2, -, -, hT, -⟩ :=
    rckIIpAt_excFive_toral_bridge ht hrow hcfg
  obtain ⟨η, E', S, a, i, w, hηker, hηrange, hSq, -, -, -, -, hE'torus, hE'el, hE'card, hE'1, hE'2,
      hrootMem, hrd1, hap, hpartη, hi_eq, hi_qs⟩ :=
    rckExc_lang_component_core ht hGG hp hp2 (fun d hd => hAnorm (hD_le_A hd)) hDC heD hene
      hKcomp θ E hθker hθrange hEfix hEel hEcard hE1 hE2 hT
  exact ⟨η, E', S, a, i, hηker, hηrange, hSq, hE'torus, hE'el, hE'card, hE'1, hE'2, hrootMem, hrd1,
    hap, hpartη, hi_eq, hi_qs⟩

end CFSG.StandardType.RCKC1
