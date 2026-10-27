module

public import CFSG.LocalAnalysis.StandardType.ExcPos.LangFrameDefs
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aBridge
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aToral
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.LieType.Chevalley.TorusTupleLift
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.Blueprint.Chevalley
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem nonempty_excLangFrame_of_toral_of
    {t : StatedLieTag} (hexc : GGExcFive t) {X : Type} [Group X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D : Subgroup X} {x d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hDel : IsElemAbelian p D) (hDB : D ≤ B₁) (hf : 1 ≤ f)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {lam : ↥B₁ →* ModGL (langTag t) GGL}
    (hθker : θ.ker = Subgroup.center ↥G₀)
    (hθrange : θ.range = ⁅ggFixGp t f, ggFixGp t f⁆)
    (hθι : ∀ (k : (ggU t n f).K) (hk : ψ k ∈ G₀), θ ⟨ψ k, hk⟩ = ggIotaK t n f hf k)
    (hlam : ∀ b, lam b ∈ ggFixGp t f)
    (hpart : ∀ b : ↥B₁, GGLiePartner G₀ θ b (lam b))
    (hlam1 : ∀ b : ↥B₁, lam b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X))
    (hT : IsToralSubgroup (langTag t) GGL ((D.subgroupOf B₁).map lam))
    (hdD : d ∈ D) (hclosure : Subgroup.closure ({x, d} : Set X) = D) :
    Nonempty (ExcLangFrame t n f p ψ G₀ B₁ D x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let E : Subgroup (ModGL (langTag t) GGL) := (D.subgroupOf B₁).map lam
  have hEfix : E ≤ ggFixGp t f := by
    rintro y hy
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact hlam b
  have hDsub : IsElemAbelian p (D.subgroupOf B₁) := hDel.comap B₁.subtype_injective
  have hEel : IsElemAbelian p E := hDsub.map lam
  have hΦ := CFSG.StandardType.LieCore.isSteinbergEnd_ggPhi hexc f
  have : CharP GGL 2 := inferInstance
  have hfinΦ : Finite ↥(CFSG.StandardType.LieCore.ratPoints (ggPhi t f)) :=
    CFSG.StandardType.LieCore.finite_ratPoints (q := 2 ^ f)
      (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2))
      (CFSG.StandardType.LieCore.isSteinbergEndZ_of_isSteinbergEnd hΦ)
  obtain ⟨w, g, hg, hlang, hEtorus0⟩ :=
    CFSG.StandardType.LieCore.ggLieLangPosition_holds (langTag t)
      (CFSG.StandardType.LieCore.isExcTag (langTag t)) GGL f hf (ggPhi t f)
      (CFSG.StandardType.LieCore.isSteinbergEndZ_of_isSteinbergEnd hΦ) hfinΦ p hp hp2 E
      hEfix hEel hT
  let c : ModGL (langTag t) GGL →* ModGL (langTag t) GGL :=
    (MulAut.conj g⁻¹).toMonoidHom
  have hc_inj : Function.Injective c := (MulAut.conj g⁻¹).injective
  let Δ : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum (langTag t) GGL :=
    CFSG.StandardType.LieCore.langDatumOfPosition hΦ w g hg hlang
  have htransport :=
    CFSG.StandardType.LieCore.langDatumOfPosition_transport hΦ w g hg hlang hEtorus0
  have hmodel : (CFSG.StandardType.LieCore.ratPoints (ggPhi t f)).map c = Δ.model :=
    htransport.1
  have hEtorusD : E.map c ≤ Δ.torus := htransport.2
  have hfinD : Finite ↥Δ.model := by
    have : Finite ↥(CFSG.StandardType.LieCore.ratPoints (ggPhi t f)) := hfinΦ
    have hsurj : Function.Surjective
        (fun x : ↥(CFSG.StandardType.LieCore.ratPoints (ggPhi t f)) =>
          (⟨c x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ :
            ↥((CFSG.StandardType.LieCore.ratPoints (ggPhi t f)).map c))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfinMap : Finite ↥((CFSG.StandardType.LieCore.ratPoints (ggPhi t f)).map c) :=
      Finite.of_surjective _ hsurj
    rwa [hmodel] at hfinMap
  obtain ⟨ρ, hρ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.frobeniusOnRoots_proved (langTag t) GGL Δ
  let η : ↥G₀ →* ModGL (langTag t) GGL := c.comp θ
  let Θ : ↥B₁ →* ModGL (langTag t) GGL := c.comp lam
  have hΔg : Δ.g0 = g := rfl
  have hηeq : ∀ y, η y = Δ.g0⁻¹ * θ y * Δ.g0 := by
    intro y
    rw [hΔg]
    change MulAut.conj g⁻¹ (θ y) = g⁻¹ * θ y * g
    rw [MulAut.conj_apply, inv_inv]
  have hηrange : η.range = Δ.Γ := by
    have hfix : (ggFixGp t f : Subgroup (ModGL (langTag t) GGL)) =
        CFSG.StandardType.LieCore.ratPoints (ggPhi t f) := rfl
    have h1 : η.range = (⁅ggFixGp t f, ggFixGp t f⁆).map c := by
      change (c.comp θ).range = _
      rw [MonoidHom.range_comp, hθrange]
    rw [h1, Subgroup.map_commutator, hfix, hmodel]
    rfl
  have hΘmem : ∀ b : ↥B₁, Θ b ∈ Δ.model := by
    intro b
    have hb : lam b ∈ CFSG.StandardType.LieCore.ratPoints (ggPhi t f) := hlam b
    have hmem : c (lam b) ∈
        (CFSG.StandardType.LieCore.ratPoints (ggPhi t f)).map c :=
      Subgroup.mem_map.mpr ⟨lam b, hb, rfl⟩
    rw [hmodel] at hmem
    exact hmem
  have hΘeq1 : ∀ b : ↥B₁, Θ b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
    intro b
    have h : c (lam b) = 1 ↔ lam b = 1 := by
      constructor
      · intro hb
        apply (MulAut.conj g⁻¹).injective
        simpa [c] using hb
      · intro hb
        simp [c, hb]
    change c (lam b) = 1 ↔ _
    rw [h, hlam1 b]
  have hηconj : ∀ (b : ↥B₁) (g g' : ↥G₀), (g' : X) = b * g * (b : X)⁻¹ →
      η g' = Θ b * η g * (Θ b)⁻¹ := by
    intro b g g' hgg
    have hmem : b * (g : X) * (b : X)⁻¹ ∈ G₀ := by
      rw [← hgg]
      exact g'.2
    have hθ := hpart b g hmem
    have hsub : (⟨b * (g : X) * (b : X)⁻¹, hmem⟩ : ↥G₀) = g' := Subtype.ext hgg.symm
    have hθ' : θ g' = lam b * θ g * (lam b)⁻¹ := by
      rw [← hsub]
      exact hθ
    have hc := congrArg c hθ'
    simp only [map_mul, map_inv] at hc
    simpa [η, Θ] using hc
  have hcoord : ∀ (e : X) (he : e ∈ D), ∃ a : Fin (langTag t).rank → GGLˣ,
      Θ ⟨e, hDB he⟩ = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        (langTag t) a := by
    intro e he
    have hmemE : lam ⟨e, hDB he⟩ ∈ E := by
      refine Subgroup.mem_map.mpr ⟨⟨e, hDB he⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr he
    have hmemMap : c (lam ⟨e, hDB he⟩) ∈ E.map c :=
      Subgroup.mem_map.mpr ⟨lam ⟨e, hDB he⟩, hmemE, rfl⟩
    have hmemT : c (lam ⟨e, hDB he⟩) ∈ Δ.torus := hEtorusD hmemMap
    obtain ⟨a, ha⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hmemT).1
    exact ⟨a, ha⟩
  let coord : X → Fin (langTag t).rank → GGLˣ :=
    fun e => if he : e ∈ D then Classical.choose (hcoord e he) else 1
  have hΘcoord : ∀ b : ↥B₁, (b : X) ∈ D →
      Θ b = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        (langTag t) (coord b) := by
    intro b hb
    have hspec := Classical.choose_spec (hcoord (b : X) hb)
    have hcb : coord (b : X) = Classical.choose (hcoord (b : X) hb) := by
      show (if he : (b : X) ∈ D then Classical.choose (hcoord (b : X) he) else 1) = _
      rw [dif_pos hb]
    rw [hcb]
    simpa using hspec
  have hcoordpow : ∀ e ∈ D, ∀ i, coord e i ^ p = 1 := by
    intro e he i
    have hcoordp : coord e ^ p = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := langTag t)
      rw [← CFSG.LieType.Chevalley.rootDiagUnit_pow,
        CFSG.LieType.Chevalley.rootDiagUnit_one]
      rw [← hΘcoord ⟨e, hDB he⟩ he]
      have hep : (⟨e, hDB he⟩ : ↥B₁) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hDel.2 e he
      rw [← map_pow, hep, map_one]
    simpa using congrFun hcoordp i
  have hcoordt : ∀ e ∈ D,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        (langTag t) (coord e) ∈ Δ.torus := by
    intro e he
    rw [← hΘcoord ⟨e, hDB he⟩ he]
    have hmemE : lam ⟨e, hDB he⟩ ∈ E := by
      refine Subgroup.mem_map.mpr ⟨⟨e, hDB he⟩, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr he
    have hmemMap : c (lam ⟨e, hDB he⟩) ∈ E.map c :=
      Subgroup.mem_map.mpr ⟨lam ⟨e, hDB he⟩, hmemE, rfl⟩
    exact hEtorusD hmemMap
  exact ⟨hf, θ, hθker, hθrange, hθι, Δ, rfl, rfl, ρ, hρ, hfinD, η, hηeq, hηrange, Θ,
    hΘmem, hΘeq1, hηconj, coord, hΘcoord, hcoordpow, hcoordt, d, hdD, hclosure⟩

theorem nonempty_excLangFrame_of_toral
    {t : StatedLieTag} (hexc : GGExcFive t) {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) (hf : 1 ≤ f)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {lam : ↥B₁ →* ModGL (langTag t) GGL}
    (hθker : θ.ker = Subgroup.center ↥G₀)
    (hθrange : θ.range = ⁅ggFixGp t f, ggFixGp t f⁆)
    (hθι : ∀ (k : (ggU t n f).K) (hk : ψ k ∈ G₀), θ ⟨ψ k, hk⟩ = ggIotaK t n f hf k)
    (hlam : ∀ b, lam b ∈ ggFixGp t f)
    (hpart : ∀ b : ↥B₁, GGLiePartner G₀ θ b (lam b))
    (hlam1 : ∀ b : ↥B₁, lam b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X))
    (hT : IsToralSubgroup (langTag t) GGL ((D.subgroupOf B₁).map lam)) :
    Nonempty (ExcLangFrame t n f p ψ G₀ B₁ D x) := by
  classical
  have hcfg := h
  obtain ⟨-, -, -, -, hp, hp2, -, -, hB1el, -, hDB, hDcard, -, -, -, -, hxD, hx1, -, -, -,
    -, -, -, -, -, -, -, -, -, -⟩ := hcfg
  have : Fact p.Prime := ⟨hp⟩
  have hDel : IsElemAbelian p D := hB1el.mono hDB
  have hxord : orderOf x = p := orderOf_eq_prime (hDel.2 x hxD) hx1
  have hLcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hLle : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
  have hd_exists : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
    by_contra hcontra
    push Not at hcontra
    have hDle : D ≤ Subgroup.zpowers x := fun d hd => hcontra d hd
    have hcardle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) :=
      Subgroup.card_le_of_le hDle
    rw [hDcard, hLcard] at hcardle
    have hlt : p < p ^ 2 := by
      rw [pow_two]
      simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
    exact (not_lt_of_ge hcardle) hlt
  obtain ⟨d, hdD, hdL⟩ := hd_exists
  have hd1 : d ≠ 1 := by
    intro hd
    rw [hd] at hdL
    exact hdL (Subgroup.one_mem (Subgroup.zpowers x))
  have hdord : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1
  have hMcard : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, hdord]
  have hMle : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
  let S : Subgroup X := Subgroup.zpowers x ⊔ Subgroup.zpowers d
  have hsup_le : S ≤ D := by
    change Subgroup.zpowers x ⊔ Subgroup.zpowers d ≤ D
    exact sup_le hLle hMle
  have hlt : Subgroup.zpowers x < S := by
    change Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers d
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    have hdM : d ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers d :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    rw [← h] at hdM
    exact hdL hdM
  have hcardlt : Nat.card (Subgroup.zpowers x) < Nat.card S :=
    Subgroup.card_lt_of_lt hlt
  rw [hLcard] at hcardlt
  have hdvd : Nat.card S ∣ p ^ 2 := by
    have h := Subgroup.card_dvd_of_le hsup_le
    rwa [hDcard] at h
  have hsupcard : Nat.card S = p ^ 2 := by
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk, hcard⟩
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hcard
      rw [hcard] at hcardlt
      exact (not_lt_of_ge (le_of_lt hp.one_lt)) hcardlt
    have hk1 : k ≠ 1 := by
      intro h1
      rw [h1, pow_one] at hcard
      rw [hcard] at hcardlt
      exact (lt_irrefl p) hcardlt
    have hk2 : k = 2 := by omega
    rw [hk2] at hcard
    exact hcard
  have hsup_eq : S = D :=
    Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hDcard, hsupcard])
  have hclosure : Subgroup.closure ({x, d} : Set X) = D := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
    exact hsup_eq
  exact nonempty_excLangFrame_of_toral_of hexc hp hp2 hDel hDB hf hθker hθrange hθι hlam hpart
    hlam1 hT hdD hclosure

theorem nonempty_excLangFrame
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) :
    Nonempty (ExcLangFrame t n f p ψ G₀ B₁ D x) := by
  have hexc : GGExcFive t := by rcases ht with rfl | rfl | rfl <;> simp [GGExcFive]
  obtain ⟨hf, θ, lam, hθker, hθrange, hθι, hcent, hlam, hpart, hlam1⟩ :=
    excU1a_bridge hexc h
  have hT := excU1a_toral ht h hf hθker hθrange hθι hcent hlam hpart hlam1
  exact nonempty_excLangFrame_of_toral (θ := θ) (lam := lam) hexc h hf hθker hθrange hθι
    hlam hpart hlam1 hT

end CFSG.StandardType.LieKnownR2.ExcPos
