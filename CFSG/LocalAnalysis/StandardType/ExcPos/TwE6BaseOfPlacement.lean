module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameDefs
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6Datum
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6OrbitClause
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeComp
public import CFSG.LocalAnalysis.StandardType.GGLieCoreCentOrbit

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus


private theorem lk0xttbase_card_galois {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 f) = 2 ^ f :=
  GaloisField.card 2 f (by omega)

theorem exists_twE6_base {X : Type} [Group X] [Finite X] {n f p : ℕ} (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J A : Subgroup X} {x : X}
    (hB₁A : B₁ ≤ A) (hDB : D ≤ B₁) (hDel : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2)
    (hx : x ∈ D) (hx1 : x ≠ 1) (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hJ : CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL) (Θ : ↥A →* ModGL (langTag .twistedE6) GGL)
    (hθψ : ∀ (k : (ggU .twistedE6 n f).K) (h : ψ k ∈ G₀),
      θ ⟨ψ k, h⟩ = ggIotaK .twistedE6 n f hf k)
    (hθker : θ.ker = Subgroup.center ↥G₀)
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆)
    (hΘR : ∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f)
    (hΘone : ∀ a : ↥A, Θ a = 1 ↔ (a : X) ∈ Subgroup.centralizer (G₀ : Set X))
    (hpart : ∀ a : ↥A, GGLiePartner G₀ θ (a : X) (Θ a))
    (E : Subgroup (ModGL (langTag .twistedE6) GGL)) (hDE : ∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E)
    (hpos : TwE6LawPos p f E) :
    ∃ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ht, w, g, ⟨hg, hlang, hconj⟩, hlaw⟩ := hpos
  obtain ⟨Δ, ρ, hρ, hfin, hΦΔ, hq, hn, hg0, hmodel, hρroots⟩ :=
    exists_twE6_datum hf hg hlang
  have hq' : Δ.q = Nat.card (GaloisField 2 f) := by
    rw [hq, ← lk0xttbase_card_galois hf]
  let Fr : ExcOmega f →+* ExcOmega f := ggFrobT f
  let diag : ModGL (langTag .twistedE6) (ExcOmega f) :=
    diagramAt (langTag .twistedE6) (ExcOmega f) TwistTag.E6 rfl
  have hFr : ∀ c : ExcOmega f, Fr c = c ^ Nat.card (GaloisField 2 f) := by
    intro c
    rw [lk0xttbase_card_galois hf]
    exact ggFrobT_apply f c
  have hdiag : diag = 1 ∨ ∃ h : TwistTag.E6.tag = (Tag.E6),
      diag = diagramAt (Tag.E6) (ExcOmega f) .E6 h :=
    Or.inr ⟨rfl, rfl⟩
  have hΦ : ∀ g : ModGL (langTag .twistedE6) GGL,
      Δ.Φ g = diag * Units.map (entrywiseHom Fr) g * diag⁻¹ := by
    intro y
    rw [hΦΔ]
    change twistHom TwistTag.E6 GGL (ggFrobT f) y =
      diag * Units.map (entrywiseHom (ggFrobT f)) y * diag⁻¹
    simp only [twistHom, MonoidHom.comp_apply, MulAut.conj_apply]
    rfl
  let η : ↥G₀ →* ModGL (langTag .twistedE6) GGL := (MulAut.conj g⁻¹).toMonoidHom.comp θ
  have hconj_one : ∀ z : ModGL (langTag .twistedE6) GGL,
      (MulAut.conj g⁻¹).toMonoidHom z = 1 ↔ z = 1 := by
    intro z
    constructor
    · intro h
      have := congrArg (MulAut.conj g) h
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro h
      simp [h]
  have hηker : η.ker = Subgroup.center ↥G₀ := by
    rw [← hθker]
    ext z
    change (MulAut.conj g⁻¹).toMonoidHom (θ z) = 1 ↔ θ z = 1
    exact hconj_one (θ z)
  have hηrange : η.range = Δ.Γ := by
    change ((MulAut.conj g⁻¹).toMonoidHom.comp θ).range = Δ.Γ
    rw [MonoidHom.range_comp, hθrange, Subgroup.map_commutator, ← hmodel]
    rfl
  let Θ' : ↥B₁ →* ModGL (langTag .twistedE6) GGL :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (Θ.comp (Subgroup.inclusion hB₁A))
  let ΘA' : ↥A →* ModGL (langTag .twistedE6) GGL := (MulAut.conj g⁻¹).toMonoidHom.comp Θ
  have hΘ'mem : ∀ b : ↥B₁, Θ' b ∈ Δ.model := by
    intro b
    rw [hmodel]
    exact Subgroup.mem_map_of_mem ((MulAut.conj g⁻¹).toMonoidHom) (hΘR ⟨b, hB₁A b.2⟩)
  have hΘ'one : ∀ b : ↥B₁, Θ' b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
    intro b
    have h := hΘone ⟨b, hB₁A b.2⟩
    change (MulAut.conj g⁻¹).toMonoidHom (Θ ⟨b, hB₁A b.2⟩) = 1 ↔
      (b : X) ∈ Subgroup.centralizer (G₀ : Set X)
    rw [hconj_one]
    exact h
  have hη'conj : ∀ (b : ↥B₁) (g₁ g' : ↥G₀), (g' : X) = b * g₁ * (b : X)⁻¹ →
      η g' = Θ' b * η g₁ * (Θ' b)⁻¹ := by
    intro b g₁ g' hg'
    have hxG : b * (g₁ : X) * (b : X)⁻¹ ∈ G₀ := by
      rw [← hg']; exact g'.2
    have h1 := (hpart ⟨b, hB₁A b.2⟩) g₁ hxG
    have hsub : (⟨b * (g₁ : X) * (b : X)⁻¹, hxG⟩ : ↥G₀) = g' := by
      apply Subtype.ext
      exact hg'.symm
    rw [hsub] at h1
    change (MulAut.conj g⁻¹).toMonoidHom (θ g') =
      (MulAut.conj g⁻¹).toMonoidHom (Θ ⟨b, hB₁A b.2⟩) *
        (MulAut.conj g⁻¹).toMonoidHom (θ g₁) *
        ((MulAut.conj g⁻¹).toMonoidHom (Θ ⟨b, hB₁A b.2⟩))⁻¹
    rw [h1]
    simp only [map_mul, map_inv]
  have hDN : D ≤ Subgroup.normalizer (G₀ : Set X) := hDB.trans (hB₁A.trans hAN)
  have hΘ'torus : ∀ (b : ↥B₁) (hb : (b : X) ∈ D), Θ' b ∈ Δ.torus := by
    intro b hb
    have hΘE : Θ ⟨(b : X), hB₁A b.2⟩ ∈ E := hDE ⟨(b : X), hB₁A b.2⟩ hb
    have hmap : (MulAut.conj g⁻¹).toMonoidHom (Θ ⟨(b : X), hB₁A b.2⟩) ∈
        E.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hΘE
    have htorus : (MulAut.conj g⁻¹).toMonoidHom (Θ ⟨(b : X), hB₁A b.2⟩) ∈
        CFSG.RankThree.PartOne.KE.twistedTorusOf (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w)
          (ggPhi .twistedE6 f) := hconj hmap
    have hΔ : Δ.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf
        (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w) (ggPhi .twistedE6 f) := by
      rw [LangDatum.torus, hn, hΦΔ]
    rw [hΔ]
    exact htorus
  have coord_witness : ∀ (b : ↥B₁) (hb : (b : X) ∈ D),
      ∃ a : Fin (langTag .twistedE6).rank → (ExcOmega f)ˣ, Θ' b = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) a := by
    intro b hb
    exact exists_rootDiagUnit_eq_of_mem_torusGroup (τ := langTag .twistedE6) (K := ExcOmega f)
      (h := Θ' b) (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 (hΘ'torus b hb)).1
  let coord : X → Fin (langTag .twistedE6).rank → (ExcOmega f)ˣ := fun e =>
    if he : e ∈ D then (coord_witness ⟨e, hDB he⟩ he).choose else 1
  have hcoord_apply : ∀ (e : X) (he : e ∈ D),
      coord e = (coord_witness ⟨e, hDB he⟩ he).choose := by
    intro e he
    dsimp only [coord]
    rw [dif_pos he]
  have hΘ'coord : ∀ b : ↥B₁, (b : X) ∈ D → Θ' b = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord b) := by
    intro b hb
    have hcoord_b : coord b = (coord_witness ⟨(b : X), hDB hb⟩ hb).choose := by
      show coord (b : X) = _
      exact hcoord_apply (b : X) hb
    rw [hcoord_b]
    exact (coord_witness ⟨(b : X), hDB hb⟩ hb).choose_spec
  have hcoord_pow : ∀ e ∈ D, ∀ i, coord e i ^ p = 1 := by
    intro e he i
    have hΘ'e : Θ' ⟨e, hDB he⟩ = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord e) := hΘ'coord ⟨e, hDB he⟩ he
    have hpow : (Θ' ⟨e, hDB he⟩) ^ p = 1 := by
      have hep : (⟨e, hB₁A (hDB he)⟩ : ↥A) ^ p = 1 := by
        apply Subtype.ext
        change e ^ p = 1
        exact hDel.2 e he
      have hc : (ΘA' ⟨e, hB₁A (hDB he)⟩) ^ p = 1 := by
        rw [← map_pow, hep, map_one]
      exact hc
    have hrootpow : (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord e)) ^ p = 1 := by
      rw [← hΘ'e]
      exact hpow
    have htuple : (coord e) ^ p = 1 := by
      apply rootDiagUnit_injective (τ := langTag .twistedE6) (K := ExcOmega f)
      calc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) ((coord e) ^ p)
          = (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) ((coord e) ^ p) := rfl
        _ = ((rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) (coord e)) ^ p :=
            map_pow (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) (coord e) p
        _ = (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord e)) ^ p := rfl
        _ = 1 := hrootpow
        _ = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) 1 :=
            (rootDiagUnit_one (τ := langTag .twistedE6) (K := ExcOmega f)).symm
    exact congrFun htuple i
  have hcoord_torus : ∀ e ∈ D, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord e) ∈ Δ.torus := by
    intro e he
    rw [← hΘ'coord ⟨e, hDB he⟩ he]
    exact hΘ'torus ⟨e, hDB he⟩ he
  have hx_pow : x ^ p = 1 := hDel.2 x hx
  have hzx_card : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx_pow hx1]
  have hzx_lt : Nat.card (Subgroup.zpowers x) < Nat.card D := by
    rw [hzx_card, hDcard]
    nlinarith [hp.two_le]
  have hzx_ne : Subgroup.zpowers x ≠ D := by
    intro h
    rw [h] at hzx_lt
    exact lt_irrefl _ hzx_lt
  obtain ⟨d, hdD, hdnot⟩ := Set.exists_of_ssubset
    (Set.ssubset_iff_subset_ne.2 ⟨Subgroup.zpowers_le.2 hx,
      fun h => hzx_ne (Subgroup.ext fun y =>
        Iff.of_eq (congrArg (fun S : Set X => y ∈ S) h))⟩)
  have hclosure : Subgroup.closure ({x, d} : Set X) = D := by
    have hle : Subgroup.closure ({x, d} : Set X) ≤ D :=
      (Subgroup.closure_le D).2 (by
        intro y hy
        rcases hy with rfl | rfl
        · exact hx
        · exact hdD)
    apply Subgroup.eq_of_le_of_card_ge hle
    have hzx_le : Subgroup.zpowers x ≤ Subgroup.closure ({x, d} : Set X) :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have hcard_ge : p ≤ Nat.card (Subgroup.closure ({x, d} : Set X)) := by
      rw [← hzx_card]
      exact Subgroup.card_le_of_le hzx_le
    have hcard_ne : Nat.card (Subgroup.closure ({x, d} : Set X)) ≠ p := by
      intro hcard
      have heq : Subgroup.zpowers x = Subgroup.closure ({x, d} : Set X) :=
        Subgroup.eq_of_le_of_card_ge hzx_le (by rw [hcard, hzx_card])
      exact hdnot (heq ▸ Subgroup.subset_closure (by simp))
    have hcard_gt : p < Nat.card (Subgroup.closure ({x, d} : Set X)) :=
      lt_of_le_of_ne hcard_ge hcard_ne.symm
    have hdvd : Nat.card (Subgroup.closure ({x, d} : Set X)) ∣ p ^ 2 := by
      have hdvd' : Nat.card ((Subgroup.closure ({x, d} : Set X)).subgroupOf D) ∣ Nat.card D :=
        Subgroup.card_subgroup_dvd_card ((Subgroup.closure ({x, d} : Set X)).subgroupOf D)
      have hcard : Nat.card ((Subgroup.closure ({x, d} : Set X)).subgroupOf D) =
          Nat.card (Subgroup.closure ({x, d} : Set X)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      rw [hcard, hDcard] at hdvd'
      exact hdvd'
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hcard_eq : Nat.card (Subgroup.closure ({x, d} : Set X)) = p ^ 2 := by
      have hp_two : 2 ≤ p := hp.two_le
      interval_cases k
      · simp only [pow_zero] at hk; omega
      · simp only [pow_one] at hk; omega
      · simpa using hk
    omega
  have hd_mem_B₁ : d ∈ B₁ := hDB hdD
  let A' : Subgroup (ModGL (langTag .twistedE6) GGL) := (D.comap A.subtype).map ΘA'
  have hD_A : D.comap A.subtype =
      Subgroup.closure ({⟨x, hB₁A (hDB hx)⟩, ⟨d, hB₁A (hDB hdD)⟩} : Set ↥A) := by
    apply Subgroup.map_injective (f := A.subtype) A.subtype_injective
    have hmapD : (D.comap A.subtype).map A.subtype = D := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact Subgroup.mem_comap.1 ha
      · intro hy
        exact ⟨⟨y, hB₁A (hDB hy)⟩, Subgroup.mem_comap.2 hy, rfl⟩
    rw [hmapD, MonoidHom.map_closure]
    have himg : A.subtype '' ({⟨x, hB₁A (hDB hx)⟩, ⟨d, hB₁A (hDB hdD)⟩} : Set ↥A) =
        ({x, d} : Set X) := by
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · intro hy
        rcases hy with hy | hy
        · rw [hy]
          exact ⟨⟨x, hB₁A (hDB hx)⟩, Or.inl rfl, rfl⟩
        · rw [hy]
          exact ⟨⟨d, hB₁A (hDB hdD)⟩, Or.inr rfl, rfl⟩
    rw [himg, hclosure]
  have hA' : A' = Subgroup.closure
      ({CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord x), CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord d)} :
        Set (ModGL (langTag .twistedE6) GGL)) := by
    rw [show A' = (D.comap A.subtype).map ΘA' from rfl, hD_A, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rcases hb with hb | hb
      · left
        rw [hb]
        exact hΘ'coord ⟨x, hDB hx⟩ hx
      · right
        rw [hb]
        exact hΘ'coord ⟨d, hDB hdD⟩ hdD
    · intro hy
      rcases hy with hy | hy
      · refine ⟨⟨x, hB₁A (hDB hx)⟩, Or.inl rfl, ?_⟩
        rw [hy]
        exact hΘ'coord ⟨x, hDB hx⟩ hx
      · refine ⟨⟨d, hB₁A (hDB hdD)⟩, Or.inr rfl, ?_⟩
        rw [hy]
        exact hΘ'coord ⟨d, hDB hdD⟩ hdD
  have hpartη : ∀ a : ↥A, GGLiePartner G₀ η (a : X) (ΘA' a) := fun a =>
    GGLiePartner.comp (hpart a) ((MulAut.conj g⁻¹).toMonoidHom)
  have hattachJ : CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map η)
      (Δ.Γ ⊓ Subgroup.centralizer
        ({CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord x), CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord d)} :
          Set (ModGL (langTag .twistedE6) GGL))) := by
    have h := ggLieBridge_component G₀ D J Δ.Γ A' η hηker hηrange hDN ?_ ?_ hJ
    · rwa [hA', Subgroup.centralizer_closure] at h
    · intro d' hd'
      refine ⟨ΘA' ⟨d', hB₁A (hDB hd')⟩, ?_, hpartη ⟨d', hB₁A (hDB hd')⟩⟩
      exact Subgroup.mem_map_of_mem ΘA' (Subgroup.mem_comap.2 hd')
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      exact ⟨(a' : X), Subgroup.mem_comap.1 ha', hpartη a'⟩
  have hattachNbr : ∀ e ∈ D, ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)) →
      CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map η)
        (Δ.Γ ⊓ Subgroup.centralizer {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord e)}) := by
    intro e he K hKG hK
    have hK' : CFSG.Assembly.IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) := by
      refine ⟨le_inf hKG hK.1, ?_, hK.2.2⟩
      have h := CFSG.Assembly.IsSubnormal.inf_of_le hK.2.1
        (inf_le_right : G₀ ⊓ Subgroup.centralizer ({e} : Set X) ≤ Subgroup.centralizer ({e} : Set X))
      rwa [inf_eq_left.2 (le_inf hKG hK.1)] at h
    have hparte : GGLiePartner G₀ η e (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord e)) := by
      rw [← hΘ'coord ⟨e, hDB he⟩ he]
      exact hpartη ⟨e, hB₁A (hDB he)⟩
    have heN : e ∈ Subgroup.normalizer (G₀ : Set X) := hDN he
    have h := ggLieBridge_component_of_partner G₀ K Δ.Γ η hηker hηrange heN hparte hK'
    exact h
  obtain ⟨iJ, hmapJ⟩ := ggLieCentOrbit_component_le_orbitSpan
    (D := Δ) (ρ := ρ) hρ hfin hp hp2 (coord x) (coord d)
    (hcoord_torus x hx) (hcoord_torus d hdD)
    (by
      have htuple : (coord x) ^ p = 1 := funext fun i => hcoord_pow x hx i
      calc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord x) ^ p
          = ((rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) (coord x)) ^ p := rfl
        _ = (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) ((coord x) ^ p) :=
            (map_pow (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) (coord x) p).symm
        _ = (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) 1 := by rw [htuple]
        _ = 1 := map_one _)
    (by
      have htuple : (coord d) ^ p = 1 := funext fun i => hcoord_pow d hdD i
      calc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit (langTag .twistedE6) (coord d) ^ p
          = ((rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) (coord d)) ^ p := rfl
        _ = (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) ((coord d) ^ p) :=
            (map_pow (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) (coord d) p).symm
        _ = (rootDiagUnitHom (langTag .twistedE6) (ExcOmega f)) 1 := by rw [htuple]
        _ = 1 := map_one _)
    ((J.subgroupOf G₀).map η) (by
      rw [Subgroup.centralizer_closure]
      exact hattachJ)
  have horbit : componentOrbitLength ρ
        (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ) = 1 ∨
      (componentOrbitLength ρ (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ) = 2 ∧
        (∃ h : TwistTag.E6.tag = Tag.E6, diag = diagramAt (Tag.E6) (ExcOmega f) .E6 h) ∧
        p ∣ Nat.card (GaloisField 2 f) - 1 ∧ Δ.n = 1) := by
    rcases twE6_orbitLength_clause hp hp2 hreg ht hlaw hρroots
        (LieCore.jointChar (coord x) (coord d)) iJ with h | ⟨h2, hpdiv, hw1⟩
    · exact Or.inl h
    · refine Or.inr ⟨h2, ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [lk0xttbase_card_galois hf]
        exact hpdiv
      · rw [hn, hw1, canonicalRep_one]
  refine ⟨{
    one_le_f := hf
    Fr := Fr
    hFr := hFr
    diag := diag
    hdiag := hdiag
    Δ := Δ
    hΦ := hΦ
    hq := hq'
    ρ := ρ
    frob := hρ
    finite := hfin
    η := η
    ker_η := hηker.le
    range_η := hηrange
    Θ := Θ'
    Θ_mem := hΘ'mem
    Θ_eq_one := hΘ'one
    η_conj := hη'conj
    coord := coord
    Θ_eq_coord := hΘ'coord
    coord_pow := hcoord_pow
    coord_torus := hcoord_torus
    d := d
    d_mem := hdD
    closure_eq := hclosure
    iJ := iJ
    map_J_le := hmapJ
    attach_J := hattachJ
    attach_nbr := hattachNbr
    orbit := horbit }, ?_⟩
  · refine ⟨hΦΔ, ?_, ?_⟩
    · intro k hk
      change (MulAut.conj g⁻¹).toMonoidHom (θ ⟨ψ k, hk⟩) =
        Δ.g0⁻¹ * ggIotaK .twistedE6 n f hf k * Δ.g0
      rw [hθψ k hk, hg0]
      simp [MulAut.conj_apply]
    · exact ⟨ht, w, hlaw, hn⟩

end CFSG.StandardType.LieKnownR2.ExcPos
