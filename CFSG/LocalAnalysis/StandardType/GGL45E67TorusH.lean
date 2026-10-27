module

public import CFSG.LocalAnalysis.StandardType.GGL45NtGlue
public import CFSG.LocalAnalysis.StandardType.GGL45NtLift
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcThreePart
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.Quasithin.H13.NQSetupFieldPowerG2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.LocalAnalysis.StandardType.GGL45NtClBlocks
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FourHI
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.KGD.D4QFrame

public section

namespace CFSG.StandardType

open CFSG.Open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.LieCore CFSG.Quasithin.H13.NQSetup
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.C14Exc CFSG.HardMathSupport.C14Cl
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8Lift

private theorem ggL45E67TorusH_conj_injective {K R : Type*} [Group K] [Group R]
    (hK : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* R) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  apply ggL45Nt_eq_one_of_forall_commute hK θ
  intro s
  have h1 := congrArg (fun f : MulAut R => f s) hr
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc s * r = (r * s * r⁻¹) * r := by rw [h1]
    _ = r * s := by group

private theorem ggL45E67TorusH_inCIp_iff {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (E : Subgroup (MulAut K))
    (u : MulAut R) :
    GGL45NtCIp p I (E.map (ggInducedAut θ)) u ↔ GGL45InCIp p I θ E u := by
  constructor
  · rintro ⟨hI, hcomm, hp⟩
    refine ⟨hI, ?_, hp⟩
    intro e he
    exact hcomm (ggInducedAut θ e) (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)
  · rintro ⟨hI, hcomm, hp⟩
    refine ⟨hI, ?_, hp⟩
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    exact hcomm e he

theorem ggL45TorusH123_of_hOne_of_inner {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hK : commutator K = ⊤) {ψ : MulAut K} {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hEψ : ∀ e ∈ E, e * ψ = ψ * e) (hInn : ∀ r : R, MulAut.conj r ∈ I)
    (hOut : ∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ}
    (hk : ¬ p ∣ k) (hc : c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s])
    (hcomm : ∀ φ ∈ I, ∀ φ' ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
        (∀ x ∈ E, φ' * ggInducedAut θ x = ggInducedAut θ x * φ') → φ * φ' = φ' * φ)
    (hH1 : GGL45HOne p I θ E (ggInducedAut θ ψ) s c)
    (hpair : ∃ a₁ a₂ : MulAut R, GGL45InCIp p I θ E a₁ ∧ GGL45InCIp p I θ E a₂ ∧
        ∀ m n : ℕ, (a₁ ^ p ^ (s - 1)) ^ m * (a₂ ^ p ^ (s - 1)) ^ n = 1 → p ∣ m ∧ p ∣ n) :
    GGL45TorusH123 p I θ ψ E := by
  have hconj_inj := ggL45E67TorusH_conj_injective hK θ
  have hC1 : ∀ u v : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      GGL45NtCIp p I (E.map (ggInducedAut θ)) v → u * v = v * u := by
    intro u v hu hv
    exact hH1.1 u v ((ggL45E67TorusH_inCIp_iff θ I E u).mp hu)
      ((ggL45E67TorusH_inCIp_iff θ I E v).mp hv)
  have hC2 : ∀ u : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u →
      u ^ p ^ s = 1 ∧ ggInducedAut θ ψ * u * (ggInducedAut θ ψ)⁻¹ = u ^ c := by
    intro u hu
    exact hH1.2 u ((ggL45E67TorusH_inCIp_iff θ I E u).mp hu)
  have hC3 : ∀ u : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) u → ∀ w ∈ I,
      (∀ e ∈ E.map (ggInducedAut θ), w * e = e * w) → w * u = u * w := by
    intro u hu w hw hwE
    obtain ⟨huI, huE, _⟩ := (ggL45E67TorusH_inCIp_iff θ I E u).mp hu
    refine hcomm w hw u huI ?_ huE
    intro x hx
    exact hwE (ggInducedAut θ x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hC4 : ∃ a₁ a₂ : MulAut R, GGL45NtCIp p I (E.map (ggInducedAut θ)) a₁ ∧
      GGL45NtCIp p I (E.map (ggInducedAut θ)) a₂ ∧
      ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j := by
    obtain ⟨a₁, a₂, ha₁, ha₂, hind⟩ := hpair
    exact ⟨a₁, a₂, (ggL45E67TorusH_inCIp_iff θ I E a₁).mpr ha₁,
      (ggL45E67TorusH_inCIp_iff θ I E a₂).mpr ha₂, hind⟩
  refine ⟨s, hs, c, k, hk, hc, hH1, ?_, ?_⟩
  · exact ggL45NtGlue_H2 hp θ I ψ E hInn hZ hconj_inj hEψ s c hC1 hC2 hC3
  · exact ggL45NtGlue_H3 hp θ I E hOut hZ hconj_inj hE s hs c hC4


private theorem ggL45E67_frame_diagram_facts
    {L : Type} [Field L] {Fr : L →+* L} {t : TwistTag} {τ : Tag} (h : t.tag = τ)
    (ht6 : t = .E6) :
    Units.map (entrywiseHom Fr) (diagramAt τ L t h) = diagramAt τ L t h ∧
    diagramAt τ L t h ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
    ∀ m ∈ adjointGroup τ L,
      m * diagramAt τ L t h * (m * diagramAt τ L t h) ∈ adjointGroup τ L := by
  subst ht6
  cases h
  simp only [diagramAt]
  refine ⟨?_, ?_, ?_⟩
  · exact units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (K := L) Fr
  · exact diagramMap_mem_normalizer (k := L) TwistTag.E6
  · intro m hm
    have hconj := diagramMap_conj_mem_adjointGroup (t := TwistTag.E6) (K := L) hm
    have hinv : (diagramMap TwistTag.E6 L)⁻¹ = diagramMap TwistTag.E6 L :=
      diagramMap_E6_inv
    have hPP : diagramMap TwistTag.E6 L * diagramMap TwistTag.E6 L = 1 := by
      nth_rewrite 2 [← hinv]; exact mul_inv_cancel _
    have heq : m * diagramMap TwistTag.E6 L * (m * diagramMap TwistTag.E6 L) =
        m * (diagramMap TwistTag.E6 L * m * (diagramMap TwistTag.E6 L)⁻¹) *
          (diagramMap TwistTag.E6 L * diagramMap TwistTag.E6 L) := by
      group
    rw [heq, hPP, mul_one]
    exact mul_mem hm hconj

private theorem ggL45E67_frame_basic_frw
    {τ : Tag} {L : Type} [Field L] {Fr : L →+* L} {w : WeylGroup τ} :
    Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) L w) =
        canonicalRep (coxeterSystem τ) L w ∧
      canonicalRep (coxeterSystem τ) L w ∈
        Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      canonicalRep (coxeterSystem τ) L w ∈ adjointGroup τ L :=
  ⟨units_map_entrywiseHom_canonicalRep Fr w, canonicalRep_mem_normalizer w,
    canonicalRep_mem_adjointGroup (coxeterSystem τ) L w⟩

private theorem ggL45E67_frame_steinberg
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ} (hF₀ : IsSteinbergEnd τ L (2 ^ e) F₀)
    (hτ : τ = .E6 ∨ τ = .E7) :
    ∃ (Fr : L →+* L) (P : ModGL τ L),
      (∀ c, Fr c = c ^ (2 ^ e)) ∧
      (∀ g, F₀ g = P * Units.map (entrywiseHom Fr) g * P⁻¹) ∧
      Units.map (entrywiseHom Fr) P = P ∧
      P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      ∀ m ∈ adjointGroup τ L, m * P * (m * P) ∈ adjointGroup τ L := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := hF₀
  have hmain : ∀ (P : ModGL τ L),
      (P = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ), P = diagramAt τ L t h) →
      Units.map (entrywiseHom Fr) P = P ∧
      P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      ∀ m ∈ adjointGroup τ L, m * P * (m * P) ∈ adjointGroup τ L := by
    intro P hP
    rcases hP with rfl | ⟨t, ht, hPeq⟩
    · refine ⟨by simp, Subgroup.one_mem _, ?_⟩
      intro m hm
      simpa using mul_mem hm hm
    · have ht6 : t = .E6 := by
        rcases hτ with rfl | rfl
        · cases t <;> simp [TwistTag.tag] at ht ⊢
        · cases t <;> simp [TwistTag.tag] at ht
      rw [hPeq]
      exact ggL45E67_frame_diagram_facts (Fr := Fr) ht ht6
  obtain ⟨hfix, hnorm, hadj⟩ := hmain P hP
  exact ⟨Fr, P, hFr, hΦ, hfix, hnorm, hadj⟩
private theorem ggL45E67_frame_Fw_apply
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {Fr : L →+* L} {P n : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L}
    (hF₀P : ∀ x, F₀ x = P * Units.map (entrywiseHom Fr) x * P⁻¹)
    (hFw_def : ∀ x, Fw x = n * F₀ x * n⁻¹)
    (hQ_def : Q = n * P) :
    ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹ := by
  intro x
  rw [hFw_def x, hF₀P x, hQ_def]
  group

private theorem ggL45E67_frame_Fr'_pow
    {τ : Tag} {L : Type} [Field L] {e : ℕ} {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (2 ^ e)) :
    ∀ t ∈ torusGroup τ L, Units.map (entrywiseHom Fr) t = t ^ (2 ^ e) := by
  intro t ht
  exact units_map_entrywiseHom_eq_pow_of_mem_torusGroup Fr hFr ht

private theorem ggL45E67_frame_Fw_mem
    {τ : Tag} {L : Type} [Field L] {e : ℕ}
    {Fr : L →+* L} {P n : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L}
    (hPnorm : P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hnorm : n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hQ_def : Q = n * P)
    (hFr_pow : ∀ t ∈ torusGroup τ L, Units.map (entrywiseHom Fr) t = t ^ (2 ^ e))
    (hFw_eq : ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹) :
    ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L := by
  have hQnorm : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
    rw [hQ_def]; exact mul_mem hnorm hPnorm
  intro t ht
  have hmem : Units.map (entrywiseHom Fr) t ∈ torusGroup τ L := by
    rw [hFr_pow t ht]; exact Subgroup.pow_mem _ ht _
  rw [hFw_eq t]
  exact (Subgroup.mem_normalizer_iff.mp hQnorm _).mp hmem

private theorem ggL45E67_frame_Fw_square
    {τ : Tag} {L : Type} [Field L] {e : ℕ}
    {Fr : L →+* L} {P n : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L}
    (hPfix : Units.map (entrywiseHom Fr) P = P)
    (hFrn : Units.map (entrywiseHom Fr) n = n)
    (hQ2T : Q ^ 2 ∈ torusGroup τ L)
    (hQ_def : Q = n * P)
    (hFr_pow : ∀ t ∈ torusGroup τ L, Units.map (entrywiseHom Fr) t = t ^ (2 ^ e))
    (hFw_eq : ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹) :
    ∀ t ∈ torusGroup τ L, Fw (Fw t) = t ^ (2 ^ e) ^ 2 := by
  have hFrQ : Units.map (entrywiseHom Fr) Q = Q := by
    rw [hQ_def, map_mul, hFrn, hPfix]
  intro t ht
  have hFr't : Units.map (entrywiseHom Fr) t = t ^ (2 ^ e) := hFr_pow t ht
  have hFr2 : Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) t) =
      t ^ (2 ^ e) ^ 2 := by
    rw [hFr't, map_pow, hFr't, ← pow_mul, pow_two]
  have hFr2T : Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) t) ∈
      torusGroup τ L := by
    rw [hFr2]; exact Subgroup.pow_mem _ ht _
  calc Fw (Fw t) = Q * Units.map (entrywiseHom Fr) (Fw t) * Q⁻¹ := hFw_eq _
    _ = Q * (Units.map (entrywiseHom Fr) Q *
          Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) t) *
          (Units.map (entrywiseHom Fr) Q)⁻¹) * Q⁻¹ := by
        rw [hFw_eq t, map_mul, map_mul, map_inv]
    _ = Q * (Q * Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) t) * Q⁻¹) *
          Q⁻¹ := by rw [hFrQ]
    _ = Q ^ 2 * Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) t) *
          (Q ^ 2)⁻¹ := by rw [pow_two]; group
    _ = Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) t) := by
        rw [pow_two]
        have hcomm := torusGroup_comm hQ2T hFr2T
        rw [show Q * Q = Q ^ 2 from (pow_two Q).symm, hcomm]
        group
    _ = t ^ (2 ^ e) ^ 2 := hFr2

private theorem ggL45E67_frame_F0_conj_iter
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {n g : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L}
    (hFw_def : ∀ x, Fw x = n * F₀ x * n⁻¹)
    (hFg : F₀ g = g * n) :
    ∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹ := by
  have hF₀_eq : ∀ x, F₀ x = n⁻¹ * Fw x * n := by
    intro x; rw [hFw_def x]; group
  intro k
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    rw [Function.iterate_succ_apply', ih, map_mul, map_mul, map_inv, hFg, hF₀_eq,
      Function.iterate_succ_apply']
    have hinv : (g * n)⁻¹ = n⁻¹ * g⁻¹ := by group
    rw [hinv]
    group

private theorem ggL45E67_frame_Fw_torus
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ} {Fr : L →+* L} {P n g : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L}
    (hFr : ∀ c, Fr c = c ^ (2 ^ e))
    (hF₀P : ∀ x, F₀ x = P * Units.map (entrywiseHom Fr) x * P⁻¹)
    (hPfix : Units.map (entrywiseHom Fr) P = P)
    (hFrn : Units.map (entrywiseHom Fr) n = n)
    (hPnorm : P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hnorm : n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    (hQ2T : Q ^ 2 ∈ torusGroup τ L)
    (hFw_def : ∀ x, Fw x = n * F₀ x * n⁻¹)
    (hQ_def : Q = n * P)
    (hFg : F₀ g = g * n) :
    (∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹) ∧
    (∀ t ∈ torusGroup τ L, Units.map (entrywiseHom Fr) t = t ^ (2 ^ e)) ∧
    (∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L) ∧
    (∀ t ∈ torusGroup τ L, Fw (Fw t) = t ^ (2 ^ e) ^ 2) ∧
    (∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹) := by
  have hFw_eq := ggL45E67_frame_Fw_apply hF₀P hFw_def hQ_def
  have hFr_pow := ggL45E67_frame_Fr'_pow (τ := τ) (e := e) hFr
  have hFwT := ggL45E67_frame_Fw_mem hPnorm hnorm hQ_def hFr_pow hFw_eq
  exact ⟨hFw_eq, hFr_pow, hFwT,
    ggL45E67_frame_Fw_square hPfix hFrn hQ2T hQ_def hFr_pow hFw_eq,
    ggL45E67_frame_F0_conj_iter hFw_def hFg⟩

private theorem ggL45E67_frame_Q2_adjoint
    {τ : Tag} {L : Type} [Field L]
    {P n : ModGL τ L} {Q : ModGL τ L}
    (hQ_def : Q = n * P)
    (hnadj : n ∈ adjointGroup τ L)
    (hPadj : ∀ m ∈ adjointGroup τ L, m * P * (m * P) ∈ adjointGroup τ L) :
    Q ^ 2 ∈ adjointGroup τ L := by
  rw [pow_two, hQ_def]
  exact hPadj n hnadj

private theorem ggL45E67_frame_Q_conj_pow
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ} {Fr : L →+* L} {n : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L} {A : Subgroup (ModGL τ L)}
    (hFr : ∀ c, Fr c = c ^ (2 ^ e))
    (hFw_def : ∀ x, Fw x = n * F₀ x * n⁻¹)
    (hFw_eq : ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹)
    (hAT : A ≤ twistedTorusOf n F₀)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hqr : (2 ^ e) ^ 2 % 3 = 1) :
    ∀ a ∈ A, (MulAut.conj Q) a = a ^ (2 ^ e) := by
  intro a ha
  have haT : a ∈ torusGroup τ L := (mem_twistedTorusOf.mp (hAT ha)).1
  have hFwa : Fw a = a := by
    rw [hFw_def a]
    exact (mem_twistedTorusOf.mp (hAT ha)).2
  have hFr'a : Units.map (entrywiseHom Fr) a = a ^ (2 ^ e) :=
    units_map_entrywiseHom_eq_pow_of_mem_torusGroup Fr hFr haT
  have hconjq : (MulAut.conj Q) (a ^ (2 ^ e)) = a := by
    rw [MulAut.conj_apply, ← hFr'a, ← hFw_eq a]
    exact hFwa
  have ha3 : a ^ 3 = 1 := hA3 a ha
  have hconj3 : ((MulAut.conj Q) a) ^ 3 = 1 := by
    rw [← map_pow, ha3, map_one]
  have hqa : ((MulAut.conj Q) a) ^ (2 ^ e) = a := by
    rw [← map_pow]
    exact hconjq
  have hqa2 : ((MulAut.conj Q) a) ^ ((2 ^ e) * (2 ^ e)) = a ^ (2 ^ e) := by
    rw [pow_mul]
    exact congrArg (· ^ (2 ^ e)) hqa
  have hfix : ((MulAut.conj Q) a) ^ ((2 ^ e) * (2 ^ e)) = (MulAut.conj Q) a := by
    rw [pow_eq_pow_mod ((2 ^ e) * (2 ^ e)) hconj3]
    have hq : (2 ^ e) * (2 ^ e) % 3 = 1 := by
      rw [← pow_two]; exact hqr
    rw [hq, pow_one]
  calc (MulAut.conj Q) a = ((MulAut.conj Q) a) ^ ((2 ^ e) * (2 ^ e)) := hfix.symm
    _ = a ^ (2 ^ e) := hqa2

private theorem ggL45E67_frame_Q_conj
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ} {Fr : L →+* L} {n : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L} {A : Subgroup (ModGL τ L)}
    (hFr : ∀ c, Fr c = c ^ (2 ^ e))
    (hFw_def : ∀ x, Fw x = n * F₀ x * n⁻¹)
    (hFw_eq : ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹)
    (hAT : A ≤ twistedTorusOf n F₀)
    (hpow : ∀ a ∈ A, (MulAut.conj Q) a = a ^ (2 ^ e)) :
    ∀ a ∈ A, (MulAut.conj Q) ((MulAut.conj Q) a) = a := by
  intro a ha
  have hconjq : (MulAut.conj Q) (a ^ (2 ^ e)) = a := by
    have hFwa : Fw a = a := by
      rw [hFw_def a]
      exact (mem_twistedTorusOf.mp (hAT ha)).2
    have hFr'a : Units.map (entrywiseHom Fr) a = a ^ (2 ^ e) :=
      units_map_entrywiseHom_eq_pow_of_mem_torusGroup Fr hFr
        (mem_twistedTorusOf.mp (hAT ha)).1
    rw [MulAut.conj_apply, ← hFr'a, ← hFw_eq a]
    exact hFwa
  calc (MulAut.conj Q) ((MulAut.conj Q) a) = (MulAut.conj Q) (a ^ (2 ^ e)) := by
        rw [hpow a ha]
    _ = a := hconjq

private theorem ggL45E67_frame_Q2_fixed
    {τ : Tag} {L : Type} [Field L]
    {Q : ModGL τ L} {A : Subgroup (ModGL τ L)}
    (hQconj : ∀ a ∈ A, (MulAut.conj Q) ((MulAut.conj Q) a) = a) :
    ∀ a ∈ A, Q ^ 2 * a * (Q ^ 2)⁻¹ = a := by
  intro a ha
  have h := hQconj a ha
  simp only [MulAut.conj_apply] at h
  calc Q ^ 2 * a * (Q ^ 2)⁻¹ = Q * (Q * a * Q⁻¹) * Q⁻¹ := by
        rw [pow_two]; group
    _ = a := h

private theorem ggL45E67_frame_Q2_centralizer
    {τ : Tag} {L : Type} [Field L] {Q : ModGL τ L} {A : Subgroup (ModGL τ L)}
    (hfixed : ∀ a ∈ A, Q ^ 2 * a * (Q ^ 2)⁻¹ = a) :
    Q ^ 2 ∈ Subgroup.centralizer (A : Set (ModGL τ L)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  calc a * Q ^ 2 = (Q ^ 2 * a * (Q ^ 2)⁻¹) * Q ^ 2 := by rw [hfixed a ha]
    _ = Q ^ 2 * a := by group

private theorem ggL45E67_frame_Q2_torus
    {τ : Tag} {L : Type} [Field L] {Q : ModGL τ L} {A : Subgroup (ModGL τ L)}
    (hQ2adj : Q ^ 2 ∈ adjointGroup τ L)
    (hQ2cent : Q ^ 2 ∈ Subgroup.centralizer (A : Set (ModGL τ L)))
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) =
      torusGroup τ L) :
    Q ^ 2 ∈ torusGroup τ L := by
  rw [← hcent]
  exact Subgroup.mem_inf.mpr ⟨hQ2adj, hQ2cent⟩

private theorem ggL45E67_frame_lang_group
    {τ : Tag} {L : Type} [Field L] {A : Subgroup (ModGL τ L)}
    (hroots : rootsTrivialOn A = ∅) :
    familyGroup (K := L)
      (fun i : {b : Fin τ.rank → Lˣ //
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ b ∈ A} => i.1) =
      torusGroup τ L := by
  let a : {b : Fin τ.rank → Lˣ //
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ b ∈ A} →
      Fin τ.rank → Lˣ := fun i => i.1
  change familyGroup (K := L) a = torusGroup τ L
  have hker : familyKernel a = rootsTrivialOn A := by
    ext γ
    constructor
    · rintro ⟨hroot, hfix⟩
      exact ⟨hroot, fun b hb => hfix ⟨b, hb⟩⟩
    · rintro ⟨hroot, hfix⟩
      exact ⟨hroot, fun i => hfix i.1 i.2⟩
  rw [familyGroup, hker, hroots]
  simp [rootSpan]

private theorem ggL45E67_frame_lang_closed
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ)
    (hgroup : familyGroup (K := L) a = torusGroup τ L) :
    closedIdentityComponent
      (familyGroup (K := L) a ⊓ Subgroup.centralizer (∅ : Set (ModGL τ L))) =
      torusGroup τ L := by
  have htop : Subgroup.centralizer (∅ : Set (ModGL τ L)) = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact absurd hy (by simp)
  rw [htop, inf_top_eq, ← hgroup]
  exact closedIdentityComponent_familyGroup a

private theorem ggL45E67_frame_lang_preserves
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {e : ℕ} {Q : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hgroup : familyGroup (K := L) a = torusGroup τ L)
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L)
    (hFw_iter3 : ∀ x, (⇑Fw)^[3] x = frobTwistGL τ L 2 (e * 3) (Q ^ 3) x) :
    ∀ g ∈ familyGroup (K := L) a ⊓ Subgroup.centralizer (∅ : Set (ModGL τ L)),
      frobTwistGL τ L 2 (e * 3) (Q ^ 3) g ∈
        familyGroup (K := L) a ⊓ Subgroup.centralizer (∅ : Set (ModGL τ L)) := by
  intro g hg
  rw [hgroup] at hg ⊢
  obtain ⟨hgT, -⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [← hFw_iter3 g]
    simpa [Function.iterate_succ_apply'] using hFwT _ (hFwT _ (hFwT _ hgT))
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact absurd hx (by simp)

private theorem ggL45E67_frame_lang_forall
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {e : ℕ} (he : 1 ≤ e) {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L)
    (hFw_iter3 : ∀ x, (⇑Fw)^[3] x = frobTwistGL τ L 2 (e * 3) (Q ^ 3) x)
    (A : Subgroup (ModGL τ L)) (hroots : rootsTrivialOn A = ∅) :
    ∀ y : ↥(torusGroup τ L), ∃ x : ↥(torusGroup τ L), y = x⁻¹ * (FZ^[3]) x := by
  have hFZ_apply : ∀ z : ↥(torusGroup τ L), (FZ z : ModGL τ L) = Fw (z : ModGL τ L) := by
    intro z
    simpa using hFZ_iter 1 z
  let Z := ↥(torusGroup τ L)
  let a : {b : Fin τ.rank → Lˣ //
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ b ∈ A} →
      Fin τ.rank → Lˣ := fun i => i.1
  have hgroup : familyGroup (K := L) a = torusGroup τ L :=
    ggL45E67_frame_lang_group (A := A) hroots
  have hclosed : closedIdentityComponent
      (familyGroup (K := L) a ⊓ Subgroup.centralizer (∅ : Set (ModGL τ L))) =
      torusGroup τ L := ggL45E67_frame_lang_closed a hgroup
  have hS := ggL45E67_frame_lang_preserves a hgroup hFwT hFw_iter3
  have hLangAll := exists_inv_mul_frobTwistGL_familyGroup_inf_centralizer
    (p := 2) (a := a) (T := (∅ : Set (ModGL τ L))) (e := e * 3) (by omega) (Q ^ 3) hS
  rw [hclosed] at hLangAll
  intro y
  obtain ⟨ζ, hζ, hζeq⟩ := hLangAll y y.2
  refine ⟨⟨ζ, hζ⟩, ?_⟩
  apply Subtype.ext
  change (y : ModGL τ L) = ζ⁻¹ * (((⇑FZ)^[3]) (⟨ζ, hζ⟩ : Z) : ModGL τ L)
  rw [hFZ_iter 3 (⟨ζ, hζ⟩ : Z), hFw_iter3]
  exact hζeq.symm

private theorem ggL45E67_frame_lang_square
    {τ : Tag} {L : Type} [Field L] {e : ℕ}
    {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFw2 : ∀ t ∈ torusGroup τ L, Fw (Fw t) = t ^ (2 ^ e) ^ 2) :
    ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2 := by
  intro z
  apply Subtype.ext
  have hiter := hFZ_iter 2 z
  have h2 : ((FZ (FZ z) : ↥(torusGroup τ L)) : ModGL τ L) =
      Fw (Fw (z : ModGL τ L)) := by
    simpa [Function.iterate_succ_apply'] using hiter
  rw [h2, hFw2 (z : ModGL τ L) z.2]
  rfl

private theorem ggL45E67_frame_lang
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {e : ℕ} (he : 1 ≤ e) {Fw : ModGL τ L →* ModGL τ L} {Q : ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L)
    (hFw2 : ∀ t ∈ torusGroup τ L, Fw (Fw t) = t ^ (2 ^ e) ^ 2)
    (hFw_iter3 : ∀ x, (⇑Fw)^[3] x = frobTwistGL τ L 2 (e * 3) (Q ^ 3) x)
    (A : Subgroup (ModGL τ L)) (hroots : rootsTrivialOn A = ∅) :
    (∀ y : ↥(torusGroup τ L), ∃ x : ↥(torusGroup τ L), y = x⁻¹ * (FZ^[3]) x) ∧
    (∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2) :=
  ⟨ggL45E67_frame_lang_forall he hFZ_iter hFwT hFw_iter3 A hroots,
    ggL45E67_frame_lang_square hFZ_iter hFw2⟩

private theorem ggL45E67_two_pow_sq_mod_three (e : ℕ) : (2 ^ e) ^ 2 % 3 = 1 := by
  induction e with
  | zero => norm_num
  | succ k ih =>
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [h2, mul_pow, Nat.mul_mod, ih]
    norm_num

private theorem ggL45E67_frame_A3
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R}
    {E : Subgroup (MulAut K)} {u : H} {g : ModGL τ L} {A : Subgroup (ModGL τ L)}
    (hEab : IsElemAbelian 3 E)
    (hΘ : Function.Injective Θ)
    (hAdef : A = (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
      (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom) :
    ∀ a ∈ A, a ^ 3 = 1 := by
  intro a ha
  rw [hAdef] at ha
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
  have hx3 : x ^ 3 = 1 := by
    have hxE : Θ x ∈ E.map (ggInducedAut θ) := by
      simpa [Subgroup.mem_comap] using hx
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hxE
    have he3 : e ^ 3 = 1 := hEab.2 e he
    apply hΘ
    rw [map_pow, map_one]
    calc (Θ x) ^ 3 = (ggInducedAut θ e) ^ 3 := by rw [heq]
      _ = ggInducedAut θ (e ^ 3) := (map_pow _ e 3).symm
      _ = 1 := by rw [he3, map_one]
  have hx3' : (x : ModGL τ L) ^ 3 = 1 := by
    have := congrArg (fun y : H => (y : ModGL τ L)) hx3
    simpa using this
  change (MulAut.conj ((u : ModGL τ L) * g)⁻¹) (x : ModGL τ L) ^ 3 = 1
  rw [MulAut.conj_apply, conj_pow, hx3']
  group

private theorem ggL45E67_frame_frob_iter3
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {e : ℕ} {Fr : L →+* L} {P n Q : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L}
    (hFr : ∀ c, Fr c = c ^ (2 ^ e))
    (hFrn : Units.map (entrywiseHom Fr) n = n)
    (hPfix : Units.map (entrywiseHom Fr) P = P)
    (hQ : Q = n * P)
    (hFw_eq : ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹) :
    ∀ x, (⇑Fw)^[3] x = frobTwistGL τ L 2 (e * 3) (Q ^ 3) x := by
  have hFr_eq : Fr = iterateFrobenius L 2 e := RingHom.ext fun c => by
    rw [hFr c, iterateFrobenius_def]
  have hQfix : entrywiseFrobGL τ L 2 e Q = Q := by
    have h : entrywiseFrobGL τ L 2 e Q = Units.map (entrywiseHom Fr) Q := by
      change Units.map (entrywiseHom (iterateFrobenius L 2 e)) Q =
        Units.map (entrywiseHom Fr) Q
      rw [← hFr_eq]
    rw [h, hQ, map_mul, hFrn, hPfix]
  have hFrob_eq : ∀ x, entrywiseFrobGL τ L 2 e x = Units.map (entrywiseHom Fr) x := by
    intro x
    change Units.map (entrywiseHom (iterateFrobenius L 2 e)) x = Units.map (entrywiseHom Fr) x
    rw [← hFr_eq]
  have hFw_frob : ∀ x, Fw x = frobTwistGL τ L 2 e Q x := by
    intro x
    rw [frobTwistGL_apply, hFrob_eq]
    exact hFw_eq x
  intro x
  rw [show ⇑Fw = ⇑(frobTwistGL τ L 2 e Q) from funext hFw_frob]
  rw [frobTwistGL_iterate (p := 2) e hQfix 3 x]
  rfl

private theorem ggL45E67_frame_FZ
    {τ : Tag} {L : Type} [Field L]
    {Fw : ModGL τ L →* ModGL τ L}
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L) :
    ∃ FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L),
      ∀ k z, ((FZ ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L) := by
  let FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L) :=
    { toFun := fun z => ⟨Fw z, hFwT z z.2⟩
      map_one' := Subtype.ext (map_one Fw)
      map_mul' := fun a b => Subtype.ext (by
        change Fw ((a : ModGL τ L) * (b : ModGL τ L)) =
          Fw (a : ModGL τ L) * Fw (b : ModGL τ L)
        exact map_mul Fw _ _) }
  refine ⟨FZ, ?_⟩
  intro k
  induction k with
  | zero => intro z; simp [FZ]
  | succ k ih =>
    intro z
    rw [Function.iterate_succ_apply']
    show Fw (((⇑FZ)^[k]) z : ModGL τ L) = (⇑Fw)^[k + 1] (z : ModGL τ L)
    rw [ih, Function.iterate_succ_apply']

private theorem ggL45E67_frame_mem_H_iff
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {H : Subgroup (ModGL τ L)} {x₀ : ModGL τ L} {u : H} {g : ModGL τ L}
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ L ∧ (⇑F₀)^[3] x = x)
    (huH : (u : ModGL τ L) ∈ adjointGroup τ L ∧
      (⇑F₀)^[3] (u : ModGL τ L) = (u : ModGL τ L))
    (hx₀adj : x₀ ∈ adjointGroup τ L) (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hF0conj : ∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹) :
    ∀ y ∈ torusGroup τ L, (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y := by
  intro y hy
  have hyadj : y ∈ adjointGroup τ L := torusGroup_le_adjointGroup' hy
  have hfix_eq : (⇑F₀)^[3] (x₀ * y * x₀⁻¹) = x₀ * (⇑Fw)^[3] y * x₀⁻¹ := by
    rw [hx₀]
    rw [show (u : ModGL τ L) * g * y * ((u : ModGL τ L) * g)⁻¹ =
        (u : ModGL τ L) * (g * y * g⁻¹) * (u : ModGL τ L)⁻¹ by group]
    rw [iterate_map_mul (f := F₀) (n := 3) (x := (u : ModGL τ L) * (g * y * g⁻¹))
        (y := (u : ModGL τ L)⁻¹),
      iterate_map_inv (f := F₀) (n := 3) (x := (u : ModGL τ L)),
      iterate_map_mul (f := F₀) (n := 3) (x := (u : ModGL τ L)) (y := g * y * g⁻¹)]
    rw [huH.2, hF0conj 3 y]
    group
  rw [hH (x₀ * y * x₀⁻¹)]
  constructor
  · rintro ⟨-, hfix⟩
    rw [hfix_eq] at hfix
    exact mul_left_cancel (mul_right_cancel hfix)
  · intro hfix
    exact ⟨mul_mem (mul_mem hx₀adj hyadj) (inv_mem hx₀adj), by rw [hfix_eq, hfix]⟩

private theorem ggL45E67_frame_fin
    {τ : Tag} {L : Type} [Field L] {K : Type} [Group K] [Finite K]
    {R : Type} [Group R] {θ : K ⧸ Subgroup.center K ≃* R}
    {H : Subgroup (ModGL τ L)} {Θ : H →* MulAut R} (hΘ : Function.Injective Θ)
    {x₀ : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y) :
    ∀ z : ↥(torusGroup τ L), (⇑FZ)^[3] z = z → IsOfFinOrder z := by
  intro z hz
  haveI : Finite R := Finite.of_surjective (θ : K ⧸ Subgroup.center K → R) θ.surjective
  haveI : Finite (MulAut R) := TableBSymp.finite_mulAut
  have hzfix : (⇑Fw)^[3] (z : ModGL τ L) = (z : ModGL τ L) := by
    have := congrArg (fun w : ↥(torusGroup τ L) => (w : ModGL τ L)) hz
    rwa [hFZ_iter 3 z] at this
  have hzH : x₀ * (z : ModGL τ L) * x₀⁻¹ ∈ H :=
    (hHmem_iff (z : ModGL τ L) z.2).mpr hzfix
  let w : H := ⟨x₀ * (z : ModGL τ L) * x₀⁻¹, hzH⟩
  obtain ⟨m, hmpos, hm⟩ := isOfFinOrder_iff_pow_eq_one.mp
    (isOfFinOrder_of_finite (Θ w))
  have hwm : w ^ m = 1 := hΘ (by rw [map_pow, hm, map_one])
  have hunder : (x₀ * (z : ModGL τ L) * x₀⁻¹) ^ m = 1 := by
    have := congrArg (fun y : H => (y : ModGL τ L)) hwm
    simpa [w] using this
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hmpos, ?_⟩
  apply Subtype.ext
  have hzpow : x₀ * (z : ModGL τ L) ^ m * x₀⁻¹ = 1 := by
    rw [← conj_pow]
    exact hunder
  calc (z : ModGL τ L) ^ m
      = x₀⁻¹ * (x₀ * (z : ModGL τ L) ^ m * x₀⁻¹) * x₀ := by group
    _ = 1 := by rw [hzpow]; group

private theorem ggL45E67_frame_transport_A
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R}
    {K : Type} [Group K] {E : Subgroup (MulAut K)}
    {θ : K ⧸ Subgroup.center K ≃* R} {Ā : Subgroup (ModGL τ L)} {h : H}
    (hΘ : Function.Injective Θ)
    (hcomm : ∀ x ∈ E, Θ h * ggInducedAut θ x = ggInducedAut θ x * Θ h)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype) :
    ∀ b : H, (b : ModGL τ L) ∈ Ā → h * b = b * h := by
  intro b hb
  rw [hĀdef] at hb
  obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.mp hb
  have hb'E : Θ b' ∈ E.map (ggInducedAut θ) := by
    simpa [Subgroup.mem_comap] using hb'
  obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hb'E
  have hc := hcomm e he
  rw [heq] at hc
  have hb'eq : b' = b := Subtype.ext hb''
  rw [← hb'eq]
  apply hΘ
  rw [map_mul, map_mul]
  exact hc

private theorem ggL45E67_frame_transport_y_mem
    {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} {A Ā : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {x₀ : ModGL τ L} {u : H} {g : ModGL τ L} {h : H}
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) =
      torusGroup τ L)
    (hAdef : A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype)
    (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hx₀adj : x₀ ∈ adjointGroup τ L)
    (hh0adj : (h : ModGL τ L) ∈ adjointGroup τ L)
    (hcommA : ∀ b : H, (b : ModGL τ L) ∈ Ā → h * b = b * h) :
    x₀⁻¹ * (h : ModGL τ L) * x₀ ∈ torusGroup τ L := by
  have hyadj : x₀⁻¹ * (h : ModGL τ L) * x₀ ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem hx₀adj) hh0adj) hx₀adj
  have hycent : x₀⁻¹ * (h : ModGL τ L) * x₀ ∈
      Subgroup.centralizer (A : Set (ModGL τ L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hAdef] at ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    rw [hĀdef] at hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    have hbcomm : h * x = x * h := hcommA x (by
      rw [hĀdef]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hbcomm' : (h : ModGL τ L) * (x : ModGL τ L) =
        (x : ModGL τ L) * (h : ModGL τ L) := by
      have := congrArg (fun z : H => (z : ModGL τ L)) hbcomm
      simpa using this
    rw [hx₀]
    calc (↑u * g)⁻¹ * ↑x * (↑u * g) * ((↑u * g)⁻¹ * ↑h * (↑u * g))
        = (↑u * g)⁻¹ * (↑x * ↑h) * (↑u * g) := by group
      _ = (↑u * g)⁻¹ * (↑h * ↑x) * (↑u * g) := by rw [hbcomm']
      _ = (↑u * g)⁻¹ * ↑h * (↑u * g) * ((↑u * g)⁻¹ * ↑x * (↑u * g)) := by group
  rw [← hcent]
  exact Subgroup.mem_inf.mpr ⟨hyadj, hycent⟩

private theorem ggL45E67_frame_transport
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    {H : Subgroup (ModGL τ L)} {A Ā : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {I : Set (MulAut R)} {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {x₀ : ModGL τ L} {u : H} {g : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ L ∧ (⇑F₀)^[3] x = x)
    (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) =
      torusGroup τ L)
    (hAdef : A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype)
    (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hx₀adj : x₀ ∈ adjointGroup τ L)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y) :
    ∀ φ ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
      ∃ y : ModGL τ L, ∃ hy : y ∈ torusGroup τ L, ∃ hfix : (⇑Fw)^[3] y = y,
        φ = Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩ := by
  intro φ hφ hcomm
  obtain ⟨h, rfl⟩ := (hI φ).mp hφ
  have hcommA := ggL45E67_frame_transport_A hΘ hcomm hĀdef
  have hh0adj : (h : ModGL τ L) ∈ adjointGroup τ L := ((hH (h : ModGL τ L)).mp h.2).1
  let y : ModGL τ L := x₀⁻¹ * (h : ModGL τ L) * x₀
  have hyT : y ∈ torusGroup τ L :=
    ggL45E67_frame_transport_y_mem hcent hAdef hĀdef hx₀ hx₀adj hh0adj hcommA
  have hxy : x₀ * y * x₀⁻¹ = (h : ModGL τ L) := by
    dsimp [y]
    group
  have hmem : x₀ * y * x₀⁻¹ ∈ H := by rw [hxy]; exact h.2
  have hFwy : (⇑Fw)^[3] y = y := (hHmem_iff y hyT).mp hmem
  refine ⟨y, hyT, hFwy, ?_⟩
  congr 1
  apply Subtype.ext
  exact hxy.symm

private theorem ggL45E67_frame_transport_rev_A
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} {n : ModGL τ L}
    {H : Subgroup (ModGL τ L)} {A Ā : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {x₀ : ModGL τ L} {u : H} {g : ModGL τ L} {y : ModGL τ L} {h : H}
    (hAT : A ≤ twistedTorusOf n F₀)
    (hAdef : A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype)
    (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hy : y ∈ torusGroup τ L) (hh : (h : ModGL τ L) = x₀ * y * x₀⁻¹) :
    ∀ b : H, (b : ModGL τ L) ∈ Ā → h * b = b * h := by
  intro b hb
  rw [hĀdef] at hb
  obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.mp hb
  have hbx : b = x := Subtype.ext hxb.symm
  rw [hbx]
  have hxA : x₀⁻¹ * (x : ModGL τ L) * x₀ ∈ A := by
    rw [hAdef]
    refine Subgroup.mem_map.mpr ⟨(x : ModGL τ L), ?_, ?_⟩
    · rw [hĀdef]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · change (MulAut.conj ((u : ModGL τ L) * g)⁻¹) (x : ModGL τ L) =
        x₀⁻¹ * (x : ModGL τ L) * x₀
      rw [MulAut.conj_apply, inv_inv, ← hx₀]
  have hxT : x₀⁻¹ * (x : ModGL τ L) * x₀ ∈ torusGroup τ L :=
    (mem_twistedTorusOf.mp (hAT hxA)).1
  have hcommT := torusGroup_comm hy hxT
  apply Subtype.ext
  change (h : ModGL τ L) * (x : ModGL τ L) = (x : ModGL τ L) * (h : ModGL τ L)
  rw [hh]
  calc (x₀ * y * x₀⁻¹) * (x : ModGL τ L)
      = x₀ * (y * (x₀⁻¹ * (x : ModGL τ L) * x₀)) * x₀⁻¹ := by group
    _ = x₀ * ((x₀⁻¹ * (x : ModGL τ L) * x₀) * y) * x₀⁻¹ := by rw [hcommT]
    _ = (x : ModGL τ L) * (x₀ * y * x₀⁻¹) := by group

private theorem ggL45E67_frame_transport_rev
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} {n : ModGL τ L}
    {H : Subgroup (ModGL τ L)} {A Ā : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {I : Set (MulAut R)} {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {x₀ : ModGL τ L} {u : H} {g : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hEI : ∀ e ∈ E, ggInducedAut θ e ∈ I)
    (hAT : A ≤ twistedTorusOf n F₀)
    (hAdef : A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype)
    (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y) :
    ∀ y, ∀ hy : y ∈ torusGroup τ L, ∀ hfix : (⇑Fw)^[3] y = y,
      Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩ ∈ I ∧
      ∀ e ∈ E, Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩ *
        ggInducedAut θ e = ggInducedAut θ e *
          Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩ := by
  intro y hy hfix
  have hmk : x₀ * y * x₀⁻¹ ∈ H := (hHmem_iff y hy).mpr hfix
  let h : H := ⟨x₀ * y * x₀⁻¹, hmk⟩
  have hh : (h : ModGL τ L) = x₀ * y * x₀⁻¹ := rfl
  have hcommA := ggL45E67_frame_transport_rev_A hAT hAdef hĀdef hx₀ hy hh
  refine ⟨?_, ?_⟩
  · exact (hI _).mpr ⟨h, rfl⟩
  · intro e he
    obtain ⟨b, hbI⟩ := (hI (ggInducedAut θ e)).mp (hEI e he)
    have hbh : h * b = b * h := hcommA b (by
      rw [hĀdef]
      exact Subgroup.mem_map.mpr ⟨b, by
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_map.mpr ⟨e, he, hbI.symm⟩, rfl⟩)
    change Θ h * ggInducedAut θ e = ggInducedAut θ e * Θ h
    rw [← hbI]
    rw [← map_mul, ← map_mul]
    exact congrArg Θ hbh

private theorem ggL45E67_frame_commutative
    {τ : Tag} {L : Type} [Field L] {R : Type} [Group R]
    {H : Subgroup (ModGL τ L)} {I : Set (MulAut R)} {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R}
    {E : Subgroup (MulAut K)} {x₀ : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (htransport : ∀ φ ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
      ∃ y : ModGL τ L, ∃ hy : y ∈ torusGroup τ L, ∃ hfix : (⇑Fw)^[3] y = y,
        φ = Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩) :
    ∀ φ ∈ I, ∀ φ' ∈ I,
      (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
      (∀ x ∈ E, φ' * ggInducedAut θ x = ggInducedAut θ x * φ') → φ * φ' = φ' * φ := by
  intro φ hφ φ' hφ' hc hc'
  obtain ⟨y, hy, hfix, rfl⟩ := htransport φ hφ hc
  obtain ⟨y', hy', hfix', rfl⟩ := htransport φ' hφ' hc'
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (x₀ * y * x₀⁻¹) * (x₀ * y' * x₀⁻¹) =
    (x₀ * y' * x₀⁻¹) * (x₀ * y * x₀⁻¹)
  calc (x₀ * y * x₀⁻¹) * (x₀ * y' * x₀⁻¹) = x₀ * (y * y') * x₀⁻¹ := by group
    _ = x₀ * (y' * y) * x₀⁻¹ := by rw [torusGroup_comm hy hy']
    _ = (x₀ * y' * x₀⁻¹) * (x₀ * y * x₀⁻¹) := by group


private theorem ggL45E67_frame_hone_hzpow_data
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R}
    {x₀ : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)} {e s : ℕ}
    {y : ModGL τ L} {hy : y ∈ torusGroup τ L} {hfix : (⇑Fw)^[3] y = y} {h : H}
    (hΘ : Function.Injective Θ)
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFZ2 : ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2)
    (hs' : ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1) (c : ℤ)
    (hc : c * ((2 ^ e : ℕ) : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s])
    (hh : (h : ModGL τ L) = x₀ * y * x₀⁻¹)
    (hu3 : GGL45IsPElt 3 (Θ h)) :
    (⟨y, hy⟩ : ↥(torusGroup τ L)) ^ 3 ^ s = 1 ∧
      FZ (⟨y, hy⟩ : ↥(torusGroup τ L)) = (⟨y, hy⟩ : ↥(torusGroup τ L)) ^ c := by
  let Z := ↥(torusGroup τ L)
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (torusGroup_comm a.2 b.2) }
  have hfixZ : (⇑FZ)^[3] (⟨y, hy⟩ : Z) = ⟨y, hy⟩ := by
    apply Subtype.ext
    rw [hFZ_iter 3 (⟨y, hy⟩ : Z)]
    exact hfix
  have hz3 : ∃ k : ℕ, (⟨y, hy⟩ : Z) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hu3
    have hh' : h ^ 3 ^ k = 1 := by
      apply hΘ
      rw [map_pow, map_one]
      exact hk
    have hunder : (x₀ * y * x₀⁻¹) ^ 3 ^ k = 1 := by
      have := congrArg (fun z : H => (z : ModGL τ L)) hh'
      simpa [hh] using this
    have hy3 : y ^ 3 ^ k = 1 := by
      have hconj : x₀ * y ^ 3 ^ k * x₀⁻¹ = 1 := by
        rw [← conj_pow]
        exact hunder
      calc y ^ 3 ^ k = x₀⁻¹ * (x₀ * y ^ 3 ^ k * x₀⁻¹) * x₀ := by group
        _ = 1 := by rw [hconj]; group
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simpa using hy3
  exact ⟨CFSG.HardMathSupport.C14Exc.pow_three_pow_eq_one_of_iterate_three_eq
      FZ hFZ2 hs' hfixZ hz3,
    CFSG.HardMathSupport.C14Exc.map_eq_zpow_of_iterate_three_eq FZ hFZ2 hs' hc hfixZ hz3⟩

private theorem ggL45E67_frame_hone_hFwj
    {τ : Tag} {L : Type} [Field L]
    {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    {y : ModGL τ L} {hy : y ∈ torusGroup τ L} {c : ℤ}
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L)
    (hFZy : FZ (⟨y, hy⟩ : ↥(torusGroup τ L)) =
      (⟨y, hy⟩ : ↥(torusGroup τ L)) ^ c) :
    (∀ k : ℕ, (⇑Fw)^[k] y = y ^ (c ^ k)) ∧
      ∀ k : ℕ, (⇑Fw)^[k] y ∈ torusGroup τ L := by
  let Z := ↥(torusGroup τ L)
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (torusGroup_comm a.2 b.2) }
  have hFZj : ∀ k : ℕ, ((⇑FZ)^[k] (⟨y, hy⟩ : Z)) = (⟨y, hy⟩ : Z) ^ (c ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_zpow, hFZy, ← zpow_mul, ← pow_succ']
  have hFwj : ∀ k : ℕ, (⇑Fw)^[k] y = y ^ (c ^ k) := by
    intro k
    have := congrArg (fun z : Z => (z : ModGL τ L)) (hFZj k)
    rw [hFZ_iter k (⟨y, hy⟩ : Z)] at this
    simpa using this
  refine ⟨hFwj, ?_⟩
  intro k
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hFwT _ ih

private theorem ggL45E67_frame_hone_exp
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R} {h : H} {s : ℕ}
    (hzpow' : (h : ModGL τ L) ^ 3 ^ s = 1) :
    (Θ h) ^ 3 ^ s = 1 := by
  have hhpow : h ^ 3 ^ s = 1 := Subtype.ext hzpow'
  calc (Θ h) ^ 3 ^ s = Θ (h ^ 3 ^ s) := (map_pow Θ h (3 ^ s)).symm
    _ = Θ 1 := by rw [hhpow]
    _ = 1 := map_one Θ

private theorem ggL45E67_frame_hone_hfar_data
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {F₀ : ModGL τ L →* ModGL τ L} {x₀ : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {g : ModGL τ L} {u : H} {j : ℕ}
    {y : ModGL τ L} {hfix : (⇑Fw)^[3] y = y} {h : H}
    (c : ℤ)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (hFwj : ∀ k : ℕ, (⇑Fw)^[k] y = y ^ (c ^ k))
    (hyj_mem : ∀ k : ℕ, (⇑Fw)^[k] y ∈ torusGroup τ L)
    (hF0conj : ∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹)
    (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hmk : x₀ * y * x₀⁻¹ ∈ H) (hh : (h : ModGL τ L) = x₀ * y * x₀⁻¹) :
    ∃ h1 h2 hfar : H,
      (h2 : ModGL τ L) = (⇑F₀)^[j] (h1 : ModGL τ L) ∧ hfar = h ^ (c ^ j) ∧
      (h1 : ModGL τ L) = g * y * g⁻¹ ∧
      (h2 : ModGL τ L) = g * (⇑Fw)^[j] y * g⁻¹ ∧
      (hfar : ModGL τ L) = x₀ * (⇑Fw)^[j] y * x₀⁻¹ := by
  have h1H : g * y * g⁻¹ ∈ H := by
    have hEq : g * y * g⁻¹ =
        (u : ModGL τ L)⁻¹ * (x₀ * y * x₀⁻¹) * (u : ModGL τ L) := by
      rw [hx₀]; group
    rw [hEq]
    exact H.mul_mem (H.mul_mem (H.inv_mem u.2) hmk) u.2
  have hfixj : (⇑Fw)^[3] ((⇑Fw)^[j] y) = (⇑Fw)^[j] y := by
    calc (⇑Fw)^[3] ((⇑Fw)^[j] y) = (⇑Fw)^[3 + j] y :=
          (Function.iterate_add_apply _ 3 j y).symm
      _ = (⇑Fw)^[j + 3] y := by rw [Nat.add_comm]
      _ = (⇑Fw)^[j] ((⇑Fw)^[3] y) := Function.iterate_add_apply _ j 3 y
      _ = (⇑Fw)^[j] y := by rw [hfix]
  have h2H : g * (⇑Fw)^[j] y * g⁻¹ ∈ H := by
    have hEq : g * (⇑Fw)^[j] y * g⁻¹ =
        (u : ModGL τ L)⁻¹ * (x₀ * (⇑Fw)^[j] y * x₀⁻¹) * (u : ModGL τ L) := by
      rw [hx₀]; group
    rw [hEq]
    exact H.mul_mem (H.mul_mem (H.inv_mem u.2)
      ((hHmem_iff ((⇑Fw)^[j] y) (hyj_mem j)).mpr hfixj)) u.2
  let h1 : H := ⟨g * y * g⁻¹, h1H⟩
  let h2 : H := ⟨g * (⇑Fw)^[j] y * g⁻¹, h2H⟩
  have hh1 : (h2 : ModGL τ L) = (⇑F₀)^[j] (h1 : ModGL τ L) := by
    dsimp [h1, h2]
    exact (hF0conj j y).symm
  have hfarH : x₀ * (⇑Fw)^[j] y * x₀⁻¹ ∈ H :=
    (hHmem_iff ((⇑Fw)^[j] y) (hyj_mem j)).mpr hfixj
  let hfar : H := ⟨x₀ * (⇑Fw)^[j] y * x₀⁻¹, hfarH⟩
  have hfar_eq : hfar = h ^ (c ^ j) := by
    apply Subtype.ext
    change x₀ * (⇑Fw)^[j] y * x₀⁻¹ = (h : ModGL τ L) ^ (c ^ j)
    rw [hh, hFwj j, conj_zpow]
  exact ⟨h1, h2, hfar, hh1, hfar_eq, rfl, rfl, rfl⟩

private theorem ggL45E67_frame_hone_hfar
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K}
    {f : MulAut R} {j : ℕ}
    {F₀ : ModGL τ L →* ModGL τ L} {x₀ : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {g : ModGL τ L} {u : H}
    {y : ModGL τ L} {hfix : (⇑Fw)^[3] y = y} {h : H}
    (c : ℤ)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (hFwj : ∀ k : ℕ, (⇑Fw)^[k] y = y ^ (c ^ k))
    (hyj_mem : ∀ k : ℕ, (⇑Fw)^[k] y ∈ torusGroup τ L)
    (hF0conj : ∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹)
    (hψ : ggInducedAut θ ψ = Θ u * f * (Θ u)⁻¹)
    (hfj : ∀ h h' : H, (h' : ModGL τ L) = (⇑F₀)^[j] h → f * Θ h * f⁻¹ = Θ h')
    (hx₀ : x₀ = (u : ModGL τ L) * g)
    (hmk : x₀ * y * x₀⁻¹ ∈ H) (hh : (h : ModGL τ L) = x₀ * y * x₀⁻¹) :
    ∃ hfar : H, ggInducedAut θ ψ * Θ h * (ggInducedAut θ ψ)⁻¹ = Θ hfar ∧
      hfar = h ^ (c ^ j) := by
  obtain ⟨h1, h2, hfar, hh1, hfar_eq, h1eq, h2eq, hfareq⟩ :=
    ggL45E67_frame_hone_hfar_data (H := H) (F₀ := F₀) (x₀ := x₀) (Fw := Fw)
      (g := g) (u := u) (y := y) (hfix := hfix) (h := h) (j := j)
      c hHmem_iff hFwj hyj_mem hF0conj hx₀ hmk hh
  have hUh : (Θ u)⁻¹ * Θ h * Θ u = Θ h1 := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (u : ModGL τ L)⁻¹ * (h : ModGL τ L) * (u : ModGL τ L) = (h1 : ModGL τ L)
    rw [h1eq, hh, hx₀]
    group
  have hu2 : Θ u * Θ h2 * (Θ u)⁻¹ = Θ hfar := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (u : ModGL τ L) * (h2 : ModGL τ L) * (u : ModGL τ L)⁻¹ = (hfar : ModGL τ L)
    rw [h2eq, hfareq, hx₀]
    group
  have hleft : ggInducedAut θ ψ * Θ h * (ggInducedAut θ ψ)⁻¹ = Θ hfar := by
    rw [hψ]
    calc (Θ u * f * (Θ u)⁻¹) * Θ h * (Θ u * f * (Θ u)⁻¹)⁻¹
        = Θ u * (f * ((Θ u)⁻¹ * Θ h * Θ u) * f⁻¹) * (Θ u)⁻¹ := by group
      _ = Θ u * (f * Θ h1 * f⁻¹) * (Θ u)⁻¹ := by rw [hUh]
      _ = Θ u * Θ h2 * (Θ u)⁻¹ := by rw [hfj h1 h2 hh1]
      _ = Θ hfar := hu2
  exact ⟨hfar, hleft, hfar_eq⟩
private theorem ggL45E67_frame_hone_one
    {τ : Tag} {L : Type} [Field L] {R : Type} [Group R]
    {H : Subgroup (ModGL τ L)} {I : Set (MulAut R)} {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K}
    {E : Subgroup (MulAut K)} {f : MulAut R} {j s e : ℕ}
    {F₀ : ModGL τ L →* ModGL τ L}
    {x₀ : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)} {g : ModGL τ L} {u : H}
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (htransport : ∀ φ ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
      ∃ y : ModGL τ L, ∃ hy : y ∈ torusGroup τ L, ∃ hfix : (⇑Fw)^[3] y = y,
        φ = Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩)
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFZ2 : ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2)
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L)
    (hF0conj : ∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹)
    (hψ : ggInducedAut θ ψ = Θ u * f * (Θ u)⁻¹)
    (hfj : ∀ h h' : H, (h' : ModGL τ L) = (⇑F₀)^[j] h → f * Θ h * f⁻¹ = Θ h')
    (hΘ : Function.Injective Θ)
    (hs' : ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1) (hx₀ : x₀ = (u : ModGL τ L) * g)
    (c : ℤ) (hc : c * ((2 ^ e : ℕ) : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s]) :
    ∀ φ : MulAut R, GGL45InCIp 3 I θ E φ →
      φ ^ 3 ^ s = 1 ∧
        ggInducedAut θ ψ * φ * (ggInducedAut θ ψ)⁻¹ = φ ^ (c ^ j) := by
  intro φ hφ
  obtain ⟨y, hy, hfix, rfl⟩ := htransport φ hφ.1 hφ.2.1
  let h : H := ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩
  have hh : (h : ModGL τ L) = x₀ * y * x₀⁻¹ := rfl
  obtain ⟨hzpow, hFZy⟩ :=
    ggL45E67_frame_hone_hzpow_data (H := H) (R := R) (Θ := Θ)
      (h := h) (x₀ := x₀) (Fw := Fw) (FZ := FZ) (y := y) (hy := hy)
      (hfix := hfix)
      (e := e) (s := s) hΘ hFZ_iter hFZ2 hs' c hc hh hφ.2.2
  obtain ⟨hFwj, hyj_mem⟩ :=
    ggL45E67_frame_hone_hFwj (Fw := Fw) (FZ := FZ) (y := y) (hy := hy) (c := c)
      hFZ_iter hFwT hFZy
  constructor
  · have hzpow' : y ^ 3 ^ s = 1 := by
      have := congrArg (fun z : ↥(torusGroup τ L) => (z : ModGL τ L)) hzpow
      simpa using this
    have hhpow : (h : ModGL τ L) ^ 3 ^ s = 1 := by
      change (x₀ * y * x₀⁻¹) ^ 3 ^ s = 1
      rw [conj_pow, hzpow']
      group
    exact ggL45E67_frame_hone_exp hhpow
  · obtain ⟨hfar, hleft, hfar_eq⟩ :=
      ggL45E67_frame_hone_hfar (H := H) (R := R) (Θ := Θ) (K := K)
        (θ := θ) (ψ := ψ) (f := f) (F₀ := F₀) (x₀ := x₀) (Fw := Fw)
        (g := g) (u := u) (y := y) (hfix := hfix) (h := h) (j := j)
        c hHmem_iff hFwj hyj_mem hF0conj hψ hfj hx₀
        ((hHmem_iff y hy).mpr hfix) hh
    calc ggInducedAut θ ψ * Θ h * (ggInducedAut θ ψ)⁻¹ = Θ hfar := hleft
      _ = Θ (h ^ (c ^ j)) := by rw [hfar_eq]
      _ = (Θ h) ^ (c ^ j) := map_zpow Θ h (c ^ j)

private theorem ggL45E67_frame_hone
    {τ : Tag} {L : Type} [Field L] {R : Type} [Group R]
    {H : Subgroup (ModGL τ L)} {I : Set (MulAut R)} {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K}
    {E : Subgroup (MulAut K)} {f : MulAut R} {j s e : ℕ}
    {F₀ : ModGL τ L →* ModGL τ L}
    {x₀ : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)} {g : ModGL τ L} {u : H}
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (htransport : ∀ φ ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
      ∃ y : ModGL τ L, ∃ hy : y ∈ torusGroup τ L, ∃ hfix : (⇑Fw)^[3] y = y,
        φ = Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩)
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFZ2 : ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2)
    (hFwT : ∀ t ∈ torusGroup τ L, Fw t ∈ torusGroup τ L)
    (hF0conj : ∀ k y, (⇑F₀)^[k] (g * y * g⁻¹) = g * (⇑Fw)^[k] y * g⁻¹)
    (hψ : ggInducedAut θ ψ = Θ u * f * (Θ u)⁻¹)
    (hfj : ∀ h h' : H, (h' : ModGL τ L) = (⇑F₀)^[j] h → f * Θ h * f⁻¹ = Θ h')
    (hΘ : Function.Injective Θ)
    (hs' : ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1) (hx₀ : x₀ = (u : ModGL τ L) * g)
    (c : ℤ) (hc : c * ((2 ^ e : ℕ) : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s]) :
    GGL45HOne 3 I θ E (ggInducedAut θ ψ) s (c ^ j) := by
  refine ⟨?_, ?_⟩
  · intro φ φ' hφ hφ'
    obtain ⟨y₁, hy₁, hfix₁, rfl⟩ := htransport φ hφ.1 hφ.2.1
    obtain ⟨y₂, hy₂, hfix₂, rfl⟩ := htransport φ' hφ'.1 hφ'.2.1
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (x₀ * y₁ * x₀⁻¹) * (x₀ * y₂ * x₀⁻¹) =
      (x₀ * y₂ * x₀⁻¹) * (x₀ * y₁ * x₀⁻¹)
    calc (x₀ * y₁ * x₀⁻¹) * (x₀ * y₂ * x₀⁻¹) = x₀ * (y₁ * y₂) * x₀⁻¹ := by group
      _ = x₀ * (y₂ * y₁) * x₀⁻¹ := by rw [torusGroup_comm hy₁ hy₂]
      _ = (x₀ * y₂ * x₀⁻¹) * (x₀ * y₁ * x₀⁻¹) := by group
  · exact ggL45E67_frame_hone_one (H := H) (R := R) (I := I) (Θ := Θ) (K := K)
      (θ := θ) (ψ := ψ) (E := E) (f := f) (F₀ := F₀) (x₀ := x₀) (Fw := Fw)
      (FZ := FZ) (g := g) (u := u) (j := j) (s := s) (e := e)
      hHmem_iff htransport hFZ_iter hFZ2 hFwT hF0conj hψ hfj hΘ hs' hx₀ c hc
private theorem ggL45E67_frame_pair_card
    {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R] {I : Set (MulAut R)}
    {Θ : H →* MulAut R} {K : Type} [Group K]
    {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {u : H} {g : ModGL τ L} {A Ā : Subgroup (ModGL τ L)}
    (hAdef : A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hEI : ∀ e ∈ E, ggInducedAut θ e ∈ I) (hΘ : Function.Injective Θ)
    (hK : commutator K = ⊤) (hE2 : 3 ^ 2 ≤ Nat.card E) :
    Nat.card A = Nat.card E ∧ 3 ^ 2 ≤ Nat.card A := by
  have hbar : Nat.card A = Nat.card E := by
    have hconj : Nat.card A = Nat.card Ā := by
      rw [hAdef]
      exact Subgroup.card_map_of_injective (MulAut.conj ((u : ModGL τ L) * g)⁻¹).injective
    have hsub : Nat.card Ā = Nat.card
        (((E.map (ggInducedAut θ)).comap Θ) : Subgroup H) := by
      rw [hĀdef]
      exact Subgroup.card_map_of_injective H.subtype_injective
    have hcomap : Nat.card
        (((E.map (ggInducedAut θ)).comap Θ) : Subgroup H) =
        Nat.card (E.map (ggInducedAut θ)) := by
      have hmap := Subgroup.map_comap_eq_self (f := Θ)
        (H := E.map (ggInducedAut θ)) (by
          intro φ hφ
          obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hφ
          obtain ⟨g, hg⟩ := (hI (ggInducedAut θ e)).mp (hEI e he)
          exact ⟨g, hg⟩)
      calc Nat.card (((E.map (ggInducedAut θ)).comap Θ) : Subgroup H)
          = Nat.card (Subgroup.map Θ (((E.map (ggInducedAut θ)).comap Θ) : Subgroup H)) :=
            (Subgroup.card_map_of_injective hΘ).symm
        _ = Nat.card (E.map (ggInducedAut θ)) := by rw [hmap]
    have hE : Nat.card (E.map (ggInducedAut θ)) = Nat.card E :=
      Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hK θ)
    rw [hconj, hsub, hcomap, hE]
  exact ⟨hbar, by rw [hbar]; exact hE2⟩

private theorem ggL45E67_frame_pair_y
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    {A : Subgroup (ModGL τ L)} {w : WeylGroup τ}
    (hAT : A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hFw_def : ∀ x, Fw x = canonicalRep (coxeterSystem τ) L w * F₀ x *
      (canonicalRep (coxeterSystem τ) L w)⁻¹)
    (hcard : 3 ^ 2 ≤ Nat.card A)
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFZ_apply : ∀ z : ↥(torusGroup τ L), (FZ z : ModGL τ L) = Fw (z : ModGL τ L)) :
    ∃ (y₁ y₂ : ModGL τ L) (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
      (hy1T : y₁ ∈ torusGroup τ L) (hy2T : y₂ ∈ torusGroup τ L),
      Fw y₁ = y₁ ∧ Fw y₂ = y₂ ∧ (⇑Fw)^[3] y₁ = y₁ ∧ (⇑Fw)^[3] y₂ = y₂ ∧
      (⇑FZ)^[3] (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) = ⟨y₁, hy1T⟩ ∧
      (⇑FZ)^[3] (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) = ⟨y₂, hy2T⟩ ∧
      (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 ∧
      (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 ∧
      FZ (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) = ⟨y₁, hy1T⟩ ∧
      FZ (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) = ⟨y₂, hy2T⟩ ∧
      (∀ m n : ℕ, y₁ ^ m * y₂ ^ n = 1 → 3 ∣ m ∧ 3 ∣ n) := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hind⟩ :=
    CFSG.HardMathSupport.C14Cl.exists_indep Nat.prime_three A hA3 hcard
  have hy1T : y₁ ∈ torusGroup τ L := (mem_twistedTorusOf.mp (hAT hy₁)).1
  have hy2T : y₂ ∈ torusGroup τ L := (mem_twistedTorusOf.mp (hAT hy₂)).1
  have hFw1 : Fw y₁ = y₁ := by
    rw [hFw_def y₁]
    exact (mem_twistedTorusOf.mp (hAT hy₁)).2
  have hFw2 : Fw y₂ = y₂ := by
    rw [hFw_def y₂]
    exact (mem_twistedTorusOf.mp (hAT hy₂)).2
  have hfix1 : (⇑Fw)^[3] y₁ = y₁ := by
    simpa [Function.iterate_succ_apply', hFw1]
  have hfix2 : (⇑Fw)^[3] y₂ = y₂ := by
    simpa [Function.iterate_succ_apply', hFw2]
  have hfix1Z : (⇑FZ)^[3] (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) = ⟨y₁, hy1T⟩ := by
    apply Subtype.ext
    rw [hFZ_iter 3 (⟨y₁, hy1T⟩ : ↥(torusGroup τ L))]
    exact hfix1
  have hfix2Z : (⇑FZ)^[3] (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) = ⟨y₂, hy2T⟩ := by
    apply Subtype.ext
    rw [hFZ_iter 3 (⟨y₂, hy2T⟩ : ↥(torusGroup τ L))]
    exact hfix2
  have hy13 : (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 := by
    apply Subtype.ext
    exact hA3 y₁ hy₁
  have hy23 : (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 := by
    apply Subtype.ext
    exact hA3 y₂ hy₂
  have hFy1 : FZ (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) = ⟨y₁, hy1T⟩ := by
    apply Subtype.ext
    rw [hFZ_apply]
    exact hFw1
  have hFy2 : FZ (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) = ⟨y₂, hy2T⟩ := by
    apply Subtype.ext
    rw [hFZ_apply]
    exact hFw2
  exact ⟨y₁, y₂, hy₁, hy₂, hy1T, hy2T, hFw1, hFw2, hfix1, hfix2,
    hfix1Z, hfix2Z, hy13, hy23, hFy1, hFy2, hind⟩

private theorem ggL45E67_frame_pair_hpe
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R} {x₀ : ModGL τ L} {s : ℕ}
    {z : ↥(torusGroup τ L)} (hmk : x₀ * (z : ModGL τ L) * x₀⁻¹ ∈ H)
    (hzpow : (z : ModGL τ L) ^ 3 ^ s = 1) :
    GGL45IsPElt 3 (Θ ⟨x₀ * (z : ModGL τ L) * x₀⁻¹, hmk⟩) := by
  refine ⟨s, ?_⟩
  calc (Θ ⟨x₀ * (z : ModGL τ L) * x₀⁻¹, hmk⟩) ^ 3 ^ s
      = Θ (⟨x₀ * (z : ModGL τ L) * x₀⁻¹, hmk⟩ ^ 3 ^ s) :=
        (map_pow Θ _ (3 ^ s)).symm
    _ = Θ 1 := by
        congr 1
        apply Subtype.ext
        change (x₀ * (z : ModGL τ L) * x₀⁻¹) ^ 3 ^ s = 1
        rw [conj_pow, hzpow]
        group
    _ = 1 := map_one Θ

private theorem ggL45E67_frame_pair_z_finish
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R} {x₀ : ModGL τ L} {s : ℕ}
    {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    {z₁ z₂ : ↥(torusGroup τ L)}
    (hmk1 : x₀ * (z₁ : ModGL τ L) * x₀⁻¹ ∈ H)
    (hmk2 : x₀ * (z₂ : ModGL τ L) * x₀⁻¹ ∈ H) {y₁ y₂ : ModGL τ L}
    (hz1fix : (⇑FZ)^[3] z₁ = z₁) (hz2fix : (⇑FZ)^[3] z₂ = z₂)
    (hz1pow : (z₁ : ModGL τ L) ^ 3 ^ s = 1)
    (hz2pow : (z₂ : ModGL τ L) ^ 3 ^ s = 1)
    (hz1eq : (z₁ : ModGL τ L) ^ 3 ^ (s - 1) = y₁)
    (hz2eq : (z₂ : ModGL τ L) ^ 3 ^ (s - 1) = y₂)
    (hz1fix' : (⇑Fw)^[3] (z₁ : ModGL τ L) = (z₁ : ModGL τ L))
    (hz2fix' : (⇑Fw)^[3] (z₂ : ModGL τ L) = (z₂ : ModGL τ L)) :
    ∃ (z₁ z₂ : ↥(torusGroup τ L))
      (hmk1 : x₀ * (z₁ : ModGL τ L) * x₀⁻¹ ∈ H)
      (hmk2 : x₀ * (z₂ : ModGL τ L) * x₀⁻¹ ∈ H),
      (⇑FZ)^[3] z₁ = z₁ ∧ (⇑FZ)^[3] z₂ = z₂ ∧
      (z₁ : ModGL τ L) ^ 3 ^ s = 1 ∧ (z₂ : ModGL τ L) ^ 3 ^ s = 1 ∧
      (z₁ : ModGL τ L) ^ 3 ^ (s - 1) = y₁ ∧
      (z₂ : ModGL τ L) ^ 3 ^ (s - 1) = y₂ ∧
      (⇑Fw)^[3] (z₁ : ModGL τ L) = (z₁ : ModGL τ L) ∧
      (⇑Fw)^[3] (z₂ : ModGL τ L) = (z₂ : ModGL τ L) ∧
      GGL45IsPElt 3 (Θ ⟨x₀ * (z₁ : ModGL τ L) * x₀⁻¹, hmk1⟩) ∧
      GGL45IsPElt 3 (Θ ⟨x₀ * (z₂ : ModGL τ L) * x₀⁻¹, hmk2⟩) := by
  refine ⟨z₁, z₂, hmk1, hmk2, hz1fix, hz2fix, hz1pow, hz2pow, hz1eq, hz2eq,
    hz1fix', hz2fix', ?_, ?_⟩
  · exact ggL45E67_frame_pair_hpe (H := H) (R := R) (Θ := Θ) hmk1 hz1pow
  · exact ggL45E67_frame_pair_hpe (H := H) (R := R) (Θ := Θ) hmk2 hz2pow

private theorem ggL45E67_frame_pair_z_prep
    {τ : Tag} {L : Type} [Field L] {e : ℕ} {A : Subgroup (ModGL τ L)}
    {y₁ y₂ : ModGL τ L} (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hy1T : y₁ ∈ torusGroup τ L) (hy2T : y₂ ∈ torusGroup τ L)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) :
    (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 ∧
      (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 ∧ ¬ 3 ∣ 2 ^ e := by
  have hy13 : (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 := by
    apply Subtype.ext
    exact hA3 y₁ hy₁
  have hy23 : (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) ^ 3 = 1 := by
    apply Subtype.ext
    exact hA3 y₂ hy₂
  have hq3 : ¬ 3 ∣ 2 ^ e := by
    intro h
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h2
  exact ⟨hy13, hy23, hq3⟩

private theorem ggL45E67_frame_pair_z
    {τ : Tag} {L : Type} [Field L] {e : ℕ}
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R] {Θ : H →* MulAut R}
    {x₀ : ModGL τ L} {Fw : ModGL τ L →* ModGL τ L}
    {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)} {A : Subgroup (ModGL τ L)}
    {s : ℕ} {y₁ y₂ : ModGL τ L} (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hy1T : y₁ ∈ torusGroup τ L) (hy2T : y₂ ∈ torusGroup τ L)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFZ2 : ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2)
    (hfin : ∀ z : ↥(torusGroup τ L), (⇑FZ)^[3] z = z → IsOfFinOrder z)
    (hlang : ∀ y : ↥(torusGroup τ L), ∃ x : ↥(torusGroup τ L),
      y = x⁻¹ * (FZ^[3]) x)
    (hs : 3 ^ s ∣ (2 ^ e) ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (hFy1 : FZ (⟨y₁, hy1T⟩ : ↥(torusGroup τ L)) = ⟨y₁, hy1T⟩)
    (hFy2 : FZ (⟨y₂, hy2T⟩ : ↥(torusGroup τ L)) = ⟨y₂, hy2T⟩) :
    ∃ (z₁ z₂ : ↥(torusGroup τ L))
      (hmk1 : x₀ * (z₁ : ModGL τ L) * x₀⁻¹ ∈ H)
      (hmk2 : x₀ * (z₂ : ModGL τ L) * x₀⁻¹ ∈ H),
      (⇑FZ)^[3] z₁ = z₁ ∧ (⇑FZ)^[3] z₂ = z₂ ∧
      (z₁ : ModGL τ L) ^ 3 ^ s = 1 ∧ (z₂ : ModGL τ L) ^ 3 ^ s = 1 ∧
      (z₁ : ModGL τ L) ^ 3 ^ (s - 1) = y₁ ∧
      (z₂ : ModGL τ L) ^ 3 ^ (s - 1) = y₂ ∧
      (⇑Fw)^[3] (z₁ : ModGL τ L) = (z₁ : ModGL τ L) ∧
      (⇑Fw)^[3] (z₂ : ModGL τ L) = (z₂ : ModGL τ L) ∧
      GGL45IsPElt 3 (Θ ⟨x₀ * (z₁ : ModGL τ L) * x₀⁻¹, hmk1⟩) ∧
      GGL45IsPElt 3 (Θ ⟨x₀ * (z₂ : ModGL τ L) * x₀⁻¹, hmk2⟩) := by
  let Z := ↥(torusGroup τ L)
  letI : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (torusGroup_comm a.2 b.2) }
  obtain ⟨hy13, hy23, hq3⟩ :=
    ggL45E67_frame_pair_z_prep hy₁ hy₂ hy1T hy2T hA3
  obtain ⟨z₁, hz₁fix, hz₁pow, hz₁eq⟩ :=
    CFSG.HardMathSupport.C14Exc.exists_pow_three_pow_eq_of_lang FZ hq3 hFZ2 hfin
      hlang hs hs' hy13 hFy1
  obtain ⟨z₂, hz₂fix, hz₂pow, hz₂eq⟩ :=
    CFSG.HardMathSupport.C14Exc.exists_pow_three_pow_eq_of_lang FZ hq3 hFZ2 hfin
      hlang hs hs' hy23 hFy2
  have hz₁fix' : (⇑Fw)^[3] (z₁ : ModGL τ L) = (z₁ : ModGL τ L) := by
    have := congrArg (fun z : ↥(torusGroup τ L) => (z : ModGL τ L)) hz₁fix
    rwa [hFZ_iter 3 z₁] at this
  have hz₂fix' : (⇑Fw)^[3] (z₂ : ModGL τ L) = (z₂ : ModGL τ L) := by
    have := congrArg (fun z : ↥(torusGroup τ L) => (z : ModGL τ L)) hz₂fix
    rwa [hFZ_iter 3 z₂] at this
  have hmk1 : x₀ * (z₁ : ModGL τ L) * x₀⁻¹ ∈ H :=
    (hHmem_iff (z₁ : ModGL τ L) z₁.2).mpr hz₁fix'
  have hmk2 : x₀ * (z₂ : ModGL τ L) * x₀⁻¹ ∈ H :=
    (hHmem_iff (z₂ : ModGL τ L) z₂.2).mpr hz₂fix'
  have hzpow1 : (z₁ : ModGL τ L) ^ 3 ^ s = 1 := by
    have := congrArg (fun z : ↥(torusGroup τ L) => (z : ModGL τ L)) hz₁pow
    rw [Subgroup.coe_pow] at this
    exact this
  have hzpow2 : (z₂ : ModGL τ L) ^ 3 ^ s = 1 := by
    have := congrArg (fun z : ↥(torusGroup τ L) => (z : ModGL τ L)) hz₂pow
    rw [Subgroup.coe_pow] at this
    exact this
  have hz₁eq' : (z₁ : ModGL τ L) ^ 3 ^ (s - 1) = y₁ := by
    have := congrArg (fun z : Z => (z : ModGL τ L)) hz₁eq
    simpa using this
  have hz₂eq' : (z₂ : ModGL τ L) ^ 3 ^ (s - 1) = y₂ := by
    have := congrArg (fun z : Z => (z : ModGL τ L)) hz₂eq
    simpa using this
  exact ggL45E67_frame_pair_z_finish hmk1 hmk2 hz₁fix hz₂fix hzpow1 hzpow2
    hz₁eq' hz₂eq' hz₁fix' hz₂fix'
private theorem ggL45E67_frame_pair_powers
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R} {x₀ : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {s : ℕ}
    {z₁ z₂ : ↥(torusGroup τ L)}
    (hmk1 : x₀ * (z₁ : ModGL τ L) * x₀⁻¹ ∈ H)
    (hmk2 : x₀ * (z₂ : ModGL τ L) * x₀⁻¹ ∈ H)
    {y₁ y₂ : ModGL τ L} (hy1T : y₁ ∈ torusGroup τ L)
    (hy2T : y₂ ∈ torusGroup τ L) (hfix1 : (⇑Fw)^[3] y₁ = y₁)
    (hfix2 : (⇑Fw)^[3] y₂ = y₂)
    (hz1eq : (z₁ : ModGL τ L) ^ 3 ^ (s - 1) = y₁)
    (hz2eq : (z₂ : ModGL τ L) ^ 3 ^ (s - 1) = y₂)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y) :
    (Θ ⟨x₀ * (z₁ : ModGL τ L) * x₀⁻¹, hmk1⟩) ^ 3 ^ (s - 1) =
      Θ ⟨x₀ * y₁ * x₀⁻¹, (hHmem_iff y₁ hy1T).mpr hfix1⟩ ∧
    (Θ ⟨x₀ * (z₂ : ModGL τ L) * x₀⁻¹, hmk2⟩) ^ 3 ^ (s - 1) =
      Θ ⟨x₀ * y₂ * x₀⁻¹, (hHmem_iff y₂ hy2T).mpr hfix2⟩ := by
  constructor
  · rw [← map_pow]
    congr 1
    apply Subtype.ext
    change (x₀ * (z₁ : ModGL τ L) * x₀⁻¹) ^ (3 ^ (s - 1)) = x₀ * y₁ * x₀⁻¹
    rw [conj_pow, hz1eq]
  · rw [← map_pow]
    congr 1
    apply Subtype.ext
    change (x₀ * (z₂ : ModGL τ L) * x₀⁻¹) ^ (3 ^ (s - 1)) = x₀ * y₂ * x₀⁻¹
    rw [conj_pow, hz2eq]

private theorem ggL45E67_frame_pair_independence
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {Θ : H →* MulAut R} {x₀ : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {s : ℕ}
    {z₁ z₂ : ↥(torusGroup τ L)}
    (hmk1 : x₀ * (z₁ : ModGL τ L) * x₀⁻¹ ∈ H)
    (hmk2 : x₀ * (z₂ : ModGL τ L) * x₀⁻¹ ∈ H)
    {y₁ y₂ : ModGL τ L} (hy1T : y₁ ∈ torusGroup τ L)
    (hy2T : y₂ ∈ torusGroup τ L) (hfix1 : (⇑Fw)^[3] y₁ = y₁)
    (hfix2 : (⇑Fw)^[3] y₂ = y₂)
    (hz1eq : (z₁ : ModGL τ L) ^ 3 ^ (s - 1) = y₁)
    (hz2eq : (z₂ : ModGL τ L) ^ 3 ^ (s - 1) = y₂)
    (hind : ∀ m n : ℕ, y₁ ^ m * y₂ ^ n = 1 → 3 ∣ m ∧ 3 ∣ n)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y) (hΘ : Function.Injective Θ) :
    ∀ m n : ℕ,
      ((Θ ⟨x₀ * (z₁ : ModGL τ L) * x₀⁻¹, hmk1⟩) ^ 3 ^ (s - 1)) ^ m *
        ((Θ ⟨x₀ * (z₂ : ModGL τ L) * x₀⁻¹, hmk2⟩) ^ 3 ^ (s - 1)) ^ n = 1 →
      3 ∣ m ∧ 3 ∣ n := by
  obtain ⟨ha1, ha2⟩ :=
    ggL45E67_frame_pair_powers (H := H) (R := R) (Θ := Θ) (Fw := Fw)
      hmk1 hmk2 hy1T hy2T hfix1 hfix2 hz1eq hz2eq hHmem_iff
  intro m n hmn
  let a1 : MulAut R := Θ ⟨x₀ * (z₁ : ModGL τ L) * x₀⁻¹, hmk1⟩
  let a2 : MulAut R := Θ ⟨x₀ * (z₂ : ModGL τ L) * x₀⁻¹, hmk2⟩
  have hyprodT : y₁ ^ m * y₂ ^ n ∈ torusGroup τ L :=
    mul_mem (Subgroup.pow_mem _ hy1T m) (Subgroup.pow_mem _ hy2T n)
  have hfixprod : (⇑Fw)^[3] (y₁ ^ m * y₂ ^ n) = y₁ ^ m * y₂ ^ n := by
    rw [iterate_map_mul (f := Fw) (n := 3) (x := y₁ ^ m) (y := y₂ ^ n),
      iterate_map_pow (f := Fw) (n := 3) (x := y₁) (k := m),
      iterate_map_pow (f := Fw) (n := 3) (x := y₂) (k := n), hfix1, hfix2]
  have hprodH : x₀ * (y₁ ^ m * y₂ ^ n) * x₀⁻¹ ∈ H :=
    (hHmem_iff _ hyprodT).mpr hfixprod
  have hprod : (a1 ^ 3 ^ (s - 1)) ^ m * (a2 ^ 3 ^ (s - 1)) ^ n =
      Θ ⟨x₀ * (y₁ ^ m * y₂ ^ n) * x₀⁻¹, hprodH⟩ := by
    rw [ha1, ha2]
    rw [← map_pow, ← map_pow, ← map_mul]
    congr 1
    apply Subtype.ext
    change (x₀ * y₁ * x₀⁻¹) ^ m * (x₀ * y₂ * x₀⁻¹) ^ n =
      x₀ * (y₁ ^ m * y₂ ^ n) * x₀⁻¹
    rw [conj_pow (a := x₀) (b := y₁) (i := m),
      conj_pow (a := x₀) (b := y₂) (i := n)]
    group
  have hzero : y₁ ^ m * y₂ ^ n = 1 := by
    have h1 : (⟨x₀ * (y₁ ^ m * y₂ ^ n) * x₀⁻¹, hprodH⟩ : H) = 1 := by
      apply hΘ
      rw [map_one, ← hprod]
      exact hmn
    have hh1 := congrArg (fun z : H => (z : ModGL τ L)) h1
    have h2 : x₀ * (y₁ ^ m * y₂ ^ n) * x₀⁻¹ = 1 := by
      simpa using hh1
    calc y₁ ^ m * y₂ ^ n =
        x₀⁻¹ * (x₀ * (y₁ ^ m * y₂ ^ n) * x₀⁻¹) * x₀ := by group
      _ = 1 := by rw [h2]; group
  exact hind m n hzero
private theorem ggL45E67_frame_pair
    {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ} {H : Subgroup (ModGL τ L)}
    {R : Type} [Group R] {I : Set (MulAut R)} {Θ : H →* MulAut R}
    {K : Type} [Group K] {θ : K ⧸ Subgroup.center K ≃* R}
    {E : Subgroup (MulAut K)} {u : H} {g : ModGL τ L} {w : WeylGroup τ}
    {A Ā : Subgroup (ModGL τ L)} {x₀ : ModGL τ L}
    {Fw : ModGL τ L →* ModGL τ L} {FZ : ↥(torusGroup τ L) →* ↥(torusGroup τ L)}
    {s : ℕ}
    (hAdef : A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom)
    (hĀdef : Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hEI : ∀ e ∈ E, ggInducedAut θ e ∈ I) (hΘ : Function.Injective Θ)
    (hK : commutator K = ⊤) (hE2 : 3 ^ 2 ≤ Nat.card E)
    (hAT : A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hFw_def : ∀ x, Fw x = canonicalRep (coxeterSystem τ) L w * F₀ x *
      (canonicalRep (coxeterSystem τ) L w)⁻¹)
    (hFZ_iter : ∀ k z, ((FZ^[k]) z : ModGL τ L) = (⇑Fw)^[k] (z : ModGL τ L))
    (hFZ_apply : ∀ z : ↥(torusGroup τ L), (FZ z : ModGL τ L) = Fw (z : ModGL τ L))
    (hFZ2 : ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2)
    (hfin : ∀ z : ↥(torusGroup τ L), (⇑FZ)^[3] z = z → IsOfFinOrder z)
    (hlang : ∀ y : ↥(torusGroup τ L), ∃ x : ↥(torusGroup τ L),
      y = x⁻¹ * (FZ^[3]) x)
    (hHmem_iff : ∀ y ∈ torusGroup τ L,
      (x₀ * y * x₀⁻¹ ∈ H) ↔ (⇑Fw)^[3] y = y)
    (htransport_rev : ∀ y, ∀ hy : y ∈ torusGroup τ L, ∀ hfix : (⇑Fw)^[3] y = y,
      Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩ ∈ I ∧
      ∀ e ∈ E, Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩ *
        ggInducedAut θ e = ggInducedAut θ e *
          Θ ⟨x₀ * y * x₀⁻¹, (hHmem_iff y hy).mpr hfix⟩)
    (hs : 3 ^ s ∣ (2 ^ e) ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1) :
    ∃ a₁ a₂ : MulAut R, GGL45InCIp 3 I θ E a₁ ∧ GGL45InCIp 3 I θ E a₂ ∧
      ∀ m n : ℕ, (a₁ ^ 3 ^ (s - 1)) ^ m * (a₂ ^ 3 ^ (s - 1)) ^ n = 1 → 3 ∣ m ∧ 3 ∣ n := by
  obtain ⟨hbar, hcard⟩ :=
    ggL45E67_frame_pair_card hAdef hĀdef hI hEI hΘ hK hE2
  obtain ⟨y₁, y₂, hy₁, hy₂, hy1T, hy2T, hFw1, hFw2, hfix1, hfix2,
    hfix1Z, hfix2Z, hy13, hy23, hFy1, hFy2, hind⟩ :=
    ggL45E67_frame_pair_y hAT hA3 hFw_def hcard hFZ_iter hFZ_apply
  obtain ⟨z₁, z₂, hmk1, hmk2, hz1fix, hz2fix, hz1pow, hz2pow, hz1eq, hz2eq,
    hz1fix', hz2fix', hpe1, hpe2⟩ :=
    ggL45E67_frame_pair_z (H := H) (R := R) (Θ := Θ) hy₁ hy₂ hy1T hy2T hA3
      hFZ_iter hFZ2 hfin hlang hs hs' hHmem_iff hFy1 hFy2
  refine ⟨Θ ⟨x₀ * (z₁ : ModGL τ L) * x₀⁻¹, hmk1⟩,
    Θ ⟨x₀ * (z₂ : ModGL τ L) * x₀⁻¹, hmk2⟩, ?_, ?_, ?_⟩
  · exact ⟨(htransport_rev (z₁ : ModGL τ L) z₁.2 hz1fix').1,
      (htransport_rev (z₁ : ModGL τ L) z₁.2 hz1fix').2, hpe1⟩
  · exact ⟨(htransport_rev (z₂ : ModGL τ L) z₂.2 hz2fix').1,
      (htransport_rev (z₂ : ModGL τ L) z₂.2 hz2fix').2, hpe2⟩
  · exact ggL45E67_frame_pair_independence hmk1 hmk2 hy1T hy2T hfix1 hfix2
      hz1eq hz2eq hind hHmem_iff hΘ
private theorem ggL45E67_frame_setup_basic
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ}
    {w : WeylGroup τ} (hτ : τ = .E6 ∨ τ = .E7)
    (hF₀ : IsSteinbergEnd τ L (2 ^ e) F₀) :
    ∃ (Fr : L →+* L) (P n Q : ModGL τ L) (Fw : ModGL τ L →* ModGL τ L),
      (∀ c, Fr c = c ^ (2 ^ e)) ∧
      (∀ x, F₀ x = P * Units.map (entrywiseHom Fr) x * P⁻¹) ∧
      Units.map (entrywiseHom Fr) P = P ∧
      P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      (∀ m ∈ adjointGroup τ L, m * P * (m * P) ∈ adjointGroup τ L) ∧
      Units.map (entrywiseHom Fr) n = n ∧
      n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      n ∈ adjointGroup τ L ∧
      (∀ x, Fw x = n * F₀ x * n⁻¹) ∧
      (∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹) ∧
      Q = n * P ∧ n = canonicalRep (coxeterSystem τ) L w := by
  obtain ⟨Fr, P, hFr, hF₀P, hPfix, hPnorm, hPadj⟩ :=
    ggL45E67_frame_steinberg hF₀ hτ
  let n : ModGL τ L := canonicalRep (coxeterSystem τ) L w
  let Q : ModGL τ L := n * P
  let Fw : ModGL τ L →* ModGL τ L := (MulAut.conj n).toMonoidHom.comp F₀
  have hFw_def : ∀ x, Fw x = n * F₀ x * n⁻¹ := fun x => rfl
  obtain ⟨hFrn, hnorm, hnadj⟩ := ggL45E67_frame_basic_frw (Fr := Fr) (w := w)
  have hFw_eq : ∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹ :=
    ggL45E67_frame_Fw_apply hF₀P hFw_def rfl
  exact ⟨Fr, P, n, Q, Fw, hFr, hF₀P, hPfix, hPnorm, hPadj, hFrn, hnorm, hnadj,
    hFw_def, hFw_eq, rfl, rfl⟩

private theorem ggL45E67_frame_setup_A
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ}
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R]
    {Θ : H →* MulAut R} {K : Type} [Group K]
    {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {u : H} {g : ModGL τ L} {w : WeylGroup τ}
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ L ∧ (⇑F₀)^[3] x = x)
    (hA : ∀ A : Subgroup (ModGL τ L), A = (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
          (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom →
        A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀ ∧ rootsTrivialOn A = ∅ ∧
          adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) = torusGroup τ L)
    (hEab : IsElemAbelian 3 E) (hΘ : Function.Injective Θ)
    (hg : g ∈ adjointGroup τ L) :
    ∃ (A Ā : Subgroup (ModGL τ L)) (x₀ : ModGL τ L),
      A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom ∧
      Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype ∧
      A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀ ∧
      rootsTrivialOn A = ∅ ∧
      adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) = torusGroup τ L ∧
      x₀ = (u : ModGL τ L) * g ∧
      ((u : ModGL τ L) ∈ adjointGroup τ L ∧
        (⇑F₀)^[3] (u : ModGL τ L) = (u : ModGL τ L)) ∧
      x₀ ∈ adjointGroup τ L ∧ (2 ^ e) ^ 2 % 3 = 1 ∧
      ∀ a ∈ A, a ^ 3 = 1 := by
  let Ā : Subgroup (ModGL τ L) := ((E.map (ggInducedAut θ)).comap Θ).map H.subtype
  let A : Subgroup (ModGL τ L) := Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom
  obtain ⟨hAT, hroots, hcent⟩ := hA A rfl
  let x₀ : ModGL τ L := (u : ModGL τ L) * g
  have huH : (u : ModGL τ L) ∈ adjointGroup τ L ∧
      (⇑F₀)^[3] (u : ModGL τ L) = (u : ModGL τ L) := (hH (u : ModGL τ L)).mp u.2
  have hx₀adj : x₀ ∈ adjointGroup τ L := by
    rw [show x₀ = (u : ModGL τ L) * g from rfl]
    exact mul_mem huH.1 hg
  have hqr : (2 ^ e) ^ 2 % 3 = 1 := ggL45E67_two_pow_sq_mod_three e
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := ggL45E67_frame_A3 hEab hΘ rfl
  exact ⟨A, Ā, x₀, rfl, rfl, hAT, hroots, hcent, rfl, huH, hx₀adj, hqr, hA3⟩

private theorem ggL45E67_frame_setup
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ}
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R]
    {Θ : H →* MulAut R} {K : Type} [Group K]
    {θ : K ⧸ Subgroup.center K ≃* R} {E : Subgroup (MulAut K)}
    {u : H} {g : ModGL τ L} {w : WeylGroup τ}
    (hτ : τ = .E6 ∨ τ = .E7) (hF₀ : IsSteinbergEnd τ L (2 ^ e) F₀)
    (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ L ∧ (⇑F₀)^[3] x = x)
    (hA : ∀ A : Subgroup (ModGL τ L), A = (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
          (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom →
        A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀ ∧ rootsTrivialOn A = ∅ ∧
          adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) = torusGroup τ L)
    (hEab : IsElemAbelian 3 E) (hΘ : Function.Injective Θ)
    (hg : g ∈ adjointGroup τ L) :
    ∃ (Fr : L →+* L) (P n Q : ModGL τ L) (Fw : ModGL τ L →* ModGL τ L)
      (A Ā : Subgroup (ModGL τ L)) (x₀ : ModGL τ L),
      (∀ c, Fr c = c ^ (2 ^ e)) ∧
      (∀ x, F₀ x = P * Units.map (entrywiseHom Fr) x * P⁻¹) ∧
      Units.map (entrywiseHom Fr) P = P ∧
      P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      (∀ m ∈ adjointGroup τ L, m * P * (m * P) ∈ adjointGroup τ L) ∧
      Units.map (entrywiseHom Fr) n = n ∧
      n ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) ∧
      n ∈ adjointGroup τ L ∧
      (∀ x, Fw x = n * F₀ x * n⁻¹) ∧
      (∀ x, Fw x = Q * Units.map (entrywiseHom Fr) x * Q⁻¹) ∧ Q = n * P ∧
      n = canonicalRep (coxeterSystem τ) L w ∧
      A = Ā.map (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom ∧
      Ā = ((E.map (ggInducedAut θ)).comap Θ).map H.subtype ∧
      A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀ ∧
      rootsTrivialOn A = ∅ ∧
      adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) = torusGroup τ L ∧
      x₀ = (u : ModGL τ L) * g ∧
      ((u : ModGL τ L) ∈ adjointGroup τ L ∧
        (⇑F₀)^[3] (u : ModGL τ L) = (u : ModGL τ L)) ∧
      x₀ ∈ adjointGroup τ L ∧ (2 ^ e) ^ 2 % 3 = 1 ∧
      ∀ a ∈ A, a ^ 3 = 1 := by
  obtain ⟨Fr, P, n, Q, Fw, hFr, hF₀P, hPfix, hPnorm, hPadj, hFrn, hnorm, hnadj,
    hFw_def, hFw_eq, hQ, hn⟩ := ggL45E67_frame_setup_basic (w := w) hτ hF₀
  obtain ⟨A, Ā, x₀, hAdef, hĀdef, hAT, hroots, hcent, hx₀, huH, hx₀adj, hqr, hA3⟩ :=
    ggL45E67_frame_setup_A (e := e) hH hA hEab hΘ hg
  exact ⟨Fr, P, n, Q, Fw, A, Ā, x₀, hFr, hF₀P, hPfix, hPnorm, hPadj, hFrn, hnorm,
    hnadj, hFw_def, hFw_eq, hQ, hn, hAdef, hĀdef, hAT, hroots, hcent, hx₀, huH, hx₀adj,
    hqr, hA3⟩

theorem ggL45E67_frame_hOne
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {F₀ : ModGL τ L →* ModGL τ L} {e : ℕ} (he : 1 ≤ e) (hF₀ : IsSteinbergEnd τ L (2 ^ e) F₀)
    {H : Subgroup (ModGL τ L)} (hH : ∀ x, x ∈ H ↔ x ∈ adjointGroup τ L ∧ (⇑F₀)^[3] x = x)
    {R : Type} [Group R] {I : Set (MulAut R)} (Θ : H →* MulAut R) (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hEab : IsElemAbelian 3 E)
    (hE2 : 3 ^ 2 ≤ Nat.card E) (hEI : ∀ e ∈ E, ggInducedAut θ e ∈ I)
    {f : MulAut R} (u : H) (hψ : ggInducedAut θ ψ = Θ u * f * (Θ u)⁻¹) {j : ℕ}
    (hfj : ∀ h h' : H, (h' : ModGL τ L) = (⇑F₀)^[j] h → f * Θ h * f⁻¹ = Θ h')
    {w : WeylGroup τ} {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hFg : F₀ g = g * canonicalRep (coxeterSystem τ) L w)
    (hA : ∀ A : Subgroup (ModGL τ L), A = (((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map
          (MulAut.conj ((u : ModGL τ L) * g)⁻¹).toMonoidHom →
        A ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀ ∧ rootsTrivialOn A = ∅ ∧
          adjointGroup τ L ⊓ Subgroup.centralizer (A : Set (ModGL τ L)) = torusGroup τ L)
    {s : ℕ} (hs : 3 ^ s ∣ (2 ^ e) ^ 6 - 1) (hs' : ¬ 3 ^ (s + 1) ∣ (2 ^ e) ^ 6 - 1) :
    (∀ φ ∈ I, ∀ φ' ∈ I, (∀ x ∈ E, φ * ggInducedAut θ x = ggInducedAut θ x * φ) →
        (∀ x ∈ E, φ' * ggInducedAut θ x = ggInducedAut θ x * φ') → φ * φ' = φ' * φ) ∧
      (∀ c : ℤ, c * ((2 ^ e : ℕ) : ℤ) ^ 2 ≡ 1 [ZMOD 3 ^ s] →
        GGL45HOne 3 I θ E (ggInducedAut θ ψ) s (c ^ j)) ∧
      ∃ a₁ a₂ : MulAut R, GGL45InCIp 3 I θ E a₁ ∧ GGL45InCIp 3 I θ E a₂ ∧
        ∀ m n : ℕ, (a₁ ^ 3 ^ (s - 1)) ^ m * (a₂ ^ 3 ^ (s - 1)) ^ n = 1 → 3 ∣ m ∧ 3 ∣ n := by
  classical
  obtain ⟨Fr, P, n, Q, Fw, A, Ā, x₀, hFr, hF₀P, hPfix, hPnorm, hPadj, hFrn, hnorm,
    hnadj, hFw_def, hFw_eq, hQ, hn, hAdef, hĀdef, hAT, hroots, hcent, hx₀, huH, hx₀adj,
    hqr, hA3⟩ := ggL45E67_frame_setup hτ hF₀ hH hA hEab hΘ hg
  have hATn : A ≤ twistedTorusOf n F₀ := by rwa [← hn] at hAT
  have hQ2adj : Q ^ 2 ∈ adjointGroup τ L :=
    ggL45E67_frame_Q2_adjoint hQ hnadj hPadj
  have hQpow := ggL45E67_frame_Q_conj_pow hFr hFw_def hFw_eq hATn hA3 hqr
  have hQconj := ggL45E67_frame_Q_conj hFr hFw_def hFw_eq hATn hQpow
  have hQ2fixed := ggL45E67_frame_Q2_fixed hQconj
  have hQ2cent := ggL45E67_frame_Q2_centralizer hQ2fixed
  have hQ2T : Q ^ 2 ∈ torusGroup τ L :=
    ggL45E67_frame_Q2_torus hQ2adj hQ2cent hcent
  have hFgn : F₀ g = g * n := by rwa [← hn] at hFg
  obtain ⟨hFw_eq', hFr_pow, hFwT, hFw2, hF0conj⟩ :=
    ggL45E67_frame_Fw_torus hFr hF₀P hPfix hFrn hPnorm hnorm hQ2T hFw_def hQ hFgn
  have hFw_iter3 := ggL45E67_frame_frob_iter3 hFr hFrn hPfix hQ hFw_eq
  obtain ⟨FZ, hFZ_iter⟩ := ggL45E67_frame_FZ (Fw := Fw) hFwT
  have hFZ_apply : ∀ z : ↥(torusGroup τ L), (FZ z : ModGL τ L) = Fw (z : ModGL τ L) := by
    intro z
    simpa using hFZ_iter 1 z
  have hlang := ggL45E67_frame_lang he hFZ_iter hFwT hFw2 hFw_iter3 A hroots
  have hFZ2 : ∀ z : ↥(torusGroup τ L), FZ (FZ z) = z ^ (2 ^ e) ^ 2 := hlang.2
  have hHmem_iff := ggL45E67_frame_mem_H_iff hH huH hx₀adj hx₀ hF0conj
  have hfin : ∀ z : ↥(torusGroup τ L), (⇑FZ)^[3] z = z → IsOfFinOrder z :=
    ggL45E67_frame_fin (θ := θ) hΘ hFZ_iter hHmem_iff
  have htransport := ggL45E67_frame_transport hH hΘ hI hcent hAdef hĀdef
    hx₀ hx₀adj hHmem_iff
  have htransport_rev := ggL45E67_frame_transport_rev hI hEI hAT hAdef hĀdef hx₀ hHmem_iff
  rw [hn] at hFw_def
  refine ⟨ggL45E67_frame_commutative hHmem_iff htransport, ?_, ?_⟩
  ·
    intro c hc
    exact ggL45E67_frame_hone hHmem_iff htransport hFZ_iter hFZ2 hFwT hF0conj
      hψ hfj hΘ hs' hx₀ c hc
  ·
    exact ggL45E67_frame_pair hAdef hĀdef hI hEI hΘ hK hE2 hAT hA3 hFw_def
      hFZ_iter hFZ_apply hFZ2 hfin hlang.1 hHmem_iff htransport_rev hs hs'

end CFSG.StandardType
