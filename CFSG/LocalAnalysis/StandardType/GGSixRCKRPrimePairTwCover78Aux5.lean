module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1

public section

namespace CFSG.StandardType.RCKRP

variable {CoeffField : Type} [Field CoeffField] [IsAlgClosed CoeffField] [CharP CoeffField 2]
attribute [local instance] ZMod.algebra


open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.Open (StatedLieTag StatedLieAdmissible)

@[expose] noncomputable def rckTw78_phi
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (z₁ : ModGL τ CoeffField) :
    twistedE6Group 2 h →* ModGL τ CoeffField :=
  (MulAut.conj z₁).toMonoidHom.comp
    ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom)

omit [IsAlgClosed CoeffField] in
theorem rckTw78_psi2_injective
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) :
    Function.Injective (psi2 τ CoeffField 2 h) := by
  intro x y hxy
  apply Subtype.ext
  have h1 := baseChangeGL_injective _ hxy
  exact (m27Equiv τ (K2 CoeffField 2 h)).symm.injective (Subtype.ext h1)

theorem rckTw78_phi_injective
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (z₁ : ModGL τ CoeffField) :
    Function.Injective (rckTw78_phi h hh z₁) := by
  intro x y hxy
  have h1 : (MulAut.conj z₁).toMonoidHom
      (((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom) x) =
      (MulAut.conj z₁).toMonoidHom
        (((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom) y) := hxy
  have h2 := (MulAut.conj z₁).injective h1
  exact (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).injective (rckTw78_psi2_injective h h2)

theorem rckTw78_phi_range
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (nv hL : ModGL τ CoeffField) (X P₀ : Subgroup (ModGL τ CoeffField))
    (hP : X = P₀.map (MulAut.conj nv).toMonoidHom)
    (hconj : P₀.map (MulAut.conj hL).toMonoidHom = (psi2 τ CoeffField 2 h).range) :
    (rckTw78_phi h hh (nv * hL⁻¹)).range = X := by
  have hcomp : (MulAut.conj (nv * hL⁻¹)).toMonoidHom.comp (MulAut.conj hL).toMonoidHom =
      (MulAut.conj nv).toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    show (nv * hL⁻¹) * (hL * x * hL⁻¹) * (nv * hL⁻¹)⁻¹ = nv * x * nv⁻¹
    group
  have h1 : (rckTw78_phi h hh (nv * hL⁻¹)).range =
      ((psi2 τ CoeffField 2 h).range).map (MulAut.conj (nv * hL⁻¹)).toMonoidHom := by
    show (((MulAut.conj (nv * hL⁻¹)).toMonoidHom.comp
      ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom)).range) = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).surjective, Subgroup.map_top]
  rw [h1, hP, ← hconj, Subgroup.map_map, hcomp]

theorem rckTw78_phi_ker
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (z₁ : ModGL τ CoeffField) :
    (rckTw78_phi h hh z₁).ker ≤ Subgroup.center (twistedE6Group 2 h) := by
  rw [(MonoidHom.ker_eq_bot_iff _).mpr (rckTw78_phi_injective h hh z₁)]
  exact bot_le

theorem rckTw78_phi_quasisimple
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (z₁ : ModGL τ CoeffField) (X : Subgroup (ModGL τ CoeffField))
    (hX : (rckTw78_phi h hh z₁).range = X) :
    CFSG.IsQuasisimple ↥X := by
  haveI : Finite (K2 CoeffField 2 h) :=
    finite_frobeniusFixedField (L := CoeffField) (ℓ := 2) (m := 2 * h) (by omega)
  have hk : Nat.card (K2 CoeffField 2 h) = (2 ^ h) ^ 2 := by
    rw [card_K2 (L := CoeffField) (ℓ := 2) (f := h) (by omega), pow_mul']
  have hk4 : 4 ≤ Nat.card (K2 CoeffField 2 h) := by
    rw [hk]
    have h2 : 2 ≤ 2 ^ h := le_trans (by norm_num) (Nat.le_self_pow hh.ne' 2)
    nlinarith
  have hqsG := fixedGroup_isQuasisimple_of_four_le_card (theta2 CoeffField 2 h) theta2_theta2 hk4
  have hqsT : CFSG.IsQuasisimple (twistedE6Group 2 h) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).symm hqsG
  have hqsR : CFSG.IsQuasisimple ↥((rckTw78_phi h hh z₁).range) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (rckTw78_phi_injective h hh z₁)) hqsT
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hX) hqsR

theorem rckTw78_frob
    {τ : Tag} [M27Ok τ] [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ CoeffField p₀) {h : ℕ}
    (hq : S.D.q = 2 ^ h) :
    S.D.Φ = Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) := by
  have hτ : M27Ok τ := ‹M27Ok τ›
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq'⟩ := S.exists_char_pow
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP CoeffField ℓ := hchar
  have hℓ2 : ℓ = 2 := by
    have hc2 : CharP CoeffField 2 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 2) CoeffField).injective 2
    exact CharP.eq CoeffField hchar hc2
  have hfh : f = h := by
    have h2 : ℓ ^ f = 2 ^ h := by rw [← hq', hq]
    rw [hℓ2] at h2
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h2
  subst ℓ
  subst f
  haveI : CharP CoeffField 2 := hchar
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hFr' : Fr = iterateFrobenius CoeffField 2 h := by
    ext c
    rw [hFr, hq', iterateFrobenius_def]
  rw [hΦ, hFr']

omit [IsAlgClosed CoeffField] [CharP CoeffField 2] in
theorem rckTw78_n1fix
    {τ : Tag} [M27Ok τ] [E6Sub τ] (n₁ : ModGL τ CoeffField)
    (hgen : ∀ j ∈ e6Set τ, ∀ c : CoeffField,
      n₁ * xUnit τ CoeffField j c * n₁⁻¹ = xUnit τ CoeffField (rhoτ τ j) c ∧
        n₁ * yUnit τ CoeffField j c * n₁⁻¹ = yUnit τ CoeffField (rhoτ τ j) c) :
    ∀ g ∈ rootSpan τ CoeffField ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ),
      -(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ)} : Set (Fin τ.rank → ℤ)), n₁ * g * n₁⁻¹ = g := by
  have hmem : (e6Idx 1 : Fin τ.rank) ∈ e6Set τ := e6Idx_mem_e6Set (τ := τ) 1
  have hfixn : rhoτ τ (e6Idx 1) = e6Idx 1 := by
    rw [rhoτ_e6Idx]
    have h6 : rho6 (1 : Fin Tag.E6.rank) = 1 := by decide
    rw [h6]
  have hx : ∀ c : CoeffField, n₁ * xUnit τ CoeffField (e6Idx 1) c * n₁⁻¹ = xUnit τ CoeffField (e6Idx 1) c := by
    intro c
    have := (hgen (e6Idx 1) hmem c).1
    rwa [hfixn] at this
  have hy : ∀ c : CoeffField, n₁ * yUnit τ CoeffField (e6Idx 1) c * n₁⁻¹ = yUnit τ CoeffField (e6Idx 1) c := by
    intro c
    have := (hgen (e6Idx 1) hmem c).2
    rwa [hfixn] at this
  have hgenC : ∀ δ ∈ ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ),
      -(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ)} : Set (Fin τ.rank → ℤ)),
      rootSubgroup τ CoeffField δ ≤ Subgroup.centralizer ({n₁} : Set (ModGL τ CoeffField)) := by
    intro δ hδ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rw [rootSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    change pinnedX τ CoeffField δ c ∈ Subgroup.centralizer ({n₁} : Set (ModGL τ CoeffField))
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hδ with rfl | rfl
    · rw [pinnedX_single]
      calc xUnit τ CoeffField (e6Idx 1) c * n₁
          = (n₁ * xUnit τ CoeffField (e6Idx 1) c * n₁⁻¹) * n₁ := by rw [hx c]
        _ = n₁ * xUnit τ CoeffField (e6Idx 1) c := by group
    · rw [pinnedX_neg_single]
      calc yUnit τ CoeffField (e6Idx 1) c * n₁
          = (n₁ * yUnit τ CoeffField (e6Idx 1) c * n₁⁻¹) * n₁ := by rw [hy c]
        _ = n₁ * yUnit τ CoeffField (e6Idx 1) c := by group
  intro g hg
  have hle : rootSpan τ CoeffField ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ),
      -(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ)} : Set (Fin τ.rank → ℤ)) ≤
      Subgroup.centralizer ({n₁} : Set (ModGL τ CoeffField)) := by
    rw [rootSpan]
    exact iSup₂_le (fun δ hδ => hgenC δ hδ)
  have hcomm : g * n₁ = n₁ * g := Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  calc n₁ * g * n₁⁻¹ = (g * n₁) * n₁⁻¹ := by rw [hcomm]
    _ = g := by group

omit [IsAlgClosed CoeffField] in
theorem rckTw78_hconj
    {τ : Tag} [M27Ok τ] [E6Sub τ] (h : ℕ) (nv nw hL n₁ : ModGL τ CoeffField)
    (hh' : hL ∈ subsystemGroup τ CoeffField (e6Set τ))
    (hlangpt : ∀ g : ModGL τ CoeffField,
      (nv⁻¹ * nw * nv) * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) g *
          (nv⁻¹ * nw * nv)⁻¹ =
        hL⁻¹ * (n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (hL * g * hL⁻¹) *
          n₁⁻¹) * hL) :
    (rootSpan τ CoeffField (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints (nv⁻¹ * nw * nv)
        (Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)))).map (MulAut.conj hL).toMonoidHom =
      stdLayer τ 2 h n₁ := by
  have hlang : ∀ g : ModGL τ CoeffField,
      (nv⁻¹ * nw * nv) * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) g *
          (nv⁻¹ * nw * nv)⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (hL * g * hL⁻¹) * n₁⁻¹ =
          hL * g * hL⁻¹ := by
    intro g
    have hpt := hlangpt g
    constructor
    · intro hx
      have h1 : hL⁻¹ * (n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h))
          (hL * g * hL⁻¹) * n₁⁻¹) * hL = g := by rw [← hpt, hx]
      calc n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (hL * g * hL⁻¹) * n₁⁻¹
          = hL * (hL⁻¹ * (n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h))
              (hL * g * hL⁻¹) * n₁⁻¹) * hL) * hL⁻¹ := by group
        _ = hL * g * hL⁻¹ := by rw [h1]
    · intro hx
      rw [hpt, hx]
      group
  have hQeq : rootSpan τ CoeffField (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ CoeffField (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  ext g
  constructor
  · rintro ⟨x, ⟨hxQ, hxF⟩, rfl⟩
    rw [hQeq] at hxQ
    refine mem_stdLayer.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hh' hxQ) (inv_mem hh')
    · exact (hlang x).1 hxF
  · intro hg
    obtain ⟨hgQ, hgF⟩ := mem_stdLayer.1 hg
    have hx : hL⁻¹ * g * hL ∈ subsystemGroup τ CoeffField (e6Set τ) :=
      mul_mem (mul_mem (inv_mem hh') hgQ) hh'
    have hhx : hL * (hL⁻¹ * g * hL) * hL⁻¹ = g := by group
    refine ⟨hL⁻¹ * g * hL, ⟨by rw [hQeq]; exact hx, ?_⟩, hhx⟩
    refine (hlang _).2 ?_
    rw [hhx]
    exact hgF

end CFSG.StandardType.RCKRP

end
