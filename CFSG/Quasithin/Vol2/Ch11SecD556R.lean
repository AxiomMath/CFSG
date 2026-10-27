module

public import CFSG.Quasithin.Vol2.Ch11SecD556Q
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecD556B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isCComponent_conj_and_quasisimple {Y I' : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hI' : quasithinIsCComponent I' Y)
    (hq : CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I')) :
    quasithinIsCComponent (I'.map (MulAut.conj g).toMonoidHom) Y ∧
      CFSG.IsQuasisimple (↥(I'.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(I'.map (MulAut.conj g).toMonoidHom)) := by
  constructor
  · have h1 := SecA.isCComponent_map_equiv (MulAut.conj g) hI'
    rwa [SecA.map_conj_eq_of_mem_normalizer hg] at h1
  · let e : ↥I' ≃* ↥(I'.map (MulAut.conj g).toMonoidHom) :=
      I'.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have he : (CFSG.pCore 2 ↥I').map e.toMonoidHom =
        CFSG.pCore 2 ↥(I'.map (MulAut.conj g).toMonoidHom) :=
      CFSG.pCore_map_iso 2 e
    let e' := QuotientGroup.congr (CFSG.pCore 2 ↥I')
      (CFSG.pCore 2 ↥(I'.map (MulAut.conj g).toMonoidHom)) e he
    refine CFSG.LocalCores.isQuasisimple_of_surjective hq e'.toMonoidHom e'.surjective ?_
    intro z hz
    have h1 : e' z = 1 := hz
    have h2 : z = 1 := e'.injective (by rw [h1, map_one])
    rw [h2]
    exact Subgroup.one_mem _

theorem le_normalizer_sSup_qs (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer
      ((sSup {I' : Subgroup G | quasithinIsCComponent I' Y ∧
        CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I')} : Subgroup G) : Set G) := by
  intro g hg
  apply A4.mem_normalizer_of_conj_mem
  intro x hx
  have hle : sSup {I' : Subgroup G | quasithinIsCComponent I' Y ∧
      CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I')} ≤
      (sSup {I' : Subgroup G | quasithinIsCComponent I' Y ∧
        CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I')}).comap (MulAut.conj g).toMonoidHom :=
    sSup_le fun I' hI' => by
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (isCComponent_conj_and_quasisimple hg hI'.1 hI'.2)
  simpa [MulAut.conj_apply] using hle hx

variable {T L I : Subgroup G} {n : ℕ}

theorem stmt11_5_6_four_of' (hF : SecA.NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {V₁ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X)
    (h3 : ∀ I' : Subgroup G, quasithinIsCComponent I' (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) →
      CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I') →
      ⁅I', X⁆ ≤ pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) :
    ∀ P : Subgroup G, P = ⁅P, X⁆ → P ≤ T →
      (frattini ↥P).map P.subtype ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) →
      ⁅P, Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))⁆ ≤
        pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) := by
  intro P hPX hPT hΦ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := Subgroup.normalizer (V₁ : Set G) with hG₁def
  set Y := Subgroup.centralizer (V₁ : Set G) ⊓
    sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) with hYdef
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  have hTG : T ≤ G₁ := SecA.IsVi.le_normalizer hV₁
  have hYG : Y ≤ G₁ := inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
  have hYN : G₁ ≤ Subgroup.normalizer (Y : Set G) := normalizer_le_normalizer_Y L V₁
  have hXG : X ≤ G₁ := cartan_le_normalizer_V₁ hF h1102 h hV₁ hX
  have hYO : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hNYO : G₁ ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hOY : pCoreOf 2 Y ≤ pCoreOf 2 G₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYG)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYG)).mpr hNYO)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  set N := sSup {I' : Subgroup G | quasithinIsCComponent I' Y ∧
    CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I')} with hNdef
  have hNY : N ≤ Y := sSup_le fun I' hI' => A3.subnormal_le hI'.1.2.2.1
  have hNN : G₁ ≤ Subgroup.normalizer (N : Set G) := hYN.trans (le_normalizer_sSup_qs Y)
  have hA : ⁅N, X⁆ ≤ pCoreOf 2 Y :=
    commutator_sSup_le (hNY.trans hYO) fun I' hI' => h3 I' hI'.1 hI'.2
  have hXsc : X ≤ sectionCentralizer N (pCoreOf 2 Y) := fun x hx => by
    refine ⟨hNN (hXG hx), hNYO (hXG hx), fun a ha => ?_⟩
    have := Subgroup.commutator_le.mp hA a ha x hx
    have e : x * a * x⁻¹ * a⁻¹ = ⁅a, x⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.inv_mem _ this
  have hPsc : P ≤ sectionCentralizer N (pCoreOf 2 Y) := by
    rw [hPX]
    refine Subgroup.commutator_le.mpr fun p hp x hx => ?_
    have hpN := mem_normalizer_sectionCentralizer (X := N) (K := pCoreOf 2 Y)
      (hNN (hTG (hPT hp))) (hNYO (hTG (hPT hp)))
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hpN x).mp (hXsc hx))
      (Subgroup.inv_mem _ (hXsc hx))
  have hPN : ⁅P, N⁆ ≤ pCoreOf 2 G₁ := by
    refine Subgroup.commutator_le.mpr fun p hp y hy => hOY ?_
    rw [commutatorElement_def]
    exact (hPsc hp).2.2 y hy
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, E ≤ G₁ → IsElemAbelian p E →
      ∀ r, Nat.card E = p ^ r → r ≤ 2 := fun p hp hp2 E hE hEab r hr =>
    le_two_of_elemAbelian h.fsu.qtke.2.2 (SecA.IsVi.ne_bot h hV₁ le_rfl) (hT2.to_le hV₁T) hp hp2
      hE hEab hr
  have hIN : ∀ I' ∈ cComp Y, CFSG.IsQuasisimple (↥I' ⧸ CFSG.pCore 2 ↥I') → I' ≤ N :=
    fun I' hI' hq => le_sSup ⟨hI', hq⟩
  have hPY' := commutator_le_pCoreOf_of_components hrank hYG hYN hXG hX.2.1 (hPT.trans hTG)
    (hT2.to_le hPT) hPX.symm hΦ fun I' hI' hq =>
      (Subgroup.commutator_mono le_rfl (hIN I' hI' hq)).trans hPN
  have hPYY : ⁅P, Y⁆ ≤ Y := Subgroup.commutator_le.mpr fun p hp y hy => by
    have hpY : p ∈ Subgroup.normalizer (Y : Set G) := hYN (hTG (hPT hp))
    rw [commutatorElement_def]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hpY y).mp hy) (Y.inv_mem hy)
  have hle : pCoreOf 2 G₁ ⊓ Y ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun y hy =>
        mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₁ (hYG hy))
          (Subgroup.le_normalizer hy))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁).to_le inf_le_left)
  exact (le_inf hPY' hPYY).trans hle

end CFSG.Quasithin.Vol2.Ch11.SecD
