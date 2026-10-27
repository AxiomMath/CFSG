module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankTwE6
public import CFSG.LocalAnalysis.StandardType.GGOrdPFieldConjAtExc
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutInduces
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Torus
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6
public import CFSG.LieType.SeitzGeneration.TwE6SubfieldInndiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTwField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.TwE6Subfield CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TwE6FieldCore
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley ExcFrames
open CFSG.Open (IsElemAbelian)

namespace LayerSixE

theorem ggPsiInnerDiag_of_induces_twistedE6
    {f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπ : Function.Surjective π)
    (hπval : ∀ z,
      ((π z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f))
          (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {G : Type} [Group G] (ψ : twistedE6Group 2 f →* G) (hkπ : ψ.ker ≤ π.ker) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G))
    {α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hα : GGInduces π ψ c α) (hαD : α ∈ twInndiagAut f) :
    GGPsiInnerDiag (twistedE6Datum 2 f) ψ c := by
  classical
  have hπker : π.ker ≤ Subgroup.center (twistedE6Group 2 f) :=
    RootDetectTwE6.ker_le_center f π hπval
  have hodd : Odd (Nat.card π.ker) := RootDetectTwE6.odd_card_ker f π hπval
  have hαinv : GGInduces π ψ c⁻¹ α⁻¹ := hα.inv
  have hαinvD : α⁻¹ ∈ twInndiagAut f := inv_mem hαD
  haveI : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range.Normal :=
    RootCentExc.normal_range_mulAutConj
  obtain ⟨i, hi, d, hd, hid⟩ := Subgroup.mem_sup_of_normal_left.1 hαinvD
  obtain ⟨w, rfl⟩ := hi
  obtain ⟨b, rfl⟩ := hd
  have hb : ∀ i, (b : Fin 6 → (GaloisField 2 (2 * f))ˣ) (rhoPerm i) =
      Units.map (frobQ 2 f : GaloisField 2 (2 * f) →* GaloisField 2 (2 * f))
        ((b : Fin 6 → (GaloisField 2 (2 * f))ˣ) i) := by
    intro i
    exact (TableB.TwE6.mem_compat (K := GaloisField 2 (2 * f)) (frobQ 2 f)).1 b.2 i
  obtain ⟨a₀, ha₀⟩ := hπ w
  have hdiag : ∀ δ ∈ (twistedE6Datum 2 f).roots, ∃ h ∈ ggTorus (twistedE6Datum 2 f),
      ∀ z ∈ (twistedE6Datum 2 f).rootGroup δ,
        ((π (h * z * h⁻¹) : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
          rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ) *
            ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
              ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
            (rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ))⁻¹ := by
    intro δ hδ
    obtain ⟨h, hh, hz⟩ :=
      RootDetectTwE6.hdiag_twisted (frobQ 2 f) (frobQ_frobQ 2 f hf)
        (b : Fin 6 → (GaloisField 2 (2 * f))ˣ) hb δ hδ
    exact ⟨h, hh, fun z hz' => by
      rw [hπval (h * z * h⁻¹), hπval z]
      exact hz z hz'⟩
  refine MpStdE6.ggPsiInnerDiag_of_conj_diag (twistedE6Datum 2 f) hπker hodd
    (RootDetectTwE6.twistedRootGroup_mul_self f)
    (b : Fin 6 → (GaloisField 2 (2 * f))ˣ) hdiag hcN a₀ ?_
  intro y y' h
  have h1 : π y' = α⁻¹ (π y) := hαinv y y' (by simpa using h)
  have h1' : ((π y' : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((α⁻¹ (π y) : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    congrArg (fun z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) => (z : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) h1
  rw [h1', ← hid]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    RootCentExc.coe_compatParamAut_apply]
  rw [show ((w : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
    ((π a₀ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) from (congrArg Subtype.val ha₀).symm]
  group

end LayerSixE

namespace ExcFieldAutCentRankTwE6Three

theorem three_dvd_card_sub_one {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) :
    3 ∣ Nat.card (GaloisField 2 (2 * f)) - 1 := by
  have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    generalize 2 ^ f = m at h1 ⊢
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    omega
  rw [hcard, h]
  exact Dvd.dvd.mul_right h3 _

theorem card_le_three_pow_six
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    {Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))} (hY : IsElemAbelian 3 Y) (hYD : Y ≤ LayerSixE.twInndiagAut f) :
    Nat.card Y ≤ 3 ^ 6 := by
  have hX := NoOffTwE6Three.isElemAbelian_twLift hf hYD hY
  have hcard := NoOffTwE6Three.card_twLift hf hYD
  have hXI := NoOffTwE6Three.twLift_le_hatAut_range hf Y
  have hbound :=
    (TableBExc.E6Three.card_le_and_normalizes_of_le_hatAut
      (three_dvd_card_sub_one hf h3) hX hXI).1
  rwa [hcard] at hbound

theorem exists_elemAbelian_fixed_fieldActor_lower
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {η : K ≃+* K}
    (hηp : η ^ p = 1) (hη1 : η ≠ 1) (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = e) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧
      (∀ x ∈ E, fieldActor (t := TwistTag.E6) σ η x = x) ∧
      p ^ (degCountTw e - 1) ≤ Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hK2 : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, Nat.mul_comm]
  have hcord : orderOf η = p := orderOf_eq_prime hηp hη1
  have hoddp : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hpdvd, hKfix⟩ := fixSubfield_card_of_odd hf hK η (by rw [hcord]; exact hoddp)
  rw [hcord] at hpdvd hKfix
  have hfdiv : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos
  haveI : Finite (fixSubfield η) :=
    Finite.of_injective (Subtype.val : fixSubfield η → K) Subtype.val_injective
  haveI : CharP (fixSubfield η) 2 := Subfield.charP (fixSubfield η) 2
  have hσfix : ∀ c : ↥(fixSubfield η), fixSubfieldRestrict σ η c = c ^ (2 ^ (f / p)) := by
    refine fixSubfieldRestrict_eq_pow hKfix hoddp ?_
    intro c
    rw [hσ, show (f / p) * p = f from Nat.div_mul_cancel hpdvd]
  have hefix : orderOf (((2 ^ (f / p) : ℕ)) : ZMod p) =
      orderOf (((2 ^ f : ℕ)) : ZMod p) := by
    have hcast : (((2 ^ f : ℕ)) : ZMod p) = (((2 ^ (f / p) : ℕ)) : ZMod p) := by
      conv_lhs => rw [show f = (f / p) * p from (Nat.div_mul_cancel hpdvd).symm]
      rw [pow_mul, Nat.cast_pow, ZMod.pow_card]
    rw [hcast]
  obtain ⟨E₀, hE₀, hE₀card⟩ :=
    exists_twistedE6 (ℓ := 2) (f := f / p) (K := ↥(fixSubfield η)) (e := e) Nat.prime_two hfdiv
      hKfix (fixSubfieldRestrict σ η) hσfix hp hp2 (by rw [← he]; exact hefix)
  let φ : (↥(twistedE6RootGroup (↥(fixSubfield η)) (fixSubfieldRestrict σ η))) →*
      twistedE6RootGroup K σ :=
    (twFJ σ η).subtype.comp (twFJModelEquiv σ η).toMonoidHom
  have hφinj : Function.Injective φ := fun a b hab =>
    (twFJModelEquiv σ η).injective (Subtype.ext hab)
  refine ⟨E₀.map φ, hE₀.map φ, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (mem_fixedSubgroup (α := fieldActor (t := TwistTag.E6) σ η)).1
      (twFJ_le_twR σ η (twFJModelEquiv σ η y).2)
  · rw [Subgroup.card_map_of_injective hφinj]
    exact hE₀card

theorem card_bstar_le
    {G : Type} [Group G] {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hS : GGSixFusionSetting 3 Bs G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (h3 : 3 ∣ 2 ^ f + 1) : Nat.card Bs ≤ 3 ^ 6 := by
  classical
  have hpres : GGPresentsG0 G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ := hS.presents
  have hrange : ψ.range = G₀ := hS.range_eq
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K := hpres.2.1.2
  have hCψ : Subgroup.centralizer (G₀ : Set G) = ⊥ := hS.centralizer_eq_bot
  have hCψ' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hCψ
  let ψ₂ : twistedE6Group 2 f →* G := ψ
  have hrange₂ : ψ₂.range = G₀ := hrange
  have hCψ₂ : Subgroup.centralizer (ψ₂.range : Set G) = ⊥ := by rw [hrange₂]; exact hCψ
  have hker₂ : ψ₂.ker ≤ Subgroup.center (twistedE6Group 2 f) := hker
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ₂.ker ≤ π.ker := hπker ▸ hker₂
  have hkerEq : ψ₂.ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hπker]
    intro z hz
    have hz' : z ∈ Subgroup.center (twistedE6Group 2 f) := hz
    rw [MonoidHom.mem_ker]
    have h : ψ₂ z ∈ Subgroup.centralizer (ψ₂.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz' u]
    rw [hCψ₂, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχinj, hχrange, hval⟩ :=
    NormalizerAut.exists_injective_factor_of_surjective hπ hkerEq
  have hM : Bs ≤ Subgroup.normalizer (χ.range : Set G) := by
    rw [hχrange, hrange₂]
    exact hS.bstar_le
  let Φ : Bs →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) := NormalizerAut.normAutOn χ hχinj hM
  have hΦinj : Function.Injective Φ :=
    NormalizerAut.normAutOn_injective χ hχinj hM (by rw [hχrange]; exact hCψ₂)
  have hinner₂ : ∀ b ∈ Bs, GGPsiInnerDiag (twistedE6Datum 2 f) ψ₂ b := hS.innerDiag
  have hΦD : ∀ b : Bs, Φ b ∈ LayerSixE.twInndiagAut f := by
    intro b
    have hbN : (b : G) ∈ Subgroup.normalizer (ψ₂.range : Set G) := by
      rw [hrange₂]; exact hS.bstar_le b.2
    obtain ⟨α, hαD, hα⟩ :=
      LayerSixE.exists_induces_twistedE6 hf hπval ψ₂ hker₂ hkπ hbN (hinner₂ b b.2)
    have hind := NormalizerAut.ggInduces_normAutOn (π := π) (ψ := ψ₂) χ hχinj hval hM b
    have huniq := LayerSixE.GGInduces.unique hπ hbN hind hα
    rw [huniq]
    exact hαD
  have hElemTop : IsElemAbelian 3 (⊤ : Subgroup Bs) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact hS.elem.1.is_comm.comm a.1 b.1
    · exact hS.elem.2 x x.2
  have hBsD : (⊤ : Subgroup Bs).map Φ ≤ LayerSixE.twInndiagAut f := by
    rintro _ ⟨b, -, rfl⟩
    exact hΦD b
  have hBscard : Nat.card ((⊤ : Subgroup Bs).map Φ) = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective hΦinj, Subgroup.card_top]
  rw [← hBscard]
  exact card_le_three_pow_six hf h3 (hElemTop.map Φ) hBsD

theorem exists_elemAbelian_centralizing_of_not_mem_twInndiag
    {f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G]
    {χ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G}
    (hχinj : Function.Injective χ) {y : G}
    {α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hαeq : ∀ u, χ (α u) = y * χ u * y⁻¹) (hαp : α ^ 3 = 1)
    (hαnotD : α ∉ LayerSixE.twInndiagAut f) (h3 : 3 ∣ 2 ^ f + 1) :
    ∃ E₀ : Subgroup G, E₀ ≤ χ.range ∧ IsElemAbelian 3 E₀ ∧
      (∀ x ∈ E₀, y * x = x * y) ∧ 3 ^ 5 ≤ Nat.card E₀ := by
  classical
  let σ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) := frobQEquiv hf
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hK2 : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) := by
    rw [hK, ← pow_mul, Nat.mul_comm]
  have htw : LayerSixE.twInndiagAut f = twistedE6Inn (GaloisField 2 (2 * f)) σ ⊔
      twistedE6Diag (GaloisField 2 (2 * f)) σ := by
    rw [LayerSixE.twInndiagAut,
      ← NoOffTwE6Three.range_compatParamAut_eq_twistedE6Diag (K := GaloisField 2 (2 * f)) σ]
    rfl
  have hαo : α ∉ twistedE6Inn (GaloisField 2 (2 * f)) σ ⊔
      twistedE6Diag (GaloisField 2 (2 * f)) σ := by
    intro hmem
    exact hαnotD (htw.symm ▸ hmem)
  let α_σ : MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) σ) := α
  have hαp_σ : α_σ ^ 3 = 1 := hαp
  have hαo_σ : α_σ ∉ twistedE6Inn (GaloisField 2 (2 * f)) σ ⊔
      twistedE6Diag (GaloisField 2 (2 * f)) σ := hαo
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, -, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK σ hσ
  obtain ⟨hηo, -, ψ', hψ'⟩ :=
    exists_conj_fieldActor_of_not_mem_twistedE6Inndiag Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK2 σ hσ Θ hΘ Nat.prime_three (by norm_num) hαp_σ hαo_σ
  set η : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) := Θ α_σ with hηdef
  have hηp : η ^ 3 = 1 := by rw [hηdef, ← map_pow, hαp_σ, map_one]
  have hη1 : η ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hηo
    omega
  have he2 : orderOf (((2 ^ f : ℕ)) : ZMod 3) = 2 := by
    have h1 : (((2 ^ f + 1 : ℕ)) : ZMod 3) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact h3
    have h2 : (((2 ^ f : ℕ)) : ZMod 3) = -1 := by
      have h1' : (((2 ^ f : ℕ)) : ZMod 3) + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using h1
      exact eq_neg_of_add_eq_zero_left h1'
    rw [h2]
    exact orderOf_eq_prime (by decide) (by decide)
  obtain ⟨E, hE, hEfix, hEcard⟩ :=
    exists_elemAbelian_fixed_fieldActor_lower (p := 3) (e := 2)
      hf (GaloisField 2 (2 * f)) hK σ hσ Nat.prime_three (by norm_num) hηp hη1 he2
  have hdeg : degCountTw 2 = 6 := by
    rw [degCountTw, show ennola 2 = 1 from by decide]
    decide
  have hEcard' : 3 ^ 5 ≤ Nat.card E := by simpa [hdeg] using hEcard
  let E₁ : Subgroup (twistedE6RootGroup (GaloisField 2 (2 * f)) σ) := E.map ψ'⁻¹.toMonoidHom
  have hE₁ : IsElemAbelian 3 E₁ := hE.map ψ'⁻¹.toMonoidHom
  have hE₁card : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective ψ'⁻¹.injective
  have hE₁fix : ∀ u ∈ E₁, α_σ u = u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ψ'.injective ?_
    have h4 : (ψ' * α_σ * ψ'⁻¹) v = v := by rw [hψ']; exact hEfix v hv
    simpa [MulAut.mul_apply] using h4
  have hαeq₂ : ∀ u : twistedE6RootGroup (GaloisField 2 (2 * f)) σ,
      χ (α_σ u) = y * χ u * y⁻¹ := fun u => hαeq u
  let E₀ : Subgroup G := E₁.map χ
  have hE₀ : IsElemAbelian 3 E₀ := hE₁.map χ
  have hE₀card : Nat.card E₀ = Nat.card E₁ := Subgroup.card_map_of_injective hχinj
  have hE₀le : E₀ ≤ χ.range := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  have hE₀comm : ∀ u ∈ E₀, y * u = u * y := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 := hαeq₂ v
    rw [hE₁fix v hv] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  refine ⟨E₀, hE₀le, hE₀, hE₀comm, ?_⟩
  rw [hE₀card, hE₁card]
  exact hEcard'

end ExcFieldAutCentRankTwE6Three

theorem ggExcFieldAutCentRankTwE6Three_holds :
    GGExcFieldAutCentRankTwE6Three := by
  intro G _ _ p Bs G₀ n f ψ hS hp3 h3 y hyM hyp hdf hni
  subst p
  classical
  have hpres : GGPresentsG0 G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ := hS.presents
  have hrange : ψ.range = G₀ := hS.range_eq
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K := hpres.2.1.2
  have hCψ : Subgroup.centralizer (G₀ : Set G) = ⊥ := hS.centralizer_eq_bot
  have hCψ' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hCψ
  let ψ₂ : twistedE6Group 2 f →* G := ψ
  have hrange₂ : ψ₂.range = G₀ := hrange
  have hCψ₂ : Subgroup.centralizer (ψ₂.range : Set G) = ⊥ := by rw [hrange₂]; exact hCψ
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ₂.ker ≤ π.ker := hπker ▸ hker
  have hkerEq : ψ₂.ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hπker]
    intro z hz
    have hz' : z ∈ Subgroup.center (twistedE6Group 2 f) := hz
    rw [MonoidHom.mem_ker]
    have h : ψ₂ z ∈ Subgroup.centralizer (ψ₂.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz' u]
    rw [hCψ₂, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχinj, hχrange, hval⟩ :=
    NormalizerAut.exists_injective_factor_of_surjective hπ hkerEq
  have hχrange₂ : χ.range = ψ₂.range := hχrange
  have hval₂ : ∀ y, χ (π y) = ψ₂ y := hval
  have hBsbound : Nat.card Bs ≤ 3 ^ 6 := ExcFieldAutCentRankTwE6Three.card_bstar_le hS h3
  have hyN : y ∈ Subgroup.normalizer (χ.range : Set G) := by
    rw [hχrange₂, hrange₂]; exact hyM
  obtain ⟨α, hαeq⟩ := ExcFieldAutCentRankF4.exists_aut_of_mem_normalizer χ hχinj hyN
  have hαk : ∀ (k : ℕ) u, χ ((α ^ k) u) = y ^ k * χ u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih => intro u; rw [pow_succ', MulAut.mul_apply, hαeq, ih]; group
  have hyp1 : y ^ 3 = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hαp : α ^ 3 = 1 := by
    refine MulEquiv.ext fun u => hχinj ?_
    rw [hαk, hyp1]
    simp
  have hαInd : LayerSixE.GGInduces π ψ₂ y α := by
    intro a a' ha
    apply hχinj
    rw [hval₂ a', hαeq (π a), hval₂ a]
    exact ha
  have hyN₂ : y ∈ Subgroup.normalizer (ψ₂.range : Set G) := by
    rw [← hχrange₂]; exact hyN
  have hαnotD : α ∉ LayerSixE.twInndiagAut f := by
    intro hαD
    exact hni (LayerSixE.ggPsiInnerDiag_of_induces_twistedE6 hf hπ hπval ψ₂
      hkπ hyN₂ hαInd hαD)
  obtain ⟨E₀, hE₀χ, hE₀, hE₀comm, hE₀card⟩ :=
    ExcFieldAutCentRankTwE6Three.exists_elemAbelian_centralizing_of_not_mem_twInndiag
      hf hχinj hαeq hαp hαnotD h3
  have hE₀le : E₀ ≤ G₀ := by
    rw [← hrange₂]
    exact hE₀χ.trans (le_of_eq hχrange₂)
  refine ⟨E₀, hE₀le, hE₀, hE₀comm, ?_⟩
  calc Nat.card Bs ≤ 3 ^ 6 := hBsbound
    _ = 3 * 3 ^ 5 := by norm_num
    _ ≤ 3 * Nat.card E₀ := Nat.mul_le_mul_left 3 hE₀card

theorem ggOrdPFieldConjAt_twistedE6_holds :
    GGOrdPFieldConjAt .twistedE6 :=
  ggOrdPFieldConjAt_twistedE6 ggExcFieldAutCentRankTwE6Three_holds

end CFSG.StandardType
