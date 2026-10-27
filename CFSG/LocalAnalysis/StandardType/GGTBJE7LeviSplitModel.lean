module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplitModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem exists_conj_torusPow_range_e7
    {X : Type} [Group X] {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : p ∣ Nat.card Fq - 1)
    (e : X ≃* adjointGroup .E7 Fq) {E : Subgroup (adjointGroup .E7 Fq)}
    (hEel : IsElemAbelian p E) (hEcard : p ^ 7 ≤ Nat.card E) {A : Subgroup (MulAut X)}
    (hA : A.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq))) :
    ∃ f : X ≃* adjointGroup .E7 Fq,
      A.map (MulAut.congr f).toMonoidHom =
        (TableBExc.torusPow .E7 Fq p).map
          (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := E7SplitTorus.exists_conj_torusPow (K := Fq) hp hp2 hq E hEel hEcard
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hcomp : MulAut.congr (e.trans (MulAut.conj g)) =
      (MulAut.congr e).trans (MulAut.congr (MulAut.conj g)) := by
    apply MulEquiv.ext
    intro x
    apply MulEquiv.ext
    intro y
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hhom : ((MulAut.congr e).trans (MulAut.congr (MulAut.conj g))).toMonoidHom =
      (MulAut.congr (MulAut.conj g)).toMonoidHom.comp (MulAut.congr e).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, hhom, ← Subgroup.map_map, hA, Subgroup.map_map, ← hg, Subgroup.map_map]
  exact congrArg (fun h => E.map h)
    (MonoidHom.ext fun x => congr_conj (MulAut.conj g) x)

private theorem largeEvenLabelAll_torusLift_e7Split
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll (⟨.E7, 0, n⟩ : LargeEvenLabel) fun R _ _ _ => GGTorusLift p 7 R := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', TableBExc.ggTorusLift_E7 hp hp2 hpq⟩

theorem ggE7Split_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ e : ↥L ≃* adjointGroup .E7 Fq,
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          (TableBExc.torusPow .E7 Fq p).map
            (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn
  have hml : LargeEvenMarking ↥L (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.1
  obtain ⟨hLperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hml
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    largeEvenLabelAll_torusLift_e7Split hp hp2 hpn _ hL
  have hlift : GGTorusLift p 7 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 7 ≤ Nat.card (ggGamma L hNmark).range :=
    (card_range_ggGamma_bstar_ge hH.1 hLperf θ hNmark hlift).1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggE7_model hRig hΛ hH.2.2.1.1 hL
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e7Levi_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨f, hf⟩ := exists_conj_torusPow_range_e7 hp2 hq e hEel hEcard hArange
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, f, hf⟩

theorem ggE7Split_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ e : ↥K ≃* adjointGroup .E7 Fq,
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          (TableBExc.torusPow .E7 Fq p).map
            (MulAut.conj : adjointGroup .E7 Fq →* MulAut (adjointGroup .E7 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmk : LargeEvenMarking ↥K (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hmk
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    largeEvenLabelAll_torusLift_e7Split hp hp2 hpn _ hK
  have hlift : GGTorusLift p 7 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 7 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggE7_model hRig hΛ (hH.2.2.1.2 y K hnb) hK
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e7Levi_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨f, hf⟩ := exists_conj_torusPow_range_e7 hp2 hq e hEel hEcard hArange
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, f, hf⟩

theorem e7Split_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K)
      (n : Fin Tag.E7.rank → adjointGroup .E7 K),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = TableBExc.torusPow .E7 K p ∧
      (∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .E7 K) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer ((TableBExc.torusPow .E7 K p) : Set (adjointGroup .E7 K)),
        ∃ v : WeylGroup .E7, ∀ s,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) ∧
      ∃ wt : GGTorusTorWit (Nat.card K - 1) 7 (adjointGroup .E7 K)
          ((TableBExc.torusPow .E7 K p).map
            (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))),
        (∀ k, wt.n k = n k) ∧ wt.Holds CartanMatrix.E₇ CoxeterMatrix.E₇ := by
  classical
  have hp : p.Prime := Fact.out
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hfull : ∀ a : Fin Tag.E7.rank → Kˣ,
      rootDiagUnit .E7 a ∈ torusGroup .E7 K :=
    fun a => TableBExc.full_of_E7_E8 (Or.inl rfl) a
  let ι := ExcFrames.frameHom hfull ζ hζ (1 : adjointGroup .E7 K)
  have hιcoe : ∀ s : Fin Tag.E7.rank → ZMod p,
      (ι (Multiplicative.ofAdd s) : ModGL .E7 K) = ExcFrames.frameDiag ζ hζ s := by
    intro s
    simp only [ι, ExcFrames.coe_frameHom, Subgroup.coe_one, inv_one, one_mul, mul_one]
  have hdet : IsUnit ((Tag.E7.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inl rfl)) hp2
  have hι : Function.Injective ι := by
    intro s t h
    have hco := congrArg Subtype.val h
    rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, hιcoe, hιcoe] at hco
    exact Multiplicative.toAdd.injective (ExcFrames.frameDiag_injective hζo hζ hdet hco)
  have hrange : ι.range = TableBExc.torusPow .E7 K p := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      apply ExcFrames.mem_torusPow_iff_coe.mpr
      rw [← ofAdd_toAdd s, hιcoe]
      exact ExcFrames.frameDiag_mem hfull ζ hζ _
    · intro hg
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet
        (ExcFrames.mem_torusPow_iff_coe.mp hg)
      exact ⟨Multiplicative.ofAdd s, Subtype.ext ((hιcoe s).trans hs)⟩
  let n := E7SplitTorus.simpleRep (K := K)
  have hsimple : ∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s)) := by
    intro k s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe, n, E7SplitTorus.simpleRep]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ (simple .E7 k) s
  have hnorm : ∀ g ∈ Subgroup.normalizer
      ((TableBExc.torusPow .E7 K p) : Set (adjointGroup .E7 K)),
      ∃ w : WeylGroup .E7, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p w s)) := by
    intro g hg
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes
      (Subgroup.mem_normalizer_iff.mp hg)
    refine ⟨w, fun s => ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe]
    rw [hw _ (ExcFrames.frameDiag_mem hfull ζ hζ s)]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ w s
  refine ⟨ζ, hζ, ι, n, hζo, hι, hrange, hιcoe, hsimple, hnorm, ?_⟩
  have hC : Tag.E7.cartan = CartanMatrix.E 7 := cartanE_eq 7
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    FrameRoute.coxeterE7_eq.symm
  have hCsymm : (Tag.E7.cartan).IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 7
  obtain ⟨l⟩ := E8SplitTorus.exists_rootValue_equiv (K := K)
  let φ := E7SplitTorus.coordHom (K := K)
  let E := TableBExc.torusPow .E7 K p
  have hnformula : ∀ k (a : Fin Tag.E7.rank → Kˣ),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.E7.cartan.transpose k (a k)))⁻¹ := by
    intro k a
    rw [hCsymm.eq]
    exact E7SplitTorus.simple_conj_coordHom k a
  have hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range :=
    fun g => E7SplitTorus.mem_torusPow_iff g
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hsimple hnorm
  have hm : Odd (Nat.card K - 1) := by
    let : Fintype K := Fintype.ofFinite K
    have hEven : Even (Nat.card K) := by
      rw [Nat.even_iff, Nat.card_eq_fintype_card]
      exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
    obtain ⟨k, hk⟩ := hEven
    have hpos : 1 < Nat.card K := Finite.one_lt_card
    exact ⟨k - 1, by omega⟩
  have hdetq : IsUnit ((Tag.E7.cartan.det : ℤ) : ZMod (Nat.card K - 1)) := by
    rw [det_cartan_E7]
    simpa using (ZMod.isUnit_iff_coprime 2 (Nat.card K - 1)).mpr
      (Nat.coprime_two_left.mpr hm)
  obtain ⟨B, hCB', hBC'⟩ := exists_int_matrix_inverse_mod_of_isUnit_det Tag.E7.cartan hdetq
  obtain ⟨w, -, -, -, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod l φ E7SplitTorus.coordHom_injective
      Tag.E7.cartan B hCB' hBC' center_adjointGroup_eq_bot E hE ζ hζ hζ1 n hnA hnformula
      (E7SplitTorus.centralizer_le_range hp hp2 hq)
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .E7)) ρ hρ hρrange hρsimple
  refine ⟨w, hwn, ?_⟩
  rw [hM] at hwh
  simpa only [hC, Tag.rank] using hwh

end CFSG.StandardType

end
