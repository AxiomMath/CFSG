module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

private theorem exists_conj_torusPow_range
    {X : Type} [Group X] {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : p ∣ Nat.card Fq - 1)
    (e : X ≃* adjointGroup .E8 Fq) {E : Subgroup (adjointGroup .E8 Fq)}
    (hEel : IsElemAbelian p E) (hEcard : p ^ 8 ≤ Nat.card E) {A : Subgroup (MulAut X)}
    (hA : A.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq))) :
    ∃ f : X ≃* adjointGroup .E8 Fq,
      A.map (MulAut.congr f).toMonoidHom =
        (TableBExc.torusPow .E8 Fq p).map
          (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)) := by
  have hp : p.Prime := Fact.out
  have hT : GGExcToralRankInput .E8 Fq p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact ggE8ThreeToralRankInput_holds Fq hq
    · exact ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hq
  obtain ⟨g, hg⟩ := hT E hEel (by simpa only [Tag.rank] using hEcard)
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

private theorem largeEvenLabelAll_torusLift_e8Split
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll (⟨.E8, 0, n⟩ : LargeEvenLabel) fun R _ _ _ => GGTorusLift p 8 R := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', TableBExc.ggTorusLift_E8 hp hp2 hpq⟩

theorem ggE8Split_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ e : ↥L ≃* adjointGroup .E8 Fq,
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          (TableBExc.torusPow .E8 Fq p).map
            (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)) := by
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
    largeEvenLabelAll_torusLift_e8Split hp hp2 hpn _ hL
  have hlift : GGTorusLift p 8 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 8 ≤ Nat.card (ggGamma L hNmark).range :=
    (card_range_ggGamma_bstar_ge hH.1 hLperf θ hNmark hlift).1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggMaxRank_model hRig hΛ hH.2.2.1.1 hL
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨f, hf⟩ := exists_conj_torusPow_range hp2 hq e hEel hEcard hArange
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, f, hf⟩

theorem ggE8Split_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ e : ↥K ≃* adjointGroup .E8 Fq,
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          (TableBExc.torusPow .E8 Fq p).map
            (MulAut.conj : adjointGroup .E8 Fq →* MulAut (adjointGroup .E8 Fq)) := by
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
    largeEvenLabelAll_torusLift_e8Split hp hp2 hpn _ hK
  have hlift : GGTorusLift p 8 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 8 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggMaxRank_model hRig hΛ (hH.2.2.1.2 y K hnb) hK
  obtain ⟨E, hEel, hEcard, hEsc, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨f, hf⟩ := exists_conj_torusPow_range hp2 hq e hEel hEcard hArange
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, f, hf⟩

theorem e8Split_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
      (n : Fin Tag.E8.rank → adjointGroup .E8 K),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = TableBExc.torusPow .E8 K p ∧
      (∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .E8 K) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer ((TableBExc.torusPow .E8 K p) : Set (adjointGroup .E8 K)),
        ∃ v : WeylGroup .E8, ∀ s,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) ∧
      ∃ wt : GGTorusTorWit (Nat.card K - 1) 8 (adjointGroup .E8 K)
          ((TableBExc.torusPow .E8 K p).map
            (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))),
        (∀ k, wt.n k = n k) ∧ wt.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ := by
  classical
  have hp : p.Prime := Fact.out
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hfull : ∀ a : Fin Tag.E8.rank → Kˣ,
      rootDiagUnit .E8 a ∈ torusGroup .E8 K :=
    CFSG.RankThree.PartOne.KE.rootDiagUnit_E8_mem_torusGroup
  let ι := ExcFrames.frameHom hfull ζ hζ (1 : adjointGroup .E8 K)
  have hιcoe : ∀ s : Fin Tag.E8.rank → ZMod p,
      (ι (Multiplicative.ofAdd s) : ModGL .E8 K) = ExcFrames.frameDiag ζ hζ s := by
    intro s
    simp only [ι, ExcFrames.coe_frameHom, Subgroup.coe_one, inv_one, one_mul, mul_one]
  have hdet : IsUnit ((Tag.E8.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2
  have hι : Function.Injective ι := by
    intro s t h
    have hco := congrArg Subtype.val h
    rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, hιcoe, hιcoe] at hco
    exact Multiplicative.toAdd.injective (ExcFrames.frameDiag_injective hζo hζ hdet hco)
  have hrange : ι.range = TableBExc.torusPow .E8 K p := by
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
  let n := E8SplitTorus.simpleRep (K := K)
  have hsimple : ∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s)) := by
    intro k s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe, n, E8SplitTorus.simpleRep]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ (simple .E8 k) s
  have hnorm : ∀ g ∈ Subgroup.normalizer
      ((TableBExc.torusPow .E8 K p) : Set (adjointGroup .E8 K)),
      ∃ w : WeylGroup .E8, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p w s)) := by
    intro g hg
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes
      (Subgroup.mem_normalizer_iff.mp hg)
    refine ⟨w, fun s => ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe]
    rw [hw _ (ExcFrames.frameDiag_mem hfull ζ hζ s)]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ w s
  refine ⟨ζ, hζ, ι, n, hζo, hι, hrange, hιcoe, hsimple, hnorm, ?_⟩
  have hC : Tag.E8.cartan = CartanMatrix.E₈ := cartanE_eq 8
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    FrameRoute.coxeterE8_eq.symm
  have hBC : CFSG.RankThree.PartOne.KE.cartanInvE8 * Tag.E8.cartan = 1 :=
    CFSG.RankThree.PartOne.KE.cartanInvE8_mul
  have hCB : Tag.E8.cartan * CFSG.RankThree.PartOne.KE.cartanInvE8 = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.E8.rank))).mp hBC
  have hCsymm : (Tag.E8.cartan).IsSymm := hC.symm ▸ CartanMatrix.E_isSymm 8
  obtain ⟨l⟩ := E8SplitTorus.exists_rootValue_equiv (K := K)
  let φ := E8SplitTorus.coordHom (K := K)
  let E := TableBExc.torusPow .E8 K p
  have hnformula : ∀ k (a : Fin Tag.E8.rank → Kˣ),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.E8.cartan.transpose k (a k)))⁻¹ := by
    intro k a
    rw [hCsymm.eq]
    exact E8SplitTorus.simple_conj_coordHom k a
  have hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range :=
    fun g => E8SplitTorus.mem_torusPow_iff g
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hsimple hnorm
  obtain ⟨w, -, -, -, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod
      l φ E8SplitTorus.coordHom_injective Tag.E8.cartan
      CFSG.RankThree.PartOne.KE.cartanInvE8 (by rw [hCB, map_one])
      (by rw [hBC, map_one]) center_adjointGroup_eq_bot E hE ζ hζ hζ1 n hnA hnformula
      (E8SplitTorus.centralizer_le_range hp hp2 hq)
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)) ρ hρ hρrange hρsimple
  refine ⟨w, hwn, ?_⟩
  rw [hM] at hwh
  simpa only [hC, Tag.rank] using hwh

end CFSG.StandardType

end
