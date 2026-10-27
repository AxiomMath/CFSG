module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplitComp
public import CFSG.LocalAnalysis.StandardType.GGTBTorF4
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggF4_quotModel
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    {Bs X : Subgroup G} {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.F4, 0, n⟩)
    (hinn : GGInnerDiagOn Bs X) (hlab : GGHasLabel ⟨.F4, 0, n⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ π : ↥X →* adjointGroup .F4 K, Function.Surjective π ∧ π.ker = Subgroup.center ↥X ∧
        Group.IsPerfect ↥X ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := by
  classical
  obtain ⟨hperf, lab', _hlab', hraw'⟩ := ggInnerDiagOn_relabel hRig hinn hΛ hlab
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨_, _, hrest₀⟩ := hQ₀
  obtain ⟨_, hP₀⟩ := hrest₀
  obtain ⟨hlabeq, _, _⟩ := hP₀
  subst hlabeq
  have hInnAll : LargeEvenLabelAll ⟨.F4, 0, n⟩
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) :=
    largeEvenLabelAll_subset_inn hΛ (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨R, _instR, I, F, hQR, hguard⟩ := largeEvenRawDatum_exists (hInnAll _ hraw')
  obtain ⟨hsR, hnaR, hrest⟩ := hQR
  obtain ⟨θ, hP'⟩ := hrest
  obtain ⟨_, hBsN, hind⟩ := hP'
  have hI : I ⊆ LargeEvenInnSet R := hguard hsR hnaR
  have hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ :=
    F4AutRefl.exists_conj_of_inn hperf θ hI hBsN hind
  obtain ⟨K, _instK, _finK, hKcard, hQK⟩ := hraw'
  obtain ⟨_, _, hrestK⟩ := hQK
  obtain ⟨θ_K, _hPK⟩ := hrestK
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K .F4
  have : CharP K 2 := charP_two_of_card hKcard
  let eAd : ↥X ⧸ Subgroup.center ↥X ≃* adjointGroup .F4 K :=
    (θ_K.trans eQ).trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := .F4) (K := K))).trans QuotientGroup.quotientBot)
  let π : ↥X →* adjointGroup .F4 K :=
    eAd.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hπ : Function.Surjective π := eAd.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Subgroup.center ↥X := by
    rw [MonoidHom.ker_comp_of_injective _ _ eAd.injective, QuotientGroup.ker_mk']
  exact ⟨K, _instK, _finK, inferInstance, hKcard, π, hπ, hπker, Group.isPerfect_def.mpr hperf,
    hBsN, hinner⟩

theorem ggF4_model'
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    {Bs X : Subgroup G} {n : ℕ} (hn : 2 ≤ n ∨ Subgroup.center ↥X = ⊥)
    (hΛ : LargeEvenInLambda2 ⟨.F4, 0, n⟩)
    (hinn : GGInnerDiagOn Bs X) (hlab : GGHasLabel ⟨.F4, 0, n⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ _ : ↥X ≃* adjointGroup .F4 K, Subgroup.center ↥X = ⊥ ∧
        Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := by
  classical
  obtain ⟨K, _instK, _finK, _instChar, hKcard, π, hπ, hπker, hperf, hBsN, hinner⟩ :=
    ggF4_quotModel hRig hΛ hinn hlab
  have hbij : Function.Bijective π := by
    rcases hn with hn | hZX
    · have hK4 : 4 ≤ Nat.card K := by
        rw [hKcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      exact CFSG.LieType.Steinberg.CentralExt.f4_even_bijective_of_perfect hK4 π hπ hπker.le
    · refine ⟨?_, hπ⟩
      rw [← MonoidHom.ker_eq_bot_iff, hπker, hZX]
  have hZ : Subgroup.center ↥X = ⊥ := by
    rw [← hπker]
    exact (MonoidHom.ker_eq_bot_iff π).mpr hbij.1
  exact ⟨K, _instK, _finK, inferInstance, hKcard, MulEquiv.ofBijective π hbij, hZ, hBsN, hinner⟩

theorem ggF4_model
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    {Bs X : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hΛ : LargeEvenInLambda2 ⟨.F4, 0, n⟩)
    (hinn : GGInnerDiagOn Bs X) (hlab : GGHasLabel ⟨.F4, 0, n⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ _ : ↥X ≃* adjointGroup .F4 K, Subgroup.center ↥X = ⊥ ∧
        Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ :=
  ggF4_model' hRig (Or.inl hn) hΛ hinn hlab

private theorem f4ls_two_le {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1) :
    2 ≤ n := by
  by_contra h
  have hn1 : n = 1 := by omega
  rw [hn1] at hpn
  have h1 : p ∣ 1 := by simpa using hpn
  exact hp.ne_one (Nat.dvd_one.mp h1)

private theorem f4ls_torusPow_eq (K : Type) [Field K]
    (p : ℕ) :
    TableBF4.torusPow K p = TableBExc.torusPow .F4 K p :=
  Subgroup.ext fun _ => Iff.rfl

private theorem f4ls_exists_conj_torusPow_range
    {X : Type} [Group X] {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : p ∣ Nat.card Fq - 1)
    (e : X ≃* adjointGroup .F4 Fq) {E : Subgroup (adjointGroup .F4 Fq)}
    (hEel : IsElemAbelian p E) (hEcard : p ^ 4 ≤ Nat.card E) {A : Subgroup (MulAut X)}
    (hA : A.map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq))) :
    ∃ f : X ≃* adjointGroup .F4 Fq,
      A.map (MulAut.congr f).toMonoidHom =
        (TableBExc.torusPow .F4 Fq p).map
          (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := exists_conjugator_torusPow hp hp2 hq hEel hEcard
  rw [f4ls_torusPow_eq] at hg
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

private theorem largeEvenLabelAll_torusLift_f4Split
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll (⟨.F4, 0, n⟩ : LargeEvenLabel) fun R _ _ _ => GGTorusLift p 4 R := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', TableBF4.ggTorusLift_F4 hp hp2 hpq⟩

theorem ggF4Split_model_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ e : ↥L ≃* adjointGroup .F4 Fq,
        (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
          (TableBExc.torusPow .F4 Fq p).map
            (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn
  have hn2 : 2 ≤ n := f4ls_two_le hp hΛ.1 hpn
  have hml : LargeEvenMarking ↥L (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.1
  obtain ⟨hLperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hml
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    largeEvenLabelAll_torusLift_f4Split hp hp2 hpn _ hL
  have hlift : GGTorusLift p 4 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 4 ≤ Nat.card (ggGamma L hNmark).range :=
    (card_range_ggGamma_bstar_ge hH.1 hLperf θ hNmark hlift).1
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggF4_model hRig hn2 hΛ hH.2.2.1.1 hL
  obtain ⟨E, hEel, hEcard, -, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨f, hf⟩ := f4ls_exists_conj_torusPow_range hp2 hq e hEel hEcard hArange
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, f, hf⟩

theorem ggF4Split_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
      (_ : CharP Fq 2), Nat.card Fq = 2 ^ n ∧
      ∃ e : ↥K ≃* adjointGroup .F4 Fq,
        (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
          (TableBExc.torusPow .F4 Fq p).map
            (MulAut.conj : adjointGroup .F4 Fq →* MulAut (adjointGroup .F4 Fq)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn
  have hn2 : 2 ≤ n := f4ls_two_le hp hΛ.1 hpn
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmk : LargeEvenMarking ↥K (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
    hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, _lab', R, _instR, _I, _F, θ, _hlab', hmark⟩ :=
    largeEvenMarking_exists' hmk
  obtain ⟨hNmark, _hind⟩ := hmark
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, ⟨⟨θ₀⟩, hlift₀⟩⟩ :=
    largeEvenLabelAll_torusLift_f4Split hp hp2 hpn _ hK
  have hlift : GGTorusLift p 4 R :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 4 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  obtain ⟨Fq, _instFq, _instFin, _instChar, hFqcard, e, hZL, _hN', hinner⟩ :=
    ggF4_model hRig hn2 hΛ (hH.2.2.1.2 y K hnb) hK
  obtain ⟨E, hEel, hEcard, -, hArange⟩ :=
    e8Enn_adjointModel hH.1.2.1.2.1 hH.1.2.1.2.2.2 e hZL hinner hNmark hlb
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  obtain ⟨f, hf⟩ := f4ls_exists_conj_torusPow_range hp2 hq e hEel hEcard hArange
  exact ⟨hNmark, Fq, inferInstance, inferInstance, inferInstance, hFqcard, f, hf⟩

theorem f4Split_frame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hq : p ∣ Nat.card K - 1) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K)
      (n : Fin Tag.F4.rank → adjointGroup .F4 K),
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = TableBExc.torusPow .F4 K p ∧
      (∀ s, (ι₀ (Multiplicative.ofAdd s) : ModGL .F4 K) = ExcFrames.frameDiag ζ hζ s) ∧
      (∀ k s, n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s))) ∧
      ∃ wt : GGTorusTorWit (Nat.card K - 1) 4 (adjointGroup .F4 K)
          ((TableBExc.torusPow .F4 K p).map
            (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K))),
        (∀ k, wt.n k = n k) ∧ wt.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := by
  classical
  have hp : p.Prime := Fact.out
  have hpk : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hfull : ∀ a : Fin Tag.F4.rank → Kˣ, rootDiagUnit .F4 a ∈ torusGroup .F4 K :=
    fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a
  let ι := ExcFrames.frameHom hfull ζ hζ (1 : adjointGroup .F4 K)
  have hιcoe : ∀ s : Fin Tag.F4.rank → ZMod p,
      (ι (Multiplicative.ofAdd s) : ModGL .F4 K) = ExcFrames.frameDiag ζ hζ s := by
    intro s
    simp only [ι, ExcFrames.coe_frameHom, Subgroup.coe_one, inv_one, one_mul, mul_one]
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) hp2
  have hι : Function.Injective ι := by
    intro s t h
    have hco := congrArg Subtype.val h
    rw [← ofAdd_toAdd s, ← ofAdd_toAdd t, hιcoe, hιcoe] at hco
    exact Multiplicative.toAdd.injective (ExcFrames.frameDiag_injective hζo hζ hdet hco)
  have hrange : ι.range = TableBExc.torusPow .F4 K p := by
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
  let n : Fin Tag.F4.rank → adjointGroup .F4 K := fun k =>
    ⟨canonicalRep (coxeterSystem .F4) K (simple .F4 k), canonicalRep_mem_adjointGroup _ _ _⟩
  have hsimple : ∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
      ι (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s)) := by
    intro k s
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe, n]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ (simple .F4 k) s
  have hnorm : ∀ g ∈ Subgroup.normalizer
      ((TableBExc.torusPow .F4 K p) : Set (adjointGroup .F4 K)),
      ∃ w : WeylGroup .F4, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .F4 p w s)) := by
    intro g hg
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes
      (Subgroup.mem_normalizer_iff.mp hg)
    refine ⟨w, fun s => ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιcoe]
    rw [hw _ (ExcFrames.frameDiag_mem hfull ζ hζ s)]
    exact ExcFrames.canonicalRep_conj_frameDiag ζ hζ w s
  refine ⟨ζ, hζ, ι, n, hζo, hι, hrange, hιcoe, hsimple, ?_⟩
  obtain ⟨l⟩ := F4SplitTorus.exists_unitValue_equiv (K := K)
  let φ : (Fin Tag.F4.rank → Kˣ) →* adjointGroup .F4 K := F4SplitTorus.coordHom
  let E := TableBExc.torusPow .F4 K p
  have hFormula : ∀ k (a : Fin Tag.F4.rank → Kˣ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple Tag.F4.cartan k (a k)))⁻¹ := by
    intro k a
    apply Subtype.ext
    change canonicalRep (coxeterSystem .F4) K (simple .F4 k) *
        (φ a : ModGL .F4 K) * (canonicalRep (coxeterSystem .F4) K (simple .F4 k))⁻¹ = _
    rw [canonicalRep_simple]
    have h := F4SplitTorus.simple_conj_coordHom k a
    have hcor : F4SplitTorus.corootHom k (a k) = φ (corTuple Tag.F4.cartan k (a k)) := by
      change φ (F4SplitTorus.corootTupleHom k (a k)) =
        φ (corTuple Tag.F4.cartan k (a k))
      apply congrArg φ
      funext i
      have hC : Tag.F4.cartan k i = CartanMatrix.F₄ i k := by
        fin_cases i <;> fin_cases k <;> rfl
      simp only [F4SplitTorus.corootTupleHom, MonoidHom.coe_mk, OneHom.coe_mk, corTuple, hC]
    rw [hcor] at h
    exact h
  have hEiff : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range := fun g => by
    change g ∈ TableBExc.torusPow .F4 K p ↔ _
    rw [← f4ls_torusPow_eq]
    exact (F4SplitTorus.mem_torusPow_iff g p).trans and_comm
  have hcent : Subgroup.centralizer (E : Set (adjointGroup .F4 K)) ≤ φ.range := by
    change Subgroup.centralizer
      ((TableBExc.torusPow .F4 K p : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) ≤ _
    rw [← f4ls_torusPow_eq]
    exact centralizer_torusPow_le_coordHom_range hp hp2 hq
  have hAB : Tag.F4.cartan * cartanInvF4 = 1 := cartan_mul_cartanInv_F4
  have hBA : cartanInvF4 * Tag.F4.cartan = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin Tag.F4.rank))).mp hAB
  have hCB : Tag.F4.cartan.transpose * cartanInvF4.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hBA
  have hBC : cartanInvF4.transpose * Tag.F4.cartan.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hAB
  have hFormulaColumn : ∀ k (a : Fin Tag.F4.rank → Kˣ),
      n k * φ a * (n k)⁻¹ =
        φ a * (φ (corTuple Tag.F4.cartan.transpose.transpose k (a k)))⁻¹ := by
    simpa only [Matrix.transpose_transpose] using hFormula
  obtain ⟨hnA, ρ, hρ, hρrange, hρsimple⟩ := exists_markedWeyl_innerHom
    (hp.odd_of_ne_two hp2) E mulAut_conj_injective_adjointGroup ι hι hrange n hsimple hnorm
  obtain ⟨w, -, -, -, hwn, hwh⟩ :=
    exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod
      l φ F4SplitTorus.coordHom_injective Tag.F4.cartan.transpose cartanInvF4.transpose
      (by rw [hCB, map_one]) (by rw [hBC, map_one]) center_adjointGroup_eq_bot E hEiff ζ hζ hζ1
      n hnA hFormulaColumn hcent
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)) ρ hρ hρrange hρsimple
  refine ⟨w, hwn, ?_⟩
  have hC : Tag.F4.cartan.transpose = CartanMatrix.F₄ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    FrameRoute.coxeterF4_eq.symm
  rw [hM, hC] at hwh
  exact hwh

theorem f4Split_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) :
    GGF4LeviFrame p (TableBExc.torusPow .F4 K p) := by
  have hp : p.Prime := Fact.out
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hK4 : 4 ≤ Nat.card K := by
    have hle := Nat.le_of_dvd (by omega) hpK
    have := hp.two_le
    omega
  obtain ⟨ζ, hζ, ι₀, nk, hζo, hι, hrange, hιι₀, hsimple, wt, hwn, hwt⟩ :=
    f4Split_frame (K := K) hp2 hpK
  refine ⟨K, inferInstance, ζ, hζ, ι₀, nk, _, wt, hζo, hι, hrange, hsimple, hwn, hwt,
    fun t _ Y hY => ?_⟩
  obtain ⟨i, hi, hcent⟩ := e8Split_class hK4 hιι₀ hY
  exact ⟨i, hcent, fun _ _ _ _ => e8Split_lower hιι₀ i hi⟩

theorem ggF4Split_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    GGF4LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, hA⟩ := ggF4Split_model_L hRig hH hΛ hL hpn
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  exact ⟨hN, adjointGroup .F4 Fq, inferInstance, center_adjointGroup_eq_bot, e, _, hA,
    f4Split_leviFrame (ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn) hq⟩

theorem ggF4Split_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    GGF4LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, hA⟩ := ggF4Split_model_K hRig hH hΛ hK hpn
  have hq : p ∣ Nat.card Fq - 1 := by rw [hFqcard]; exact hpn
  exact ⟨hN, adjointGroup .F4 Fq, inferInstance, center_adjointGroup_eq_bot, e, _, hA,
    f4Split_leviFrame (ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn) hq⟩

theorem ggTBJF4LeviL_minus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
  ggTBJF4LeviL_of_model hH (ggF4Split_leviModel_L hRig hH hΛ hL hpn)

theorem ggTBJF4LeviK_minus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.F4, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J :=
  ggTBJF4LeviK_of_model hH hJK (ggF4Split_leviModel_K hRig hH hΛ hK hpn)

end CFSG.StandardType

end
