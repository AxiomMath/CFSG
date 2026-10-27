module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBSelfCent
public import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIso
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.RankThree.PartOne.KE8F
  CFSG.RankThree.CentralCover CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwo TableBExcTwoFusion

private abbrev ordAdj (τ : Tag) (K : Type) [Field K] : Type :=
  CFSG.Blueprint.Chevalley.adjointGroup τ K

private theorem ord_card_coxeterE7 :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
  have hmat : CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
      (M := CoxeterMatrix.E₇) (isFiniteType_cartan .E7) (hc.symm ▸ ggIntCartan_E₇)
    exact h.symm
  have hgroup : WeylGroup .E7 = (CoxeterMatrix.E₇).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E7) = Nat.card (CoxeterMatrix.E₇).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E7

private theorem ord_card_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
  have hmat : CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
      (M := CoxeterMatrix.E₈) (isFiniteType_cartan .E8) (hc.symm ▸ ggIntCartan_E₈)
    exact h.symm
  have hgroup : WeylGroup .E8 = (CoxeterMatrix.E₈).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E8) = Nat.card (CoxeterMatrix.E₈).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E8

private theorem ord_card_torusPow_of_E7_E8
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2) :
    Nat.card (torusPow τ (FiniteField.Extension K 2 2) 3) = 3 ^ τ.rank := by
  have h3 : 3 ∣ Nat.card (FiniteField.Extension K 2 2) - 1 :=
    three_dvd_natCard_ext_sub_one hK
  rcases hτ with rfl | rfl
  · exact card_torusPow_E7 (K := FiniteField.Extension K 2 2) Nat.prime_three h3
  · exact card_torusPow_E8 (K := FiniteField.Extension K 2 2) Nat.prime_three h3

private theorem ord_card_tE_range
    {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : TableBExcTwo.OrthFrame τ d) (hd : d + 1 = τ.rank) :
    Nat.card ((TableBExcTwoTB.tE K F).range : Subgroup (ordAdj τ K)) = 3 ^ τ.rank := by
  have e : Multiplicative (Fin (d + 1) → ZMod 3) ≃ (TableBExcTwoTB.tE K F).range :=
    (MonoidHom.ofInjective (TableBExcTwoTB.tE_injective (K := K) F)).toEquiv
  rw [← hd, ← Nat.card_congr e, Nat.card_congr (Multiplicative.toAdd),
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem ord_conj_mem_torusPow
    {τ : Tag} {L : Type} [Field L] [Finite L] [CharP L 2]
    {m : ordAdj τ L}
    (hm : (m : ModGL τ L) ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    {x : ordAdj τ L} (hx : x ∈ torusPow τ L 3) : m * x * m⁻¹ ∈ torusPow τ L 3 := by
  rw [mem_torusPow] at hx ⊢
  refine ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hm (x : ModGL τ L)).mp hx.1
  · refine Subtype.ext ?_
    have hx3 : (x : ModGL τ L) ^ 3 = 1 := by
      have := congrArg (fun z : ordAdj τ L => (z : ModGL τ L)) hx.2
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
    have h1 : ((MulAut.conj (m : ModGL τ L)) (x : ModGL τ L)) ^ 3 = 1 := by
      rw [← map_pow, hx3, map_one]
    rwa [MulAut.conj_apply] at h1

private theorem ord_canonicalRep_mem_normalizer_torusPow
    {τ : Tag} {L : Type} [Field L] [Finite L] [CharP L 2] (w : WeylGroup τ) :
    (⟨canonicalRep (coxeterSystem τ) L w,
      CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ : ordAdj τ L) ∈
      Subgroup.normalizer ((torusPow τ L 3 : Subgroup (ordAdj τ L)) : Set (ordAdj τ L)) := by
  set n : ordAdj τ L :=
    ⟨canonicalRep (coxeterSystem τ) L w,
      CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ with hn
  have hnN : (n : ModGL τ L) ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    CFSG.LieType.Chevalley.canonicalRep_mem_normalizer (R := L) w
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ord_conj_mem_torusPow (m := n) hnN hx
  · intro hx
    have hx' := ord_conj_mem_torusPow (m := n⁻¹) (inv_mem hnN) hx
    have hx'' : x ∈ torusPow τ L 3 := by
      rw [show x = n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ by group]
      exact hx'
    exact hx''

private theorem ord_card_ggAutsOf_tE_le
    {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) (F : TableBExcTwo.OrthFrame τ d) (hd : d + 1 = τ.rank)
    (hK : Nat.card K = 2) :
    Nat.card (CFSG.StandardType.ggAutsOf
      ((TableBExcTwoTB.tE K F).range : Subgroup (ordAdj τ K))
      (Subgroup.normalizer (((TableBExcTwoTB.tE K F).range : Subgroup (ordAdj τ K)) :
        Set (ordAdj τ K))) le_rfl) ≤ Nat.card (WeylGroup τ) := by
  classical
  set T : Subgroup (ordAdj τ K) := (TableBExcTwoTB.tE K F).range with hT
  set N : Subgroup (ordAdj τ K) := Subgroup.normalizer (T : Set (ordAdj τ K)) with hN
  change Nat.card (CFSG.StandardType.ggAutsOf T N le_rfl) ≤ Nat.card (WeylGroup τ)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := FiniteField.Extension K 2 2 with hL
  have hV : Nat.card (torusPow τ L 3) = 3 ^ τ.rank := ord_card_torusPow_of_E7_E8 hτ hK
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3)
    (three_dvd_natCard_ext_sub_one hK)
  set G : ordAdj τ L := langElt F hωo with hG
  set ι : ordAdj τ K →* ordAdj τ L :=
    TableBExcTwo.adjointMap τ (algebraMap K L) with hι
  have hιinj : Function.Injective ι := TableBExcTwo.adjointMap_injective _
  have hTV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = torusPow τ L 3 := by
    rw [hT]
    exact TableBExcTwoTB.langElt_conj_frame_eq_torusPow hτ F hd hV hωo
  let Ψ : T →* ordAdj τ L := (MulAut.conj G⁻¹).toMonoidHom.comp (ι.comp T.subtype)
  have hΨ_coe : ∀ y : T, Ψ y = G⁻¹ * ι (y : ordAdj τ K) * G := by
    intro y
    simp [Ψ, MulAut.conj_apply]
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hιinj
    have h : G⁻¹ * ι (x : ordAdj τ K) * G = G⁻¹ * ι (y : ordAdj τ K) * G := by
      rw [← hΨ_coe x, ← hΨ_coe y]
      exact hxy
    calc ι (x : ordAdj τ K) = G * (G⁻¹ * ι (x : ordAdj τ K) * G) * G⁻¹ := by group
      _ = G * (G⁻¹ * ι (y : ordAdj τ K) * G) * G⁻¹ := by rw [h]
      _ = ι (y : ordAdj τ K) := by group
  have hΨrange : Ψ.range = torusPow τ L 3 := by
    rw [← hTV]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ι (y : ordAdj τ K), ⟨(y : ordAdj τ K), y.2, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let eΨ : T ≃* torusPow τ L 3 :=
    (MonoidHom.ofInjective hΨinj).trans (MulEquiv.subgroupCongr hΨrange)
  have hΨ_apply : ∀ y : T, ((eΨ y : torusPow τ L 3) : ordAdj τ L) = Ψ y := by
    intro y
    simp only [eΨ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
  have hcanon : ∀ w : WeylGroup τ,
      (⟨canonicalRep (coxeterSystem τ) L w,
        CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ : ordAdj τ L) ∈
        Subgroup.normalizer ((torusPow τ L 3 : Subgroup (ordAdj τ L)) : Set (ordAdj τ L)) :=
    fun w => ord_canonicalRep_mem_normalizer_torusPow (L := L) w
  let θ : WeylGroup τ → MulAut (torusPow τ L 3) := fun w =>
    (torusPow τ L 3).normalizerMonoidHom
      ⟨⟨canonicalRep (coxeterSystem τ) L w,
        CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩, hcanon w⟩
  let Θ : WeylGroup τ → MulAut T := fun w => (eΨ.trans (θ w)).trans eΨ.symm
  have hθ_apply : ∀ (w : WeylGroup τ) (v : torusPow τ L 3),
      ((θ w v : torusPow τ L 3) : ordAdj τ L) =
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ : ordAdj τ L) *
          (v : ordAdj τ L) *
        (⟨canonicalRep (coxeterSystem τ) L w,
          CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup (cs := coxeterSystem τ) (K := L) w⟩ : ordAdj τ L)⁻¹ :=
    fun w v => CFSG.StandardType.normalizerMonoidHom_apply_coe (hcanon w) v
  have hconjT_mem : ∀ (g : N) (y : T), (g : ordAdj τ K) * y * (g : ordAdj τ K)⁻¹ ∈ T :=
    fun g y => (Subgroup.mem_normalizer_iff.mp g.2 (y : ordAdj τ K)).mp y.2
  have hint : ∀ (g : N) (y : T),
      (eΨ (⟨(g : ordAdj τ K) * y * (g : ordAdj τ K)⁻¹, hconjT_mem g y⟩ : T) : ordAdj τ L) =
        (G⁻¹ * ι (g : ordAdj τ K) * G) * (eΨ y) * (G⁻¹ * ι (g : ordAdj τ K) * G)⁻¹ := by
    intro g y
    simp only [hΨ_apply, hΨ_coe, map_mul, map_inv]
    group
  have key : ∀ g : N, ∃ w : WeylGroup τ, T.normalizerMonoidHom g = Θ w := by
    intro g
    set a : ordAdj τ L := G⁻¹ * ι (g : ordAdj τ K) * G with ha_def
    have ha : ∀ x : ordAdj τ L,
        x ∈ torusPow τ L 3 ↔ a * x * a⁻¹ ∈ torusPow τ L 3 := by
      intro x
      constructor
      · intro hx
        have h := hint g (eΨ.symm ⟨x, hx⟩)
        have hx' : (eΨ (eΨ.symm ⟨x, hx⟩) : ordAdj τ L) = x := by
          rw [MulEquiv.apply_symm_apply]
        rw [hx'] at h
        rw [← h]
        exact (eΨ _).2
      · intro hx
        have h := hint g⁻¹ (eΨ.symm ⟨a * x * a⁻¹, hx⟩)
        have hcoef : G⁻¹ * ι ((g⁻¹ : N) : ordAdj τ K) * G = a⁻¹ := by
          rw [ha_def]
          simp only [Subgroup.coe_inv, map_inv]
          group
        rw [hcoef, MulEquiv.apply_symm_apply] at h
        have hx_eq : x = (eΨ (⟨((g⁻¹ : N) : ordAdj τ K) *
            (eΨ.symm ⟨a * x * a⁻¹, hx⟩) * ((g⁻¹ : N) : ordAdj τ K)⁻¹,
            hconjT_mem g⁻¹ _⟩ : T) : ordAdj τ L) := by
          rw [h]; group
        rw [hx_eq]
        exact (eΨ _).2
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes (p := 3) ha
    refine ⟨w, MulEquiv.ext fun x => ?_⟩
    apply eΨ.injective
    have h1 : (eΨ (T.normalizerMonoidHom g x) : ordAdj τ L) = a * (eΨ x) * a⁻¹ := by
      have hx_eq : T.normalizerMonoidHom g x =
          ⟨(g : ordAdj τ K) * x * (g : ordAdj τ K)⁻¹, hconjT_mem g x⟩ :=
        Subtype.ext (CFSG.StandardType.normalizerMonoidHom_apply_coe g.2 x)
      rw [hx_eq]
      exact hint g x
    have h2 : (eΨ (Θ w x) : ordAdj τ L) = a * (eΨ x) * a⁻¹ := by
      change (eΨ (eΨ.symm (θ w (eΨ x))) : ordAdj τ L) = a * (eΨ x) * a⁻¹
      rw [MulEquiv.apply_symm_apply, hθ_apply]
      refine Subtype.ext ?_
      have hmem : ((eΨ x : torusPow τ L 3) : ModGL τ L) ∈ ExcFrames.splitPow τ L 3 :=
        ExcFrames.mem_torusPow_iff_coe.mp (eΨ x).2
      show (canonicalRep (coxeterSystem τ) L w * ((eΨ x : torusPow τ L 3) : ModGL τ L) *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) =
          (a : ModGL τ L) * ((eΨ x : torusPow τ L 3) : ModGL τ L) * (a : ModGL τ L)⁻¹
      exact (hw _ hmem).symm
    exact Subtype.ext (h1.trans h2.symm)
  have hrange : (↑(CFSG.StandardType.ggAutsOf T N le_rfl) : Set (MulAut T)) ⊆ Set.range Θ := by
    rintro a ha
    rw [CFSG.StandardType.ggAutsOf] at ha
    change ∃ g : N, (T.normalizerMonoidHom.comp (Subgroup.inclusion le_rfl)) g = a at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨w, hw⟩ := key g
    exact ⟨w, by rw [← hg]; exact hw.symm⟩
  have hinj : Function.Injective
      (fun a : ↥(CFSG.StandardType.ggAutsOf T N le_rfl) =>
        (⟨a.1, hrange a.2⟩ : ↥(Set.range Θ))) :=
    fun a b hab => Subtype.ext (congrArg (fun z : ↥(Set.range Θ) => (z : MulAut T)) hab)
  have h1 : Nat.card ↥(CFSG.StandardType.ggAutsOf T N le_rfl) ≤ Nat.card ↥(Set.range Θ) :=
    Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card ↥(Set.range Θ) ≤ Nat.card (WeylGroup τ) :=
    Nat.card_le_card_of_surjective (fun w => (⟨Θ w, w, rfl⟩ : ↥(Set.range Θ)))
      (fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩)
  exact h1.trans h2

theorem card_normalizer_tE_le
    {τ : Tag} {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) (F : TableBExcTwo.OrthFrame τ d) (hd : d + 1 = τ.rank) (hK : Nat.card K = 2) :
    Nat.card (Subgroup.normalizer (((TableBExcTwoTB.tE K F).range : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ K)) :
        Set (CFSG.Blueprint.Chevalley.adjointGroup τ K))) ≤
      Nat.card (Subgroup.centralizer (((TableBExcTwoTB.tE K F).range : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup τ K)) :
        Set (CFSG.Blueprint.Chevalley.adjointGroup τ K))) * Nat.card (CFSG.LieType.Chevalley.WeylGroup τ) := by
  set T : Subgroup (ordAdj τ K) := (TableBExcTwoTB.tE K F).range with hT
  set N : Subgroup (ordAdj τ K) := Subgroup.normalizer (T : Set (ordAdj τ K)) with hN
  change Nat.card N ≤ Nat.card (Subgroup.centralizer (T : Set (ordAdj τ K))) *
    Nat.card (CFSG.LieType.Chevalley.WeylGroup τ)
  have hC : Subgroup.centralizer (T : Set (ordAdj τ K)) ≤ N := Subgroup.centralizer_le_normalizer _
  have hcard := CFSG.StandardType.card_ggAutsOf_mul_card (X := T) (S := N) le_rfl
  rw [inf_eq_right.mpr hC] at hcard
  have hb := ord_card_ggAutsOf_tE_le hτ F hd hK
  calc Nat.card N
      = Nat.card (CFSG.StandardType.ggAutsOf T N le_rfl) *
          Nat.card (Subgroup.centralizer (T : Set (ordAdj τ K))) := hcard.symm
    _ ≤ Nat.card (WeylGroup τ) * Nat.card (Subgroup.centralizer (T : Set (ordAdj τ K))) :=
        Nat.mul_le_mul_right _ hb
    _ = Nat.card (Subgroup.centralizer (T : Set (ordAdj τ K))) * Nat.card (WeylGroup τ) :=
        mul_comm _ _

theorem lss92_torus_order_E7
    (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 7) :
    Nat.card (Subgroup.normalizer (E : Set G)) ≤ 3 ^ 7 * Nat.card (CoxeterMatrix.E₇).Group := by
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hsimple hEm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E7 := by rcases hmt with ⟨-, h⟩ | ⟨h, -⟩ <;> [exact h; omega]
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hZ
  let eG : G ≃* ordAdj .E7 (GaloisField 2 1) := Subgroup.topEquiv.symm.trans e
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  let E' : Subgroup (ordAdj .E7 (GaloisField 2 1)) := E.map eG.toMonoidHom
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE eG.toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective eG.injective, hcard]
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hGF hE' hcard'.ge
  set T' : Subgroup (ordAdj .E7 (GaloisField 2 1)) :=
    (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE7).range with hT'
  have hnormal : Nat.card (Subgroup.normalizer (E : Set G)) =
      Nat.card (Subgroup.normalizer (T' : Set (ordAdj .E7 (GaloisField 2 1)))) := by
    have h1 : Nat.card (Subgroup.normalizer (E : Set G)) =
        Nat.card (Subgroup.normalizer (E' : Set (ordAdj .E7 (GaloisField 2 1)))) := by
      rw [show E' = E.map eG.toMonoidHom from rfl,
        GGRootNorm.normalizer_map_mulEquiv eG E,
        Subgroup.card_map_of_injective eG.injective]
    have h2 : Nat.card (Subgroup.normalizer (E' : Set (ordAdj .E7 (GaloisField 2 1)))) =
        Nat.card (Subgroup.normalizer (T' : Set (ordAdj .E7 (GaloisField 2 1)))) := by
      rw [hc, GGRootNorm.normalizer_map_mulEquiv (MulAut.conj c) T',
        Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact h1.trans h2
  calc Nat.card (Subgroup.normalizer (E : Set G))
      = Nat.card (Subgroup.normalizer (T' : Set (ordAdj .E7 (GaloisField 2 1)))) := hnormal
    _ ≤ Nat.card (Subgroup.centralizer (T' : Set (ordAdj .E7 (GaloisField 2 1)))) *
          Nat.card (WeylGroup .E7) :=
        card_normalizer_tE_le (hτ := Or.inl rfl) (F := TableBExcTwo.frameE7) (hd := rfl) hGF
    _ = 3 ^ 7 * Nat.card (WeylGroup .E7) := by
        rw [hT', TableBExcTwoTB.centralizer_tE_frameE7 hGF,
          ord_card_tE_range TableBExcTwo.frameE7 rfl]
        simp only [CFSG.Blueprint.Chevalley.Tag.rank]
    _ = 3 ^ 7 * Nat.card (CoxeterMatrix.E₇).Group := by
        rw [show Nat.card (WeylGroup .E7) = Nat.card (CoxeterMatrix.E₇).Group from
          CFSG.StandardType.NoOffExc.card_weyl_E7.trans ord_card_coxeterE7.symm]

private theorem ord_famKernel_univ_eq_empty_E8
    {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3) :
    famKernel (Set.univ : Set (Fin Tag.E8.rank → Lˣ)) = ∅ := by
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hα, hall⟩
  apply redMod_ne_zero_of_isRoot TableBExcTwo.frameE8.symm_one hα
  funext j
  have h1 : ω ^ α j = 1 := by
    rw [← ExcSplitL.rootChar_mulSingle]
    exact hall _ trivial
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hω] at h2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (α j) 3).2 (by exact_mod_cast h2)

theorem centralizer_tE_frameE8
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Subgroup.centralizer ((TableBExcTwoTB.tE K TableBExcTwo.frameE8).range :
        Set (CFSG.Blueprint.Chevalley.adjointGroup .E8 K)) =
      (TableBExcTwoTB.tE K TableBExcTwo.frameE8).range := by
  classical
  refine le_antisymm ?_ fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  swap
  · obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  set L := FiniteField.Extension K 2 2 with hL
  have := Fact.mk Nat.prime_three
  have h3 := three_dvd_natCard_ext_sub_one hK
  obtain ⟨ω, hω⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  have hV : Nat.card (torusPow .E8 L 3) = 3 ^ Tag.E8.rank :=
    card_torusPow_E8 (K := L) Nat.prime_three h3
  have hpow : ∀ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 a ^ 3 = 1 := fun a => by
    rw [ExcSplitL.rootDiagUnit_pow', show a ^ 3 = 1 from funext fun i => units_pow_three hK (a i),
      rootDiagUnit_one]
  set G := langElt TableBExcTwo.frameE8 hω with hG
  set ι := TableBExcTwo.adjointMap .E8 (algebraMap K L) with hι
  set T := (TableBExcTwoTB.tE K TableBExcTwo.frameE8).range with hT
  have hTV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = torusPow .E8 L 3 :=
    TableBExcTwoTB.langElt_conj_frame_eq_torusPow (Or.inr rfl) TableBExcTwo.frameE8 rfl hV hω
  intro c hc
  set x : ordAdj .E8 L := G⁻¹ * ι c * G with hx
  have hcomm : ∀ a ∈ (Set.univ : Set (Fin Tag.E8.rank → Lˣ)),
      rootDiagUnit .E8 a * (x : ModGL .E8 L) * (rootDiagUnit .E8 a)⁻¹ = x := by
    intro a _
    have hda : rootDiagUnit .E8 a ∈ torusGroup .E8 L := full_of_E7_E8 (Or.inr rfl) a
    set d : ordAdj .E8 L := ⟨rootDiagUnit .E8 a, torusGroup_le_adjointGroup hda⟩ with hd
    have hdV : d ∈ torusPow .E8 L 3 :=
      ⟨hda, Subtype.ext (by
        rw [Subgroup.coe_pow, hd]
        exact hpow a)⟩
    rw [← hTV] at hdV
    obtain ⟨_, ⟨t, ht, rfl⟩, hdt⟩ := hdV
    have hct : t * c = c * t := Subgroup.mem_centralizer_iff.1 hc t ht
    have hdt' : d = G⁻¹ * ι t * G := by
      rw [← hdt, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hxd : d * x = x * d := by
      rw [hdt', hx]
      calc G⁻¹ * ι t * G * (G⁻¹ * ι c * G) = G⁻¹ * ι (t * c) * G := by rw [map_mul]; group
        _ = G⁻¹ * ι (c * t) * G := by rw [hct]
        _ = G⁻¹ * ι c * G * (G⁻¹ * ι t * G) := by rw [map_mul]; group
    have h1 : d * x * d⁻¹ = x := by rw [hxd]; group
    have h2 := congrArg Subtype.val h1
    simpa [hd] using h2
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hxeq⟩ := fam_factor Set.univ x.2 hcomm
  have hker0 := ord_famKernel_univ_eq_empty_E8 hω
  have hbot : ∀ S : Set (Fin Tag.E8.rank → ℤ), rootSpan .E8 L (∅ ∩ S) = ⊥ := by
    intro S
    rw [Set.empty_inter]
    exact le_bot_iff.1 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  rw [hker0, hbot, Subgroup.mem_bot] at hu hv
  subst hu hv
  have hw1 : w = 1 :=
    ExcSplitL.eq_one_of_mem_rootCharStabilizer (p := 3) (by norm_num) hω fun j => hw _ trivial
  subst hw1
  have hxh : (x : ModGL .E8 L) = h := by
    rw [hxeq, canonicalRep_one, mul_one, mul_one, mul_one]
  have hxV : x ∈ torusPow .E8 L 3 := by
    refine ⟨hxh ▸ hh, Subtype.ext ?_⟩
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    rw [Subgroup.coe_pow, hxh, hb]
    exact hpow b
  rw [← hTV] at hxV
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hxV
  have hιt : ι t = ι c := by
    have e : G⁻¹ * ι t * G = G⁻¹ * ι c * G := by
      rw [← hx, ← hxt, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    simpa using e
  rw [← TableBExcTwo.adjointMap_injective _ hιt]
  exact ht

theorem lss92_torus_order_E8
    (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G)) (hsimple : IsSimpleGroup G)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 8) :
    Nat.card (Subgroup.normalizer (E : Set G)) ≤ 3 ^ 8 * Nat.card (CoxeterMatrix.E₈).Group := by
  obtain ⟨hZ, ⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_label_of_marking hsimple hEm
  dsimp only at hmt hn
  subst hn
  have ht : t = .E8 := by rcases hmt with ⟨h, -⟩ | ⟨-, h⟩ <;> [omega; exact h]
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_adjointGroup_of_isLabel_E8
    (lab := ⟨t, r, 1⟩) hlab ht hZ
  let eG : G ≃* ordAdj .E8 (GaloisField 2 1) := Subgroup.topEquiv.symm.trans e
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by omega)]; norm_num
  let E' : Subgroup (ordAdj .E8 (GaloisField 2 1)) := E.map eG.toMonoidHom
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE eG.toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 8 := by
    rw [Subgroup.card_map_of_injective eG.injective, hcard]
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 hGF hE' hcard'.ge
  set T' : Subgroup (ordAdj .E8 (GaloisField 2 1)) :=
    (TableBExcTwoTB.tE (GaloisField 2 1) TableBExcTwo.frameE8).range with hT'
  have hnormal : Nat.card (Subgroup.normalizer (E : Set G)) =
      Nat.card (Subgroup.normalizer (T' : Set (ordAdj .E8 (GaloisField 2 1)))) := by
    have h1 : Nat.card (Subgroup.normalizer (E : Set G)) =
        Nat.card (Subgroup.normalizer (E' : Set (ordAdj .E8 (GaloisField 2 1)))) := by
      rw [show E' = E.map eG.toMonoidHom from rfl,
        GGRootNorm.normalizer_map_mulEquiv eG E,
        Subgroup.card_map_of_injective eG.injective]
    have h2 : Nat.card (Subgroup.normalizer (E' : Set (ordAdj .E8 (GaloisField 2 1)))) =
        Nat.card (Subgroup.normalizer (T' : Set (ordAdj .E8 (GaloisField 2 1)))) := by
      rw [hc, GGRootNorm.normalizer_map_mulEquiv (MulAut.conj c) T',
        Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact h1.trans h2
  calc Nat.card (Subgroup.normalizer (E : Set G))
      = Nat.card (Subgroup.normalizer (T' : Set (ordAdj .E8 (GaloisField 2 1)))) := hnormal
    _ ≤ Nat.card (Subgroup.centralizer (T' : Set (ordAdj .E8 (GaloisField 2 1)))) *
          Nat.card (WeylGroup .E8) :=
        card_normalizer_tE_le (hτ := Or.inr rfl) (F := TableBExcTwo.frameE8) (hd := rfl) hGF
    _ = 3 ^ 8 * Nat.card (WeylGroup .E8) := by
        rw [hT', centralizer_tE_frameE8 hGF, ord_card_tE_range TableBExcTwo.frameE8 rfl]
        simp only [CFSG.Blueprint.Chevalley.Tag.rank]
    _ = 3 ^ 8 * Nat.card (CoxeterMatrix.E₈).Group := by
        rw [show Nat.card (WeylGroup .E8) = Nat.card (CoxeterMatrix.E₈).Group from
          CFSG.StandardType.NoOffExc.card_weyl_E8.trans ord_card_coxeterE8.symm]

end CFSG.StandardType.FrameRoute

end
