module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicCover
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.StandardType

namespace LayerCC

open CFSG.Assembly CFSG.RankThree.PartOne.KCLinComm Matrix
open CFSG.ComponentClassification

section Odd

variable {n : ℕ} {F : Type} [Field F]

theorem mem_ggFix_slConjugation {B : GL (Fin n) F} {s : SpecialLinearGroup (Fin n) F} :
    s ∈ ggFix (CatalogueBHigherLinearAction.slConjugation n F B) ↔
      SpecialLinearGroup.toGL s ∈ Subgroup.centralizer
        ((Subgroup.zpowers B : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
  rw [mem_ggFix, ← SpecialLinearGroup.toGL_injective.eq_iff,
    CatalogueBHigherLinearAction.toGL_slConjugation, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem odd_orderOf_of_slConjugation_pow [Finite F] [CharP F 2] {p : ℕ} (hp : Odd p)
    {B : GL (Fin n) F} (hB : CatalogueBHigherLinearAction.slConjugation n F B ^ p = 1) :
    ¬ 2 ∣ orderOf B := by
  have : Fintype F := Fintype.ofFinite F
  have hcomm : ∀ t : TransvectionStruct (Fin n) F,
      Commute t.toMatrix ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    intro t
    let s : SpecialLinearGroup (Fin n) F := ⟨t.toMatrix, t.det⟩
    have h1 : CatalogueBHigherLinearAction.slConjugation n F (B ^ p) s = s := by
      rw [map_pow, hB, MulAut.one_apply]
    have h2 : ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * t.toMatrix *
        (((B ^ p)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = t.toMatrix := by
      have h3 := CatalogueBHigherLinearAction.slConjugation_matrix n F (B ^ p) s
      rw [h1] at h3
      exact h3.symm
    show t.toMatrix * _ = _ * t.toMatrix
    calc t.toMatrix * ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * t.toMatrix *
            (((B ^ p)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h2]
      _ = ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * t.toMatrix := by
        rw [Matrix.mul_assoc _ _ ((B ^ p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have hsc := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  have hmem : B ^ p ∈ Subgroup.center (GL (Fin n) F) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hsc
  rw [GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc1 : c ^ (Fintype.card F - 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero)
  have hB1 : B ^ (p * (Fintype.card F - 1)) = 1 := by
    rw [pow_mul, ← hc, ← map_pow, hc1, map_one]
  have hcard2 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hodd : Odd (p * (Fintype.card F - 1)) := hp.mul (Nat.odd_iff.mpr (by omega))
  intro h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
    (h2.trans (orderOf_dvd_of_pow_eq_one hB1)))

end Odd

section Blocks

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ b, Field (E b)] {m : ι → ℕ}

theorem apply_eq_one_of_mem_blockSL {b c : ι} (hcb : c ≠ b) {w : PiGL E m}
    (hw : w ∈ blockSL E m b) : w c = 1 := by
  obtain ⟨s, rfl⟩ := hw
  exact blockEmbed_apply_of_ne hcb s

theorem apply_mem_center_of_commute_blockSL {b : ι} {w : PiGL E m}
    (hw : ∀ g ∈ blockSL E m b, w * g = g * w) : w b ∈ Subgroup.center (GL (Fin (m b)) (E b)) := by
  have hcomm : ∀ s : SpecialLinearGroup (Fin (m b)) (E b),
      Commute (s : Matrix (Fin (m b)) (Fin (m b)) (E b))
        ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) := by
    intro s
    have h1 := congrFun (hw _ ⟨s, rfl⟩) b
    simp only [Pi.mul_apply, blockEmbed_apply_self] at h1
    have h3 := congrArg (fun g : GL (Fin (m b)) (E b) =>
      (g : Matrix (Fin (m b)) (Fin (m b)) (E b))) h1
    show (s : Matrix (Fin (m b)) (Fin (m b)) (E b)) * _ = _ * _
    simpa using h3.symm
  have hsc : ((w b : GL (Fin (m b)) (E b)) : Matrix (Fin (m b)) (Fin (m b)) (E b)) ∈
      Set.range (Matrix.scalar (Fin (m b))) :=
    Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => hcomm ⟨t.toMatrix, t.det⟩
  exact GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hsc

end Blocks

theorem exists_ne_one_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ∃ x : Q, x ≠ 1 := by
  obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hQ
  refine ⟨a, fun ha => hab ?_⟩
  rw [ha, one_mul, mul_one]

theorem isCyclic_center_GL {k : ℕ} {D : Type*} [Field D] [Finite D] :
    IsCyclic (Subgroup.center (GL (Fin k) D)) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact isCyclic_of_surjective _ (GeneralLinearGroup.scalar (Fin k)).rangeRestrict_surjective

theorem ggModelLayerCyclic_slConjugation {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (B : GL (Fin n) F) :
    GGModelLayerCyclic p (CatalogueBHigherLinearAction.slConjugation n F B) := by
  classical
  intro _ hαp hcomp S hSE hSC _
  set C₀ := ggFix (CatalogueBHigherLinearAction.slConjugation n F B) with hC₀
  have hBodd := odd_orderOf_of_slConjugation_pow (hp.odd_of_ne_two hp2) hαp
  have hcardA : (Nat.card (Subgroup.zpowers B) : F) ≠ 0 := by
    rw [Nat.card_zpowers, Ne, CharP.cast_eq_zero_iff F 2]
    exact hBodd
  obtain ⟨r, D, d, _, _, _, θ, hθinj, hθrange⟩ :=
    LayerFacts.exists_piGL_centralizer (Subgroup.zpowers B) hcardA
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  set ι : SpecialLinearGroup (Fin n) F →* GL (Fin n) F := SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  have hC₀θ : C₀ = θ.range.comap ι := by
    ext s
    rw [hC₀, mem_ggFix_slConjugation, hθrange]
    rfl
  set S' : {b : Fin r // LayerFacts.GoodBlock D d b} → Subgroup (SpecialLinearGroup (Fin n) F) :=
    fun b => ((blockSL D d b.1).map θ).comap ι with hS'def
  have hSrange : ∀ b : {b : Fin r // LayerFacts.GoodBlock D d b},
      (blockSL D d b.1).map θ ≤ ι.range := by
    intro b
    have hperf : ⁅blockSL D d b.1, blockSL D d b.1⁆ = blockSL D d b.1 :=
      CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect
        (isPerfect_blockSL b.1 b.2.1 b.2.2)
    rw [← hperf, Subgroup.map_commutator]
    refine (Subgroup.commutator_mono le_top le_top).trans ?_
    rw [← _root_.commutator_def, hιdef, SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Abelianization.commutator_subset_ker _
  have hSmap : ∀ b, (S' b).map ι = (blockSL D d b.1).map θ := fun b =>
    Subgroup.map_comap_eq_self (hSrange b)
  have hÑmap : (⨆ b, S' b).map ι = (LayerFacts.goodSL D d).map θ := by
    rw [Subgroup.map_iSup, LayerFacts.goodSL, Subgroup.map_iSup]
    exact iSup_congr hSmap
  have hSq : ∀ b, CFSG.IsQuasisimple (S' b) := fun b =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((Subgroup.equivMapOfInjective _ θ hθinj).trans
        (MulEquiv.subgroupCongr (hSmap b)).symm).trans
          (Subgroup.equivMapOfInjective _ ι hιinj).symm)
      (isQuasisimple_blockSL b.1 b.2.1 b.2.2)
  have hSC₀ : ∀ b, S' b ≤ C₀ := fun b => by
    rw [hC₀θ]
    exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
  have hSn : ∀ b, ∀ c ∈ C₀, ∀ s ∈ S' b, c * s * c⁻¹ ∈ S' b := by
    intro b c hc s hs
    rw [hC₀θ] at hc
    obtain ⟨w, hw⟩ := hc
    obtain ⟨g, hg, hgs⟩ := hs
    refine ⟨w * g * w⁻¹, conj_mem_blockSL b.1 w hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hw, hgs, map_mul, map_mul, map_inv]
  have hder : ∃ k, LayerFacts.ggDer C₀ k ≤ ⨆ b, S' b := by
    obtain ⟨k, hk⟩ := LayerFacts.exists_derivedSeries_le_goodSL (E := D) (m := d)
    refine ⟨k, ?_⟩
    rw [← Subgroup.map_le_map_iff_of_injective hιinj, LayerFacts.map_ggDer, hÑmap]
    calc LayerFacts.ggDer (C₀.map ι) k ≤ LayerFacts.ggDer θ.range k :=
          LayerFacts.ggDer_mono (by rw [hC₀θ]; exact Subgroup.map_comap_le _ _) k
      _ = (LayerFacts.ggDer ⊤ k).map θ := by rw [LayerFacts.map_ggDer, ← MonoidHom.range_eq_map]
      _ = (derivedSeries _ k).map θ := by rw [LayerFacts.ggDer_top]
      _ ≤ (LayerFacts.goodSL D d).map θ := Subgroup.map_mono hk
  have hZ : ∀ z ∈ ⨆ b, S' b, (∀ y ∈ ⨆ b, S' b, z * y = y * z) → z ^ 2 = 1 → z = 1 := by
    intro z hz hzc hz2
    obtain ⟨w, hw, hwz⟩ : ι z ∈ (LayerFacts.goodSL D d).map θ :=
      hÑmap ▸ Subgroup.mem_map_of_mem ι hz
    have hwc : ∀ g ∈ LayerFacts.goodSL D d, w * g = g * w := by
      intro g hg
      obtain ⟨y, hy, hyg⟩ : θ g ∈ (⨆ b, S' b).map ι := hÑmap ▸ Subgroup.mem_map_of_mem θ hg
      apply hθinj
      rw [map_mul, map_mul, hwz, ← hyg, ← map_mul, ← map_mul, hzc y hy]
    have hw2 : w ^ 2 = 1 := by
      apply hθinj
      rw [map_pow, hwz, map_one, ← map_pow, hz2, map_one]
    apply hιinj
    rw [← hwz, LayerFacts.eq_one_of_mem_goodSL_of_commute hw hwc hw2, map_one, map_one]
  have hlayer : LargeEvenLayer C₀ = ⨆ b, S' b := by
    have h := (LayerFacts.ggLayer_of_core (MonoidHom.id (SpecialLinearGroup (Fin n) F))
      (by rw [MonoidHom.ker_id]; exact bot_le) (H := C₀) (C₀ := C₀) (by rw [Subgroup.map_id])
      (by rw [Subgroup.map_id, Subgroup.subgroupOf_self]; infer_instance)
      (by rw [Subgroup.map_id]; exact CFSG.RankThree.PartOne.KCUnitary.commutator_self_le C₀)
      S' hSC₀ hSn hSq hder hZ).1
    rwa [Subgroup.map_id] at h
  set Ly := LargeEvenLayer C₀ with hLy
  have hEq : CFSG.IsQuasisimple Ly := (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hSE' : ∀ b, S' b ≤ Ly := fun b => by
    rw [hlayer]
    exact le_iSup S' b
  have hdisj : ∀ b₁ b₂ : {b : Fin r // LayerFacts.GoodBlock D d b}, b₁ ≠ b₂ →
      ∀ x ∈ S' b₁, x ∈ S' b₂ → x = 1 := by
    intro b₁ b₂ hne x hx1 hx2
    obtain ⟨w₁, hw₁, hw₁x⟩ := hx1
    obtain ⟨w₂, hw₂, hw₂x⟩ := hx2
    have hw : w₁ = w₂ := hθinj (hw₁x.trans hw₂x.symm)
    have hw1 : w₁ = 1 := by
      funext c
      by_cases hc : c = b₁.1
      · have hc2 : c ≠ b₂.1 := fun h => hne (Subtype.ext (hc.symm.trans h))
        rw [hw]
        exact apply_eq_one_of_mem_blockSL hc2 hw₂
      · exact apply_eq_one_of_mem_blockSL hc hw₁
    apply hιinj
    rw [← hw₁x, hw1, map_one, map_one]
  have huniq : ∀ b₁ b₂ : {b : Fin r // LayerFacts.GoodBlock D d b}, b₁ = b₂ := by
    intro b₁ b₂
    by_contra hne
    have hNnormal : ((S' b₁).subgroupOf Ly).Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hSn b₁ g (largeEvenLayer_le C₀ g.2) x hx
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hEq hNnormal with h | h
    · obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne_one_of_isQuasisimple (hSq b₂)
      have hxN : (⟨x, hSE' b₂ hx⟩ : Ly) ∈ (S' b₁).subgroupOf Ly := by
        rw [h]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at hxN
      exact hx1 (Subtype.ext (hdisj b₁ b₂ hne x hxN hx))
    · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple (hSq b₁)
      have hxZ := h (show (⟨x, hSE' b₁ hx⟩ : Ly) ∈ (S' b₁).subgroupOf Ly from hx)
      have h1 := Subgroup.mem_center_iff.mp hxZ ⟨y, hSE' b₁ hy⟩
      apply hxy
      apply Subtype.ext
      exact (congrArg Subtype.val h1).symm
  obtain ⟨b₀⟩ : Nonempty {b : Fin r // LayerFacts.GoodBlock D d b} := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hbot : (⨆ b, S' b) = ⊥ := iSup_of_empty _
    obtain ⟨x, hx1⟩ := exists_ne_one_of_isQuasisimple hEq
    apply hx1
    have hx : (x : SpecialLinearGroup (Fin n) F) ∈
        (⊥ : Subgroup (SpecialLinearGroup (Fin n) F)) := by
      rw [← hbot, ← hlayer]
      exact x.2
    exact Subtype.ext (Subgroup.mem_bot.mp hx)
  have hC₀range : ∀ s : C₀, (ι.comp C₀.subtype) s ∈ θ.range := fun s => by
    have hs : (s : SpecialLinearGroup (Fin n) F) ∈ θ.range.comap ι := by
      rw [← hC₀θ]
      exact s.2
    exact hs
  let toPi : C₀ →* (∀ i, GL (Fin (d i)) (D i)) :=
    (MonoidHom.ofInjective hθinj).symm.toMonoidHom.comp
      ((ι.comp C₀.subtype).codRestrict θ.range hC₀range)
  have hθtoPi : ∀ s : C₀, θ (toPi s) = ι s := fun s =>
    MonoidHom.apply_ofInjective_symm hθinj _
  have hSC₀' : S ≤ C₀ := hSE.trans (largeEvenLayer_le C₀)
  let χS : S →* GL (Fin (d b₀.1)) (D b₀.1) :=
    ((Pi.evalMonoidHom _ b₀.1).comp toPi).comp (Subgroup.inclusion hSC₀')
  have hgood : ∀ s : S, toPi (Subgroup.inclusion hSC₀' s) ∈ LayerFacts.goodSL D d := by
    intro s
    have h1 : ι s ∈ (LayerFacts.goodSL D d).map θ := by
      rw [← hÑmap, ← hlayer]
      exact Subgroup.mem_map_of_mem ι (hSE s.2)
    obtain ⟨w, hw, hws⟩ := h1
    have hweq : w = toPi (Subgroup.inclusion hSC₀' s) := hθinj (by rw [hws, hθtoPi]; rfl)
    rw [← hweq]
    exact hw
  have hcomm : ∀ s : S, ∀ g ∈ LayerFacts.goodSL D d,
      toPi (Subgroup.inclusion hSC₀' s) * g = g * toPi (Subgroup.inclusion hSC₀' s) := by
    intro s g hg
    obtain ⟨y, hy, hyg⟩ : θ g ∈ (⨆ b, S' b).map ι := hÑmap ▸ Subgroup.mem_map_of_mem θ hg
    have hyL : y ∈ Ly := by
      rw [hlayer]
      exact hy
    have hsy : y * s = s * y := Subgroup.mem_centralizer_iff.mp (hSC s.2) y hyL
    apply hθinj
    rw [map_mul, map_mul, hθtoPi, ← hyg]
    show ι s * ι y = ι y * ι s
    rw [← map_mul, ← map_mul, hsy]
  have hχinj : Function.Injective χS := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hw : toPi (Subgroup.inclusion hSC₀' s) = 1 := by
      funext c
      by_cases hc : c = b₀.1
      · subst hc
        exact hs
      · have hcbad : ¬ LayerFacts.GoodBlock D d c := fun hcg =>
          hc (congrArg Subtype.val (huniq ⟨c, hcg⟩ b₀))
        exact LayerFacts.apply_eq_one_of_mem_goodSL (hgood s) hcbad
    have h1 := hθtoPi (Subgroup.inclusion hSC₀' s)
    rw [hw, map_one] at h1
    apply Subtype.ext
    apply hιinj
    rw [OneMemClass.coe_one, map_one]
    exact h1.symm
  have hχcen : χS.range ≤ Subgroup.center (GL (Fin (d b₀.1)) (D b₀.1)) := by
    rintro _ ⟨s, rfl⟩
    exact apply_mem_center_of_commute_blockSL (b := b₀.1) fun g hg =>
      hcomm s g (LayerFacts.blockSL_le_goodSL b₀.2 hg)
  have hZcyc : IsCyclic (Subgroup.center (GL (Fin (d b₀.1)) (D b₀.1))) := isCyclic_center_GL
  have hRcyc : IsCyclic χS.range :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hχcen) (MulEquiv.surjective _)
  exact isCyclic_of_surjective (MonoidHom.ofInjective hχinj).symm (MulEquiv.surjective _)

end LayerCC

end CFSG.StandardType

end
