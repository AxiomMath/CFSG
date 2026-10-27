module

public import CFSG.OddTranspositions.PartThree.Twelve.Seven
public import CFSG.OddTranspositions.PartThree.Twelve.SpChart
public import CFSG.OddTranspositions.PartThree.Twelve.MarkedEmbedding
import CFSG.OddTranspositions.WidthSylow
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockSp
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.Open
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def IsOrthMarked (Γ : Set G) (n f : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (Q₀ : QuadraticForm K (Fin n → K))
    (ι : G → Fin n → K), Nat.card K = 2 ^ f ∧ Q₀.polarBilin.Nondegenerate ∧
    (∀ z ∈ Γ, Q₀ (ι z) = 1) ∧ (∀ v, Q₀ v = 1 → ∃ z ∈ Γ, ι z = v) ∧ Set.InjOn ι Γ ∧
    (∀ z ∈ Γ, ∀ z' ∈ Γ, z * z' * z⁻¹ ∈ Γ ∧ ι (z * z' * z⁻¹) = reflect Q₀ (ι z) (ι z')) ∧
    (∀ z ∈ Γ, ∀ z' ∈ Γ, (Commute z z' ↔ polar Q₀ (ι z) (ι z') = 0)) ∧
    TauCeti.QuadraticMap.orthogonalGroup Q₀ ≤ Subgroup.closure (reflect Q₀ '' {v | Q₀ v = 1})

omit [Finite G] in
theorem IsOrthMarked.preimage {Γ : Set G} {n f : ℕ} (h : IsOrthMarked Γ n f) (φ : G ≃* G) :
    IsOrthMarked (φ ⁻¹' Γ) n f := by
  obtain ⟨K, hK, hKf, hK2, Q₀, ι, hcard, hQ, h1, hsurj, hinj, hconj, hcomm, hgen⟩ := h
  refine ⟨K, hK, hKf, hK2, Q₀, ι ∘ φ, hcard, hQ, fun z hz => h1 _ hz, fun v hv => ?_, ?_, ?_, ?_,
    hgen⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj v hv
    exact ⟨φ.symm z, by simpa using hz, by simp⟩
  · intro z hz z' hz' hzz
    exact φ.injective (hinj hz hz' hzz)
  · intro z hz z' hz'
    obtain ⟨hm, he⟩ := hconj _ hz _ hz'
    exact ⟨by simpa [Set.mem_preimage, map_mul, map_inv] using hm,
      by simpa [Function.comp_apply, map_mul, map_inv] using he⟩
  · intro z hz z' hz'
    rw [Function.comp_apply, Function.comp_apply, ← hcomm _ hz _ hz']
    exact ⟨fun h => h.map φ, fun h => by simpa using h.map φ.symm⟩

theorem commute_symmetryGL_iff {K : Type} [Field K] [CharP K 2] {n : ℕ}
    {Q₀ : QuadraticForm K (Fin n → K)} (hQ : Q₀.polarBilin.Nondegenerate) {a b : Fin n → K}
    (ha : Q₀ a = 1) (hb : Q₀ b = 1) :
    Commute (symmetryGL Q₀ a) (symmetryGL Q₀ b) ↔ polar Q₀ a b = 0 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at ha
    exact zero_ne_one ha
  rw [show Commute (symmetryGL Q₀ a) (symmetryGL Q₀ b) ↔
      symmetryGL Q₀ a ∈ Subgroup.centralizer {symmetryGL Q₀ b} from
      Subgroup.mem_centralizer_singleton_iff.symm,
    mem_centralizer_symmetryGL_iff hQ hb (symmetryGL_mem Q₀ a), symmetryGL_mulVec_of_charTwo ha,
    add_eq_left, smul_eq_zero, or_iff_left ha0]

theorem isOrthMarked_compSet_of_isOrthReflection (hN : IsNormalSet D) (hD : IsOddTransp D)
    {x y d : G} (hloc : ∀ v ∈ compSet D x y d, LocalPivot D x y v)
    (hns : ¬ Group.IsSolvable (Subgroup.closure (compSet D x y d))) {n f : ℕ} {t : G}
    (ht : t ∈ compSet D x y d)
    (hOt : IsOrthReflection (Subgroup.closure (compSet D x y d)) n f
      ⟨t, Subgroup.subset_closure ht⟩) :
    IsOrthMarked (compSet D x y d) n f := by
  classical
  have hd : d ∈ commSet D x ∩ commSet D y := by
    obtain ⟨htΓ, hreach⟩ := ht
    rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨c, hc, -⟩
    exacts [htΓ, hc.1]
  set Ω := compSet D x y d with hΩdef
  have hcls := isClass_inClosure_compSet hN hD hd
    (fun v hv => (hloc v hv).2.1) (fun v hv => (hloc v hv).2.2.1)
  have hS := setup_inClosure hD (fun z hz => hz.1.1.1) hcls
  have hcen := solvableRadical_le_center_of_noTwins hS
    (noOpenTwins_inClosure_compSet (fun v hv => (hloc v hv).1) fun v hv => (hloc v hv).2.2.2.2)
    (noClosedTwins_inClosure_compSet fun v hv => (hloc v hv).2.2.2.1)
  set S := Subgroup.closure Ω with hSdef
  set R := CFSG.solvableRadical S with hRdef
  have hRZ : R = Subgroup.center S :=
    le_antisymm hcen (CFSG.OddTranspositions.center_le_solvableRadical S)
  have hZX : Subgroup.center (S ⧸ R) = ⊥ := by
    have h1 := CFSG.OddTranspositions.center_le_solvableRadical (S ⧸ R)
    rwa [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient, le_bot_iff] at h1
  set tS : S := ⟨t, Subgroup.subset_closure ht⟩ with htS
  have hOX : IsOrthReflection (S ⧸ R) n f (QuotientGroup.mk' R tS) := by
    refine isOrthReflection_of_centerQuotient
      (((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans
        (QuotientGroup.quotientMulEquivOfEq hRZ)) ?_ hOt
    rfl
  have hclsΩ : inClosure Ω = {g | IsConj tS g} := by
    obtain ⟨t₀, ht₀⟩ := hcls
    have htt : IsConj t₀ tS := by
      have : tS ∈ inClosure Ω := ht
      rw [ht₀] at this
      exact this
    rw [ht₀]
    ext g
    exact ⟨fun h => (isConj_comm.mp htt).trans h, fun h => htt.trans h⟩
  have hE := isOddTransp_inClosure (Ω := Ω) hD (fun z hz => hz.1.1.1)
  have hnc := exists_not_commute_of_setup hS hns
  have hinjS := injOn_mk_of_le_center hE hRZ.le hnc
  have hcommiff : ∀ c ∈ inClosure Ω, ∀ c' ∈ inClosure Ω,
      (Commute c c' ↔ Commute (QuotientGroup.mk' R c) (QuotientGroup.mk' R c')) :=
    fun c hc c' hc' => ⟨fun h => h.map _, commute_of_commute_mk_of_le_center' hE hRZ.le hc hc'⟩
  obtain ⟨K, _, _, _, Q₀, ψ, v₀, hK, hQ₀, hψinj, hψrange, hv₀, hψt, hsym⟩ :=
    exists_symmetry_model_of_isOrthReflection hZX hOX
  have hψmem : ∀ g, ψ g ∈ matrixIsometries Q₀ := fun g => hψrange ▸ ⟨g, rfl⟩
  have hcS : ∀ a b : S, Commute a b ↔ Commute (a : G) (b : G) :=
    fun a b => ⟨fun h => h.map S.subtype, fun h => Subtype.ext h.eq⟩
  have hψc : ∀ a b : S ⧸ R, Commute a b ↔ Commute (ψ a) (ψ b) :=
    fun a b => ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  have hsymΩ : ∀ c ∈ inClosure Ω,
      ∃ a, Q₀ a = 1 ∧ ψ (QuotientGroup.mk' R c) = symmetryGL Q₀ a := by
    intro c hc
    rw [hclsΩ] at hc
    obtain ⟨g, rfl⟩ := isConj_iff.mp hc
    refine ⟨(ψ (QuotientGroup.mk' R g) : Matrix (Fin n) (Fin n) K) *ᵥ v₀, ?_, ?_⟩
    · rw [← hv₀]
      exact (mem_matrixIsometries_iff Q₀ _).mp (hψmem _) v₀
    · simp only [map_mul, map_inv]
      rw [hψt, conj_symmetryGL (hψmem _)]
  choose! ι₀ hι₀1 hι₀ψ using hsymΩ
  let ι : G → Fin n → K := fun z =>
    if hz : z ∈ Ω then ι₀ ⟨z, Subgroup.subset_closure hz⟩ else 0
  have hι : ∀ z (hz : z ∈ Ω), ι z = ι₀ ⟨z, Subgroup.subset_closure hz⟩ := fun z hz => by
    simp only [ι, dif_pos hz]
  have hmemΩ : ∀ z (hz : z ∈ Ω), (⟨z, Subgroup.subset_closure hz⟩ : S) ∈ inClosure Ω :=
    fun z hz => hz
  have hψι : ∀ z (hz : z ∈ Ω), ψ (QuotientGroup.mk' R ⟨z, Subgroup.subset_closure hz⟩) =
      symmetryGL Q₀ (ι z) := fun z hz => by rw [hι z hz]; exact hι₀ψ _ (hmemΩ z hz)
  have hι1 : ∀ z ∈ Ω, Q₀ (ι z) = 1 := fun z hz => by rw [hι z hz]; exact hι₀1 _ (hmemΩ z hz)
  have hconjΩ : ∀ z ∈ Ω, ∀ z' ∈ Ω, z * z' * z⁻¹ ∈ Ω := by
    intro z hz z' hz'
    have h1 : (⟨z', Subgroup.subset_closure hz'⟩ : S) ∈ {g | IsConj tS g} := by
      rw [← hclsΩ]
      exact hz'
    have h2 : (⟨z, Subgroup.subset_closure hz⟩ * ⟨z', Subgroup.subset_closure hz'⟩ *
        ⟨z, Subgroup.subset_closure hz⟩⁻¹ : S) ∈ inClosure Ω := by
      rw [hclsΩ]
      exact (show IsConj tS _ from h1).trans (isConj_iff.mpr ⟨_, rfl⟩)
    exact h2
  refine ⟨K, inferInstance, inferInstance, inferInstance, Q₀, ι,
    by rw [Nat.card_eq_fintype_card, hK], hQ₀, hι1, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    obtain ⟨t', ht', hψt'⟩ := hsym v hv
    obtain ⟨g, rfl⟩ := isConj_iff.mp ht'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R g
    have hc : g * tS * g⁻¹ ∈ inClosure Ω := by
      rw [hclsΩ]
      exact isConj_iff.mpr ⟨g, rfl⟩
    refine ⟨((g * tS * g⁻¹ : S) : G), hc, ?_⟩
    apply eq_of_symmetryGL_eq hQ₀ (hι1 _ hc) hv
    rw [← hψι _ hc, ← hψt', Subtype.coe_eta]
    simp only [map_mul, map_inv]
  · intro z hz z' hz' hzz
    have h1 : ψ (QuotientGroup.mk' R ⟨z, Subgroup.subset_closure hz⟩) =
        ψ (QuotientGroup.mk' R ⟨z', Subgroup.subset_closure hz'⟩) := by
      rw [hψι z hz, hψι z' hz', hzz]
    exact congrArg Subtype.val (hinjS (hmemΩ z hz) (hmemΩ z' hz') (hψinj h1))
  · intro z hz z' hz'
    have hm := hconjΩ z hz z' hz'
    refine ⟨hm, ?_⟩
    have hb1 : Q₀ (reflect Q₀ (ι z) (ι z')) = 1 := by
      rw [map_of_mem (reflect_mem_orthogonalGroup Q₀ _), hι1 z' hz']
    apply eq_of_symmetryGL_eq hQ₀ (hι1 _ hm) hb1
    rw [← hψι _ hm]
    have h1 : (⟨z * z' * z⁻¹, Subgroup.subset_closure hm⟩ : S) =
        ⟨z, Subgroup.subset_closure hz⟩ * ⟨z', Subgroup.subset_closure hz'⟩ *
          ⟨z, Subgroup.subset_closure hz⟩⁻¹ := rfl
    rw [h1]
    simp only [map_mul, map_inv]
    rw [hψι z hz, hψι z' hz', conj_symmetryGL (symmetryGL_mem Q₀ _), symmetryGL_mulVec]
  · intro z hz z' hz'
    rw [← commute_symmetryGL_iff hQ₀ (hι1 z hz) (hι1 z' hz'), ← hψι z hz, ← hψι z' hz',
      ← hψc, ← hcommiff _ (hmemΩ z hz) _ (hmemΩ z' hz'), hcS]
  ·
    have htop : Subgroup.closure (QuotientGroup.mk' R '' inClosure Ω) = ⊤ := by
      rw [← MonoidHom.map_closure,
        show Subgroup.closure (inClosure Ω) = ⊤ from Subgroup.closure_closure_coe_preimage,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)]
    have hgenM : matrixIsometries Q₀ ≤
        Subgroup.closure (symmetryGL Q₀ '' {v | Q₀ v = 1}) := by
      rw [← hψrange, MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨ι₀ c, hι₀1 c hc, (hι₀ψ c hc).symm⟩
    intro g hg
    have hg' : matrixLinearIso.symm g ∈ matrixIsometries Q₀ := by
      change matrixLinearIso (matrixLinearIso.symm g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀
      rwa [MulEquiv.apply_symm_apply]
    have h1 := Subgroup.mem_map_of_mem matrixLinearIso.toMonoidHom (hgenM hg')
    rw [MonoidHom.map_closure] at h1
    have h2 : matrixLinearIso.toMonoidHom '' (symmetryGL Q₀ '' {v | Q₀ v = 1}) =
        reflect Q₀ '' {v | Q₀ v = 1} := by
      rw [Set.image_image]
      exact Set.image_congr fun v _ => matrixLinearIso_symmetryGL
    rw [h2] at h1
    simpa using h1

theorem isOrthMarked_pivot (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    IsOrthMarked (commSet D x ∩ commSet D y) n f := by
  have hdΓ := d_mem_commSet_inter hC hx hy
  obtain ⟨t, ht, hOt⟩ := twelveSix_sp_component hIH hC hMZ hα hs hn hf hSp hx hy hxy
  rw [← compSet_eq_of_not_disconnected hdΓ
    (not_disconnected_commSet_inter hC hMZ hα hs hn hf hSp hx hy hxy)]
  exact isOrthMarked_compSet_of_isOrthReflection hC.setup.normal hC.setup.oddT
    (fun v hv => localPivot_of_mem hC hMZ hα hs hn hf hSp hv.1.1.1
      ⟨hx.1, hv.1.1.2.1.symm, fun h => hv.1.1.2.2 h.symm⟩
      ⟨hy.1, hv.1.2.2.1.symm, fun h => hv.1.2.2.2 h.symm⟩ hxy)
    (not_isSolvable_closure_of_subset hC hMZ hα hs hn hf hSp hx hy hxy
      (gammaAt_self_subset_compSet hdΓ)) ht hOt

theorem isOrthMarked_commSet_inter (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hwv : Commute w v) :
    IsOrthMarked (commSet D hC.d ∩ commSet D w) n f := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hv.1 hC.hd)
  set φ := MulAut.conj g with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem g h⟩
    have := hC.setup.conj_mem g⁻¹ h
    simpa [mul_assoc] using this
  have hφv : φ v = hC.d := by rw [MulAut.conj_apply, hg]
  have hwv' : w ≠ v := by
    rintro rfl
    exact hwd hv.2.1
  have hx : φ hC.d ∈ commSet D hC.d := by
    have h := (mem_commSet_map_iff φ hφD (a := v) (z := hC.d)).mpr
      ⟨hC.hd, hv.2.1.symm, fun h => hv.2.2 h.symm⟩
    rwa [hφv] at h
  have hy : φ w ∈ commSet D hC.d := by
    have h := (mem_commSet_map_iff φ hφD (a := v) (z := w)).mpr ⟨hw, hwv, hwv'⟩
    rwa [hφv] at h
  have hxy : ¬ Commute (φ hC.d) (φ w) := fun h => hwd ((commute_map_iff φ).mp h).symm
  have hM := (isOrthMarked_pivot hIH hC hMZ hα hs hn hf hSp hx hy hxy).preimage φ
  have hset : φ ⁻¹' (commSet D (φ hC.d) ∩ commSet D (φ w)) =
      commSet D hC.d ∩ commSet D w := by
    ext z
    rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_inter_iff, mem_commSet_map_iff φ hφD,
      mem_commSet_map_iff φ hφD]
  rwa [hset] at hM

omit [Finite G] in
theorem exists_quadraticForm_of_isOrthMarked {hC : HypothesisC D} {hα : hC.alpha = {hC.d}}
    {k : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2] (c : SpChart hC hα k F) {Γ : Set G}
    (hΓ : Γ ⊆ commSet D hC.d) {n f : ℕ} (hnk : n = 2 * k) (hn : 4 ≤ n)
    (hF : Nat.card F = 2 ^ f) (h : IsOrthMarked Γ n f) :
    ∃ Q : QuadraticForm F (Fin k ⊕ Fin k → F), (∀ a b, polar Q a b = spForm k F a b) ∧
      (∀ z ∈ commSet D hC.d, (z ∈ Γ ↔ Q (c.vec z) = 1)) ∧
      ∀ g : StatedSp k F, (∀ v, Q (spEnd g v) = Q v) →
        g ∈ Subgroup.closure ((fun a => spTransvection a 1) '' {a | Q a = 1}) := by
  classical
  obtain ⟨K, _, _, _, Q₀, ι, hK, hQ₀, h1, hsurj, hinj, hconj, hcomm, hgen⟩ := h
  choose! zOf hzOfΓ hzOfι using hsurj
  let φ : (Fin n → K) → (Fin k ⊕ Fin k → F) := fun x => c.vec (zOf x)
  have hzOf : ∀ z ∈ Γ, zOf (ι z) = z := fun z hz =>
    hinj (hzOfΓ _ (h1 z hz)) hz (hzOfι _ (h1 z hz))
  have hφconj : ∀ w x, Q₀ w = 1 → Q₀ x = 1 →
      φ (reflect Q₀ w x) = φ x + spForm k F (φ x) (φ w) • φ w := by
    intro w x hw hx
    have hzw := hzOfΓ w hw
    have hzx := hzOfΓ x hx
    obtain ⟨hm, he⟩ := hconj (zOf w) hzw (zOf x) hzx
    have hre : zOf (reflect Q₀ w x) = zOf w * zOf x * (zOf w)⁻¹ := by
      rw [← hzOfι w hw, ← hzOfι x hx, ← he, hzOfι w hw, hzOfι x hx, hzOf _ hm]
    have hv : c.vec (zOf w * zOf x * (zOf w)⁻¹) =
        spEnd (c.ρ ⟨zOf w, mem_Halpha_of_mem_commSet hC hα (hΓ hzw)⟩) (c.vec (zOf x)) :=
      (c.vec_conj ⟨zOf w, mem_Halpha_of_mem_commSet hC hα (hΓ hzw)⟩ (hΓ hzx)).2
    show c.vec (zOf (reflect Q₀ w x)) =
      c.vec (zOf x) + spForm k F (c.vec (zOf x)) (c.vec (zOf w)) • c.vec (zOf w)
    rw [hre, hv, c.map_eq _ (hΓ hzw), spEnd_spTransvection, one_mul]
  have hφcomm : ∀ x y, Q₀ x = 1 → Q₀ y = 1 →
      (spForm k F (φ x) (φ y) = 0 ↔ polar Q₀ x y = 0) := by
    intro x y hx hy
    rw [← c.commute_iff _ (hΓ (hzOfΓ x hx)) _ (hΓ (hzOfΓ y hy)),
      hcomm _ (hzOfΓ x hx) _ (hzOfΓ y hy), hzOfι x hx, hzOfι y hy]
  have hdimU : finrank K (Fin n → K) = n := by simp
  have hdimV : finrank F (Fin k ⊕ Fin k → F) = n := by simp [hnk, two_mul]
  obtain ⟨Q, hpol, hQ, hgenQ⟩ := exists_quadraticForm_of_marked (b := spForm k F) (φ := φ) hQ₀
    (by rw [hdimU]; omega) (fun v => spForm_self v)
    (fun v hv => spForm_nondegenerate.1 v hv) (hK.trans hF.symm) (hdimV.trans hdimU.symm)
    hφconj hφcomm hgen
  have hgenSp : ∀ g : StatedSp k F, (∀ v, Q (spEnd g v) = Q v) →
      g ∈ Subgroup.closure ((fun a => spTransvection a 1) '' {a | Q a = 1}) := by
    intro g hg
    have h1 := hgenQ (spLin k F g) hg
    have h2 : {t | ∃ a, Q a = 1 ∧ t = CFSG.ClassicalGroups.Alternating.symplecticTransvection
        (spForm k F) (fun v => spForm_self v) a 1} =
        spLin k F '' ((fun a => spTransvection a 1) '' {a | Q a = 1}) := by
      ext t
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨spTransvection a 1, ⟨a, ha, rfl⟩, spLin_spTransvection a 1⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, spLin_spTransvection a 1⟩
    rw [h2, ← MonoidHom.map_closure] at h1
    exact (Subgroup.mem_map_iff_mem spLin_injective).mp h1
  refine ⟨Q, hpol, fun z hz => ⟨fun hzΓ => (hQ _).mpr ⟨ι z, h1 z hzΓ, ?_⟩, fun hz1 => ?_⟩,
    hgenSp⟩
  · show c.vec (zOf (ι z)) = c.vec z
    rw [hzOf z hzΓ]
  · obtain ⟨x, hx, hφx⟩ := (hQ _).mp hz1
    have : zOf x = z := c.injOn (hΓ (hzOfΓ x hx)) hz hφx
    rw [← this]
    exact hzOfΓ x hx

theorem exists_quadraticForm_commSet_inter (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {k : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2] (c : SpChart hC hα k F)
    (hnk : n = 2 * k) (hF : Nat.card F = 2 ^ f)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hwv : Commute w v) :
    ∃ Q : QuadraticForm F (Fin k ⊕ Fin k → F), (∀ a b, polar Q a b = spForm k F a b) ∧
      (∀ z ∈ commSet D hC.d, (z ∈ commSet D w ↔ Q (c.vec z) = 1)) ∧
      ∀ g : StatedSp k F, (∀ v, Q (spEnd g v) = Q v) →
        g ∈ Subgroup.closure ((fun a => spTransvection a 1) '' {a | Q a = 1}) := by
  obtain ⟨Q, hpol, hQ, hgen⟩ := exists_quadraticForm_of_isOrthMarked c Set.inter_subset_left hnk
    hn hF (isOrthMarked_commSet_inter hIH hC hMZ hα hs hn hf hSp hv hw hwd hwv)
  exact ⟨Q, hpol, fun z hz => ⟨fun h => (hQ z hz).mp ⟨hz, h⟩, fun h => ((hQ z hz).mpr h).2⟩,
    hgen⟩

end CFSG.OddTranspositions.PartThree
