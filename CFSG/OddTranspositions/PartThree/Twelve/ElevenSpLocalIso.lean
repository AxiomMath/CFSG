module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpConj
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocalIso
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpLocal
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpOverlap
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull
open QuadraticMap

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D} {B : SpBranch hC}
  {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (fixing mem_fixing)

omit [DecidableEq F] in
private theorem mem_Halpha_of_mem_Halpha_conj_of_commute (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d) {h : G}
    (hh : h ∈ Halpha D (hC.conj g).alpha) (hcomm : Commute h hC.d) :
    h ∈ Halpha D hC.alpha := by
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  have hset : g⁻¹ * (hC.conj g).d * (g⁻¹)⁻¹ = hC.d := by
    rw [HypothesisC.conj_d hC g]
    group
  have hm : g⁻¹ * (hC.conj g).d * (g⁻¹)⁻¹ ∈ commSet D (hC.conj g).d := hset ▸ hdv
  have hle := inf_centralizer_le_Halpha_conj (B := B.conj g)
    (SpChart.conj (B := B) c g) (g⁻¹) hm
  have hα : ((hC.conj g).conj g⁻¹).alpha = hC.alpha := by
    rw [HypothesisC.conj_alpha, HypothesisC.conj_alpha]
    ext x
    simp only [cimg, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      convert hz using 1
      group
    · intro hx
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩
  rw [hα] at hle
  refine hle ⟨hh, ?_⟩
  rw [hset]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq

omit [DecidableEq F] in
private theorem mem_Halpha_conj_of_mem_Halpha_of_commute (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d) {h : G}
    (hh : h ∈ Halpha D hC.alpha) (hcomm : Commute h (hC.conj g).d) :
    h ∈ Halpha D (hC.conj g).alpha := by
  have hle := inf_centralizer_le_Halpha_conj (B := B) c g hv
  refine hle ⟨hh, ?_⟩
  rw [← HypothesisC.conj_d hC g]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq

omit [Fintype F] [DecidableEq F] in
private theorem mem_spMarkedStab_iff_commute {g : G}
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hdv : hC.d ∈ commSet D (hC.conj g).d)
    (h : ↥(Halpha D (hC.conj g).alpha)) :
    ev h ∈ spMarkedStab (cv.vec hC.d) ↔ Commute (h : G) hC.d := by
  rw [spMarkedStab, Subgroup.mem_comap, mem_fixing]
  constructor
  · intro hv
    have h1 : spEnd (ev h).1 (cv.vec hC.d) = cv.vec hC.d := by
      rw [spEnd_apply]
      exact hv (cv.vec hC.d) (Set.mem_singleton _)
    rw [hev h] at h1
    have h2 : cv.vec ((h : G) * hC.d * (h : G)⁻¹) = cv.vec hC.d := by
      rw [(SpChart.vec_conj cv h hdv).2]
      exact h1
    have h3 : (h : G) * hC.d * (h : G)⁻¹ = hC.d :=
      cv.injOn (SpChart.vec_conj cv h hdv).1 hdv h2
    rw [Commute]
    calc (h : G) * hC.d = ((h : G) * hC.d * (h : G)⁻¹) * (h : G) := by group
      _ = hC.d * (h : G) := by rw [h3]
  · intro hcomm v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    have h1 : (h : G) * hC.d * (h : G)⁻¹ = hC.d := by
      rw [Commute] at hcomm
      calc (h : G) * hC.d * (h : G)⁻¹ = (hC.d * (h : G)) * (h : G)⁻¹ := by rw [hcomm]
        _ = hC.d := by group
    change spEnd (ev h).1 (cv.vec hC.d) = cv.vec hC.d
    rw [hev h, ← (SpChart.vec_conj cv h hdv).2, h1]

omit [DecidableEq F] in
private theorem eq_mLift_of_mForm_eq_one_of_polar_mU_eq_zero
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {X : MSpace k F}
    (hX : mForm Q₀ X = 1) (hXU : polar (mForm Q₀) mU X = 0) :
    X = mLift Q₀ X.2 := by
  rcases X with ⟨⟨a, b⟩, x⟩
  have hb : b = 0 := by
    have h := hXU
    rw [polar_mForm (Q₀ := Q₀) hQ₀ mU ((a, b), x)] at h
    simpa [mU] using h
  subst hb
  have ha : a * a = 1 + Q₀ x := by
    have h : a * a + Q₀ x = 1 := by
      simpa [pow_two] using hX
    have h2 : Q₀ x + Q₀ x = 0 := CharTwo.add_self_eq_zero (Q₀ x)
    calc a * a = a * a + Q₀ x + Q₀ x := by rw [add_assoc, h2, add_zero]
      _ = 1 + Q₀ x := by rw [h]
  have hfrob : (frobeniusEquiv F 2) a = 1 + Q₀ x := by
    rw [frobeniusEquiv_apply, frobenius_def, pow_two]
    exact ha
  have haeq : a = (frobeniusEquiv F 2).symm (1 + Q₀ x) := by
    rw [← hfrob, RingEquiv.symm_apply_apply]
  simp [mLift, haeq]

omit [DecidableEq F] in
private theorem exists_mLift_eq_of_isometry {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγU : γ mU = V₀) {W : MSpace k F} (hW : mForm Q₀ W = 1)
    (hWV₀ : polar (mForm Q₀) W V₀ = 0) (hWne : W ≠ V₀) :
    ∃ x : Fin k ⊕ Fin k → F, x ≠ 0 ∧ γ (mLift Q₀ x) = W := by
  set X : MSpace k F := γ.symm W with hXdef
  have hγX : γ X = W := LinearEquiv.apply_symm_apply γ W
  have hXnorm : mForm Q₀ X = 1 := by
    have h := hγ X
    rw [hγX, hW] at h
    exact h.symm
  have hXU : polar (mForm Q₀) mU X = 0 := by
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hγ) X mU
    rw [hγU, hγX] at h1
    rw [polar_comm, ← h1]
    exact hWV₀
  have hXlift : X = mLift Q₀ X.2 :=
    eq_mLift_of_mForm_eq_one_of_polar_mU_eq_zero hQ₀ hXnorm hXU
  have hXsec : X.2 ≠ 0 := by
    intro h0
    apply hWne
    calc W = γ X := hγX.symm
      _ = γ (mLift Q₀ X.2) := congrArg γ hXlift
      _ = γ (mLift Q₀ 0) := by rw [h0]
      _ = γ mU := by simp [mLift, mU]
      _ = V₀ := hγU
  refine ⟨X.2, hXsec, ?_⟩
  rw [← hXlift]
  exact hγX

omit [DecidableEq F] in
private theorem modelChart_mRefl_mU_eq {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F} (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) :
    e ⟨mRefl Q₀ mU, mRefl_mem_centralizer_of_polar_eq_zero hV₀perp⟩ =
      (spTransvection y' 1, Multiplicative.ofAdd 1) := by
  have h := he.2.2.2 y' hy' (by
    rw [hγy']
    exact mRefl_mem_centralizer_of_polar_eq_zero hV₀perp)
  have heq : (⟨mRefl Q₀ (γ (mLift Q₀ y')), (by
      rw [hγy']
      exact mRefl_mem_centralizer_of_polar_eq_zero hV₀perp)⟩ :
        ↥(Subgroup.centralizer {mRefl Q₀ V₀})) =
      ⟨mRefl Q₀ mU, mRefl_mem_centralizer_of_polar_eq_zero hV₀perp⟩ := by
    apply Subtype.ext
    show mRefl Q₀ (γ (mLift Q₀ y')) = mRefl Q₀ mU
    rw [hγy']
  rw [← heq]
  exact h

omit [DecidableEq F] in
private theorem mem_spMarkedStab_model_iff_commute
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0) (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e)
    (m : ↥(Subgroup.centralizer {mRefl Q₀ V₀})) :
    e m ∈ spMarkedStab y' ↔ Commute (m : MGroup Q₀) (mRefl Q₀ mU) := by
  have hmemU := mRefl_mem_centralizer_of_polar_eq_zero hV₀perp
  have heU := modelChart_mRefl_mU_eq hV₀perp hy' hγy' he
  rw [spMarkedStab, Subgroup.mem_comap, mem_fixing]
  constructor
  · intro h
    have hfix : spEnd (e m).1 y' = y' := by
      rw [spEnd_apply]
      exact h y' (Set.mem_singleton y')
    have hcomm1 : Commute (e m).1 (spTransvection y' 1) :=
      (commute_spTransvection_one_iff hy').mpr hfix
    have hcommU : Commute (e m) (e ⟨mRefl Q₀ mU, hmemU⟩) := by
      rw [Prod.commute_iff]
      exact ⟨by rw [heU]; exact hcomm1, Commute.all _ _⟩
    exact (Commute.of_map e.injective hcommU).map (Subgroup.subtype _)
  · intro h
    have hcommU : Commute (e m) (e ⟨mRefl Q₀ mU, hmemU⟩) := by
      have hm : Commute m ⟨mRefl Q₀ mU, hmemU⟩ := Subtype.ext h
      exact hm.map e.toMonoidHom
    rw [Prod.commute_iff, heU] at hcommU
    have hfix := (commute_spTransvection_one_iff hy').mp hcommU.1
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    change spEnd (e m).1 y' = y'
    exact hfix

omit [DecidableEq F] in
private theorem mem_Halpha_of_mem_spMarkedStab (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    (ev.symm p : G) ∈ Halpha D hC.alpha := by
  have hp : ev (ev.symm p) ∈ spMarkedStab (cv.vec hC.d) := by
    rw [MulEquiv.apply_symm_apply]
    exact p.2
  have hcomm : Commute (ev.symm p : G) hC.d :=
    (mem_spMarkedStab_iff_commute (B := B) (g := g) cv ev hev
      (mem_commSet_symm hC.hd hv) (ev.symm p)).mp hp
  exact mem_Halpha_of_mem_Halpha_conj_of_commute (B := B) (g := g) c hv (ev.symm p).2 hcomm

omit [DecidableEq F] in
private theorem mem_centralizer_mRefl_of_mem_spMarkedStab (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    {V₀ : MSpace k F}
    (hθv : ((θ (⟨(hC.conj g).d,
      mem_Halpha_of_mem_commSet hC B.hα hv⟩ : ↥(Halpha D hC.alpha)) :
        ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ V₀)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    ((θ (⟨(ev.symm p : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
        ↥(Halpha D hC.alpha)) :
        ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) ∈
      Subgroup.centralizer {mRefl Q₀ V₀} := by
  set hH : ↥(Halpha D hC.alpha) :=
    ⟨(ev.symm p : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ with hHdef
  set hV : ↥(Halpha D hC.alpha) :=
    ⟨(hC.conj g).d, mem_Halpha_of_mem_commSet hC B.hα hv⟩ with hVdef
  have hcommv : Commute (hH : G) (hV : G) := by
    have h := commute_d_of_mem_Halpha (hC.conj g) (B.conj g).hα (ev.symm p)
    simpa [hHdef, hVdef] using h
  have hcommH : Commute hH hV := Commute.of_map (Subgroup.subtype_injective _) hcommv
  have hmap : Commute ((θ hH : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀)
      ((θ hV : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) :=
    (hcommH.map θ.toMonoidHom).map (Subgroup.subtype _)
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [← hθv]
  exact hmap

omit [Finite G] [DecidableEq F] in
private theorem theta_conj_d_eq_mRefl {c : SpChart hC B.hα k F} {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d)) :
    ((θ (⟨(hC.conj g).d, mem_Halpha_of_mem_commSet hC B.hα hv⟩ :
      ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) :
        MGroup Q₀) = mRefl Q₀ V₀ := by
  rw [hθ.2.2 _ hv, hV₀def]

private noncomputable def spMarkedStabHom (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    ↥(spMarkedStab (cv.vec hC.d)) →* ↥(spMarkedStab y') := by
  classical
  have hθv : ((θ (⟨(hC.conj g).d,
      mem_Halpha_of_mem_commSet hC B.hα hv⟩ : ↥(Halpha D hC.alpha)) :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ V₀ :=
    theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def
  let hH : ∀ p : ↥(spMarkedStab (cv.vec hC.d)), (ev.symm p : G) ∈ Halpha D hC.alpha :=
    fun p => mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p
  let f1 : ↥(spMarkedStab (cv.vec hC.d)) →* ↥(Halpha D (hC.conj g).alpha) :=
    ev.symm.toMonoidHom.comp (spMarkedStab (cv.vec hC.d)).subtype
  let f1G : ↥(spMarkedStab (cv.vec hC.d)) →* G :=
    (Subgroup.subtype (Halpha D (hC.conj g).alpha)).comp f1
  let f2 : ↥(spMarkedStab (cv.vec hC.d)) →* ↥(Halpha D hC.alpha) := f1G.codRestrict _ hH
  let f3 : ↥(spMarkedStab (cv.vec hC.d)) →* MGroup Q₀ :=
    (Subgroup.subtype (Subgroup.centralizer {mRefl Q₀ mU})).comp (θ.toMonoidHom.comp f2)
  let hm3 : ∀ p : ↥(spMarkedStab (cv.vec hC.d)), f3 p ∈ Subgroup.centralizer {mRefl Q₀ V₀} :=
    fun p => mem_centralizer_mRefl_of_mem_spMarkedStab (B := B) (g := g)
      c hv cv ev hev hθv p
  let f4 : ↥(spMarkedStab (cv.vec hC.d)) →* ↥(Subgroup.centralizer {mRefl Q₀ V₀}) :=
    f3.codRestrict _ hm3
  let hStab : ∀ p : ↥(spMarkedStab (cv.vec hC.d)),
      e (f4 p) ∈ spMarkedStab y' := by
    intro p
    refine (mem_spMarkedStab_model_iff_commute hV₀perp hy' hγy' he (f4 p)).mpr ?_
    change Commute ((θ (f2 p) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀)
      (mRefl Q₀ mU)
    exact Subgroup.mem_centralizer_singleton_iff.mp (θ (f2 p)).2
  let f5 : ↥(spMarkedStab (cv.vec hC.d)) →* SpMarkedGroup k F := e.toMonoidHom.comp f4
  exact f5.codRestrict _ hStab

omit [DecidableEq F] in
private theorem spMarkedStabHom_apply (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
      SpMarkedGroup k F) =
      e (⟨((θ (⟨(ev.symm p : G),
          mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
            ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀),
        mem_centralizer_mRefl_of_mem_spMarkedStab (B := B) (g := g)
          c hv cv ev hev (theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def) p⟩ :
          ↥(Subgroup.centralizer {mRefl Q₀ V₀})) := rfl

omit [DecidableEq F] in
private theorem spMarkedStabHom_injective (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    Function.Injective (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp
      hy' hγy' he hθ) := by
  intro a b h
  have h1 : (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp hy' hγy'
      he hθ a : SpMarkedGroup k F) =
      spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ b :=
    congrArg Subtype.val h
  rw [spMarkedStabHom_apply (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ a,
    spMarkedStabHom_apply (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ b]
    at h1
  have h2 := e.injective h1
  have h3 : ((θ (⟨(ev.symm a : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev a⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) =
      ((θ (⟨(ev.symm b : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev b⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) :=
    congrArg (fun x : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) => (x : MGroup Q₀)) h2
  have h4 : (θ (⟨(ev.symm a : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev a⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
      θ (⟨(ev.symm b : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev b⟩ :
          ↥(Halpha D hC.alpha)) := Subtype.ext h3
  have h5 : (⟨(ev.symm a : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev a⟩ :
          ↥(Halpha D hC.alpha)) =
      ⟨(ev.symm b : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev b⟩ :=
    θ.injective h4
  have h6 : (ev.symm a : G) = (ev.symm b : G) :=
    congrArg (fun x : ↥(Halpha D hC.alpha) => (x : G)) h5
  exact Subtype.ext (ev.symm.injective (Subtype.ext h6))

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem commute_of_theta_eq {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    {h a : ↥(Halpha D hC.alpha)} {m r : MGroup Q₀}
    (hθh : ((θ h : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = m)
    (hθa : ((θ a : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = r)
    (hmr : Commute m r) : Commute (h : G) (a : G) := by
  have h1 : Commute (θ h) (θ a) := Commute.of_map (Subgroup.subtype_injective _)
    (by simpa only [Subgroup.coe_subtype, hθh, hθa] using hmr)
  exact (Commute.of_map θ.injective h1).map (Subgroup.subtype _)

omit [DecidableEq F] in
private theorem spMarkedStabHom_surjective_commutes (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (m : ↥(Subgroup.centralizer {mRefl Q₀ V₀}))
    (hmU : Commute (m : MGroup Q₀) (mRefl Q₀ mU)) :
    ∃ h : ↥(Halpha D hC.alpha), (h : G) ∈ Halpha D (hC.conj g).alpha ∧
      Commute (h : G) hC.d ∧
      (θ h : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        ⟨(m : MGroup Q₀), Subgroup.mem_centralizer_singleton_iff.mpr hmU⟩ := by
  classical
  have hθd : ((θ (⟨hC.d, hu⟩ : ↥(Halpha D hC.alpha)) :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ mU := hθ.2.1
  have hθv : ((θ (⟨(hC.conj g).d,
      mem_Halpha_of_mem_commSet hC B.hα hv⟩ : ↥(Halpha D hC.alpha)) :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ V₀ :=
    theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def
  have hmCU : (m : MGroup Q₀) ∈ Subgroup.centralizer {mRefl Q₀ mU} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hmU
  let h : ↥(Halpha D hC.alpha) := θ.symm ⟨(m : MGroup Q₀), hmCU⟩
  have hθh : (θ h : ↥(Subgroup.centralizer {mRefl Q₀ mU})) = ⟨(m : MGroup Q₀), hmCU⟩ :=
    MulEquiv.apply_symm_apply θ _
  have hcommv : Commute (h : G) (hC.conj g).d :=
    commute_of_theta_eq (hθh := congrArg Subtype.val hθh) (hθa := hθv)
      (Subgroup.mem_centralizer_singleton_iff.mp m.2)
  have hhv : (h : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_conj_of_mem_Halpha_of_commute (B := B) (g := g) c hv h.2 hcommv
  have hcommd : Commute (h : G) hC.d :=
    commute_of_theta_eq (hθh := congrArg Subtype.val hθh) (hθa := hθd) hmU
  exact ⟨h, hhv, hcommd, hθh⟩

omit [DecidableEq F] in
private theorem exists_semilinear_localIso_theta_eq (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    {h : ↥(Halpha D hC.alpha)} (hhv : (h : G) ∈ Halpha D (hC.conj g).alpha)
    {m : MGroup Q₀}
    (hθh : ((θ h : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = m)
    (p : ↥(spMarkedStab (cv.vec hC.d)))
    (hp : ev.symm p = ⟨(h : G), hhv⟩) :
    ((θ (⟨(ev.symm p : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
        ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = m := by
  have harg : (⟨(ev.symm p : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
        ↥(Halpha D hC.alpha)) = h := by
    apply Subtype.ext
    exact congrArg (fun x : ↥(Halpha D (hC.conj g).alpha) => (x : G)) hp
  rw [harg]
  exact hθh

omit [DecidableEq F] in
private theorem spMarkedStabHom_surjective (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    Function.Surjective (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp
      hy' hγy' he hθ) := by
  intro q
  classical
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  let m : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) := e.symm q
  have heq : e m = q := MulEquiv.apply_symm_apply e q
  have hq : e m ∈ spMarkedStab y' := by rw [heq]; exact q.2
  have hmU : Commute (m : MGroup Q₀) (mRefl Q₀ mU) :=
    (mem_spMarkedStab_model_iff_commute hV₀perp hy' hγy' he m).mp hq
  obtain ⟨h, hhv, hcommd, hθh⟩ :=
    spMarkedStabHom_surjective_commutes (B := B) c hv hV₀def hθ m hmU
  let p : ↥(spMarkedStab (cv.vec hC.d)) :=
    ⟨ev ⟨(h : G), hhv⟩,
      (mem_spMarkedStab_iff_commute (B := B) (g := g) cv ev hev hdv
        ⟨(h : G), hhv⟩).mpr hcommd⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  rw [spMarkedStabHom_apply (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p]
  have hm3p : ((θ (⟨(ev.symm p : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
        ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) =
      (m : MGroup Q₀) :=
    exists_semilinear_localIso_theta_eq (B := B) (g := g) c hv cv ev hev hhv
      (congrArg (fun x : ↥(Subgroup.centralizer {mRefl Q₀ mU}) => (x : MGroup Q₀)) hθh)
      p (MulEquiv.symm_apply_apply ev _)
  rw [show (⟨((θ (⟨(ev.symm p : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀),
      mem_centralizer_mRefl_of_mem_spMarkedStab (B := B) (g := g)
        c hv cv ev hev (theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def) p⟩ :
        ↥(Subgroup.centralizer {mRefl Q₀ V₀})) = m from
    Subtype.ext hm3p]
  rw [heq]

private noncomputable def spMarkedStabEquiv (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    ↥(spMarkedStab (cv.vec hC.d)) ≃* ↥(spMarkedStab y') :=
  MulEquiv.ofBijective (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp
      hy' hγy' he hθ)
    ⟨spMarkedStabHom_injective (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ,
      spMarkedStabHom_surjective (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ⟩

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_apply (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
      SpMarkedGroup k F) =
      (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
        SpMarkedGroup k F) := rfl

omit [DecidableEq F] in
private theorem mem_centralizer_mRefl_mLift {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγU : γ mU = V₀) (a : Fin k ⊕ Fin k → F) :
    mRefl Q₀ (γ (mLift Q₀ a)) ∈ Subgroup.centralizer {mRefl Q₀ V₀} := by
  refine mRefl_mem_centralizer_of_polar_eq_zero ?_
  have h1 : polar (mForm Q₀) (γ (mLift Q₀ a)) (γ mU) =
      polar (mForm Q₀) (mLift Q₀ a) mU :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hγ) _ _
  rw [hγU] at h1
  rw [h1, polar_comm]
  exact polar_mU_mLift a

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_base (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ
      ⟨(spTransvection (cv.vec hC.d) 1, Multiplicative.ofAdd 1),
        Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton (cv.vec hC.d) 1)⟩ :
      SpMarkedGroup k F) = (spTransvection y' 1, Multiplicative.ofAdd 1) := by
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  let p0 : ↥(spMarkedStab (cv.vec hC.d)) :=
    ⟨(spTransvection (cv.vec hC.d) 1, Multiplicative.ofAdd 1),
      Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton (cv.vec hC.d) 1)⟩
  have hp0 : (p0 : SpMarkedGroup k F) = ev ⟨hC.d,
      mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv⟩ := by
    change (spTransvection (cv.vec hC.d) 1, Multiplicative.ofAdd 1) =
      ev ⟨hC.d, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv⟩
    rw [hev3 hC.d hdv]
  have hsymm : (ev.symm p0 : ↥(Halpha D (hC.conj g).alpha)) =
      ⟨hC.d, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv⟩ := by
    apply ev.injective
    rw [MulEquiv.apply_symm_apply]
    exact hp0
  have hval : (spMarkedStabHom (B := B) (γ := γ) c hv cv ev hev hV₀def hV₀perp
      hy' hγy' he hθ p0 : SpMarkedGroup k F) =
      e ⟨mRefl Q₀ mU, mRefl_mem_centralizer_of_polar_eq_zero hV₀perp⟩ := by
    rw [spMarkedStabHom_apply]
    congr 1
    apply Subtype.ext
    exact exists_semilinear_localIso_theta_eq (B := B) (g := g) c hv cv ev hev
      (h := ⟨hC.d, hu⟩) (mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv)
      hθ.2.1 p0 hsymm
  rw [spMarkedStabEquiv_apply, hval]
  exact modelChart_mRefl_mU_eq hV₀perp hy' hγy' he

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_forward_mark (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F} (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (hθv : ((θ (⟨(hC.conj g).d,
      mem_Halpha_of_mem_commSet hC B.hα hv⟩ : ↥(Halpha D hC.alpha)) :
        ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ V₀)
    (p : ↥(spMarkedStab (cv.vec hC.d))) {z : G} (hz_d : z ∈ commSet D hC.d)
    (hzH : z ∈ Halpha D (hC.conj g).alpha)
    (hsymm : (ev.symm p : ↥(Halpha D (hC.conj g).alpha)) = ⟨z, hzH⟩)
    {x : Fin k ⊕ Fin k → F} (hx0 : x ≠ 0)
    (hθzx : (θ (⟨z, mem_Halpha_of_mem_commSet hC B.hα hz_d⟩ :
        ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        mRefl Q₀ (γ (mLift Q₀ x))) :
    (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
      SpMarkedGroup k F) = (spTransvection x 1, Multiplicative.ofAdd 1) := by
  rw [spMarkedStabEquiv_apply, spMarkedStabHom_apply]
  have hC : (⟨((θ (⟨(ev.symm p : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀),
      mem_centralizer_mRefl_of_mem_spMarkedStab (B := B) (g := g)
        c hv cv ev hev hθv p⟩ : ↥(Subgroup.centralizer {mRefl Q₀ V₀})) =
      ⟨mRefl Q₀ (γ (mLift Q₀ x)),
        mem_centralizer_mRefl_mLift (Q₀ := Q₀) he.1 he.2.1 x⟩ := by
    apply Subtype.ext
    change ((θ (⟨(ev.symm p : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) =
      mRefl Q₀ (γ (mLift Q₀ x))
    rw [show (⟨(ev.symm p : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
          ↥(Halpha D hC.alpha)) = ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz_d⟩ from by
      apply Subtype.ext
      exact congrArg (fun x : ↥(Halpha D (hC.conj g).alpha) => (x : G)) hsymm]
    exact hθzx
  rw [hC]
  exact he.2.2.2 x hx0 (mem_centralizer_mRefl_mLift (Q₀ := Q₀) he.1 he.2.1 x)

omit [Fintype F] [DecidableEq F] in
private theorem exists_ev_symm_eq_of_mem_spMarkedSet {g : G}
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    (hdv : hC.d ∈ commSet D (hC.conj g).d)
    (p : ↥(spMarkedStab (cv.vec hC.d)))
    (hp : (p : SpMarkedGroup k F) ∈ spMarkedSet) :
    ∃ (z : G) (_ : z ∈ commSet D (hC.conj g).d)
      (hzH : z ∈ Halpha D (hC.conj g).alpha),
      (ev.symm p : ↥(Halpha D (hC.conj g).alpha)) = ⟨z, hzH⟩ ∧
      Commute z hC.d := by
  obtain ⟨a, ha0, hpa⟩ := hp
  obtain ⟨z, hz, hzv⟩ := cv.exists_vec a ha0
  have hzH : z ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz
  have hevz : (ev ⟨z, hzH⟩ : SpMarkedGroup k F) =
      (spTransvection a 1, Multiplicative.ofAdd 1) := by
    rw [hev3 z hz, hzv]
  have hp_eq : (p : SpMarkedGroup k F) = ev ⟨z, hzH⟩ := hpa.trans hevz.symm
  have hsymm : (ev.symm p : ↥(Halpha D (hC.conj g).alpha)) = ⟨z, hzH⟩ := by
    apply ev.injective
    rw [MulEquiv.apply_symm_apply]
    exact hp_eq
  have hcommz : Commute z hC.d :=
    (mem_spMarkedStab_iff_commute (B := B) (g := g) cv ev hev hdv ⟨z, hzH⟩).mp
      (by rw [← hp_eq]; exact p.2)
  exact ⟨z, hz, hzH, hsymm, hcommz⟩

omit [Finite G] [DecidableEq F] in
private theorem exists_mLift_eq_of_mem_commSet (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγU : γ mU = V₀) {z : G} (hz : z ∈ commSet D (hC.conj g).d)
    (hz_d : z ∈ commSet D hC.d) :
    ∃ x : Fin k ⊕ Fin k → F, x ≠ 0 ∧ γ (mLift Q₀ x) = mLift Q₀ (c.vec z) := by
  have hWV₀ : polar (mForm Q₀) (mLift Q₀ (c.vec z)) V₀ = 0 := by
    rw [hV₀def, polar_mForm (Q₀ := Q₀) hQ₀]
    simpa [mLift] using (c.commute_iff z hz_d ((hC.conj g).d) hv).mp hz.2.1
  have hWne : mLift Q₀ (c.vec z) ≠ V₀ := by
    intro h
    have hvec : c.vec z = c.vec ((hC.conj g).d) := by
      have := congrArg (fun X : MSpace k F => X.2) h
      simpa [hV₀def, mLift] using this
    exact hz.2.2 (c.injOn hz_d hv hvec)
  exact exists_mLift_eq_of_isometry (Q₀ := Q₀) hQ₀ hγ hγU
    (mForm_mLift (Q₀ := Q₀) (c.vec z)) hWV₀ hWne

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem eq_transvection_of_ev_symm_eq {g : G}
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {p : ↥(spMarkedStab (cv.vec hC.d))} {z : G}
    (hz : z ∈ commSet D (hC.conj g).d)
    {hzH : z ∈ Halpha D (hC.conj g).alpha}
    (hsymm : (ev.symm p : ↥(Halpha D (hC.conj g).alpha)) = ⟨z, hzH⟩) :
    (p : SpMarkedGroup k F) = (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1) := by
  calc (p : SpMarkedGroup k F) = ev (ev.symm p) := (MulEquiv.apply_symm_apply ev p).symm
    _ = ev ⟨z, hzH⟩ := by rw [hsymm]
    _ = ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ := by
      rw [show (⟨z, hzH⟩ : ↥(Halpha D (hC.conj g).alpha)) =
        ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ from
          Subtype.ext rfl]
    _ = (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1) := hev3 z hz

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_mem_spMarkedSet_forward (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    ((p : SpMarkedGroup k F) ∈ spMarkedSet →
      (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
        SpMarkedGroup k F) ∈ spMarkedSet) := by
  classical
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  have hθv := theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def
  intro hp
  obtain ⟨z, hz, hzH, hsymm, hcommz⟩ :=
    exists_ev_symm_eq_of_mem_spMarkedSet (B := B) cv ev hev hev3 hdv p hp
  by_cases hzd : z = hC.d
  · subst z
    have hp_p0 : p = (⟨(spTransvection (cv.vec hC.d) 1, Multiplicative.ofAdd 1),
        Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton (cv.vec hC.d) 1)⟩ :
        ↥(spMarkedStab (cv.vec hC.d))) :=
      Subtype.ext (eq_transvection_of_ev_symm_eq (B := B) (g := g) cv ev hev3 hdv hsymm)
    rw [hp_p0]
    rw [spMarkedStabEquiv_base (B := B) c hv cv ev hev hev3 hV₀def hV₀perp
      hy' hγy' he hθ]
    exact ⟨y', hy', rfl⟩
  · have hz_d : z ∈ commSet D hC.d := ⟨hz.1, hcommz, hzd⟩
    obtain ⟨x, hx0, hγx⟩ :=
      exists_mLift_eq_of_mem_commSet (B := B) c hv hQ₀ hV₀def he.1 he.2.1 hz hz_d
    have hθzx : (θ (⟨z, mem_Halpha_of_mem_commSet hC B.hα hz_d⟩ :
        ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) =
        mRefl Q₀ (γ (mLift Q₀ x)) := by
      rw [hθ.2.2 z hz_d, ← hγx]
    exact ⟨x, hx0, spMarkedStabEquiv_forward_mark (B := B) c hv cv ev hev hV₀def hV₀perp
      hy' hγy' he hθ hθv p hz_d hzH hsymm hx0 hθzx⟩

omit [DecidableEq F] in
private theorem theta_eq_mRefl_of_spMarkedStabEquiv_eq (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0) (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) {b : Fin k ⊕ Fin k → F} (hb0 : b ≠ 0)
    (hpb : (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
      SpMarkedGroup k F) = (spTransvection b 1, Multiplicative.ofAdd 1)) :
    (θ (⟨(ev.symm p : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
        ↥(Halpha D hC.alpha)) : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ b)) := by
  have hθv : ((θ (⟨(hC.conj g).d,
      mem_Halpha_of_mem_commSet hC B.hα hv⟩ : ↥(Halpha D hC.alpha)) :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ V₀ :=
    theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def
  rw [spMarkedStabEquiv_apply, spMarkedStabHom_apply] at hpb
  have hCore : (⟨((θ (⟨(ev.symm p : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
          ↥(Halpha D hC.alpha)) : ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀),
      mem_centralizer_mRefl_of_mem_spMarkedStab (B := B) (g := g)
        c hv cv ev hev hθv p⟩ : ↥(Subgroup.centralizer {mRefl Q₀ V₀})) =
      ⟨mRefl Q₀ (γ (mLift Q₀ b)),
        mem_centralizer_mRefl_mLift (Q₀ := Q₀) he.1 he.2.1 b⟩ := by
    apply e.injective
    rw [hpb, he.2.2.2 b hb0 (mem_centralizer_mRefl_mLift (Q₀ := Q₀) he.1 he.2.1 b)]
  exact congrArg (fun x : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) => (x : MGroup Q₀)) hCore

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_reverse_orthogonal
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    {b : Fin k ⊕ Fin k → F} {t : ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (ht : (t : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ b))) :
    mForm Q₀ (γ (mLift Q₀ b)) = 1 ∧ polar (mForm Q₀) mU (γ (mLift Q₀ b)) = 0 := by
  have hcommθ : Commute (mRefl Q₀ (γ (mLift Q₀ b))) (mRefl Q₀ mU) := by
    rw [← ht]
    exact Subgroup.mem_centralizer_singleton_iff.mp t.2
  have hγb : mForm Q₀ (γ (mLift Q₀ b)) = 1 := by rw [hγ]; exact mForm_mLift b
  have hγbperp : polar (mForm Q₀) mU (γ (mLift Q₀ b)) = 0 := by
    have hcomm' : Commute (CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀)
        (γ (mLift Q₀ b))) (CFSG.ClassicalGroups.Orthogonal.reflect (mForm Q₀) mU) :=
      hcommθ.map (Subgroup.subtype _)
    have h := (CFSG.ClassicalGroups.Orthogonal.commute_reflect_iff (Q := mForm Q₀) hγb
      (mForm_mU (Q₀ := Q₀))).mp hcomm'
    rw [polar_comm]
    exact h
  exact ⟨hγb, hγbperp⟩

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_mem_spMarkedSet_reverse_zero (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0) (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) (b : Fin k ⊕ Fin k → F) (hb0 : b ≠ 0)
    (hpb : (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
      SpMarkedGroup k F) = (spTransvection b 1, Multiplicative.ofAdd 1))
    (hb' : (γ (mLift Q₀ b)).2 = 0) :
    (p : SpMarkedGroup k F) ∈ spMarkedSet := by
  classical
  have hzH_H : (ev.symm p : G) ∈ Halpha D hC.alpha :=
    mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p
  have hθz : (θ (⟨(ev.symm p : G), hzH_H⟩ :
      ↥(Halpha D hC.alpha)) : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ b)) :=
    theta_eq_mRefl_of_spMarkedStabEquiv_eq (B := B) c hv cv ev hev hV₀def
      hV₀perp hy' hγy' he hθ p hb0 hpb
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  obtain ⟨hγb, hγbperp⟩ := spMarkedStabEquiv_reverse_orthogonal he.1 hθz
  have hγbU : γ (mLift Q₀ b) = mU := by
    have hlift := eq_mLift_of_mForm_eq_one_of_polar_mU_eq_zero hQ₀ hγb hγbperp
    rw [hb'] at hlift
    simpa [mLift, mU] using hlift
  have hθd' : (θ (⟨(ev.symm p : G), hzH_H⟩ :
      ↥(Halpha D hC.alpha)) : MGroup Q₀) = mRefl Q₀ mU := by
    rw [hθz, hγbU]
  have hsymm : (ev.symm p : ↥(Halpha D (hC.conj g).alpha)) =
      ⟨hC.d, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv⟩ := by
    apply Subtype.ext
    exact congrArg (fun x : ↥(Halpha D hC.alpha) => (x : G))
      (θ.injective (Subtype.ext (hθd'.trans hθ.2.1.symm)))
  have hp0 : p = (⟨(spTransvection (cv.vec hC.d) 1, Multiplicative.ofAdd 1),
      Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton (cv.vec hC.d) 1)⟩ :
      ↥(spMarkedStab (cv.vec hC.d))) :=
    Subtype.ext (eq_transvection_of_ev_symm_eq (B := B) (g := g) cv ev hev3 hdv hsymm)
  rw [hp0]; exact ⟨cv.vec hC.d, cv.vec_ne_zero hC.d hdv, rfl⟩

omit [Finite G] [DecidableEq F] in
private theorem exists_theta_eq_mRefl_of_vec_eq_second (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {b : Fin k ⊕ Fin k → F}
    (hb' : (γ (mLift Q₀ b)).2 ≠ 0)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (hlift : γ (mLift Q₀ b) = mLift Q₀ (γ (mLift Q₀ b)).2) :
    ∃ (z : G) (hz : z ∈ commSet D hC.d),
      (θ (⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ :
        ↥(Halpha D hC.alpha)) : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ b)) := by
  obtain ⟨z, hz, hzv⟩ := c.exists_vec (γ (mLift Q₀ b)).2 hb'
  have hθeq : (θ (⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ :
      ↥(Halpha D hC.alpha)) : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ b)) := by
    rw [hθ.2.2 z hz, hzv, ← hlift]
  exact ⟨z, hz, hθeq⟩

omit [Finite G] [DecidableEq F] in
private theorem ne_conj_d_of_theta_eq_mRefl {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγU : γ mU = V₀)
    {b : Fin k ⊕ Fin k → F} (hb0 : b ≠ 0)
    (hγb : mForm Q₀ (γ (mLift Q₀ b)) = 1) (hV₀ : mForm Q₀ V₀ = 1)
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθv : ((θ (⟨(hC.conj g).d,
      mem_Halpha_of_mem_commSet hC B.hα hv⟩ : ↥(Halpha D hC.alpha)) :
      ↥(Subgroup.centralizer {mRefl Q₀ mU})) : MGroup Q₀) = mRefl Q₀ V₀)
    {zH : ↥(Halpha D (hC.conj g).alpha)} {hzH_H : (zH : G) ∈ Halpha D hC.alpha}
    (hθz : (θ (⟨(zH : G), hzH_H⟩ : ↥(Halpha D hC.alpha)) : MGroup Q₀) =
      mRefl Q₀ (γ (mLift Q₀ b))) :
    (zH : G) ≠ (hC.conj g).d := by
  intro hzvEq
  have hθzH_v : (θ (⟨(zH : G), hzH_H⟩ : ↥(Halpha D hC.alpha)) : MGroup Q₀) =
      mRefl Q₀ V₀ := by
    have hEq : (⟨(zH : G), hzH_H⟩ : ↥(Halpha D hC.alpha)) =
        ⟨(hC.conj g).d, mem_Halpha_of_mem_commSet hC B.hα hv⟩ :=
      Subtype.ext hzvEq
    rw [hEq]
    exact hθv
  have hrefl : mRefl Q₀ (γ (mLift Q₀ b)) = mRefl Q₀ V₀ := hθz.symm.trans hθzH_v
  have hvec : γ (mLift Q₀ b) = V₀ :=
    (CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflect_iff (Q := mForm Q₀)
      (nondegenerate_polarBilin_mForm (Q₀ := Q₀) hQ₀) hγb hV₀).mp
      (congrArg Subtype.val hrefl)
  have h1 : mLift Q₀ b = mU := by
    apply γ.injective
    rw [hvec, hγU]
  have hb_eq : b = 0 := by
    simpa [mLift, mU] using congrArg (fun X : MSpace k F => X.2) h1
  exact hb0 hb_eq

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_mem_spMarkedSet_reverse_nonzero (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0) (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) (b : Fin k ⊕ Fin k → F) (hb0 : b ≠ 0)
    (hpb : (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
      SpMarkedGroup k F) = (spTransvection b 1, Multiplicative.ofAdd 1))
    (hb' : (γ (mLift Q₀ b)).2 ≠ 0) :
    (p : SpMarkedGroup k F) ∈ spMarkedSet := by
  classical
  let zH : ↥(Halpha D (hC.conj g).alpha) := ev.symm p
  have hzH_H : (zH : G) ∈ Halpha D hC.alpha :=
    mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p
  have hθz : (θ (⟨(zH : G), hzH_H⟩ :
      ↥(Halpha D hC.alpha)) : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ b)) :=
    theta_eq_mRefl_of_spMarkedStabEquiv_eq (B := B) c hv cv ev hev hV₀def
      hV₀perp hy' hγy' he hθ p hb0 hpb
  have hV₀ : mForm Q₀ V₀ = 1 := by rw [hV₀def]; exact mForm_mLift _
  obtain ⟨hγb, hγbperp⟩ := spMarkedStabEquiv_reverse_orthogonal he.1 hθz
  have hlift := eq_mLift_of_mForm_eq_one_of_polar_mU_eq_zero hQ₀ hγb hγbperp
  obtain ⟨z, hz, hθeq⟩ :=
    exists_theta_eq_mRefl_of_vec_eq_second (B := B) c hb' hθ hlift
  have hzG : z = (zH : G) := congrArg Subtype.val
    (θ.injective (Subtype.ext (hθeq.trans hθz.symm)))
  have hcommv_z : Commute z ((hC.conj g).d) := by
    simpa [hzG] using commute_d_of_mem_Halpha (hC.conj g) (B.conj g).hα zH
  have hzv_ne : z ≠ (hC.conj g).d := by
    rw [hzG]
    exact ne_conj_d_of_theta_eq_mRefl (B := B) hv hQ₀ he.2.1 hb0 hγb hV₀
      (theta_conj_d_eq_mRefl (B := B) hv hθ hV₀def) hθz
  have hz_v : z ∈ commSet D (hC.conj g).d := ⟨hz.1, hcommv_z, hzv_ne⟩
  have hsymm : (ev.symm p : ↥(Halpha D (hC.conj g).alpha)) =
      ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz_v⟩ :=
    Subtype.ext hzG.symm
  have hp_mark := eq_transvection_of_ev_symm_eq (B := B) (g := g) cv ev hev3 hz_v hsymm
  exact ⟨cv.vec z, cv.vec_ne_zero z hz_v, hp_mark⟩

private theorem spMarkedStabEquiv_mem_spMarkedSet_reverse (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    ((spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
        SpMarkedGroup k F) ∈ spMarkedSet →
      (p : SpMarkedGroup k F) ∈ spMarkedSet) := by
  classical
  intro hp
  obtain ⟨b, hb0, hpb⟩ := hp
  by_cases hb' : (γ (mLift Q₀ b)).2 = 0
  · exact spMarkedStabEquiv_mem_spMarkedSet_reverse_zero (B := B) c hv cv ev hev hev3 hQ₀ hV₀def
      hV₀perp hy' hγy' he hθ p b hb0 hpb hb'
  · exact spMarkedStabEquiv_mem_spMarkedSet_reverse_nonzero (B := B) c hv cv ev hev hev3 hQ₀ hV₀def
      hV₀perp hy' hγy' he hθ p b hb0 hpb hb'

private theorem spMarkedStabEquiv_mem_spMarkedSet (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      ev ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    ((p : SpMarkedGroup k F) ∈ spMarkedSet ↔
      (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy' he hθ p :
        SpMarkedGroup k F) ∈ spMarkedSet) :=
  ⟨fun hp => spMarkedStabEquiv_mem_spMarkedSet_forward c hv cv ev hev hev3 hQ₀
      hV₀def hV₀perp hy' hγy' he hθ p hp,
    fun hp => spMarkedStabEquiv_mem_spMarkedSet_reverse c hv cv ev hev hev3 hQ₀
      hV₀def hV₀perp hy' hγy' he hθ p hp⟩

omit [DecidableEq F] in
private theorem modelChart_symm_mark_mgroup {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγU : γ mU = V₀)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) :
    (e.symm (spTransvection a 1, Multiplicative.ofAdd 1) : MGroup Q₀) =
      mRefl Q₀ (γ (mLift Q₀ a)) := by
  let hmem := mem_centralizer_mRefl_mLift (Q₀ := Q₀) hγ hγU a
  have hval : e ⟨mRefl Q₀ (γ (mLift Q₀ a)), hmem⟩ =
      (spTransvection a 1, Multiplicative.ofAdd 1) := he.2.2.2 a ha hmem
  have hsymm : e.symm (spTransvection a 1, Multiplicative.ofAdd 1) =
      ⟨mRefl Q₀ (γ (mLift Q₀ a)), hmem⟩ := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hval]
  rw [hsymm]

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_symm_apply (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (ev : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev : ∀ h, (ev h).1 = cv.ρ h)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F}
    (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0)
    (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (p : ↥(spMarkedStab (cv.vec hC.d))) :
    ((e.symm (spMarkedStabEquiv (B := B) c hv cv ev hev hV₀def hV₀perp hy' hγy'
      he hθ p) : ↥(Subgroup.centralizer {mRefl Q₀ V₀})) : MGroup Q₀) =
      (θ (⟨((ev.symm p : ↥(Halpha D (hC.conj g).alpha)) : G),
        mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv ev hev p⟩ :
          ↥(Halpha D hC.alpha)) : MGroup Q₀) := by
  rw [spMarkedStabEquiv_apply, spMarkedStabHom_apply]
  rw [MulEquiv.symm_apply_apply]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem spMarked_extension_mark {σ : F ≃+* F}
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {β : SpMarkedGroup k F ≃* SpMarkedGroup k F}
    (hA : Function.Bijective A) (hadd : ∀ x z, A (x + z) = A x + A z)
    (hsmul : ∀ (c : F) x, A (c • x) = σ c • A x)
    (hform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hsp : ∀ p x, spEnd (β p).1 (A x) = A (spEnd p.1 x))
    (hsecond : ∀ p : SpMarkedGroup k F, (β p).2 = p.2)
    (a : Fin k ⊕ Fin k → F) (ε : Multiplicative (ZMod 2)) :
    β (spTransvection a 1, ε) = (spTransvection (A a) 1, ε) := by
  apply Prod.ext
  · apply CFSG.RankThree.PartOne.KCSpComm.eq_of_spEnd_eq
    intro y
    obtain ⟨x, rfl⟩ := hA.2 y
    rw [hsp, spEnd_spTransvection, spEnd_spTransvection]
    simp only [one_mul]
    rw [hadd, hsmul, hform]
  · rw [hsecond]

omit [DecidableEq F] in
private theorem exists_semilinear_localIso_chart
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) (V₀ : MSpace k F)
    (hV₀ : mForm Q₀ V₀ = 1) (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    (hV₀U : V₀ ≠ mU) :
    ∃ (γ : MSpace k F ≃ₗ[F] MSpace k F)
      (eV : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F)
      (y' : Fin k ⊕ Fin k → F),
      IsModelChartAt Q₀ V₀ γ eV ∧ (∀ X, mForm Q₀ (γ X) = mForm Q₀ X) ∧ γ mU = V₀ ∧
        y' ≠ 0 ∧ γ (mLift Q₀ y') = mU := by
  obtain ⟨γ, eV, he⟩ := exists_isModelChartAt (Q₀ := Q₀) hQ₀ V₀ hV₀
  have hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X := he.1
  have hγU : γ mU = V₀ := he.2.1
  obtain ⟨y', hy'0, hγy'U⟩ :=
    exists_mLift_eq_of_isometry (Q₀ := Q₀) hQ₀ hγ hγU (mForm_mU) hV₀perp hV₀U.symm
  exact ⟨γ, eV, y', he, hγ, hγU, hy'0, hγy'U⟩

omit [DecidableEq F] in
private theorem exists_semilinear_localIso_mark {g : G}
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (evc : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      evc ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)} {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {eV : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ eV)
    (β : SpMarkedGroup k F ≃* SpMarkedGroup k F)
    {σ : F ≃+* F} {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    (hAbij : Function.Bijective A) (hAadd : ∀ x z, A (x + z) = A x + A z)
    (hAsmul : ∀ (t : F) x, A (t • x) = σ t • A x)
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hβsp : ∀ p x, spEnd (β p).1 (A x) = A (spEnd p.1 x))
    (hβ2 : ∀ p, (β p).2 = p.2)
    (ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ V₀}))
    (hψp : ∀ x, ψ₁ x = eV.symm (β (evc x))) :
    ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
        MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ (A (cv.vec z)))) := by
  intro z hz
  have hzH : z ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz
  have hzmark : evc ⟨z, hzH⟩ =
      (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1) := hev3 z hz
  have hAne : A (cv.vec z) ≠ 0 := by
    intro h0
    have hzero : cv.vec z = 0 := hAbij.1 (by
      rw [h0]
      exact show 0 = A 0 from (map_zero (AddMonoidHom.mk' A hAadd)).symm)
    exact cv.vec_ne_zero z hz hzero
  have hβz : β (evc ⟨z, hzH⟩) =
      (spTransvection (A (cv.vec z)) 1, Multiplicative.ofAdd 1) := by
    rw [hzmark]
    exact spMarked_extension_mark (σ := σ) (A := A) hAbij hAadd hAsmul hAform hβsp hβ2
      (cv.vec z) (Multiplicative.ofAdd 1)
  calc (ψ₁ ⟨z, hzH⟩ : MGroup Q₀) =
      (eV.symm (β (evc ⟨z, hzH⟩)) : MGroup Q₀) := by rw [hψp]
    _ = (eV.symm (spTransvection (A (cv.vec z)) 1, Multiplicative.ofAdd 1) :
        MGroup Q₀) := by rw [hβz]
    _ = mRefl Q₀ (γ (mLift Q₀ (A (cv.vec z)))) :=
      modelChart_symm_mark_mgroup he.1 he.2.1 he hAne

omit [Finite G] [DecidableEq F] in
private theorem exists_eq_mRefl_of_mem_commSet
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγU : γ mU = V₀) {m : MGroup Q₀}
    (hm : m ∈ commSet (mClass Q₀) (mRefl Q₀ V₀)) :
    ∃ x : Fin k ⊕ Fin k → F, x ≠ 0 ∧ m = mRefl Q₀ (γ (mLift Q₀ x)) := by
  obtain ⟨Y, hYnorm, rfl⟩ := hm.1
  have hV₀ : mForm Q₀ V₀ = 1 := by rw [← hγU, hγ, mForm_mU]
  have hYV₀ : polar (mForm Q₀) Y V₀ = 0 :=
    (CFSG.ClassicalGroups.Orthogonal.commute_reflect_iff hYnorm hV₀).mp
      (hm.2.1.map (Subgroup.subtype _))
  obtain ⟨x, hx0, hγx⟩ := exists_mLift_eq_of_isometry (Q₀ := Q₀) hQ₀ hγ hγU hYnorm hYV₀
    fun h => hm.2.2 (by rw [h])
  exact ⟨x, hx0, by rw [hγx]⟩

omit [DecidableEq F] in
private theorem exists_semilinear_localIso_onto {g : G}
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (evc : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev3 : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      evc ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
        (spTransvection (cv.vec z) 1, Multiplicative.ofAdd 1))
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {V₀ : MSpace k F}
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {eV : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ eV)
    (β : SpMarkedGroup k F ≃* SpMarkedGroup k F)
    {σ : F ≃+* F} {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    (hAbij : Function.Bijective A) (hAadd : ∀ x z, A (x + z) = A x + A z)
    (hAsmul : ∀ (t : F) x, A (t • x) = σ t • A x)
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hβsp : ∀ p x, spEnd (β p).1 (A x) = A (spEnd p.1 x))
    (hβ2 : ∀ p, (β p).2 = p.2)
    (ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ V₀}))
    (hψp : ∀ x, ψ₁ x = eV.symm (β (evc x))) :
    ∀ m ∈ commSet (mClass Q₀) (mRefl Q₀ V₀),
      ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
        (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = m := by
  intro m hm
  obtain ⟨x, hx0, hmx⟩ :=
    exists_eq_mRefl_of_mem_commSet (Q₀ := Q₀) hQ₀ he.1 he.2.1 hm
  obtain ⟨a, ha⟩ := hAbij.2 x
  have ha0 : a ≠ 0 := fun h0 =>
    hx0 (by rw [← ha, h0]; exact map_zero (AddMonoidHom.mk' A hAadd))
  obtain ⟨z, hz, hzv⟩ := cv.exists_vec a ha0
  have hzH : z ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz
  have hzmark : evc ⟨z, hzH⟩ = (spTransvection a 1, Multiplicative.ofAdd 1) := by
    simpa [hzv] using hev3 z hz
  have hβz : β (evc ⟨z, hzH⟩) =
      (spTransvection x 1, Multiplicative.ofAdd 1) := by
    rw [hzmark, spMarked_extension_mark (σ := σ) (A := A) hAbij hAadd hAsmul hAform
      hβsp hβ2 a (Multiplicative.ofAdd 1), ha]
  have hψz : (ψ₁ ⟨z, hzH⟩ : MGroup Q₀) = mRefl Q₀ (γ (mLift Q₀ x)) := by
    calc (ψ₁ ⟨z, hzH⟩ : MGroup Q₀) =
        (eV.symm (β (evc ⟨z, hzH⟩)) : MGroup Q₀) := by rw [hψp]
      _ = (eV.symm (spTransvection x 1, Multiplicative.ofAdd 1) : MGroup Q₀) := by rw [hβz]
      _ = mRefl Q₀ (γ (mLift Q₀ x)) :=
        modelChart_symm_mark_mgroup he.1 he.2.1 he hx0
  exact ⟨z, hz, by rw [hmx]; exact hψz⟩

omit [Finite G] [DecidableEq F] in
private theorem exists_semilinear_localIso_V0U (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F} (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d)) : V₀ ≠ mU := by
  intro h
  have hvec : c.vec (hC.conj g).d = 0 := by
    have := congrArg (fun X : MSpace k F => X.2) h
    simpa [hV₀def, mLift, mU] using this
  exact c.vec_ne_zero (hC.conj g).d hv hvec

omit [DecidableEq F] in
private theorem exists_semilinear_localIso_extension {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {y' : Fin k ⊕ Fin k → F}
    (α : ↥(spMarkedStab (cv.vec hC.d)) ≃* ↥(spMarkedStab y'))
    (hαmark : ∀ p : ↥(spMarkedStab (cv.vec hC.d)),
      (p : SpMarkedGroup k F) ∈ spMarkedSet ↔ (α p : SpMarkedGroup k F) ∈ spMarkedSet)
    (hαy : (α ⟨(spTransvection (cv.vec hC.d) 1, Multiplicative.ofAdd 1),
        Subgroup.mem_comap.mpr (spTransvection_mem_fixing_singleton (cv.vec hC.d) 1)⟩ :
          SpMarkedGroup k F) = (spTransvection y' 1, Multiplicative.ofAdd 1)) :
    ∃ (σ : F ≃+* F) (A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F))
      (β : SpMarkedGroup k F ≃* SpMarkedGroup k F),
      Function.Bijective A ∧ (∀ x z, A (x + z) = A x + A z) ∧
      (∀ (t : F) x, A (t • x) = σ t • A x) ∧
      (∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)) ∧
      A (cv.vec hC.d) = y' ∧
      (∀ p x, spEnd (β p).1 (A x) = A (spEnd p.1 x)) ∧ (∀ p, (β p).2 = p.2) ∧
      ∀ p : ↥(spMarkedStab (cv.vec hC.d)), β p = α p := by
  have hk : 2 ≤ k := B.two_le_rank hnk
  have hF4 : 4 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    exact B.four_le_two_pow
  have hy : cv.vec hC.d ≠ 0 := cv.vec_ne_zero hC.d (mem_commSet_symm hC.hd hv)
  exact exists_spMarked_extension (y := cv.vec hC.d) (y' := y') hk hF4 hy α hαmark hαy

omit [DecidableEq F] in
private theorem spMarkedStabEquiv_apply_eq_theta (c : SpChart hC B.hα k F) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (evc : ↥(Halpha D (hC.conj g).alpha) ≃* SpMarkedGroup k F)
    (hev1 : ∀ h, (evc h).1 = cv.ρ h)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {V₀ : MSpace k F} (hV₀def : V₀ = mLift Q₀ (c.vec (hC.conj g).d))
    (hV₀perp : polar (mForm Q₀) mU V₀ = 0)
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {y' : Fin k ⊕ Fin k → F} (hy' : y' ≠ 0) (hγy' : γ (mLift Q₀ y') = mU)
    {e : ↥(Subgroup.centralizer {mRefl Q₀ V₀}) ≃* SpMarkedGroup k F}
    (he : IsModelChartAt Q₀ V₀ γ e) {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (β : SpMarkedGroup k F ≃* SpMarkedGroup k F)
    (hβα : ∀ p : ↥(spMarkedStab (cv.vec hC.d)),
      β p = spMarkedStabEquiv (B := B) c hv cv evc hev1 hV₀def hV₀perp hy' hγy' he hθ p)
    (ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ V₀}))
    (hψp : ∀ x, ψ₁ x = e.symm (β (evc x))) :
    ∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀) := by
  intro r hr
  have hcommr : Commute (r : G) hC.d := commute_d_of_mem_Halpha hC B.hα r
  let p : ↥(spMarkedStab (cv.vec hC.d)) :=
    ⟨evc ⟨r, hr⟩,
      (mem_spMarkedStab_iff_commute (B := B) (g := g) cv evc hev1
        (mem_commSet_symm hC.hd hv) ⟨r, hr⟩).mpr hcommr⟩
  have hp : (p : SpMarkedGroup k F) = evc ⟨r, hr⟩ := rfl
  have hβEq : β (evc ⟨r, hr⟩) =
      spMarkedStabEquiv (B := B) c hv cv evc hev1 hV₀def hV₀perp hy' hγy' he hθ p := by
    rw [← hp]
    exact hβα p
  have hsymm : evc.symm p = ⟨(r : G), hr⟩ := by
    apply evc.injective
    rw [MulEquiv.apply_symm_apply]
  have hθeq : (θ (⟨((evc.symm p : ↥(Halpha D (hC.conj g).alpha)) : G),
      mem_Halpha_of_mem_spMarkedStab (B := B) (g := g) c hv cv evc hev1 p⟩ :
        ↥(Halpha D hC.alpha)) : MGroup Q₀) = (θ r : MGroup Q₀) :=
    exists_semilinear_localIso_theta_eq (B := B) (g := g) (h := r) c hv cv evc hev1
      hr rfl p hsymm
  calc (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (e.symm (β (evc ⟨r, hr⟩)) : MGroup Q₀) := by rw [hψp]
    _ = (e.symm (spMarkedStabEquiv (B := B) c hv cv evc hev1 hV₀def hV₀perp
        hy' hγy' he hθ p) : MGroup Q₀) := by rw [hβEq]
    _ = (θ r : MGroup Q₀) := by
      rw [spMarkedStabEquiv_symm_apply (B := B) c hv cv evc hev1 hV₀def hV₀perp
        hy' hγy' he hθ p]
      exact hθeq

theorem exists_semilinear_localIso (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) :
    ∃ (σ : F ≃+* F) (A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F))
      (γ : MSpace k F ≃ₗ[F] MSpace k F) (y' : Fin k ⊕ Fin k → F)
      (ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
        ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})),
      Function.Bijective A ∧ (∀ x z, A (x + z) = A x + A z) ∧
      (∀ (t : F) x, A (t • x) = σ t • A x) ∧
      (∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)) ∧
      (∀ X, mForm Q₀ (γ X) = mForm Q₀ X) ∧ γ mU = mLift Q₀ (c.vec (hC.conj g).d) ∧
      y' ≠ 0 ∧ γ (mLift Q₀ y') = mU ∧ A ((SpChart.conj (B := B) c g).vec hC.d) = y' ∧
      (∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀)) ∧
      (∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
        (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
          mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) ∧
      ∀ m ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
        ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
          (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = m := by
  let cv : SpChart (hC.conj g) (B.conj g).hα k F := SpChart.conj (B := B) c g
  let V₀ : MSpace k F := mLift Q₀ (c.vec (hC.conj g).d)
  have hV₀perp : polar (mForm Q₀) mU V₀ = 0 := polar_mU_mLift _
  obtain ⟨γ, eV, y', he, hγ, hγU, hy'0, hγy'⟩ :=
    exists_semilinear_localIso_chart (Q₀ := Q₀) hQ₀ V₀ (mForm_mLift _) hV₀perp
      (exists_semilinear_localIso_V0U (B := B) c hv rfl)
  obtain ⟨_hu_v, evc, hev1, _hev2, hev3⟩ := exists_spCoord (B := B.conj g) cv
  let α : ↥(spMarkedStab (cv.vec hC.d)) ≃* ↥(spMarkedStab y') :=
    spMarkedStabEquiv (B := B) c hv cv evc hev1 rfl hV₀perp hy'0 hγy' he hθ
  obtain ⟨σ, A, β, hAbij, hAadd, hAsmul, hAform, hAy, hβsp, hβ2, hβα⟩ :=
    exists_semilinear_localIso_extension (B := B) hv cv hnk hF α
      (spMarkedStabEquiv_mem_spMarkedSet (B := B) c hv cv evc hev1 hev3 hQ₀ rfl hV₀perp hy'0
        hγy' he hθ)
      (spMarkedStabEquiv_base (B := B) c hv cv evc hev1 hev3 rfl hV₀perp hy'0 hγy' he hθ)
  let ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ V₀}) := evc.trans (β.trans eV.symm)
  have hψp : ∀ x, ψ₁ x = eV.symm (β (evc x)) := fun _ => rfl
  refine ⟨σ, A, γ, y', ψ₁, hAbij, hAadd, hAsmul, hAform, hγ, hγU, hy'0, hγy', hAy,
    ?_, ?_, ?_⟩
  · exact spMarkedStabEquiv_apply_eq_theta (B := B) c hv cv evc hev1 rfl hV₀perp
      hy'0 hγy' he hθ β hβα ψ₁ hψp
  · exact exists_semilinear_localIso_mark (B := B) cv evc hev3 he
      β hAbij hAadd hAsmul hAform hβsp hβ2 ψ₁ hψp
  · exact exists_semilinear_localIso_onto (B := B) cv evc hev3 hQ₀ he β hAbij hAadd hAsmul
      hAform hβsp hβ2 ψ₁ hψp

end CFSG.OddTranspositions.PartThree.ElevenSp

end
