module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpLocalForms
public import CFSG.OddTranspositions.PartThree.Twelve.Branches
public import CFSG.Fischer.Uniq.Graph
import CFSG.OddTranspositions.PartThree.Twelve.NineGraphIso
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelOrder
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.OddTranspositions.PartThree.Nine.NineFiveGraph
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.OddTranspositions.PartThree.Twelve.NineSp
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpRegGraph
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFivePatch

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open
  CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull
open CFSG.OddTranspositions.QZ CFSG.GroupTheory.WeirSylow CFSG.Fischer
open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.EvenSporadicStandard.HNRecog.Section4

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D} {B : SpBranch hC}
  {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}


private def halphaSet : Set ↥D := {x | (x : G) ∈ Halpha D hC.alpha}

private def modelBaseSet (Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)) : Set ↥(mClass Q₀) :=
  {m | (m : MGroup Q₀) ∈ Subgroup.centralizer {mRefl Q₀ mU}}

omit [Finite G] [DecidableEq F] in
private lemma theta_mem_mClass (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) {x : G}
    (hxH : x ∈ Halpha D hC.alpha) (hxD : x ∈ D) :
    (θ ⟨x, hxH⟩ : MGroup Q₀) ∈ mClass Q₀ := by
  have hcomm : Commute x hC.d := commute_d_of_mem_Halpha hC B.hα ⟨x, hxH⟩
  by_cases hxd : x = hC.d
  · subst hxd
    rw [hθ.2.1]
    refine ⟨mLift Q₀ 0, mForm_mLift 0, ?_⟩
    rw [mLift_zero]
  · have hxd' : x ∈ commSet D hC.d := ⟨hxD, hcomm, hxd⟩
    rw [hθ.2.2 x hxd']
    exact ⟨mLift Q₀ (c.vec x), mForm_mLift _, rfl⟩

private noncomputable def baseMap (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) : ↥D → ↥(mClass Q₀) := by
  classical
  exact fun x => if hx : (x : G) ∈ Halpha D hC.alpha then
      ⟨(θ ⟨x, hx⟩ : MGroup Q₀), theta_mem_mClass (B := B) c hθ hx x.2⟩
    else ⟨mRefl Q₀ (mLift Q₀ 0), ⟨mLift Q₀ 0, mForm_mLift 0, rfl⟩⟩

omit [Finite G] [DecidableEq F] in
private lemma baseMap_of_mem (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) {x : ↥D} (hx : x ∈ halphaSet (hC := hC)) :
    (baseMap (B := B) c hθ x : MGroup Q₀) = (θ ⟨x, hx⟩ : MGroup Q₀) := by
  classical
  have hx' : (x : G) ∈ Halpha D hC.alpha := hx
  rw [baseMap, dif_pos hx']


@[instance_reducible] private noncomputable def conjActD :
    MulAction ↥(Halpha D hC.alpha) ↥D :=
  let smul : ↥(Halpha D hC.alpha) → ↥D → ↥D :=
    fun h x => ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩
  { smul := smul
    one_smul := fun x => by
      show smul 1 x = x
      apply Subtype.ext
      show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
      simp
    mul_smul := fun h k x => by
      show smul (h * k) x = smul h (smul k x)
      apply Subtype.ext
      show ((h * k : ↥(Halpha D hC.alpha)) : G) * (x : G) *
        ((h * k : ↥(Halpha D hC.alpha)) : G)⁻¹ =
        (h : G) * ((k : G) * (x : G) * (k : G)⁻¹) * (h : G)⁻¹
      simp [mul_assoc] }

attribute [local instance] conjActD

omit [Finite G] in
private lemma mem_baseSet_iff {B : SpBranch hC} {hu : hC.d ∈ Halpha D hC.alpha} {x : ↥D} :
    x ∈ halphaSet (hC := hC) ↔ (x : G) = hC.d ∨ (x : G) ∈ commSet D hC.d := by
  constructor
  · intro hx
    have hcomm : Commute (x : G) hC.d := commute_d_of_mem_Halpha hC B.hα ⟨x, hx⟩
    by_cases hxd : (x : G) = hC.d
    · exact Or.inl hxd
    · exact Or.inr ⟨x.2, hcomm, hxd⟩
  · rintro (h | h)
    · change (x : G) ∈ Halpha D hC.alpha
      rw [h]; exact hu
    · exact mem_Halpha_of_mem_commSet hC B.hα h

omit [CharP F 2] in
private lemma mem_modelBaseSet_iff {m : ↥(mClass Q₀)} :
    m ∈ modelBaseSet Q₀ ↔ (m : MGroup Q₀) = mRefl Q₀ mU ∨
      (m : MGroup Q₀) ∈ commSet (mClass Q₀) (mRefl Q₀ mU) := by
  constructor
  · intro hm
    have hcomm : Commute (m : MGroup Q₀) (mRefl Q₀ mU) :=
      Subgroup.mem_centralizer_singleton_iff.mp hm
    by_cases h : (m : MGroup Q₀) = mRefl Q₀ mU
    · exact Or.inl h
    · exact Or.inr ⟨m.2, hcomm, h⟩
  · rintro (h | h)
    · change (m : MGroup Q₀) ∈ Subgroup.centralizer {mRefl Q₀ mU}
      rw [h]; exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl _)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h.2.1

omit [Finite G] [CharP F 2] in
private lemma modelBaseSet_eq_baseSet :
    modelBaseSet Q₀ = CFSG.OddTranspositions.PartThree.baseSet (mClass Q₀) (mRefl Q₀ mU) :=
  Set.ext fun _ => mem_modelBaseSet_iff (Q₀ := Q₀)

omit [Finite G] [DecidableEq F] in
private lemma baseMap_mapsTo (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    Set.MapsTo (baseMap (B := B) c hθ) (halphaSet (hC := hC)) (modelBaseSet Q₀) := by
  intro x hx
  change (baseMap (B := B) c hθ x : MGroup Q₀) ∈
    Subgroup.centralizer {mRefl Q₀ mU}
  rw [baseMap_of_mem (B := B) c hθ hx]
  exact (θ ⟨x, hx⟩).2

omit [Finite G] [DecidableEq F] in
private lemma baseMap_injOn (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    Set.InjOn (baseMap (B := B) c hθ) (halphaSet (hC := hC)) := by
  intro x hx y hy hxy
  have hx' : (x : G) ∈ Halpha D hC.alpha := hx
  have hy' : (y : G) ∈ Halpha D hC.alpha := hy
  have h1 : (θ ⟨x, hx'⟩ : MGroup Q₀) = (θ ⟨y, hy'⟩ : MGroup Q₀) := by
    rw [← baseMap_of_mem (B := B) c hθ hx, ← baseMap_of_mem (B := B) c hθ hy]
    exact congrArg Subtype.val hxy
  have h2 : (⟨x, hx'⟩ : ↥(Halpha D hC.alpha)) = ⟨y, hy'⟩ :=
    θ.injective (Subtype.ext h1)
  exact Subtype.ext (congrArg (fun t : ↥(Halpha D hC.alpha) => (t : G)) h2)

omit [Finite G] in
private lemma baseMap_surjOn (c : SpChart hC B.hα k F)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    Set.SurjOn (baseMap (B := B) c hθ) (halphaSet (hC := hC)) (modelBaseSet Q₀) := by
  intro m hm
  rw [mem_modelBaseSet_iff] at hm
  rcases hm with h | h
  · refine ⟨⟨hC.d, hC.hd⟩, hu, ?_⟩
    apply Subtype.ext
    rw [baseMap_of_mem (B := B) c hθ hu, hθ.2.1, h]
  · obtain ⟨x, hxne, hmx⟩ := (mem_commSet_mRefl_mU_iff hQ₀).mp h
    obtain ⟨z, hz, hzv⟩ := c.exists_vec x hxne
    refine ⟨⟨z, hz.1⟩, mem_Halpha_of_mem_commSet hC B.hα hz, ?_⟩
    apply Subtype.ext
    rw [baseMap_of_mem (B := B) c hθ (mem_Halpha_of_mem_commSet hC B.hα hz),
      hθ.2.2 z hz, hzv, ← hmx]


omit [Finite G] [DecidableEq F] in
private lemma baseMap_equivariant (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (h : ↥(Halpha D hC.alpha)) {x : ↥D}
    (hx : x ∈ CFSG.OddTranspositions.PartThree.baseSet D hC.d) :
    (baseMap (B := B) c hθ
        ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
      (θ h : MGroup Q₀) * (baseMap (B := B) c hθ x : MGroup Q₀) *
        (θ h : MGroup Q₀)⁻¹ := by
  have hx' : (x : G) ∈ Halpha D hC.alpha :=
    (mem_baseSet_iff (B := B) (hu := hu)).mpr hx
  have hxmem : (⟨(h : G) * (x : G) * (h : G)⁻¹,
      hC.setup.conj_mem (h : G) x.2⟩ : ↥D) ∈ halphaSet (hC := hC) := by
    change ((⟨(h : G) * (x : G) * (h : G)⁻¹,
      hC.setup.conj_mem (h : G) x.2⟩ : ↥D) : G) ∈ Halpha D hC.alpha
    exact (h * ⟨x, hx'⟩ * h⁻¹).2
  have h1 : (baseMap (B := B) c hθ
      ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
      (θ ⟨(h : G) * (x : G) * (h : G)⁻¹, hxmem⟩ : MGroup Q₀) :=
    baseMap_of_mem (B := B) c hθ hxmem
  have h2 : (baseMap (B := B) c hθ x : MGroup Q₀) = (θ ⟨x, hx'⟩ : MGroup Q₀) :=
    baseMap_of_mem (B := B) c hθ hx'
  have h3 : (θ ⟨(h : G) * (x : G) * (h : G)⁻¹, hxmem⟩ : MGroup Q₀) =
      (θ h : MGroup Q₀) * (θ ⟨x, hx'⟩ : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹ := by
    have harg : (⟨(h : G) * (x : G) * (h : G)⁻¹, hxmem⟩ :
        ↥(Halpha D hC.alpha)) = h * ⟨x, hx'⟩ * h⁻¹ := by
      apply Subtype.ext
      rfl
    rw [harg, map_mul, map_mul, map_inv]
    rfl
  rw [h1, h3, h2]

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma exists_conj_of_mem_commSet (c : SpChart hC B.hα k F)
    {u v : G} (hu : u ∈ commSet D hC.d) (hv : v ∈ commSet D hC.d) :
    ∃ h : ↥(Halpha D hC.alpha), h * u * h⁻¹ = v := by
  obtain ⟨s, hs⟩ := exists_spEnd_eq (c.vec_ne_zero u hu) (c.vec_ne_zero v hv)
  obtain ⟨h, hh⟩ := c.surjective s
  refine ⟨h, ?_⟩
  have h1 := SpChart.vec_conj c h hu
  have h2 : c.vec ((h : G) * u * (h : G)⁻¹) = c.vec v := by
    rw [h1.2, hh, hs]
  exact c.injOn h1.1 hv h2

private abbrev residualCentralizer (g : G) : Subgroup ↥(Halpha D hC.alpha) :=
  (Subgroup.centralizer {(hC.conj g).d}).comap (Subgroup.subtype (Halpha D hC.alpha))

private abbrev residualSlice (g : G) : Set ↥D :=
  CFSG.OddTranspositions.PartThree.sliceSet D hC.d (hC.conj g).d

private noncomputable def residualMap (c : SpChart hC B.hα k F) (g : G)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀) : ↥D → ↥(mClass Q₀) := by
  classical
  exact fun x =>
    if hx : (x : G) ∈ commSet D (hC.conj g).d then
      ⟨(ψ ⟨x, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx⟩ : MGroup Q₀),
        hψmem x hx⟩
    else ⟨mRefl Q₀ (mLift Q₀ 0), ⟨mLift Q₀ 0, mForm_mLift 0, rfl⟩⟩

omit [DecidableEq F] in
private lemma residualMap_apply (c : SpChart hC B.hα k F) (g : G)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀) {x : ↥D} (hx : (x : G) ∈ commSet D (hC.conj g).d) :
    (residualMap (B := B) c g ψ hψmem x : MGroup Q₀) =
      (ψ ⟨x, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx⟩ : MGroup Q₀) := by
  classical
  simp only [residualMap, dif_pos hx]

omit [Finite G] in
private lemma mem_Halpha_conj_d (g : G) {hu : hC.d ∈ Halpha D hC.alpha} :
    (hC.conj g).d ∈ Halpha D (hC.conj g).alpha := by
  rw [HypothesisC.conj_alpha, HypothesisC.conj_d,
    Halpha_cimg hC.setup.normal g hC.alpha]
  exact Subgroup.mem_map.mpr ⟨hC.d, hu, rfl⟩

omit [Fintype F] [DecidableEq F] in
private lemma coord_ne_zero_of_not_commute {Y : MSpace k F}
    (h : ¬ Commute (mRefl Q₀ Y) (mRefl Q₀ mU)) : Y.1.2 ≠ 0 := fun hb =>
  h (Subgroup.mem_centralizer_singleton_iff.mp
    (mRefl_mem_centralizer_of_polar_eq_zero (by rw [polar_comm, polar_mU_eq_snd, hb])))

omit [DecidableEq F] in
private lemma not_commute_mRefl_of_not_commute (c : SpChart hC B.hα k F) (g : G)
    {ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {s : G} (hsHv : s ∈ Halpha D (hC.conj g).alpha) {Y : MSpace k F}
    (hYeq : (ψ ⟨s, hsHv⟩ : MGroup Q₀) = mRefl Q₀ Y)
    (hψd : ∀ hd : (hC.d : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ ⟨hC.d, hd⟩ : MGroup Q₀) = mRefl Q₀ mU)
    (hsd : ¬ Commute s hC.d) :
    ¬ Commute (mRefl Q₀ Y) (mRefl Q₀ mU) := by
  intro hc
  apply hsd
  have hdv : hC.d ∈ commSet D (hC.conj g).d :=
    ⟨hC.hd, hgv.2.1.symm, fun h => hgv.2.2 h.symm⟩
  have hdHv : (hC.d : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv
  have hc' : Commute (ψ ⟨s, hsHv⟩) (ψ ⟨hC.d, hdHv⟩) := by
    apply Subtype.ext
    show (ψ ⟨s, hsHv⟩ : MGroup Q₀) * (ψ ⟨hC.d, hdHv⟩ : MGroup Q₀) =
      (ψ ⟨hC.d, hdHv⟩ : MGroup Q₀) * (ψ ⟨s, hsHv⟩ : MGroup Q₀)
    rw [hYeq, hψd hdHv]
    exact hc.eq
  have h := hc'.map ψ.symm.toMonoidHom
  simpa using h.map (Subgroup.subtype (Halpha D (hC.conj g).alpha))

omit [DecidableEq F] in
private lemma coord_ne_zero_of_mem_residualSlice (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {s : ↥D} (hs : s ∈ residualSlice (hC := hC) g) {Y : MSpace k F}
    (hYeq : (ψ ⟨s, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hs.1⟩ :
      MGroup Q₀) = mRefl Q₀ Y) :
    Y.1.2 ≠ 0 := by
  have hψd : ∀ hd : (hC.d : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ ⟨hC.d, hd⟩ : MGroup Q₀) = mRefl Q₀ mU :=
    fun hd => by rw [hψθ ⟨hC.d, hu⟩ hd, hθ.2.1]
  exact coord_ne_zero_of_not_commute (not_commute_mRefl_of_not_commute (B := B) c g hgv
    (mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hs.1) hYeq hψd hs.2)

private lemma exists_residualMap_eq_mRefl_commute_iff (c : SpChart hC B.hα k F)
    (hnk : B.n = 2 * k) (hF : Nat.card F = 2 ^ B.f)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψform : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)))
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {s : ↥D} (hs : s ∈ residualSlice (hC := hC) g) :
    ∃ Y : MSpace k F,
      (residualMap (B := B) c g ψ hψmem s : MGroup Q₀) = mRefl Q₀ Y ∧
      ∀ h : ↥(Halpha D hC.alpha),
        (Commute (h : G) (s : G) ↔ Commute (θ h : MGroup Q₀) (mRefl Q₀ Y)) := by
  obtain ⟨Y, hY, hYeq, hform⟩ := hψform (s : G) hs.1
  have hβ : Y.1.2 ≠ 0 :=
    coord_ne_zero_of_mem_residualSlice (B := B) c g hθ hψθ hgv hs hYeq
  have hψ's : (residualMap (B := B) c g ψ hψmem s : MGroup Q₀) = mRefl Q₀ Y := by
    rw [residualMap_apply (B := B) c g ψ hψmem hs.1, hYeq]
  exact ⟨Y, hψ's,
    fun h => commute_iff_of_form_eq (B := B) c hnk hF hQ₀ hθ s.2 hY hβ (hform hs.2) h⟩

private lemma residualMap_stabilizer_iff (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψform : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)))
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {s : ↥D} (hs : s ∈ residualSlice (hC := hC) g)
    (h : ↥(Halpha D hC.alpha)) :
    ((h : G) * (s : G) * (h : G)⁻¹ = (s : G)) ↔
      ((θ h : MGroup Q₀) * (residualMap (B := B) c g ψ hψmem s : MGroup Q₀) *
        (θ h : MGroup Q₀)⁻¹ = (residualMap (B := B) c g ψ hψmem s : MGroup Q₀)) := by
  obtain ⟨Y, hψ's, hkey⟩ :=
    exists_residualMap_eq_mRefl_commute_iff (B := B) c hnk hF hQ₀ hθ g ψ hψmem hψθ
      hψform hgv hs
  constructor
  · intro hss
    have hcomm : Commute (h : G) (s : G) := by
      rw [commute_iff_eq]
      calc (h : G) * (s : G) = ((h : G) * (s : G) * (h : G)⁻¹) * (h : G) := by group
        _ = (s : G) * (h : G) := by rw [hss]
    have hc := (hkey h).mp hcomm
    rw [hψ's]
    exact hc.mul_inv_cancel
  · intro hconj
    rw [hψ's] at hconj
    have hc : Commute (θ h : MGroup Q₀) (mRefl Q₀ Y) := by
      rw [commute_iff_eq]
      calc (θ h : MGroup Q₀) * mRefl Q₀ Y
          = (θ h : MGroup Q₀) * mRefl Q₀ Y * (θ h : MGroup Q₀)⁻¹ *
              (θ h : MGroup Q₀) := by group
        _ = mRefl Q₀ Y * (θ h : MGroup Q₀) := by rw [hconj]
    exact ((hkey h).mpr hc).mul_inv_cancel

private lemma residualSlice_fusion (c : SpChart hC B.hα k F)
    (hF : Nat.card F = 2 ^ B.f) (g : G) (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {s : ↥D} (hs : s ∈ residualSlice (hC := hC) g) (h : ↥(Halpha D hC.alpha))
    (hsh : (⟨(h : G) * (s : G) * (h : G)⁻¹,
      hC.setup.conj_mem (h : G) s.2⟩ : ↥D) ∈ residualSlice (hC := hC) g) :
    ∃ r ∈ residualCentralizer (hC := hC) g,
      (r : G) * (s : G) * (r : G)⁻¹ = (h : G) * (s : G) * (h : G)⁻¹ := by
  let cv : SpChart (hC.conj g) (B.conj g).hα k F :=
    CFSG.OddTranspositions.PartThree.SpChart.conj (B := B) c g
  have hx : (s : G) ∈ commSet D (hC.conj g).d := hs.1
  have hx' : (h : G) * (s : G) * (h : G)⁻¹ ∈ commSet D (hC.conj g).d := hsh.1
  have hb := spForm_eq_of_conj_eq (B := B) hF g hgv cv hx hx' h.2 rfl
  obtain ⟨r, hr, hreq⟩ := exists_conj_of_spForm_eq (B := B) g hgv cv hx hx' hs.2 hb
  exact ⟨⟨r, hr.1⟩, (Subgroup.mem_comap).mpr hr.2, hreq⟩

omit [DecidableEq F] in
private lemma commute_mRefl_mLift_of_mem_slice (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    {t : ↥D} (ht : t ∈ residualSlice (hC := hC) g) {Y : MSpace k F}
    (hYeq : (ψ ⟨t, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα ht.1⟩ :
      MGroup Q₀) = mRefl Q₀ Y) :
    Commute (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) (mRefl Q₀ Y) := by
  have hvH : ((hC.conj g).d) ∈ Halpha D hC.alpha := mem_Halpha_of_mem_commSet hC B.hα hgv
  have hvHc : ((hC.conj g).d) ∈ Halpha D (hC.conj g).alpha := mem_Halpha_conj_d g (hu := hu)
  have hψv : (ψ ⟨(hC.conj g).d, hvHc⟩ : MGroup Q₀) =
      mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) := by
    rw [hψθ ⟨(hC.conj g).d, hvH⟩ hvHc, hθ.2.2 ((hC.conj g).d) hgv]
  have htHv : (t : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα ht.1
  have hcH : Commute (⟨t, htHv⟩ : ↥(Halpha D (hC.conj g).alpha))
      ⟨(hC.conj g).d, hvHc⟩ := by
    apply Subtype.ext
    show (t : G) * ((hC.conj g).d) = ((hC.conj g).d) * (t : G)
    exact ht.1.2.1.eq
  have hcM : Commute (ψ ⟨t, htHv⟩ : MGroup Q₀)
      (ψ ⟨(hC.conj g).d, hvHc⟩ : MGroup Q₀) :=
    congrArg Subtype.val (hcH.map ψ.toMonoidHom).eq
  rw [hψv, hYeq] at hcM
  exact hcM.symm

omit [Finite G] [DecidableEq F] in
private lemma mem_map_residualCentralizer (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {r' : MGroup Q₀}
    (hr'mem : r' ∈ Subgroup.centralizer {mRefl Q₀ mU} ⊓
      Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}) :
    (⟨r', hr'mem.1⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU})) ∈
      (residualCentralizer (hC := hC) g).map θ.toMonoidHom := by
  have hvH : ((hC.conj g).d) ∈ Halpha D hC.alpha := mem_Halpha_of_mem_commSet hC B.hα hgv
  have hV₀mem : mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) ∈
      Subgroup.centralizer {mRefl Q₀ mU} :=
    mRefl_mem_centralizer_of_polar_eq_zero (by rw [polar_comm]; exact polar_mU_mLift _)
  have hr'C : Commute (⟨r', hr'mem.1⟩ : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
      ⟨mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)), hV₀mem⟩ := by
    apply Subtype.ext
    show (r' : MGroup Q₀) * mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) =
      mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) * r'
    exact Subgroup.mem_centralizer_singleton_iff.mp hr'mem.2
  have hsymm : (θ.symm ⟨mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)), hV₀mem⟩ :
      ↥(Halpha D hC.alpha)) = ⟨(hC.conj g).d, hvH⟩ := by
    apply θ.injective
    rw [θ.apply_symm_apply]
    exact Subtype.ext (hθ.2.2 ((hC.conj g).d) hgv).symm
  have hcv : Commute ((θ.symm ⟨r', hr'mem.1⟩ : ↥(Halpha D hC.alpha)) : G)
      ((hC.conj g).d) := by
    have h := (hr'C.map θ.symm.toMonoidHom).map
      (Subgroup.subtype (Halpha D hC.alpha))
    simpa [hsymm] using h
  refine (Subgroup.mem_map).mpr ⟨θ.symm ⟨r', hr'mem.1⟩, ?_, θ.apply_symm_apply _⟩
  rw [residualCentralizer, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  exact hcv

omit [DecidableEq F] in
private lemma residualMap_fusion (c : SpChart hC B.hα k F)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψform : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)))
    {s' : ↥(mClass Q₀)} (hs' : ∃ t ∈ residualSlice (hC := hC) g,
      (residualMap (B := B) c g ψ hψmem t : MGroup Q₀) = (s' : MGroup Q₀))
    {h' : ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hh' : ∃ t' ∈ residualSlice (hC := hC) g,
      (residualMap (B := B) c g ψ hψmem t' : MGroup Q₀) =
        (h' : MGroup Q₀) * (s' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹) :
    ∃ r ∈ (residualCentralizer (hC := hC) g).map θ.toMonoidHom,
      (r : MGroup Q₀) * (s' : MGroup Q₀) * (r : MGroup Q₀)⁻¹ =
        (h' : MGroup Q₀) * (s' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹ := by
  obtain ⟨t, ht, htψ⟩ := hs'
  obtain ⟨t', ht', ht'ψ⟩ := hh'
  obtain ⟨Y, hY, hYeq, -⟩ := hψform t ht.1
  obtain ⟨Y', hY', hY'eq, -⟩ := hψform t' ht'.1
  have hst : (s' : MGroup Q₀) = mRefl Q₀ Y := by
    rw [← htψ, residualMap_apply (B := B) c g ψ hψmem ht.1, hYeq]
  have hconj' : (h' : MGroup Q₀) * mRefl Q₀ Y * (h' : MGroup Q₀)⁻¹ = mRefl Q₀ Y' := by
    rw [← hst, ← ht'ψ, residualMap_apply (B := B) c g ψ hψmem ht'.1, hY'eq]
  have hxY := commute_mRefl_mLift_of_mem_slice (B := B) c g hθ hgv hψθ ht hYeq
  have hxY' := commute_mRefl_mLift_of_mem_slice (B := B) c g hθ hgv hψθ ht' hY'eq
  have hβ : Y.1.2 ≠ 0 :=
    coord_ne_zero_of_mem_residualSlice (B := B) c g hθ hψθ hgv ht hYeq
  have hcoord : Y.1.2 = Y'.1.2 :=
    polar_mU_eq_of_conj hQ₀ hY hY' h'.2 hconj'
  obtain ⟨r', hr'mem, hr'eq⟩ := exists_conj_eq_of_polar_mU_eq_of_commute
    (Q₀ := Q₀) hQ₀ (x := c.vec (hC.conj g).d) hY hY' hβ hcoord hxY hxY'
  refine ⟨⟨r', hr'mem.1⟩, mem_map_residualCentralizer (B := B) c g hθ hgv hr'mem, ?_⟩
  change (r' : MGroup Q₀) * (s' : MGroup Q₀) * (r' : MGroup Q₀)⁻¹ =
    (h' : MGroup Q₀) * (s' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹
  rw [hst, hconj', hr'eq]

private lemma exists_conj_commSet_not_commute (hk : 2 ≤ k)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {x₀ : Fin k ⊕ Fin k → F} (hx₀ : x₀ ≠ 0)
    {m : ↥(mClass Q₀)} (hm : m ∉ modelBaseSet Q₀) :
    ∃ h' ∈ Subgroup.centralizer {mRefl Q₀ mU},
      ((h' * (m : MGroup Q₀) * h'⁻¹ ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ x₀))) ∧
        ¬ Commute (h' * (m : MGroup Q₀) * h'⁻¹) (mRefl Q₀ mU)) := by
  have hnotcomm : ¬ Commute (m : MGroup Q₀) (mRefl Q₀ mU) := by
    intro hc
    exact hm (Subgroup.mem_centralizer_singleton_iff.mpr hc)
  obtain ⟨X, hX, hmX⟩ := m.2
  have hβ : X.1.2 ≠ 0 := by
    apply coord_ne_zero_of_not_commute
    rwa [← hmX]
  obtain ⟨a, ha, haform, -⟩ := exists_mStabForm_eq_one_of_two (Q₀ := Q₀) hQ₀ hk X X
  have hcomm_a : Commute (mRefl Q₀ (mLift Q₀ a)) (m : MGroup Q₀) := by
    rw [hmX]
    exact (commute_mLift_iff hQ₀ hX hβ a).mpr haform
  obtain ⟨h', hh'C, hh'eq⟩ := exists_conj_mRefl_mLift_eq (Q₀ := Q₀) hQ₀ ha hx₀
  have hh'U : Commute h' (mRefl Q₀ mU) :=
    Subgroup.mem_centralizer_singleton_iff.mp hh'C
  have hconjU : h' * mRefl Q₀ mU * h'⁻¹ = mRefl Q₀ mU := by
    rw [hh'U.eq]
    group
  have hnotcommU : ¬ Commute (h' * (m : MGroup Q₀) * h'⁻¹) (mRefl Q₀ mU) := by
    have h := ((Commute.conj_iff h').not).mpr hnotcomm
    rwa [hconjU] at h
  refine ⟨h', hh'C, ?_, hnotcommU⟩
  refine ⟨(setup_mClass hQ₀ hk).conj_mem h' m.2, ?_, ?_⟩
  · have hcm : Commute (h' * (m : MGroup Q₀) * h'⁻¹)
        (h' * mRefl Q₀ (mLift Q₀ a) * h'⁻¹) :=
      (Commute.conj_iff h').mpr hcomm_a.symm
    rwa [hh'eq] at hcm
  · intro heq
    rw [heq] at hnotcommU
    exact hnotcommU (Subgroup.mem_centralizer_singleton_iff.mp (mRefl_mLift_mem_centralizer _))

private lemma exists_conj_residualMap (c : SpChart hC B.hα k F)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψsurj : ∀ w ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
      ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = w)
    (hk : 2 ≤ k) {m : ↥(mClass Q₀)}
    (hm : m ∉ CFSG.OddTranspositions.PartThree.baseSet (mClass Q₀) (mRefl Q₀ mU)) :
    ∃ h' : ↥(Subgroup.centralizer {mRefl Q₀ mU}),
      ∃ s' ∈ residualMap (B := B) c g ψ hψmem ''
          CFSG.OddTranspositions.PartThree.sliceSet D hC.d (hC.conj g).d,
        (h' : MGroup Q₀) * (s' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹ = (m : MGroup Q₀) := by
  rw [← modelBaseSet_eq_baseSet] at hm
  obtain ⟨h', hh'C, hconj_m, hnotcommU⟩ :=
    exists_conj_commSet_not_commute hk hQ₀ (c.vec_ne_zero _ hgv) hm
  obtain ⟨z, hz, hzψ⟩ := hψsurj _ hconj_m
  have hdv : hC.d ∈ commSet D (hC.conj g).d :=
    ⟨hC.hd, hgv.2.1.symm, fun h => hgv.2.2 h.symm⟩
  have hdHv : (hC.d : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv
  have hψd : (ψ ⟨hC.d, hdHv⟩ : MGroup Q₀) = mRefl Q₀ mU := by
    rw [hψθ ⟨hC.d, hu⟩ hdHv, hθ.2.1]
  have hzHv : z ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz
  have hnd : ¬ Commute z hC.d := by
    intro hc
    apply hnotcommU
    have hcH : Commute (⟨z, hzHv⟩ : ↥(Halpha D (hC.conj g).alpha)) ⟨hC.d, hdHv⟩ := by
      apply Subtype.ext
      show z * hC.d = hC.d * z
      exact hc.eq
    have hcM : Commute (ψ ⟨z, hzHv⟩ : MGroup Q₀) (ψ ⟨hC.d, hdHv⟩ : MGroup Q₀) :=
      congrArg Subtype.val (hcH.map ψ.toMonoidHom).eq
    rwa [hψd, hzψ] at hcM
  refine ⟨⟨h', hh'C⟩⁻¹, ?_⟩
  refine ⟨residualMap (B := B) c g ψ hψmem ⟨z, hz.1⟩, ⟨⟨z, hz.1⟩, ⟨hz, hnd⟩, rfl⟩, ?_⟩
  rw [residualMap_apply (B := B) c g ψ hψmem hz, hzψ]
  simp only [Subgroup.coe_inv]
  group

omit [DecidableEq F] in
private lemma residualMap_conj (c : SpChart hC B.hα k F) (g : G)
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {r : ↥(Halpha D hC.alpha)} (hr : r ∈ residualCentralizer (hC := hC) g)
    {s : ↥D} (hs : s ∈ residualSlice (hC := hC) g) :
    (residualMap (B := B) c g ψ hψmem
        ⟨(r : G) * (s : G) * (r : G)⁻¹, hC.setup.conj_mem (r : G) s.2⟩ : MGroup Q₀) =
      (θ r : MGroup Q₀) * (residualMap (B := B) c g ψ hψmem s : MGroup Q₀) *
        (θ r : MGroup Q₀)⁻¹ := by
  have hrv : (r : G) ∈ Subgroup.centralizer {(hC.conj g).d} := hr
  have hrHv : (r : G) ∈ Halpha D (hC.conj g).alpha :=
    inf_centralizer_le_Halpha_conj (B := B) c g hgv ⟨r.2, hrv⟩
  have hconjsv : (r : G) * (s : G) * (r : G)⁻¹ ∈ commSet D (hC.conj g).d :=
    conj_mem_commSet_of_commute hC.setup.normal
      (Subgroup.mem_centralizer_singleton_iff.mp hrv) hs.1
  have hconjH : (r : G) * (s : G) * (r : G)⁻¹ ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hconjsv
  have hsHv : (s : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hs.1
  have hsub : (⟨(r : G) * (s : G) * (r : G)⁻¹, hconjH⟩ :
      ↥(Halpha D (hC.conj g).alpha)) =
      (⟨r, hrHv⟩ : ↥(Halpha D (hC.conj g).alpha)) * ⟨s, hsHv⟩ * ⟨r, hrHv⟩⁻¹ := by
    apply Subtype.ext
    rfl
  have hψapply : (ψ ⟨(r : G) * (s : G) * (r : G)⁻¹, hconjH⟩ : MGroup Q₀) =
      (ψ ⟨r, hrHv⟩ : MGroup Q₀) * (ψ ⟨s, hsHv⟩ : MGroup Q₀) *
        (ψ ⟨r, hrHv⟩ : MGroup Q₀)⁻¹ := by
    rw [hsub, map_mul, map_mul, map_inv]
    rfl
  have hψr : (ψ ⟨r, hrHv⟩ : MGroup Q₀) = (θ r : MGroup Q₀) := hψθ r hrHv
  rw [residualMap_apply (B := B) c g ψ hψmem hconjsv, hψapply, hψr,
    residualMap_apply (B := B) c g ψ hψmem hs.1]

omit [DecidableEq F] in
private lemma residualMap_notMem_modelBaseSet (c : SpChart hC B.hα k F) (g : G)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψbase : ∀ hd : (hC.d : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ ⟨hC.d, hd⟩ : MGroup Q₀) = mRefl Q₀ mU)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {s : ↥D} (hs : s ∈ residualSlice (hC := hC) g) :
    residualMap (B := B) c g ψ hψmem s ∉ modelBaseSet Q₀ := by
  intro hm
  have hm' : (residualMap (B := B) c g ψ hψmem s : MGroup Q₀) ∈
      Subgroup.centralizer {mRefl Q₀ mU} := hm
  have hcommM : Commute (residualMap (B := B) c g ψ hψmem s : MGroup Q₀)
      (mRefl Q₀ mU) := Subgroup.mem_centralizer_singleton_iff.mp hm'
  have hdv : hC.d ∈ commSet D (hC.conj g).d :=
    ⟨hC.hd, hgv.2.1.symm, fun h => hgv.2.2 h.symm⟩
  have hdHv : (hC.d : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdv
  have hsHv : (s : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hs.1
  have hcommψ : Commute (ψ ⟨s, hsHv⟩) (ψ ⟨hC.d, hdHv⟩) := by
    apply Subtype.ext
    show (ψ ⟨s, hsHv⟩ : MGroup Q₀) * (ψ ⟨hC.d, hdHv⟩ : MGroup Q₀) =
      (ψ ⟨hC.d, hdHv⟩ : MGroup Q₀) * (ψ ⟨s, hsHv⟩ : MGroup Q₀)
    rw [← residualMap_apply (B := B) c g ψ hψmem hs.1, hψbase hdHv]
    exact hcommM.eq
  have hsd : Commute (s : G) hC.d := by
    have h := hcommψ.map ψ.symm.toMonoidHom
    simpa using h.map (Subgroup.subtype (Halpha D (hC.conj g).alpha))
  exact hs.2 hsd

omit [DecidableEq F] in
private lemma residualMap_bijOn (c : SpChart hC B.hα k F) (g : G)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀) :
    Set.BijOn (residualMap (B := B) c g ψ hψmem) (residualSlice (hC := hC) g)
      (residualMap (B := B) c g ψ hψmem '' residualSlice (hC := hC) g) := by
  refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_, fun m hm => hm⟩
  intro x hx y hy hxy
  have hxHv : (x : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx.1
  have hyHv : (y : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hy.1
  have heq : (ψ ⟨x, hxHv⟩ : MGroup Q₀) = (ψ ⟨y, hyHv⟩ : MGroup Q₀) := by
    rw [← residualMap_apply (B := B) c g ψ hψmem hx.1,
      ← residualMap_apply (B := B) c g ψ hψmem hy.1]
    exact congrArg Subtype.val hxy
  have h2 := ψ.injective (Subtype.ext heq)
  exact Subtype.ext (congrArg (fun t : ↥(Halpha D (hC.conj g).alpha) => (t : G)) h2)

private def patchSet (g : G) : Set ↥D :=
  {x | (x : G) = (hC.conj g).d ∨ (x : G) ∈ commSet D (hC.conj g).d}

private def modelPatchSet (c : SpChart hC B.hα k F) (g : G) : Set ↥(mClass Q₀) :=
  {m | (m : MGroup Q₀) = mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) ∨
    (m : MGroup Q₀) ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)))}

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma baseSet_commute_iff
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    {F' : ↥D ≃ ↥(mClass Q₀)}
    (hFeq : ∀ (h : ↥(Halpha D hC.alpha)) (x : ↥D),
      (F' ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
        (θ h : MGroup Q₀) * (F' x : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹)
    (hFB : ∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
      (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀))
    {z : ↥D} (hz : z ∈ halphaSet (hC := hC)) (y : ↥D) :
    Commute (z : G) (y : G) ↔ Commute (F' z : MGroup Q₀) (F' y : MGroup Q₀) := by
  have hzH : (z : G) ∈ Halpha D hC.alpha := hz
  have hFz : (F' z : MGroup Q₀) = (θ ⟨z, hzH⟩ : MGroup Q₀) := hFB ⟨z, hzH⟩ z.2
  constructor
  · intro hc
    have hzy : (⟨(z : G) * (y : G) * (z : G)⁻¹,
        hC.setup.conj_mem (z : G) y.2⟩ : ↥D) = y := by
      apply Subtype.ext
      show (z : G) * (y : G) * (z : G)⁻¹ = (y : G)
      rw [hc.eq]
      group
    have h1 := hFeq ⟨z, hzH⟩ y
    rw [hzy] at h1
    rw [hFz]
    show (θ ⟨z, hzH⟩ : MGroup Q₀) * (F' y : MGroup Q₀) =
      (F' y : MGroup Q₀) * (θ ⟨z, hzH⟩ : MGroup Q₀)
    calc (θ ⟨z, hzH⟩ : MGroup Q₀) * (F' y : MGroup Q₀)
        = (θ ⟨z, hzH⟩ : MGroup Q₀) * (F' y : MGroup Q₀) *
            (θ ⟨z, hzH⟩ : MGroup Q₀)⁻¹ * (θ ⟨z, hzH⟩ : MGroup Q₀) := by group
      _ = (F' y : MGroup Q₀) * (θ ⟨z, hzH⟩ : MGroup Q₀) := by rw [← h1]
  · intro hc
    have hc' : Commute (θ ⟨z, hzH⟩ : MGroup Q₀) (F' y : MGroup Q₀) := by
      rwa [hFz] at hc
    have h1 := hFeq ⟨z, hzH⟩ y
    have h2 : (F' ⟨(z : G) * (y : G) * (z : G)⁻¹,
        hC.setup.conj_mem (z : G) y.2⟩ : MGroup Q₀) = (F' y : MGroup Q₀) := by
      rw [h1]
      show (θ ⟨z, hzH⟩ : MGroup Q₀) * (F' y : MGroup Q₀) * (θ ⟨z, hzH⟩ : MGroup Q₀)⁻¹ =
        (F' y : MGroup Q₀)
      rw [hc'.eq]
      group
    have h3 := F'.injective (Subtype.ext h2)
    have h4 : (z : G) * (y : G) * (z : G)⁻¹ = (y : G) :=
      congrArg (fun t : ↥D => (t : G)) h3
    show (z : G) * (y : G) = (y : G) * (z : G)
    calc (z : G) * (y : G) = ((z : G) * (y : G) * (z : G)⁻¹) * (z : G) := by group
      _ = (y : G) * (z : G) := by rw [h4]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma sliceSet_commute_iff (g : G) {F' : ↥D ≃ ↥(mClass Q₀)}
    {ψ : ↥(Halpha D (hC.conj g).alpha) →* MGroup Q₀} (hψinj : Function.Injective ψ)
    (hψF : ∀ x, ∀ hx : x ∈ commSet D (hC.conj g).d,
      (F' ⟨x, hx.1⟩ : MGroup Q₀) =
        ψ ⟨x, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx⟩)
    {x y : ↥D} (hx : (x : G) ∈ commSet D (hC.conj g).d)
    (hy : (y : G) ∈ commSet D (hC.conj g).d) :
    Commute (x : G) (y : G) ↔ Commute (F' x : MGroup Q₀) (F' y : MGroup Q₀) := by
  have hxHv : (x : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx
  have hyHv : (y : G) ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hy
  constructor
  · intro hc
    have hcH : Commute (⟨x, hxHv⟩ : ↥(Halpha D (hC.conj g).alpha)) ⟨y, hyHv⟩ := by
      apply Subtype.ext
      show (x : G) * (y : G) = (y : G) * (x : G)
      exact hc.eq
    have hcM : Commute (ψ ⟨x, hxHv⟩) (ψ ⟨y, hyHv⟩) := hcH.map ψ
    have hx' : (F' x : MGroup Q₀) = ψ ⟨x, hxHv⟩ := hψF x hx
    have hy' : (F' y : MGroup Q₀) = ψ ⟨y, hyHv⟩ := hψF y hy
    rw [hx', hy']
    exact hcM
  · intro hc
    have hx' : (F' x : MGroup Q₀) = ψ ⟨x, hxHv⟩ := hψF x hx
    have hy' : (F' y : MGroup Q₀) = ψ ⟨y, hyHv⟩ := hψF y hy
    have hcM : Commute (ψ ⟨x, hxHv⟩) (ψ ⟨y, hyHv⟩) := by
      rw [← hx', ← hy']
      exact hc
    have h1 : (⟨x, hxHv⟩ : ↥(Halpha D (hC.conj g).alpha)) * ⟨y, hyHv⟩ =
        ⟨y, hyHv⟩ * ⟨x, hxHv⟩ :=
      hψinj (by rw [map_mul, map_mul]; exact hcM.eq)
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg (fun t : ↥(Halpha D (hC.conj g).alpha) => (t : G)) h1

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma patchSet_adj_iff (g : G)
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    {F' : ↥D ≃ ↥(mClass Q₀)}
    (hFeq : ∀ (h : ↥(Halpha D hC.alpha)) (x : ↥D),
      (F' ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
        (θ h : MGroup Q₀) * (F' x : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹)
    (hFB : ∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
      (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀))
    {ψ : ↥(Halpha D (hC.conj g).alpha) →* MGroup Q₀} (hψinj : Function.Injective ψ)
    (hψF : ∀ x, ∀ hx : x ∈ commSet D (hC.conj g).d,
      (F' ⟨x, hx.1⟩ : MGroup Q₀) =
        ψ ⟨x, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx⟩)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {x y : ↥D} (hx : x ∈ patchSet (hC := hC) g) (hy : y ∈ patchSet (hC := hC) g) :
    (commGraph D).Adj x y ↔ (commGraph (mClass Q₀)).Adj (F' x) (F' y) := by
  have hvH : ((hC.conj g).d) ∈ Halpha D hC.alpha :=
    mem_Halpha_of_mem_commSet hC B.hα hgv
  have hvbase : (⟨(hC.conj g).d, hgv.1⟩ : ↥D) ∈ halphaSet (hC := hC) := hvH
  rw [commGraph_adj, commGraph_adj]
  constructor
  · rintro ⟨hne, hcomm⟩
    refine ⟨?_, ?_⟩
    · intro h; exact hne (F'.injective h)
    · rcases hx with hxv | hxDv
      · have hxb : x ∈ halphaSet (hC := hC) := by
          change (x : G) ∈ Halpha D hC.alpha
          rw [hxv]; exact hvH
        exact (baseSet_commute_iff hFeq hFB hxb y).mp hcomm
      · rcases hy with hyv | hyDv
        · have hyb : y ∈ halphaSet (hC := hC) := by
            change (y : G) ∈ Halpha D hC.alpha
            rw [hyv]; exact hvH
          exact ((baseSet_commute_iff hFeq hFB hyb x).mp hcomm.symm).symm
        · exact (sliceSet_commute_iff (B := B) g hψinj hψF hxDv hyDv).mp hcomm
  · rintro ⟨hne, hcomm⟩
    refine ⟨?_, ?_⟩
    · intro h; exact hne (congrArg F' h)
    · rcases hx with hxv | hxDv
      · have hxb : x ∈ halphaSet (hC := hC) := by
          change (x : G) ∈ Halpha D hC.alpha
          rw [hxv]; exact hvH
        exact (baseSet_commute_iff hFeq hFB hxb y).mpr hcomm
      · rcases hy with hyv | hyDv
        · have hyb : y ∈ halphaSet (hC := hC) := by
            change (y : G) ∈ Halpha D hC.alpha
            rw [hyv]; exact hvH
          exact ((baseSet_commute_iff hFeq hFB hyb x).mpr hcomm.symm).symm
        · exact (sliceSet_commute_iff (B := B) g hψinj hψF hxDv hyDv).mpr hcomm

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma exists_residualPoint (c : SpChart hC B.hα k F) (hk0 : 0 < k) :
    ∃ g : G, (hC.conj g).d ∈ commSet D hC.d := by
  let x₀ : Fin k ⊕ Fin k → F := Pi.single (Sum.inl ⟨0, hk0⟩) 1
  have hx₀ : x₀ ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl ⟨0, hk0⟩)
    simp [x₀] at h1
  obtain ⟨v, hv, -⟩ := c.exists_vec x₀ hx₀
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv.1)
  refine ⟨g, ?_⟩
  rw [HypothesisC.conj_d, hg]
  exact hv

private lemma exists_residualChart (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    (hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
      IsFormOfLine c Q₀ w₀) :
    ∃ ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
        ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}),
      (∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
          mClass Q₀) ∧
      (∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀)) ∧
      (∀ m ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
        ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
          (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = m) ∧
      ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)) := by
  obtain ⟨ψ, hψθ, hψsurj, hψform⟩ := exists_local_iso_forms_eq c hnk hF hQ₀ hθ g hgv hQ₀ty
  have hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀ := by
    intro z hz
    obtain ⟨Y, hY, hYeq, -⟩ := hψform z hz
    exact ⟨Y, hY, hYeq⟩
  exact ⟨ψ, hψmem, hψθ, hψsurj, hψform⟩

omit [Finite G] in
private lemma baseMap_bijOn (c : SpChart hC B.hα k F)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) :
    Set.BijOn (baseMap (B := B) c hθ) (CFSG.OddTranspositions.PartThree.baseSet D hC.d)
      (CFSG.OddTranspositions.PartThree.baseSet (mClass Q₀) (mRefl Q₀ mU)) := by
  have hB : halphaSet (hC := hC) = CFSG.OddTranspositions.PartThree.baseSet D hC.d :=
    Set.ext fun x => mem_baseSet_iff (B := B) (hu := hu)
  rw [← hB, ← modelBaseSet_eq_baseSet]
  exact ⟨baseMap_mapsTo (B := B) c hθ, baseMap_injOn (B := B) c hθ,
    baseMap_surjOn (B := B) c hQ₀ hθ⟩

private lemma disjoint_residualMap_image_baseSet (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hgv : (hC.conj g).d ∈ commSet D hC.d) :
    Disjoint (residualMap (B := B) c g ψ hψmem ''
        CFSG.OddTranspositions.PartThree.sliceSet D hC.d (hC.conj g).d)
      (CFSG.OddTranspositions.PartThree.baseSet (mClass Q₀) (mRefl Q₀ mU)) := by
  rw [← modelBaseSet_eq_baseSet, Set.disjoint_left]
  rintro m ⟨s, hs, rfl⟩ hm
  exact residualMap_notMem_modelBaseSet (B := B) c g ψ hψmem
    (fun hd => by rw [hψθ ⟨hC.d, hu⟩ hd, hθ.2.1]) hgv hs hm

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma exists_conj_of_notMem_baseSet (c : SpChart hC B.hα k F) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {x : ↥D}
    (hx : x ∉ CFSG.OddTranspositions.PartThree.baseSet D hC.d) :
    ∃ h : ↥(Halpha D hC.alpha),
      ∃ s ∈ CFSG.OddTranspositions.PartThree.sliceSet D hC.d (hC.conj g).d,
        (h : G) * (s : G) * (h : G)⁻¹ = (x : G) :=
  exists_conj_eq_of_not_mem_baseSet hC.setup (H := Halpha D hC.alpha) hgv
    (fun h hh => commute_d_of_mem_Halpha hC B.hα ⟨h, hh⟩)
    (fun w hw hnc => B.hdiam hC.d hC.hd w hw (fun h => hnc h.symm))
    (fun _ ha _ hb => (exists_conj_of_mem_commSet (B := B) c ha hb).elim
      fun h hh => ⟨h, h.2, hh⟩) hx

private lemma residualMap_fusion_sliceSet (c : SpChart hC B.hα k F)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈
        mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψform : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)))
    (hk : 2 ≤ k) {s' : ↥(mClass Q₀)}
    (hs' : s' ∈ residualMap (B := B) c g ψ hψmem ''
      CFSG.OddTranspositions.PartThree.sliceSet D hC.d (hC.conj g).d)
    (h' : ↥(Subgroup.centralizer {mRefl Q₀ mU}))
    (hh' : (⟨(h' : MGroup Q₀) * (s' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h' : MGroup Q₀) s'.2⟩ : ↥(mClass Q₀)) ∈
      residualMap (B := B) c g ψ hψmem ''
        CFSG.OddTranspositions.PartThree.sliceSet D hC.d (hC.conj g).d) :
    ∃ r ∈ residualCentralizer (hC := hC) g,
      (θ r : MGroup Q₀) * (s' : MGroup Q₀) * (θ r : MGroup Q₀)⁻¹ =
        (h' : MGroup Q₀) * (s' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹ := by
  obtain ⟨r, hr, hreq⟩ := residualMap_fusion (B := B) (s' := s') c hQ₀ hθ g hgv ψ
    hψmem hψθ hψform
    (by rcases hs' with ⟨t, ht, ht'⟩; exact ⟨t, ht, congrArg Subtype.val ht'⟩)
    (by rcases hh' with ⟨t, ht, ht'⟩; exact ⟨t, ht, congrArg Subtype.val ht'⟩)
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  exact ⟨r₀, hr₀, hreq⟩

private lemma exists_equivariant_patchMap (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d)
    (ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}))
    (hψmem : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) ∈ mClass Q₀)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψsurj : ∀ w ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
      ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = w)
    (hψform : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)))
    (hk : 2 ≤ k) :
    ∃ F' : ↥D ≃ ↥(mClass Q₀),
      (∀ (h : ↥(Halpha D hC.alpha)) (x : ↥D),
        (F' ⟨(h : G) * x * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
          (θ h : MGroup Q₀) * (F' x : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹) ∧
      (∀ x ∈ halphaSet (hC := hC), F' x = baseMap (B := B) c hθ x) ∧
      ∀ s ∈ residualSlice (hC := hC) g, F' s = residualMap (B := B) c g ψ hψmem s := by
  obtain ⟨F', hFeq, hFB, hFS⟩ := exists_conj_equivariant_equiv_of_patch
    hC.setup (setup_mClass hQ₀ hk) θ
    (fun h hh => commute_d_of_mem_Halpha hC B.hα ⟨h, hh⟩)
    (residualCentralizer (hC := hC) g)
    (fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hr))
    (baseMap (B := B) c hθ) (residualMap (B := B) c g ψ hψmem)
    (baseMap_bijOn (B := B) c hQ₀ hθ)
    (fun h x hx => baseMap_equivariant (B := B) c hθ h hx)
    (residualMap_bijOn (B := B) c g ψ hψmem)
    (disjoint_residualMap_image_baseSet (B := B) c g hθ ψ hψmem hψθ hgv)
    (fun r hr s hs => residualMap_conj (B := B) c g ψ hψmem hψθ hgv hr hs)
    (fun x hx => exists_conj_of_notMem_baseSet (B := B) c g hgv hx)
    (fun m hm => exists_conj_residualMap (B := B) c hQ₀ hθ g hgv ψ hψmem hψθ hψsurj hk hm)
    (fun s hs h => residualMap_stabilizer_iff (B := B) c hnk hF hQ₀ hθ g ψ hψmem hψθ
      hψform hgv hs h)
    (fun s hs h hsh => residualSlice_fusion (B := B) c hF g hgv hs h hsh)
    (fun s hs h hsh => residualMap_fusion_sliceSet c hQ₀ hθ g hgv ψ hψmem hψθ
      hψform hk hs h hsh)
  exact ⟨F', hFeq, fun x hx => hFB x ((mem_baseSet_iff (B := B) (hu := hu)).mp hx), hFS⟩

omit [DecidableEq F] in
private lemma eq_psi_of_notMem_residualSlice (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    {ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)),
      ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    {F' : ↥D ≃ ↥(mClass Q₀)}
    (hθFB : ∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
      (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀))
    {x : G} (hx : x ∈ commSet D (hC.conj g).d)
    (hxS : (⟨x, hx.1⟩ : ↥D) ∉ residualSlice (hC := hC) g) :
    (F' ⟨x, hx.1⟩ : MGroup Q₀) =
      (ψ ⟨x, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx⟩ : MGroup Q₀) := by
  have hcomm : Commute x hC.d := by
    by_contra hnc
    exact hxS ⟨hx, hnc⟩
  have hxB : (⟨x, hx.1⟩ : ↥D) ∈ halphaSet (hC := hC) := by
    rw [mem_baseSet_iff (B := B) (hu := hu)]
    by_cases hxd : x = hC.d
    · exact Or.inl hxd
    · exact Or.inr ⟨hx.1, hcomm, hxd⟩
  have hxHv : x ∈ Halpha D (hC.conj g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx
  rw [hθFB ⟨x, hxB⟩ hx.1]
  exact (hψθ ⟨x, hxB⟩ hxHv).symm

theorem exists_patchMap (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    (hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
      IsFormOfLine c Q₀ w₀) :
    ∃ F' : ↥D ≃ ↥(mClass Q₀),
      (∀ (h : ↥(Halpha D hC.alpha)) (x : ↥D),
        (F' ⟨(h : G) * x * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
          (θ h : MGroup Q₀) * (F' x : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹) ∧
      (∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
        (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀)) ∧
      ∃ g : G, (hC.conj g).d ∈ commSet D hC.d ∧
        ∃ ψ : ↥(Halpha D (hC.conj g).alpha) →* MGroup Q₀, Function.Injective ψ ∧
          ∀ x, ∀ hx : x ∈ commSet D (hC.conj g).d,
            (F' ⟨x, hx.1⟩ : MGroup Q₀) =
              ψ ⟨x, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hx⟩ := by
  classical
  have hk : 2 ≤ k := B.two_le_rank hnk
  obtain ⟨g, hgv⟩ := exists_residualPoint (B := B) c (by omega)
  obtain ⟨ψ, hψmem, hψθ, hψsurj, hψform⟩ :=
    exists_residualChart (B := B) c hnk hF hQ₀ hθ g hgv hQ₀ty
  obtain ⟨F', hFeq, hFB, hFS⟩ := exists_equivariant_patchMap (B := B) c hnk hF hQ₀ hθ
    g hgv ψ hψmem hψθ hψsurj hψform hk
  have hθFB : ∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
      (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀) := by
    intro z hz
    rw [hFB ⟨z, hz⟩ z.2, baseMap_of_mem (B := B) c hθ z.2]
  let ψM : ↥(Halpha D (hC.conj g).alpha) →* MGroup Q₀ :=
    (Subgroup.subtype (Subgroup.centralizer
      {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})).comp ψ.toMonoidHom
  refine ⟨F', hFeq, hθFB, g, hgv, ψM, ?_, ?_⟩
  · intro a b hab
    exact ψ.injective (Subtype.ext hab)
  · intro x hx
    by_cases hxS : (⟨x, hx.1⟩ : ↥D) ∈ residualSlice (hC := hC) g
    · rw [hFS _ hxS]
      exact residualMap_apply (B := B) c g ψ hψmem hx
    · exact eq_psi_of_notMem_residualSlice (B := B) (hu := hu) c g hψθ hθFB hx hxS

omit [Finite G] in
private lemma mem_patchSet_iff {g : G} {x : ↥D} :
    x ∈ patchSet (hC := hC) g ↔
      (x : G) = (hC.conj g).d ∨ (x : G) ∈ commSet D (hC.conj g).d :=
  Iff.rfl

omit [Finite G] [DecidableEq F] in
private lemma mem_modelPatchSet_iff (c : SpChart hC B.hα k F) (g : G) {m : ↥(mClass Q₀)} :
    m ∈ modelPatchSet (B := B) c g ↔
      (m : MGroup Q₀) = mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) ∨
        (m : MGroup Q₀) ∈
          commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) :=
  Iff.rfl

omit [Finite G] in
private lemma coe_smulD (h : ↥(Halpha D hC.alpha)) (x : ↥D) :
    ((h • x : ↥D) : G) = (h : G) * (x : G) * (h : G)⁻¹ :=
  rfl

omit [Finite G] in
private lemma mem_commSet_of_adj {E : Set G} {x y : ↥E} (hxy : (commGraph E).Adj x y) :
    (y : G) ∈ commSet E x :=
  ⟨y.2, hxy.2.symm, fun h => hxy.1 (Subtype.ext h.symm)⟩

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma exists_smul_mem_patchSet_of_mem_commSet (c : SpChart hC B.hα k F) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {x y : ↥D}
    (hx : (x : G) ∈ commSet D hC.d) (hxy : (commGraph D).Adj x y) :
    ∃ h : ↥(Halpha D hC.alpha),
      h • x ∈ patchSet (hC := hC) g ∧ h • y ∈ patchSet (hC := hC) g := by
  obtain ⟨h, hh⟩ := exists_conj_of_mem_commSet (B := B) c hx hgv
  have hne : (x : G) ≠ (y : G) := fun h' => hxy.1 (Subtype.ext h')
  refine ⟨h, ?_, ?_⟩
  · rw [mem_patchSet_iff, coe_smulD]
    exact Or.inl hh
  · rw [mem_patchSet_iff, coe_smulD, ← hh]
    exact Or.inr (conj_mem_commSet hC.setup.normal (h : G) (mem_commSet_of_adj hxy))

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma exists_smul_mem_patchSet_of_eq_d (c : SpChart hC B.hα k F) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {x y : ↥D} (hx : (x : G) = hC.d)
    (hxy : (commGraph D).Adj x y) :
    ∃ h : ↥(Halpha D hC.alpha),
      h • x ∈ patchSet (hC := hC) g ∧ h • y ∈ patchSet (hC := hC) g := by
  have hxy' : (x : G) ≠ (y : G) := fun h' => hxy.1 (Subtype.ext h')
  have hy : (y : G) ∈ commSet D hC.d := by
    have h := mem_commSet_of_adj hxy
    rwa [hx] at h
  obtain ⟨h, hh⟩ := exists_conj_of_mem_commSet (B := B) c hy hgv
  have hhd : Commute (h : G) hC.d := commute_d_of_mem_Halpha hC B.hα h
  have hdx : ((h • x : ↥D) : G) = hC.d := by
    rw [coe_smulD, hx, hhd.eq]
    group
  refine ⟨h, ?_, ?_⟩
  · rw [mem_patchSet_iff, hdx]
    exact Or.inr ⟨hC.hd, hgv.2.1.symm, fun h' => hgv.2.2 h'.symm⟩
  · rw [mem_patchSet_iff, coe_smulD]
    exact Or.inl hh

omit [DecidableEq F] in
private lemma exists_smul_mem_patchSet_of_not_commute (c : SpChart hC B.hα k F)
    (hnk : B.n = 2 * k) (hF : Nat.card F = 2 ^ B.f) (g : G)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {x y : ↥D}
    (hxu : ¬ Commute (x : G) hC.d) (hyu : ¬ Commute (y : G) hC.d)
    (hxy : (commGraph D).Adj x y) :
    ∃ h : ↥(Halpha D hC.alpha),
      h • x ∈ patchSet (hC := hC) g ∧ h • y ∈ patchSet (hC := hC) g := by
  have hne : (x : G) ≠ (y : G) := fun h' => hxy.1 (Subtype.ext h')
  obtain ⟨u, hu⟩ := commSet_inter_inter_nonempty (B := B) c hnk hF x.2 y.2 hxu hyu hxy.2 hne
  rw [Set.mem_inter_iff, Set.mem_inter_iff] at hu
  obtain ⟨⟨huA, huX⟩, huY⟩ := hu
  obtain ⟨h, hh⟩ := exists_conj_of_mem_commSet (B := B) c huA hgv
  refine ⟨h, ?_, ?_⟩
  · have hxu : (x : G) ∈ commSet D u := ⟨x.2, huX.2.1.symm, fun h => huX.2.2 h.symm⟩
    rw [mem_patchSet_iff, coe_smulD, ← hh]
    exact Or.inr (conj_mem_commSet hC.setup.normal (h : G) hxu)
  · have hyu' : (y : G) ∈ commSet D u := ⟨y.2, huY.2.1.symm, fun h => huY.2.2 h.symm⟩
    rw [mem_patchSet_iff, coe_smulD, ← hh]
    exact Or.inr (conj_mem_commSet hC.setup.normal (h : G) hyu')

omit [DecidableEq F] in
private lemma exists_smul_mem_patchSet_of_adj (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) (g : G) (hgv : (hC.conj g).d ∈ commSet D hC.d)
    {x y : ↥D} (hxy : (commGraph D).Adj x y) :
    ∃ h : ↥(Halpha D hC.alpha),
      h • x ∈ patchSet (hC := hC) g ∧ h • y ∈ patchSet (hC := hC) g := by
  by_cases hx : (x : G) ∈ commSet D hC.d
  · exact exists_smul_mem_patchSet_of_mem_commSet (B := B) c g hgv hx hxy
  · by_cases hxd : (x : G) = hC.d
    · exact exists_smul_mem_patchSet_of_eq_d (B := B) c g hgv hxd hxy
    · have hxu : ¬ Commute (x : G) hC.d := fun hc => hx ⟨x.2, hc, hxd⟩
      by_cases hy : (y : G) ∈ commSet D hC.d
      · have h' := exists_smul_mem_patchSet_of_mem_commSet (B := B) (x := y) (y := x) c g hgv
          hy (((commGraph D).adj_comm _ _).mpr hxy)
        obtain ⟨h, h1, h2⟩ := h'
        exact ⟨h, h2, h1⟩
      · by_cases hyd : (y : G) = hC.d
        · have h' := exists_smul_mem_patchSet_of_eq_d (B := B) (x := y) (y := x) c g hgv hyd
            (((commGraph D).adj_comm _ _).mpr hxy)
          obtain ⟨h, h1, h2⟩ := h'
          exact ⟨h, h2, h1⟩
        · have hyu : ¬ Commute (y : G) hC.d := fun hc => hy ⟨y.2, hc, hyd⟩
          exact exists_smul_mem_patchSet_of_not_commute (B := B) c hnk hF g hgv hxu hyu hxy

omit [Finite G] in
private lemma exists_conjModel_mem_modelPatchSet_of_mem_commSet (c : SpChart hC B.hα k F) (g : G)
    (hk : 2 ≤ k) (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {m m' : ↥(mClass Q₀)}
    (hm : (m : MGroup Q₀) ∈ commSet (mClass Q₀) (mRefl Q₀ mU))
    (hmm' : (commGraph (mClass Q₀)).Adj m m') :
    ∃ h : ↥(Subgroup.centralizer {mRefl Q₀ mU}),
      (⟨(h : MGroup Q₀) * (m : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g ∧
      (⟨(h : MGroup Q₀) * (m' : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m'.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g := by
  obtain ⟨a, ha, hma⟩ := (mem_commSet_mRefl_mU_iff hQ₀).mp hm
  have hVne : c.vec (hC.conj g).d ≠ 0 := c.vec_ne_zero _ hgv
  obtain ⟨h', hh'C, hh'eq⟩ := exists_conj_mRefl_mLift_eq (Q₀ := Q₀) hQ₀ ha hVne
  have h1 : (h' : MGroup Q₀) * (m : MGroup Q₀) * (h' : MGroup Q₀)⁻¹ =
      (h' : MGroup Q₀) * mRefl Q₀ (mLift Q₀ a) * (h' : MGroup Q₀)⁻¹ := by
    rw [hma]
  refine ⟨⟨h', hh'C⟩, ?_, ?_⟩
  · rw [mem_modelPatchSet_iff]
    dsimp only
    rw [h1]
    exact Or.inl hh'eq
  · rw [mem_modelPatchSet_iff]
    dsimp only
    have hconj := conj_mem_commSet (setup_mClass hQ₀ hk).normal (h' : MGroup Q₀)
      (mem_commSet_of_adj hmm')
    rw [hma, hh'eq] at hconj
    exact Or.inr hconj

omit [Finite G] in
private lemma exists_conjModel_mem_modelPatchSet_of_eq_mU (c : SpChart hC B.hα k F) (g : G)
    (hk : 2 ≤ k) (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {m m' : ↥(mClass Q₀)}
    (hm : (m : MGroup Q₀) = mRefl Q₀ mU) (hmm' : (commGraph (mClass Q₀)).Adj m m') :
    ∃ h : ↥(Subgroup.centralizer {mRefl Q₀ mU}),
      (⟨(h : MGroup Q₀) * (m : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g ∧
      (⟨(h : MGroup Q₀) * (m' : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m'.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g := by
  have hm' : (m' : MGroup Q₀) ∈ commSet (mClass Q₀) (mRefl Q₀ mU) := by
    have h := mem_commSet_of_adj hmm'
    rwa [hm] at h
  obtain ⟨a, ha, hm'a⟩ := (mem_commSet_mRefl_mU_iff hQ₀).mp hm'
  have hVne : c.vec (hC.conj g).d ≠ 0 := c.vec_ne_zero _ hgv
  obtain ⟨h', hh'C, hh'eq⟩ := exists_conj_mRefl_mLift_eq (Q₀ := Q₀) hQ₀ ha hVne
  have hU : Commute (h' : MGroup Q₀) (mRefl Q₀ mU) :=
    Subgroup.mem_centralizer_singleton_iff.mp hh'C
  have hUeq : (h' : MGroup Q₀) * mRefl Q₀ mU * (h' : MGroup Q₀)⁻¹ = mRefl Q₀ mU := by
    rw [hU.eq]
    group
  have hm'conj : (h' : MGroup Q₀) * (m' : MGroup Q₀) * (h' : MGroup Q₀)⁻¹ =
      mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) := by
    rw [hm'a, hh'eq]
  have hmem : (mRefl Q₀ mU) ∈ commSet (mClass Q₀)
      (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) := by
    refine ⟨⟨mU, ?_, rfl⟩,
      (Subgroup.mem_centralizer_singleton_iff.mp (mRefl_mLift_mem_centralizer _)).symm, ?_⟩
    · exact mForm_mU
    · intro heq
      refine hm'.2.2 ?_
      calc (m' : MGroup Q₀) = (h' : MGroup Q₀)⁻¹ * ((h' : MGroup Q₀) * (m' : MGroup Q₀) *
            (h' : MGroup Q₀)⁻¹) * (h' : MGroup Q₀) := by group
        _ = (h' : MGroup Q₀)⁻¹ * mRefl Q₀ mU * (h' : MGroup Q₀) := by rw [hm'conj, ← heq]
        _ = mRefl Q₀ mU := by
          have hcomm : Commute ((h' : MGroup Q₀)⁻¹) (mRefl Q₀ mU) := hU.inv_left
          rw [hcomm.eq]
          group
  refine ⟨⟨h', hh'C⟩, ?_, ?_⟩
  · rw [mem_modelPatchSet_iff]
    dsimp only
    rw [hm, hUeq]
    exact Or.inr hmem
  · rw [mem_modelPatchSet_iff]
    dsimp only
    exact Or.inl hm'conj

omit [Finite G] in
private lemma conj_mem_modelPatchSet_of_mem_commSet (c : SpChart hC B.hα k F) (g : G)
    (hk : 2 ≤ k) (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {m : ↥(mClass Q₀)} {a : Fin k ⊕ Fin k → F}
    {h' : ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hh'eq : (h' : MGroup Q₀) * mRefl Q₀ (mLift Q₀ a) * (h' : MGroup Q₀)⁻¹ =
      mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)))
    (hcomm : Commute (mRefl Q₀ (mLift Q₀ a)) (m : MGroup Q₀))
    (hne : (m : MGroup Q₀) ≠ mRefl Q₀ (mLift Q₀ a)) :
    (⟨(h' : MGroup Q₀) * (m : MGroup Q₀) * (h' : MGroup Q₀)⁻¹,
      (setup_mClass hQ₀ hk).conj_mem (h' : MGroup Q₀) m.2⟩ : ↥(mClass Q₀)) ∈
      modelPatchSet (B := B) c g := by
  have hmc : (m : MGroup Q₀) ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ a)) :=
    ⟨m.2, hcomm.symm, hne⟩
  have hconj := conj_mem_commSet (setup_mClass hQ₀ hk).normal (h' : MGroup Q₀) hmc
  rw [hh'eq] at hconj
  rw [mem_modelPatchSet_iff]
  dsimp only
  exact Or.inr hconj

omit [Finite G] in
private lemma exists_conjModel_mem_modelPatchSet_of_not_mem (c : SpChart hC B.hα k F) (g : G)
    (hk : 2 ≤ k) (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {m m' : ↥(mClass Q₀)}
    (hm : m ∉ modelBaseSet Q₀) (hm' : m' ∉ modelBaseSet Q₀) :
    ∃ h : ↥(Subgroup.centralizer {mRefl Q₀ mU}),
      (⟨(h : MGroup Q₀) * (m : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g ∧
      (⟨(h : MGroup Q₀) * (m' : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m'.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g := by
  have hnc : ¬ Commute (m : MGroup Q₀) (mRefl Q₀ mU) := by
    rw [mem_modelBaseSet_iff] at hm
    intro hc
    exact hm (Or.inr ⟨m.2, hc, fun heq => hm (Or.inl heq)⟩)
  have hnc' : ¬ Commute (m' : MGroup Q₀) (mRefl Q₀ mU) := by
    rw [mem_modelBaseSet_iff] at hm'
    intro hc
    exact hm' (Or.inr ⟨m'.2, hc, fun heq => hm' (Or.inl heq)⟩)
  obtain ⟨X, hX, hmX⟩ := m.2
  obtain ⟨X', hX', hmX'⟩ := m'.2
  have hβ : X.1.2 ≠ 0 := by
    apply coord_ne_zero_of_not_commute
    rwa [← hmX]
  have hβ' : X'.1.2 ≠ 0 := by
    apply coord_ne_zero_of_not_commute
    rwa [← hmX']
  obtain ⟨a, ha, haform, haform'⟩ := exists_mStabForm_eq_one_of_two (Q₀ := Q₀) hQ₀ hk X X'
  have hcomm : Commute (mRefl Q₀ (mLift Q₀ a)) (m : MGroup Q₀) := by
    rw [hmX]
    exact (commute_mLift_iff hQ₀ hX hβ a).mpr haform
  have hcomm' : Commute (mRefl Q₀ (mLift Q₀ a)) (m' : MGroup Q₀) := by
    rw [hmX']
    exact (commute_mLift_iff hQ₀ hX' hβ' a).mpr haform'
  have hVne : c.vec (hC.conj g).d ≠ 0 := c.vec_ne_zero _ hgv
  obtain ⟨h', hh'C, hh'eq⟩ := exists_conj_mRefl_mLift_eq (Q₀ := Q₀) hQ₀ ha hVne
  have hne : (m : MGroup Q₀) ≠ mRefl Q₀ (mLift Q₀ a) := by
    intro heq
    rw [heq] at hnc
    exact hnc (Subgroup.mem_centralizer_singleton_iff.mp (mRefl_mLift_mem_centralizer a))
  have hne' : (m' : MGroup Q₀) ≠ mRefl Q₀ (mLift Q₀ a) := by
    intro heq
    rw [heq] at hnc'
    exact hnc' (Subgroup.mem_centralizer_singleton_iff.mp (mRefl_mLift_mem_centralizer a))
  refine ⟨⟨h', hh'C⟩, ?_, ?_⟩
  · exact conj_mem_modelPatchSet_of_mem_commSet (B := B) c g hk hQ₀ hh'eq hcomm hne
  · exact conj_mem_modelPatchSet_of_mem_commSet (B := B) c g hk hQ₀ hh'eq hcomm' hne'

omit [Finite G] in
private lemma exists_smul_mem_modelPatchSet_of_adj (c : SpChart hC B.hα k F) (g : G) (hk : 2 ≤ k)
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (hgv : (hC.conj g).d ∈ commSet D hC.d) {m m' : ↥(mClass Q₀)}
    (hmm' : (commGraph (mClass Q₀)).Adj m m') :
    ∃ h : ↥(Subgroup.centralizer {mRefl Q₀ mU}),
      (⟨(h : MGroup Q₀) * (m : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g ∧
      (⟨(h : MGroup Q₀) * (m' : MGroup Q₀) * (h : MGroup Q₀)⁻¹,
        (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) m'.2⟩ : ↥(mClass Q₀)) ∈
        modelPatchSet (B := B) c g := by
  by_cases hm : m ∈ modelBaseSet Q₀
  · rw [mem_modelBaseSet_iff] at hm
    rcases hm with hme | hmc
    · exact exists_conjModel_mem_modelPatchSet_of_eq_mU (B := B) c g hk hQ₀ hgv hme hmm'
    · exact exists_conjModel_mem_modelPatchSet_of_mem_commSet (B := B) c g hk hQ₀ hgv hmc hmm'
  · by_cases hm' : m' ∈ modelBaseSet Q₀
    · rw [mem_modelBaseSet_iff] at hm'
      rcases hm' with hm'e | hm'c
      · have h' := exists_conjModel_mem_modelPatchSet_of_eq_mU (B := B) (m := m') (m' := m) c g
          hk hQ₀ hgv hm'e (((commGraph (mClass Q₀)).adj_comm _ _).mpr hmm')
        obtain ⟨h, h1, h2⟩ := h'
        exact ⟨h, h2, h1⟩
      · have h' := exists_conjModel_mem_modelPatchSet_of_mem_commSet (B := B) (m := m') (m' := m)
          c g hk hQ₀ hgv hm'c (((commGraph (mClass Q₀)).adj_comm _ _).mpr hmm')
        obtain ⟨h, h1, h2⟩ := h'
        exact ⟨h, h2, h1⟩
    · exact exists_conjModel_mem_modelPatchSet_of_not_mem (B := B) c g hk hQ₀ hgv hm hm'

omit [Finite G] [DecidableEq F] in
private lemma apply_patchPoint_eq_and_commute_iff (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) {F' : ↥D ≃ ↥(mClass Q₀)}
    (hFeq : ∀ (h : ↥(Halpha D hC.alpha)) (x : ↥D),
      (F' ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
        (θ h : MGroup Q₀) * (F' x : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹)
    (hFB : ∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
      (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀))
    (hgv : (hC.conj g).d ∈ commSet D hC.d) :
    (F' ⟨(hC.conj g).d, hgv.1⟩ : MGroup Q₀) =
        mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) ∧
      ∀ y : ↥D, Commute ((hC.conj g).d) (y : G) ↔
        Commute (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) (F' y : MGroup Q₀) := by
  have hvH : ((hC.conj g).d) ∈ Halpha D hC.alpha :=
    mem_Halpha_of_mem_commSet hC B.hα hgv
  have hvB : (⟨(hC.conj g).d, hgv.1⟩ : ↥D) ∈ halphaSet (hC := hC) := hvH
  have hv : (F' ⟨(hC.conj g).d, hgv.1⟩ : MGroup Q₀) =
      mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d)) := by
    rw [hFB ⟨(hC.conj g).d, hvH⟩ hgv.1, hθ.2.2 ((hC.conj g).d) hgv]
  refine ⟨hv, fun y => ?_⟩
  have h := baseSet_commute_iff hFeq hFB hvB y
  rwa [hv] at h

omit [Finite G] [DecidableEq F] in
private lemma image_patchSet (c : SpChart hC B.hα k F) (g : G)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) {F' : ↥D ≃ ↥(mClass Q₀)}
    (hFeq : ∀ (h : ↥(Halpha D hC.alpha)) (x : ↥D),
      (F' ⟨(h : G) * (x : G) * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : MGroup Q₀) =
        (θ h : MGroup Q₀) * (F' x : MGroup Q₀) * (θ h : MGroup Q₀)⁻¹)
    (hFB : ∀ (z : ↥(Halpha D hC.alpha)) (hz : (z : G) ∈ D),
      (F' ⟨z, hz⟩ : MGroup Q₀) = (θ z : MGroup Q₀))
    (hgv : (hC.conj g).d ∈ commSet D hC.d) :
    F' '' patchSet (hC := hC) g = modelPatchSet (B := B) c g := by
  obtain ⟨hv, hcomm⟩ := apply_patchPoint_eq_and_commute_iff (B := B) c g hθ hFeq hFB hgv
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_patchSet_iff] at hx
    rw [mem_modelPatchSet_iff]
    rcases hx with hxv | hxDv
    · have hx' : x = ⟨(hC.conj g).d, hgv.1⟩ := Subtype.ext hxv
      rw [hx']
      exact Or.inl hv
    · refine Or.inr ⟨(F' x).2, ?_, ?_⟩
      · exact ((hcomm x).mp hxDv.2.1.symm).symm
      · intro heq
        refine hxDv.2.2 ?_
        have h1 : F' x = F' ⟨(hC.conj g).d, hgv.1⟩ := by
          apply Subtype.ext
          rw [hv]
          exact heq
        rw [F'.injective h1]
  · intro hm
    rw [mem_modelPatchSet_iff] at hm
    rcases hm with hmv | hmDv
    · refine ⟨⟨(hC.conj g).d, hgv.1⟩, Or.inl rfl, ?_⟩
      apply Subtype.ext
      show (F' ⟨(hC.conj g).d, hgv.1⟩ : MGroup Q₀) = (m : MGroup Q₀)
      rw [hv, hmv]
    · obtain ⟨y, hy⟩ := F'.surjective ⟨m, hmDv.1⟩
      have hmy : (F' y : MGroup Q₀) = (m : MGroup Q₀) := congrArg Subtype.val hy
      refine ⟨y, Or.inr ⟨y.2, ?_, ?_⟩, hy⟩
      · have h := hmDv.2.1
        rw [← hmy] at h
        exact ((hcomm y).mpr h.symm).symm
      · intro heq
        refine hmDv.2.2 ?_
        have hyv : y = ⟨(hC.conj g).d, hgv.1⟩ := Subtype.ext heq
        rw [← hmy, hyv, hv]

theorem exists_commGraphIso (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    (hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
      IsFormOfLine c Q₀ w₀) :
    Nonempty (commGraph (mClass Q₀) ≃g commGraph D) := by
  classical
  have hk : 2 ≤ k := B.two_le_rank hnk
  obtain ⟨hu, θ, hθ⟩ := exists_theta (B := B) c hQ₀
  obtain ⟨F', hFeq, hFB, g, hgv, ψ, hψinj, hψF⟩ :=
    exists_patchMap (B := B) c hnk hF hQ₀ hθ hQ₀ty
  have himage : F' '' patchSet (hC := hC) g = modelPatchSet (B := B) c g :=
    image_patchSet (B := B) c g hθ hFeq hFB hgv
  have hP : ∀ x ∈ patchSet (hC := hC) g, ∀ y ∈ patchSet (hC := hC) g,
      (commGraph D).Adj x y ↔ (commGraph (mClass Q₀)).Adj (F' x) (F' y) :=
    fun x hx y hy => patchSet_adj_iff (B := B) g hFeq hFB hψinj hψF hgv hx hy
  have hcov : ∀ x y : ↥D, (commGraph D).Adj x y →
      ∃ h : ↥(Halpha D hC.alpha),
        (⟨(h : G) * x * (h : G)⁻¹, hC.setup.conj_mem (h : G) x.2⟩ : ↥D) ∈
          patchSet (hC := hC) g ∧
        (⟨(h : G) * y * (h : G)⁻¹, hC.setup.conj_mem (h : G) y.2⟩ : ↥D) ∈
          patchSet (hC := hC) g := by
    intro x y hxy
    obtain ⟨h, h1, h2⟩ := exists_smul_mem_patchSet_of_adj (B := B) c hnk hF g hgv hxy
    exact ⟨h, h1, h2⟩
  have hcov' : ∀ x y : ↥(mClass Q₀), (commGraph (mClass Q₀)).Adj x y →
      ∃ h : ↥(Subgroup.centralizer {mRefl Q₀ mU}),
        (⟨(h : MGroup Q₀) * x * (h : MGroup Q₀)⁻¹,
          (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) x.2⟩ : ↥(mClass Q₀)) ∈
          F' '' patchSet (hC := hC) g ∧
        (⟨(h : MGroup Q₀) * y * (h : MGroup Q₀)⁻¹,
          (setup_mClass hQ₀ hk).conj_mem (h : MGroup Q₀) y.2⟩ : ↥(mClass Q₀)) ∈
          F' '' patchSet (hC := hC) g := by
    intro x y hxy
    obtain ⟨h, h1, h2⟩ := exists_smul_mem_modelPatchSet_of_adj (B := B) c g hk hQ₀ hgv hxy
    exact ⟨h, by rw [himage]; exact h1, by rw [himage]; exact h2⟩
  exact nonempty_commGraphIso_of_conj_equivariant hC.setup (setup_mClass hQ₀ hk) θ F' hFeq
    (patchSet (hC := hC) g) hP hcov hcov'

theorem twelveEleven_sp_core (h87 : Theorem8_7) (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m : ℕ} {f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) :
    ∃ t ∈ D, IsOrthReflection G (m + 2) f t := by
  classical
  obtain ⟨k, F, hFld, hFint, hChar, hnk, hF, ⟨c⟩⟩ := exists_spChart hC hMZ hα hs hSp
  let instF : Field F := hFld
  let instFin : Fintype F := hFint
  let instDec : DecidableEq F := Classical.decEq F
  let instChar : CharP F 2 := hChar
  have hk : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hO4 : ¬ O4PairData G D :=
    not_o4PairData_of_isSymplecticTransvection hMZ hs hm hf hSp
  let B : SpBranch hC :=
    { hIH := hIH, hrad := hrad, hMZ := hMZ, hα := hα, s := s, hs := hs,
      n := m, f := f, hn := hm, hf := hf, hSp := hSp,
      hdiam := fun a ha b hb hab =>
        Nine.commSet_inter_nonempty_of_theorem8_7 h87 hC hα hrad hO4 ha hb hab }
  obtain ⟨w₀, hw₀D, hw₀nc, hw₀line⟩ :=
    (twelveSeven_sp_exists hIH hC hMZ hα hs hm hf hSp).2
  obtain ⟨v₀, hv₀d, hv₀w⟩ :=
    B.hdiam hC.d hC.hd w₀ hw₀D (fun h => hw₀nc h.symm)
  obtain ⟨Q₀, hQ₀, hQ₀line⟩ :=
    exists_quadraticForm_commSet_inter hIH hC hMZ hα hs hm hf hSp c hnk hF
      hv₀d hw₀D hw₀nc hv₀w.2.1.symm
  obtain ⟨hu, θ, hθ⟩ := exists_theta (B := B) c hQ₀
  obtain ⟨β⟩ := exists_commGraphIso (B := B) c hnk hF hQ₀
    ⟨w₀, hw₀D, by simpa using hw₀line, ⟨hQ₀, hQ₀line.1⟩⟩
  have hZ : Subgroup.center G = ⊥ := hrad (Subgroup.center G) inferInstance inferInstance
  have hdiam' : ∀ w ∈ D, ¬ Commute w hC.d →
      (commSet D hC.d ∩ commSet D w).Nonempty :=
    fun w hw hwd => B.hdiam hC.d hC.hd w hw (fun h => hwd h.symm)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_commGraphIso
    (setup_mClass hQ₀ hk) hC.setup (center_mGroup_eq_bot hQ₀ hk1) hZ β
    (fun u σ hσ => twelveNine_sp hIH hC hMZ hα hs hm hf hSp hdiam' u σ hσ)
  have hmU : mRefl Q₀ mU ∈ mClass Q₀ := ⟨mU, mForm_mU, rfl⟩
  refine ⟨φ (mRefl Q₀ mU), ?_, ?_⟩
  · have hh : φ (mRefl Q₀ mU) = (β (⟨mRefl Q₀ mU, hmU⟩ : ↥(mClass Q₀)) : G) := by
      simpa using hφ (⟨mRefl Q₀ mU, hmU⟩ : ↥(mClass Q₀))
    rw [hh]
    exact (β ⟨mRefl Q₀ mU, hmU⟩).2
  · have h := isOrthReflection_mGroup (Q₀ := Q₀) hQ₀ hk1 hF
    have := isOrthReflection_map φ h
    rwa [show 2 * k + 2 = m + 2 by omega] at this


end CFSG.OddTranspositions.PartThree.ElevenSp

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.OddTranspositions.PartFour
  CFSG.OddTranspositions.PartThree.ElevenSp

theorem twelveSpBranch_of_theorem8_7 (h87 : Theorem8_7) : TwelveSpBranch := by
  intro G _ _ D hC hIH hrad hE hMZ _hO4 hα s hs m f hm hf hSp
  exact Or.inl ⟨s, hs, m, f, by omega, hf, hSp,
    twelveEleven_sp_core h87 hIH hC hrad hMZ hα hs hm hf hSp⟩

end CFSG.OddTranspositions.PartThree

end
