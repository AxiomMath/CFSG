module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpHyp
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModel
import CFSG.OddTranspositions.PartThree.Twelve.Ten
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelChart
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.OddTranspositions.WidthSylow
import Mathlib.Algebra.Group.TypeTags.Basic
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull
open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D}

omit [Finite G] in
private lemma mem_commSet_conj_iff (hC : HypothesisC D) (g z : G) :
    z ∈ commSet D (hC.conj g).d ↔ g⁻¹ * z * g ∈ commSet D hC.d := by
  rw [HypothesisC.conj_d hC g, commSet_conj hC.setup.normal g hC.d, mem_cimg]

theorem exists_spBranch_conj (B : SpBranch hC) (g : G) :
    ∃ B' : SpBranch (hC.conj g), B'.n = B.n ∧ B'.f = B.f := by
  classical
  have hMZ : CFSG.solvableRadical (Halpha D (hC.conj g).alpha) ≤
      Subgroup.center (Halpha D (hC.conj g).alpha) := by
    rw [← conjRadical_map hC g, ← Subgroup.map_center_eq (conjEquiv hC g)]
    exact Subgroup.map_mono B.hMZ
  have hα : (hC.conj g).alpha = {(hC.conj g).d} := by
    rw [HypothesisC.conj_alpha hC g, B.hα, HypothesisC.conj_d hC g]
    ext x
    rw [mem_cimg, Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * hC.d * g⁻¹ := by rw [h]
    · intro h
      rw [h]
      group
  let θ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃*
      Halpha D (hC.conj g).alpha ⧸ CFSG.solvableRadical (Halpha D (hC.conj g).alpha) :=
    QuotientGroup.congr _ _ (conjEquiv hC g) (conjRadical_map hC g)
  have hs : θ B.s ∈ imageClass (hC.conj g) := by
    rw [← imageClass_conj hC g]
    exact ⟨B.s, B.hs, rfl⟩
  let B' : SpBranch (hC.conj g) :=
    { hIH := B.hIH, hrad := B.hrad, hMZ := hMZ, hα := hα, s := θ B.s, hs := hs,
      n := B.n, f := B.f, hn := B.hn, hf := B.hf,
      hSp := isSymplecticTransvection_map θ B.hSp, hdiam := B.hdiam }
  exact ⟨B', rfl, rfl⟩

noncomputable def SpBranch.conj (B : SpBranch hC) (g : G) : SpBranch (hC.conj g) :=
  (exists_spBranch_conj B g).choose

theorem SpBranch.conj_n (B : SpBranch hC) (g : G) : (B.conj g).n = B.n :=
  (exists_spBranch_conj B g).choose_spec.1

theorem SpBranch.conj_f (B : SpBranch hC) (g : G) : (B.conj g).f = B.f :=
  (exists_spBranch_conj B g).choose_spec.2

variable {B : SpBranch hC} {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma spChart_conj_rho_apply (c : SpChart hC B.hα k F) (g : G) (z : G)
    (hz : z ∈ commSet D (hC.conj g).d) :
    (c.ρ.comp (conjEquiv hC g).symm.toMonoidHom)
        ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
      spTransvection (c.vec (g⁻¹ * z * g)) 1 := by
  have hz' : g⁻¹ * z * g ∈ commSet D hC.d := (mem_commSet_conj_iff hC g z).mp hz
  have hsymm : (conjEquiv hC g).symm
      ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ =
      ⟨g⁻¹ * z * g, mem_Halpha_of_mem_commSet hC B.hα hz'⟩ := by
    apply (conjEquiv hC g).injective
    rw [MulEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [conjEquiv_coe]
    show z = g * (g⁻¹ * z * g) * g⁻¹
    group
  show c.ρ ((conjEquiv hC g).symm
      ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩) =
    spTransvection (c.vec (g⁻¹ * z * g)) 1
  rw [hsymm]
  exact c.map_eq (g⁻¹ * z * g) hz'

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma exists_mem_commSet_conj_vec (c : SpChart hC B.hα k F) (g : G) (v : Fin k ⊕ Fin k → F)
    (hv : v ≠ 0) :
    ∃ z ∈ commSet D (hC.conj g).d, c.vec (g⁻¹ * z * g) = v := by
  obtain ⟨z, hz, hzv⟩ := c.exists_vec v hv
  refine ⟨g * z * g⁻¹, (mem_commSet_conj_iff hC g (g * z * g⁻¹)).mpr ?_, ?_⟩
  · show g⁻¹ * (g * z * g⁻¹) * g ∈ commSet D hC.d
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact hz
  · show c.vec (g⁻¹ * (g * z * g⁻¹) * g) = v
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group, hzv]

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma commute_iff_spForm_conj (c : SpChart hC B.hα k F) (g : G)
    {z z' : G} (hz : z ∈ commSet D (hC.conj g).d) (hz' : z' ∈ commSet D (hC.conj g).d) :
    Commute z z' ↔ spForm k F (c.vec (g⁻¹ * z * g)) (c.vec (g⁻¹ * z' * g)) = 0 := by
  have hz'' : g⁻¹ * z * g ∈ commSet D hC.d := (mem_commSet_conj_iff hC g z).mp hz
  have hz3 : g⁻¹ * z' * g ∈ commSet D hC.d := (mem_commSet_conj_iff hC g z').mp hz'
  have hcomm' : Commute z z' ↔ Commute (g⁻¹ * z * g) (g⁻¹ * z' * g) := by
    rw [← Commute.conj_iff (h := g⁻¹)]
    simp
  rw [hcomm']
  exact c.commute_iff _ hz'' _ hz3

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem exists_spChart_conj (g : G) (c : SpChart hC B.hα k F) :
    ∃ c' : SpChart (hC.conj g) (B.conj g).hα k F,
      ∀ z : G, c'.vec z = c.vec (g⁻¹ * z * g) := by
  classical
  have hsurj : Function.Surjective (c.ρ.comp (conjEquiv hC g).symm.toMonoidHom) := by
    intro y
    obtain ⟨x, hx⟩ := c.surjective y
    exact ⟨(conjEquiv hC g) x, by
      show c.ρ ((conjEquiv hC g).symm ((conjEquiv hC g) x)) = y
      rw [MulEquiv.symm_apply_apply, hx]⟩
  have hker : (c.ρ.comp (conjEquiv hC g).symm.toMonoidHom).ker =
      CFSG.solvableRadical (Halpha D (hC.conj g).alpha) := by
    rw [MulEquiv.toMonoidHom_eq_coe (f := (conjEquiv hC g).symm),
      MonoidHom.ker_comp_mulEquiv (g := c.ρ) (iso := (conjEquiv hC g).symm), c.ker_eq]
    simpa only [MulEquiv.symm_symm] using conjRadical_map hC g
  have hvnz : ∀ z ∈ commSet D (hC.conj g).d, c.vec (g⁻¹ * z * g) ≠ 0 := by
    intro z hz
    exact c.vec_ne_zero (g⁻¹ * z * g) ((mem_commSet_conj_iff hC g z).mp hz)
  have hinj : Set.InjOn (fun z => c.vec (g⁻¹ * z * g)) (commSet D (hC.conj g).d) := by
    intro z hz z' hz' h
    have h2 : c.vec (g⁻¹ * z * g) = c.vec (g⁻¹ * z' * g) := h
    have h3 := c.injOn ((mem_commSet_conj_iff hC g z).mp hz)
      ((mem_commSet_conj_iff hC g z').mp hz') h2
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z' * g) * g⁻¹ := by rw [h3]
      _ = z' := by group
  let c' : SpChart (hC.conj g) (B.conj g).hα k F :=
    { ρ := c.ρ.comp (conjEquiv hC g).symm.toMonoidHom,
      vec := fun z => c.vec (g⁻¹ * z * g),
      surjective := hsurj,
      ker_eq := hker,
      vec_ne_zero := hvnz,
      map_eq := spChart_conj_rho_apply (B := B) c g,
      exists_vec := exists_mem_commSet_conj_vec (B := B) c g,
      injOn := hinj,
      commute_iff := fun z hz z' hz' => commute_iff_spForm_conj (B := B) c g hz hz' }
  exact ⟨c', fun z => rfl⟩

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem _root_.CFSG.OddTranspositions.PartThree.SpChart.ker_eq_zpowers (B : SpBranch hC)
    (c : SpChart hC B.hα k F) (hu : hC.d ∈ Halpha D hC.alpha) :
    c.ρ.ker = Subgroup.zpowers ⟨hC.d, hu⟩ := by
  obtain ⟨_, hZ, -, -⟩ := twelveTen_sp_center hC B.hMZ B.hs B.hn B.hf B.hSp
  exact c.ker_eq.trans ((le_antisymm B.hMZ (center_le_solvableRadical _)).trans hZ)

private lemma zmodTwoHom_apply_of_mem_commSet {hu : hC.d ∈ Halpha D hC.alpha}
    (χ : ↥(Halpha D hC.alpha) →* Multiplicative (ZMod 2))
    (hχker : χ.ker = commutator (Halpha D hC.alpha))
    (hχu : χ ⟨hC.d, hu⟩ = Multiplicative.ofAdd 1)
    (hxd : ∀ x ∈ DstarH hC, x * ⟨hC.d, hu⟩ ∈ commutator (Halpha D hC.alpha))
    {z : G} (hz : z ∈ commSet D hC.d) :
    χ ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ = Multiplicative.ofAdd 1 := by
  set zH : Halpha D hC.alpha := ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ with hzH
  have hzu : χ zH * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
    have h1 : zH * ⟨hC.d, hu⟩ ∈ χ.ker := by
      rw [hχker]
      exact hxd zH (mem_DstarH_of_mem_commSet hC B.hα hz)
    rwa [MonoidHom.mem_ker, map_mul, hχu] at h1
  calc χ zH = (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ := eq_inv_of_mul_eq_one_left hzu
    _ = Multiplicative.ofAdd 1 := by decide

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem exists_spCoord (c : SpChart hC B.hα k F) :
    ∃ (hu : hC.d ∈ Halpha D hC.alpha)
      (e : ↥(Halpha D hC.alpha) ≃* (↥(StatedSp k F) × Multiplicative (ZMod 2))),
      (∀ h, (e h).1 = c.ρ h) ∧ e ⟨hC.d, hu⟩ = (1, Multiplicative.ofAdd 1) ∧
      ∀ z, ∀ hz : z ∈ commSet D hC.d,
        e ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ =
          (spTransvection (c.vec z) 1, Multiplicative.ofAdd 1) := by
  classical
  obtain ⟨hu, hZ, hZH, hxd⟩ :=
    twelveTen_sp_center hC B.hMZ B.hs B.hn B.hf B.hSp
  let u : Halpha D hC.alpha := ⟨hC.d, hu⟩
  have hu1 : u ≠ 1 := by
    intro h
    exact hC.setup.oddT.ne_one hC.hd (congrArg Subtype.val h)
  have hu2 : u ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (hC.setup.oddT.mul_self_eq_one hC.hd)
  have hker : c.ρ.ker = Subgroup.zpowers u := c.ker_eq_zpowers B hu
  have huH' : u ∉ commutator (Halpha D hC.alpha) := by
    intro h1
    have h2 : u ∈ Subgroup.center (Halpha D hC.alpha) ⊓ commutator (Halpha D hC.alpha) :=
      ⟨by rw [hZ]; exact Subgroup.mem_zpowers u, h1⟩
    rw [hZH, Subgroup.mem_bot] at h2
    exact hu1 h2
  obtain ⟨χ, hχker, hχu⟩ := exists_zmodTwoHom_ker_eq_commutator
    (S := DstarH hC) (DstarH_closure_eq_top hC) huH' hu2 (fun x hx => hxd x hx)
  have hbij : Function.Bijective (c.ρ.prod χ) :=
    bijective_prod_of_ker_eq_zpowers c.ρ χ c.surjective hker hu2 hχu
  let e : ↥(Halpha D hC.alpha) ≃* (↥(StatedSp k F) × Multiplicative (ZMod 2)) :=
    MulEquiv.ofBijective (c.ρ.prod χ) hbij
  have hρu : c.ρ u = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_zpowers u
  have hχz : ∀ z (hz : z ∈ commSet D hC.d),
      χ ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ = Multiplicative.ofAdd 1 :=
    fun z hz => zmodTwoHom_apply_of_mem_commSet (B := B) χ hχker hχu hxd hz
  refine ⟨hu, e, fun h => rfl, ?_, ?_⟩
  · show (c.ρ u, χ u) = (1, Multiplicative.ofAdd 1)
    rw [hρu, hχu]
  · intro z hz
    show (c.ρ ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩,
        χ ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩) =
      (spTransvection (c.vec z) 1, Multiplicative.ofAdd 1)
    rw [c.map_eq z hz, hχz z hz]

@[expose] def IsBasePointIdentification {hα : hC.alpha = {hC.d}}
    (c : SpChart hC hα k F) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hu : hC.d ∈ Halpha D hC.alpha)
    (θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})) : Prop :=
  (∀ (h : ↥(Halpha D hC.alpha)) (x : Fin k ⊕ Fin k → F),
    spEnd (c.ρ h) x = (((θ h : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2) ∧
  ((θ ⟨hC.d, hu⟩ : MGroup Q₀) = mRefl Q₀ mU) ∧
  ∀ z, ∀ hz : z ∈ commSet D hC.d,
    (θ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : MGroup Q₀) =
      mRefl Q₀ (mLift Q₀ (c.vec z))

omit [DecidableEq F] in
theorem exists_theta (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) :
    ∃ (hu : hC.d ∈ Halpha D hC.alpha)
      (θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})),
      IsBasePointIdentification (hα := B.hα) c hu θ := by
  classical
  obtain ⟨hu, e, he1, he2, he3⟩ := exists_spCoord (B := B) c
  obtain ⟨eM, hm⟩ := exists_isModelChart (Q₀ := Q₀) hQ₀
  obtain ⟨hm1, hm2, hm3⟩ := hm
  have hmemU : mRefl Q₀ mU ∈ Subgroup.centralizer {mRefl Q₀ mU} :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hmemLift : ∀ x : Fin k ⊕ Fin k → F, x ≠ 0 →
      mRefl Q₀ (mLift Q₀ x) ∈ Subgroup.centralizer {mRefl Q₀ mU} := by
    intro x _
    rw [mem_centralizer_mRefl_mU_iff hQ₀]
    show reflect (mForm Q₀) (mLift Q₀ x) mU = mU
    exact reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact polar_mU_mLift x)
  refine ⟨hu, e.trans eM.symm, ?_, ?_, ?_⟩
  · intro h x
    have h1 := hm1 (e.trans eM.symm h) x
    rw [show eM (e.trans eM.symm h) = e h from MulEquiv.apply_symm_apply eM (e h), he1 h] at h1
    exact h1
  · refine congrArg Subtype.val (show e.trans eM.symm ⟨hC.d, hu⟩ =
        ⟨mRefl Q₀ mU, hmemU⟩ from ?_)
    apply eM.injective
    rw [show eM (e.trans eM.symm ⟨hC.d, hu⟩) = e ⟨hC.d, hu⟩ from
      MulEquiv.apply_symm_apply eM (e ⟨hC.d, hu⟩), he2, hm2 hmemU]
  · intro z hz
    have hx : c.vec z ≠ 0 := c.vec_ne_zero z hz
    refine congrArg Subtype.val (show e.trans eM.symm
        ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ =
        ⟨mRefl Q₀ (mLift Q₀ (c.vec z)), hmemLift (c.vec z) hx⟩ from ?_)
    apply eM.injective
    rw [show eM (e.trans eM.symm ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩) =
        e ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ from
      MulEquiv.apply_symm_apply eM (e ⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩),
      he3 z hz, hm3 (c.vec z) hx (hmemLift (c.vec z) hx)]

end CFSG.OddTranspositions.PartThree.ElevenSp

namespace CFSG.OddTranspositions.PartThree

namespace SpChart

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D}
  {B : ElevenSp.SpBranch hC} {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [CharP F 2]

noncomputable def conj (c : SpChart hC B.hα k F) (g : G) :
    SpChart (hC.conj g) (B.conj g).hα k F :=
  (ElevenSp.exists_spChart_conj (B := B) g c).choose

end SpChart

end CFSG.OddTranspositions.PartThree

end
