module

public import CFSG.RankThree.PartOne.Q1327Z.Transport
public import CFSG.RankThree.PartOne.KFCL.SpBlocks
public import CFSG.Certificates.Kernel.ThDemp.OrbElt
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.R10Final
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.Q1327C.BRows
public import CFSG.RankThree.PartOne.Q1327C.P5Glue
public import CFSG.RankThree.PartOne.Q1327Z.Refl
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate9130

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG.LieType.Universal.Symplectic.SpExtras CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.RankThree.PartOne.KFCL.Sp CFSG.Assembly.LowTwoRank

section Root

variable {K : Type} [Field K] {p : ℕ}

@[expose] noncomputable def ratio (t : StatedSp 3 K) (a b : Fin 3 ⊕ Fin 3) : K :=
  mat 3 K t a a * (mat 3 K t b b)⁻¹

theorem pos2_eq {n : ℕ} (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) :
    pos2 r = (par (pos1 r).2, par (pos1 r).1) := by
  cases r <;> simp [pos1, pos2, par]

theorem pos2_ne {n : ℕ} (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) :
    (pos2 r).1 ≠ (pos2 r).2 := by
  rw [pos2_eq]
  exact fun h => pos1_ne r (par_injective h).symm

theorem E_diag {n : ℕ} (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) (a : Fin n ⊕ Fin n) :
    E K r a a = 0 := by
  by_contra h
  rcases eq_pos_of_E_ne_zero r a a h with h' | h'
  · exact pos1_ne r ((congrArg Prod.fst h').symm.trans (congrArg Prod.snd h'))
  · exact pos2_ne r ((congrArg Prod.fst h').symm.trans (congrArg Prod.snd h'))

theorem ratio_pos2 {t : StatedSp 3 K} (ht : t ∈ spTorus p 3 K)
    (r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3) (hp : p ≠ 0) :
    ratio t (pos2 r).1 (pos2 r).2 = ratio t (pos1 r).1 (pos1 r).2 := by
  have h1 := spTorus_ne_zero ht (pos1 r).1 hp
  have h2 := spTorus_ne_zero ht (pos1 r).2 hp
  rw [pos2_eq]
  simp only [ratio]
  rw [spTorus_par ht, spTorus_par ht]
  field_simp

theorem mul_left_entry {D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K}
    (hD : ∀ a b, a ≠ b → D a b = 0) (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (a b : Fin 3 ⊕ Fin 3) : (D * M) a b = D a a * M a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rw [hD a c (Ne.symm hc), zero_mul]
  · simp

theorem mul_right_entry {D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K}
    (hD : ∀ a b, a ≠ b → D a b = 0) (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (a b : Fin 3 ⊕ Fin 3) : (M * D) a b = M a b * D b b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · intro c _ hc
    rw [hD c b hc, mul_zero]
  · simp

theorem conj_elt {t : StatedSp 3 K} (ht : t ∈ spTorus p 3 K) (hp : p ≠ 0)
    (r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3) (u : K) :
    t * elt r u * t⁻¹ = elt r (ratio t (pos1 r).1 (pos1 r).2 * u) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt]
  have hD : ∀ a b, a ≠ b → mat 3 K t a b = 0 := fun a b hab => spTorus_apply_ne ht hab
  have hne0 := fun a => spTorus_ne_zero ht a hp
  have hkey : ∀ a b, E K r a b ≠ 0 →
      mat 3 K t a a = ratio t (pos1 r).1 (pos1 r).2 * mat 3 K t b b := by
    intro a b hab
    rcases eq_pos_of_E_ne_zero r a b hab with h' | h'
    · have ha : a = (pos1 r).1 := congrArg Prod.fst h'
      have hb : b = (pos1 r).2 := congrArg Prod.snd h'
      rw [ha, hb, ratio, mul_assoc, inv_mul_cancel₀ (hne0 _), mul_one]
    · have h3 := ratio_pos2 ht r hp
      have ha : a = (pos2 r).1 := congrArg Prod.fst h'
      have hb : b = (pos2 r).2 := congrArg Prod.snd h'
      rw [ha, hb, ← h3, ratio, mul_assoc, inv_mul_cancel₀ (hne0 _), mul_one]
  ext a b
  rw [mul_left_entry hD, mul_right_entry hD, Matrix.add_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [E_diag]
    simp
  · rw [Matrix.one_apply_ne hab]
    by_cases hE : E K r a b = 0
    · rw [hE]
      simp
    · rw [hkey a b hE]
      ring

theorem eq_of_le_of_relIndex_eq_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {S S' T : Subgroup G} (hSS' : S ≤ S') (hS'T : S' ≤ T) (hidx : S.relIndex T = p)
    (hne : S' ≠ T) : S = S' := by
  have h1 := Subgroup.relIndex_mul_relIndex S S' T hSS' hS'T
  rw [hidx] at h1
  have hd : S'.relIndex T ∣ p := ⟨S.relIndex S', by rw [← h1, mul_comm]⟩
  rcases (Nat.dvd_prime hp).1 hd with h2 | h2
  · exact absurd (le_antisymm hS'T (Subgroup.relIndex_eq_one.1 h2)) hne
  · rw [h2] at h1
    have h3 : S.relIndex S' = 1 := Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h1, one_mul])
    exact le_antisymm hSS' (Subgroup.relIndex_eq_one.1 h3)

theorem noncommOK_spTorus (hp : p.Prime) : NoncommOK p (spTorus p 3 K) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rintro g - S hST hSidx hgS ⟨x, hxT, hx⟩ - - c hcT hcS -
  have hgx : ¬ Commute x g := by
    intro h
    apply hx
    have h1 : g * x = x * g := h.eq.symm
    rw [h1]
    group
  have hxd : ∀ a b, a ≠ b → mat 3 K x a b = 0 := fun a b hab => spTorus_apply_ne hxT hab
  rw [commute_iff_entries hxd] at hgx
  push Not at hgx
  obtain ⟨a, b, hab⟩ := hgx
  have hg0 : mat 3 K g a b ≠ 0 := fun h0 => hab (by rw [h0, mul_zero, zero_mul])
  have hxab : mat 3 K x a a ≠ mat 3 K x b b := fun h => hab (by rw [h, mul_comm])
  have hne : a ≠ b := fun h => hxab (by rw [h])
  have hS : ∀ s ∈ S, mat 3 K s a a = mat 3 K s b b := by
    intro s hs
    have hcomm : Commute s g := by
      have h1 := hgS s hs
      show s * g = g * s
      calc s * g = (g * s * g⁻¹) * g := by rw [h1]
        _ = g * s := by group
    have h2 := (commute_iff_entries (fun a b hab => spTorus_apply_ne (hST hs) hab)).1 hcomm a b
    exact mul_right_cancel₀ hg0 (by rw [h2, mul_comm])
  obtain ⟨r, hr⟩ : ∃ r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3,
      (a, b) = pos1 r ∨ (a, b) = pos2 r :=
    ⟨ofPos a b, eq_pos_of_wt_sub _ a b (stdVec_ofPos hne).symm⟩
  have hσ : ∀ t ∈ spTorus p 3 K, ratio t a b = ratio t (pos1 r).1 (pos1 r).2 := by
    intro t ht
    rcases hr with h' | h'
    · have ha : a = (pos1 r).1 := congrArg Prod.fst h'
      have hb : b = (pos1 r).2 := congrArg Prod.snd h'
      rw [ha, hb]
    · have ha : a = (pos2 r).1 := congrArg Prod.fst h'
      have hb : b = (pos2 r).2 := congrArg Prod.snd h'
      rw [ha, hb]
      exact ratio_pos2 ht r hp0
  have hσS : ∀ s ∈ S, ratio s (pos1 r).1 (pos1 r).2 = 1 := by
    intro s hs
    rw [← hσ s (hST hs), ratio, hS s hs]
    exact mul_inv_cancel₀ (spTorus_ne_zero (hST hs) b hp0)
  have hσx : ratio x (pos1 r).1 (pos1 r).2 ≠ 1 := by
    rw [← hσ x hxT, ratio]
    intro h1
    exact hxab ((mul_inv_eq_one₀ (spTorus_ne_zero hxT b hp0)).1 h1)
  have hY : elt r (1 : K) ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := conj_elt (hST hs) hp0 r 1
    rw [hσS s hs, one_mul] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hSS' : S ≤ spTorus p 3 K ⊓ Subgroup.centralizer {elt r (1 : K)} := fun s hs =>
    ⟨hST hs, Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hY s hs)⟩
  have hxS' : x ∉ spTorus p 3 K ⊓ Subgroup.centralizer {elt r (1 : K)} := by
    rintro ⟨-, hx'⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hx'
    have h2 := conj_elt hxT hp0 r 1
    rw [mul_inv_eq_iff_eq_mul.2 h1, mul_one] at h2
    exact hσx (elt_injective r h2).symm
  have hS'ne : spTorus p 3 K ⊓ Subgroup.centralizer {elt r (1 : K)} ≠ spTorus p 3 K := fun h =>
    hxS' (by rw [h]; exact hxT)
  have hSeq := eq_of_le_of_relIndex_eq_prime hp hSS' inf_le_left hSidx hS'ne
  have hσc : ratio c (pos1 r).1 (pos1 r).2 ≠ 1 := by
    intro h1
    apply hcS
    rw [hSeq]
    refine ⟨hcT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h2 := conj_elt hcT hp0 r 1
    rw [h1, one_mul] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2
  refine ⟨elt r 1, hY, ?_⟩
  have hσ0 : ratio c (pos1 r).1 (pos1 r).2 ≠ 0 := by
    rw [ratio]
    exact mul_ne_zero (spTorus_ne_zero hcT _ hp0) (inv_ne_zero (spTorus_ne_zero hcT _ hp0))
  generalize hσdef : ratio c (pos1 r).1 (pos1 r).2 = σ at hσc hσ0
  have hconj : ∀ u : K, c * elt r u * c⁻¹ = elt r (σ * u) := fun u => by
    rw [conj_elt hcT hp0 r u, hσdef]
  have hc1 : c * elt r σ⁻¹ * c⁻¹ = elt r 1 := by
    rw [hconj, mul_inv_cancel₀ hσ0]
  have hc2 : c⁻¹ * elt r 1 * c = elt r σ⁻¹ := by
    rw [← hc1]
    group
  have hYc : elt r 1 * c * (elt r 1)⁻¹ = c * elt r (σ⁻¹ + -1) := by
    have e1 : elt r 1 * c * (elt r 1)⁻¹ = c * (c⁻¹ * elt r 1 * c) * (elt r 1)⁻¹ := by group
    rw [e1, hc2, elt_add, ← elt_neg r 1, mul_assoc]
  intro hcomm
  rw [hYc] at hcomm
  have hcomm' : Commute c (elt r (σ⁻¹ + -1)) := by
    have h1 := (Commute.refl c).inv_right.mul_right hcomm
    simpa using h1
  have h4 : c * elt r (σ⁻¹ + -1) * c⁻¹ = elt r (σ⁻¹ + -1) := by
    rw [hcomm'.eq]
    exact mul_inv_cancel_right _ _
  rw [hconj] at h4
  have h5 := elt_injective r h4
  have h6 : (σ - 1) * (σ⁻¹ + -1) = 0 := by linear_combination h5
  rcases mul_eq_zero.1 h6 with h7 | h7
  · exact hσc (sub_eq_zero.1 h7)
  · apply hσc
    have h8 : σ⁻¹ = 1 := by linear_combination h7
    exact inv_eq_one.1 h8

end Root

end CFSG.RankThree.PartOne.Q1327Z
