module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalRoots
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.Quasithin.H13.A6S13820AutL3a
import CFSG.RankThree.GF2n.DecompSetupSplit
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.LocalAnalysis.OddStandard.Seitz77U
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Final
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.Monster.Existence.Defs
import CFSG.Open.MonsterY443Defs
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C2A3Orbits
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.G64Case1
import CFSG.Quasithin.Background.InternalSecRealB
import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
import CFSG.Quasithin.EmptyFaithful.R3c2Types
import CFSG.Quasithin.EmptyFaithful.R3cBlocks
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
import CFSG.Quasithin.H13.A6S13820Aut3
import CFSG.Quasithin.H13.A6S13820AutT
import CFSG.Quasithin.H13.A6S13821a
import CFSG.Quasithin.H13.A6S13821b
import CFSG.Quasithin.H13.A6S13825w
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public noncomputable section

namespace CFSG.Quasithin.F112R.St84.G2q

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 (i1)

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem entrywise_dT (ρ : K ≃+* K) (s t : Kˣ) :
    Units.map (entrywiseHom ρ.toRingHom) (dT s t) =
      dT (Units.map ρ.toRingHom.toMonoidHom s) (Units.map ρ.toRingHom.toMonoidHom t) := by
  simp only [dT, map_mul, entrywise_torusElt, map_pow]


private theorem units_map_X (ρ : K ≃+* K) (γ : Fin Tag.G2.rank → ℤ) (c : K) :
    Units.map (entrywiseHom ρ.toRingHom) (X γ c) = X γ (ρ c) :=
  Units.ext (entrywise_pinnedX ρ.toRingHom γ c)

private theorem X_r_mem (c : K) : X g2r c ∈ borelGroup Tag.G2 K := by
  rw [pinnedX_r_eq_g2N]
  exact g2N_mem_borelGroup _ _ _ _ _ _

private theorem X_a_mem (c : K) : X g2a c ∈ borelGroup Tag.G2 K := by
  rw [pinnedX_a_eq_g2N]
  exact g2N_mem_borelGroup _ _ _ _ _ _

private theorem X_c_mem (c : K) : X g2c c ∈ borelGroup Tag.G2 K := by
  rw [pinnedX_c_eq_g2N]
  exact g2N_mem_borelGroup _ _ _ _ _ _

private theorem X_r_mem_unip (c : K) : X g2r c ∈ posUnipotent Tag.G2 K := by
  rw [pinnedX_r_eq_g2N]
  exact g2N_mem_posUnipotent _ _ _ _ _ _

private theorem X_a_mem_unip (c : K) : X g2a c ∈ posUnipotent Tag.G2 K := by
  rw [pinnedX_a_eq_g2N]
  exact g2N_mem_posUnipotent _ _ _ _ _ _

private theorem X_c_mem_unip (c : K) : X g2c c ∈ posUnipotent Tag.G2 K := by
  rw [pinnedX_c_eq_g2N]
  exact g2N_mem_posUnipotent _ _ _ _ _ _

private theorem X_r_injective : Function.Injective (X g2r) := fun a b e => by
  rw [pinnedX_r_eq_g2N, pinnedX_r_eq_g2N] at e
  exact (g2N_injective e).1

private theorem X_a_injective : Function.Injective (X g2a) := fun a b e => by
  rw [pinnedX_a_eq_g2N, pinnedX_a_eq_g2N] at e
  exact (g2N_injective e).2.1

private theorem dT_comm_X_r (s : Kˣ) (c : K) : dT s 1 * X g2r c = X g2r c * dT s 1 := by
  have e := dT_conj_r s 1 c
  rw [Units.val_one, one_mul] at e
  exact mul_inv_eq_iff_eq_mul.1 e

private theorem dT_comm_X_a (t : Kˣ) (c : K) : dT 1 t * X g2a c = X g2a c * dT 1 t := by
  have e := dT_conj_a 1 t c
  rw [Units.val_one, one_mul] at e
  exact mul_inv_eq_iff_eq_mul.1 e

private theorem dT_conj_dT (s t s' t' : Kˣ) : dT s t * dT s' t' * (dT s t)⁻¹ = dT s' t' := by
  rw [dT_mul, mul_comm s, mul_comm t, ← dT_mul, mul_inv_cancel_right]

private theorem X_c_comm_X_r [CharP K 2] (c : K) :
    X g2c 1 * X g2r c = X g2r c * X g2c 1 := by
  rw [pinnedX_r_eq_g2N]
  exact (g2N_commute_X_c c 0 0 0 0 0 1).symm.eq

private theorem X_c_comm_X_a [CharP K 2] (c : K) :
    X g2c 1 * X g2a c = X g2a c * X g2c 1 := by
  rw [pinnedX_a_eq_g2N]
  exact (g2N_commute_X_c 0 c 0 0 0 0 1).symm.eq

private theorem exists_ringEquiv_of_unit_mul {l : K ≃+ K} {θ : Kˣ → K}
    (hθ : ∀ (t : Kˣ) (c : K), θ t * l c = l ((t : K) * c)) :
    ∃ ρ : K ≃+* K, ∀ x, l x = l 1 * ρ x := by
  have hl1 : l 1 ≠ 0 := fun e => one_ne_zero (l.injective (by rw [e, map_zero]))
  obtain ⟨ρ, hρ, -, -⟩ := exists_ringEquiv_of_map_mul l.toAddMonoidHom
    (AddMonoidHom.mk' (fun y => l y * (l 1)⁻¹) fun a b => by rw [map_add, add_mul])
    l.toAddMonoidHom l.bijective fun y t => by
      show l (y * t) = l y * (l 1)⁻¹ * l t
      by_cases hy : y = 0
      · rw [hy, zero_mul, map_zero, zero_mul, zero_mul]
      · have e1 := hθ (Units.mk0 y hy) t
        have e2 := hθ (Units.mk0 y hy) 1
        rw [Units.val_mk0] at e1 e2
        rw [mul_one] at e2
        rw [← e1, ← e2, mul_inv_cancel_right₀ hl1]
  exact ⟨ρ, hρ⟩

private structure Hyp {Γ : Type*} [Group Γ] (ι : Γ →* ModGL Tag.G2 K) (τ : MulAut Γ) : Prop where
  inj : Function.Injective ι
  range : ∀ g, g ∈ borelGroup Tag.G2 K ↔ ∃ b, ι b = g
  unip : ∀ b, ι b ∈ posUnipotent Tag.G2 K ↔ ι (τ b) ∈ posUnipotent Tag.G2 K
  torus : ∀ b, ι b ∈ torusGroup Tag.G2 K ↔ ι (τ b) ∈ torusGroup Tag.G2 K
  rad : ∀ b, ι b ∈ parabolicRadical Tag.G2 K {i1} ↔ ι (τ b) ∈ parabolicRadical Tag.G2 K {i1}

namespace Hyp

variable {Γ : Type*} [Group Γ] {ι : Γ →* ModGL Tag.G2 K} {τ : MulAut Γ}

private theorem symm (h : Hyp ι τ) : Hyp ι τ⁻¹ where
  inj := h.inj
  range := h.range
  unip b := by
    have e := h.unip (τ⁻¹ b)
    rw [MulAut.apply_inv_self] at e
    exact e.symm
  torus b := by
    have e := h.torus (τ⁻¹ b)
    rw [MulAut.apply_inv_self] at e
    exact e.symm
  rad b := by
    have e := h.rad (τ⁻¹ b)
    rw [MulAut.apply_inv_self] at e
    exact e.symm

private theorem mem_borel (h : Hyp ι τ) (b : Γ) : ι b ∈ borelGroup Tag.G2 K :=
  (h.range _).2 ⟨b, rfl⟩

open Classical in
private def tr (h : Hyp ι τ) (g : ModGL Tag.G2 K) : ModGL Tag.G2 K :=
  if hg : g ∈ borelGroup Tag.G2 K then ι (τ ((h.range g).1 hg).choose) else 1

private theorem tr_iota (h : Hyp ι τ) (b : Γ) : h.tr (ι b) = ι (τ b) := by
  have hb := h.mem_borel b
  unfold tr
  rw [dif_pos hb, h.inj ((h.range (ι b)).1 hb).choose_spec]

private theorem tr_one (h : Hyp ι τ) : h.tr 1 = 1 := by
  rw [← map_one ι, h.tr_iota, map_one, map_one]

private theorem tr_mul (h : Hyp ι τ) {g g' : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K)
    (hg' : g' ∈ borelGroup Tag.G2 K) : h.tr (g * g') = h.tr g * h.tr g' := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  obtain ⟨b', rfl⟩ := (h.range g').1 hg'
  rw [← map_mul, h.tr_iota, h.tr_iota, h.tr_iota, map_mul, map_mul]

private theorem tr_inv (h : Hyp ι τ) {g : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K) :
    h.tr g⁻¹ = (h.tr g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← h.tr_mul (inv_mem hg) hg, inv_mul_cancel, h.tr_one]

private theorem tr_inj (h : Hyp ι τ) {g g' : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K)
    (hg' : g' ∈ borelGroup Tag.G2 K) (he : h.tr g = h.tr g') : g = g' := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  obtain ⟨b', rfl⟩ := (h.range g').1 hg'
  rw [h.tr_iota, h.tr_iota] at he
  rw [τ.injective (h.inj he)]

private theorem tr_unip (h : Hyp ι τ) {g : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K) :
    g ∈ posUnipotent Tag.G2 K ↔ h.tr g ∈ posUnipotent Tag.G2 K := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  rw [h.tr_iota]
  exact h.unip b

private theorem tr_torus (h : Hyp ι τ) {g : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K) :
    g ∈ torusGroup Tag.G2 K ↔ h.tr g ∈ torusGroup Tag.G2 K := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  rw [h.tr_iota]
  exact h.torus b

private theorem tr_rad (h : Hyp ι τ) {g : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K) :
    g ∈ parabolicRadical Tag.G2 K {i1} ↔ h.tr g ∈ parabolicRadical Tag.G2 K {i1} := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  rw [h.tr_iota]
  exact h.rad b

private theorem tr_comm (h : Hyp ι τ) {g g' : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K)
    (hg' : g' ∈ borelGroup Tag.G2 K) (hc : g * g' = g' * g) :
    h.tr g * h.tr g' = h.tr g' * h.tr g := by
  rw [← h.tr_mul hg hg', ← h.tr_mul hg' hg, hc]

private theorem tr_conj (h : Hyp ι τ) {g g' : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K)
    (hg' : g' ∈ borelGroup Tag.G2 K) :
    h.tr (g * g' * g⁻¹) = h.tr g * h.tr g' * (h.tr g)⁻¹ := by
  rw [h.tr_mul (mul_mem hg hg') (inv_mem hg), h.tr_mul hg hg', h.tr_inv hg]

private theorem symm_tr_tr (h : Hyp ι τ) {g : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K) :
    h.symm.tr (h.tr g) = g := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  rw [h.tr_iota, h.symm.tr_iota, MulAut.inv_apply_self]

private theorem tr_symm_tr (h : Hyp ι τ) {g : ModGL Tag.G2 K} (hg : g ∈ borelGroup Tag.G2 K) :
    h.tr (h.symm.tr g) = g := by
  obtain ⟨b, rfl⟩ := (h.range g).1 hg
  rw [h.symm.tr_iota, h.tr_iota, MulAut.apply_inv_self]

private theorem tr_dT_mem (h : Hyp ι τ) (s t : Kˣ) : ∃ s' t' : Kˣ, h.tr (dT s t) = dT s' t' := by
  obtain ⟨s', t', e⟩ := mem_torusGroup_iff.1
    ((h.tr_torus (dT_mem_borelGroup s t)).1 (dT_mem_torusGroup s t))
  exact ⟨s', t', e.symm⟩

private theorem exists_addEquiv_of_tr [Finite K] (h : Hyp ι τ) {α : Fin Tag.G2.rank → ℤ}
    (hmem : ∀ c, X α c ∈ borelGroup Tag.G2 K) (hinj : Function.Injective (X α))
    (hex : ∀ c, ∃ a, h.tr (X α c) = X α a) : ∃ l : K ≃+ K, ∀ c, h.tr (X α c) = X α (l c) := by
  choose L hL using hex
  have hadd : ∀ a b, L (a + b) = L a + L b := fun a b => hinj (by
    rw [← hL, pinnedX_add, h.tr_mul (hmem a) (hmem b), hL, hL, pinnedX_add])
  have hLinj : Function.Injective L := fun a b e =>
    hinj (h.tr_inj (hmem a) (hmem b) (by rw [hL, hL, e]))
  exact ⟨AddEquiv.ofBijective (AddMonoidHom.mk' L hadd)
    ⟨hLinj, Finite.injective_iff_surjective.1 hLinj⟩, hL⟩

private theorem tr_X_r_eq [CharP K 2] (h : Hyp ι τ) {w : Kˣ}
    (hw1 : w ≠ 1) (c : K) : ∃ a, h.tr (X g2r c) = X g2r a := by
  obtain ⟨s', t', hst⟩ := h.tr_dT_mem w 1
  obtain ⟨A, B, C, D, E, F, hN⟩ := exists_g2N_of_mem_posUnipotent
    ((h.tr_unip (X_r_mem 1)).1 (X_r_mem_unip 1))
  have hA : A ≠ 0 := by
    intro hA0
    have hq : h.tr (X g2r 1) ∈ parabolicRadical Tag.G2 K {i1} := by
      rw [← hN]
      exact g2N_mem_parabolicRadical_one_iff.2 hA0
    have := (h.tr_rad (X_r_mem 1)).2 hq
    rw [pinnedX_r_eq_g2N, g2N_mem_parabolicRadical_one_iff] at this
    exact one_ne_zero this
  have hcomm : dT s' t' * g2N A B C D E F = g2N A B C D E F * dT s' t' := by
    rw [← hst, hN]
    exact h.tr_comm (dT_mem_borelGroup w 1) (X_r_mem 1) (dT_comm_X_r w 1)
  have ht' : t' = 1 := eq_one_of_commute_dT_of_ne_zero_left hA hcomm
  subst ht'
  have hs' : s' ≠ 1 := by
    rintro rfl
    apply hw1
    have e : h.tr (dT w 1) = h.tr 1 := by rw [hst, dT_one, h.tr_one]
    exact (dT_eq_one_iff.1 (h.tr_inj (dT_mem_borelGroup w 1) (one_mem _) e)).1
  obtain ⟨A', B', C', D', E', F', hN'⟩ := exists_g2N_of_mem_posUnipotent
    ((h.tr_unip (X_r_mem c)).1 (X_r_mem_unip c))
  refine ⟨A', ?_⟩
  rw [← hN']
  refine g2N_eq_of_commute_dT_left hs' ?_
  rw [← hst, hN']
  exact h.tr_comm (dT_mem_borelGroup w 1) (X_r_mem c) (dT_comm_X_r w c)

private theorem torus_X_r (h : Hyp ι τ) {l : K ≃+ K} (hl : ∀ c, h.tr (X g2r c) = X g2r (l c))
    {s t s' t' : Kˣ} (he : h.tr (dT s t) = dT s' t') (c : K) :
    (t' : K) * l c = l ((t : K) * c) := by
  have e := h.tr_conj (dT_mem_borelGroup s t) (X_r_mem c)
  rw [dT_conj_r, hl, he, hl, dT_conj_r] at e
  exact (X_r_injective e).symm

private theorem torus_X_a (h : Hyp ι τ) {m : K ≃+ K} (hm : ∀ c, h.tr (X g2a c) = X g2a (m c))
    {s t s' t' : Kˣ} (he : h.tr (dT s t) = dT s' t') (c : K) :
    (s' : K) * m c = m ((s : K) * c) := by
  have e := h.tr_conj (dT_mem_borelGroup s t) (X_a_mem c)
  rw [dT_conj_a, hm, he, hm, dT_conj_a] at e
  exact (X_a_injective e).symm

private theorem tr_bc [CharP K 2] (h : Hyp ι τ) {l : K ≃+ K}
    (hl : ∀ c, h.tr (X g2r c) = X g2r (l c)) (E F : K) :
    ∃ E' F', h.tr (g2N 0 0 0 0 E F) = g2N 0 0 0 0 E' F' := by
  have hmem := g2N_mem_borelGroup (0 : K) 0 0 0 E F
  obtain ⟨A', B', C', D', E', F', hN⟩ := exists_g2N_of_mem_posUnipotent
    ((h.tr_unip hmem).1 (g2N_mem_posUnipotent _ _ _ _ _ _))
  have hA : A' = 0 := by
    have := (h.tr_rad hmem).1 (g2N_mem_parabolicRadical_one_iff.2 rfl)
    rwa [← hN, g2N_mem_parabolicRadical_one_iff] at this
  have hc : ∀ c, Commute (g2N A' B' C' D' E' F') (X g2r c) := fun c => by
    obtain ⟨c', rfl⟩ := l.surjective c
    rw [hN, ← hl]
    exact h.tr_comm hmem (X_r_mem c') (g2N_commute_X_r_iff.2 ⟨rfl, rfl, rfl⟩ c')
  obtain ⟨hB, hC, hD⟩ := g2N_commute_X_r_iff.1 hc
  exact ⟨E', F', by rw [← hN, hA, hB, hC, hD]⟩

private theorem symm_tr_X_r (h : Hyp ι τ) {l : K ≃+ K} (hl : ∀ c, h.tr (X g2r c) = X g2r (l c))
    (c : K) : h.symm.tr (X g2r c) = X g2r (l.symm c) := by
  conv_lhs => rw [← l.apply_symm_apply c, ← hl]
  exact h.symm_tr_tr (X_r_mem _)

private theorem tr_B_eq_zero [CharP K 2] (h : Hyp ι τ)
    {l : K ≃+ K} (hl : ∀ c, h.tr (X g2r c) = X g2r (l c)) {A B C D E F A' B' C' D' E' F' : K}
    (hN : h.tr (g2N A B C D E F) = g2N A' B' C' D' E' F') (hB : B = 0) : B' = 0 := by
  refine (g2N_commute_bc_iff (A := A') (C := C') (D := D') (E := E') (F := F')).1
    fun e f => ?_
  obtain ⟨e', f', he⟩ := h.symm.tr_bc (h.symm_tr_X_r hl) e f
  have hmem := g2N_mem_borelGroup (0 : K) 0 0 0 e' f'
  have hef : g2N (0 : K) 0 0 0 e f = h.tr (g2N 0 0 0 0 e' f') := by
    rw [← he, h.tr_symm_tr (g2N_mem_borelGroup _ _ _ _ _ _)]
  rw [hef, ← hN]
  exact h.tr_comm (g2N_mem_borelGroup _ _ _ _ _ _) hmem (g2N_commute_bc_iff.2 hB e' f')

private theorem tr_B_eq_zero_iff [CharP K 2] (h : Hyp ι τ)
    {l : K ≃+ K} (hl : ∀ c, h.tr (X g2r c) = X g2r (l c)) {A B C D E F A' B' C' D' E' F' : K}
    (hN : h.tr (g2N A B C D E F) = g2N A' B' C' D' E' F') : B = 0 ↔ B' = 0 := by
  have hN' : h.symm.tr (g2N A' B' C' D' E' F') = g2N A B C D E F := by
    rw [← hN, h.symm_tr_tr (g2N_mem_borelGroup _ _ _ _ _ _)]
  exact ⟨h.tr_B_eq_zero hl hN, h.symm.tr_B_eq_zero (h.symm_tr_X_r hl) hN'⟩

private theorem tr_X_a_eq [CharP K 2] (h : Hyp ι τ) {l : K ≃+ K}
    (hl : ∀ c, h.tr (X g2r c) = X g2r (l c)) {w s' t' : Kˣ} (hst : h.tr (dT 1 w) = dT s' t')
    (ht3 : (t' : K) ^ 3 ≠ 1) (c : K) : ∃ b, h.tr (X g2a c) = X g2a b := by
  obtain ⟨A, B, C, D, E, F, hN⟩ := exists_g2N_of_mem_posUnipotent
    ((h.tr_unip (X_a_mem 1)).1 (X_a_mem_unip 1))
  have hN1 : h.tr (g2N 0 1 0 0 0 0) = g2N A B C D E F := by
    rw [← pinnedX_a_eq_g2N]
    exact hN.symm
  have hB : B ≠ 0 := fun hB0 => one_ne_zero ((h.tr_B_eq_zero_iff hl hN1).2 hB0)
  have hcomm : dT s' t' * g2N A B C D E F = g2N A B C D E F * dT s' t' := by
    rw [← hst, hN]
    exact h.tr_comm (dT_mem_borelGroup 1 w) (X_a_mem 1) (dT_comm_X_a w 1)
  have hs' : s' = 1 := eq_one_of_commute_dT_of_ne_zero_right hB hcomm
  subst hs'
  obtain ⟨A', B', C', D', E', F', hN'⟩ := exists_g2N_of_mem_posUnipotent
    ((h.tr_unip (X_a_mem c)).1 (X_a_mem_unip c))
  refine ⟨B', ?_⟩
  rw [← hN']
  refine g2N_eq_of_commute_dT_right ht3 ?_
  rw [← hst, hN']
  exact h.tr_comm (dT_mem_borelGroup 1 w) (X_a_mem c) (dT_comm_X_a w c)

private theorem eq_of_agree [CharP K 2] (h : Hyp ι τ) {s₀ : K}
    (h0 : s₀ ≠ 0) (h1 : s₀ ≠ 1) (ρ : K ≃+* K) (d : ModGL Tag.G2 K)
    (hr : ∀ c, h.tr (X g2r c) = d * Units.map (entrywiseHom ρ.toRingHom) (X g2r c) * d⁻¹)
    (ha : ∀ c, h.tr (X g2a c) = d * Units.map (entrywiseHom ρ.toRingHom) (X g2a c) * d⁻¹)
    (ht : ∀ s t, h.tr (dT s t) = d * Units.map (entrywiseHom ρ.toRingHom) (dT s t) * d⁻¹)
    (b : Γ) : ι (τ b) = d * Units.map (entrywiseHom ρ.toRingHom) (ι b) * d⁻¹ := by
  let F₁ : Γ →* ModGL Tag.G2 K := ι.comp τ.toMonoidHom
  let F₂ : Γ →* ModGL Tag.G2 K :=
    (MulAut.conj d).toMonoidHom.comp ((Units.map (entrywiseHom ρ.toRingHom)).comp ι)
  let S : Subgroup (ModGL Tag.G2 K) := (F₁.eqLocus F₂).map ι
  have hS : ∀ g, g ∈ borelGroup Tag.G2 K →
      h.tr g = d * Units.map (entrywiseHom ρ.toRingHom) g * d⁻¹ → g ∈ S := by
    intro g hg he
    obtain ⟨b, rfl⟩ := (h.range g).1 hg
    refine ⟨b, ?_, rfl⟩
    show ι (τ b) = d * Units.map (entrywiseHom ρ.toRingHom) (ι b) * d⁻¹
    rw [← h.tr_iota, he]
  have hN : ∀ A B C D E F : K, g2N A B C D E F ∈ S :=
    g2N_mem_of_forall_mem h0 h1 (fun c => hS _ (X_r_mem c) (hr c))
      (fun c => hS _ (X_a_mem c) (ha c))
  have hb : ι b ∈ S := by
    obtain ⟨s, t, A, B, C, D, E, F, he⟩ := mem_borelGroup_iff.1 (h.mem_borel b)
    rw [he]
    exact mul_mem (hS _ (dT_mem_borelGroup s t) (ht s t)) (hN A B C D E F)
  obtain ⟨b', hb', he⟩ := hb
  rw [← h.inj he]
  exact hb'

end Hyp

theorem exists_eq_conj_entrywise_of_mulAut [Finite K] [CharP K 2]
    {Γ : Type*} [Group Γ] (ι : Γ →* ModGL Tag.G2 K) (hι : Function.Injective ι)
    (hrange : ∀ g, g ∈ borelGroup Tag.G2 K ↔ ∃ b, ι b = g) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f) (τ : MulAut Γ)
    (hU : ∀ b, ι b ∈ posUnipotent Tag.G2 K ↔ ι (τ b) ∈ posUnipotent Tag.G2 K)
    (hT : ∀ b, ι b ∈ torusGroup Tag.G2 K ↔ ι (τ b) ∈ torusGroup Tag.G2 K)
    (hQ : ∀ b, ι b ∈ parabolicRadical Tag.G2 K {i1} ↔
      ι (τ b) ∈ parabolicRadical Tag.G2 K {i1}) :
    ∃ (ρ : K ≃+* K) (s t : Kˣ), ∀ b,
      ι (τ b) = dT s t * Units.map (entrywiseHom ρ.toRingHom) (ι b) * (dT s t)⁻¹ := by
  have h : Hyp ι τ := ⟨hι, hrange, hU, hT, hQ⟩
  have hK4 : 4 < Nat.card K := by
    rw [hK]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨w, hw⟩ := CFSG.RankThree.GF2n.exists_units_pow_three_ne_one hK4
  have hw3 : (w : K) ^ 3 ≠ 1 := fun e =>
    hw (Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one]))
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hw (one_pow 3)
  have hw1' : (w : K) ≠ 1 := fun e => hw1 (Units.val_eq_one.1 e)
  obtain ⟨l, hl⟩ := h.exists_addEquiv_of_tr X_r_mem X_r_injective (h.tr_X_r_eq hw1)
  have hl1 : l 1 ≠ 0 := fun e => one_ne_zero (l.injective (by rw [e, map_zero]))
  choose S T hST using h.tr_dT_mem
  obtain ⟨ρr, hlρ⟩ := exists_ringEquiv_of_unit_mul (l := l) (θ := fun t => (T 1 t : K))
    fun t c => h.torus_X_r hl (hST 1 t) c
  have hT' : ∀ s t, (T s t : K) = ρr t := fun s t => by
    have e := h.torus_X_r hl (hST s t) 1
    rw [mul_one, hlρ (t : K)] at e
    exact mul_right_cancel₀ hl1 (by rw [e, mul_comm])
  have ht3 : (T 1 w : K) ^ 3 ≠ 1 := by
    rw [hT']
    exact fun e => hw3 (ρr.injective (by rw [map_pow, e, map_one]))
  obtain ⟨m, hm⟩ := h.exists_addEquiv_of_tr X_a_mem X_a_injective
    (h.tr_X_a_eq hl (hST 1 w) ht3)
  have hm1 : m 1 ≠ 0 := fun e => one_ne_zero (m.injective (by rw [e, map_zero]))
  obtain ⟨ρa, hmρ⟩ := exists_ringEquiv_of_unit_mul (l := m) (θ := fun s => (S s 1 : K))
    fun s c => h.torus_X_a hm (hST s 1) c
  have hS' : ∀ s t, (S s t : K) = ρa s := fun s t => by
    have e := h.torus_X_a hm (hST s t) 1
    rw [mul_one, hmρ (s : K)] at e
    exact mul_right_cancel₀ hm1 (by rw [e, mul_comm])
  obtain ⟨A, B, C, D, E, F, hN⟩ := exists_g2N_of_mem_posUnipotent
    ((h.tr_unip (X_c_mem 1)).1 (X_c_mem_unip 1))
  have hcr : ∀ c, Commute (g2N A B C D E F) (X g2r c) := fun c => by
    obtain ⟨c', rfl⟩ := l.surjective c
    rw [hN, ← hl]
    exact h.tr_comm (X_c_mem 1) (X_r_mem c') (X_c_comm_X_r c')
  have hca : ∀ c, Commute (g2N A B C D E F) (X g2a c) := fun c => by
    obtain ⟨c', rfl⟩ := m.surjective c
    rw [hN, ← hm]
    exact h.tr_comm (X_c_mem 1) (X_a_mem c') (X_c_comm_X_a c')
  obtain ⟨rfl, rfl, rfl⟩ := g2N_commute_X_r_iff.1 hcr
  obtain ⟨rfl, rfl⟩ := g2N_commute_X_a_iff.1 hca
  have hF : F ≠ 0 := by
    rintro rfl
    rw [g2N_zero] at hN
    have e := h.tr_inj (X_c_mem 1) (one_mem _) (by rw [← hN, h.tr_one])
    rw [pinnedX_c_eq_g2N, ← g2N_zero] at e
    exact one_ne_zero (g2N_injective e).2.2.2.2.2
  have key : ∀ u : Kˣ, ρa (u : K) ^ 3 = ρr (u : K) ^ 3 := fun u => by
    have hst1 : ((u ^ 3 : Kˣ) : K) ^ 2 * ((u⁻¹ ^ 2 : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        show (u ^ 3) ^ 2 * (u⁻¹ ^ 2) ^ 3 = 1 by group, Units.val_one]
    have hc : dT (u ^ 3) (u⁻¹ ^ 2) * X g2c 1 = X g2c 1 * dT (u ^ 3) (u⁻¹ ^ 2) := by
      have e := dT_conj_c (u ^ 3) (u⁻¹ ^ 2) 1
      rw [hst1, one_mul] at e
      exact mul_inv_eq_iff_eq_mul.1 e
    have hcomm : dT (S (u ^ 3) (u⁻¹ ^ 2)) (T (u ^ 3) (u⁻¹ ^ 2)) * g2N 0 0 0 0 0 F =
        g2N 0 0 0 0 0 F * dT (S (u ^ 3) (u⁻¹ ^ 2)) (T (u ^ 3) (u⁻¹ ^ 2)) := by
      rw [← hST, hN]
      exact h.tr_comm (dT_mem_borelGroup _ _) (X_c_mem 1) hc
    have e6 := eq_one_of_commute_dT_of_ne_zero_top hF hcomm
    rw [hS', hT', Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      map_pow, map_pow, map_inv₀, inv_pow, inv_pow,
      mul_inv_eq_one₀ (pow_ne_zero _ (pow_ne_zero _ ((map_ne_zero ρr).2 u.ne_zero)))] at e6
    have e6' : (ρa (u : K) ^ 3) ^ 2 = (ρr (u : K) ^ 3) ^ 2 := by
      rw [e6]
      ring
    have hsq : (ρa (u : K) ^ 3 - ρr (u : K) ^ 3) ^ 2 = 0 := by
      linear_combination e6' + (ρr (u : K) ^ 6 - ρa (u : K) ^ 3 * ρr (u : K) ^ 3) *
        two_eq_zero_K (K := K)
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
  have hκ : ρa.trans ρr.symm = 1 := by
    rcases CFSG.Quasithin.H13.A6.Aut20.sigma_eq_one_of_fix_cubes20 (n := f) (by omega) hK
      (ρa.trans ρr.symm) (fun u => by
        rw [RingEquiv.trans_apply, map_pow, key u, ← map_pow ρr,
          RingEquiv.symm_apply_apply]) with h1 | h2
    · exact h1
    · omega
  have hρ : ∀ x, ρa x = ρr x := fun x => by
    have e : ρr.symm (ρa x) = x := DFunLike.congr_fun hκ x
    calc ρa x = ρr (ρr.symm (ρa x)) := (ρr.apply_symm_apply _).symm
      _ = ρr x := by rw [e]
  refine ⟨ρr, Units.mk0 (m 1) hm1, Units.mk0 (l 1) hl1,
    h.eq_of_agree w.ne_zero hw1' ρr _ ?_ ?_ ?_⟩
  · intro c
    rw [hl, units_map_X, dT_conj_r, Units.val_mk0, hlρ c]
  · intro c
    rw [hm, units_map_X, dT_conj_a, Units.val_mk0, hmρ c, hρ c]
  · intro s t
    rw [hST, entrywise_dT, dT_conj_dT]
    exact congrArg₂ dT (Units.ext (by rw [hS', hρ, Units.coe_map]; rfl))
      (Units.ext (by rw [hT', Units.coe_map]; rfl))

end CFSG.Quasithin.F112R.St84.G2q

end
