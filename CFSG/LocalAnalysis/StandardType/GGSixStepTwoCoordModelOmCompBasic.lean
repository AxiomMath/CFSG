module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOm
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmMain
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmExcl
public import CFSG.RankThree.PartOne.S11d.OrthCyclic
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)

local notation "bComp" => CFSG.RankThree.PartOne.KCOrthogonal.blockComponent
local notation "bCompApply" => CFSG.RankThree.PartOne.KCOrthogonal.blockComponent_apply_of_mem

section Basic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem mem_orthDerived_of_pow [Finite K] [CharP K 2] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgp : g ^ p = 1) : g ∈ orthDerived Q :=
  CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    (CFSG.RankThree.PartOne.mem_omegaGroup_of_pow_eq_one hQ (hp.odd_of_ne_two hp2) hg hgp)

variable {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem frame_triv_or_fpf (F : SevOm.Frame Q p A r) {y : V ≃ₗ[K] V} (hy : y ∈ A) (j : Fin r) :
    (∀ u ∈ F.U j, y u = u) ∨ ∀ u ∈ F.U j, y u = u → u = 0 := by
  obtain ⟨s, rfl⟩ := F.exists_eq hy
  by_cases hs : toAdd s j = 0
  · exact Or.inl (F.triv s j hs)
  · exact Or.inr (F.fpf s j hs)

theorem frame_apply_mem (F : SevOm.Frame Q p A r) {y : V ≃ₗ[K] V} (hy : y ∈ A) (j : Fin r)
    {u : V} (hu : u ∈ F.U j) : y u ∈ F.U j := by
  obtain ⟨s, rfl⟩ := F.exists_eq hy
  exact F.mapsTo s j u hu

theorem frame_comm (F : SevOm.Frame Q p A r) {y z : V ≃ₗ[K] V} (hy : y ∈ A) (hz : z ∈ A) :
    y * z = z * y := by
  obtain ⟨s, rfl⟩ := F.exists_eq hy
  obtain ⟨t, rfl⟩ := F.exists_eq hz
  rw [← map_mul, ← map_mul, mul_comm]

theorem frame_single_fpf (F : SevOm.Frame Q p A r) [Fact p.Prime] (j : Fin r) {u : V}
    (hu : u ∈ F.U j) (hfix : F.ι (ofAdd (Pi.single j 1)) u = u) : u = 0 := by
  classical
  refine F.fpf _ j ?_ u hu hfix
  rw [toAdd_ofAdd, Pi.single_eq_same]
  exact one_ne_zero

theorem le_of_fpf [FiniteDimensional K V] {y : V ≃ₗ[K] V} {U W : Submodule K V}
    (hyU : ∀ u ∈ U, y u ∈ U) (hfpf : ∀ u ∈ U, y u = u → u = 0) (hW : ∀ v, y v - v ∈ W) :
    U ≤ W := by
  set T : U →ₗ[K] U := (y.toLinearMap - LinearMap.id).restrict
    (fun u hu => by
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      exact sub_mem (hyU u hu) hu) with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : y (u : V) - u = 0 := congrArg Subtype.val hu
    exact Subtype.ext (hfpf u u.2 (sub_eq_zero.mp h1))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro u hu
  obtain ⟨u', hu'⟩ := hsurj ⟨u, hu⟩
  have h1 : y (u' : V) - u' = u := congrArg Subtype.val hu'
  rw [← h1]
  exact hW u'

end Basic

section Factors

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem othersSpace_apply_mem {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {h : K[X]} {v : V}
    (hv : v ∈ othersSpace x.toLinearMap h) : g v ∈ othersSpace x.toLinearMap h := by
  unfold othersSpace at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ ⨆ (k : K[X])
      (_ : k ∈ primaryFactors x.toLinearMap ∧ k ≠ h ∧ k ≠ reciprocalPolynomial h),
      primaryComponent x.toLinearMap k) hv (fun k v hv => ?_) (by simp)
    (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ ⨆ (k : K[X])
      (_ : k ∈ primaryFactors x.toLinearMap ∧ k ≠ h ∧ k ≠ reciprocalPolynomial h),
      primaryComponent x.toLinearMap k) hv (fun hk v hv => ?_) (by simp)
    (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
  exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk
    (apply_mem_primaryComponent_of_mem_centralizer hg hv))

theorem sub_mem_orbitSpace (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x h)
    (v : V) : g v - v ∈ orbitSpace x.toLinearMap h := by
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  have hgw : g w = w := (mem_supportedBlock.mp hg).2 w hw
  have hgu : g u ∈ orbitSpace x.toLinearMap h :=
    mem_orbitSpace_of_apply (Subgroup.mem_inf.mp (mem_supportedBlock.mp hg).1).2 hu
  rw [map_add, hgw, add_sub_add_right_eq_sub]
  exact sub_mem hgu hu

theorem sub_mem_othersSpace (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {y : V ≃ₗ[K] V}
    (hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hy : ∀ u ∈ orbitSpace x.toLinearMap h, y u = u) (v : V) :
    y v - v ∈ othersSpace x.toLinearMap h := by
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  rw [map_add, hy u hu, add_sub_add_left_eq_sub]
  exact sub_mem (othersSpace_apply_mem hyc hw) hw

theorem commute_of_triv (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {g y : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x h)
    (hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hy : ∀ u ∈ orbitSpace x.toLinearMap h, y u = u) : g * y = y * g := by
  have hgc := (Subgroup.mem_inf.mp (mem_supportedBlock.mp hg).1).2
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hy u hu, (mem_supportedBlock.mp hg).2 w hw, hy (g u) (mem_orbitSpace_of_apply hgc hu),
    (mem_supportedBlock.mp hg).2 (y w) (othersSpace_apply_mem hyc hw)]

end Factors

section Block

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

open scoped Classical in
theorem blockComponent_pow_apply {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (g : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))) (h : K[X]) (n : ℕ) {a : K[X]}
    (ha : a ∈ primaryFactors x.toLinearMap) {v : V} (hv : v ∈ primaryComponent x.toLinearMap a) :
    ((bComp hx g h).1 ^ n) v =
      if a = h ∨ a = reciprocalPolynomial h then (g.1 ^ n) v else v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : ((bComp hx g h).1 ^ n) v ∈ primaryComponent x.toLinearMap a := by
      rw [ih]
      split_ifs
      · exact apply_mem_primaryComponent_of_mem_centralizer (Subgroup.pow_mem _ g.2 n) hv
      · exact hv
    rw [pow_succ', LinearEquiv.mul_apply, bCompApply hx g h ha hmem, ih]
    split_ifs
    · rw [pow_succ', LinearEquiv.mul_apply]
    · rfl

variable [Finite K] [CharP K 2]

theorem blockComponent_mem_A (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (F : SevOm.Frame Q p A r) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hxA : x ∈ A) {y : V ≃ₗ[K] V} (hyA : y ∈ A)
    (hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) (h : K[X])
    (hh : h ∈ primaryFactors x.toLinearMap) : (bComp hx ⟨y, hyc⟩ h).1 ∈ A := by
  classical
  set c := (bComp hx ⟨y, hyc⟩ h).1 with hc
  have hcB : c ∈ supportedBlock Q x h := hx.blockComponent_mem
    (Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ hyA), hyc⟩) hh
  have hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp (mem_supportedBlock.mp hcB).1).1
  have hyp : y ^ p = 1 := by
    obtain ⟨s, rfl⟩ := F.exists_eq hyA
    exact F.pow_p s
  have hcp : c ^ p = 1 := by
    apply LinearEquiv.toLinearMap_injective
    refine ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_
    show (c ^ p) v = (1 : V ≃ₗ[K] V) v
    rw [hc, blockComponent_pow_apply hx ⟨y, hyc⟩ h p ha hv]
    split_ifs
    · show (y ^ p) v = (1 : V ≃ₗ[K] V) v
      rw [hyp]
    · rfl
  have hcΩ : c ∈ orthDerived Q := mem_orthDerived_of_pow hQ hT hp hp2 hcO hcp
  refine hmax c hcΩ hcp fun z hz => ?_
  have hzc : z ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F hz hxA)
  apply LinearEquiv.toLinearMap_injective
  refine ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_
  show c (z v) = z (c v)
  have hzv : z v ∈ primaryComponent x.toLinearMap a :=
    apply_mem_primaryComponent_of_mem_centralizer hzc hv
  rw [hc, bCompApply hx ⟨y, hyc⟩ h ha hzv,
    bCompApply hx ⟨y, hyc⟩ h ha hv]
  split_ifs
  · show y (z v) = z (y v)
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, frame_comm F hyA hz]
  · rfl

theorem frame_piece_dichotomy (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (F : SevOm.Frame Q p A r) (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (s₀ : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s₀).toLinearMap) (j : Fin r) :
    F.U j ≤ orbitSpace (F.ι s₀).toLinearMap h ∨ F.U j ≤ othersSpace (F.ι s₀).toLinearMap h := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set x := F.ι s₀ with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ s₀
  have hxA : x ∈ A := F.mem s₀
  set y := F.ι (ofAdd (Pi.single j (1 : ZMod p))) with hydef
  have hyA : y ∈ A := F.mem _
  have hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F hyA hxA)
  set c := (bComp hx ⟨y, hyc⟩ h).1 with hc
  have hcA : c ∈ A := blockComponent_mem_A hQ hT hp hp2 F hAΩ hmax hx hxA hyA hyc h hh
  have hcB : c ∈ supportedBlock Q x h := hx.blockComponent_mem
    (Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup (hAΩ hyA), hyc⟩) hh
  have hcc : c ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp (mem_supportedBlock.mp hcB).1).2
  rcases frame_triv_or_fpf F hcA j with htriv | hfpf
  ·
    right
    have hcy : ∀ u ∈ orbitSpace x.toLinearMap h, c u = y u := by
      intro u hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
      have hh' := hx.reciprocalPolynomial_mem hh
      rw [map_add, map_add, hc, bCompApply hx ⟨y, hyc⟩ h hh hu₁,
        bCompApply hx ⟨y, hyc⟩ h hh' hu₂]
      simp only [true_or, or_true, ite_true]
    have hy'A : y * c⁻¹ ∈ A := A.mul_mem hyA (A.inv_mem hcA)
    have hy'c : y * c⁻¹ ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      Subgroup.mul_mem _ hyc (Subgroup.inv_mem _ hcc)
    have hy'orb : ∀ u ∈ orbitSpace x.toLinearMap h, (y * c⁻¹) u = u := by
      intro u hu
      have hu' : c⁻¹ u ∈ orbitSpace x.toLinearMap h :=
        mem_orbitSpace_of_apply (Subgroup.inv_mem _ hcc) hu
      show y (c⁻¹ u) = u
      rw [← hcy _ hu']
      show (c * c⁻¹) u = u
      rw [mul_inv_cancel]
      rfl
    refine le_of_fpf (fun u hu => frame_apply_mem F hy'A j hu) (fun u hu hfix => ?_)
      (sub_mem_othersSpace hx hh hy'c hy'orb)
    have hcu : c⁻¹ u = u := by
      have h1 := htriv u hu
      calc c⁻¹ u = c⁻¹ (c u) := by rw [h1]
        _ = u := by
          show (c⁻¹ * c) u = u
          rw [inv_mul_cancel]
          rfl
    have h2 : y (c⁻¹ u) = u := hfix
    rw [hcu] at h2
    exact frame_single_fpf F j hu h2
  ·
    left
    exact le_of_fpf (fun u hu => frame_apply_mem F hcA j hu) hfpf (sub_mem_orbitSpace hx hh hcB)

end Block

end CoordOm

end CFSG.StandardType
