module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

theorem exists_polar_eq_one_of_ne_zero {ι : Type} {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate) {u : ι → K}
    (hu0 : u ≠ 0) : ∃ y₀ : ι → K, polar Q' u y₀ = 1 := by
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu0
  exact ⟨(polar Q' u y)⁻¹ • y, by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]⟩

theorem eq_smul_of_polar_perp {ι : Type} {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate) {u w y₀ : ι → K}
    (hy₀ : polar Q' u y₀ = 1) (hcon : ∀ w' : ι → K, polar Q' u w' = 0 → polar Q' w' w = 0) :
    w = polar Q' y₀ w • u := by
  have hlin : ∀ x : ι → K, polar Q' x w = polar Q' y₀ w * polar Q' u x := by
    intro x
    have hc : polar Q' u (x - polar Q' u x • y₀) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hy₀, mul_one, sub_self]
    have h0 := hcon _ hc
    calc polar Q' x w = polar Q' ((x - polar Q' u x • y₀) + polar Q' u x • y₀) w := by
          rw [sub_add_cancel]
      _ = polar Q' (x - polar Q' u x • y₀) w + polar Q' (polar Q' u x • y₀) w := by
          rw [polar_add_left]
      _ = polar Q' y₀ w * polar Q' u x := by
          rw [h0, polar_smul_left_eq, zero_add]
          ring
  rw [← sub_eq_zero]
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  rw [polar_sub_left, polar_smul_left_eq, polar_comm Q' w y, hlin y, sub_self]

theorem exists_eichler_witness_of_ne_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate) {u w : ι → K}
    (hu : Q' u = 0) (hu0 : u ≠ 0) (hw : polar Q' u w = 0) (hE : eichler Q' u w ≠ 1) :
    ∃ w' y₀ : ι → K, polar Q' u w' = 0 ∧ polar Q' y₀ u = 1 ∧
      eichler Q' u w (eichler Q' u w' y₀ - y₀) ≠ eichler Q' u w' y₀ - y₀ := by
  obtain ⟨y₀, hy₀⟩ := exists_polar_eq_one_of_ne_zero hQ hu0
  have hy₀s : polar Q' y₀ u = 1 := (polar_comm Q' y₀ u).trans hy₀
  have hex : ∃ w' : ι → K, polar Q' u w' = 0 ∧ polar Q' w' w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hE
    obtain ⟨a, ha⟩ : ∃ a : K, w = a • u :=
      ⟨polar Q' y₀ w, eq_smul_of_polar_perp hQ hy₀ hcon⟩
    rw [ha, ← zero_add (a • u), eichler_add_smul_self hu 0 a, eichler_zero_right]
  obtain ⟨w', hw', hpw⟩ := hex
  refine ⟨w', y₀, hw', hy₀s, fun heq => ?_⟩
  have hx₀ : eichler Q' u w' y₀ - y₀ = w' - (polar Q' y₀ w' + Q' w') • u := by
    rw [eichler_apply hu hw' y₀, hy₀s]
    module
  have hEx : polar Q' (eichler Q' u w' y₀ - y₀) u = 0 := by
    rw [hx₀, polar_sub_left, polar_smul_left_eq, polar_self_eq_zero hu, mul_zero, sub_zero,
      polar_comm Q' w' u, hw']
  have hEx2 : polar Q' (eichler Q' u w' y₀ - y₀) w = polar Q' w' w := by
    rw [hx₀, polar_sub_left, polar_smul_left_eq, hw, mul_zero, sub_zero]
  have hfin : eichler Q' u w (eichler Q' u w' y₀ - y₀) =
      (eichler Q' u w' y₀ - y₀) - polar Q' w' w • u := by
    rw [eichler_apply hu hw, hEx, hEx2]
    simp only [zero_smul, add_zero, mul_zero]
  rw [hfin, sub_eq_self, smul_eq_zero] at heq
  rcases heq with h | h
  · exact hpw h
  · exact hu0 h


theorem eichler_of_mem_LomGL {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q X) {u : ι → K}
    {A : GL ι K} (hA : A ∈ E.LomGL u) :
    ∃ w : ι → K, polar Q u w = 0 ∧ ∀ x : ι → K, (A : Matrix ι ι K) *ᵥ x = eichler Q u w x := by
  unfold ElemMatrixIso.LomGL at hA
  obtain ⟨hAX, hmem⟩ := CFSG.ClassicalGroups.F2Fixed.mem_matrixOf_iff.mp hA
  obtain ⟨w, hw, hEq⟩ := CFSG.ClassicalGroups.Orthogonal.mem_rootGroup.mp
    (CFSG.ClassicalGroups.Orthogonal.mem_Lom.mp hmem)
  refine ⟨w, hw, fun x => ?_⟩
  rw [hEq]
  exact (E.app ⟨A, hAX⟩ x).symm

theorem exists_mem_act_eq_eichler {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q X) {u : ι → K} {R L : Subgroup G} (φ : ↥R →* GL ι K)
    (hL : (L.subgroupOf R).map φ = E.LomGL u) {w : ι → K} (hw : polar Q u w = 0) :
    ∃ s : ↥R, (s : G) ∈ L ∧ ∀ x : ι → K, (φ s : Matrix ι ι K) *ᵥ x = eichler Q u w x := by
  obtain ⟨B, hB⟩ : ∃ B : X, E.equiv B = CFSG.ClassicalGroups.Orthogonal.eichlerG Q u w :=
    ⟨E.equiv.symm _, E.equiv.apply_symm_apply _⟩
  have hBmem : (B : GL ι K) ∈ E.LomGL u := by
    unfold ElemMatrixIso.LomGL
    refine CFSG.ClassicalGroups.F2Fixed.mem_matrixOf_iff.mpr ⟨B.2, ?_⟩
    have hB' : E.equiv ⟨(B : GL ι K), B.2⟩ = CFSG.ClassicalGroups.Orthogonal.eichlerG Q u w := hB
    rw [hB']
    exact CFSG.ClassicalGroups.Orthogonal.eichlerG_mem_Lom hw
  rw [← hL] at hBmem
  obtain ⟨s, hs, hsB⟩ := Subgroup.mem_map.mp hBmem
  refine ⟨s, Subgroup.mem_subgroupOf.mp hs, fun x => ?_⟩
  have hx : (CFSG.ClassicalGroups.Orthogonal.eichlerG Q u w).app x =
      ((B : GL ι K) : Matrix ι ι K) *ᵥ x := by
    rw [← hB]
    exact E.app B x
  rw [hsB]
  exact hx.symm

theorem mem_of_comm_comm_mem_Z_of_rootGroup {G : Type} [Group G] [Finite G]
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) {R V Z N L : Subgroup G} (hLR : L ≤ R) (hZV : Z ≤ V)
    (φ : ↥R →* GL ι K) (hker : φ.ker = N.subgroupOf R)
    (hsec : SectionAct K R V Z φ (fun g => (g : Matrix ι ι K)))
    {u : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0) (hL : (L.subgroupOf R).map φ = E.LomGL u)
    {l : G} (hl : l ∈ L) (h : ∀ v ∈ ⁅V, L⁆, ⁅l, v⁆ ∈ Z) : l ∈ N := by
  clear hZV
  unfold SectionAct at hsec
  obtain ⟨hVR, hN, ψ, hψ⟩ := hsec
  by_contra hlN
  obtain ⟨l', hl'⟩ : ∃ l' : ↥R, (l' : G) = l := ⟨⟨l, hLR hl⟩, rfl⟩
  have hl'L : (l' : G) ∈ L := by
    rw [hl']
    exact hl
  have hA1 : φ l' ≠ 1 := by
    intro h1
    apply hlN
    have hk : l' ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker, Subgroup.mem_subgroupOf, hl'] at hk
    exact hk
  have hAmem : φ l' ∈ E.LomGL u := by
    rw [← hL]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hl'L)
  obtain ⟨w, hw, hwA⟩ := eichler_of_mem_LomGL E hAmem
  have hne : eichler Q' u w ≠ 1 := by
    intro h1
    apply hA1
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [Matrix.one_mulVec, hwA x, h1]
    rfl
  obtain ⟨w', y₀, hw', -, hconc⟩ := exists_eichler_witness_of_ne_one hQ hu hu0 hw hne
  obtain ⟨s, hsL, hsA⟩ := exists_mem_act_eq_eichler E φ hL hw'
  obtain ⟨ŷ, hŷ⟩ := exists_secVec_eq ψ y₀
  have hvV : ⁅(s : G), (ŷ : G)⁆ ∈ V := comm_mem_of_le_normalizer hVR s ŷ
  have hcomm : ⁅(s : G), (ŷ : G)⁆ ∈ ⁅V, L⁆ := by
    have h1 := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ŷ.2 hsL)
    rwa [commutatorElement_inv] at h1
  have hvecv : secVec ψ ⟨⁅(s : G), (ŷ : G)⁆, hvV⟩ = eichler Q' u w' y₀ - y₀ := by
    have h1 := secVec_comm φ ψ hψ hVR s ŷ
    rw [hŷ, hsA] at h1
    exact h1
  have hmemw : (l' : G) * ⁅(s : G), (ŷ : G)⁆ * (l' : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hVR l'.2) ⁅(s : G), (ŷ : G)⁆).mp hvV
  have hact : secVec ψ ⟨(l' : G) * ⁅(s : G), (ŷ : G)⁆ * (l' : G)⁻¹, hmemw⟩ =
      (φ l' : Matrix ι ι K) *ᵥ secVec ψ ⟨⁅(s : G), (ŷ : G)⁆, hvV⟩ :=
    hψ l' ⟨⁅(s : G), (ŷ : G)⁆, hvV⟩ ⟨(l' : G) * ⁅(s : G), (ŷ : G)⁆ * (l' : G)⁻¹, hmemw⟩ rfl
  have hZ : ⁅(l' : G), ⁅(s : G), (ŷ : G)⁆⁆ ∈ Z := by
    rw [hl']
    exact h _ hcomm
  have hcomm2 : secVec ψ ⟨(l' : G) * ⁅(s : G), (ŷ : G)⁆ * (l' : G)⁻¹, hmemw⟩ =
      secVec ψ ⟨⁅(s : G), (ŷ : G)⁆, hvV⟩ :=
    (secVec_eq_iff ψ _ _).mpr hZ
  have hfix : (φ l' : Matrix ι ι K) *ᵥ secVec ψ ⟨⁅(s : G), (ŷ : G)⁆, hvV⟩ =
      secVec ψ ⟨⁅(s : G), (ŷ : G)⁆, hvV⟩ :=
    hact.symm.trans hcomm2
  rw [hvecv, hwA] at hfix
  exact hconc hfix


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_CN_of_comm_comm_mem_Z (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {l : G} (hl : l ∈ LB M Q B)
    (h : ∀ v ∈ ⁅Vt M (LB M Q B) B Z t, LB M Q B⁆, ⁅l, v⁆ ∈ Z) : l ∈ hc.CN t := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · exact mem_of_comm_comm_mem_Z_of_rootGroup (ElemMatrixIso.plus hm')
      (nondegenerate_polarBilin_quadPlus m' K) hLR hZV φ hker hsec hu hu0
      (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu) hl h
  · exact mem_of_comm_comm_mem_Z_of_rootGroup (ElemMatrixIso.minus hm' hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m' K hirr) hLR hZV φ hker hsec hu hu0
      (by rw [ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu) hl h

end CFSG.RankThree.GF2n.Stroth80
