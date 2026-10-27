module

public import CFSG.LinearAlgebra.SLThreeLeviOvergroups
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph
public import CFSG.LocalAnalysis.WeakClosure81.PSLThreeOuterInvolutions
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
public import CFSG.Goldschmidt75.Equivariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.Blueprint Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.Vol2.Ch11
open CFSG.RankThree.PartTwo.Sec4.L34Odd (embSL embSL_coe)
open scoped MatrixGroups

variable {K : Type} [Field K]

private noncomputable def psl3Inner_stdSign : SpecialLinearGroup (Fin 3) K :=
  embSL (-1 : GL (Fin 2) K)

private theorem psl3Inner_stdSign_coe :
    ((psl3Inner_stdSign (K := K) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
  rw [psl3Inner_stdSign, embSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.RankThree.PartTwo.Sec4.L34Odd.blockMat, Matrix.diagonal,
      Units.val_neg, Units.val_one, Matrix.det_fin_two]

private theorem psl3Inner_stdSign_sq :
    psl3Inner_stdSign (K := K) * psl3Inner_stdSign = 1 := by
  rw [psl3Inner_stdSign, ← map_mul]
  have h : (-1 : GL (Fin 2) K) * (-1) = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_neg, Units.val_one]
    rw [neg_mul_neg, mul_one]
  rw [h, map_one]

private theorem psl3Inner_stdSign_proj_orderOf (h2 : (2 : K) ≠ 0) :
    orderOf (proj 3 K (psl3Inner_stdSign (K := K))) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, pow_two, psl3Inner_stdSign_sq, map_one]
  · intro h
    have hmem : psl3Inner_stdSign (K := K) ∈ scalars 3 K := by
      rw [← ker_proj, MonoidHom.mem_ker]
      exact h
    obtain ⟨c, -, hmat⟩ := mem_scalars.mp hmem
    have h00 := congrFun (congrFun hmat 0) 0
    have h22 := congrFun (congrFun hmat 2) 2
    simp [psl3Inner_stdSign_coe, Matrix.scalar, Matrix.diagonal] at h00 h22
    exact h2 (by linear_combination h22 - h00)

private theorem psl3Inner_embSL_comm_stdSign (A : GL (Fin 2) K) :
    embSL A * psl3Inner_stdSign (K := K) = psl3Inner_stdSign (K := K) * embSL A := by
  change embSL A * embSL (-1 : GL (Fin 2) K) = embSL (-1 : GL (Fin 2) K) * embSL A
  exact (Commute.neg_one_right A).map embSL

private theorem psl3Inner_matrix_commute_of_graph_fixed (A : GL (Fin 3) K)
    (hgl : CFSG.ComponentClassification.Burgoyne.PSL.graphLift A
      (psl3Inner_stdSign (K := K)) = psl3Inner_stdSign (K := K)) :
    (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * (A : Matrix (Fin 3) (Fin 3) K) := by
  have hsq : psl3Inner_stdSign (K := K) * psl3Inner_stdSign = 1 := psl3Inner_stdSign_sq
  have hinv : (psl3Inner_stdSign (K := K))⁻¹ = psl3Inner_stdSign (K := K) :=
    inv_eq_of_mul_eq_one_right hsq
  have hinvMat :
      (((psl3Inner_stdSign (K := K))⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      ((psl3Inner_stdSign (K := K) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    rw [hinv]
  have htrans :
      ((((psl3Inner_stdSign (K := K))⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))ᵀ =
      ((psl3Inner_stdSign (K := K) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    rw [hinvMat, psl3Inner_stdSign_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, Matrix.diagonal]
  have hgl' : CFSG.LinearAlgebra.SLThreeLevi.graphAut A
      (psl3Inner_stdSign (K := K)) = psl3Inner_stdSign (K := K) := hgl
  have hmat : (A : Matrix (Fin 3) (Fin 3) K) *
      ((((psl3Inner_stdSign (K := K))⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K))ᵀ *
      (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      ((psl3Inner_stdSign (K := K) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    rw [← CFSG.LinearAlgebra.SLThreeLevi.coe_graphAut A (psl3Inner_stdSign (K := K))]
    exact congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K)) hgl'
  rw [htrans] at hmat
  have hglEq : A * SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K)) * A⁻¹ =
      SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K)) := by
    apply Units.ext
    simpa [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hmat
  have hcommGL : A * SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K)) =
      SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K)) * A := by
    calc A * SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K))
        = (A * SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K)) * A⁻¹) * A := by
          group
      _ = SpecialLinearGroup.toGL (psl3Inner_stdSign (K := K)) * A := by rw [hglEq]
  have hcommMat :
      (A : Matrix (Fin 3) (Fin 3) K) *
        ((psl3Inner_stdSign (K := K) : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
      ((psl3Inner_stdSign (K := K) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hcommGL
    simpa [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using this
  rw [← psl3Inner_stdSign_coe]
  exact hcommMat

private theorem psl3Inner_exists_blockGL (h2 : (2 : K) ≠ 0) (A : GL (Fin 3) K)
    (hcomm : (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * (A : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (P : GL (Fin 2) K) (s : Kˣ), A = CFSG.LinearAlgebra.SLThreeLevi.blockGL P s := by
  obtain ⟨h02, h12, h20, h21⟩ :=
    CFSG.RankThree.SubgroupLists.block_eq_zero_of_commute_negDiag h2 hcomm
  have hAb : (A : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LinearAlgebra.SLThreeLevi.blockMat
        (CFSG.RankThree.SubgroupLists.ulBlock (A : Matrix (Fin 3) (Fin 3) K)) 0 0
        ((A : Matrix (Fin 3) (Fin 3) K) 2 2) := by
    rw [← CFSG.LinearAlgebra.SLThreeLevi.blockMat_ulBlock_blockb_blockc_blockd
      (A : Matrix (Fin 3) (Fin 3) K)]
    have hb : CFSG.LinearAlgebra.SLThreeLevi.blockb (A : Matrix (Fin 3) (Fin 3) K) = 0 := by
      funext i
      fin_cases i
      · simpa [CFSG.LinearAlgebra.SLThreeLevi.blockb] using h02
      · simpa [CFSG.LinearAlgebra.SLThreeLevi.blockb] using h12
    have hc : CFSG.LinearAlgebra.SLThreeLevi.blockc (A : Matrix (Fin 3) (Fin 3) K) = 0 := by
      funext i
      fin_cases i
      · simpa [CFSG.LinearAlgebra.SLThreeLevi.blockc] using h20
      · simpa [CFSG.LinearAlgebra.SLThreeLevi.blockc] using h21
    rw [hb, hc]
    rfl
  have hdetprod : (A : Matrix (Fin 3) (Fin 3) K).det =
      (CFSG.RankThree.SubgroupLists.ulBlock (A : Matrix (Fin 3) (Fin 3) K)).det *
        ((A : Matrix (Fin 3) (Fin 3) K) 2 2) := by
    conv_lhs => rw [hAb]
    exact CFSG.LinearAlgebra.SLThreeLevi.blockMat_det_diag _ _
  have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := A.det_ne_zero
  have hPdet : (CFSG.RankThree.SubgroupLists.ulBlock
      (A : Matrix (Fin 3) (Fin 3) K)).det ≠ 0 := by
    intro h
    apply hdetA
    rw [hdetprod, h, zero_mul]
  have h22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h
    apply hdetA
    rw [hdetprod, h, mul_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hPdet,
    Units.mk0 ((A : Matrix (Fin 3) (Fin 3) K) 2 2) h22, ?_⟩
  apply Units.ext
  rw [CFSG.LinearAlgebra.SLThreeLevi.blockGL_coe,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Units.val_mk0]
  exact hAb

private theorem psl3Inner_exists_mul_mem_centralizer
    {G : Type} [Group G] [Finite G] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {L : Subgroup G} (hAS : SecE3.AlmostSimple L)
    (e : ↥L ≃* projectiveSL 3 K)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    ∀ g : G, ∃ l ∈ L, l * g ∈ Subgroup.centralizer ({z} : Set G) := by
  haveI : L.Normal := hAS.normal
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  set w : projectiveSL 3 K := e ⟨z, hzL⟩ with hwdef
  have hw2 : orderOf w = 2 := by
    rw [hwdef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2]
  intro g
  set y : G := g * z * g⁻¹ with hydef
  have hyL : y ∈ L := by
    rw [hydef]
    exact hAS.normal.conj_mem z hzL g
  have hy2 : orderOf y = 2 := by
    rw [hydef, show orderOf (g * z * g⁻¹) = orderOf z from by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z]
    exact hz2
  have hyproj2 : orderOf (e ⟨y, hyL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
  obtain ⟨a, ha⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psl3
    (a := e ⟨y, hyL⟩) (b := w) hodd hyproj2 hw2
  set l : G := ((e.symm a : ↥L) : G) with hldef
  have hlL : l ∈ L := (e.symm a).2
  have hconj : l * y * l⁻¹ = z := by
    have ha' : e.symm a * (⟨y, hyL⟩ : ↥L) * (e.symm a)⁻¹ = (⟨z, hzL⟩ : ↥L) := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hwdef]
      exact ha
    have := congrArg (fun x : ↥L => (x : G)) ha'
    simpa [l, Subgroup.coe_mul, Subgroup.coe_inv] using this
  refine ⟨l, hlL, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmain : l * g * z * (l * g)⁻¹ = z := by
    calc l * g * z * (l * g)⁻¹ = l * (g * z * g⁻¹) * l⁻¹ := by group
      _ = z := by rw [← hydef]; exact hconj
  calc l * g * z = (l * g * z * (l * g)⁻¹) * (l * g) := by group
    _ = z * (l * g) := by rw [hmain]

private theorem psl3Inner_rho_graphLift
    {G : Type} [Group G]
    {L : Subgroup G} [L.Normal]
    (e : ↥L ≃* projectiveSL 3 K)
    {A : GL (Fin 3) K} {c : G}
    (hβ : MulAut.congr e (MulAut.conjNormal (H := L) c) =
      conjAut 3 K A * dualAut 3 K)
    (m : SpecialLinearGroup (Fin 3) K) :
    L.subtype (e.symm (proj 3 K
      (CFSG.ComponentClassification.Burgoyne.PSL.graphLift A m))) =
      c * L.subtype (e.symm (proj 3 K m)) * c⁻¹ := by
  have hleft : (MulAut.congr e (MulAut.conjNormal (H := L) c)) (proj 3 K m) =
      e (MulAut.conjNormal c (e.symm (proj 3 K m))) := by
    simp [MulAut.congr_apply]
  have hcongr := congrArg (fun f : MulAut (projectiveSL 3 K) => f (proj 3 K m)) hβ
  rw [hleft, CFSG.ComponentClassification.Burgoyne.PSL.conjAut_mul_dualAut_proj] at hcongr
  have h1 : MulAut.conjNormal c (e.symm (proj 3 K m)) =
      e.symm (proj 3 K (CFSG.ComponentClassification.Burgoyne.PSL.graphLift A m)) := by
    rw [← hcongr, MulEquiv.symm_apply_apply]
  calc L.subtype (e.symm (proj 3 K
        (CFSG.ComponentClassification.Burgoyne.PSL.graphLift A m)))
      = L.subtype (MulAut.conjNormal c (e.symm (proj 3 K m))) := by rw [← h1]
    _ = c * L.subtype (e.symm (proj 3 K m)) * c⁻¹ :=
        MulAut.conjNormal_apply c (e.symm (proj 3 K m))

private theorem psl3Inner_isCoatom_std
    {G : Type} [Group G] [Finite G] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hf : Odd f)
    {L : Subgroup G} (hAS : SecE3.AlmostSimple L)
    (e : ↥L ≃* projectiveSL 3 K)
    (hGL : ∃ g : G, g ∉ L)
    {z : G} (hzL : z ∈ L)
    (hzstd : e ⟨z, hzL⟩ = proj 3 K (psl3Inner_stdSign (K := K))) :
    IsCoatom (Subgroup.centralizer ({z} : Set G)) := by
  classical
  haveI : L.Normal := hAS.normal
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf (e ⟨z, hzL⟩) = orderOf z := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    rw [← h1, hzstd, psl3Inner_stdSign_proj_orderOf h2]
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  have hsupp : ∀ g : G, ∃ l ∈ L, l * g ∈ C :=
    psl3Inner_exists_mul_mem_centralizer hp hp2 hK hAS e hzL hz2
  obtain ⟨t₀, ht₀⟩ := hGL
  obtain ⟨l₀, hl₀, hl₀C⟩ := hsupp t₀
  set c : G := l₀ * t₀ with hcdef
  have hcL : c ∉ L := by
    intro hcL
    apply ht₀
    have : t₀ = l₀⁻¹ * c := by rw [hcdef]; group
    rw [this]
    exact L.mul_mem (L.inv_mem hl₀) hcL
  have hcC : c ∈ C := hl₀C
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  obtain ⟨A, hβA⟩ := conjNormal_transport_eq_conjAut_mul_dualAut hAS hp hK hf e hcL
  have hfix : (MulAut.congr e (MulAut.conjNormal (H := L) c))
      (proj 3 K (psl3Inner_stdSign (K := K))) = proj 3 K (psl3Inner_stdSign (K := K)) := by
    have hsymm : e.symm (proj 3 K (psl3Inner_stdSign (K := K))) = (⟨z, hzL⟩ : ↥L) := by
      rw [← hzstd, MulEquiv.symm_apply_apply]
    have h2' : (MulAut.congr e (MulAut.conjNormal (H := L) c))
        (proj 3 K (psl3Inner_stdSign (K := K))) =
        e (MulAut.conjNormal c (⟨z, hzL⟩ : ↥L)) := by
      simp [MulAut.congr_apply, hsymm]
    rw [h2']
    have hconjz : MulAut.conjNormal c (⟨z, hzL⟩ : ↥L) = ⟨z, hzL⟩ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show c * z * c⁻¹ = z
      rw [hcz]
      group
    rw [hconjz, hzstd]
  have hprojfix : proj 3 K (CFSG.ComponentClassification.Burgoyne.PSL.graphLift A
      (psl3Inner_stdSign (K := K))) = proj 3 K (psl3Inner_stdSign (K := K)) := by
    rw [← CFSG.ComponentClassification.Burgoyne.PSL.conjAut_mul_dualAut_proj A
      (psl3Inner_stdSign (K := K)), ← hβA]
    exact hfix
  have hgl2 : CFSG.ComponentClassification.Burgoyne.PSL.graphLift A
      (psl3Inner_stdSign (K := K)) *
      CFSG.ComponentClassification.Burgoyne.PSL.graphLift A
        (psl3Inner_stdSign (K := K)) = 1 := by
    rw [← map_mul, psl3Inner_stdSign_sq, map_one]
  have hgl_fix : CFSG.ComponentClassification.Burgoyne.PSL.graphLift A
      (psl3Inner_stdSign (K := K)) = psl3Inner_stdSign (K := K) :=
    CFSG.GH74.KGroups.L3Eps.eq_of_proj_eq (j := 1)
      (by simpa [pow_two] using hgl2)
      (by simpa [pow_two] using psl3Inner_stdSign_sq) hprojfix
  have hAcomm : (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * (A : Matrix (Fin 3) (Fin 3) K) :=
    psl3Inner_matrix_commute_of_graph_fixed A hgl_fix
  obtain ⟨P, s, hAeq⟩ := psl3Inner_exists_blockGL h2 A hAcomm
  let ρ : SpecialLinearGroup (Fin 3) K →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (proj 3 K))
  have hρsurj : ∀ l ∈ L, ∃ m : SpecialLinearGroup (Fin 3) K, ρ m = l := by
    intro l hl
    obtain ⟨m, hm⟩ := proj_surjective 3 K (e ⟨l, hl⟩)
    refine ⟨m, ?_⟩
    change ((e.symm (proj 3 K m) : ↥L) : G) = l
    rw [hm, MulEquiv.symm_apply_apply]
  have hdesc : ∀ m : SpecialLinearGroup (Fin 3) K,
      ρ (CFSG.LinearAlgebra.SLThreeLevi.graphAut
        (CFSG.LinearAlgebra.SLThreeLevi.blockGL P s) m) = c * ρ m * c⁻¹ := by
    intro m
    rw [← hAeq]
    change ((e.symm (proj 3 K (CFSG.ComponentClassification.Burgoyne.PSL.graphLift A m)) :
      ↥L) : G) = c * ((e.symm (proj 3 K m) : ↥L) : G) * c⁻¹
    exact psl3Inner_rho_graphLift e hβA m
  have hleviC : CFSG.LinearAlgebra.SLThreeLevi.levi ≤ C.comap ρ := by
    intro m hm
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hmcomm : m * psl3Inner_stdSign (K := K) =
        psl3Inner_stdSign (K := K) * m := by
      rw [CFSG.LinearAlgebra.SLThreeLevi.mem_levi_iff] at hm
      obtain ⟨A', rfl⟩ := hm
      exact psl3Inner_embSL_comm_stdSign A'
    have hprojcomm : proj 3 K m * proj 3 K (psl3Inner_stdSign (K := K)) =
        proj 3 K (psl3Inner_stdSign (K := K)) * proj 3 K m := by
      rw [← map_mul, ← map_mul, hmcomm]
    have hLcomm : (e.symm (proj 3 K m) : ↥L) * (⟨z, hzL⟩ : ↥L) =
        (⟨z, hzL⟩ : ↥L) * (e.symm (proj 3 K m)) := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hzstd]
      exact hprojcomm
    have h := congrArg (fun x : ↥L => (x : G)) hLcomm
    change ((e.symm (proj 3 K m) : ↥L) : G) * z =
      z * ((e.symm (proj 3 K m) : ↥L) : G)
    simpa [Subgroup.coe_mul] using h
  refine ⟨fun htop => hz1 ?_, ?_⟩
  · have hzcent : z ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlC : l ∈ C := by rw [htop]; exact Subgroup.mem_top l
      exact Subgroup.mem_centralizer_singleton_iff.mp hlC
    rw [hAS.centralizer_eq] at hzcent
    exact Subgroup.mem_bot.mp hzcent
  · intro H hCH
    let M : Subgroup (SpecialLinearGroup (Fin 3) K) := H.comap ρ
    have hleviM : CFSG.LinearAlgebra.SLThreeLevi.levi ≤ M :=
      hleviC.trans (Subgroup.comap_mono hCH.le)
    have hstabM : M.map (CFSG.LinearAlgebra.SLThreeLevi.graphAut
        (CFSG.LinearAlgebra.SLThreeLevi.blockGL P s)).toMonoidHom ≤ M := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_comap] at hm ⊢
      change ρ ((CFSG.LinearAlgebra.SLThreeLevi.graphAut
        (CFSG.LinearAlgebra.SLThreeLevi.blockGL P s)) m) ∈ H
      rw [hdesc m]
      exact H.mul_mem (H.mul_mem (hCH.le hcC) hm) (H.inv_mem (hCH.le hcC))
    have hdich := CFSG.LinearAlgebra.SLThreeLevi.eq_levi_or_top_of_graph_blockDiag
      M P s h2 hleviM hstabM
    rcases hdich with hM | hM
    ·
      exfalso
      have hHC : H ≤ C := by
        intro h hh
        obtain ⟨l, hl, hlh⟩ := hsupp h
        have hlH : l ∈ H := by
          have : l = (l * h) * h⁻¹ := by group
          rw [this]
          exact H.mul_mem (hCH.le hlh) (H.inv_mem hh)
        obtain ⟨m, hm⟩ := hρsurj l hl
        have hmM : m ∈ M := by
          rw [Subgroup.mem_comap]
          rw [hm]
          exact hlH
        have hmlevi : m ∈ CFSG.LinearAlgebra.SLThreeLevi.levi := by
          have hmM' := hmM
          rw [hM] at hmM'
          exact hmM'
        have hρmC : ρ m ∈ C := hleviC hmlevi
        rw [hm] at hρmC
        have hmem : l⁻¹ * (l * h) ∈ C := C.mul_mem (C.inv_mem hρmC) hlh
        rw [show l⁻¹ * (l * h) = h from by group] at hmem
        exact hmem
      exact hCH.ne (le_antisymm hCH.le hHC)
    ·
      have hLH : L ≤ H := by
        intro l hl
        obtain ⟨m, hm⟩ := hρsurj l hl
        have hmM : m ∈ M := by rw [hM]; exact Subgroup.mem_top m
        have hρmH : ρ m ∈ H := Subgroup.mem_comap.mp hmM
        rw [hm] at hρmH
        exact hρmH
      refine eq_top_iff.mpr fun g _ => ?_
      obtain ⟨l, hl, hlg⟩ := hsupp g
      have hmem : l⁻¹ * (l * g) ∈ H := H.mul_mem (H.inv_mem (hLH hl)) (hCH.le hlg)
      rw [show g = l⁻¹ * (l * g) from by group]
      exact hmem

theorem isCoatom_centralizer_of_psl3_graph_extension
    {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hf : Odd f)
    {L : Subgroup G} (hAS : SecE3.AlmostSimple L)
    (e : ↥L ≃* projectiveSL 3 K)
    (hGL : ∃ g : G, g ∉ L)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set G)) := by
  classical
  haveI : L.Normal := hAS.normal
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  set w : projectiveSL 3 K := e ⟨z, hzL⟩ with hwdef
  have hw2 : orderOf w = 2 := by
    rw [hwdef, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2]
  have hs2 : orderOf (proj 3 K (psl3Inner_stdSign (K := K))) = 2 :=
    psl3Inner_stdSign_proj_orderOf h2
  obtain ⟨g₀, hg₀⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psl3
    (a := w) (b := proj 3 K (psl3Inner_stdSign (K := K))) hodd hw2 hs2
  set c₀ : G := ((e.symm g₀ : ↥L) : G) with hc₀def
  have hyL : c₀ * z * c₀⁻¹ ∈ L := hAS.normal.conj_mem z hzL c₀
  set y : G := c₀ * z * c₀⁻¹ with hydef
  have hyL' : y ∈ L := by rw [hydef]; exact hyL
  have hy2 : orderOf y = 2 := by
    rw [hydef, show orderOf (c₀ * z * c₀⁻¹) = orderOf z from by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj c₀).toMonoidHom (MulAut.conj c₀).injective z]
    exact hz2
  have hystd : e ⟨y, hyL'⟩ = proj 3 K (psl3Inner_stdSign (K := K)) := by
    have hyeq : (⟨y, hyL'⟩ : ↥L) =
        (e.symm g₀) * (⟨z, hzL⟩ : ↥L) * (e.symm g₀)⁻¹ := by
      apply Subtype.ext
      show y = (((e.symm g₀) * (⟨z, hzL⟩ : ↥L) * (e.symm g₀)⁻¹ : ↥L) : G)
      rw [hydef, hc₀def]
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyeq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hwdef]
    exact hg₀
  have hcoat_y : IsCoatom (Subgroup.centralizer ({y} : Set G)) :=
    psl3Inner_isCoatom_std hp hp2 hK hf hAS e hGL hyL' hystd
  have hconjSub : CFSG.Goldschmidt.conjSub c₀⁻¹
      (Subgroup.centralizer ({z} : Set G)) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj c₀).toMonoidHom := by
    rw [CFSG.Goldschmidt.conjSub, inv_inv]
  have hmap : Subgroup.centralizer ({y} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj c₀).toMonoidHom := by
    have h := CFSG.Goldschmidt75.conjSub_centralizer_singleton (s := c₀⁻¹) (t := z)
    rw [← hconjSub, h, hydef, inv_inv]
  have hcoat_map : IsCoatom
      ((Subgroup.centralizer ({z} : Set G)).map (MulAut.conj c₀).toMonoidHom) := by
    rwa [← hmap]
  have hiff := (MulEquiv.mapSubgroup (MulAut.conj c₀)).isCoatom_iff
    (Subgroup.centralizer ({z} : Set G))
  simpa [MulEquiv.mapSubgroup_apply] using hiff.mp hcoat_map

end CFSG.LocalAnalysis.WeakClosure81

end
