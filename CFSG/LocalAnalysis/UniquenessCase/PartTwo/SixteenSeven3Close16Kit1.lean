module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Vol2.Ch10SecQ9H8
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4APt
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32B
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
open CFSG.Quasithin.Stellmacher.PU.L3YC
open Matrix

private abbrev SL4 := SpecialLinearGroup (Fin 4) (ZMod 2)

private abbrev SL3 := SpecialLinearGroup (Fin 3) (ZMod 2)

private theorem close16_stabV_single : stabV (Pi.single (0 : Fin 4) 1) = ptStab := by
  apply Subgroup.ext
  intro M
  rw [mem_stabV]
  rfl

private theorem close16_block_det (M : ↥ptStab) :
    (Matrix.of fun i j : Fin 3 =>
      ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ).det = 1 := by
  have h1 := ptStab_shape (M : SL4) M.2
  have h2 := congrArg Matrix.det h1
  rw [det_blk4] at h2
  rw [← h2]
  exact (M : SL4).2

private theorem close16_block_mul (M N : ↥ptStab) :
    (Matrix.of fun i j : Fin 3 =>
        ((M * N : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) =
      (Matrix.of fun i j : Fin 3 =>
        ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) *
      (Matrix.of fun i j : Fin 3 =>
        ((N : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) := by
  ext i j
  simp only [Matrix.of_apply]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply]
  conv_lhs => rw [Fin.sum_univ_succ]
  have hM0 : ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ 0 = 0 := by
    have := (mem_ptStab_iff (M : SL4)).1 M.2 i.succ
    simpa using this
  rw [hM0, zero_mul, zero_add]
  simp only [Matrix.of_apply]

private def close16_blockHom : ↥ptStab →* SL3 where
  toFun M :=
    ⟨Matrix.of fun i j : Fin 3 =>
        ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ,
      close16_block_det M⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [Matrix.one_apply, Fin.succ_inj]
  map_mul' M N := by
    apply Subtype.ext
    show (Matrix.of fun i j : Fin 3 =>
        ((M * N : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) =
      (Matrix.of fun i j : Fin 3 =>
        ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) *
      (Matrix.of fun i j : Fin 3 =>
        ((N : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ)
    exact close16_block_mul M N

private theorem close16_blockHom_blk4SL (y : Fin 3 → ZMod 2) (A : SL3) :
    close16_blockHom ⟨blk4SL y A, blk4SL_mem y A⟩ = A := by
  apply Subtype.ext
  change (Matrix.of fun i j : Fin 3 =>
      ((blk4SL y A : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) = ↑A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4SL_coe, blk4, Matrix.cons_val_zero, Matrix.cons_val_succ]

private theorem close16_blockHom_surjective : Function.Surjective close16_blockHom :=
  fun A => ⟨⟨blk4SL 0 A, blk4SL_mem 0 A⟩, close16_blockHom_blk4SL 0 A⟩

private theorem close16_card_SL3 : Nat.card SL3 = 168 := by
  rw [Matrix.card_SL_field 3, ZMod.card]
  simp [Fin.prod_univ_succ]

private theorem close16_card_ker_of_surj {G : Type*} [Group G] [Finite G] {f : G →* SL3}
    (hf : Function.Surjective f) (hG : Nat.card G = 1344) : Nat.card f.ker = 8 := by
  have hcard := Subgroup.card_ker_mul_card_of_surjective hf
  rw [close16_card_SL3, hG] at hcard
  omega

private theorem close16_ker_isPGroup {G : Type*} [Group G] [Finite G] {f : G →* SL3}
    (hf : Function.Surjective f) (hG : Nat.card G = 1344) : IsPGroup 2 f.ker :=
  IsPGroup.of_card (n := 3) (by rw [close16_card_ker_of_surj hf hG]; norm_num)

private theorem close16_ptStab_maximal {J : Subgroup SL4} (h : ptStab ≤ J) :
    J = ptStab ∨ J = ⊤ := by
  by_cases hJ : J = ptStab
  · exact Or.inl hJ
  · right
    have hex : ∃ g ∈ J, g ∉ ptStab := by
      by_contra hc
      rw [not_exists] at hc
      exact hJ (le_antisymm (fun x hx => by
        by_contra hx'
        exact (hc x) ⟨hx, hx'⟩) h)
    obtain ⟨g, hgJ, hg⟩ := hex
    refine le_antisymm le_top ?_
    intro y hy
    rcases ptStab_double g y hg with hy' | ⟨a, ha, b, hb, rfl⟩
    · exact h hy'
    · exact J.mul_mem (J.mul_mem (h ha) hgJ) (h hb)

private theorem close16_ptStab_quot :
    ∃ f : ↥ptStab →* SL3,
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧ Nat.card f.ker = 8 :=
  ⟨close16_blockHom, close16_blockHom_surjective,
    close16_ker_isPGroup close16_blockHom_surjective card_ptStab,
    close16_card_ker_of_surj close16_blockHom_surjective card_ptStab⟩

private theorem close16_pElementSubgroup_le {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    CFSG.RankThree.PartOne.pElementSubgroup p X ≤ X := by
  rw [CFSG.RankThree.PartOne.pElementSubgroup]
  intro x hx
  exact Subgroup.mem_closure.mp hx X (fun y hy => hy.1)

private theorem close16_conjBy_self {G : Type} [Group G] (X : Subgroup G) {x : G}
    (hx : x ∈ X) : CFSG.RankThree.PartOne.conjBy x X = X := by
  ext y
  change y ∈ X.map (MulAut.conj x).toMonoidHom ↔ y ∈ X
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx)
  · intro hy
    refine ⟨x⁻¹ * y * x, X.mul_mem (X.mul_mem (X.inv_mem hx) hy) hx, ?_⟩
    show x * (x⁻¹ * y * x) * x⁻¹ = y
    group

private theorem close16_opp_conjBy_self {G : Type} [Group G] (p : ℕ) (X : Subgroup G) (x : G)
    (hx : x ∈ X) : (Opp p X).map (MulAut.conj x).toMonoidHom = Opp p X := by
  have h1 := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p x X
  have h2 : CFSG.RankThree.PartOne.conjBy x X = X := close16_conjBy_self X hx
  rw [h2] at h1
  exact h1.symm

private def close16_A3 : SL3 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide +kernel⟩

private theorem close16_A3_ne_one : close16_A3 ≠ 1 := by decide +kernel

private theorem close16_blk4SL_A3_cube : (blk4SL 0 close16_A3) ^ 3 = 1 := by decide +kernel

private theorem close16_blk4SL_A3_ne_one : (blk4SL 0 close16_A3) ≠ 1 := by decide +kernel

private theorem close16_blk4SL_A3_orderOf : orderOf (blk4SL 0 close16_A3) = 3 :=
  orderOf_eq_prime close16_blk4SL_A3_cube close16_blk4SL_A3_ne_one

private abbrev close16_Tsub : Subgroup ↥ptStab := (Opp 3 ptStab).subgroupOf ptStab

private abbrev close16_E : Subgroup ↥ptStab := close16_blockHom.ker

private def close16_Eelt (y : Fin 3 → ZMod 2) : ↥ptStab := ⟨blk4SL y 1, blk4SL_mem y 1⟩

private def close16_a : ↥ptStab := ⟨blk4SL 0 close16_A3, blk4SL_mem 0 close16_A3⟩

private def close16_e : ↥ptStab := close16_Eelt (Pi.single (0 : Fin 3) 1)

private def close16_n : ↥ptStab := close16_a * close16_e * close16_a⁻¹ * close16_e⁻¹

private theorem close16_blockHom_a : close16_blockHom close16_a = close16_A3 :=
  close16_blockHom_blk4SL 0 close16_A3

private theorem close16_blockHom_e : close16_blockHom close16_e = 1 :=
  close16_blockHom_blk4SL _ 1

private theorem close16_a_mem : close16_a ∈ close16_Tsub := by
  rw [Subgroup.mem_subgroupOf]
  show (blk4SL 0 close16_A3) ∈ Opp 3 ptStab
  show (blk4SL 0 close16_A3) ∈
    Subgroup.closure {x : SL4 | x ∈ ptStab ∧ ∃ k, orderOf x = 3 ^ k}
  exact Subgroup.subset_closure ⟨blk4SL_mem 0 close16_A3,
    ⟨1, by simpa using close16_blk4SL_A3_orderOf⟩⟩

private theorem close16_Tsub_normal : close16_Tsub.Normal := by
  change ((CFSG.RankThree.PartOne.pElementSubgroup 3 ptStab).subgroupOf ptStab).Normal
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (close16_pElementSubgroup_le 3 ptStab)]
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact close16_opp_conjBy_self 3 ptStab g hg

private theorem close16_n_mem_E : close16_n ∈ close16_E := by
  show close16_blockHom close16_n = 1
  dsimp only [close16_n]
  simp [map_mul, map_inv, close16_blockHom_a, close16_blockHom_e]

private theorem close16_n_mem_T : close16_n ∈ close16_Tsub := by
  have hN : close16_Tsub.Normal := close16_Tsub_normal
  have h1 : close16_a ∈ close16_Tsub := close16_a_mem
  have h2 := hN.conj_mem close16_a⁻¹ (close16_Tsub.inv_mem h1) close16_e
  have hn : close16_n = close16_a * (close16_e * close16_a⁻¹ * close16_e⁻¹) := by
    dsimp only [close16_n]; group
  rw [hn]
  exact close16_Tsub.mul_mem h1 h2

private theorem close16_n_ne_one : close16_n ≠ 1 := by decide +kernel

private theorem close16_ker_eq_Eelt (M : ↥ptStab) (hM : M ∈ close16_blockHom.ker) :
    ∃ y : Fin 3 → ZMod 2, M = close16_Eelt y := by
  rw [MonoidHom.mem_ker] at hM
  refine ⟨fun i => ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 i.succ, ?_⟩
  dsimp only [close16_Eelt]
  apply Subtype.ext
  apply Subtype.ext
  have hker : (Matrix.of fun i j : Fin 3 =>
      ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have h := congrArg (fun A : SL3 => (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) hM
    change (Matrix.of fun i j : Fin 3 =>
        ((M : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) =
          (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) at h
    simpa using h
  rw [ptStab_shape (M : SL4) M.2, blk4SL_coe, hker, Matrix.SpecialLinearGroup.coe_one]
  congr 1
  funext i
  fin_cases i <;> simp [blk4]

private theorem close16_Eelt_zero : close16_Eelt 0 = 1 := by decide +kernel

private theorem close16_conj_blk4SL :
    ∀ (y : Fin 3 → ZMod 2) (A : SL3),
      (⟨blk4SL 0 A, blk4SL_mem 0 A⟩ : ↥ptStab) * close16_Eelt y *
          (⟨blk4SL 0 A, blk4SL_mem 0 A⟩ : ↥ptStab)⁻¹ =
        close16_Eelt (y ᵥ* ((A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
  decide +kernel

private theorem close16_row_trans (y y' : Fin 3 → ZMod 2) (hy : y ≠ 0) (hy' : y' ≠ 0) :
    ∃ A : SL3, y ᵥ* ((A : SL3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = y' := by
  obtain ⟨C, hCdet, hC⟩ := exists_mat3 y y' hy hy'
  refine ⟨⟨Cᵀ, by rwa [Matrix.det_transpose]⟩, ?_⟩
  change y ᵥ* Cᵀ = y'
  rw [Matrix.vecMul_transpose, hC]

private theorem close16_ker_le_Tsub : close16_E ≤ close16_Tsub := by
  intro e' he'
  obtain ⟨y', hy'⟩ := close16_ker_eq_Eelt e' he'
  by_cases hy'0 : y' = 0
  · have he1 : e' = 1 := by rw [hy', hy'0, close16_Eelt_zero]
    rw [he1]
    exact close16_Tsub.one_mem
  · obtain ⟨yn, hyn⟩ := close16_ker_eq_Eelt close16_n close16_n_mem_E
    have hyn0 : yn ≠ 0 := by
      intro h0
      exact close16_n_ne_one (by rw [hyn, h0, close16_Eelt_zero])
    obtain ⟨B, hB⟩ := close16_row_trans yn y' hyn0 hy'0
    have hgn : (⟨blk4SL 0 B⁻¹, blk4SL_mem 0 B⁻¹⟩ : ↥ptStab) * close16_n *
        (⟨blk4SL 0 B⁻¹, blk4SL_mem 0 B⁻¹⟩ : ↥ptStab)⁻¹ = e' := by
      rw [hyn, hy', close16_conj_blk4SL]
      rw [inv_inv, hB]
    have hmem : (⟨blk4SL 0 B⁻¹, blk4SL_mem 0 B⁻¹⟩ : ↥ptStab) * close16_n *
        (⟨blk4SL 0 B⁻¹, blk4SL_mem 0 B⁻¹⟩ : ↥ptStab)⁻¹ ∈ close16_Tsub :=
      close16_Tsub_normal.conj_mem close16_n close16_n_mem_T _
    rw [hgn] at hmem
    exact hmem

private theorem close16_eq_top_of_map_eq_top_of_ker_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) {N : Subgroup G} (hN : N.map f = ⊤) (hker : f.ker ≤ N) : N = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : f g ∈ N.map f := by rw [hN]; exact Subgroup.mem_top _
  rw [Subgroup.mem_map] at hg
  obtain ⟨n, hn, hfn⟩ := hg
  have hgn : g * n⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, mul_inv_cancel]
  have := hker hgn
  rw [show g = g * n⁻¹ * n by group]
  exact N.mul_mem this hn

private theorem close16_ptStab_opp : Opp 3 ptStab = ptStab := by
  haveI : IsSimpleGroup SL3 := CFSG.ClassicalInvolution.Q3.TL4.isSimpleGroup_sl3Two
  have hE_le : close16_E ≤ close16_Tsub := close16_ker_le_Tsub
  have hNtop : close16_Tsub.map close16_blockHom = ⊤ := by
    have hNnormal : (close16_Tsub.map close16_blockHom).Normal :=
      close16_Tsub_normal.map close16_blockHom close16_blockHom_surjective
    haveI : (close16_Tsub.map close16_blockHom).Normal := hNnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (close16_Tsub.map close16_blockHom) with
      hbot | htop
    · exact absurd hbot (by
        intro h
        have hA3 : close16_A3 ∈ close16_Tsub.map close16_blockHom := by
          have := Subgroup.mem_map_of_mem close16_blockHom close16_a_mem
          rwa [close16_blockHom_a] at this
        rw [h, Subgroup.mem_bot] at hA3
        exact close16_A3_ne_one hA3)
    · exact htop
  have hTop : close16_Tsub = ⊤ :=
    close16_eq_top_of_map_eq_top_of_ker_le close16_blockHom hNtop hE_le
  rw [Subgroup.subgroupOf_eq_top] at hTop
  exact le_antisymm (close16_pElementSubgroup_le 3 ptStab) hTop

theorem close16_sl4_stab_maximal {x : Fin 4 → ZMod 2} (hx : x ≠ 0)
    {J : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))} (h : stabV x ≤ J) :
    J = stabV x ∨ J = ⊤ := by
  obtain ⟨g₀, hg₀⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.exists_mulVec_eq
    (v := Pi.single (0 : Fin 4) 1) (w := x) (by decide) hx
  have hx' : x = g₀ • (Pi.single (0 : Fin 4) 1) := by
    rw [smul_eq_mulVec']; exact hg₀.symm
  have hstab : stabV x = (stabV (Pi.single (0 : Fin 4) 1)).map
      (MulAut.conj g₀).toMonoidHom := by
    rw [hx']
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g₀ (Pi.single (0 : Fin 4) 1)
  have hstab' : stabV x = ptStab.map (MulAut.conj g₀).toMonoidHom := by
    rw [hstab, close16_stabV_single]
  have hK : ptStab ≤ J.comap (MulAut.conj g₀).toMonoidHom := by
    apply Subgroup.map_le_iff_le_comap.mp
    rw [← hstab']
    exact h
  have hmap : (J.comap (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g₀).toMonoidHom = J :=
    Subgroup.map_comap_eq_self_of_surjective
      (f := (MulAut.conj g₀).toMonoidHom) (MulAut.conj g₀).surjective J
  rcases close16_ptStab_maximal hK with hcase | hcase
  · left
    rw [← hmap, hcase, hstab']
  · right
    rw [← hmap, hcase, Subgroup.map_top]
    exact MonoidHom.range_eq_top_of_surjective ((MulAut.conj g₀).toMonoidHom)
      (MulAut.conj g₀).surjective

theorem close16_sl4_stab_quot {x : Fin 4 → ZMod 2} (hx : x ≠ 0) :
    ∃ f : ↥(stabV x) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧ Nat.card f.ker = 8 := by
  obtain ⟨g₀, hg₀⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.exists_mulVec_eq
    (v := Pi.single (0 : Fin 4) 1) (w := x) (by decide) hx
  have hx' : x = g₀ • (Pi.single (0 : Fin 4) 1) := by
    rw [smul_eq_mulVec']; exact hg₀.symm
  let e : ↥(stabV (Pi.single (0 : Fin 4) 1)) ≃* ↥(stabV x) :=
    MulAction.stabilizerEquivStabilizer hx'
  let c : ↥(stabV (Pi.single (0 : Fin 4) 1)) ≃* ↥ptStab :=
    MulEquiv.subgroupCongr close16_stabV_single
  let Φ : ↥(stabV x) →* ↥ptStab :=
    (c : ↥(stabV (Pi.single (0 : Fin 4) 1)) →* ↥ptStab).comp
      (e.symm : ↥(stabV x) →* ↥(stabV (Pi.single (0 : Fin 4) 1)))
  have hΦ : Function.Surjective Φ :=
    (MulEquiv.surjective c).comp (MulEquiv.surjective e.symm)
  obtain ⟨f₀, hf₀surj, hf₀p, hf₀card⟩ := close16_ptStab_quot
  have hf : Function.Surjective (f₀.comp Φ) := hf₀surj.comp hΦ
  have hG : Nat.card ↥(stabV x) = 1344 := card_stabV_four hx
  exact ⟨f₀.comp Φ, hf, close16_ker_isPGroup hf hG, close16_card_ker_of_surj hf hG⟩

theorem close16_sl4_stab_opp {x : Fin 4 → ZMod 2} (hx : x ≠ 0) :
    Opp 3 (stabV x) = stabV x := by
  obtain ⟨g₀, hg₀⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.exists_mulVec_eq
    (v := Pi.single (0 : Fin 4) 1) (w := x) (by decide) hx
  have hx' : x = g₀ • (Pi.single (0 : Fin 4) 1) := by
    rw [smul_eq_mulVec']; exact hg₀.symm
  have hstab : stabV x = CFSG.RankThree.PartOne.conjBy g₀ (stabV (Pi.single (0 : Fin 4) 1)) := by
    rw [hx']
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g₀ (Pi.single (0 : Fin 4) 1)
  calc Opp 3 (stabV x)
      = Opp 3 (CFSG.RankThree.PartOne.conjBy g₀ (stabV (Pi.single (0 : Fin 4) 1))) := by
        rw [hstab]
    _ = CFSG.RankThree.PartOne.conjBy g₀ (Opp 3 (stabV (Pi.single (0 : Fin 4) 1))) :=
        CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy 3 g₀
          (stabV (Pi.single (0 : Fin 4) 1))
    _ = CFSG.RankThree.PartOne.conjBy g₀ (Opp 3 ptStab) := by rw [close16_stabV_single]
    _ = CFSG.RankThree.PartOne.conjBy g₀ ptStab := by rw [close16_ptStab_opp]
    _ = CFSG.RankThree.PartOne.conjBy g₀ (stabV (Pi.single (0 : Fin 4) 1)) := by
        rw [close16_stabV_single]
    _ = stabV x := hstab.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
