module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoFrameDefs
public import CFSG.LocalAnalysis.StandardType.FF81.OverlapLinear
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKBlocks
import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSL
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType

open Polynomial Matrix CoordSL Multiplicative CFSG.ClassicalInvolution.WeakCT
  CFSG.RankThree.CALinearPlane
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

attribute [-instance] CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace QTwoCharts

section Pos

variable {N e s d : ℕ}

@[expose] def IsPosFrame (ε : Fin N ≃ (Fin e × Fin s) ⊕ Fin d) : Prop :=
  (∀ (a : Fin e) (k : Fin s), (ε.symm (Sum.inl (a, k))).val = a.val + 2 * k.val) ∧
    ∀ j : Fin d, (ε.symm (Sum.inr j)).val = 2 * s + j.val

theorem exists_isPosFrame (he : e = 2) (hN : N = 2 * s + d) :
    ∃ ε : Fin N ≃ (Fin e × Fin s) ⊕ Fin d, IsPosFrame ε := by
  subst he
  refine ⟨(finCongr (by omega : N = s * 2 + d)).trans (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin s) (Fin 2)))
      (Equiv.refl (Fin d)))), fun a k => ?_, fun j => ?_⟩
  · show a.val + 2 * k.val = a.val + 2 * k.val
    rfl
  · show s * 2 + j.val = 2 * s + j.val
    ring

variable {ε : Fin N ≃ (Fin e × Fin s) ⊕ Fin d}

theorem IsPosFrame.val_of_inl (hε : IsPosFrame ε) {p : Fin N} {a : Fin e} {k : Fin s}
    (h : ε p = Sum.inl (a, k)) : p.val = a.val + 2 * k.val := by
  rw [← hε.1 a k, ← h, Equiv.symm_apply_apply]

theorem IsPosFrame.val_of_inr (hε : IsPosFrame ε) {p : Fin N} {j : Fin d}
    (h : ε p = Sum.inr j) : p.val = 2 * s + j.val := by
  rw [← hε.2 j, ← h, Equiv.symm_apply_apply]

theorem IsPosFrame.mem_fixS (hε : IsPosFrame ε) (he : e = 2) {Tb : Finset (Fin s)} {p : Fin N} :
    p ∈ SLNS.fixS ε Tb ↔ ∀ k ∈ Tb, ¬ (2 * k.val ≤ p.val ∧ p.val < 2 * k.val + 2) := by
  rw [SLNS.mem_fixS]
  rcases hp : ε p with ⟨a, k⟩ | j
  · have hv := hε.val_of_inl hp
    have ha : a.val < 2 := he ▸ a.isLt
    simp only [SLNS.inT, Sum.elim_inl]
    constructor
    · intro hk k' hk' hc
      have hkk : k' = k := Fin.ext (by omega)
      exact hk (hkk ▸ hk')
    · intro h hk
      exact h k hk ⟨by omega, by omega⟩
  · have hv := hε.val_of_inr hp
    simp only [SLNS.inT, Sum.elim_inr, not_false_eq_true, true_iff]
    intro k _ hc
    have := k.isLt
    omega

theorem IsPosFrame.shift {M : ℕ} {ε : Fin (M + 2) ≃ (Fin e × Fin (s + 1)) ⊕ Fin d}
    {εo : Fin M ≃ (Fin e × Fin s) ⊕ Fin d} (hε : IsPosFrame ε) (hεo : IsPosFrame εo) (q : Fin M) :
    ε ⟨q.val + 2, by omega⟩ = Sum.map (Prod.map id Fin.succ) id (εo q) := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  apply Fin.ext
  rcases hq : εo q with ⟨a, k⟩ | j
  · simp only [Sum.map_inl, Prod.map_apply, id_eq]
    rw [hε.1, Fin.val_succ, hεo.val_of_inl hq]
    ring
  · simp only [Sum.map_inr, id_eq]
    rw [hε.2, hεo.val_of_inr hq]
    ring

end Pos

section Shift

variable {M e s d : ℕ} {ε : Fin (M + 2) ≃ (Fin e × Fin (s + 1)) ⊕ Fin d}
  {εo : Fin M ≃ (Fin e × Fin s) ⊕ Fin d}

theorem block_zero_of_shift
    (hsh : ∀ q : Fin M, ε ⟨q.val + 2, by omega⟩ = Sum.map (Prod.map id Fin.succ) id (εo q))
    {p : Fin (M + 2)} (hp : p.val < 2) : ∃ a, ε p = Sum.inl (a, 0) := by
  have key : ∀ y, ε p ≠ Sum.map (Prod.map id Fin.succ) id y := by
    intro y hy
    have h1 := hsh (εo.symm y)
    rw [Equiv.apply_symm_apply, ← hy] at h1
    have h2 : (εo.symm y).val + 2 = p.val := congrArg Fin.val (ε.injective h1)
    omega
  rcases hε : ε p with ⟨a, k⟩ | j
  · refine ⟨a, ?_⟩
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · rfl
    · exact absurd hε (key (Sum.inl (a, k')))
  · exact absurd hε (key (Sum.inr j))

theorem nsCore_map_succ {F : Type} [Field F] (C : Matrix (Fin e) (Fin e) F) (k : Fin (s + 1) → ℕ)
    (u u' : (Fin e × Fin s) ⊕ Fin d) :
    SLNS.nsCore C k (Sum.map (Prod.map id Fin.succ) id u)
        (Sum.map (Prod.map id Fin.succ) id u') =
      SLNS.nsCore C (fun j => k j.succ) u u' := by
  rcases u with ⟨a, i⟩ | j <;> rcases u' with ⟨b, i'⟩ | j'
  · simp only [Sum.map_inl, Prod.map_apply, id_eq, SLNS.nsCore, fromBlocks_apply₁₁,
      blockDiagonal_apply, Fin.succ_inj]
  · simp [SLNS.nsCore]
  · simp [SLNS.nsCore]
  · simp only [Sum.map_inr, id_eq, SLNS.nsCore, fromBlocks_apply₂₂]

theorem nsSL_eq_blockSL_of_shift {F : Type} [Field F]
    (hsh : ∀ q : Fin M, ε ⟨q.val + 2, by omega⟩ = Sum.map (Prod.map id Fin.succ) id (εo q))
    {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1) (k : Fin (s + 1) → ℕ) (hk : k 0 = 0) :
    SLNS.nsSL ε hC k = blockSL F (M + 2) M 2 (by omega) (SLNS.nsSL εo hC fun j => k j.succ) := by
  have htriv : ∀ p : Fin (M + 2), p.val < 2 → QTwoBlocks.NsTriv k (ε p) := by
    intro p hp a i hai
    obtain ⟨a', ha'⟩ := block_zero_of_shift hsh hp
    rw [ha'] at hai
    cases hai
    exact hk
  apply Subtype.ext
  rw [coe_blockSL]
  ext p q
  show SLNS.nsMat ε C k p q = blockMat (M + 2) 2 (SLNS.nsMat εo C fun j => k j.succ) p q
  rw [blockMat_apply]
  have := p.isLt
  have := q.isLt
  split_ifs with hpq
  · obtain ⟨⟨hp1, hp2⟩, hq1, hq2⟩ := hpq
    have hp' : ε p = Sum.map (Prod.map id Fin.succ) id (εo ⟨p.val - 2, by omega⟩) := by
      rw [← hsh]
      exact congrArg ε (Fin.ext (show p.val = p.val - 2 + 2 by omega))
    have hq' : ε q = Sum.map (Prod.map id Fin.succ) id (εo ⟨q.val - 2, by omega⟩) := by
      rw [← hsh]
      exact congrArg ε (Fin.ext (show q.val = q.val - 2 + 2 by omega))
    simp only [SLNS.nsMat, submatrix_apply]
    rw [hp', hq', nsCore_map_succ]
  · by_cases hp : p.val < 2
    · exact QTwoBlocks.nsMat_apply_of_left ε (htriv p hp) q
    · exact QTwoBlocks.nsMat_apply_of_right ε (htriv q (by omega)) p

end Shift

theorem exists_compIndicator_eq_pow {g : (ZMod 2)[X]} [Fact (Irreducible g)]
    (hg : g ∣ cyclotomic 3 (ZMod 2)) {M s d : ℕ}
    (εo : Fin M ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin d) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ 3 = 1) (Tb : Finset (Fin s)) :
    ∃ o : ℕ, compIndicator (ZMod 2) (SLNS.fixS εo Tb) =
        ((SLNS.nsSL εo hC (SLNS.kT Tb) : Matrix (Fin M) (Fin M) (ZMod 2)) - 1) ^ o ∧
      compIndicator (ZMod 2) (SLNS.fixS εo Tb) =
        ((((SLNS.nsSL εo hC (SLNS.kT Tb))⁻¹ : SL(M, ZMod 2)) : Matrix (Fin M) (Fin M) (ZMod 2)) -
          1) ^ o := by
  have hK : ¬ 3 ∣ Nat.card (ZMod 2) - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    decide
  have hu1 := isUnit_rootMat_pow_sub Nat.prime_three hK (by decide) hg 1 (by norm_num) 1
  have hu2 := isUnit_rootMat_pow_sub Nat.prime_three hK (by decide) hg 2 (by norm_num) 1
  rw [pow_one, one_smul] at hu1
  rw [one_smul] at hu2
  obtain ⟨o₁, ho₁, h₁⟩ := SLNS.exists_pow_sub_one_eq_one hu1
  obtain ⟨o₂, ho₂, h₂⟩ := SLNS.exists_pow_sub_one_eq_one hu2
  have ho : 1 ≤ o₁ * o₂ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hinv : (SLNS.nsSL εo hC (SLNS.kT Tb))⁻¹ = SLNS.nsSL εo hC (2 • SLNS.kT Tb) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [SLNS.nsSL_mul, show SLNS.kT Tb + 2 • SLNS.kT Tb = 3 • SLNS.kT Tb by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring,
      ← SLNS.nsSL_pow, SLNS.nsSL_pow_p εo hC hCp]
  refine ⟨o₁ * o₂, ?_, ?_⟩
  · refine RestSL.compIndicator_eq_pow εo hC (SLNS.kT Tb) Tb
      (fun i hi => by simp [SLNS.kT, hi]) ho fun i hi => ?_
    rw [SLNS.kT, if_pos hi, pow_one, pow_mul, h₁, one_pow]
  · rw [hinv]
    refine RestSL.compIndicator_eq_pow εo hC (2 • SLNS.kT Tb) Tb
      (fun i hi => by simp [SLNS.kT, hi]) ho fun i hi => ?_
    rw [Pi.smul_apply, SLNS.kT, if_pos hi, smul_eq_mul, mul_one, mul_comm, pow_mul, h₂, one_pow]

end QTwoCharts

namespace GGSecFiveBPermQTwoKFrame

variable {G : Type} [Group G] {Bs K : Subgroup G} {n r m d : ℕ}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {π : Fin (r + 2) ≃ Fin n}
  {g : (ZMod 2)[X]} [Fact (Irreducible g)]
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ 3 = 1}

theorem reframe {ε : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d}
    {κ : SL(m, ZMod 2) →* G} (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (ε' : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d) :
    GGSecFiveBPermQTwoKFrame Bs K eta π ε' hC hCp
      (κ.comp (MulAut.conj (TypeA.permSL (ε.trans ε'.symm))).toMonoidHom) := by
  obtain ⟨hinj, hrange, hg, hact⟩ := hF
  have hns : ∀ k, TypeA.permSL (ε.trans ε'.symm) * SLNS.nsSL ε' hC k *
      (TypeA.permSL (ε.trans ε'.symm))⁻¹ = SLNS.nsSL ε hC k := by
    intro k
    apply Subtype.ext
    rw [FF81.coe_permSL_conj_submatrix]
    show ((SLNS.nsCore (rootMat g) k).submatrix ε' ε').submatrix (ε.trans ε'.symm)
      (ε.trans ε'.symm) = (SLNS.nsCore (rootMat g) k).submatrix ε ε
    rw [submatrix_submatrix]
    congr 1 <;> funext p <;> simp
  have hι : ∀ t, CoordSL.frameHom (κ.comp (MulAut.conj (TypeA.permSL (ε.trans ε'.symm))).toMonoidHom)
      1 ε' hC hCp t = CoordSL.frameHom κ 1 ε hC hCp t := by
    intro t
    obtain ⟨t, rfl⟩ := ofAdd.surjective t
    rw [CoordSL.frameHom_apply, CoordSL.frameHom_apply, one_mul, inv_one, mul_one, one_mul,
      mul_one]
    exact congrArg κ (hns _)
  refine ⟨hinj.comp (MulAut.conj _).injective, ?_, hg, fun b u => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj _).surjective,
      ← MonoidHom.range_eq_map, hrange]
  · rw [hι]
    exact hact b _

theorem overlap_conj_torus {M : ℕ} {ε : Fin (M + 2) ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d}
    {κ : SL(M + 2, ZMod 2) →* G} (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    {εo : Fin M ≃ (Fin (rootPB g).dim × Fin r) ⊕ Fin d}
    (hsh : ∀ q : Fin M, ε ⟨q.val + 2, by omega⟩ = Sum.map (Prod.map id Fin.succ) id (εo q))
    {x : G} (hx : x ∈ Subgroup.normalizer (Bs : Set G))
    (hxη : MulAut.congr eta (ggConjAut Bs hx) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hxN : ∀ z : SL(M, ZMod 2), ∃ z' : SL(M, ZMod 2),
      x * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹ =
        κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z'))
    (Tb : Finset (Fin r)) (z : SL(M, ZMod 2)) :
    x * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb) * z *
        (SLNS.nsSL εo hC (SLNS.kT Tb))⁻¹)) * x⁻¹ =
      κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb))) *
        (x * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹) *
          (κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb))))⁻¹ := by
  classical
  let c : Fin (r + 2) → ZMod 3 := fun j =>
    if h : 2 ≤ j.val then (if (⟨j.val - 2, by omega⟩ : Fin r) ∈ Tb then 1 else 0) else 0
  let v : Fin n → Multiplicative (ZMod 3) := fun i => ofAdd (c (π.symm i))
  have hbv : eta (eta.symm v) = v := MulEquiv.apply_symm_apply _ _
  have hbT : CoordSL.frameHom κ 1 ε hC hCp (ggSecFiveBPermQTwoCoords eta π (eta.symm v)) =
      κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb))) := by
    have hcoords : ggSecFiveBPermQTwoCoords eta π (eta.symm v) = ofAdd fun k => c k.succ := by
      apply toAdd.injective
      funext k
      simp only [ggSecFiveBPermQTwoCoords, toAdd_ofAdd, hbv, v, Equiv.symm_apply_apply]
    rw [hcoords, frameHom_ofAdd]
    congr 1
    rw [QTwoCharts.nsSL_eq_blockSL_of_shift hsh hC _ (by simp [c])]
    congr 2
    funext j
    have h2 : 2 ≤ (j.succ.succ : Fin (r + 2)).val := by simp [Fin.val_succ]
    have hj : (⟨(j.succ.succ : Fin (r + 2)).val - 2, by omega⟩ : Fin r) = j :=
      Fin.ext (by simp [Fin.val_succ])
    simp only [c, dif_pos h2, hj, SLNS.kT]
    split_ifs <;> rfl
  have hact : ∀ u, ((eta.symm v : ↥Bs) : G) * κ u * ((eta.symm v : ↥Bs) : G)⁻¹ =
      κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb))) * κ u *
        (κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb))))⁻¹ := by
    intro u
    rw [hF.2.2.2 (eta.symm v) u, hbT]
  have hxb : x * ((eta.symm v : ↥Bs) : G) * x⁻¹ = (eta.symm v : ↥Bs) := by
    have h1 : ggConjAut Bs hx (eta.symm v) = eta.symm v := by
      apply eta.injective
      funext i
      have h2 := eta_ggConjAut_apply_of_permAut hx hxη (eta.symm v) (Equiv.swap (π 0) (π 1) i)
      rw [Equiv.swap_apply_self] at h2
      rw [h2, hbv]
      show ofAdd (c (π.symm (Equiv.swap (π 0) (π 1) i))) = ofAdd (c (π.symm i))
      have hc01 : c 0 = c 1 := by simp [c]
      rcases eq_or_ne i (π 0) with rfl | h0
      · rw [Equiv.swap_apply_left, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hc01]
      · rcases eq_or_ne i (π 1) with rfl | h1
        · rw [Equiv.swap_apply_right, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hc01]
        · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    have h3 := congrArg Subtype.val h1
    rwa [ggConjAut_apply] at h3
  obtain ⟨z', hz'⟩ := hxN z
  calc x * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) (SLNS.nsSL εo hC (SLNS.kT Tb) * z *
        (SLNS.nsSL εo hC (SLNS.kT Tb))⁻¹)) * x⁻¹
      = x * (((eta.symm v : ↥Bs) : G) * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) *
          ((eta.symm v : ↥Bs) : G)⁻¹) * x⁻¹ := by
        rw [hact]
        simp only [map_mul, map_inv]
    _ = (x * ((eta.symm v : ↥Bs) : G) * x⁻¹) *
          (x * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z) * x⁻¹) *
            (x * ((eta.symm v : ↥Bs) : G) * x⁻¹)⁻¹ := by group
    _ = ((eta.symm v : ↥Bs) : G) * κ (blockSL (ZMod 2) (M + 2) M 2 (by omega) z') *
          ((eta.symm v : ↥Bs) : G)⁻¹ := by rw [hxb, hz']
    _ = _ := by rw [hact, ← hz']

end GGSecFiveBPermQTwoKFrame

end CFSG.StandardType

end
