module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.Mathlib.GroupTheory.GL3Monomial
import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Nilpotent.Lemmas

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open scoped Matrix
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single vecElt_single_one)

private noncomputable def coord {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) (i : Fin 3) : Fin 3 → ZMod 3 :=
  Classical.choose (h.settingCore.mem_torG.mp
    ((Subgroup.mem_normalizer_iff.mp x.2 (GGFF.zs z i)).mp (by
      rw [← vecElt_single_one (z := GGFF.zs z) i]
      exact GGFF.vecElt_mem_tor (GGFF.zs z) (Pi.single i 1))))

private theorem coord_spec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) (i : Fin 3) :
    vecElt (GGFF.zs z) (coord h x i) = (x : G) * GGFF.zs z i * (x : G)⁻¹ :=
  (Classical.choose_spec (h.settingCore.mem_torG.mp
    ((Subgroup.mem_normalizer_iff.mp x.2 (GGFF.zs z i)).mp (by
      rw [← vecElt_single_one (z := GGFF.zs z) i]
      exact GGFF.vecElt_mem_tor (GGFF.zs z) (Pi.single i 1))))).symm

private noncomputable def glMat {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun j i => coord h x i j

private theorem glMat_mulVec_single {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) (i : Fin 3) :
    glMat h x *ᵥ Pi.single i 1 = coord h x i := by
  rw [Matrix.mulVec_single_one]
  rfl

private theorem vecElt_add_three {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (a c d : Fin 3 → ZMod 3) :
    vecElt (GGFF.zs z) (a + c + d) =
      vecElt (GGFF.zs z) a * vecElt (GGFF.zs z) c * vecElt (GGFF.zs z) d := by
  rw [GGFF.vecElt_add h.settingCore.zs_pow h.settingCore.zs_comm,
    GGFF.vecElt_add h.settingCore.zs_pow h.settingCore.zs_comm]

private theorem vecElt_nsmul {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (m : ℕ) (w : Fin 3 → ZMod 3) :
    vecElt (GGFF.zs z) (m • w) = vecElt (GGFF.zs z) w ^ m := by
  induction m with
  | zero => simp [GGFF.vecElt_zero]
  | succ m ih =>
      rw [succ_nsmul, GGFF.vecElt_add h.settingCore.zs_pow h.settingCore.zs_comm, ih, pow_succ]

private theorem vecElt_zsmul {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (c : ZMod 3) (w : Fin 3 → ZMod 3) :
    vecElt (GGFF.zs z) (c • w) = vecElt (GGFF.zs z) w ^ c.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, vecElt_nsmul h]

private theorem glMat_vecElt {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) (v : Fin 3 → ZMod 3) :
    vecElt (GGFF.zs z) (glMat h x *ᵥ v) =
      (x : G) * vecElt (GGFF.zs z) v * (x : G)⁻¹ := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i 1 := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Pi.single_eq_of_ne' hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hlin : glMat h x *ᵥ v = ∑ i : Fin 3, v i • coord h x i := by
    conv_lhs => rw [hv]
    rw [← Matrix.mulVecLin_apply, map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply, glMat_mulVec_single]
  rw [hlin, Fin.sum_univ_three, vecElt_add_three h, vecElt_zsmul h, vecElt_zsmul h,
    vecElt_zsmul h, coord_spec, coord_spec, coord_spec]
  conv_rhs => rw [← MulAut.conj_apply]
  simp only [vecElt, map_mul, map_pow, MulAut.conj_apply]

private theorem glMat_mul {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x y : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) :
    glMat h (x * y) = glMat h x * glMat h y := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [glMat_mulVec_single, ← Matrix.mulVec_mulVec, glMat_mulVec_single]
  apply GGFF.vecElt_injective h.settingCore.zs_pow h.settingCore.zs_comm h.settingCore.inj'
  rw [coord_spec h (x * y) i, glMat_vecElt h x (coord h y i), coord_spec h y i]
  simp only [Subgroup.coe_mul]
  group

private theorem glMat_one {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    glMat h 1 = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [glMat_mulVec_single, Matrix.one_mulVec]
  apply GGFF.vecElt_injective h.settingCore.zs_pow h.settingCore.zs_comm h.settingCore.inj'
  rw [coord_spec h 1 i, vecElt_single_one]
  simp

private theorem glMat_mul_inv {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) :
    glMat h x * glMat h x⁻¹ = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, glMat_mulVec_single, Matrix.one_mulVec]
  apply GGFF.vecElt_injective h.settingCore.zs_pow h.settingCore.zs_comm h.settingCore.inj'
  rw [glMat_vecElt h x (coord h x⁻¹ i), coord_spec h x⁻¹ i, vecElt_single_one]
  simp only [Subgroup.coe_inv]
  group

private theorem glMat_inv_mul {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) :
    glMat h x⁻¹ * glMat h x = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, glMat_mulVec_single, Matrix.one_mulVec]
  apply GGFF.vecElt_injective h.settingCore.zs_pow h.settingCore.zs_comm h.settingCore.inj'
  rw [glMat_vecElt h x⁻¹ (coord h x i), coord_spec h x i, vecElt_single_one]
  simp only [Subgroup.coe_inv]
  group

private noncomputable def glHom {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    Subgroup.normalizer ((bOne z : Subgroup G) : Set G) →*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) where
  toFun x := ⟨glMat h x, glMat h x⁻¹, glMat_mul_inv h x, glMat_inv_mul h x⟩
  map_one' := Units.ext (glMat_one h)
  map_mul' x y := Units.ext (glMat_mul h x y)

private theorem matrix_pow_p_eq_one_of_pow_prime_pow {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hp3 : 3 ≤ p) (M : Matrix (Fin 3) (Fin 3) K) (k : ℕ)
    (hMk : M ^ (p ^ k) = 1) : M ^ p = 1 := by
  have hN : (M - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right M), hMk, one_pow, sub_self]
  have hnil : IsNilpotent (M - 1) := ⟨p ^ k, hN⟩
  have hnil' : IsNilpotent (Matrix.toLin' (M - 1)) := (Matrix.isNilpotent_toLin'_iff _).2 hnil
  have hch := IsNilpotent.charpoly_eq_X_pow_finrank hnil'
  have hca := LinearMap.aeval_self_charpoly (Matrix.toLin' (M - 1))
  rw [hch] at hca
  have hfr : Module.finrank K (Fin 3 → K) = 3 := by simp
  rw [hfr] at hca
  simp only [map_pow, Polynomial.aeval_X] at hca
  have h3 : (M - 1) ^ 3 = 0 := by
    have h1 : Matrix.toLinAlgEquiv' (R := K) ((M - 1) ^ 3) = 0 := by
      rw [map_pow]
      exact hca
    exact (map_eq_zero_iff _ (Matrix.toLinAlgEquiv' (R := K)).injective).1 h1
  have hNp : (M - 1) ^ p = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hp3
    rw [pow_add, h3, zero_mul]
  have hMp : M ^ p = 1 := by
    have h1 : (M - 1 + 1) ^ p = (M - 1) ^ p + 1 ^ p :=
      add_pow_char_of_commute p (Commute.one_right _)
    rw [sub_add_cancel, hNp, one_pow, zero_add] at h1
    exact h1
  exact hMp

private theorem matrix_pow_three_eq_one_of_pow_three_pow
    (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (k : ℕ) (hMk : M ^ (3 ^ k) = 1) : M ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : CharP (ZMod 3) 3 := inferInstance
  exact matrix_pow_p_eq_one_of_pow_prime_pow (K := ZMod 3) (p := 3) (by norm_num) M k hMk

private def monMat (j : Fin 3 → Fin 3) (e : Fin 3 → ZMod 3) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun b i => if j i = b then e i else 0

private theorem monMat_mulVec_single (j : Fin 3 → Fin 3) (e : Fin 3 → ZMod 3) (i : Fin 3) :
    monMat j e *ᵥ Pi.single i 1 = Pi.single (j i) (e i) := by
  rw [Matrix.mulVec_single_one]
  ext b
  by_cases h : j i = b
  · subst h; simp [monMat]
  · have h' : b ≠ j i := fun hh => h hh.symm
    simp [monMat, Matrix.col, Pi.single, h, h']

private theorem monMat_pow_three_fixes_e0 :
    ∀ (j : Fin 3 → Fin 3) (e : Fin 3 → ZMod 3),
      monMat j e ^ 3 = 1 → monMat j e *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      monMat j e = 1 := by
  decide +kernel

private theorem le_normalizer_of_subgroupOf_normal {G : Type} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hN : (H.subgroupOf K).Normal) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (Subgroup.normal_subgroupOf_iff hHK).mp hN h k hh hk
  · intro hh
    have hk' : k⁻¹ ∈ K := K.inv_mem hk
    have hthis := (Subgroup.normal_subgroupOf_iff hHK).mp hN (k * h * k⁻¹) k⁻¹ hh hk'
    have hcalc : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
    rwa [hcalc] at hthis

private theorem glMat_pow {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (x : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) (k : ℕ) :
    glMat h (x ^ k) = (glMat h x) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact glMat_one h
  | succ k ih => rw [pow_succ, glMat_mul, ih, pow_succ]

private theorem range_has_monomial {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∃ g ∈ (glHom h).range, ∀ i : Fin 3,
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ Pi.single i 1 = Pi.single (σ i) (ε i) := by
  intro σ ε hε
  obtain ⟨k, hk⟩ := h.model.mono σ ε hε
  have hkNorm : (k : G) ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge ?_ ?_
    · change (Subgroup.closure (Set.range (GGFF.zs z))).map (MulAut.conj (k : G)) ≤
        Subgroup.closure (Set.range (GGFF.zs z))
      rw [Subgroup.map_le_iff_le_comap]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      have hki : (k : G) * GGFF.zs z i * (k : G)⁻¹ = GGFF.zs z (σ i) ^ (ε i).val := by
        have := congrArg (fun t : ↥L => (t : G)) (hk i)
        simpa [GGFF.zs] using this
      change (MulAut.conj (k : G)) (GGFF.zs z i) ∈
        Subgroup.closure (Set.range (GGFF.zs z))
      rw [MulAut.conj_apply, hki]
      exact (bOne z).pow_mem (Subgroup.subset_closure ⟨σ i, rfl⟩) _
    · exact (Subgroup.card_map_of_injective (MulAut.conj (k : G)).injective).ge
  refine ⟨glHom h ⟨k, hkNorm⟩, ⟨⟨k, hkNorm⟩, rfl⟩, ?_⟩
  intro i
  change glMat h ⟨k, hkNorm⟩ *ᵥ Pi.single i 1 = Pi.single (σ i) (ε i)
  rw [glMat_mulVec_single]
  apply GGFF.vecElt_injective h.settingCore.zs_pow h.settingCore.zs_comm h.settingCore.inj'
  rw [coord_spec h ⟨k, hkNorm⟩ i, vecElt_single]
  have := congrArg (fun t : ↥L => (t : G)) (hk i)
  simpa [GGFF.zs] using this

private theorem not_nine_dvd_range {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {S : Subgroup G}
    (hS : IsPGroup 3 S) (hmax : ∀ R : Subgroup G, IsPGroup 3 R → S ≤ R → R = S)
    (hSN : S ≤ Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) {g : G} (hgS : g ∈ S)
    (hSg : ∀ x ∈ S, ∃ k : ℕ, ∀ y ∈ bOne z, x * y * x⁻¹ = g ^ k * y * (g ^ k)⁻¹) :
    ¬ 9 ∣ Nat.card (glHom h).range := by
  classical
  intro h9dvd
  have hS0 := h.settingCore
  let NN : Subgroup G := Subgroup.normalizer ((bOne z : Subgroup G) : Set G)
  have hSN' : S ≤ NN := hSN
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 3 S NN := by
    refine ⟨⟨S.subgroupOf NN, ?_, ?_⟩, ?_⟩
    · exact hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSN').symm
    · intro R hR hSR
      have hRmap : IsPGroup 3 (R.map NN.subtype) := hR.map NN.subtype
      have hle : S ≤ R.map NN.subtype := by
        calc S = (S.subgroupOf NN).map NN.subtype := by
              rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSN']
          _ ≤ R.map NN.subtype := Subgroup.map_mono hSR
      have hRmapS : R.map NN.subtype = S := hmax _ hRmap hle
      refine le_antisymm ?_ hSR
      intro x hx
      have hx' : (x : G) ∈ R.map NN.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hRmapS] at hx'
      exact hx'
    · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSN']
  let C : Subgroup G := (glHom h).ker.map NN.subtype
  have hCN : C ≤ NN := Subgroup.map_subtype_le _
  have hCsub : C.subgroupOf NN = (glHom h).ker :=
    Subgroup.comap_map_eq_self_of_injective NN.subtype_injective _
  have hCnormal : (C.subgroupOf NN).Normal := by rw [hCsub]; infer_instance
  have hNC : NN ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_subgroupOf_normal hCN hCnormal
  have hSylC : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ C) C :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hSylN hCN hNC
  have hcardS : Nat.card S = 3 ^ (Nat.card NN).factorization 3 :=
    CFSG.ABGLocalTools.IsSylowOf.card_eq hSylN
  have hcardSC : Nat.card ↥(S ⊓ C) = 3 ^ (Nat.card C).factorization 3 :=
    CFSG.ABGLocalTools.IsSylowOf.card_eq hSylC
  have hcardC : Nat.card C = Nat.card (glHom h).ker :=
    Subgroup.card_map_of_injective NN.subtype_injective
  have hNY : Nat.card (glHom h).ker * Nat.card (glHom h).range = Nat.card NN :=
    Subgroup.card_ker_mul_card_range (glHom h)
  let φS : S →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) :=
    (glHom h).comp (Subgroup.inclusion hSN')
  have hmapker : φS.ker.map S.subtype = S ⊓ C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨y.2, Subgroup.mem_map.mpr ⟨⟨(y : G), hSN' y.2⟩, hy, rfl⟩⟩
    · rintro ⟨hxS, hxC⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxS⟩, ?_, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxC
      show φS ⟨x, hxS⟩ = 1
      change glHom h ⟨x, hSN' hxS⟩ = 1
      have hyl : (⟨x, hSN' hxS⟩ : NN) = y := Subtype.ext hyx.symm
      rw [hyl]
      exact hy
  have hkerS : Nat.card φS.ker = Nat.card ↥(S ⊓ C) := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective, hmapker]
  have hPY : φS.range ≤ (glHom h).range := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨(x : G), hSN' x.2⟩, rfl⟩
  have hSP : Nat.card φS.ker * Nat.card φS.range = Nat.card S :=
    Subgroup.card_ker_mul_card_range φS
  have hPle3 : Nat.card φS.range ≤ 3 := by
    let gS : S := ⟨g, hgS⟩
    have hcyc : φS.range ≤ Subgroup.zpowers (φS gS) := by
      rintro y ⟨x, rfl⟩
      obtain ⟨k, hk⟩ := hSg (x : G) x.2
      have hmat : glMat h ⟨(x : G), hSN' x.2⟩ =
          (glMat h ⟨g, hSN' hgS⟩) ^ k := by
        rw [← glMat_pow h ⟨g, hSN' hgS⟩ k]
        apply Matrix.ext_of_mulVec_single
        intro i
        rw [glMat_mulVec_single, glMat_mulVec_single]
        apply GGFF.vecElt_injective hS0.zs_pow hS0.zs_comm hS0.inj'
        rw [coord_spec h ⟨(x : G), hSN' x.2⟩ i, coord_spec h (⟨g, hSN' hgS⟩ ^ k) i,
          Subgroup.coe_pow]
        exact hk (GGFF.zs z i) (Subgroup.subset_closure ⟨i, rfl⟩)
      have hφx : φS x = (φS gS) ^ k := by
        apply Units.ext
        change glMat h ⟨(x : G), hSN' x.2⟩ = (glMat h ⟨g, hSN' hgS⟩) ^ k
        exact hmat
      rw [hφx]
      exact Subgroup.npow_mem_zpowers _ _
    obtain ⟨e, he⟩ := hS gS
    have hpow : (φS gS) ^ (3 ^ e) = 1 := by
      rw [← map_pow, he, map_one]
    have hg3 : (φS gS) ^ 3 = 1 := by
      apply Units.ext
      change (glMat h ⟨g, hSN' hgS⟩) ^ 3 = 1
      have h1 : (glMat h ⟨g, hSN' hgS⟩) ^ (3 ^ e) = 1 := by
        have hcoe : ((φS gS : Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) :
            Matrix (Fin 3) (Fin 3) (ZMod 3)) = glMat h ⟨g, hSN' hgS⟩ := rfl
        have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) =>
          (u : Matrix (Fin 3) (Fin 3) (ZMod 3))) hpow
        rw [Units.val_pow_eq_pow_val, hcoe, Units.val_one] at this
        exact this
      exact matrix_pow_three_eq_one_of_pow_three_pow _ e h1
    have horder : orderOf (φS gS) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    calc Nat.card φS.range ≤ Nat.card (Subgroup.zpowers (φS gS)) :=
          Subgroup.card_le_of_le hcyc
      _ = orderOf (φS gS) := Nat.card_zpowers _
      _ ≤ 3 := Nat.le_of_dvd (by norm_num) horder
  have hfact : (Nat.card (glHom h).ker).factorization 3 +
      (Nat.card (glHom h).range).factorization 3 = (Nat.card NN).factorization 3 := by
    rw [← hNY, Nat.factorization_mul (Nat.card_pos (α := (glHom h).ker)).ne'
      (Nat.card_pos (α := (glHom h).range)).ne', Finsupp.add_apply]
  set a := (Nat.card C).factorization 3 with ha
  set bb := (Nat.card (glHom h).range).factorization 3 with hbb
  have hfact2 : (Nat.card (glHom h).ker).factorization 3 + bb = (Nat.card NN).factorization 3 := by
    rw [hbb]; exact hfact
  have hSval : Nat.card S = 3 ^ (a + bb) := by
    rw [hcardS]
    congr 1
    rw [← hfact2, ha, hcardC]
  have hPval : Nat.card φS.range = 3 ^ bb := by
    have h1 : 3 ^ a * Nat.card φS.range = Nat.card S := by
      rw [← hcardSC, ← hkerS]
      exact hSP
    rw [hSval, pow_add] at h1
    exact Nat.mul_left_cancel (pow_pos (by norm_num) a) h1
  have hble : 3 ^ bb ≤ 3 := by
    rw [hPval] at hPle3
    exact hPle3
  have hb1 : bb ≤ 1 := by
    have h : 3 ^ bb ≤ 3 ^ 1 := by simpa using hble
    exact (pow_le_pow_iff_right₀ (show (1 : ℕ) < 3 by norm_num)).mp h
  have hb2 : 2 ≤ bb := by
    have hn : Nat.card (glHom h).range ≠ 0 := (Nat.card_pos (α := (glHom h).range)).ne'
    have h9' : 3 ^ 2 ∣ Nat.card (glHom h).range := by
      have h : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h]
      exact h9dvd
    have := (Nat.prime_three.pow_dvd_iff_le_factorization hn).mp h9'
    simpa [hbb] using this
  omega

theorem centralizes_bOne_of_fixes_z0 {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {S : Subgroup G}
    (hS : IsPGroup 3 S) (hmax : ∀ R : Subgroup G, IsPGroup 3 R → S ≤ R → R = S)
    (hSN : S ≤ Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) {g : G} (hgS : g ∈ S)
    (hSg : ∀ x ∈ S, ∃ k : ℕ, ∀ y ∈ bOne z, x * y * x⁻¹ = g ^ k * y * (g ^ k)⁻¹) {d : G}
    (hd : d ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G))
    (hd3 : IsPGroup 3 (Subgroup.zpowers d)) (hdz : d * GGFF.zs z 0 = GGFF.zs z 0 * d) :
    ∀ y ∈ bOne z, d * y * d⁻¹ = y := by
  classical
  have hS0 := h.settingCore
  have h9 := not_nine_dvd_range h hS hmax hSN hgS hSg
  have hmono : ∀ i : Fin 3, ∃ j : Fin 3, ∃ e : ZMod 3,
      glMat h ⟨d, hd⟩ *ᵥ Pi.single i 1 = Pi.single j e := by
    intro i
    have := CFSG.GL3Monomial.exists_mulVec_single_eq (glHom h).range (range_has_monomial h) h9
      (g := glHom h ⟨d, hd⟩) ⟨⟨d, hd⟩, rfl⟩ i
    simpa [glHom] using this
  choose j e hje using hmono
  have hMeq : glMat h ⟨d, hd⟩ = monMat j e := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [monMat_mulVec_single]
    exact hje i
  have h3 : (glMat h ⟨d, hd⟩) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hd3 ⟨d, Subgroup.mem_zpowers d⟩
    have hkG : d ^ (3 ^ k) = 1 := by
      have := congrArg (fun x : ↥(Subgroup.zpowers d) => (x : G)) hk
      simpa using this
    have hpow : (glHom h ⟨d, hd⟩) ^ (3 ^ k) = 1 := by
      rw [← map_pow]
      rw [show (⟨d, hd⟩ : Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) ^ (3 ^ k) = 1 from
        Subtype.ext hkG, map_one]
    have h1 : (glMat h ⟨d, hd⟩) ^ (3 ^ k) = 1 := by
      have hcoe : ((glHom h ⟨d, hd⟩ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)) = glMat h ⟨d, hd⟩ := rfl
      have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 3) (ZMod 3) =>
        (u : Matrix (Fin 3) (Fin 3) (ZMod 3))) hpow
      rw [Units.val_pow_eq_pow_val, hcoe, Units.val_one] at this
      exact this
    exact matrix_pow_three_eq_one_of_pow_three_pow _ k h1
  have h0 : glMat h ⟨d, hd⟩ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [glMat_mulVec_single]
    apply GGFF.vecElt_injective hS0.zs_pow hS0.zs_comm hS0.inj'
    rw [coord_spec h ⟨d, hd⟩ 0, vecElt_single_one]
    change d * GGFF.zs z 0 * d⁻¹ = GGFF.zs z 0
    rw [hdz, mul_assoc, mul_inv_cancel, mul_one]
  have h3M : (monMat j e) ^ 3 = 1 := by rw [← hMeq]; exact h3
  have h0M : monMat j e *ᵥ Pi.single 0 1 = Pi.single 0 1 := by rw [← hMeq]; exact h0
  have hMone : monMat j e = 1 := monMat_pow_three_fixes_e0 j e h3M h0M
  have hdMat : glMat h ⟨d, hd⟩ = 1 := by rw [hMeq, hMone]
  intro y hy
  obtain ⟨v, rfl⟩ := hS0.mem_torG.mp hy
  rw [← glMat_vecElt h ⟨d, hd⟩ v, hdMat]
  simp
end CFSG.StandardType.FF81.PropOne

end
