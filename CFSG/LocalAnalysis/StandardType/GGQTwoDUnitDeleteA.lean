module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitConj
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitShared
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open scoped Matrix

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

theorem qtwoDB12_pow_val_ne (hω : orderOf ω = 3) {a b : ZMod 3} (h : a ≠ b) :
    ω ^ a.val ≠ ω ^ b.val := by
  intro hab
  rw [pow_inj_mod, hω] at hab
  rw [Nat.mod_eq_of_lt a.val_lt, Nat.mod_eq_of_lt b.val_lt] at hab
  exact h (ZMod.val_injective 3 hab)

theorem qtwoDB12_permMatrix_apply {K : Type} [Field K] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ.permMatrix K i j = if j = σ i then 1 else 0 := by
  change σ.toPEquiv.toMatrix i j = if j = σ i then 1 else 0
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases h : j = σ i
  · rw [if_pos (by simpa using h.symm), if_pos h]
  · rw [if_neg (by simpa [eq_comm] using h), if_neg h]

theorem qtwoDB12_swap_apply_of_notMem {n : ℕ} {a b x : Fin n}
    (hx : x ∉ ({a, b} : Finset (Fin n))) : Equiv.swap a b x = x := by
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2

theorem qtwoDB12_permSU_mem_coordBlockSU {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ggPermSU (K := K) (f := 1) (Equiv.swap a b) ∈
      coordBlockSU K 2 1 ({a, b} : Finset (Fin n)) := by
  rw [mem_coordBlockSU_iff]
  intro p q hpq
  change (Equiv.swap a b).permMatrix K p q = (if p = q then 1 else 0)
  rw [qtwoDB12_permMatrix_apply]
  have hiff : (q = Equiv.swap a b p) ↔ p = q := by
    constructor
    · intro hq
      rcases hpq with hp | hq'
      · have h1 : Equiv.swap a b p = p := qtwoDB12_swap_apply_of_notMem hp
        rw [hq, h1]
      · have h1 : Equiv.swap a b q = q := qtwoDB12_swap_apply_of_notMem hq'
        have h2 : Equiv.swap a b q = p := by rw [hq, Equiv.swap_apply_self]
        rw [h1] at h2
        exact h2.symm
    · intro h
      rw [h]
      by_cases hq' : q ∈ ({a, b} : Finset (Fin n))
      · exfalso
        rcases hpq with hp | hq''
        · exact hp (h ▸ hq')
        · exact hq'' hq'
      · exact (qtwoDB12_swap_apply_of_notMem hq').symm
  by_cases h : p = q
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

theorem qtwoDB12_eq_one_of_mem_center_coordBlockSU {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n) {J : Finset (Fin n)} {c : Fin n}
    (hc : c ∉ J) {z : Su K 2 1 n} (hz : z ∈ Subgroup.center (Su K 2 1 n))
    (hzJ : z ∈ coordBlockSU K 2 1 J) : z = 1 := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨u, hu⟩ := CFSG.ClassicalInvolution.Phan.exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := K) (p := 2)
      (f := 1) hK') hn hz
  have h1 : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c = 1 := by
    rw [(mem_coordBlockSU_iff (K := K) (p := 2) (f := 1) (J := J)).mp hzJ c c (Or.inl hc),
      if_pos rfl]
  have h2 := CFSG.ClassicalInvolution.Phan.scalar_eq_one_of_apply_eq_one hu h1
  exact Subtype.ext (Units.ext h2)

omit [Finite G] in
theorem qtwoDB12_mem_closure_of_const (hxBs : x ∈ Bs)
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {c c0 : Fin m} (hc0 : c0 ≠ c)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1) {s : ↥Bs}
    (hconst : ∀ i ∈ Finset.univ.erase c, ∀ j ∈ Finset.univ.erase c,
      βL (Additive.ofMul s) i = βL (Additive.ofMul s) j) :
    (s : G) ∈ Subgroup.closure {x, (b' : G)} := by
  classical
  have hc0' : c0 ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hc0, Finset.mem_univ c0⟩
  let v : DVec m := βL (Additive.ofMul s)
  let a : ZMod 3 := v c0
  let m0 : ℕ := a.val
  let n0 : ℕ := (v c - a).val
  let xBs : ↥Bs := ⟨x, hxBs⟩
  have hxcoord' : βL (Additive.ofMul xBs) = fun _ => (1 : ZMod 3) := hxcoord
  have hveq : v = a • (1 : DVec m) + (v c - a) • (Pi.single c (1 : ZMod 3)) := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one, v, a]
      ring
    · have hiS : i ∈ Finset.univ.erase c := by
        rw [Finset.mem_erase]
        exact ⟨hi, Finset.mem_univ i⟩
      have hci : v i = a := hconst i hiS c0 hc0'
      rw [hci]
      simp [Pi.single_eq_of_ne hi]
  have hβ : βL (Additive.ofMul (xBs ^ m0 * b' ^ n0)) = v := by
    rw [ofMul_mul, map_add, ofMul_pow, ofMul_pow, map_nsmul,
      map_nsmul, hxcoord', hb', hveq]
    congr 1
    · funext i
      simp [m0, nsmul_eq_mul]
    · funext i
      by_cases hi : i = c
      · subst hi
        simp [n0, nsmul_eq_mul]
      · simp [hi]
  have hs_eq : s = xBs ^ m0 * b' ^ n0 := by
    have hβ' : βL (Additive.ofMul s) = βL (Additive.ofMul (xBs ^ m0 * b' ^ n0)) := by
      rw [hβ]
    exact Additive.ofMul.injective (βL.injective hβ')
  have hx_mem : x ∈ Subgroup.closure ({x, (b' : G)} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hb'_mem : (b' : G) ∈ Subgroup.closure ({x, (b' : G)} : Set G) :=
    Subgroup.subset_closure (by simp)
  rw [show (s : G) = ((xBs ^ m0 * b' ^ n0 : ↥Bs) : G) from congrArg Subtype.val hs_eq,
    Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx_mem _) (Subgroup.pow_mem _ hb'_mem _)

theorem qtwoDB12_diag_eq_of_conj_permSU (hF0 : Nat.card F0 = 4) (hm : 3 ≤ m) {i j : Fin m}
    {cfun : Fin m → F0ˣ} {u' : Su F0 2 1 m}
    (hu'mat : (u' : GL (Fin m) F0) = qTwoChartTwoThree_diag cfun *
      (ggPermSU (K := F0) (f := 1) (Equiv.swap i j) : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag cfun)⁻¹)
    (hz : u' * (ggPermSU (K := F0) (f := 1) (Equiv.swap i j))⁻¹ ∈
      Subgroup.center (Su F0 2 1 m)) : cfun i = cfun j := by
  set u : Su F0 2 1 m := ggPermSU (K := F0) (f := 1) (Equiv.swap i j)
  have hu_basis : ∀ l : Fin m, ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single l 1 = Pi.single (Equiv.swap i j l) 1 := by
    intro l
    change (Equiv.swap i j).permMatrix F0 *ᵥ Pi.single l (1 : F0) =
      Pi.single (Equiv.swap i j l) 1
    rw [Matrix.permMatrix_mulVec]
    ext r
    by_cases hr : r = Equiv.swap i j l
    · rw [hr, Function.comp_apply, Equiv.swap_apply_self, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Function.comp_apply,
        Pi.single_eq_of_ne (fun h => hr (by rw [← h, Equiv.swap_apply_self])),
        Pi.single_eq_of_ne hr]
  have hcard2 : ({i, j} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h2 : ({i, j} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard2
  have hki : k ≠ i := fun h => hk (by rw [h]; simp)
  have hkj : k ≠ j := fun h => hk (by rw [h]; simp)
  have hσk : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
  have hzu : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      (((qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag cfun)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *
        (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
    rw [show (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        ((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) by rfl]
    rw [hu'mat]
  have hdiag : ∀ l : Fin m, ((qTwoChartTwoThree_diag cfun : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single l 1 = Pi.single l ((cfun l : F0ˣ) : F0) := by
    intro l
    change Matrix.diagonal (fun i => (cfun i : F0)) *ᵥ Pi.single l (1 : F0) = _
    rw [Matrix.diagonal_mulVec_single, mul_one]
  have hdiaginv : ∀ l : Fin m, (((qTwoChartTwoThree_diag cfun)⁻¹ : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single l 1 =
        Pi.single l (((cfun l)⁻¹ : F0ˣ) : F0) := by
    intro l
    change Matrix.diagonal (fun i => (((cfun i)⁻¹ : F0ˣ) : F0)) *ᵥ Pi.single l (1 : F0) = _
    rw [Matrix.diagonal_mulVec_single, mul_one]
  have huk : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1 =
      Pi.single k 1 := by
    rw [hu_basis k, hσk]
  have huinvk : (((u : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single k 1 = Pi.single k 1 := by
    conv_lhs => rw [← huk]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hzk : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single k 1 = Pi.single k 1 := by
    rw [hzu]
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [huinvk, hdiaginv k]
    rw [show Pi.single k (((cfun k)⁻¹ : F0ˣ) : F0) =
        ((((cfun k)⁻¹ : F0ˣ)) : F0) • Pi.single k (1 : F0) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]]
    rw [Matrix.mulVec_smul, huk, Matrix.mulVec_smul, hdiag k]
    rw [show Pi.single k ((cfun k : F0ˣ) : F0) =
        (((cfun k : F0ˣ)) : F0) • Pi.single k (1 : F0) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]]
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hzk_entry : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) k k = 1 := by
    have h := congrFun hzk k
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same] at h
    exact h
  have hK' : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hF0]; norm_num
  obtain ⟨r, hr⟩ := CFSG.ClassicalInvolution.Phan.exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := F0) (p := 2)
      (f := 1) hK') hm hz
  have hz1mat : (((u' * u⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = 1 :=
    CFSG.ClassicalInvolution.Phan.scalar_eq_one_of_apply_eq_one hr hzk_entry
  have hz1 : u' * u⁻¹ = 1 := Subtype.ext (Units.ext hz1mat)
  have hu'u : u' = u := mul_inv_eq_one.mp hz1
  have huD : (u : GL (Fin m) F0) = qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag cfun)⁻¹ := by
    rw [hu'u] at hu'mat
    exact hu'mat
  have hL : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single j 1 := by
    rw [hu_basis i, Equiv.swap_apply_left]
  have hR : ((qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) *
      (qTwoChartTwoThree_diag cfun)⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single i 1 =
        Pi.single j ((((cfun i)⁻¹ : F0ˣ) : F0) * ((cfun j : F0ˣ) : F0)) := by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [hdiaginv i]
    rw [show Pi.single i (((cfun i)⁻¹ : F0ˣ) : F0) =
        ((((cfun i)⁻¹ : F0ˣ)) : F0) • Pi.single i (1 : F0) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]]
    rw [Matrix.mulVec_smul, hu_basis i, Equiv.swap_apply_left, Matrix.mulVec_smul, hdiag j]
    rw [show Pi.single j ((cfun j : F0ˣ) : F0) =
        (((cfun j : F0ˣ)) : F0) • Pi.single j (1 : F0) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]]
    rw [smul_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  have hmat : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      ((qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag cfun)⁻¹ : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) :=
    congrArg (fun g : GL (Fin m) F0 => ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) huD
  have hEq : (Pi.single j ((((cfun i)⁻¹ : F0ˣ) : F0) * ((cfun j : F0ˣ) : F0)) :
      Fin m → F0) = (Pi.single j (1 : F0) : Fin m → F0) := by
    rw [← hR, ← hL, hmat]
  have hcoord : ((((cfun i)⁻¹ : F0ˣ) : F0) * ((cfun j : F0ˣ) : F0)) = 1 := by
    have h := congrFun hEq j
    simpa using h
  have hprod : (cfun i)⁻¹ * cfun j = 1 := by
    apply Units.ext
    simpa [Units.val_mul, Units.val_one] using hcoord
  exact inv_mul_eq_one.mp hprod


theorem qtwoDB12_injective_block (hbase : QTwoUnitBase p B Bs x L ψ ε)
    {J : Finset (Fin m)} {c : Fin m} (hc : c ∉ J) :
    Function.Injective (fun u : ↥(coordBlockSU F0 2 1 J) => ψ (u : Su F0 2 1 m)) := by
  intro u v huv
  have huv' : ψ (u : Su F0 2 1 m) = ψ (v : Su F0 2 1 m) := huv
  have hz : (u : Su F0 2 1 m) * (v : Su F0 2 1 m)⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := by
    apply hbase.hyp.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv', mul_inv_cancel]
  have hzJ : (u : Su F0 2 1 m) * (v : Su F0 2 1 m)⁻¹ ∈ coordBlockSU F0 2 1 J :=
    mul_mem u.2 (inv_mem v.2)
  have h1 := qtwoDB12_eq_one_of_mem_center_coordBlockSU hbase.card_field
    (by have := hbase.hyp.four_le; omega) hc hz hzJ
  exact Subtype.ext (mul_inv_eq_one.mp h1)

theorem qtwoDB12_card_map_coordBlockSU_three (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hm : 4 ≤ m) {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Nat.card ↥((coordBlockSU F0 2 1 ({a, b, c} : Finset (Fin m))).map ψ) = 216 := by
  have hJcard : ({a, b, c} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hlt : ({a, b, c} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [hJcard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let S := coordBlockSU F0 2 1 ({a, b, c} : Finset (Fin m))
  let φ : ↥S →* G := ψ.comp S.subtype
  have hφinj : Function.Injective φ := by
    intro u v huv
    have huv' : ψ (u : Su F0 2 1 m) = ψ (v : Su F0 2 1 m) := huv
    have hz : (u : Su F0 2 1 m) * (v : Su F0 2 1 m)⁻¹ ∈ Subgroup.center (Su F0 2 1 m) := by
      apply hbase.hyp.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv', mul_inv_cancel]
    have hzS : (u : Su F0 2 1 m) * (v : Su F0 2 1 m)⁻¹ ∈ S := mul_mem u.2 (inv_mem v.2)
    have h1 := qtwoDB12_eq_one_of_mem_center_coordBlockSU hbase.card_field
      (by omega : 3 ≤ m) hd hz hzS
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hrange : φ.range = S.map ψ := by
    ext z
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(y : Su F0 2 1 m), y.2, hy⟩
    · rintro ⟨y, hy, hzy⟩
      exact ⟨⟨y, hy⟩, hzy⟩
  have hcard : Nat.card ↥(S.map ψ) = Nat.card ↥S := by
    rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj,
      Subgroup.card_top]
  calc Nat.card ↥((coordBlockSU F0 2 1 ({a, b, c} : Finset (Fin m))).map ψ)
      = Nat.card ↥(S.map ψ) := rfl
    _ = Nat.card ↥S := hcard
    _ = Nat.card (Su F0 2 1 ({a, b, c} : Finset (Fin m)).card) := natCard_coordBlockSU _
    _ = Nat.card (Su F0 2 1 3) := by rw [hJcard]
    _ = 216 := qTwoS34_card_Su_three hbase.card_field

end CFSG.StandardType.QTwo

end
