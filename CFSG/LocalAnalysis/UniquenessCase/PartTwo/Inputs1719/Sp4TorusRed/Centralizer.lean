module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.PointStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.LeviStab
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusRegular
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

def torusDiagSp4 (s : Fin 2 → Kˣ) : Fin 2 ⊕ Fin 2 → K :=
  Sum.elim (fun i => (s i : K)) fun i => (((s i)⁻¹ : Kˣ) : K)

omit [Finite K] [CharP K 2] in
theorem spMat_torusHom_diag (s : Fin 2 → Kˣ) :
    (((torusHom s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.diagonal (torusDiagSp4 s) :=
  coe_torusHom s

omit [Finite K] [CharP K 2] in
theorem sp4_entry_eq_zero_of_commute_torusHom {s : Fin 2 → Kˣ} {x : StatedSp 2 K}
    (h : x * torusHom s = torusHom s * x) {k j : Fin 2 ⊕ Fin 2}
    (hkj : torusDiagSp4 s k ≠ torusDiagSp4 s j) : (spMat x) k j = 0 := by
  have hcomm : Matrix.diagonal (torusDiagSp4 s) * (spMat x) =
      (spMat x) * Matrix.diagonal (torusDiagSp4 s) := by
    have h' := congrArg (fun z : StatedSp 2 K => spMat z) h
    simp only [coe_mul_statedSp, spMat_torusHom_diag] at h'
    exact h'.symm
  exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm hkj

omit [Finite K] [CharP K 2] in
theorem sp4_mulVec_single_of_isPermSp {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : TorusQS.IsPermSp n π) (j : Fin 2 ⊕ Fin 2) :
    (spMat n) *ᵥ Pi.single j 1 = Pi.single (π j) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  change (spMat n) i j = (Pi.single (π j) (1 : K) : Fin 2 ⊕ Fin 2 → K) i
  rw [hn, Pi.single_apply]

omit [Finite K] [CharP K 2] in
theorem sp4_mulVec_single_of_commute_torusHom {s : Fin 2 → Kˣ} {x : StatedSp 2 K}
    (h : x * torusHom s = torusHom s * x) {j : Fin 2 ⊕ Fin 2}
    (huniq : ∀ k, k ≠ j → torusDiagSp4 s k ≠ torusDiagSp4 s j) :
    (spMat x) *ᵥ Pi.single j 1 = (spMat x) j j • Pi.single j 1 := by
  ext k
  rw [Matrix.mulVec_single_one, Pi.smul_apply]
  by_cases hk : k = j
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, smul_zero]
    change (spMat x) k j = 0
    exact sp4_entry_eq_zero_of_commute_torusHom h (huniq k hk)

omit [Finite K] in
theorem sp4_eq_one_of_eq_inv_charTwo {u : Kˣ} (h : u = u⁻¹) : u = 1 := by
  rcases (Units.inv_eq_self_iff u).mp h.symm with h1 | h1
  · exact h1
  · rw [h1]
    exact Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq])

omit [Finite K] in
theorem sp4_diag_ne_inl_one {s : Fin 2 → Kˣ} (h0 : s 0 = 1) (h1 : s 1 ≠ 1)
    {k : Fin 2 ⊕ Fin 2} (hk : k ≠ Sum.inl 1) :
    torusDiagSp4 s k ≠ torusDiagSp4 s (Sum.inl 1) := by
  have h1K : (1 : K) ≠ (s 1 : K) := fun h => h1 (Units.ext h.symm)
  have hinv : (s 1)⁻¹ ≠ s 1 := fun h => h1 (sp4_eq_one_of_eq_inv_charTwo h.symm)
  have hinvK : (((s 1)⁻¹ : Kˣ) : K) ≠ (s 1 : K) := fun h => hinv (Units.ext h)
  rcases k with i | i <;> fin_cases i
  · simpa [torusDiagSp4, h0] using h1K
  · exact absurd rfl hk
  · simpa [torusDiagSp4, h0] using h1K
  · simpa [torusDiagSp4] using hinvK

omit [Finite K] in
theorem sp4_diag_ne_inl_zero {s : Fin 2 → Kˣ} (h0 : s 0 ≠ 1) (h1 : s 1 = 1)
    {k : Fin 2 ⊕ Fin 2} (hk : k ≠ Sum.inl 0) :
    torusDiagSp4 s k ≠ torusDiagSp4 s (Sum.inl 0) := by
  have h0K : (1 : K) ≠ (s 0 : K) := fun h => h0 (Units.ext h.symm)
  have hinv : (s 0)⁻¹ ≠ s 0 := fun h => h0 (sp4_eq_one_of_eq_inv_charTwo h.symm)
  have hinvK : (((s 0)⁻¹ : Kˣ) : K) ≠ (s 0 : K) := fun h => hinv (Units.ext h)
  rcases k with i | i <;> fin_cases i
  · exact absurd rfl hk
  · simpa [torusDiagSp4, h1] using h0K
  · simpa [torusDiagSp4] using hinvK
  · simpa [torusDiagSp4, h1] using h0K

omit [Finite K] [CharP K 2] in
theorem sp4_torus_le_map_conj_of_mem_normalizer {X : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ X) {n : StatedSp 2 K}
    (hn : n ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) :
    torus 2 K ≤ X.map (MulAut.conj n).toMonoidHom := by
  have hmap : (torus 2 K).map (MulAut.conj n).toMonoidHom = torus 2 K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [← hmap]
  exact Subgroup.map_mono hT

theorem mem_normalizer_torus_of_fixes_single (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {x : StatedSp 2 K} (hx : x ∈ X) (j : Fin 2 ⊕ Fin 2) {c : K}
    (hxc : (spMat x) *ᵥ Pi.single j 1 = c • Pi.single j 1) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  obtain ⟨n, π, hn, -, hπj⟩ := TorusQS.exists_isPermSp_apply_eq_inl_zero (K := K) j
  have hline : IsLinePerm π (spMat n) := isLinePerm_of_isPermSp hn
  have hnN : n ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    mem_normalizer_torus_of_isLinePerm hline
  have hTmap : torus 2 K ≤ X.map (MulAut.conj n).toMonoidHom :=
    sp4_torus_le_map_conj_of_mem_normalizer hT hnN
  have hXmap : IsRootFree (X.map (MulAut.conj n).toMonoidHom) := hX.map_conj hline
  have hy : n * x * n⁻¹ ∈ X.map (MulAut.conj n).toMonoidHom := ⟨x, hx, rfl⟩
  have hnj : (spMat n⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single j 1 := by
    have hπ' : π⁻¹ (Sum.inl 0) = j := by
      rw [← hπj]
      simp
    have hinv := sp4_mulVec_single_of_isPermSp hn.inv (Sum.inl 0)
    rwa [hπ'] at hinv
  have hyc : (spMat (n * x * n⁻¹)) *ᵥ Pi.single (Sum.inl 0) 1 =
      c • Pi.single (Sum.inl 0) 1 := by
    rw [coe_mul_statedSp, coe_mul_statedSp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hnj, hxc, Matrix.mulVec_smul, sp4_mulVec_single_of_isPermSp hn j, hπj]
  have hyN := mem_normalizer_torus_of_fixes_inl_zero hK hTmap hXmap hy hyc
  rw [show x = n⁻¹ * (n * x * n⁻¹) * n by group]
  have hinv : n⁻¹ ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    inv_mem hnN
  have h1 : n⁻¹ * (n * x * n⁻¹) ∈
      Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    mul_mem hinv hyN
  exact mul_mem h1 hnN

theorem sp4_mem_normalizer_of_commute_of_eq_one_zero (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {s : Fin 2 → Kˣ} (h0 : s 0 = 1) (ht1 : torusHom s ≠ 1)
    {x : StatedSp 2 K} (hx : x ∈ X) (hxt : x * torusHom s = torusHom s * x) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  have h1 : s 1 ≠ 1 := by
    intro h1
    apply ht1
    have hsall : s = fun _ => 1 := by
      funext i
      fin_cases i <;> simp [h0, h1]
    rw [hsall]
    show torusHom (1 : Fin 2 → Kˣ) = 1
    exact map_one (torusHom (r := 2) (k := K))
  exact mem_normalizer_torus_of_fixes_single hK hT hX hx (Sum.inl 1)
    (sp4_mulVec_single_of_commute_torusHom hxt fun k hk => sp4_diag_ne_inl_one h0 h1 hk)

theorem sp4_mem_normalizer_of_commute_of_eq_one_one (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {s : Fin 2 → Kˣ} (h0 : s 0 ≠ 1) (h1 : s 1 = 1)
    {x : StatedSp 2 K} (hx : x ∈ X) (hxt : x * torusHom s = torusHom s * x) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  exact mem_normalizer_torus_of_fixes_single hK hT hX hx (Sum.inl 0)
    (sp4_mulVec_single_of_commute_torusHom hxt fun k hk => sp4_diag_ne_inl_zero h0 h1 hk)

theorem sp4_mem_normalizer_of_commute_of_eq (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {s : Fin 2 → Kˣ} (hs : s 0 = s 1) (ht1 : torusHom s ≠ 1)
    {x : StatedSp 2 K} (hx : x ∈ X) (hxt : x * torusHom s = torusHom s * x) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  have hs1 : s 0 ≠ 1 := by
    intro h
    apply ht1
    have hsall : s = fun _ => 1 := by
      funext i
      fin_cases i
      · exact h
      · change s 1 = 1
        rw [← hs, h]
    rw [hsall]
    show torusHom (1 : Fin 2 → Kˣ) = 1
    exact map_one (torusHom (r := 2) (k := K))
  have hne : s 0 ≠ (s 0)⁻¹ := fun h => hs1 (sp4_eq_one_of_eq_inv_charTwo h)
  have hneK : (s 0 : K) ≠ (((s 0)⁻¹ : Kˣ) : K) := fun h => hne (Units.ext h)
  have hneK' : (((s 0)⁻¹ : Kˣ) : K) ≠ (s 0 : K) := fun h => hneK h.symm
  have hdiag : ∀ i : Fin 2, s i = s 0 := by
    intro i
    fin_cases i
    · rfl
    · exact hs.symm
  refine mem_normalizer_torus_of_mem_range_leviSp hK hT hX hx (mem_range_leviSp_of_blocks ?_)
  intro i j
  constructor
  · refine sp4_entry_eq_zero_of_commute_torusHom hxt ?_
    simp only [torusDiagSp4, Sum.elim_inl, Sum.elim_inr, hdiag i, hdiag j]
    exact hneK
  · refine sp4_entry_eq_zero_of_commute_torusHom hxt ?_
    simp only [torusDiagSp4, Sum.elim_inl, Sum.elim_inr, hdiag i, hdiag j]
    exact hneK'

omit [Finite K] [CharP K 2] in
theorem sp4_torusHom_eq_lam (t : Fin 2 → Kˣ) :
    torusHom t = lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)) := by
  rw [lam_sl2Diag, lam_sl2Diag, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

omit [Finite K] [CharP K 2] in
theorem sp4_conj_lam_one_sl2W_torusHom (t : Fin 2 → Kˣ) :
    lam (r := 2) 1 sl2W * torusHom t * (lam (r := 2) 1 sl2W)⁻¹ =
      lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)⁻¹) := by
  set s : StatedSp 2 K := lam (r := 2) 1 sl2W with hs
  have hc : s * lam 0 (sl2Diag (t 0)) = lam 0 (sl2Diag (t 0)) * s :=
    (commute_lam_lam (by decide) _ _).eq
  rw [sp4_torusHom_eq_lam, ← sl2W_conj_sl2Diag, map_mul, map_mul, map_inv, ← hs]
  calc s * (lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1))) * s⁻¹
      = (s * lam 0 (sl2Diag (t 0))) * lam 1 (sl2Diag (t 1)) * s⁻¹ := by
        simp only [mul_assoc]
    _ = (lam 0 (sl2Diag (t 0)) * s) * lam 1 (sl2Diag (t 1)) * s⁻¹ := by
        rw [hc]
    _ = lam 0 (sl2Diag (t 0)) * (s * lam 1 (sl2Diag (t 1)) * s⁻¹) := by
        simp only [mul_assoc]

omit [Finite K] [CharP K 2] in
theorem sp4_conj_lam_one_sl2W_torusHom_of_eq_inv {s : Fin 2 → Kˣ}
    (h : s 0 = (s 1)⁻¹) :
    lam (r := 2) 1 sl2W * torusHom s * (lam (r := 2) 1 sl2W)⁻¹ =
      torusHom (fun _ : Fin 2 => s 0) := by
  rw [sp4_conj_lam_one_sl2W_torusHom, ← h, sp4_torusHom_eq_lam]

theorem sp4_mem_normalizer_of_commute_of_eq_inv (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {s : Fin 2 → Kˣ} (hs : s 0 = (s 1)⁻¹) (ht1 : torusHom s ≠ 1)
    {x : StatedSp 2 K} (hx : x ∈ X) (hxt : x * torusHom s = torusHom s * x) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  let n : StatedSp 2 K := lam (r := 2) 1 sl2W
  have hn : TorusQS.IsPermSp n (Equiv.swap (Sum.inl 1) (Sum.inr 1)) :=
    TorusQS.isPermSp_lam_sl2W 1
  have hline : IsLinePerm (Equiv.swap (Sum.inl 1) (Sum.inr 1)) (spMat n) :=
    isLinePerm_of_isPermSp hn
  have hnN : n ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    mem_normalizer_torus_of_isLinePerm hline
  have hXmap : IsRootFree (X.map (MulAut.conj n).toMonoidHom) := hX.map_conj hline
  have hTmap := sp4_torus_le_map_conj_of_mem_normalizer hT hnN
  have hxmap : n * x * n⁻¹ ∈ X.map (MulAut.conj n).toMonoidHom := ⟨x, hx, rfl⟩
  have hconjt : n * torusHom s * n⁻¹ = torusHom (fun _ : Fin 2 => s 0) :=
    sp4_conj_lam_one_sl2W_torusHom_of_eq_inv hs
  have hxt' : (n * x * n⁻¹) * torusHom (fun _ : Fin 2 => s 0) =
      torusHom (fun _ : Fin 2 => s 0) * (n * x * n⁻¹) := by
    rw [← hconjt]
    calc (n * x * n⁻¹) * (n * torusHom s * n⁻¹)
        = n * (x * torusHom s) * n⁻¹ := by group
      _ = n * (torusHom s * x) * n⁻¹ := by rw [hxt]
      _ = (n * torusHom s * n⁻¹) * (n * x * n⁻¹) := by group
  have ht1' : torusHom (fun _ : Fin 2 => s 0) ≠ 1 := by
    intro h
    apply ht1
    have h' : n⁻¹ * torusHom (fun _ : Fin 2 => s 0) * n = 1 := by
      rw [h]
      group
    rw [← hconjt] at h'
    simpa [mul_assoc] using h'
  have hcase := sp4_mem_normalizer_of_commute_of_eq hK hTmap hXmap (s := fun _ => s 0)
    rfl ht1' hxmap hxt'
  rw [show x = n⁻¹ * (n * x * n⁻¹) * n by group]
  have hinv : n⁻¹ ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    inv_mem hnN
  have h1 : n⁻¹ * (n * x * n⁻¹) ∈
      Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    mul_mem hinv hcase
  exact mul_mem h1 hnN

theorem mem_normalizer_torus_of_commute (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {t : StatedSp 2 K} (ht : t ∈ torus 2 K) (ht1 : t ≠ 1) {x : StatedSp 2 K} (hx : x ∈ X)
    (hxt : x * t = t * x) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  obtain ⟨s, rfl⟩ := ht
  by_cases h0 : s 0 = 1
  · exact sp4_mem_normalizer_of_commute_of_eq_one_zero hK hT hX h0 ht1 hx hxt
  by_cases h1 : s 1 = 1
  · exact sp4_mem_normalizer_of_commute_of_eq_one_one hK hT hX h0 h1 hx hxt
  by_cases h01 : s 0 = s 1
  · exact sp4_mem_normalizer_of_commute_of_eq hK hT hX h01 ht1 hx hxt
  by_cases h01' : s 0 = (s 1)⁻¹
  · exact sp4_mem_normalizer_of_commute_of_eq_inv hK hT hX h01' ht1 hx hxt
  · exact Subgroup.le_normalizer (mem_torus_of_commute_torusHom_sp4
      (torusHom_diag_injective_sp4 h0 h1 h01 h01') hxt)

theorem mem_normalizer_torus_of_inf_ne_bot (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {x : StatedSp 2 K} (hx : x ∈ X)
    (hne : torus 2 K ⊓ (torus 2 K).map (MulAut.conj x).toMonoidHom ≠ ⊥) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _, hncard⟩ := FiniteField.card K 2
  have hcardK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hncard]
  have hoddK : Odd (Nat.card K - 1) := by
    rw [hcardK]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, ne_of_gt n.pos⟩) odd_one
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have htT : (t : StatedSp 2 K) ∈ torus 2 K := (Subgroup.mem_inf.mp t.2).1
  have htmap : (t : StatedSp 2 K) ∈
      (torus 2 K).map (MulAut.conj x).toMonoidHom := (Subgroup.mem_inf.mp t.2).2
  have ht1' : (t : StatedSp 2 K) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have : IsMulCommutative ↥(torus 2 K) :=
    Subgroup.range_isMulCommutative (torusHom (r := 2) (k := K))
  have hmapX : (torus 2 K).map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    show x * t₀ * x⁻¹ ∈ X
    exact X.mul_mem (X.mul_mem hx (hT ht₀)) (X.inv_mem hx)
  have hle : (torus 2 K).map (MulAut.conj x).toMonoidHom ≤ torus 2 K := by
    rintro y hy
    have hyX : y ∈ X := hmapX hy
    have hcomm : y * (t : StatedSp 2 K) = (t : StatedSp 2 K) * y :=
      Subgroup.mul_comm_of_mem_isMulCommutative
        ((torus 2 K).map (MulAut.conj x).toMonoidHom) hy htmap
    have hyN := mem_normalizer_torus_of_commute hK hT hX htT ht1' hyX hcomm
    have hodd : Odd (orderOf y) := by
      obtain ⟨t₀, ht₀, rfl⟩ := hy
      change Odd (orderOf ((MulAut.conj x) t₀))
      rw [MulEquiv.orderOf_eq (MulAut.conj x) t₀]
      obtain ⟨s, rfl⟩ := ht₀
      rw [orderOf_injective (torusHom (r := 2) (k := K))
        (torusHom_injective (r := 2) (k := K))]
      have hdvd : orderOf s ∣ (Nat.card K - 1) ^ 2 := by
        have h1 : orderOf s ∣ Nat.card (Fin 2 → Kˣ) := orderOf_dvd_natCard s
        have h2 : Nat.card (Fin 2 → Kˣ) = (Nat.card K - 1) ^ 2 := by
          rw [Nat.card_fun, Nat.card_units, Nat.card_fin]
        rwa [h2] at h1
      by_contra hoddneg
      rw [Nat.not_odd_iff_even] at hoddneg
      exact (hoddK.pow (n := 2)).not_two_dvd_nat (hoddneg.two_dvd.trans hdvd)
    exact mem_torus_of_mem_normalizer_of_odd hK hyN hodd
  have hcard : Nat.card (torus 2 K) ≤
      Nat.card ((torus 2 K).map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective]
  have heq : (torus 2 K).map (MulAut.conj x).toMonoidHom = torus 2 K :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
