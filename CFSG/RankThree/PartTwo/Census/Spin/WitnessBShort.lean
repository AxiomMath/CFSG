module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierBWeyl
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBTwo

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

namespace CarrierB

open TauCeti TauCeti.TypeBSpinCarrier Cliff RootData

variable {n : ℕ}

section Matrices

theorem intMap_one' (K : Type*) [Field K] :
    intMap K (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) = 1 := by
  ext a b
  simp [intMap, Matrix.one_apply]

theorem intMap_add' (K : Type*) [Field K]
    (Z W : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    intMap K (Z + W) = intMap K Z + intMap K W := by
  ext a b
  simp [intMap]

theorem isIntOp_one : IsIntOp n 1 1 := by
  unfold IsIntOp
  rw [map_one]
  exact HasIntMatrix.one

theorem IsIntOp.add' {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (h : IsIntOp n c X) (h' : IsIntOp n d Y) : IsIntOp n (c + d) (X + Y) := by
  unfold IsIntOp at *
  rw [map_add]
  exact HasIntMatrix.add h h'

noncomputable def wlMat (i : Fin (n + 1)) : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  (1 + rootIntMatrix n (.inl i)) * (1 - rootIntMatrix n (.inr i)) * (1 + rootIntMatrix n (.inl i))

noncomputable def wlInv (i : Fin (n + 1)) : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  (1 - rootIntMatrix n (.inl i)) * (1 + rootIntMatrix n (.inr i)) * (1 - rootIntMatrix n (.inl i))

theorem wlInv_mul (i : Fin (n + 1)) : wlInv i * wlMat i = 1 :=
  weyl_inv_mul ((intRootData n).sqZero i).ee ((intRootData n).sqZero i).ff

theorem isIntOp_weyl {i : Fin (n + 1)} {e f : Cl n} (he : IsIntOp n e (rootIntMatrix n (.inl i)))
    (hf : IsIntOp n f (rootIntMatrix n (.inr i))) :
    IsIntOp n ((1 + e) * (1 - f) * (1 + e)) (wlMat i) ∧
      IsIntOp n ((1 - e) * (1 + f) * (1 - e)) (wlInv i) :=
  ⟨((isIntOp_one.add' he).mul (isIntOp_one.sub hf)).mul (isIntOp_one.add' he),
    ((isIntOp_one.sub he).mul (isIntOp_one.add' hf)).mul (isIntOp_one.sub he)⟩

theorem conj_transfer {K : Type*} [Field K] {w w' c c' : Cl n}
    {W W' M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (hw : IsIntOp n w W)
    (hw' : IsIntOp n w' W') (hc : IsIntOp n c M) (hww' : w * w' = 1) (hW'W : W' * W = 1)
    (hwc : w * c = c' * w) :
    IsIntOp n c' (W * M * W') ∧ intMap K W * intMap K M = intMap K (W * M * W') * intMap K W := by
  refine ⟨((hw.mul hc).mul hw').congr (by rw [hwc, mul_assoc, hww', mul_one]), ?_⟩
  rw [← intMap_mul, ← intMap_mul, mul_assoc (W * M), hW'W, mul_one]

theorem intMap_bracket (K : Type*) [Field K]
    {X Y Z : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (h : X * Y - Y * X = Z) :
    intMap K X * intMap K Y - intMap K Y * intMap K X = intMap K Z := by
  rw [← intMap_mul, ← intMap_mul, ← intMap_sub', h]

theorem intMap_sandwich (K : Type*) [Field K]
    {X Y Z : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} (h : Y * X * Y = Z) :
    intMap K Y * intMap K X * intMap K Y = intMap K Z := by
  rw [← intMap_mul, ← intMap_mul, h]

end Matrices

section Group

variable {K : Type} [Field K] {σ : K →+* K} {F : (rootData n K).G →* (rootData n K).G}

noncomputable abbrev nu (i : Fin (n + 1)) : (rootData n K).G :=
  (rootData n K).x i 1 * (rootData n K).y i (-1) * (rootData n K).x i 1

theorem mat_nu (i : Fin (n + 1)) : (rootData n K).mat (nu i) = intMap K (wlMat i) := by
  rw [nu, mat_mul, mat_mul, mat_x', mat_y', one_smul, neg_one_smul, wlMat, intMap_mul,
    intMap_mul, intMap_add', intMap_sub', intMap_one', sub_eq_add_neg]
  rfl

theorem nu_mem (hF : (rootData n K).IsFrobenius σ F) (i : Fin (n + 1)) :
    nu i ∈ fixedSubgroup F := by
  have h1 : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have hm1 : (-1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).neg_mem h1
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (x_mem_fixed hF h1) (y_mem_fixed hF hm1))
    (x_mem_fixed hF h1)

theorem rootOpIn_conj {D : Subgroup (rootData n K).G} {L : Subfield K} {i : Fin (n + 1)}
    {e f c c' : Cl n} {M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (he : IsIntOp n e (rootIntMatrix n (.inl i))) (hf : IsIntOp n f (rootIntMatrix n (.inr i)))
    (hee : e * e = 0) (hff : f * f = 0) (hc : IsIntOp n c M)
    (hwc : (1 + e) * (1 - f) * (1 + e) * c = c' * ((1 + e) * (1 - f) * (1 + e)))
    (hD : ∀ g ∈ D, nu i * g * (nu i)⁻¹ ∈ D) (h : (rootData n K).RootOpIn D L (intMap K M)) :
    IsIntOp n c' (wlMat i * M * wlInv i) ∧
      (rootData n K).RootOpIn D L (intMap K (wlMat i * M * wlInv i)) := by
  obtain ⟨hw, hw'⟩ := isIntOp_weyl he hf
  obtain ⟨h1, h2⟩ := conj_transfer (K := K) hw hw' hc (weyl_mul_inv hee hff) (wlInv_mul i) hwc
  exact ⟨h1, h.conj (nu i) hD (by rw [mat_nu]; exact h2)⟩

theorem shortSimple_mem_commutator (hF : (rootData n K).IsFrobenius σ F) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hn : 2 ≤ n) {u : K}
    (hu : u ∈ RootData.fixedField σ) :
    (rootData n K).x (Fin.last n) u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n K).y (Fin.last n) u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
  obtain ⟨l, hl⟩ : ∃ l : Fin (n + 1), l.val = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have hlm : l ≠ Fin.last n := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  have hl1 : (⟨l.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  have hlt : l.val < n := by omega
  have hEl : IsIntOp n (crB n l * anB n (Fin.last n)) (rootIntMatrix n (.inl l)) := by
    have h := isIntOp_E_lt n l hlt
    rw [hl1] at h
    exact h
  have hFl : IsIntOp n (crB n (Fin.last n) * anB n l) (rootIntMatrix n (.inr l)) := by
    have h := isIntOp_F_lt n l hlt
    rw [hl1] at h
    exact h
  have hEm := isIntOp_E_last n
  have hFm := isIntOp_F_last n
  have hHn : ∀ i, ∀ g ∈ fixedSubgroup F, nu i * g * (nu i)⁻¹ ∈ fixedSubgroup F := fun i g hg =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (nu_mem hF i) hg) (Subgroup.inv_mem _ (nu_mem hF i))
  have hzw : Commute (zeta n) (weylL l (Fin.last n)) :=
    commute_weylL (zeta_cr n l) (zeta_an n l) (zeta_cr n _) (zeta_an n _)
  have h1L : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have huu : u * u ∈ RootData.fixedField σ := (RootData.fixedField σ).mul_mem hu hu
  have key : ∀ {A B : Matrix (Fin (dimension n)) (Fin (dimension n)) K}
      {g g' : (rootData n K).G} {v : K}, A * A = 0 → B * B = 0 → A * B * A = 0 →
      (rootData n K).mat g = 1 + (1 : K) • A → (rootData n K).mat g' = 1 + v • B →
      (rootData n K).mat ⁅g, g'⁆ = 1 + v • (A * B - B * A) + (v * v) • (B * A * B) := by
    intro A B g g' v hA hB hABA hg hg'
    rw [commutatorElement_def, mat_mul, mat_mul, mat_mul,
      mat_inv_one_add_smul (rootData n K) hA hg, mat_inv_one_add_smul (rootData n K) hB hg',
      hg, hg', commutator_one_add_sandwich hA hB hABA, one_mul]
  constructor
  ·
    have hwc : weylL l (Fin.last n) * (zeta n * anB n (Fin.last n)) =
        zeta n * anB n l * weylL l (Fin.last n) := by
      rw [← mul_assoc, ← hzw.eq, mul_assoc, weylL_mul_an hlm, ← mul_assoc]
    obtain ⟨hS, hSR⟩ := rootOpIn_conj (i := l) hEl hFl (EL_sq hlm) (FL_sq hlm) hFm hwc (hHn l)
      (RootOpIn.of_y (R := rootData n K) (D := fixedSubgroup F) (L := RootData.fixedField σ)
        (Fin.last n) fun v hv => y_mem_fixed hF hv)
    have hwc' : weylS n * (crB n l * anB n (Fin.last n)) =
        -(crB n l * crB n (Fin.last n)) * weylS n := by
      have hcw : Commute (crB n l) (weylS n) :=
        commute_weylS n (cr_cr (polarizationBasis n) l _) (cr_an (polarizationBasis n) hlm)
          (cr_zeta n l)
      rw [← mul_assoc, ← hcw.eq, mul_assoc, weylS_mul_an]
      noncomm_ring
    obtain ⟨hL, hLR⟩ := rootOpIn_conj (i := Fin.last n) hEm hFm (ES_sq n) (FS_sq n) hEl hwc'
      (hHn _) (RootOpIn.of_x (R := rootData n K) (D := fixedSubgroup F)
        (L := RootData.fixedField σ) l fun v hv => x_mem_fixed hF hv)
    have hL' := hL.neg.congr (neg_neg _)
    have hLR' := hLR.neg
    rw [← intMap_neg'] at hLR'
    obtain ⟨gL, hgL, hmL⟩ := hLR'.memD 1 h1L
    obtain ⟨gS, hgS, hmS⟩ := hSR.memD u hu
    have hABA := intMap_eq_of (K := K) hL' hS IsIntOp.zero (LSL_zero hlm)
    rw [intMap_zero] at hABA
    have hbr := intMap_bracket K (((hL'.mul hS).sub (hS.mul hL')).eq
      (hEm.congr (LS_bracket hlm).symm))
    have hSLS := intMap_sandwich K (((hS.mul hL').mul hS).eq
      (hFl.neg.congr (SLS_eq hlm).symm))
    rw [intMap_neg' n K (rootIntMatrix n (.inr l))] at hSLS
    have hEF : (rootData n K).E (Fin.last n) * (rootData n K).F l = 0 := by
      show intMap K _ * intMap K _ = 0
      rw [← intMap_mul, (hEm.mul hFl).eq_zero EF_zero, intMap_zero]
    have hcm := key hLR'.sq hSR.sq hABA hmL hmS
    rw [hbr, hSLS] at hcm
    have hE : intMap K (rootIntMatrix n (.inl (Fin.last n))) = (rootData n K).E (Fin.last n) :=
      rfl
    have hF' : intMap K (rootIntMatrix n (.inr l)) = (rootData n K).F l := rfl
    have hxy : (rootData n K).x (Fin.last n) u * (rootData n K).y l (-(u * u)) = ⁅gL, gS⁆ := by
      apply (rootData n K).mat_injective
      rw [hcm, hE, hF', mat_mul, mat_x', mat_y', add_mul, one_mul, mul_add, mul_one,
        smul_mul_smul, hEF, smul_zero, add_zero, smul_neg, neg_smul]
      abel
    have hyinv : ((rootData n K).y l (-(u * u)))⁻¹ = (rootData n K).y l (u * u) := by
      rw [inv_eq_iff_mul_eq_one, ← y_add, neg_add_cancel, y_zero]
    have hx : (rootData n K).x (Fin.last n) u = ⁅gL, gS⁆ * (rootData n K).y l (u * u) := by
      rw [← hyinv, ← hxy, mul_inv_cancel_right]
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hgL hgS)
      (long_mem_commutator hF hc hn l hlt huu).2
  ·
    have hwc : weylL l (Fin.last n) * (crB n (Fin.last n) * zeta n) =
        crB n l * zeta n * weylL l (Fin.last n) := by
      rw [← mul_assoc, weylL_mul_cr hlm, mul_assoc, ← hzw.eq, ← mul_assoc]
    have hwc' : weylS n * (crB n (Fin.last n) * anB n l) =
        -(anB n (Fin.last n) * anB n l) * weylS n := by
      have haw : Commute (anB n l) (weylS n) :=
        commute_weylS n (an_cr (polarizationBasis n) hlm.symm) (an_an (polarizationBasis n) l _)
          (an_zeta n l)
      rw [← mul_assoc, weylS_mul_cr, mul_assoc, ← haw.eq]
      noncomm_ring
    have hu' : -u ∈ RootData.fixedField σ := (RootData.fixedField σ).neg_mem hu
    obtain ⟨hS, hSR⟩ := rootOpIn_conj (i := l) hEl hFl (EL_sq hlm) (FL_sq hlm) hEm hwc (hHn l)
      (RootOpIn.of_x (R := rootData n K) (D := fixedSubgroup F) (L := RootData.fixedField σ)
        (Fin.last n) fun v hv => x_mem_fixed hF hv)
    obtain ⟨hL, hLR⟩ := rootOpIn_conj (i := Fin.last n) hEm hFm (ES_sq n) (FS_sq n) hFl hwc'
      (hHn _) (RootOpIn.of_y (R := rootData n K) (D := fixedSubgroup F)
        (L := RootData.fixedField σ) l fun v hv => y_mem_fixed hF hv)
    have hL' := hL.neg.congr (neg_neg _)
    have hLR' := hLR.neg
    rw [← intMap_neg'] at hLR'
    obtain ⟨gL, hgL, hmL⟩ := hLR'.memD 1 h1L
    obtain ⟨gS, hgS, hmS⟩ := hSR.memD (-u) hu'
    have hABA := intMap_eq_of (K := K) hL' hS IsIntOp.zero (LSL_zero' hlm)
    rw [intMap_zero] at hABA
    have hbr := intMap_bracket K (((hL'.mul hS).sub (hS.mul hL')).eq
      (hFm.neg.congr (LS_bracket' hlm).symm))
    rw [intMap_neg' n K (rootIntMatrix n (.inr (Fin.last n)))] at hbr
    have hSLS := intMap_sandwich K (((hS.mul hL').mul hS).eq
      (hEl.neg.congr (SLS_eq' hlm).symm))
    rw [intMap_neg' n K (rootIntMatrix n (.inl l))] at hSLS
    have hFE : (rootData n K).F (Fin.last n) * (rootData n K).E l = 0 := by
      show intMap K _ * intMap K _ = 0
      rw [← intMap_mul, (hFm.mul hEl).eq_zero (FE_zero hlm), intMap_zero]
    have hcm := key hLR'.sq hSR.sq hABA hmL hmS
    rw [hbr, hSLS] at hcm
    have hF' : intMap K (rootIntMatrix n (.inr (Fin.last n))) = (rootData n K).F (Fin.last n) :=
      rfl
    have hE : intMap K (rootIntMatrix n (.inl l)) = (rootData n K).E l := rfl
    have hyx : (rootData n K).y (Fin.last n) u * (rootData n K).x l (-(u * u)) = ⁅gL, gS⁆ := by
      apply (rootData n K).mat_injective
      rw [hcm, hE, hF', mat_mul, mat_y', mat_x', add_mul, one_mul, mul_add, mul_one,
        smul_mul_smul, hFE, smul_zero, add_zero]
      simp only [smul_neg, neg_smul, neg_neg, neg_mul_neg]
      abel
    have hxinv : ((rootData n K).x l (-(u * u)))⁻¹ = (rootData n K).x l (u * u) := by
      rw [inv_eq_iff_mul_eq_one, ← x_add, neg_add_cancel, x_zero]
    have hy : (rootData n K).y (Fin.last n) u = ⁅gL, gS⁆ * (rootData n K).x l (u * u) := by
      rw [← hxinv, ← hyx, mul_inv_cancel_right]
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hgL hgS)
      (long_mem_commutator hF hc hn l hlt huu).1

theorem exists_shortOp (hF : (rootData n K).IsFrobenius σ F) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hn : 2 ≤ n) (i : Fin (n + 1)) :
    ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crB n i * zeta n) M ∧ IsIntOp n (zeta n * anB n i) N ∧
      (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N) := by
  have hHn : ∀ (j : Fin (n + 1)), ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu j * g * (nu j)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j g hg =>
    conj_mem_commutator (nu_mem hF j) g hg
  refine Fin.reverseInduction ?_ (fun j ih => ?_) i
  · exact ⟨_, _, isIntOp_E_last n, isIntOp_F_last n,
      RootOpIn.of_x (Fin.last n) fun u hu => (shortSimple_mem_commutator hF hc hn hu).1,
      RootOpIn.of_y (Fin.last n) fun u hu => (shortSimple_mem_commutator hF hc hn hu).2⟩
  · obtain ⟨M, N, hM, hN, hMR, hNR⟩ := ih
    have hjt : j.castSucc.val < n := j.isLt
    have hs : (⟨j.castSucc.val + 1, by omega⟩ : Fin (n + 1)) = j.succ := Fin.ext rfl
    have hne : j.castSucc ≠ j.succ := fun h => by
      have h' := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at h'
      omega
    have hE := isIntOp_E_lt n j.castSucc hjt
    have hF' := isIntOp_F_lt n j.castSucc hjt
    rw [hs] at hE hF'
    have hzw : Commute (zeta n) (weylL j.castSucc j.succ) :=
      commute_weylL (zeta_cr n _) (zeta_an n _) (zeta_cr n _) (zeta_an n _)
    have hwM : weylL j.castSucc j.succ * (crB n j.succ * zeta n) =
        crB n j.castSucc * zeta n * weylL j.castSucc j.succ := by
      rw [← mul_assoc, weylL_mul_cr hne, mul_assoc, ← hzw.eq, ← mul_assoc]
    have hwN : weylL j.castSucc j.succ * (zeta n * anB n j.succ) =
        zeta n * anB n j.castSucc * weylL j.castSucc j.succ := by
      rw [← mul_assoc, ← hzw.eq, mul_assoc, weylL_mul_an hne, ← mul_assoc]
    obtain ⟨hM', hMR'⟩ := rootOpIn_conj hE hF' (EL_sq hne) (FL_sq hne) hM hwM (hHn _) hMR
    obtain ⟨hN', hNR'⟩ := rootOpIn_conj hE hF' (EL_sq hne) (FL_sq hne) hN hwN (hHn _) hNR
    exact ⟨_, _, hM', hN', hMR', hNR'⟩

omit [Field K] in
theorem short_anticomm (i : Fin (n + 1)) :
    crB n i * zeta n * (zeta n * anB n i) + zeta n * anB n i * (crB n i * zeta n) = 1 := by
  have hc := commute_mul_of_anticomm₂ (zeta_an n i) (zeta_cr n i)
  calc crB n i * zeta n * (zeta n * anB n i) + zeta n * anB n i * (crB n i * zeta n)
      = crB n i * (zeta n * zeta n) * anB n i + zeta n * (anB n i * crB n i) * zeta n := by
        noncomm_ring
    _ = crB n i * (zeta n * zeta n) * anB n i + anB n i * crB n i * (zeta n * zeta n) := by
        rw [hc]
        noncomm_ring
    _ = 1 := by rw [zeta_sq, mul_one, mul_one, cr_an_self]

theorem hasWitness_short_gen (hF : (rootData n K).IsFrobenius σ F) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hchar : (2 : K) = 0) (hn : 4 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  choose M N hM hN hMR hNR using exists_shortOp (K := K) hF hc (by omega)
  have h1 : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  choose gM hgMD hgM using fun i => (hMR i).memD 1 h1
  choose gN hgND hgN using fun i => (hNR i).memD 1 h1
  have hgM' : ∀ i, (rootData n K).mat (gM i) = 1 + intMap K (M i) := fun i => by
    rw [hgM, one_smul]
  have hgN' : ∀ i, (rootData n K).mat (gN i) = 1 + intMap K (N i) := fun i => by
    rw [hgN, one_smul]
  have hneg : ∀ A : Matrix (Fin (dimension n)) (Fin (dimension n)) K, -A = A := fun A => by
    ext a b
    rw [Matrix.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, hchar, zero_mul]
  have hcomm : ∀ {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ},
      IsIntOp n c X → IsIntOp n d Y → c * d = -(d * c) →
        Commute (intMap K X) (intMap K Y) := fun hc hd h => by
    show intMap K _ * intMap K _ = intMap K _ * intMap K _
    rw [← intMap_mul, ← intMap_mul, (hc.mul hd).eq ((hd.mul hc).neg.congr h.symm), intMap_neg',
      hneg]
  have hpair : ∀ i, SqZeroPair (intMap K (M i)) (intMap K (N i)) := fun i =>
    { ee := (hMR i).sq
      ff := (hNR i).sq
      efe := intMap_eq_of (hM i) (hN i) (hM i) (STS n i)
      fef := intMap_eq_of (hN i) (hM i) (hN i) (TST n i) }
  have hne : ∀ i, intMap K (M i) ≠ 0 := fun i h0 => by
    have h : intMap K (M i) * intMap K (N i) + intMap K (N i) * intMap K (M i) = 1 := by
      rw [← intMap_mul, ← intMap_mul, ← intMap_add',
        (((hM i).mul (hN i)).add' ((hN i).mul (hM i))).eq
          (isIntOp_one.congr (short_anticomm i).symm), intMap_one']
    rw [h0, zero_mul, mul_zero, add_zero] at h
    have h' := congrFun (congrFun h (vac (n := n))) (vac (n := n))
    rw [Matrix.zero_apply, Matrix.one_apply_eq] at h'
    exact zero_ne_one h'
  let J : Fin 4 → Fin (n + 1) := fun a => ⟨a.val, by omega⟩
  have hJ : ∀ a b, a ≠ b → J a ≠ J b := fun a b hab h => by
    have h' := congrArg Fin.val h
    exact hab (Fin.ext h')
  let t4 : Fin (n + 1) := ⟨4, by omega⟩
  have hJt : ∀ a, t4 ≠ J a := fun a h => by
    have h' := congrArg Fin.val h
    simp only [t4, J] at h'
    omega
  have h := RootData.three_witness_pairs (R := rootData n K) hchar (F := F)
    (X := fun a => intMap K (M (J a))) (Y := fun a => intMap K (N (J a)))
    (fun a => hpair (J a)) (fun a => hne (J a)) (fun a => gM (J a)) (fun a => gN (J a))
    (fun a => hgM' (J a)) (fun a => hgN' (J a)) (fun a => hgMD (J a)) (fun a => hgND (J a))
    (fun a b _ => hcomm (hM _) (hM _) SS_anticomm)
    (fun a b hab => hcomm (hM _) (hN _) (ST_anticomm (hJ a b hab)))
    (fun a b _ => hcomm (hN _) (hN _) TT_anticomm) (gM t4) (hgMD t4) ?_ ?_
    (fun a => (rootData n K).commute_of_mat (by
      rw [hgM, hgM]
      exact commute_one_add_smul (hcomm (hM t4) (hM (J a)) SS_anticomm) 1 1))
    (fun a => (rootData n K).commute_of_mat (by
      rw [hgM, hgN]
      exact commute_one_add_smul (hcomm (hM t4) (hN (J a)) (ST_anticomm (hJt a))) 1 1))
  · rwa [Fintype.card_fin] at h
  · apply (rootData n K).mat_injective
    have hXX : intMap K (M t4) + intMap K (M t4) = 0 := by
      nth_rewrite 1 [← hneg (intMap K (M t4))]
      exact neg_add_cancel _
    rw [pow_two, mat_mul, hgM', mat_one, mul_add, mul_one, add_mul, one_mul, (hMR t4).sq,
      add_zero, add_assoc, hXX, add_zero]
  · refine ⟨gN t4, hgND t4, fun h => hne t4 ?_⟩
    have hm := congrArg (rootData n K).mat h
    rw [mat_mul, mat_mul, hgM', hgN'] at hm
    have hXY : intMap K (M t4) * intMap K (N t4) = intMap K (N t4) * intMap K (M t4) := by
      have e1 : intMap K (M t4) * intMap K (N t4) =
          (1 + intMap K (M t4)) * (1 + intMap K (N t4)) - 1 - intMap K (M t4) -
            intMap K (N t4) := by noncomm_ring
      have e2 : intMap K (N t4) * intMap K (M t4) =
          (1 + intMap K (N t4)) * (1 + intMap K (M t4)) - 1 - intMap K (M t4) -
            intMap K (N t4) := by noncomm_ring
      rw [e1, e2, hm]
    calc intMap K (M t4) = intMap K (M t4) * intMap K (N t4) * intMap K (M t4) :=
          (hpair t4).efe.symm
      _ = intMap K (M t4) * intMap K (M t4) * intMap K (N t4) := by
          rw [mul_assoc, ← hXY, mul_assoc]
      _ = 0 := by rw [(hpair t4).ee, zero_mul]

end Group

variable (b : TypeBLieIndex)

theorem hasWitness_short (h2 : b.1.characteristic = 2) (hn : 4 ≤ b.carrierRank) :
    HasWitness b.Group 3 4 := by
  have hchar : (2 : b.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → b.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero b.1.Closure b.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := exists_unit_order_seven b h2
  exact hasWitness_short_gen (isFrobenius b) hc hchar hn

end CarrierB

end CFSG.RankThree.PartTwo.Census.Spin
