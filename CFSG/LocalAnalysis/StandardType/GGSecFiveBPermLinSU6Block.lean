module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
import CFSG.LieType.SemisimpleCentralizers.OrderThree.BlockModel

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LieType.SemisimpleCentralizers.OrderThree
open scoped MatrixGroups commutatorElement

private theorem hypGram_mul_blockMat_mul {a k : ℕ} {K : Type} [Field K]
    (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
    (Z : Matrix (Fin a) (Fin a) K) :
    hypGram a k K * blockMat X Y Z * hypGram a k K = blockMat Z Y X := by
  ext i j
  rw [mul_hypGram_apply, hypGram_mul_apply]
  rcases i with i | k' | i <;> rcases j with j | l | j <;>
    simp [blockMat, hypPartner]

theorem exists_sl_three_of_centralizer_hypEntries_const {F : Type} [Field F] {a p : ℕ}
    (h : UnitaryFieldData 2 a F) (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {c : ZMod p} (hc : c ≠ 0) {t : hypSU h 3 0}
    (ht : ((t : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) =
      diagonal (hypEntries ζ (fun _ => c))) :
    ∃ H : Subgroup (hypSU h 3 0), Subgroup.center (hypSU h 3 0) ≤ H ∧
      Nat.card H ≤ Nat.card SL(3, F) ∧
      ⁅Subgroup.centralizer ({t} : Set (hypSU h 3 0)),
        Subgroup.centralizer ({t} : Set (hypSU h 3 0))⁆ ≤ H := by
  classical
  have hchar : CharP F 2 := h.charP
  have : NeZero p := ⟨hp.ne_zero⟩
  let lam : F := ζ ^ c.val
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (hζ.ne_zero hp.ne_zero)
  have hlam1 : lam ≠ 1 := by
    intro h1
    have hdvd : p ∣ c.val := (hζ.pow_eq_one_iff_dvd c.val).mp h1
    have hval0 : c.val ≠ 0 := fun h0 => hc ((ZMod.val_eq_zero c).mp h0)
    exact absurd (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt c)) hval0
  have hpow : lam ^ p = 1 := by
    show (ζ ^ c.val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hlamne : lam ≠ lam⁻¹ := by
    intro h1
    have hsq : lam ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel₀ hlam0
    have hcop : Nat.Coprime p 2 := (hp.odd_of_ne_two hp2).coprime_two_right
    have hrgcd : Nat.gcd p 2 = 1 := Nat.Coprime.gcd_eq_one hcop
    have h2 : lam = 1 := by
      have h3 := pow_gcd_eq_one.mpr ⟨hpow, hsq⟩
      rwa [hrgcd, pow_one] at h3
    exact hlam1 h2
  have htmat : ((t : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) =
      hypDiag 3 0 lam 0 lam⁻¹ := by
    rw [ht, hypDiag_eq_diagonal, Matrix.diagonal_eq_diagonal_iff]
    intro x
    rcases x with i | k | i
    · rfl
    · exact k.elim0
    · rfl
  have decomp : ∀ g : hypSU h 3 0,
      g ∈ Subgroup.centralizer ({t} : Set (hypSU h 3 0)) →
      ∃ X : GL (Fin 3) F, ∃ Y : GL (Fin 0) F, ∃ Z : GL (Fin 3) F,
        (g : GL (HypIndex 3 0) F) = blockDiag X Y Z ∧ Z = starInv h X := by
    intro g hg
    have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcomm : Commute (((g : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F)) (hypDiag 3 0 lam 0 lam⁻¹) := by
      rw [commute_iff_eq]
      have h1 := congrArg (fun u : hypSU h 3 0 =>
        (((u : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F))) hgt
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, htmat] at h1
      exact h1
    obtain ⟨X, Y, Z, hgX, -, hZ⟩ := exists_blockDiag_of_mem_hypSU_of_commute
      (a := 3) (k := 0) (α := lam) (β := 0) (γ := lam⁻¹) hlam0
      (Ne.symm (inv_ne_zero hlam0)) hlamne hcomm
    exact ⟨X, Y, Z, hgX, hZ⟩
  have hsub0 : Subsingleton (GL (Fin 0) F) :=
    ⟨fun x y => Units.ext (Subsingleton.elim (x : Matrix (Fin 0) (Fin 0) F)
      (y : Matrix (Fin 0) (Fin 0) F))⟩
  refine ⟨(phi2Hom h 3 0).range, ?_, ?_, ?_⟩
  · intro z hz
    have hzC : z ∈ Subgroup.centralizer ({t} : Set (hypSU h 3 0)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hz t).symm
    obtain ⟨X, Y, Z, hzmat, hZ⟩ := decomp z hzC
    have hY1 : Y = 1 := @Subsingleton.elim (GL (Fin 0) F) hsub0 Y 1
    have hone : (1 : F) ∈ h.traceZero := by
      rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
      exact CharTwo.add_self_eq_zero 1
    let w₀ : Equiv.Perm (Fin 3 ⊕ Fin 3) := swapSet (Finset.univ : Finset (Fin 3))
    have hw₀ : w₀ ∈ hypWeyl 3 := by
      simpa [w₀] using swapSet_mem_hypWeyl (Finset.univ : Finset (Fin 3))
    let w : hypSU h 3 0 := weylElt h hone one_ne_zero hw₀
    have hperm : ∀ x : HypIndex 3 0, weylPerm (ε := 0) w₀ x = hypPartner x := by
      intro x
      rcases x with i | k | i
      · rw [weylPerm_inl]
        simp [w₀, lineCoord, swapSet, hypPartner]
      · exact k.elim0
      · rw [weylPerm_inr_inr]
        simp [w₀, lineCoord, swapSet, hypPartner]
    have hcoeff : weylCoeff (ε := 0) h 1 w₀ = fun _ => 1 := by
      funext x
      rcases x with i | k | i
      · simp only [weylCoeff]
        rcases hx : w₀ (.inl i) with j | j <;> rfl
      · exact k.elim0
      · simp only [weylCoeff]
        rcases hx : w₀ (.inl i) with j | j <;> simp
    have hwJ : (((w : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) = hypGram 3 0 F := by
      show (((weylElt h hone one_ne_zero hw₀ : hypSU h 3 0) : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F) = hypGram 3 0 F
      rw [coe_weylElt, weylMat, hcoeff]
      ext a b
      rw [CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, hperm b, hypGram_apply]
      have hiff : (a = hypPartner b) ↔ (b = hypPartner a) := by
        rw [eq_comm]
        exact hypPartner_eq_iff
      by_cases hab : a = hypPartner b
      · rw [if_pos hab, if_pos (hiff.mp hab)]
      · rw [if_neg hab, if_neg (fun hba => hab (hiff.mpr hba))]
    have hzw : z * w = w * z := (Subgroup.mem_center_iff.mp hz w).symm
    set Mz : Matrix (HypIndex 3 0) (HypIndex 3 0) F :=
      ((z : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) with hMzdef
    have hMz : Mz = blockMat (X : Matrix (Fin 3) (Fin 3) F)
        (Y : Matrix (Fin 0) (Fin 0) F) (Z : Matrix (Fin 3) (Fin 3) F) := by
      rw [hMzdef, hzmat, coe_blockDiag]
    have hzW : Mz * hypGram 3 0 F = hypGram 3 0 F * Mz := by
      have h1 := congrArg (fun u : hypSU h 3 0 =>
        (((u : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F))) hzw
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hwJ,
        ← hMzdef] at h1
      exact h1
    have hconj : hypGram 3 0 F * Mz * hypGram 3 0 F =
        blockMat (Z : Matrix (Fin 3) (Fin 3) F) (Y : Matrix (Fin 0) (Fin 0) F)
          (X : Matrix (Fin 3) (Fin 3) F) := by
      rw [hMz]
      exact hypGram_mul_blockMat_mul (X : Matrix (Fin 3) (Fin 3) F)
        (Y : Matrix (Fin 0) (Fin 0) F) (Z : Matrix (Fin 3) (Fin 3) F)
    have hMeq : Mz = blockMat (Z : Matrix (Fin 3) (Fin 3) F)
        (Y : Matrix (Fin 0) (Fin 0) F) (X : Matrix (Fin 3) (Fin 3) F) := by
      calc Mz = Mz * (hypGram 3 0 F * hypGram 3 0 F) := by
            rw [hypGram_mul_self, mul_one]
        _ = Mz * hypGram 3 0 F * hypGram 3 0 F := by rw [mul_assoc]
        _ = hypGram 3 0 F * Mz * hypGram 3 0 F := by rw [hzW]
        _ = blockMat (Z : Matrix (Fin 3) (Fin 3) F) (Y : Matrix (Fin 0) (Fin 0) F)
            (X : Matrix (Fin 3) (Fin 3) F) := hconj
    have hXZ : (X : Matrix (Fin 3) (Fin 3) F) = (Z : Matrix (Fin 3) (Fin 3) F) :=
      (blockMat_inj.mp (hMz.symm.trans hMeq)).1
    have hdetz : ((z : GL (HypIndex 3 0) F) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) F).det = 1 := (mem_hypSU.mp z.2).2
    have hdetXZ : ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
        ((Z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      have h1 := hdetz
      rw [hzmat, coe_blockDiag, blockMat_det, hY1] at h1
      simpa using h1
    have hdetX : ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      have hsq : ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
          ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
        have h1 := hdetXZ
        rw [← hXZ] at h1
        exact h1
      have hsq' : ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ^ 2 = 1 := by
        rw [pow_two]
        exact hsq
      exact CharTwo.sq_injective (by simpa using hsq')
    refine MonoidHom.mem_range.mpr
      ⟨⟨X, CFSG.Open.StatedAPI.mem_statedSL_of_det hdetX⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_phi2Hom, coe_blockDiag, hzmat, coe_blockDiag, hY1, hZ]
  · have hcard : Nat.card (phi2Hom h 3 0).range = Nat.card SL(3, F) := by
      calc Nat.card (phi2Hom h 3 0).range = Nat.card (CFSG.Open.StatedSL 3 F) :=
            (Nat.card_congr (MonoidHom.ofInjective
              (phi2Hom_injective (a := 3) (k := 0) h)).toEquiv).symm
        _ = Nat.card SL(3, F) := CFSG.Open.StatedAPI.card_statedSL 3 F
    exact le_of_eq hcard
  · refine Subgroup.commutator_le.mpr ?_
    intro x hx y hy
    obtain ⟨X, Y, Z, hxmat, hZ⟩ := decomp x hx
    obtain ⟨X', Y', Z', hymat, hZ'⟩ := decomp y hy
    have hY1 : Y = 1 := @Subsingleton.elim (GL (Fin 0) F) hsub0 Y 1
    have hY1' : Y' = 1 := @Subsingleton.elim (GL (Fin 0) F) hsub0 Y' 1
    have hcommY : (⁅Y, Y'⁆ : GL (Fin 0) F) = 1 := by
      rw [hY1, hY1', commutatorElement_def]
      simp
    have hdetcomm : (((⁅X, X'⁆ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det = 1 :=
      det_commutator_eq_one X X'
    refine MonoidHom.mem_range.mpr
      ⟨⟨⁅X, X'⁆, CFSG.Open.StatedAPI.mem_statedSL_of_det hdetcomm⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_phi2Hom, coe_blockDiag, commutator_hypSU_eq h hxmat hymat hZ hZ', coe_blockDiag,
      hcommY]

end CFSG.StandardType

end
