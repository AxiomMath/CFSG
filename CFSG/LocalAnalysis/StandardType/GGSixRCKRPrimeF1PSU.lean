module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDCommute
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckRPf1su_odd_card_sub_one {F : Type} {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) : Odd (Nat.card F - 1) := by
  have hpowF : Nat.card F = 2 * 2 ^ (2 * f - 1) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hc
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm f 2]
      _ = 2 * 2 ^ (2 * f - 1) := by
            conv_lhs => rw [show 2 * f = (2 * f - 1) + 1 by omega]
            rw [pow_add, pow_one]
            ring
  rw [hpowF]
  refine ⟨2 ^ (2 * f - 1) - 1, ?_⟩
  have hX : 1 ≤ 2 ^ (2 * f - 1) := Nat.one_le_two_pow
  omega

private theorem rckRPf1su_odd_order {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hf : 1 ≤ f)
    {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : X}
    (hdp : d ^ p = 1) {s : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      ψ s d) : Odd (orderOf s) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hsp : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hdp] at h
  obtain ⟨c, hc_eq⟩ := isGLLift_unique_PSU hc n ψ hψ hsp isGLLift_one
  have hsmat : (s : Matrix (Fin n) (Fin n) F) ^ p = Matrix.scalar (Fin n) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit : IsUnit ((s : Matrix (Fin n) (Fin n) F) ^ p) := IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) F).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin n) (Fin n) F) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) F).det = c ^ n := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    have hn0 : n ≠ 0 := by omega
    exact ((isUnit_pow_iff (a := c) (n := n) hn0).mp hm).ne_zero
  let u : Fˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hoddF : Odd (Nat.card F - 1) := rckRPf1su_odd_card_sub_one hc hf
  have hu_pow : u ^ (Nat.card F - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hodd_p, hodd_u⟩) hdvd

theorem rckF1_PSU
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K J : Subgroup X} {d : X}
    (hdp : d ^ p = 1) {n g : ℕ} (hn : 3 ≤ n) (φ : (ggU .PSU n (g + 1)).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X)) (hdID : GGPsiInnerDiag (ggU .PSU n (g + 1)).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    ∃ s : GL (Fin n) (GaloisField 2 (2 * (g + 1))),
      Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n ∧
      IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype φ s d ∧ Odd (orderOf s) ∧
      ∃ ε : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1))),
        IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n)
          (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) ε ∧
        (∃ e, IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' {s})) e ∧
          e * ε = e ∧
          (e = ε ∨ (e ≠ ε ∧ formAdj (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) e ≠ e ∧
            ε = e + formAdj (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) e))) ∧
        ∃ J' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n),
          IsComponentOf J' ⁅glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype {s} ε,
            glBlockCentralizer (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype {s} ε⁆ ∧
          J'.map φ = J := by
  let F := GaloisField 2 (2 * (g + 1))
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 (g + 1)
  let j : ↥(Unitary.SU σ n) →* GL (Fin n) F := (Unitary.SU σ n).subtype
  let ψ : ↥(Unitary.SU σ n) →* X := φ
  have hc : Nat.card F = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hψ : ψ.ker ≤ Subgroup.center ↥(Unitary.SU σ n) := hφk
  have hdID' : GGPsiInnerDiag (Unitary.rootDatum hc n) ψ d := hdID
  have hbN : d ∈ Subgroup.normalizer (ψ.range : Set X) := by
    change d ∈ Subgroup.normalizer (φ.range : Set X)
    rw [hφr]
    exact hdN
  obtain ⟨s, hsunit, hslift⟩ :=
    exists_isGLLift_PSU hc n hn ψ hψ hbN hdID'
  have hsodd : Odd (orderOf s) :=
    rckRPf1su_odd_order hc hn (by omega) ψ hψ hp hp2 hdp hslift
  let D : Subgroup X := Subgroup.zpowers d
  let P : GL (Fin n) F → Prop := fun s' => s' ∈ Subgroup.zpowers s
  have hDcent : Subgroup.centralizer (D : Set X) = Subgroup.centralizer ({d} : Set X) := by
    change Subgroup.centralizer ((Subgroup.zpowers d : Set X)) = _
    rw [Subgroup.zpowers_eq_closure d]
    exact Subgroup.centralizer_closure ({d} : Set X)
  have hJ' : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    change IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set X))
    rw [hφr, hDcent]
    exact hJ
  have hpowD : ∀ x ∈ Subgroup.closure ({d} : Set X), x ^ p = 1 := by
    intro x hx
    rw [← Subgroup.zpowers_eq_closure d] at hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    calc (d ^ k) ^ p = (d ^ k) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = d ^ (k * (p : ℤ)) := by rw [← zpow_mul]
      _ = d ^ ((p : ℤ) * k) := by rw [mul_comm]
      _ = (d ^ (p : ℤ)) ^ k := by rw [zpow_mul]
      _ = (d ^ p) ^ k := by rw [zpow_natCast]
      _ = 1 := by rw [hdp, one_zpow]
  have hlift : ∀ d' ∈ D, ∃ s' : GL (Fin n) F,
      P s' ∧ IsGLLift j ψ s' d' := by
    intro d' hd'
    change d' ∈ Subgroup.zpowers d at hd'
    rw [Subgroup.zpowers_eq_closure d] at hd'
    induction hd' using Subgroup.closure_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨s, Subgroup.mem_zpowers s, hslift⟩
    | one => exact ⟨1, Subgroup.one_mem _, isGLLift_one⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨sx, hsxP, hsxL⟩ := ihx
        obtain ⟨sy, hsyP, hsyL⟩ := ihy
        exact ⟨sy * sx, Subgroup.mul_mem _ hsyP hsxP, hsxL.mul hsyL⟩
    | inv x hx ihx =>
        obtain ⟨sx, hsxP, hsxL⟩ := ihx
        refine ⟨sx ^ (p - 1), Subgroup.pow_mem _ hsxP (p - 1), ?_⟩
        have hxpow : x ^ p = 1 := hpowD x hx
        have hxinv : x ^ (p - 1) = x⁻¹ := by
          have hmul : x * x ^ (p - 1) = 1 := by
            have h1p : 1 ≤ p := Nat.succ_le_of_lt hp.pos
            rw [← pow_succ', Nat.sub_add_cancel h1p, hxpow]
          exact eq_inv_of_mul_eq_one_right hmul
        have h := hsxL.pow (p - 1)
        rwa [hxinv] at h
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift (j := j)
      (hj := Subgroup.subtype_injective _) (ψ := ψ) (hψ := hψ) (P := P)
      (D := D) (J := J) hJ' hlift
  let Sset : Set (GL (Fin n) F) :=
    {s' | P s' ∧ ∃ d' ∈ D, IsGLLift j ψ s' d'}
  have hcl : Subgroup.closure Sset = Subgroup.zpowers s := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
    · rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le, Set.singleton_subset_iff]
      exact Subgroup.subset_closure
        ⟨Subgroup.mem_zpowers s, d, Subgroup.mem_zpowers d, hslift⟩
  have hcent : Subgroup.centralizer Sset =
      Subgroup.centralizer ({s} : Set (GL (Fin n) F)) := by
    rw [← Subgroup.centralizer_closure Sset, hcl, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hJ'compS : IsComponentOf J'
      ((Subgroup.centralizer Sset).comap j) := hJ'comp
  have hJ'comp' : IsComponentOf J'
      ((Subgroup.centralizer ({s} : Set (GL (Fin n) F))).comap j) := by
    rwa [hcent] at hJ'compS
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n) F)),
      ∀ b ∈ ({s} : Set (GL (Fin n) F)), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl s
  obtain ⟨ε, hεprim, hcomp⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSU (F := F) (f := g + 1) n
      ({s} : Set (GL (Fin n) F)) hS hJ'comp'
  have hSU : ∀ a ∈ ({s} : Set (GL (Fin n) F)),
      Unitary.conjTr σ (a : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n *
        (a : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsunit
  obtain ⟨e, heprim, heε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSU n g ({s} : Set (GL (Fin n) F))
      hSU hS hεprim
  exact ⟨s, hsunit, hslift, hsodd, ε, hεprim, ⟨e, heprim, heε, hsplit⟩,
    J', hcomp, hJ'map⟩

end CFSG.StandardType.RCKRP
