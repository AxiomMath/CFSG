module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckW1F1_odd_card (g : ℕ) (hg : 1 ≤ g) :
    Odd (Nat.card (GaloisField 2 g) - 1) := by
  have hcard : Nat.card (GaloisField 2 g) = 2 ^ g :=
    GaloisField.card (p := 2) (n := g) (by omega)
  rw [hcard]
  refine ⟨2 ^ (g - 1) - 1, ?_⟩
  have h2 : 2 ^ g = 2 * 2 ^ (g - 1) := by
    conv_lhs => rw [show g = (g - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hpos : 1 ≤ 2 ^ (g - 1) := Nat.one_le_two_pow
  omega

private theorem rckW1F1_odd_order (m g p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hg : 1 ≤ g)
    {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)))
    {d : X} (hdp : d ^ p = 1) {s : GL (Fin (m + 1)) (GaloisField 2 g)}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d) : Odd (orderOf s) := by
  haveI : Fintype (GaloisField 2 g) := Fintype.ofFinite _
  have hsp : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hdp] at h
  obtain ⟨c, hc_eq⟩ :=
    isGLLift_unique_PSL m (GaloisField 2 g) ψ hψ hsp isGLLift_one
  have hsmat : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) ^ p =
      Matrix.scalar (Fin (m + 1)) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit :
        IsUnit ((s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) ^ p) :=
      IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin (m + 1)) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin (m + 1)) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)).det = c ^ (m + 1) := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    have hm0 : m + 1 ≠ 0 := by omega
    exact ((isUnit_pow_iff (a := c) (n := m + 1) hm0).mp hm).ne_zero
  let u : (GaloisField 2 g)ˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hoddF : Odd (Nat.card (GaloisField 2 g) - 1) := rckW1F1_odd_card g hg
  have hu_pow : u ^ (Nat.card (GaloisField 2 g) - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : GaloisField 2 g) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hodd_p, hodd_u⟩) hdvd

theorem rckF1_PSL
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K J : Subgroup X} {d : X}
    (hdp : d ^ p = 1) {m g : ℕ} (hg : 1 ≤ g) (φ : (ggU .PSL (m + 1) g).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSL (m + 1) g).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X)) (hdID : GGPsiInnerDiag (ggU .PSL (m + 1) g).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    ∃ s : GL (Fin (m + 1)) (GaloisField 2 g), IsGLLift Matrix.SpecialLinearGroup.toGL φ s d ∧
      Odd (orderOf s) ∧ ∃ e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g),
        IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' {s})) e ∧
        ∃ J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)),
          IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL {s} e,
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL {s} e⁆ ∧ J'.map φ = J := by
  have hbN : d ∈ Subgroup.normalizer (φ.range : Set X) := by rw [hφr]; exact hdN
  obtain ⟨s, hs⟩ :=
    exists_isGLLift_PSL m (GaloisField 2 g) φ hφk hbN hdID
  have hsodd : Odd (orderOf s) := rckW1F1_odd_order m g p hp hp2 hg φ hφk hdp hs
  let D : Subgroup X := Subgroup.zpowers d
  let P : GL (Fin (m + 1)) (GaloisField 2 g) → Prop := fun s' => s' ∈ Subgroup.zpowers s
  have hDcent : Subgroup.centralizer (D : Set X) = Subgroup.centralizer ({d} : Set X) := by
    change Subgroup.centralizer ((Subgroup.zpowers d : Set X)) = _
    rw [Subgroup.zpowers_eq_closure d]
    exact Subgroup.centralizer_closure ({d} : Set X)
  have hJ' : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set X)) := by
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
  have hlift : ∀ d' ∈ D, ∃ s' : GL (Fin (m + 1)) (GaloisField 2 g),
      P s' ∧ IsGLLift Matrix.SpecialLinearGroup.toGL φ s' d' := by
    intro d' hd'
    change d' ∈ Subgroup.zpowers d at hd'
    rw [Subgroup.zpowers_eq_closure d] at hd'
    induction hd' using Subgroup.closure_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨s, Subgroup.mem_zpowers s, hs⟩
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
    StepA.exists_isComponentOf_comap_lift_of_isGLLift (j := Matrix.SpecialLinearGroup.toGL)
      (hj := Matrix.SpecialLinearGroup.toGL_injective) (ψ := φ) (hψ := hφk) (P := P)
      (D := D) (J := J) hJ' hlift
  let Sset : Set (GL (Fin (m + 1)) (GaloisField 2 g)) :=
    {s' | P s' ∧ ∃ d' ∈ D, IsGLLift Matrix.SpecialLinearGroup.toGL φ s' d'}
  have hcl : Subgroup.closure Sset = Subgroup.zpowers s := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
    · rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le, Set.singleton_subset_iff]
      exact Subgroup.subset_closure
        ⟨Subgroup.mem_zpowers s, d, Subgroup.mem_zpowers d, hs⟩
  have hcent : Subgroup.centralizer Sset =
      Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))) := by
    rw [← Subgroup.centralizer_closure Sset, hcl, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hJ'compS : IsComponentOf J'
      ((Subgroup.centralizer Sset).comap Matrix.SpecialLinearGroup.toGL) := hJ'comp
  have hJ'comp' : IsComponentOf J'
      ((Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g)))).comap
        Matrix.SpecialLinearGroup.toGL) := by
    rwa [hcent] at hJ'compS
  have hS : ∀ a ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))),
      ∀ b ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl s
  obtain ⟨e, heprim, hcomp⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSL m (GaloisField 2 g)
      ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 g))) hS hJ'comp'
  exact ⟨s, hs, hsodd, e, heprim, J', hcomp, hJ'map⟩

end CFSG.StandardType.RCKRP
