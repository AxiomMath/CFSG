module

public import CFSG.LocalAnalysis.StandardType.GGSixTCBlockField
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section CharacterKernel

theorem exists_ne_one_mem_ker_not_mem_zpowers_of_card_sq {D : Type*} [Group D] [Finite D]
    {p : ℕ} (hp : p.Prime)
    (hD : Nat.card D = p ^ 2) {K : Type*} [Field K] (χ : D →* Kˣ) (hχ : ∀ d, χ d ^ p = 1)
    {x : D} (hx : x ^ p = 1) (hχx : χ x ≠ 1) :
    ∃ g₀ : D, g₀ ≠ 1 ∧ χ g₀ = 1 ∧ g₀ ∉ Subgroup.zpowers x := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hrange_le : χ.range ≤ rootsOfUnity p K := by
    intro y hy
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [mem_rootsOfUnity]
    exact hχ d
  have hcardR : Nat.card χ.range ≤ p :=
    (Subgroup.card_le_of_le hrange_le).trans (card_rootsOfUnity K p)
  have hprod : Nat.card χ.ker * Nat.card χ.range = p ^ 2 :=
    (Subgroup.card_ker_mul_card_range χ).trans hD
  have hp2 : 2 ≤ p := hp.two_le
  have hker_ne : χ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, one_mul] at hprod
    nlinarith
  obtain ⟨g₀, hg₀ker, hg₀⟩ : ∃ g₀ ∈ χ.ker, g₀ ≠ 1 := by
    by_contra hcon
    apply hker_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    exact hcon ⟨g, hg, hg1⟩
  refine ⟨g₀, hg₀, (MonoidHom.mem_ker).mp hg₀ker, ?_⟩
  intro hmem
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hχx (map_one χ)
  have hxord : orderOf x = p := orderOf_eq_prime hx hx1
  have hg₀ord : orderOf g₀ = p := by
    have hdvd : orderOf g₀ ∣ p := by
      rw [← hxord]
      exact orderOf_dvd_of_mem_zpowers hmem
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hg₀
    · exact h1
  have hcard : Nat.card (Subgroup.zpowers g₀) = Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hg₀ord, hxord]
  have hle : Subgroup.zpowers g₀ ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hmem
  have heq : Subgroup.zpowers g₀ = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hxg : x ∈ Subgroup.zpowers g₀ := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  have hkerle : Subgroup.zpowers g₀ ≤ χ.ker := Subgroup.zpowers_le.mpr hg₀ker
  exact hχx ((MonoidHom.mem_ker).mp (hkerle hxg))

end CharacterKernel

section NotDvdAlgebra

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

theorem PSUσ_apply (g : ℕ) (x : PSUF g) : PSUσ g x = x ^ 2 ^ (g + 1) :=
  CFSG.LieType.BorelTits.unitaryInvolution_apply (PSUF g) 2 (g + 1) x

theorem conjTr_scalar_mul_antidiag_mul_scalar (n g : ℕ) (c : PSUF g) :
    Matrix.transpose ((Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) (PSUF g)).map
      (⇑(PSUσ g).toRingHom)) * Unitary.antidiag n * Matrix.scalar (Fin n) c =
      (PSUσ g c * c) • (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) := by
  have hm : (Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) (PSUF g)).map
      (⇑(PSUσ g).toRingHom) = Matrix.diagonal (fun _ => PSUσ g c) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [hm, Matrix.scalar_apply, Matrix.diagonal_transpose, ← Matrix.smul_eq_diagonal_mul,
    Matrix.smul_mul, ← Matrix.smul_eq_mul_diagonal, smul_smul]

theorem scalar_mem_GUsub {n g : ℕ} {z : GL (Fin n) (PSUF g)} {c : PSUF g}
    (hz : (z : Matrix (Fin n) (Fin n) (PSUF g)) = Matrix.scalar (Fin n) c)
    (hc : c ^ (2 ^ (g + 1) + 1) = 1) : z ∈ GUsub (PSUσ g) n := by
  rw [mem_GUsub_iff, hz, conjTr_scalar_mul_antidiag_mul_scalar, PSUσ_apply, ← pow_succ, hc,
    one_smul]

theorem pow_succ_eq_one_of_pow_scalar (hn : 1 ≤ n) {s : GL (Fin n) (PSUF g)}
    (hs : s ∈ GUsub (PSUσ g) n) {c : PSUF g}
    (hsc : (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) c) :
    c ^ (2 ^ (g + 1) + 1) = 1 := by
  have hsp : s ^ p ∈ GUsub (PSUσ g) n := Subgroup.pow_mem _ hs p
  have h := mem_GUsub_iff.mp hsp
  rw [Units.val_pow_eq_pow_val, hsc, conjTr_scalar_mul_antidiag_mul_scalar] at h
  have hi : 0 < n := hn
  have hij := congrFun (congrFun h ⟨0, hi⟩) (Fin.rev ⟨0, hi⟩)
  have hanti : (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) ⟨0, hi⟩ (Fin.rev ⟨0, hi⟩) =
      1 := by
    simp [Unitary.antidiag]
  rw [Matrix.smul_apply, hanti, smul_eq_mul, mul_one] at hij
  rw [PSUσ_apply] at hij
  rw [pow_succ]
  exact hij

theorem exists_pow_eq_of_pow_eq_one_of_not_dvd {M : Type*} [Monoid M] {p N : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N)
    (hN : 1 < N) {c : M} (hc : c ^ N = 1) : ∃ b : M, b ^ p = c ∧ b ^ N = 1 := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN) hN
  have hdm := Nat.div_add_mod (p * m) N
  rw [hm] at hdm
  refine ⟨c ^ m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm m p, ← hdm, pow_succ, pow_mul, hc, one_pow, one_mul]
  · rw [← pow_mul, mul_comm m N, pow_mul, hc, one_pow]

theorem PSULiftHyp.exists_pow_scalar_of_not_dvd (hH : PSULiftHyp n g ψ p B)
    (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {s : GL (Fin n) (PSUF g)} (hs : s ∈ psuE ψ B) :
    ∃ b : PSUF g, (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) (b ^ p) := by
  obtain ⟨-, c, -, hsc⟩ := hH.psuE_pow_scalar_odd hs
  have hc := pow_succ_eq_one_of_pow_scalar (by have := hH.three_le; omega) hs.1 hsc
  obtain ⟨b, hb, -⟩ := exists_pow_eq_of_pow_eq_one_of_not_dvd hH.prime hpq (by
    have : 1 ≤ 2 ^ (g + 1) := Nat.one_le_two_pow
    omega) hc
  exact ⟨b, by rw [hb]; exact hsc⟩

theorem PSUBlock.not_dvd_units_card_of_two_le {S : Set (GL (Fin n) (PSUF g))}
    {ε e : Matrix (Fin n) (Fin n) (PSUF g)} (hH : PSULiftHyp n g ψ p B) (hb : PSUBlock ψ B S ε e)
    (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    (hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e) :
    ¬ p ∣ Nat.card (PSUF g)ˣ := by
  intro hpF
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have h1 := blockDegree_eq_one_of_pow_eq_pow hH.prime hpF (hb.S_comm hH) (hb.S_odd hH)
    (fun s hs => hH.exists_pow_scalar_of_not_dvd hpq (hb.subE s hs)) hb.e_prim
  omega

theorem exists_isGLLift_pow_eq_one_PSU
    {X : Type} [Group X] {n g p : ℕ} (hn : 1 ≤ n)
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} (hψ : ψ.ker ≤ Subgroup.center _)
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    {s : GL (Fin n) (PSUF g)} (hsU : s ∈ GUsub (PSUσ g) n)
    {b : X} (hb : b ^ p = 1) (hsl : IsGLLift (PSUj n g) ψ s b) :
    ∃ t : GL (Fin n) (PSUF g), t ∈ GUsub (PSUσ g) n ∧
      IsGLLift (PSUj n g) ψ t b ∧ t ^ p = 1 := by
  have hsp : IsGLLift (PSUj n g) ψ (s ^ p) 1 := by
    have h := hsl.pow p
    rwa [hb] at h
  obtain ⟨c, hc⟩ := isGLLift_unique_PSU (card_PSUF g) n ψ hψ hsp isGLLift_one
  have hsc : (s : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = Matrix.scalar (Fin n) c := by
    simpa only [inv_one, one_mul, Units.val_pow_eq_pow_val] using hc
  have hcN := pow_succ_eq_one_of_pow_scalar hn hsU hsc
  have hN : 1 < 2 ^ (g + 1) + 1 := by
    have : 1 ≤ 2 ^ (g + 1) := Nat.one_le_two_pow
    omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hcN
    exact zero_ne_one hcN
  obtain ⟨β, hβ, hβN⟩ := exists_pow_eq_of_pow_eq_one_of_not_dvd hp hpq hN hcN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hβ
    exact hc0 hβ.symm
  let z : GL (Fin n) (PSUF g) :=
    Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 β⁻¹ (inv_ne_zero hβ0))
  have hz : (z : Matrix (Fin n) (Fin n) (PSUF g)) = Matrix.scalar (Fin n) β⁻¹ := by
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hzU : z ∈ GUsub (PSUσ g) n := scalar_mem_GUsub hz (by rw [inv_pow, hβN, inv_one])
  have hzc : z ∈ Subgroup.center (GL (Fin n) (PSUF g)) := mem_center_GL_of_scalar hz
  refine ⟨z * s, Subgroup.mul_mem _ hzU hsU, hsl.central_mul hzc, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, hz,
    (Matrix.scalar_commute (n := Fin n) β⁻¹ (fun r' => Commute.all _ r')
      (s : Matrix (Fin n) (Fin n) (PSUF g))).mul_pow, ← map_pow, hsc, ← map_mul, Units.val_one]
  have hβc : β⁻¹ ^ p * c = 1 := by
    rw [inv_pow, hβ]
    exact inv_mul_cancel₀ hc0
  rw [hβc, map_one]

theorem eq_of_isGLLift_pow_eq_one_PSU
    {X : Type} [Group X] {n g p : ℕ} (hn : 1 ≤ n)
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} (hψ : ψ.ker ≤ Subgroup.center _)
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    {s s' : GL (Fin n) (PSUF g)} (hsU : s ∈ GUsub (PSUσ g) n)
    (hsU' : s' ∈ GUsub (PSUσ g) n) (hsp : s ^ p = 1) (hsp' : s' ^ p = 1)
    {b : X} (hsl : IsGLLift (PSUj n g) ψ s b) (hsl' : IsGLLift (PSUj n g) ψ s' b) :
    s = s' := by
  obtain ⟨c, hc⟩ := isGLLift_unique_PSU (card_PSUF g) n ψ hψ hsl hsl'
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have htU : s'⁻¹ * s ∈ GUsub (PSUσ g) n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hsU') hsU
  have htC : s'⁻¹ * s ∈ Subgroup.center (GL (Fin n) (PSUF g)) :=
    mem_center_GL_of_scalar hc
  have hcomm : Commute s'⁻¹ s := by
    have hh := Subgroup.mem_center_iff.mp htC s'
    have hh' : s = s'⁻¹ * s * s' := by simpa only [mul_inv_cancel_left] using hh
    change s'⁻¹ * s = s * s'⁻¹
    calc s'⁻¹ * s = (s'⁻¹ * s * s') * s'⁻¹ := by group
      _ = s * s'⁻¹ := by rw [← hh']
  have htp : (s'⁻¹ * s) ^ p = 1 := by
    rw [hcomm.mul_pow, inv_pow, hsp, hsp', inv_one, one_mul]
  have hcp : c ^ p = 1 := by
    have h1 : ((s'⁻¹ * s : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, htp, Units.val_one]
    rw [hc, ← map_pow] at h1
    exact Matrix.scalar_inj.mp (h1.trans (map_one _).symm)
  have hcN : c ^ (2 ^ (g + 1) + 1) = 1 :=
    pow_succ_eq_one_of_pow_scalar (p := 1) hn htU (by rw [pow_one]; exact hc)
  have hcop : Nat.Coprime p (2 ^ (g + 1) + 1) := hp.coprime_iff_not_dvd.mpr hpq
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hcp, hcN⟩
    rwa [hcop, pow_one] at h
  have h1 : s'⁻¹ * s = 1 := by
    apply Units.ext
    rw [hc, hc1, map_one, Units.val_one]
  exact (inv_mul_eq_one.mp h1).symm

theorem mem_SU_of_mem_GUsub_of_pow_eq_one
    {n g p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    {s : GL (Fin n) (PSUF g)} (hsU : s ∈ GUsub (PSUσ g) n) (hsp : s ^ p = 1) :
    s ∈ Unitary.SU (PSUσ g) n := by
  have hdetTr : (Unitary.conjTr (PSUσ g) (s : Matrix (Fin n) (Fin n) (PSUF g))).det =
      PSUσ g (s : Matrix (Fin n) (Fin n) (PSUF g)).det := by
    unfold Unitary.conjTr
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (PSUσ g).toRingHom _).symm
  have hdetU := congrArg Matrix.det (mem_GUsub.mp hsU)
  rw [Matrix.det_mul, Matrix.det_mul, hdetTr] at hdetU
  have hnorm : PSUσ g (s : Matrix (Fin n) (Fin n) (PSUF g)).det *
      (s : Matrix (Fin n) (Fin n) (PSUF g)).det = 1 := by
    apply mul_right_cancel₀ (Unitary.det_antidiag_ne_zero n)
    rw [one_mul]
    calc (PSUσ g (s : Matrix (Fin n) (Fin n) (PSUF g)).det *
        (s : Matrix (Fin n) (Fin n) (PSUF g)).det) * (Unitary.antidiag n).det =
        (PSUσ g (s : Matrix (Fin n) (Fin n) (PSUF g)).det * (Unitary.antidiag n).det) *
          (s : Matrix (Fin n) (Fin n) (PSUF g)).det := by ring
      _ = (Unitary.antidiag n).det := hdetU
  have hdN : (s : Matrix (Fin n) (Fin n) (PSUF g)).det ^ (2 ^ (g + 1) + 1) = 1 := by
    simpa only [pow_succ, PSUσ_apply] using hnorm
  have hdp : (s : Matrix (Fin n) (Fin n) (PSUF g)).det ^ p = 1 := by
    have h := congrArg (fun a : GL (Fin n) (PSUF g) =>
      (a : Matrix (Fin n) (Fin n) (PSUF g)).det) hsp
    simpa only [Units.val_pow_eq_pow_val, Matrix.det_pow, Units.val_one, Matrix.det_one] using h
  have hcop : Nat.Coprime p (2 ^ (g + 1) + 1) := hp.coprime_iff_not_dvd.mpr hpq
  have hd1 : (s : Matrix (Fin n) (Fin n) (PSUF g)).det = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hdp, hdN⟩
    rwa [hcop, pow_one] at h
  exact ⟨hd1, hsU⟩

section CanonicalLift

variable (hH : PSULiftHyp n g ψ p B)
include hH

theorem PSULiftHyp.exists_lift_pow_eq_one (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {b : X} (hb : b ∈ B) :
    ∃ s : GL (Fin n) (PSUF g), s ∈ psuE ψ B ∧ IsGLLift (PSUj n g) ψ s b ∧ s ^ p = 1 := by
  obtain ⟨s, hsU, hsl⟩ := hH.exists_lift hb
  obtain ⟨t, htU, htl, htp⟩ := exists_isGLLift_pow_eq_one_PSU
    (by have := hH.three_le; omega) hH.ker hH.prime hpq hsU (hH.pow_eq_one hb) hsl
  exact ⟨t, ⟨htU, b, hb, htl⟩, htl, htp⟩

theorem PSULiftHyp.eq_of_lift_pow_eq_one (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    {s s' : GL (Fin n) (PSUF g)} (hs : s ∈ psuE ψ B) (hs' : s' ∈ psuE ψ B) (hsp : s ^ p = 1)
    (hsp' : s' ^ p = 1) {b : X} (hl : IsGLLift (PSUj n g) ψ s b)
    (hl' : IsGLLift (PSUj n g) ψ s' b) : s = s' := by
  exact eq_of_isGLLift_pow_eq_one_PSU (by have := hH.three_le; omega)
    hH.ker hH.prime hpq hs.1 hs'.1 hsp hsp' hl hl'

noncomputable def PSULiftHyp.liftP (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) (b : X) (hb : b ∈ B) :
    GL (Fin n) (PSUF g) :=
  Classical.choose (hH.exists_lift_pow_eq_one hpq hb)

theorem PSULiftHyp.liftP_spec (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {b : X} (hb : b ∈ B) :
    hH.liftP hpq b hb ∈ psuE ψ B ∧ IsGLLift (PSUj n g) ψ (hH.liftP hpq b hb) b ∧
      hH.liftP hpq b hb ^ p = 1 :=
  Classical.choose_spec (hH.exists_lift_pow_eq_one hpq hb)

theorem PSULiftHyp.liftP_eq (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {b : X} (hb : b ∈ B)
    {s : GL (Fin n) (PSUF g)} (hs : s ∈ psuE ψ B) (hsp : s ^ p = 1)
    (hl : IsGLLift (PSUj n g) ψ s b) : hH.liftP hpq b hb = s :=
  hH.eq_of_lift_pow_eq_one hpq (hH.liftP_spec hpq hb).1 hs (hH.liftP_spec hpq hb).2.2 hsp
    (hH.liftP_spec hpq hb).2.1 hl

theorem PSULiftHyp.liftP_one (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) : hH.liftP hpq 1 B.one_mem = 1 :=
  hH.liftP_eq hpq B.one_mem (Subgroup.one_mem _) (one_pow p) isGLLift_one

theorem PSULiftHyp.liftP_mul (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {b b' : X} (hb : b ∈ B)
    (hb' : b' ∈ B) :
    hH.liftP hpq (b * b') (B.mul_mem hb hb') = hH.liftP hpq b hb * hH.liftP hpq b' hb' := by
  have h1 := hH.liftP_spec hpq hb
  have h2 := hH.liftP_spec hpq hb'
  have hcomm : Commute (hH.liftP hpq b hb) (hH.liftP hpq b' hb') := hH.psuE_comm h1.1 h2.1
  refine hH.liftP_eq hpq (B.mul_mem hb hb') (Subgroup.mul_mem _ h1.1 h2.1) ?_ ?_
  · rw [hcomm.mul_pow, h1.2.2, h2.2.2, one_mul]
  · rw [hcomm.eq]
    exact h1.2.1.mul h2.2.1

@[expose] noncomputable def PSULiftHyp.lam (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) :
    B →* GL (Fin n) (PSUF g) where
  toFun b := hH.liftP hpq b.1 b.2
  map_one' := hH.liftP_one hpq
  map_mul' b b' := hH.liftP_mul hpq b.2 b'.2

theorem PSULiftHyp.lam_spec (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {b : X} (hb : b ∈ B) :
    (hH.lam hpq ⟨b, hb⟩ : GL (Fin n) (PSUF g)) ∈ psuE ψ B ∧
      IsGLLift (PSUj n g) ψ (hH.lam hpq ⟨b, hb⟩ : GL (Fin n) (PSUF g)) b ∧
      (hH.lam hpq ⟨b, hb⟩ : GL (Fin n) (PSUF g)) ^ p = 1 :=
  hH.liftP_spec hpq hb

end CanonicalLift

section Character

theorem PSUBlock.exists_mem_ker [Finite X] (hH : PSULiftHyp n g ψ p B)
    (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {S : Set (GL (Fin n) (PSUF g))}
    {ε e : Matrix (Fin n) (Fin n) (PSUF g)} (hb : PSUBlock ψ B S ε e)
    {D : Subgroup X} (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2)
    (hSD : ∀ d ∈ D, ∀ s ∈ psuE ψ B, IsGLLift (PSUj n g) ψ s d → s ∈ S)
    {x : X} (hxD : x ∈ D)
    (hx : ((hH.lam hpq ⟨x, hDB hxD⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      e ≠ e) :
    ∃ (g₀ : X) (hg₀ : g₀ ∈ D), g₀ ≠ 1 ∧ g₀ ∉ Subgroup.zpowers x ∧
      ((hH.lam hpq ⟨g₀, hDB hg₀⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * e =
        e := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  obtain ⟨K, hKf, hKa, hKfin, π, hπs, hπk, hπd⟩ := exists_blockField (hb.S_comm hH) (hb.S_odd hH)
    hb.e_prim
  let : Field K := hKf
  let : Algebra (PSUF g) K := hKa
  have hmemS : ∀ (d : X) (hd : d ∈ D),
      ((hH.lam hpq ⟨d, hDB hd⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) ∈
        Algebra.adjoin (PSUF g) (Units.val '' S) := by
    intro d hd
    have h1 := hH.liftP_spec hpq (hDB hd)
    exact Algebra.subset_adjoin ⟨_, hSD d hd _ h1.1 h1.2.1, rfl⟩
  let a : ∀ d : X, d ∈ D → Algebra.adjoin (PSUF g) (Units.val '' S) := fun d hd =>
    ⟨_, hmemS d hd⟩
  have ha_val : ∀ (d : X) (hd : d ∈ D), (a d hd : Matrix (Fin n) (Fin n) (PSUF g)) =
      ((hH.lam hpq ⟨d, hDB hd⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) :=
    fun d hd => rfl
  have ha_mul : ∀ (d : X) (hd : d ∈ D) (d' : X) (hd' : d' ∈ D),
      a (d * d') (D.mul_mem hd hd') = a d hd * a d' hd' := by
    intro d hd d' hd'
    apply Subtype.ext
    rw [Subalgebra.coe_mul, ha_val (d * d') (D.mul_mem hd hd'), ha_val d hd, ha_val d' hd']
    have : hH.lam hpq ⟨d * d', hDB (D.mul_mem hd hd')⟩ =
        hH.lam hpq ⟨d, hDB hd⟩ * hH.lam hpq ⟨d', hDB hd'⟩ :=
      map_mul (hH.lam hpq) ⟨d, hDB hd⟩ ⟨d', hDB hd'⟩
    rw [this, Units.val_mul]
  have ha_one : a 1 D.one_mem = 1 := by
    apply Subtype.ext
    rw [ha_val 1 D.one_mem]
    have : hH.lam hpq ⟨1, hDB D.one_mem⟩ = 1 := map_one (hH.lam hpq)
    rw [this, Units.val_one]
    rfl
  have ha_pow : ∀ (d : X) (hd : d ∈ D), a d hd ^ p = 1 := by
    intro d hd
    apply Subtype.ext
    rw [Subalgebra.coe_pow, ha_val d hd, ← Units.val_pow_eq_pow_val]
    have := (hH.liftP_spec hpq (hDB hd)).2.2
    change (((hH.liftP hpq d (hDB hd)) ^ p : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) = 1
    rw [this, Units.val_one]
  have hne : ∀ (d : X) (hd : d ∈ D), π (a d hd) ≠ 0 := by
    intro d hd h0
    have h1 : π (a d hd) ^ p = 1 := by rw [← map_pow, ha_pow d hd, map_one]
    rw [h0, zero_pow hH.prime.ne_zero] at h1
    exact zero_ne_one h1
  let χ : ↥D →* Kˣ :=
    { toFun := fun d => Units.mk0 (π (a d.1 d.2)) (hne d.1 d.2)
      map_one' := by
        apply Units.ext
        change π (a 1 D.one_mem) = 1
        rw [ha_one, map_one]
      map_mul' := fun d d' => by
        apply Units.ext
        change π (a (d.1 * d'.1) (D.mul_mem d.2 d'.2)) = π (a d.1 d.2) * π (a d'.1 d'.2)
        rw [ha_mul d.1 d.2 d'.1 d'.2, map_mul] }
  have hχp : ∀ d : ↥D, χ d ^ p = 1 := by
    intro d
    apply Units.ext
    change π (a d.1 d.2) ^ p = 1
    rw [← map_pow, ha_pow d.1 d.2, map_one]
  have hχiff : ∀ (d : X) (hd : d ∈ D), χ ⟨d, hd⟩ = 1 ↔
      ((hH.lam hpq ⟨d, hDB hd⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * e =
        e := by
    intro d hd
    constructor
    · intro h
      have h1 : π (a d hd) = 1 := congrArg Units.val h
      have h2 : π (a d hd - 1) = 0 := by rw [map_sub, h1, map_one, sub_self]
      have h3 := (hπk _).mp h2
      rw [Subalgebra.coe_sub, ha_val d hd, Subalgebra.coe_one, sub_mul, one_mul, sub_eq_zero] at h3
      exact h3
    · intro h
      apply Units.ext
      change π (a d hd) = 1
      have h2 : π (a d hd - 1) = 0 := by
        rw [hπk, Subalgebra.coe_sub, ha_val d hd, Subalgebra.coe_one, sub_mul, one_mul, h, sub_self]
      rw [map_sub, map_one, sub_eq_zero] at h2
      exact h2
  have hxp : (⟨x, hxD⟩ : ↥D) ^ p = 1 := Subtype.ext (hH.pow_eq_one (hDB hxD))
  have hχx : χ ⟨x, hxD⟩ ≠ 1 := fun h => hx ((hχiff x hxD).mp h)
  obtain ⟨g₀, hg1, hχg, hnot⟩ := exists_ne_one_mem_ker_not_mem_zpowers_of_card_sq hH.prime
    hDcard χ hχp hxp hχx
  refine ⟨g₀.1, g₀.2, fun h => hg1 (Subtype.ext h), ?_, (hχiff g₀.1 g₀.2).mp hχg⟩
  intro hmem
  apply hnot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

end Character

end NotDvdAlgebra

section YT

open CFSG.StandardType.ClassicalPosition.Geo

variable {X : Type} [Group X] {n g p : ℕ} {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X}

noncomputable def PSUYsd (n g : ℕ) (T : Matrix (Fin n) (Fin n) (PSUF g)) :
    Subgroup ↥(Unitary.SU (PSUσ g) n) :=
  (glFixing (1 - T)).comap (PSUj n g)

theorem mem_PSUYsd {T : Matrix (Fin n) (Fin n) (PSUF g)} {u : ↥(Unitary.SU (PSUσ g) n)} :
    u ∈ PSUYsd n g T ↔
      ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - T) =
        1 - T := Iff.rfl

theorem formAdj_sub_PSU (a b : Matrix (Fin n) (Fin n) (PSUF g)) :
    formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (a - b) =
      formAdj (PSUσ g).toRingHom (Unitary.antidiag n) a -
        formAdj (PSUσ g).toRingHom (Unitary.antidiag n) b := by
  have h1 : a - b = a + (-1 : PSUF g) • b := by rw [neg_smul, one_smul, sub_eq_add_neg]
  have h2 : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) ((-1 : PSUF g) • b) =
      (-1 : PSUF g) • formAdj (PSUσ g).toRingHom (Unitary.antidiag n) b := by
    rw [formAdj_smul]
    simp
  rw [h1, formAdj_add, h2, neg_smul, one_smul, sub_eq_add_neg]

theorem formAdj_one_sub_PSU {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hT : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T) :
    formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (1 - T) = 1 - T := by
  rw [formAdj_sub_PSU, hT, formAdj_one (PSUσ g).toRingHom (PSUantidiag_isUnit_det n g)]

theorem formAdj_PSU_unit (u : ↥(Unitary.SU (PSUσ g) n)) :
    formAdj (PSUσ g).toRingHom (Unitary.antidiag n)
        ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      (((PSUj n g u)⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) :=
  formAdj_eq_inv_of_isometry (PSUσ g).toRingHom (PSUantidiag_isUnit_det n g) (PSUj n g u)
    u.2.2

theorem PSUYsd.one_sub_mul {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hT : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    {u : ↥(Unitary.SU (PSUσ g) n)} (hu : u ∈ PSUYsd n g T) :
    (1 - T) * ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) = 1 - T := by
  have h1 : ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - T) =
      1 - T := hu
  have h2 := congrArg (formAdj (PSUσ g).toRingHom (Unitary.antidiag n)) h1
  rw [formAdj_mul (PSUσ g).toRingHom (PSUantidiag_isUnit_det n g), formAdj_PSU_unit u,
    formAdj_one_sub_PSU hT] at h2
  have h4 := congrArg (fun M => M * ((PSUj n g u : GL (Fin n) (PSUF g)) :
    Matrix (Fin n) (Fin n) (PSUF g))) h2
  simp only [Matrix.mul_assoc] at h4
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] at h4
  exact h4.symm

theorem PSUYsd.comm_T {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hT : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    {u : ↥(Unitary.SU (PSUσ g) n)} (hu : u ∈ PSUYsd n g T) :
    ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * T =
      T * ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
  set U : Matrix (Fin n) (Fin n) (PSUF g) :=
    ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) with hUdef
  have h1 : U * (1 - T) = 1 - T := hu
  have h3 : (1 - T) * U = 1 - T := PSUYsd.one_sub_mul hT hu
  have e1 : U - U * T = 1 - T := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
  have e2 : U - T * U = 1 - T := by rw [← h3, Matrix.sub_mul, Matrix.one_mul]
  exact sub_right_inj.mp (e1.trans e2.symm)

theorem glFixing_conj_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {P : Matrix ι ι F} {c y : GL ι F}
    (hc : (c : Matrix ι ι F) * P = P * (c : Matrix ι ι F)) (hy : y ∈ glFixing P) :
    c * y * c⁻¹ ∈ glFixing P := by
  have hy' : (y : Matrix ι ι F) * P = P := hy
  have hcc : (c : Matrix ι ι F) * ((c⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcc' : ((c⁻¹ : GL ι F) : Matrix ι ι F) * (c : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hci : ((c⁻¹ : GL ι F) : Matrix ι ι F) * P = P * ((c⁻¹ : GL ι F) : Matrix ι ι F) := by
    calc ((c⁻¹ : GL ι F) : Matrix ι ι F) * P
        = ((c⁻¹ : GL ι F) : Matrix ι ι F) * P * ((c : Matrix ι ι F) *
            ((c⁻¹ : GL ι F) : Matrix ι ι F)) := by rw [hcc, Matrix.mul_one]
      _ = ((c⁻¹ : GL ι F) : Matrix ι ι F) * (P * (c : Matrix ι ι F)) *
            ((c⁻¹ : GL ι F) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
      _ = ((c⁻¹ : GL ι F) : Matrix ι ι F) * ((c : Matrix ι ι F) * P) *
            ((c⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hc]
      _ = P * ((c⁻¹ : GL ι F) : Matrix ι ι F) := by
          rw [← Matrix.mul_assoc, hcc', Matrix.one_mul]
  change ((c * y * c⁻¹ : GL ι F) : Matrix ι ι F) * P = P
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hci,
    ← Matrix.mul_assoc (y : Matrix ι ι F), hy', ← Matrix.mul_assoc, hc, Matrix.mul_assoc, hcc,
    Matrix.mul_one]

theorem PSUYsd_normal_subgroupOf_centralizer {T : Matrix (Fin n) (Fin n) (PSUF g)}
    {s : GL (Fin n) (PSUF g)}
    (hTc : ∀ c : GL (Fin n) (PSUF g), c ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) →
      (c : Matrix (Fin n) (Fin n) (PSUF g)) * T = T * (c : Matrix (Fin n) (Fin n) (PSUF g))) :
    ((PSUYsd n g T).subgroupOf
      ((Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g)))).comap (PSUj n g))).Normal := by
  refine ⟨fun y hy c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  have hcT := hTc (PSUj n g c.1) c.2
  have hc1 : ((PSUj n g c.1 : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - T) =
      (1 - T) * ((PSUj n g c.1 : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcT]
  have := glFixing_conj_mem hc1 (show PSUj n g y.1 ∈ glFixing (1 - T) from hy)
  change PSUj n g (c.1 * y.1 * c.1⁻¹) ∈ glFixing (1 - T)
  simpa only [map_mul, map_inv] using this

theorem PSUYsd_le_centralizer {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hT : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T) {s : GL (Fin n) (PSUF g)}
    (hsT : (s : Matrix (Fin n) (Fin n) (PSUF g)) * T = T)
    (hTs : T * (s : Matrix (Fin n) (Fin n) (PSUF g)) = T) :
    PSUYsd n g T ≤ (Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g)))).comap (PSUj n g) := by
  intro u hu
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  subst ht
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set U : Matrix (Fin n) (Fin n) (PSUF g) :=
    ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) with hUdef
  set Sm : Matrix (Fin n) (Fin n) (PSUF g) := (t : Matrix (Fin n) (Fin n) (PSUF g)) with hSdef
  have h1 : U * (1 - T) = 1 - T := hu
  have h3 : (1 - T) * U = 1 - T := PSUYsd.one_sub_mul hT hu
  have hcomm : U * T = T * U := PSUYsd.comm_T hT hu
  have e1 : U - U * T = 1 - T := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
  have e2 : U - T * U = 1 - T := by rw [← h3, Matrix.sub_mul, Matrix.one_mul]
  have eU1 : U = (1 - T) + T * U := sub_eq_iff_eq_add.mp e2
  have eU2 : U = (1 - T) + U * T := sub_eq_iff_eq_add.mp e1
  calc Sm * U = Sm * ((1 - T) + T * U) := by rw [← eU1]
    _ = Sm * (1 - T) + (Sm * T) * U := by rw [Matrix.mul_add, Matrix.mul_assoc]
    _ = (Sm - T) + T * U := by rw [Matrix.mul_sub, Matrix.mul_one, hsT]
    _ = (Sm - T) + U * T := by rw [← hcomm]
    _ = (1 - T) * Sm + U * (T * Sm) := by rw [Matrix.sub_mul, Matrix.one_mul, hTs]
    _ = ((1 - T) + U * T) * Sm := by rw [Matrix.add_mul, Matrix.mul_assoc]
    _ = U * Sm := by rw [← eU2]

theorem glBlockCentralizer_le_PSUYsd {S : Set (GL (Fin n) (PSUF g))}
    {ε T : Matrix (Fin n) (Fin n) (PSUF g)} (hεT : ε * T = ε) :
    glBlockCentralizer (PSUj n g) S ε ≤ PSUYsd n g T := by
  intro u hu
  have hu' : PSUj n g u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) := hu
  have h1 : ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε) =
      1 - ε := hu'.2
  have h2 : (1 - ε) * (1 - T) = 1 - T := by
    have : ε * (1 - T) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hεT, sub_self]
    rw [Matrix.sub_mul, Matrix.one_mul, this, sub_zero]
  change ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - T) =
    1 - T
  calc ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - T)
      = ((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
          ((1 - ε) * (1 - T)) := by rw [h2]
    _ = (((PSUj n g u : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - ε)) *
          (1 - T) := by rw [Matrix.mul_assoc]
    _ = 1 - T := by rw [h1, h2]

theorem commute_avgPow {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {s c : GL ι F}
    (h : c * s = s * c) (p : ℕ) :
    (c : Matrix ι ι F) * avgPow s p = avgPow s p * (c : Matrix ι ι F) := by
  unfold avgPow
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : c * s ^ i = s ^ i * c := ((Commute.pow_right (show Commute c s from h) i)).eq
  have := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hc
  simpa [Units.val_mul] using this

theorem PSUBlock.avg_spec [Finite X] (hH : PSULiftHyp n g ψ p B) (hpq : ¬ p ∣ 2 ^ (g + 1) + 1)
    {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
    (hb : PSUBlock ψ B S ε e) {D : Subgroup X} (hDB : D ≤ B)
    (hSD : ∀ d ∈ D, ∀ s ∈ psuE ψ B, IsGLLift (PSUj n g) ψ s d → s ∈ S)
    {y : X} (hyD : y ∈ D)
    (hye : ((hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      e = e) :
    avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p ∈ Algebra.adjoin (PSUF g) (Units.val '' S) ∧
    IsIdempotentElem (avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p) ∧
    formAdj (PSUσ g).toRingHom (Unitary.antidiag n) (avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p) =
      avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p ∧
    ((hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p = avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p ∧
    avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p *
      ((hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p ∧
    e * avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p = e ∧
    ε * avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p = ε ∧
    Matrix.rank e ≤ Matrix.rank (avgPow (hH.lam hpq ⟨y, hDB hyD⟩) p) := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hspec := hH.liftP_spec hpq (hDB hyD)
  have hsp : (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) ^ p = 1 := hspec.2.2
  have hsE : (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) ∈ psuE ψ B := hspec.1
  have hsS : (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) ∈ S :=
    hSD y hyD _ hsE hspec.2.1
  have hodd : Odd p := hH.prime.odd_of_ne_two hH.ne_two
  set s : GL (Fin n) (PSUF g) := (hH.lam hpq ⟨y, hDB hyD⟩ : GL (Fin n) (PSUF g)) with hsdef
  set T : Matrix (Fin n) (Fin n) (PSUF g) := avgPow s p with hTdef
  have hTA : T ∈ Algebra.adjoin (PSUF g) (Units.val '' S) := avgPow_mem_adjoin hsS p
  have hTidem : IsIdempotentElem T := isIdempotentElem_avgPow hodd hsp
  have hTadj : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T :=
    formAdj_avgPow (PSUσ g).toRingHom (PSUσ_involutive g) (PSUantidiag_isUnit_det n g)
      (mem_GUsub_iff.mp hsE.1) hsp
  have hsT : (s : Matrix (Fin n) (Fin n) (PSUF g)) * T = T := mul_avgPow hsp
  have hTs : T * (s : Matrix (Fin n) (Fin n) (PSUF g)) = T := avgPow_mul hsp
  have hTe : T * e = e := avgPow_mul_eq_self hodd hye
  have heT : e * T = e := by
    have hcomm := (adjoin_commute (hb.S_comm hH) T hTA e hb.e_prim.1).eq
    rw [← hcomm, hTe]
  refine ⟨hTA, hTidem, hTadj, hsT, hTs, heT, ?_, ?_⟩
  · rcases hb.cases with h | ⟨_, _, hε⟩
    · rw [← h]
      exact heT
    · rw [hε, Matrix.add_mul]
      have h1 := congrArg (formAdj (PSUσ g).toRingHom (Unitary.antidiag n)) hTe
      rw [formAdj_mul (PSUσ g).toRingHom (PSUantidiag_isUnit_det n g), hTadj] at h1
      rw [heT, h1]
  · calc Matrix.rank e = Matrix.rank (T * e) := by rw [hTe]
      _ ≤ Matrix.rank T := Matrix.rank_mul_le_left T e

theorem PSU_center_scalar (hadm : StatedLieAdmissible .PSU n 2 (g + 1))
    {z : ↥(Unitary.SU (PSUσ g) n)} (hz : z ∈ Subgroup.center ↥(Unitary.SU (PSUσ g) n)) :
    ∃ c : PSUF g, ((z : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      Matrix.scalar (Fin n) c := by
  have hF : Nat.card (PSUF g) = (2 ^ (g + 1)) ^ 2 := card_PSUF g
  let P0 := (Unitary.exists_wittMatrix (F := PSUF g) (p := 2) (f := g + 1) hF n).choose
  let hP0 := (Unitary.exists_wittMatrix (F := PSUF g) (p := 2) (f := g + 1) hF n).choose_spec
  let e : ↥(Unitary.SU (PSUσ g) n) ≃* ↥(StatedSU n (2 ^ (g + 1)) (PSUF g)) :=
    (Unitary.conjEquiv P0 hP0).trans
      (MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU (F := PSUF g) (p := 2) (f := g + 1) hF n))
  have hcen := (Unitary.isQuasisimple_statedSU_of_card (F := PSUF g) (p := 2) (f := g + 1) hF
    hadm.2.2.1 hadm.2.2.2).2
  have h1 : e z ∈ Subgroup.center ↥(StatedSU n (2 ^ (g + 1)) (PSUF g)) := by
    have := Unitary.map_center_mulEquiv e
    rw [← this]
    exact ⟨z, hz, rfl⟩
  rw [hcen, Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp h1
  have hez : ((e z : ↥(StatedSU n (2 ^ (g + 1)) (PSUF g))) : GL (Fin n) (PSUF g)) =
      P0 * (z : GL (Fin n) (PSUF g)) * P0⁻¹ := rfl
  have hcentral : Matrix.GeneralLinearGroup.scalar (Fin n) u ∈
      Subgroup.center (GL (Fin n) (PSUF g)) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have hz' : (z : GL (Fin n) (PSUF g)) = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    have h2 : P0 * (z : GL (Fin n) (PSUF g)) * P0⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin n) u := by
      rw [← hez]
      exact hu.symm
    calc (z : GL (Fin n) (PSUF g)) = P0⁻¹ * (P0 * (z : GL (Fin n) (PSUF g)) * P0⁻¹) * P0 := by
          group
      _ = P0⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u * P0 := by rw [h2]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) u * P0⁻¹ * P0 := by
          rw [(Subgroup.mem_center_iff.mp hcentral P0⁻¹)]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) u := by group
  refine ⟨(u : PSUF g), ?_⟩
  rw [hz', Matrix.GeneralLinearGroup.coe_scalar]

theorem PSULiftHyp.map_centralizer_lam (hH : PSULiftHyp n g ψ p B)
    (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) (hpF : ¬ p ∣ Nat.card (PSUF g)ˣ) {y : X} (hy : y ∈ B) :
    ((Subgroup.centralizer
      ({hH.lam hpq ⟨y, hy⟩} : Set (GL (Fin n) (PSUF g)))).comap (PSUj n g)).map ψ =
      ψ.range ⊓ Subgroup.centralizer ({y} : Set X) := by
  classical
  have : Fintype (PSUF g) := Fintype.ofFinite (PSUF g)
  have hn := hH.three_le
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hspec := hH.liftP_spec hpq hy
  have hs : IsGLLift (PSUj n g) ψ (hH.lam hpq ⟨y, hy⟩ : GL (Fin n) (PSUF g)) y := hspec.2.1
  have hsp : (hH.lam hpq ⟨y, hy⟩ : GL (Fin n) (PSUF g)) ^ p = 1 := hspec.2.2
  set s : GL (Fin n) (PSUF g) := (hH.lam hpq ⟨y, hy⟩ : GL (Fin n) (PSUF g)) with hsdef
  have hinj : Function.Injective (PSUj n g) := Subgroup.subtype_injective _
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, ?_⟩
    have hu' : PSUj n g u ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) := hu
    rw [Subgroup.mem_centralizer_iff] at hu'
    have hcomm : s * PSUj n g u = PSUj n g u * s := hu' s (Set.mem_singleton s)
    obtain ⟨u', hj, hψ'⟩ := hs u
    have : PSUj n g u' = PSUj n g u := by rw [hj, hcomm]; group
    have hu'u : u' = u := hinj this
    rw [hu'u] at hψ'
    show ψ u ∈ Subgroup.centralizer ({y} : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    calc t * ψ u = t * (t⁻¹ * ψ u * t) := by rw [hψ']
      _ = ψ u * t := by group
  · rintro ⟨⟨u, rfl⟩, hcent⟩
    refine ⟨u, ?_, rfl⟩
    have hcent' : ψ u ∈ Subgroup.centralizer ({y} : Set X) := hcent
    rw [Subgroup.mem_centralizer_iff] at hcent'
    have hcent := hcent'
    have hyc : y * ψ u = ψ u * y := hcent y (Set.mem_singleton y)
    obtain ⟨u', hj, hψ'⟩ := hs u
    have hψeq : ψ u' = ψ u := by rw [← hψ']; calc y⁻¹ * ψ u * y = y⁻¹ * (ψ u * y) := by group
      _ = y⁻¹ * (y * ψ u) := by rw [hyc]
      _ = ψ u := by group
    have hker : u⁻¹ * u' ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, inv_mul_cancel]
    obtain ⟨c, hc⟩ := PSU_center_scalar hH.adm (hH.ker hker)
    set z : GL (Fin n) (PSUF g) := PSUj n g (u⁻¹ * u') with hzdef
    have hzmat : (z : Matrix (Fin n) (Fin n) (PSUF g)) = Matrix.scalar (Fin n) c := hc
    have hzc : z ∈ Subgroup.center (GL (Fin n) (PSUF g)) := mem_center_GL_of_scalar hzmat
    have hconj : s * PSUj n g u * s⁻¹ = PSUj n g u * z := by
      rw [← hj, hzdef, map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hpow : ∀ k : ℕ, s ^ k * PSUj n g u * (s ^ k)⁻¹ = PSUj n g u * z ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hzk : z ^ k ∈ Subgroup.center (GL (Fin n) (PSUF g)) := Subgroup.pow_mem _ hzc k
        have hzk' := Subgroup.mem_center_iff.mp hzk
        calc s ^ (k + 1) * PSUj n g u * (s ^ (k + 1))⁻¹
            = s * (s ^ k * PSUj n g u * (s ^ k)⁻¹) * s⁻¹ := by group
          _ = s * (PSUj n g u * z ^ k) * s⁻¹ := by rw [ih]
          _ = s * PSUj n g u * (z ^ k * s⁻¹) := by group
          _ = s * PSUj n g u * (s⁻¹ * z ^ k) := by rw [hzk' s⁻¹]
          _ = (s * PSUj n g u * s⁻¹) * z ^ k := by group
          _ = PSUj n g u * z * z ^ k := by rw [hconj]
          _ = PSUj n g u * z ^ (k + 1) := by group
    have hzp : z ^ p = 1 := by
      have h1 := hpow p
      rw [hsp, inv_one, one_mul, mul_one] at h1
      have h2 : PSUj n g u * z ^ p = PSUj n g u * 1 := by rw [mul_one]; exact h1.symm
      exact mul_left_cancel h2
    have hcp : c ^ p = 1 := by
      have h2 : ((z ^ p : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) = 1 := by
        rw [hzp, Units.val_one]
      rw [Units.val_pow_eq_pow_val, hzmat, ← map_pow] at h2
      exact Matrix.scalar_inj.mp (h2.trans (map_one _).symm)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hH.prime.ne_zero] at hcp
      exact zero_ne_one hcp
    have hcN : c ^ (Nat.card (PSUF g) - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one c hc0
    have hcop : Nat.Coprime p (Nat.card (PSUF g)ˣ) :=
      (Nat.Prime.coprime_iff_not_dvd hH.prime).mpr hpF
    rw [Nat.card_units] at hcop
    have hc1 : c = 1 := by
      have h3 := pow_gcd_eq_one.mpr ⟨hcp, hcN⟩
      rwa [hcop, pow_one] at h3
    have hz1 : z = 1 := by
      apply Units.ext
      rw [hzmat, hc1, map_one, Units.val_one]
    have hfix : s * PSUj n g u * s⁻¹ = PSUj n g u := by rw [hconj, hz1, mul_one]
    show PSUj n g u ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g)))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    calc s * PSUj n g u = (s * PSUj n g u * s⁻¹) * s := by group
      _ = PSUj n g u * s := by rw [hfix]

end YT

end CFSG.StandardType.TableCRes
