module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListStd
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutLin
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutUni
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 psuConj psuField mem_unitaryIsom3 coe_suConj
  suConj psuConj_mk psuField_mul_psuConj_mul_inv exists_psuConj_mul_psuField
  eq_one_of_psuConj_mul_psuField_eq_one glAut_mem_unitaryIsom3)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

variable {K : Type} [Field K] {p f : ℕ}

theorem eq_of_conj_rel {A y s y' s' : GL (Fin 3) K} {c₁ c₂ ℓ ℓ' : Kˣ}
    (hy : A * y' * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c₁ * y)
    (hs : A * s' * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c₂ * s)
    (hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * s)
    (hys' : y' * s' * y'⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ' * s') : ℓ' = ℓ := by
  set C₁ := GeneralLinearGroup.scalar (Fin 3) c₁ with hC₁
  set C₂ := GeneralLinearGroup.scalar (Fin 3) c₂ with hC₂
  have hc : ∀ (u : Kˣ) (g : GL (Fin 3) K), g * GeneralLinearGroup.scalar (Fin 3) u =
      GeneralLinearGroup.scalar (Fin 3) u * g := Sec17.Proof17Res7.scalar_mul_comm
  have h1 : A * (y' * s' * y'⁻¹) * A⁻¹ = A * (GeneralLinearGroup.scalar (Fin 3) ℓ' * s') * A⁻¹ :=
    by rw [hys']
  have e1 : A * (y' * s' * y'⁻¹) * A⁻¹ =
      (A * y' * A⁻¹) * (A * s' * A⁻¹) * (A * y' * A⁻¹)⁻¹ := by group
  have e2 : A * (GeneralLinearGroup.scalar (Fin 3) ℓ' * s') * A⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ℓ' * (A * s' * A⁻¹) := by
    rw [show A * (GeneralLinearGroup.scalar (Fin 3) ℓ' * s') * A⁻¹ =
      (A * GeneralLinearGroup.scalar (Fin 3) ℓ') * s' * A⁻¹ by group, hc]
    group
  rw [e1, e2, hy, hs] at h1
  have e3 : C₁ * y * (C₂ * s) * (C₁ * y)⁻¹ = C₂ * (y * s * y⁻¹) := by
    calc C₁ * y * (C₂ * s) * (C₁ * y)⁻¹ = C₁ * (y * (C₂ * s) * y⁻¹) * C₁⁻¹ := by group
      _ = y * (C₂ * s) * y⁻¹ * C₁ * C₁⁻¹ := by rw [← hc c₁ (y * (C₂ * s) * y⁻¹)]
      _ = y * C₂ * s * y⁻¹ := by group
      _ = C₂ * y * s * y⁻¹ := by rw [hc c₂ y]
      _ = C₂ * (y * s * y⁻¹) := by group
  rw [e3, hys] at h1
  have h2 : C₂ * GeneralLinearGroup.scalar (Fin 3) ℓ = GeneralLinearGroup.scalar (Fin 3) ℓ' * C₂ :=
    by
      have := congrArg (fun g => g * s⁻¹) h1
      simpa [mul_assoc] using this
  rw [hC₂, ← map_mul, ← map_mul] at h2
  have h3 := Sec17.Proof17Res7.scalar_injective h2
  rw [mul_comm ℓ' c₂] at h3
  exact (mul_left_cancel h3).symm

theorem glAut_scalar (σ : K ≃+* K) (u : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) u) := by
  apply Units.ext
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, diagonal_map (map_zero σ), Units.coe_map]
  rfl

theorem inverseTranspose_scalar (u : Kˣ) :
    GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, ← map_inv, GeneralLinearGroup.coe_scalar,
    scalar_apply, diagonal_transpose]

theorem eq_one_of_inv_eq {G : Type*} [Group G] {ℓ : G} (hℓ3 : ℓ ^ 3 = 1) (h : ℓ⁻¹ = ℓ) :
    ℓ = 1 := by
  have h2 : ℓ * ℓ = 1 := by
    calc ℓ * ℓ = ℓ⁻¹ * ℓ := by rw [h]
      _ = 1 := inv_mul_cancel ℓ
  calc ℓ = ℓ ^ 3 * (ℓ * ℓ)⁻¹ := by group
    _ = 1 := by rw [hℓ3, h2]; group

theorem mem_unitaryIsom3_of_glPi (h : UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi false 3 (p ^ f) K) : g ∈ unitaryIsom3 h := by
  rw [mem_glPi_false h] at hg
  exact mem_unitaryIsom3.mpr hg

theorem congr_conjM'_true (hπ : true = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi true 3 (p ^ f) K) :
    MulAut.congr (pslEquivProjective (p ^ f) K) (Res8Hess.conjM' hπ hg) = conjAut 3 K g := by
  ext x
  obtain ⟨t, rfl⟩ := proj_surjective 3 K x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hΦs : (pslEquivProjective (p ^ f) K).symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  rw [hΦs, conjAut_proj]
  have e : Res8Hess.conjM' hπ hg (slToPsl (p ^ f) K t) =
      slToPsl (p ^ f) K (slConjugation 3 K g t) := by
    apply Subtype.ext
    rw [Res8Hess.coe_conjM', coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul, map_mul,
      map_inv]
  rw [e, pslEquivProjective_slToPsl]

theorem congr_conjM'_false (h : UnitaryFieldData p f K)
    (hπ : false = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi false 3 (p ^ f) K) :
    MulAut.congr (psuEquivUnitary h) (Res8Hess.conjM' hπ hg) =
      psuConj h ⟨g, mem_unitaryIsom3_of_glPi h hg⟩ := by
  ext x
  obtain ⟨t, rfl⟩ := unitaryProj_surjective h 3 x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hΦs : (psuEquivUnitary h).symm (unitaryProj h 3 t) = suToPsu p f K t := by
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  rw [hΦs, psuConj_unitaryProj]
  have e : Res8Hess.conjM' hπ hg (suToPsu p f K t) =
      suToPsu p f K (suConj h ⟨g, mem_unitaryIsom3_of_glPi h hg⟩ t) := by
    apply Subtype.ext
    rw [Res8Hess.coe_conjM', coe_suToPsu, coe_suToPsu, coe_suConj, Subgroup.coe_inv, map_mul,
      map_mul, map_inv]
  rw [e, psuEquivUnitary_suToPsu]

variable {π : Bool}

theorem coe_conjM'_pow (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (n : ℕ) (m : projImage (slPi π 3 (p ^ f) K)) :
    (((Res8Hess.conjM' hπ hg ^ n) m : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g ^ n * m * (ProjGenLinGroup.mk g ^ n)⁻¹ := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, Res8Hess.coe_conjM', pow_succ]
    group

theorem mk_comm_of_conjM'_comm (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {a b : GL (Fin 3) K}
    (ha : a ∈ glPi π 3 (p ^ f) K) (hb : b ∈ glPi π 3 (p ^ f) K)
    (h : Res8Hess.conjM' hπ ha * Res8Hess.conjM' hπ hb =
      Res8Hess.conjM' hπ hb * Res8Hess.conjM' hπ ha) :
    ProjGenLinGroup.mk a * ProjGenLinGroup.mk b = ProjGenLinGroup.mk b * ProjGenLinGroup.mk a := by
  set A := ProjGenLinGroup.mk a
  set B := ProjGenLinGroup.mk b
  have hu : (B * A)⁻¹ * (A * B) = 1 := by
    refine Sec13.eq_one_of_conj_eq_self hK hq hq2 fun x hx => ?_
    have h1 := congrArg (fun φ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      ((φ ⟨x, hx⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) h
    simp only [MulAut.mul_apply, Res8Hess.coe_conjM'] at h1
    calc (B * A)⁻¹ * (A * B) * x * ((B * A)⁻¹ * (A * B))⁻¹ =
        (B * A)⁻¹ * (A * (B * x * B⁻¹) * A⁻¹) * (B * A) := by group
      _ = (B * A)⁻¹ * (B * (A * x * A⁻¹) * B⁻¹) * (B * A) := by rw [h1]
      _ = x := by group
  calc A * B = B * A * ((B * A)⁻¹ * (A * B)) := by group
    _ = B * A := by rw [hu, mul_one]

theorem conjM'_eq_one (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {y s : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) (hy3 : Type123 π (p ^ f) K y 3)
    (hsSL : s ∈ slPi π 3 (p ^ f) K) (hsH : s ∈ glPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) {a : GL (Fin 3) K}
    (ha : a ∈ glPi π 3 (p ^ f) K)
    (has : Res8Hess.conjM' hπ ha * Res8Hess.conjM' hπ hsH =
      Res8Hess.conjM' hπ hsH * Res8Hess.conjM' hπ ha)
    (hay : Res8Hess.conjM' hπ ha * Res8Hess.conjM' hπ hy =
      Res8Hess.conjM' hπ hy * Res8Hess.conjM' hπ ha)
    {n : ℕ} (hn : ¬ 3 ∣ n) (han : Res8Hess.conjM' hπ ha ^ n = 1) :
    Res8Hess.conjM' hπ ha = 1 := by
  have hcs := mk_comm_of_conjM'_comm hπ hK hq hq2 ha hsH has
  have hcy := mk_comm_of_conjM'_comm hπ hK hq hq2 ha hy hay
  have hpow : ProjGenLinGroup.mk a ^ n = 1 := by
    refine Sec13.eq_one_of_conj_eq_self hK hq hq2 fun x hx => ?_
    have h1 := coe_conjM'_pow hπ ha n ⟨x, hx⟩
    rw [han, MulAut.one_apply] at h1
    exact h1.symm
  have hord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk a)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
  have h1 := eq_one_of_comm_ys hπ hK hq hy hy3 hsSL hsZ hs3 hys hcy hcs hord
  ext m
  rw [Res8Hess.coe_conjM', h1, MulAut.one_apply]
  group

theorem exists_comm_scalar (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {y s : GL (Fin 3) K} (hy3 : Type123 π (p ^ f) K y 3)
    (hsSL : s ∈ slPi π 3 (p ^ f) K) (hsZ : s ∉ StatedScalars (Fin 3) K)
    (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) :
    ∃ ℓ : Kˣ, y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * s ∧ ℓ ^ 3 = 1 ∧ ℓ ≠ 1 := by
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := exists_tau hK hq
  obtain ⟨ℓ, hℓ⟩ := hys
  have hysl : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * s := by
    rw [hℓ]
    group
  refine ⟨ℓ, hysl, pow_three_eq_one_of_conj_eq_scalar_mul hysl, fun h1 => ?_⟩
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hsSL).2
  refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ₀ hτ₀1 h3 hsdet hs3 hsZ ?_ hy3.2.2
  rw [h1, map_one, one_mul] at hysl
  calc y * s = y * s * y⁻¹ * y := by group
    _ = s * y := by rw [hysl]

theorem conj_eq_scalar_mul_of {A s s' : GL (Fin 3) K} {c : Kˣ}
    (h : GeneralLinearGroup.scalar (Fin 3) c = (s * A)⁻¹ * (A * s')) :
    A * s' * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * s := by
  have e : A * s' = s * A * GeneralLinearGroup.scalar (Fin 3) c := by rw [h]; group
  calc A * s' * A⁻¹ = s * (A * GeneralLinearGroup.scalar (Fin 3) c) * A⁻¹ := by rw [e]; group
    _ = s * (GeneralLinearGroup.scalar (Fin 3) c * A) * A⁻¹ := by
        rw [Sec17.Proof17Res7.scalar_mul_comm c A]
    _ = s * GeneralLinearGroup.scalar (Fin 3) c := by group
    _ = GeneralLinearGroup.scalar (Fin 3) c * s := Sec17.Proof17Res7.scalar_mul_comm c s

theorem rigid_prime (hπ : π = false → UnitaryFieldData p 1 K) (hK : PiField π p 1 K)
    (hq : ModThree π (p ^ 1)) (hq2 : 2 < p ^ 1) {y s : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ 1) K) (hy3 : Type123 π (p ^ 1) K y 3)
    (hsSL : s ∈ slPi π 3 (p ^ 1) K) (hsH : s ∈ glPi π 3 (p ^ 1) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K)
    (τ : MulAut (projImage (slPi π 3 (p ^ 1) K)))
    (hτs : τ * Res8Hess.conjM' hπ hsH = Res8Hess.conjM' hπ hsH * τ)
    (hτy : τ * Res8Hess.conjM' hπ hy = Res8Hess.conjM' hπ hy * τ)
    {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : τ ^ n = 1) : τ = 1 := by
  have := hK.finite
  have hp : p.Prime := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, hysl, hℓ3, hℓ1⟩ := exists_comm_scalar hπ hK hq hy3 hsSL hsZ hs3 hys
  have hinner : ∀ (a : GL (Fin 3) K) (ha : a ∈ glPi π 3 (p ^ 1) K),
      τ = Res8Hess.conjM' hπ ha → τ = 1 := by
    intro a ha hτa
    subst hτa
    exact conjM'_eq_one hπ hK hq hq2 hy hy3 hsSL hsH hsZ hs3 hys ha hτs hτy hn hτn
  cases π
  ·
    have h := hK.unitary
    have hcard : Nat.card K = p ^ 2 := by rw [h.card]
    set Φ := psuEquivUnitary h with hΦ
    set τ' := MulAut.congr Φ τ with hτ'
    obtain ⟨A, σ, hA⟩ := exists_psuConj_mul_psuField hq2 τ'
    set s' : unitaryIsom3 h := ⟨s, mem_unitaryIsom3_of_glPi h hsH⟩ with hs'
    set y' : unitaryIsom3 h := ⟨y, mem_unitaryIsom3_of_glPi h hy⟩ with hy'
    have hτs' : τ' * psuConj h s' = psuConj h s' * τ' := by
      rw [hτ', hs', ← congr_conjM'_false h hπ hsH, ← map_mul (MulAut.congr Φ),
        ← map_mul (MulAut.congr Φ), hτs]
    have hτy' : τ' * psuConj h y' = psuConj h y' * τ' := by
      rw [hτ', hy', ← congr_conjM'_false h hπ hy, ← map_mul (MulAut.congr Φ),
        ← map_mul (MulAut.congr Φ), hτy]
    rcases Sec17.Proof17Res7.ringEquiv_eq_one_or_frob hp hcard σ with rfl | hσ
    ·
      rw [map_one, mul_one] at hA
      have hAg : (A : GL (Fin 3) K) ∈ glPi false 3 (p ^ 1) K := by
        rw [mem_glPi_false h]
        exact mem_unitaryIsom3.mp A.2
      refine hinner A hAg ((MulAut.congr Φ).injective ?_)
      rw [← hτ', hA, congr_conjM'_false h hπ hAg]
    ·
      exfalso
      have key : ∀ (b : unitaryIsom3 h), τ' * psuConj h b = psuConj h b * τ' →
          ∃ c : Kˣ, (A : GL (Fin 3) K) * glAut σ (b : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
            GeneralLinearGroup.scalar (Fin 3) c * b := by
        intro b hb
        have hf := psuField_mul_psuConj_mul_inv σ b
        have e1 : psuConj h (A * ⟨glAut σ b, glAut_mem_unitaryIsom3 σ b.2⟩) * psuField h σ =
            psuConj h (b * A) * psuField h σ := by
          rw [map_mul, map_mul, ← hf]
          rw [hA] at hb
          calc psuConj h A * (psuField h σ * psuConj h b * (psuField h σ)⁻¹) * psuField h σ =
              psuConj h A * psuField h σ * psuConj h b := by group
            _ = psuConj h b * (psuConj h A * psuField h σ) := hb
            _ = psuConj h b * psuConj h A * psuField h σ := by group
        have e2 := mul_right_cancel e1
        have e3 : psuConj h ((b * A)⁻¹ * (A * ⟨glAut σ b, glAut_mem_unitaryIsom3 σ b.2⟩)) = 1 := by
          rw [map_mul, map_inv, e2, inv_mul_cancel]
        obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one
          ((b * A)⁻¹ * (A * ⟨glAut σ b, glAut_mem_unitaryIsom3 σ b.2⟩)) 1
          (by rw [map_one (psuField h), mul_one]; exact e3)
        refine ⟨c, conj_eq_scalar_mul_of ?_⟩
        rw [← hc]
        rfl
      obtain ⟨c₁, hc₁⟩ := key y' hτy'
      obtain ⟨c₂, hc₂⟩ := key s' hτs'
      have hσys : glAut σ y * glAut σ s * (glAut σ y)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) ℓ) * glAut σ s := by
        rw [← map_inv, ← map_mul, ← map_mul, hysl, map_mul, glAut_scalar]
      have hrel := eq_of_conj_rel hc₁ hc₂ hysl hσys
      have hp3 : p % 3 = 2 := by
        have := hq
        change p ^ 1 % 3 = 2 at this
        rwa [pow_one] at this
      have hσℓ : Units.map (σ : K →* K) ℓ = ℓ⁻¹ := by
        apply Units.ext
        rw [Units.coe_map]
        change σ (ℓ : K) = ((ℓ⁻¹ : Kˣ) : K)
        rw [hσ, ← Units.val_pow_eq_pow_val]
        congr 1
        rw [← Nat.mod_add_div p 3, hp3, pow_add, pow_mul, hℓ3, one_pow, mul_one]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hℓ3])
      rw [hσℓ] at hrel
      exact hℓ1 (eq_one_of_inv_eq hℓ3 hrel)
  ·
    have hcard : Nat.card K = p := by
      have := hK.card
      change Nat.card K = p ^ 1 at this
      rwa [pow_one] at this
    set Φ := pslEquivProjective (p ^ 1) K with hΦ
    set τ' := MulAut.congr Φ τ with hτ'
    obtain ⟨A, σ, ε, hε, hA⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 τ'
    rw [Sec17.Proof17Res7.ringEquiv_eq_one_of_card hcard σ, map_one, mul_one] at hA
    have hτs' : τ' * conjAut 3 K s = conjAut 3 K s * τ' := by
      rw [hτ', ← congr_conjM'_true hπ hsH, ← map_mul (MulAut.congr Φ),
        ← map_mul (MulAut.congr Φ), hτs]
    have hτy' : τ' * conjAut 3 K y = conjAut 3 K y * τ' := by
      rw [hτ', ← congr_conjM'_true hπ hy, ← map_mul (MulAut.congr Φ),
        ← map_mul (MulAut.congr Φ), hτy]
    interval_cases ε
    ·
      rw [pow_zero, mul_one] at hA
      refine hinner A (mem_glPi_true _ _) ((MulAut.congr Φ).injective ?_)
      rw [← hτ', hA, congr_conjM'_true hπ (mem_glPi_true _ _)]
    ·
      exfalso
      rw [pow_one] at hA
      have key : ∀ b : GL (Fin 3) K, τ' * conjAut 3 K b = conjAut 3 K b * τ' →
          ∃ c : Kˣ, A * GeneralLinearGroup.inverseTranspose b * A⁻¹ =
            GeneralLinearGroup.scalar (Fin 3) c * b := by
        intro b hb
        rw [hA] at hb
        have e1 : conjAut 3 K (A * GeneralLinearGroup.inverseTranspose b) * dualAut 3 K =
            conjAut 3 K (b * A) * dualAut 3 K := by
          rw [map_mul, map_mul, mul_assoc, ← dualAut_mul_conjAut, ← mul_assoc, hb, mul_assoc]
        have e2 := mul_right_cancel e1
        have e3 : conjAut 3 K ((b * A)⁻¹ * (A * GeneralLinearGroup.inverseTranspose b)) *
            fieldAut 3 K 1 = 1 := by
          rw [map_one, mul_one, map_mul, map_inv, e2, inv_mul_cancel]
        obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ 1 e3
        exact ⟨c, conj_eq_scalar_mul_of hc⟩
      obtain ⟨c₁, hc₁⟩ := key y hτy'
      obtain ⟨c₂, hc₂⟩ := key s hτs'
      have hδys : GeneralLinearGroup.inverseTranspose y * GeneralLinearGroup.inverseTranspose s *
          (GeneralLinearGroup.inverseTranspose y)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) ℓ⁻¹ * GeneralLinearGroup.inverseTranspose s := by
        rw [← map_inv, ← map_mul, ← map_mul, hysl, map_mul, inverseTranspose_scalar]
      have hrel := eq_of_conj_rel hc₁ hc₂ hysl hδys
      exact hℓ1 (eq_one_of_inv_eq hℓ3 hrel)

end CFSG.RankThree.PartTwo.Sec14.L3PGL
