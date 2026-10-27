module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Models.BenderSuzuki
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model

public section

namespace CFSG.Quasithin.H13.KG115U3

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
  CFSG.Quasithin.H13.KG14726
open scoped Matrix LinearAlgebra.Projectivization Pointwise commutatorElement

theorem two_pow_add_one_ne_three_pow {f k : ℕ} (hf : 2 ≤ f) (h3 : f ≠ 3) :
    2 ^ f + 1 ≠ 3 ^ k := by
  intro h
  rcases Nat.lt_or_ge f 4 with hf4 | hf4
  · have hf2 : f = 2 := by omega
    subst hf2
    have hk : k ≤ 2 := by
      by_contra hk
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> omega
  ·
    have h8 : 2 ^ 3 ∣ 2 ^ f := Nat.pow_dvd_pow 2 (by omega)
    norm_num at h8
    have hk2 : k % 2 = 0 := by
      by_contra hk
      obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      have h9 : 3 ^ (2 * m + 1) % 8 = 3 := by
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      omega
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    obtain ⟨a, ha⟩ : ∃ a, a = 3 ^ m := ⟨_, rfl⟩
    have ha1 : 1 ≤ a := ha ▸ Nat.one_le_pow _ _ (by norm_num)
    have hsq : 3 ^ (2 * m) = a * a := by rw [ha, ← pow_add, two_mul]
    rw [hsq] at h
    have hfac : 2 ^ f = (a - 1) * (a + 1) := by
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha1
      rw [Nat.add_sub_cancel]
      have : (b + 1) * (b + 1) = b * (b + 1 + 1) + 1 := by ring
      omega
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hfac.symm)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ hfac.symm)
    have hij : 2 ^ j = 2 ^ i + 2 := by omega
    rcases i with _ | _ | i
    · rcases j with _ | j
      · simp at hij
      · rw [pow_succ] at hij
        omega
    · have ha3 : a = 3 := by simp at hi; omega
      rw [ha3] at hfac
      have : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
      omega
    · have h4i : 4 ∣ 2 ^ (i + 2) := ⟨2 ^ i, by rw [pow_add]; ring⟩
      rcases j with _ | _ | j
      · simp at hij
      · simp at hij
      · have h4j : 4 ∣ 2 ^ (j + 2) := ⟨2 ^ j, by rw [pow_add]; ring⟩
        omega

theorem exists_prime_ge_five_dvd {f : ℕ} (hf : 2 ≤ f) (h3 : f ≠ 3) :
    ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ 2 ^ f + 1 := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f + 1 → d = 3 := by
    intro d hd hdvd
    have h5 : d < 5 := by
      by_contra h
      exact hcon d hd (by omega) hdvd
    interval_cases d
    · exact absurd hd (by decide)
    · exact absurd hd (by decide)
    · omega
    · rfl
    · exact absurd hd (by decide)
  have h := Nat.eq_prime_pow_of_unique_prime_dvd (by positivity) hall
  exact two_pow_add_one_ne_three_pow hf h3 h

section Action

variable {G Ω : Type*} [Group G] (rho : G →* Equiv.Perm Ω) (pinf : Ω) {R : Subgroup G}

theorem eq_one_of_fix (hreg : ∀ a b : Ω, a ≠ pinf → b ≠ pinf → ∃! r : R, rho r a = b) {r : G}
    (hr : r ∈ R) {a : Ω} (ha : a ≠ pinf) (h : rho r a = a) : r = 1 := by
  obtain ⟨r₀, -, huniq⟩ := hreg a a ha ha
  have e1 := huniq ⟨r, hr⟩ h
  have e2 := huniq 1 (by beta_reduce; rw [Subgroup.coe_one, map_one, Equiv.Perm.one_apply])
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem not_comm_of_orderOf_eq_three (hinj : Function.Injective rho) (hR2 : IsPGroup 2 R)
    (hfix : ∀ r ∈ R, rho r pinf = pinf)
    (hreg : ∀ a b : Ω, a ≠ pinf → b ≠ pinf → ∃! r : R, rho r a = b)
    (h3pts : ∀ a : Ω, ∃ b : Ω, b ≠ pinf ∧ b ≠ a) {y : G} (hy3 : orderOf y = 3)
    (hyR : ∀ s ∈ R, s * y = y * s) : False := by
  have hcomm' : ∀ r ∈ R, ∀ a : Ω, rho r (rho y a) = rho y (rho r a) := by
    intro r hr a
    rw [← Equiv.Perm.mul_apply, ← map_mul, hyR r hr, map_mul, Equiv.Perm.mul_apply]
  have hyinf : rho y pinf = pinf := by
    by_contra hne
    obtain ⟨b, hb, hba⟩ := h3pts (rho y pinf)
    obtain ⟨r, hr, -⟩ := hreg (rho y pinf) b hne hb
    have : rho (r : G) (rho y pinf) = rho y pinf := by
      rw [hcomm' r r.2, hfix r r.2]
    exact hba (hr.symm.trans this)
  have hya : ∀ a : Ω, a ≠ pinf → rho y a = a := by
    intro a ha
    have hya1 : rho y a ≠ pinf := by
      intro h
      apply ha
      apply (rho y).injective
      rw [h, hyinf]
    obtain ⟨ρ, hρ, -⟩ := hreg a (rho y a) ha hya1
    have hc : ∀ n : ℕ, (ρ : G) * y ^ n = y ^ n * ρ := fun n =>
      (Commute.pow_right (hyR ρ ρ.2 : Commute (ρ : G) y) n).eq
    have hpow : ∀ n : ℕ, rho (y ^ n) a = rho ((ρ : G) ^ n) a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc rho (y ^ (n + 1)) a = rho (y ^ n) (rho y a) := by
              rw [pow_succ, map_mul, Equiv.Perm.mul_apply]
          _ = rho (y ^ n) (rho ρ a) := by rw [hρ]
          _ = rho ρ (rho (y ^ n) a) := by
              rw [← Equiv.Perm.mul_apply, ← map_mul, ← hc n, map_mul, Equiv.Perm.mul_apply]
          _ = rho ρ (rho ((ρ : G) ^ n) a) := by rw [ih]
          _ = rho ((ρ : G) ^ (n + 1)) a := by
              rw [pow_succ', map_mul, Equiv.Perm.mul_apply]
    have h3 := hpow 3
    have hy3' : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy3] at this
    rw [hy3', map_one, Equiv.Perm.one_apply] at h3
    have hρ3 : (ρ : G) ^ 3 = 1 := eq_one_of_fix rho pinf hreg (R.pow_mem ρ.2 3) ha h3.symm
    have hρ1 : (ρ : G) = 1 := by
      obtain ⟨k, hk⟩ := (hR2 ρ)
      have hk' : (ρ : G) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have h1 := orderOf_dvd_of_pow_eq_one hρ3
      have h2 : orderOf (ρ : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h3' : orderOf (ρ : G) ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num))] at h3'
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3')
    rw [← hρ, hρ1, map_one, Equiv.Perm.one_apply]
  have hy1 : y = 1 := by
    apply hinj
    rw [map_one]
    ext a
    by_cases ha : a = pinf
    · rw [ha, hyinf, Equiv.Perm.one_apply]
    · rw [hya a ha, Equiv.Perm.one_apply]
  rw [hy1, orderOf_one] at hy3
  omega

theorem fix_of_comm (hreg : ∀ a b : Ω, a ≠ pinf → b ≠ pinf → ∃! r : R, rho r a = b)
    (hfix : ∀ r ∈ R, rho r pinf = pinf) {l : G} (hlR : l ∈ R) (hl1 : l ≠ 1) {g : G}
    (hg : g * l = l * g) : rho g pinf = pinf := by
  by_contra hne
  apply hl1
  apply eq_one_of_fix rho pinf hreg hlR hne
  rw [← Equiv.Perm.mul_apply, ← map_mul, ← hg, map_mul, Equiv.Perm.mul_apply, hfix l hlR]

theorem kg115At_conj {X : Type} [Group X] {S : Subgroup X} {l : X} (g : X)
    (h : KG115At X S l) : KG115At X (S.map (MulAut.conj g).toMonoidHom) (g * l * g⁻¹) := by
  intro D N hSD hDl hy hND hodd hcard h27
  set φ : X ≃* X := MulAut.conj g⁻¹ with hφ
  have hφx : ∀ x : X, φ x = g⁻¹ * x * g := fun x => by
    rw [hφ, MulAut.conj_apply, inv_inv]
  refine h (D.map φ.toMonoidHom) (N.map φ.toMonoidHom) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    refine ⟨g * s * g⁻¹, hSD ⟨s, hs, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hφx]
    group
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := hDl d hd
    rw [MulEquiv.coe_toMonoidHom, hφx]
    calc g⁻¹ * d * g * l = g⁻¹ * (d * (g * l * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * l * g⁻¹) * d) * g := by rw [h1]
      _ = l * (g⁻¹ * d * g) := by group
  · obtain ⟨y, hyN, hy3⟩ := hy
    exact ⟨φ y, ⟨y, hyN, rfl⟩, by rw [MulEquiv.orderOf_eq]; exact hy3⟩
  · rw [← Subgroup.map_equiv_normalizer_eq, hND]
  · intro ℓ hℓ hp hp2
    have h1 : g * ℓ * g⁻¹ * (g * l * g⁻¹) = g * l * g⁻¹ * (g * ℓ * g⁻¹) := by
      calc g * ℓ * g⁻¹ * (g * l * g⁻¹) = g * (ℓ * l) * g⁻¹ := by group
        _ = g * (l * ℓ) * g⁻¹ := by rw [hℓ]
        _ = g * l * g⁻¹ * (g * ℓ * g⁻¹) := by group
    have ho : orderOf (g * ℓ * g⁻¹) = orderOf ℓ := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    refine ⟨g * ℓ * g⁻¹, hodd _ h1 (ho ▸ hp) (ho ▸ hp2), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hφx]
    group
  · rwa [Subgroup.card_map_of_injective φ.injective]
  · rwa [Subgroup.card_map_of_injective φ.injective]

theorem commutatorElement_mul_central {M : Type*} [Group M] {x x' c c' : M}
    (h1 : Commute c x') (h2 : Commute c' x) (h3 : Commute c c') :
    ⁅x * c, x' * c'⁆ = ⁅x, x'⁆ := by
  have h2' : c' * x⁻¹ = x⁻¹ * c' := h2.inv_right.eq
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (x' * c') * (x * c)⁻¹ * (x' * c')⁻¹
      = x * (c * x') * c' * c⁻¹ * x⁻¹ * c'⁻¹ * x'⁻¹ := by group
    _ = x * (x' * c) * c' * c⁻¹ * x⁻¹ * c'⁻¹ * x'⁻¹ := by rw [h1.eq]
    _ = x * x' * (c * c') * c⁻¹ * x⁻¹ * c'⁻¹ * x'⁻¹ := by group
    _ = x * x' * (c' * c) * c⁻¹ * x⁻¹ * c'⁻¹ * x'⁻¹ := by rw [h3.eq]
    _ = x * x' * (c' * x⁻¹) * c'⁻¹ * x'⁻¹ := by group
    _ = x * x' * (x⁻¹ * c') * c'⁻¹ * x'⁻¹ := by rw [h2']
    _ = x * x' * x⁻¹ * x'⁻¹ := by group

end Action

section Model

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] def fstZero : Subgroup (hermitianUnipotentCoord J) where
  carrier := {z | z.1.1 = 0}
  mul_mem' {z w} hz hw := by
    show (hermitianUnipotentMul J z w).1.1 = 0
    simp only [hermitianUnipotentMul]
    rw [show z.1.1 = 0 from hz, show w.1.1 = 0 from hw, add_zero]
  one_mem' := rfl
  inv_mem' {z} hz := by
    show (hermitianUnipotentInv J z).1.1 = 0
    simp only [hermitianUnipotentInv]
    rw [show z.1.1 = 0 from hz, neg_zero]

theorem torus_comm {k : Kˣ} (hk : J.conj (k : K) * k = 1) {z : hermitianUnipotentCoord J}
    (hz : z.1.1 = 0) :
    hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ z =
      hermitianUnipotentPSU J hJ z * hermitianTorusPSU J hJ k := by
  rw [hermitianTorusPSU_mul_unipotent]
  congr 2
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hc0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  apply Subtype.ext
  apply Prod.ext
  · simp [hermitianTorusAction, hz]
  · simp only [hermitianTorusAction]
    have : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 1 := by
      rw [← mul_inv, hk, inv_one]
    rw [mul_assoc, this, mul_one]

theorem torus_ne_one {k : Kˣ} (hk : J.conj (k : K) * k = 1) (hk3 : (k : K) ^ 3 ≠ 1) :
    hermitianTorusPSU J hJ k ≠ 1 := by
  intro htorus
  have hpgl : Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1 :=
    congrArg Subtype.val htorus
  have hcenter : hermitianTorusGL J k ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
    exact hpgl
  rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter with ⟨c, hc⟩
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hc
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
  rw [hermitianTorusGL_val] at h11 h22
  simp [hermitianTorusMatrix, Matrix.scalar_apply] at h11 h22
  have hmid : J.conj (k : K) * (k : K)⁻¹ = (k : K) := h11.symm.trans h22
  have hsq : J.conj (k : K) = (k : K) * (k : K) := by
    have h := congrArg (fun x : K => x * (k : K)) hmid
    simpa [mul_assoc, Units.ne_zero k] using h
  apply hk3
  calc (k : K) ^ 3 = ((k : K) * (k : K)) * (k : K) := by ring
    _ = J.conj (k : K) * (k : K) := by rw [← hsq]
    _ = 1 := hk

theorem orderOf_torus {k : Kˣ} (hk : J.conj (k : K) * k = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hkp : orderOf k = p) : orderOf (hermitianTorusPSU J hJ k) = p := by
  have : Fact p.Prime := ⟨hp⟩
  apply orderOf_eq_prime
  · rw [← map_pow, ← hkp, pow_orderOf_eq_one, map_one]
  · apply torus_ne_one J hJ hk
    intro h3
    have h3' : k ^ 3 = 1 := Units.ext (by simpa using h3)
    have := orderOf_dvd_of_pow_eq_one h3'
    rw [hkp] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

@[expose] def fstHom : hermitianUnipotentCoord J →* Multiplicative K where
  toFun z := Multiplicative.ofAdd z.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fstHom_apply (z : hermitianUnipotentCoord J) :
    fstHom J z = Multiplicative.ofAdd z.1.1 := rfl

theorem comm_of_fst_eq_zero {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0)
    (w : hermitianUnipotentCoord J) : z * w = w * z := by
  apply Subtype.ext
  apply Prod.ext
  · show z.1.1 + w.1.1 = w.1.1 + z.1.1
    ring
  · show z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 = w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1
    rw [hz, map_zero]
    ring

theorem fst_torusAction (k : Kˣ) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.1 = z.1.1 * k * (J.conj (k : K))⁻¹ ^ 2 := rfl

theorem snd_torusAction (k : Kˣ) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.2 = z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹ := rfl

theorem torus_eq_one_of {k : Kˣ} (hk : J.conj (k : K) * k = 1) (hk3 : (k : K) ^ 3 = 1) :
    hermitianTorusPSU J hJ k = 1 := by
  have hσ : J.conj (k : K) = (k : K)⁻¹ := eq_inv_of_mul_eq_one_left hk
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨k, ?_⟩
  rw [hermitianTorusGL_val]
  have hinv : (k : K)⁻¹ = (k : K) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hk3)
  have h1 : (k : K)⁻¹ * (k : K)⁻¹ = k := by
    rw [hinv, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hk3, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, Matrix.scalar_apply, hσ, inv_inv, h1, Matrix.diagonal]

theorem torus_ne_one_of_fixed {k : Kˣ} (hk : J.conj (k : K) = k) (hk2 : (k : K) ^ 2 ≠ 1) :
    hermitianTorusPSU J hJ k ≠ 1 := by
  intro htorus
  have hpgl : Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1 :=
    congrArg Subtype.val htorus
  have hcenter : hermitianTorusGL J k ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
    exact hpgl
  rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter with ⟨c, hc⟩
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
  rw [hermitianTorusGL_val] at h00 h22
  simp [hermitianTorusMatrix, Matrix.scalar_apply, hk] at h00 h22
  apply hk2
  have h : (k : K)⁻¹ = k := h00.symm.trans h22
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  calc (k : K) ^ 2 = (k : K) * k := by ring
    _ = (k : K) * (k : K)⁻¹ := by rw [h]
    _ = 1 := mul_inv_cancel₀ hk0

end Model

section Main

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)

theorem sq_sub_one_eq (q : ℕ) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  have := Nat.sq_sub_sq q 1
  simpa using this

theorem kg115Excluded_psu (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
    (h3 : f ≠ 3) (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f) :
    KG115Excluded (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have : IsSimpleGroup G := huppert_II_10_13 J q (by omega) hKcard hfixed
  rcases huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, pinf, hinj, -, -,
      ⟨R, H, hRle, -, -, -, -, -, hRcard, hcomm, -, -, hreg, ⟨coord, hcoord⟩, -, -⟩, -,
      hGcard, -⟩
  have hcoordU : ∀ z, ((coord z : R) : G) = hermitianUnipotentPSU J hJ z := by
    intro z
    obtain ⟨M, hM, hzM⟩ := hcoord z
    apply Subtype.ext
    rw [hzM, hermitianUnipotentPSU_val]
    congr 1
    exact Units.ext (by rw [hM]; rfl)
  have hRU : ∀ g ∈ R, ∃ z, hermitianUnipotentPSU J hJ z = g := by
    intro g hg
    obtain ⟨z, hz⟩ := coord.surjective ⟨g, hg⟩
    exact ⟨z, by rw [← hcoordU, hz]⟩
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := f * 3) (by rw [hRcard, hq, ← pow_mul])
  have hRi : ¬ 2 ∣ R.index := by
    have hd : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
      have h1 : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, sq_sub_one_eq q⟩
      exact ((Nat.gcd_dvd_right _ _).trans h1).mul_left _
    have hG' : Nat.card G * Nat.gcd 3 (q + 1) = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
      rw [hGcard]
      exact Nat.div_mul_cancel hd
    have hcm := R.card_mul_index
    rw [hRcard] at hcm
    have hq3 : 0 < q ^ 3 := by positivity
    have key : R.index * Nat.gcd 3 (q + 1) = (q ^ 3 + 1) * (q ^ 2 - 1) := by
      apply Nat.eq_of_mul_eq_mul_left hq3
      calc q ^ 3 * (R.index * Nat.gcd 3 (q + 1)) = Nat.card G * Nat.gcd 3 (q + 1) := by
            rw [← hcm]; ring
        _ = q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by rw [hG']; ring
    have h2q : 2 ∣ q := dvd_pow_self 2 (by omega)
    have h2q2 : 2 ∣ q ^ 2 := dvd_pow h2q (by norm_num)
    have h2q3 : 2 ∣ q ^ 3 := dvd_pow h2q (by norm_num)
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    intro h2
    have h2' : 2 ∣ (q ^ 3 + 1) * (q ^ 2 - 1) := key ▸ Dvd.dvd.mul_right h2 _
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2' with h | h <;> omega
  refine kg115Excluded_of_prime_conj hR2 hRi ?_ ?_
  ·
    intro y hy3 hyR
    have h3pts : ∀ a : Ω, ∃ b : Ω, b ≠ pinf ∧ b ≠ a := by
      intro a
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have : Fintype Ω := Fintype.ofFinite Ω
      have : DecidableEq Ω := Classical.decEq Ω
      have hsub : (Finset.univ : Finset Ω) ⊆ {pinf, a} := by
        intro b _
        by_cases hb : b = pinf
        · simp [hb]
        · simp [hcon b hb]
      have h1 := Finset.card_le_card hsub
      have h2 : ({pinf, a} : Finset Ω).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hΩcard] at h1
      have : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
      omega
    exact not_comm_of_orderOf_eq_three rho pinf hinj hR2 (fun r hr => hRle hr) hreg h3pts hy3 hyR
  ·
    intro u hu hcent hu1
    have huZ : (⟨u, hu⟩ : R) ∈ Subgroup.center R :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcent g g.2)
    rw [← hcomm] at huZ
    have hle : commutator R ≤
        ((fstZero J).map (hermitianUnipotentPSU J hJ)).subgroupOf R := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨z₁, hz₁⟩ := hRU g₁ g₁.2
      obtain ⟨z₂, hz₂⟩ := hRU g₂ g₂.2
      rw [Subgroup.mem_subgroupOf]
      refine ⟨⁅z₁, z₂⁆, CFSG.BenderSuzuki.Background.hermitianUnipotent_commutator_fst J z₁ z₂,
        ?_⟩
      rw [map_commutatorElement, hz₁, hz₂]
      simp [commutatorElement_def]
    obtain ⟨z, hz0, hzu⟩ := hle huZ
    obtain ⟨p, hp, hp5, hpq⟩ := exists_prime_ge_five_dvd hf h3
    have : Fact p.Prime := ⟨hp⟩
    have hcardK : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hKcard]
    have hpK : p ∣ Nat.card Kˣ := by
      rw [hcardK]
      exact hpq.trans ⟨q - 1, sq_sub_one_eq q⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' p hpK
    have hkq : k ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hk]; exact hpq)
    have hnorm : J.conj (k : K) * k = 1 := by
      rw [huppert_II_10_4_conj_eq_frobenius J q hKcard hfixed (k : K), ← pow_succ,
        ← Units.val_pow_eq_pow_val, hkq, Units.val_one]
    refine ⟨hermitianTorusPSU J hJ k, ?_, p, hp, hp5, orderOf_torus J hJ hnorm hp hp5 hk⟩
    have hzu' : hermitianUnipotentPSU J hJ z = u := hzu
    rw [← hzu']
    exact torus_comm J hJ hnorm hz0

end Main

section Eight

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)

theorem kg115Excluded_psu8 (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hKcard : Nat.card K = (2 ^ 3) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ 3) :
    KG115Excluded (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := 2 ^ 3 with hq
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have : IsSimpleGroup G := huppert_II_10_13 J q (by norm_num [hq]) hKcard hfixed
  rcases huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, pinf, hinj, -, -,
      ⟨R, H, hRle, hHle, hN, hinf, hsup, -, hRcard, hcomm, hcommcard, -, hreg, ⟨coord, hcoord⟩,
        hHcoord, hHsurj⟩, -, hGcard, -⟩
  set U := hermitianUnipotentPSU J hJ with hUdef
  set T := hermitianTorusPSU J hJ with hTdef
  have hUinj : Function.Injective U :=
    CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hcoordU : ∀ z, ((coord z : R) : G) = U z := by
    intro z
    obtain ⟨M, hM, hzM⟩ := hcoord z
    apply Subtype.ext
    rw [hzM, hUdef, hermitianUnipotentPSU_val]
    congr 1
    exact Units.ext (by rw [hM]; rfl)
  have hRU : ∀ g ∈ R, ∃ z, U z = g := by
    intro g hg
    obtain ⟨z, hz⟩ := coord.surjective ⟨g, hg⟩
    exact ⟨z, by rw [← hcoordU, hz]⟩
  have hUR : ∀ z, U z ∈ R := fun z => hcoordU z ▸ (coord z).2
  have hHT : ∀ h ∈ H, ∃ k : Kˣ, h = T k := by
    intro h hh
    obtain ⟨k, M, hM, hhM⟩ := hHcoord ⟨h, hh⟩
    refine ⟨k, Subtype.ext ?_⟩
    rw [hhM, hTdef, hermitianTorusPSU_val]
    congr 1
    exact Units.ext (by rw [hM]; rfl)
  have hTH : ∀ k : Kˣ, T k ∈ H := by
    intro k
    obtain ⟨h, M, hM, hhM⟩ := hHsurj k
    have : (h : G) = T k := by
      apply Subtype.ext
      rw [hhM, hTdef, hermitianTorusPSU_val]
      congr 1
      exact Units.ext (by rw [hM]; rfl)
    rw [← this]
    exact h.2
  have hstab : ∀ x : G, rho x pinf = pinf → ∃ r ∈ R, ∃ k : Kˣ, x = r * T k := by
    intro x hx
    have hxU : x ∈ R ⊔ H := by rw [hsup]; exact hx
    have hHN : H ≤ Subgroup.normalizer (R : Set G) := hHle.trans hN
    have hx' : x ∈ (R : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left R H hHN]
      exact hxU
    obtain ⟨r, hr, h, hh, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨k, rfl⟩ := hHT h hh
    exact ⟨r, hr, k, rfl⟩
  have hTnorm : ∀ k : Kˣ, ∀ r ∈ R, T k * r * (T k)⁻¹ ∈ R := by
    intro k r hr
    exact (Subgroup.mem_normalizer_iff.mp (hN (hHle (hTH k))) r).mp hr
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 3 * 3) (by rw [hRcard, hq, ← pow_mul])
  have hRi : ¬ 2 ∣ R.index := by
    have hcm := R.card_mul_index
    rw [hRcard, hGcard] at hcm
    norm_num [hq] at hcm
    omega
  have h3pts : ∀ a : Ω, ∃ b : Ω, b ≠ pinf ∧ b ≠ a := by
    intro a
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have : Fintype Ω := Fintype.ofFinite Ω
    have : DecidableEq Ω := Classical.decEq Ω
    have hsub : (Finset.univ : Finset Ω) ⊆ {pinf, a} := by
      intro b _
      by_cases hb : b = pinf
      · simp [hb]
      · simp [hcon b hb]
    have h1 := Finset.card_le_card hsub
    have h2 : ({pinf, a} : Finset Ω).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hΩcard] at h1
    norm_num [hq] at h1
    omega
  have hno3 : ∀ y : G, orderOf y = 3 → ¬ ∀ s ∈ R, s * y = y * s := fun y hy3 hyR =>
    not_comm_of_orderOf_eq_three rho pinf hinj hR2 (fun r hr => hRle hr) hreg h3pts hy3 hyR
  have hcenterR : ∀ u ∈ R, (∀ s ∈ R, s * u = u * s) → ∃ z, U z = u ∧ z.1.1 = 0 := by
    intro u hu hcent
    have huZ : (⟨u, hu⟩ : R) ∈ Subgroup.center R :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcent g g.2)
    rw [← hcomm] at huZ
    have hle : commutator R ≤ ((fstZero J).map U).subgroupOf R := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨z₁, hz₁⟩ := hRU g₁ g₁.2
      obtain ⟨z₂, hz₂⟩ := hRU g₂ g₂.2
      rw [Subgroup.mem_subgroupOf]
      refine ⟨⁅z₁, z₂⁆, CFSG.BenderSuzuki.Background.hermitianUnipotent_commutator_fst J z₁ z₂,
        ?_⟩
      rw [map_commutatorElement, hz₁, hz₂]
      simp [commutatorElement_def]
    obtain ⟨z, hz0, hzu⟩ := hle huZ
    exact ⟨z, hzu, hz0⟩
  have hfst_onto : ∀ t : K, ∃ w : hermitianUnipotentCoord J, w.1.1 = t := by
    have e : hermitianUnipotentCoord J ≃* R :=
      (MonoidHom.ofInjective hUinj).trans (MulEquiv.subgroupCongr (by
        ext g
        constructor
        · rintro ⟨z, rfl⟩
          exact hUR z
        · intro hg
          exact hRU g hg))
    have hcardC : Nat.card (hermitianUnipotentCoord J) = q ^ 3 := by
      rw [Nat.card_congr e.toEquiv, hRcard]
    have hker : (fstHom J).ker ≤ Subgroup.center (hermitianUnipotentCoord J) := by
      intro z hz
      rw [MonoidHom.mem_ker, fstHom_apply] at hz
      exact Subgroup.mem_center_iff.mpr fun w => (comm_of_fst_eq_zero J hz w).symm
    have hcenter : Nat.card (Subgroup.center (hermitianUnipotentCoord J)) = q := by
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, ← hcomm, hcommcard]
    have hkerc : Nat.card (fstHom J).ker ≤ q := hcenter ▸ Subgroup.card_le_of_le hker
    have hsplit : Nat.card (hermitianUnipotentCoord J) =
        Nat.card (fstHom J).range * Nat.card (fstHom J).ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (fstHom J).ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange (fstHom J)).toEquiv]
    have hKc : Nat.card (Multiplicative K) = q ^ 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, hKcard]
    have hq0 : 0 < q := by norm_num [hq]
    have hge : q ^ 2 ≤ Nat.card (fstHom J).range := by
      have h1 : q ^ 2 * q ≤ Nat.card (fstHom J).range * q := by
        calc q ^ 2 * q = q ^ 3 := by ring
          _ = Nat.card (fstHom J).range * Nat.card (fstHom J).ker := by rw [← hsplit, hcardC]
          _ ≤ Nat.card (fstHom J).range * q := Nat.mul_le_mul_left _ hkerc
      exact Nat.le_of_mul_le_mul_right h1 hq0
    have htop : (fstHom J).range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      exact le_antisymm (Subgroup.card_le_card_group _) (hKc ▸ hge)
    intro t
    obtain ⟨w, hw⟩ := (MonoidHom.range_eq_top.mp htop) (Multiplicative.ofAdd t)
    exact ⟨w, by rw [fstHom_apply] at hw; exact Multiplicative.ofAdd.injective hw⟩
  refine kg115Excluded_of_simple fun hc =>
    kg115Excluded_of_at hc (sylowTwoNoThree_of_conj hR2 hRi hno3) ?_
  intro S hS hSi l hlS hlc hl1
  obtain ⟨g, hg⟩ := exists_conj_of_sylow hS hSi hR2 hRi
  have hl'R : g⁻¹ * l * g ∈ R := (hg l).mp hlS
  have hl'c : ∀ s ∈ R, s * (g⁻¹ * l * g) = g⁻¹ * l * g * s := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ S := (hg _).mpr (by simpa [mul_assoc] using hs)
    have h := hlc _ hs'
    calc s * (g⁻¹ * l * g) = g⁻¹ * ((g * s * g⁻¹) * l) * g := by group
      _ = g⁻¹ * (l * (g * s * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * l * g * s := by group
  have hl'1 : g⁻¹ * l * g ≠ 1 := by
    intro h
    apply hl1
    calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hSR : S = R.map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [hg x, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · rintro ⟨r, hr, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simpa [mul_assoc] using hr
  have hll : l = g * (g⁻¹ * l * g) * g⁻¹ := by group
  rw [hSR, hll]
  apply kg115At_conj
  set l' := g⁻¹ * l * g with hl'def
  intro D N hRD hDl hy hND _ ⟨a, hDa⟩ _
  obtain ⟨y, hyN, hy3⟩ := hy
  have hND' : N ≤ D := by rw [← hND]; exact Subgroup.le_normalizer
  have hyD := hND' hyN
  have hDfix : ∀ x ∈ D, rho x pinf = pinf := fun x hx =>
    fix_of_comm rho pinf hreg (fun r hr => hRle hr) hl'R hl'1 (hDl x hx)
  obtain ⟨z₀, hz₀, hz₀1⟩ := hcenterR l' hl'R hl'c
  have hz₀2 : z₀.1.2 ≠ 0 := by
    intro h
    apply hl'1
    rw [← hz₀]
    have : z₀ = 1 := Subtype.ext (Prod.ext hz₀1 h)
    rw [this, map_one]
  obtain ⟨r₀, hr₀, k₀, hyk⟩ := hstab y (hDfix y hyD)
  obtain ⟨zr, hzr⟩ := hRU r₀ hr₀
  have hTl : T k₀ * l' = l' * T k₀ := by
    have h1 := hDl y hyD
    have h2 := hl'c r₀ hr₀
    rw [hyk] at h1
    have : T k₀ = r₀⁻¹ * y := by rw [hyk]; group
    calc T k₀ * l' = r₀⁻¹ * (r₀ * T k₀ * l') := by group
      _ = r₀⁻¹ * (l' * (r₀ * T k₀)) := by rw [h1]
      _ = r₀⁻¹ * (l' * r₀) * T k₀ := by group
      _ = r₀⁻¹ * (r₀ * l') * T k₀ := by rw [h2]
      _ = l' * T k₀ := by group
  have hnorm : J.conj (k₀ : K) * k₀ = 1 := by
    rw [← hz₀, hTdef, hUdef, hermitianTorusPSU_mul_unipotent] at hTl
    have h1 := hUinj (mul_right_cancel hTl)
    have h2 := congrArg (fun z : hermitianUnipotentCoord J => z.1.2) h1
    simp only [snd_torusAction] at h2
    have h3 : (J.conj (k₀ : K))⁻¹ * (k₀ : K)⁻¹ = 1 := by
      have h4 : z₀.1.2 * ((J.conj (k₀ : K))⁻¹ * (k₀ : K)⁻¹) = z₀.1.2 * 1 := by
        rw [mul_one, ← mul_assoc]
        exact h2
      exact mul_left_cancel₀ hz₀2 h4
    have hk0 : (k₀ : K) ≠ 0 := k₀.ne_zero
    have hc0 : J.conj (k₀ : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
    rw [← mul_inv] at h3
    exact inv_eq_one.mp h3
  have hT1 : T k₀ ≠ 1 := by
    intro h
    rw [h, mul_one] at hyk
    obtain ⟨n, hn⟩ := hR2 ⟨y, by rw [hyk]; exact hr₀⟩
    have hn' : y ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have h1 := orderOf_dvd_of_pow_eq_one hn'
    rw [hy3] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hk3 : (k₀ : K) ^ 3 ≠ 1 := fun h => hT1 (torus_eq_one_of J hJ hnorm h)
  set lam := (k₀ : K) * (J.conj (k₀ : K))⁻¹ ^ 2 with hlam
  have hσ : J.conj (k₀ : K) = (k₀ : K)⁻¹ := eq_inv_of_mul_eq_one_left hnorm
  have hlam3 : lam = (k₀ : K) ^ 3 := by
    rw [hlam, hσ, inv_inv]
    ring
  have hlam1 : 1 - lam ≠ 0 := by
    rw [hlam3, sub_ne_zero]
    exact fun h => hk3 h.symm
  have hcommN : ∀ w : hermitianUnipotentCoord J,
      ∃ u : hermitianUnipotentCoord J, U u ∈ N ∧ u.1.1 = (1 - lam) * w.1.1 := by
    intro w
    refine ⟨w * zr * hermitianTorusAction J k₀ w⁻¹ * zr⁻¹, ?_, ?_⟩
    · have hUw : U w ∈ D := hRD (hUR w)
      have h1 : U w * y * (U w)⁻¹ ∈ N := by
        rw [← hND] at hUw
        exact (Subgroup.mem_normalizer_iff.mp hUw y).mp hyN
      have h2 : U w * y * (U w)⁻¹ * y⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem hyN)
      have e : U (w * zr * hermitianTorusAction J k₀ w⁻¹ * zr⁻¹) =
          U w * y * (U w)⁻¹ * y⁻¹ := by
        have hT := hermitianTorusPSU_mul_unipotent J hJ k₀ w⁻¹
        rw [← hTdef, ← hUdef] at hT
        have hiw : U w⁻¹ = (U w)⁻¹ := U.map_inv w
        have hizr : U zr⁻¹ = (U zr)⁻¹ := U.map_inv zr
        rw [hyk, ← hzr, U.map_mul, U.map_mul, U.map_mul, hizr, ← hiw]
        calc U w * U zr * U (hermitianTorusAction J k₀ w⁻¹) * (U zr)⁻¹
            = U w * U zr * (U (hermitianTorusAction J k₀ w⁻¹) * T k₀) * (T k₀)⁻¹ *
                (U zr)⁻¹ := by group
          _ = U w * U zr * (T k₀ * U w⁻¹) * (T k₀)⁻¹ * (U zr)⁻¹ := by rw [hT]
          _ = U w * (U zr * T k₀) * U w⁻¹ * (U zr * T k₀)⁻¹ := by group
      rw [e]
      exact h2
    · show (w.1.1 + zr.1.1 + (hermitianTorusAction J k₀ w⁻¹).1.1 + (zr⁻¹).1.1) = _
      rw [fst_torusAction]
      show w.1.1 + zr.1.1 + (-w.1.1) * k₀ * (J.conj (k₀ : K))⁻¹ ^ 2 + (-zr.1.1) = _
      rw [hlam]
      ring
  have hcentral : ∀ c : hermitianUnipotentCoord J, c.1.1 = 0 → ∀ r ∈ R, U c * r = r * U c := by
    intro c hc r hr
    obtain ⟨w, rfl⟩ := hRU r hr
    rw [← map_mul, ← map_mul, comm_of_fst_eq_zero J hc w]
  have hdecomp : ∀ v : hermitianUnipotentCoord J, ∃ u c : hermitianUnipotentCoord J,
      U u ∈ N ∧ c.1.1 = 0 ∧ v = u * c := by
    intro v
    obtain ⟨w, hw⟩ := hfst_onto ((1 - lam)⁻¹ * v.1.1)
    obtain ⟨u, huN, hu⟩ := hcommN w
    refine ⟨u, u⁻¹ * v, huN, ?_, by group⟩
    show -u.1.1 + v.1.1 = 0
    rw [hu, hw, ← mul_assoc, mul_inv_cancel₀ hlam1, one_mul]
    ring
  have hcommR : ⁅R, R⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx x' hx'
    obtain ⟨v, rfl⟩ := hRU x hx
    obtain ⟨v', rfl⟩ := hRU x' hx'
    obtain ⟨u, c, huN, hc, rfl⟩ := hdecomp v
    obtain ⟨u', c', hu'N, hc', rfl⟩ := hdecomp v'
    have e : ⁅U (u * c), U (u' * c')⁆ = ⁅U u, U u'⁆ := by
      rw [U.map_mul, U.map_mul]
      exact commutatorElement_mul_central (hcentral c hc (U u') (hUR u'))
        (hcentral c' hc' (U u) (hUR u)) (hcentral c hc (U c') (hUR c'))
    rw [e, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem huN hu'N) (N.inv_mem huN)) (N.inv_mem hu'N)
  have hRN : R ≤ N := by
    intro x hx
    obtain ⟨v, rfl⟩ := hRU x hx
    obtain ⟨u, c, huN, hc, rfl⟩ := hdecomp v
    rw [U.map_mul]
    refine N.mul_mem huN ?_
    have hcZ : (⟨U c, hUR c⟩ : R) ∈ Subgroup.center R :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcentral c hc g g.2).symm
    rw [← hcomm] at hcZ
    have hmem : U c ∈ (commutator R).map R.subtype := ⟨_, hcZ, rfl⟩
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmem
    exact hcommR hmem
  have hKu : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hKcard]
    norm_num [hq]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨k₇, hk₇⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hKu]; norm_num)
  have h7 : (k₇ : K) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hk₇, pow_orderOf_eq_one, Units.val_one]
  have hk₇q : J.conj (k₇ : K) = k₇ := by
    rw [huppert_II_10_4_conj_eq_frobenius J q hKcard hfixed (k₇ : K), hq,
      show 2 ^ 3 = 7 + 1 from rfl, pow_succ, h7, one_mul]
  have hT7 : T k₇ ≠ 1 := by
    refine torus_ne_one_of_fixed J hJ hk₇q fun h2 => ?_
    have h2' : k₇ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
    have h := orderOf_dvd_of_pow_eq_one h2'
    rw [hk₇] at h
    exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
  have hT7o : orderOf (T k₇) = 7 :=
    orderOf_eq_prime (by rw [← map_pow, ← hk₇, pow_orderOf_eq_one, map_one]) hT7
  have hconjN : ∀ k : Kˣ, ∀ n ∈ N, T k * n * (T k)⁻¹ ∈ N := by
    intro k n hn
    obtain ⟨r, hr, k', rfl⟩ := hstab n (hDfix n (hND' hn))
    have hTk' : T k' ∈ N := by
      have e : T k' = r⁻¹ * (r * T k') := by group
      rw [e]
      exact N.mul_mem (N.inv_mem (hRN hr)) hn
    have hc : T k * T k' = T k' * T k := by rw [← map_mul, ← map_mul, mul_comm]
    have e : T k * (r * T k') * (T k)⁻¹ = (T k * r * (T k)⁻¹) * T k' := by
      calc T k * (r * T k') * (T k)⁻¹ = (T k * r * (T k)⁻¹) * (T k * T k' * (T k)⁻¹) := by
            group
        _ = (T k * r * (T k)⁻¹) * T k' := by rw [hc]; group
    rw [e]
    exact N.mul_mem (hRN (hTnorm k r hr)) hTk'
  have hT7N : T k₇ ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hconjN k₇ n
    · intro hn
      have h1 := hconjN k₇⁻¹ _ hn
      have e : T k₇⁻¹ * (T k₇ * n * (T k₇)⁻¹) * (T k₇⁻¹)⁻¹ = n := by
        rw [T.map_inv]
        group
      rwa [e] at h1
  rw [hND] at hT7N
  have h7D := (Subgroup.orderOf_dvd_natCard D hT7N).trans hDa
  rw [hT7o] at h7D
  exact not_prime_dvd_two_pow_mul (by norm_num) (by norm_num) a h7D

end Eight

theorem kg115U3Input_holds : KG115U3Input := by
  intro f X _ hf hX
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := hX
  have hcard : Nat.card K₀ = 2 ^ (2 * f) := by rw [hK₀, ← pow_mul, mul_comm]
  let e₁ : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K₀ (2 ^ f)) := e
  let e₂ : X ≃* CFSG.Open.PSU3 2 f :=
    e₁.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₃ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
    CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₄ : ProjectiveSpecialUnitaryMatrixGroup J ≃* CFSG.Open.PSU3 2 f :=
    e₃.trans (MulEquiv.subgroupCongr hmodel)
  refine kg115Excluded_of_mulEquiv (e₂.trans e₄.symm) ?_
  by_cases h3 : f = 3
  · subst h3
    exact kg115Excluded_psu8 J hJ hKcard hfixed
  · exact kg115Excluded_psu J hJ hf h3 hKcard hfixed

end CFSG.Quasithin.H13.KG115U3
