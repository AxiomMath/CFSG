module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedLiftComponent
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary

section Genuine

private theorem psut_odd_card_sub_one
    {E : Type} {f : ℕ}
    (hc : Nat.card E = (2 ^ f) ^ 2) (hf : 1 ≤ f) : Odd (Nat.card E - 1) := by
  have hpowF : Nat.card E = 2 * 2 ^ (2 * f - 1) := by
    calc Nat.card E = (2 ^ f) ^ 2 := hc
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

private theorem psut_pow_scalar_odd
    {E : Type} [Field E] [Finite E] [CharP E 2] {f n : ℕ}
    (hc : Nat.card E = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hf : 1 ≤ f)
    {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (unitaryInvolution E 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : X}
    (hdp : d ^ p = 1) {s : GL (Fin n) E}
    (hs : CFSG.StandardType.ClassicalPosition.IsGLLift
      (Unitary.SU (unitaryInvolution E 2 f) n).subtype ψ s d) :
    Odd (orderOf s) := by
  haveI : Fintype E := Fintype.ofFinite E
  have hsp : CFSG.StandardType.ClassicalPosition.IsGLLift
      (Unitary.SU (unitaryInvolution E 2 f) n).subtype ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hdp] at h
  obtain ⟨c, hc_eq⟩ := CFSG.StandardType.ClassicalPosition.isGLLift_unique_PSU hc n ψ hψ
    hsp CFSG.StandardType.ClassicalPosition.isGLLift_one
  have hsmat : (s : Matrix (Fin n) (Fin n) E) ^ p = Matrix.scalar (Fin n) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit : IsUnit ((s : Matrix (Fin n) (Fin n) E) ^ p) := IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) E).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin n) (Fin n) E) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) E).det = c ^ n := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    have hn0 : n ≠ 0 := by omega
    exact ((isUnit_pow_iff (a := c) (n := n) hn0).mp hm).ne_zero
  let u : Eˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hoddF : Odd (Nat.card E - 1) := psut_odd_card_sub_one hc hf
  have hu_pow : u ^ (Nat.card E - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : E) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hodd_p, hodd_u⟩) hdvd

private theorem psut_lifts_odd
    {E : Type} [Field E] [Finite E] [CharP E 2] {f : ℕ}
    (hc : Nat.card E = (2 ^ f) ^ 2) (hf : 1 ≤ f) (n : ℕ) (hn : 3 ≤ n)
    {X : Type} [Group X]
    (ψ : ↥(CFSG.LieType.Universal.Unitary.SU (unitaryInvolution E 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center
      ↥(CFSG.LieType.Universal.Unitary.SU (unitaryInvolution E 2 f) n))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X}
    (hab : IsElemAbelian p D) :
    Odd (Nat.card (Subgroup.closure
      {s : GL (Fin n) E |
        CFSG.StandardType.InnerDiagSU.IsJUnitary (unitaryInvolution E 2 f) s ∧
        ∃ d ∈ D, CFSG.StandardType.ClassicalPosition.IsGLLift
          (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution E 2 f) n).subtype ψ s d})) := by
  set S₀ : Set (GL (Fin n) E) :=
    {s : GL (Fin n) E |
      CFSG.StandardType.InnerDiagSU.IsJUnitary (unitaryInvolution E 2 f) s ∧
      ∃ d ∈ D, CFSG.StandardType.ClassicalPosition.IsGLLift
        (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution E 2 f) n).subtype ψ s d} with hS₀def
  have hS₀one : (1 : GL (Fin n) E) ∈ S₀ := by
    refine ⟨?_, 1, one_mem D, ?_⟩
    · simp only [CFSG.StandardType.InnerDiagSU.IsJUnitary, Units.val_one, conjTr_one,
        Matrix.one_mul, Matrix.mul_one]
    · exact CFSG.StandardType.ClassicalPosition.isGLLift_one
  have hS₀mul : ∀ s ∈ S₀, ∀ s' ∈ S₀, s * s' ∈ S₀ := by
    intro s hs s' hs'
    obtain ⟨hsU, d, hd, hsL⟩ := hs
    obtain ⟨hs'U, d', hd', hs'L⟩ := hs'
    refine ⟨hsU.mul hs'U, d * d', mul_mem hd hd', ?_⟩
    have hcomm : d' * d = d * d' := by
      have h := isMulCommutative_iff.mp hab.1 ⟨d', hd'⟩ ⟨d, hd⟩
      exact congrArg (fun x : ↥D => (x : X)) h
    have h := hs'L.mul hsL
    rwa [hcomm] at h
  have hS₀pow : ∀ s ∈ S₀, ∀ k : ℕ, s ^ k ∈ S₀ := by
    intro s hs k
    induction k with
    | zero => simpa using hS₀one
    | succ k ih =>
        have h := hS₀mul (s ^ k) ih s hs
        simpa only [pow_succ] using h
  have hoddS₀ : ∀ s ∈ S₀, Odd (orderOf s) := by
    intro s hs
    obtain ⟨-, d, hd, hsL⟩ := hs
    exact psut_pow_scalar_odd hc hn hf ψ hψ hp hp2 (hab.2 d hd) hsL
  have hcl : ∀ g ∈ Subgroup.closure S₀, g ∈ S₀ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact hS₀one
    | mul x y hx hy ihx ihy => exact hS₀mul x ihx y ihy
    | inv x hx ihx =>
        have hxpow : x * x ^ (orderOf x - 1) = 1 := by
          have hlt : 1 ≤ orderOf x := orderOf_pos x
          rw [← pow_succ', Nat.sub_add_cancel hlt, pow_orderOf_eq_one]
        have hxinv : x ^ (orderOf x - 1) = x⁻¹ := eq_inv_of_mul_eq_one_right hxpow
        rw [← hxinv]
        exact hS₀pow x ihx (orderOf x - 1)
  have hoddPmem : ∀ g ∈ Subgroup.closure S₀, Odd (orderOf g) := fun g hg => hoddS₀ g (hcl g hg)
  rcases Nat.even_or_odd (Nat.card (Subgroup.closure S₀)) with he | ho
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.closure S₀)) 2
      (even_iff_two_dvd.1 he)
    have hg2 : orderOf g = 2 := hg
    have h1 := hoddPmem (g : GL (Fin n) E) g.2
    rw [Subgroup.orderOf_coe g, hg2] at h1
    exact (Nat.not_odd_iff_even.2 even_two) h1
  · exact ho

theorem ggA6_transport_PSU
    (n f : ℕ) (X : Type) [Group X] [Finite X]
    (ψ : (ggU .PSU n f).K →* X) (p : ℕ) (G₀ D J : Subgroup X) :
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .PSU n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .PSU n 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) →
    (∀ d ∈ D, GGPsiInnerDiag (ggU .PSU n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    ∃ (P J' : Subgroup (GL (Fin n) (GaloisField 2 (2 * f)))),
      (∀ A ∈ P, CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (A : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f))) * CFSG.LieType.Universal.Unitary.antidiag n *
          (A : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * f))) = CFSG.LieType.Universal.Unitary.antidiag n) ∧
      Odd (Nat.card P) ∧
      IsComponentOf J' (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n ⊓
        Subgroup.centralizer (P : Set (GL (Fin n) (GaloisField 2 (2 * f))))) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
  intro hrange hker hLie hp hp2 hDN hdiag hab hD hJ
  have hadm := LieModel.admissible hLie
  have hf : 1 ≤ f := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hc : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul 2 f hf
  have e : ggU .PSU n f =
      ⟨CFSG.LieType.Universal.Unitary.SU
          (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        CFSG.LieType.Universal.Unitary.rootDatum
          (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  revert hdiag hker hrange ψ
  rw [e]
  intro ψ hrange hker hdiag
  let E := GaloisField 2 (2 * f)
  let σ : E ≃+* E := unitaryInvolution E 2 f
  let U := ↥(CFSG.LieType.Universal.Unitary.SU σ n)
  let j : U →* GL (Fin n) E := (CFSG.LieType.Universal.Unitary.SU σ n).subtype
  have hkerU : ψ.ker ≤ Subgroup.center U := hker
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin n) E,
      CFSG.StandardType.InnerDiagSU.IsJUnitary σ s ∧
        CFSG.StandardType.ClassicalPosition.IsGLLift j ψ s d := by
    intro d hd
    have hbN : d ∈ Subgroup.normalizer (ψ.range : Set X) := by
      rw [hrange]; exact hDN hd
    have hbd : GGPsiInnerDiag (CFSG.LieType.Universal.Unitary.rootDatum hc n) ψ d :=
      hdiag d hd
    obtain ⟨s, hsU, hsL⟩ :=
      CFSG.StandardType.ClassicalPosition.exists_isGLLift_PSU hc n hn ψ hkerU hbN hbd
    exact ⟨s, by simpa only [CFSG.StandardType.InnerDiagSU.IsJUnitary] using hsU, hsL⟩
  let S₀ : Set (GL (Fin n) E) :=
    {s | CFSG.StandardType.InnerDiagSU.IsJUnitary σ s ∧
      ∃ d ∈ D, CFSG.StandardType.ClassicalPosition.IsGLLift j ψ s d}
  let P : Subgroup (GL (Fin n) E) := Subgroup.closure S₀
  have hPU : ∀ A ∈ P, CFSG.StandardType.InnerDiagSU.IsJUnitary σ A := by
    let GU : Subgroup (GL (Fin n) E) :=
      { carrier := {A | CFSG.StandardType.InnerDiagSU.IsJUnitary σ A}
        mul_mem' := fun ha hb => ha.mul hb
        one_mem' := by
          change CFSG.StandardType.InnerDiagSU.IsJUnitary σ 1
          simp only [CFSG.StandardType.InnerDiagSU.IsJUnitary, Units.val_one, conjTr_one,
            Matrix.one_mul, Matrix.mul_one]
        inv_mem' := fun ha => ha.inv }
    have hsub : S₀ ⊆ GU := fun s hs => hs.1
    exact fun A hA => (Subgroup.closure_le GU).mpr hsub hA
  have hJ' : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [hrange]; exact hJ
  have hliftP : ∀ d ∈ D, ∃ s : GL (Fin n) E, s ∈ P ∧
      CFSG.StandardType.ClassicalPosition.IsGLLift j ψ s d := by
    intro d hd
    obtain ⟨s, hsU, hsL⟩ := hlift d hd
    exact ⟨s, Subgroup.subset_closure ⟨hsU, d, hd, hsL⟩, hsL⟩
  obtain ⟨K, hKcomp, hKmap⟩ :=
    CFSG.StandardType.ClassicalPosition.StepA.exists_isComponentOf_comap_lift_of_isGLLift
      j (Subgroup.subtype_injective (CFSG.LieType.Universal.Unitary.SU σ n)) ψ hkerU
      (fun s => s ∈ P) hJ' hliftP
  let Sstep : Set (GL (Fin n) E) :=
    {s | s ∈ P ∧ ∃ d ∈ D, CFSG.StandardType.ClassicalPosition.IsGLLift j ψ s d}
  have hSstep : Subgroup.closure Sstep = P := by
    apply le_antisymm
    · rw [Subgroup.closure_le]; intro s hs; exact hs.1
    · change Subgroup.closure S₀ ≤ Subgroup.closure Sstep
      rw [Subgroup.closure_le]; intro s hs
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure hs, hs.2⟩
  have hcent : Subgroup.centralizer Sstep =
      Subgroup.centralizer (P : Set (GL (Fin n) E)) := by
    rw [← hSstep, Subgroup.centralizer_closure]
  have hKcomp' : IsComponentOf K
      ((Subgroup.centralizer (P : Set (GL (Fin n) E))).comap j) := by
    rw [← hcent]; exact hKcomp
  let J'' : Subgroup (GL (Fin n) E) := K.map j
  have hJ''comp : IsComponentOf J''
      (CFSG.LieType.Universal.Unitary.SU σ n ⊓
        Subgroup.centralizer (P : Set (GL (Fin n) E))) := by
    have hmap := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := j)
      (Subgroup.subtype_injective (CFSG.LieType.Universal.Unitary.SU σ n))).mpr hKcomp'
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype] at hmap
    exact hmap
  have hKperfect : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  let fJ : ↥K →* ↥J := (ψ.comp K.subtype).codRestrict J (fun x => by
    have hx : ψ (x : U) ∈ K.map ψ := Subgroup.mem_map_of_mem ψ x.2
    rwa [hKmap] at hx)
  have hfJapply : ∀ x : ↥K, (fJ x : X) = ψ (x : U) := fun x => rfl
  have hfJsurj : Function.Surjective fJ := by
    intro y
    have hy : (y : X) ∈ K.map ψ := by rw [hKmap]; exact y.2
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hfJker : fJ.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx1 : ψ (x : U) = 1 := by
      have h := congrArg (fun z : ↥J => (z : X)) (MonoidHom.mem_ker.1 hx)
      simpa [hfJapply x] using h
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 (hkerU (MonoidHom.mem_ker.mpr hx1)) (y : U)
  have hc1 : Subgroup.center ↥K =
      ((QuotientGroup.mk' (Subgroup.center ↥J)).comp fJ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hKperfect fJ hfJsurj hfJker]
  let e1 : ↥K ⧸ Subgroup.center ↥K ≃* ↥J ⧸ Subgroup.center ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hc1).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hfJsurj))
  let jK : ↥K →* ↥(K.map j) :=
    (j.comp K.subtype).codRestrict (K.map j) (fun x => Subgroup.mem_map_of_mem j x.2)
  have hjKapply : ∀ x : ↥K, (jK x : GL (Fin n) E) = j (x : U) := fun x => rfl
  have hjKsurj : Function.Surjective jK := by
    intro y
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hjKker : jK.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx1 : j (x : U) = 1 := by
      have h := congrArg (fun z : ↥(K.map j) => (z : GL (Fin n) E))
        (MonoidHom.mem_ker.1 hx)
      simpa [hjKapply x] using h
    have hx2 : (x : U) = 1 := Subtype.ext hx1
    have hxone : x = 1 := Subtype.ext hx2
    rw [hxone]; exact Subgroup.one_mem _
  have hc2 : Subgroup.center ↥K =
      ((QuotientGroup.mk' (Subgroup.center ↥(K.map j))).comp jK).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hKperfect jK hjKsurj hjKker]
  let e2 : ↥K ⧸ Subgroup.center ↥K ≃* J'' ⧸ Subgroup.center J'' :=
    (QuotientGroup.quotientMulEquivOfEq hc2).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk'_surjective _).comp hjKsurj))
  refine ⟨P, J'', ?_, ?_, ?_, ?_⟩
  · intro A hA
    simpa only [CFSG.StandardType.InnerDiagSU.IsJUnitary] using hPU A hA
  · exact psut_lifts_odd hc hf n hn ψ hkerU p hp hp2 hab
  · exact hJ''comp
  · exact ⟨e1.symm.trans e2⟩

end Genuine

end CFSG.StandardType.A6Red
