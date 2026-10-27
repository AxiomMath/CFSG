module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSUTorus
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSUAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical2 (exists_orderOf_eq_norm_one)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace UnitModel

theorem sq_dvd_two_pow_add_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ f)
    (hdvd : p ∣ 2 ^ f + 1) : p ^ 2 ∣ 2 ^ f + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, rfl⟩ := hpf
  set r := 2 ^ g with hrdef
  have hrp : 2 ^ (p * g) = r ^ p := by rw [hrdef, ← pow_mul, mul_comm]
  rw [hrp] at hdvd ⊢
  have hr : p ∣ r + 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
    rw [Nat.cast_add, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at hdvd
    rw [Nat.cast_add, Nat.cast_one]
    exact hdvd
  have hnr : ¬ p ∣ r := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hv := padicValNat.pow_add_pow (x := r) (y := 1) (hp.odd_of_ne_two hp2) (by simpa using hr)
    hnr (hp.odd_of_ne_two hp2)
  rw [one_pow] at hv
  have hne : r ^ p + 1 ≠ 0 := by omega
  rw [padicValNat_dvd_iff_le hne, hv, padicValNat_self]
  have : 1 ≤ padicValNat p (r + 1) := one_le_padicValNat_of_dvd (n := r + 1) (by positivity) hr
  omega

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

theorem not_pow_eq_of_not_exists [Finite F] (h : UnitaryFieldData 2 f F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {ω : Fˣ} (hω : ω ^ p = 1)
    (hB : ¬ ∃ ζ' : Fˣ, ζ' ^ p = ω ∧ (ζ' : F) ^ (2 ^ f + 1) = 1) {l : Fˣ} (hl : l ^ p = 1)
    (hl1 : l ≠ 1) (ν : Fˣ) : ν ^ p ≠ l := by
  intro hν
  have : Fact p.Prime := ⟨hp⟩
  have hlprim : IsPrimitiveRoot l p := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hl hl1)
  have hlprim' : IsPrimitiveRoot (l : F) p := IsPrimitiveRoot.coe_units_iff.mpr hlprim
  have hlN : l ^ (2 ^ f + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hl, one_pow]
  have hνN : ν ^ (2 ^ f + 1) = 1 := SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hν hlN
  obtain ⟨j, -, hj⟩ := hlprim'.eq_pow_of_pow_eq_one (ξ := (ω : F))
    (by rw [← Units.val_pow_eq_pow_val, hω, Units.val_one])
  apply hB
  refine ⟨ν ^ j, Units.ext ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hν, Units.val_pow_eq_pow_val, hj]
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hνN, one_pow, Units.val_one]

theorem eq_one_of_pow_eq_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnp : n = p)
    {Y : GL (Fin n) F} (hdet : GeneralLinearGroup.det Y = 1) {l : F}
    (hY : ((Y : Matrix (Fin n) (Fin n) F)) ^ p = Matrix.scalar (Fin n) l)
    (hnot : l ≠ 1 → ∀ b : F, b ^ p ≠ l) : l = 1 := by
  by_contra hl1
  have h1 := LinModel.det_eq_of_pow_eq_scalar hp hp2 (by rw [Fintype.card_fin, hnp]) hY
    (hnot hl1)
  have h2 := GeneralLinearGroup.val_det_apply Y
  rw [hdet, Units.val_one, h1] at h2
  exact hl1 h2.symm

theorem exists_det_one_conj_diag [Finite F] [NeZero n] {p : ℕ} (h : UnitaryFieldData 2 f F)
    (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) {Y : GL (Fin n) F}
    (hYU : Y ∈ primeFormUnitary h (idGram F n)) (hYp : Y ^ p = 1) :
    ∃ (s : ↥(unitarySU 2 f F n)) (τ : Fin n → Fˣ),
      (s : GL (Fin n) F)⁻¹ * Y * s = diagHom n τ := by
  set Yu : primeFormUnitary h (idGram F n) := ⟨Y, hYU⟩ with hYu
  have hYup : Yu ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hYp)
  obtain ⟨Q, hQ⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq
    (Subgroup.zpowers Yu)
    (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self Yu i j).eq)
    (fun x hx => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hYup,
        _root_.one_zpow])
  have hd := hQ Yu (Subgroup.mem_zpowers Yu)
  set X : GL (Fin n) F := ((Q⁻¹ * Yu * Q : primeFormUnitary h (idGram F n)) : GL (Fin n) F)
    with hX
  have hXd : (X : Matrix (Fin n) (Fin n) F) = diagonal fun i => (X : Matrix (Fin n) (Fin n) F) i i :=
    hd.diagonal_diag.symm
  have hXne : ∀ i, (X : Matrix (Fin n) (Fin n) F) i i ≠ 0 := by
    intro i hi
    have h1 : (X : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    rw [hXd, det_diagonal] at h1
    exact h1 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  set τ : Fin n → Fˣ := fun i => Units.mk0 _ (hXne i) with hτ
  have hXτ : X = diagHom n τ := by
    apply Units.ext
    rw [coe_diagHom, hXd]
    rfl
  set δ := GeneralLinearGroup.det (Q : GL (Fin n) F) with hδ
  have hδN : δ ^ (2 ^ f + 1) = 1 := UnitModel.det_pow_eq_one_of_mem h Q.2
  set E : GL (Fin n) F := diagHom n (Pi.mulSingle 0 δ⁻¹) with hE
  have hEU : E ∈ primeFormUnitary h (idGram F n) := by
    rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
    refine CFSG.RankThree.Classical2.diagHom_unitary h fun i => ?_
    by_cases hi : i = 0
    · rw [hi, Pi.mulSingle_eq_same, ← Units.val_pow_eq_pow_val, inv_pow, hδN, inv_one,
        Units.val_one]
    · rw [Pi.mulSingle_eq_of_ne hi, Units.val_one, one_pow]
  have hQE : (Q : GL (Fin n) F) * E ∈ unitarySU 2 f F n := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [← GeneralLinearGroup.val_det_apply, map_mul, hE]
      have h1 : GeneralLinearGroup.det (diagHom n (Pi.mulSingle (0 : Fin n) δ⁻¹)) = δ⁻¹ := by
        apply Units.ext
        rw [GeneralLinearGroup.val_det_apply, det_diagHom, ← Units.coe_prod,
          Finset.prod_pi_mulSingle']
        simp
      rw [h1, mul_inv_cancel, Units.val_one]
    · have h1 := mem_primeFormUnitary.mp ((primeFormUnitary h (idGram F n)).mul_mem Q.2 hEU)
      simp only [idGram, Units.val_one, Matrix.mul_one] at h1
      exact h1
  refine ⟨⟨(Q : GL (Fin n) F) * E, hQE⟩, τ, ?_⟩
  change ((Q : GL (Fin n) F) * E)⁻¹ * Y * ((Q : GL (Fin n) F) * E) = diagHom n τ
  have hXQ : X = (Q : GL (Fin n) F)⁻¹ * Y * Q := rfl
  rw [_root_.mul_inv_rev, show E⁻¹ * (Q : GL (Fin n) F)⁻¹ * Y * ((Q : GL (Fin n) F) * E) =
    E⁻¹ * ((Q : GL (Fin n) F)⁻¹ * Y * Q) * E by group, ← hXQ, hXτ, hE, ← map_inv, ← map_mul,
    ← map_mul, mul_comm (Pi.mulSingle (0 : Fin n) δ⁻¹)⁻¹ τ, mul_assoc, inv_mul_cancel, mul_one]

theorem card_bstar_eq_of_su [Finite G] {p m f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 1 = p)
    (hpq : p ∣ 2 ^ (f + 1) + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1) →* G}
    (hker : ψ.ker ≤
      Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum
      (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) (m + 1)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs) {y : G}
    (hyM : y ∈ Subgroup.normalizer (ψ.range : Set G)) (hyo : orderOf y = p)
    (hy : ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), g⁻¹ * y * g ∉ Bs) :
    Nat.card Bs = p ^ (p - 1) := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hnq : (m + 1, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : m + 1 = 3 := congrArg Prod.fst h'
    omega
  have hpow : ∀ u : (GaloisField 2 (2 * (f + 1)))ˣ, u ^ (m + 1) = u ^ p := fun u => by rw [hmp]
  obtain ⟨P, hP, hBsD, hupper⟩ := exists_frame_of_su hp hp5 hmp hpq hker hC hBsM hBsE hBsI hU
  set φ := SURep.ggFrameU hF ψ P hP with hφ
  have hφr : φ.range = ψ.range := SURep.range_ggFrameU hF ψ P hP
  have hcent : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hφr]; exact hC
  have hkerφ : SURep.GGFrameKer φ := SURep.ggFrameKer_ggFrameU hF ψ P hP (by omega) hnq hker
  have hT : frameTorus p h φ ≤ Bs := frameTorus_le h hcent hBsD hom
  obtain ⟨ω, hωo, hωN⟩ := exists_orderOf_eq_norm_one h hp hpq
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.iff_orderOf.mpr hωo
  have hωN' : ((ω : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
      (2 ^ (f + 1) + 1) = 1 := by rw [← Units.val_pow_eq_pow_val, hωN, Units.val_one]
  have hτN : ∀ (a : Fin (m + 1) → ZMod p) (i : Fin (m + 1)),
      ((ω ^ (a i).val : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
        (2 ^ (f + 1) + 1) = 1 := fun a i => by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm (a i).val, pow_mul, hωN', one_pow]
  have hfin : (∀ a : Fin (m + 1) → ZMod p, ∃ g : G,
      SURep.GGFrameActs φ g (fun i => ω ^ (a i).val)) → Nat.card Bs = p ^ (p - 1) := by
    intro hreal
    have h1 := card_le_card_frameTorus h (by omega) hkerφ hω hreal
    rw [show p - 1 = m by omega]
    have h2 : Nat.card Bs ≤ p ^ m := by simpa using hupper
    exact le_antisymm h2 (h1.trans (Subgroup.card_le_of_le hT))
  by_cases hB : ∃ ζ' : (GaloisField 2 (2 * (f + 1)))ˣ, ζ' ^ p = ω ∧
      (ζ' : GaloisField 2 (2 * (f + 1))) ^ (2 ^ (f + 1) + 1) = 1
  · obtain ⟨ζ', h1, h2⟩ := hB
    exact hfin fun a => exists_frameActs_of_pow_eq h hmp φ h1 h2 a
  by_cases hA : ∃ (g₀ : G) (A₀ : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))),
      A₀ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1)) ∧
      (g₀, A₀) ∈ SUTorus.suPairs φ ∧
      ¬ ∃ c : (GaloisField 2 (2 * (f + 1)))ˣ, c ^ p = GeneralLinearGroup.det A₀
  · obtain ⟨g₀, A₀, hU0, h0, hd⟩ := hA
    exact hfin fun a => exists_frameActs_of_det h hp hp2 hpq hmp hU0 h0 hd (hτN a)
  exfalso
  have hpf : ¬ p ∣ f + 1 := by
    intro hdvd
    apply hB
    have hsq := sq_dvd_two_pow_add_one hp hp2 hdvd hpq
    have hcardK : p ^ 2 ∣ Nat.card (GaloisField 2 (2 * (f + 1)))ˣ := by
      rw [Nat.card_units, hF]
      refine hsq.trans ⟨2 ^ (f + 1) - 1, ?_⟩
      rw [← Nat.sq_sub_sq, one_pow]
    obtain ⟨ζ', hζ'⟩ := LinModel.exists_pow_eq_of_sq_dvd hp hcardK hω.pow_eq_one
    refine ⟨ζ', hζ', ?_⟩
    rw [← Units.val_pow_eq_pow_val, SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hζ' hωN,
      Units.val_one]
  have hσ : ∀ φ' : GaloisField 2 (2 * (f + 1)) ≃+* GaloisField 2 (2 * (f + 1)),
      φ' ^ p = 1 → φ' = 1 := fun φ' h' =>
    LinModel.eq_one_of_pow_eq_one_of_not_dvd (by omega) hp (fun hd => hpf
      ((Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) hd))) h'
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨A, hAJ, hAc⟩ := exists_mem_suInducedPairs_of_pow_eq_one h (by omega) hker hC hσ hyM hyp
  have hY : (y, P * A * P⁻¹) ∈ SUTorus.suPairs φ :=
    SUTorus.mem_suPairs_transfer P hP
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF (m + 1)) hAJ hAc
  have hYU : P * A * P⁻¹ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1)) :=
    SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP hAJ)
  obtain ⟨c, hc⟩ : ∃ c : (GaloisField 2 (2 * (f + 1)))ˣ,
      c ^ p = GeneralLinearGroup.det (P * A * P⁻¹) := by
    by_contra hne
    exact hA ⟨y, _, hYU, hY, hne⟩
  have hcN : c ^ (2 ^ (f + 1) + 1) = 1 :=
    SUTorus.pow_add_one_eq_one_of_pow h hp hp2 hpq hc (det_pow_eq_one_of_mem h hYU)
  set Y₁ := GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * (P * A * P⁻¹) with hY₁
  have hY₁U : Y₁ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1)) := by
    refine (primeFormUnitary h _).mul_mem ?_ hYU
    rw [SUTorus.scalar_mem_primeFormUnitary_iff, h.bar_apply]
    have h1 : ((c⁻¹ : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
        (2 ^ (f + 1) + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, hcN, inv_one, Units.val_one]
    rwa [pow_succ] at h1
  have hY₁det : GeneralLinearGroup.det Y₁ = 1 := by
    rw [hY₁, map_mul, LinModel.det_scalar_eq, hpow, inv_pow, hc, inv_mul_cancel]
  have hY₁SU : Y₁ ∈ unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) (m + 1) := by
    rw [mem_unitarySU_iff h]
    refine ⟨by rw [← GeneralLinearGroup.val_det_apply, hY₁det, Units.val_one], ?_⟩
    have h1 := mem_primeFormUnitary.mp hY₁U
    simp only [idGram, Units.val_one, Matrix.mul_one] at h1
    exact h1
  have hY₁pair : (y, Y₁) ∈ SUTorus.suPairs φ := by
    have h1 := (SUTorus.suPairs φ).mul_mem (SUTorus.one_scalar_mem_suPairs φ c⁻¹) hY
    rwa [Prod.mk_mul_mk, one_mul] at h1
  set s₁ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) (m + 1)) := ⟨Y₁, hY₁SU⟩ with hs₁
  have hyφ : y = φ s₁ := SURep.eq_of_act_eqU hcent fun s => by
    rw [hY₁pair.2 s (s₁ * s * s₁⁻¹) rfl, map_mul, map_mul, map_inv]
  have hs₁p : s₁ ^ p = 1 := by
    have h1 : φ (s₁ ^ p) = 1 := by rw [map_pow, ← hyφ, hyp]
    obtain ⟨l, hl⟩ := hkerφ (s₁ ^ p) h1
    have hY₁l : ((Y₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))))) ^ p =
        Matrix.scalar (Fin (m + 1)) l := by
      rw [← hl, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    have hlp : l ^ p = 1 := by
      have h2 := congrArg Matrix.det hY₁l
      rw [Matrix.det_pow, ← GeneralLinearGroup.val_det_apply, hY₁det, Units.val_one, one_pow,
        Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at h2
      have h3 : l ^ (m + 1) = l ^ p := by rw [hmp]
      rw [← h3]
      exact h2.symm
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hlp
      exact zero_ne_one hlp
    have hl1 : l = 1 := by
      refine eq_one_of_pow_eq_scalar hp hp2 hmp hY₁det hY₁l fun hl1 b hb => ?_
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hb
        exact hl0 hb.symm
      have hlu : (Units.mk0 l hl0) ^ p = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hlp, Units.val_one])
      have hlu1 : Units.mk0 l hl0 ≠ 1 := fun h' => hl1 (by
        have := congrArg Units.val h'
        simpa using this)
      exact not_pow_eq_of_not_exists h hp hp2 hpq hω.pow_eq_one hB hlu hlu1 (Units.mk0 b hb0)
        (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, hb]))
    apply Subtype.ext
    apply Units.ext
    rw [hl, hl1, OneMemClass.coe_one, Units.val_one, Matrix.scalar_apply, diagonal_one]
  have hY₁p : Y₁ ^ p = 1 := by
    have h1 := congrArg Subtype.val hs₁p
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
  obtain ⟨s₀, τ, hτ⟩ := exists_det_one_conj_diag h hp hpq hY₁U hY₁p
  have hz : (φ s₀)⁻¹ * y * φ s₀ ∈ frameTorus p h φ := by
    have h1 := (SUTorus.suPairs φ).mul_mem ((SUTorus.suPairs φ).mul_mem
      ((SUTorus.suPairs φ).inv_mem (mem_suPairs_coe φ s₀)) hY₁pair) (mem_suPairs_coe φ s₀)
    rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, hτ] at h1
    have hτp : ∀ i, τ i ^ p = 1 := by
      have h2 : diagHom (m + 1) (τ ^ p) = 1 := by
        rw [map_pow, ← hτ, show ((s₀ : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))))⁻¹ * Y₁ *
          s₀ = MulAut.conj ((s₀ : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))))⁻¹ Y₁ by
          rw [MulAut.conj_apply, inv_inv], ← map_pow, hY₁p, map_one]
      intro i
      have h3 := congrFun (diagHom_injective (m + 1) (h2.trans (map_one _).symm)) i
      simpa using h3
    have hτN : ∀ i, ((τ i : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
        (2 ^ (f + 1) + 1) = 1 := fun i => by
      obtain ⟨k, hk⟩ := hpq
      rw [← Units.val_pow_eq_pow_val, hk, pow_mul, hτp i, one_pow, Units.val_one]
    exact ⟨τ, hτp, hτN, fun s s' hs' => h1.2 s s' hs'⟩
  exact hy (φ s₀) (by rw [← hφr]; exact Subgroup.le_normalizer ⟨s₀, rfl⟩) (hT hz)

end UnitModel

section Inputs

theorem ggSixLinearRankOn_PSU : GGSixLinearRankOn .PSU := by
  intro G _ _ p Bs G₀ n f ψ hS hlin y hyM hyo hy
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hpq : p ∣ 2 ^ f + 1 := by
    rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hS.2.1
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hrange
  exact UnitModel.card_bstar_eq_of_su hS.prime hp5 hnp hpq hker hS.2.2.1 hS.bstar_le hS.elem
    hS.2.2.2.1.2.2 hS.omega hS.unique hyM hyo hy

theorem ggSixLinearRankInput_holds : GGSixLinearRankInput :=
  ggSixLinearRankInput_of_tags ggSixLinearRankOn_PSL ggSixLinearRankOn_PSU

end Inputs

end CFSG.StandardType
