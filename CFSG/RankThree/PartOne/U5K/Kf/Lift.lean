module

public import CFSG.RankThree.PartOne.U5K.Kf.Frame
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveModelBridge

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem scalar_commutator_pow_five {x y : GL (Fin 5) K} {κ : Kˣ}
    (hc : x * y * x⁻¹ * y⁻¹ = GeneralLinearGroup.scalar (Fin 5) κ) : κ ^ 5 = 1 := by
  have h1 := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)).det) hc
  simp only [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ((x⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det *
      (x : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have h3 : ((y⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det *
      (y : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← h1]
  calc (x : Matrix (Fin 5) (Fin 5) K).det * (y : Matrix (Fin 5) (Fin 5) K).det *
        ((x⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det *
        ((y⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det
      = ((x⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det *
        (x : Matrix (Fin 5) (Fin 5) K).det *
        (((y⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det *
        (y : Matrix (Fin 5) (Fin 5) K).det) := by ring
    _ = 1 := by rw [h2, h3, mul_one]

omit [Fact p.Prime] in
theorem scalar_commutator_pow_p {x y : GL (Fin 5) K} {κ : Kˣ}
    (hc : x * y * x⁻¹ * y⁻¹ = GeneralLinearGroup.scalar (Fin 5) κ) {ε : Kˣ}
    (hy : y ^ p = GeneralLinearGroup.scalar (Fin 5) ε) : κ ^ p = 1 := by
  have h1 : x * y * x⁻¹ = GeneralLinearGroup.scalar (Fin 5) κ * y := by
    rw [← hc]
    group
  have h2 : (x * y * x⁻¹) ^ p = (GeneralLinearGroup.scalar (Fin 5) κ * y) ^ p := by rw [h1]
  rw [conj_pow, ((commute_scalar κ y).symm).mul_pow, hy, ← map_pow] at h2
  have h3 : x * GeneralLinearGroup.scalar (Fin 5) ε * x⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) ε := by
    rw [(commute_scalar ε x).eq, mul_inv_cancel_right]
  rw [h3] at h2
  have h4 : GeneralLinearGroup.scalar (Fin 5) (κ ^ p) = 1 := mul_eq_right.1 h2.symm
  have h5 := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) 0 0) h4
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq, Units.val_one,
    Matrix.one_apply_eq] at h5
  exact Units.ext h5

theorem ZetaData.abelian_lift_of_ne_five (Z : ZetaData h p) (hp5 : p ≠ 5)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    {x y : primeFormUnitary h (idGram K 5)} (hx : primeFormConjHom h (idGram K 5) x ∈ Ab)
    (hy : primeFormConjHom h (idGram K 5) y ∈ Ab) : x * y = y * x := by
  have := hel
  have hcomm : primeFormConjHom h (idGram K 5) (x * y * x⁻¹ * y⁻¹) = 1 := by
    have h1 := hel.toIsMulCommutative.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩
    have h2 : primeFormConjHom h (idGram K 5) x * primeFormConjHom h (idGram K 5) y =
        primeFormConjHom h (idGram K 5) y * primeFormConjHom h (idGram K 5) x :=
      congrArg Subtype.val h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  obtain ⟨κ, -, hκ⟩ := (Z.conj_eq_one_iff _).1 hcomm
  have hκ' : (x : GL (Fin 5) K) * y * (x : GL (Fin 5) K)⁻¹ * (y : GL (Fin 5) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) κ := by simpa using hκ
  have hyp : y ^ p ∈ idScalarKernel h 5 := by
    rw [← Z.conj_eq_one_iff, map_pow]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hy
  obtain ⟨ε, -, hε⟩ := hyp
  have hε' : (y : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) ε := by simpa using hε
  have h5 := scalar_commutator_pow_five hκ'
  have hpp := scalar_commutator_pow_p hκ' hε'
  have hcop : Nat.Coprime 5 p := (Nat.coprime_primes (by norm_num) (Fact.out : p.Prime)).2
    (Ne.symm hp5)
  have hκ1 : κ = 1 := by
    have h1 : orderOf κ ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have h2 : orderOf κ ∣ p := orderOf_dvd_of_pow_eq_one hpp
    have : orderOf κ ∣ Nat.gcd 5 p := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  rw [hκ1, map_one] at hκ'
  apply Subtype.ext
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hκ'
  exact hκ'

section Five

open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
  CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge

theorem card_sup_dvd_of_le_normalizer' {G : Type*} [Group G] [Finite G] (N I : Subgroup G)
    (hI : I ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2


theorem ZetaData.exists_plane (Z : ZetaData h p) (hp5 : p = 5)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    {x y : primeFormUnitary h (idGram K 5)} (hx : primeFormConjHom h (idGram K 5) x ∈ Ab)
    (hy : primeFormConjHom h (idGram K 5) y ∈ Ab) (hxy : x * y ≠ y * x) :
    ∃ D : Subgroup (MulAut (primeFormP h (idGram K 5))), D ≤ Ab ∧
      primeFormConjHom h (idGram K 5) x ∈ D ∧ primeFormConjHom h (idGram K 5) y ∈ D ∧
      Nat.card D = 5 ^ 2 := by
  subst hp5
  have := hel
  have hfinK := h.finite
  have hfin : Finite (primeFormP h (idGram K 5)) := finite_primeFormP
  set a := primeFormConjHom h (idGram K 5) x with ha
  set b := primeFormConjHom h (idGram K 5) y with hb
  have hab : a * b = b * a :=
    congrArg Subtype.val (hel.toIsMulCommutative.is_comm.comm ⟨a, hx⟩ ⟨b, hy⟩)
  set D := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hD
  have hDAb : D ≤ Ab := sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hy)
  have haD : a ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hbD : b ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hdvd : Nat.card D ∣ 5 ^ 2 := by
    have h1 : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set _) := by
      refine (Subgroup.zpowers_le.2 ?_).trans (Subgroup.centralizer_le_normalizer _)
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        exact (Commute.zpow_left hab n).eq
    have h2 := card_sup_dvd_of_le_normalizer' _ _ h1
    have h3 : Nat.card (Subgroup.zpowers a) ∣ 5 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (CFSG.elemPow_eq_one_of_isElementaryAbelian a hx)
    have h4 : Nat.card (Subgroup.zpowers b) ∣ 5 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (CFSG.elemPow_eq_one_of_isElementaryAbelian b hy)
    exact h2.trans (by rw [pow_two]; exact Nat.mul_dvd_mul h3 h4)
  have hnc : ¬ IsCyclic D := by
    intro hcyc
    set W : Subgroup (primeFormUnitary h (idGram K 5)) :=
      D.comap (primeFormConjHom h (idGram K 5)) with hW
    let ψ : W →* D := ((primeFormConjHom h (idGram K 5)).comp W.subtype).codRestrict D
      (fun w => w.2)
    have hker : ψ.ker ≤ Subgroup.center W := by
      intro w hw
      have h1 : primeFormConjHom h (idGram K 5) (w : primeFormUnitary h (idGram K 5)) = 1 := by
        have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hw)
        simpa [ψ] using this
      obtain ⟨c, -, hc⟩ := (Z.conj_eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      show ((v : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) *
        ((w : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
          ((w : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) *
            ((v : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K)
      rw [hc]
      exact (commute_scalar c _).eq
    have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ψ hker
    have hxW : x ∈ W := haD
    have hyW : y ∈ W := hbD
    exact hxy (congrArg (fun w : W => (w : primeFormUnitary h (idGram K 5))) 
      (this.is_comm.comm ⟨x, hxW⟩ ⟨y, hyW⟩))
  refine ⟨D, hDAb, haD, hbD, ?_⟩
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
  interval_cases k
  · exfalso
    apply hnc
    have : Nat.card D = 1 := by simpa using hk'
    have := Nat.card_eq_one_iff_unique.1 this
    have := this.1
    exact isCyclic_of_subsingleton
  · exfalso
    apply hnc
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card (p := 5) (by simpa using hk')
  · simpa using hk'


theorem ZetaData.abelian_lift_of_five (Z : ZetaData h p) (hp5 : p = 5)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    (hcard : p ^ 3 ≤ Nat.card Ab) (hD : Ab ≤ primeFormD h (idGram K 5))
    {x y : primeFormUnitary h (idGram K 5)} (hx : primeFormConjHom h (idGram K 5) x ∈ Ab)
    (hy : primeFormConjHom h (idGram K 5) y ∈ Ab) : x * y = y * x := by
  by_contra hxy
  obtain ⟨D, hDAb, hxD, hyD, hDcard⟩ := Z.exists_plane hp5 hel hx hy hxy
  subst hp5
  have hfinK := h.finite
  have h5 : 5 ∣ 2 ^ f + 1 := Z.dvd
  have hq : ¬(2 * 2 + 1 = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have ha : 1 ≤ 2 := by norm_num
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  set Ξ := MulAut.congr (hypToPrimeForm h hR).symm with hΞ
  set D' : Subgroup (MulAut (hypPSU h 2 1)) := D.map Ξ.toMonoidHom with hD'
  have hΞρ : ∀ x, Ξ (primeFormConjHom h (idGram K 5) x) =
      linearSimAut h ha le_rfl (toSimilitude h hR x) := fun x => mulAut_congr_conj_eq h hR x
  have hAI : ∀ α ∈ Ab, Ξ α ∈ linearSimAutGroup h ha le_rfl := by
    intro α hα
    obtain ⟨X, rfl⟩ := hD hα
    exact ⟨toSimilitude h hR X, (hΞρ X).symm⟩
  have hDI : D' ≤ linearSimAutGroup h ha le_rfl := by
    rintro _ ⟨α, hα, rfl⟩
    exact hAI α (hDAb hα)
  have hDab : ∀ a ∈ D', ∀ b ∈ D', a * b = b * a := by
    rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    have h1 : (⟨α, hDAb hα⟩ : Ab) * ⟨β, hDAb hβ⟩ = ⟨β, hDAb hβ⟩ * ⟨α, hDAb hα⟩ :=
      hel.toIsMulCommutative.is_comm.comm _ _
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    change Ξ α * Ξ β = Ξ β * Ξ α
    rw [← map_mul, ← map_mul, h2]
  have hDp : ∀ a ∈ D', a ^ 5 = 1 := by
    rintro _ ⟨α, hα, rfl⟩
    change (Ξ α) ^ 5 = 1
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian α (hDAb hα), map_one]
  have hcard' : Nat.card D' = 5 ^ 2 := by
    rw [hD', Subgroup.card_map_of_injective Ξ.injective, hDcard]
  have hna' : ¬ ∀ X ∈ D'.comap (linearSimAut h ha le_rfl),
      ∀ Y ∈ D'.comap (linearSimAut h ha le_rfl), X * Y = Y * X := by
    intro hcomm
    apply hxy
    have hX : toSimilitude h hR x ∈ D'.comap (linearSimAut h ha le_rfl) := by
      rw [Subgroup.mem_comap, ← hΞρ]
      exact ⟨_, hxD, rfl⟩
    have hY : toSimilitude h hR y ∈ D'.comap (linearSimAut h ha le_rfl) := by
      rw [Subgroup.mem_comap, ← hΞρ]
      exact ⟨_, hyD, rfl⟩
    have h1 := hcomm _ hX _ hY
    have h2 := congrArg (fun X : linearSimilitudes h 2 1 =>
      transportGL hR (X : GL (HypIndex 2 1) K)) h1
    simp only [toSimilitude, Subgroup.coe_mul] at h2
    rw [transportGL_mul h hR, transportGL_mul h hR, transportGL_transportGLInv h hR,
      transportGL_transportGLInv h hR] at h2
    exact Subtype.ext h2
  obtain ⟨-, hC, -⟩ := unitary_projective_nonabelian_plane_centralizer_cyclic_field_quotient h
    Nat.prime_five (by norm_num : 5 = 2 * 2 + 1) ha h5 hq D' hDI hDab hDp hcard' hna'
  have hle : Ab.map Ξ.toMonoidHom ≤ D' := by
    rw [← hC]
    rintro _ ⟨α, hα, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hAI α hα⟩
    rintro _ ⟨β, hβ, rfl⟩
    have h1 : (⟨β, hDAb hβ⟩ : Ab) * ⟨α, hα⟩ = ⟨α, hα⟩ * ⟨β, hDAb hβ⟩ :=
      hel.toIsMulCommutative.is_comm.comm _ _
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    change Ξ β * Ξ α = Ξ α * Ξ β
    rw [← map_mul, ← map_mul, h2]
  have h6 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective Ξ.injective, hcard'] at h6
  omega

end Five

theorem ZetaData.abelian_lift (Z : ZetaData h p)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hel : IsElementaryAbelian p ↥Ab)
    (hcard : p ^ 3 ≤ Nat.card Ab) (hD : Ab ≤ primeFormD h (idGram K 5))
    {x y : primeFormUnitary h (idGram K 5)} (hx : primeFormConjHom h (idGram K 5) x ∈ Ab)
    (hy : primeFormConjHom h (idGram K 5) y ∈ Ab) : x * y = y * x := by
  by_cases hp5 : p = 5
  · exact Z.abelian_lift_of_five hp5 hel hcard hD hx hy
  · exact Z.abelian_lift_of_ne_five hp5 hel hx hy

end CFSG.RankThree.PartOne.U5K.Kf
