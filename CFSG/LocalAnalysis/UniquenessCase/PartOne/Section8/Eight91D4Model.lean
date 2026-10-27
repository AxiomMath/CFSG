module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4ThreeBCentralizer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Bridge
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158GInn3
import CFSG.GroupTheory.PrimeOrderSubgroups
import CFSG.RankThree.PartTwo.Sec14.Ronan148BD4Short
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (DerInf8)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup exists_mulEquiv_graphFixedRootGroup_card
  ringEquiv_cube_apply_eq)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo
open CFSG.RankThree.Classical2 (unitarySet)

private lemma r891_mem_map_conj {G : Type} [Group G] {c z : G} {R : Subgroup G}
    (h : c * z * c⁻¹ ∈ R) : z ∈ R.map (MulAut.conj c⁻¹).toMonoidHom := by
  refine Subgroup.mem_map.2 ⟨c * z * c⁻¹, h, ?_⟩
  simp
  group

private lemma r891_centralizer_map_conj {G : Type} [Group G] {c z : G} {R : Subgroup G}
    (h : R ≤ Subgroup.centralizer ({c * z * c⁻¹} : Set G)) :
    R.map (MulAut.conj c⁻¹).toMonoidHom ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hr' := Subgroup.mem_centralizer_singleton_iff.1 (h hr)
  have hc := congrArg (fun t => c⁻¹ * t * c) hr'
  simpa [MulAut.conj_apply, mul_assoc] using hc

private lemma r891_commutator_map_conj {G : Type} [Group G] {c z : G} {R : Subgroup G}
    (hc : ∀ a ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set G),
      ∀ b ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set G), a * b * a⁻¹ * b⁻¹ ∈ R) :
    ∀ a ∈ Subgroup.centralizer ({z} : Set G),
      ∀ b ∈ Subgroup.centralizer ({z} : Set G),
        a * b * a⁻¹ * b⁻¹ ∈ R.map (MulAut.conj c⁻¹).toMonoidHom := by
  intro a ha b hb
  have ha' : c * a * c⁻¹ ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    simpa [mul_assoc] using congrArg (fun t => c * t * c⁻¹) ha
  have hb' : c * b * c⁻¹ ∈ Subgroup.centralizer ({c * z * c⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hb ⊢
    simpa [mul_assoc] using congrArg (fun t => c * t * c⁻¹) hb
  have h := hc (c * a * c⁻¹) ha' (c * b * c⁻¹) hb'
  refine Subgroup.mem_map.2 ⟨(c * a * c⁻¹) * (c * b * c⁻¹) * (c * a * c⁻¹)⁻¹ *
    (c * b * c⁻¹)⁻¹, h, ?_⟩
  simp
  group

private lemma r891_transport_threeA {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {x : X} {z : Y} (hex : e x = z) {S : Subgroup Y} (hzS : z ∈ S)
    (hcent : S ≤ Subgroup.centralizer ({z} : Set Y))
    (hcomm : ∀ a ∈ Subgroup.centralizer ({z} : Set Y),
      ∀ b ∈ Subgroup.centralizer ({z} : Set Y), a * b * a⁻¹ * b⁻¹ ∈ S) :
    ∃ SX : Subgroup X, x ∈ SX ∧ SX ≤ Subgroup.centralizer ({x} : Set X) ∧
      (∀ a ∈ Subgroup.centralizer ({x} : Set X),
        ∀ b ∈ Subgroup.centralizer ({x} : Set X), a * b * a⁻¹ * b⁻¹ ∈ SX) ∧
      Nonempty (↥SX ≃* ↥S) := by
  have hz : e.symm z = x := by rw [← hex, MulEquiv.symm_apply_apply]
  let SX : Subgroup X := S.map e.symm.toMonoidHom
  refine ⟨SX, ?_, ?_, ?_, ⟨(Subgroup.equivMapOfInjective S e.symm.toMonoidHom
    e.symm.injective).symm⟩⟩
  · exact Subgroup.mem_map.2 ⟨z, hzS, hz⟩
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hcent hr)
    have hc := congrArg e.symm h
    simpa [hz] using hc
  · intro a ha b hb
    have ha' : e a ∈ Subgroup.centralizer ({z} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
      simpa [hex] using congrArg e ha
    have hb' : e b ∈ Subgroup.centralizer ({z} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hb ⊢
      simpa [hex] using congrArg e hb
    have h := hcomm (e a) ha' (e b) hb'
    refine Subgroup.mem_map.2 ⟨e a * e b * (e a)⁻¹ * (e b)⁻¹, h, ?_⟩
    simp

private lemma r891_map_conj_centralizer {G : Type} [Group G] {S : Subgroup G} {g z : G}
    (h : g * z * g⁻¹ ∈ Subgroup.centralizer (S : Set G)) :
    S.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.1 hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := Subgroup.mem_centralizer_iff.1 h s₀ hs₀
  have := congrArg (fun t => g⁻¹ * t * g) hc
  simpa [MulAut.conj_apply, mul_assoc] using this

private lemma r891_map_centralizer_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {x : X} {z : Y} (hex : e x = z) {S : Subgroup Y}
    (h : S ≤ Subgroup.centralizer ({z} : Set Y)) :
    S.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({x} : Set X) := by
  have hz : e.symm z = x := by rw [← hex, MulEquiv.symm_apply_apply]
  intro s hs
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (h hr)
  have := congrArg e.symm hc
  simpa [hz] using this

private lemma r891_two_pow_mod_three_of_even {n : ℕ} (h : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := h
  have hm : 2 ^ (k + k) ≡ 1 [MOD 3] := by
    rw [← two_mul, pow_mul]
    simpa using (show (2 : ℕ) ^ 2 ≡ 1 [MOD 3] by decide).pow k
  simpa [Nat.ModEq] using hm

private lemma r891_two_pow_mod_three_of_odd {n : ℕ} (h : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := h
  have h1 : 2 ^ (2 * k) % 3 = 1 := by
    simpa [two_mul] using r891_two_pow_mod_three_of_even (n := 2 * k) ⟨k, by ring⟩
  rw [pow_succ, Nat.mul_mod, h1]

section Model


theorem r891_is3D4_model {X : Type} [Group X] {n : ℕ} (hX : Is3D4 X n) :
    1 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σ c = c ^ 2 ^ n) ∧
        Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hadm := hX.admissible
  rcases hX with ⟨ht, -⟩ | ⟨-, -, hM⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two
        hadm.2.1 hM.2
    exact ⟨hadm.2.1, K, inferInstance, inferInstance, σ, hcard, hσ, ⟨e⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end Model

section Classes


theorem r891_threeA_model_of_conj_short
    {X : Type} [Group X] [Finite X] {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn1 : 1 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {x : X}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgS : g * e x * g⁻¹ ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) :
    ∃ R : Subgroup X, x ∈ R ∧ R ≤ centralizer ({x} : Set X) ∧
        (∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
          a * b * a⁻¹ * b⁻¹ ∈ R) ∧
        ((Even n ∧ CFSG.IsQuasisimple ↥R ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ n ∧ Nonempty (↥R ≃* Matrix.SpecialLinearGroup (Fin 3) F)) ∨
          (Odd n ∧ ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
            (U : Subgroup (GL (Fin 3) Ω)), (U : Set (GL (Fin 3) Ω)) = unitarySet (2 ^ n) 3 ∧
            ∃ e : ↥R ≃* ↥U, 2 ≤ n → CFSG.IsQuasisimple ↥R ∧
              ∀ y : ↥R, y ∈ center ↥R ↔ ∃ μ : Ω,
                (((e y : ↥U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
                  Matrix.scalar (Fin 3) μ)) := by
  let z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e x
  have hz3 : z ^ 3 = 1 := by
    change (e x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have hz1 : z ≠ 1 := by
    intro h
    refine hx1 (e.injective ?_)
    rw [map_one]
    exact h
  have hw3 : (g * z * g⁻¹) ^ 3 = 1 := by
    have h : g * z * g⁻¹ = (MulAut.conj g) z := rfl
    rw [h, ← map_pow, hz3, map_one]
  have hw1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have h' : g⁻¹ * (g * z * g⁻¹) * g = 1 := by
      have := congrArg (fun t => g⁻¹ * t * g) h
      rwa [show g⁻¹ * 1 * g = 1 by group] at this
    rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h'
  rcases Nat.even_or_odd n with hn_even | hn_odd
  ·
    have hq1 : 2 ^ n % 3 = 1 := r891_two_pow_mod_three_of_even hn_even
    obtain ⟨c, R, hcR, hRcent, hRcomm, hRq, F, hFfield, hFfin, hFcard, ⟨eR⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model (K := K) (ℓ := 2) (f := n)
        Nat.prime_two hn1 (by norm_num) hq1 hcard hσ hgS hw3 hw1
    have hdz : (c * g) * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by
      group
    have hRcent' : R ≤ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _) := by
      rw [hdz]
      exact hRcent
    have hRcomm' : ∀ a ∈ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _),
        ∀ b ∈ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _),
          a * b * a⁻¹ * b⁻¹ ∈ R := by
      rw [hdz]
      exact hRcomm
    let S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      R.map (MulAut.conj (c * g)⁻¹).toMonoidHom
    have hzS : z ∈ S := r891_mem_map_conj (c := c * g) (z := z) (hdz ▸ hcR)
    have hcentS : S ≤ Subgroup.centralizer ({z} : Set _) :=
      r891_centralizer_map_conj (c := c * g) (z := z) hRcent'
    have hcommS := r891_commutator_map_conj (c := c * g) (z := z) hRcomm'
    obtain ⟨RX, hxRX, hcentX, hcommX, ⟨eRX⟩⟩ :=
      r891_transport_threeA e rfl hzS hcentS hcommS
    let eRS : ↥R ≃* ↥S :=
      Subgroup.equivMapOfInjective R (MulAut.conj (c * g)⁻¹).toMonoidHom
        (MulAut.conj (c * g)⁻¹).injective
    have hQS : CFSG.IsQuasisimple ↥S :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eRS hRq
    have hQSX : CFSG.IsQuasisimple ↥RX :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eRX.symm hQS
    exact ⟨RX, hxRX, hcentX, hcommX, Or.inl ⟨hn_even, hQSX, F, hFfield, hFfin,
      hFcard, ⟨eRX.trans (eRS.symm.trans eR)⟩⟩⟩
  ·
    have hq1 : 2 ^ n % 3 = 2 := r891_two_pow_mod_three_of_odd hn_odd
    by_cases hn2 : 2 ≤ n
    · have hq2 : 2 < 2 ^ n := by
        have h4 : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        omega
      obtain ⟨c, R, hcR, hRcent, hRcomm, hRq, U, hU, eRU, hZ⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary (K := K) (ℓ := 2)
          (f := n) Nat.prime_two hn1 (by norm_num) hq1 hq2 hcard hσ hgS hw3 hw1
      have hdz : (c * g) * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by
        group
      have hRcent' : R ≤ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _) := by
        rw [hdz]
        exact hRcent
      have hRcomm' : ∀ a ∈ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _),
          ∀ b ∈ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _),
            a * b * a⁻¹ * b⁻¹ ∈ R := by
        rw [hdz]
        exact hRcomm
      let S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
        R.map (MulAut.conj (c * g)⁻¹).toMonoidHom
      have hzS : z ∈ S := r891_mem_map_conj (c := c * g) (z := z) (hdz ▸ hcR)
      have hcentS : S ≤ Subgroup.centralizer ({z} : Set _) :=
        r891_centralizer_map_conj (c := c * g) (z := z) hRcent'
      have hcommS := r891_commutator_map_conj (c := c * g) (z := z) hRcomm'
      obtain ⟨RX, hxRX, hcentX, hcommX, ⟨eRX⟩⟩ :=
        r891_transport_threeA e rfl hzS hcentS hcommS
      let eRS : ↥R ≃* ↥S :=
        Subgroup.equivMapOfInjective R (MulAut.conj (c * g)⁻¹).toMonoidHom
          (MulAut.conj (c * g)⁻¹).injective
      have hQS : CFSG.IsQuasisimple ↥S :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eRS hRq
      have hQSX : CFSG.IsQuasisimple ↥RX :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eRX.symm hQS
      have : CharP K 2 := by
        have : Fintype K := Fintype.ofFinite K
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact charP_of_card_eq_prime_pow (p := 2) (f := 3 * n) (by
          rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
      refine ⟨RX, hxRX, hcentX, hcommX, Or.inr ⟨hn_odd, ?_⟩⟩
      refine ⟨AlgebraicClosure K, inferInstance, inferInstance, ?_, U, hU,
        ⟨eRX.trans (eRS.symm.trans eRU), ?_⟩⟩
      · exact charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
      · intro _
        refine ⟨hQSX, ?_⟩
        intro y
        rw [CFSG.RankThree.PartTwo.Sec21.Item219LieProof.mem_center_mulEquiv eRX y,
          CFSG.RankThree.PartTwo.Sec21.Item219LieProof.mem_center_mulEquiv eRS.symm (eRX y)]
        exact hZ (eRS.symm (eRX y))
    ·
      obtain ⟨c, R, hcR, hRcent, hRcomm, U, hU, ⟨eRU⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary_two (K := K)
          (ℓ := 2) (f := n) Nat.prime_two hn1 (by norm_num) hq1 hcard hσ hgS hw3 hw1
      have hdz : (c * g) * z * (c * g)⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by
        group
      have hRcent' : R ≤ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _) := by
        rw [hdz]
        exact hRcent
      have hRcomm' : ∀ a ∈ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _),
          ∀ b ∈ Subgroup.centralizer ({(c * g) * z * (c * g)⁻¹} : Set _),
            a * b * a⁻¹ * b⁻¹ ∈ R := by
        rw [hdz]
        exact hRcomm
      let S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
        R.map (MulAut.conj (c * g)⁻¹).toMonoidHom
      have hzS : z ∈ S := r891_mem_map_conj (c := c * g) (z := z) (hdz ▸ hcR)
      have hcentS : S ≤ Subgroup.centralizer ({z} : Set _) :=
        r891_centralizer_map_conj (c := c * g) (z := z) hRcent'
      have hcommS := r891_commutator_map_conj (c := c * g) (z := z) hRcomm'
      obtain ⟨RX, hxRX, hcentX, hcommX, ⟨eRX⟩⟩ :=
        r891_transport_threeA e rfl hzS hcentS hcommS
      let eRS : ↥R ≃* ↥S :=
        Subgroup.equivMapOfInjective R (MulAut.conj (c * g)⁻¹).toMonoidHom
          (MulAut.conj (c * g)⁻¹).injective
      have : CharP K 2 := by
        have : Fintype K := Fintype.ofFinite K
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact charP_of_card_eq_prime_pow (p := 2) (f := 3 * n) (by
          rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
      refine ⟨RX, hxRX, hcentX, hcommX, Or.inr ⟨hn_odd, ?_⟩⟩
      refine ⟨AlgebraicClosure K, inferInstance, inferInstance, ?_, U, hU,
        ⟨eRX.trans (eRS.symm.trans eRU), ?_⟩⟩
      · exact charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
      · intro hn2'
        exact absurd hn2' hn2

theorem r891_three_classes {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n) {x : X}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    (∃ S : Subgroup X, S ≤ centralizer ({x} : Set X) ∧
        Nat.card S = (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1)) ∨
      ∃ R : Subgroup X, x ∈ R ∧ R ≤ centralizer ({x} : Set X) ∧
        (∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
          a * b * a⁻¹ * b⁻¹ ∈ R) ∧
        ((Even n ∧ CFSG.IsQuasisimple ↥R ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ n ∧ Nonempty (↥R ≃* Matrix.SpecialLinearGroup (Fin 3) F)) ∨
          (Odd n ∧ ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
            (U : Subgroup (GL (Fin 3) Ω)), (U : Set (GL (Fin 3) Ω)) = unitarySet (2 ^ n) 3 ∧
            ∃ e : ↥R ≃* ↥U, 2 ≤ n → CFSG.IsQuasisimple ↥R ∧
              ∀ y : ↥R, y ∈ center ↥R ↔ ∃ μ : Ω,
                (((e y : ↥U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
                  Matrix.scalar (Fin 3) μ)) := by
  obtain ⟨hn1, K, hKfield, hKfin, σ, hcard, hσ, ⟨e⟩⟩ := r891_is3D4_model hX
  let z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e x
  have hz3 : z ^ 3 = 1 := by
    change (e x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have hz1 : z ≠ 1 := by
    intro h
    refine hx1 (e.injective ?_)
    rw [map_one]
    exact h
  have hq3 : ¬ 3 ∣ 2 ^ n := by
    intro h
    have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h2
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h := ringEquiv_cube_apply_eq (K := K) (q := 2 ^ n) hcard hσ c
    simpa [pow_succ] using h
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds
    (K := K) (q := 2 ^ n) (σ := σ) hcard hσ hq3 z hz3 hz1
  rcases hg with hgS | hgC
  · exact Or.inr (r891_threeA_model_of_conj_short hn1 hcard σ hσ e hx3 hx1 g hgS)
  ·
    let S₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom
    let S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      S₀.map (MulAut.conj g⁻¹).toMonoidHom
    let SX : Subgroup X := S.map e.symm.toMonoidHom
    have hcentS : S ≤ Subgroup.centralizer ({z} : Set _) :=
      r891_map_conj_centralizer hgC
    have hcentX : SX ≤ Subgroup.centralizer ({x} : Set X) :=
      r891_map_centralizer_mulEquiv e rfl hcentS
    have hcardS : Nat.card S = Nat.card S₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hcardSX : Nat.card SX = Nat.card S :=
      Subgroup.card_map_of_injective e.symm.injective
    refine Or.inl ⟨SX, hcentX, ?_⟩
    rw [hcardSX, hcardS, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.card_d4ShortSL2 hσ3,
      hcard]


theorem r891_threeA_model_of_central_sylow
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n)
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) {x : X}
    (hxc : ∀ p ∈ P, p * x = x * p) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ R : Subgroup X, x ∈ R ∧ R ≤ centralizer ({x} : Set X) ∧
        (∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
          a * b * a⁻¹ * b⁻¹ ∈ R) ∧
        ((Even n ∧ CFSG.IsQuasisimple ↥R ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ n ∧ Nonempty (↥R ≃* Matrix.SpecialLinearGroup (Fin 3) F)) ∨
          (Odd n ∧ ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
            (U : Subgroup (GL (Fin 3) Ω)), (U : Set (GL (Fin 3) Ω)) = unitarySet (2 ^ n) 3 ∧
            ∃ e : ↥R ≃* ↥U, 2 ≤ n → CFSG.IsQuasisimple ↥R ∧
              ∀ y : ↥R, y ∈ center ↥R ↔ ∃ μ : Ω,
                (((e y : ↥U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
                  Matrix.scalar (Fin 3) μ)) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn1, K, hKfield, hKfin, σ, hcard, hσ, ⟨e⟩⟩ := r891_is3D4_model hX
  let P' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := P.map e.toMonoidHom
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
    rw [show Nat.card P' = Nat.card P from Subgroup.card_map_of_injective
      (f := e.toMonoidHom) e.injective]
    simpa only [Subgroup.card_top, Nat.card_congr e.toEquiv] using hP.card_eq
  have hxc' : ∀ p ∈ P', p * e x = e x * p := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hp
    change e a * e x = e x * e a
    simpa only [map_mul] using congrArg e (hxc a ha)
  have hx3' : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx1' : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hgS⟩ := D4ThreeBCentralizer.exists_conj_mem_short_of_central_sylow_three_triality_two
    hn1 hcard σ hσ hP' hxc' hx3' hx1'
  exact r891_threeA_model_of_conj_short hn1 hcard σ hσ e hx3 hx1 g hgS

theorem r891SL3Two_R891X_of_central_sylow_of_two_le
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n) (hX : Is3D4 X n)
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hZ : Nat.card (ZOf P) = 3) : R891SL3Two ↥(R891X ⊤ (ZOf P) n) n := by
  obtain ⟨x, hxZ, hx3, hZx⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hZ
  have hxc : ∀ p ∈ P, p * x = x * p :=
    fun p hp => Subgroup.mem_centralizer_iff.mp hxZ.2 p hp
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    have : orderOf x = 1 := by rw [h, orderOf_one]
    omega
  obtain ⟨R, _, hRC, hcomm, hmodel⟩ := r891_threeA_model_of_central_sylow hX hP hxc hx3' hx1
  have hRshape : R891SL3Two ↥R n := by
    rcases hmodel with ⟨hev, hRq, F, hFfield, hFfin, hFcard, ⟨eR⟩⟩ |
        ⟨hod, Ω, hΩfield, hΩclosed, hΩchar, U, hU, eRU, hRq⟩
    · exact Or.inr (Or.inl ⟨hn, hev, threeCover_psl3_of_mulEquiv hn hev hFcard hRq eR⟩)
    · exact Or.inr (Or.inr ⟨hn, hod,
        threeCover_psu3_of_mulEquiv hn hod hU (hRq hn).1 eRU⟩)
  have hRperfect : ⁅R, R⁆ = R := by
    have hq : CFSG.Open.IsQuasisimple ↥R := by
      rcases hRshape with ⟨h1, _⟩ | ⟨_, _, hTC⟩ | ⟨_, _, hTC⟩
      · omega
      · exact hTC.1
      · exact hTC.1
    have hmap := congrArg (Subgroup.map R.subtype) hq.1
    simpa only [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype] using hmap
  have hcent : centralizer ((ZOf P : Subgroup X) : Set X) =
      centralizer ({x} : Set X) := by
    rw [hZx, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hres : R891X (⊤ : Subgroup X) (ZOf P) n = R := by
    rw [R891X, if_neg (by omega), top_inf_eq, hcent]
    exact derInf8_eq_of_perfect hRC hRperfect hcomm
  rwa [hres]


private theorem r891_threeB_model_of_conj_centralizer
    {X : Type} [Group X] [Finite X] {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn1 : 1 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {x : X}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgC : g * e x * g⁻¹ ∈ centralizer
      ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Set _)) :
    ∃ R : Subgroup X, R ≤ centralizer ({x} : Set X) ∧
      (∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
        a * b * a⁻¹ * b⁻¹ ∈ R) ∧ LieModel ↥R .PSL 2 2 (3 * n) ∧ ⁅R, R⁆ = R := by
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h := ringEquiv_cube_apply_eq (K := K) (q := 2 ^ n) hcard hσ c
    simpa [pow_succ] using h
  have hq3 : ¬ 3 ∣ 2 ^ n := fun h =>
    (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hw3 : (g * e x * g⁻¹) ^ 3 = 1 := by
    change ((MulAut.conj g) (e x)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hx3, map_one, map_one]
  have hw1 : g * e x * g⁻¹ ≠ 1 := by
    intro h
    have h' : (MulAut.conj g) (e x) = (MulAut.conj g) 1 := by
      change g * e x * g⁻¹ = g * 1 * g⁻¹
      simpa only [mul_one, mul_inv_cancel] using h
    exact hx1 (e.injective (((MulAut.conj g).injective h').trans (map_one e).symm))
  let S₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom
  let S := S₀.map (MulAut.conj g⁻¹).toMonoidHom
  let SX := S.map e.symm.toMonoidHom
  have hcentS : S ≤ centralizer ({e x} : Set _) := r891_map_conj_centralizer hgC
  have hcentX : SX ≤ centralizer ({x} : Set X) :=
    r891_map_centralizer_mulEquiv e rfl hcentS
  have hcomm₀ := (CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds
    K (2 ^ n) σ hcard hσ hq3 (g * e x * g⁻¹) hgC hw3 hw1).1
  have hcommS := r891_commutator_map_conj (c := g) hcomm₀
  have hcommX : ∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
      a * b * a⁻¹ * b⁻¹ ∈ SX := by
    intro a ha b hb
    have ha' : e a ∈ centralizer ({e x} : Set _) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
      simpa only [map_mul] using congrArg e ha
    have hb' : e b ∈ centralizer ({e x} : Set _) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hb ⊢
      simpa only [map_mul] using congrArg e hb
    refine Subgroup.mem_map.2 ⟨e a * e b * (e a)⁻¹ * (e b)⁻¹,
      hcommS _ ha' _ hb', ?_⟩
    change e.symm (e a * e b * (e a)⁻¹ * (e b)⁻¹) = a * b * a⁻¹ * b⁻¹
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  obtain ⟨e₀⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148B.Res148BD4.nonempty_sl2_equiv_short hσ3
  let eS : ↥S₀ ≃* ↥S := Subgroup.equivMapOfInjective S₀
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  let eX : ↥S ≃* ↥SX := Subgroup.equivMapOfInjective S e.symm.toMonoidHom e.symm.injective
  let eRX : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥SX := e₀.trans (eS.trans eX)
  have hKcard : Nat.card K = 2 ^ (3 * n) := by rw [hcard, ← pow_mul, mul_comm]
  let instK : Fintype K := Fintype.ofFinite K
  have hKfin : @Fintype.card K instK = 2 ^ (3 * n) := by
    rw [← @Nat.card_eq_fintype_card K instK, hKcard]
  have hmodel : LieModel ↥SX .PSL 2 2 (3 * n) :=
    @CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two
      ↥SX _ (3 * n) (by omega) K _ instK hKfin eRX.symm
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4
  have hperfX : Group.IsPerfect ↥SX :=
    Group.IsPerfect.ofSurjective (f := eRX.toMonoidHom) eRX.surjective
  exact ⟨SX, hcentX, hcommX, hmodel, Subgroup.isPerfect_iff.mp hperfX⟩

theorem r891_x1_model_of_not_conj_sylow_center
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n)
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hZ : Nat.card (ZOf P) = 3) {A : Subgroup X} (hA : Nat.card A = 3)
    (hnot : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≠ ZOf P) :
    LieModel ↥(DerInf8 (centralizer (A : Set X))) .PSL 2 2 (3 * n) ∧
      R891CentShape ↥(centralizer (A : Set X)) n := by
  obtain ⟨a, _, haord, hAa⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hA
  obtain ⟨z, hzZ, hzord, hZz⟩ := CFSG.GroupTheory.exists_generator_of_card_prime Nat.prime_three hZ
  have ha3 : a ^ 3 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have hz3 : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have ha1 : a ≠ 1 := by intro h; have := haord; rw [h, orderOf_one] at this; omega
  have hz1 : z ≠ 1 := by intro h; have := hzord; rw [h, orderOf_one] at this; omega
  have hzc : ∀ p ∈ P, p * z = z * p :=
    fun p hp => Subgroup.mem_centralizer_iff.mp hzZ.2 p hp
  obtain ⟨hn1, K, hKfield, hKfin, σ, hcard, hσ, ⟨e⟩⟩ := r891_is3D4_model hX
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P' := P.map e.toMonoidHom
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
    rw [show Nat.card P' = Nat.card P from Subgroup.card_map_of_injective
      (f := e.toMonoidHom) e.injective]
    simpa only [Subgroup.card_top, Nat.card_congr e.toEquiv] using hP.card_eq
  have hzc' : ∀ p ∈ P', p * e z = e z * p := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hp
    change e b * e z = e z * e b
    simpa only [map_mul] using congrArg e (hzc b hb)
  have hz3' : (e z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz1' : e z ≠ 1 := fun h => hz1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨k, hkS⟩ := D4ThreeBCentralizer.exists_conj_mem_short_of_central_sylow_three_triality_two
    hn1 hcard σ hσ hP' hzc' hz3' hz1'
  have ha3' : (e a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have ha1' : e a ≠ 1 := fun h => ha1 (e.injective (h.trans (map_one e).symm))
  have hq3 : ¬ 3 ∣ 2 ^ n := fun h =>
    (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h := ringEquiv_cube_apply_eq (K := K) (q := 2 ^ n) hcard hσ c
    simpa [pow_succ] using h
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3 * n) (by omega) (by rw [hcard, ← pow_mul, mul_comm])
  have h3K : (3 : K) ≠ 0 := by
    rw [show (3 : K) = 1 + (2 : K) by ring, CharTwo.two_eq_zero, add_zero]
    exact one_ne_zero
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds
    K (2 ^ n) σ hcard hσ hq3 (e a) ha3' ha1'
  have hgC : g * e a * g⁻¹ ∈ centralizer
      ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Set _) := by
    rcases hg with hgS | hgC
    · exfalso
      have hpow (u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (v : X)
          (hv : v ^ 3 = 1) : (u * e v * u⁻¹) ^ 3 = 1 := by
        change ((MulAut.conj u) (e v)) ^ 3 = 1
        rw [← map_pow, ← map_pow, hv, map_one, map_one]
      have hne (u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (v : X)
          (hv : v ≠ 1) : u * e v * u⁻¹ ≠ 1 := by
        intro h
        have h' : (MulAut.conj u) (e v) = (MulAut.conj u) 1 := by
          change u * e v * u⁻¹ = u * 1 * u⁻¹
          simpa only [mul_one, mul_inv_cancel] using h
        exact hv (e.injective (((MulAut.conj u).injective h').trans (map_one e).symm))
      obtain ⟨t, _, ht⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_short
        hσ3 h3K hgS hkS (hpow g a ha3) (hne g a ha1) (hpow k z hz3) (hne k z hz1)
      have haz : (k⁻¹ * t * g) * e a * (k⁻¹ * t * g)⁻¹ = e z := by
        have h := congrArg (fun w => k⁻¹ * w * k) ht
        convert h using 1; group
      have hconj : (e.symm (k⁻¹ * t * g)) * a * (e.symm (k⁻¹ * t * g))⁻¹ = z := by
        apply e.injective
        simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using haz
      apply hnot (e.symm (k⁻¹ * t * g))
      rw [hAa, hZz, MonoidHom.map_zpowers]
      change Subgroup.zpowers ((e.symm (k⁻¹ * t * g)) * a *
        (e.symm (k⁻¹ * t * g))⁻¹) = Subgroup.zpowers z
      rw [hconj]
    · exact hgC
  obtain ⟨R, hRC, hcomm, hmodel, hperf⟩ :=
    r891_threeB_model_of_conj_centralizer hn1 hcard σ hσ e ha3 ha1 g hgC
  have hcent : centralizer (A : Set X) = centralizer ({a} : Set X) := by
    rw [hAa, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hres : DerInf8 (centralizer (A : Set X)) = R := by
    rw [hcent]
    exact derInf8_eq_of_perfect hRC hperf hcomm
  refine ⟨by rwa [hres], ?_⟩
  let C := centralizer (A : Set X)
  let U := R.subgroupOf C
  have hRC' : R ≤ C := by simpa only [C, hcent] using hRC
  refine ⟨U, CFSG.Blueprint.LieModel.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hRC').symm hmodel, ?_⟩
  intro b c
  change ((b : X) * (c : X) * (b : X)⁻¹ * (c : X)⁻¹) ∈ R
  exact hcomm b (by simpa only [C, hcent] using b.2) c
    (by simpa only [C, hcent] using c.2)


end Classes

section Outer


theorem r891_outer_cases {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n)
    {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : α ∉ (MulAut.conj : X →* MulAut X).range) :
    Nat.card (R891Fix α) = ordG2 (2 ^ n) ∨
      ∃ (π : Bool) (F : Type) (_ : Field F) (_ : Finite F), Sec4.PiField π 2 n F ∧
        cond π (Even n) (Odd n) ∧
        Nonempty (↥(R891Fix α) ≃* ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F))) := by
  obtain ⟨hn1, K, hKfield, hKfin, σ, hcard, hσ, ⟨e⟩⟩ := r891_is3D4_model hX
  have hβ3 : (MulAut.congr e α) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut (MulAut.congr e α) := by
    intro h
    apply hout
    have h' : MulAut.congr e α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := h
    exact (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp h'
  rcases CFSG.LocalAnalysis.GLTheoremA.T158G.t158g_td4_outer_cases hn1 hcard hσ hβ3 hβout with
    ⟨k, hkfield, hkfin, hkcard, ⟨eG⟩⟩ | ⟨π, F, hFfield, hFfin, hPi, hc, ⟨eP⟩⟩
  · left
    have hcardfix : Nat.card (R891Fix α) =
        Nat.card (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e α)) :=
      Nat.card_congr
        (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e α).toEquiv
    rw [hcardfix, Nat.card_congr eG.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hkcard]
  · right
    refine ⟨π, F, hFfield, hFfin, hPi, hc, ?_⟩
    exact ⟨(CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e α).trans eP⟩


end Outer

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
