module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearSylowGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearDihedralModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaImage
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI

universe u

theorem psl2_even_subgroup_sylow_elementary
    {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (R : Sylow 2 A) : IsElementaryAbelian 2 R := by
  obtain ⟨P, hP⟩ := R.exists_comap_subtype_eq
  let : IsElementaryAbelian 2 P := (psl2_even_sylow_elementary_card f hcard P).1
  let embedding : R →* P :=
    { toFun r := ⟨((r : A) : PSL2MatrixGroup K), by
        change (r : A) ∈ (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype
        rw [hP]
        exact r.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply CFSG.ShultStronglyClosedTI.LocalTheta.elementary_of_injective embedding
  intro r s hrs
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : P => (a : PSL2MatrixGroup K)) hrs

theorem psl2_even_no_split_primes_frobenius_kernel
    {K : Type u} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (hAeven : Even (Nat.card A))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K - 1))
    (hAnot : ¬ ∃ n : ℕ, Nat.card A = 2 ^ n) (R : Sylow 2 A) :
    ∃ N : Subgroup A, IsFrobeniusGroupWithKernelComplement N (R : Subgroup A) ∧
      Nat.card R = 2 ∧ IsCyclic N ∧ Odd (Nat.card N) ∧
      3 ≤ Nat.card N ∧ Nat.card N ∣ Nat.card K + 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRne : (R : Subgroup A) ≠ ⊥ := R.ne_bot_of_dvd_card
    (even_iff_two_dvd.mp hAeven)
  have hRproper : (R : Subgroup A) ≠ ⊤ := by
    intro htop
    have hRA : Nat.card R = Nat.card A := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
    exact hAnot ⟨n, hRA.symm.trans hn⟩
  obtain ⟨N, hFrob, hRcard, hNodd, hNcomm, _⟩ :=
    elementary_two_TI_frobenius_decomposition (R : Subgroup A) hRne hRproper
      (psl2_even_subgroup_sylow_elementary f hcard A R)
      (psl2_no_split_primes_subgroup_sylow_TI f hcard A hcop R)
  let : IsMulCommutative N := hNcomm
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot
  let xG : PSL2MatrixGroup K := (x : A)
  have hxG : xG ≠ 1 := by
    intro h
    exact hx (Subtype.ext (Subtype.ext h))
  have hxodd : Odd (orderOf xG) := by
    have h := hNodd.of_dvd_nat (orderOf_dvd_natCard x)
    simpa only [xG, Subgroup.orderOf_coe] using h
  let C := Subgroup.centralizer ({xG} : Set (PSL2MatrixGroup K))
  obtain ⟨hCcyclic, hCcard, _⟩ :=
    psl2_even_odd_element_full_centralizer f hf hcard xG hxG hxodd
  let : IsCyclic C := hCcyclic
  let embedding : N →* C :=
    { toFun y := ⟨((y : A) : PSL2MatrixGroup K), by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg (fun z : N => ((z : A) : PSL2MatrixGroup K)) (isMulCommutative_iff.mp hNcomm y x)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hinj : Function.Injective embedding := by
    intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : C => (a : PSL2MatrixGroup K)) hyz
  have hNcyclic : IsCyclic N := isCyclic_of_injective embedding hinj
  have hNdiv : Nat.card N ∣ Nat.card C := Subgroup.card_dvd_of_injective embedding hinj
  have hNgt : 1 < Nat.card N :=
    (Subgroup.one_lt_card_iff_ne_bot N).mpr hFrob.kernel_ne_bot
  have hNge : 3 ≤ Nat.card N := by
    obtain ⟨n, hn⟩ := hNodd
    omega
  have hNplus : Nat.card N ∣ Nat.card K + 1 := by
    rcases hCcard with hminus | hplus
    · have hdiv : Nat.card N ∣ Nat.card K - 1 := hminus ▸ hNdiv
      have hcopN : Nat.Coprime (Nat.card N) (Nat.card K - 1) :=
        hcop.of_dvd_left N.card_subgroup_dvd_card
      have hNone : Nat.card N = 1 := hcopN.eq_one_of_dvd hdiv
      omega
    · exact hplus ▸ hNdiv
  exact ⟨N, hFrob, hRcard, hNcyclic, hNodd, hNge, hNplus⟩

theorem psl2_even_no_split_primes_dihedral
    {K : Type u} [Field K] [Finite K]
    (hKeven : Even (Nat.card K)) (hKge : 4 ≤ Nat.card K)
    (A : Subgroup (PSL2MatrixGroup K)) (hAeven : Even (Nat.card A))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K - 1))
    (hAnot : ¬ ∃ n : ℕ, Nat.card A = 2 ^ n) :
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ m ∣ Nat.card K + 1 ∧
      Nonempty (A ≃* DihedralGroup m) ∧
      ∃ phi : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod m)),
        Nonempty (A ≃* Multiplicative (ZMod m) ⋊[phi] Multiplicative (ZMod 2)) ∧
        ∀ t : Multiplicative (ZMod 2), t ≠ 1 →
          ∀ x : Multiplicative (ZMod m), phi t x = x⁻¹) ∧
      ∀ R : Sylow 2 A, Nat.card R = 2 := by
  obtain ⟨f, hf, hcard⟩ := even_field_binary_size hKeven hKge
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Sylow 2 A := default
  obtain ⟨N, hFrob, hRcard, hNcyclic, hNodd, hNge, hNplus⟩ :=
    psl2_even_no_split_primes_frobenius_kernel f hf hcard A hAeven hcop hAnot R
  let : IsCyclic N := hNcyclic
  obtain ⟨_, _, hdihedral⟩ := cyclic_two_frobenius_dihedral N (R : Subgroup A) hFrob hRcard
  obtain ⟨phi, hsemi, hinvert⟩ :=
    cyclic_two_frobenius_semidirect_inversion N (R : Subgroup A) hFrob hRcard
  refine ⟨⟨Nat.card N, hNodd, hNge, hNplus, hdihedral, phi, hsemi, hinvert⟩, ?_⟩
  intro S
  exact (Nat.card_congr (Sylow.equiv S R).toEquiv).trans hRcard

theorem linear_even_subgroup_without_split_primes_dihedral
    (K : Type) [Field K] [Finite K]
    (hKeven : Even (Nat.card K)) (hKge : 4 ≤ Nat.card K)
    (A : Subgroup (CFSG.Open.GLAProj (CFSG.Open.GLASLGroup (Fin 2) K)))
    (hAeven : Even (Nat.card A))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K - 1))
    (hAnot : ¬ ∃ n : ℕ, Nat.card A = 2 ^ n) :
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ m ∣ Nat.card K + 1 ∧
      Nonempty (A ≃* DihedralGroup m) ∧
      ∃ phi : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod m)),
        Nonempty (A ≃* Multiplicative (ZMod m) ⋊[phi] Multiplicative (ZMod 2)) ∧
        ∀ t : Multiplicative (ZMod 2), t ≠ 1 →
          ∀ x : Multiplicative (ZMod m), phi t x = x⁻¹) ∧
      ∀ R : Sylow 2 A, Nat.card R = 2 := by
  let e := CFSG.ShultStronglyClosedTI.glaSLQuotientEquivPSL (ι := Fin 2) (K := K)
  let B := A.map e.toMonoidHom
  let c : A ≃* B := A.equivMapOfInjective e.toMonoidHom e.injective
  have hAB : Nat.card A = Nat.card B := Nat.card_congr c.toEquiv
  have hBeven : Even (Nat.card B) := hAB ▸ hAeven
  have hBcop : Nat.Coprime (Nat.card B) (Nat.card K - 1) := hAB ▸ hcop
  have hBnot : ¬ ∃ n : ℕ, Nat.card B = 2 ^ n := by
    intro h
    exact hAnot (hAB.symm ▸ h)
  obtain ⟨⟨m, hmOdd, hmge, hmplus, hBdih, phi, hBsemi, hinvert⟩, hBsylow⟩ :=
    psl2_even_no_split_primes_dihedral hKeven hKge B hBeven hBcop hBnot
  refine ⟨⟨m, hmOdd, hmge, hmplus, ⟨c.trans hBdih.some⟩, phi,
    ⟨c.trans hBsemi.some⟩, hinvert⟩, ?_⟩
  intro R
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 B := R.mapSurjective (f := c.toMonoidHom) c.surjective
  have hRS : Nat.card S = Nat.card R := by
    change Nat.card ((R : Subgroup A).map c.toMonoidHom) = Nat.card R
    exact Subgroup.card_map_of_injective c.injective
  exact hRS.symm.trans (hBsylow S)

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
