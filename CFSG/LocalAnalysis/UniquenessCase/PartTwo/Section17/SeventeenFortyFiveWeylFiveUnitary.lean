module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveProj
import CFSG.RankThree.PartOne.KC.UnitaryDefiningThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private noncomputable def unitaryPSUEquivPrimeFormP (h : UnitaryFieldData p f K) (n : ℕ) :
    unitaryPSU h n ≃* primeFormP h (1 : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.congr (unitaryScalars h n)
    (normOneScalars h (gramSU h (1 : Matrix (Fin n) (Fin n) K)) n)
    (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨c, hcN, hcn, hw'⟩ := mem_normOneScalars.mp hw
        exact mem_normOneScalars.mpr ⟨c, hcN, hcn, by simpa using hw'⟩
      · intro hz
        obtain ⟨c, hcN, hcn, hz'⟩ := mem_normOneScalars.mp hz
        refine ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ?_, ?_⟩
        · exact mem_normOneScalars.mpr ⟨c, hcN, hcn, by simpa using hz'⟩
        · exact (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).apply_symm_apply z)

theorem weylFivePower_of_model_PSU {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSU n p f) (hn : n ≤ 4) (hp2 : p ≠ 2) (hp31 : p ≠ 31) :
    WeylFivePower X := by
  obtain ⟨⟨hp, hf, hn3, hne⟩, K, hfield, hfin, hKcard, ⟨e⟩⟩ := h
  have _ : p ≠ 2 := hp2
  have hpow : (p ^ f) ^ 2 = p ^ (2 * f) := by
    rw [← pow_mul, show f * 2 = 2 * f from by omega]
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hKcard, hpow]⟩
  have hringChar : ringChar K = p := (CharP.eq (R := K) hU.charP (ringChar.charP K)).symm
  have hK31 : ringChar K ≠ 31 := by
    rw [hringChar]
    exact hp31
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) :=
    CFSG.RankThree.PartOne.KCUnitaryDefining.isPrimeFormGram_one
  have hnpos : 1 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have hZ : ∀ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (p ^ f) K →
      c ^ 31 = 1 → c = 1 := by
    intro c hc hc31
    have hdet : c ^ n = 1 := by
      have h1 := (mem_unitarySU_iff hU).mp hc
      have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c) = 1 := by
        ext
        simpa using h1.1
      simpa [Fintype.card_fin] using h2
    have hndvd : ¬ 31 ∣ n := by
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hcop : Nat.Coprime n 31 :=
      Nat.coprime_comm.mp ((by norm_num : Nat.Prime 31).coprime_iff_not_dvd.mpr hndvd)
    have hgcd : orderOf c ∣ Nat.gcd n 31 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdet) (orderOf_dvd_of_pow_eq_one hc31)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hnf : ∀ α : MulAut (StatedProj (StatedSU n (p ^ f) K)), α ^ 5 = 1 →
      ∃ (m : ℕ) (A : GL (Fin n) K) (σ : K ≃+* K), ¬ 5 ∣ m ∧
        ∃ θ : StatedSU n (p ^ f) K →* StatedSU n (p ^ f) K,
          (∀ x, (θ x : GL (Fin n) K) = semilinConjGL A σ x) ∧
          ∀ x, (α ^ m) (QuotientGroup.mk x : StatedProj (StatedSU n (p ^ f) K)) =
            QuotientGroup.mk (θ x) := by
    intro α _
    let e0 := unitaryPSUEquivPrimeFormP hU n
    let eP : primeFormP hU (1 : Matrix (Fin n) (Fin n) K) ≃*
        StatedProj (StatedSU n (p ^ f) K) :=
      e0.symm.trans (unitaryPSUEquiv hU hnpos)
    let eH : gramSU hU (1 : Matrix (Fin n) (Fin n) K) ≃* StatedSU n (p ^ f) K :=
      (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hU n)).symm
    let β : MulAut (primeFormP hU (1 : Matrix (Fin n) (Fin n) K)) :=
      (MulAut.congr eP).symm α
    obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor hU hC hn3 hq β
    let σθ : MulAut (gramSU hU (1 : Matrix (Fin n) (Fin n) K)) :=
      primeFormConjSU hU (1 : Matrix (Fin n) (Fin n) K) A *
        primeFormFieldSU hU hC φ
    let θ : StatedSU n (p ^ f) K →* StatedSU n (p ^ f) K :=
      eH.toMonoidHom.comp (σθ.toMonoidHom.comp eH.symm.toMonoidHom)
    have hβmk : ∀ g : gramSU hU (1 : Matrix (Fin n) (Fin n) K),
        β (g : primeFormP hU (1 : Matrix (Fin n) (Fin n) K)) =
          ((σθ g : gramSU hU (1 : Matrix (Fin n) (Fin n) K)) :
            primeFormP hU (1 : Matrix (Fin n) (Fin n) K)) := by
      intro g
      rw [hA, MulAut.mul_apply]
      change primeFormConjAut hU (1 : Matrix (Fin n) (Fin n) K) A
        (primeFormFieldAut hU hC φ (g : primeFormP hU (1 : Matrix (Fin n) (Fin n) K))) = _
      rw [primeFormFieldAut_mk, primeFormConjAut_mk]
      rfl
    have he0 : ∀ g : gramSU hU (1 : Matrix (Fin n) (Fin n) K),
        e0.symm (g : primeFormP hU (1 : Matrix (Fin n) (Fin n) K)) =
          unitaryProj hU n (eH g) := by
      intro g
      rw [show e0 = unitaryPSUEquivPrimeFormP hU n from rfl, unitaryPSUEquivPrimeFormP,
        QuotientGroup.congr_symm, QuotientGroup.congr_mk]
      rfl
    have hePmk : ∀ g : gramSU hU (1 : Matrix (Fin n) (Fin n) K),
        eP (g : primeFormP hU (1 : Matrix (Fin n) (Fin n) K)) =
          (QuotientGroup.mk (eH g) : StatedProj (StatedSU n (p ^ f) K)) := by
      intro g
      change unitaryPSUEquiv hU hnpos
        (e0.symm (g : primeFormP hU (1 : Matrix (Fin n) (Fin n) K))) = _
      rw [he0, unitaryPSUEquiv_unitaryProj]
    have hαcongr : MulAut.congr eP β = α := (MulAut.congr eP).apply_symm_apply α
    have hαeP : ∀ y : primeFormP hU (1 : Matrix (Fin n) (Fin n) K),
        α (eP y) = eP (β y) := by
      intro y
      rw [← hαcongr, MulAut.congr_apply]
      simp
    have hθcoe : ∀ x : StatedSU n (p ^ f) K,
        (θ x : GL (Fin n) K) = semilinConjGL (A : GL (Fin n) K) φ x := by
      intro x
      have h2 : (θ x : GL (Fin n) K) =
          (σθ (eH.symm x) : GL (Fin n) K) := rfl
      have h1 : (σθ (eH.symm x) : GL (Fin n) K) =
          (A : GL (Fin n) K) * glAut φ (x : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ := rfl
      have hgl : glAut φ (x : GL (Fin n) K) =
          GeneralLinearGroup.map φ.toRingHom (x : GL (Fin n) K) := Units.ext rfl
      rw [h2, h1, hgl]
      rfl
    refine ⟨1, (A : GL (Fin n) K), φ, by norm_num, θ, hθcoe, ?_⟩
    intro x
    rw [pow_one]
    calc α (QuotientGroup.mk x : StatedProj (StatedSU n (p ^ f) K))
        = α (eP (QuotientGroup.mk (eH.symm x) :
            primeFormP hU (1 : Matrix (Fin n) (Fin n) K))) := by
          rw [hePmk, MulEquiv.apply_symm_apply]
      _ = eP (β (QuotientGroup.mk (eH.symm x) :
            primeFormP hU (1 : Matrix (Fin n) (Fin n) K))) := hαeP _
      _ = eP (QuotientGroup.mk (σθ (eH.symm x)) :
            primeFormP hU (1 : Matrix (Fin n) (Fin n) K)) := by
          rw [hβmk]
      _ = QuotientGroup.mk (eH (σθ (eH.symm x))) := hePmk _
      _ = QuotientGroup.mk (θ x) := rfl
  exact WeylFivePower.of_mulEquiv e.symm
    (weylFivePower_statedProj (ι := Fin n) (K := K) hK31 (StatedSU n (p ^ f) K) hZ
      (Or.inl (by simpa using hn)) hnf)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
