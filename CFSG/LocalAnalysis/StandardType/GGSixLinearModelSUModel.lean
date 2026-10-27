module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUTriple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace SUModel

variable {G : Type} [Group G]

theorem torusModel_of_su [Finite G] {p m f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmp : m + 1 = p)
    (hpq : p ∣ 2 ^ (f + 1) + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1) →* G}
    (hker : ψ.ker ≤
      Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBsM : Bs ≤ Subgroup.normalizer (ψ.range : Set G)) (hBsE : IsElemAbelian p Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum
      (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) (m + 1)) ψ b)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hU : GGBstarUniqueIn p (Subgroup.normalizer (ψ.range : Set G)) Bs)
    (hNBs : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ψ.range : Set G))
    (hfield : p ∣ f + 1 → ∀ y ∈ Subgroup.normalizer (ψ.range : Set G), y ^ p = 1 →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))),
        (y, A) ∈ UFusion.suInducedPairs ψ)
    (hyex : ∃ y ∈ Subgroup.normalizer (ψ.range : Set G), orderOf y = p ∧
      ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), g⁻¹ * y * g ∉ Bs) :
    (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Bs : Set G) → IsPGroup p Q →
      IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
        Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G))) ∧
    ∀ z ∈ Subgroup.normalizer (Bs : Set G), z ∉ Subgroup.centralizer (Bs : Set G) →
      z ^ p = 1 → ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs ψ.range (f + 1) z v := by
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hn : 3 ≤ m + 1 := by omega
  have hq : ¬(m + 1 = 3 ∧ 2 ^ (f + 1) = 2) := fun h' => by omega
  have hnq : (m + 1, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : m + 1 = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P, hP, hBsD, -⟩ := UnitModel.exists_frame_of_su hp hp5 hmp hpq hker hC hBsM hBsE hBsI hU
  set φ := SURep.ggFrameU hF ψ P hP with hφ
  have hφr : φ.range = ψ.range := SURep.range_ggFrameU hF ψ P hP
  have hcent : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hφr]; exact hC
  have hkerφ : SURep.GGFrameKer φ := SURep.ggFrameKer_ggFrameU hF ψ P hP (by omega) hnq hker
  have hkerφ' : φ.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) (m + 1)) :=
    SURep.ker_ggFrameU_le hF ψ P hP hker
  have hBs : UnitModel.frameTorus p h φ = Bs := frameTorus_eq h hn hkerφ hcent hBsD hBsE.2 hom
  obtain ⟨y, hyM, hyo, hy⟩ := hyex
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨A, hAJ, hAc⟩ : ∃ A : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))),
      (y, A) ∈ UFusion.suInducedPairs ψ := by
    by_cases hpf : p ∣ f + 1
    · exact hfield hpf y hyM hyp
    · have hσ : ∀ φ' : GaloisField 2 (2 * (f + 1)) ≃+* GaloisField 2 (2 * (f + 1)),
          φ' ^ p = 1 → φ' = 1 := fun φ' h' =>
        LinModel.eq_one_of_pow_eq_one_of_not_dvd (by omega) hp (fun hd => hpf
          ((Nat.Coprime.dvd_of_dvd_mul_left
            ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) hd))) h'
      exact UnitModel.exists_mem_suInducedPairs_of_pow_eq_one h (by omega) hker hC hσ hyM hyp
  have hY : (y, P * A * P⁻¹) ∈ SUTorus.suPairs φ :=
    SUTorus.mem_suPairs_transfer P hP
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF (m + 1)) hAJ hAc
  have hYU : P * A * P⁻¹ ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1)) :=
    SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP hAJ)
  have hdet : ¬ ∃ c : (GaloisField 2 (2 * (f + 1)))ˣ,
      c ^ p = GeneralLinearGroup.det (P * A * P⁻¹) := by
    intro hd
    obtain ⟨s, hs⟩ := exists_conj_mem_frameTorus_of_det h hp hp2 hpq hmp hnq hkerφ' hyp hYU hY hd
    have hsM : φ s ∈ Subgroup.normalizer (ψ.range : Set G) := by
      rw [← hφr]
      exact Subgroup.le_normalizer ⟨s, rfl⟩
    exact hy _ hsM (by rw [← hBs]; exact hs)
  have hreal := fun B (hB : B ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1))) =>
    exists_mem_suPairs_of_det h hp hp2 hpq hmp hYU hY hdet hB
  obtain ⟨ω, hωo, hωN⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h hp hpq
  have hω : IsPrimitiveRoot ω p := IsPrimitiveRoot.iff_orderOf.mpr hωo
  have hω1 : ω ≠ 1 := hω.ne_one hp.one_lt
  have hωN' : ((ω : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
      (2 ^ (f + 1) + 1) = 1 := by rw [← Units.val_pow_eq_pow_val, hωN, Units.val_one]
  have hreal1 : ∀ l : Fin (m + 1), ∃ g : G, SURep.GGFrameActs φ g (Pi.mulSingle l ω) := by
    intro l
    have hτN : ∀ i, (((Pi.mulSingle l ω : Fin (m + 1) → (GaloisField 2 (2 * (f + 1)))ˣ) i :
        (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^ (2 ^ (f + 1) + 1) = 1 := by
      intro i
      by_cases hi : i = l
      · rw [hi, Pi.mulSingle_eq_same, hωN']
      · rw [Pi.mulSingle_eq_of_ne hi, Units.val_one, one_pow]
    have hU' : diagHom (m + 1) (Pi.mulSingle l ω) ∈
        primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1)) := by
      rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
      exact CFSG.RankThree.Classical2.diagHom_unitary h hτN
    obtain ⟨g, hg⟩ := hreal _ hU'
    exact ⟨g, hτN, fun s s' hs' => hg.2 s s' hs'⟩
  have hmat : ∀ u ∈ Subgroup.normalizer (Bs : Set G), (∃ k, u ^ (p ^ k) = 1) →
      ∃ A : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))),
        A ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) (m + 1)) ∧
        (u, A) ∈ SUTorus.suPairs φ := by
    rintro u hu ⟨k, hk⟩
    have huN : u ∈ Subgroup.normalizer (φ.range : Set G) := by
      rw [hφr]
      exact hNBs hu
    exact exists_mem_suPairs_of_pow_pow_eq_one h hn hq hkerφ' hcent hp hpq hreal hBs hom huN hk
  have hmono : ∀ u ∈ Subgroup.normalizer (Bs : Set G),
      ∀ A : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))), (u, A) ∈ SUTorus.suPairs φ → ∃ π,
        LinModel.IsPermOf (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 (2 * (f + 1))))
          π :=
    fun u hu A hA => LinModel.exists_isPermOf fun i l l' hl hl' =>
      eq_of_ne_zero_of_mem_normalizer h hn hq hkerφ' hp hpq hω1 hω.pow_eq_one hreal1 hBs hu hA
        hl hl'
  refine ⟨fun Q hQN hQp => torus_clause_one h hn hq hkerφ' hcent hp hmp hpq hω1 hω.pow_eq_one
    hreal1 hBs (fun u hu hk => (hmat u hu hk).imp fun _ hA => hA.2) Q hQN hQp, ?_⟩
  intro z hzN hzC hzp
  rw [← hφr]
  refine torusCoords_of_triple h hn hq hkerφ' hcent hp hmp hpq hkerφ hω hBs hmat hmono ?_ hzN hzC
    hzp
  rintro b - d hbd g hg ⟨L, hL, hLA⟩
  rw [hφr] at hg hL
  exact tripleValue_of_component hF h hn hnq hp hpq hker hP hω1 hωN' hbd hg hL hLA

end SUModel

end CFSG.StandardType
