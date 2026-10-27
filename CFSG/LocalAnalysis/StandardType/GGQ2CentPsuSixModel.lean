module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly TableB U63TB Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.StandardType.LineU CFSG.StandardType.Line63.H5

theorem mem_twoSub_center_iff {M : Type} [Group M] [Finite M] {L : Subgroup M} (z : L) :
    z ∈ U63TB.twoSub (Subgroup.center L) le_rfl ↔
      z ∈ Subgroup.center L ∧ ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  rw [U63TB.mem_twoSub]
  constructor
  · rintro ⟨hz, hzpow⟩
    exact ⟨hz, Nat.card L, hzpow⟩
  · rintro ⟨hz, k, hk⟩
    refine ⟨hz, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hdiv : 2 ^ j ∣ Nat.card L := hj ▸ orderOf_dvd_natCard z
    have hlt : 2 ^ j < 2 ^ Nat.card L :=
      lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos hdiv) Nat.lt_two_pow_self
    have hjl : j ≤ Nat.card L :=
      le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt)
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hj]; exact pow_dvd_pow 2 hjl)

theorem exists_quotModel_six
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hL : commutator L = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ ψ : ↥(unitarySU 2 1 K 6) →* L ⧸ U63TB.twoSub (Subgroup.center L) le_rfl,
      UnitTB.Model ψ ∧
      ∀ b : ↥Bs, ∃ (t : Fin 6 → K) (M : GL (Fin 6) K)
        (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        (M : Matrix (Fin 6) (Fin 6) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K 6)) (l : L),
          (QuotientGroup.mk l : L ⧸ U63TB.twoSub (Subgroup.center L) le_rfl) = ψ s →
          (QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN b.2⟩ l) :
            L ⧸ U63TB.twoSub (Subgroup.center L) le_rfl) = ψ (conjN M hM s) := by
  have hpos : GGTableBPosition 3 L Bs
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) θ hN :=
    tableBPosition_of_config hcfg θ hL hN h3
  have hr : 3 ^ (6 - 1) ≤ Nat.card Bs := by
    simpa using line63Q2_holds G B Bs x L D J hcfg K hK hL θ hN h3
  obtain ⟨ψ, hψ, hdiag⟩ := exists_model_quotient_six_one
    (p := 3) (K := K) hK Nat.prime_three (by norm_num) (by norm_num)
    (M := G) (L' := L) (E := Bs) (θ := θ) (hE := hN) hpos hr
    (U63TB.twoSub (Subgroup.center L) le_rfl) mem_twoSub_center_iff
  exact ⟨ψ, hψ, hdiag⟩

end CFSG.StandardType.GGQ2CentPort

end
