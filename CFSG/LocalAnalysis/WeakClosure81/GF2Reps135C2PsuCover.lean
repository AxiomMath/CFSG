module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSUCover
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (LieModel)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open scoped commutatorElement Pointwise

private theorem c2psucov_scalars_le_center {K : Type} [Field K] {n q : ℕ} :
    (StatedScalars (Fin n) K).subgroupOf (StatedSU n q K) ≤
      Subgroup.center ↥(StatedSU n q K) := by
  intro z hz
  have hz' : (z : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    have h1 := Subgroup.mem_subgroupOf.1 hz
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)

private theorem c2psucov_data
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L) (hirr : IsIrrOn L ⊤ ⊥) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) :
    3 ≤ n ∧ 1 ≤ f ∧ (n, 2 ^ f) ≠ (3, 2) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = (2 ^ f) ^ 2 ∧
        ∃ φ : ↥(StatedSU n (2 ^ f) K) →* ↥L, Function.Surjective φ ∧
          φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) ∧
          ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)).map φ =
            Subgroup.center ↥L := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun a b h => MulEquiv.ext (congr_fun h))
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  haveI : Group.IsPerfect ↥L := hQ.1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible hW'
      (fun U hU => hirr.2.2.2 U hU bot_le le_top)
  have hsc : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f :=
    hlie.statedClassicalModel (by decide)
  obtain ⟨⟨-, hf, hm, hq⟩, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hsc
  letI : Field K := hKfield
  haveI : Finite K := hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := f * 2) (by rw [hK, pow_mul])
  obtain ⟨φ, hφs, hφk, hφmap⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.exists_su_cover hodd hK hf hm hq e
  exact ⟨hm, hf, hq, K, hKfield, hKfin, inferInstance, hK, φ, hφs, hφk, hφmap⟩

theorem w135c2_psu_cover
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L) (hirr : IsIrrOn L ⊤ ⊥) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) :
    3 ≤ n ∧ 1 ≤ f ∧ (n, 2 ^ f) ≠ (3, 2) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = (2 ^ f) ^ 2 ∧
        ∃ φ : SU (unitaryInvolution K 2 f) n →* ↥L, Function.Surjective φ ∧
          φ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n) ∧
          Odd (Nat.card φ.ker) := by
  classical
  obtain ⟨hm, hf, hq, K, hKfield, hKfin, hKchar, hK, φ, hφs, hφk, -⟩ :=
    c2psucov_data hW hQ hirr hlie
  letI : Field K := hKfield
  haveI : Finite K := hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := hKchar
  let ψ : SU (unitaryInvolution K 2 f) n ≃* ↥(StatedSU n (2 ^ f) K) := suToStated hK n
  have hfpos : 0 < f := hf
  have hcardK : Nat.card K = 2 ^ (2 * f) := by
    rw [hK, ← pow_mul]
    congr 1
    omega
  have hoddK : Odd (Nat.card K - 1) := by
    rw [hcardK]
    obtain ⟨k, hk⟩ : ∃ k, 2 * f = k + 1 := ⟨2 * f - 1, by omega⟩
    rw [hk, pow_succ]
    refine ⟨2 ^ k - 1, ?_⟩
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
    omega
  have hdvdScal : Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) ∣
      Nat.card K - 1 :=
    CFSG.Quasithin.Vol2.Ch11.SecA.card_scalars_subgroupOf_dvd _
  have hoddker : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat hoddK ((Subgroup.card_dvd_of_le hφk).trans hdvdScal)
  have hker : (φ.comp ψ.toMonoidHom).ker = φ.ker.map ψ.symm.toMonoidHom := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨ψ x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  refine ⟨hm, hf, hq, K, hKfield, hKfin, hKchar, hK, φ.comp ψ.toMonoidHom,
    hφs.comp ψ.surjective, ?_, ?_⟩
  · intro x hx
    have hx1 : φ (ψ x) = 1 := hx
    have hz : ψ x ∈ Subgroup.center ↥(StatedSU n (2 ^ f) K) :=
      c2psucov_scalars_le_center (hφk hx1)
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hz (ψ g)
  · rw [hker, Subgroup.card_map_of_injective ψ.symm.injective]
    exact hoddker

end CFSG.LocalAnalysis.WeakClosure81
