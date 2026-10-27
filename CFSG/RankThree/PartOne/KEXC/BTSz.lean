module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
  CFSG.SignalizerFunctorTheorem.McBride.SzModel

theorem card_stabilizer_ovoid' {m : ℕ} (hm : 0 < m) (a : {p // p ∈ suzukiOvoidSet m}) :
    letI := suzukiOvoidAction m
    Nat.card (MulAction.stabilizer (SuzukiMatrixGroup m) a) =
      (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let := suzukiOvoidAction m
  have := suzuki_ovoid_two_transitive m
  have : MulAction.IsPretransitive (SuzukiMatrixGroup m) {p // p ∈ suzukiOvoidSet m} :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have h1 := (MulAction.stabilizer (SuzukiMatrixGroup m) a).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive, suzuki_ovoid_card,
    CFSG.SectionRank.card_suzukiMatrixGroup m hm] at h1
  have hpos : 0 < (2 ^ (2 * m + 1)) ^ 2 + 1 := Nat.succ_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  ring

theorem szMatrix_bt {m : ℕ} (hm : 0 < m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ (2 * m + 1) - 1) {S : Subgroup (SuzukiMatrixGroup m)} (hS : S ≠ ⊥)
    (hSp : IsPGroup 2 S) {g : SuzukiMatrixGroup m} (hg : g ^ p = 1)
    (hgN : g ∈ Subgroup.normalizer (S : Set (SuzukiMatrixGroup m))) : g = 1 := by
  by_contra hne
  obtain ⟨a, ha⟩ := exists_fixed_point_normalizer hm hS hSp
  let := suzukiOvoidAction m
  have hgstab : g ∈ MulAction.stabilizer (SuzukiMatrixGroup m) a := ha g hgN
  have hdvd := Subgroup.orderOf_dvd_natCard _ hgstab
  have hord : orderOf g = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hg hne
  rw [card_stabilizer_ovoid' hm a] at hdvd
  have hdvd' : p ∣ (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
    have h1 : orderOf (g : SuzukiMatrixGroup m) ∣ _ := hdvd
    rwa [hord] at h1
  rcases (Nat.Prime.dvd_mul hp).1 hdvd' with h | h
  · have h2 := hp.dvd_of_dvd_pow h
    have h3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
    exact hp2 h3
  · exact hpq h

theorem suzukiGroup_bt {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1) {R : Subgroup (CFSG.Blueprint.suzukiGroup a K)}
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) {g : CFSG.Blueprint.suzukiGroup a K} (hg : g ^ p = 1)
    (hgN : g ∈ Subgroup.normalizer (R : Set (CFSG.Blueprint.suzukiGroup a K))) : g = 1 := by
  let e : CFSG.Blueprint.suzukiGroup a K ≃* SuzukiMatrixGroup a :=
    ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK)).trans (szEquiv a)
  have hR' : R.map e.toMonoidHom ≠ ⊥ := by
    intro h
    exact hR ((Subgroup.map_eq_bot_iff_of_injective R e.injective).1 h)
  have hR2' : IsPGroup 2 (R.map e.toMonoidHom) := hR2.map e.toMonoidHom
  have hgN' : e g ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    have hmem : ∀ z, e z ∈ R.map e.toMonoidHom ↔ z ∈ R := fun z => by
      constructor
      · rintro ⟨w, hw, hwz⟩
        exact (e.injective hwz) ▸ hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hmem, ← map_mul, ← map_inv, ← map_mul, hmem]
    exact Subgroup.mem_normalizer_iff.1 hgN y
  have := szMatrix_bt (by omega) hp hp2 hpq hR' hR2' (by rw [← map_pow, hg, map_one]) hgN'
  exact e.injective (by rw [this, map_one])

end CFSG.RankThree.PartOne.KEXC
