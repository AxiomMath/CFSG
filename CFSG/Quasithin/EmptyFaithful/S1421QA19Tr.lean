module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA19

variable {G : Type} [Group G]

theorem card_oTwoQuot_dvd_card_centralizer [Finite G] {L K : Subgroup G} (hKL : K ≤ L) {z : G}
    (hz : z ∈ L) (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) :
    Nat.card (OTwoQuot K) ∣ Nat.card (Subgroup.centralizer
      ({(QuotientGroup.mk' (CFSG.pCore 2 ↥L) : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L) ⟨z, hz⟩} :
        Set (↥L ⧸ CFSG.pCore 2 ↥L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let g : ↥K →* ↥L ⧸ CFSG.pCore 2 ↥L := π.comp (Subgroup.inclusion hKL)
  let f : ↥K →* OTwoQuot K := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)
  have hker : g.ker ≤ f.ker := by
    intro x hx
    have hx' : Subgroup.inclusion hKL x ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have hnorm : ((CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hKL)).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥L)).comap _
    have hp : IsPGroup 2 ((CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hKL)) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective _
        (Subgroup.inclusion_injective hKL)
    have hle := le_pCore 2 hnorm hp
    exact (QuotientGroup.eq_one_iff _).mpr (hle hx')
  let φ : ↥K ⧸ g.ker →* OTwoQuot K := QuotientGroup.lift g.ker f hker
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk k, rfl⟩
  have h1 : Nat.card (OTwoQuot K) ∣ Nat.card (↥K ⧸ g.ker) :=
    Subgroup.card_dvd_of_surjective (f := φ) hφ
  have h2 : Nat.card (↥K ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h3 : g.range ≤ Subgroup.centralizer ({π ⟨z, hz⟩} : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (k : G) * z = z * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp (hKz k.2)
    show π (Subgroup.inclusion hKL k) * π ⟨z, hz⟩ = π ⟨z, hz⟩ * π (Subgroup.inclusion hKL k)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  exact h1.trans (h2 ▸ Subgroup.card_dvd_of_le h3)

theorem dvd_card_oTwoQuot_of_dvd_card [Finite G] {K : Subgroup G} {m : ℕ} (hm : Odd m)
    (h : m ∣ Nat.card K) : m ∣ Nat.card (OTwoQuot K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : IsPGroup 2 (CFSG.Open.pCore 2 ↥K) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hO
  have hmul : Nat.card (OTwoQuot K) * Nat.card (CFSG.Open.pCore 2 ↥K) = Nat.card K :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K)).symm
  rw [← hmul, ha] at h
  exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)).dvd_of_dvd_mul_right h

theorem two_pow_dvd_card_of_isSylowTwoOf {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsSylowTwoOf P ⊤) {e m : ℕ} (hX : Nat.card X = 2 ^ e * m) : 2 ^ e ∣ Nat.card P := by
  have hidx : ¬ 2 ∣ P.index := by
    have h := hP.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right P] at h
  have hmul : Nat.card P * P.index = Nat.card X := Subgroup.card_mul_index P
  have hcop : Nat.Coprime (2 ^ e) P.index :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  have hdvd : 2 ^ e ∣ Nat.card P * P.index := by
    rw [hmul, hX]
    exact Dvd.intro _ rfl
  exact hcop.dvd_of_dvd_mul_right hdvd

end QA19

end CFSG.Quasithin
