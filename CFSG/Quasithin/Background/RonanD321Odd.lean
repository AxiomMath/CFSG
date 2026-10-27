module

public import CFSG.Quasithin.Background.RonanD321Model
public import CFSG.Quasithin.Background.RonanD321End
public import CFSG.Quasithin.Background.RonanD321OddDihedral

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem exists_inverting_of_d321Three (h3 : D321Three Mp L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card ↥L) :
    ∃ u ∈ L, u ^ p = 1 ∧ u ≠ 1 ∧ ∃ s ∈ L, s * s = 1 ∧ s * u * s = u⁻¹ := by
  obtain ⟨n, -, K, _, _, hK, _, π₀, -, -, -, hreal⟩ := h3
  haveI : Fact p.Prime := ⟨hp⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK, Nat.cast_pow] at h
    exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (eq_zero_of_pow_eq_zero h)
  let π : ↥(StatedSL 2 K) →* ↥L := π₀
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hreal 0)
  let e : ↥(StatedSL 2 K) ≃* ↥L := MulEquiv.ofBijective π ⟨hπi, (hreal 0).1⟩
  have : Finite ↥(StatedSL 2 K) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p ((Nat.card_congr e.toEquiv) ▸ hpL)
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hg] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.one_lt.ne hg
  obtain ⟨s, hss, hsg⟩ := exists_statedSL_two_inverting g hg2
  refine ⟨((π g : ↥L) : MulAut W), (π g).2, ?_, ?_, ((π s : ↥L) : MulAut W), (π s).2, ?_, ?_⟩
  · have h1 : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  · intro h
    apply hg1
    apply hπi
    rw [map_one]
    exact Subtype.ext h
  · rw [← Subgroup.coe_mul, ← map_mul, hss, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hsg, map_inv,
      Subgroup.coe_inv]

theorem smul_eq_of_odd (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    (hle : commV L ≤ fixV (conjAutSub t L))
    (hcent : M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : MulAut W} (hyM : y ∈ M) (hyL : ∀ l ∈ L, y * l = l * y)
    (hyk : ∃ k : ℕ, y ^ (p ^ k) = 1)
    (hyp : letI := qAct hB.hD.hyp.Mp_normal;
      ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hyM⟩ : ↥M) ^ p • q = q) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hyM⟩ : ↥M) • q = q := by
  by_cases hpL : p ∣ Nat.card ↥L
  swap
  · exact smul_eq_of_pElement hB h3 hp hp2 hpL hyM hyL hyp
  by_cases hyLt : y ∈ conjAutSub t L
  · let _i := qAct hB.hD.hyp.Mp_normal
    rintro _ ⟨w, hw, rfl⟩
    change (QuotientGroup.mk (y w) : W ⧸ modFix Mp (⊤ : Subgroup W)) = QuotientGroup.mk w
    rw [(mem_fixV.1 (hle hw)) _ hyLt]
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzM, hzL, hzp, hzLt⟩ := exists_pow_eq_one_not_mem hB h3 hcent hp hyM hyL hyk hyLt
  have hzNL : z ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun l hl => (hzL l hl).symm)
  have hzN : z ∈ Subgroup.normalizer (conjAutSub t L : Set (MulAut W)) :=
    mem_normalizer_iff_conjAutSub.2 (hB.conj_Lt_of_mem_normalizer hzM hzNL)
  have hpLt : p ∣ Nat.card ↥(conjAutSub t L) := by
    rw [show Nat.card ↥(conjAutSub t L) = Nat.card ↥L from
      Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact hpL
  obtain ⟨c, hcLt, hco, hcz⟩ := exists_orderOf_eq_comm_of_mem_normalizer hzN hzp hpLt
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hco
    exact hp.one_lt.ne hco
  obtain ⟨u, huL, hu, hu1, s, hsL, hss, hsu⟩ := exists_inverting_of_d321Three h3 hp hp2 hpL
  refine false_of_dihedral_mul_elemAbelian hB.hD.hyp.qsqtk hp hp2 (hB.L_le huL) (hB.L_le hsL)
    (hB.Lt_le hcLt) hzM hu hu1 (hco ▸ pow_orderOf_eq_one c) hc1 hzp hss hsu
    (hB.comm u huL c hcLt) (hzL u huL).symm hcz (hB.comm s hsL c hcLt) (hzL s hsL).symm
    fun hzc => hzLt ?_
  exact Subgroup.zpowers_le.2 hcLt hzc

end CFSG.Quasithin.RonanD321
