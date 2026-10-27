module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FUnitary
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Center

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]


theorem uc22s2114r4f_fieldDataBody_psu_odd_of_no_large_gcd
    {D : Data G} {Ch : Choice2011 G} (hGA : GriessAllModelsStatement)
    (hSg : UC6S846.SigmaStd D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {m f : ℕ} (hm : 8 ≤ m) (hX : LieModel (BarInf L) .PSU m 2 f)
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrn : r ∣ 2 ^ c.n - 1) (hodd : Odd c.n)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hgcd : ∀ q : ℕ, q.Prime → 7 ≤ q → ¬ q ∣ Nat.gcd m (2 ^ f + 1)) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have hr2 : r ≠ 2 := by omega
  have hrq : ¬ r ∣ 2 ^ f + 1 := uc22s2114r3f_not_dvd_two_pow_add_one hodd hr hr2 hrn
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hSig : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 → p ∈ D.sig := by
    intro p hp hp2 hpf
    refine hSg.four_mem p hp hp2 ?_
    exact (uc22s2114r3u_four_le_pRank hGA hL (by omega) hX hp hp2 (fun hm5 => by omega)
      hpf).trans (CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le)
  have hrZ : ¬ r ∣ Nat.card (center (Bar2 L)) := by
    intro hdvd
    have hgen : r ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSU m 2 f).1 :=
      CFSG.LocalAnalysis.RankFourTheoremC.p_dvd_genericOrders_of_lieModel hGA hr hr5 hL.2.2
        e.symm (CFSG.Models.LieModel.of_blueprint (by decide) hX) hdvd
    have hgcdr : r ∣ Nat.gcd m (2 ^ f + 1) := by
      simpa [CFSG.Blueprint.Multiplier.genericOrders] using hgen
    exact hrq (hgcdr.trans (Nat.gcd_dvd_right _ _))
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) := by
    rw [uc22s2114r3f_card_solvableRadical hL]
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h2 | hZ
    · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
      rw [hk] at h2
      have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)
      omega
    · exact hrZ hZ
  obtain ⟨⟨p, hp, hp2, hpf, X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, hqf, A, hAcomm, hAfin, hAq, hAcyc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_psu_odd c (by omega) hX hbL hr hr5 hbr hrn hodd hin
  have hqZ : ¬ q ∣ Nat.card (center (Bar2 L)) := by
    intro hdvd
    have hgen : q ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSU m 2 f).1 :=
      CFSG.LocalAnalysis.RankFourTheoremC.p_dvd_genericOrders_of_lieModel hGA hq (by omega)
        hL.2.2 e.symm (CFSG.Models.LieModel.of_blueprint (by decide) hX) hdvd
    have hgcdq : q ∣ Nat.gcd m (2 ^ f + 1) := by
      simpa [CFSG.Blueprint.Multiplier.genericOrders] using hgen
    exact hgcd q hq hq7 hgcdq
  have hqK : ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L) := by
    rw [uc22s2114r3f_card_solvableRadical hL]
    intro h
    rcases (Nat.Prime.dvd_mul hq).1 h with h2 | hZ
    · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
      rw [hk] at h2
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2)
      omega
    · exact hqZ hZ
  exact ⟨hrK, ⟨p, hp, hp2, hSig p hp hp2 hpf, X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, hqK, A, hAcomm, hAfin, hAq, hAcyc, κ, hκ, ι, hι, hθι⟩⟩

theorem uc22s2114r4f_fieldDataBody_psu_odd_dataOfSetup4
    (hGA : GriessAllModelsStatement) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (_hMS : S.InMSigma) (_hPart : PartIAt S.M)
    {c : Ctx21 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True)}
    {L : Subgroup G} (hL : L ∈ calC (UC6.dataOfSetup4 hS hU S).M)
    {m f : ℕ} (hm : 8 ≤ m)
    (hX : LieModel (BarInf L) .PSU m 2 f)
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrn : r ∣ 2 ^ c.n - 1) (hodd : Odd c.n)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hgcd : ∀ q : ℕ, q.Prime → 7 ≤ q → ¬ q ∣ Nat.gcd m (2 ^ f + 1)) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ (UC6.dataOfSetup4 hS hU S).sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) :=
  uc22s2114r4f_fieldDataBody_psu_odd_of_no_large_gcd hGA
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) c hL hm hX hbL hr hr5 hbr hrn hodd hin hgcd

end CFSG.LocalAnalysis.UniquenessCase.UC22
