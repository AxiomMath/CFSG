module

public import CFSG.Quasithin.Background.SzQFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LieType.BorelTits.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.Quasithin.SzQ

open CFSG.Open

theorem le_normalizer_of_pCoreOf_ne_bot {K : Type*} [Group K] [Finite K] (S : Sylow 2 K)
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((S : Subgroup K) : Set K)))
    {A : Subgroup K} (hSA : (S : Subgroup K) ≤ A) (hR : CFSG.Open.pCoreOf 2 A ≠ ⊥) :
    A ≤ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((S : Subgroup K) : Set K) with hN
  set R := CFSG.Open.pCoreOf 2 A with hRdef
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A
  have hAR : A ≤ Subgroup.normalizer (R : Set K) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A
  have hRS : R ≤ (S : Subgroup K) := by
    have hsup : IsPGroup 2 ((S : Subgroup K) ⊔ R : Subgroup K) :=
      S.isPGroup'.to_sup_of_normal_right' hRp (hSA.trans hAR)
    have hmax := S.is_maximal' hsup le_sup_left
    exact le_sup_right.trans hmax.le
  have hRN : R ≤ N := hRS.trans Subgroup.le_normalizer
  intro a ha
  by_contra haN
  have hodd := hSE.2.2 a haN
  have hle : R ≤ N ⊓ N.map (MulAut.conj a⁻¹).toMonoidHom := by
    intro r hr
    refine ⟨hRN hr, Subgroup.mem_map.mpr ⟨a * r * a⁻¹, hRN ?_, ?_⟩⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAR ha) r).mp hr
    · simp [mul_assoc]
  have hnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  obtain ⟨m, hm, hcard⟩ := hRp.nontrivial_iff_card.mp hnt
  have hdvd : 2 ∣ Nat.card ↥(N ⊓ N.map (MulAut.conj a⁻¹).toMonoidHom) :=
    (dvd_pow_self 2 hm.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hle)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

private theorem sz_eq_suzukiMatrixGroup (n : ℕ) :
    Sz n = CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n :=
  (show CFSG.Theory.Comparator.SzModel n = Sz n by
      simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, Sz,
        SzGenerators]).symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n)

theorem le_normalizer_of_solvable {K : Type} [Group K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (e : K ≃* ↥(Sz n)) (S : Sylow 2 K) {A : Subgroup K}
    (hSA : (S : Subgroup K) ≤ A) (hA : Group.IsSolvable ↥A) :
    A ≤ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  have hB : fusionBenderBorel K (2 ^ (2 * n + 1)) 2 :=
    (bender_suzuki_borel_full n hn).map_mulEquiv e.symm
  obtain ⟨hSE, -, -, hZ, hS⟩ := hB S
  have hnc : ¬ IsMulCommutative ↥(S : Subgroup K) := by
    intro hc
    have htop : Subgroup.center ↥(S : Subgroup K) = ⊤ := Subgroup.center_eq_top_iff.mpr hc
    rw [htop, Subgroup.card_top, hS] at hZ
    have hq : 2 ≤ 2 ^ (2 * n + 1) :=
      Nat.le_self_pow (Nat.succ_ne_zero _) 2
    nlinarith
  have hcyc : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ R : Sylow r K, IsCyclic ↥(R : Subgroup K) := by
    intro r _ hr R
    exact CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv
      (e.trans (MulEquiv.subgroupCongr (sz_eq_suzukiMatrixGroup n))) r hr R
  exact le_normalizer_of_pCoreOf_ne_bot S hSE hSA
    (pCoreOf_two_ne_bot_of_solvable_of_nonabelian_sylow hcyc S hnc hSA hA)

theorem le_normalizer_of_solvable_ambient {Q : Type} [Group Q]
    [Finite Q] {L S A : Subgroup Q} {n : ℕ} (hn : 1 ≤ n) (e : ↥L ≃* ↥(Sz n))
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S L) (hSA : S ≤ A) (hAL : A ≤ L)
    (hA : Group.IsSolvable ↥A) : A ≤ Subgroup.normalizer (S : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 ↥(S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let S₁ : Sylow 2 ↥L := hpg.toSylow hS.2.2
  have hS₁ : (S₁ : Subgroup ↥L) = S.subgroupOf L := rfl
  have hSA₁ : (S₁ : Subgroup ↥L) ≤ A.subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hSA (Subgroup.mem_subgroupOf.mp (hS₁ ▸ hx)))
  have hA₁ : Group.IsSolvable ↥(A.subgroupOf L) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hAL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAL).symm.surjective
  have hmain := le_normalizer_of_solvable hn e S₁ hSA₁ hA₁
  have hNeq : Subgroup.normalizer ((S₁ : Subgroup ↥L) : Set ↥L) =
      (Subgroup.normalizer (S : Set Q)).comap L.subtype := by
    rw [hS₁]
    exact (Subgroup.comap_normalizer_eq_of_le_range (f := L.subtype)
      (by rw [Subgroup.range_subtype]; exact hS.1)).symm
  intro a ha
  have h1 : (⟨a, hAL ha⟩ : ↥L) ∈ A.subgroupOf L := Subgroup.mem_subgroupOf.mpr ha
  have h2 := hmain h1
  rw [hNeq] at h2
  exact h2

end CFSG.Quasithin.SzQ
