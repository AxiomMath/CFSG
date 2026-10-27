module

public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.LieType.BorelTits.Suzuki
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Models.BenderSuzuki
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b

public section

namespace CFSG.Quasithin.E6.E68Proof

open CFSG.Open

@[expose] def ModelOf (A : Type*) [Group A] (q k : ℕ) : Prop :=
  (k = 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧
      Nonempty (A ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))) ∨
    (k = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (A ≃* Sz a)) ∨
    (k = 3 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (A ≃* PSU3 2 f))

theorem modelOf_of_stated_psl {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S
      CFSG.Assembly.LowTwoRank.StatedLieTag.PSL 2 2 n) : ModelOf S (2 ^ n) 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact Or.inl ⟨rfl, n, hn, rfl, ⟨e.trans
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 n (by omega) hK)⟩⟩

theorem modelOf_of_stated_psu {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel S
      CFSG.Assembly.LowTwoRank.StatedLieTag.PSU 3 2 n) : ModelOf S (2 ^ n) 3 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  let e' : S ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) := e
  exact Or.inr (Or.inr ⟨rfl, n, hn, rfl, ⟨e'.trans
    (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)⟩⟩)

theorem modelOf_of_suzuki {S : Type} [Group S] {n : ℕ}
    (h : CFSG.Blueprint.SuzukiModel S 2 n) : ModelOf S (2 ^ n) 2 := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  exact Or.inr (Or.inl ⟨rfl, a, ha, rfl, ⟨e.trans
    ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))⟩⟩)

theorem ModelOf.fusionBenderBorel {A : Type*} [Group A] [Finite A] {q k : ℕ}
    (h : ModelOf A q k) : fusionBenderBorel A q k := by
  rcases h with ⟨rfl, f, hf, rfl, ⟨e⟩⟩ | ⟨rfl, a, ha, rfl, ⟨e⟩⟩ | ⟨rfl, f, hf, rfl, ⟨e⟩⟩
  · have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Finite.of_equiv A e.toEquiv
    exact (bender_psl2_borel_full f hf).map_mulEquiv e.symm
  · have : Finite (Sz a) := Finite.of_equiv A e.toEquiv
    exact (bender_suzuki_borel_full a ha).map_mulEquiv e.symm
  · have : Finite (PSU3 2 f) := Finite.of_equiv A e.toEquiv
    exact (bender_psu3_borel_full f hf).map_mulEquiv e.symm

theorem ModelOf.params {A : Type*} [Group A] {q k : ℕ} (h : ModelOf A q k) :
    4 ≤ q ∧ 4 ∣ q ∧ 1 ≤ k ∧ k ≤ 3 := by
  have key : ∀ m : ℕ, 2 ≤ m → 4 ≤ 2 ^ m ∧ 4 ∣ 2 ^ m := fun m hm =>
    ⟨by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm,
      by simpa using Nat.pow_dvd_pow 2 hm⟩
  rcases h with ⟨rfl, f, hf, rfl, -⟩ | ⟨rfl, a, ha, rfl, -⟩ | ⟨rfl, f, hf, rfl, -⟩
  · exact ⟨(key f hf).1, (key f hf).2, le_rfl, by norm_num⟩
  · exact ⟨(key _ (by omega)).1, (key _ (by omega)).2, by norm_num, by norm_num⟩
  · exact ⟨(key f hf).1, (key f hf).2, by norm_num, le_rfl⟩

theorem ModelOf.sz {A : Type*} [Group A] {q : ℕ} (h : ModelOf A q 2) :
    ∃ a : ℕ, 1 ≤ a ∧ Nonempty (A ≃* Sz a) := by
  rcases h with ⟨h1, -⟩ | ⟨-, a, ha, -, he⟩ | ⟨h3, -⟩
  · omega
  · exact ⟨a, ha, he⟩
  · omega

theorem ModelOf.psu {A : Type*} [Group A] {q : ℕ} (h : ModelOf A q 3) :
    ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (A ≃* PSU3 2 f) := by
  rcases h with ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨-, f, hf, hq, he⟩
  · omega
  · omega
  · exact ⟨f, hf, hq, he⟩

theorem ModelOf.isBenderGroup {A : Type*} [Group A] {q k : ℕ} (h : ModelOf A q k) :
    CFSG.BenderSuzuki.IsBenderGroup A := by
  rcases h with ⟨rfl, f, hf, rfl, ⟨e⟩⟩ | ⟨rfl, a, ha, rfl, ⟨e⟩⟩ | ⟨rfl, f, hf, rfl, ⟨e⟩⟩
  · exact .isPSL2 f hf e
  · have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
    exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    exact .isPSU3 f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))

theorem ModelOf.nonempty_mulEquiv {A B : Type*} [Group A] [Group B] {q k : ℕ}
    (hA : ModelOf A q k) (hB : ModelOf B q k) : Nonempty (A ≃* B) := by
  rcases hA with ⟨hk, f, hf, hq, ⟨e⟩⟩ | ⟨hk, a, ha, hq, ⟨e⟩⟩ | ⟨hk, f, hf, hq, ⟨e⟩⟩ <;>
    rcases hB with ⟨hk', f', hf', hq', ⟨e'⟩⟩ | ⟨hk', a', ha', hq', ⟨e'⟩⟩ |
      ⟨hk', f', hf', hq', ⟨e'⟩⟩
  · obtain rfl : f = f' := Nat.pow_right_injective le_rfl (hq.symm.trans hq')
    exact ⟨e.trans e'.symm⟩
  · omega
  · omega
  · omega
  · have h := Nat.pow_right_injective (le_refl 2) (hq.symm.trans hq')
    obtain rfl : a = a' := by omega
    exact ⟨e.trans e'.symm⟩
  · omega
  · omega
  · omega
  · obtain rfl : f = f' := Nat.pow_right_injective le_rfl (hq.symm.trans hq')
    exact ⟨e.trans e'.symm⟩

end CFSG.Quasithin.E6.E68Proof
