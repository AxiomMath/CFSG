module

public import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofNotHJ
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Late.Transitivity
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] def KS1424Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X →
    ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
    ∀ H : Subgroup X, H ≤ Subgroup.normalizer (R : Set X) →
    ∀ (n : ℕ), 4 ≤ n → ∀ (T : Type) [Group T], Sec4.IsoLThreePi T 2 n →
      ∀ φ : ↥H →* T, ¬ Function.Surjective φ

namespace Proof1424Steps

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_of_isoLThreePi_two {T : Type} [Group T] {n : ℕ} (hn : 2 ≤ n)
    (h : Sec4.IsoLThreePi T 2 n) : IsSimpleGroup T := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 n)
    exact φ.isSimpleGroup
  · have hq : 2 ^ n ≠ 2 := by
      intro h2
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 n (by omega) hq
    exact φ.isSimpleGroup

theorem exists_surjective_of_ctx {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) {T : Type} [Group T]
    {f : ↥(A ⊔ Y) →* Multiplicative (ZMod 3) × T} (hTiso : Sec4.IsoLThreePi T 2 n)
    (hfs : Function.Surjective f) (hker : f.ker = kerAO2 A Y) :
    ∃ φ : ↥((Y ⊓ L).subgroupOf L) →* T, Function.Surjective φ := by
  have hD := hctx.std.toSec13Data
  have hn4 := hctx.four_le
  have : IsSimpleGroup T := isSimpleGroup_of_isoLThreePi_two (by omega) hTiso
  set g : ↥(A ⊔ Y) →* T := (MonoidHom.snd (Multiplicative (ZMod 3)) T).comp f with hg
  have hgs : Function.Surjective g := fun t => by
    obtain ⟨γ, hγ⟩ := hfs (1, t)
    exact ⟨γ, by rw [hg, MonoidHom.comp_apply, hγ]; rfl⟩
  set W := (Y.subgroupOf (A ⊔ Y)).map g with hW
  have hYn : (Y.subgroupOf (A ⊔ Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hctx.le_normalizer Subgroup.le_normalizer)
  have hWn : W.Normal := hYn.map g hgs
  have hWtop : W = ⊤ := by
    rcases hWn.eq_bot_or_eq_top with h | h
    · exfalso
      have hYk : Y.subgroupOf (A ⊔ Y) ≤ g.ker := by
        intro y hy
        have hgy : g y ∈ W := ⟨y, hy, rfl⟩
        rw [h, Subgroup.mem_bot] at hgy
        exact hgy
      have h1 : g.ker.index = Nat.card T := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hgs, Subgroup.card_top]
      have h2 : Nat.card T ∣ 27 :=
        h1 ▸ (Subgroup.index_dvd_of_le hYk).trans
          (index_subgroupOf_dvd_twentySeven hctx.le_normalizer hD.card_eq)
      have h3 := two_pow_dvd_card_of_isoLThreePi (by omega) hTiso
      have h4 : 2 ^ 12 ∣ 2 ^ (3 * n) := Nat.pow_dvd_pow 2 (by omega)
      have h5 := (h4.trans h3).trans h2
      norm_num at h5
    · exact h
  have hYLAY : Y ⊓ L ≤ A ⊔ Y := inf_le_left.trans le_sup_right
  let ι : ↥((Y ⊓ L).subgroupOf L) →* ↥(A ⊔ Y) :=
    (L.subtype.comp ((Y ⊓ L).subgroupOf L).subtype).codRestrict (A ⊔ Y)
      fun h => hYLAY (Subgroup.mem_subgroupOf.mp h.2)
  refine ⟨g.comp ι, fun t => ?_⟩
  have htW : t ∈ W := hWtop ▸ Subgroup.mem_top t
  have hWL : W = ((Y ⊓ L).subgroupOf (A ⊔ Y)).map g := by
    rw [hW, hg, ← Subgroup.map_map, ← Subgroup.map_map, map_inf_eq_map hctx.eq_sup hker]
  rw [hWL] at htW
  obtain ⟨γ, hγ, rfl⟩ := htW
  have hγL : (γ : G) ∈ L := (Subgroup.mem_subgroupOf.mp hγ).2
  refine ⟨⟨⟨γ, hγL⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hγ)⟩, ?_⟩
  rw [MonoidHom.comp_apply]
  congr 1

theorem isLThreePi_of_ctx {A L Y : Subgroup G} {c : G} {n : ℕ} (hctx : Ctx1424 G A c L Y n)
    (h12 : 2 ^ 12 ∣ Nat.card L) : IsLThreePi ↥L := by
  have hD := hctx.std.toSec13Data
  have hθ := aschbacherSolvableCore_eq_bot hctx
  let e : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot
  rcases (hctx.std.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1 with
      hJ | ⟨p, k, hp, hk, hiso⟩ | hA7 | hM22 | hM12
  · obtain ⟨φ⟩ := hJ
    rw [Nat.card_congr (e.symm.trans φ).toEquiv, KFacts.KS14.card_nativeJ2] at h12
    norm_num at h12
  · refine ⟨p, k, hp, hk, ?_⟩
    rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact Or.inl ⟨hq, ⟨e.symm.trans φ⟩⟩
    · exact Or.inr ⟨hq, ⟨e.symm.trans φ⟩⟩
  · obtain ⟨φ⟩ := hA7
    rw [Nat.card_congr (e.symm.trans φ).toEquiv,
      KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at h12
    norm_num [Nat.factorial] at h12
  · obtain ⟨φ⟩ := hM22
    rw [Nat.card_congr (e.symm.trans φ).toEquiv, KFacts.KS14.card_nativeM22] at h12
    norm_num at h12
  · obtain ⟨φ⟩ := hM12
    rw [Nat.card_congr (e.symm.trans φ).toEquiv, KFacts.KS14.card_nativeM12] at h12
    norm_num at h12

end Proof1424Steps

open Proof1424Steps in
theorem step1424Core_of (hK : KS1424Core) : Step1424Core := by
  intro G _ _ A c L Y n hctx
  by_contra hne
  obtain ⟨T, _, f, hTiso, hfs, hker⟩ := exists_quotMap hctx
  obtain ⟨φ, hφ⟩ := exists_surjective_of_ctx hctx hTiso hfs hker
  have h12 : 2 ^ 12 ∣ Nat.card L := by
    have h1 := two_pow_dvd_card_of_isoLThreePi (by have := hctx.four_le; omega) hTiso
    have h2 : 2 ^ 12 ∣ 2 ^ (3 * n) := Nat.pow_dvd_pow 2 (by have := hctx.four_le; omega)
    have h3 : Nat.card T ∣ Nat.card ↥((Y ⊓ L).subgroupOf L) :=
      Subgroup.card_dvd_of_surjective hφ
    have h4 : Nat.card ↥((Y ⊓ L).subgroupOf L) ∣ Nat.card L := Subgroup.card_subgroup_dvd_card _
    exact ((h2.trans h1).trans h3).trans h4
  have hL3 := isLThreePi_of_ctx hctx h12
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hR1 : (P ⊓ L).subgroupOf L ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : P ⊓ L ≤ L), h, Subgroup.map_bot]
  have hR2 : IsPGroup 2 ((P ⊓ L).subgroupOf L) := (hP2.to_le inf_le_left).comap_subtype
  have hHR : (Y ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((P ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    have hYLN : Y ⊓ L ≤ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
      Late.le_normalizer_inf (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
        (inf_le_right.trans Subgroup.le_normalizer)
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hYLN (Subgroup.mem_subgroupOf.mp hh)) (x : G)
  exact hK ↥L hL3 _ hR1 hR2 _ hHR n hctx.four_le T hTiso φ hφ

end CFSG.RankThree.PartTwo.Sec15
