module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
open CFSG.QuasithinUnique.Unc25G2.BenderBorel

variable {G : Type} [Group G]

theorem mem_image_iff {L B : Subgroup G} {K : Type} [Group K] (φ : ↥L →* K)
    (hker : ∀ x : ↥L, φ x = 1 → x ∈ B.subgroupOf L) (y : ↥L) :
    φ y ∈ (B.subgroupOf L).map φ ↔ y ∈ B.subgroupOf L := by
  refine ⟨fun ⟨b, hb, hby⟩ => ?_, fun hy => ⟨y, hy, rfl⟩⟩
  have h1 : φ (y * b⁻¹) = 1 := by rw [map_mul, map_inv, ← hby, mul_inv_cancel]
  have := (B.subgroupOf L).mul_mem (hker _ h1) hb
  simpa using this

theorem normalizer_le_of_image {L B : Subgroup G} {K : Type} [Group K] (φ : ↥L →* K)
    (hker : ∀ x : ↥L, φ x = 1 → x ∈ B.subgroupOf L)
    (hK : ∀ H' : Subgroup K, (B.subgroupOf L).map φ ≤ H' → H' ≠ ⊤ →
      H' ≤ Subgroup.normalizer (((B.subgroupOf L).map φ : Subgroup K) : Set K))
    {H : Subgroup G} (hBH : B ≤ H) (hHL : H ≤ L) (hH : H ≠ L) :
    H ≤ Subgroup.normalizer (B : Set G) := by
  set P' : Subgroup K := (B.subgroupOf L).map φ with hP'
  set H' : Subgroup K := (H.subgroupOf L).map φ with hH'
  have hPH' : P' ≤ H' := Subgroup.map_mono (fun x hx => hBH hx)
  have hne : H' ≠ ⊤ := by
    intro htop
    apply hH
    refine le_antisymm hHL (fun l hl => ?_)
    have hmem : φ ⟨l, hl⟩ ∈ H' := htop ▸ Subgroup.mem_top _
    obtain ⟨x, hx, hxe⟩ := hmem
    have h2 : φ (x⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hxe, inv_mul_cancel]
    have h3 : x⁻¹ * ⟨l, hl⟩ ∈ B.subgroupOf L := hker _ h2
    have h4 : x⁻¹ * ⟨l, hl⟩ ∈ H.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr (hBH (Subgroup.mem_subgroupOf.mp h3))
    have h5 : (⟨l, hl⟩ : ↥L) ∈ H.subgroupOf L := by
      have := (H.subgroupOf L).mul_mem hx h4
      simpa using this
    exact Subgroup.mem_subgroupOf.mp h5
  have hN := hK H' hPH' hne
  have key : ∀ x ∈ H, ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
    intro x hx b hb
    have hxL : x ∈ L := hHL hx
    have hbL : b ∈ L := (show B ≤ L from hBH.trans hHL) hb
    have hφx : φ ⟨x, hxL⟩ ∈ H' := ⟨⟨x, hxL⟩, hx, rfl⟩
    have hφb : φ ⟨b, hbL⟩ ∈ P' := ⟨⟨b, hbL⟩, hb, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.mp (hN hφx) _).mp hφb
    have hconj : φ (⟨x, hxL⟩ * ⟨b, hbL⟩ * ⟨x, hxL⟩⁻¹) ∈ P' := by
      simpa only [map_mul, map_inv] using hmem
    exact Subgroup.mem_subgroupOf.mp ((mem_image_iff φ hker _).mp hconj)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => key x hx b hb, fun hb => ?_⟩
  have := key x⁻¹ (H.inv_mem hx) _ hb
  simpa [mul_assoc] using this

theorem pCore_le_subgroupOf {L P : Subgroup G} (hP : IsSylowTwoOf P L) (x : ↥L)
    (hx : x ∈ CFSG.pCore 2 ↥L) : x ∈ P.subgroupOf L := by
  have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by assumption
  have h1 : (x : G) ∈ pCoreOf 2 L := ⟨x, hx', rfl⟩
  exact hP.pCoreOf_le h1

variable [Finite G]

theorem le_normalizer_of_overgroup {L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {H : Subgroup G} (hPH : P ≤ H)
    (hHL : H ≤ L) (hH : H ≠ L) : H ≤ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥L, π x = 1 → x ∈ P.subgroupOf L := fun x hx =>
    pCore_le_subgroupOf hP x ((QuotientGroup.eq_one_iff x).mp hx)
  let Q : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) := (CFSG.Quasithin.A4.toSylow hP).mapSurjective hπ
  have hQ : (Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = (P.subgroupOf L).map π := rfl
  refine normalizer_le_of_image π hker (fun H' hH'1 hH'2 => ?_) hPH hHL hH
  rw [← hQ] at hH'1 ⊢
  exact le_normalizer_of_bender hB Q hH'1 hH'2

theorem mem_of_centralizes {L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {x : G} (hxL : x ∈ L)
    (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hxC : ∀ p ∈ P, x * p = p * x) : x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : ↥L, π y = 1 → y ∈ P.subgroupOf L := fun y hy =>
    pCore_le_subgroupOf hP y ((QuotientGroup.eq_one_iff y).mp hy)
  let Q : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) := (CFSG.Quasithin.A4.toSylow hP).mapSurjective hπ
  have hQ : (Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = (P.subgroupOf L).map π := rfl
  obtain ⟨q, k, hq4, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hsup⟩, -, -, -⟩ := hBor Q
  have hsolvN := isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  have hxN' : π ⟨x, hxL⟩ ∈ Subgroup.normalizer
      ((Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    obtain ⟨y, rfl⟩ := hπ h
    have e : π ⟨x, hxL⟩ * π y * (π ⟨x, hxL⟩)⁻¹ = π (⟨x, hxL⟩ * y * ⟨x, hxL⟩⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e, hQ, mem_image_iff π hker, mem_image_iff π hker]
    have := Subgroup.mem_normalizer_iff.mp hxN (y : G)
    exact this
  have hxC' : ∀ q' ∈ (Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)),
      π ⟨x, hxL⟩ * q' = q' * π ⟨x, hxL⟩ := by
    intro q' hq'
    rw [hQ] at hq'
    obtain ⟨p, hp, rfl⟩ := hq'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxC p (Subgroup.mem_subgroupOf.mp hp))
  have hmem := centralizer_le_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolvN hSE.1 hxN' hxC'
  rw [hQ] at hmem
  exact Subgroup.mem_subgroupOf.mp ((mem_image_iff π hker _).mp hmem)

end CFSG.Quasithin.GoldMLA
