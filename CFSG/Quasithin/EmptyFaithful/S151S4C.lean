module

public import CFSG.Quasithin.EmptyFaithful.S151S4B
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.Quasithin.S151S4

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem l2_rank_one [Finite G] {L B : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) (hB : IsSylowTwoOf B L) :
    ∃ Bor : Subgroup G, Bor ≤ L ∧ B ≤ Bor ∧ Bor ≠ L ∧
      (∀ H : Subgroup G, B ≤ H → H ≤ L → H ≤ Bor ∨ H = L) ∧
      ¬ L ≤ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hF, hfin, hchar, hcard, ⟨e⟩⟩ := exists_equiv_sl2 hL
  have hK : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  let φ : ↥L →* SL2 K := e.toMonoidHom.comp π
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerφ : ∀ x : ↥L, φ x = 1 → x ∈ CFSG.pCore 2 ↥L := by
    intro x hx
    have h1 : π x = 1 := by
      apply e.injective
      simpa [φ] using hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  let SL : Sylow 2 ↥L := CFSG.Quasithin.A4.toSylow hB
  let P : Sylow 2 (SL2 K) := SL.mapSurjective hφ
  have hPcoe : (P : Subgroup (SL2 K)) = (B.subgroupOf L).map φ := rfl
  obtain ⟨Bor', hBor'top, hPBor', hmax', hnn'⟩ := sl2_sylow_borel K hK P
  have hpc : ∀ x : ↥L, x ∈ CFSG.pCore 2 ↥L → x ∈ B.subgroupOf L := by
    intro x hx
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by assumption
    have h1 : (x : G) ∈ pCoreOf 2 L := ⟨x, hx', rfl⟩
    exact hB.pCoreOf_le h1
  refine ⟨((Bor'.comap φ).map L.subtype), Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hbL : b ∈ L := hB.1 hb
    refine ⟨⟨b, hbL⟩, ?_, rfl⟩
    apply hPBor'
    rw [hPcoe]
    exact ⟨⟨b, hbL⟩, hb, rfl⟩
  · intro h
    apply hBor'top
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨l, rfl⟩ := hφ y
    have hl : (l : G) ∈ (Bor'.comap φ).map L.subtype := by
      rw [h]
      exact l.2
    obtain ⟨x, hx, hxl⟩ := hl
    have : x = l := Subtype.ext hxl
    rw [← this]
    exact hx
  · intro H hBH hHL
    set H' : Subgroup (SL2 K) := (H.subgroupOf L).map φ with hH'
    have hPH' : (P : Subgroup (SL2 K)) ≤ H' := by
      rw [hPcoe]
      exact Subgroup.map_mono (fun x hx => hBH hx)
    rcases hmax' H' hPH' with h1 | h1
    · left
      intro x hx
      refine ⟨⟨x, hHL hx⟩, ?_, rfl⟩
      apply h1
      exact ⟨⟨x, hHL hx⟩, hx, rfl⟩
    · right
      refine le_antisymm hHL (fun l hl => ?_)
      have hmem : φ ⟨l, hl⟩ ∈ H' := h1 ▸ Subgroup.mem_top _
      obtain ⟨x, hx, hxe⟩ := hmem
      have h2 : φ (x⁻¹ * ⟨l, hl⟩) = 1 := by
        rw [map_mul, map_inv, hxe, inv_mul_cancel]
      have h3 : x⁻¹ * ⟨l, hl⟩ ∈ B.subgroupOf L := hpc _ (hkerφ _ h2)
      have h4 : x⁻¹ * ⟨l, hl⟩ ∈ H.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr (hBH (Subgroup.mem_subgroupOf.mp h3))
      have h5 : (⟨l, hl⟩ : ↥L) ∈ H.subgroupOf L := by
        have := (H.subgroupOf L).mul_mem hx h4
        simpa using this
      exact Subgroup.mem_subgroupOf.mp h5
  · intro hnorm
    apply hnn'
    rw [hPcoe]
    have : (B.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hB.1).mpr hnorm
    exact Subgroup.Normal.map inferInstance φ hφ

end CFSG.Quasithin.S151S4
