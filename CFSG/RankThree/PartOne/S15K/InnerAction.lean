module

public import CFSG.RankThree.PartOne.S15K.LinAutRank
public import CFSG.RankThree.PartOne.S15K.NormAct
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem actP_mem_range_conjAut [Finite G] {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {ℓ m : ℕ} (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {I E : Subgroup G} (φ : ↥I ≃* projectiveSL n K) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hWI : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (I : Set G))
    (hEexp : ∀ e ∈ E, e ^ p = 1) (hEcard : p < Nat.card E) (hirr : torusIrreducible E) :
    ∀ e : E, actP φ ⟨(e : G), hEI e.2⟩ ∈ (conjAut n K).range := by
  classical
  have hN : (conjAut n K).range.Normal := conjAut_range_normal hn
  let ρ : ↥E →* MulAut (projectiveSL n K) := (actP φ).comp (Subgroup.inclusion hEI)
  let E0 : Subgroup ↥E := (conjAut n K).range.comap ρ
  have hE0inv : torusInvariant E ⊤ (E0.map E.subtype) := by
    intro w hw b hb
    obtain ⟨b', hb', rfl⟩ := hb
    have hwW : w ∈ Subgroup.normalizer (E : Set G) := hw.2
    have hmem : w * (b' : G) * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hwW (b' : G)).1 b'.2
    refine ⟨⟨w * (b' : G) * w⁻¹, hmem⟩, ?_, rfl⟩
    have hwI : w ∈ Subgroup.normalizer (I : Set G) := hWI hwW
    have hprod : (⟨w * (b' : G) * w⁻¹, hEI hmem⟩ : ↥(Subgroup.normalizer (I : Set G))) =
        ⟨w, hwI⟩ * ⟨(b' : G), hEI b'.2⟩ * ⟨w, hwI⟩⁻¹ := Subtype.ext rfl
    show actP φ ⟨w * (b' : G) * w⁻¹, hEI hmem⟩ ∈ (conjAut n K).range
    rw [hprod, map_mul, map_mul, map_inv]
    exact hN.conj_mem _ hb' _
  have hE : ∀ e : ↥E, e ^ p = 1 := fun e => Subtype.ext (hEexp e e.2)
  rcases hirr (E0.map E.subtype) (Subgroup.map_subtype_le E0) hE0inv with hbot | htop
  · exfalso
    have hinj : ∀ e : ↥E, ρ e ∈ (conjAut n K).range → e = 1 := by
      intro e he
      have : (e : G) ∈ E0.map E.subtype := ⟨e, he, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have := card_le_of_injective_mod_pgl hn hℓ hK hp hp2 hE ρ hinj
    omega
  · intro e
    have : (e : G) ∈ E0.map E.subtype := by rw [htop]; exact e.2
    obtain ⟨e', he', he'e⟩ := this
    have : e' = e := Subtype.ext he'e
    rw [← this]
    exact he'

end CFSG.RankThree.PartOne.S15K
