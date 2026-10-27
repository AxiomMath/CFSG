module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G} {s d r : G}

omit [Finite G] in
theorem mem_normalizer_omegaOneZ_inf {g : G} (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgY : g ∈ Subgroup.normalizer (Y₁ : Set G)) :
    g ∈ Subgroup.normalizer ((omegaOneZ p Q ⊓ Y₁ : Subgroup G) : Set G) :=
  le_normalizer_inf (Subgroup.zpowers_le.mpr (normalizer_le_normalizer_omegaOneZ p Q hgQ))
    (Subgroup.zpowers_le.mpr hgY) (Subgroup.mem_zpowers g)

theorem Sec17Data.zpowers_conj_s (h415 : Sec4.Item4_15) (h1721 : Item1721)
    (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r) :
    s ∈ Subgroup.normalizer (L : Set G) ∧
      Subgroup.zpowers (s * d * s⁻¹) = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨hdA, hdL⟩ := Subgroup.mem_inf.mp h.d_mem
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_mem hwL h.orderOf_w
  have hsH : s ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (s * c * s⁻¹) = _
    rw [h.s_inverts_c, Subgroup.zpowers_inv]
  have hsL : s ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L hsH
  refine ⟨hsL, ?_⟩
  have hsd : s * d * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsL d).mp hdL
  have hsdA : s * d * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp h.s_mem_W d).mp hdA
  obtain ⟨hdL', S₀, hdS₀, hS₀d⟩ := h.d_threeCentral
  have hc₁ := Item134SylowBarProof.central_conj hsL hdL' ⟨S₀, hdS₀, hS₀d⟩ hsd
  have hsd1 : s * d * s⁻¹ ≠ 1 := fun h1 => h.d_ne_one (conj_eq_one_iff.mp h1)
  exact Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ h.isE27.isPGroup hsdA hdA
    hsd hdL' hsd1 h.d_ne_one hc₁ ⟨S₀, hdS₀, hS₀d⟩

end CFSG.RankThree.PartTwo.Sec17
