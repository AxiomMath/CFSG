module

public import CFSG.Quasithin.EmptyFaithful.S151U5
public import CFSG.Quasithin.EmptyFaithful.S151WM

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem s151u_comm_le_pCore [Finite G] (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) {d : G} (hd : d ∈ H)
    (hnd : d ∉ Subgroup.normalizer (L : Set G)) {y l : G} (hy : d⁻¹ * y * d ∈ L) (hl : l ∈ L) :
    ⁅l, y⁆ ∈ pCoreOf 2 L := by
  have hne : L ≠ L.map (MulAut.conj d).toMonoidHom := fun h =>
    hnd (A38.map_conj_eq_iff.mp h.symm)
  have h := (lemma_1_2_1_two hK hs hnab h37 hH hL (map_conj_mem_cComp hL hd) hne).1
  have hy' : y ∈ L.map (MulAut.conj d).toMonoidHom := A38.mem_map_conj.mpr hy
  exact (h (Subgroup.commutator_mem_commutator hl hy')).1

theorem s151u_mem_normalizer_of_comm [Finite G] (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {H L B : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) (hB : IsSylowTwoOf B L)
    (hN : L ⊓ Subgroup.normalizer (B : Set G) ≤ B) {a : G} (ha : a ∈ H)
    (hac : ∀ c ∈ B, ⁅a, c⁆ ∈ Subgroup.centralizer (L : Set G)) :
    a ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hna
  have hO2 : pCoreOf 2 L ≤ B := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hB
  have key : ∀ l ∈ L, ∀ b ∈ B, l * b * l⁻¹ ∈ B := by
    intro l hl b hb
    have hbL : b ∈ L := hB.1 hb
    obtain ⟨t, ht⟩ : ∃ t : G, t = ⁅a, b⁆ := ⟨_, rfl⟩
    have htc : t ∈ Subgroup.centralizer (L : Set G) := ht ▸ hac b hb
    have hteq : a * b * a⁻¹ = t * b := by
      rw [ht, commutatorElement_def]
      group
    have hy : a⁻¹ * (a * b * a⁻¹) * a ∈ L := by
      have : a⁻¹ * (a * b * a⁻¹) * a = b := by group
      rw [this]
      exact hbL
    have h1 := s151u_comm_le_pCore hK hs hnab h37 hH hL ha hna hy hl
    have hw : l * b * l⁻¹ * b⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hl hbL) (L.inv_mem hl)) (L.inv_mem hbL)
    have hwt : (l * b * l⁻¹ * b⁻¹) * t = t * (l * b * l⁻¹ * b⁻¹) :=
      Subgroup.mem_centralizer_iff.mp htc _ hw
    have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp htc l hl
    have h2 : ⁅l, a * b * a⁻¹⁆ = l * b * l⁻¹ * b⁻¹ := by
      rw [hteq, commutatorElement_def]
      calc l * (t * b) * l⁻¹ * (t * b)⁻¹ = (l * t) * b * l⁻¹ * b⁻¹ * t⁻¹ := by group
        _ = (t * l) * b * l⁻¹ * b⁻¹ * t⁻¹ := by rw [hlt]
        _ = t * (l * b * l⁻¹ * b⁻¹) * t⁻¹ := by group
        _ = (l * b * l⁻¹ * b⁻¹) * t * t⁻¹ := by rw [← hwt]
        _ = l * b * l⁻¹ * b⁻¹ := by group
    have h4 : l * b * l⁻¹ = ⁅l, a * b * a⁻¹⁆ * b := by
      rw [h2]
      group
    rw [h4]
    exact B.mul_mem (hO2 h1) hb
  have hLN : L ≤ Subgroup.normalizer (B : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key l hl x hx, fun hx => ?_⟩
    have := key l⁻¹ (L.inv_mem hl) _ hx
    simpa [mul_assoc] using this
  have hLB : L ≤ B := fun l hl => hN ⟨hl, hLN hl⟩
  have hLp : IsPGroup 2 ↥L := hB.2.1.to_le hLB
  have := hLp.isNilpotent
  exact not_isSolvable_of_mem_cComp hL inferInstance

theorem s151u_cent_le_normalizer [Finite G] (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {H L B P : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) (hB : IsSylowTwoOf B L) (hPL : P ≤ L) (hBP : B ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B)
    (hnn : ¬ P ≤ Subgroup.normalizer (B : Set G)) {d : G} (hd : d ∈ H)
    (hdc : ∀ x ∈ oPrimeResidualOf 3 P, d * x = x * d) :
    d ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hnd
  have hO2 : pCoreOf 2 L ≤ B := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hB
  have hXN : oPrimeResidualOf 3 P ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    have hxL : x ∈ L := hPL (zb_oPrime_le hx)
    have key : ∀ x ∈ oPrimeResidualOf 3 P, ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
      intro x hx b hb
      have hxL : x ∈ L := hPL (zb_oPrime_le hx)
      have hxd : d⁻¹ * x * d ∈ L := by
        have : d⁻¹ * x * d = x := by
          rw [mul_assoc, ← hdc x hx, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
        exact hxL
      have h1 := s151u_comm_le_pCore hK hs hnab h37 hH hL hd hnd hxd (hB.1 hb)
      have h2 : x * b * x⁻¹ = (⁅b, x⁆)⁻¹ * b := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact B.mul_mem (B.inv_mem (hO2 h1)) hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
    have hx' : x⁻¹ ∈ oPrimeResidualOf 3 P := Subgroup.inv_mem _ hx
    have := key x⁻¹ hx' _ hy
    simpa [mul_assoc] using this
  have hPeq : oPrimeResidualOf 3 P ⊔ B = P := zb_oPrime_sup_eq hBP hcard hB.2.1
  apply hnn
  rw [← hPeq]
  exact sup_le hXN Subgroup.le_normalizer

theorem s151u_zl2_of_type [Finite G] {S L : Subgroup G}
    (htype : IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) (hperf : ⁅L, L⁆ = L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hB : IsSylowTwoOf (S ⊓ L) L)
    (hN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → S ⊓ L ≤ H →
      Nat.card H = 3 * Nat.card (S ⊓ L : Subgroup G)) : ZL2 S L := by
  rcases htype with h3 | h6 | hg
  · exact s151u_zl2_L3 h3 hperf hSN hB hN hmax3
  · exact s151u_zl2_A6 h6 hperf hSN hB hN hmax3
  · exact s151u_zl2_G2 hg hperf hSN hB hN hmax3

theorem s151u_inf_normalizer_inf (S L : Subgroup G) :
    S ⊓ Subgroup.normalizer (L : Set G) ⊓ L = S ⊓ L := by
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩

theorem s151u_zl2_SH [Finite G]
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L)
    (htype : IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) :
    ZL2 (s1516 T Z₁ ⊓ Subgroup.normalizer (L : Set G)) L := by
  have hB : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := hc.h20.sylow
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hc.hL.comp
  obtain ⟨hN, hlat⟩ := input15122Rank2Lat_holds G L (s1516 T Z₁ ⊓ L) htype hB
  have hN' : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ s1516 T Z₁ ⊓ L := hN
  have hSHL := s151u_inf_normalizer_inf (s1516 T Z₁) L
  refine s151u_zl2_of_type htype hperf inf_le_right ?_ ?_ ?_
  · rw [hSHL]
    exact hB
  · rw [hSHL]
    exact hN'
  · rw [hSHL]
    exact s151u_hmax3_of_lat hlat

end CFSG.Quasithin
