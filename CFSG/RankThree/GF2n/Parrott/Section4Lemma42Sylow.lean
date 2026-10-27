module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalSigma
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps
public import CFSG.RankThree.GF2n.Parrott.E27LineCount
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem normalizer_le_normalizer_inf_centralizer (T : Subgroup G) :
    normalizer (T : Set G) ≤
      normalizer ((T ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ normalizer (T : Set G), ∀ x ∈ T ⊓ centralizer (T : Set G),
      m * x * m⁻¹ ∈ T ⊓ centralizer (T : Set G) := by
    intro m hm x hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hm x).mp hxT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht' : m⁻¹ * t * m ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) t).mp ht
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC _ ht'
    calc t * (m * x * m⁻¹) = m * ((m⁻¹ * t * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * t * m)) * m⁻¹ := by rw [hcomm]
      _ = m * x * m⁻¹ * t := by group
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have h1 := key n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using h1

theorem centerIn_J_le_inf_centralizer_of_isSylowOf (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {M : Subgroup G} (hM : centerIn (J z) ≤ M)
    {T : Subgroup G} (hT : IsSylowOf 2 T (H z ⊓ M)) :
    centerIn (J z) ≤ T ⊓ centralizer (T : Set G) := by
  have hTH : T ≤ H z := hT.le.trans inf_le_left
  have hZC : centerIn (J z) ≤ H z ⊓ M := fun e he =>
    Subgroup.mem_inf.mpr ⟨J_le_H he.1, hM he⟩
  have hZT' : centerIn (J z) ≤ T := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hT hZC ?_
      (IsPGroup.of_card (n := 2) (by rw [card_centerIn_J h]; norm_num))
    intro c hc
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro e he
    have heH : e ∈ centerIn (H z) := hZ ▸ he
    exact (mem_centralizer_iff.mp heH.2 c hc.1).symm
  intro e he
  refine Subgroup.mem_inf.mpr ⟨hZT' he, ?_⟩
  rw [mem_centralizer_iff]
  intro t ht
  have heH : e ∈ centerIn (H z) := hZ ▸ he
  exact mem_centralizer_iff.mp heH.2 t (hTH ht)

omit [Finite G] in
theorem centerIn_J_le_centralizer_of_mem_H (hZ : centerIn (J z) = centerIn (H z)) {a : G}
    (haH : a ∈ H z) : centerIn (J z) ≤ centralizer ({a} : Set G) := fun e he => by
  rw [mem_centralizer_singleton_iff]
  have heH : e ∈ centerIn (H z) := hZ ▸ he
  exact (mem_centralizer_iff.mp heH.2 a haH).symm

theorem isSylowOf_centralizer_of_centre_card (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (A0 : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z)
    {y : G} (hyH : y ∈ H z) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({y} : Set G)))
    (hZT : Nat.card ↥(T ⊓ centralizer (T : Set G)) = 4 ∨
      Nat.card ↥(T ⊓ centralizer (T : Set G)) = 8) :
    IsSylowOf 2 T (centralizer ({y} : Set G)) := by
  have hTH : T ≤ H z := hT.le.trans inf_le_left
  have hZW := centerIn_J_le_inf_centralizer_of_isSylowOf h hZ
    (centerIn_J_le_centralizer_of_mem_H hZ hyH) hT
  refine isSylowOf_of_normalizer_inf_le hT ?_
  intro n hn
  have hnW := normalizer_le_normalizer_inf_centralizer T (Subgroup.mem_inf.mp hn).1
  rcases hZT with h4 | h8
  · have hWeq : centerIn (J z) = T ⊓ centralizer (T : Set G) :=
      Subgroup.eq_of_le_of_card_ge hZW (by rw [h4, card_centerIn_J h])
    exact normalizer_centerIn_J_le h hZ (hWeq ▸ hnW)
  · exact normalizer_le_H_of_card_eight h hZ
      (fun g hg hgW => A0 g hg (hTH (Subgroup.mem_inf.mp hgW).1)) h8 hZW hnW

omit [Finite G] in
private theorem conjugate_zpowers_eq (a g : G) :
    CFSG.conjugate (Subgroup.zpowers a) g = Subgroup.zpowers (g⁻¹ * a * g) := by
  rw [CFSG.conjugate, MonoidHom.map_zpowers]
  simp

private theorem conjugate_conjugate_eq (R : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate R a) b = CFSG.conjugate R (a * b) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  have : a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
  rw [this]

omit [Finite G] in
private theorem card_conjugate_eq (R : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate R g) = Nat.card R := by
  rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

omit [Finite G] in
private theorem card_centralizer_conj (a g : G) :
    Nat.card (centralizer ({g * a * g⁻¹} : Set G)) = Nat.card (centralizer ({a} : Set G)) := by
  have : centralizer ({g * a * g⁻¹} : Set G) =
      (centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx]
        _ = a * (g⁻¹ * x * g) := by group
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
        _ = g * (a * y) * g⁻¹ := by rw [hy]
        _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  rw [this, Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
private theorem centralizer_eq_of_zpowers_eq {a b : G}
    (hab : Subgroup.zpowers a = Subgroup.zpowers b) :
    centralizer ({a} : Set G) = centralizer ({b} : Set G) := by
  have key : ∀ {c d : G}, Subgroup.zpowers c = Subgroup.zpowers d →
      centralizer ({c} : Set G) ≤ centralizer ({d} : Set G) := by
    intro c d hcd x hx
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have hd : d ∈ Subgroup.zpowers c := hcd ▸ Subgroup.mem_zpowers d
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((show Commute x c from hx).zpow_right k).eq
  exact le_antisymm (key hab) (key hab.symm)

end CFSG.RankThree.GF2n.Parrott
