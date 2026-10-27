module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1One
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem Vertex.le_of_not_mem {H T C : Subgroup D} (hv : Vertex H T) (hTC : T ≤ C) (hCH : C ≤ H)
    {x : D} (hxC : x ∈ C) (hxT : x ∉ T) : H ≤ C := by
  have h3 := Subgroup.relIndex_mul_relIndex T C H hTC hCH
  rw [hv.index_eq] at h3
  have hdvd : T.relIndex C ∣ 3 := Dvd.intro _ h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h4 | h4
  · exact absurd (Subgroup.relIndex_eq_one.mp h4 hxC) hxT
  · rw [h4] at h3
    exact Subgroup.relIndex_eq_one.mp (by omega)

theorem GoldHyp.not_pCoreOf_right_le_left (h : GoldHyp G₁ G₂)
    (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) : ¬ pCoreOf 2 G₂ ≤ pCoreOf 2 G₁ := by
  intro hle
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₂) (pCoreOf 2 G₁) (G₁ ⊓ G₂) hle
    h.pCoreOf_left_le
  rw [h.relIndex_pCoreOf_T_left, h.relIndex_pCoreOf_T_right] at h1
  have h2 : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 1 := by omega
  exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle)

theorem IsNaturalAt.pCoreOf_ne (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂ := by
  refine h.pCoreOf_ne ?_
  have h1 := Subgroup.card_le_of_le (hn.le_pCoreOf.trans h.pCoreOf_left_le)
  rw [hn.card_eq] at h1
  omega

theorem IsNaturalAt.eq_one_or_eq_of_centralizes (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) {u : D} (hu : u ∈ V)
    (hc : ∀ q ∈ pCoreOf 2 G₂, q * u = u * q) : u = 1 ∨ u = z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hu1, huz⟩ := hcon
  obtain ⟨t, htQ₂, htQ₁⟩ : ∃ t ∈ pCoreOf 2 G₂, t ∉ pCoreOf 2 G₁ := by
    by_contra hcon
    push Not at hcon
    exact h.not_pCoreOf_right_le_left (hn.pCoreOf_ne h) (fun t ht => hcon t ht)
  have htT : t ∈ G₁ ⊓ G₂ := h.pCoreOf_right_le htQ₂
  have h1 : t * u * t⁻¹ = u * z := hn.conj_eq_mul inf_le_left htT htQ₁ hu hu1 huz
  have h2 : t * u * t⁻¹ = u := by
    rw [hc t htQ₂]; group
  have h3 : u * z = u * 1 := by rw [← h1, h2, mul_one]
  exact hn.z_ne (mul_left_cancel h3)

theorem centralizes_of_critDist_two (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) :
    ∀ y ∈ G₂, y * z * y⁻¹ = z := by
  obtain ⟨-, -, -, x, hxG₂, -, -, -, -, -, hVW, hc2, -⟩ :=
    critDist_two_structure_of_natural h hn hb
  rw [hn.inf_centralizer_eq_zpowers h] at hVW
  have hzmem : z ∈ V ⊓ conjSub x V := hVW ▸ Subgroup.mem_zpowers z
  have hxz : x⁻¹ * z * x ∈ V := mem_conjSub.mp hzmem.2
  have hzZ₂ : z ∈ centerOf (pCoreOf 2 G₂) :=
    ⟨h.centerOf_le_pCoreOf_right hn.z_mem,
      Subgroup.centralizer_le h.pCoreOf_right_le hn.z_mem.2⟩
  have hxQ : x⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) :=
    le_normalizer_pCoreOf 2 G₂ (G₂.inv_mem hxG₂)
  have hconj := conj_mem_centerOf' hxQ hzZ₂
  rw [inv_inv] at hconj
  have hcases := hn.eq_one_or_eq_of_centralizes h hxz fun q hq =>
    Subgroup.mem_centralizer_iff.mp hconj.2 q hq
  have hxz' : x⁻¹ * z * x = z := by
    rcases hcases with h1 | h1
    · exfalso
      apply hn.z_ne
      have : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      rw [this, h1]; group
    · exact h1
  have hxT : x ∉ G₁ ⊓ G₂ := by
    intro hxT
    have hN : x ∈ Subgroup.normalizer (V : Set D) := hn.reduced.2.1 hxT.1
    rw [F7.conjSub_eq_of_mem_normalizer hN, inf_idem, hn.card_eq] at hc2
    omega
  have hzx : z * x = x * z := by
    calc z * x = x * (x⁻¹ * z * x) := by group
      _ = x * z := by rw [hxz']
  let C : Subgroup D := G₂ ⊓ Subgroup.centralizer ({z} : Set D)
  have hTC : G₁ ⊓ G₂ ≤ C := fun t ht =>
    ⟨ht.2, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact (Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht).symm⟩
  have hxC : x ∈ C := ⟨hxG₂, Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hzx⟩
  have hHC : G₂ ≤ C := h.vertex_right.le_of_not_mem hTC inf_le_left hxC hxT
  intro y hy
  have hyz : z * y = y * z := Subgroup.mem_centralizer_iff.mp (hHC hy).2 z rfl
  calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [← hyz]
    _ = z := by group

theorem two_structure_of_critDist_two (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) :
    ⁅V, G₁ ⊓ G₂⁆ = Subgroup.zpowers z ∧ ⁅V, pCoreOf 2 G₂⁆ = Subgroup.zpowers z ∧
      ⁅conjClosure V G₂, pCoreOf 2 G₂⁆ = Subgroup.zpowers z ∧
      ⁅conjClosure V G₂, conjClosure V G₂⁆ = Subgroup.zpowers z :=
  labelled_two_structure h hn (centralizes_of_critDist_two h hn hb) hb

end GoldAmL

end F6

end CFSG.Quasithin
