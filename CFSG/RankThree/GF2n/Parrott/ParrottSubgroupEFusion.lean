module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ElemAbelianClosure
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup

variable {K : Type} [Group K] [Finite K] {w : K}

omit [Finite K] in
private theorem H_commute_w {y : K} (hy : y ∈ H w) : y * w = w * y :=
  Subgroup.mem_centralizer_singleton_iff.mp hy

omit [Finite K] in
private theorem mem_conjugate_iff'' {S : Subgroup K} {g x : K} :
    x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ S
    rw [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
    exact hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group⟩

omit [Finite K] in
private theorem exists_isSylowOf_ge'' {p : ℕ} {L P : Subgroup K} (hPL : P ≤ L)
    (hP : IsPGroup p P) : ∃ R : Subgroup K, IsSylowOf p R L ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := L)).exists_le_sylow
  exact ⟨(Q : Subgroup L).map L.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩⟩

theorem hfus_of_isConj_mem {E : Subgroup K} (hEH : E ≤ H w) (hE2 : IsElemAbelian 2 E)
    (hweak : ∀ T : Subgroup K, IsSylowOf 2 T (H w) → E ≤ T →
      ∀ g : K, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    (hy : ∃ y ∈ E, y ≠ w ∧ IsConj w y) :
    ∃ e ∈ E, e ≠ w ∧ ∃ n ∈ Subgroup.normalizer (E : Set K), n * w * n⁻¹ = e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyE, hyw, hc⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hE₁H : CFSG.conjugate E g ≤ H w := by
    intro x hx
    rw [mem_conjugate_iff''] at hx
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hE2.comm hx hyE
    rw [← hg] at h1
    calc x * w = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = w * x := by group
  obtain ⟨T, hT, hET⟩ := exists_isSylowOf_ge'' hEH hE2.isPGroup
  have hE₁p : IsPGroup 2 (CFSG.conjugate E g) := (hE2.map (MulAut.conj g⁻¹).toMonoidHom).isPGroup
  obtain ⟨T₁, hT₁, hE₁T₁⟩ := exists_isSylowOf_ge'' hE₁H hE₁p
  obtain ⟨k, hkH, hk⟩ := hT₁.exists_mem_conj hT
  have hle : CFSG.conjugate E (g * k⁻¹) ≤ T := by
    intro x hx
    rw [mem_conjugate_iff''] at hx
    refine (hk x).mpr (hE₁T₁ ?_)
    rw [mem_conjugate_iff'']
    have : g * (k⁻¹ * x * k) * g⁻¹ = (g * k⁻¹) * x * (g * k⁻¹)⁻¹ := by group
    rw [this]
    exact hx
  have heq := hweak T hT hET (g * k⁻¹) hle
  have hn : g * k⁻¹ ∈ Subgroup.normalizer (E : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff'', heq]
  refine ⟨y, hyE, hyw, g * k⁻¹, hn, ?_⟩
  have hkw : k⁻¹ * w * k = w := by
    have := H_commute_w (inv_mem hkH)
    calc k⁻¹ * w * k = (w * k⁻¹) * k := by rw [← this]
      _ = w := by group
  rw [← hg]
  calc g * k⁻¹ * w * (g * k⁻¹)⁻¹ = g * (k⁻¹ * w * k) * g⁻¹ := by group
    _ = g * w * g⁻¹ := by rw [hkw]

theorem hgen_of_hfus (hw : orderOf w = 2) {E : Subgroup K} (hEH : E ≤ H w) (hwE : w ∈ E)
    (hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    (hgen1 : ∀ e ∈ E, e ∉ J w →
      Subgroup.closure ({w} ∪ {y : K | ∃ n ∈ Subgroup.normalizer (E : Set K) ⊓ H w,
        y = n * e * n⁻¹}) = E)
    (hfus : ∃ e ∈ E, e ≠ w ∧ ∃ n ∈ Subgroup.normalizer (E : Set K), n * w * n⁻¹ = e) :
    ∀ x ∈ E, x ∈ Subgroup.closure
      {y : K | ∃ n ∈ Subgroup.normalizer (E : Set K), y = n * w * n⁻¹} := by
  obtain ⟨e, heE, hew, n₀, hn₀, hne⟩ := hfus
  have hw1 : w ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hw
    exact absurd hw (by decide)
  have heJ : e ∉ J w := by
    intro heJ
    have hc : IsConj w e := isConj_iff.mpr ⟨n₀, hne⟩
    refine hJ e heJ (fun hmem => ?_) hc
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hw).mp hmem with h1 | h1
    · apply hw1
      have h2 : n₀ * w * n₀⁻¹ = 1 := hne.trans h1
      calc w = n₀⁻¹ * (n₀ * w * n₀⁻¹) * n₀ := by group
        _ = 1 := by rw [h2]; group
    · exact hew h1
  intro x hx
  rw [← hgen1 e heE heJ] at hx
  refine (Subgroup.closure_le _ |>.mpr ?_) hx
  rintro y (hy | ⟨n, hn, rfl⟩)
  · rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.subset_closure ⟨1, one_mem _, by group⟩
  · refine Subgroup.subset_closure ⟨n * n₀, mul_mem (Subgroup.mem_inf.mp hn).1 hn₀, ?_⟩
    rw [← hne]
    group

end CFSG.RankThree.GF2n.Parrott
