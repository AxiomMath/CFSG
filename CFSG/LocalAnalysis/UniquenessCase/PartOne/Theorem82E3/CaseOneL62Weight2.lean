module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Center
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Fusion
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsCore
import CFSG.GF2Type.Aschbacher1976Full.HSBurnside
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Frame
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

private def Weight1 (v : Fin 3 → ZMod 3) : Prop :=
  ∃ i, ∀ j, j ≠ i → v j = 0

private def Weight2 (v : Fin 3 → ZMod 3) : Prop :=
  ∃ i, v i = 0 ∧ ∀ j, j ≠ i → v j ≠ 0

private def Weight3 (v : Fin 3 → ZMod 3) : Prop :=
  ∀ i, v i ≠ 0

private theorem weight_trichotomy (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    Weight3 v ∨ Weight2 v ∨ Weight1 v := by
  unfold Weight3 Weight2 Weight1
  revert v
  decide +kernel

private theorem ne_zero_001 : (![0, 0, 1] : Fin 3 → ZMod 3) ≠ 0 := by decide
private theorem ne_zero_120 : (![1, 2, 0] : Fin 3 → ZMod 3) ≠ 0 := by decide
private theorem ne_zero_111 : (![1, 1, 1] : Fin 3 → ZMod 3) ≠ 0 := by decide
private theorem ne_zero_200 : (![2, 0, 0] : Fin 3 → ZMod 3) ≠ 0 := by decide
private theorem ne_zero_110 : (![1, 1, 0] : Fin 3 → ZMod 3) ≠ 0 := by decide
private theorem weight_111 : ((∀ i, (![1, 1, 1] : Fin 3 → ZMod 3) i ≠ 0) ∨
    ∃ i, ∀ j, j ≠ i → (![1, 1, 1] : Fin 3 → ZMod 3) j = 0) := by decide
private theorem weight_200 : ((∀ i, (![2, 0, 0] : Fin 3 → ZMod 3) i ≠ 0) ∨
    ∃ i, ∀ j, j ≠ i → (![2, 0, 0] : Fin 3 → ZMod 3) j = 0) := by decide
private theorem vec_111 : (![1, 1, 1] : Fin 3 → ZMod 3) = ![1, 1, 0] + ![0, 0, 1] := by decide
private theorem vec_200 : (![2, 0, 0] : Fin 3 → ZMod 3) = ![1, 1, 0] + ![1, 2, 0] := by decide

theorem normalizes_of_weight_two_of_fix (a b d : Fin 3 → ZMod 3) (hab : a + b = ![1, 1, 0])
    (hT : ∀ u : Fin 3 → ZMod 3, (∃ i, u i = 0 ∧ ∀ j, j ≠ i → u j ≠ 0) →
      ∃ i, (u 0 • a + u 1 • b + u 2 • d) i = 0 ∧ ∀ j, j ≠ i → (u 0 • a + u 1 • b + u 2 • d) j ≠ 0) :
    (d = ![0, 0, 1] ∨ d = ![0, 0, 2]) ∧ (a + 2 • b = ![1, 2, 0] ∨ a + 2 • b = ![2, 1, 0]) := by
  obtain rfl : b = ![1, 1, 0] - a := by rw [← hab]; abel
  clear hab
  revert a d
  decide +kernel

private theorem centralizer_ne_top_of_ne_bot {G : Type} [Group G]
    (hG : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G}
    (hX : X ≠ ⊥) : Subgroup.centralizer (X : Set G) ≠ ⊤ := by
  obtain ⟨a, b, hab⟩ := hnonab
  intro htop
  have hsub : X ≤ Subgroup.center G := (Subgroup.centralizer_eq_top_iff_subset).mp htop
  have hcenter : Subgroup.center G = ⊥ := by
    rcases hG.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  exact hX (eq_bot_iff.mpr (by simpa [hcenter] using hsub))

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem pt_injective : Function.Injective s.pt := fun u v huv =>
  Multiplicative.ofAdd.injective (s.ptHom_injective (by simpa [ptHom_apply] using huv))

private theorem pt_nsmul (n : ℕ) (v : Fin 3 → ZMod 3) :
    s.pt (n • v) = s.pt v ^ n := by
  induction n with
  | zero => simp [pt_zero]
  | succ n ih =>
      rw [succ_nsmul, pt_add, ih, pow_succ]

private theorem eq_sum_basis (u : Fin 3 → ZMod 3) :
    u = (u 0).val • (![1, 0, 0] : Fin 3 → ZMod 3) + (u 1).val • (![0, 1, 0] : Fin 3 → ZMod 3) +
      (u 2).val • (![0, 0, 1] : Fin 3 → ZMod 3) := by
  revert u
  decide +kernel

private theorem signed_e0_not_weight_two (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ¬ Weight2 (fun i => ε i * (![1, 0, 0] : Fin 3 → ZMod 3) (σ i)) := by
  unfold Weight2
  revert σ ε
  decide +kernel

private theorem not_good_of_weight_two
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0])) {v : Fin 3 → ZMod 3} (hv : v ≠ 0)
    (hz : Weight2 v) :
    ¬ GoodPoint D.M (s.pt v) := by
  unfold Weight2 at hz
  obtain ⟨σ, ε, hε, hv'⟩ := exists_perm_signs v hv ⟨hz.choose, hz.choose_spec.1⟩
  obtain ⟨g, hgN, hgconj⟩ := s.exists_conj σ ε hε
  have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
  rcases hv' with rfl | rfl
  · exact (signed_e0_not_weight_two σ ε hε hz).elim
  · intro hgv
    apply hbad
    have hgc := hgv.conj (g := (g : G)⁻¹) (D.M.inv_mem hgM)
    have h1 : (g : G)⁻¹ * s.pt (fun i => ε i * (![1, 1, 0] : Fin 3 → ZMod 3) (σ i)) *
        ((g : G)⁻¹)⁻¹ = s.pt ![1, 1, 0] := by
      rw [← hgconj]
      group
    rwa [h1] at hgc

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem weight2_ne_zero {v : Fin 3 → ZMod 3} (hv : Weight2 v) : v ≠ 0 := by
  unfold Weight2 at hv
  revert v
  decide +kernel

private theorem zmod_smul_eq_nsmul (c : ZMod 3) (v : Fin 3 → ZMod 3) :
    c • v = c.val • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

private theorem eq_sum_basis_smul (u : Fin 3 → ZMod 3) :
    u = u 0 • (![1, 0, 0] : Fin 3 → ZMod 3) + u 1 • (![0, 1, 0] : Fin 3 → ZMod 3) +
      u 2 • (![0, 0, 1] : Fin 3 → ZMod 3) := by
  revert u
  decide +kernel

private noncomputable def conjCoord {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) (u : Fin 3 → ZMod 3) :
    Fin 3 → ZMod 3 :=
  Classical.choose (s.exists_pt_of_mem
    ((Subgroup.mem_normalizer_iff.mp hnA (s.pt u)).mp (s.pt_mem_A u)))

private theorem conjCoord_spec {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) (u : Fin 3 → ZMod 3) :
    s.pt (s.conjCoord n hnA u) = (n : G) * s.pt u * (n : G)⁻¹ :=
  Classical.choose_spec (s.exists_pt_of_mem
    ((Subgroup.mem_normalizer_iff.mp hnA (s.pt u)).mp (s.pt_mem_A u)))

private theorem conjCoord_zero {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) :
    s.conjCoord n hnA 0 = 0 := by
  apply s.pt_injective
  rw [s.conjCoord_spec, s.pt_zero]
  simp

private theorem conjCoord_add {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) (u v : Fin 3 → ZMod 3) :
    s.conjCoord n hnA (u + v) = s.conjCoord n hnA u + s.conjCoord n hnA v := by
  apply s.pt_injective
  rw [s.conjCoord_spec, s.pt_add, s.pt_add, s.conjCoord_spec, s.conjCoord_spec]
  group

private theorem conjCoord_nsmul {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) (k : ℕ) (u : Fin 3 → ZMod 3) :
    s.conjCoord n hnA (k • u) = k • s.conjCoord n hnA u := by
  induction k with
  | zero => simp [s.conjCoord_zero]
  | succ k ih =>
      rw [succ_nsmul, s.conjCoord_add, ih, succ_nsmul]

private theorem conjCoord_smul {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) (c : ZMod 3) (u : Fin 3 → ZMod 3) :
    s.conjCoord n hnA (c • u) = c • s.conjCoord n hnA u := by
  rw [zmod_smul_eq_nsmul c u, zmod_smul_eq_nsmul c (s.conjCoord n hnA u), s.conjCoord_nsmul]

private theorem conjCoord_e {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G))
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    s.conjCoord n hnA ![1, 1, 0] = ![1, 1, 0] := by
  apply s.pt_injective
  rw [s.conjCoord_spec]
  have hncomm : (n : G) * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * (n : G) := hXc (n : G) n.2
  rw [hncomm]
  group

private theorem conjCoord_ne_zero {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) {u : Fin 3 → ZMod 3} (hu : u ≠ 0) :
    s.conjCoord n hnA u ≠ 0 := by
  intro h0
  apply hu
  apply s.pt_injective
  have h1 : (n : G) * s.pt u * (n : G)⁻¹ = 1 := by
    rw [← s.conjCoord_spec n hnA u, h0, s.pt_zero]
  have h2 : s.pt u = 1 := by
    calc s.pt u = (n : G)⁻¹ * ((n : G) * s.pt u * (n : G)⁻¹) * (n : G) := by group
      _ = 1 := by rw [h1]; group
  rw [h2, s.pt_zero]

private theorem conjCoord_weight2
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G} (n : ↥X) (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G))
    {u : Fin 3 → ZMod 3} (hu : Weight2 u) :
    Weight2 (s.conjCoord n hnA u) := by
  have hu0 : u ≠ 0 := weight2_ne_zero hu
  have hTune : s.conjCoord n hnA u ≠ 0 := s.conjCoord_ne_zero n hnA hu0
  have hnotgood : ¬ GoodPoint D.M (s.pt (s.conjCoord n hnA u)) := by
    intro hg
    have hg' := hg.conj (g := (n : G)⁻¹) (D.M.inv_mem (hNA hnA))
    have h1 : (n : G)⁻¹ * s.pt (s.conjCoord n hnA u) * ((n : G)⁻¹)⁻¹ = s.pt u := by
      rw [s.conjCoord_spec n hnA u]
      group
    rw [h1] at hg'
    exact (s.not_good_of_weight_two hgood hbad hu0 hu) hg'
  rcases weight_trichotomy (s.conjCoord n hnA u) hTune with h3 | h2 | h1
  · exfalso
    exact hnotgood (hgood _ hTune (Or.inl (by simpa [Weight3] using h3)))
  · exact h2
  · exfalso
    exact hnotgood (hgood _ hTune (Or.inr (by simpa [Weight1] using h1)))

private theorem conjCoord_comp {X : Subgroup G} (n : ↥X)
    (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) (u : Fin 3 → ZMod 3) :
    s.conjCoord n hnA u = u 0 • s.conjCoord n hnA ![1, 0, 0] +
      u 1 • s.conjCoord n hnA ![0, 1, 0] + u 2 • s.conjCoord n hnA ![0, 0, 1] := by
  conv_lhs => rw [eq_sum_basis_smul u]
  rw [s.conjCoord_add, s.conjCoord_add, s.conjCoord_smul, s.conjCoord_smul, s.conjCoord_smul]

private theorem conjCoord_normalizes
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G}
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x)
    {n : ↥X} (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) :
    (s.conjCoord n hnA ![0, 0, 1] = ![0, 0, 1] ∨ s.conjCoord n hnA ![0, 0, 1] = ![0, 0, 2]) ∧
    (s.conjCoord n hnA ![1, 2, 0] = ![1, 2, 0] ∨
      s.conjCoord n hnA ![1, 2, 0] = ![2, 1, 0]) := by
  classical
  have hab : s.conjCoord n hnA ![1, 0, 0] + s.conjCoord n hnA ![0, 1, 0] = ![1, 1, 0] := by
    rw [← s.conjCoord_add, show (![1, 0, 0] : Fin 3 → ZMod 3) + ![0, 1, 0] = ![1, 1, 0] by decide,
      s.conjCoord_e n hnA hXc]
  have hT' : ∀ u : Fin 3 → ZMod 3, Weight2 u →
      ∃ i, (u 0 • s.conjCoord n hnA ![1, 0, 0] + u 1 • s.conjCoord n hnA ![0, 1, 0] +
        u 2 • s.conjCoord n hnA ![0, 0, 1]) i = 0 ∧
        ∀ j, j ≠ i → (u 0 • s.conjCoord n hnA ![1, 0, 0] + u 1 • s.conjCoord n hnA ![0, 1, 0] +
          u 2 • s.conjCoord n hnA ![0, 0, 1]) j ≠ 0 := by
    intro u hu
    have h := s.conjCoord_weight2 hgood hbad hNA n hnA hu
    unfold Weight2 at h
    rw [s.conjCoord_comp n hnA u] at h
    exact h
  obtain ⟨hd, hz2⟩ := normalizes_of_weight_two_of_fix (s.conjCoord n hnA ![1, 0, 0])
    (s.conjCoord n hnA ![0, 1, 0]) (s.conjCoord n hnA ![0, 0, 1]) hab hT'
  have hTz2 : s.conjCoord n hnA ![1, 2, 0] =
      s.conjCoord n hnA ![1, 0, 0] + 2 • s.conjCoord n hnA ![0, 1, 0] := by
    rw [show (![1, 2, 0] : Fin 3 → ZMod 3) = ![1, 0, 0] + 2 • ![0, 1, 0] by decide,
      s.conjCoord_add, s.conjCoord_nsmul]
  exact ⟨hd, by rwa [← hTz2] at hz2⟩

private theorem conj_pt_of_mem_normalizer
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G}
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x)
    {n : ↥X} (hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G)) :
    ((n : G) * s.pt ![0, 0, 1] * (n : G)⁻¹ = s.pt ![0, 0, 1] ∨
      (n : G) * s.pt ![0, 0, 1] * (n : G)⁻¹ = (s.pt ![0, 0, 1]) ^ 2) ∧
    ((n : G) * s.pt ![1, 2, 0] * (n : G)⁻¹ = s.pt ![1, 2, 0] ∨
      (n : G) * s.pt ![1, 2, 0] * (n : G)⁻¹ = (s.pt ![1, 2, 0]) ^ 2) := by
  obtain ⟨hd, hz2⟩ := s.conjCoord_normalizes hgood hbad hNA hXc hnA
  have hconj1 : (n : G) * s.pt ![0, 0, 1] * (n : G)⁻¹ = s.pt ![0, 0, 1] ∨
      (n : G) * s.pt ![0, 0, 1] * (n : G)⁻¹ = (s.pt ![0, 0, 1]) ^ 2 := by
    rcases hd with h | h
    · left
      rw [← s.conjCoord_spec n hnA ![0, 0, 1], h]
    · right
      rw [← s.conjCoord_spec n hnA ![0, 0, 1], h]
      rw [show (![0, 0, 2] : Fin 3 → ZMod 3) = 2 • ![0, 0, 1] by decide, s.pt_nsmul]
  have hconj2 : (n : G) * s.pt ![1, 2, 0] * (n : G)⁻¹ = s.pt ![1, 2, 0] ∨
      (n : G) * s.pt ![1, 2, 0] * (n : G)⁻¹ = (s.pt ![1, 2, 0]) ^ 2 := by
    rcases hz2 with h | h
    · left
      rw [← s.conjCoord_spec n hnA ![1, 2, 0], h]
    · right
      rw [← s.conjCoord_spec n hnA ![1, 2, 0], h]
      rw [show (![2, 1, 0] : Fin 3 → ZMod 3) = 2 • ![1, 2, 0] by decide, s.pt_nsmul]
  exact ⟨hconj1, hconj2⟩

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem mem_normalizer_of_mem_normalizer_subgroupOf
    {X : Subgroup G} (hAX : h.A ≤ X) {n : ↥X}
    (hn : n ∈ Subgroup.normalizer ((h.A.subgroupOf X) : Set ↥X)) :
    (n : G) ∈ Subgroup.normalizer (h.A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro x ⟨y, hyA, rfl⟩
    show (MulAut.conj (n : G)) y ∈ h.A
    rw [MulAut.conj_apply]
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hn ⟨y, hAX hyA⟩).mp (Subgroup.mem_subgroupOf.mpr hyA))
  · intro x hx
    refine ⟨(n : G)⁻¹ * x * (n : G), ?_, ?_⟩
    · show (n : G)⁻¹ * x * (n : G) ∈ h.A
      have := Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) ⟨x, hAX hx⟩).mp
          (Subgroup.mem_subgroupOf.mpr hx))
      simpa using this
    · show (MulAut.conj (n : G)) ((n : G)⁻¹ * x * (n : G)) = x
      rw [MulAut.conj_apply]
      group

private theorem isWeaklyClosedIn_zpowers_of_normalizes
    {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {S Z : Subgroup X} (Q : Sylow p X) (hQS : S = (Q : Subgroup X))
    (hZS : Z ≤ S) (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hN : ∀ n ∈ Subgroup.normalizer (S : Set X), ∀ z ∈ Z, n * z * n⁻¹ ∈ Z) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z S := by
  intro g hg
  apply Subgroup.eq_of_le_of_card_ge
  · intro y hy
    have hyZ : g * y * g⁻¹ ∈ Z :=
      (CFSG.ASVolI.ChIJK.burnsideI2BN_mem_conjugate).mp hy
    have hyS : y ∈ S := hg hy
    have hconjS : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ ∈ S := by
      rwa [show g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y by group]
    have hweak : ∀ k : X, CFSG.conjugate S k ≤ (Q : Subgroup X) →
        CFSG.conjugate S k = S :=
      fun k hk => Subgroup.eq_of_le_of_card_ge (by rwa [← hQS] at hk)
        (by rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective])
    obtain ⟨n, hnN, hnconj⟩ :=
      CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion Q S (le_of_eq hQS) hab hweak
        (hZS hyZ) hconjS
    have hnconj' : n * (g * y * g⁻¹) * n⁻¹ = y := by
      rw [hnconj]
      group
    have := hN n hnN (g * y * g⁻¹) hyZ
    rwa [hnconj'] at this
  · rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

private theorem normalizes_plane_z1
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    ∀ n ∈ Subgroup.normalizer ((h.A.subgroupOf X : Subgroup ↥X) : Set ↥X),
      ∀ z ∈ ((Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X : Subgroup ↥X),
        n * z * n⁻¹ ∈ ((Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X : Subgroup ↥X) := by
  intro n hn z hz
  let Z1 : Subgroup ↥X := (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X
  let z1 : ↥X := ⟨s.pt ![0, 0, 1], hAX (s.pt_mem_A _)⟩
  have hz1Z : z1 ∈ Z1 := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
  have hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf (X := X) hAX hn
  have hgen := (s.conj_pt_of_mem_normalizer hgood hbad hNA hXc hnA).1
  have hlift : n * z1 * n⁻¹ = z1 ∨ n * z1 * n⁻¹ = z1 ^ 2 := by
    rcases hgen with hg | hg
    · left
      apply Subtype.ext
      simpa [z1] using hg
    · right
      apply Subtype.ext
      simpa [z1] using hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
  have hz_eq : z = z1 ^ k := by
    apply Subtype.ext
    simpa [z1] using hk.symm
  rw [hz_eq]
  have hzp : n * z1 ^ k * n⁻¹ = (n * z1 * n⁻¹) ^ k := by
    simpa [MulAut.conj_apply] using map_zpow (MulAut.conj n) z1 k
  rw [hzp]
  rcases hlift with hg | hg
  · rw [hg]
    exact Z1.zpow_mem hz1Z k
  · rw [hg]
    exact Z1.zpow_mem (Z1.pow_mem hz1Z 2) k

private theorem normalizes_plane_z2
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    ∀ n ∈ Subgroup.normalizer ((h.A.subgroupOf X : Subgroup ↥X) : Set ↥X),
      ∀ z ∈ ((Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X : Subgroup ↥X),
        n * z * n⁻¹ ∈ ((Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X : Subgroup ↥X) := by
  intro n hn z hz
  let Z2 : Subgroup ↥X := (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X
  let z2 : ↥X := ⟨s.pt ![1, 2, 0], hAX (s.pt_mem_A _)⟩
  have hz2Z : z2 ∈ Z2 := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
  have hnA : (n : G) ∈ Subgroup.normalizer (h.A : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf (X := X) hAX hn
  have hgen := (s.conj_pt_of_mem_normalizer hgood hbad hNA hXc hnA).2
  have hlift : n * z2 * n⁻¹ = z2 ∨ n * z2 * n⁻¹ = z2 ^ 2 := by
    rcases hgen with hg | hg
    · left
      apply Subtype.ext
      simpa [z2] using hg
    · right
      apply Subtype.ext
      simpa [z2] using hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
  have hz_eq : z = z2 ^ k := by
    apply Subtype.ext
    simpa [z2] using hk.symm
  rw [hz_eq]
  have hzp : n * z2 ^ k * n⁻¹ = (n * z2 * n⁻¹) ^ k := by
    simpa [MulAut.conj_apply] using map_zpow (MulAut.conj n) z2 k
  rw [hzp]
  rcases hlift with hg | hg
  · rw [hg]
    exact Z2.zpow_mem hz2Z k
  · rw [hg]
    exact Z2.zpow_mem (Z2.pow_mem hz2Z 2) k

private theorem weak_closed_zpowers
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 h.A X) :
    IsWeaklyClosedIn ((Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X)
        (h.A.subgroupOf X) ∧
      IsWeaklyClosedIn ((Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X)
        (h.A.subgroupOf X) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let S : Subgroup ↥X := h.A.subgroupOf X
  let Z1 : Subgroup ↥X := (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X
  let Z2 : Subgroup ↥X := (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X
  have hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    have := h.elemAbelian.1.is_comm.comm
      (⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ : ↥h.A)
      (⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩ : ↥h.A)
    exact congrArg (fun z : ↥h.A => (z : G)) this
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hQS : S = (Q : Subgroup ↥X) := hQ.symm
  have hN1 := s.normalizes_plane_z1 hgood hbad hNA hAX hXc
  have hN2 := s.normalizes_plane_z2 hgood hbad hNA hAX hXc
  have hZ1S : Z1 ≤ S := by
    intro x hx
    exact Subgroup.zpowers_le.mpr (s.pt_mem_A _) (Subgroup.mem_subgroupOf.mp hx)
  have hZ2S : Z2 ≤ S := by
    intro x hx
    exact Subgroup.zpowers_le.mpr (s.pt_mem_A _) (Subgroup.mem_subgroupOf.mp hx)
  constructor
  · exact isWeaklyClosedIn_zpowers_of_normalizes (S := S) (Z := Z1) Q hQS hZ1S hab hN1
  · exact isWeaklyClosedIn_zpowers_of_normalizes (S := S) (Z := Z2) Q hQS hZ2S hab hN2

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem pt_mem_sup_zpowers (u : Fin 3 → ZMod 3) :
    s.pt u ∈ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) := by
  have he : s.pt ![1, 1, 0] ∈ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hz₂ : s.pt ![1, 2, 0] ∈ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hz₁ : s.pt ![0, 0, 1] ∈ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have he₀ : s.pt ![1, 0, 0] ∈ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) := by
    rw [show (![1, 0, 0] : Fin 3 → ZMod 3) = 2 • ![1, 1, 0] + 2 • ![1, 2, 0] by decide,
      s.pt_add, s.pt_nsmul, s.pt_nsmul]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ he 2) (Subgroup.pow_mem _ hz₂ 2)
  have he₁ : s.pt ![0, 1, 0] ∈ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) := by
    rw [show (![0, 1, 0] : Fin 3 → ZMod 3) = 2 • ![1, 1, 0] + ![1, 2, 0] by decide,
      s.pt_add, s.pt_nsmul]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ he 2) hz₂
  have hdecomp : s.pt u = s.pt ![1, 0, 0] ^ (u 0).val *
      s.pt ![0, 1, 0] ^ (u 1).val * s.pt ![0, 0, 1] ^ (u 2).val := by
    conv_lhs => rw [eq_sum_basis u]
    rw [s.pt_add, s.pt_add, s.pt_nsmul, s.pt_nsmul, s.pt_nsmul]
  rw [hdecomp]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ he₀ _)
    (Subgroup.pow_mem _ he₁ _)) (Subgroup.pow_mem _ hz₁ _)

private theorem A_le_sup_zpowers :
    h.A ≤ Subgroup.zpowers (s.pt ![0, 0, 1]) ⊔
      Subgroup.zpowers (s.pt ![1, 2, 0]) ⊔ Subgroup.zpowers (s.pt ![1, 1, 0]) := by
  intro y hy
  obtain ⟨u, hu⟩ := s.exists_pt_of_mem hy
  rw [← hu]
  exact s.pt_mem_sup_zpowers u

private theorem zpowers_pt_ne :
    Subgroup.zpowers (s.pt ![0, 0, 1]) ≠ Subgroup.zpowers (s.pt ![1, 2, 0]) := by
  intro heq
  have hmem : s.pt ![0, 0, 1] ∈ Subgroup.zpowers (s.pt ![1, 2, 0]) := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : Multiplicative.ofAdd (![0, 0, 1] : Fin 3 → ZMod 3) =
      (Multiplicative.ofAdd (![1, 2, 0] : Fin 3 → ZMod 3)) ^ k := by
    apply s.ptHom_injective
    rw [map_zpow]
    simpa [ptHom_apply] using hk.symm
  have hk2 : (![0, 0, 1] : Fin 3 → ZMod 3) = k • ![1, 2, 0] := by
    have := congrArg Multiplicative.toAdd hk'
    simpa [toAdd_zpow] using this
  have h0 : (0 : ZMod 3) = (k : ZMod 3) := by
    simpa [zsmul_eq_mul] using congrFun hk2 0
  have h2 : (1 : ZMod 3) = (k : ZMod 3) * 0 := by
    simpa [zsmul_eq_mul] using congrFun hk2 2
  rw [← h0] at h2
  simpa using h2

private theorem frattini_sylow_data
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 h.A X) :
    CFSG.ABGLocalTools.IsSylowOf 3 (h.A.subgroupOf X) ⊤ ∧
    CFSG.Open.IsElemAbelian 3 (h.A.subgroupOf X) ∧
    Nat.card (h.A.subgroupOf X) = 27 ∧
    (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X ≤ h.A.subgroupOf X ∧
    (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X ≤ h.A.subgroupOf X ∧
    Nat.card ((Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X) = 3 ∧
    Nat.card ((Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X) = 3 := by
  classical
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (h.A.subgroupOf X) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := X)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAX,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hsyl
  have hz₁X : Subgroup.zpowers (s.pt ![0, 0, 1]) ≤ X :=
    (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
  have hz₂X : Subgroup.zpowers (s.pt ![1, 2, 0]) ≤ X :=
    (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
  refine ⟨hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.elemAbelian.subgroupOf X
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, h.card_A]
  · intro x hx
    exact (Subgroup.zpowers_le.mpr (s.pt_mem_A _)) (Subgroup.mem_subgroupOf.mp hx)
  · intro x hx
    exact (Subgroup.zpowers_le.mpr (s.pt_mem_A _)) (Subgroup.mem_subgroupOf.mp hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz₁X).toEquiv, Nat.card_zpowers,
      s.orderOf_pt ne_zero_001]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz₂X).toEquiv, Nat.card_zpowers,
      s.orderOf_pt ne_zero_120]

private theorem frattini_zpowers_ne {X : Subgroup G} (hAX : h.A ≤ X) :
    (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X ≠
    (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X := by
  intro heq
  have hz₁X : Subgroup.zpowers (s.pt ![0, 0, 1]) ≤ X :=
    (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
  have hz₂X : Subgroup.zpowers (s.pt ![1, 2, 0]) ≤ X :=
    (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
  apply s.zpowers_pt_ne
  calc Subgroup.zpowers (s.pt ![0, 0, 1]) =
        ((Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X).map X.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hz₁X).symm
    _ = ((Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X).map X.subtype := by rw [heq]
    _ = Subgroup.zpowers (s.pt ![1, 2, 0]) := Subgroup.map_subgroupOf_eq_of_le hz₂X

private theorem frattini_center_data
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    (Subgroup.zpowers (s.pt ![1, 1, 0])).subgroupOf X ≤ Subgroup.center ↥X ∧
    h.A.subgroupOf X ≤
      (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X ⊔
      (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X ⊔
      (Subgroup.zpowers (s.pt ![1, 1, 0])).subgroupOf X := by
  constructor
  · intro b hb
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    have hcomm : Commute (s.pt ![1, 1, 0]) (x : G) := (hXc (x : G) x.2).symm
    have hbx : (b : G) * (x : G) = (x : G) * (b : G) := by
      rw [← hk]
      exact (hcomm.zpow_left k).eq
    simpa using hbx.symm
  · have hz₁X : Subgroup.zpowers (s.pt ![0, 0, 1]) ≤ X :=
      (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
    have hz₂X : Subgroup.zpowers (s.pt ![1, 2, 0]) ≤ X :=
      (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
    have heX : Subgroup.zpowers (s.pt ![1, 1, 0]) ≤ X :=
      (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
    have h := Subgroup.subgroupOf_mono X s.A_le_sup_zpowers
    rwa [Subgroup.subgroupOf_sup (sup_le hz₁X hz₂X) heX,
      Subgroup.subgroupOf_sup hz₁X hz₂X] at h

private theorem frattini_centralizer_z1
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    Subgroup.centralizer (((Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X :
      Subgroup ↥X) : Set ↥X) ≤ D.M.subgroupOf X := by
  intro w hw
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hz₁X : Subgroup.zpowers (s.pt ![0, 0, 1]) ≤ X :=
    (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
  have hwz : (w : G) ∈ Subgroup.centralizer ({s.pt ![0, 0, 1]} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : (⟨s.pt ![0, 0, 1], hz₁X (Subgroup.mem_zpowers _)⟩ : ↥X) ∈
        (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
    have := congrArg (fun z : ↥X => (z : G))
      ((Subgroup.mem_centralizer_iff.mp hw) _ hz)
    exact this.symm
  have hwe : (w : G) * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * (w : G) :=
    hXc (w : G) w.2
  have hprod : (w : G) * s.pt ![1, 1, 1] = s.pt ![1, 1, 1] * (w : G) := by
    rw [vec_111, s.pt_add]
    calc (w : G) * (s.pt ![1, 1, 0] * s.pt ![0, 0, 1]) =
          ((w : G) * s.pt ![1, 1, 0]) * s.pt ![0, 0, 1] := by group
      _ = (s.pt ![1, 1, 0] * (w : G)) * s.pt ![0, 0, 1] := by rw [hwe]
      _ = s.pt ![1, 1, 0] * ((w : G) * s.pt ![0, 0, 1]) := by group
      _ = s.pt ![1, 1, 0] * (s.pt ![0, 0, 1] * (w : G)) := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hwz]
      _ = (s.pt ![1, 1, 0] * s.pt ![0, 0, 1]) * (w : G) := by group
  exact (hgood (![1, 1, 1] : Fin 3 → ZMod 3) ne_zero_111 weight_111).centralizer_le
    (Subgroup.mem_centralizer_singleton_iff.mpr hprod)

private theorem frattini_centralizer_z2
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    Subgroup.centralizer (((Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X :
      Subgroup ↥X) : Set ↥X) ≤ D.M.subgroupOf X := by
  intro w hw
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hz₂X : Subgroup.zpowers (s.pt ![1, 2, 0]) ≤ X :=
    (Subgroup.zpowers_le.mpr (s.pt_mem_A _)).trans hAX
  have hwz : (w : G) ∈ Subgroup.centralizer ({s.pt ![1, 2, 0]} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : (⟨s.pt ![1, 2, 0], hz₂X (Subgroup.mem_zpowers _)⟩ : ↥X) ∈
        (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
    have := congrArg (fun z : ↥X => (z : G))
      ((Subgroup.mem_centralizer_iff.mp hw) _ hz)
    exact this.symm
  have hwe : (w : G) * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * (w : G) :=
    hXc (w : G) w.2
  have hprod : (w : G) * s.pt ![2, 0, 0] = s.pt ![2, 0, 0] * (w : G) := by
    rw [vec_200, s.pt_add]
    calc (w : G) * (s.pt ![1, 1, 0] * s.pt ![1, 2, 0]) =
          ((w : G) * s.pt ![1, 1, 0]) * s.pt ![1, 2, 0] := by group
      _ = (s.pt ![1, 1, 0] * (w : G)) * s.pt ![1, 2, 0] := by rw [hwe]
      _ = s.pt ![1, 1, 0] * ((w : G) * s.pt ![1, 2, 0]) := by group
      _ = s.pt ![1, 1, 0] * (s.pt ![1, 2, 0] * (w : G)) := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp hwz]
      _ = (s.pt ![1, 1, 0] * s.pt ![1, 2, 0]) * (w : G) := by group
  exact (hgood (![2, 0, 0] : Fin 3 → ZMod 3) ne_zero_200 weight_200).centralizer_le
    (Subgroup.mem_centralizer_singleton_iff.mpr hprod)

private theorem frattini_normalizer
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G} (hAX : h.A ≤ X) :
    Subgroup.normalizer ((h.A.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤ D.M.subgroupOf X :=
  fun n hn => Subgroup.mem_subgroupOf.mpr
    (hNA (mem_normalizer_of_mem_normalizer_subgroupOf (X := X) hAX hn))

private theorem frattini_step_l62 (hK332 : UCK.K332ThreeAb)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x)
    (hXtop : X ≠ ⊤)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 h.A X) :
    X ≤ (X ⊓ D.M) ⊔ CFSG.Open.relPPrimeCore 3 X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let S : Subgroup ↥X := h.A.subgroupOf X
  let Z₁ : Subgroup ↥X := (Subgroup.zpowers (s.pt ![0, 0, 1])).subgroupOf X
  let Z₂ : Subgroup ↥X := (Subgroup.zpowers (s.pt ![1, 2, 0])).subgroupOf X
  let B : Subgroup ↥X := (Subgroup.zpowers (s.pt ![1, 1, 0])).subgroupOf X
  let Y : Subgroup ↥X := D.M.subgroupOf X
  obtain ⟨hS, hSe, hS27, hZ₁S, hZ₂S, hZ₁, hZ₂⟩ := s.frattini_sylow_data hAX hsyl
  have hZ₁₂ := s.frattini_zpowers_ne hAX
  obtain ⟨hB, hgen⟩ := s.frattini_center_data hAX hXc
  obtain ⟨hw₁, hw₂⟩ := s.weak_closed_zpowers hgood hbad hNA hAX hXc hsyl
  have hC₁ := s.frattini_centralizer_z1 hgood hAX hXc
  have hC₂ := s.frattini_centralizer_z2 hgood hAX hXc
  have hN := frattini_normalizer hNA hAX
  have hK : CFSG.Open.IsKGroup ↥X :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper D.standing.kProper hXtop
  have hFratt := top_le_sup_pPrimeCore_of_weaklyClosed hK332 hK hS hSe hS27 hZ₁S hZ₂S
    hZ₁ hZ₂ hZ₁₂ hw₁ hw₂ hB hgen hC₁ hC₂ hN
  have hmap := Subgroup.map_mono (f := X.subtype) hFratt
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.subgroupOf_map_subtype,
    ← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three X] at hmap
  simpa [Y, inf_comm] using hmap

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

private def planeE1 : Subgroup (Multiplicative (Fin 3 → ZMod 3)) where
  carrier := {v | Multiplicative.toAdd v 1 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, toAdd_mul, Pi.add_apply] at *
    rw [ha, hb]
    simp
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, toAdd_inv, Pi.neg_apply] at *
    rw [ha]
    decide

private instance : DecidablePred (· ∈ planeE1) := fun v =>
  inferInstanceAs (Decidable (Multiplicative.toAdd v 1 = 0))

private theorem card_planeE1 : Nat.card planeE1 = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem plane_translate (u : Fin 3 → ZMod 3) (hu : u ≠ 0) (h1 : u 1 = 0) :
    ∃ k : Fin 3, (u + k.val • (![1, 1, 0] : Fin 3 → ZMod 3)) ≠ 0 ∧
      ((∀ i, (u + k.val • (![1, 1, 0] : Fin 3 → ZMod 3)) i ≠ 0) ∨
      ∃ i, ∀ j, j ≠ i → (u + k.val • (![1, 1, 0] : Fin 3 → ZMod 3)) j = 0) := by
  revert u
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private def planeEF : Subgroup G := planeE1.map s.ptHom

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple in
private theorem relPPrimeCore_eq_iSup_plane {X : Subgroup G} (hAX : h.A ≤ X) :
    CFSG.Open.relPPrimeCore 3 X = ⨆ m : s.planeEF, ⨆ (_ : m ≠ 1),
      CFSG.Open.relPPrimeCore 3 X ⊓ Subgroup.centralizer ({(m : G)} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hEFleA : s.planeEF ≤ h.A := s.map_ptHom_le_A planeE1
  have hEFleX : s.planeEF ≤ X := hEFleA.trans hAX
  have hcardEF : Nat.card s.planeEF = 9 := by
    dsimp only [planeEF]
    rw [s.card_map_ptHom, card_planeE1]
  have hpower : ∀ m : s.planeEF, m ^ 3 = 1 := by
    intro m
    apply Subtype.ext
    exact h.elemAbelian.2 (m : G) (hEFleA m.2)
  have hcop : ¬ 3 ∣ Nat.card (CFSG.Open.relPPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_relPPrimeCore Nat.prime_three X)
  have hNX : CFSG.Open.relPPrimeCore 3 X ≤ X := relPPrimeCore_le X
  have hNnorm : ((CFSG.Open.relPPrimeCore 3 X).subgroupOf X).Normal :=
    relPPrimeCore_normal Nat.prime_three X
  have hiff := (Subgroup.normal_subgroupOf_iff hNX).mp hNnorm
  have hnormal : s.planeEF ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore 3 X : Set G) := by
    intro x hx
    have hxX : x ∈ X := hEFleX hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hiff y x hy hxX
    · intro hy
      have h := hiff (x * y * x⁻¹) x⁻¹ hy (X.inv_mem hxX)
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h
  exact CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three s.planeEF (CFSG.Open.relPPrimeCore 3 X) hpower
    (by rw [hcardEF]; norm_num) hcop hnormal

private theorem relPPrimeCore_le_of_plane
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    {X : Subgroup G} (hAX : h.A ≤ X)
    (hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x) :
    CFSG.Open.relPPrimeCore 3 X ≤ D.M := by
  classical
  rw [s.relPPrimeCore_eq_iSup_plane hAX]
  refine iSup_le fun m => iSup_le fun hm => ?_
  obtain ⟨u, huE, hu⟩ := Subgroup.mem_map.mp (m.2 : (m : G) ∈ s.planeEF)
  have hw1 : Multiplicative.toAdd u 1 = 0 := huE
  have hw0 : Multiplicative.toAdd u ≠ 0 := by
    intro h0
    apply hm
    apply Subtype.ext
    rw [← hu, s.ptHom_apply u, h0, s.pt_zero]
    rfl
  obtain ⟨k, hkne, hk⟩ := plane_translate (Multiplicative.toAdd u) hw0 hw1
  have hgoodk : GoodPoint D.M
      (s.pt (Multiplicative.toAdd u + k.val • ![1, 1, 0])) :=
    hgood _ hkne hk
  have hle : CFSG.Open.relPPrimeCore 3 X ⊓
      Subgroup.centralizer ({(m : G)} : Set G) ≤
      Subgroup.centralizer ({s.pt (Multiplicative.toAdd u + k.val • ![1, 1, 0])} : Set G) := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    have hxX : x ∈ X :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le X hxN
    have hxe : x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x := hXc x hxX
    have hmpt : (m : G) = s.pt (Multiplicative.toAdd u) := by
      rw [← hu, s.ptHom_apply u]
    have hxm : x * s.pt (Multiplicative.toAdd u) = s.pt (Multiplicative.toAdd u) * x := by
      rwa [hmpt] at hxC
    have hcomm : Commute (s.pt ![1, 1, 0]) x := hxe.symm
    have hxepow : x * s.pt ![1, 1, 0] ^ k.val =
        s.pt ![1, 1, 0] ^ k.val * x :=
      (hcomm.pow_left k.val).eq.symm
    rw [s.pt_add, s.pt_nsmul]
    calc x * (s.pt (Multiplicative.toAdd u) * s.pt ![1, 1, 0] ^ k.val)
        = (x * s.pt (Multiplicative.toAdd u)) * s.pt ![1, 1, 0] ^ k.val := by group
      _ = (s.pt (Multiplicative.toAdd u) * x) * s.pt ![1, 1, 0] ^ k.val := by rw [hxm]
      _ = s.pt (Multiplicative.toAdd u) * (x * s.pt ![1, 1, 0] ^ k.val) := by group
      _ = s.pt (Multiplicative.toAdd u) *
            (s.pt ![1, 1, 0] ^ k.val * x) := by rw [hxepow]
      _ = (s.pt (Multiplicative.toAdd u) * s.pt ![1, 1, 0] ^ k.val) * x := by group
  exact hle.trans hgoodk.centralizer_le

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem A_le_centralizer_pt (v : Fin 3 → ZMod 3) :
    h.A ≤ Subgroup.centralizer ({s.pt v} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg (fun z : ↥h.A => (z : G))
    (h.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨s.pt v, s.pt_mem_A v⟩)

private theorem centralizer_pt_ne_top (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    Subgroup.centralizer ({s.pt v} : Set G) ≠ ⊤ := by
  have hzpne : Subgroup.zpowers (s.pt v) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact s.pt_ne_one hv
  have hCtop := centralizer_ne_top_of_ne_bot D.standing.simple D.standing.nonab hzpne
  simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hCtop

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

theorem centralizer_le_of_isSylowOf_of_l62 (hK332 : UCK.K332ThreeAb)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hbad : ¬ GoodPoint D.M (s.pt ![1, 1, 0]))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 h.A
      (Subgroup.centralizer ({s.pt ![1, 1, 0]} : Set G))) :
    Subgroup.centralizer ({s.pt ![1, 1, 0]} : Set G) ≤ D.M := by
  classical
  let X : Subgroup G := Subgroup.centralizer ({s.pt ![1, 1, 0]} : Set G)
  have hAX : h.A ≤ X := s.A_le_centralizer_pt ![1, 1, 0]
  have hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mp hx
  have hXtop : X ≠ ⊤ := s.centralizer_pt_ne_top ![1, 1, 0] ne_zero_110
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf 3 h.A X := by simpa [X] using hsyl
  have hfr := s.frattini_step_l62 hK332 hgood hbad hNA hAX hXc hXtop hsyl'
  have hrel := s.relPPrimeCore_le_of_plane hgood hAX hXc
  exact hfr.trans (sup_le inf_le_right hrel)

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private theorem good_of_centralizer_e (hK332 : UCK.K332ThreeAb) (hCA : K7L6TwoCentA)
    (hlie : IsLie811 c.Lbar .l6 2 1) (hP : Nat.card h.P = 81) (h7 : 7 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy7 : orderOf y = 7)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M) :
    GoodPoint D.M (s.pt ![1, 1, 0]) := by
  classical
  by_contra hbad
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let X : Subgroup G := Subgroup.centralizer ({s.pt ![1, 1, 0]} : Set G)
  have hAX : h.A ≤ X := s.A_le_centralizer_pt ![1, 1, 0]
  have hXc : ∀ x : G, x ∈ X → x * s.pt ![1, 1, 0] = s.pt ![1, 1, 0] * x :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mp hx
  have hXtop : X ≠ ⊤ := s.centralizer_pt_ne_top ![1, 1, 0] ne_zero_110
  have hAsub : IsPGroup 3 (h.A.subgroupOf X) := h.elemAbelian.isPGroup.comap_subtype
  obtain ⟨Q, hQle⟩ := hAsub.exists_le_sylow
  let S : Subgroup G := (Q : Subgroup ↥X).map X.subtype
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 S X := ⟨Q, rfl⟩
  have hAS : h.A ≤ S := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAX]
    exact Subgroup.map_mono hQle
  have hSleX : S ≤ X := Subgroup.map_subtype_le _
  by_cases hlt : h.A < S ⊓ Subgroup.normalizer (h.A : Set G)
  · have hge := s.good_of_lt_normalizer_of_l62 hCA hlie hP
      (fun v hv3 => hgood v (by
        intro h0
        exact hv3 0 (by rw [h0]; rfl)) (Or.inl hv3)) hNA
      (s.pt_mem_A _) (s.pt_ne_one ne_zero_110) hS.isPGroup hAS
      (fun x hx => hSleX hx) hlt
    exact hbad hge
  · have hS_eq : S = h.A := by
      by_contra hne
      have hltAS : h.A < S := lt_of_le_of_ne hAS (Ne.symm hne)
      exact hlt (CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 3) hS.isPGroup hltAS)
    have hsylA : CFSG.ABGLocalTools.IsSylowOf 3 h.A X := by
      rwa [hS_eq] at hS
    have hC : X ≤ D.M := s.centralizer_le_of_isSylowOf_of_l62 hK332 hgood hbad hNA hsylA
    have hdvdM : ∀ B : Subgroup G, B ≤ h.A → Nat.card B = 3 →
        7 ∣ Nat.card (D.M ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
      intro B hBA hB3
      have hyB : y ∈ D.M ⊓ Subgroup.centralizer (B : Set G) := by
        refine ⟨hy.1, ?_⟩
        exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
          Subgroup.mem_centralizer_iff.mp hy.2 z (hBA hz)
      have hdvd : orderOf y ∣ Nat.card (D.M ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :=
        Subgroup.orderOf_dvd_natCard _ hyB
      rwa [hy7] at hdvd
    exact hbad (h.good_of_centralizer_le_of_dvdM h7 hdvdM (s.pt_mem_A _)
      (s.orderOf_pt ne_zero_110) hC)

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

theorem good_of_ne_zero_of_l62 (hK332 : UCK.K332ThreeAb) (hCA : K7L6TwoCentA)
    (hlie : IsLie811 c.Lbar .l6 2 1) (hP : Nat.card h.P = 81) (h7 : 7 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy7 : orderOf y = 7)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ((∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) →
      GoodPoint D.M (s.pt v))
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M) {v : Fin 3 → ZMod 3} (hv : v ≠ 0) :
    GoodPoint D.M (s.pt v) := by
  classical
  rcases weight_trichotomy v hv with h3 | h2 | h1
  · exact hgood v hv (Or.inl (by simpa [Weight3] using h3))
  · obtain ⟨σ, ε, hε, hv'⟩ := exists_perm_signs v hv ⟨h2.choose, h2.choose_spec.1⟩
    obtain ⟨g, -, hgconj⟩ := s.exists_conj σ ε hε
    have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
    rcases hv' with rfl | rfl
    · exact (signed_e0_not_weight_two σ ε hε h2).elim
    · have hge := s.good_of_centralizer_e hK332 hCA hlie hP h7 hy hy7 hgood hNA
      have hgc := (GoodPoint.conj (M := D.M) hgM hge)
      simpa [hgconj] using hgc
  · exact hgood v hv (Or.inr (by simpa [Weight1] using h1))

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
