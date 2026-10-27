module

public import CFSG.RankThree.PartOne.NF7J.LRoots1
public import CFSG.RankThree.PartOne.HESS.Node
public import CFSG.RankThree.PartOne.NF7J.SwapRule

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.SP4C
open scoped commutatorElement

section Root

variable {G : Type} [Group G] [Finite G]

@[expose] def RootGp (p : ℕ) (E : Subgroup G) (f : ℕ) (t : MulAut E) : Set (Subgroup G) :=
  {S | S ≤ kZero p E t ∧ (∀ s ∈ S, s * s = 1) ∧ Nat.card S = 2 ^ f ∧
    ∀ a ∈ E, ∀ s ∈ S, a * s * a⁻¹ ∈ S}

omit [Finite G] in
theorem conjBy_mem_rootGp {p : ℕ} {E : Subgroup G} {f : ℕ} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {t : MulAut E} {S : Subgroup G}
    (hS : S ∈ RootGp p E f t) :
    conjBy w S ∈ RootGp p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  obtain ⟨hSK, hsq, hcard, hinv⟩ := hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kZero_conj p t hw]
    exact Subgroup.map_mono hSK
  · intro s hs
    rw [Equivariance.mem_conjBy] at hs
    have h1 := hsq _ hs
    calc s * s = w * ((w⁻¹ * s * w) * (w⁻¹ * s * w)) * w⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · unfold conjBy
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hcard
  · intro a ha s hs
    rw [Equivariance.mem_conjBy] at hs ⊢
    have h1 := hinv _ (HESS.inv_conj_mem (A := E) hw ha) _ hs
    have e : w⁻¹ * (a * s * a⁻¹) * w = (w⁻¹ * a * w) * (w⁻¹ * s * w) * (w⁻¹ * a * w)⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem rule_node {K : Type} [Field K] [Finite K] [CharP K 2] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {E : Subgroup G} {r : MulAut E}
    {φ : Matrix.SpecialLinearGroup (Fin 2) K →* G} (hφ : Function.Injective φ)
    (hrange : φ.range = kZero p E r)
    (hroot : RootGp p E f r = {(Uplus K).map φ, (Uminus K).map φ})
    (hne : (Uplus K).map φ ≠ (Uminus K).map φ) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hfix : conjAut E w hw * r * (conjAut E w hw)⁻¹ = r) {n : ℕ}
    (hn : w * φ (hmat ζ) * w⁻¹ = φ (hmat ζ) ^ n) :
    (n % p = 1 → conjBy w ((Uplus K).map φ) = (Uplus K).map φ ∧
        conjBy w ((Uminus K).map φ) = (Uminus K).map φ) ∧
      ((n + 1) % p = 0 → conjBy w ((Uplus K).map φ) = (Uminus K).map φ ∧
        conjBy w ((Uminus K).map φ) = (Uplus K).map φ) := by
  have h0 : (Uplus K).map φ ∈ RootGp p E f r := by rw [hroot]; exact Set.mem_insert _ _
  have h4 : (Uminus K).map φ ∈ RootGp p E f r := by
    rw [hroot]; exact Set.mem_insert_of_mem _ rfl
  have hc0 := conjBy_mem_rootGp hw h0
  have hc4 := conjBy_mem_rootGp hw h4
  rw [hfix, hroot] at hc0 hc4
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc0 hc4
  have hK : conjBy w (kZero p E r) = kZero p E r := by rw [← kZero_conj p r hw, hfix]
  have hw' : ∀ M, ∃ M', φ M' = w * φ M * w⁻¹ := by
    intro M
    have : w * φ M * w⁻¹ ∈ conjBy w (kZero p E r) :=
      Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom (hrange ▸ ⟨M, rfl⟩)
    rw [hK, ← hrange] at this
    obtain ⟨M', hM'⟩ := this
    exact ⟨M', hM'⟩
  have hinj : Function.Injective (conjBy w : Subgroup G → Subgroup G) :=
    Subgroup.map_injective (MulAut.conj w).injective
  obtain ⟨hA, hB⟩ := frame_rule hp hp2 hdvd hodd φ hφ hζ w hw' hn hc0
  constructor
  · intro hn1
    have e0 := hA hn1
    refine ⟨e0, ?_⟩
    rcases hc4 with h | h
    · exact absurd (hinj (e0.trans h.symm)) hne
    · exact h
  · intro hn1
    have e0 := hB hn1
    refine ⟨e0, ?_⟩
    rcases hc4 with h | h
    · exact h
    · exact absurd (hinj (e0.trans h.symm)) hne

end Root

namespace RFrame

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K)

theorem octNC_irrefl : ∀ i : Fin 8, ¬ OctNC i i := by decide

theorem rg_ne {i j : Fin 8} (h : OctNC i j) : F.rg i ≠ F.rg j := by
  intro heq
  obtain ⟨x, hx, y, hy, hxy⟩ := F.rg_ncomm h
  rw [← heq] at hy
  exact hxy (F.rg_comm (octNC_irrefl i) x hx y hy)

theorem hζ2 (h5 : 5 ≤ p) : F.ζ ^ 2 ≠ 1 :=
  F.hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)

@[expose] noncomputable def b₀ : G := F.phi₀ (hmat F.ζ)

@[expose] noncomputable def b₁ : G := F.phi₁ (hmat F.ζ)

theorem rootGp_r₀ (h5 : 5 ≤ p) : RootGp p E f F.r₀ = {F.rg 0, F.rg 4} := by
  ext S
  constructor
  · rintro ⟨hSK, hsq, hcard, hinv⟩
    have hb : F.phi₀ (hmat F.ζ) ∈ E := F.phi₀_hmat_mem_E
    rcases frame_cases F.phi₀ F.phi₀_injective (F.hζ2 h5) (by rw [F.phi₀_range]; exact hSK) hsq
      (by rw [hcard, F.card]) (fun s hs => hinv _ hb s hs) with h | h
    · left
      rw [h, F.rg_zero_eq]
    · right
      rw [Set.mem_singleton_iff, h, F.rg_four_eq]
  · intro hS
    have hK : ∀ T : Subgroup ↥(spRev K), T ≤ (spBlock (K := K)).range →
        T.map F.rgHom ≤ kZero p E F.r₀ := by
      intro T hT
      rw [F.kZero_r₀_eq]
      exact Subgroup.map_mono hT
    rcases hS with rfl | rfl
    · refine ⟨hK _ ?_, fun s hs => F.rg_sq hs, F.card_rg 0, fun a ha s hs => F.rg_conj_E ha hs⟩
      rw [octSub_zero_eq]
      rintro _ ⟨M, -, rfl⟩
      exact ⟨M, rfl⟩
    · refine ⟨hK _ ?_, fun s hs => F.rg_sq hs, F.card_rg 4, fun a ha s hs => F.rg_conj_E ha hs⟩
      rw [octSub_four_eq]
      rintro _ ⟨M, -, rfl⟩
      exact ⟨M, rfl⟩

theorem rootGp_r₁ (h5 : 5 ≤ p) : RootGp p E f F.r₁ = {F.rg 7, F.rg 3} := by
  ext S
  constructor
  · rintro ⟨hSK, hsq, hcard, hinv⟩
    have hb : F.phi₁ (hmat F.ζ) ∈ E := F.phi₁_hmat_mem_E
    rcases frame_cases F.phi₁ F.phi₁_injective (F.hζ2 h5) (by rw [F.phi₁_range]; exact hSK) hsq
      (by rw [hcard, F.card]) (fun s hs => hinv _ hb s hs) with h | h
    · left
      rw [h, F.rg_seven_eq]
    · right
      rw [Set.mem_singleton_iff, h, F.rg_three_eq]
  · intro hS
    have hK : ∀ T : Subgroup ↥(spRev K), T ≤ (spBlock' (K := K)).range →
        T.map F.rgHom ≤ kZero p E F.r₁ := by
      intro T hT
      rw [F.kZero_r₁_eq]
      exact Subgroup.map_mono hT
    rcases hS with rfl | rfl
    · refine ⟨hK _ ?_, fun s hs => F.rg_sq hs, F.card_rg 7, fun a ha s hs => F.rg_conj_E ha hs⟩
      rw [octSub_seven_eq]
      rintro _ ⟨M, -, rfl⟩
      exact ⟨M, rfl⟩
    · refine ⟨hK _ ?_, fun s hs => F.rg_sq hs, F.card_rg 3, fun a ha s hs => F.rg_conj_E ha hs⟩
      rw [octSub_three_eq]
      rintro _ ⟨M, -, rfl⟩
      exact ⟨M, rfl⟩

theorem rule_r₀ (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p) (hdvd : p ∣ 2 ^ f - 1)
    (hodd : 2 ^ f % 3 = 2) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hfix : conjAut E w hw * F.r₀ * (conjAut E w hw)⁻¹ = F.r₀) {n : ℕ}
    (hn : w * F.b₀ * w⁻¹ = F.b₀ ^ n) :
    (n % p = 1 → conjBy w (F.rg 0) = F.rg 0 ∧ conjBy w (F.rg 4) = F.rg 4) ∧
      ((n + 1) % p = 0 → conjBy w (F.rg 0) = F.rg 4 ∧ conjBy w (F.rg 4) = F.rg 0) := by
  rw [F.rg_zero_eq, F.rg_four_eq]
  exact rule_node hp hp2 hdvd hodd F.phi₀_injective F.phi₀_range
    (by rw [← F.rg_zero_eq, ← F.rg_four_eq]; exact F.rootGp_r₀ h5)
    (by rw [← F.rg_zero_eq, ← F.rg_four_eq]; exact F.rg_ne (by decide)) F.hζ hw hfix hn

end RFrame

end CFSG.RankThree.PartOne.NF7J
