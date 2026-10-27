module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.LemmaR
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem isPGroup_posUnipotent
    [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r] :
    IsPGroup r (posUnipotent τ K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K r
  have hqcard : Nat.card K = r ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  refine IsPGroup.of_card (n := (n : ℕ) * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard)
    ?_
  rw [card_posUnipotent, hqcard, ← pow_mul]

theorem exists_conj_le_posUnipotent
    [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    {P : Subgroup (ModGL τ K)} (hPC : P ≤ adjointGroup τ K) (hPr : IsPGroup r P) :
    ∃ g ∈ adjointGroup τ K, ∀ x ∈ P, g⁻¹ * x * g ∈ posUnipotent τ K := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  obtain ⟨⟨PU, hPU⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K r w₀ hw₀
  have hP' : IsPGroup r (P.subgroupOf (adjointGroup τ K)) := hPr.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) PU Q
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hPC hx⟩ : adjointGroup τ K) ∈ (Q : Subgroup (adjointGroup τ K)) :=
    hQ (Subgroup.mem_subgroupOf.2 hx)
  rw [← hg, coe_smul_sylow_eq_map, hPU] at hxQ
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 hxQ
  have hu' : (u : ModGL τ K) ∈ posUnipotent τ K := Subgroup.mem_subgroupOf.1 hu
  have h1 : (g : ModGL τ K)⁻¹ * x * g = u := by
    have := congrArg Subtype.val hux
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv] at this
    rw [← this]
    group
  rw [h1]
  exact hu'

theorem eq_bot_of_isPGroup_of_normalized
    [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    {J W : Subgroup (ModGL τ K)} (hJC : J ≤ adjointGroup τ K) (hWC : W ≤ adjointGroup τ K)
    (hWr : IsPGroup r W) (hJx : ∀ i : Fin τ.rank, xUnit τ K i 1 ∈ J)
    {w₀ : WeylGroup τ} (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hJn : canonicalRep (coxeterSystem τ) K w₀ ∈ J)
    (hnorm : ∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W) : W = ⊥ := by
  set U₀ : Subgroup (ModGL τ K) := Subgroup.closure (Set.range fun i : Fin τ.rank =>
    xUnit τ K i 1) with hU₀
  have hU₀J : U₀ ≤ J := (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hJx i)
  have hU₀U : U₀ ≤ posUnipotent τ K := (Subgroup.closure_le _).2 (by
    rintro _ ⟨i, rfl⟩; exact xUnit_mem_posUnipotent i 1)
  have hU₀r : IsPGroup r U₀ := IsPGroup.to_le (isPGroup_posUnipotent r) hU₀U
  have hnormW : U₀ ≤ Subgroup.normalizer (W : Set (ModGL τ K)) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm j (hU₀J hj) x hx, fun hx => ?_⟩
    have := hnorm j⁻¹ (inv_mem (hU₀J hj)) _ hx
    simpa [mul_assoc] using this
  have hPr : IsPGroup r (W ⊔ U₀ : Subgroup (ModGL τ K)) := hWr.to_sup_of_normal_left' hU₀r hnormW
  have hPC : (W ⊔ U₀ : Subgroup (ModGL τ K)) ≤ adjointGroup τ K :=
    sup_le hWC (hU₀J.trans hJC)
  obtain ⟨g, hgC, hg⟩ := exists_conj_le_posUnipotent r hPC hPr
  have hgB : g ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_simple_mem_posUnipotent hgC fun i => hg _ ?_
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, rfl⟩)
  have hWU : ∀ x ∈ W, x ∈ posUnipotent τ K := by
    intro x hx
    have h1 := hg x (Subgroup.mem_sup_left hx)
    have h2 := conj_mem_posUnipotent_of_mem_borel hgB h1
    simpa [mul_assoc] using h2
  have hVmap := map_conj_canonicalRep_longest (τ := τ) (K := K) hw₀
  have hWV : ∀ x ∈ W, x ∈ negUnipotent τ K := by
    intro x hx
    have hx' : (canonicalRep (coxeterSystem τ) K w₀)⁻¹ * x * canonicalRep (coxeterSystem τ) K w₀ ∈
        W := by
      simpa using hnorm _ (inv_mem hJn) x hx
    have h1 := hWU _ hx'
    rw [← hVmap]
    refine ⟨_, h1, ?_⟩
    simp [MulAut.conj_apply]
    group
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ posUnipotent τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2 ⟨hWU x hx, hWV x hx⟩
  rwa [CFSG.LieType.Chevalley.posUnipotent_inf_negUnipotent] at hmem

theorem eq_one_of_commute_simple_longest
    [Finite K] {x : ModGL τ K}
    (hxC : x ∈ adjointGroup τ K) {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hs : ∀ i : Fin τ.rank, x * xUnit τ K i 1 = xUnit τ K i 1 * x)
    (hn : x * canonicalRep (coxeterSystem τ) K w₀ = canonicalRep (coxeterSystem τ) K w₀ * x) :
    x = 1 := by
  have hxB : x ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_simple_mem_posUnipotent hxC fun i => ?_
    have : x⁻¹ * xUnit τ K i 1 * x = xUnit τ K i 1 := by
      rw [mul_assoc, ← hs i]
      group
    rw [this]
    exact xUnit_mem_posUnipotent i 1
  set n := canonicalRep (coxeterSystem τ) K w₀ with hnn
  have hxn : x = n * x * n⁻¹ := by rw [← hn]; group
  have hB : x ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1]
    exact hxB
  obtain ⟨t, ht, u, hu, hxtu⟩ := hB
  have hT : n * t * n⁻¹ ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 ((canonical_weyl_root_transport τ K).2.2 w₀) t).1 ht
  have hV : n * u * n⁻¹ ∈ negUnipotent τ K := by
    rw [← map_conj_canonicalRep_longest (τ := τ) (K := K) hw₀]
    exact ⟨u, hu, rfl⟩
  have hx2 : x = (n * t * n⁻¹) * (n * u * n⁻¹) := by
    calc x = n * x * n⁻¹ := hxn
      _ = n * (t * u) * n⁻¹ := by simp only [] at hxtu; rw [hxtu]
      _ = (n * t * n⁻¹) * (n * u * n⁻¹) := by group
  have hv : (n * t * n⁻¹)⁻¹ * x ∈ borelGroup τ K ⊓ negUnipotent τ K := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (torusGroup_le_borelGroup hT)) hxB, ?_⟩
    have : (n * t * n⁻¹)⁻¹ * x = n * u * n⁻¹ := by rw [hx2]; group
    rw [this]
    exact hV
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, inv_mul_eq_one] at hv
  have hxT : x ∈ torusGroup τ K := by
    rw [← hv]
    exact hT
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
  have ha : ∀ i, (a i : K) = 1 := by
    intro i
    have h1 := (root_diagonal_conjugation τ K a).1 i 1
    have h2 : rootDiagUnit τ a * xUnit τ K i 1 * (rootDiagUnit τ a)⁻¹ = xUnit τ K i 1 := by
      rw [hs i]
      group
    rw [h2] at h1
    have := xUnit_injective i (h1.symm.trans rfl)
    simpa using this
  have : a = 1 := funext fun i => Units.ext (ha i)
  rw [this, rootDiagUnit_one]

end CFSG.SignalizerFunctorTheorem.NonLocalExc
