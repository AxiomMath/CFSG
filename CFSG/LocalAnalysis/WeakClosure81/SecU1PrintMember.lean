module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
import CFSG.LocalAnalysis.WeakClosure81.InCalEOneMembers
import CFSG.Quasithin.Vol2.Ch11SecU1Main
import CFSG.Goldschmidt.Steps.G52
import CFSG.LocalAnalysis.WeakClosure81.SecU1ElemAbelianPair
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.Vol2.Ch11SecU1Aux

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.Vol2.Ch11.SecU1
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

theorem exists_inCalEi_not_le_centralizer_of_oddTorus {L : Subgroup G}
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {z b : G} (hzA : z ∈ A) (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hbA : b ∈ A) (hzb : z ≠ b) (hb : SecU1.OddTorus L b) {i : ℕ}
    (hi : 1 ≤ i) :
    ∃ K : Subgroup G, InCalEi i T A K ∧ ¬ K ≤ Subgroup.centralizer {z} := by
  obtain ⟨P, -, hPp, hP2, hPn, hPc⟩ := hb
  have hzc : z ∈ L ⊓ Subgroup.centralizer {b} :=
    ⟨hzL, le_centralizer_of_isElemAbelian hA hbA hzA⟩
  have hPz := hPc z hzc hz2 hzb
  have hτP : tA T A ≤ Subgroup.normalizer (P : Set G) :=
    (tauOf_le_centralizer hO2 hbA).trans hPn
  have hP : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by simp)
  have hcyc : IsCyclic ↥P := by
    have : Fact (Nat.card P).Prime := ⟨hPp⟩
    exact isCyclic_of_prime_card (p := Nat.card P) rfl
  refine ⟨P ⊔ tA T A, ?_, fun hle => hPz (le_sup_left.trans hle)⟩
  exact inCalEi_sup_tA_of_isCyclic hPp hP2 hT hAT hA hi hP hcyc hτP ⟨z, hzA, hPz⟩

theorem exists_inCalEi_not_le_centralizer_of_sigmaFacts {L : Subgroup G} (h : SecU1.Setting L)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {v b z : G} (hvA : v ∈ A) (hvL : v ∈ L) (hv1 : v ≠ 1)
    (hbA : b ∈ A) (hA4 : ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.centralizer {b}) (Subgroup.centralizer {b}))
    (hb : SecU1.SigmaFacts L b) (hzL : z ∈ L) (hz2 : orderOf z = 2) {i : ℕ} (hi : 1 ≤ i) :
    ∃ K : Subgroup G, InCalEi i T A K ∧ ¬ K ≤ Subgroup.centralizer {z} := by
  obtain ⟨L₀, hle, hs, hnab, hnorm, hcent⟩ := hb
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hL₀C : L₀ ≤ C := hle.trans inf_le_right
  have hSyl₀ : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    have h1 := B6.isSylowTwoOf_inf_normal hSyl hL₀C hnorm
    rwa [inf_assoc, inf_eq_right.mpr hL₀C] at h1
  have hbc : b ∈ Subgroup.centralizer (L₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL₀C hl)
  have hvc : v ∉ Subgroup.centralizer (L₀ : Set G) := fun hv => hv1 (by
    have h1 : v ∈ L ⊓ Subgroup.centralizer (L₀ : Set G) := ⟨hvL, hv⟩
    rw [hcent] at h1
    exact Subgroup.mem_bot.mp h1)
  have hcomm : v * b = b * v := hA.comm hvA hbA
  have hvv : v * v = 1 := hA.mul_self_eq_one hvA
  have hrel : (A ⊓ Subgroup.centralizer (L₀ : Set G)).relIndex A = 2 := by
    refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
      ⟨v, hvA, fun hv => hvc hv.2, fun x hx => ?_⟩
    rcases hA4 x hx with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨A.one_mem, Subgroup.one_mem _⟩
    · exact Or.inl ⟨A.mul_mem hvA hvA, by rw [hvv]; exact Subgroup.one_mem _⟩
    · exact Or.inr ⟨hbA, hbc⟩
    · refine Or.inl ⟨A.mul_mem (A.mul_mem hvA hbA) hvA, ?_⟩
      rw [mul_assoc, ← hcomm, ← mul_assoc, hvv, one_mul]
      exact hbc
  have hτ : tA T A ≤ Subgroup.normalizer (L₀ : Set G) :=
    (tauOf_le_centralizer hO2 hbA).trans hnorm
  refine ⟨L₀ ⊔ tA T A,
    inCalEi_sup_tA_of_isSimpleGroup hT hAT hA hi hs hnab hτ hSyl₀ hrel, fun hK => ?_⟩
  have hL₀z : L₀ ≤ L ⊓ Subgroup.centralizer {z} :=
    le_inf (hle.trans inf_le_left) (le_sup_left.trans hK)
  have := h.inner_solvable z hzL hz2
  have : Group.IsSolvable ↥L₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hL₀z)
  exact not_isSolvable_of_simple hnab this

theorem exists_conj_inCalEi_not_le_centralizer {L : Subgroup G} (h : SecU1.Setting L)
    {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {z : G}
    (hzL : z ∈ L) (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {i : ℕ} (hi : 1 ≤ i) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, InCalEi i T (A1b.conjSub g A) K ∧
      ¬ K ≤ Subgroup.centralizer {z} := by
  have hLn := h.almostSimple.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ x ∈ A, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    CFSG.Goldschmidt.G52.orderOf_eq_two_of_mem hA hx hx1
  have hz1 : z ≠ 1 := fun h => by
    rw [← orderOf_eq_one_iff] at h
    omega
  by_cases hI : ∃ x ∈ A, x ∈ L ∧ x ≠ 1 ∧ ∃ y ∈ A, y ∈ L ∧ y ≠ 1 ∧ x ≠ y
  ·
    obtain ⟨x, hxA, hxL, hx1, y, hyA, hyL, hy1, hxy⟩ := hI
    obtain ⟨l, -, hl⟩ := h.inner_conj x hxL z hzL (hord x hxA hx1) hz2
    obtain ⟨g, hgT, hgx⟩ := exists_conj_le_eq hT hzT hA hxA hl
    have hzA : z ∈ A1b.conjSub g A := hgx ▸ mem_conjSub_of_mem hxA
    have hy2 : orderOf (g * y * g⁻¹) = 2 := by rw [orderOf_conj']; exact hord y hyA hy1
    have hzy : z ≠ g * y * g⁻¹ := fun he => hxy (conj_injective (hgx.trans he))
    obtain ⟨K, hK, hKz⟩ := exists_inCalEi_not_le_centralizer_of_oddTorus hO2 hT hgT
      (isElemAbelian_conjSub hA g) hzA hzL hz2 (mem_conjSub_of_mem hyA) hzy
      (h.inner_torus _ (hLn.conj_mem y hyL g) hy2) hi
    exact ⟨g, hgT, K, hK, hKz⟩
  push Not at hI
  obtain ⟨v, b, hvA, hvL, hv1, hbA, hbL, hA4'⟩ :=
    exists_generators_of_not_two_involutions h hA hA4 hI
  have hne1 : ∀ x ∈ A, x ∉ L → x ≠ 1 := fun x _ hxL hx => hxL (hx ▸ L.one_mem)
  obtain ⟨l, -, hl⟩ := h.inner_conj v hvL z hzL (hord v hvA hv1) hz2
  obtain ⟨g, hgT, hgv⟩ := exists_conj_le_eq hT hzT hA hvA hl
  have hzA : z ∈ A1b.conjSub g A := hgv ▸ mem_conjSub_of_mem hvA
  have hb₃L : g * b * g⁻¹ ∉ L := fun hm => hbL (by
    have := hLn.conj_mem _ hm g⁻¹
    simpa [mul_assoc] using this)
  have hb₃2 : orderOf (g * b * g⁻¹) = 2 := by rw [orderOf_conj']; exact hord b hbA (hne1 b hbA hbL)
  have hA' := isElemAbelian_conjSub hA g
  rcases h.outer _ hb₃L hb₃2 with hδ | hσ
  · obtain ⟨K, hK, hKz⟩ := exists_inCalEi_not_le_centralizer_of_oddTorus hO2 hT hgT hA' hzA hzL hz2
      (mem_conjSub_of_mem hbA) (fun e => hb₃L (e ▸ hzL)) hδ hi
    exact ⟨g, hgT, K, hK, hKz⟩
  obtain ⟨k, hkT, hkSyl⟩ := exists_conj_le_sylow hT hA' (mem_conjSub_of_mem hbA)
  have hz1' : k * z * k⁻¹ ≠ 1 := fun e => hz1 (conj_eq_one_iff.mp e)
  have hA4'' : ∀ x ∈ A1b.conjSub k (A1b.conjSub g A),
      x = 1 ∨ x = k * z * k⁻¹ ∨ x = k * (g * b * g⁻¹) * k⁻¹ ∨
        x = (k * z * k⁻¹) * (k * (g * b * g⁻¹) * k⁻¹) := by
    intro x hx
    rw [A1b.mem_conjSub_iff, A1b.mem_conjSub_iff] at hx
    have hxe : x = k * g * (g⁻¹ * (k⁻¹ * x * k) * g) * (k * g)⁻¹ := by group
    rcases hA4' _ hx with h1 | h1 | h1 | h1 <;> rw [h1] at hxe
    · exact Or.inl (by rw [hxe]; group)
    · refine Or.inr (Or.inl ?_)
      rw [hxe, ← hgv]
      group
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [hxe]
      group
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hxe, ← hgv]
      group
  obtain ⟨K, hK, hKz⟩ := exists_inCalEi_not_le_centralizer_of_sigmaFacts h hO2 hT hkT
    (isElemAbelian_conjSub hA' k) (mem_conjSub_of_mem hzA) (hLn.conj_mem z hzL k) hz1'
    (mem_conjSub_of_mem (mem_conjSub_of_mem hbA)) hA4'' hkSyl (hσ.conj hLn k) hzL hz2 hi
  refine ⟨k * g, ?_, K, ?_, hKz⟩
  · rw [A1b.conjSub_mul]; exact hkT
  · rw [A1b.conjSub_mul]; exact hK

end CFSG.LocalAnalysis.WeakClosure81
