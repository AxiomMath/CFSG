module

public import CFSG.LocalAnalysis.StandardType.GGPGLBlockFrobenius
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMove
public import CFSG.Mathlib.GroupTheory.Automorphism.Translations
public import CFSG.GroupTheory.PrimeSqDvdCard

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix
open scoped BigOperators

theorem CentralBlockModel.exists_raw_SL_block_word
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
    {p : ℕ} {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    (hcard : (Nat.card G : K) ≠ 0) (n : Fin D.numBlocks → ℕ) :
    ∃ E : SpecialLinearGroup ι K,
      (∀ f : Fin D.numBlocks → Kˣ, Commute (SpecialLinearGroup.toGL E) (D.scalarBlocks f)) ∧
      ∀ (x : G) (u : Kˣ), (x : GL ι K) ^ Nat.card K =
          GeneralLinearGroup.scalar ι u * (x : GL ι K) →
        SpecialLinearGroup.toGL E * (x : GL ι K) * (SpecialLinearGroup.toGL E)⁻¹ =
          D.scalarBlocks (fun j => u ^ n j) * (x : GL ι K) := by
  classical
  have hE := fun b => D.exists_raw_SL_block_operator hcard b
  choose E hcomm haction using hE
  let es : List (SpecialLinearGroup ι K) := List.ofFn fun b => E b ^ n b
  refine ⟨es.prod, ?_, ?_⟩
  · intro f
    apply Subgroup.mem_centralizer_singleton_iff.mp
    rw [map_list_prod]
    apply Subgroup.list_prod_mem
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp ha
    rw [map_pow]
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm b f).pow_left (n b))
  · intro x u hxq
    let δ : Fin D.numBlocks → Fin D.numBlocks → Kˣ := fun b j => if j = b then u else 1
    let l : List (MulAut (GL ι K) × GL ι K) := List.ofFn fun b =>
      (MulAut.conj (SpecialLinearGroup.toGL (E b ^ n b)), D.scalarBlocks (δ b) ^ n b)
    have hm : ∀ z ∈ l, z.1 (x : GL ι K) = (x : GL ι K) * z.2 := by
      intro z hz
      obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hz
      have ha : MulAut.conj (SpecialLinearGroup.toGL (E b)) (x : GL ι K) =
          (x : GL ι K) * D.scalarBlocks (δ b) :=
        (haction b x u hxq).trans (D.commute_scalarBlocks x.2 (δ b)).eq.symm
      have hf : MulAut.conj (SpecialLinearGroup.toGL (E b)) (D.scalarBlocks (δ b)) =
          D.scalarBlocks (δ b) := by
        change SpecialLinearGroup.toGL (E b) * D.scalarBlocks (δ b) *
          (SpecialLinearGroup.toGL (E b))⁻¹ = D.scalarBlocks (δ b)
        rw [(hcomm b (δ b)).eq, mul_assoc, mul_inv_cancel, mul_one]
      change MulAut.conj (SpecialLinearGroup.toGL (E b ^ n b)) (x : GL ι K) = _
      rw [map_pow, map_pow]
      exact MulAut.pow_apply_eq_mul_pow_of_fixed _ ha hf (n b)
    have hf : ∀ z ∈ l, ∀ w ∈ l, z.1 w.2 = w.2 := by
      intro z hz w hw
      obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hz
      obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hw
      change MulAut.conj (SpecialLinearGroup.toGL (E b ^ n b))
        (D.scalarBlocks (δ c) ^ n c) = _
      change SpecialLinearGroup.toGL (E b ^ n b) * (D.scalarBlocks (δ c) ^ n c) *
        (SpecialLinearGroup.toGL (E b ^ n b))⁻¹ = _
      rw [map_pow, ((hcomm b (δ c)).pow_pow (n b) (n c)).eq,
        mul_assoc, mul_inv_cancel, mul_one]
    have hfst : (l.map Prod.fst).prod = MulAut.conj (SpecialLinearGroup.toGL es.prod) := by
      simpa only [l, es, List.map_ofFn, Function.comp_def, MonoidHom.comp_apply] using
        (map_list_prod
          ((MulAut.conj : GL ι K →* MulAut (GL ι K)).comp SpecialLinearGroup.toGL) es).symm
    have hcoords : (List.ofFn fun b => δ b ^ n b).prod = fun j => u ^ n j := by
      rw [List.prod_ofFn]
      funext j
      simp [δ, eq_comm]
    have hsnd : (l.map Prod.snd).prod = D.scalarBlocks (fun j => u ^ n j) := by
      calc (l.map Prod.snd).prod =
          ((List.ofFn fun b => δ b ^ n b).map D.scalarBlocks).prod := by
            simp only [l, List.map_ofFn, Function.comp_def, map_pow]
        _ = D.scalarBlocks (List.ofFn fun b => δ b ^ n b).prod := (map_list_prod _ _).symm
        _ = D.scalarBlocks (fun j => u ^ n j) := congrArg D.scalarBlocks hcoords
    have h := MulAut.list_prod_apply_eq_mul_prod_of_fixed l (x : GL ι K) hm hf
    rw [hfst, hsnd, MulAut.conj_apply] at h
    exact h.trans (D.commute_scalarBlocks x.2 _).eq

theorem CentralBlockModel.exists_SL_projected_kernel_word
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {p : ℕ} {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hG : IsProjElem p G)
    (hcard : (Nat.card G : K) ≠ 0)
    {H : Type*} [Group H] (c : GL ι K →* H)
    (hc : ∀ u : Kˣ, c (GeneralLinearGroup.scalar ι u) = 1)
    {y : GL ι K} (hy : y ∈ D.kernel) :
    ∃ (E : SpecialLinearGroup ι K) (δ : GL ι K),
      δ ∈ D.kernel ∧ δ ^ p = 1 ∧ c δ = c y ∧
      (∀ z ∈ D.kernel, Commute (SpecialLinearGroup.toGL E) z) ∧
      SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
          (SpecialLinearGroup.toGL E)⁻¹ = δ * (D.primitive : GL ι K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let ζ := D.scalar ^ ((Nat.card K - 1) / p)
  have hζp : ζ ^ p = 1 := by
    change (D.scalar ^ ((Nat.card K - 1) / p)) ^ p = 1
    rw [← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hpK]
    simpa only [Nat.card_units] using pow_card_eq_one' (x := D.scalar)
  have hζne : ζ ≠ 1 := by
    intro heq
    have hdiv : p ∣ Nat.card Kˣ := by simpa only [Nat.card_units] using hpK
    obtain ⟨u, hu⟩ := IsCyclic.exists_pow_eq_of_pow_card_div_eq_one hp.pos hdiv
      (u := D.scalar) (by simpa only [Nat.card_units] using heq)
    exact D.scalar_not_pow u hu
  have hζ : IsPrimitiveRoot ζ p := by
    simpa only [orderOf_eq_prime hζp hζne] using IsPrimitiveRoot.orderOf ζ
  obtain ⟨f, -, hfp, hfker, hfimage⟩ := D.exists_normalized_kernel_coords hG c hc
    (D.block D.point) hy
  have he : ∀ j, ∃ m < p, ζ ^ m = f j :=
    fun j => QuotMove.exists_pow_eq_units hζ (hfp j)
  choose n hn hnf using he
  have hnfun : (fun j => ζ ^ n j) = f := funext hnf
  obtain ⟨E, hEcomm, hEaction⟩ := D.exists_raw_SL_block_word hcard n
  have hq : Nat.card K = p * ((Nat.card K - 1) / p) + 1 := by
    rw [Nat.mul_div_cancel' hpK, Nat.sub_add_cancel]
    exact le_of_lt (Finite.one_lt_card (α := K))
  have hxq : (D.primitive : GL ι K) ^ Nat.card K =
      GeneralLinearGroup.scalar ι ζ * (D.primitive : GL ι K) := by
    rw [hq, pow_succ, pow_mul, D.primitive_pow, ← map_pow]
  refine ⟨E, D.scalarBlocks f, hfker, ?_, hfimage, ?_, ?_⟩
  · have hfp' : f ^ p = 1 := funext hfp
    rw [← map_pow, hfp', map_one]
  · intro z hz
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp (D.kernel_le_blockKernelGroup hz)
    exact hEcomm g
  · simpa only [hnfun] using hEaction D.primitive ζ hxq

end CFSG.StandardType.TypeA.PGLTor
