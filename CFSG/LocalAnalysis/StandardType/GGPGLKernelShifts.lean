module

public import CFSG.LocalAnalysis.StandardType.GGPGLBlockFrobenius
public import CFSG.Mathlib.GroupTheory.Automorphism.Translations
public import CFSG.GroupTheory.PrimeSqDvdCard

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

theorem CentralBlockModel.exists_SL_kernel_shift
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    {p : ℕ} {G : Subgroup (GL ι K)} (D : CentralBlockModel p G)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hG : IsProjElem p G) {z : GL ι K} (hz : z ∈ G) (hzp : z ^ p = 1) :
    ∃ E : SpecialLinearGroup ι K,
      SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
          (SpecialLinearGroup.toGL E)⁻¹ = z * D.primitive ∧
      ∀ y ∈ D.kernel, SpecialLinearGroup.toGL E * y = y * SpecialLinearGroup.toGL E := by
  classical
  have : Nonempty ι := ⟨D.point⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hcard : (Nat.card G : K) ≠ 0 := isProjElem_card_cast_ne_zero hp hp2 hG
  choose e hecomm hecontrol using fun b => D.exists_raw_SL_block_operator hcard b
  let k := (Nat.card K - 1) / p
  let μ := D.scalar ^ k
  have hμ : IsPrimitiveRoot μ p := D.isPrimitiveRoot_scalar_pow_card_sub_one_div hp hpK
  have hpk : p * k = Nat.card K - 1 := by
    have h := Nat.mod_add_div (Nat.card K - 1) p
    rw [Nat.mod_eq_zero_of_dvd hpK, zero_add] at h
    exact h
  have hq : Nat.card K = p * k + 1 := by have := Finite.one_lt_card (α := K); omega
  have hXq : (D.primitive : GL ι K) ^ Nat.card K =
      GeneralLinearGroup.scalar ι μ * D.primitive := by
    rw [hq, pow_add, pow_mul, pow_one, D.primitive_pow, ← map_pow]
  let v : Fin D.numBlocks → Fin D.numBlocks → Kˣ := fun b j => if b = j then μ else 1
  let δ : Fin D.numBlocks → GL ι K := fun b => D.scalarBlocks (v b)
  obtain ⟨w, hw⟩ := D.exists_blockRoot_word_of_pow_eq_one hμ hz hzp
  let γ : SpecialLinearGroup ι K →* MulAut (GL ι K) :=
    (MulAut.conj : GL ι K →* MulAut (GL ι K)).comp SpecialLinearGroup.toGL
  have hfix (b : Fin D.numBlocks) (f : Fin D.numBlocks → Kˣ) :
      γ (e b) (D.scalarBlocks f) = D.scalarBlocks f := by
    change SpecialLinearGroup.toGL (e b) * D.scalarBlocks f *
      (SpecialLinearGroup.toGL (e b))⁻¹ = D.scalarBlocks f
    rw [(hecomm b f).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hmove (b : Fin D.numBlocks) : γ (e b) D.primitive = D.primitive * δ b := by
    have h := hecontrol b D.primitive μ hXq
    have hv : (fun j => if j = b then μ else 1) = v b := by
      funext j
      simp only [v, eq_comm]
    rw [hv] at h
    exact h.trans (D.commute_scalarBlocks D.primitive.2 (v b)).eq.symm
  let l : List (MulAut (GL ι K) × GL ι K) := w.map fun b => (γ (e b), δ b)
  have hla : ∀ a ∈ l, a.1 (D.primitive : GL ι K) = D.primitive * a.2 := by
    rintro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact hmove b
  have hlf : ∀ a ∈ l, ∀ b ∈ l, a.1 b.2 = b.2 := by
    rintro a ha b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact hfix i (v j)
  let E : SpecialLinearGroup ι K := (w.map e).prod
  have hauto : (l.map Prod.fst).prod = γ E := by
    dsimp only [l, E]
    rw [map_list_prod, List.map_map, List.map_map]
    rfl
  have hinc : (l.map Prod.snd).prod = z := by
    dsimp only [l]
    rw [List.map_map]
    exact hw
  have hshift : γ E D.primitive = z * D.primitive := by
    have h := MulAut.list_prod_apply_eq_mul_prod_of_fixed l (D.primitive : GL ι K) hla hlf
    rw [hauto, hinc] at h
    exact h.trans (congrArg Subtype.val (D.commutative.is_comm.comm
      D.primitive ⟨z, hz⟩))
  have hfixed (f : Fin D.numBlocks → Kˣ) : γ E (D.scalarBlocks f) = D.scalarBlocks f := by
    have hs : γ E ∈ MulAction.stabilizer (MulAut (GL ι K)) (D.scalarBlocks f) := by
      dsimp only [E]
      rw [map_list_prod, List.map_map]
      apply Subgroup.list_prod_mem
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      change γ (e b) (D.scalarBlocks f) = D.scalarBlocks f
      exact hfix b f
    exact hs
  refine ⟨E, hshift, ?_⟩
  intro y hy
  have hyblock := D.kernel_le_blockKernelGroup hy
  change y ∈ (blockPowCoords p (D.block D.point)).map D.scalarBlocks at hyblock
  obtain ⟨f, _, hfy⟩ := Subgroup.mem_map.mp hyblock
  have hf : SpecialLinearGroup.toGL E * y * (SpecialLinearGroup.toGL E)⁻¹ = y := by
    change γ E y = y
    rw [← hfy]
    exact hfixed f
  exact (mul_inv_eq_iff_eq_mul).mp hf

end CFSG.StandardType.TypeA.PGLTor
