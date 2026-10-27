module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock

public section

namespace CFSG.StandardType.SlDvdRootGen

open Matrix CFSG.Assembly CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane
open CFSG.StandardType.TypeA CFSG.StandardType.TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem offDiag_eq_zero_of_mul_diagonal_pairVec_block
    {s : Matrix (Fin d) (Fin d) K} (hs : s.det ≠ 0) (hd : 5 ≤ d)
    {ζ : K} (hζ : ζ ≠ ζ⁻¹) {i j : Fin d} (hij : i ≠ j)
    (h : ∀ k l : Fin d, k ≠ l → k ∉ ({i, j} : Finset (Fin d)) →
      l ∉ ({i, j} : Finset (Fin d)) → ∃ c : K,
      s * diagonal (ggPairVec k l ζ) = c • (diagonal (ggPairVec k l ζ) * s)) :
    ∀ a b : Fin d, a ≠ b → ({a, b} : Finset (Fin d)) ≠ {i, j} → s a b = 0 := by
  classical
  obtain ⟨π, hπ⟩ := TypeANbrDvd.exists_perm_forall_ne_zero hs
  have hζ0 : ζ ≠ 0 := fun h0 => hζ (by rw [h0, _root_.inv_zero])
  have hζ1 : ζ ≠ 1 := fun h0 => hζ (by rw [h0, _root_.inv_one])
  have key : ∀ (k l : Fin d) (_ : k ≠ l) (c : K),
      s * diagonal (ggPairVec k l ζ) = c • (diagonal (ggPairVec k l ζ) * s) →
      c = 1 ∧ ∀ x y, s x y ≠ 0 → ggPairVec k l ζ y = c * ggPairVec k l ζ x := by
    intro k l _ c hc
    have hv : ∀ m, m ≠ k → m ≠ l → ggPairVec k l ζ m = 1 := fun m hmk hml => by
      rw [ggPairVec_apply, ite_eq_right hmk, ite_eq_right hml, mul_one]
    have hrel : ∀ x y, s x y ≠ 0 → ggPairVec k l ζ y = c * ggPairVec k l ζ x := by
      intro x y hxy
      have h1 := congrFun (congrFun hc x) y
      rw [mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h1
      apply mul_right_cancel₀ hxy
      linear_combination h1
    refine ⟨?_, hrel⟩
    obtain ⟨x, hxk, hxl, hxpk, hxpl⟩ := TypeANbrDvd.exists_ne_of_four hd k l
      (π.symm k) (π.symm l)
    have hπk : π x ≠ k := fun h' => hxpk (by rw [← h', Equiv.symm_apply_apply])
    have hπl : π x ≠ l := fun h' => hxpl (by rw [← h', Equiv.symm_apply_apply])
    have h1 := hrel (π x) x (hπ x)
    rw [hv x hxk hxl, hv (π x) hπk hπl, mul_one] at h1
    exact h1.symm
  intro a b hab hne
  by_contra hne0
  by_cases ha : a ∈ ({i, j} : Finset (Fin d))
  · by_cases hb : b ∈ ({i, j} : Finset (Fin d))
    ·
      exfalso
      apply hne
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      · rw [Finset.card_pair hij, Finset.card_pair hab]
    ·
      obtain ⟨m, hmb, hmi, hmj, -⟩ := TypeANbrDvd.exists_ne_of_four hd b i j i
      have hm : m ∉ ({i, j} : Finset (Fin d)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hmi, hmj⟩
      have ham : a ≠ m := fun h' => hm (h' ▸ ha)
      obtain ⟨c, hc⟩ := h m b hmb hm hb
      obtain ⟨hc1, hrel⟩ := key m b hmb c hc
      have h1 := hrel a b hne0
      have hva : ggPairVec m b ζ a = 1 := by
        rw [ggPairVec_apply, ite_eq_right ham, ite_eq_right hab, mul_one]
      have hvb : ggPairVec m b ζ b = ζ⁻¹ := by
        rw [ggPairVec_apply, ite_eq_right hmb.symm, ite_eq_left rfl, one_mul]
      rw [hva, hvb, hc1, one_mul] at h1
      exact hζ1 (inv_eq_one.mp h1)
  · by_cases hb : b ∈ ({i, j} : Finset (Fin d))
    ·
      obtain ⟨m, hma, hmi, hmj, -⟩ := TypeANbrDvd.exists_ne_of_four hd a i j i
      have hm : m ∉ ({i, j} : Finset (Fin d)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hmi, hmj⟩
      have hmb : m ≠ b := fun h' => hm (h' ▸ hb)
      obtain ⟨c, hc⟩ := h a m hma.symm ha hm
      obtain ⟨hc1, hrel⟩ := key a m hma.symm c hc
      have h1 := hrel a b hne0
      have hva : ggPairVec a m ζ a = ζ := by
        rw [ggPairVec_apply, ite_eq_left rfl, ite_eq_right hma.symm, mul_one]
      have hvb : ggPairVec a m ζ b = 1 := by
        rw [ggPairVec_apply, ite_eq_right hab.symm, ite_eq_right hmb.symm, mul_one]
      rw [hva, hvb, hc1, one_mul] at h1
      exact hζ1 h1.symm
    ·
      obtain ⟨c, hc⟩ := h a b hab ha hb
      obtain ⟨hc1, hrel⟩ := key a b hab c hc
      have h1 := hrel a b hne0
      have hva : ggPairVec a b ζ a = ζ := by
        rw [ggPairVec_apply, ite_eq_left rfl, ite_eq_right hab, mul_one]
      have hvb : ggPairVec a b ζ b = ζ⁻¹ := by
        rw [ggPairVec_apply, ite_eq_right hab.symm, ite_eq_left rfl, one_mul]
      rw [hva, hvb, hc1, one_mul] at h1
      exact hζ h1.symm

theorem ggHypCent_permSL_eq (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 5 ≤ d) {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t) {i j : Fin d}
    (hij : i ≠ j) :
    ggHypCent A (φ' (TypeA.permSL (Equiv.swap i j))) = (TypeA.pairCent p K i j).map φ' := by
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := K) hp hpK
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  ext l
  obtain ⟨s, rfl⟩ := hφ's l
  constructor
  · intro hl
    unfold ggHypCent at hl
    simp only [Subgroup.mem_iInf, mem_ggFix] at hl
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    unfold pairCent
    rw [Subgroup.mem_centralizer_iff]
    intro D hDmem
    obtain ⟨t, hDt, hti, -⟩ := hDmem
    refine ((commute_diagonal_iff hDt).mpr ?_).symm
    intro a b hab
    have hblock : ∀ x y : Fin d, x ≠ y → ({x, y} : Finset (Fin d)) ≠ {i, j} →
        (s : Matrix (Fin d) (Fin d) K) x y = 0 := by
      refine offDiag_eq_zero_of_mul_diagonal_pairVec_block ?_ hd hζinv hij ?_
      · rw [s.2]
        exact one_ne_zero
      · intro k l hkl hk hlJ
        have hζ0 : ζ ≠ 0 := fun h0 => hζinv (by rw [h0, _root_.inv_zero])
        have hvpow : ∀ m, ggPairVec k l ζ m ^ p = 1 := pow_ggPairVec hζ.pow_eq_one
        have hprod : ∏ m, ggPairVec k l ζ m = 1 := prod_ggPairVec ζ hζ0
        let E : SpecialLinearGroup (Fin d) K :=
          ⟨diagonal (ggPairVec k l ζ), by rw [det_diagonal]; exact hprod⟩
        have hE : (E : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l ζ) := rfl
        have hEconj : MulAut.conj (φ' E) ∈ A :=
          TypeANbrDvd.conj_mem_of_selfCent hsc hdiag hE hvpow
        have hik : i ≠ k := fun h' => hk (h' ▸ Finset.mem_insert_self i {j})
        have hil : i ≠ l := fun h' => hlJ (h' ▸ Finset.mem_insert_self i {j})
        have hjk : j ≠ k := fun h' => hk (h' ▸ (by simp : j ∈ ({i, j} : Finset (Fin d))))
        have hjl : j ≠ l := fun h' => hlJ (h' ▸ (by simp : j ∈ ({i, j} : Finset (Fin d))))
        have hvi : ggPairVec k l ζ i = 1 := by
          rw [ggPairVec_apply, ite_eq_right hik, ite_eq_right hil, mul_one]
        have hvj : ggPairVec k l ζ j = 1 := by
          rw [ggPairVec_apply, ite_eq_right hjk, ite_eq_right hjl, mul_one]
        have hcomp : ggPairVec k l ζ ∘ Equiv.swap i j = ggPairVec k l ζ := by
          funext m
          rw [Function.comp_apply]
          by_cases hmi : m = i
          · rw [hmi, Equiv.swap_apply_left, hvj, hvi]
          · by_cases hmj : m = j
            · rw [hmj, Equiv.swap_apply_right, hvi, hvj]
            · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]
        have hPEP : TypeA.permSL (Equiv.swap i j) * E *
            (TypeA.permSL (Equiv.swap i j))⁻¹ = E := by
          apply Subtype.ext
          rw [coe_permSL_conj hE (Equiv.swap i j), hcomp, hE]
        have hEP : E * TypeA.permSL (Equiv.swap i j) =
            TypeA.permSL (Equiv.swap i j) * E := by
          calc E * TypeA.permSL (Equiv.swap i j) =
              (TypeA.permSL (Equiv.swap i j) * E *
                (TypeA.permSL (Equiv.swap i j))⁻¹) * TypeA.permSL (Equiv.swap i j) := by
                rw [hPEP]
            _ = TypeA.permSL (Equiv.swap i j) * E := by group
        have hncomm : φ' (TypeA.permSL (Equiv.swap i j)) * φ' E =
            φ' E * φ' (TypeA.permSL (Equiv.swap i j)) := by
          rw [← map_mul, ← map_mul, hEP]
        have hconjcomm : MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j))) *
            MulAut.conj (φ' E) = MulAut.conj (φ' E) *
              MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j))) := by
          calc MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j))) * MulAut.conj (φ' E)
              = MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j)) * φ' E) := by
                rw [map_mul]
            _ = MulAut.conj (φ' E * φ' (TypeA.permSL (Equiv.swap i j))) := by
                rw [hncomm]
            _ = MulAut.conj (φ' E) *
                MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j))) := by
                rw [map_mul]
        have hfix : MulAut.conj (φ' E) (φ' s) = φ' s :=
          hl (MulAut.conj (φ' E)) ⟨hEconj, hconjcomm⟩
        have hEsE : φ' (E * s * E⁻¹) = φ' s := by
          rw [← hfix, MulAut.conj_apply, map_mul, map_mul, map_inv]
        have hEs : φ' (E * s) = φ' (s * E) := by
          have h := congrArg (fun x => x * φ' E) hEsE
          rw [← map_mul, ← map_mul] at h
          rw [mul_assoc (E * s) E⁻¹ E, inv_mul_cancel, mul_one] at h
          exact h
        let g : SpecialLinearGroup (Fin d) K := (E * s)⁻¹ * (s * E)
        have hg1 : φ' g = 1 := by
          change φ' ((E * s)⁻¹ * (s * E)) = 1
          rw [map_mul, map_inv, hEs, inv_mul_cancel]
        obtain ⟨c, -, hcg⟩ := mem_scalars.mp (hφker g hg1)
        refine ⟨(c : K), ?_⟩
        have h4 : E * s * g = s * E := by
          change E * s * ((E * s)⁻¹ * (s * E)) = s * E
          group
        have h5 : (E : Matrix (Fin d) (Fin d) K) * (s : Matrix (Fin d) (Fin d) K) *
            scalar (Fin d) (c : K) = (s : Matrix (Fin d) (Fin d) K) *
              (E : Matrix (Fin d) (Fin d) K) := by
          have h := congrArg (fun x : SpecialLinearGroup (Fin d) K =>
            (x : Matrix (Fin d) (Fin d) K)) h4
          simpa only [Matrix.SpecialLinearGroup.coe_mul, hcg] using h
        rw [hE] at h5
        rw [← h5, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    have hne : ({a, b} : Finset (Fin d)) ≠ {i, j} := by
      intro h
      have haJ : a ∈ ({i, j} : Finset (Fin d)) := by rw [← h]; simp
      have hbJ : b ∈ ({i, j} : Finset (Fin d)) := by rw [← h]; simp
      have hta : t a = t i := by
        rcases (by simpa using haJ : a = i ∨ a = j) with rfl | rfl
        · rfl
        · exact hti.symm
      have htb : t b = t i := by
        rcases (by simpa using hbJ : b = i ∨ b = j) with rfl | rfl
        · rfl
        · exact hti.symm
      exact hab (hta.trans htb.symm)
    have habne : a ≠ b := fun h' => hab (by rw [h'])
    exact hblock a b habne hne
  · intro hl
    unfold ggHypCent
    simp only [Subgroup.mem_iInf]
    intro a ha
    rw [mem_ggFix]
    obtain ⟨haA, hcomm⟩ := ha
    obtain ⟨s', hs', hφs'⟩ := Subgroup.mem_map.mp hl
    obtain ⟨t, hat⟩ := hdiag a haA
    have hfixa : MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j))) * a *
        (MulAut.conj (φ' (TypeA.permSL (Equiv.swap i j))))⁻¹ = a := by
      rw [hcomm]
      group
    have hat' : TypeANbrDvd.ActsDiag φ' a (t ∘ Equiv.swap i j) := by
      have h := hat.conj_perm (Equiv.swap i j)
      rwa [hfixa] at h
    obtain ⟨m, hmi, hmj⟩ := TypeANbrDvd.exists_ne_of_two (by omega : 3 ≤ d) i j
    have hti : t i = t j := by
      have hratio := hat.ratio hφker hat' (k := i) (l := m) hmi.symm
      simp only [Function.comp_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hmi hmj] at hratio
      exact mul_right_cancel₀ (inv_ne_zero (hat.ne_zero m)) hratio
    have hblock : ∀ x y : Fin d, x ≠ y → ({x, y} : Finset (Fin d)) ≠ {i, j} →
        (s' : Matrix (Fin d) (Fin d) K) x y = 0 := fun x y hxy hne =>
      TypeA.entry_eq_zero_of_mem_pairCent hp hp2 hpK (by omega) hij hxy hne hs'
    have hDcomm : diagonal t * (s' : Matrix (Fin d) (Fin d) K) =
        (s' : Matrix (Fin d) (Fin d) K) * diagonal t := by
      ext x y
      rw [mul_diagonal, diagonal_mul]
      by_cases hxy : x = y
      · subst hxy
        ring
      · by_cases hJ : ({x, y} : Finset (Fin d)) = {i, j}
        · have hxJ : x ∈ ({i, j} : Finset (Fin d)) := by rw [← hJ]; simp
          have hyJ : y ∈ ({i, j} : Finset (Fin d)) := by rw [← hJ]; simp
          have htx : t x = t i := by
            rcases (by simpa using hxJ : x = i ∨ x = j) with rfl | rfl
            · rfl
            · exact hti.symm
          have hty : t y = t i := by
            rcases (by simpa using hyJ : y = i ∨ y = j) with rfl | rfl
            · rfl
            · exact hti.symm
          rw [htx, hty]
          ring
        · rw [hblock x y hxy hJ, mul_zero, zero_mul]
    have hacts : a (φ' s') = φ' s' := by
      obtain ⟨D, hD, haD⟩ := hat
      have hDcommD : (D : Matrix (Fin d) (Fin d) K) * (s' : Matrix (Fin d) (Fin d) K) =
          (s' : Matrix (Fin d) (Fin d) K) * (D : Matrix (Fin d) (Fin d) K) := by
        rw [hD]
        exact hDcomm
      have hconj : CatalogueBHigherLinearAction.slConjugation d K D s' = s' := by
        apply Subtype.ext
        rw [coe_slConjugation, hDcommD]
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rw [haD, hconj]
    rw [← hφs']
    exact hacts

theorem isComponentOf_coordBlockSL_ggHypCent (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) {L' : Type} [Group L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ' a t) {i j : Fin d}
    (hij : i ≠ j) :
    IsComponentOf ((coordBlockSL K ({i, j} : Finset (Fin d))).map φ')
      (ggHypCent A (φ' (TypeA.permSL (Equiv.swap i j)))) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    obtain ⟨c, hc⟩ := hpK
    have hK2 : 2 ≤ Nat.card K := by
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        rw [mul_zero] at hc
        omega
      · exact h
    have hc1 : 1 ≤ c := hcpos
    have h3 : 3 ≤ p * c := calc
      3 ≤ p := hp3
      _ = p * 1 := (mul_one p).symm
      _ ≤ p * c := Nat.mul_le_mul_left p hc1
    have hK : Nat.card K = p * c + 1 := by
      rw [← hc, Nat.sub_add_cancel (by omega : 1 ≤ Nat.card K)]
    omega
  rw [ggHypCent_permSL_eq hp hp2 hpK hd hφ's hφker hsc hdiag hij]
  exact TypeA.isComponentOf_coordBlockSL_pair hp hp2 hpK h4 (by omega) hφker hij

end CFSG.StandardType.SlDvdRootGen

end
