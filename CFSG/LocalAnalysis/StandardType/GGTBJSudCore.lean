module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

private lemma ggTBJsudC_ratio_inv_eq {K : Type} [Field K] {d : ℕ} {ta tb : Fin d → K}
    {i i₀ : Fin d} (hb : tb i ≠ 0) (hb₀ : tb i₀ ≠ 0) (ha₀ : ta i₀ ≠ 0)
    (h : ta i * (ta i₀)⁻¹ = tb i * (tb i₀)⁻¹) :
    (tb i)⁻¹ * ta i = (tb i₀)⁻¹ * ta i₀ := by
  field_simp at h
  field_simp
  linear_combination h

theorem ggTBJ_sud_count {K : Type} [Field K] {n d p : ℕ} (hK : UnitaryFieldData 2 n K)
    (hd : 3 ≤ d) (hp : p.Prime) {L' : Type} [Group L'] [Finite L']
    {φ : ↥(unitarySU 2 n K d) →* L'}
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t)
    (hAp : ∀ a ∈ A, a ^ p = 1) (I : Finset (Fin d)) {C : Subgroup (MulAut L')}
    (hC : ∀ a ∈ A, ∀ t : Fin d → K, LineU.ActsDiagU φ a t →
      (∀ i ∈ I, ∀ j ∈ I, t i = t j) → a ∈ C) :
    Nat.card ↥A ≤ p ^ (I.card - 1) * Nat.card ↥(A ⊓ C) := by
  classical
  haveI hKfin : Finite K := hK.finite
  haveI hMAfin : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
  · have hsub : A ≤ C := by
      intro a ha
      obtain ⟨t, ht⟩ := hdiag a ha
      refine hC a ha t ht (fun i hi => ?_)
      rw [hI] at hi
      exact absurd hi (Finset.notMem_empty i)
    rw [inf_eq_left.mpr hsub, hI]
    simp
  · haveI : Nonempty ↥A := ⟨1, A.one_mem⟩
    let t : ↥A → Fin d → K := fun a => (hdiag (a : MulAut L') a.2).choose
    have ht : ∀ a : ↥A, LineU.ActsDiagU φ (a : MulAut L') (t a) := fun a =>
      (hdiag (a : MulAut L') a.2).choose_spec
    let w : ↥A → ↥(I.erase i₀) → rootsOfUnity p K := fun a i =>
      ⟨Units.mk0 (t a i.1 * (t a i₀)⁻¹)
          (mul_ne_zero ((ht a).ne_zero i.1) (inv_ne_zero ((ht a).ne_zero i₀))), by
        rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
          Units.val_mk0]
        exact LineU.ActsDiagU.ratio_pow hK hd hφker (ht a) (hAp (a : MulAut L') a.2) i.1 i₀⟩
    let s : (↥(I.erase i₀) → rootsOfUnity p K) → ↥A := Function.invFun w
    have hs : ∀ a : ↥A, w (s (w a)) = w a := fun a => Function.invFun_eq ⟨a, rfl⟩
    have key : ∀ a b : ↥A, w b = w a → (((b⁻¹ * a : ↥A)) : MulAut L') ∈ C := by
      intro a b hba
      have hratio : ∀ i : ↥(I.erase i₀),
          t b i.1 * (t b i₀)⁻¹ = t a i.1 * (t a i₀)⁻¹ := by
        intro i
        have h := congrArg (fun z : rootsOfUnity p K => ((z : Kˣ) : K)) (congrFun hba i)
        simpa [w, Units.val_mk0] using h
      have hu : LineU.ActsDiagU φ (((b⁻¹ * a : ↥A)) : MulAut L')
          (fun k => (t b k)⁻¹ * t a k) :=
        (ht b).inv.mul (ht a)
      refine hC _ (A.mul_mem (A.inv_mem b.2) a.2) _ hu ?_
      intro i hi j hj
      have hstep : ∀ k ∈ I, (t b k)⁻¹ * t a k = (t b i₀)⁻¹ * t a i₀ := by
        intro k hk
        by_cases hk0 : k = i₀
        · rw [hk0]
        · exact ggTBJsudC_ratio_inv_eq ((ht b).ne_zero k) ((ht b).ne_zero i₀)
            ((ht a).ne_zero i₀)
            (hratio ⟨k, Finset.mem_erase_of_ne_of_mem hk0 hk⟩).symm
      exact (hstep i hi).trans (hstep j hj).symm
    let G : ↥A → (↥(I.erase i₀) → rootsOfUnity p K) × ↥(A ⊓ C) := fun a =>
      (w a, ⟨(((s (w a))⁻¹ * a : ↥A) : MulAut L'),
        Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem (s (w a)).2) a.2,
          key a (s (w a)) (hs a)⟩⟩)
    have hinj : Function.Injective G := by
      intro a b hab
      have h1 : w a = w b := congrArg Prod.fst hab
      have h2 : (((s (w a))⁻¹ * a : ↥A) : MulAut L') =
          (((s (w b))⁻¹ * b : ↥A) : MulAut L') :=
        congrArg (fun z : ↥(A ⊓ C) => (z : MulAut L')) (congrArg Prod.snd hab)
      rw [h1] at h2
      exact Subtype.ext (mul_left_cancel h2)
    have hfun : Nat.card (↥(I.erase i₀) → rootsOfUnity p K) ≤ p ^ (I.card - 1) := by
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hroot : Nat.card (rootsOfUnity p K) ≤ p := card_rootsOfUnity K p
      have hι : Nat.card ↥(I.erase i₀) = I.card - 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_erase_of_mem hi₀]
      calc Nat.card (↥(I.erase i₀) → rootsOfUnity p K)
          = Nat.card (rootsOfUnity p K) ^ Nat.card ↥(I.erase i₀) := Nat.card_fun
        _ = Nat.card (rootsOfUnity p K) ^ (I.card - 1) := by rw [hι]
        _ ≤ p ^ (I.card - 1) := Nat.pow_le_pow_left hroot _
    calc Nat.card ↥A ≤ Nat.card ((↥(I.erase i₀) → rootsOfUnity p K) × ↥(A ⊓ C)) :=
          Nat.card_le_card_of_injective G hinj
      _ = Nat.card (↥(I.erase i₀) → rootsOfUnity p K) * Nat.card ↥(A ⊓ C) :=
          Nat.card_prod _ _
      _ ≤ p ^ (I.card - 1) * Nat.card ↥(A ⊓ C) := Nat.mul_le_mul_right _ hfun

theorem ggTBJ_sud_noncomm {K : Type} [Field K] {n d p : ℕ} (hK : UnitaryFieldData 2 n K)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d) {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L')} (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t)
    (hAp : ∀ a ∈ A, a ^ p = 1) (hsc : GGTorusSelfCent p A)
    {a b c : Fin d} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h₁ : MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b))) ∈
      Subgroup.normalizer (A : Set (MulAut L')))
    (h₂ : MulAut.conj (φ (LineU.permSU hK (Equiv.swap b c))) ∈
      Subgroup.normalizer (A : Set (MulAut L'))) :
    ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  intro hcomm
  let g₁ : MulAut L' := MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b)))
  let g₂ : MulAut L' := MulAut.conj (φ (LineU.permSU hK (Equiv.swap b c)))
  let g₃ : MulAut L' := MulAut.conj (φ (LineU.permSU hK (Equiv.swap a c)))
  have hswap : Equiv.swap a b * Equiv.swap b c * Equiv.swap a b = Equiv.swap a c := by
    have h := Equiv.swap_mul_swap_mul_swap (x := c) (y := b) (z := a)
      (Ne.symm hbc) (Ne.symm hac)
    rw [Equiv.swap_comm b a, Equiv.swap_comm c b] at h
    exact h
  have hPP : LineU.permSU hK (Equiv.swap a c) =
      LineU.permSU hK (Equiv.swap a b) * LineU.permSU hK (Equiv.swap b c) *
        LineU.permSU hK (Equiv.swap a b) := by
    rw [← UnitAct.permSU_mul, ← UnitAct.permSU_mul, hswap]
  have hφP : φ (LineU.permSU hK (Equiv.swap a c)) =
      φ (LineU.permSU hK (Equiv.swap a b)) * φ (LineU.permSU hK (Equiv.swap b c)) *
        φ (LineU.permSU hK (Equiv.swap a b)) := by
    rw [hPP, map_mul, map_mul]
  have hPab2 : LineU.permSU hK (Equiv.swap a b) *
      LineU.permSU hK (Equiv.swap a b) = 1 := by
    rw [← UnitAct.permSU_mul, Equiv.swap_mul_self, UnitAct.permSU_one]
  have hφPab2 : φ (LineU.permSU hK (Equiv.swap a b)) *
      φ (LineU.permSU hK (Equiv.swap a b)) = 1 := by
    rw [← map_mul, hPab2, map_one]
  have hg₁sq : g₁ * g₁ = 1 := by
    show MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b))) *
      MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b))) = 1
    rw [← map_mul, hφPab2, map_one]
  have hg₁inv : g₁⁻¹ = g₁ := by
    show (MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b))))⁻¹ = _
    exact inv_eq_of_mul_eq_one_right hg₁sq
  have hg : g₃ = g₁ * g₂ * g₁⁻¹ := by
    show MulAut.conj (φ (LineU.permSU hK (Equiv.swap a c))) =
      MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b))) *
        MulAut.conj (φ (LineU.permSU hK (Equiv.swap b c))) *
        (MulAut.conj (φ (LineU.permSU hK (Equiv.swap a b))))⁻¹
    rw [hφP, map_mul, map_mul, hg₁inv]
  have h₃ : MulAut.conj (φ (LineU.permSU hK (Equiv.swap a c))) ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
    SuDvdRootGen.conj_permSU_mem_normalizer hK hpq (by omega) hφs hφker hdiag hAp hsc _
  have heq : ggConjAut A h₃ = ggConjAut A h₂ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    let c' : ↥A := (ggConjAut A h₁)⁻¹ b
    have hc' : ggConjAut A h₁ c' = b := MulAut.apply_inv_self ↥A (ggConjAut A h₁) b
    have hc1 : g₁ * (c' : MulAut L') * g₁⁻¹ = (b : MulAut L') := by
      have h := congrArg (fun x : ↥A => (x : MulAut L')) hc'
      rw [ggConjAut_apply] at h
      exact h
    have hcc := DFunLike.congr_fun hcomm c'
    have hcc' : g₁ * (g₂ * (c' : MulAut L') * g₂⁻¹) * g₁⁻¹ =
        g₂ * (g₁ * (c' : MulAut L') * g₁⁻¹) * g₂⁻¹ := by
      have h := congrArg (fun x : ↥A => (x : MulAut L')) hcc
      simp only [MulAut.mul_apply, ggConjAut_apply] at h
      exact h
    rw [ggConjAut_apply, ggConjAut_apply]
    change g₃ * (b : MulAut L') * g₃⁻¹ = g₂ * (b : MulAut L') * g₂⁻¹
    rw [hg]
    calc (g₁ * g₂ * g₁⁻¹) * (b : MulAut L') * (g₁ * g₂ * g₁⁻¹)⁻¹
        = g₁ * (g₂ * (c' : MulAut L') * g₂⁻¹) * g₁⁻¹ := by rw [← hc1]; group
      _ = g₂ * (g₁ * (c' : MulAut L') * g₁⁻¹) * g₂⁻¹ := hcc'
      _ = g₂ * (b : MulAut L') * g₂⁻¹ := by rw [hc1]
  have hpair := SuDvdRootGen.pair_eq_of_ggConjAut_eq_permSU (i := a) (j := c) (k := b) (l := c)
    hK hp hpq hd hφs hφker hdiag hsc hac hbc h₃ h₂ heq
  have hm : a ∈ ({b, c} : Finset (Fin d)) := by
    rw [← hpair]
    exact Finset.mem_insert_self a {c}
  rw [Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.elim hab hac

end CFSG.StandardType

end
