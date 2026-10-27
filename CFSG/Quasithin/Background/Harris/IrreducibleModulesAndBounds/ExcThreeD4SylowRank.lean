module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4SylowKey

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

namespace D4Syl

variable {K : Type} [Field K] {σ : K ≃+* K} {k : Subfield K} {P : Type} [Group P]
  (D : D4Syl K σ k P) [Finite K] [Finite P]

include D in
theorem card_elemAbelian_le (hK3 : Nat.card K = Nat.card k ^ 3) (E : Subgroup P)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * Nat.card k ^ 5 := by
  classical
  let φ : E →* Multiplicative K := D.π1hom.comp E.subtype
  have hφ := Subgroup.card_ker_mul_card_range φ
  let S : AddSubgroup K := Subgroup.toAddSubgroup φ.range
  let E0 : Subgroup P := E ⊓ D.N
  let χ : E0 →* Multiplicative (k × K × K × k) :=
    MonoidHom.mk' (fun n => Multiplicative.ofAdd (D.ρf n.1)) fun n n' => by
      rw [Subgroup.coe_mul, D.ρf_mul n.2.2 n'.2.2]; rfl
  have hχ := Subgroup.card_ker_mul_card_range χ
  let W : AddSubgroup (k × K × K × k) := Subgroup.toAddSubgroup χ.range
  have hkerφ : Nat.card φ.ker ≤ Nat.card E0 := by
    refine Nat.card_le_card_of_injective
      (fun e : φ.ker => (⟨e.1.1, e.1.2, D.mem_N_of_π1f (by
        have := e.2
        rw [MonoidHom.mem_ker] at this
        have h := congrArg Multiplicative.toAdd this
        simpa [φ, π1hom] using h)⟩ : E0)) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hkerχ : Nat.card χ.ker ≤ Nat.card k := by
    refine Nat.card_le_card_of_injective (fun n : χ.ker => D.c6f n.1.1) ?_
    intro x y hxy
    have hx : D.ρf x.1.1 = 0 := by
      have := x.2
      rw [MonoidHom.mem_ker] at this
      simpa [χ] using congrArg Multiplicative.toAdd this
    have hy : D.ρf y.1.1 = 0 := by
      have := y.2
      rw [MonoidHom.mem_ker] at this
      simpa [χ] using congrArg Multiplicative.toAdd this
    obtain ⟨b, u, v, e, g, hnx⟩ := D.mem_N_iff.1 x.1.2.2
    obtain ⟨b', u', v', e', g', hny⟩ := D.mem_N_iff.1 y.1.2.2
    have hxz : x.1.1 = D.nf 0 0 0 0 (D.c6f x.1.1) := by
      rw [hnx] at hx ⊢
      rw [D.ρf_nf] at hx
      simp only [Prod.mk_eq_zero] at hx
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      rw [D.c6f_nf]
    have hyz : y.1.1 = D.nf 0 0 0 0 (D.c6f y.1.1) := by
      rw [hny] at hy ⊢
      rw [D.ρf_nf] at hy
      simp only [Prod.mk_eq_zero] at hy
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hy
      rw [D.c6f_nf]
    apply Subtype.ext
    apply Subtype.ext
    rw [hxz, hyz]
    simp only at hxy
    rw [hxy]
  have hfix : ∀ s ∈ S, ∀ w ∈ W, D.Mfun s w = w := by
    intro s hs w hw
    obtain ⟨e, he⟩ : ∃ e : E, φ e = Multiplicative.ofAdd s := hs
    obtain ⟨n, hn⟩ : ∃ n : E0, χ n = Multiplicative.ofAdd w := hw
    have hs' : D.π1f e.1 = s := by
      have := congrArg Multiplicative.toAdd he
      simpa [φ, π1hom] using this
    have hw' : D.ρf n.1 = w := by
      have := congrArg Multiplicative.toAdd hn
      simpa [χ] using this
    have hcomm : e.1 * n.1 = n.1 * e.1 := hc _ e.2 _ n.2.1
    have h1 : e.1 * n.1 * e.1⁻¹ = n.1 := by rw [hcomm]; group
    have h3 := D.ρf_conj_gen (g := e.1) n.2.2
    rw [h1, hs', hw'] at h3
    exact h3.symm
  have hiso : ∀ w ∈ W, ∀ w' ∈ W, D.omega w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨n, hn⟩ : ∃ n : E0, χ n = Multiplicative.ofAdd w := hw
    obtain ⟨n', hn'⟩ : ∃ n : E0, χ n = Multiplicative.ofAdd w' := hw'
    have hw1 : D.ρf n.1 = w := by
      have := congrArg Multiplicative.toAdd hn
      simpa [χ] using this
    have hw2 : D.ρf n'.1 = w' := by
      have := congrArg Multiplicative.toAdd hn'
      simpa [χ] using this
    have hcomm : n.1 * n'.1 = n'.1 * n.1 := hc _ n.2.1 _ n'.2.1
    have hA := D.c6f_mul n.2.2 n'.2.2
    have hB := D.c6f_mul n'.2.2 n.2.2
    have hEq : D.c6f (n.1 * n'.1) = D.c6f (n'.1 * n.1) := by rw [hcomm]
    rw [hA, hB, hw1, hw2] at hEq
    unfold omega
    rw [D.Tr_add]
    have h4 := D.add_self_k (w'.1 * w.2.2.2 + D.Tr (w'.2.1 * w.2.2.1))
    linear_combination (-1 : k) * hEq + h4
  have hS : Nat.card S = Nat.card φ.range := rfl
  have hW : Nat.card W = Nat.card χ.range := rfl
  have hkey := D.key_card hK3 S W hfix hiso
  rw [hS, hW] at hkey
  have hq : 0 ≤ Nat.card k := Nat.zero_le _
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hφ.symm
    _ ≤ Nat.card E0 * Nat.card φ.range := Nat.mul_le_mul_right _ hkerφ
    _ = (Nat.card χ.ker * Nat.card χ.range) * Nat.card φ.range := by rw [hχ]
    _ ≤ (Nat.card k * Nat.card χ.range) * Nat.card φ.range :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hkerχ)
    _ = Nat.card k * (Nat.card φ.range * Nat.card χ.range) := by ring
    _ ≤ Nat.card k * (2 * Nat.card k ^ 4) := Nat.mul_le_mul_left _ hkey
    _ = 2 * Nat.card k ^ 5 := by ring

end D4Syl

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
