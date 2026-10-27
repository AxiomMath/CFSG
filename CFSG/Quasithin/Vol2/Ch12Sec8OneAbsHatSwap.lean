module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatSwap
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsMod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

omit [Finite G] in
theorem rconj_congr_of_eq_one_or {X : Subgroup G} {z : G} (hzX : z ∈ X)
    (hall : ∀ w ∈ X, w = 1 ∨ w = z) {s₁ s₂ : G} (h : s₁⁻¹ * z * s₁ = s₂⁻¹ * z * s₂) :
    rconj X s₁ = rconj X s₂ := by
  have key : ∀ a b : G, a⁻¹ * z * a = b⁻¹ * z * b → ∀ y ∈ rconj X a, y ∈ rconj X b := by
    intro a b hab y hy
    rw [mem_rconj] at hy ⊢
    rcases hall _ hy with h1 | h1
    · have hy1 : y = 1 := by
        calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
      rw [hy1]
      simp
    · have hy' : y = a⁻¹ * z * a := by
        calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
          _ = a⁻¹ * z * a := by rw [h1]
      rw [hy', hab]
      have e : b * (b⁻¹ * z * b) * b⁻¹ = z := by group
      rw [e]
      exact hzX
  ext y
  exact ⟨key s₁ s₂ h y, key s₂ s₁ h.symm y⟩

omit [Finite G] in
theorem rconj_uA_eq (S : Setting V V₁ L T) {s : G} (hs : s ∈ Subgroup.normalizer (V : Set G)) :
    rconj (uA V V₁) s = conjClosure V (Subgroup.centralizer (rconj V₁ s : Set G)) := by
  show rconj (conjClosure V (Subgroup.normalizer (V₁ : Set G))) s = _
  rw [S.normalizer_eq_centralizer, rconj_conjClosure_eq, rconj_eq_of_mem_normalizer hs,
    rconj_centralizer_eq]

omit [Finite G] in
theorem rconj_wA_eq_of_mem_normalizer (S : Setting V V₁ L T) {s : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G)) :
    rconj (wA V V₁) s =
      conjClosure V (Subgroup.centralizer (rconj V₁ s : Set G)) ⊓
        Subgroup.centralizer (V : Set G) := by
  show rconj (uA V V₁ ⊓ Subgroup.centralizer (V : Set G)) s = _
  rw [rconj_inf_eq, S.rconj_uA_eq hs, rconj_centralizer_eq, rconj_eq_of_mem_normalizer hs]


theorem exists_swap (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) :
    ∃ t : G, t ∈ Subgroup.normalizer (V : Set G) ∧ t ∈ L ⊔ uA V V₁ ∧
      rconj (V₁) t⁻¹ = rconj (V₁) g ∧
      rconj (wA V V₁) t⁻¹ = rconj (wA V V₁) g ∧
      rconj (rconj (wA V V₁) g) t⁻¹ = wA V V₁ := by
  classical
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  have hzV : z ∈ V := S.V₁_le hzZ
  have hzz : z * z = 1 := by
    simpa [sq] using S.base.sq_eq_one_of_mem_V hzV
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzc : ∀ u ∈ uA V V₁, z * u = u * z := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (S.V₁_le_centerOf hzZ).2 u hu).symm
  have hgN : g ∈ Subgroup.normalizer (V : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans S.LT_le_normalizer_V) hg.mem
  obtain ⟨z', hz'def⟩ : ∃ z', z' = g⁻¹ * z * g := ⟨_, rfl⟩
  have hz'V : z' ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z).mp hzV
    rw [hz'def]
    simpa using this
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hz1
    have : z = g * z' * g⁻¹ := by rw [hz'def]; group
    rw [this, h1]
    group
  have hz'nZ : z' ∉ V₁ := by
    intro hz'Z
    rcases hall _ hz'Z with h1 | h1
    · exact hz'1 h1
    · apply hg.not_mem
      rw [S.normalizer_eq_centralizer, Subgroup.mem_centralizer_iff]
      intro w hw
      rcases hall w hw with h2 | h2
      · rw [h2]
        simp
      · rw [h2]
        have h3 : g⁻¹ * z * g = z := by rw [← hz'def]; exact h1
        calc z * g = g * (g⁻¹ * z * g) := by group
          _ = g * z := by rw [h3]
  have hcases := S.V_cases hzZ hz1 hz'V hz'nZ
  have hgz' : g * z' * g⁻¹ = z := by rw [hz'def]; group
  have hg3 : g ^ 3 ∈ Subgroup.centralizer (V : Set G) :=
    S.pCoreOf_LT_le_centralizer (S.pow_three_mem_pCoreOf_LT hg.mem)
  have hyV : g⁻¹ * z' * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z').mp hz'V
    simpa using this
  have hy : g⁻¹ * z' * g = z * z' := by
    rcases hcases _ hyV with h0 | h0 | h0 | h0
    · exfalso
      apply hz'1
      have : z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
      rw [this, h0]
      group
    · exfalso
      apply hz'nZ
      have e : g⁻¹ * g⁻¹ * g⁻¹ * z * (g * g * g) = z' := by
        calc g⁻¹ * g⁻¹ * g⁻¹ * z * (g * g * g) = g⁻¹ * (g⁻¹ * (g⁻¹ * z * g) * g) * g := by group
          _ = g⁻¹ * (g⁻¹ * z' * g) * g := by rw [← hz'def]
          _ = g⁻¹ * z * g := by rw [h0]
          _ = z' := hz'def.symm
      have e2 : g⁻¹ * g⁻¹ * g⁻¹ * z * (g * g * g) = z := by
        have e3 : g * g * g = g ^ 3 := by rw [pow_three, mul_assoc]
        rw [e3]
        have hh := Subgroup.mem_centralizer_iff.mp hg3 z hzV
        calc g⁻¹ * g⁻¹ * g⁻¹ * z * g ^ 3 = g⁻¹ * g⁻¹ * g⁻¹ * (z * g ^ 3) := by group
          _ = g⁻¹ * g⁻¹ * g⁻¹ * (g ^ 3 * z) := by rw [hh]
          _ = z := by group
      rw [← e, e2]
      exact hzZ
    · exfalso
      apply hz'nZ
      have e : z' = z := by
        calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
          _ = g * z' * g⁻¹ := by rw [h0]
          _ = z := hgz'
      rw [e]
      exact hzZ
    · exact h0
  have hgz : g * z * g⁻¹ = z' * z := by
    have h1 : z' = (g * z * g⁻¹) * z := by
      calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
        _ = g * (z * z') * g⁻¹ := by rw [hy]
        _ = (g * z * g⁻¹) * (g * z' * g⁻¹) := by group
        _ = (g * z * g⁻¹) * z := by rw [hgz']
    calc g * z * g⁻¹ = ((g * z * g⁻¹) * z) * z⁻¹ := by group
      _ = z' * z⁻¹ := by rw [← h1]
      _ = z' * z := by rw [hz_inv]
  obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uA V V₁, u₀ ∉ wA V V₁ := by
    by_contra hall'
    push Not at hall'
    exact S.not_le_centralizer_V fun u hu => (hall' u hu).2
  have hu₀N : u₀ ∈ Subgroup.normalizer (V : Set G) := S.uA_le_normalizer_V hu₀U
  have hu₀Z : u₀ ∈ Subgroup.centralizer (V₁ : Set G) :=
    S.uA_le_centralizer hu₀U
  have hu₀C : u₀ ∉ Subgroup.centralizer (V : Set G) := fun hc => hu₀W ⟨hu₀U, hc⟩
  have hu₀z : u₀ * z * u₀⁻¹ = z := by
    have h1 := hzc u₀ hu₀U
    calc u₀ * z * u₀⁻¹ = (z * u₀) * u₀⁻¹ := by rw [h1]
      _ = z := by group
  have hu₀z' : u₀ * z' * u₀⁻¹ = z * z' :=
    S.conj_eq_of_not_centralizes hzZ hz1 hz'V hz'nZ hu₀N hu₀Z hu₀C
  obtain ⟨t, ht⟩ : ∃ t, t = g * u₀ * g⁻¹ := ⟨_, rfl⟩
  have htN : t ∈ Subgroup.normalizer (V : Set G) := by
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hu₀N) (Subgroup.inv_mem _ hgN)
  have htz : t * z * t⁻¹ = z' := by
    have e1 : t * z * t⁻¹ = g * (u₀ * z' * u₀⁻¹) * g⁻¹ := by
      rw [ht, hz'def]
      group
    rw [e1, hu₀z']
    have e2 : g * (z * z') * g⁻¹ = (g * z * g⁻¹) * (g * z' * g⁻¹) := by group
    rw [e2, hgz, hgz', mul_assoc, hzz, mul_one]
  have htz' : t * z' * t⁻¹ = z := by
    have e1 : t * z' * t⁻¹ = g * (u₀ * (g⁻¹ * z' * g) * u₀⁻¹) * g⁻¹ := by
      rw [ht]
      group
    rw [e1, hy]
    have e2 : u₀ * (z * z') * u₀⁻¹ = (u₀ * z * u₀⁻¹) * (u₀ * z' * u₀⁻¹) := by group
    rw [e2, hu₀z, hu₀z']
    have e3 : z * (z * z') = z' := by rw [← mul_assoc, hzz, one_mul]
    rw [e3]
    exact hgz'
  have hrz : rconj (V₁) t⁻¹ = rconj (V₁) g := by
    refine rconj_congr_of_eq_one_or hzZ hall ?_
    rw [inv_inv, ← hz'def]
    exact htz
  have hrz2 : rconj (V₁) (g * t⁻¹) =
      rconj (V₁) 1 := by
    refine rconj_congr_of_eq_one_or hzZ hall ?_
    have e : (g * t⁻¹)⁻¹ * z * (g * t⁻¹) = t * (g⁻¹ * z * g) * t⁻¹ := by group
    rw [e, ← hz'def, htz']
    simp
  have ht'N : t⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ htN
  have htI : t ∈ L ⊔ uA V V₁ := by
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hg.mem_sup _) (Subgroup.mem_sup_right hu₀U))
      (Subgroup.inv_mem _ (hg.mem_sup _))
  refine ⟨t, htN, htI, hrz, ?_, ?_⟩
  · rw [S.rconj_wA_eq_of_mem_normalizer ht'N, S.rconj_wA_eq_of_mem_normalizer hgN, hrz]
  · rw [rconj_rconj_eq]
    have hgt : g * t⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ hgN ht'N
    have h1N : (1 : G) ∈ Subgroup.normalizer (V : Set G) := Subgroup.one_mem _
    have h2 := S.rconj_wA_eq_of_mem_normalizer hgt
    rw [hrz2, ← S.rconj_wA_eq_of_mem_normalizer h1N, rconj_one_eq] at h2
    exact h2

end Setting

end L128A

end CFSG.Quasithin.H13
