module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSixSwap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

def partStab {α : Type*} (Γ : Set α) : Subgroup (Perm α) where
  carrier := {g | (∀ x, g x ∈ Γ ↔ x ∈ Γ) ∨ (∀ x, g x ∈ Γ ↔ x ∉ Γ)}
  one_mem' := Or.inl fun _ => Iff.rfl
  mul_mem' := by
    rintro f g (hf | hf) (hg | hg)
    · exact Or.inl fun x => (hf (g x)).trans (hg x)
    · exact Or.inr fun x => (hf (g x)).trans (hg x)
    · exact Or.inr fun x => (hf (g x)).trans (not_congr (hg x))
    · exact Or.inl fun x => (hf (g x)).trans ((not_congr (hg x)).trans not_not)
  inv_mem' := by
    rintro f (hf | hf)
    · exact Or.inl fun x => by simpa using (hf (f⁻¹ x)).symm
    · exact Or.inr fun x => by
        have := hf (f⁻¹ x)
        simp at this
        tauto

theorem mem_partStab {α : Type*} {Γ : Set α} {g : Perm α} :
    g ∈ partStab Γ ↔ (∀ x, g x ∈ Γ ↔ x ∈ Γ) ∨ (∀ x, g x ∈ Γ ↔ x ∉ Γ) :=
  Iff.rfl

theorem le_of_lt_of_maxOver_eq_singleton {G : Type*} [Group G] [Finite G] {K T M N : Subgroup G}
    (hM : maxOver K T = {M}) (hTN : T ≤ N) (hNK : N < K) : N ≤ M := by
  obtain ⟨N', hN', hNN'⟩ := exists_isMaxSubgroupIn hNK
  have h : N' ∈ maxOver K T := ⟨hN', hTN.trans hNN'⟩
  rw [hM, Set.mem_singleton_iff] at h
  exact h ▸ hNN'

theorem b5_FiveSixPart_swap_mem_partStab {α : Type*} [DecidableEq α] {Γ : Set α} {p q : α}
    (hp : p ∈ Γ) (hq : q ∈ Γ) : swap p q ∈ partStab Γ := by
  rw [mem_partStab]
  left
  intro x
  rcases eq_or_ne x p with rfl | hxp
  · rw [swap_apply_left]
    exact iff_of_true hq hp
  · rcases eq_or_ne x q with rfl | hxq
    · rw [swap_apply_right]
      exact iff_of_true hp hq
    · rw [swap_apply_of_ne_of_ne hxp hxq]

theorem b5_FiveSixPart_conj_mem_iff {G : Type*} [Group G] {S : Subgroup G} {t : G} (ht : t ∈ S)
    (h : G) : h ∈ S ↔ t * h * t⁻¹ ∈ S := by
  constructor
  · intro hh
    exact S.mul_mem (S.mul_mem ht hh) (S.inv_mem ht)
  · intro hh
    have := S.mul_mem (S.mul_mem (S.inv_mem ht) hh) ht
    simpa [mul_assoc] using this

theorem b5_FiveSixPart_isSwap_conj_iff {α : Type*} [DecidableEq α] (t h : Perm α) :
    h.IsSwap ↔ (t * h * t⁻¹).IsSwap := by
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨t p, t q, t.injective.ne hpq, by rw [swap_apply_apply]⟩
  · intro hh
    obtain ⟨p, q, hpq, hpq'⟩ := hh
    refine ⟨t⁻¹ p, t⁻¹ q, t⁻¹.injective.ne hpq, ?_⟩
    rw [swap_apply_apply t⁻¹ p q, ← hpq']
    simp [mul_assoc]

theorem partStab_compl {α : Type*} (Γ : Set α) : partStab Γᶜ = partStab Γ := by
  ext g
  simp only [mem_partStab, Set.mem_compl_iff]
  constructor
  · rintro (h | h)
    · left; intro x
      constructor
      · intro hgx
        by_contra hx
        exact ((h x).mpr hx) hgx
      · intro hx
        by_contra hgx
        exact ((h x).mp hgx) hx
    · right; intro x
      constructor
      · intro hgx hx
        exact ((h x).mpr (not_not_intro hx)) hgx
      · intro hx
        by_contra hgx
        exact ((h x).mp hgx) hx
  · rintro (h | h)
    · left; intro x
      constructor
      · intro hgx hx
        exact hgx ((h x).mpr hx)
      · intro hx hgx
        exact hx ((h x).mp hgx)
    · right; intro x
      constructor
      · intro hgx hx
        exact hgx ((h x).mpr hx)
      · intro hx hgx
        exact hx ((h x).mp hgx)

theorem cyc3_mem_partStab_of_mem {α : Type*} [DecidableEq α] {Γ : Set α} {a b c : α}
    (ha : a ∈ Γ) (hb : b ∈ Γ) (hc : c ∈ Γ) : cyc3 a b c ∈ partStab Γ := by
  rw [cyc3]
  exact mul_mem (b5_FiveSixPart_swap_mem_partStab ha hb)
    (b5_FiveSixPart_swap_mem_partStab hb hc)

theorem cyc3_mem_partStab_of_notMem {α : Type*} [DecidableEq α] {Γ : Set α} {a b c : α}
    (ha : a ∉ Γ) (hb : b ∉ Γ) (hc : c ∉ Γ) : cyc3 a b c ∈ partStab Γ := by
  rw [← partStab_compl Γ]
  exact cyc3_mem_partStab_of_mem (Γ := Γᶜ) ha hb hc

theorem cyc3_notMem_partStab {α : Type*} [DecidableEq α] {Γ : Set α} {x y z : α} (hx : x ∈ Γ)
    (hy : y ∉ Γ) (hzx : z ≠ x) (hzy : z ≠ y) : cyc3 x y z ∉ partStab Γ := by
  intro hmem
  rw [mem_partStab] at hmem
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  have hgx := cyc3_apply_left hxy hzx.symm hzy.symm
  have hgy := cyc3_apply_middle hxy hzx.symm hzy.symm
  have hgz := cyc3_apply_right hxy hzx.symm hzy.symm
  rcases hmem with h | h
  · have hx' : cyc3 x y z x ∈ Γ := (h x).mpr hx
    rw [hgx] at hx'
    exact hy hx'
  · have hy' : cyc3 x y z y ∈ Γ := (h y).mpr hy
    rw [hgy] at hy'
    have hz' : cyc3 x y z z ∈ Γ := by rw [hgz]; exact hx
    exact ((h z).mp hz') hy'

theorem inf_partStab_le {n : ℕ} (hn : 3 ≤ n) {K T M : Subgroup (Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ K) (hM : maxOver K T = {M}) {Γ : Set (Fin n)}
    (hΓ : Γ.Nonempty) (hΓc : Γᶜ.Nonempty) (hT : T ≤ partStab Γ) :
    K ⊓ partStab Γ ≤ M := by
  have hMmem : M ∈ maxOver K T := hM ▸ Set.mem_singleton M
  have hMK : M < K := hMmem.1.1
  have hTM : T ≤ M := hMmem.2
  have hTK : T ≤ K := hTM.trans hMK.le
  have hTN : T ≤ K ⊓ partStab Γ := le_inf hTK hT
  obtain ⟨x, hx⟩ := hΓ
  obtain ⟨y, hy⟩ := hΓc
  have hy' : y ∉ Γ := hy
  have hxy : x ≠ y := fun h => hy' (h ▸ hx)
  obtain ⟨z, hzx, hzy⟩ :=
    ENat.exists_ne_ne_of_three_le (by simpa using hn) x y
  have hgA : cyc3 x y z ∈ alternatingGroup (Fin n) := cyc3_mem_alternatingGroup hxy hzy.symm
  have hgK : cyc3 x y z ∈ K := hA hgA
  have hgNot : cyc3 x y z ∉ partStab Γ := cyc3_notMem_partStab hx hy hzx hzy
  have hNK : K ⊓ partStab Γ < K := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    exact hgNot (hEq ▸ hgK).2
  exact le_of_lt_of_maxOver_eq_singleton hM hTN hNK

theorem inf_setNormalizer_swaps_le {n : ℕ} (hn : 3 ≤ n) {K T M S : Subgroup (Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ K) (hM : maxOver K T = {M}) (hTS : T ≤ S)
    (hS : IsPGroup 2 S) (hsw : ∃ a b : Fin n, a ≠ b ∧ swap a b ∈ S) :
    K ⊓ Subgroup.setNormalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} ≤ M := by
  have hMmem : M ∈ maxOver K T := hM ▸ Set.mem_singleton M
  have hMK : M < K := hMmem.1.1
  have hTM : T ≤ M := hMmem.2
  have hTK : T ≤ K := hTM.trans hMK.le
  have hTnorm : T ≤ Subgroup.setNormalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} := by
    intro t ht
    have htS : t ∈ S := hTS ht
    change t ∈ Subgroup.normalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap}
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
    exact and_congr (b5_FiveSixPart_conj_mem_iff htS h) (b5_FiveSixPart_isSwap_conj_iff t h)
  have hTN : T ≤ K ⊓ Subgroup.setNormalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} :=
    le_inf hTK hTnorm
  obtain ⟨a, b, hab, habS⟩ := hsw
  obtain ⟨c, hca, hcb⟩ := ENat.exists_ne_ne_of_three_le (by simpa using hn) a b
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  have hgA : cyc3 a b c ∈ alternatingGroup (Fin n) := cyc3_mem_alternatingGroup hab hbc
  have hgK : cyc3 a b c ∈ K := hA hgA
  have hgNot : cyc3 a b c ∉ Subgroup.setNormalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} := by
    intro hgmem
    change cyc3 a b c ∈ Subgroup.normalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} at hgmem
    have hiff := (Subgroup.mem_set_normalizer_iff.mp hgmem) (swap a b)
    have habMem : swap a b ∈ {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} :=
      ⟨habS, a, b, hab, rfl⟩
    have hconj : cyc3 a b c * swap a b * (cyc3 a b c)⁻¹ ∈
        {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} := hiff.mp habMem
    rw [Set.mem_setOf_eq, cyc3_mul_swap_mul_inv hab hac hbc] at hconj
    exact false_of_swap_mem_of_swap_mem hS hab hac hbc habS hconj.1
  have hNK : K ⊓ Subgroup.setNormalizer {t : Perm (Fin n) | t ∈ S ∧ t.IsSwap} < K := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    exact hgNot (hEq ▸ hgK).2
  exact le_of_lt_of_maxOver_eq_singleton hM hTN hNK

end CFSG.LocalAnalysis.WeakClosure81
