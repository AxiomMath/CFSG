module

public import CFSG.Quasithin.Recognition.GoldschmidtTriple
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.Sporadic.Bridge

namespace F6

@[expose] def wordLst (gL giL : ℕ → List ℕ) (n : ℕ) : List (ℕ × Bool) → List ℕ
  | [] => List.range n
  | l :: w => compL (if l.2 then gL l.1 else giL l.1) (wordLst gL giL n w)

theorem repL_wordProd {n : ℕ} {gen : ℕ → Equiv.Perm (Fin n)} {gL giL : ℕ → List ℕ}
    (hg : ∀ i, RepL (gL i) (gen i)) (hgi : ∀ i, RepL (giL i) (gen i)⁻¹)
    (w : List (ℕ × Bool)) : RepL (wordLst gL giL n w) (wordProd gen w) := by
  induction w with
  | nil => exact repL_one n
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have e : wordProd gen ((i, b) :: w) = (if b then gen i else (gen i)⁻¹) * wordProd gen w := by
      simp [wordProd]
    rw [e]
    cases b
    · exact repL_mul (hgi i) ih
    · exact repL_mul (hg i) ih

@[expose] def powLst (n : ℕ) (l : List ℕ) : ℕ → List ℕ
  | 0 => List.range n
  | k + 1 => compL (powLst n l k) l

theorem repL_pow {n : ℕ} {l : List ℕ} {σ : Equiv.Perm (Fin n)} (h : RepL l σ) (k : ℕ) :
    RepL (powLst n l k) (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact repL_one n
  | succ k ih => rw [pow_succ]; exact repL_mul ih h

@[expose] def lfun (n : ℕ) [NeZero n] (l : List ℕ) (i : Fin n) : Fin n :=
  ⟨l.getD i 0 % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem smul_finset_finset_of_repL {n : ℕ} [NeZero n] {l : List ℕ} {σ : Equiv.Perm (Fin n)}
    (h : RepL l σ) (X : Finset (Finset (Fin n))) :
    σ • X = X.image (Finset.image (lfun n l)) := by
  have hf : (fun i : Fin n => σ • i) = lfun n l := by
    funext i
    apply Fin.ext
    simp only [lfun, Equiv.Perm.smul_def]
    rw [h.2 i, Nat.mod_eq_of_lt (σ i).2]
  rw [Finset.smul_finset_def]
  congr 1
  funext B
  rw [Finset.smul_finset_def, hf]

theorem mem_stabilizer_of_repL {n : ℕ} [NeZero n] {l : List ℕ} {σ : Equiv.Perm (Fin n)}
    (h : RepL l σ) {X : Finset (Finset (Fin n))}
    (hX : X.image (Finset.image (lfun n l)) = X) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) X := by
  rw [MulAction.mem_stabilizer_iff, smul_finset_finset_of_repL h, hX]

theorem not_mem_stabilizer_of_repL {n : ℕ} [NeZero n] {l : List ℕ} {σ : Equiv.Perm (Fin n)}
    (h : RepL l σ) {X : Finset (Finset (Fin n))}
    (hX : X.image (Finset.image (lfun n l)) ≠ X) :
    σ ∉ MulAction.stabilizer (Equiv.Perm (Fin n)) X := by
  rw [MulAction.mem_stabilizer_iff, smul_finset_finset_of_repL h]
  exact hX

theorem pow_eq_one_of_mulEquiv {D K : Type*} [Group D] [Group K] {H : Subgroup D}
    (e : ↥H ≃* K) {p q : ℕ} (hK : ∀ y : K, y ^ p = 1 ∨ y ^ q = 1) {x : D} (hx : x ∈ H) :
    x ^ p = 1 ∨ x ^ q = 1 := by
  have key : ∀ m : ℕ, e ⟨x, hx⟩ ^ m = 1 → x ^ m = 1 := fun m hm => by
    rw [← map_pow, MulEquiv.map_eq_one_iff] at hm
    simpa using congrArg Subtype.val hm
  exact (hK (e ⟨x, hx⟩)).imp (key p) (key q)

theorem eq_closure_of_card {D : Type*} [Group D] [Finite D] {T₀ H : Subgroup D} (hTH : T₀ ≤ H)
    (hH : Nat.card H = 3 * Nat.card T₀) {d : D} (hdH : d ∈ H) (hdT : d ∉ T₀) :
    H = Subgroup.closure ((T₀ : Set D) ∪ {d}) := by
  set C := Subgroup.closure ((T₀ : Set D) ∪ {d})
  have hCH : C ≤ H :=
    (Subgroup.closure_le _).mpr (Set.union_subset hTH (Set.singleton_subset_iff.mpr hdH))
  have hTC : T₀ ≤ C := fun y hy => Subgroup.subset_closure (Set.mem_union_left _ hy)
  have hdC : d ∈ C := Subgroup.subset_closure (Set.mem_union_right _ rfl)
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hTC
  have h1 := Subgroup.card_dvd_of_le hCH
  rw [hH, hk, mul_comm 3] at h1
  have hk3 : k = 1 ∨ k = 3 := (Nat.dvd_prime Nat.prime_three).mp
    (Nat.dvd_of_mul_dvd_mul_left hpos h1)
  rcases hk3 with rfl | rfl
  · exfalso
    rw [mul_one] at hk
    exact hdT ((Subgroup.eq_of_le_of_card_ge hTC hk.le) ▸ hdC)
  · exact (Subgroup.eq_of_le_of_card_ge hCH (by rw [hH, hk, mul_comm])).symm

theorem not_goldschmidt_of_cover {D : Type*} [Group D] [Finite D] (T₀ : Subgroup D)
    (hT₀ : IsPGroup 2 T₀) (hidx : ¬ 2 ∣ T₀.index) {K : Type*} [Group K]
    (hK : Nat.card K = 3 * Nat.card T₀) {p q : ℕ} (hKpq : ∀ y : K, y ^ p = 1 ∨ y ^ q = 1)
    (rep : ℕ → D) (J : List ℕ)
    (hcover : ∀ g : D, ∃ j ∈ J, ∃ t ∈ T₀, ∃ t' ∈ T₀, g = t * rep j * t')
    (Good : List ℕ)
    (hR : ∀ j ∈ J, rep j ∈ T₀ ∨ j ∈ Good ∨
      ∃ x ∈ Subgroup.closure ((T₀ : Set D) ∪ {rep j}), ¬ (x ^ p = 1 ∨ x ^ q = 1))
    (hpair : ∀ j ∈ Good, ∀ j' ∈ Good, j ≠ j' →
      Subgroup.closure ((T₀ : Set D) ∪ {rep j, rep j'}) ≠ ⊤) :
    ∀ G₁ G₂ : Subgroup D, IsGoldschmidtTriple G₁ G₂ →
      ¬ (Nonempty (↥G₁ ≃* K) ∧ Nonempty (↥G₂ ≃* K)) := by
  intro G₁ G₂ hG ⟨⟨e₁⟩, ⟨e₂⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hG.sylow
  let S₀ : Sylow 2 D := hT₀.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D S S₀
  let φ : D ≃* D := MulAut.conj g
  have hmapS : (G₁ ⊓ G₂).map φ.toMonoidHom = T₀ := by
    have h1 := congrArg (fun P : Sylow 2 D => (P : Subgroup D)) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    rw [← hS]
    change (S : Subgroup D).map (MulAut.conj g).toMonoidHom = (S₀ : Subgroup D)
    rw [← h1]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  set H₁ := G₁.map φ.toMonoidHom with hH₁
  set H₂ := G₂.map φ.toMonoidHom with hH₂
  have hinf : H₁ ⊓ H₂ = T₀ := by rw [← Subgroup.map_inf _ _ _ φ.injective]; exact hmapS
  have hsup : H₁ ⊔ H₂ = ⊤ := by
    rw [← Subgroup.map_sup, hG.gen, Subgroup.map_top_of_surjective _ φ.surjective]
  have eH₁ : ↥H₁ ≃* K := (G₁.equivMapOfInjective _ φ.injective).symm.trans e₁
  have eH₂ : ↥H₂ ≃* K := (G₂.equivMapOfInjective _ φ.injective).symm.trans e₂
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  have key : ∀ H : Subgroup D, T₀ ≤ H → (↥H ≃* K) →
      ∃ j ∈ Good, H = Subgroup.closure ((T₀ : Set D) ∪ {rep j}) := by
    intro H hTH e
    have hcardH : Nat.card H = 3 * Nat.card T₀ := (Nat.card_congr e.toEquiv).trans hK
    obtain ⟨x, hxH, hxT⟩ : ∃ x ∈ H, x ∉ T₀ := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show H ≤ T₀ from hcon)
      omega
    obtain ⟨j, hjJ, t, ht, t', ht', rfl⟩ := hcover x
    have hrepH : rep j ∈ H := by
      have e1 : rep j = t⁻¹ * (t * rep j * t') * t'⁻¹ := by group
      rw [e1]
      exact H.mul_mem (H.mul_mem (H.inv_mem (hTH ht)) hxH) (H.inv_mem (hTH ht'))
    have hrepT : rep j ∉ T₀ := fun h => hxT (T₀.mul_mem (T₀.mul_mem ht h) ht')
    have hHC := eq_closure_of_card hTH hcardH hrepH hrepT
    rcases hR j hjJ with h | h | ⟨y, hyC, hy⟩
    · exact absurd h hrepT
    · exact ⟨j, h, hHC⟩
    · exact absurd (pow_eq_one_of_mulEquiv e hKpq (hHC ▸ hyC)) hy
  obtain ⟨j₁, hj₁, h₁⟩ := key H₁ (by rw [← hinf]; exact inf_le_left) eH₁
  obtain ⟨j₂, hj₂, h₂⟩ := key H₂ (by rw [← hinf]; exact inf_le_right) eH₂
  by_cases hj : j₁ = j₂
  · subst hj
    have h12 : H₁ = H₂ := h₁.trans h₂.symm
    rw [h12, inf_idem] at hinf
    have h3 := (Nat.card_congr eH₂.toEquiv).trans hK
    rw [hinf] at h3
    omega
  · apply hpair j₁ hj₁ j₂ hj₂ hj
    rw [← hsup, h₁, h₂, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe]
    tauto

end F6

end CFSG.Quasithin
