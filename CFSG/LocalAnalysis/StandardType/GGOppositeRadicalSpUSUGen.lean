module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUStd
public import CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary GGOppRad
open scoped commutatorElement

section Levels

variable {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

theorem mem_flagStab_natRep_of_block [Finite F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Subgroup (GL ι F)} {ℓ : ι → ℕ} {g : H}
    (hg : ∀ c a, ℓ c ≠ ℓ a → ((g : GL ι F) : Matrix ι ι F) c a = 0) :
    g ∈ flagStab (natRep H) (stdFlag ℓ) := by
  refine GGOppRad.mem_flagStab_of_forall (natRep H) fun k v hv c hc => ?_
  rw [natRep_apply, mulVec, dotProduct]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hca : ℓ c = ℓ a
  · rw [hv a (by omega), mul_zero]
  · rw [hg c a hca, zero_mul]

theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply GGTwoSig.mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, GGTwoSig.map_conj_eq hA, GGTwoSig.map_conj_eq hB]

theorem mem_normalizer_of_support [Finite F] [CharP F 2] {n M : ℕ} {ℓ : Fin n → ℕ}
    (hℓ : IsSULevel M ℓ) {g : SU σ n} (P : Fin n → Fin n → Prop)
    (hg : ∀ c a, ¬ P c a →
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c a = (1 : Matrix (Fin n) (Fin n) F) c a)
    (hsign : (∀ c a, P c a → ℓ c < ℓ a) ∨ (∀ c a, P c a → ℓ a < ℓ c) ∨
      (∀ c a, P c a → ℓ c = ℓ a)) :
    g ∈ Subgroup.normalizer
      ((suU σ ℓ ⊔ suU σ (ℓ ∘ Fin.rev) : Subgroup (SU σ n)) : Set (SU σ n)) := by
  rcases hsign with h | h | h
  · refine Subgroup.le_normalizer (Subgroup.mem_sup_left (mem_suU_iff.mpr fun c a hca => ?_))
    exact hg c a fun hP => hca (h c a hP)
  · refine Subgroup.le_normalizer (Subgroup.mem_sup_right ((mem_suU_comp_rev_iff hℓ).mpr
      fun c a hac => ?_))
    exact hg c a fun hP => hac (h c a hP)
  · have hblk : ∀ c a, ℓ c ≠ ℓ a →
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c a = 0 := by
      intro c a hca
      rw [hg c a fun hP => hca (h c a hP), Matrix.one_apply_ne (fun he => hca (by rw [he]))]
    have hblk' : ∀ c a, (ℓ ∘ Fin.rev) c ≠ (ℓ ∘ Fin.rev) a →
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c a = 0 := by
      intro c a hca
      refine hblk c a fun he => hca ?_
      have := hℓ c
      have := hℓ a
      simp only [Function.comp_apply]
      omega
    exact mem_normalizer_sup
      (flagStab_le_normalizer_flagKernel _ _ (mem_flagStab_natRep_of_block hblk))
      (flagStab_le_normalizer_flagKernel _ _ (mem_flagStab_natRep_of_block hblk'))

end Levels

section Finite

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem eq_top_of_root_le (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (R : Subgroup (SU (unitaryInvolution F 2 f) n))
    (h₁ : ∀ (i j : Fin n) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j), j ≠ Fin.rev i →
      (rootHom (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) hij hi hj).range ≤ R)
    (h₂ : ∀ (i : Fin n) (hi : i ≠ Fin.rev i), (longRootHom (unitaryInvolution F 2 f) hi).range ≤ R)
    (h₃ : ∀ (i k : Fin n) (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k),
      heisenbergSubgroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) hi hik hk ≤
        R) :
    R = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have htop := (isCTGroupDatum hF n hn ζ hζ).iSup_eq_top
  rw [eq_top_iff, ← htop]
  refine iSup₂_le fun γ _ => ?_
  rw [rootGroup]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun hji => iSup_le fun _ => h₁ i j hij hi hj hji
  · exact iSup_le fun i => iSup_le fun hi => iSup_le fun _ => h₂ i hi
  · exact iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik => iSup_le fun hk =>
      iSup_le fun _ => h₃ i k hi hik hk

theorem normal_sup_suU_comp_rev (hF : Nat.card F = (2 ^ f) ^ 2) {n M : ℕ} (hn : 2 ≤ n)
    {ℓ : Fin n → ℕ} (hℓ : IsSULevel M ℓ) :
    (suU (unitaryInvolution F 2 f) ℓ ⊔ suU (unitaryInvolution F 2 f) (ℓ ∘ Fin.rev)).Normal := by
  set σ := unitaryInvolution F 2 f
  rw [← Subgroup.normalizer_eq_top_iff]
  refine eq_top_of_root_le hF hn _ ?_ ?_ ?_
  · rintro i j hij hi hj hji _ ⟨c, rfl⟩
    refine mem_normalizer_of_support σ hℓ
      (fun x y => (x = i ∧ y = j) ∨ (x = Fin.rev j ∧ y = Fin.rev i)) (fun x y hxy => ?_) ?_
    · rw [coe_rootHom, rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
        Matrix.single_apply]
      have h1 : ¬ (i = x ∧ j = y) := fun h => hxy (Or.inl ⟨h.1.symm, h.2.symm⟩)
      have h2 : ¬ (Fin.rev j = x ∧ Fin.rev i = y) := fun h => hxy (Or.inr ⟨h.1.symm, h.2.symm⟩)
      rw [ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero]
    · have := hℓ i
      have := hℓ j
      rcases lt_trichotomy (ℓ i) (ℓ j) with h | h | h
      · left
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega
      · right; right
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega
      · right; left
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega
  · rintro i hi _ ⟨c, rfl⟩
    refine mem_normalizer_of_support σ hℓ (fun x y => x = i ∧ y = Fin.rev i)
      (fun x y hxy => ?_) ?_
    · rw [coe_longRootHom, longRootMatrix, Matrix.add_apply, Matrix.single_apply]
      have h1 : ¬ (i = x ∧ Fin.rev i = y) := fun h => hxy ⟨h.1.symm, h.2.symm⟩
      rw [ite_eq_right h1, add_zero]
    · rcases lt_trichotomy (ℓ i) (ℓ (Fin.rev i)) with h | h | h
      · left
        rintro x y ⟨rfl, rfl⟩
        exact h
      · right; right
        rintro x y ⟨rfl, rfl⟩
        exact h
      · right; left
        rintro x y ⟨rfl, rfl⟩
        exact h
  · rintro i k hi hik hk g ⟨a, b, -, hg⟩
    refine mem_normalizer_of_support σ hℓ
      (fun x y => (x = i ∧ y = k) ∨ (x = k ∧ y = Fin.rev i) ∨ (x = i ∧ y = Fin.rev i))
      (fun x y hxy => ?_) ?_
    · rw [hg, heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.single_apply, Matrix.single_apply, Matrix.single_apply]
      have h1 : ¬ (i = x ∧ k = y) := fun h => hxy (Or.inl ⟨h.1.symm, h.2.symm⟩)
      have h2 : ¬ (k = x ∧ Fin.rev i = y) := fun h => hxy (Or.inr (Or.inl ⟨h.1.symm, h.2.symm⟩))
      have h3 : ¬ (i = x ∧ Fin.rev i = y) := fun h => hxy (Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩))
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, add_zero, sub_zero, add_zero]
    · have hki := hℓ k
      rw [hk] at hki
      have := hℓ i
      rcases lt_trichotomy (ℓ i) (ℓ (Fin.rev i)) with h | h | h
      · left
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega
      · right; right
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega
      · right; left
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

theorem eq_one_of_mem_center_su (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) (h2 : z ^ 2 = 1) : z = 1 := by
  set e := equivStatedSU hF n
  have hcen := (isQuasisimple_statedSU_of_card hF hn hnq).2
  have hez : e z ∈ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU n (2 ^ f) F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [hcen, Subgroup.mem_subgroupOf] at hez
  obtain ⟨c, hc⟩ := hez
  have h2' : ((e z : CFSG.Assembly.LowTwoRank.StatedSU n (2 ^ f) F) : GL (Fin n) F) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, h2, map_one, Subgroup.coe_one]
  rw [← hc, ← map_pow] at h2'
  have hc2 : (c : F) * c = 1 := by
    have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)
      ⟨0, by omega⟩ ⟨0, by omega⟩) h2'
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, pow_two] using this
  have hc1 : (c : F) = 1 := by
    have h4 : ((c : F) - 1) ^ 2 = 0 := by
      calc ((c : F) - 1) ^ 2 = ((c : F) * c - 1) - 2 * ((c : F) - 1) := by ring
        _ = 0 := by rw [hc2, CharTwo.two_eq_zero]; ring
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h4)
  have hez1 : e z = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hc]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc1, Units.val_one, Matrix.scalar_apply,
      Matrix.diagonal_one]
  exact e.injective (by rw [hez1, map_one])

theorem le_center_or_eq_top_of_perfect {G : Type*} [Group G] (h1 : commutator G = ⊤)
    (h2 : IsSimpleGroup (G ⧸ Subgroup.center G)) (N : Subgroup G) [hN : N.Normal] :
    N ≤ Subgroup.center G ∨ N = ⊤ := by
  have := h2
  set π := QuotientGroup.mk' (Subgroup.center G)
  have hnorm : (N.map π).Normal := Subgroup.Normal.map hN π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro x hx
    have : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · right
    have hdec : ∀ g : G, ∃ n ∈ N, n⁻¹ * g ∈ Subgroup.center G := by
      intro g
      have : π g ∈ N.map π := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := this
      exact ⟨n, hn, QuotientGroup.eq.mp hng⟩
    rw [eq_top_iff, ← h1, commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨n, hn, hz⟩ := hdec g
    have hzc := Subgroup.mem_center_iff.mp hz h
    have hcomm : ⁅g, h⁆ = n * (h * n⁻¹ * h⁻¹) := by
      have hg : g = n * (n⁻¹ * g) := by group
      rw [commutatorElement_def]
      calc g * h * g⁻¹ * h⁻¹ = n * ((n⁻¹ * g) * h) * (n⁻¹ * g)⁻¹ * n⁻¹ * h⁻¹ := by group
        _ = n * (h * (n⁻¹ * g)) * (n⁻¹ * g)⁻¹ * n⁻¹ * h⁻¹ := by rw [← hzc]
        _ = n * (h * n⁻¹ * h⁻¹) := by group
    rw [hcomm]
    exact mul_mem hn (hN.conj_mem _ (inv_mem hn) h)

theorem sup_suU_comp_rev (hF : Nat.card F = (2 ^ f) ^ 2) {n M : ℕ} (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {ℓ : Fin n → ℕ} (hℓ : IsSULevel M ℓ)
    (hne : suU (unitaryInvolution F 2 f) ℓ ≠ ⊥) :
    suU (unitaryInvolution F 2 f) ℓ ⊔ suU (unitaryInvolution F 2 f) (ℓ ∘ Fin.rev) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := normal_sup_suU_comp_rev hF (by omega : 2 ≤ n) hℓ
  have hq := isQuasisimple_SU hF hn hnq
  rcases le_center_or_eq_top_of_perfect hq.1.commutator_eq_top hq.2.1
    (suU (unitaryInvolution F 2 f) ℓ ⊔ suU (unitaryInvolution F 2 f) (ℓ ∘ Fin.rev)) with h | h
  · exfalso
    obtain ⟨m, hm⟩ := exists_stdFlag_eq_top (K := F) ℓ
    have h2 : IsPGroup 2 (flagKernel (natRep (SU (unitaryInvolution F 2 f) n))
        (stdFlag (K := F) ℓ)) :=
      isPGroup_flagKernel (natRep (SU (unitaryInvolution F 2 f) n)) 2
        (natRep_injective (SU (unitaryInvolution F 2 f) n)) (stdFlag_zero ℓ) hm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp h2 :
      ∃ k, Nat.card (suU (unitaryInvolution F 2 f) ℓ) = 2 ^ k)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hne hk
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := suU (unitaryInvolution F 2 f) ℓ) 2
      (hk ▸ dvd_pow_self 2 hk0)
    have hx1 : (x : SU (unitaryInvolution F 2 f) n) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    have hx2' : x ^ 2 = 1 := by
      have h3 := pow_orderOf_eq_one x
      rwa [hx] at h3
    have hx2 : (x : SU (unitaryInvolution F 2 f) n) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hx2', Subgroup.coe_one]
    exact hx1 (eq_one_of_mem_center_su hF hn hnq (h (Subgroup.mem_sup_left x.2)) hx2)
  · exact h

end Finite

end GGOppRadSpU

end CFSG.StandardType
