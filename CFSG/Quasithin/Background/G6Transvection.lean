module

public import CFSG.Quasithin.Background.G6Swap
public import CFSG.Quasithin.Background.G6SQTK
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace G6

universe u

variable {V : Type u} [CommGroup V]

@[expose] def IsG64Type (Ki : Subgroup (MulAut V)) (Vi : Subgroup V) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ IsLnNatural Ki Vi n) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ IsSymNatural Ki Vi n) ∨
  (∃ n, (n = 6 ∨ n = 8) ∧ IsSymCore Ki Vi n)

@[expose] def IsSmallG64Type (Ki : Subgroup (MulAut V)) : Prop :=
  Nonempty (Ki ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) ∨
  Nonempty (Ki ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∨
  Nonempty (Ki ≃* Equiv.Perm (Fin 5))

structure IsTransvectionDecomposition (K : Subgroup (MulAut V)) {s : ℕ}
    (Ks : Fin s → Subgroup (MulAut V)) : Prop where
  pos : 0 < s
  le_two : s ≤ 2
  iSup_eq : ⨆ i, Ks i = K
  indep : iSupIndep Ks
  centralize : ∀ i j, i ≠ j → Ks i ≤ Subgroup.centralizer (Ks j : Set (MulAut V))
  iSup_commV : ⨆ i, commV (Ks i) = ⊤
  commV_indep : iSupIndep fun i => commV (Ks i)
  commOn_eq_bot : ∀ i j, i ≠ j → commOn (Ks i) (commV (Ks j)) = ⊥
  isHSubmodule : ∀ i, IsHSubmodule (Ks i) (commV (Ks i))
  type : ∀ i, IsG64Type (Ks i) (commV (Ks i))
  small : s = 2 → ∀ i, IsSmallG64Type (Ks i)

def QuotedTransvectionClassification : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut V)) (D : Set (MulAut V)),
      pCoreOf 2 K = ⊥ → IsQuotientOfSQTK K →
      (∀ d ∈ D, d ∈ K ∧ d ≠ 1 ∧ Nat.card (commV (Subgroup.zpowers d)) = 2 ∧
        ∀ k ∈ K, k * d * k⁻¹ ∈ D) →
      Subgroup.closure D = K → commV K = ⊤ →
      ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)), IsTransvectionDecomposition K Ks

def QuotedTransvectionNormalizers : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut V)) (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)),
      IsTransvectionDecomposition K Ks → ∀ g : MulAut V, (∀ k ∈ K, g * k * g⁻¹ ∈ K) →
        (∀ i, ∃ j, conjSubgroup (Ks i) g = Ks j) ∧
          ((∀ i, conjSubgroup (Ks i) g = Ks i) → g ∈ K)

theorem commV_zpowers_conj (g a : MulAut V) :
    commV (Subgroup.zpowers (g * a * g⁻¹)) = (commV (Subgroup.zpowers a)).map g.toMonoidHom :=
  CFSG.Quasithin.commV_zpowers_conj_eq a g

theorem card_commV_zpowers_conj (g a : MulAut V) :
    Nat.card (commV (Subgroup.zpowers (g * a * g⁻¹))) = Nat.card (commV (Subgroup.zpowers a)) := by
  rw [commV_zpowers_conj]
  exact Subgroup.card_map_of_injective g.injective

theorem iSup_fin_two {α : Type*} [CompleteLattice α] (f : Fin 2 → α) : ⨆ i, f i = f 0 ⊔ f 1 :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp) (sup_le (le_iSup f 0) (le_iSup f 1))

theorem mem_sup_of_centralizes {G : Type*} [Group G] {H K : Subgroup G}
    (h : H ≤ Subgroup.centralizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hn : H ≤ Subgroup.normalizer (K : Set G) :=
    h.trans (Subgroup.centralizer_le_normalizer _)
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K hn
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [this] at hx'
  exact hx'

namespace IsTransvectionDecomposition

variable {K : Subgroup (MulAut V)} {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)}

theorem comp (h : IsTransvectionDecomposition K Ks) (e : Fin s ≃ Fin s) :
    IsTransvectionDecomposition K (Ks ∘ e) where
  pos := h.pos
  le_two := h.le_two
  iSup_eq := by
    rw [← h.iSup_eq]
    exact e.iSup_comp (g := Ks)
  indep := h.indep.comp e.injective
  centralize := fun i j hij => h.centralize (e i) (e j) (e.injective.ne hij)
  iSup_commV := by
    rw [← h.iSup_commV]
    exact e.iSup_comp (g := fun i => commV (Ks i))
  commV_indep := h.commV_indep.comp e.injective
  commOn_eq_bot := fun i j hij => h.commOn_eq_bot (e i) (e j) (e.injective.ne hij)
  isHSubmodule := fun i => h.isHSubmodule (e i)
  type := fun i => h.type (e i)
  small := fun hs i => h.small hs (e i)

theorem apply_eq_of_ne (h : IsTransvectionDecomposition K Ks) {i j : Fin s} (hij : i ≠ j)
    {k : MulAut V} (hk : k ∈ Ks i) {v : V} (hv : v ∈ commV (Ks j)) : k v = v := by
  have := mem_commOn_of_mem hk hv
  rw [h.commOn_eq_bot i j hij, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

theorem exists_mem_of_transvection (h : IsTransvectionDecomposition K Ks) {c : MulAut V}
    (hc : c ∈ K) (hc1 : c ≠ 1) (hcard : Nat.card (commV (Subgroup.zpowers c)) = 2) :
    ∃ i, c ∈ Ks i := by
  have hs : s = 1 ∨ s = 2 := by have := h.pos; have := h.le_two; omega
  rcases hs with rfl | rfl
  · rw [← h.iSup_eq, iSup_unique] at hc
    exact ⟨default, hc⟩
  · rw [← h.iSup_eq, iSup_fin_two] at hc
    obtain ⟨c₀, h₀, c₁, h₁, rfl⟩ := mem_sup_of_centralizes (h.centralize 0 1 (by decide)) hc
    have hV : commV (Ks 0) ⊔ commV (Ks 1) = ⊤ := by
      have := iSup_fin_two (fun i => commV (Ks i))
      rw [h.iSup_commV] at this
      exact this.symm
    have hdis : Disjoint (commV (Ks 0)) (commV (Ks 1)) :=
      h.commV_indep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)
    by_contra hcon
    push Not at hcon
    have hc₀ : c₀ ≠ 1 := fun e => hcon 1 (by rw [e, one_mul]; exact h₁)
    have hc₁ : c₁ ≠ 1 := fun e => hcon 0 (by rw [e, mul_one]; exact h₀)
    have key : ∀ (i j : Fin 2), i ≠ j → ∀ k ∈ Ks i, k ≠ 1 →
        commV (Ks i) ⊔ commV (Ks j) = ⊤ →
        ∃ v ∈ commV (Ks i), k v ≠ v := by
      intro i j hij k hk hk1 hsup
      obtain ⟨v, hv⟩ : ∃ v : V, k v ≠ v := by
        by_contra hcon'
        push Not at hcon'
        exact hk1 (MulEquiv.ext hcon')
      have hvmem : v ∈ commV (Ks i) ⊔ commV (Ks j) := by rw [hsup]; exact Subgroup.mem_top v
      obtain ⟨vi, hvi, vj, hvj, rfl⟩ := Subgroup.mem_sup.1 hvmem
      refine ⟨vi, hvi, fun hk' => hv ?_⟩
      rw [map_mul, hk', h.apply_eq_of_ne hij hk hvj]
    have hV' : commV (Ks 1) ⊔ commV (Ks 0) = ⊤ := by rw [sup_comm]; exact hV
    obtain ⟨v₀, hv₀, hmv₀⟩ := key 0 1 (by decide) c₀ h₀ hc₀ hV
    obtain ⟨v₁, hv₁, hmv₁⟩ := key 1 0 (by decide) c₁ h₁ hc₁ hV'
    set x₀ : V := c₀ v₀ * v₀⁻¹ with hx₀
    set x₁ : V := c₁ v₁ * v₁⁻¹ with hx₁
    have hx₀V : x₀ ∈ commV (Ks 0) :=
      (commV (Ks 0)).mul_mem (h.isHSubmodule 0 c₀ h₀ v₀ hv₀) ((commV (Ks 0)).inv_mem hv₀)
    have hx₁V : x₁ ∈ commV (Ks 1) :=
      (commV (Ks 1)).mul_mem (h.isHSubmodule 1 c₁ h₁ v₁ hv₁) ((commV (Ks 1)).inv_mem hv₁)
    have hx₀ne : x₀ ≠ 1 := fun e => hmv₀ (mul_inv_eq_one.1 e)
    have hx₁ne : x₁ ≠ 1 := fun e => hmv₁ (mul_inv_eq_one.1 e)
    have hcv₀ : (c₀ * c₁) v₀ = c₀ v₀ := by
      show c₀ (c₁ v₀) = _
      rw [h.apply_eq_of_ne (by decide : (1 : Fin 2) ≠ 0) h₁ hv₀]
    have hcv₁ : (c₀ * c₁) v₁ = c₁ v₁ := by
      show c₀ (c₁ v₁) = _
      exact h.apply_eq_of_ne (by decide : (0 : Fin 2) ≠ 1) h₀
        (h.isHSubmodule 1 c₁ h₁ v₁ hv₁)
    have hm₀ : x₀ ∈ commV (Subgroup.zpowers (c₀ * c₁)) := by
      have := mem_commV_of_mem (Subgroup.mem_zpowers (c₀ * c₁)) v₀
      rwa [hcv₀] at this
    have hm₁ : x₁ ∈ commV (Subgroup.zpowers (c₀ * c₁)) := by
      have := mem_commV_of_mem (Subgroup.mem_zpowers (c₀ * c₁)) v₁
      rwa [hcv₁] at this
    by_cases hx : x₀ = x₁
    · have : x₀ ∈ commV (Ks 0) ⊓ commV (Ks 1) := ⟨hx₀V, hx ▸ hx₁V⟩
      rw [hdis.eq_bot, Subgroup.mem_bot] at this
      exact hx₀ne this
    · exact false_of_card_two hcard hm₀ hm₁ hx₀ne hx₁ne hx

end IsTransvectionDecomposition

section Apply

variable {X : Subgroup (MulAut V)} {a : MulAut V}

theorem closure_conj_set_eq (X : Subgroup (MulAut V)) (a : MulAut V) :
    Subgroup.closure {d | ∃ g ∈ X, d = g * a * g⁻¹} = classClosure X a := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro d ⟨g, hg, rfl⟩
    exact conj_mem_classClosure hg
  · unfold classClosure
    refine conjClosure_le fun g hg z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [show g * a ^ k * g⁻¹ = (g * a * g⁻¹) ^ k from conj_zpow.symm]
    have hmem : g * a * g⁻¹ ∈ Subgroup.closure {d | ∃ g ∈ X, d = g * a * g⁻¹} :=
      Subgroup.subset_closure ⟨g, hg, rfl⟩
    exact Subgroup.zpow_mem _ hmem k

theorem pCoreOf_classClosure_eq_bot [Finite V] (h : Hypothesis61 X a) :
    pCoreOf 2 (classClosure X a) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := classClosure X a with hK
  have hnormK : X ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    le_normalizer_conjClosure (Subgroup.zpowers a) X
  have hNK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hNX : pCoreOf 2 K ≤ X := hNK.trans (classClosure_le h.mem)
  have hnormN : X ≤ Subgroup.normalizer (pCoreOf 2 K : Set (MulAut V)) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 K (hnormK hg)
  have := le_pCoreOf_of_le_normalizer 2 hNX hnormN (pCoreOf_isPGroup 2 K)
  rw [h.pCoreOf_eq_bot] at this
  exact le_bot_iff.1 this

theorem exists_decomposition [Finite V] (Q1 : QuotedTransvectionClassification.{u})
    (h : Hypothesis61 X a) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)),
      IsTransvectionDecomposition (classClosure X a) Ks := by
  refine Q1 V h.sq_eq_one (classClosure X a) {d | ∃ g ∈ X, d = g * a * g⁻¹}
    (pCoreOf_classClosure_eq_bot h)
    (IsQuotientOfSQTK.of_le (classClosure_le h.mem) h.isQuotientOfSQTK) ?_
    (closure_conj_set_eq X a) (lemma_G62_1 h)
  rintro d ⟨g, hg, rfl⟩
  refine ⟨conj_mem_classClosure hg, ?_, ?_, ?_⟩
  · intro h1
    apply h.ne_one
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, h1]
    group
  · rw [card_commV_zpowers_conj]
    exact htr
  · intro k hk
    have hkX : k ∈ X := classClosure_le h.mem hk
    refine ⟨k * g, X.mul_mem hkX hg, ?_⟩
    group

private theorem not_subsingleton_perm (n : ℕ) (hn : 2 ≤ n) :
    ¬ Subsingleton (Equiv.Perm (Fin n)) := by
  intro hs
  have h : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun f : Equiv.Perm (Fin n) => f ⟨0, by omega⟩) h
  simp at h2

theorem IsTransvectionDecomposition.ne_bot {K : Subgroup (MulAut V)} {s : ℕ}
    {Ks : Fin s → Subgroup (MulAut V)} (hd : IsTransvectionDecomposition K Ks) (i : Fin s) :
    Ks i ≠ ⊥ := by
  intro hbot
  have hcomm : commV (Ks i) = ⊥ := by
    rw [hbot, eq_bot_iff, commV_le_iff]
    intro x hx v
    rw [Subgroup.mem_bot] at hx
    subst hx
    simp
  have hsub : Subsingleton (Ks i) := by rw [hbot]; infer_instance
  rcases hd.type i with ⟨n, hn2, _, hL⟩ | ⟨n, hn5, _, ⟨θ, β, _, _, _⟩⟩ | ⟨n, hn, ⟨θ, β, _, _, _⟩⟩
  · have := hL.2.1
    rw [hcomm, Subgroup.card_bot] at this
    have : 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · have : Subsingleton (Equiv.Perm (Fin n)) := θ.surjective.subsingleton
    exact not_subsingleton_perm n (by omega) this
  · have : Subsingleton (Equiv.Perm (Fin n)) := θ.surjective.subsingleton
    exact not_subsingleton_perm n (by omega) this

theorem transitive_of_permute {s : ℕ}
    {Ks : Fin s → Subgroup (MulAut V)} (hd : IsTransvectionDecomposition (classClosure X a) Ks)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, conjSubgroup (Ks i) g = Ks j) {i₀ : Fin s} (hi₀ : a ∈ Ks i₀) :
    ∀ i j, ∃ g ∈ X, conjSubgroup (Ks i) g = Ks j := by
  have hs : s = 1 ∨ s = 2 := by have := hd.pos; have := hd.le_two; omega
  have hfrom : ∀ j, ∃ g ∈ X, conjSubgroup (Ks i₀) g = Ks j := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      exact ⟨1, X.one_mem, conjSubgroup_one _⟩
    · by_contra hcon
      push Not at hcon
      have hall : ∀ g ∈ X, conjSubgroup (Ks i₀) g = Ks i₀ := by
        intro g hg
        obtain ⟨j', hj'⟩ := hperm g hg i₀
        have hj'j : j' ≠ j := fun e => hcon g hg (hj' ▸ e ▸ rfl)
        have : j' = i₀ := by
          rcases hs with rfl | rfl
          · exact Subsingleton.elim _ _
          · have := j'.isLt; have := j.isLt; have := i₀.isLt
            apply Fin.ext
            have h1 : j' ≠ j := hj'j
            have h2 : j ≠ i₀ := hj
            rw [Ne, Fin.ext_iff] at h1 h2
            omega
        rw [hj', this]
      have hle : classClosure X a ≤ Ks i₀ := by
        unfold classClosure
        refine conjClosure_le fun g hg z hz => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        rw [show g * a ^ k * g⁻¹ = (g * a * g⁻¹) ^ k from conj_zpow.symm]
        have hmem : g * a * g⁻¹ ∈ Ks i₀ := by
          have : a ∈ conjSubgroup (Ks i₀) g := by rw [hall g hg]; exact hi₀
          exact mem_conjSubgroup_iff.1 this
        exact Subgroup.zpow_mem _ hmem k
      have hjK : Ks j ≤ classClosure X a := by
        rw [← hd.iSup_eq]
        exact le_iSup Ks j
      have hdis : Disjoint (Ks i₀) (Ks j) := hd.indep.pairwiseDisjoint (Ne.symm hj)
      apply hd.ne_bot j
      rw [eq_bot_iff]
      intro x hx
      have := hdis.le_bot ⟨hle (hjK hx), hx⟩
      simpa using this
  intro i j
  obtain ⟨g₁, hg₁, h₁⟩ := hfrom i
  obtain ⟨g₂, hg₂, h₂⟩ := hfrom j
  refine ⟨g₁⁻¹ * g₂, X.mul_mem (X.inv_mem hg₁) hg₂, ?_⟩
  have h3 : conjSubgroup (Ks i) g₁⁻¹ = Ks i₀ := by
    rw [← h₁, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  rw [← conjSubgroup_conjSubgroup, h3, h₂]

structure G64Decomposition (X : Subgroup (MulAut V)) (a : MulAut V) {s : ℕ}
    (Ks : Fin s → Subgroup (MulAut V)) : Prop where
  decomp : IsTransvectionDecomposition (classClosure X a) Ks
  mem_first : ∃ hs : 0 < s, a ∈ Ks ⟨0, hs⟩
  permute : ∀ g ∈ X, ∀ i, ∃ j, conjSubgroup (Ks i) g = Ks j
  transitive : ∀ i j, ∃ g ∈ X, conjSubgroup (Ks i) g = Ks j

theorem lemma_G64_1 [Finite V] (Q1 : QuotedTransvectionClassification.{u})
    (Q2 : QuotedTransvectionNormalizers.{u}) (h : Hypothesis61 X a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)), G64Decomposition X a Ks := by
  obtain ⟨s, Ks, hd⟩ := exists_decomposition Q1 h htr
  obtain ⟨i₀, hi₀⟩ := hd.exists_mem_of_transvection (mem_classClosure_self X a) h.ne_one htr
  have hpos := hd.pos
  let e : Fin s ≃ Fin s := Equiv.swap ⟨0, hpos⟩ i₀
  have hd' := hd.comp e
  have hmem : a ∈ (Ks ∘ e) ⟨0, hpos⟩ := by
    show a ∈ Ks (e ⟨0, hpos⟩)
    rw [show e ⟨0, hpos⟩ = i₀ from Equiv.swap_apply_left _ _]
    exact hi₀
  have hperm : ∀ g ∈ X, ∀ i, ∃ j, conjSubgroup ((Ks ∘ e) i) g = (Ks ∘ e) j := by
    intro g hg i
    exact (Q2 V h.sq_eq_one (classClosure X a) s (Ks ∘ e) hd' g
      (fun k hk => conj_mem_classClosure_of_mem hg hk)).1 i
  exact ⟨s, Ks ∘ e, hd', ⟨hpos, hmem⟩, hperm,
    transitive_of_permute hd' hperm hmem⟩

theorem conjSubgroup_inj {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (h : conjSubgroup A g = conjSubgroup B g) : A = B := by
  have := congrArg (fun C => conjSubgroup C g⁻¹) h
  simpa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using this

theorem eq_of_mul_eq_mul_of_disjoint {G : Type*} [Group G] {A B : Subgroup G}
    (hdis : Disjoint A B) {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B)
    (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h]
  have hA : a'⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha') ha
  have hB : a'⁻¹ * a ∈ B := h1 ▸ B.mul_mem hb' (B.inv_mem hb)
  have h2 : a'⁻¹ * a = 1 := by
    have := hdis.le_bot ⟨hA, hB⟩
    simpa using this
  have h3 : a = a' := by
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

theorem lemma_G64_3_one [Finite V] (Q2 : QuotedTransvectionNormalizers.{u}) (h : Hypothesis61 X a)
    {Ks : Fin 1 → Subgroup (MulAut V)} (hd : G64Decomposition X a Ks) :
    X = classClosure X a := by
  refine le_antisymm (fun g hg => ?_) (classClosure_le h.mem)
  obtain ⟨h1, h2⟩ := Q2 V h.sq_eq_one (classClosure X a) 1 Ks hd.decomp g
    (fun k hk => conj_mem_classClosure_of_mem hg hk)
  apply h2
  intro i
  obtain ⟨j, hj⟩ := h1 i
  rwa [Subsingleton.elim j i] at hj

theorem mem_classClosure_of_fixes_first [Finite V] (Q2 : QuotedTransvectionNormalizers.{u})
    (h : Hypothesis61 X a) {Ks : Fin 2 → Subgroup (MulAut V)} (hd : G64Decomposition X a Ks)
    {g : MulAut V} (hg : g ∈ X) (h0 : conjSubgroup (Ks 0) g = Ks 0) : g ∈ classClosure X a := by
  have hdd := hd.decomp
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hq2 := Q2 V h.sq_eq_one (classClosure X a) 2 Ks hdd g
    (fun k hk => conj_mem_classClosure_of_mem hg hk)
  have hne01 : ∀ i j : Fin 2, i ≠ j → conjSubgroup (Ks i) g ≠ conjSubgroup (Ks j) g := by
    intro i j hij heq
    have := conjSubgroup_inj heq
    have hdij : Disjoint (Ks i) (Ks j) := hdd.indep.pairwiseDisjoint hij
    apply hdd.ne_bot i
    rw [eq_bot_iff]
    intro x hx
    have hxj : x ∈ Ks j := by rw [← this]; exact hx
    have := hdij.le_bot ⟨hx, hxj⟩
    simpa using this
  refine hq2.2 fun i => ?_
  fin_cases i
  · exact h0
  · obtain ⟨j, hj⟩ := hq2.1 1
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj01 with rfl | rfl
    · exact absurd (hj.trans h0.symm) (hne01 1 0 h01.symm)
    · exact hj

theorem lemma_G64_3_two [Finite V] (Q2 : QuotedTransvectionNormalizers.{u}) (h : Hypothesis61 X a)
    {Ks : Fin 2 → Subgroup (MulAut V)} (hd : G64Decomposition X a Ks) :
    IsSmallG64Type (Ks 0) ∧ IsSmallG64Type (Ks 1) ∧
      ∃ t ∈ X, t * t = 1 ∧ X = classClosure X a ⊔ Subgroup.zpowers t ∧
        conjSubgroup (Ks 0) t = Ks 1 := by
  have hdd := hd.decomp
  refine ⟨hdd.small rfl 0, hdd.small rfl 1, ?_⟩
  set K := classClosure X a with hK
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hdis : Disjoint (Ks 0) (Ks 1) := hdd.indep.pairwiseDisjoint h01
  have hKeq : K = Ks 0 ⊔ Ks 1 := by rw [← hdd.iSup_eq, iSup_fin_two]
  have hnb0 := hdd.ne_bot 0
  have hnb1 := hdd.ne_bot 1
  have hKX : K ≤ X := classClosure_le h.mem
  have hq2 : ∀ g ∈ X, (∀ i, ∃ j, conjSubgroup (Ks i) g = Ks j) ∧
      ((∀ i, conjSubgroup (Ks i) g = Ks i) → g ∈ K) := fun g hg =>
    Q2 V h.sq_eq_one K 2 Ks hdd g (fun k hk => conj_mem_classClosure_of_mem hg hk)
  have hKn0 : K ≤ Subgroup.normalizer (Ks 0 : Set (MulAut V)) := by
    rw [hKeq]
    exact sup_le Subgroup.le_normalizer
      ((hdd.centralize 1 0 h01.symm).trans (Subgroup.centralizer_le_normalizer _))
  have hKn1 : K ≤ Subgroup.normalizer (Ks 1 : Set (MulAut V)) := by
    rw [hKeq]
    exact sup_le ((hdd.centralize 0 1 h01).trans (Subgroup.centralizer_le_normalizer _))
      Subgroup.le_normalizer
  have hKfix1 : ∀ k ∈ K, conjSubgroup (Ks 1) k = Ks 1 := fun k hk =>
    conjSubgroup_eq_iff_mem_normalizer.2 (hKn1 hk)
  have hne01 : ∀ g : MulAut V, ∀ i j : Fin 2, i ≠ j → conjSubgroup (Ks i) g ≠ conjSubgroup (Ks j) g := by
    intro g i j hij heq
    have := conjSubgroup_inj heq
    have hdij : Disjoint (Ks i) (Ks j) := hdd.indep.pairwiseDisjoint hij
    apply hdd.ne_bot i
    rw [eq_bot_iff]
    intro x hx
    have hxj : x ∈ Ks j := by rw [← this]; exact hx
    have := hdij.le_bot ⟨hx, hxj⟩
    simpa using this
  have hF4 : ∀ g ∈ X, conjSubgroup (Ks 0) g = Ks 0 → conjSubgroup (Ks 1) g = Ks 1 := by
    intro g hg h0
    obtain ⟨j, hj⟩ := (hq2 g hg).1 1
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj01 with rfl | rfl
    · exact absurd (hj.trans h0.symm) (hne01 g 1 0 h01.symm)
    · exact hj
  have hX0 : ∀ g ∈ X, conjSubgroup (Ks 0) g = Ks 0 → g ∈ K := by
    intro g hg h0
    refine (hq2 g hg).2 fun i => ?_
    fin_cases i
    · exact h0
    · exact hF4 g hg h0
  obtain ⟨g, hgX, hg0⟩ := hd.transitive 0 1
  have hg1 : conjSubgroup (Ks 1) g = Ks 0 := by
    obtain ⟨j, hj⟩ := (hq2 g hgX).1 1
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj01 with rfl | rfl
    · exact hj
    · exact absurd (hj.trans hg0.symm) (hne01 g 1 0 h01.symm)
  have hgg : g * g ∈ K := by
    refine hX0 (g * g) (X.mul_mem hgX hgX) ?_
    rw [← conjSubgroup_conjSubgroup, hg0, hg1]
  obtain ⟨k₀, hk₀, k₁, hk₁, hk₀₁⟩ := mem_sup_of_centralizes (hdd.centralize 0 1 h01)
    (hKeq ▸ hgg)
  have hgk₀ : g * k₀ * g⁻¹ ∈ Ks 1 := by
    have : k₀ ∈ conjSubgroup (Ks 1) g := by rw [hg1]; exact hk₀
    exact mem_conjSubgroup_iff.1 this
  have hgk₁ : g * k₁ * g⁻¹ ∈ Ks 0 := by
    have : k₁ ∈ conjSubgroup (Ks 0) g := by rw [hg0]; exact hk₁
    exact mem_conjSubgroup_iff.1 this
  have hprod : (g * k₁ * g⁻¹) * (g * k₀ * g⁻¹) = k₀ * k₁ := by
    have hcomm : (g * k₀ * g⁻¹) * (g * k₁ * g⁻¹) = (g * k₁ * g⁻¹) * (g * k₀ * g⁻¹) :=
      ((hdd.centralize 1 0 h01.symm) hgk₀ (g * k₁ * g⁻¹) hgk₁).symm
    rw [← hcomm]
    calc g * k₀ * g⁻¹ * (g * k₁ * g⁻¹) = g * (k₀ * k₁) * g⁻¹ := by group
      _ = g * (g * g) * g⁻¹ := by rw [hk₀₁]
      _ = g * g := by group
      _ = k₀ * k₁ := hk₀₁.symm
  obtain ⟨e1, e0⟩ := eq_of_mul_eq_mul_of_disjoint hdis hgk₁ hk₀ hgk₀ hk₁ hprod
  have h1 : g * k₁ = k₀ * g := by rw [← e1]; group
  have h2 : k₀⁻¹ * g = g * k₁⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul]
    have : k₀ * (g * k₁⁻¹) = g := by rw [← mul_assoc, ← h1]; group
    exact this.symm
  have hk₀K : k₀ ∈ K := by rw [hKeq]; exact Subgroup.mem_sup_left hk₀
  have ht : g * k₀⁻¹ ∈ X := X.mul_mem hgX (X.inv_mem (hKX hk₀K))
  have htt : g * k₀⁻¹ * (g * k₀⁻¹) = 1 := by
    calc g * k₀⁻¹ * (g * k₀⁻¹) = g * (k₀⁻¹ * g) * k₀⁻¹ := by group
      _ = g * (g * k₁⁻¹) * k₀⁻¹ := by rw [h2]
      _ = (g * g) * k₁⁻¹ * k₀⁻¹ := by group
      _ = (k₀ * k₁) * k₁⁻¹ * k₀⁻¹ := by rw [hk₀₁]
      _ = 1 := by group
  refine ⟨g * k₀⁻¹, ht, htt, ?_, ?_⟩
  · refine le_antisymm (fun g' hg' => ?_) (sup_le hKX (Subgroup.zpowers_le.2 ht))
    obtain ⟨j, hj⟩ := (hq2 g' hg').1 0
    have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hj01 with rfl | rfl
    · exact Subgroup.mem_sup_left (hX0 g' hg' hj)
    · have hX1 : conjSubgroup (Ks 0) (g' * g⁻¹) = Ks 0 := by
        rw [← conjSubgroup_conjSubgroup, hj, ← hg0, conjSubgroup_conjSubgroup, mul_inv_cancel,
          conjSubgroup_one]
      have hg'' : g' * g⁻¹ ∈ K := hX0 _ (X.mul_mem hg' (X.inv_mem hgX)) hX1
      have : g' = (g' * g⁻¹) * (g * k₀⁻¹) * k₀ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg'')
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_left hk₀K)
  · rw [← conjSubgroup_conjSubgroup, hg0]
    exact hKfix1 _ (K.inv_mem hk₀K)

theorem IsTransvectionDecomposition.le_normalizer {K : Subgroup (MulAut V)} {s : ℕ}
    {Ks : Fin s → Subgroup (MulAut V)} (hd : IsTransvectionDecomposition K Ks) (i : Fin s) :
    K ≤ Subgroup.normalizer (Ks i : Set (MulAut V)) := by
  rw [← hd.iSup_eq]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · exact (hd.centralize j i hij).trans (Subgroup.centralizer_le_normalizer _)

theorem lemma_G64_4 [Finite V] (Q2 : QuotedTransvectionNormalizers.{u}) (h : Hypothesis61 X a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)}
    (hd : G64Decomposition X a Ks)
    (hT : ∃ T : Subgroup (MulAut V), CFSG.QuasithinUnique.IsSylowTwoOf T X ∧ a ∈ T ∧
      ∀ t ∈ T, t * a = a * t) :
    s = 1 ∧ X = classClosure X a ∧
      ((∃ n, 2 ≤ n ∧ n ≤ 5 ∧ Nonempty (X ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2))) ∨
        Nonempty (X ≃* Equiv.Perm (Fin 6)) ∨ Nonempty (X ≃* Equiv.Perm (Fin 7))) := by
  obtain ⟨T, ⟨hTX, hTp, hTi⟩, haT, hcent⟩ := hT
  have hdd := hd.decomp
  have hs12 : s = 1 ∨ s = 2 := by have := hdd.pos; have := hdd.le_two; omega
  have hs1 : s = 1 := by
    rcases hs12 with hs | hs
    · exact hs
    · exfalso
      subst hs
      obtain ⟨_, _, t, htX, htt, hXeq, hconj⟩ := lemma_G64_3_two Q2 h hd
      set K := classClosure X a with hK
      have h01 : (0 : Fin 2) ≠ 1 := by decide
      have hdis : Disjoint (Ks 0) (Ks 1) := hdd.indep.pairwiseDisjoint h01
      have ha0 : a ∈ Ks 0 := hd.mem_first.choose_spec
      have hTK : T ≤ K := by
        intro τ hτ
        refine mem_classClosure_of_fixes_first Q2 h hd (hTX hτ) ?_
        obtain ⟨j, hj⟩ := hd.permute τ (hTX hτ) 0
        have haτ : a ∈ conjSubgroup (Ks 0) τ := by
          rw [mem_conjSubgroup_iff, hcent τ hτ]
          simpa using ha0
        have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        rcases hj01 with rfl | rfl
        · exact hj
        · exfalso
          rw [hj] at haτ
          have := hdis.le_bot ⟨ha0, haτ⟩
          exact h.ne_one (by simpa using this)
      have hne : ¬ X ≤ K := by
        intro hXK
        obtain ⟨g, hgX, hg0⟩ := hd.transitive 0 1
        have hgn : conjSubgroup (Ks 0) g = Ks 0 :=
          conjSubgroup_eq_iff_mem_normalizer.2 (hdd.le_normalizer 0 (hXK hgX))
        have heq : Ks 0 = Ks 1 := hgn.symm.trans hg0
        apply hdd.ne_bot 0
        rw [eq_bot_iff]
        intro x hx
        have hx1 : x ∈ Ks 1 := by rw [← heq]; exact hx
        have := hdis.le_bot ⟨hx, hx1⟩
        simpa using this
      have hdvd : K.relIndex X ∣ 2 := by
        rw [Subgroup.relIndex_dvd_two_iff]
        refine ⟨t, htX, fun b hb => ?_⟩
        obtain ⟨j, hj⟩ := hd.permute b hb 0
        have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        rcases hj01 with rfl | rfl
        · exact Or.inr (mem_classClosure_of_fixes_first Q2 h hd hb hj)
        · refine Or.inl (mem_classClosure_of_fixes_first Q2 h hd (X.mul_mem hb htX) ?_)
          rw [← conjSubgroup_conjSubgroup, hj, ← hconj, conjSubgroup_conjSubgroup, htt,
            conjSubgroup_one]
      have hne1 : K.relIndex X ≠ 1 := fun h1 => hne (Subgroup.relIndex_eq_one.1 h1)
      have h2 : K.relIndex X = 2 := ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne1
      have hmul := Subgroup.relIndex_mul_relIndex T K X hTK (classClosure_le h.mem)
      apply hTi
      change 2 ∣ T.relIndex X
      rw [← hmul, h2]
      exact Dvd.intro_left _ rfl
  subst hs1
  have hXK : X = classClosure X a := lemma_G64_3_one Q2 h hd
  have hK0 : Ks 0 = X := by
    have := hdd.iSup_eq
    rw [iSup_unique] at this
    rw [hXK]
    exact this
  refine ⟨rfl, hXK, ?_⟩
  have ha0 : a ∈ Ks 0 := hd.mem_first.choose_spec
  have hTX0 : T ≤ Ks 0 := hK0 ▸ hTX
  have hTi0 : ¬ 2 ∣ (T.subgroupOf (Ks 0)).index := by rw [hK0]; exact hTi
  rcases hdd.type 0 with ⟨n, hn2, hn5, hL⟩ | ⟨n, hn5, hn8, ⟨θ, β, hequiv, hrange, hker⟩⟩ |
      ⟨n, hn, ⟨θ, β, hequiv, hrange, hker⟩⟩
  · obtain ⟨⟨e⟩, _, _⟩ := hL
    exact Or.inl ⟨n, hn2, hn5, ⟨(MulEquiv.subgroupCongr hK0.symm).trans e⟩⟩
  · have hsw := isSwap_of_card_commV_eq_two (by omega : 5 ≤ n) θ β hequiv (hker ▸ le_rfl) ha0 htr
    have hn5' : n ≠ 5 := fun hn' =>
      not_central_in_sylow_of_isSwap (Or.inl hn') θ ha0 hsw hTX0 hTp hTi0 (fun t ht => hcent t ht)
    have hn8' : n ≠ 8 := fun hn' =>
      not_central_in_sylow_of_isSwap (Or.inr hn') θ ha0 hsw hTX0 hTp hTi0 (fun t ht => hcent t ht)
    have h67 : n = 6 ∨ n = 7 := by omega
    rcases h67 with rfl | rfl
    · exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hK0.symm).trans θ⟩)
    · exact Or.inr (Or.inr ⟨(MulEquiv.subgroupCongr hK0.symm).trans θ⟩)
  · have hsw := isSwap_of_card_commV_eq_two (by omega : 5 ≤ n) θ β hequiv
      (hker ▸ bot_le) ha0 htr
    have hn8' : n ≠ 8 := fun hn' =>
      not_central_in_sylow_of_isSwap (Or.inr hn') θ ha0 hsw hTX0 hTp hTi0 (fun t ht => hcent t ht)
    have h6 : n = 6 := by omega
    subst h6
    exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hK0.symm).trans θ⟩)

theorem lemma_G64_2 {s : ℕ} {Ks : Fin s → Subgroup (MulAut V)} (hd : G64Decomposition X a Ks)
    (i : Fin s) :
    IsHSubmodule (Ks i) (commV (Ks i)) ∧ IsG64Type (Ks i) (commV (Ks i)) :=
  ⟨hd.decomp.isHSubmodule i, hd.decomp.type i⟩

theorem lemma_G64 [Finite V] (Q1 : QuotedTransvectionClassification.{u})
    (Q2 : QuotedTransvectionNormalizers.{u}) (h : Hypothesis61 X a)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    (∃ Ks : Fin 1 → Subgroup (MulAut V), G64Decomposition X a Ks ∧ X = classClosure X a) ∨
    (∃ Ks : Fin 2 → Subgroup (MulAut V), G64Decomposition X a Ks ∧ IsSmallG64Type (Ks 0) ∧
      IsSmallG64Type (Ks 1) ∧ ∃ t ∈ X, t * t = 1 ∧ X = classClosure X a ⊔ Subgroup.zpowers t ∧
        conjSubgroup (Ks 0) t = Ks 1) := by
  obtain ⟨s, Ks, hd⟩ := lemma_G64_1 Q1 Q2 h htr
  have hs : s = 1 ∨ s = 2 := by
    have := hd.decomp.pos
    have := hd.decomp.le_two
    omega
  rcases hs with rfl | rfl
  · exact Or.inl ⟨Ks, hd, lemma_G64_3_one Q2 h hd⟩
  · exact Or.inr ⟨Ks, hd, lemma_G64_3_two Q2 h hd⟩

end Apply

end G6

end CFSG.Quasithin
