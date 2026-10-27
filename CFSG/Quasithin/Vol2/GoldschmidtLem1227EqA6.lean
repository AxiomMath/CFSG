module

public import CFSG.Quasithin.H13.Sp62S6Over
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAbs

public section

namespace CFSG.Quasithin.H13.Lem1227Eq

open Equiv Equiv.Perm CFSG.Quasithin.H13.A6 CFSG.QuasithinUnique

@[expose] def Dsub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ QA6list}
  one_mem' := by decide +kernel
  mul_mem' := by
    have key : ∀ a ∈ QA6list, ∀ b ∈ QA6list, a * b ∈ QA6list := by decide +kernel
    intro a b ha hb
    exact key a ha b hb
  inv_mem' := by
    have key : ∀ a ∈ QA6list, a⁻¹ ∈ QA6list := by decide +kernel
    intro a ha
    exact key a ha

theorem mem_Dsub {σ : Perm (Fin 6)} : σ ∈ Dsub ↔ σ ∈ QA6list := Iff.rfl

theorem Dsub_le_alternating : Dsub ≤ alternatingGroup (Fin 6) := by
  have key : ∀ a ∈ QA6list, sign a = 1 := by decide +kernel
  intro a ha
  exact Equiv.Perm.mem_alternatingGroup.2 (key a ha)

theorem card_Dsub : Nat.card Dsub = 8 := by
  have h : Nat.card Dsub = (QA6list.toFinset).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun σ => by simp [mem_Dsub]))
  rw [h]
  decide +kernel

abbrev Alt6 : Type := ↥(alternatingGroup (Fin 6))

@[expose] def S6 : Subgroup Alt6 := Dsub.subgroupOf (alternatingGroup (Fin 6))

theorem card_S6 : Nat.card S6 = 8 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Dsub_le_alternating).toEquiv).trans card_Dsub

theorem card_Alt6 : Nat.card Alt6 = 360 := by
  rw [Lem8.card_alternatingGroup_fin (by norm_num)]
  decide

theorem isSylowTwoOf_S6 : IsSylowTwoOf S6 ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowTwoOf_top_iff']
  refine ⟨IsPGroup.of_card (n := 3) (by rw [card_S6]; norm_num), ?_⟩
  have h := S6.index_mul_card
  rw [card_S6, card_Alt6] at h
  have : S6.index = 45 := by omega
  rw [this]
  decide

@[expose] def Q1 : Subgroup Alt6 := P1sub.subgroupOf (alternatingGroup (Fin 6))

@[expose] def Q2 : Subgroup Alt6 := P2sub.subgroupOf (alternatingGroup (Fin 6))

theorem card_Q1 : Nat.card Q1 = 24 := by
  classical
  have h : Nat.card Q1 = (Finset.univ.filter (fun σ : Alt6 => InP1 (σ : Perm (Fin 6)))).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
      simp [Q1, mem_P1sub, Subgroup.mem_subgroupOf])
  rw [h]
  decide +kernel

theorem card_Q2 : Nat.card Q2 = 24 := by
  classical
  have h : Nat.card Q2 = (Finset.univ.filter (fun σ : Alt6 => InP2 (σ : Perm (Fin 6)))).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
      simp [Q2, mem_P2sub, Subgroup.mem_subgroupOf])
  rw [h]
  decide +kernel

theorem lattice_S6 (P : Subgroup Alt6) (hP : S6 ≤ P) :
    Nat.card P = 8 ∨ Nat.card P = 24 ∨ P = ⊤ := by
  have h8 : 8 ∣ Nat.card P := card_S6 ▸ Subgroup.card_dvd_of_le hP
  set Y : Subgroup (Perm (Fin 6)) := P.map (alternatingGroup (Fin 6)).subtype with hY
  have hYA : Y ≤ alternatingGroup (Fin 6) := Subgroup.map_subtype_le P
  have hmemD : ∀ σ ∈ QA6list, σ ∈ Y := fun σ hσ =>
    ⟨⟨σ, Dsub_le_alternating (mem_Dsub.2 hσ)⟩,
      hP (Subgroup.mem_subgroupOf.2 (mem_Dsub.2 hσ)), rfl⟩
  have hga : ga ∈ Y := hmemD _ (by decide +kernel)
  have hgb : gb ∈ Y := hmemD _ (by decide +kernel)
  have hgc : gc ∈ Y := hmemD _ (by decide +kernel)
  have hdiv : ∀ Q : Subgroup Alt6, Nat.card Q = 24 → P ≤ Q →
      Nat.card P = 8 ∨ Nat.card P = 24 := by
    intro Q hQ hle
    have hd : Nat.card P ∣ 24 := hQ ▸ Subgroup.card_dvd_of_le hle
    have hle24 : Nat.card P ≤ 24 := Nat.le_of_dvd (by norm_num) hd
    generalize Nat.card P = n at h8 hd hle24
    interval_cases n <;> omega
  rcases overgroup_A6 Y hYA hga hgb hgc with h | h | h
  · exact (hdiv Q1 card_Q1 fun σ hσ => by
      rw [Q1, Subgroup.mem_subgroupOf, mem_P1sub]
      exact h _ ⟨σ, hσ, rfl⟩).elim Or.inl fun h => Or.inr (Or.inl h)
  · exact (hdiv Q2 card_Q2 fun σ hσ => by
      rw [Q2, Subgroup.mem_subgroupOf, mem_P2sub]
      exact h _ ⟨σ, hσ, rfl⟩).elim Or.inl fun h => Or.inr (Or.inl h)
  · right; right
    rw [eq_top_iff]
    intro σ _
    have hσ : (σ : Perm (Fin 6)) ∈ Y := by rw [h]; exact σ.2
    obtain ⟨p, hp, hpσ⟩ := hσ
    rwa [← Subtype.ext hpσ]

theorem normalizer_S6 : Subgroup.normalizer (S6 : Set Alt6) = S6 := by
  apply le_antisymm
  · intro σ hσ
    have key : ∀ σ : Perm (Fin 6), sign σ = 1 →
        (∀ d ∈ QA6list, σ * d * σ⁻¹ ∈ QA6list) → σ ∈ QA6list := by decide +kernel
    have h := key σ.1 (Equiv.Perm.mem_alternatingGroup.1 σ.2) fun d hd => by
      have hs : (⟨d, Dsub_le_alternating (mem_Dsub.2 hd)⟩ : Alt6) ∈ S6 :=
        Subgroup.mem_subgroupOf.2 (mem_Dsub.2 hd)
      have := (Subgroup.mem_normalizer_iff.1 hσ _).1 hs
      exact mem_Dsub.1 (Subgroup.mem_subgroupOf.1 this)
    exact Subgroup.mem_subgroupOf.2 (mem_Dsub.2 h)
  · exact Subgroup.le_normalizer

@[expose] def HasUniqueCentralInvolution {Q : Type*} [Group Q] (S : Subgroup Q) : Prop :=
  ∃ c ∈ S, c ≠ 1 ∧ c ^ 2 = 1 ∧ (∀ s ∈ S, c * s = s * c) ∧
    ∀ c' ∈ S, c' ≠ 1 → c' ^ 2 = 1 → (∀ s ∈ S, c' * s = s * c') → c' = c

theorem central_S6 : HasUniqueCentralInvolution S6 := by
  have hga : ga ∈ Dsub := mem_Dsub.2 (by decide +kernel)
  have h1 : ga ≠ 1 := by decide +kernel
  have h2 : ga ^ 2 = 1 := by decide +kernel
  have h3 : ∀ s ∈ QA6list, ga * s = s * ga := by decide +kernel
  have h4 : ∀ c' ∈ QA6list, c' ≠ 1 → c' ^ 2 = 1 → (∀ s ∈ QA6list, c' * s = s * c') →
      c' = ga := by decide +kernel
  refine ⟨⟨ga, Dsub_le_alternating hga⟩, Subgroup.mem_subgroupOf.2 hga, ?_, ?_, ?_, ?_⟩
  · intro h
    exact h1 (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using h2)
  · intro s hs
    exact Subtype.ext (h3 _ (mem_Dsub.1 (Subgroup.mem_subgroupOf.1 hs)))
  · intro c' hc' hne hsq hcomm
    refine Subtype.ext (h4 _ (mem_Dsub.1 (Subgroup.mem_subgroupOf.1 hc')) ?_ ?_ ?_)
    · intro h
      exact hne (Subtype.ext h)
    · simpa using congrArg Subtype.val hsq
    · intro s hs
      have hs' : (⟨s, Dsub_le_alternating (mem_Dsub.2 hs)⟩ : Alt6) ∈ S6 :=
        Subgroup.mem_subgroupOf.2 (mem_Dsub.2 hs)
      exact congrArg Subtype.val (hcomm _ hs')

structure A6Syl (Q : Type*) [Group Q] (S : Subgroup Q) : Prop where
  card : Nat.card S = 8
  normalizer : Subgroup.normalizer (S : Set Q) ≤ S
  central : HasUniqueCentralInvolution S
  lattice : ∀ P : Subgroup Q, S ≤ P → Nat.card P = 8 ∨ Nat.card P = 24 ∨ P = ⊤

theorem A6Syl.S6 : A6Syl Alt6 S6 :=
  ⟨card_S6, normalizer_S6.le, central_S6, lattice_S6⟩

theorem A6Syl.of_equiv {Q Q' : Type*} [Group Q] [Group Q'] (ψ : Q ≃* Q') {S : Subgroup Q}
    {S' : Subgroup Q'} (hS : S.map ψ.toMonoidHom = S') (h : A6Syl Q' S') : A6Syl Q S := by
  have hmem : ∀ x : Q, x ∈ S ↔ ψ x ∈ S' := fun x => by
    rw [← hS]
    exact (Subgroup.mem_map_iff_mem ψ.injective).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h.card, ← hS]
    exact (Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective).symm
  · intro x hx
    rw [hmem]
    refine h.normalizer ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    obtain ⟨y, rfl⟩ := ψ.surjective y'
    have h1 := Subgroup.mem_normalizer_iff.1 hx y
    rw [show ψ x * ψ y * (ψ x)⁻¹ = ψ (x * y * x⁻¹) by simp [map_mul, map_inv], ← hmem y,
      ← hmem (x * y * x⁻¹)]
    exact h1
  · obtain ⟨c', hc', h1, h2, h3, h4⟩ := h.central
    obtain ⟨c, rfl⟩ := ψ.surjective c'
    refine ⟨c, (hmem c).2 hc', fun h => h1 (by rw [h, map_one]), ?_, ?_, ?_⟩
    · apply ψ.injective
      rw [map_pow, h2, map_one]
    · intro s hs
      apply ψ.injective
      rw [map_mul, map_mul]
      exact h3 _ ((hmem s).1 hs)
    · intro c₂ hc₂ hne hsq hcomm
      apply ψ.injective
      refine h4 _ ((hmem c₂).1 hc₂) (fun h => hne (ψ.injective (by rw [h, map_one]))) ?_ ?_
      · rw [← map_pow, hsq, map_one]
      · intro s' hs'
        obtain ⟨s, rfl⟩ := ψ.surjective s'
        rw [← map_mul, ← map_mul, hcomm s ((hmem s).2 hs')]
  · intro P hP
    have hP' : S' ≤ P.map ψ.toMonoidHom := by
      rw [← hS]
      exact Subgroup.map_mono hP
    rcases h.lattice _ hP' with h8 | h24 | htop
    · left
      rw [← h8]
      exact (Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective).symm
    · right; left
      rw [← h24]
      exact (Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective).symm
    · right; right
      have := congrArg (Subgroup.comap ψ.toMonoidHom) htop
      rwa [Subgroup.comap_map_eq_self_of_injective ψ.injective, Subgroup.comap_top] at this

theorem A6Syl.of_sylow {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Alt6) {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) : A6Syl Q S := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq_of_sylow e hS isSylowTwoOf_S6
  exact A6Syl.of_equiv ψ hψ A6Syl.S6

theorem A6Syl.maximal_of_card_gt {Q : Type} [Group Q] [Finite Q] {S P : Subgroup Q} (h : A6Syl Q S)
    (hSP : S ≤ P) (hPne : P ≠ ⊤) (hcard : 8 < Nat.card P) :
    Nat.card P = 24 ∧ ∀ R : Subgroup Q, P ≤ R → R = P ∨ R = ⊤ := by
  have h24 : Nat.card P = 24 := by
    rcases h.lattice P hSP with h8 | h24 | htop
    · omega
    · exact h24
    · exact absurd htop hPne
  refine ⟨h24, fun R hPR => ?_⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by omega)
  rcases h.lattice R (hSP.trans hPR) with h8 | h24' | htop
  · have := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hPR)
    omega
  · left
    exact (Subgroup.eq_of_le_of_card_ge hPR (by omega)).symm
  · right
    exact htop

end CFSG.Quasithin.H13.Lem1227Eq
