module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def IsLeviBlock (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (X ≃* Equiv.Perm (Fin 6)) ∨
    (CFSG.Open.IsQuasisimple X ∧ Odd (Nat.card (center X)) ∧ 2 ∣ Nat.card X)

theorem IsLeviBlock.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsLeviBlock X) : IsLeviBlock X' := by
  rcases h with h3 | h6 | ⟨hq, ho, h2⟩
  · obtain ⟨e3⟩ := h3
    exact Or.inl ⟨e.symm.trans e3⟩
  · obtain ⟨e6⟩ := h6
    exact Or.inr (Or.inl ⟨e.symm.trans e6⟩)
  · exact Or.inr (Or.inr ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq,
      Nat.card_congr (Subgroup.centerCongr e).toEquiv ▸ ho, Nat.card_congr e.toEquiv ▸ h2⟩)

@[expose] def CensusAlt {ι : Type} {G : ι → Type} [∀ j, Group (G j)]
    (S : ∀ j, Subgroup (G j)) : Prop :=
  (Nat.card {j // S j ≠ ⊥} ≤ 2 ∧ ∀ j, S j = ⊥ ∨ CFSG.Open.IsQuasisimple ↥(S j)) ∨
    ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → ∀ n, 3 ≤ n → ¬ IsL2 (↥(S j) ⧸ center ↥(S j)) n

@[expose] def HasLeviData (R : Type) [Group R] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (σ : Q →* R) (ι : Type) (_ : Finite ι)
    (G : ι → Type) (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j))
    (S : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j),
    Function.Surjective σ ∧ σ.ker ≤ center Q ∧ Odd (Nat.card σ.ker) ∧ IsPGroup 2 β.ker ∧
    Subgroup.pi Set.univ S ≤ β.range ∧
    β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)) ∧
    ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range ∧
    (∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) ∧ CensusAlt S

@[expose] def BlockFacts (two big : Prop) {ι : Type} {G : ι → Type} [∀ j, Group (G j)]
    (S : ∀ j, Subgroup (G j)) : Prop :=
  (∀ j, CFSG.Open.IsQuasisimple ↥(S j) → 3 ∣ Nat.card (↥(S j) ⧸ center ↥(S j))) ∧
    (∀ j, Nonempty (↥(S j) ≃* Equiv.Perm (Fin 3)) → two) ∧
    (Nat.card {j // S j ≠ ⊥} ≤ 2 ∨ big)

theorem BlockFacts.mono {two big two' big' : Prop} {ι : Type} {G : ι → Type}
    [∀ j, Group (G j)] {S : ∀ j, Subgroup (G j)} (h2 : two → two') (hb : big → big')
    (h : BlockFacts two big S) : BlockFacts two' big' S :=
  ⟨h.1, fun j hj => h2 (h.2.1 j hj), h.2.2.imp_right hb⟩

@[expose] def HasLeviDataX (two big : Prop) (R : Type) [Group R] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (σ : Q →* R) (ι : Type) (_ : Finite ι)
    (G : ι → Type) (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j))
    (S : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j),
    Function.Surjective σ ∧ σ.ker ≤ center Q ∧ Odd (Nat.card σ.ker) ∧ IsPGroup 2 β.ker ∧
    Subgroup.pi Set.univ S ≤ β.range ∧
    β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)) ∧
    ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range ∧
    (∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) ∧ CensusAlt S ∧ BlockFacts two big S

theorem HasLeviDataX.hasLeviData {two big : Prop} {R : Type} [Group R]
    (h : HasLeviDataX two big R) : HasLeviData R := by
  obtain ⟨Q, _, _, σ, ι, _, G, _, _, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, halt, -⟩ := h
  exact ⟨Q, inferInstance, inferInstance, σ, ι, inferInstance, G, inferInstance, inferInstance,
    S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, halt⟩

theorem HasLeviDataX.mono {two big two' big' : Prop} {R : Type} [Group R] (h2 : two → two')
    (hb : big → big') (h : HasLeviDataX two big R) : HasLeviDataX two' big' R := by
  obtain ⟨Q, _, _, σ, ι, _, G, _, _, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, halt, hB⟩ := h
  exact ⟨Q, inferInstance, inferInstance, σ, ι, inferInstance, G, inferInstance, inferInstance,
    S, β, hσ, hc, ho, hβ, hle, hn, hi, hS, halt, hB.mono h2 hb⟩

theorem not_nonempty_mulEquiv_perm_three {Y : Type} [Group Y] {H : Subgroup Y}
    (h : H = ⊥ ∨ CFSG.Open.IsQuasisimple ↥H) : ¬ Nonempty (↥H ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨e⟩
  rcases h with hbot | hq
  · have hc := Nat.card_congr e.toEquiv
    rw [hbot, Subgroup.card_bot, Nat.card_perm, Nat.card_fin] at hc
    norm_num at hc
  · have hker : (Equiv.Perm.sign.comp e.toMonoidHom).ker = ⊤ :=
      top_le_iff.mp (hq.1 ▸ Abelianization.commutator_subset_ker _)
    have h1 : e.symm (Equiv.swap 0 1) ∈ (Equiv.Perm.sign.comp e.toMonoidHom).ker :=
      hker ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
    simp at h1

private theorem exists_restrict_cover {X C : Type} [Group X] [Group C] [Finite C]
    {L J : Subgroup X} (hJL : J ≤ L) (ρ : C →* ↥L) (hρ : Function.Surjective ρ)
    (hc : ρ.ker ≤ center C) (ho : Odd (Nat.card ρ.ker)) :
    ∃ σ : ↥((J.subgroupOf L).comap ρ) →* ↥J, Function.Surjective σ ∧
      σ.ker ≤ center ↥((J.subgroupOf L).comap ρ) ∧ Odd (Nat.card σ.ker) := by
  classical
  let Q : Subgroup C := (J.subgroupOf L).comap ρ
  let σ : ↥Q →* ↥J :=
    (Subgroup.subgroupOfEquivOfLe hJL).toMonoidHom.comp
      ((ρ.domRestrict Q).codRestrict (J.subgroupOf L) fun c => c.2)
  have hσcoe : ∀ c : ↥Q, ((σ c : ↥J) : X) = (ρ (c : C) : X) := fun c =>
    Subgroup.subgroupOfEquivOfLe_apply_coe hJL _
  have hσ : Function.Surjective σ := by
    intro j
    obtain ⟨c, hc⟩ := hρ ⟨(j : X), hJL j.2⟩
    have hcQ : c ∈ Q := by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hc]
      exact j.2
    refine ⟨⟨c, hcQ⟩, Subtype.ext ?_⟩
    rw [hσcoe]
    exact congrArg Subtype.val hc
  have hσker_coe : ∀ z : ↥Q, z ∈ σ.ker → ρ (z : C) = 1 := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    refine Subtype.ext ?_
    rw [← hσcoe z, hz]
    rfl
  have hσker : σ.ker ≤ center ↥Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hc (hσker_coe z hz)) (w : C))
  have hker_le : ρ.ker ≤ Q := by
    intro c hc'
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.mem_ker.mp hc']
    exact J.one_mem
  have hkerEq : σ.ker = (ρ.ker).subgroupOf Q := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun hz => hσker_coe z (by rwa [MonoidHom.mem_ker]),
      fun hz => Subtype.ext (by rw [hσcoe]; simpa using congrArg Subtype.val hz)⟩
  have hcard : Nat.card σ.ker = Nat.card ρ.ker := by
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  exact ⟨σ, hσ, hσker, hcard ▸ ho⟩

theorem hasLeviDataX_of_cover {two big : Prop} {X C : Type} [Group X] [Group C] [Finite C]
    {L J : Subgroup X} (hJL : J ≤ L) (ρ : C →* ↥L) (hρ : Function.Surjective ρ)
    (hc : ρ.ker ≤ center C) (ho : Odd (Nat.card ρ.ker)) {ι : Type} [Finite ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    (β : ↥((J.subgroupOf L).comap ρ) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) (halt : CensusAlt S)
    (hB : BlockFacts two big S) : HasLeviDataX two big ↥J := by
  obtain ⟨σ, hσ, hσker, hσo⟩ := exists_restrict_cover hJL ρ hρ hc ho
  exact ⟨_, inferInstance, inferInstance, σ, ι, inferInstance, G, inferInstance, inferInstance,
    S, β, hσ, hσker, hσo, hβ, hle, hn, hi, hS, halt, hB⟩

theorem hasLeviDataX_of_mulEquiv {two big : Prop} {X C : Type} [Group X] [Group C] [Finite C]
    {L J : Subgroup X} (hJL : J ≤ L) (ρ : C ≃* ↥L) {ι : Type} [Finite ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    (β : ↥((J.subgroupOf L).comap ρ.toMonoidHom) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range)
    (hS : ∀ j, S j = ⊥ ∨ IsLeviBlock ↥(S j)) (halt : CensusAlt S)
    (hB : BlockFacts two big S) : HasLeviDataX two big ↥J := by
  have hker : ρ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr ρ.injective
  refine hasLeviDataX_of_cover hJL ρ.toMonoidHom ρ.surjective ?_ ?_ β hβ hle hn hi hS halt hB
  · rw [hker]
    exact bot_le
  · rw [hker, Subgroup.card_bot]
    exact odd_one

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
