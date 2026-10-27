module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAltTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Equiv

private theorem card_ofSubtype_range_of_card_five (s : Finset (Fin 10)) (hs : s.card = 5) :
    Nat.card ↥((alternatingGroup.ofSubtype s).range) = 60 := by
  have hcard : Nat.card ↥s = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hs
  have hnt : Nontrivial ↥s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have he : alternatingGroup ↥s ≃* (alternatingGroup.ofSubtype s).range :=
    MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))
  rw [← Nat.card_congr he.toEquiv, nat_card_alternatingGroup, hcard]
  decide

private lemma exists_mem_ofSubtype_range_map_pair (B : Finset (Fin 10)) (hB : 4 ≤ B.card)
    {y z u v : Fin 10} (hyB : y ∈ B) (hzB : z ∈ B) (huB : u ∈ B) (hvB : v ∈ B)
    (hyz : y ≠ z) (huv : u ≠ v) :
    ∃ φ ∈ (alternatingGroup.ofSubtype B).range,
      (φ : Equiv.Perm (Fin 10)) y = u ∧ (φ : Equiv.Perm (Fin 10)) z = v := by
  have hBcard : 4 ≤ Nat.card ↥B := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hB
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup ↥B) ↥B 2 := by
    have hint := alternatingGroup.isMultiplyPretransitive ↥B
    exact MulAction.isMultiplyPretransitive_of_le (m := 2) (n := Nat.card ↥B - 2)
      (by omega) (by omega)
  obtain ⟨w, hwy, hwz⟩ := MulAction.is_two_pretransitive_iff.mp h2
    (show (⟨y, hyB⟩ : ↥B) ≠ ⟨z, hzB⟩ from fun hcon => hyz (Subtype.ext_iff.mp hcon))
    (show (⟨u, huB⟩ : ↥B) ≠ ⟨v, hvB⟩ from fun hcon => huv (Subtype.ext_iff.mp hcon))
  have hwy' : w.1 ⟨y, hyB⟩ = ⟨u, huB⟩ := by
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hwy
  have hwz' : w.1 ⟨z, hzB⟩ = ⟨v, hvB⟩ := by
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hwz
  refine ⟨alternatingGroup.ofSubtype B w, MonoidHom.mem_range.mpr ⟨w, rfl⟩, ?_, ?_⟩
  · rw [alternatingGroup.coe_ofSubtype, Equiv.Perm.ofSubtype_apply_of_mem _ hyB]
    exact Subtype.ext_iff.mp hwy'
  · rw [alternatingGroup.coe_ofSubtype, Equiv.Perm.ofSubtype_apply_of_mem _ hzB]
    exact Subtype.ext_iff.mp hwz'

private theorem sup_ofSubtype_range_eq_top (A B : Finset (Fin 10))
    (hAB : A ∪ B = Finset.univ) (hInter : 2 ≤ (A ∩ B).card) (hBcard : 4 ≤ B.card) :
    (alternatingGroup.ofSubtype A).range ⊔ (alternatingGroup.ofSubtype B).range = ⊤ := by
  classical
  apply eq_top_iff.mpr
  rw [← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
  rintro g hg
  set D : Finset (Fin 10) := (g : Equiv.Perm (Fin 10)).support with hDdef
  have hDcard : D.card = 3 := hg.card_support
  by_cases hDA : D ⊆ A
  · exact Subgroup.mem_sup_left ((alternatingGroup.mem_range_ofSubtype_iff A g).mpr hDA)
  by_cases hDB : D ⊆ B
  · exact Subgroup.mem_sup_right ((alternatingGroup.mem_range_ofSubtype_iff B g).mpr hDB)
  have hDsub : D ⊆ A ∪ B := by rw [hAB]; exact Finset.subset_univ D
  have hexA : ∃ x ∈ D, x ∉ A := by
    by_contra hcon
    push Not at hcon
    exact hDA hcon
  have hEsubD : D ∩ B ⊆ D := Finset.inter_subset_left
  have hEneD : D ∩ B ≠ D := by
    intro heq
    exact hDB (heq ▸ Finset.inter_subset_right)
  have hEcard_le : (D ∩ B).card ≤ 2 := by
    have hle : (D ∩ B).card ≤ D.card := Finset.card_le_card hEsubD
    have hne : (D ∩ B).card ≠ D.card := fun hc =>
      hEneD (Finset.eq_of_subset_of_card_le hEsubD (le_of_eq hc.symm))
    omega
  have hEcard_ge : 1 ≤ (D ∩ B).card := by
    obtain ⟨x, hxD, hxA⟩ := hexA
    have hxB : x ∈ B := by
      rcases Finset.mem_union.mp (hDsub hxD) with h | h
      · exact absurd h hxA
      · exact h
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxD, hxB⟩⟩
  have hyz_exists : ∃ y z : Fin 10, y ∈ B ∧ z ∈ B ∧ y ≠ z ∧ D ∩ B ⊆ {y, z} := by
    rcases (show (D ∩ B).card = 1 ∨ (D ∩ B).card = 2 by omega) with h1 | h2
    · obtain ⟨y, hEeq⟩ := Finset.card_eq_one.mp h1
      have hyE : y ∈ D ∩ B := by rw [hEeq]; exact Finset.mem_singleton_self y
      have hyB : y ∈ B := (Finset.mem_inter.mp hyE).2
      have hz_exists : ∃ z ∈ B, z ≠ y := by
        by_contra hcon
        push Not at hcon
        have hsub : B ⊆ {y} := fun z hz => by rw [Finset.mem_singleton]; exact hcon z hz
        have hle : B.card ≤ ({y} : Finset (Fin 10)).card := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hle
        omega
      obtain ⟨z, hzB, hzy⟩ := hz_exists
      refine ⟨y, z, hyB, hzB, Ne.symm hzy, ?_⟩
      rw [hEeq]
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self y {z})
    · obtain ⟨y, z, hyz, hEeq⟩ := Finset.card_eq_two.mp h2
      have hyB : y ∈ B := by
        have : y ∈ D ∩ B := by rw [hEeq]; exact Finset.mem_insert_self y {z}
        exact (Finset.mem_inter.mp this).2
      have hzB : z ∈ B := by
        have : z ∈ D ∩ B := by rw [hEeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self z)
        exact (Finset.mem_inter.mp this).2
      refine ⟨y, z, hyB, hzB, hyz, ?_⟩
      rw [hEeq]
  obtain ⟨y, z, hyB, hzB, hyz, hEsub⟩ := hyz_exists
  obtain ⟨u, huAB, v, hvAB, huv⟩ := Finset.one_lt_card.mp (show 1 < (A ∩ B).card by omega)
  have huA : u ∈ A := (Finset.mem_inter.mp huAB).1
  have huB : u ∈ B := (Finset.mem_inter.mp huAB).2
  have hvA : v ∈ A := (Finset.mem_inter.mp hvAB).1
  have hvB : v ∈ B := (Finset.mem_inter.mp hvAB).2
  obtain ⟨φ, hφmem, hφy, hφz⟩ :=
    exists_mem_ofSubtype_range_map_pair B hBcard hyB hzB huB hvB hyz huv
  have hφsupp : (φ : Equiv.Perm (Fin 10)).support ⊆ B :=
    (alternatingGroup.mem_range_ofSubtype_iff B φ).mp hφmem
  have hmapDA : D.map (φ : Equiv.Perm (Fin 10)).toEmbedding ⊆ A := by
    intro w hw
    obtain ⟨x, hxD, rfl⟩ := Finset.mem_map.mp hw
    change (φ : Equiv.Perm (Fin 10)) x ∈ A
    by_cases hxB : x ∈ B
    · have hxE : x ∈ D ∩ B := Finset.mem_inter.mpr ⟨hxD, hxB⟩
      have hx12 : x ∈ ({y, z} : Finset (Fin 10)) := hEsub hxE
      rw [Finset.mem_insert, Finset.mem_singleton] at hx12
      rcases hx12 with rfl | rfl
      · rw [hφy]; exact huA
      · rw [hφz]; exact hvA
    · have hxfix : (φ : Equiv.Perm (Fin 10)) x = x := by
        rw [← Equiv.Perm.notMem_support]
        exact fun hx => hxB (hφsupp hx)
      rw [hxfix]
      have hxA : x ∈ A := by
        have : x ∈ A ∪ B := by rw [hAB]; exact Finset.mem_univ x
        rw [Finset.mem_union] at this
        exact this.resolve_right hxB
      exact hxA
  have hconjA : φ * g * φ⁻¹ ∈ (alternatingGroup.ofSubtype A).range := by
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    have hcoe : (↑(φ * g * φ⁻¹) : Equiv.Perm (Fin 10)) =
        (φ : Equiv.Perm (Fin 10)) * (g : Equiv.Perm (Fin 10)) * (φ : Equiv.Perm (Fin 10))⁻¹ :=
      rfl
    rw [hcoe, Equiv.Perm.support_conj, ← hDdef]
    exact hmapDA
  have hφB : φ ∈ (alternatingGroup.ofSubtype B).range := hφmem
  have hgeq : g = φ⁻¹ * (φ * g * φ⁻¹) * φ := by group
  rw [hgeq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_right (Subgroup.inv_mem _ hφB)) (Subgroup.mem_sup_left hconjA))
    (Subgroup.mem_sup_right hφB)

private theorem concrete_sup_eq_top
    (X₁ X₂ : Subgroup (alternatingGroup (Fin 10)))
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (A : Subgroup (alternatingGroup (Fin 10))) (hA : A ≤ X₁) (hA3 : Nat.card A = 3) :
    X₁ ⊔ X₂ ⊔ Subgroup.normalizer (A : Set (alternatingGroup (Fin 10))) = ⊤ := by
  classical
  obtain ⟨S, hScard, hfix₁, hfix₂⟩ := exists_split_of_commuting_alt5 X₁ X₂ h₁ h₂ hcomm
  have hX₁card : Nat.card ↥X₁ = 60 := by
    obtain ⟨e⟩ := h₁
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hX₂card : Nat.card ↥X₂ = 60 := by
    obtain ⟨e⟩ := h₂
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hX₁_le : X₁ ≤ (alternatingGroup.ofSubtype S).range := by
    intro x hx
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro i hi
    by_contra hnot
    rw [Equiv.Perm.mem_support] at hi
    exact hi (hfix₁ x hx i hnot)
  have hX₁_eq : X₁ = (alternatingGroup.ofSubtype S).range :=
    Subgroup.eq_of_le_of_card_ge hX₁_le (by
      rw [card_ofSubtype_range_of_card_five S hScard, hX₁card])
  have hScompl : Sᶜ.card = 5 := by
    rw [Finset.card_compl, Fintype.card_fin, hScard]
  have hX₂_le : X₂ ≤ (alternatingGroup.ofSubtype Sᶜ).range := by
    intro x hx
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    intro i hi
    by_contra hnot
    simp only [Finset.mem_compl, not_not] at hnot
    rw [Equiv.Perm.mem_support] at hi
    exact hi (hfix₂ x hx i hnot)
  have hX₂_eq : X₂ = (alternatingGroup.ofSubtype Sᶜ).range :=
    Subgroup.eq_of_le_of_card_ge hX₂_le (by
      rw [card_ofSubtype_range_of_card_five Sᶜ hScompl, hX₂card])
  have hA_ne_bot : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA3
    omega
  obtain ⟨c, hcA, hcne⟩ : ∃ c ∈ A, c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA_ne_bot (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  have hc_order : orderOf c = 3 := by
    have hdvd : orderOf c ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hcA
    rw [hA3] at hdvd
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf c) hdvd with h1 | h3
    · exact absurd h1 fun h => hcne (orderOf_eq_one_iff.mp h)
    · exact h3
  have hA_eq_zpowers : A = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
    have hcard : Nat.card A ≤ Nat.card ↥(Subgroup.zpowers c) := by
      rw [hA3, Nat.card_zpowers, hc_order]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  set T : Finset (Fin 10) := (c : Equiv.Perm (Fin 10)).support with hTdef
  have hT_sub_S : T ⊆ S :=
    (alternatingGroup.mem_range_ofSubtype_iff S c).mp (hX₁_eq ▸ hA hcA)
  have hTcard : T.card = 3 := by
    have hc_order_perm : orderOf (c : Equiv.Perm (Fin 10)) = 3 := by
      rw [Subgroup.orderOf_coe c, hc_order]
    have hprime : (orderOf (c : Equiv.Perm (Fin 10))).Prime := by
      rw [hc_order_perm]; exact Nat.prime_three
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hprime
    have hsum : ((c : Equiv.Perm (Fin 10)).cycleType).sum = T.card := by
      rw [Equiv.Perm.sum_cycleType]
    rw [hn, hc_order_perm, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hle : T.card ≤ 5 := by
      rw [← hScard]; exact Finset.card_le_card hT_sub_S
    have hpos : 0 < T.card := by
      rw [Finset.card_pos]
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      exact hcne (Subtype.ext (Equiv.Perm.support_eq_empty_iff.mp hemp))
    omega
  have hN_le : (alternatingGroup.ofSubtype Tᶜ).range ≤
      Subgroup.normalizer (A : Set (alternatingGroup (Fin 10))) := by
    rw [hA_eq_zpowers, Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxsupp : (x : Equiv.Perm (Fin 10)).support ⊆ Tᶜ :=
      (alternatingGroup.mem_range_ofSubtype_iff Tᶜ x).mp hx
    have hdisj : Disjoint (x : Equiv.Perm (Fin 10)).support (c : Equiv.Perm (Fin 10)).support := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      rw [Finset.mem_inter] at hi
      have hi1 : i ∈ Tᶜ := hxsupp hi.1
      have hi2 : i ∈ T := by rw [hTdef]; exact hi.2
      rw [Finset.mem_compl] at hi1
      exact hi1 hi2
    have hcomm_perm : Commute (x : Equiv.Perm (Fin 10)) (c : Equiv.Perm (Fin 10)) :=
      Equiv.Perm.Disjoint.commute (Equiv.Perm.disjoint_iff_disjoint_support.mpr hdisj)
    have hxc : Commute x c := Subtype.ext hcomm_perm
    have hxck : Commute x (c ^ k) := hxc.zpow_right k
    have hgoal : x * c ^ k * x⁻¹ = c ^ k := by
      rw [hxck.eq]; group
    rw [hgoal]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hgen : (alternatingGroup.ofSubtype S).range ⊔ (alternatingGroup.ofSubtype Tᶜ).range = ⊤ := by
    refine sup_ofSubtype_range_eq_top S Tᶜ ?_ ?_ ?_
    · apply Finset.eq_univ_iff_forall.mpr
      intro x
      by_cases hx : x ∈ T
      · exact Finset.mem_union_left _ (hT_sub_S hx)
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hx)
    · have hST : S ∩ Tᶜ = S \ T := (Finset.sdiff_eq_inter_compl S T).symm
      rw [hST, Finset.card_sdiff_of_subset hT_sub_S, hScard, hTcard]
    · rw [Finset.card_compl, Fintype.card_fin, hTcard]
      omega
  have hle : (alternatingGroup.ofSubtype S).range ⊔ (alternatingGroup.ofSubtype Tᶜ).range ≤
      X₁ ⊔ X₂ ⊔ Subgroup.normalizer (A : Set (alternatingGroup (Fin 10))) := by
    apply sup_le
    · rw [← hX₁_eq]; exact le_sup_left.trans le_sup_left
    · exact hN_le.trans le_sup_right
  rw [eq_top_iff, ← hgen]
  exact hle

theorem sup_normalizer_eq_top_of_commuting_alt5 {I : Type} [Group I]
    (hI : Nonempty (I ≃* alternatingGroup (Fin 10))) (X₁ X₂ A : Subgroup I)
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) (hA : A ≤ X₁) (hA3 : Nat.card A = 3) :
    X₁ ⊔ X₂ ⊔ Subgroup.normalizer (A : Set I) = ⊤ := by
  classical
  obtain ⟨e⟩ := hI
  let X₁' : Subgroup (alternatingGroup (Fin 10)) := X₁.map e.toMonoidHom
  let X₂' : Subgroup (alternatingGroup (Fin 10)) := X₂.map e.toMonoidHom
  let A' : Subgroup (alternatingGroup (Fin 10)) := A.map e.toMonoidHom
  have h₁' : Nonempty (↥X₁' ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.equivMapOfInjective X₁ e.toMonoidHom e.injective).symm.trans h₁.some⟩
  have h₂' : Nonempty (↥X₂' ≃* alternatingGroup (Fin 5)) :=
    ⟨(Subgroup.equivMapOfInjective X₂ e.toMonoidHom e.injective).symm.trans h₂.some⟩
  have hcomm' : ∀ x ∈ X₁', ∀ y ∈ X₂', x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.mem_map] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hcomm x₀ hx₀ y₀ hy₀]
  have hA' : A' ≤ X₁' := Subgroup.map_mono hA
  have hA3' : Nat.card ↥A' = 3 := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).toEquiv]
    exact hA3
  have htop : X₁' ⊔ X₂' ⊔ Subgroup.normalizer (A' : Set (alternatingGroup (Fin 10))) = ⊤ :=
    concrete_sup_eq_top X₁' X₂' h₁' h₂' hcomm' A' hA' hA3'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_equiv_normalizer_eq,
    Subgroup.map_top_of_surjective (f := e.toMonoidHom) e.surjective]
  exact htop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
