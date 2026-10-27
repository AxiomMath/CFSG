module

public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def K4Frame : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | InK4 σ}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro σ τ hσ hτ
    rcases hσ with rfl | rfl | rfl | rfl <;> rcases hτ with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro σ hσ
    rcases hσ with rfl | rfl | rfl | rfl <;> decide

theorem mem_K4Frame {σ : Equiv.Perm (Fin 5)} : σ ∈ K4Frame ↔ InK4 σ := Iff.rfl

namespace Frame

variable {G : Type} [Group G] {T K I : Subgroup G}

@[expose] noncomputable def R1 (F : Frame T K I) : Subgroup G :=
  T ⊓ (K4Frame.comap F.ρ).map (Subgroup.normalizer (I : Set G)).subtype

theorem R1_le_T (F : Frame T K I) : F.R1 ≤ T := inf_le_left

theorem mem_R1 (F : Frame T K I) {t : G} (ht : t ∈ T) : t ∈ F.R1 ↔ InK4 (F.ρ ⟨t, F.T_le ht⟩) := by
  constructor
  · rintro ⟨-, y, hy, hyt⟩
    have : y = ⟨t, F.T_le ht⟩ := Subtype.ext hyt
    rw [← this]
    exact hy
  · intro h
    exact ⟨ht, ⟨t, F.T_le ht⟩, h, rfl⟩

theorem card_I (F : Frame T K I) : Nat.card I = 16 := by
  rw [Nat.card_congr F.ψ.toEquiv, card_W5]

theorem conj_eq_iff (F : Frame T K I) (g : ↥(Subgroup.normalizer (I : Set G))) (v : ↥I) :
    (g : G) * v * (g : G)⁻¹ = v ↔ pact (F.ρ g) (F.ψ v) = F.ψ v := by
  have e : F.ψ ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
      pact (F.ρ g) (F.ψ v) := by
    rw [← F.equiv]
    congr 1
  rw [← e]
  constructor
  · intro h
    congr 1
    exact Subtype.ext h
  · intro h
    have := congrArg Subtype.val (F.ψ.injective h)
    simpa using this

theorem ker_rho_restrict (F : Frame T K I) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (I : Set G)) :
    (F.ρ.comp (Subgroup.inclusion hAN)).ker =
      (A ⊓ Subgroup.centralizer (I : Set G)).subgroupOf A := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
  constructor
  · intro h
    exact ⟨b.2, F.mem_centralizer_of_rho _ h⟩
  · intro h
    exact F.rho_eq_one_of_mem _ h.2

theorem centralizer_le_R1 (F : Frame T K I) : T ⊓ Subgroup.centralizer (I : Set G) ≤ F.R1 := by
  intro t ht
  have htT : t ∈ T := (Subgroup.mem_inf.mp ht).1
  refine (F.mem_R1 htT).2 (Or.inl ?_)
  exact F.rho_eq_one_of_mem _ (Subgroup.mem_inf.mp ht).2

theorem le_R1 (F : Frame T K I) (hI : IsElemAbelian 2 I) (hIT : I ≤ T) : I ≤ F.R1 := fun v hv =>
  F.centralizer_le_R1 ⟨hIT hv, Subgroup.mem_centralizer_iff.mpr fun w hw =>
    congrArg Subtype.val (hI.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)⟩

theorem le_centralizer_of_isMaxElemAbelian_le_R1 [Finite G] (F : Frame T K I)
    (hI : IsElemAbelian 2 I) {R : Subgroup G}
    (hIR : I ≤ R) (hRR1 : R ≤ F.R1) {A : Subgroup G} (hA : IsMaxElemAbelian R A) :
    A ≤ Subgroup.centralizer (I : Set G) := by
  have hAR1 : A ≤ F.R1 := hA.1.trans hRR1
  have hAT : A ≤ T := hAR1.trans F.R1_le_T
  have hAN : A ≤ Subgroup.normalizer (I : Set G) := hAT.trans F.T_le
  by_contra hAV
  obtain ⟨a, haA, ha⟩ := IsConcreteLE.not_le_iff_exists.1 hAV
  have hK4 : ∀ b (hb : b ∈ A), InK4 (F.ρ ⟨b, hAN hb⟩) := fun b hb =>
    (F.mem_R1 (hAT hb)).1 (hAR1 hb)
  have hra1 : F.ρ ⟨a, hAN haA⟩ ≠ 1 := fun h => ha (F.mem_centralizer_of_rho _ h)
  have hff := card_mul_le_of_isMaxElemAbelian hI hIR hA
  rw [F.card_I] at hff
  have hKpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) := Nat.card_pos
  set f := F.ρ.comp (Subgroup.inclusion hAN)
  have hfker := F.ker_rho_restrict hAN
  have hfval : ∀ b : ↥A, f b = F.ρ ⟨(b : G), hAN b.2⟩ := fun _ => rfl
  have hmemList : ∀ b (hb : b ∈ A), F.ρ ⟨b, hAN hb⟩ ≠ 1 → F.ρ ⟨b, hAN hb⟩ ∈ [pa, pb, pc] := by
    intro b hb hb1
    rcases hK4 b hb with h | h | h | h
    · exact absurd h hb1
    all_goals simp [h]
  by_cases hcase : ∃ (b : G) (hb : b ∈ A), F.ρ ⟨b, hAN hb⟩ ≠ 1 ∧
      F.ρ ⟨b, hAN hb⟩ ≠ F.ρ ⟨a, hAN haA⟩
  ·
    obtain ⟨b, hbA, hb1, hba⟩ := hcase
    have hA4 := card_le_of_range_subset inf_le_left f hfker {σ | InK4 σ}
      fun c => by rw [hfval]; exact hK4 c c.2
    have hX4 : Nat.card ({σ | InK4 σ} : Set (Equiv.Perm (Fin 5))) = 4 := by
      rw [← card_InK4, ← Nat.card_eq_fintype_card]
      rfl
    rw [hX4] at hA4
    have hCV : Nat.card ↥(I ⊓ Subgroup.centralizer (A : Set G)) ≤ 2 := by
      rw [← card_one_W4, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective (fun v => ⟨F.ψ ⟨v, v.2.1⟩, ?_⟩) ?_
      · have hfa : pact (F.ρ ⟨a, hAN haA⟩) (F.ψ ⟨v, v.2.1⟩) = F.ψ ⟨v, v.2.1⟩ := by
          refine (F.conj_eq_iff ⟨a, hAN haA⟩ ⟨v, v.2.1⟩).1 ?_
          have := Subgroup.mem_centralizer_iff.mp v.2.2 a haA
          show a * (v : G) * a⁻¹ = v
          rw [this]; group
        have hfb : pact (F.ρ ⟨b, hAN hbA⟩) (F.ψ ⟨v, v.2.1⟩) = F.ψ ⟨v, v.2.1⟩ := by
          refine (F.conj_eq_iff ⟨b, hAN hbA⟩ ⟨v, v.2.1⟩).1 ?_
          have := Subgroup.mem_centralizer_iff.mp v.2.2 b hbA
          show b * (v : G) * b⁻¹ = v
          rw [this]; group
        exact fix_K4_pair _ (hmemList a haA hra1) _ (hmemList b hbA hb1) (Ne.symm hba) _ hfa hfb
      · intro v w hvw
        have h1 := F.ψ.injective (congrArg Subtype.val hvw)
        exact Subtype.ext (congrArg (fun x : ↥I => (x : G)) h1)
    have : 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) ≤
        8 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) :=
      calc 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G))
          ≤ Nat.card A * Nat.card ↥(I ⊓ Subgroup.centralizer (A : Set G)) := hff
        _ ≤ (4 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G))) * 2 :=
          Nat.mul_le_mul hA4 hCV
        _ = 8 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) := by ring
    omega
  ·
    push Not at hcase
    have hA2 := card_le_of_range_subset inf_le_left f hfker
      {σ | σ = 1 ∨ σ = F.ρ ⟨a, hAN haA⟩} fun c => by
        rw [hfval]
        by_cases h1 : F.ρ ⟨(c : G), hAN c.2⟩ = 1
        · exact Or.inl h1
        · exact Or.inr (hcase c c.2 h1)
    have hX2 : Nat.card ({σ | σ = 1 ∨ σ = F.ρ ⟨a, hAN haA⟩} : Set (Equiv.Perm (Fin 5))) ≤ 2 := by
      have : ({σ | σ = 1 ∨ σ = F.ρ ⟨a, hAN haA⟩} : Set (Equiv.Perm (Fin 5))) =
          {1, F.ρ ⟨a, hAN haA⟩} := by
        ext σ; simp
      rw [this, Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have hCV : Nat.card ↥(I ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 := by
      rw [← card_fix_K4 _ (hK4 a haA) hra1, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective (fun v => ⟨F.ψ ⟨v, v.2.1⟩, ?_⟩) ?_
      · refine (F.conj_eq_iff ⟨a, hAN haA⟩ ⟨v, v.2.1⟩).1 ?_
        have := Subgroup.mem_centralizer_iff.mp v.2.2 a haA
        show a * (v : G) * a⁻¹ = v
        rw [this]; group
      · intro v w hvw
        have h1 := F.ψ.injective (congrArg Subtype.val hvw)
        exact Subtype.ext (congrArg (fun x : ↥I => (x : G)) h1)
    have : 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) ≤
        8 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) :=
      calc 16 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G))
          ≤ Nat.card A * Nat.card ↥(I ⊓ Subgroup.centralizer (A : Set G)) := hff
        _ ≤ (2 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G))) * 4 :=
          Nat.mul_le_mul (hA2.trans (Nat.mul_le_mul_right _ hX2)) hCV
        _ = 8 * Nat.card ↥(A ⊓ Subgroup.centralizer (I : Set G)) := by ring
    omega

theorem le_centralizer_of_isMaxElemAbelian_R1 [Finite G] (F : Frame T K I)
    (hI : IsElemAbelian 2 I) (hIT : I ≤ T)
    {A : Subgroup G} (hA : IsMaxElemAbelian F.R1 A) : A ≤ Subgroup.centralizer (I : Set G) :=
  F.le_centralizer_of_isMaxElemAbelian_le_R1 hI (F.le_R1 hI hIT) le_rfl hA

theorem lemma_13_2_4_one [Finite G] (F : Frame T K I) (hI : IsElemAbelian 2 I) (hIT : I ≤ T) :
    thompsonJ F.R1 ≤ T ⊓ Subgroup.centralizer (I : Set G) ∧
      thompsonJ F.R1 = thompsonJ (T ⊓ Subgroup.centralizer (I : Set G)) ∧
      baum F.R1 = baum (T ⊓ Subgroup.centralizer (I : Set G)) := by
  have hJ : thompsonJ F.R1 ≤ F.R1 ⊓ Subgroup.centralizer (I : Set G) :=
    iSup₂_le fun A hA => le_inf hA.1 (F.le_centralizer_of_isMaxElemAbelian_R1 hI hIT hA)
  have hRQ : F.R1 ⊓ Subgroup.centralizer (I : Set G) = T ⊓ Subgroup.centralizer (I : Set G) :=
    le_antisymm (inf_le_inf_right _ F.R1_le_T) (le_inf F.centralizer_le_R1 inf_le_right)
  rw [hRQ] at hJ
  refine ⟨hJ, thompsonJ_eq_of_le hJ F.centralizer_le_R1, ?_⟩
  have h := baum_eq_baum_centralizer hI (F.le_R1 hI hIT) (by rw [hRQ]; exact hJ)
  rwa [hRQ] at h

end Frame

end CFSG.Quasithin.H13.A5
