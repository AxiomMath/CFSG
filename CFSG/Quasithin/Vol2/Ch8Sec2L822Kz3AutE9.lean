module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1b

public section

namespace CFSG.Quasithin.H13

section AutE9

variable {A : Type} [Group A]

theorem kzE9_ne_inv {a : A} (h3 : a ^ 3 = 1) (ha : a ≠ 1) : a ≠ a⁻¹ := by
  intro h
  apply ha
  have hsq : a * a = 1 := by
    have h' : a * a⁻¹ = 1 := mul_inv_cancel a
    rwa [← h] at h'
  have h3a : a ^ 3 = a := by rw [pow_three, hsq, mul_one]
  exact h3a.symm.trans h3

def kzE9Lines (A : Type) [Group A] [Fintype A] [DecidableEq A] : Finset (Finset A) :=
  (Finset.univ.erase (1 : A)).image (fun a => ({a, a⁻¹} : Finset A))

theorem kzE9_mem_lines_iff [Fintype A] [DecidableEq A] {S : Finset A} :
    S ∈ kzE9Lines A ↔ ∃ a : A, a ≠ 1 ∧ ({a, a⁻¹} : Finset A) = S := by
  unfold kzE9Lines
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, (Finset.mem_erase.mp ha).1, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩, h⟩

theorem kzE9_pair_mem_lines [Fintype A] [DecidableEq A] {a : A} (ha : a ≠ 1) :
    ({a, a⁻¹} : Finset A) ∈ kzE9Lines A :=
  kzE9_mem_lines_iff.mpr ⟨a, ha, rfl⟩

theorem kzE9_image_mem_lines [Fintype A] [DecidableEq A] (σ : MulAut A) {S : Finset A}
    (hS : S ∈ kzE9Lines A) : S.image (⇑σ) ∈ kzE9Lines A := by
  obtain ⟨a, ha, rfl⟩ := kzE9_mem_lines_iff.mp hS
  refine kzE9_mem_lines_iff.mpr ⟨σ a, fun h => ha ?_, ?_⟩
  · exact (map_eq_one_iff σ σ.injective).mp h
  · rw [Finset.image_insert, Finset.image_singleton, map_inv]

theorem kzE9_card_lines_le [Fintype A] [DecidableEq A] (hcard : Fintype.card A = 9)
    (hexp : ∀ a : A, a ^ 3 = 1) : (kzE9Lines A).card ≤ 4 := by
  have hF : (Finset.univ.erase (1 : A)).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  have hn : ∀ S ∈ (Finset.univ.erase (1 : A)).image (fun a : A => ({a, a⁻¹} : Finset A)),
      2 ≤ ((Finset.univ.erase (1 : A)).filter (fun a : A => ({a, a⁻¹} : Finset A) = S)).card := by
    intro S hS
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hS
    have hb1 : b ≠ 1 := (Finset.mem_erase.mp hb).1
    have hbne : b ≠ b⁻¹ := kzE9_ne_inv (hexp b) hb1
    have hbinv : b⁻¹ ∈ Finset.univ.erase (1 : A) :=
      Finset.mem_erase.mpr ⟨inv_ne_one.mpr hb1, Finset.mem_univ _⟩
    have hsub : ({b, b⁻¹} : Finset A) ⊆
        (Finset.univ.erase (1 : A)).filter (fun a : A => ({a, a⁻¹} : Finset A) = {b, b⁻¹}) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]
        exact Finset.mem_filter.mpr ⟨hb, rfl⟩
      · rw [Finset.mem_singleton.mp h]
        exact Finset.mem_filter.mpr ⟨hbinv, by rw [inv_inv, Finset.pair_comm]⟩
    calc 2 = ({b, b⁻¹} : Finset A).card := (Finset.card_pair hbne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hmul : 2 * (kzE9Lines A).card ≤ (Finset.univ.erase (1 : A)).card :=
    Finset.mul_card_image_le_card _ 2 hn
  omega

instance kzE9LinesAct [Fintype A] [DecidableEq A] :
    MulAction (MulAut A) {S : Finset A // S ∈ kzE9Lines A} where
  smul σ S := ⟨S.1.image (⇑σ), kzE9_image_mem_lines σ S.2⟩
  one_smul S := by
    apply Subtype.ext
    show S.1.image (⇑(1 : MulAut A)) = S.1
    rw [show (⇑(1 : MulAut A)) = id from rfl, Finset.image_id]
  mul_smul σ τ S := by
    apply Subtype.ext
    show S.1.image (⇑(σ * τ)) = (S.1.image (⇑τ)).image (⇑σ)
    rw [Finset.image_image]
    congr 1

theorem kzE9_lines_perm_isSolvable [Fintype A] [DecidableEq A] (hcard : Fintype.card A = 9)
    (hexp : ∀ a : A, a ^ 3 = 1) :
    Group.IsSolvable (Equiv.Perm {S : Finset A // S ∈ kzE9Lines A}) := by
  apply Equiv.Perm.isSolvable
  rw [Nat.card_eq_finsetCard]
  exact kzE9_card_lines_le hcard hexp

theorem kzE9_commute_of_fix {σ τ : MulAut A} (hσ : ∀ x : A, σ x = x ∨ σ x = x⁻¹)
    (hτ : ∀ x : A, τ x = x ∨ τ x = x⁻¹) : σ * τ = τ * σ := by
  refine MulEquiv.ext fun a => ?_
  show σ (τ a) = τ (σ a)
  rcases hτ a with h2 | h2 <;> rcases hσ a with h1 | h1 <;>
    simp only [h1, h2, map_inv, inv_inv]

end AutE9

theorem kzAutE9Perfect_kz3_holds : KzAutE9Perfect_kz3 := by
  classical
  intro A _ _ hcard hexp R hR
  haveI : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 9 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨π, hπ⟩ : ∃ π : MulAut A →* Equiv.Perm {S : Finset A // S ∈ kzE9Lines A},
      ∀ (σ : MulAut A) (S : {S : Finset A // S ∈ kzE9Lines A}), π σ S = σ • S :=
    ⟨MulAction.toPermHom _ _, fun _ _ => rfl⟩
  haveI := kzE9_lines_perm_isSolvable hcardF hexp
  have hQ : ⁅R.map π, R.map π⁆ = R.map π := by
    rw [← Subgroup.map_commutator, hR]
  have hsub : Subsingleton ↥(R.map π) := by
    haveI : Group.IsPerfect ↥(R.map π) := Subgroup.isPerfect_iff.mpr hQ
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥(R.map π) inferInstance
  have hbot : R.map π = ⊥ := Subgroup.eq_bot_of_subsingleton (R.map π)
  have hπ1 : ∀ r ∈ R, π r = 1 := by
    intro r hr
    have h := Subgroup.mem_map_of_mem π hr
    rw [hbot, Subgroup.mem_bot] at h
    exact h
  have hfix : ∀ r ∈ R, ∀ a : A, r a = a ∨ r a = a⁻¹ := by
    intro r hr a
    by_cases ha : a = 1
    · left
      rw [ha, map_one]
    · have hx : π r ⟨{a, a⁻¹}, kzE9_pair_mem_lines ha⟩ = ⟨{a, a⁻¹}, kzE9_pair_mem_lines ha⟩ := by
        rw [hπ1 r hr]
        rfl
      have hval : ({a, a⁻¹} : Finset A).image (⇑r) = {a, a⁻¹} :=
        congrArg Subtype.val ((hπ r _).symm.trans hx)
      have hmem : r a ∈ ({a, a⁻¹} : Finset A).image (⇑r) :=
        Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
      rw [hval] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
  have hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := fun r hr s hs =>
    kzE9_commute_of_fix (hfix r hr) (hfix s hs)
  have hle : ⁅R, R⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm g hg h hh
  rw [hR] at hle
  exact le_bot_iff.mp hle

end CFSG.Quasithin.H13
