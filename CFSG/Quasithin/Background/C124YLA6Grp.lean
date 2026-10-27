module

public import CFSG.Quasithin.Background.C124YLA6Perm
public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Quasithin.Background.DicksonPerfectSL2

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv
open scoped MatrixGroups

abbrev Gam : Type := ↥(alternatingGroup (Fin 6))

theorem eq_top_of_index_six {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    (hΓ : 6 < Nat.card Γ) {H M : Subgroup Γ} (hH : H.index = 6) (hHM : H ≤ M) (hne : H ≠ M) :
    M = ⊤ := by
  have hd : M.index ∣ 6 := hH ▸ Subgroup.index_dvd_of_le hHM
  have hpos : 0 < M.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hne6 : M.index ≠ 6 := by
    intro h6
    apply hne
    have h1 := Subgroup.relIndex_mul_index hHM
    rw [hH, h6] at h1
    have : H.relIndex M = 1 := by omega
    exact le_antisymm hHM (Subgroup.relIndex_eq_one.1 this)
  by_contra hMtop
  have hge : 2 ≤ M.index := by
    rcases Nat.lt_or_ge M.index 2 with h | h
    · exact absurd (Subgroup.index_eq_one.1 (by omega)) hMtop
    · exact h
  have h6 : M.index ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  have hle3 : M.index ≤ 3 := by
    by_contra hlt
    interval_cases h : M.index <;> omega
  have hcore := Subgroup.index_normalCore_le_factorial_index (H := M)
  have hfac : Nat.factorial M.index ≤ 6 := by
    interval_cases h : M.index <;> simp [Nat.factorial]
  rcases (inferInstance : (M.normalCore).Normal).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot] at hcore
    omega
  · apply hMtop
    exact eq_top_iff.2 (h ▸ M.normalCore_le)

theorem card_Gam : Nat.card Gam = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  have h1 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
    rfl
  show Nat.card ↥(alternatingGroup (Fin 6)) = 360
  omega

instance : IsSimpleGroup Gam := alternatingGroup.isSimpleGroup (by simp)

abbrev Ygam : Subgroup Gam := Yg.subgroupOf (alternatingGroup (Fin 6))

abbrev Kgam : Subgroup Gam := Kg.subgroupOf (alternatingGroup (Fin 6))

theorem card_subgroupOf_A6 {H : Subgroup P6} (h : H ≤ alternatingGroup (Fin 6)) :
    Nat.card (H.subgroupOf (alternatingGroup (Fin 6))) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem index_Ygam : Ygam.index = 6 := by
  have h := Subgroup.index_mul_card Ygam
  rw [card_Gam, card_subgroupOf_A6 Yg_le_A6, card_Yg] at h
  omega

theorem mem_normalizer_of_mem_Pg {p : P6} (hp : p ∈ Pg) {x : P6} : x ∈ Kg ↔ p * x * p⁻¹ ∈ Kg := by
  refine ⟨Pg_norm_Kg p hp x, fun h => ?_⟩
  have := Pg_norm_Kg p⁻¹ (Pg.inv_mem hp) _ h
  simpa [mul_assoc] using this

theorem nuGam_mem_normalizer : (⟨swap 4 5 * swap 2 3, by
    have := Pg_le_A6 nu_mem_Pg
    exact this⟩ : Gam) ∈ Subgroup.normalizer (Kgam : Set Gam) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact mem_normalizer_of_mem_Pg nu_mem_Pg

theorem gen_Gam : Ygam ⊔ Subgroup.normalizer (Kgam : Set Gam) = ⊤ := by
  refine eq_top_of_index_six (by rw [card_Gam]; norm_num) index_Ygam le_sup_left ?_
  intro h
  have hmem : (⟨swap 4 5 * swap 2 3, Pg_le_A6 nu_mem_Pg⟩ : Gam) ∈
      Ygam ⊔ Subgroup.normalizer (Kgam : Set Gam) := Subgroup.mem_sup_right nuGam_mem_normalizer
  rw [← h] at hmem
  exact nu_not_mem_Yg (Subgroup.mem_subgroupOf.1 hmem)

theorem Yg_equiv_alt_five : Nonempty (↥Yg ≃* alternatingGroup (Fin 5)) := by
  have hpre : MulAction.IsPretransitive ↥Yg (Fin 6) := by
    rw [MulAction.isPretransitive_iff_base (0 : Fin 6)]
    intro y
    obtain ⟨g, hg, e⟩ := Yg_trans y
    exact ⟨⟨g, hg⟩, e⟩
  exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty hpre
    (by simp) (by rw [card_Yg])

theorem sl2_equiv_alt_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nonempty (SL(2, F) ≃* alternatingGroup (Fin 5)) := by
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hF4
  have hsimple : IsSimpleGroup SL(2, F) := CFSG.Quasithin.C126.Nat.isSimpleGroup_sl2 (by omega)
  have hcard : Nat.card SL(2, F) = 60 := CFSG.Quasithin.C124.L2.card_sl2_four hF
  exact CFSG.Quasithin.Dickson.nonempty_mulEquiv_alt_five_of_simple hcard

theorem Yg_equiv_sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥Yg ≃* SL(2, F)) := by
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e1⟩ := Yg_equiv_alt_five
  obtain ⟨e2⟩ := sl2_equiv_alt_five (F := GaloisField 2 2) hF
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hF, ⟨e1.trans e2.symm⟩⟩

end CFSG.Quasithin.C124.YL.A6
