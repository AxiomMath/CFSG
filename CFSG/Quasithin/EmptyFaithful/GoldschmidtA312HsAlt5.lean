module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HeGen

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.A312Ru

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem modO2_alt5_gen {T B Y Y₃ : Subgroup Γ} {e k : ℕ} (hB : B ∈ lFamily T) (hY : B ⊔ T = Y)
    (hek : e = k + 3) (hle : Y₃ ≤ Y) (hcard : Nat.card ↥Y = 2 ^ e * 3 * 5)
    (hcard₃ : Nat.card Y₃ = 2 ^ e * 3) (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ k)
    (hq : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 2) :
    IsAlt 5 (ModO2 B) ∧ Nonempty (↥(CFSG.pCore 2 ↥B) ≃* ↥(CFSG.pCore 2 ↥Y)) := by
  classical
  subst hY
  have hns := not_isSolvable_join hB
  have hY₃ : Nat.card (Y₃.subgroupOf (B ⊔ T)) = 2 ^ e * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hcard₃
  obtain ⟨ρ, hker, -⟩ := exists_hom_perm (Y := ↥(B ⊔ T)) hns (Y' := Y₃.subgroupOf (B ⊔ T))
    (e := e) (p := 5) (by norm_num) (by norm_num) hcard hY₃
  have hrange : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hker, hcard, hP] at h1
    have h2 : (2 : ℕ) ^ e = 2 ^ k * 8 := by rw [hek, pow_add]; norm_num
    rw [h2] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have h3 : Nat.card ρ.range * 2 ^ k = 120 * 2 ^ k := by rw [← h1]; ring
    have h4 : Nat.card ρ.range = 120 := Nat.eq_of_mul_eq_mul_right hpos h3
    rw [h4, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hρs : Function.Surjective ρ := MonoidHom.range_eq_top.mp hrange
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hAnab : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
    nonabelian_of_simple (by rw [hcardA]; norm_num)
  have hidx : Nat.card (Equiv.Perm (Fin 5) ⧸ alternatingGroup (Fin 5)) = 2 :=
    alternatingGroup.index_eq_two (α := Fin 5)
  have hHA : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ alternatingGroup (Fin 5)) :=
    IsPGroup.of_card (n := 1) (by rw [hidx]; norm_num)
  obtain ⟨⟨e'⟩, hiso⟩ := modO2_of_hom_iso hB ρ hρs hker (alternatingGroup (Fin 5)) hAnab hHA
    (by rw [hidx]; exact hq)
  exact ⟨⟨e'⟩, hiso⟩

end CFSG.Quasithin.A312Hs
