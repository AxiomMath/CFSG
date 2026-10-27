module

public import CFSG.Quasithin.EmptyFaithful.S153E56E5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E56e

open CFSG.Quasithin.S153E

section JFacts2

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem bar_comm' (cx : Ctx15350 T Mc M V₁ V₂ t) {x x' : G}
    (hx : x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hx' : x' ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (hc : x * x' * x⁻¹ * x'⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) :
    S153E55.bar cx hc = S153E55.bar cx hx * S153E55.bar cx hx' * (S153E55.bar cx hx)⁻¹ *
      (S153E55.bar cx hx')⁻¹ := by
  unfold S153E55.bar
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rfl

theorem R_two_pow (J : Subgroup G) {x : G} (hx : x ∈ pCoreOf 2 J) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 J ⟨x, hx⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem comm_j_R_mem_C (H : Hyps56 cx N₁ N₂ g s y) {j : G} (hj : j ∈ Jgp153 T M V₁ Mc y)
    (hjy : y⁻¹ * j ∈ Subgroup.centralizer (VZ T M : Set G)) {ρ : G}
    (hρ : ρ ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y)) :
    j * ρ * j⁻¹ * ρ⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨e⟩ := H.c.h53one.iso₁
  have hcomm : ∀ a ∈ N₁i cx N₁, ∀ b ∈ N₂i cx N₂, a * b = b * a := H.c.h53one.comm
  have hinf : N₁i cx N₁ ⊓ N₂i cx N₂ = ⊥ := H.c.h53one.inf
  have hyYU := y_mem_YU H
  have hJYU := J_le_YU (T := T) (M := M) (V₁ := V₁) (Mc := Mc) (y_mem_Y H)
  have hjYU := hJYU hj
  have hρJ : ρ ∈ Jgp153 T M V₁ Mc y := pCoreOf_le 2 _ hρ
  have hρYU := hJYU hρJ
  have hbj : S153E55.bar cx hjYU = ybar H := by
    have hyiYU : y⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.inv_mem _ hyYU
    have hyijYU : y⁻¹ * j ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mul_mem _ hyiYU hjYU
    have h1 : S153E55.bar cx hyijYU = 1 :=
      (convI_eq_one_iff hV ⟨y⁻¹ * j, S153E55.YU_le_normalizer_V cx hyijYU⟩).2 hjy
    rw [bar_mul' cx hyiYU hjYU, bar_inv' cx hyYU hyiYU] at h1
    exact (inv_mul_eq_one.1 h1).symm
  have hcommR : j * ρ * j⁻¹ * ρ⁻¹ ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y) := by
    have h1 : j * ρ * j⁻¹ ∈ pCoreOf 2 (Jgp153 T M V₁ Mc y) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hj) ρ).mp hρ
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hρ)
  have hcommJ : j * ρ * j⁻¹ * ρ⁻¹ ∈ Jgp153 T M V₁ Mc y := pCoreOf_le 2 _ hcommR
  have hcommYU := hJYU hcommJ
  obtain ⟨k, hk⟩ := R_two_pow _ hρ
  obtain ⟨k', hk'⟩ := R_two_pow _ hcommR
  have hρbar := bar_mem_sup cx H hρYU
  have hbc := bar_comm' cx hjYU hρYU hcommYU
  rw [hbj] at hbc
  have hk'bar := bar_pow_eq_one cx hcommYU hk'
  rw [hbc] at hk'bar
  have key := core_comm hcomm hinf e (c := ybar H) (ybar_mem_N₁ H) (ybar_pow_three H)
    (ybar_ne_one H) hρbar (bar_pow_eq_one cx hρYU hk) hk'bar
  rw [← hbc] at key
  exact (convI_eq_one_iff hV ⟨_, S153E55.YU_le_normalizer_V cx hcommYU⟩).1 key

theorem V_le_J (H : Hyps56 cx N₁ N₂ g s y) : VZ T M ≤ Jgp153 T M V₁ Mc y := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨P, hP, hVQ, hVU, hUV⟩ := H.c.h53two.perp
  have hidx : (VZ T M ⊓ UH153 T M V₁ Mc).relIndex (VZ T M) = 2 := by
    have : VZ T M ⊓ UH153 T M V₁ Mc = VZ T M ⊓ pCoreOf 2 Mc := hVU.trans hVQ.symm
    rw [this]
    exact H.c.h53two.card_Vstar
  have hV16 : Nat.card ↥(VZ T M) = 16 := cx.c.hyp.card_VZ
  have hAcard : Nat.card ↥(VZ T M ⊓ UH153 T M V₁ Mc) = 8 := by
    have e := Subgroup.relIndex_mul_card (VZ T M ⊓ UH153 T M V₁ Mc) (VZ T M)
    rw [inf_eq_left.2 (inf_le_left : VZ T M ⊓ UH153 T M V₁ Mc ≤ VZ T M), hidx, hV16] at e
    omega
  have hyN := y_mem_N H
  have hB : VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y =
      conjSubgroup (VZ T M ⊓ UH153 T M V₁ Mc) y := by
    rw [conjSubgroup_inf, conjSubgroup_eq_iff_mem_normalizer.2 hyN]
  have hBcard : Nat.card ↥(VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y) = 8 := by
    rw [hB, card_conjSubgroup, hAcard]
  have hne : VZ T M ⊓ UH153 T M V₁ Mc ≠ VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y := by
    intro hAB
    have hst : ∀ x : G, x ∈ VZ T M ⊓ UH153 T M V₁ Mc ↔ y * x * y⁻¹ ∈ VZ T M ⊓ UH153 T M V₁ Mc := by
      intro x
      have h1 := hAB.trans hB
      rw [← mem_conjSubgroup_iff, ← h1]
    have hinj : Function.Injective (commHom (ybar H)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_commHom, ybar_fixV H]
    have hsurj := Finite.injective_iff_surjective.1 hinj
    have hVA : VZ T M ≤ VZ T M ⊓ UH153 T M V₁ Mc := by
      intro v hv
      obtain ⟨w', hw'⟩ := hsurj (IntMod.mk hV ⟨v, hv⟩)
      have hv' : v = y * w'.val * y⁻¹ * w'.val⁻¹ := by
        have := congrArg IntMod.val hw'
        rw [commHom_apply, IntMod.val_mul, ybar_apply, IntMod.val_inv] at this
        exact this.symm
      have hyxV : y * w'.val * y⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hyN w'.val).mp w'.val_mem
      rw [hv']
      by_cases hxA : w'.val ∈ VZ T M ⊓ UH153 T M V₁ Mc
      · exact (VZ T M ⊓ UH153 T M V₁ Mc).mul_mem ((hst _).1 hxA)
          ((VZ T M ⊓ UH153 T M V₁ Mc).inv_mem hxA)
      · rcases coset_of_relIndex_two hidx hyxV w'.val_mem hxA with h | h
        · exact absurd ((hst _).2 h) hxA
        · exact h
    have := Subgroup.card_le_of_le hVA
    rw [hAcard, hV16] at this
    omega
  have hBA : ¬ VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y ≤ VZ T M ⊓ UH153 T M V₁ Mc := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hAcard, hBcard])).symm
  have hsupV : (VZ T M ⊓ UH153 T M V₁ Mc) ⊔ (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y) =
      VZ T M := by
    have hle : (VZ T M ⊓ UH153 T M V₁ Mc) ⊔ (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y) ≤ VZ T M :=
      sup_le inf_le_left inf_le_left
    have hd1 : 8 ∣ Nat.card ↥((VZ T M ⊓ UH153 T M V₁ Mc) ⊔
        (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y)) := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥((VZ T M ⊓ UH153 T M V₁ Mc) ⊔
        (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y)) ≤ 16 := by
      rw [← hV16]
      exact Subgroup.card_le_of_le hle
    have hne8 : Nat.card ↥((VZ T M ⊓ UH153 T M V₁ Mc) ⊔
        (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y)) ≠ 8 := by
      intro h8
      apply hBA
      have heq := Subgroup.eq_of_le_of_card_ge
        (le_sup_left : VZ T M ⊓ UH153 T M V₁ Mc ≤ _) (by rw [h8, hAcard])
      exact le_sup_right.trans heq.symm.le
    have hpos : 0 < Nat.card ↥((VZ T M ⊓ UH153 T M V₁ Mc) ⊔
        (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y)) := Nat.card_pos
    obtain ⟨m, hm⟩ := hd1
    have h16 : Nat.card ↥((VZ T M ⊓ UH153 T M V₁ Mc) ⊔
        (VZ T M ⊓ conjSubgroup (UH153 T M V₁ Mc) y)) = 16 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h16, hV16]))
  rw [← hsupV]
  exact sup_le (inf_le_right.trans (U_le_J T M V₁ Mc y)) (inf_le_right.trans (U'_le_J T M V₁ Mc y))

theorem V_comm_E (H : Hyps56 cx N₁ N₂ g s y) :
    ⁅Egp153 T M V₁ Mc y, VZ T M⁆ ≤
      quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y :=
  (Subgroup.commutator_mono le_rfl (V_le_J H)).trans H.iJ.E_comm

end JFacts2

end S153E56e

end CFSG.Quasithin
