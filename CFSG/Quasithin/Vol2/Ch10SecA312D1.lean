module

public import CFSG.Quasithin.Vol2.Ch10SecA312C2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312D

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch10.A312C
open scoped commutatorElement

theorem exists_mul_ne {S : Type*} [Group S] [Nontrivial S]
    (h : ⁅(⊤ : Subgroup S), ⊤⁆ = (⊤ : Subgroup S)) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hne
  have h1 : ⁅(⊤ : Subgroup S), ⊤⁆ = (⊥ : Subgroup S) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    by_contra hxy
    exact hne ⟨y, x, hxy⟩
  exact (top_ne_bot : (⊤ : Subgroup S) ≠ ⊥) (h.symm.trans h1)

theorem center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ⁅(⊤ : Subgroup S), ⊤⁆ = (⊤ : Subgroup S)) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h1 | h1
  · exact h1
  · obtain ⟨a, b, hab⟩ := exists_mul_ne h
    have hb : b ∈ Subgroup.center S := by rw [h1]; exact Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hz', map_one]

variable {X : Type} [Group X] {B₁ B₂ : Subgroup X}

theorem le_normalizer_of_commutator_le (hc : ⁅B₁, B₂⁆ ≤ B₁) :
    B₂ ≤ Subgroup.normalizer (B₁ : Set X) := by
  have hcB : ∀ y ∈ B₂, ∀ b ∈ B₁, y * b * y⁻¹ ∈ B₁ := fun y hy b hb => by
    have h1 : y * b * y⁻¹ * b⁻¹ ∈ B₁ :=
      hc (Subgroup.commutator_comm B₂ B₁ ▸ Subgroup.commutator_mem_commutator hy hb)
    simpa using B₁.mul_mem h1 hb
  exact fun y hy => Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => hcB y hy b hb, fun hb => by
    simpa [mul_assoc] using hcB y⁻¹ (B₂.inv_mem hy) _ hb⟩

theorem inf_le_pCoreOf (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₂) (hZ : Subgroup.center (ModO2 B₂) = ⊥) :
    B₁ ⊓ B₂ ≤ pCoreOf 2 B₂ := by
  rintro d ⟨hd1, hd2⟩
  have hcen : (QuotientGroup.mk (⟨d, hd2⟩ : ↥B₂) : ModO2 B₂) ∈ Subgroup.center (ModO2 B₂) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥B₂) z
    have h1 : ⁅d, (x : X)⁆ ∈ pCoreOf 2 B₂ := hc (Subgroup.commutator_mem_commutator hd1 x.2)
    rw [pCoreOf] at h1
    obtain ⟨c, hc1, hc2⟩ := h1
    have hcoe : ((⁅(⟨d, hd2⟩ : ↥B₂), x⁆ : ↥B₂) : X) = ⁅d, (x : X)⁆ := by
      simp [commutatorElement_def]
    have h3 : ⁅(⟨d, hd2⟩ : ↥B₂), x⁆ ∈ CFSG.pCore 2 ↥B₂ := by
      rwa [show ⁅(⟨d, hd2⟩ : ↥B₂), x⁆ = c from Subtype.ext (hcoe.trans hc2.symm)]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥B₂) x * QuotientGroup.mk' _ (⟨d, hd2⟩ : ↥B₂) =
      QuotientGroup.mk' _ (⟨d, hd2⟩ : ↥B₂) * QuotientGroup.mk' _ x
    rw [eq_comm, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  rw [pCoreOf]
  exact ⟨⟨d, hd2⟩, hcen, rfl⟩

theorem card_mul_card_modO2_dvd [Finite X] (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂)
    (e : ModO2 B₁ ≃* ModO2 B₂) (hZ : Subgroup.center (ModO2 B₁) = ⊥) :
    Nat.card B₁ * Nat.card (ModO2 B₁) ∣ Nat.card X := by
  have hN : B₂ ≤ Subgroup.normalizer (B₁ : Set X) :=
    le_normalizer_of_commutator_le (hc.trans (inf_le_left.trans (Subgroup.map_subtype_le _)))
  have hD : B₁ ⊓ B₂ ≤ pCoreOf 2 B₂ :=
    inf_le_pCoreOf (hc.trans inf_le_right) (center_eq_bot_of_mulEquiv e hZ)
  have h4 : Nat.card ↥(pCoreOf 2 B₂) = Nat.card (CFSG.pCore 2 ↥B₂) := by
    rw [pCoreOf, Subgroup.card_map_of_injective B₂.subtype_injective]
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hD
  have h5 : Nat.card ↥(B₂ ⊔ B₁) = Nat.card B₁ * Nat.card (ModO2 B₁) * m := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(B₁ ⊓ B₂)))
    rw [A312C.card_sup_mul_card_inf hN,
      (CFSG.pCore 2 ↥B₂).card_eq_card_quotient_mul_card_subgroup, ← Nat.card_congr e.toEquiv,
      ← h4, hm]
    ring
  exact (Dvd.intro m h5.symm).trans (Subgroup.card_subgroup_dvd_card _)

theorem card_mul_dvd_of_hom [Finite X] (hB₁ : ⁅B₁, B₁⁆ = B₁)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂) (e : ModO2 B₁ ≃* ModO2 B₂) {S : Type}
    [Group S] [IsSimpleGroup S] (g : ↥B₁ →* S) (hg : Function.Surjective g)
    (hk : IsPGroup 2 g.ker) : Nat.card B₁ * Nat.card S ∣ Nat.card X := by
  have : Finite S := Finite.of_surjective g hg
  have hperf : ⁅(⊤ : Subgroup S), ⊤⁆ = (⊤ : Subgroup S) := by
    have h1 : ⁅(⊤ : Subgroup ↥B₁), ⊤⁆ = (⊤ : Subgroup ↥B₁) :=
      Subgroup.map_injective B₁.subtype_injective (by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hB₁])
    rw [← Subgroup.map_top_of_surjective g hg, ← Subgroup.map_commutator, h1]
  let f := Vol2Native.A312L.modO2EquivOfHom (exists_mul_ne hperf) g hg hk
  have : IsSimpleGroup (ModO2 B₁) := f.isSimpleGroup
  rw [← Nat.card_congr f.toEquiv]
  exact card_mul_card_modO2_dvd hc e (center_eq_bot (perfect_modO2 hB₁))

end CFSG.Quasithin.Vol2.Ch10.A312D
