module

public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

@[expose] def centralizerModSolvRad {G : Type*} [Group G] (L : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅h, l⁆ ∈ solvRad L}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun l hl => ?_⟩
    have h1 : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (conj_mem_solvRad ha (hb' l hl)) (ha' l hl)
  one_mem' := ⟨Subgroup.one_mem _, fun l _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun l hl => ?_⟩
    have h1 : ⁅a⁻¹, l⁆ = a⁻¹ * (⁅a, l⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact conj_mem_solvRad (Subgroup.inv_mem _ ha) (Subgroup.inv_mem _ (ha' l hl))

theorem mem_centralizerModSolvRad {G : Type*} [Group G] {L : Subgroup G} {h : G} :
    h ∈ centralizerModSolvRad L ↔
      h ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅h, l⁆ ∈ solvRad L := Iff.rfl

@[expose] def HasS3Section {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  ∃ (K : Subgroup G) (ρ : ↥K →* Equiv.Perm (Fin 3)), K ≤ C ∧ Function.Surjective ρ

namespace A320

variable {G : Type*} [Group G]

theorem solvRad_normal_of_normal (L : Subgroup G) [L.Normal] : (solvRad L).Normal :=
  ⟨fun _ hx g => conj_mem_solvRad (by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact Subgroup.mem_top g) hx⟩

theorem centralizerModSolvRad_inf_le [Finite G] {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) : centralizerModSolvRad L ⊓ L ≤ solvRad L := by
  rintro l ⟨⟨-, hl⟩, hlL⟩
  obtain ⟨-, ⟨hsimple, hnonab⟩, -⟩ := cComp_structure hL
  obtain ⟨a, b, hab⟩ := hnonab
  have hcen : (QuotientGroup.mk (⟨l, hlL⟩ : ↥L) : ↥L ⧸ (solvRad L).subgroupOf L) ∈
      Subgroup.center (↥L ⧸ (solvRad L).subgroupOf L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨⟨l', hl'⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (QuotientGroup.mk' ((solvRad L).subgroupOf L))
        ⁅(⟨l, hlL⟩ : ↥L), ⟨l', hl'⟩⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hl l' hl'
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥L ⧸ (solvRad L).subgroupOf L)) with h | h
  · rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hcen
    exact hcen
  · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm hab

theorem centralizes_of_central_radical {L : Subgroup G} (hLperf : ⁅L, L⁆ = L)
    (hRc : ⁅solvRad L, L⁆ = ⊥) {c : G} (hc : c ∈ centralizerModSolvRad L) {l : G} (hl : l ∈ L) :
    ⁅c, l⁆ = 1 := by
  set C := centralizerModSolvRad L with hCdef
  have hCL : ⁅C, L⁆ ≤ solvRad L := Subgroup.commutator_le.2 fun c hc l hl => hc.2 l hl
  have h1 : ⁅⁅L, C⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L C]
    exact le_bot_iff.1 (hRc ▸ Subgroup.commutator_mono hCL le_rfl)
  have h2 : ⁅⁅C, L⁆, L⁆ = ⊥ := le_bot_iff.1 (hRc ▸ Subgroup.commutator_mono hCL le_rfl)
  have h3 : ⁅⁅L, L⁆, C⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := C) h1 h2
  rw [hLperf] at h3
  have h4 : ⁅l, c⁆ ∈ (⊥ : Subgroup G) := h3 ▸ Subgroup.commutator_mem_commutator hl hc
  rw [← commutatorElement_inv, Subgroup.mem_bot.1 h4, inv_one]

theorem card_solvRad_eq [Finite G] (L : Subgroup G) :
    Nat.card (solvRad L) = Nat.card (CFSG.solvableRadical ↥L) := by
  rw [← A36A.subgroupOf_solvRad L]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toEquiv).symm

theorem exists_orderOf_eq_three_of_surjective {K : Type*} [Group K] [Finite K]
    (ρ : K →* Equiv.Perm (Fin 3)) (hρ : Function.Surjective ρ) : ∃ y : K, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have h2 : Nat.card (K ⧸ ρ.ker) = 6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv, Nat.card_perm]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have : 3 ∣ Nat.card K := by
    rw [h1, h2]
    exact Dvd.dvd.mul_right (by norm_num) _
  exact exists_prime_orderOf_dvd_card' 3 this

theorem mem_zpowers_of_mem_zpowers_prime {p : ℕ} [hp : Fact p.Prime] {x y : G}
    (hx : orderOf x = p) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) :
    x ∈ Subgroup.zpowers y := by
  have hcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have := mem_zpowers_of_prime_card (G := Subgroup.zpowers x) hcard (g := ⟨y, hy⟩)
    (g' := ⟨x, Subgroup.mem_zpowers x⟩) (fun h => hy1 (congrArg Subtype.val h))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
  exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩

end A320

end CFSG.Quasithin
