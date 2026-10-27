module

public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Quasithin.Vol2.Ch11SecA02Card

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

theorem exists_starHom {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥)
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ ψ : ↥(starImage 3 L) →* (↥L ⧸ CFSG.pCore 2 ↥L), Function.Surjective ψ ∧
      ∀ y : ↥(starImage 3 L), ψ y = 1 → ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ₀ : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ₀
  set π₃ := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ₃
  let ρ : ↥L →* ↥(starImage 3 L) :=
    (π₃.comp L.subtype).codRestrict (starImage 3 L) (fun x => ⟨x, x.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : ↥L, x ∈ ρ.ker → (x : H) ∈ CFSG.pPrimeCore 3 H := by
    intro x hx
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change π₃ (x : H) = 1 at h1
    rwa [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hN3 : Nat.Coprime 3 (Nat.card ρ.ker) := by
    have hle : ρ.ker.map L.subtype ≤ CFSG.pPrimeCore 3 H := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hNX : ρ.ker.map φ₀ = ⊥ := by
    have hn : (ρ.ker.map φ₀).Normal :=
      Subgroup.Normal.map inferInstance φ₀ (QuotientGroup.mk'_surjective _)
    have hne : ρ.ker.map φ₀ ≠ ⊤ := by
      intro htop
      have h1 : Nat.card (ρ.ker.map φ₀) ∣ Nat.card ρ.ker := by
        rw [← MonoidHom.domRestrict_range]
        exact card_range_dvd _
      rw [htop, Subgroup.card_top] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right h1 hN3) h3)
        (by norm_num)
    have hle := le_center_of_normal_ne_top hQ hne
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  have hle : ρ.ker ≤ φ₀.ker := by
    intro x hx
    have : φ₀ x ∈ ρ.ker.map φ₀ := Subgroup.mem_map_of_mem φ₀ hx
    rw [hNX, Subgroup.mem_bot] at this
    exact this
  set e := QuotientGroup.quotientKerEquivOfSurjective ρ hρ with he
  have he' : ∀ x : ↥L, e.symm (ρ x) = (x : ↥L ⧸ ρ.ker) := fun x => e.symm_apply_eq.mpr rfl
  set ψ := (QuotientGroup.lift ρ.ker φ₀ hle).comp e.symm.toMonoidHom with hψ
  have hψρ : ∀ x : ↥L, ψ (ρ x) = φ₀ x := by
    intro x
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he', QuotientGroup.lift_mk]
  refine ⟨ψ, fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    exact ⟨ρ x, hψρ x⟩
  · obtain ⟨x, rfl⟩ := hρ y
    rw [hψρ, hφ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecA
