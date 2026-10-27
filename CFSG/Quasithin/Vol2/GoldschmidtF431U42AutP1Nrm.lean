module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Lat

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.F431.U42 (Y normalizer_T)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45)

theorem normalizer_That_le_Bh :
    Subgroup.normalizer (That : Set Ah) ≤ Bh := by
  have inner : ∀ y : Y, incl y ∈ Subgroup.normalizer (That : Set Ah) → incl y ∈ Bh := by
    intro y hy
    have hyT : y ∈ Subgroup.normalizer (U42.T : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := (Subgroup.mem_normalizer_iff.1 hy) (incl h)
      have e1 : h ∈ U42.T ↔ incl h ∈ That := by rw [← comap_That]; rfl
      have e2 : y * h * y⁻¹ ∈ U42.T ↔ incl y * incl h * (incl y)⁻¹ ∈ That := by
        rw [← comap_That, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      rw [e1, e2]
      exact h1
    rw [normalizer_T] at hyT
    rw [← comap_Bh] at hyT
    exact hyT
  intro g hg
  by_cases hgY : g ∈ Yh
  · obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl g).1 hgY
    exact inner y hg
  · have hf : fhatA⁻¹ ∉ Yh := fun h => fhatA_not_mem_Yh (Yh.inv_mem_iff.1 h)
    have h1 : g * fhatA⁻¹ ∈ Yh := by
      rw [Subgroup.mul_mem_iff_of_index_two index_Yh]
      exact iff_of_false hgY hf
    obtain ⟨y, hy⟩ := (mem_Yh_iff_incl _).1 h1
    have h2 : g * fhatA⁻¹ ∈ Subgroup.normalizer (That : Set Ah) :=
      Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (Subgroup.le_normalizer fhatA_mem_That))
    rw [← hy] at h2
    have h3 := inner y h2
    rw [hy] at h3
    have := Bh.mul_mem h3 fhatA_mem_Bh
    simpa using this

theorem pair_eq_of_isYAmalgamPair_A
    {N₁ N₂ : Subgroup Ah} (h : IsYAmalgamPair That N₁ N₂) :
    (N₁ = P1h ∧ N₂ = P2h) ∨ (N₁ = P2h ∧ N₂ = P1h) := by
  have h1 : P1h = N₁ ∨ P1h = N₂ :=
    (h.2.2 P1h).1 ⟨isMaximalTwoLocal_P1h, normalizer_That_le_Bh.trans Bh_le_P1h⟩
  have h2 : P2h = N₁ ∨ P2h = N₂ :=
    (h.2.2 P2h).1 ⟨isMaximalTwoLocal_P2h, normalizer_That_le_Bh.trans Bh_le_P2h⟩
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · exact absurd h2.symm P1h_ne_P2h
  · exact Or.inl ⟨rfl, h2.symm⟩
  · exact Or.inr ⟨h2.symm, rfl⟩
  · exact absurd h2.symm P1h_ne_P2h

theorem not_swapped_A {G : Type}
    [Group G] {M₁ M₂ : Subgroup G}
    (iso : (RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups P2h P1h))
    {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : z ∈ centerOf (M₁ ⊓ M₂))
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁) : False := by
  let f12 : ↥(M₁ ⊓ M₂) ≃* ↥(P2h ⊓ P1h) := iso.φ12
  let f2 : ↥M₂ ≃* ↥P1h := iso.φ2
  have hBc : P2h ⊓ P1h = Bh := inf_comm _ _
  set z' : ↥(M₁ ⊓ M₂) := ⟨z, hzc.1⟩ with hz'
  set g : Ah := ((f12 z' : ↥(P2h ⊓ P1h)) : Ah) with hg
  have hgB : g ∈ Bh := hBc ▸ (f12 z').2
  have hcomm : ∀ b ∈ Bh, b * g = g * b := by
    intro b hb
    have hb' : b ∈ P2h ⊓ P1h := hBc ▸ hb
    set u : ↥(M₁ ⊓ M₂) := f12.symm ⟨b, hb'⟩ with hu
    have h1 : u * z' = z' * u := Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzc.2) u u.2)
    have h2 := congrArg (fun a => ((f12 a : ↥(P2h ⊓ P1h)) : Ah)) h1
    simpa [hu, hg, map_mul] using h2
  have hg2 : g * g = 1 := by
    have : z' * z' = 1 := Subtype.ext (by simpa [pow_two] using hz2)
    have h := congrArg (fun a => ((f12 a : ↥(P2h ⊓ P1h)) : Ah)) this
    simpa [hg, map_mul] using h
  have hg1 : g ≠ 1 := fun h => hz1 (by
    have h1 : f12 z' = 1 := Subtype.ext h
    have h2 : z' = 1 := f12.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2)
  have hgx : g = xA := central_invol_Bh hgB hcomm hg2 hg1
  have hz2' : ((f2 ⟨z, hzc.1.2⟩ : ↥P1h) : Ah) = xA := by
    have hc2 : Subgroup.inclusion (inf_le_right : P2h ⊓ P1h ≤ P1h) (f12 z') =
        f2 (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) z') := iso.comm2 z'
    have := congrArg Subtype.val hc2
    rw [← hgx]
    exact this.symm
  have hle : M₂ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    set a : ↥P1h := f2 ⟨m, hm⟩
    set b : ↥P1h := f2 ⟨z, hzc.1.2⟩
    have hab : (b : Ah) * (a : Ah) = (a : Ah) * (b : Ah) := by
      rw [hz2']
      exact ((mul_xA_comm_iff _).2 a.2).symm
    have h2 : f2 (⟨z, hzc.1.2⟩ * ⟨m, hm⟩) = f2 (⟨m, hm⟩ * ⟨z, hzc.1.2⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hab
    exact (congrArg Subtype.val (f2.injective h2)).symm
  have hM : M₁ ⊓ M₂ = M₂ := inf_eq_right.2 (hle.trans hcz)
  have h1 : Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥(P2h ⊓ P1h) := Nat.card_congr f12.toEquiv
  have h2 : Nat.card ↥M₂ = Nat.card ↥P1h := Nat.card_congr f2.toEquiv
  rw [hM, h2, hBc, card_Bh, card_P1h] at h1
  omega

end CFSG.Quasithin.H13.F431.U42Aut
