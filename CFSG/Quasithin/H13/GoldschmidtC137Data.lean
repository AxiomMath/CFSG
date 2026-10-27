module

public import CFSG.Quasithin.H13.GoldschmidtC137Baum

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem starPreIn_eq_preI {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    (Y : Subgroup (MulAut (IntMod V hV))) : starPreIn hV A Y = preI hV A hA Y := by
  ext g
  rw [mem_starPreIn, mem_preI]
  constructor
  · rintro ⟨hgA, hgN, hY⟩
    exact ⟨hgA, hY⟩
  · rintro ⟨hgA, hY⟩
    exact ⟨hgA, hA hgA, hY⟩

theorem starPreIn_le {A : Subgroup G} {Y : Subgroup (MulAut (IntMod V hV))} :
    starPreIn hV A Y ≤ A := fun _ hg => ((mem_starPreIn).1 hg).1

theorem starPreIn_mono {A B : Subgroup G} (h : A ≤ B) {Y : Subgroup (MulAut (IntMod V hV))} :
    starPreIn hV A Y ≤ starPreIn hV B Y := fun _ hg => by
  obtain ⟨hgA, hgN, hY⟩ := (mem_starPreIn).1 hg
  exact (mem_starPreIn).2 ⟨h hgA, hgN, hY⟩

theorem autI_starPreIn {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    {Y : Subgroup (MulAut (IntMod V hV))} (hY : Y ≤ autI hV A) :
    autI hV (starPreIn hV A Y) = Y := by
  rw [starPreIn_eq_preI hV hA]
  exact autI_preI hV hY

theorem card_starPreIn {A : Subgroup G} (hA : A ≤ normalizer (V : Set G))
    {Y : Subgroup (MulAut (IntMod V hV))} (hY : Y ≤ autI hV A) :
    Nat.card (starPreIn hV A Y) = Nat.card Y * Nat.card ↥(A ⊓ centralizer (V : Set G)) := by
  rw [starPreIn_eq_preI hV hA]
  exact card_preI hV hY

theorem isSylowTwoOf_starPreIn [Finite G] {R H : Subgroup G} (hRH : R ≤ H)
    (hHN : H ≤ normalizer (V : Set G)) (hR : IsPGroup 2 R)
    (hA₂ : IsSylowTwoOf (R ⊓ centralizer (V : Set G)) (H ⊓ centralizer (V : Set G)))
    {Y : Subgroup (MulAut (IntMod V hV))} (hY : Y ≤ autI hV R) :
    IsSylowTwoOf (starPreIn hV R Y) (starPreIn hV H Y) := by
  have hRN : R ≤ normalizer (V : Set G) := hRH.trans hHN
  have hYH : Y ≤ autI hV H := hY.trans (autI_mono hV hRH)
  have hle : starPreIn hV R Y ≤ starPreIn hV H Y := starPreIn_mono hV hRH
  refine ⟨hle, hR.to_le (starPreIn_le hV), ?_⟩
  intro h2
  have c1 := card_starPreIn hV hRN hY
  have c2 := card_starPreIn hV hHN hYH
  have r1 := Subgroup.relIndex_mul_card (starPreIn hV R Y) (starPreIn hV H Y)
  rw [inf_eq_left.2 hle] at r1
  have hle2 : R ⊓ centralizer (V : Set G) ≤ H ⊓ centralizer (V : Set G) :=
    inf_le_inf_right _ hRH
  have r2 := Subgroup.relIndex_mul_card (R ⊓ centralizer (V : Set G))
    (H ⊓ centralizer (V : Set G))
  rw [inf_eq_left.2 hle2] at r2
  have hpos : 0 < Nat.card Y * Nat.card ↥(R ⊓ centralizer (V : Set G)) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : (starPreIn hV R Y).relIndex (starPreIn hV H Y) =
      (R ⊓ centralizer (V : Set G)).relIndex (H ⊓ centralizer (V : Set G)) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (starPreIn hV R Y).relIndex (starPreIn hV H Y) *
          (Nat.card Y * Nat.card ↥(R ⊓ centralizer (V : Set G)))
        = (starPreIn hV R Y).relIndex (starPreIn hV H Y) * Nat.card (starPreIn hV R Y) := by
          rw [c1]
      _ = Nat.card (starPreIn hV H Y) := r1
      _ = Nat.card Y * Nat.card ↥(H ⊓ centralizer (V : Set G)) := c2
      _ = Nat.card Y * ((R ⊓ centralizer (V : Set G)).relIndex (H ⊓ centralizer (V : Set G)) *
            Nat.card ↥(R ⊓ centralizer (V : Set G))) := by rw [r2]
      _ = _ := by ring
  apply hA₂.2.2
  show 2 ∣ (R ⊓ centralizer (V : Set G)).relIndex (H ⊓ centralizer (V : Set G))
  rw [← key]
  exact h2

theorem cjSub_starPreIn {H : Subgroup G} (hHN : H ≤ normalizer (V : Set G)) {ℓ : G} (hℓ : ℓ ∈ H)
    (Y : Subgroup (MulAut (IntMod V hV))) :
    cjSub ℓ (starPreIn hV H Y) =
      starPreIn hV H (B1.conjAut (convI hV ⟨ℓ, hHN hℓ⟩) Y) := by
  ext x
  rw [mem_cjSub, mem_starPreIn, mem_starPreIn]
  have hconv : ∀ (hxN : x ∈ normalizer (V : Set G)) (hg : ℓ⁻¹ * x * ℓ ∈ normalizer (V : Set G)),
      convI hV ⟨ℓ⁻¹ * x * ℓ, hg⟩ = (convI hV ⟨ℓ, hHN hℓ⟩)⁻¹ * convI hV ⟨x, hxN⟩ *
        convI hV ⟨ℓ, hHN hℓ⟩ := by
    intro hxN hg
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  constructor
  · rintro ⟨hH, hg, hY⟩
    have hxH : x ∈ H := by
      have := H.mul_mem (H.mul_mem hℓ hH) (H.inv_mem hℓ)
      simpa [mul_assoc] using this
    refine ⟨hxH, hHN hxH, ?_⟩
    rw [B1.mem_conjAut, ← hconv (hHN hxH) hg]
    exact hY
  · rintro ⟨hxH, hxN, hY⟩
    have hH : ℓ⁻¹ * x * ℓ ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hℓ) hxH) hℓ
    refine ⟨hH, hHN hH, ?_⟩
    rw [B1.mem_conjAut] at hY
    rw [hconv hxN (hHN hH)]
    exact hY

theorem exists_Dpiece [Finite G] {X L R : Subgroup G} (hXN : X ≤ normalizer (V : Set G))
    (hLX : L ≤ X) (hRX : R ≤ X) (hR : IsPGroup 2 R)
    (hA₂ : IsSylowTwoOf (R ⊓ centralizer (V : Set G)) ((L ⊔ R) ⊓ centralizer (V : Set G)))
    {A₀ : Subgroup G} (hA₀ : IsMaxElemAbelian R A₀) {ℓ : G} (hℓ : ℓ ∈ L) :
    (cjSub ℓ (starPreIn hV R (autI hV A₀)) ≤ X) ∧
      IsSylowTwoOf (cjSub ℓ (starPreIn hV R (autI hV A₀)))
        (starPreIn hV (L ⊔ R) (B1.conjAut (convI hV ⟨ℓ, hXN (hLX hℓ)⟩) (autI hV A₀))) ∧
      B1.conjAut (convI hV ⟨ℓ, hXN (hLX hℓ)⟩) (autI hV A₀) =
        autI hV (thompsonJ (cjSub ℓ (starPreIn hV R (autI hV A₀)))) ∧
      Open.pRank 2 (cjSub ℓ (starPreIn hV R (autI hV A₀))) = Open.pRank 2 R := by
  have hRN : R ≤ normalizer (V : Set G) := hRX.trans hXN
  have hLRX : L ⊔ R ≤ X := sup_le hLX hRX
  have hLRN : L ⊔ R ≤ normalizer (V : Set G) := hLRX.trans hXN
  have hAR : A₀ ≤ R := hA₀.1
  have hY₀ : autI hV A₀ ≤ autI hV R := autI_mono hV hAR
  set Y₀ := autI hV A₀ with hY₀def
  set RY := starPreIn hV R Y₀ with hRY
  have hA₀RY : A₀ ≤ RY := fun a ha =>
    (mem_starPreIn).2 ⟨hAR ha, hRN (hAR ha), convI_mem_autI hV ha (hRN (hAR ha))⟩
  have hrank : Open.pRank 2 RY = Open.pRank 2 R :=
    B2F.pRank_eq_of_isMaxElemAbelian hA₀ hA₀RY (starPreIn_le hV)
  have hA₀max : IsMaxElemAbelian RY A₀ := B2F.isMaxElemAbelian_of_pRank_eq hA₀ hA₀RY hrank
  have hJ : Y₀ = autI hV (thompsonJ RY) := by
    apply le_antisymm
    · exact autI_mono hV (le_iSup₂_of_le A₀ hA₀max le_rfl)
    · calc autI hV (thompsonJ RY) ≤ autI hV RY := autI_mono hV (thompsonJ_le_self RY)
        _ = Y₀ := autI_starPreIn hV hRN hY₀
  have hℓN : ℓ ∈ normalizer (V : Set G) := hXN (hLX hℓ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_cjSub] at hx
    have h1 : ℓ⁻¹ * x * ℓ ∈ X := hRX (starPreIn_le hV hx)
    have := X.mul_mem (X.mul_mem (hLX hℓ) h1) (X.inv_mem (hLX hℓ))
    simpa [mul_assoc] using this
  · have hS := isSylowTwoOf_starPreIn hV (le_sup_right : R ≤ L ⊔ R) hLRN hR hA₂ hY₀
    have := B2F.isSylowTwoOf_cjSub ℓ hS
    rwa [cjSub_starPreIn hV hLRN ((le_sup_left : L ≤ L ⊔ R) hℓ) Y₀] at this
  · have h1 : thompsonJ (cjSub ℓ RY) = cjSub ℓ (thompsonJ RY) :=
      (thompsonJ_map_mulEquiv (MulAut.conj ℓ) RY).symm
    rw [h1, ← autI_cjSub hV hℓN, ← conjAut_eq_map, ← hJ]
  · rw [B2F.pRank_cjSub, hrank]

end CFSG.Quasithin.H13.U3.GC137
