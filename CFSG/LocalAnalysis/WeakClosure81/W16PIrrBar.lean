module

public import CFSG.LocalAnalysis.WeakClosure81.W16PIrrTrans
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem normalizer_UAOf_le_normalizer_wHat_sup_aHat (h : Assumption131 G Γ VA i)
    (hrank : ∀ B ∈ Γ, mRank B ≤ i) {A B₀ : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB₀ : B₀ ≤ A)
    (hN : G ⊓ Subgroup.normalizer (A : Set (LGL 2 V)) ≤
      Subgroup.normalizer (B₀ : Set (LGL 2 V))) :
    Subgroup.normalizer (UAOf G VA A : Set (VG G)) ≤
      Subgroup.normalizer ((wHat G (VA A) ⊔ aHat G B₀ : Subgroup (VG G)) : Set (VG G)) := by
  intro y hy
  obtain ⟨v, g, rfl⟩ := exists_eq_inl_mul_inr y
  have hcommA : commSub A ≤ VA A := commSub_le_VA_of_mRank_le h hA (hrank A hA)
  have hcommB : commSub B₀ ≤ VA A := (commSub_mono B₀ A hB₀).trans hcommA
  have hinlS : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) ∈
      Subgroup.normalizer ((wHat G (VA A) ⊔ aHat G B₀ : Subgroup (VG G)) : Set (VG G)) :=
    vHat_le_normalizer_wHat_sup_aHat (W := VA A) (A := B₀) hcommB
      (mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩)
  have hinlU : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) ∈
      Subgroup.normalizer (UAOf G VA A : Set (VG G)) :=
    vHat_le_normalizer_wHat_sup_aHat (W := VA A) (A := A) hcommA
      (mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩)
  have hinrU : (SemidirectProduct.inr g : VG G) ∈
      Subgroup.normalizer (UAOf G VA A : Set (VG G)) := by
    have h1 : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G)⁻¹ *
        ((SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) * SemidirectProduct.inr g) ∈
        Subgroup.normalizer (UAOf G VA A : Set (VG G)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hinlU) hy
    rwa [inv_mul_cancel_left] at h1
  have hinvgU : (SemidirectProduct.inr g⁻¹ : VG G) ∈
      Subgroup.normalizer (UAOf G VA A : Set (VG G)) := by
    have h1 := Subgroup.inv_mem _ hinrU
    simpa [map_inv] using h1
  have hconjU : UAOf G VA (cj (g : LGL 2 V) A) = UAOf G VA A := by
    have h1 : conjSubgroup (UAOf G VA A) (SemidirectProduct.inr g⁻¹ : VG G) = UAOf G VA A :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hinvgU
    rwa [conjSubgroup_UAOf_inr_inv h hA g] at h1
  have hcjA : cj (g : LGL 2 V) A = A := by
    have h1 : (UAOf G VA (cj (g : LGL 2 V) A)).map (projG G) = cj (g : LGL 2 V) A :=
      map_projG_wHat_sup_aHat (h.le_G _ (h.invariant A hA (g : LGL 2 V) g.2))
    have h2 : (UAOf G VA A).map (projG G) = A := map_projG_wHat_sup_aHat (h.le_G A hA)
    rw [← h1, hconjU, h2]
  have hgNA : (g : LGL 2 V) ∈ Subgroup.normalizer (A : Set (LGL 2 V)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [cj] using hcjA)
  have hgNB : (g : LGL 2 V) ∈ Subgroup.normalizer (B₀ : Set (LGL 2 V)) :=
    hN ⟨g.2, hgNA⟩
  have hcjB : cj (g : LGL 2 V) B₀ = B₀ := by
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNB
    simpa [cj] using h1
  have hstab : conjSub (g : LGL 2 V) (VA A) = VA A := by
    have hmem : (g : LGL 2 V) ∈ stabilizerOf G (VA A) := by
      rw [← h.normalizer_eq A hA]
      exact ⟨g.2, hgNA⟩
    exact hmem.2
  have hinrS : (SemidirectProduct.inr g : VG G) ∈
      Subgroup.normalizer ((wHat G (VA A) ⊔ aHat G B₀ : Subgroup (VG G)) : Set (VG G)) := by
    have h1 : conjSubgroup (wHat G (VA A) ⊔ aHat G B₀) (SemidirectProduct.inr g⁻¹ : VG G) =
        wHat G (VA A) ⊔ aHat G B₀ := by
      rw [conjSubgroup_wHat_sup_aHat_inr_inv (VA A) B₀ g, hstab, hcjB]
    have h2 : (SemidirectProduct.inr g⁻¹ : VG G) ∈
        Subgroup.normalizer ((wHat G (VA A) ⊔ aHat G B₀ : Subgroup (VG G)) : Set (VG G)) :=
      conjSubgroup_eq_iff_mem_normalizer.mp h1
    have h3 := Subgroup.inv_mem _ h2
    simpa [map_inv] using h3
  exact Subgroup.mul_mem _ hinlS hinrS

private theorem barSub_le_sup_inf {G : Type*} [Group G] {K S U : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) (hS : S ≤ K) (hU : U ≤ K) (hSU : S ≤ U)
    (heq : barSub K φ S = barSub K φ U) : U ≤ S ⊔ (U ⊓ pCoreOf 2 K) := by
  intro u huU
  have huK : u ∈ K := hU huU
  have hmem : φ ⟨u, huK⟩ ∈ barSub K φ S := by
    rw [heq]
    exact mem_barSub.mpr ⟨⟨u, huK⟩, huU, rfl⟩
  obtain ⟨s, hsS, hsφ⟩ := mem_barSub.mp hmem
  have hker : ((s⁻¹ * ⟨u, huK⟩ : ↥K) : G) ∈ pCoreOf 2 K :=
    (hφ.ker_iff (s⁻¹ * ⟨u, huK⟩)).mp (by rw [map_mul, map_inv, hsφ, inv_mul_cancel])
  have hmemU : ((s⁻¹ * ⟨u, huK⟩ : ↥K) : G) ∈ U := by
    have hsU : (s : G) ∈ U := hSU hsS
    have hsinv : ((s⁻¹ : ↥K) : G) ∈ U := by
      have h1 := Subgroup.inv_mem _ hsU
      simpa [map_inv] using h1
    have h1 := Subgroup.mul_mem _ hsinv huU
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hsplit : u = (s : G) * ((s⁻¹ * ⟨u, huK⟩ : ↥K) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hsplit]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hsS)
    (Subgroup.mem_sup_right ⟨hmemU, hker⟩)

private theorem eq_bot_or_eq_of_card_le_two {H : Type*} [Group H] [Finite H] {B B' : Subgroup H}
    (hB : Nat.card B ≤ 2) (hle : B' ≤ B) : B' = ⊥ ∨ B' = B := by
  by_cases hbot : B' = ⊥
  · exact Or.inl hbot
  · right
    have h2 : 2 ≤ Nat.card B' := by
      have h := (Subgroup.one_lt_card_iff_ne_bot B').mpr hbot
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (le_trans hB h2)

theorem eq_bot_or_eq_of_barSub_UAOf (h : Assumption131 G Γ VA i) {A B₀ : Subgroup (LGL 2 V)}
    (hA : A ∈ Γ) (hB₀ : B₀ ≤ A) (h711 : Hyp711 (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G))
    {X : Type} [Group X] {φ : ↥(kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)) →* X}
    (hφ : IsBarMap (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G))
      (pCoreOf 2 (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G))) φ)
    (hbar : barSub (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)) φ
        (wHat G (VA A) ⊔ aHat G B₀) = ⊥ ∨
      barSub (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)) φ
          (wHat G (VA A) ⊔ aHat G B₀) =
        barSub (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)) φ (UAOf G VA A)) :
    B₀ = ⊥ ∨ B₀ = A := by
  let K : Subgroup (VG G) := kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)
  let U : Subgroup (VG G) := UAOf G VA A
  have hcoreK : pCoreOf 2 K ≤ pCoreOf 2 (⊤ : Subgroup (VG G)) :=
    h711.toHyp73.pcore_le
  have hUK : U ≤ K := le_kSub h711.toHyp73.mem
  have haHat : aHat G B₀ ≤ aHat G A := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
    exact mem_aHat.mpr ⟨g, hB₀ hg, rfl⟩
  have hS_le_U : wHat G (VA A) ⊔ aHat G B₀ ≤ U :=
    sup_le le_sup_left (haHat.trans le_sup_right)
  have hS_le_K : wHat G (VA A) ⊔ aHat G B₀ ≤ K := hS_le_U.trans hUK
  rcases hbar with hbot | heq
  · left
    have hS_le_J : wHat G (VA A) ⊔ aHat G B₀ ≤ pCoreOf 2 K := by
      intro x hx
      have hxK : x ∈ K := hS_le_K hx
      have hmem : φ ⟨x, hxK⟩ ∈ barSub K φ (wHat G (VA A) ⊔ aHat G B₀) :=
        mem_barSub.mpr ⟨⟨x, hxK⟩, hx, rfl⟩
      have h1 : φ ⟨x, hxK⟩ = 1 := by
        rw [hbot] at hmem
        simpa using hmem
      exact (hφ.ker_iff ⟨x, hxK⟩).mp h1
    have haHat_le_W : aHat G B₀ ≤ wHat G (VA A) := by
      have hle : aHat G B₀ ≤ UAOf G VA A ⊓ pCoreOf 2 (⊤ : Subgroup (VG G)) :=
        le_inf (le_sup_right.trans hS_le_U) (le_sup_right.trans (hS_le_J.trans hcoreK))
      rwa [inf_pCoreOf_UAOf h hA] at hle
    have hmap := Subgroup.map_mono (f := projG G) haHat_le_W
    rw [map_projG_aHat (hB₀.trans (h.le_G A hA)), map_projG_wHat (VA A)] at hmap
    exact le_bot_iff.mp hmap
  · right
    have hUJ_le_W : U ⊓ pCoreOf 2 K ≤ wHat G (VA A) := by
      intro x hx
      have hx' : x ∈ UAOf G VA A ⊓ pCoreOf 2 (⊤ : Subgroup (VG G)) :=
        ⟨hx.1, hcoreK hx.2⟩
      rwa [inf_pCoreOf_UAOf h hA] at hx'
    have hU_le : U ≤ (wHat G (VA A) ⊔ aHat G B₀) ⊔ (U ⊓ pCoreOf 2 K) :=
      barSub_le_sup_inf hφ hS_le_K hUK hS_le_U heq
    have hU_le_S : U ≤ wHat G (VA A) ⊔ aHat G B₀ :=
      hU_le.trans (sup_le le_rfl (hUJ_le_W.trans le_sup_left))
    have hSU : U = wHat G (VA A) ⊔ aHat G B₀ := le_antisymm hU_le_S hS_le_U
    have hUeq : UAOf G VA A = wHat G (VA A) ⊔ aHat G B₀ := hSU
    have hAB : A = B₀ := by
      have h1 : (UAOf G VA A).map (projG G) = A := map_projG_wHat_sup_aHat (h.le_G A hA)
      have h2 : (wHat G (VA A) ⊔ aHat G B₀).map (projG G) = B₀ :=
        map_projG_wHat_sup_aHat (hB₀.trans (h.le_G A hA))
      calc A = (UAOf G VA A).map (projG G) := h1.symm
        _ = (wHat G (VA A) ⊔ aHat G B₀).map (projG G) := by rw [hUeq]
        _ = B₀ := h2
    exact hAB.symm

section Certified


theorem eq_bot_or_eq_of_hyp711 (hTim : TimmesfeldTIRootInput) (h : Assumption131 G Γ VA i)
    (hrank : ∀ B ∈ Γ, mRank B ≤ i) {A B₀ : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB₀ : B₀ ≤ A)
    (hN : G ⊓ Subgroup.normalizer (A : Set (LGL 2 V)) ≤
      Subgroup.normalizer (B₀ : Set (LGL 2 V)))
    (h711 : Hyp711 (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G))
    {X : Type} [Group X] {φ : ↥(kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)) →* X}
    (hφ : IsBarMap (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G))
      (pCoreOf 2 (kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G))) φ) :
    B₀ = ⊥ ∨ B₀ = A := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup (VG G) := kSub (UAOf G VA A) (⊤ : Subgroup (VG G)) (vHat G)
  let U : Subgroup (VG G) := UAOf G VA A
  let S : Subgroup (VG G) := wHat G (VA A) ⊔ aHat G B₀
  have haHat : aHat G B₀ ≤ aHat G A := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
    exact mem_aHat.mpr ⟨g, hB₀ hg, rfl⟩
  have hSU : S ≤ U := sup_le le_sup_left (haHat.trans le_sup_right)
  have hle : barSub K φ S ≤ barSub K φ U := by
    intro x hx
    obtain ⟨k, hkS, hxk⟩ := mem_barSub.mp hx
    exact mem_barSub.mpr ⟨k, hSU hkS, hxk⟩
  have hbar : barSub K φ S = ⊥ ∨ barSub K φ S = barSub K φ U := by
    by_cases hc : Nat.card (barSub K φ U) ≤ 2
    · exact eq_bot_or_eq_of_card_le_two hc hle
    · have hbig : 2 < Nat.card (barSub K φ U) := not_le.1 hc
      by_cases hbot : barSub K φ S = ⊥
      · exact Or.inl hbot
      · right
        obtain ⟨⟨s, hsS⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
        have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
        have hVleB : barSub K φ U ≤ barSub K φ S := by
          intro t htV
          by_cases ht1 : t = 1
          · rw [ht1]
            exact (barSub K φ S).one_mem
          · obtain ⟨m, hmN, ht_eq⟩ :=
              exists_normalizer_conj_of_hyp711 hTim h711 hφ hbig (hle hsS) htV hs1' ht1
            have hmNS : (m : VG G) ∈ Subgroup.normalizer (S : Set (VG G)) :=
              normalizer_UAOf_le_normalizer_wHat_sup_aHat h hrank hA hB₀ hN hmN
            have hconjS : conjSubgroup S (m : VG G) = S :=
              conjSubgroup_eq_iff_mem_normalizer.mpr hmNS
            have hconj_bar : conjSubgroup (barSub K φ S) (φ m) = barSub K φ S := by
              have h1 := barSub_conjSubgroup (K := K) φ S m
              rw [hconjS] at h1
              exact h1.symm
            have hconj_inv : conjSubgroup (barSub K φ S) ((φ m)⁻¹) = barSub K φ S := by
              have h1 := conjSubgroup_conjSubgroup (barSub K φ S) (φ m) ((φ m)⁻¹)
              rw [mul_inv_cancel, conjSubgroup_one, hconj_bar] at h1
              exact h1
            have hmem : φ m * s * (φ m)⁻¹ ∈ barSub K φ S := by
              have h2 : φ m * s * (φ m)⁻¹ ∈ conjSubgroup (barSub K φ S) ((φ m)⁻¹) := by
                rw [mem_conjSubgroup_iff]
                convert hsS using 1
                group
              rwa [hconj_inv] at h2
            rw [ht_eq]
            exact hmem
        exact le_antisymm hle hVleB
  exact eq_bot_or_eq_of_barSub_UAOf h hA hB₀ h711 hφ hbar

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
