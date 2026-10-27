module

public import CFSG.Quasithin.Background.E1Defs
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commute_of_isElemAbelian {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hA ha hb

theorem mem_tauOf_of_le {H T A : Subgroup G} (hTH : T ≤ H) {t : G} :
    t ∈ tauOf H T A ↔ t ∈ T ∧ ∀ a ∈ A, ⁅t, a⁆ ∈ pCoreOf 2 H := by
  rw [mem_tauOf]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH h1), h3⟩

theorem le_tauOf [Finite G] {H T A : Subgroup G} (hT : IsSylowIn 2 T H) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) : A ⊔ pCoreOf 2 H ≤ tauOf H T A := by
  refine sup_le ?_ ?_
  · intro a ha
    refine (mem_tauOf_of_le hT.le).mpr ⟨hA ha, fun b hb => ?_⟩
    have h := commute_of_isElemAbelian hAab ha hb
    rw [commutatorElement_def, h]
    simp
  · intro o ho
    have hoT : o ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT ho
    refine (mem_tauOf_of_le hT.le).mpr ⟨hoT, fun b hb => ?_⟩
    have hbH : b ∈ H := hT.le (hA hb)
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hbH) o⁻¹).mp (inv_mem ho)
    have h2 : ⁅o, b⁆ = o * (b * o⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact Subgroup.mul_mem _ ho h1

theorem pCoreOf_two_le_of_isSylowIn [Finite G] {H S : Subgroup G} (hS : IsSylowIn 2 S H) :
    pCoreOf 2 H ≤ S :=
  B6.pCoreOf_two_le_of_isSylowTwoOf hS

theorem eight_one [Finite G] {H₁ H₂ T A K : Subgroup G} {i : ℕ} (hT : IsSylowIn 2 T H₁)
    (hA : A ≤ T) (hAab : IsElemAbelian 2 A) (hH : H₂ ≤ H₁) (hτ : tauOf H₁ T A ≤ T ⊓ H₂)
    (hS : IsSylowIn 2 (T ⊓ H₂) H₂) (hK : IsE i H₂ (T ⊓ H₂) A K) :
    A ⊔ pCoreOf 2 H₁ ≤ tauOf H₁ T A ∧ tauOf H₁ T A ≤ tauOf H₂ (T ⊓ H₂) A ∧
      tauOf H₂ (T ⊓ H₂) A ≤ tauOf K (T ⊓ K) A ∧ tauOf K (T ⊓ K) A ≤ K := by
  have h1 : A ⊔ pCoreOf 2 H₁ ≤ tauOf H₁ T A := le_tauOf hT hA hAab
  obtain ⟨hKH₂, hτK, hSK, -⟩ := hK
  have hAH₂ : A ≤ T ⊓ H₂ := fun a ha => hτ (h1 (Subgroup.mem_sup_left ha))
  have hO₁ : pCoreOf 2 H₁ ≤ H₂ := fun o ho => (hτ (h1 (Subgroup.mem_sup_right ho))).2
  have hO₁₂ : pCoreOf 2 H₁ ≤ pCoreOf 2 H₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO₁
      (hH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁)
  have h2 : tauOf H₁ T A ≤ tauOf H₂ (T ⊓ H₂) A := by
    intro t ht
    obtain ⟨-, -, ht3⟩ := mem_tauOf.mp ht
    exact (mem_tauOf_of_le inf_le_right).mpr ⟨hτ ht, fun a ha => hO₁₂ (ht3 a ha)⟩
  have h2' : A ⊔ pCoreOf 2 H₂ ≤ tauOf H₂ (T ⊓ H₂) A := le_tauOf hS (hAH₂) hAab
  have hO₂K : pCoreOf 2 H₂ ≤ K := fun o ho => (hτK (h2' (Subgroup.mem_sup_right ho))).2
  have hO₂K' : pCoreOf 2 H₂ ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO₂K
      (hKH₂.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₂))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₂)
  have hTK : (T ⊓ H₂) ⊓ K = T ⊓ K := by rw [inf_assoc, inf_eq_right.mpr hKH₂]
  have h3 : tauOf H₂ (T ⊓ H₂) A ≤ tauOf K (T ⊓ K) A := by
    intro t ht
    obtain ⟨-, -, ht3⟩ := mem_tauOf.mp ht
    have htK : t ∈ T ⊓ K := hTK ▸ hτK ht
    exact (mem_tauOf_of_le inf_le_right).mpr ⟨htK, fun a ha => hO₂K' (ht3 a ha)⟩
  have h4 : tauOf K (T ⊓ K) A ≤ K := fun t ht => (tauOf_le _ _ _ ht).2
  exact ⟨h1, h2, h3, h4⟩

theorem eight_two [Finite G] {H₁ H₂ T A K : Subgroup G} {i : ℕ} (hT : IsSylowIn 2 T H₁)
    (hA : A ≤ T) (hAab : IsElemAbelian 2 A) (hH : H₂ ≤ H₁) (hτ : tauOf H₁ T A ≤ T ⊓ H₂)
    (hS : IsSylowIn 2 (T ⊓ H₂) H₂) (hK : IsE i H₂ (T ⊓ H₂) A K) : IsE i H₁ T A K := by
  obtain ⟨-, h2, h3, h4⟩ := eight_one hT hA hAab hH hτ hS hK
  obtain ⟨hKH₂, -, hSK, hrest⟩ := hK
  have hTK : (T ⊓ H₂) ⊓ K = T ⊓ K := by rw [inf_assoc, inf_eq_right.mpr hKH₂]
  rw [hTK] at hSK hrest
  refine ⟨hKH₂.trans hH, ?_, hSK, hrest⟩
  exact (h2.trans h3).trans (tauOf_le K (T ⊓ K) A)

theorem map_pCoreOf_le [Finite G] {Q : Type*} [Group Q] (f : G →* Q) (H : Subgroup G) :
    (pCoreOf 2 H).map f ≤ pCoreOf 2 (H.map f) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 H)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).map f)
  rintro _ ⟨h, hh, rfl⟩
  exact Subgroup.le_normalizer_map f
    ⟨h, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh, rfl⟩

theorem tauOf_map_le [Finite G] {Q : Type*} [Group Q] (f : G →* Q) {H T A : Subgroup G}
    (hTH : T ≤ H) : (tauOf H T A).map f ≤ tauOf (H.map f) (T.map f) (A.map f) := by
  rintro _ ⟨t, ht, rfl⟩
  have hT' : T.map f ≤ H.map f := Subgroup.map_mono hTH
  refine (mem_tauOf_of_le hT').mpr ⟨Subgroup.mem_map_of_mem _ ht.1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_commutatorElement]
  exact map_pCoreOf_le f H (Subgroup.mem_map_of_mem _ (ht.2.2 a ha))

theorem inf_eq_pCoreOf_of_isSylowIn [Finite G] {T Y : Subgroup G} [Y.Normal]
    (hT : IsSylowIn 2 T ⊤) (hY : IsSylowIn 2 (pCoreOf 2 (⊤ : Subgroup G)) Y) :
    T ⊓ Y = pCoreOf 2 (⊤ : Subgroup G) := by
  have h1 : IsSylowIn 2 (T ⊓ Y) Y := hT.inf_normal le_top inferInstance
  have hle : pCoreOf 2 (⊤ : Subgroup G) ≤ T ⊓ Y :=
    le_inf (pCoreOf_two_le_of_isSylowIn hT) hY.le
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h1.card_eq, hY.card_eq]

theorem eight_three [Finite G] {T A Y : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T ⊤)
    (hA : A ≤ T) (hY : IsSylowIn 2 (pCoreOf 2 (⊤ : Subgroup G)) Y) :
    T ⊓ (Subgroup.centralizer ((A.map (QuotientGroup.mk' Y) : Subgroup (G ⧸ Y)) :
        Set (G ⧸ Y))).comap (QuotientGroup.mk' Y) = tauOf ⊤ T A ∧
      (tauOf ⊤ T A).map (QuotientGroup.mk' Y) ≤
        tauOf (⊤ : Subgroup (G ⧸ Y)) (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) := by
  have hTY := inf_eq_pCoreOf_of_isSylowIn hT hY
  have hOY : pCoreOf 2 (⊤ : Subgroup G) ≤ Y := hY.le
  have key : T ⊓ (Subgroup.centralizer ((A.map (QuotientGroup.mk' Y) : Subgroup (G ⧸ Y)) :
        Set (G ⧸ Y))).comap (QuotientGroup.mk' Y) = tauOf ⊤ T A := by
    ext t
    rw [mem_tauOf_of_le le_top, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.mem_centralizer_iff]
    refine and_congr_right fun htT => ?_
    constructor
    · intro h a ha
      have hc := h (QuotientGroup.mk' Y a) (Subgroup.mem_map_of_mem _ ha)
      have hcomm : QuotientGroup.mk' Y ⁅t, a⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hc.symm
      have hY' : ⁅t, a⁆ ∈ Y := (QuotientGroup.eq_one_iff _).mp hcomm
      have hT' : ⁅t, a⁆ ∈ T := by
        rw [commutatorElement_def]
        exact T.mul_mem (T.mul_mem (T.mul_mem htT (hA ha)) (T.inv_mem htT)) (T.inv_mem (hA ha))
      rw [← hTY]
      exact ⟨hT', hY'⟩
    · intro h x hx
      obtain ⟨a, ha, rfl⟩ := hx
      have h1 : ⁅t, a⁆ ∈ Y := hOY (h a ha)
      have h2 : QuotientGroup.mk' Y ⁅t, a⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
  refine ⟨key, ?_⟩
  have := tauOf_map_le (QuotientGroup.mk' Y) (H := ⊤) (T := T) (A := A) le_top
  rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y)] at this

end E1

end CFSG.Quasithin
