module

public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup
open scoped Pointwise

theorem prime_core_free_quotient_supplement_centralizer_is_prime_core {r : ℕ} (hr : r.Prime)
    {B : Type*} [Group B] [Finite B] {L N : Subgroup B} [L.Normal] [N.Normal]
    (hcore : pCore r (L ⧸ N.subgroupOf L) = ⊥) (T : Sylow r B) {K : Subgroup B} (hKL : K ≤ L)
    (hTK : (T : Subgroup B) ≤ normalizer (K : Set B))
    (hLNK : (L : Set B) = (N : Set B) * (K : Set B))
    (hR : ((centralizerSection (T : Subgroup B) L N).subgroupOf
      (K ⊔ (T : Subgroup B))).Normal) :
    ((K ⊔ (T : Subgroup B) : Subgroup B) : Set B) = (K : Set B) * (T : Set B) ∧
      centralizerSection (T : Subgroup B) L N = inSubgroup (pCore r) (K ⊔ (T : Subgroup B)) := by
  have : Fact r.Prime := ⟨hr⟩
  set KT := K ⊔ (T : Subgroup B) with hKT
  set R := centralizerSection (T : Subgroup B) L N with hRdef
  set U := inSubgroup (pCore r) KT with hU
  have hTKT : (T : Subgroup B) ≤ KT := le_sup_right
  have hKKT : K ≤ KT := le_sup_left
  have hKTmul : (KT : Set B) = (K : Set B) * (T : Set B) :=
    coe_mul_of_right_le_normalizer_left K (T : Subgroup B) hTK
  have hUr : IsPGroup r U := pCore_isPGroup.map KT.subtype
  have hUKT : U ≤ KT := map_subtype_le _
  have hUn : ∀ g ∈ KT, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    rintro g hg _ ⟨u, hu, rfl⟩
    exact ⟨⟨g, hg⟩ * u * ⟨g, hg⟩⁻¹, pCore_normal.conj_mem u hu ⟨g, hg⟩, rfl⟩
  have hUT : U ≤ (T : Subgroup B) := by
    have hTnorm : (T : Subgroup B) ≤ normalizer (U : Set B) := fun t ht => by
      rw [mem_normalizer_iff]
      intro u
      constructor
      · exact hUn t (hTKT ht) u
      · intro h
        have h' := hUn t⁻¹ (inv_mem (hTKT ht)) _ h
        simpa [mul_assoc] using h'
    have hsup : IsPGroup r ((T : Subgroup B) ⊔ U : Subgroup B) :=
      IsPGroup.to_sup_of_normal_right' T.isPGroup' hUr hTnorm
    have heq := T.is_maximal' hsup le_sup_left
    rw [← heq]
    exact le_sup_right
  have hKn : ∀ g ∈ KT, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    have hg' : g ∈ (K : Set B) * (T : Set B) := hKTmul ▸ hg
    obtain ⟨a, ha, t, ht, rfl⟩ := hg'
    have h1 : t * k * t⁻¹ ∈ K := (mem_normalizer_iff.mp (hTK ht) k).mp hk
    have h2 : a * t * k * (a * t)⁻¹ = a * (t * k * t⁻¹) * a⁻¹ := by group
    rw [h2]
    exact K.mul_mem (K.mul_mem ha h1) (K.inv_mem ha)
  have hUKN : U ⊓ K ≤ N := by
    set π := QuotientGroup.mk' (N.subgroupOf L) with hπ
    set W : Subgroup L := (U ⊓ K).subgroupOf L with hW
    have hWr' : IsPGroup r W := (hUr.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hKL)).symm
    have hWr : IsPGroup r (W.map π) := hWr'.map π
    have hWn : (W.map π).Normal := by
      refine ⟨fun x hx y => ?_⟩
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) y
      have hl : (l : B) ∈ (N : Set B) * (K : Set B) := hLNK ▸ l.2
      obtain ⟨n, hn, k, hk, hnk⟩ := hl
      have hnk' : n * k = (l : B) := hnk
      have hkL : k ∈ L := hKL hk
      have hlk : π l = π ⟨k, hkL⟩ := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
        change (l : B)⁻¹ * k ∈ N
        rw [← hnk']
        have h := (inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) k⁻¹
        have e : (n * k)⁻¹ * k = k⁻¹ * n⁻¹ * k⁻¹⁻¹ := by group
        rw [e]
        exact h
      rw [hlk, ← map_mul, ← map_inv, ← map_mul]
      refine ⟨⟨k, hkL⟩ * w * ⟨k, hkL⟩⁻¹, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf]
      have hw' : (w : B) ∈ U ⊓ K := hw
      exact ⟨hUn k (hKKT hk) _ hw'.1, K.mul_mem (K.mul_mem hk hw'.2) (K.inv_mem hk)⟩
    have hle : W.map π ≤ pCore r (L ⧸ N.subgroupOf L) := le_sSup ⟨hWn, hWr⟩
    rw [hcore] at hle
    intro x hx
    have hxL : x ∈ L := hKL hx.2
    have hmem : π ⟨x, hxL⟩ ∈ W.map π := ⟨⟨x, hxL⟩, hx, rfl⟩
    rw [le_bot_iff.mp hle, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf] at hmem
    exact hmem
  have hUR : U ≤ R := by
    intro u hu
    have huT : u ∈ (T : Subgroup B) := hUT hu
    refine ⟨huT, ?_, ?_, fun l hl => ?_⟩
    · rw [normalizer_eq_top]
      exact mem_top u
    · rw [normalizer_eq_top]
      exact mem_top u
    · have hl' : l ∈ (N : Set B) * (K : Set B) := hLNK ▸ hl
      obtain ⟨n, hn, k, hk, rfl⟩ := hl'
      have hkuU : k * u * k⁻¹ * u⁻¹ ∈ U := U.mul_mem (hUn k (hKKT hk) u hu) (U.inv_mem hu)
      have hkuK : k * u * k⁻¹ * u⁻¹ ∈ K := by
        have h := K.mul_mem hk (hKn u (hUKT hu) k⁻¹ (K.inv_mem hk))
        have e : k * (u * k⁻¹ * u⁻¹) = k * u * k⁻¹ * u⁻¹ := by group
        rwa [e] at h
      have hkuN : k * u * k⁻¹ * u⁻¹ ∈ N := hUKN ⟨hkuU, hkuK⟩
      have hunN : u * n⁻¹ * u⁻¹ ∈ N :=
        (inferInstance : N.Normal).conj_mem _ (N.inv_mem hn) u
      have e : n * k * u * (n * k)⁻¹ * u⁻¹ = n * (k * u * k⁻¹ * u⁻¹) * (u * n⁻¹ * u⁻¹) := by
        group
      rw [e]
      exact N.mul_mem (N.mul_mem hn hkuN) hunN
  have hRU : R ≤ U := by
    have hRT : R ≤ (T : Subgroup B) := centralizerSection_le_left _ _ _
    have hRKT : R ≤ KT := hRT.trans hTKT
    have hRp : IsPGroup r (R.subgroupOf KT) :=
      (T.isPGroup'.to_le hRT).of_equiv (Subgroup.subgroupOfEquivOfLe hRKT).symm
    have hle : R.subgroupOf KT ≤ pCore r KT := le_sSup ⟨hR, hRp⟩
    intro x hx
    exact ⟨⟨x, hRKT hx⟩, hle hx, rfl⟩
  exact ⟨hKTmul, le_antisymm hRU hUR⟩

end CFSG.Quasithin.SteinbergCD
