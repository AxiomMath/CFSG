module

public import CFSG.Quasithin.Background.RonanE111LSG

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lift_pgroup_sub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T T₀ N Y A : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀N : T₀ ≤ Subgroup.normalizer (N : Set G)) (hT₀Y : T₀ ≤ Subgroup.normalizer (Y : Set G))
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hYN : Y ≤ N)
    (hpg : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ Y) (hgen : N ≤ ⁅N, A⁆ ⊔ Y)
    (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀)) (hτ : E1.tauOf ⊤ T A ≤ T₀) :
    N ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K}, K) ⊔ Y := by
  set K : Subgroup G := N ⊔ T₀ with hKdef
  have hNK : N ≤ K := le_sup_left
  have hT₀K : T₀ ≤ K := le_sup_right
  have hYK : Y ≤ K := hYN.trans hNK
  have hAK : A ≤ K := hAT₀.trans hT₀K
  have hAT : A ≤ T := hAT₀.trans hT₀T
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hT₀N
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := sup_le hNY hT₀Y
  haveI hNn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  haveI hYn : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKY
  have hSylK : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K), Subgroup.map_top,
      Subgroup.range_subtype]
    exact hSyl
  have hAT' : A.subgroupOf K ≤ (T ⊓ K).subgroupOf K := Subgroup.subgroupOf_mono K (le_inf hAT hAK)
  have hAab' : IsElemAbelian 2 (A.subgroupOf K) := ronanE111_isElemAbelian_subgroupOf hAab K
  have hπs : Function.Surjective (QuotientGroup.mk' (Y.subgroupOf K)) :=
    QuotientGroup.mk'_surjective _
  have hXp : IsPGroup p ((N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K))) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨k, hk⟩ := hpg (x : G) (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨k, Subtype.ext ?_⟩
    show (y : ↥K ⧸ Y.subgroupOf K) ^ p ^ k = 1
    rw [← hxy, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  haveI hXbn : ((N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K))).Normal :=
    Subgroup.Normal.map hNn _ hπs
  have hXAle : ⁅(N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)),
      (A.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K))⁆ ≤
      (N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)) := by
    refine Subgroup.commutator_le.mpr fun x hx a _ => ?_
    have h1 := (Subgroup.mul_mem _ hx (hXbn.conj_mem x⁻¹ (Subgroup.inv_mem _ hx) a))
    rw [commutatorElement_def]
    simpa [mul_assoc] using h1
  have hYbot : (Y.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have hcl : ⁅N, A⁆ ≤ K := Subgroup.commutator_le.mpr fun n hn a ha => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hNK hn) (hAK ha)) (K.inv_mem (hNK hn)))
      (K.inv_mem (hAK ha))
  have hsubeq : (⁅N, A⁆ ⊔ Y).subgroupOf K =
      ⁅N.subgroupOf K, A.subgroupOf K⁆ ⊔ Y.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hcl hYK), Subgroup.map_sup,
      E111R.commutator_subgroupOf hNK hAK, Subgroup.map_subgroupOf_eq_of_le hcl,
      Subgroup.map_subgroupOf_eq_of_le hYK]
  have hXAge : (N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)) ≤
      ⁅(N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)),
        (A.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K))⁆ := by
    have h1 : N.subgroupOf K ≤ ⁅N.subgroupOf K, A.subgroupOf K⁆ ⊔ Y.subgroupOf K := by
      rw [← hsubeq]
      exact Subgroup.subgroupOf_mono K hgen
    have h2 := Subgroup.map_mono (f := QuotientGroup.mk' (Y.subgroupOf K)) h1
    rwa [Subgroup.map_sup, hYbot, sup_bot_eq, Subgroup.map_commutator] at h2
  have hXA := le_antisymm hXAle hXAge
  have hLift := E1.ten_six hp hp2 hSylK hAT' hAab' hXp hXA
  have hmem : ∀ K' : Subgroup ↥K, E1.IsE 1 ⊤ ((T ⊓ K).subgroupOf K) (A.subgroupOf K) K' →
      E1.IsE 1 ⊤ T A (K'.map K.subtype) := by
    intro K' hK'
    have h1 : E1.IsE 1 K (((T ⊓ K).subgroupOf K).map K.subtype) ((A.subgroupOf K).map K.subtype)
        (K'.map K.subtype) := (E1.isE_map_subtype K).mpr hK'
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K),
      Subgroup.map_subgroupOf_eq_of_le hAK] at h1
    exact E1.eight_two hT hAT hAab le_top (hτ.trans (le_inf hT₀T hT₀K)) hSyl h1
  have hfin : (N.subgroupOf K).map K.subtype ≤
      (⨆ X ∈ {X : Subgroup G | E1.IsE 1 ⊤ T A X}, X) ⊔ Y := by
    refine (Subgroup.map_mono hLift).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYK, Subgroup.map_iSup]
    refine sup_le_sup_right (iSup_le fun K' => ?_) Y
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK' => ?_
    exact le_iSup₂_of_le (K'.map K.subtype) (hmem K' hK') le_rfl
  rw [Subgroup.map_subgroupOf_eq_of_le hNK] at hfin
  exact hfin

end CFSG.Quasithin.RonanE111
