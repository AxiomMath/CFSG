module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33FFS1
public import CFSG.Quasithin.H13.A6S13816p
public import CFSG.Quasithin.Background.C126RFCases

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin S126 Equiv CFSG.Quasithin.H13.A6.FFTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pCore_HStar_eq_bot (H : Subgroup G) : CFSG.pCore 2 (S126.HStar H) = ⊥ :=
  B6.pCore_quotient_pCore

section Sum

theorem sum_star_K {T L H K : Subgroup G}
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (h2 : Case2 T L H K)
    {t : G} (ht : t ∈ T) (hKc : K ∈ cComp H) (hTH : T ≤ H)
    (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G))
    (hK0H : conjClosure K T ≤ H) (hSQ : SQTKGroup ↥H)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : ↥H →* MulAut V) (hρ : CFSG.pCore 2 ↥H ≤ ρ.ker)
    (hnt : ∃ k ∈ conjClosure K T, ∃ hk : k ∈ H, ρ ⟨k, hk⟩ ≠ 1)
    (hFF : IsFFModule ρ.range) :
    commV ((S126.star H K).map (QuotientGroup.lift (CFSG.pCore 2 ↥H) ρ hρ)) ≤
        fixV ((S126.star H (conjSub t⁻¹ K)).map (QuotientGroup.lift (CFSG.pCore 2 ↥H) ρ hρ)) ∧
      ¬ IsStrongFFModule ρ.range := by
  classical
  set ρs : S126.HStar H →* MulAut V := QuotientGroup.lift (CFSG.pCore 2 ↥H) ρ hρ with hρs
  have hrange : ρs.range = ρ.range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨y, by rw [hρs, QuotientGroup.lift_mk]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨QuotientGroup.mk y, by rw [hρs, QuotientGroup.lift_mk]⟩
  have hS : SQTKGroup (S126.HStar H) := sqtkGroup_HStar hA21 hSQ h2 hK0
  have hK2 : (S126.star H K).map (MulAut.conj (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ :
      S126.HStar H)).toMonoidHom = S126.star H (conjSub t⁻¹ K) :=
    (star_conjSub_eq_map ht hTH).symm
  have hsup : S126.star H K ⊔ S126.star H (conjSub t⁻¹ K) = S126.star H (conjClosure K T) :=
    sup_star_K_K2 h2 ht hKc hTH htK
  have hcomm : ∀ x ∈ S126.star H K, ∀ y ∈ S126.star H (conjSub t⁻¹ K), x * y = y * x :=
    commute_star_K_K2 h2 ht hKc hTH htK
  have hKn : (S126.star H K ⊔ (S126.star H K).map (MulAut.conj
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom).Normal := by
    rw [hK2, hsup]
    exact normal_star_K0 hK0
  have hQ : CFSG.pCore 2 (S126.HStar H) ≤ ρs.ker := by
    rw [pCore_HStar_eq_bot H]
    exact bot_le
  have hcommU : ⁅S126.star H K, (S126.star H K).map (MulAut.conj
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom⁆ ≤
        CFSG.pCore 2 (S126.HStar H) := by
    rw [pCore_HStar_eq_bot H, hK2]
    refine (Subgroup.commutator_le (H₁ := S126.star H K)
      (H₂ := S126.star H (conjSub t⁻¹ K)) (H₃ := ⊥)).mpr ?_
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_def, hcomm x hx y hy]
    group
  have h2' : ∀ y : S126.HStar H, ∃ e : ℕ, y ^ 2 ^ e ∈ S126.star H K ⊔ (S126.star H K).map
      (MulAut.conj (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom := by
    intro y
    refine ⟨3, ?_⟩
    rw [hK2, hsup, show (2 : ℕ) ^ 3 = 8 from rfl]
    exact pow_eight_mem_star_K0 h2 hK0 y
  have hperm : ∀ x : S126.HStar H, x ∈ Subgroup.normalizer (S126.star H K : Set (S126.HStar H)) ∨
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)⁻¹ * x ∈
        Subgroup.normalizer (S126.star H K : Set (S126.HStar H)) :=
    fun x => perm_star_K h2 ht hKc hTH htK hK0 x
  have hnt' : ¬ S126.star H K ⊔ (S126.star H K).map (MulAut.conj
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom ≤ ρs.ker := by
    intro hle
    obtain ⟨k, hk, hk', hne⟩ := hnt
    apply hne
    have hmem : (QuotientGroup.mk ⟨k, hk'⟩ : S126.HStar H) ∈ S126.star H (conjClosure K T) :=
      ⟨⟨k, hk'⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    have hmem2 : (QuotientGroup.mk ⟨k, hk'⟩ : S126.HStar H) ∈ S126.star H K ⊔
        (S126.star H K).map (MulAut.conj
          (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom := by
      rw [hK2, hsup]
      exact hmem
    have := MonoidHom.mem_ker.1 (hle hmem2)
    simpa [hρs, QuotientGroup.lift_mk] using this
  have hFF' : IsFFModule ρs.range := by rw [hrange]; exact hFF
  have hinj : Function.Injective (ρs.comp (S126.star H K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI := isSimpleGroup_star_K h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((ρs.comp (S126.star H K).subtype).ker) with hbot | htop
    · exact hbot
    · exfalso
      have hK1 : S126.star H K ≤ ρs.ker := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥(S126.star H K)) ∈ (ρs.comp (S126.star H K).subtype).ker :=
          htop ▸ Subgroup.mem_top _
        exact hx'
      have hK2le : (S126.star H K).map (MulAut.conj
          (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom ≤ ρs.ker := by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : ρs x = 1 := MonoidHom.mem_ker.1 (hK1 hx)
        rw [MonoidHom.mem_ker]
        simp [MulAut.conj_apply, map_mul, map_inv, hx1]
      exact hnt' (sup_le hK1 hK2le)
  have hK : CFSG.Quasithin.IsPSL 2 2 2 ↥((S126.star H K).map ρs) := by
    have hrng : (ρs.comp (S126.star H K).subtype).range = (S126.star H K).map ρs := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    obtain ⟨e5⟩ : Nonempty (↥(S126.star H K) ≃* alternatingGroup (Fin 5)) := by
      obtain ⟨-, e, -, -, -, -⟩ := h2
      exact e
    exact CFSG.Quasithin.C126.isPSL_two_two_two_of_alternating_five _
      ⟨(MulEquiv.subgroupCongr hrng.symm).trans
        ((MonoidHom.ofInjective hinj).symm.trans e5)⟩
  obtain ⟨hfix, hns⟩ := twoSum_of_action hA21 h56 hS hV ρs (S126.star H K)
    (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)
    (isQuasisimple_star_K_quot h2) hKn hcommU hQ h2' hperm hnt' hFF' hK
  refine ⟨?_, ?_⟩
  · rw [hK2] at hfix
    exact hfix
  · rwa [hrange] at hns

theorem star_K_comp_injective {T L H K : Subgroup G} {t : G} (ht : t ∈ T) (hTH : T ≤ H)
    (h2 : Case2 T L H K) {V : Type} [CommGroup V] (ρs : S126.HStar H →* MulAut V)
    (hnt : ¬ S126.star H K ⊔ (S126.star H K).map (MulAut.conj
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom ≤ ρs.ker) :
    Function.Injective (ρs.comp (S126.star H K).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  haveI := isSimpleGroup_star_K h2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((ρs.comp (S126.star H K).subtype).ker) with hbot | htop
  · exact hbot
  · exfalso
    have hK1 : S126.star H K ≤ ρs.ker := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥(S126.star H K)) ∈ (ρs.comp (S126.star H K).subtype).ker :=
        htop ▸ Subgroup.mem_top _
      exact hx'
    have hK2le : (S126.star H K).map (MulAut.conj
        (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom ≤ ρs.ker := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : ρs x = 1 := MonoidHom.mem_ker.1 (hK1 hx)
      rw [MonoidHom.mem_ker]
      simp [MulAut.conj_apply, map_mul, map_inv, hx1]
    exact hnt (sup_le hK1 hK2le)

theorem nontriv_star {T L H K : Subgroup G} {t : G} (h2 : Case2 T L H K) (ht : t ∈ T)
    (hKc : K ∈ cComp H) (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G))
    {V : Type} [CommGroup V] (ρs : S126.HStar H →* MulAut V)
    (hnt : ∃ k ∈ conjClosure K T, ∃ hk : k ∈ H, ρs (QuotientGroup.mk ⟨k, hk⟩) ≠ 1) :
    ¬ S126.star H K ⊔ (S126.star H K).map (MulAut.conj
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom ≤ ρs.ker := by
  intro hle
  obtain ⟨k, hk, hk', hne⟩ := hnt
  apply hne
  have hsup : S126.star H K ⊔ (S126.star H K).map (MulAut.conj
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).toMonoidHom =
      S126.star H (conjClosure K T) := by
    rw [← star_conjSub_eq_map ht hTH]
    exact sup_star_K_K2 h2 ht hKc hTH htK
  have hmem : (QuotientGroup.mk ⟨k, hk'⟩ : S126.HStar H) ∈ S126.star H (conjClosure K T) :=
    ⟨⟨k, hk'⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  rw [← hsup] at hmem
  exact MonoidHom.mem_ker.1 (hle hmem)

end Sum

end CFSG.Quasithin.H13.L1233
