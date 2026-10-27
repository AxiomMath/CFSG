module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem comm_of_sq_eq_one {G : Type*} [Group G] {A : Subgroup G} (hA : ∀ a ∈ A, a ^ 2 = 1)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have e : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hA x hx)
  rw [← e (a * b) (A.mul_mem ha hb), mul_inv_rev, e a ha, e b hb]

theorem not_escaping_of_local_centralizer_two {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G))
    (hloc2 : ∀ u : L ⧸ center L, orderOf u = 2 → ∀ B : Subgroup (L ⧸ center L),
      CFSG.Assembly.IsComponentOf B (centralizer ({u} : Set (L ⧸ center L))) →
        Nat.card ↥(centralizer ({u} : Set (L ⧸ center L)) ⊓
          centralizer (B : Set (L ⧸ center L))) = 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, -, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  obtain ⟨V, hVJ, hVe, hV4⟩ := hV
  obtain ⟨g, hg⟩ := hK₂.1
  obtain ⟨A, hAK, hA4, hA2⟩ :
      ∃ A : Subgroup G, A ≤ K₂ ∧ Nat.card A = 4 ∧ ∀ a ∈ A, a ^ 2 = 1 := by
    refine ⟨V.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
    · rw [hg]
      exact map_mono hVJ
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hV4]
    · rintro _ ⟨v, hv, rfl⟩
      have hv2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) v hv
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [sq] at hv2 ⊢
      calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv2, mul_one, mul_inv_cancel]
  have hKL : K₂ ≤ L := (le_blockGroup hK₂).trans hML
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA4
    norm_num at hA4
  obtain ⟨⟨t, htA⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (hA2 t htA) ht1'
  have htL : t ∈ L := hKL (hAK htA)
  obtain ⟨hπt, hcompK⟩ := hloc K₁ hK₁ K₂ hK₂ hne ⟨t, htL⟩ (hAK htA)
    (by rw [Subgroup.orderOf_mk]; exact ht2)
  have h2 := hloc2 _ hπt _ hcompK
  have hle : (A.subgroupOf L).map (QuotientGroup.mk' (center L)) ≤
      centralizer ({QuotientGroup.mk' (center L) ⟨t, htL⟩} : Set (L ⧸ center L)) ⊓
        centralizer (centerQuotientImage L K₁ : Set (L ⧸ center L)) := by
    rintro _ ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A := mem_subgroupOf.mp ha
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (comm_of_sq_eq_one hA2 haA htA)
    · rw [mem_centralizer_iff]
      intro y hy
      have hpa : QuotientGroup.mk' (center L) a ∈ centerQuotientImage L K₂ :=
        ⟨a, mem_subgroupOf.mpr (hAK haA), rfl⟩
      have hc := commutator_eq_bot_iff_le_centralizer.mp (hcomm K₁ hK₁ K₂ hK₂ hne).2 hy
      rw [mem_centralizer_iff] at hc
      exact (hc _ hpa).symm
  have hπinj : Function.Injective
      ((QuotientGroup.mk' (center L)).comp (A.subgroupOf L).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have ha2 : ((a : L) : G) ^ 2 = 1 := hA2 _ (mem_subgroupOf.mp a.2)
    have hz2 : (⟨(a : L), ha⟩ : center L) ^ 2 = 1 := Subtype.ext (Subtype.ext ha2)
    have hdvd : orderOf (⟨(a : L), ha⟩ : center L) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have hodd' : Odd (orderOf (⟨(a : L), ha⟩ : center L)) :=
      hodd.of_dvd_nat (orderOf_dvd_natCard _)
    have h1 : orderOf (⟨(a : L), ha⟩ : center L) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    rw [orderOf_eq_one_iff] at h1
    rw [mem_bot]
    have h1' : (a : L) = 1 := congrArg Subtype.val h1
    exact Subtype.ext h1'
  have hcard : Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (center L))) = 4 := by
    have hr : ((QuotientGroup.mk' (center L)).comp (A.subgroupOf L).subtype).range =
        (A.subgroupOf L).map (QuotientGroup.mk' (center L)) := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (hAK.trans hKL)).toEquiv, hA4]
  have := Subgroup.card_le_of_le hle
  rw [hcard, h2] at this
  norm_num at this

end CFSG.Sporadic.SmallOddCore
