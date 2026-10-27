module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.EmptyFaithful.S153EDefs3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S153E

section Final

theorem commutator_mem_of_index_two {K : Type*} [Group K] {N : Subgroup K} (h : N.index = 2)
    (a b : K) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  simp only [Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff]
  tauto

theorem commutator_top_eq_top_of_simple {G : Type*} [Group G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  have hn : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).Normal := inferInstance
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hG _ hn with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact h

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem mem_centralizer_of_mem_Y_of_mem_T (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G}
    (hyY : y ∈ Y153 Mc M) (hyT : y ∈ T) : y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hcase := cx.r49.case_one
  have hf : ∀ f : Multiplicative (Fin 2 → ZMod 3), f ^ 3 = 1 := by
    intro f
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize Multiplicative.toAdd f i = a
    revert a
    decide
  have hq3 : ∀ q : OTwoQuot (Y153 Mc M), q ^ 3 = 1 := by
    obtain ⟨e⟩ := hcase.2
    intro q
    apply e.injective
    rw [map_pow, map_one]
    exact hf _
  obtain ⟨k, hk⟩ := cx.c.hyp.qtfe.sylow.1 ⟨y, hyT⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set z : ↥(Y153 Mc M) := ⟨y, hyY⟩ with hzdef
  have hzk : z ^ 2 ^ k = 1 := Subtype.ext (by simpa [hzdef] using hk')
  set q : OTwoQuot (Y153 Mc M) := QuotientGroup.mk z with hqdef
  have hq2 : q ^ 2 ^ k = 1 := by
    rw [hqdef, ← QuotientGroup.mk_pow, hzk]
    rfl
  have hq1 : q = 1 := by
    have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hq2
    have h2 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one (hq3 q)
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h3 : orderOf q ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
    rw [hc] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hz : z ∈ CFSG.Open.pCore 2 ↥(Y153 Mc M) := (QuotientGroup.eq_one_iff z).mp hq1
  have hyO : y ∈ pCoreOf 2 (Y153 Mc M) := ⟨z, hz, rfl⟩
  rw [hcase.1] at hyO
  exact hyO.2

theorem TK_le_UCT (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hK : IsSylowTwoOf (T ⊓ oTwoUpper Mc) (Y153 Mc M ⊔ UH153 T M V₁ Mc)) :
    T ⊓ oTwoUpper Mc ≤ UCT153 T M V₁ Mc := by
  intro x hx
  have hUT : UH153 T M V₁ Mc ≤ T :=
    (cx.hF.conjClosure_Vp_le_pCoreOf).trans (pCoreOf_two_le_of_isSylowTwoOf cx.hF.sylow_H)
  have hUY : UH153 T M V₁ Mc ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
    hUT.trans (cx.c.hyp.T_le.trans (le_normalizer_Y153 Mc M))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (UH153 T M V₁ Mc) (Y153 Mc M) hUY
  have hx' : x ∈ (UH153 T M V₁ Mc ⊔ Y153 Mc M : Subgroup G) := by
    rw [sup_comm]; exact hK.1 hx
  have hx'' : x ∈ (UH153 T M V₁ Mc : Set G) * (Y153 Mc M : Set G) := by
    rw [← hmul]; exact hx'
  obtain ⟨u, hu, y, hy, hxy⟩ := hx''
  have hxy' : u * y = x := hxy
  have hyT : y ∈ T := by
    have : y = u⁻¹ * x := by rw [← hxy']; group
    rw [this]
    exact T.mul_mem (T.inv_mem (hUT hu)) hx.1
  have hyC := mem_centralizer_of_mem_Y_of_mem_T cx hy hyT
  rw [← hxy']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_right (⟨hyT, hyC⟩ : y ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G)))

theorem false_of_closing (cx : Ctx15350 T Mc M V₁ V₂ t) (h59 : Concl15359 cx) {t₂ z v : G}
    (ht₂T : t₂ ∈ T) (hord : orderOf t₂ = 2) (hUCT : t₂ ∉ UCT153 T M V₁ Mc)
    (hz : ∀ g : G, g * z * g⁻¹ ≠ t₂) (hv : ∀ g : G, g * v * g⁻¹ ≠ t₂)
    (hK : ∀ x ∈ oTwoUpper Mc, orderOf x = 2 →
      (∃ g : G, g * z * g⁻¹ = x) ∨ (∃ g : G, g * v * g⁻¹ = x)) : False := by
  set TK : Subgroup G := T ⊓ oTwoUpper Mc with hTK
  have hnotK : t₂ ∉ TK := fun h => hUCT (TK_le_UCT cx h59.two h)
  have hN : (TK.subgroupOf T).index = 2 := h59.three
  have hTKT : TK ≤ T := inf_le_left
  have hindex : Nat.Coprime 2 (T.relIndex ⊤) := by
    rw [Subgroup.relIndex_top_right]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr cx.c.hyp.qtfe.sylow.2
  have hKn : ∀ h ∈ T, ∀ k ∈ TK, h * k * h⁻¹ ∈ TK := by
    have hnorm : (TK.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hN
    intro h hh k hk
    have := hnorm.conj_mem ⟨k, hTKT hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.mp this
  have habel : ⁅T, T⁆ ≤ TK := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have := commutator_mem_of_index_two hN ⟨a, ha⟩ ⟨b, hb⟩
    exact Subgroup.mem_subgroupOf.mp this
  have htrans : t₂ ∉ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
    refine generalized_thompson_transfer_two_subgroup (X := ⊤) (H := T) (K := TK) le_top hindex
      hTKT hKn habel ht₂T hnotK hord ?_
    intro a _ ha
    by_cases hw : a⁻¹ * t₂ * a ∈ TK
    · exfalso
      have hwo : orderOf (a⁻¹ * t₂ * a) = 2 := by
        rw [← hord]
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective t₂
      rcases hK _ hw.2 hwo with ⟨g, hg⟩ | ⟨g, hg⟩
      · refine hz (a * g) ?_
        have : a * g * z * (a * g)⁻¹ = a * (g * z * g⁻¹) * a⁻¹ := by group
        rw [this, hg]
        group
      · refine hv (a * g) ?_
        have : a * g * v * (a * g)⁻¹ = a * (g * v * g⁻¹) * a⁻¹ := by group
        rw [this, hg]
        group
    · have key := Subgroup.mul_mem_iff_of_index_two hN (a := (⟨t₂, ht₂T⟩ : ↥T)⁻¹)
        (b := ⟨a⁻¹ * t₂ * a, ha⟩)
      have h1 : ((⟨t₂, ht₂T⟩ : ↥T)⁻¹ * ⟨a⁻¹ * t₂ * a, ha⟩) ∈ TK.subgroupOf T := by
        rw [key]
        constructor
        · intro h
          exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h)) hnotK
        · intro h
          exact absurd (Subgroup.mem_subgroupOf.mp h) hw
      exact Subgroup.mem_subgroupOf.mp h1
  have hperf := commutator_top_eq_top_of_simple cx.c.hyp.qtfe.simple cx.c.hyp.qtfe.nonabelian
  rw [hperf] at htrans
  exact htrans (Subgroup.mem_top t₂)

end Final

end S153E

end CFSG.Quasithin
