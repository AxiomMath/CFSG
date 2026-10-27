module

public import CFSG.Quasithin.EmptyFaithful.S153E51B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Generic

variable {G : Type*} [Group G]

omit [Group G] in
theorem commutator_le_of_le_normalizer' {G : Type*} [Group G] {Y U : Subgroup G}
    (hU : U ≤ Subgroup.normalizer (Y : Set G)) : ⁅Y, U⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hU hb) a⁻¹).mp (Y.inv_mem ha)
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact Y.mul_mem ha h1

theorem commutator_conj_mem {Y U : Subgroup G} {y' : G} (hy' : y' ∈ Y) {n : G}
    (hn : n ∈ ⁅Y, U⁆) : y' * n * y'⁻¹ ∈ ⁅Y, U⁆ := by
  have hle : ⁅Y, U⁆ ≤ (⁅Y, U⁆).comap (MulAut.conj y').toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj y').toMonoidHom ⁅a, b⁆ = ⁅y' * a, b⁆ * ⁅y', b⁆⁻¹ := by
      simp [commutatorElement_def, MulAut.conj_apply]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (Y.mul_mem hy' ha) hb)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy' hb))
  have := hle hn
  rw [Subgroup.mem_comap] at this
  simpa [MulAut.conj_apply] using this

theorem le_normalizer_commutator {Y U : Subgroup G} :
    Y ≤ Subgroup.normalizer ((⁅Y, U⁆ : Subgroup G) : Set G) := by
  intro y' hy'
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨commutator_conj_mem hy', fun hn => ?_⟩
  have := commutator_conj_mem (Y.inv_mem hy') hn
  simpa [mul_assoc] using this

theorem mem_of_sq_mem {Y N P : Subgroup G} (hNY : N ≤ Y) (hn : Y ≤ Subgroup.normalizer (N : Set G))
    (hP : IsPGroup 2 P) (hPY : P ≤ Y) {y c d : G} (hy : y ∈ Y) (hodd : Odd (orderOf y)) (hc : c ∈ N)
    (hd : d ∈ P) (hyy : y * y = c * d) : y ∈ N := by
  have : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hn
  let f : ↥Y →* ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk' (N.subgroupOf Y)
  let yy : ↥Y := ⟨y, hy⟩
  let dd : ↥Y := ⟨d, hPY hd⟩
  have hfc : f ⟨c, hNY hc⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hc
  have hsq : f yy * f yy = f dd := by
    have : yy * yy = ⟨c, hNY hc⟩ * dd := Subtype.ext hyy
    rw [← map_mul, this, map_mul, hfc, one_mul]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨d, hd⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdk : d ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one d
  have hddk : dd ^ (2 ^ k) = 1 := Subtype.ext (by simpa [dd] using hdk)
  have hfdd : (f dd) ^ (2 ^ k) = 1 := by rw [← map_pow, hddk, map_one]
  have hpow : (f yy) ^ (2 * 2 ^ k) = 1 := by
    rw [pow_mul, pow_two, hsq]
    exact hfdd
  have hdvd1 : orderOf (f yy) ∣ 2 * 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : orderOf (f yy) ∣ orderOf y := by
    have := orderOf_map_dvd f yy
    rwa [show orderOf yy = orderOf y from Subgroup.orderOf_mk y hy] at this
  have hoddf : Odd (orderOf (f yy)) := Odd.of_dvd_nat hodd hdvd2
  have hcop : Nat.Coprime (orderOf (f yy)) (2 * 2 ^ k) :=
    Nat.Coprime.mul_right hoddf.coprime_two_right (Nat.Coprime.pow_right k hoddf.coprime_two_right)
  have h1 : orderOf (f yy) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd1
  have hf1 : f yy = 1 := orderOf_eq_one_iff.mp h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hf1
  exact Subgroup.mem_subgroupOf.mp hf1

end Generic

section Three

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem three (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc) :
    Y153 Mc M = ⁅Y153 Mc M, UH153 T M V₁ Mc⁆ := by
  have hV := cx.c.hyp.elemAbelian
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hUY : UH153 T M V₁ Mc ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
    ((U_le_T cx).trans (T_le_M cx)).trans (le_normalizer_Y153 Mc M)
  have hNY : ⁅Y153 Mc M, UH153 T M V₁ Mc⁆ ≤ Y153 Mc M := commutator_le_of_le_normalizer' hUY
  refine le_antisymm ?_ hNY
  have hYO : oTwoUpper (Y153 Mc M) = Y153 Mc M := A4.oTwoUpper_oTwoUpper _
  have key : oTwoUpper (Y153 Mc M) ≤ ⁅Y153 Mc M, UH153 T M V₁ Mc⁆ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyY, hodd⟩
    obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
    have hT := cx.c.hyp.isSylowTwoOf_autI
    have hr : s₁ * s₂ ∈ autI hV (UH153 T M V₁ Mc) := mul_mem_autI_U cx h1 hS hF
    obtain ⟨u₀, hu₀U, hu₀⟩ := (mem_autI hV).1 hr
    have hyM : y ∈ M := hYM hyY
    have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := cx.c.hyp.le_normalizer hyM
    have hybM : convI hV ⟨y, hyN⟩ ∈ autI hV M := convI_mem_autI hV hyM hyN
    have hybodd : Odd (orderOf (convI hV ⟨y, hyN⟩)) := by
      refine Odd.of_dvd_nat hodd ?_
      have := orderOf_map_dvd (convI hV) (⟨y, hyN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G)))
      rwa [Subgroup.orderOf_mk] at this
    have hinv := mul_inv_of_odd hS hT hF hybM hybodd
    have hcomm : ⁅convI hV ⟨y, hyN⟩, s₁ * s₂⁆ = convI hV ⟨y, hyN⟩ * convI hV ⟨y, hyN⟩ := by
      have h2 : (s₁ * s₂) * (convI hV ⟨y, hyN⟩)⁻¹ * (s₁ * s₂)⁻¹ = convI hV ⟨y, hyN⟩ := by
        have := congrArg (fun a => a⁻¹) hinv
        simpa [mul_assoc] using this
      calc ⁅convI hV ⟨y, hyN⟩, s₁ * s₂⁆
          = convI hV ⟨y, hyN⟩ * ((s₁ * s₂) * (convI hV ⟨y, hyN⟩)⁻¹ * (s₁ * s₂)⁻¹) := by
            simp [commutatorElement_def, mul_assoc]
        _ = convI hV ⟨y, hyN⟩ * convI hV ⟨y, hyN⟩ := by rw [h2]
    set D : Subgroup.normalizer (VZ T M : Set G) :=
      ⁅(⟨y, hyN⟩ : Subgroup.normalizer (VZ T M : Set G)), u₀⁆⁻¹ * ⟨y, hyN⟩ * ⟨y, hyN⟩ with hD
    have hD1 : convI hV D = 1 := by
      rw [hD, map_mul, map_mul, map_inv, map_commutatorElement, hu₀, hcomm]
      group
    have hDC : (D : G) ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV D).1 hD1
    have hDval : (D : G) = (y * (u₀ : G) * y⁻¹ * (u₀ : G)⁻¹)⁻¹ * y * y := by
      rw [hD]
      simp [commutatorElement_def]
    have hcN : y * (u₀ : G) * y⁻¹ * (u₀ : G)⁻¹ ∈ ⁅Y153 Mc M, UH153 T M V₁ Mc⁆ :=
      Subgroup.commutator_mem_commutator hyY hu₀U
    have hDY : (D : G) ∈ Y153 Mc M := by
      rw [hDval]
      exact (Y153 Mc M).mul_mem ((Y153 Mc M).mul_mem ((Y153 Mc M).inv_mem (hNY hcN)) hyY) hyY
    have hDP : (D : G) ∈ pCoreOf 2 (Y153 Mc M) := by
      rw [cx.r49.case_one.1]
      exact ⟨hDY, hDC⟩
    have hyy : y * y = (y * (u₀ : G) * y⁻¹ * (u₀ : G)⁻¹) * (D : G) := by
      rw [hDval]
      group
    exact mem_of_sq_mem hNY le_normalizer_commutator (pCoreOf_isPGroup 2 (Y153 Mc M))
      (pCoreOf_le 2 (Y153 Mc M)) hyY hodd hcN hDP hyy
  calc Y153 Mc M = oTwoUpper (Y153 Mc M) := hYO.symm
    _ ≤ ⁅Y153 Mc M, UH153 T M V₁ Mc⁆ := key

theorem lemma_15_3_51 (cx : Ctx15350 T Mc M V₁ V₂ t) (hn : NonabelianVH153 T M Mc) :
    Concl15351 cx :=
  have h1 := not_le_pCoreOf cx hn
  { one := h1
    two := lemma_15_3_51_two cx h1
    three := three cx h1
    four_Q := four_Q cx
    four_U := four_U cx }

end Three

end S153E

end CFSG.Quasithin
