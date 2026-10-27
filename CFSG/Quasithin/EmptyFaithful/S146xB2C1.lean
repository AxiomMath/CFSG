module

public import CFSG.Quasithin.EmptyFaithful.S146xB2Cmp
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section StarFacts1

variable {G : Type} [Group G]

theorem star_sup_eq_top {I Iz K S : Subgroup G} (hKI : K ≤ I) (hSI : S ≤ I) (hIK : I = K ⊔ S) :
    E2.star Iz I K ⊔ E2.star Iz I S = ⊤ := by
  unfold E2.star
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hKI hSI, ← hIK, Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem star_cjSub_eq_map_conj {I Iz K : Subgroup G} {t : G} (ht : t ∈ I) :
    E2.star Iz I (cjSub t K) =
      (E2.star Iz I K).map
        (MulAut.conj (QuotientGroup.mk' ((kerIn Iz I).subgroupOf I) ⟨t, ht⟩)).toMonoidHom := by
  ext y
  rw [mem_map_conj_toMonoidHom_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨t, ht⟩⁻¹ * z * ⟨t, ht⟩, ?_, ?_⟩
    · have hz' : (z : G) ∈ cjSub t K := hz
      rw [mem_cjSub] at hz'
      show t⁻¹ * (z : G) * t ∈ K
      exact hz'
    · simp [map_mul, map_inv]
  · rintro ⟨w, hw, hwy⟩
    refine ⟨⟨t, ht⟩ * w * ⟨t, ht⟩⁻¹, ?_, ?_⟩
    · have hw' : (w : G) ∈ K := hw
      show (t * (w : G) * t⁻¹ : G) ∈ cjSub t K
      rw [mem_cjSub]
      simpa [mul_assoc] using hw'
    · rw [map_mul, map_mul, hwy]
      simp [map_inv, mul_assoc]

end StarFacts1

section Case1

variable {G : Type} [Group G] [Finite G]

theorem e22_case_one_b_false {I S Iz K A : Subgroup G}
    (hSQ : IsSQTKTC I) (hMP : MinParabolic I S Iz) (hK : K ∈ cComp I) (hIK : I = K ⊔ S)
    (hker : kerIn Iz I = pCoreOf 2 I) {t : G} (htS : t ∈ S) (hKt : cjSub t K ≠ K)
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hpsl : IsPSL 2 p 1 ↥(E2.star Iz I K))
    (h8 : 8 < E2.autCard (E2.star Iz I S) (E2.star Iz I K))
    (hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G)) (hAel : IsElemAbelian 2 A)
    (h4 : 4 ≤ mIdx A (pCoreOf 2 I)) : False := by
  classical
  have hp7 : 7 ≤ p := by have := hp.two_le; omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hS := hMP.isSylow
  have hSI : S ≤ I := hS.1
  have hKI : K ≤ I := hIK ▸ le_sup_left
  have htI : t ∈ I := hSI htS
  have hAI : A ≤ I := hAS.trans hSI
  have hmem : Iz ∈ maxOver I S := by
    have h := hMP.uniqueMax
    unfold IsUniqueMaxOver at h
    rw [h]
    exact Set.mem_singleton Iz
  have hSIz : S ≤ Iz := hmem.2
  have hkerle : kerIn Iz I ≤ I := (kerIn_le_self Iz I).trans hmem.1.1.le
  set π : ↥I →* E2.StarQuot Iz I := QuotientGroup.mk' ((kerIn Iz I).subgroupOf I) with hπ
  set T : Subgroup (E2.StarQuot Iz I) := E2.star Iz I S with hTdef
  set K₁ : Subgroup (E2.StarQuot Iz I) := E2.star Iz I K with hK₁def
  set τ : E2.StarQuot Iz I := π ⟨t, htI⟩ with hτdef
  set K₂ : Subgroup (E2.StarQuot Iz I) := K₁.map (MulAut.conj τ).toMonoidHom with hK₂def
  obtain ⟨hT2, hTodd⟩ := star_isPGroup_odd (Iz := Iz) hS
  have hτT : τ ∈ T := Subgroup.mem_map.mpr ⟨⟨t, htI⟩, htS, rfl⟩
  have hN3 : ¬ 3 ∣ Nat.card ((kerIn Iz I).subgroupOf I) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv, hker]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (pCoreOf_isPGroup 2 I)
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hSQ3 : CFSG.Assembly.pRank 3 (⊤ : Subgroup (E2.StarQuot Iz I)) ≤ 2 := by
    have h1 := CFSG.GroupTheory.PRankCoprimeQuotient.assembly_pRank_quotient_eq_of_not_dvd
      Nat.prime_three ((kerIn Iz I).subgroupOf I) hN3
    have h2 := hSQ.2 3 Nat.prime_three (by norm_num)
    exact h1 ▸ h2
  have hK₁sub : K₁.IsSubnormal :=
    Quasithin.A3.subnormal_top_iff.mp (Quasithin.A3.subnormal_top_map (QuotientGroup.mk'_surjective _)
      (subnormal_of_mem_cComp (subgroupOf_mem_cComp hK)))
  have hne : K₁ ≠ K₂ := by
    intro h
    have hsolv : Group.IsSolvable ↥(kerIn Iz I) := by
      rw [hker]
      have := (pCoreOf_isPGroup 2 I).isNilpotent
      infer_instance
    have hbij := cComp_quotient_bijOn_of_le hkerle inferInstance hsolv
    have hKt' : cjSub t K ∈ cComp I := map_conj_mem_cComp hK htI
    have heq : E2.star Iz I K = E2.star Iz I (cjSub t K) := by
      rw [star_cjSub_eq_map_conj htI]
      exact h
    exact hKt (hbij.injOn hK hKt' heq).symm
  have horb : ∀ s : E2.StarQuot Iz I, K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj s).toMonoidHom = K₂ := fun s =>
    map_conj_eq_or_of_isPSL hp hp7 hSQ3 hpsl hK₁sub rfl hne
  have hT₀N := inf_normalizer_le_normalizer_of_conj_eq_or (T := T) (K₁ := K₁) (K₂ := K₂) rfl hne horb
  have hidx := relIndex_inf_normalizer_le_two_of_conj_eq_or (T := T) hτT rfl horb
  have hnorm := normalizer_sup_of_conj_eq_or (K₁ := K₁) (K₂ := K₂) rfl hne horb
  have hX : K₁ ⊔ T = ⊤ := star_sup_eq_top hKI hSI hIK
  have hTN : T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (E2.StarQuot Iz I)) : Set _) :=
    fun s _ => hnorm s
  have hX2 : ∀ x : E2.StarQuot Iz I, ∃ k : ℕ, x ^ 2 ^ k ∈ K₁ ⊔ K₂ := by
    intro x
    have hx : x ∈ (K₁ ⊔ K₂) ⊔ T := by
      have : x ∈ K₁ ⊔ T := hX ▸ Subgroup.mem_top x
      exact (sup_le_sup_right le_sup_left T) this
    exact exists_pow_mem_of_mem_sup_two hT2 hTN hx
  have hp2' : p ≠ 2 := hp2
  have hpsl₂ : IsPSL 2 p 1 ↥K₂ := isPSL_two_of_mulEquiv (mapConjEquiv K₁ τ).symm hpsl
  have hc₁ : CFSG.IsComponent K₁ := isComponent_of_isPSL_two hp hp2 hpsl hK₁sub
  have hc₂ : CFSG.IsComponent K₂ :=
    isComponent_of_isPSL_two hp hp2 hpsl₂ (isSubnormal_map_conj hK₁sub τ)
  have hcomm := mul_comm_of_isComponent_ne hc₁ hc₂ hne
  have hC : ∀ x ∈ T, x ∈ Subgroup.centralizer (K₁ : Set (E2.StarQuot Iz I)) →
      x ∈ Subgroup.centralizer (K₂ : Set (E2.StarQuot Iz I)) → x = 1 := by
    intro x _ hx₁ hx₂
    exact eq_one_of_centralizes_sup hcomm
      (fun y hy hc => eq_one_of_forall_comm_of_isPSL hp hp2 hpsl hy hc)
      (fun y hy hc => eq_one_of_forall_comm_of_isPSL hp hp2 hpsl₂ hy hc) hnorm hX2 hT2 hTodd
      (Subgroup.map_mono (Subgroup.comap_mono hSIz) : E2.star Iz I S ≤ E2.star Iz I Iz)
      star_coreFree hx₁ hx₂
  have h16 : 16 ≤ ((T ⊓ Subgroup.normalizer (K₁ : Set (E2.StarQuot Iz I))) ⊓
      Subgroup.centralizer (K₁ : Set (E2.StarQuot Iz I))).relIndex
        (T ⊓ Subgroup.normalizer (K₁ : Set (E2.StarQuot Iz I))) := by
    unfold E2.autCard at h8
    obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup (hT2.to_le inf_le_left)
      ((T ⊓ Subgroup.normalizer (K₁ : Set (E2.StarQuot Iz I))) ⊓
        Subgroup.centralizer (K₁ : Set (E2.StarQuot Iz I)))
    rw [hn] at h8 ⊢
    have h4n : 4 ≤ n := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4n
  obtain ⟨F, hFfield, hFfin, hF, ⟨e₁⟩⟩ := exists_psl2_model hpsl
  let e₂ : ↥K₂ ≃* CFSG.GorensteinWalter.PSL2 F := (mapConjEquiv K₁ τ).symm.trans e₁
  set B : Subgroup (E2.StarQuot Iz I) := E2.star Iz I A with hBdef
  have hBT : B ≤ T := Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAS)
  have hBn : ∀ s ∈ T, ∀ b ∈ B, s * b * s⁻¹ ∈ B := by
    intro s hs b hb
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    refine Subgroup.mem_map.mpr ⟨s₀ * b₀ * s₀⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hs₀' : (s₀ : G) ∈ S := hs₀
    have hb₀' : (b₀ : G) ∈ A := hb₀
    show ((s₀ : G) * (b₀ : G) * (s₀ : G)⁻¹ : G) ∈ A
    exact (Subgroup.mem_normalizer_iff.mp (hSA hs₀') (b₀ : G)).mp hb₀'
  have hBel : IsElemAbelian 2 B := isElemAbelian_map_two π (isElemAbelian_subgroupOf_two hAel)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := hBel.2
  have hAJ : ∀ x ∈ A, x ∈ kerIn Iz I → x ∈ pCoreOf 2 I := fun x _ hx => hker ▸ hx
  have hBcard : 16 ≤ Nat.card B :=
    (sixteen_le_relIndex_of_mIdx (isPGroup_of_isElemAbelian hAel) h4).trans
      (relIndex_le_card_star hAI hAJ)
  have h8' : Nat.card B ≤ 8 :=
    card_le_eight_of_two_psl2_factors hp7 hF e₁ e₂ hT2 hτT rfl hT₀N hidx hC h16 hBT hBn hB2
  omega

end Case1


end CFSG.Quasithin
