module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZC
public import CFSG.Quasithin.Vol2.Ch10SecB6Pair

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped MatrixGroups

namespace E9

theorem eq_one_of_mem_zpowers {Q : Type*} [Group Q] {a x : Q} (ha : orderOf a = 3)
    (hx : x ∈ Subgroup.zpowers a) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 := ha ▸ orderOf_dvd_of_mem_zpowers hx
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h3 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by norm_num)
  have h4 := Nat.dvd_gcd h1 h2
  rw [h3, Nat.dvd_one] at h4
  exact orderOf_eq_one_iff.mp h4

theorem exists_orderOf_three {G : Type} [Group G] [Finite G] {H X : Subgroup G} (hXH : X ≤ H)
    (hs : IsSimpleGroup (ModO2 X)) (hnab : ∃ a b : ModO2 X, a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card (ModO2 X)) :
    ∃ a ∈ modO2Image H X, orderOf a = 3 ∧ ∀ x ∈ Subgroup.zpowers a,
      (∀ y ∈ modO2Image H X, x * y = y * x) → x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f⟩ := nonempty_modO2_modO2Image hXH
  have h3' : 3 ∣ Nat.card (modO2Image H X) :=
    ((Nat.card_congr f.toEquiv).symm ▸ h3).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(modO2Image H X)) 3 h3'
  refine ⟨a, a.2, by rw [Subgroup.orderOf_coe, ha], fun x hx hc => ?_⟩
  have hxX : x ∈ modO2Image H X := Subgroup.zpowers_le.mpr a.2 hx
  obtain ⟨k, hk⟩ := isPGroup_of_mem_center hXH hs hnab hxX hc
  exact eq_one_of_mem_zpowers (by rw [Subgroup.orderOf_coe, ha]) hx hk

end E9

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem false_of_components (hList : Vol2Native.A312ListFactsCat)
    (hSL2 : A312SL2Fact) (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hF1 : Fact10_2_6Pair)
    (hKG : FactA312L32RankOne) (hyp : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) {t : G}
    (ht : t ∈ T) {v : G} (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hS : IsSylowTwoOf (T1 T L) (Subgroup.centralizer ({v} : Set G)))
    (hLt : CFSG.conjugate L t ≤ Subgroup.centralizer ({v} : Set G)) {K₁ K₂ : Subgroup G}
    (hfam₁ : K₁ ∈ lFamily (T1 T L)) (hfam₂ : K₂ ∈ lFamily (T1 T L))
    (hcomm : ⁅K₁, K₂⁆ ≤ pCoreOf 2 K₁ ⊓ pCoreOf 2 K₂)
    (hN₁ : T1 T L ≤ Subgroup.normalizer (K₁ : Set G))
    (hN₂ : T1 T L ≤ Subgroup.normalizer (K₂ : Set G))
    (hK₁H : K₁ ≤ Subgroup.centralizer ({v} : Set G))
    (hK₂H : K₂ ≤ Subgroup.centralizer ({v} : Set G)) {p : ℕ} [Fact p.Prime]
    (h24 : p % 24 = 11 ∨ p % 24 = 13) (e₁ : ModO2 K₁ ≃* PSL(2, ZMod p))
    (e₂ : ModO2 K₂ ≃* PSL(2, ZMod p)) : False := by
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  set H := Subgroup.centralizer ({v} : Set G) with hHdef
  have hH2 : pCoreOf 2 H ≠ ⊥ := by
    have hv : IsPGroup 2 (Subgroup.zpowers v) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, pow_one])
    intro h
    have h1 := mem_pCoreOf_centralizer hv
    rw [← hHdef, h, Subgroup.mem_bot] at h1
    exact hv1 h1
  obtain ⟨hc₂, -, -, ⟨eLt⟩⟩ := li_data h37 h38 hyp ht (X := CFSG.conjugate L t) (Or.inr rfl)
  have hfamLt : CFSG.conjugate L t ∈ lFamily (T1 T L) :=
    cComp_subset_lFamily (inf_le_left.trans (le_fsuM T L)) hc₂
  have eX : ModO2 (CFSG.conjugate L t) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    eLt.trans h3.1.some
  have hsL : IsSimpleGroup (ModO2 L) := SecA.isSimpleGroup_of_not_normal h37 h38
    hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_modO2 hyp
  obtain ⟨I₀, hI₀, hLtI₀⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hH2 hS hLt hfamLt
  obtain ⟨I₁, hI₁, hKI₁⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hH2 hS hK₁H hfam₁
  obtain ⟨I₂, hI₂, hKI₂⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hH2 hS hK₂H hfam₂
  obtain ⟨f₁⟩ := nonempty_modO2_modO2Image hK₁H
  obtain ⟨f₂⟩ := nonempty_modO2_modO2Image hK₂H
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH2
  have h12 : I₁ ≠ I₂ := by
    intro h
    have hc : ⁅modO2Image H K₁, modO2Image H K₂⁆ ≤
        pCoreOf 2 (modO2Image H K₁) ⊓ pCoreOf 2 (modO2Image H K₂) := by
      refine (commutator_modO2Image_le hcomm).trans ?_
      exact le_inf ((modO2Image_mono' inf_le_left).trans modO2Image_pCoreOf_le)
        ((modO2Image_mono' inf_le_right).trans modO2Image_pCoreOf_le)
    exact hF1 _ hQ (modO2Image H (T1 T L)) (modO2Image H I₁) (modO2Image H K₁)
      (modO2Image H K₂) (isSylowTwoOf_modO2Image hS) (modO2Image_mem_cComp hI₁)
      (modO2Image_mem_lFamily hS hK₁H hfam₁) (modO2Image_mem_lFamily hS hK₂H hfam₂)
      (modO2Image_le_normalizer' hN₁) (modO2Image_le_normalizer' hN₂)
      (modO2Image_mono' hKI₁) (modO2Image_mono' (h ▸ hKI₂))
      hc ⟨(f₁.trans e₁).trans (f₂.trans e₂).symm⟩
  have := E9.isSimpleGroup_psl2 h24 (p := p)
  have h3K : ∀ {K : Subgroup G}, (ModO2 K ≃* PSL(2, ZMod p)) → 3 ∣ Nat.card (ModO2 K) :=
    fun e => (Dvd.intro (4 * p) (by ring)).trans
      ((Nat.card_congr e.toEquiv).symm ▸ E9.twelve_mul_dvd_card h24)
  have h0 : I₀ = I₁ ∨ I₀ = I₂ := by
    by_contra hcon
    rw [not_or] at hcon
    have hcomm' : ∀ {A B J J' : Subgroup G}, J ∈ cComp H → J' ∈ cComp H → J ≠ J' → A ≤ J →
        B ≤ J' → ∀ x ∈ modO2Image H A, ∀ y ∈ modO2Image H B, x * y = y * x :=
      fun hJ hJ' hne hA hB => modO2Image_commute' ((Subgroup.commutator_mono hA hB).trans
        (commutator_le_pCoreOf_H hK h37 hH2 hJ hJ' hne))
    obtain ⟨a₁, ha₁, ho₁, hz₁⟩ := E9.exists_orderOf_three hK₁H e₁.isSimpleGroup
      (E9.exists_mul_ne_mul_psl2 h24 e₁) (h3K e₁)
    obtain ⟨a₂, ha₂, ho₂, -⟩ := E9.exists_orderOf_three hK₂H e₂.isSimpleGroup
      (E9.exists_mul_ne_mul_psl2 h24 e₂) (h3K e₂)
    obtain ⟨a₃, ha₃, ho₃, hz₃⟩ := E9.exists_orderOf_three hLt (eLt.isSimpleGroup)
      ⟨eLt.symm a, eLt.symm b, fun h => hab (eLt.symm.injective (by
        rw [map_mul, map_mul]
        exact h))⟩
      (by rw [Nat.card_congr eX.toEquiv, card_Γ]; norm_num)
    have h3H := E9.three_le_pRank Nat.prime_three (hcomm' hI₁ hI₂ h12 hKI₁ hKI₂)
      (hcomm' hI₁ hI₀ (Ne.symm hcon.1) hKI₁ hLtI₀) (hcomm' hI₂ hI₀ (Ne.symm hcon.2) hKI₂ hLtI₀)
      ha₁ ha₂ ha₃ ho₁ ho₂ ho₃ hz₁ hz₃
    have h4 := pRank_modO2_eq H Nat.prime_three (by norm_num)
    have h5 := pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hH2 Nat.prime_three (by norm_num)
    omega
  rcases h0 with rfl | rfl
  · exact false_of_le hList hSL2 h36 h37 h39 hKG hK hyp.fsu.qtke hH2 hS hfamLt eX hI₀ hI₂ h12
      hLtI₀ hKI₁ hKI₂ h24 e₁ e₂
  · exact false_of_le hList hSL2 h36 h37 h39 hKG hK hyp.fsu.qtke hH2 hS hfamLt eX hI₀ hI₁
      (Ne.symm h12) hLtI₀ hKI₂ hKI₁ h24 e₂ e₁

end CFSG.Quasithin.Vol2.Ch10.SecB
