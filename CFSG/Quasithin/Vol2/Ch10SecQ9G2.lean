module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G1
public import CFSG.Quasithin.Vol2.Ch10SecB6S21

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

namespace RCtx

variable {T L I R H : Subgroup G} (c : RCtx T L I R H)
include c

theorem mem_fsuM_of_coprime_three (hK : LocalSQTK G) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {w : G}
    (hw : w ∈ oTwoFIn H) (hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (⟨w, C2Six.oTwoFIn_le hw⟩ : ↥H))).Coprime 3) : w ∈ fsuM T L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, Lb, hLb, hprod⟩ := SecB.c2_6_two' (c.hypC23 hK h331 h37 h38)
    (SecB.charTwo_oTwoFIn (c.oddCoreOf_eq_bot h37 h38 h331))
  obtain ⟨m, hm, y, hy, hwy⟩ := hprod w hw
  set N := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hN
  have hYH : oTwoFIn H ≤ H := C2Six.oTwoFIn_le
  have hNmem : ∀ (g : G) (hg : g ∈ oTwoFIn H),
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨g, hYH hg⟩ : ↥H) ∈ N :=
    fun g hg => C2Six.mem_oTwoFIn_iff.mp hg
  have hprodY : (List.ofFn y).prod ∈ oTwoFIn H := by
    refine Subgroup.list_prod_mem _ fun z hz => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact (hLb i).1.2.1 (hy i)
  obtain ⟨P3⟩ : Nonempty (Sylow 3 ↥N) := inferInstance
  have hP3n : (P3 : Subgroup ↥N).Normal := inferInstance
  have huniq := Sylow.unique_of_normal P3 hP3n
  set P3G : Subgroup G :=
    ((((P3 : Subgroup ↥N).map N.subtype).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
      H.subtype) with hP3G
  have hyP : ∀ i, y i ∈ P3G := by
    intro i
    have hyi : y i ∈ oTwoFIn H := (hLb i).1.2.1 (hy i)
    refine ⟨⟨y i, hYH hyi⟩, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨y i, hYH hyi⟩ : ↥H) ∈
      (P3 : Subgroup ↥N).map N.subtype
    have h3 := SecB.mk_pow_three_eq_one (hLb i).1 (hLb i).2 (hy i)
    set e : ↥N := ⟨_, hNmem _ hyi⟩ with he
    have he3 : e ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
    have hep : IsPGroup 3 (Subgroup.zpowers e) := by
      have hd : orderOf e ∣ 3 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one he3
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨Q, hQ⟩ := hep.exists_le_sylow
    have hQP : Q = P3 := Subsingleton.elim _ _
    rw [hQP] at hQ
    exact ⟨e, hQ (Subgroup.mem_zpowers e), rfl⟩
  have hzP : (List.ofFn y).prod ∈ P3G := Subgroup.list_prod_mem _ fun z hz => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hyP i
  obtain ⟨zz, hzzP, hzz⟩ := hzP
  obtain ⟨z, hzP3, hzv⟩ := hzzP
  set wN : ↥N := ⟨_, hNmem w hw⟩ with hwN
  set mN : ↥N := ⟨_, hNmem m hm.2⟩ with hmN
  have hzz' : zz = (⟨(List.ofFn y).prod, hYH hprodY⟩ : ↥H) := Subtype.ext hzz
  have hzv' : ((z : ↥N) : ↥H ⧸ CFSG.pCore 2 ↥H) = QuotientGroup.mk' (CFSG.pCore 2 ↥H) zz := hzv
  have hrel : wN = mN * z := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hzv', hzz', hwN, hmN]
    simp only [← map_mul]
    congr 1
    exact Subtype.ext (by simp [hwy])
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp P3.isPGroup') ⟨z, hzP3⟩
  rw [Subgroup.orderOf_mk] at hj
  have hcop' : (orderOf wN).Coprime (orderOf z⁻¹) := by
    rw [orderOf_inv, hj, hwN, Subgroup.orderOf_mk]
    exact Nat.Coprime.pow_right j hcop
  have hc : Commute wN z⁻¹ := Group.IsNilpotent.commute_of_orderOf_coprime hcop'
  obtain ⟨k, hk⟩ := SecB.exists_pow_eq_of_commute_coprime hc hcop'
  have hmw : mN = wN * z⁻¹ := by rw [hrel]; group
  rw [← hmw] at hk
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((⟨m, hYH hm.2⟩ : ↥H) ^ k) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨w, hYH hw⟩ : ↥H) := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
  have hO : (((⟨m, hYH hm.2⟩ : ↥H) ^ k)⁻¹ * ⟨w, hYH hw⟩ : ↥H) ∈ (CFSG.Open.pCore 2 ↥H) := by
    exact hk'
  have hoM := c.pCoreOf_le_fsuM ⟨_, hO, rfl⟩
  have hw' : w = m ^ k * (((((⟨m, hYH hm.2⟩ : ↥H) ^ k)⁻¹ * ⟨w, hYH hw⟩ : ↥H)) : G) := by
    simp
  rw [hw']
  exact (fsuM T L).mul_mem ((fsuM T L).pow_mem hm.1.1 k) hoM

theorem exists_cComp (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) {X : Subgroup G}
    (hX : X ∈ cComp (fsuM T L)) (hXH : X ≤ H) (hXR : R ≤ Subgroup.normalizer (X : Set G)) :
    ∃ K ∈ cComp H, X ≤ K ∧ (K.subgroupOf H).Normal := by
  have hXfam : X ∈ lFamily R := cComp_subset_lFamily c.R_le_fsuM hX
  obtain ⟨K, hK', hXK⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 c.two c.sylow hXH hXfam
  exact ⟨K, hK', hXK, Vol2Native.lemma_1_2_4_normal hK h37 h38 c.two c.sylow hXfam hXK hK' hXR⟩

theorem false_of_le_cComp (hF1 : SecB.Fact10_2_6Pair) (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hLK : L ≤ K) (hLtK : CFSG.conjugate L t ≤ K) : False := by
  have hyp := c.hyp
  have hL0H := c.fsuL0_le
  have hRM := c.R_le_fsuM
  obtain ⟨hc₁, hn₁, hle₁, -⟩ := SecB.li_data h37 h38 hyp ht (X := L) (Or.inl rfl)
  obtain ⟨hc₂, hn₂, hle₂, ⟨e₂⟩⟩ :=
    SecB.li_data h37 h38 hyp ht (X := CFSG.conjugate L t) (Or.inr rfl)
  have hfam₁ := cComp_subset_lFamily hRM hc₁
  have hfam₂ := cComp_subset_lFamily hRM hc₂
  obtain ⟨f₁⟩ := SecB.nonempty_modO2_modO2Image (hle₁.trans hL0H)
  obtain ⟨f₂⟩ := SecB.nonempty_modO2_modO2Image (hle₂.trans hL0H)
  have hcomm : ⁅modO2Image H L, modO2Image H (CFSG.conjugate L t)⁆ ≤
      pCoreOf 2 (modO2Image H L) ⊓ pCoreOf 2 (modO2Image H (CFSG.conjugate L t)) := by
    refine (SecB.commutator_modO2Image_le (SecA.commutator_conjugate_le h37 hyp ht htn)).trans ?_
    exact le_inf ((SecB.modO2Image_mono' inf_le_left).trans SecB.modO2Image_pCoreOf_le)
      ((SecB.modO2Image_mono' inf_le_right).trans SecB.modO2Image_pCoreOf_le)
  exact hF1 _ (Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hK c.two) (modO2Image H R)
    (modO2Image H K) (modO2Image H L) (modO2Image H (CFSG.conjugate L t))
    (SecB.isSylowTwoOf_modO2Image c.sylow) (modO2Image_mem_cComp hKc)
    (modO2Image_mem_lFamily c.sylow (hle₁.trans hL0H) hfam₁)
    (modO2Image_mem_lFamily c.sylow (hle₂.trans hL0H) hfam₂)
    (SecB.modO2Image_le_normalizer' (c.le_T1.trans hn₁))
    (SecB.modO2Image_le_normalizer' (c.le_T1.trans hn₂))
    (SecB.modO2Image_mono' hLK) (SecB.modO2Image_mono' hLtK) hcomm
    ⟨(f₁.trans e₂.symm).trans f₂.symm⟩

theorem lt_or_lt (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {K₁ K₂ : Subgroup G}
    (hLK₁ : L ≤ K₁) (hLK₂ : CFSG.conjugate L t ≤ K₂) (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H)
    (hn₁ : (K₁.subgroupOf H).Normal) (hn₂ : (K₂.subgroupOf H).Normal) :
    L < K₁ ∨ CFSG.conjugate L t < K₂ := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 : L = K₁ := eq_of_le_of_not_lt hLK₁ hcon.1
  have h2 : CFSG.conjugate L t = K₂ := eq_of_le_of_not_lt hLK₂ hcon.2
  have hN₁ := (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁H).mp hn₁
  have hN₂ := (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂H).mp hn₂
  apply c.not_le
  intro h hh
  show h ∈ Subgroup.normalizer (fsuL0 T L : Set G)
  have e1 := hN₁ hh
  have e2 := hN₂ hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at e1 e2 ⊢
  rw [SecA.fsuL0_eq_sup h37 h38 c.hyp ht htn, h2, h1, Subgroup.map_sup, e1, e2]

end RCtx

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
