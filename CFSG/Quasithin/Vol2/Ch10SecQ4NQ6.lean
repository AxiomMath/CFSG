module

public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ6a
public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

open Ch10 in
theorem hypC23Cat' (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hL0T1 : fsuL0 T L ⊔ T1 T L ≤ H) (hH2 : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf (T1 T L) H) :
    EmptyFaithfulMultiple.HypC23Cat H (pCoreOf 2 (fsuL0 T L ⊔ T)) (fsuM T L ⊓ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (fsuL0 T L ⊔ T) with hRdef
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hR1 : R ≠ ⊥ := SecA.pCoreOf_L0T_ne_bot hyp
  have hRT1 : R ≤ T1 T L := SecB.pCoreOf_L0T_le_T1 hyp
  have hT1H : T1 T L ≤ H := le_sup_right.trans hL0T1
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hL0T1
  have hL0TN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hNR := SecB.normalizer_le_fsuM_of_L0T h331 hyp hRp hR1 hL0TN
  refine ⟨hK H hH2, ⟨hRT1.trans hT1H, hR1, ?_⟩, inf_le_right, ?_, ?_⟩
  ·
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (hRT1.trans hT1H) Subgroup.le_normalizer) inf_le_right hRp) ?_
    have hT1N : T1 T L ≤ H ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf hT1H ((inf_le_left.trans le_sup_right).trans hL0TN)
    have hS' : IsSylowTwoOf (T1 T L) (H ⊓ Subgroup.normalizer (R : Set G)) :=
      B6.isSylowTwoOf_mono hS hT1N inf_le_left
    have hP1 := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS'
    have hLN : fsuL0 T L ⊔ T1 T L ≤ H ⊓ Subgroup.normalizer (R : Set G) :=
      sup_le (le_inf hL0H (le_sup_left.trans hL0TN)) hT1N
    have hP2 : pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) ≤ pCoreOf 2 (fsuL0 T L ⊔ T1 T L) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP1.trans le_sup_right)
        (hLN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    refine hP2.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_left inf_le_left _)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
    refine le_trans ?_ (SecA.normalizer_le_normalizer_pCoreOf (fsuL0 T L ⊔ T1 T L))
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun s hs => ?_
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (SecA.le_fsuM T L hs)
    have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (SecB.T1_normal h37 h38 hyp hs)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, h1, h2]
  ·
    refine iSup₂_le fun C hCR => iSup₂_le fun hC1 hCc => ?_
    have hCN : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := R) (C.subgroupOf R)
      rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h
    exact le_inf (inf_le_right.trans (SecB.normalizer_le_fsuM_of_L0T h331 hyp (hRp.to_le hCR) hC1
      (hL0TN.trans hCN))) inf_le_left
  ·
    have hT : IsSylowTwoOf T (fsuM T L) :=
      CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (SecA.le_fsuM T L)
    have h427 := (a4_2_7 (eq_oTwoUpper_of_perfect (SecB.fsuL0_perfect' h37 h38 hyp))
      (SecA.fsuL0_le_fsuM T L) (Subgroup.normal_subgroupOf_of_le_normalizer le_rfl) hT rfl
      hNR).2.2.2.2.2
    exact B6.isSylowTwoOf_mono h427 (le_conjClosure R _) (conjClosure_mono le_rfl inf_le_left)

open Ch10 in
theorem hypC23' (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hL0T1 : fsuL0 T L ⊔ T1 T L ≤ H) (hH2 : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf (T1 T L) H) :
    HypC23 H (pCoreOf 2 (fsuL0 T L ⊔ T)) (fsuM T L ⊓ H) := by
  have h := hypC23Cat' hK h331 h37 h38 hyp hL0T1 hH2 hS
  exact ⟨G64.sqtkGroup_of_isSQTKCat h.sqtk, h.radical, h.le, h.cgs, h.sylow⟩

open Ch10 in
theorem mem_fsuM_of_coprime_three' (hK : LocalSQTK G) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {H : Subgroup G} (hL0T1 : fsuL0 T L ⊔ T1 T L ≤ H)
    (hH2 : pCoreOf 2 H ≠ ⊥)
    (hS : IsSylowTwoOf (T1 T L) H) {w : G} (hw : w ∈ oTwoFIn H)
    (hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (⟨w, C2Six.oTwoFIn_le hw⟩ : ↥H))).Coprime 3) : w ∈ fsuM T L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOH := oddCoreOf_eq_bot' h37 h38 h331 hyp hL0T1 hH2
  obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two'' (hypC23' hK h331 h37 h38 hyp hL0T1 hH2 hS)
    (charTwo_oTwoFIn' hOH)
  obtain ⟨m, hm, y, hy, hwy⟩ := hprod w hw
  have hO2M : pCoreOf 2 H ≤ fsuM T L :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS).trans (inf_le_left.trans (SecA.le_fsuM T L))
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
    have h3 := mk_pow_three_eq_one' (hLb i).1 (hLb i).2 (hy i)
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
  obtain ⟨k, hk⟩ := exists_pow_eq_of_commute_coprime' hc hcop'
  have hmw : mN = wN * z⁻¹ := by rw [hrel]; group
  rw [← hmw] at hk
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((⟨m, hYH hm.2⟩ : ↥H) ^ k) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨w, hYH hw⟩ : ↥H) := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
  have hO : (((⟨m, hYH hm.2⟩ : ↥H) ^ k)⁻¹ * ⟨w, hYH hw⟩ : ↥H) ∈ (CFSG.Open.pCore 2 ↥H) := by
    exact hk'
  have hoM := hO2M ⟨_, hO, rfl⟩
  have hw' : w = m ^ k * (((((⟨m, hYH hm.2⟩ : ↥H) ^ k)⁻¹ * ⟨w, hYH hw⟩ : ↥H)) : G) := by
    simp
  rw [hw']
  exact (fsuM T L).mul_mem ((fsuM T L).pow_mem hm.1.1 k) hoM

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
