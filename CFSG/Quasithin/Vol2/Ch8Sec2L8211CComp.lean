module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8211Wire
public import CFSG.Quasithin.Vol2.Ch8Sec2L8211CRow
public import CFSG.Quasithin.EmptyFaithful.S152He9W

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.H13.L8211C CFSG.Quasithin.H13.L8211CRow

theorem isSubnormal_fsuM_of_fsu {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hfsu : FSU G T L I) :
    IsSubnormal L (fsuM T L) := by
  have hL : IsSubnormal L (L ⊔ T) := hfsu.maximal.1.2.1.2.2.1
  have hL0 : fsuL0 T L ≤ L ⊔ T :=
    CFSG.Quasithin.conjClosure_le fun h hh z hz =>
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((le_sup_right : T ≤ L ⊔ T) hh)
        ((le_sup_left : L ≤ L ⊔ T) hz)) ((L ⊔ T).inv_mem ((le_sup_right : T ≤ L ⊔ T) hh))
  have hLL0 : L ≤ fsuL0 T L := CFSG.Quasithin.le_conjClosure L T
  have hs1 : IsSubnormal L (fsuL0 T L) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL hLL0 hL0
  have hs2 : IsSubnormal (fsuL0 T L) (fsuM T L) :=
    CFSG.Quasithin.A3.subnormal_of_normal Subgroup.le_normalizer inferInstance
  exact hs1.trans hs2

theorem ne_bot_of_surjective {G : Type} [Group G] (L : Subgroup G) {R : Type} [Group R]
    [Nontrivial R] (f : ↥L →* R) (hf : Function.Surjective f) : L ≠ ⊥ := by
  intro h
  haveI : Nontrivial ↥L := hf.nontrivial
  have hsub : Subsingleton ↥L := by
    rw [h]
    infer_instance
  exact not_subsingleton _ hsub

theorem stmt8_2_11_comp_of
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2) (h825 : Stmt8_2_5)
    (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12) (hm24 : SchurMult2M24) :
    Stmt8_2_11_comp := by
  intro G _ _ T L I hyp h731 h821 hc hrow hnot24 z hz hzV
  obtain ⟨hzV', hzT, hz1G⟩ := mem_and_ne_one (T := T) hz hzV
  have hz1 : (⟨z, hzV'⟩ : ↥(fsuV T I)) ≠ 1 := fun h => hz1G (congrArg Subtype.val h)
  obtain ⟨-, hLzN, hPz, hXC, hSV, -, -, hM22, hM24⟩ :=
    row_setup h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 kg82CoverL34_holds
      kg82CoverM22_holds hm24 hyp h731 h821 hrow z hzV' hzT
  have hperf : ⁅ch8Lz L z, ch8Lz L z⁆ = ch8Lz L z := CFSG.Quasithin.perfectCore_perfect _
  have hLM : IsSubnormal L (fsuM T L) := isSubnormal_fsuM_of_fsu hyp.fsu
  have hinf : IsSubnormal (L ⊓ Subgroup.centralizer ({z} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    have h := hLM.inf_of_le (inf_le_left : fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤
      fsuM T L)
    rwa [← inf_assoc, inf_eq_left.mpr hLM.le] at h
  have hLX : IsSubnormal (ch8Lz L z) (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) :=
    CFSG.Quasithin.A3.subnormal_perfectCore hinf
  have key : IsQS ↥(ch8Lz L z) ∧ ch8Lz L z ≠ ⊥ := by
    have hrow0 := hrow
    rcases hrow with ⟨n, hn⟩ | hM22c | hM24code | hM24cc
    ·
      have hn1 : n = 1 :=
        stmt8_2_11_n1_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 kg82CoverL34_holds
          kg82CoverM22_holds hm24 G T L I hyp h731 h821 hc hrow0 hnot24 z hz hzV n hn
      subst hn1
      obtain ⟨α, β, hαs, hαk, -, -, -⟩ :=
        stmt8_2_11_L34_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 kg82CoverL34_holds
          kg82CoverM22_holds hm24 G T L I hyp h731 h821 hc hrow0 hnot24 z hz hzV hn
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥α.ker := by
        rw [hαk]
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      haveI : Group.IsNilpotent ↥α.ker := hp.isNilpotent
      exact ⟨isQS_of_surjective α hαs (perfect_top_subgroup hperf) (isQS_of_isSimpleGroup _),
        ne_bot_of_surjective _ α hαs⟩
    ·
      obtain ⟨hnt, hQP⟩ := isQS_parz22 (hM22 hM22c) hz1 hSV
      haveI := hnt
      have hsurj := L8211M.actTo_surjective hLzN hPz
      have hp : IsPGroup 2 ↥(L8211M.actTo hLzN hPz).ker :=
        L8211M.isPGroup_ker_actTo hLzN hPz hXC
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent ↥(L8211M.actTo hLzN hPz).ker := hp.isNilpotent
      exact ⟨isQS_of_surjective (L8211M.actTo hLzN hPz) hsurj (perfect_top_subgroup hperf) hQP,
        ne_bot_of_surjective _ (L8211M.actTo hLzN hPz) hsurj⟩
    · exact absurd hM24code hnot24
    ·
      obtain ⟨hnt, hQP⟩ := isQS_parz24 (hM24 hM24cc) hz1 hSV
      haveI := hnt
      have hsurj := L8211M.actTo_surjective hLzN hPz
      have hp : IsPGroup 2 ↥(L8211M.actTo hLzN hPz).ker :=
        L8211M.isPGroup_ker_actTo hLzN hPz hXC
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent ↥(L8211M.actTo hLzN hPz).ker := hp.isNilpotent
      exact ⟨isQS_of_surjective (L8211M.actTo hLzN hPz) hsurj (perfect_top_subgroup hperf) hQP,
        ne_bot_of_surjective _ (L8211M.actTo hLzN hPz) hsurj⟩
  exact mem_cComp_of_isQS hLX key.2 hperf key.1

end CFSG.Quasithin.H13
