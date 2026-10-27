module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Background.SmithC27OTwoZ
public import CFSG.Quasithin.Recognition.St84.AppTreeL2
import all CFSG.Quasithin.Recognition.St84.AppTreeL2

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.F1 CFSG.Quasithin.F7
  CFSG.Quasithin.SmithC27
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112sa_borelOf_le_sup_oTwoRes_inf {S Li B : Subgroup H}
    (hsyl : IsSylowTwoOf (S ⊓ Li) Li) (hSB : S ≤ B) (hB : borelOf Li S ≤ B) :
    borelOf Li S ≤ S ⊔ (oTwoRes Li ⊓ B) := by
  intro b hb
  obtain ⟨a, b', rfl, ha, hb', ⟨k, hak⟩, hb'odd⟩ := exists_odd_mul_two_elt b
  have hb_borel : b' ∈ borelOf Li S := Subgroup.zpowers_le.mpr hb hb'
  have ha_borel : a ∈ borelOf Li S := Subgroup.zpowers_le.mpr hb ha
  have hK : IsSylowTwoOf (S ⊓ Li) (borelOf Li S) :=
    isSylowTwoOf_mono_right hsyl (sylow_le_borelOf Li S) (borelOf_le Li S)
  have haP : a ∈ oTwoPrime (borelOf Li S) :=
    Subgroup.subset_closure ⟨ha_borel, k, hak⟩
  rw [oTwoPrime_eq_of_normal_sylow hK (borelOf_le_normalizer Li S)] at haP
  have hb'oddRes : b' ∈ oTwoRes Li :=
    Subgroup.subset_closure ⟨borelOf_le Li S hb_borel, orderOf b', hb'odd,
      pow_orderOf_eq_one b'⟩
  have haB : a ∈ B := hSB haP.1
  have hb'B : b' ∈ B := by
    have h := B.mul_mem (hB hb) (B.inv_mem haB)
    simpa [mul_assoc] using h
  have hmem := Subgroup.mul_mem_sup
    (show b' ∈ oTwoRes Li ⊓ B from ⟨hb'oddRes, hb'B⟩) haP.1
  simpa [sup_comm] using hmem

theorem f112sa_borelOf_left_le_sup_K {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    borelOf L1 S ≤ S ⊔ f112saK L1 L2 S :=
  (f112sa_borelOf_le_sup_oTwoRes_inf (B := bigB L1 L2 S) hF.1.h1.sylow le_sup_right
    (le_sup_left.trans le_sup_left)).trans
    (sup_le_sup_left (show f112saX1 L1 L2 S ≤ f112saK L1 L2 S from le_sup_left) S)

theorem f112sa_borelOf_right_le_sup_K {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    borelOf L2 S ≤ S ⊔ f112saK L1 L2 S :=
  (f112sa_borelOf_le_sup_oTwoRes_inf (B := bigB L1 L2 S) hF.1.h2.sylow le_sup_right
    (le_sup_right.trans le_sup_left)).trans
    (sup_le_sup_left (show f112saX2 L1 L2 S ≤ f112saK L1 L2 S from le_sup_right) S)

theorem f112sa_bigB_eq_S_sup_K {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) :
    bigB L1 L2 S = S ⊔ f112saK L1 L2 S := by
  refine le_antisymm ?_ (sup_le le_sup_right (f112sa_K_le_bigB L1 L2 S))
  refine sup_le (sup_le (f112sa_borelOf_left_le_sup_K hF)
    (f112sa_borelOf_right_le_sup_K hF)) le_sup_left

theorem f112saQ_isPGroup_of_f112Hyp_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) [hN : (f112saK' L1 L2 S).Normal] :
    IsPGroup 2 (f112saQ L1 L2 S) := by
  let E0 := f112saE0 L1 L2 S
  let K' := f112saK' L1 L2 S
  let S' : Subgroup E0 := S.subgroupOf (f112P1 L1 L2 S ⊓ f112P2 L1 L2 S)
  have hB : bigB L1 L2 S = S ⊔ f112saK L1 L2 S := f112sa_bigB_eq_S_sup_K hF
  have hSbig : S ≤ bigB L1 L2 S := le_sup_right
  have hSE : S ≤ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S :=
    le_inf (hSbig.trans le_sup_right) (hSbig.trans le_sup_right)
  have hKE : f112saK L1 L2 S ≤ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S :=
    le_inf ((f112sa_K_le_bigB L1 L2 S).trans le_sup_right)
      ((f112sa_K_le_bigB L1 L2 S).trans le_sup_right)
  have hSK : S ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
    hSbig.trans (f112sa_bigB_le_normalizer_K hF)
  have hsup : S' ⊔ K' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxB : (x : H) ∈ bigB L1 L2 S := (f112_inf_eq_bigB_of_hyp111R hR).le x.2
    have hxS : (x : H) ∈ S ⊔ f112saK L1 L2 S := hB ▸ hxB
    rw [sup_comm] at hxS
    obtain ⟨k, hk, s, hs, hks⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hSK).mp hxS
    have hkE : k ∈ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S := hKE hk
    have hsE : s ∈ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S := hSE hs
    have hmem : x = ⟨k, hkE⟩ * ⟨s, hsE⟩ := Subtype.ext hks
    rw [hmem, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk)
      (Subgroup.mem_subgroupOf.mpr hs)
  have hS'2 : IsPGroup 2 S' :=
    hF.1.h1.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSE).symm
  have hker : K'.map (QuotientGroup.mk' K') = ⊥ :=
    (Subgroup.map_eq_bot_iff (H := K') (f := QuotientGroup.mk' K')).mpr
      (by rw [QuotientGroup.ker_mk'])
  have hmap : S'.map (QuotientGroup.mk' K') = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' K')) hsup
    rw [Subgroup.map_sup, hker,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K')] at h
    simpa using h
  refine IsPGroup.of_surjective hS'2
    ((QuotientGroup.mk' K').comp S'.subtype) ?_
  intro y
  have hy : y ∈ S'.map (QuotientGroup.mk' K') := by rw [hmap]; exact Subgroup.mem_top y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, hxy⟩

theorem f112saQ_eq_one_of_odd_of_f112Hyp_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) [hN : (f112saK' L1 L2 S).Normal]
    {q : f112saQ L1 L2 S} (hodd : Odd (orderOf q)) : q = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ orderOf q := (f112saQ_isPGroup_of_f112Hyp_of_hyp111R hF hR).dvd_orderOf hne
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem f112EOdd_le_ker_chi_of_f112Hyp_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    f112EOdd L1 L2 S ≤ (f112saChiR hF hR).ker := by
  rw [f112EOdd, Subgroup.closure_le]
  rintro u ⟨-, huodd⟩
  exact MonoidHom.mem_ker.mpr (f112saQ_eq_one_of_odd_of_f112Hyp_of_hyp111R hF hR
    (huodd.of_dvd_nat (orderOf_map_dvd (f112saChiR hF hR) u)))

theorem f112E5_le_EOdd (L1 L2 S : Subgroup H) :
    f112E5 L1 L2 S ≤ f112EOdd L1 L2 S := by
  rw [f112E5, f112EOdd]
  refine Subgroup.closure_mono ?_
  rintro u ⟨hu, hu5⟩
  exact ⟨hu, by rw [hu5]; exact ⟨2, by norm_num⟩⟩

theorem f112E5_le_ker_chi_of_f112Hyp_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S)
    [hN : (f112saK' L1 L2 S).Normal]
    [hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal]
    [hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal] :
    f112E5 L1 L2 S ≤ (f112saChiR hF hR).ker :=
  (f112E5_le_EOdd L1 L2 S).trans (f112EOdd_le_ker_chi_of_f112Hyp_of_hyp111R hF hR)

theorem f112sa_five_map_le_E5_left {L1 L2 S : Subgroup H} :
    ((f112saFive L1).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112E5 L1 L2 S := by
  rw [f112sa_subgroupOf_closure_eq (K := f112saFive L1) (L := f112P1 L1 L2 S)
    (s := {x | x ∈ L1 ∧ orderOf x = 5}) rfl]
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨a, ha, rfl⟩
    obtain ⟨haL, haord⟩ := ha
    exact Subgroup.subset_closure ⟨Or.inl ⟨a, rfl⟩, by
      rw [orderOf_injective (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective a,
        ← Subgroup.orderOf_coe]
      exact haord⟩
  · rintro x ⟨hxL, -⟩
    exact Subgroup.mem_sup_left hxL

theorem f112sa_five_map_le_E5_right {L1 L2 S : Subgroup H} :
    ((f112saFive L2).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112E5 L1 L2 S := by
  rw [f112sa_subgroupOf_closure_eq (K := f112saFive L2) (L := f112P2 L1 L2 S)
    (s := {x | x ∈ L2 ∧ orderOf x = 5}) rfl]
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨a, ha, rfl⟩
    obtain ⟨haL, haord⟩ := ha
    exact Subgroup.subset_closure ⟨Or.inr ⟨a, rfl⟩, by
      rw [orderOf_injective (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective a,
        ← Subgroup.orderOf_coe]
      exact haord⟩
  · rintro x ⟨hxL, -⟩
    exact Subgroup.mem_sup_left hxL

theorem f112sa_oTwoRes_left_map_le_E5 {L1 L2 S : Subgroup H}
    (h1 : VA5 L1) :
    ((oTwoRes L1).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112E5 L1 L2 S :=
  (Subgroup.map_mono (Subgroup.subgroupOf_mono (f112P1 L1 L2 S)
    (f112sa_oTwoRes_le_five h1))).trans f112sa_five_map_le_E5_left

theorem f112sa_oTwoRes_right_map_le_E5 {L1 L2 S : Subgroup H}
    (h2 : VA5 L2) :
    ((oTwoRes L2).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112E5 L1 L2 S :=
  (Subgroup.map_mono (Subgroup.subgroupOf_mono (f112P2 L1 L2 S)
    (f112sa_oTwoRes_le_five h2))).trans f112sa_five_map_le_E5_right

theorem f112sa_X2_map_le_E5 {L1 L2 S : Subgroup H}
    (h2 : VA5 L2) :
    ((f112saX2 L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112E5 L1 L2 S := by
  intro u hu
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  have haX2 : (a : H) ∈ f112saX2 L1 L2 S := Subgroup.mem_subgroupOf.mp ha
  have haO : (a : H) ∈ oTwoRes L2 := haX2.1
  have haP2 : (a : H) ∈ f112P2 L1 L2 S :=
    (le_sup_left (a := L2) (b := bigB L1 L2 S)) (oTwoRes_le L2 haO)
  have heq : (f112Gold L1 L2 S).ofA a = (f112Gold L1 L2 S).ofB ⟨(a : H), haP2⟩ := by
    rw [f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, haP2⟩]
  rw [heq]
  exact f112sa_oTwoRes_right_map_le_E5 h2
    (Subgroup.mem_map_of_mem (f112Gold L1 L2 S).ofB (Subgroup.mem_subgroupOf.mpr haO))

theorem f112sa_X1_map_le_E5 {L1 L2 S : Subgroup H}
    (h1 : VA5 L1) :
    ((f112saX1 L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112E5 L1 L2 S := by
  intro u hu
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
  have haX1 : (a : H) ∈ f112saX1 L1 L2 S := Subgroup.mem_subgroupOf.mp ha
  have haO : (a : H) ∈ oTwoRes L1 := haX1.1
  have haP1 : (a : H) ∈ f112P1 L1 L2 S :=
    (le_sup_left (a := L1) (b := bigB L1 L2 S)) (oTwoRes_le L1 haO)
  have heq : (f112Gold L1 L2 S).ofB a = (f112Gold L1 L2 S).ofA ⟨(a : H), haP1⟩ := by
    rw [f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨haP1, a.2⟩]
  rw [heq]
  exact f112sa_oTwoRes_left_map_le_E5 h1
    (Subgroup.mem_map_of_mem (f112Gold L1 L2 S).ofA (Subgroup.mem_subgroupOf.mpr haO))

theorem f112sa_P1'_map_le_E5 {L1 L2 S : Subgroup H}
    (h1 : VA5 L1) (h2 : VA5 L2) :
    ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA ≤
      f112E5 L1 L2 S := by
  rw [f112saP1', Subgroup.subgroupOf_sup
    ((oTwoRes_le L1).trans le_sup_left)
    ((f112sa_X2_le_bigB L1 L2 S).trans le_sup_right), Subgroup.map_sup]
  exact sup_le (f112sa_oTwoRes_left_map_le_E5 h1) (f112sa_X2_map_le_E5 h2)

theorem f112sa_P2'_map_le_E5 {L1 L2 S : Subgroup H}
    (h1 : VA5 L1) (h2 : VA5 L2) :
    ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ≤
      f112E5 L1 L2 S := by
  rw [f112saP2', Subgroup.subgroupOf_sup
    ((oTwoRes_le L2).trans le_sup_left)
    ((f112sa_X1_le_bigB L1 L2 S).trans le_sup_right), Subgroup.map_sup]
  exact sup_le (f112sa_oTwoRes_right_map_le_E5 h2) (f112sa_X1_map_le_E5 h1)

theorem f112E5_inf_ofA_range {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    f112E5 L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range =
      ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map
        (f112Gold L1 L2 S).ofA := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  haveI hN : (f112saK' L1 L2 S).Normal := f112saK'_normal_of_hyp111R hF hR
  haveI hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal :=
    f112sa_P1'_normal hF
  haveI hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal :=
    f112sa_P2'_normal hF
  refine le_antisymm ?_ ?_
  · rintro u ⟨huE, huA⟩
    obtain ⟨p, hp⟩ := huA
    have hchi : f112saChiR hF hR u = 1 := MonoidHom.mem_ker.mp
      (f112E5_le_ker_chi_of_f112Hyp_of_hyp111R hF hR huE)
    have hchi1 : f112saChi1R hF hR p = 1 := by
      rw [← f112saChiR_ofA hF hR p, hp]
      exact hchi
    have hp1 : (p : H) ∈ f112saP1' L1 L2 S :=
      (f112saChi1R_eq_one_iff hF hR p).mp hchi1
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp1, hp⟩
  · rintro u ⟨a, ha, rfl⟩
    exact ⟨f112sa_P1'_map_le_E5 h1 h2 (Subgroup.mem_map_of_mem _ ha), ⟨a, rfl⟩⟩

theorem f112E5_inf_ofB_range {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    f112E5 L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range =
      ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map
        (f112Gold L1 L2 S).ofB := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  haveI hN : (f112saK' L1 L2 S).Normal := f112saK'_normal_of_hyp111R hF hR
  haveI hN1 : ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).Normal :=
    f112sa_P1'_normal hF
  haveI hN2 : ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).Normal :=
    f112sa_P2'_normal hF
  refine le_antisymm ?_ ?_
  · rintro u ⟨huE, huB⟩
    obtain ⟨p, hp⟩ := huB
    have hchi : f112saChiR hF hR u = 1 := MonoidHom.mem_ker.mp
      (f112E5_le_ker_chi_of_f112Hyp_of_hyp111R hF hR huE)
    have hchi2 : f112saChi2R hF hR p = 1 := by
      rw [← f112saChiR_ofB hF hR p, hp]
      exact hchi
    have hp1 : (p : H) ∈ f112saP2' L1 L2 S :=
      (f112saChi2R_eq_one_iff hF hR p).mp hchi2
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_subgroupOf.mpr hp1, hp⟩
  · rintro u ⟨a, ha, rfl⟩
    exact ⟨f112sa_P2'_map_le_E5 h1 h2 (Subgroup.mem_map_of_mem _ ha), ⟨a, rfl⟩⟩

theorem f112E5_inf_ofA_range_inf_ofB_range
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    f112E5 L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
      ((f112saK L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := by
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 2) (n := 2) (by norm_num) (by norm_num) hF.1 h1 h2
  let X := f112Gold L1 L2 S
  have hKP1' : f112saK L1 L2 S ≤ f112saP1' L1 L2 S :=
    sup_le ((show f112saX1 L1 L2 S ≤ oTwoRes L1 from inf_le_left).trans le_sup_left)
      (show f112saX2 L1 L2 S ≤ f112saP1' L1 L2 S from le_sup_right)
  rw [f112E5_inf_ofA_range hF h1 h2]
  refine le_antisymm ?_ ?_
  · rintro u ⟨huM, huB⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp huM
    have haP1' : (a : H) ∈ f112saP1' L1 L2 S := Subgroup.mem_subgroupOf.mp ha
    have huBase : X.ofA a ∈ (Monoid.PushoutI.base X.diagram).range := by
      rw [← X.ofA_range_inf_ofB_range]
      exact ⟨⟨a, rfl⟩, huB⟩
    obtain ⟨c, hc⟩ := huBase
    have htoA : X.toA c = a := X.ofA_injective (by rw [X.ofA_toA, hc])
    have haB : (a : H) ∈ bigB L1 L2 S := by
      rw [← htoA]
      exact (f112_inf_eq_bigB_of_hyp111R hR) ▸ c.2
    have haK : (a : H) ∈ f112saK L1 L2 S := by
      have h : (a : H) ∈ f112saP1' L1 L2 S ⊓ bigB L1 L2 S := ⟨haP1', haB⟩
      rwa [f112sa_P1'_inf_bigB hF] at h
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr haK, rfl⟩
  · refine le_inf ?_ ?_
    · exact Subgroup.map_mono (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) hKP1')
    · rintro u ⟨a, ha, rfl⟩
      have haB : (a : H) ∈ bigB L1 L2 S :=
        f112sa_K_le_bigB L1 L2 S (Subgroup.mem_subgroupOf.mp ha)
      have haP2 : (a : H) ∈ f112P2 L1 L2 S :=
        ((f112_inf_eq_bigB_of_hyp111R hR) ▸ haB).2
      have heq : X.ofA a = X.ofB ⟨(a : H), haP2⟩ :=
        f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, haP2⟩
      rw [heq]
      exact ⟨⟨(a : H), haP2⟩, rfl⟩

end CFSG.Quasithin.F112R.St84
