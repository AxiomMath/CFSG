module

public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwapSylow
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProof
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofKernel
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProof
import CFSG.RankThree.PartTwo.KFacts.K71bCentList
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofNotAct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1117Res5Proof

section Group

variable {G : Type} [Group G]

theorem exists_conj_mem_of_isSylowOf [Finite G] {K T : Subgroup G} (hT : IsSylowOf 3 T K) {y : G}
    (hy : y ∈ K) {k : ℕ} (hyk : y ^ 3 ^ k = 1) : ∃ h ∈ K, h * y * h⁻¹ ∈ T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, rfl⟩ := hT
  have hZ : IsPGroup 3 (Subgroup.zpowers (⟨y, hy⟩ : K)) :=
    Item1117Proof.isPGroup_zpowers (k := k) (Subtype.ext (by simpa using hyk))
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨y, hy⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (Subgroup.mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩

theorem forall_commute_of_closure {S : Set G} {t : G} (hS : ∀ u ∈ S, u * t = t * u) :
    ∀ y ∈ Subgroup.closure S, y * t = t * y := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.closure_le]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hS u hu)
  exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem forall_commutator_mem_of_closure {A D : Subgroup G} {S : Set G}
    (hA : Subgroup.closure S ≤ Subgroup.normalizer (A : Set G))
    (hD : Subgroup.closure S ≤ Subgroup.normalizer (D : Set G))
    (hS : ∀ t ∈ S, ∀ y ∈ A, t * y * t⁻¹ * y⁻¹ ∈ D) :
    ∀ w ∈ Subgroup.closure S, ∀ y ∈ A, w * y * w⁻¹ * y⁻¹ ∈ D := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem t ht => exact hS t ht
  | one => intro y _; simp
  | mul u v hu hv ihu ihv =>
    intro y hy
    have h3 : u * (v * y * v⁻¹ * y⁻¹) * u⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hD hu) _).mp (ihv y hy)
    have e : u * v * y * (u * v)⁻¹ * y⁻¹ =
        (u * (v * y * v⁻¹ * y⁻¹) * u⁻¹) * (u * y * u⁻¹ * y⁻¹) := by group
    rw [e]
    exact D.mul_mem h3 (ihu y hy)
  | inv u hu ihu =>
    intro y hy
    have hy' : u⁻¹ * y * u⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (inv_mem (hA hu)) y).mp hy
    rw [inv_inv] at hy'
    have e : u⁻¹ * y * u⁻¹⁻¹ * y⁻¹ = (u * (u⁻¹ * y * u) * u⁻¹ * (u⁻¹ * y * u)⁻¹)⁻¹ := by group
    rw [e]
    exact D.inv_mem (ihu _ hy')

end Group

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem mem_zpowers_of_mem_swap (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {e : G} (heA : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G))
    {Ye R' Y'' : Subgroup G} (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') {t : G} (htR : t ∈ R') (htc : t * c = c * t)
    (htY : t ∈ Sec4.thetaQuotCentralizer Ye) : t ∈ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstdE := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq heA hecd hYe hKYe
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd
  obtain ⟨hce, -, hd1⟩ := hstdE.not_mem_facts h.inf_eq hA'
  obtain ⟨k, hk⟩ := hstd.isSylowOf.isPGroup ⟨t, htR⟩
  have htk : t ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have he3 : e ^ 3 = 1 := h.mem_partTwoF.1.2 e heA
  have he1 : e ≠ 1 := fun h1 => hecd (h1 ▸ Subgroup.one_mem _)
  have hte : t * e = e * t := Sec12.commute_of_conj_mem_zpowers (orderOf_eq_prime he3 he1)
    ((Subgroup.mem_normalizer_iff.mp (hstd.isSylowOf.le htR) e).mp (Subgroup.mem_zpowers e)) htk
  have hdK : d ∈ sec11K L e := hstdE.d_mem_sec11K h.inf_eq
  have hKp : Group.IsPerfect (sec11K L e) := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hK1 : sec11K L e ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have hKL : sec11K L e ≤ L := sec11K_le L e
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hKK : sec11K L e ≤ sec11K Ye c :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKp (le_inf hKYe (hKL.trans hLc))
  have hY'' : Y'' = L := Sec6.eq_of_mem_thetaComponentsIn_of_le hstd.mem_thetaComponentsAt_Y
    h.mem_thetaComponentsAt hKp hK1 (hKK.trans hstd.sec11K_le) hKL
  have hK1' : sec11K Ye c ≠ ⊥ := fun hb => hK1 (le_bot_iff.mp (hb ▸ hKK))
  have htYe : t ∈ Subgroup.normalizer (Ye : Set G) :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp htY).1
  have htL : t ∈ Subgroup.normalizer (L : Set G) := by
    have := hstd.mem_normalizer_Y hK1' htYe htc
    rwa [hY''] at this
  have htK := Item1119StepsProof.commutator_mem_theta_sec11K_of_mem_thetaQuotCentralizer_Y
    hstdE htL hte htY
  obtain ⟨heN, he3', -, -, -⟩ :=
    basic_facts_of_conj h45 h.toSec11Std h.inf_eq h.closure_eq heA hecd
  have hout : Sec4.InducesOuterTheta e L :=
    ⟨heN, not_isInnerAut_of_not_mem_closure h.toHyp91 h.inf_eq h.closure_eq heA hecd heN⟩
  obtain ⟨i, hi⟩ := KFacts.exists_mul_pow_mem_thetaQuotCentralizer_of_list h.isList1016 hout he3'
    htL ⟨k, htk⟩ hte htK
  have hy1 : t * e ^ i = 1 := by
    by_contra hy1
    set H₁ := Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.normalizer (L : Set G) with hH₁
    set T := Sec4.thetaQuotCentralizer L with hT
    have hRH₁ : R ≤ H₁ := le_inf (Item1116Proof.le_centralizer_and_normalizer h45 h).1
      (Item1116Proof.le_centralizer_and_normalizer h45 h).2
    have hH₁H : H₁ ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      intro z hz
      have hzc := hz.1
      rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzc
      exact Subgroup.centralizer_le_normalizer _ hzc
    have hS₁ : IsSylowOf 3 R H₁ := h.isSylowOf.of_le hRH₁ hH₁H
    have hHN : H₁ ≤ Subgroup.normalizer ((H₁ ⊓ T : Subgroup G) : Set G) := fun z hz =>
      GroupTheory.SteinbergBY.mem_normalizer_inf (Subgroup.le_normalizer hz)
        (Item1119StepsProof.normalizer_le_normalizer_thetaQuotCentralizer L hz.2)
    have hS₂ := hS₁.inf_of_le_normalizer inf_le_left hHN
    have hec : e * c = c * e := Item1117Proof.commute_of_mem_A h heA h.mem_A
    have htcC : Commute t c := htc
    have hecC : Commute e c := hec
    have hyc : t * e ^ i * c = c * (t * e ^ i) := (htcC.mul_left (hecC.pow_left i)).eq
    have hyN : t * e ^ i ∈ H₁ ⊓ T :=
      ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr hyc,
        Subgroup.mul_mem _ htL (Subgroup.pow_mem _ heN i)⟩, hi⟩
    have hy3 : (t * e ^ i) ^ 3 ^ (k + 1) = 1 := by
      have hteC : Commute t e := hte
      rw [(hteC.pow_right i).mul_pow, pow_succ, pow_mul, htk, one_pow, one_mul,
        ← pow_mul, show i * (3 ^ k * 3) = 3 * (i * 3 ^ k) by ring, pow_mul, he3, one_pow]
    obtain ⟨m, hm, hmy⟩ := exists_conj_mem_of_isSylowOf hS₂ hyN hy3
    have hus : m * (t * e ^ i) * m⁻¹ ∈ Subgroup.zpowers s := by
      rw [← h.inf_centralizer_eq]
      exact ⟨hmy.1, hmy.2.2⟩
    have hu1 : m * (t * e ^ i) * m⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      have e1 : t * e ^ i = m⁻¹ * (m * (t * e ^ i) * m⁻¹) * m := by group
      rw [e1, h1]
      group
    have hcu := Item1119StepsProof.mem_zpowers_c_of_mem_zpowers_s h hus hu1
    have hmc : m * c = c * m := Subgroup.mem_centralizer_singleton_iff.mp hm.1.1
    have hcy : c ∈ Subgroup.zpowers (t * e ^ i) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcu
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [conj_zpow] at hn
      calc (t * e ^ i) ^ n = m⁻¹ * (m * (t * e ^ i) ^ n * m⁻¹) * m := by group
        _ = m⁻¹ * c * m := by rw [hn]
        _ = c := by rw [mul_assoc, ← hmc, ← mul_assoc, inv_mul_cancel, one_mul]
    have heY := Item1119StepsProof.a_mem_thetaQuotCentralizer_Y hstdE
    have hyY : t * e ^ i ∈ Sec4.thetaQuotCentralizer Ye :=
      Subgroup.mul_mem _ htY (Subgroup.pow_mem _ heY i)
    have hcY : c ∈ Sec4.thetaQuotCentralizer Ye := Subgroup.zpowers_le.mpr hyY hcy
    have hsec := Item1119StepsProof.mem_sectionCentralizer_of_mem_thetaQuotCentralizer h.mem_A hcY
    rw [hstd.sectionCentralizer_eq] at hsec
    exact hce hsec
  have ht : t = (e ^ i)⁻¹ := eq_inv_of_mul_eq_one_left hy1
  rw [ht]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) i)

theorem forall_commutator_mem_of_swap (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h119 : Item119)
    (h : Sec11Data G A c L a R Y d x s r g) {e : G} (heA : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) {Ye R' Y'' : Subgroup G}
    (hYe : Ye ∈ thetaComponentsAt 3 e) (hKYe : sec11K L e ≤ Ye)
    (hstd : Sec11Std G A e Ye c R' Y'') :
    ∀ w ∈ R', ∀ y ∈ A, w * y * w⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a', Y', d', x', s', r', g', h'⟩ :=
    sec11DataExists_of h97 h45 h113 h117 h119 G A e Ye c R' Y'' hstd
  have hAYe := Item1117StepsProof.inf_eq_zpowers_d_swap h45 h97 h heA hecd hYe hKYe hstd
  have hdd' : Subgroup.zpowers d' = Subgroup.zpowers d := h'.inf_eq.symm.trans hAYe
  have hd'3 : orderOf d' = 3 := Item1117Proof.orderOf_d h'
  obtain ⟨hr'R, hx'R, hs'R⟩ := Item1116Proof.mem_R h'
  have hR'e := Item1117Proof.R_le_centralizer_c h'
  have hR'Ye := (Item1116Proof.le_centralizer_and_normalizer h45 h').2
  have hR'W : R' ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_eq_closure (h113 G A e Ye c R' Y'' hstd).1
  have hWd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := Item1115Proof.W_le_normalizer_d h117 h
  have hs'a' : s' * a' = a' * s' :=
    item1115_of_mhoV h45 h113 h117 G A e Ye a' R' Y' d' x' s' r' g' h'
  have hs'e : s' * e = e * s' := Subgroup.mem_centralizer_singleton_iff.mp (hR'e hs'R)
  have hs'd' : d' * s' = s' * d' := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Item1117Proof.d_mem_zpowers_x h')
    rw [← hj]
    have hsx : Commute s' x' := h'.commute_s_x
    exact ((Commute.zpow_right hsx j).symm).eq
  have hs'A : ∀ y ∈ A, y * s' = s' * y := by
    intro y hy
    rw [h'.closure_eq] at hy
    refine forall_commute_of_closure ?_ y hy
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hs'e.symm
    · exact hs'a'.symm
    · exact hs'd'
  have hs'Y : s' ∈ Sec4.thetaQuotCentralizer Ye := by
    have hmem : s' ∈ R' ⊓ Sec4.thetaQuotCentralizer Ye := by
      rw [h'.inf_centralizer_eq]
      exact Subgroup.mem_zpowers s'
    exact hmem.2
  have hs'z : s' ∈ Subgroup.zpowers e :=
    mem_zpowers_of_mem_swap h45 h heA hecd hYe hKYe hstd hs'R (hs'A c h.mem_A).symm hs'Y
  have hr'e : r' * e = e * r' := Subgroup.mem_centralizer_singleton_iff.mp (hR'e hr'R)
  have hr's' : s' * r' = r' * s' := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hs'z
    rw [← hj]
    have her : Commute e r' := hr'e.symm
    exact (Commute.zpow_left her j).eq
  have hr'a' : a' * r' = r' * a' := by
    refine forall_commute_of_closure ?_ a' h'.a_mem_closure
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · rfl
    · exact hr's'
  have hr'd' : d' * r' = r' * d' := by
    have hd'AY : d' ∈ A ⊓ Ye := by
      rw [h'.inf_eq]
      exact Subgroup.mem_zpowers d'
    have hconj : r' * d' * r'⁻¹ ∈ A ⊓ Ye :=
      (Subgroup.mem_normalizer_iff.mp
        (GroupTheory.SteinbergBY.mem_normalizer_inf (hR'W hr'R) (hR'Ye hr'R)) d').mp hd'AY
    rw [h'.inf_eq] at hconj
    obtain ⟨n, hn⟩ := hstd.isSylowOf.isPGroup ⟨r', hr'R⟩
    have hr'n : r' ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact (Sec12.commute_of_conj_mem_zpowers hd'3 hconj hr'n).symm
  have hr'A : ∀ y ∈ A, y * r' = r' * y := by
    intro y hy
    rw [h'.closure_eq] at hy
    refine forall_commute_of_closure ?_ y hy
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hr'e.symm
    · exact hr'a'
    · exact hr'd'
  have hgen : ∀ t ∈ ({r', x', s'} : Set G), ∀ y ∈ A,
      t * y * t⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
    intro t ht y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · rw [← hr'A y hy, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨z, hz, hzy⟩ := Item1117Proof.exists_conj_of_mem_A h' hy
      have hzA : z ∈ A := Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_A h') hz
      rw [hzy, Item1117Proof.commute_of_mem_A h' hy hzA, mul_inv_cancel_right, ← hdd']
      exact hz
    · rw [← hs'A y hy, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hR'act := forall_commutator_mem_of_closure (h'.R_eq ▸ hR'W) (h'.R_eq ▸ hR'W.trans hWd) hgen
  intro w hw
  exact hR'act w (h'.R_eq ▸ hw)

end Data

end Item1117Res5Proof

section Main

open Item1117Res5Proof in
theorem gap1117SwapSylowW_holds (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) : Gap1117SwapSylowW := by
  intro G _ _ A c L a R Y d x s r g h _hsc _hrs heA hecd _hsym Ye R' Y'' hYe hKYe hstd _hx9 _hf
    _hbig w hw hw3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := g * x * g⁻¹ * x⁻¹ with he
  have hR'act := forall_commutator_mem_of_swap h45 h97 h113 h117 h119 h heA hecd hYe hKYe hstd
  have hWd : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := Item1115Proof.W_le_normalizer_d h117 h
  obtain ⟨n, hn⟩ := hw3
  obtain ⟨k, hk, hkw⟩ := exists_conj_mem_of_isSylowOf hstd.isSylowOf_inf hw hn
  have hkA : k ∈ Subgroup.normalizer (A : Set G) := hk.2
  have hc₀ : k * c * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hkA c).mp h.mem_A
  have hinner := hR'act _ hkw.1 _ hc₀
  have e1 : w * c * w⁻¹ * c⁻¹ = k⁻¹ * ((k * w * k⁻¹) * (k * c * k⁻¹) * (k * w * k⁻¹)⁻¹ *
      (k * c * k⁻¹)⁻¹) * k⁻¹⁻¹ := by group
  rw [e1]
  exact (Subgroup.mem_normalizer_iff.mp (inv_mem (hWd hkA)) _).mp hinner

theorem item1117_of_res5 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h97 : Sec9.Item97)
    (h113 : Item113) (h117 : Item117) (h118 : Item118) (h119 : Item119) (h82 : Sec8.Item82One)
    (h1016 : Sec10.Item1016) (h1116 : Item1116) (hG2 : KFact1117CubeG2)
    (hL3 : KFact1117CubeL3) (hN : Gap1117NotActXNormal) : Item1117 :=
  item1117_of_res_W h45 h48 h97 h113 h117 h118 h119 h82 h1016 h1116 hG2 hL3 hN
    (gap1117SwapSylowW_holds h45 h97 h113 h117 h119)

end Main

end CFSG.RankThree.PartTwo.Sec11
