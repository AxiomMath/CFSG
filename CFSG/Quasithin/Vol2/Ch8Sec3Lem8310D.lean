module

public import CFSG.Quasithin.Background.HL3WrV5
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts15420Proof
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837B
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837E
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative commutatorElement

namespace Ch8310

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem statedClassicalModel_psl25_of_sl24 {Q : Type} [Group Q]
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 5 1 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hc : Fintype.card F = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e54⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
  exact CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv Q 5 1 (by norm_num)
    (((e.trans (sl2MapEquiv (FiniteField.ringEquivOfCardEq hc))).trans
      (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 2)).symm).trans e54.symm)

theorem pow_mem_centralizer_of_not_three_dvd (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I) {z : G} (hz1 : z ≠ 1)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {y : G}
    (hyM : y ∈ fsuM T L) (hyz : y ∈ Subgroup.centralizer ({z} : Set G))
    (hy3 : ¬ 3 ∣ orderOf y) :
    y ^ 2 ^ 7 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨e, he, -, -, hz, hez⟩ := Ch837.exists_model_eW00_T hyp hV hrow hz1 hzV
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    have h1 : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      le_normalizer_conjClosure (fsuV T I) (fsuM T L)
    rwa [← hVVM] at h1
  have hKN : fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := inf_le_left.trans hMV
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
  set act := Ch837.actOn hV e hKN with hact
  have hstab : ∀ k : ↥(fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)), act k ∈ stabE := by
    intro k
    refine mem_stabE_iff.2 ⟨congrHom_mem_norm e he (convI_mem_normalizer_autI hV k.2.1), ?_⟩
    rw [Ch837.actOn_apply]
    change e (convI hV ⟨k, hKN k.2⟩ (e.symm (eW 0 0))) = eW 0 0
    rw [hezs, ← hez]
    congr 1
    apply IntMod.val_injective
    rw [convI_apply_val]
    change (k : G) * z * (k : G)⁻¹ = z
    rw [(Subgroup.mem_centralizer_iff.mp k.2.2 z rfl).symm, mul_inv_cancel_right]
  set ι := act.codRestrict stabE hstab with hι
  set k : ↥(fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) := ⟨y, hyM, hyz⟩ with hk
  have hd1 : orderOf (ι k) ∣ orderOf y := by
    have h := orderOf_map_dvd ι k
    rwa [← Subgroup.orderOf_coe k] at h
  have hd2 : orderOf (ι k) ∣ 2 ^ 7 * 3 ^ 2 := L3Wr.card_stabE ▸ orderOf_dvd_natCard (ι k)
  have hd3 : ¬ 3 ∣ orderOf (ι k) := fun h => hy3 (h.trans hd1)
  have hcop : Nat.Coprime (orderOf (ι k)) (3 ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hd3).symm
  have hpow : ι (k ^ 2 ^ 7) = 1 := by
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hd2)
  have h2 : act (k ^ 2 ^ 7) = 1 := congrArg Subtype.val hpow
  rw [Ch837.actOn_apply] at h2
  have h3 := (convI_eq_one_iff hV _).1 (congrHom_injective e (h2.trans (map_one _).symm))
  simpa [hk] using h3

omit [Finite G] in
theorem mem_pCoreOf_of_forall_commutator_mem {K : Subgroup G}
    (hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) {k : G} (hk : k ∈ K)
    (h : ∀ a ∈ K, k * a * k⁻¹ * a⁻¹ ∈ pCoreOf 2 K) : k ∈ pCoreOf 2 K := by
  have hz : ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    have hcomm : ((⁅(⟨k, hk⟩ : ↥K), a⁆ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      refine (Vol2.Ch10.SecA.mk_eq_one_iff _).mpr ?_
      simpa [commutatorElement_def] using h a a.2
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at hcomm
    exact hcomm.symm
  rw [hc, Subgroup.mem_bot] at hz
  exact (Vol2.Ch10.SecA.mk_eq_one_iff _).mp hz

theorem mem_pCoreOf_of_commutator_mem_pair {K K' Kz : Subgroup G} (hKz : Kz = K ⊔ K')
    (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K ⊓ pCoreOf 2 K')
    (hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hc' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥) {x : G} (hx : x ∈ Kz)
    (h : ∀ y ∈ Kz, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 Kz) : x ∈ pCoreOf 2 Kz := by
  subst hKz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm' : ⁅K', K⁆ ≤ pCoreOf 2 K' := by
    rw [Subgroup.commutator_comm]
    exact hcomm.trans inf_le_right
  have hK'NK : K' ≤ Subgroup.normalizer (K : Set G) := Ch837.le_normalizer_of_commutator_le
    (hcomm.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)))
  have hKNK' : K ≤ Subgroup.normalizer (K' : Set G) :=
    Ch837.le_normalizer_of_commutator_le (hcomm'.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K'))
  have hON : K ⊔ K' ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ K') : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hO₁ : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ K') :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
        (hK'NK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hO₂ : pCoreOf 2 K' ≤ pCoreOf 2 (K ⊔ K') :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans le_sup_right)
      (sup_le (hKNK'.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K'))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K'))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K')
  have hKinf : K ⊓ pCoreOf 2 (K ⊔ K') ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, hON (Subgroup.mem_sup_left hg)⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have hK'inf : K' ⊓ pCoreOf 2 (K ⊔ K') ≤ pCoreOf 2 K' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, hON (Subgroup.mem_sup_right hg)⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have hx' : x ∈ ((K ⊔ K' : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K K' hKNK'] at hx'
  obtain ⟨k, hk, k', hk', rfl⟩ := hx'
  have hkO : k ∈ pCoreOf 2 K := by
    refine mem_pCoreOf_of_forall_commutator_mem hc hk fun a ha => hKinf ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.mul_mem hk ha) (K.inv_mem hk)) (K.inv_mem ha)
    · have hc1 : k' * a * k'⁻¹ * a⁻¹ ∈ pCoreOf 2 K := by
        have h1 : ⁅k', a⁆ ∈ ⁅K', K⁆ := Subgroup.commutator_mem_commutator hk' ha
        rw [Subgroup.commutator_comm] at h1
        exact (hcomm h1).1
      have hc2 : k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).mp hc1
      have e : k * a * k⁻¹ * a⁻¹ = (k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹)⁻¹ *
          (a * (k * k') * a⁻¹ * (k * k')⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 (K ⊔ K')).mul_mem ((pCoreOf 2 (K ⊔ K')).inv_mem (hO₁ hc2))
        ((pCoreOf 2 (K ⊔ K')).inv_mem (h a (Subgroup.mem_sup_left ha)))
  have hk'O : k' ∈ pCoreOf 2 K' := by
    refine mem_pCoreOf_of_forall_commutator_mem hc' hk' fun b hb => hK'inf ⟨?_, ?_⟩
    · exact K'.mul_mem (K'.mul_mem (K'.mul_mem hk' hb) (K'.inv_mem hk')) (K'.inv_mem hb)
    · have hb' : k' * b * k'⁻¹ ∈ K' := K'.mul_mem (K'.mul_mem hk' hb) (K'.inv_mem hk')
      have hd : k * (k' * b * k'⁻¹) * k⁻¹ * (k' * b * k'⁻¹)⁻¹ ∈ pCoreOf 2 K' :=
        (hcomm (Subgroup.commutator_mem_commutator hk hb')).2
      have e : k' * b * k'⁻¹ * b⁻¹ =
          (k * (k' * b * k'⁻¹) * k⁻¹ * (k' * b * k'⁻¹)⁻¹)⁻¹ *
            (b * (k * k') * b⁻¹ * (k * k')⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 (K ⊔ K')).mul_mem ((pCoreOf 2 (K ⊔ K')).inv_mem (hO₂ hd))
        ((pCoreOf 2 (K ⊔ K')).inv_mem (h b (Subgroup.mem_sup_right hb)))
  exact (pCoreOf 2 (K ⊔ K')).mul_mem (hO₁ hkO) (hO₂ hk'O)

theorem isElemAbelian_of_isXi {T X P : Subgroup G} (hXi : IsXi T X) (hP : IsSylowIn 3 P X)
    (hPc : Nat.card P = 9) : IsElemAbelian 3 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, p, hp, -, hpow, -, -⟩ := hXi
  have hPc' : Nat.card P = 3 ^ 2 := by rw [hPc]; norm_num
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hPc', fun x hx => ?_⟩
  have h1 : x ^ p = 1 := by
    have hd := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 X) hP.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    exact Subgroup.disjoint_def.mp hd (P.pow_mem hx p) (hpow x (hP.le hx))
  have hd : orderOf x ∣ Nat.gcd 9 p :=
    Nat.dvd_gcd (hPc ▸ Subgroup.orderOf_dvd_natCard P hx) (orderOf_dvd_of_pow_eq_one h1)
  have hg : Nat.gcd 9 p ∣ 3 := by
    rcases Nat.coprime_or_dvd_of_prime Nat.prime_three p with hcop | h3p
    · have h9 : Nat.Coprime 9 p := by
        have := Nat.Coprime.pow_left 2 hcop
        norm_num at this
        exact this
      rw [h9]
      exact one_dvd _
    · have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
      subst hp3
      norm_num
  exact orderOf_dvd_iff_pow_eq_one.mp (hd.trans hg)

end Ch8310

open Ch8310 in
theorem claim8310Gz_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight) (h326 : Stmt3_2_6C)
    (h837 : Stmt8_3_7) (hOut : KG838Out) : Claim8310Gz := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV hK1 hH hB
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hyp.fsu.simple
  obtain ⟨K, s, hsT, hsN, hKC, hKz, F, _, _, hF, ⟨eF⟩⟩ := hK1
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hsGz : s ∈ Subgroup.centralizer ({z} : Set G) := hTz hsT
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hL0M : fsuL0 T L ≤ fsuM T L := Subgroup.le_normalizer
  have hXL0 : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hXM : ch83X T L z ≤ fsuM T L := hXL0.trans hL0M
  have hXKz : ch83X T L z ≤ ch83Kz T L z := le_conjClosure _ _
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    conjClosure_le fun h hh x hx =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hTX := Ch837.le_normalizer_ch83X (L := L) hTz
  have hres : twoResidual (ch83X T L z) = ch83X T L z :=
    twoResidual_twoResidual (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G))
  have hTGz : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
    Ch837.isSylowTwoOf_of_le hyp.fsu.sylow hTz
  have hTsyl : IsSylowIn 2 T (Subgroup.centralizer ({z} : Set G)) :=
    ⟨hTz, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTz))⟩
  have hKzM : ¬ ch83Kz T L z ≤ fsuM T L := fun h => hH.2.1 (sup_le h hTM)
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    Ch837.zpowers_le_pCoreOf hz2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl) le_rfl
  have hPGz : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ : IsSQTKIn (Subgroup.centralizer ({z} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPGz
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
  have hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)) := mem_cComp_iff.mpr hKC
  set K' := CFSG.conjugate K s with hK'def
  have hK'eq : conjByElt s⁻¹ K = K' := by
    rw [hK'def, Ch837.conjByElt_eq_conjugate, inv_inv]
  have hK'c : K' ∈ cComp (Subgroup.centralizer ({z} : Set G)) :=
    conjSub_mem_cComp_of_mem hKc (Subgroup.inv_mem _ hsGz)
  have hne : K ≠ K' := fun h => hsN (by
    have h1 : conjByElt s⁻¹ K = K := hK'eq.trans h.symm
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem (A38.map_conj_eq_iff.mp h1))
  have hcommKK' := (Vol2Native.lemma_1_2_1_two hKl h37 hPGz hKc hK'c hne).1
  have hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 5 1 :=
    statedClassicalModel_psl25_of_sl24 hF eF
  obtain ⟨eK⟩ := Ch837.nonempty_quot_conjugate_equiv K s
  have hmod' : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K' ⧸ CFSG.pCore 2 ↥K') .PSL 2 5 1 :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv eK.symm hmod
  have hcen := EmptyFaithfulMultiple.facts15420_centerPSL _ 2 5 1 hmod
  have hcen' := EmptyFaithfulMultiple.facts15420_centerPSL _ 2 5 1 hmod'
  obtain ⟨horb, hcase⟩ := hA3 _ T K hSQ hTGz hKc
  have hpair : conjSubgroupsBy (Subgroup.centralizer ({z} : Set G)) K = {K, K'} := by
    rcases hcase with hnorm | ⟨t, -, -, hp, -⟩
    · exact absurd (hnorm s hsT) hsN
    · rw [horb, hp]
      have hmem : conjByElt s⁻¹ K ∈ conjSubgroupsBy T K := ⟨s⁻¹, T.inv_mem hsT, rfl⟩
      rw [hp] at hmem
      rcases hmem with h | h
      · exact absurd (h.symm.trans hK'eq) hne
      · have h' : conjByElt s⁻¹ K = conjByElt t K := h
        rw [← h', hK'eq]
  have hperm : ∀ g ∈ Subgroup.centralizer ({z} : Set G),
      (conjByElt g K = K ∨ conjByElt g K = K') ∧
        (conjByElt g K' = K ∨ conjByElt g K' = K') := by
    intro g hg
    have hmem : ∀ y ∈ Subgroup.centralizer ({z} : Set G),
        conjByElt y K = K ∨ conjByElt y K = K' := by
      intro y hy
      have h1 : conjByElt y K ∈ conjSubgroupsBy (Subgroup.centralizer ({z} : Set G)) K :=
        ⟨y, hy, rfl⟩
      rw [hpair] at h1
      exact h1
    have e : conjByElt g K' = conjByElt (g * s⁻¹) K := by
      rw [← hK'eq]
      unfold conjByElt
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    exact ⟨hmem g hg, e ▸ hmem _ (Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hsGz))⟩
  have hKz' : ch83Kz T L z = K ⊔ K' := hKz
  have hpow := Ch837.pow_mem_of_pair (le_of_mem_cComp hKc) (le_of_mem_cComp hK'c)
    (hKz' ▸ hGzKz) hcommKK' (hOut.1 _ 5 hmod) (hOut.1 _ 5 hmod')
    (fun g hg => Ch837.sq_mem_normalizer_of_pair hne hperm hg)
  rw [← hKz'] at hpow
  set C := centralizerSection (Subgroup.centralizer ({z} : Set G)) (ch83Kz T L z)
    (pCoreOf 2 (ch83Kz T L z)) with hCdef
  have hCGz : C ≤ Subgroup.centralizer ({z} : Set G) := centralizerSection_le_left _ _ _
  have hGzC : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    fun g hg => le_normalizer_centralizerSection _ _ ⟨hg, hGzKz hg⟩
  have hsup := B6.sup_eq_of_isTwoQuotient (sup_le hKzGz hCGz)
    (Vol2.Ch10.SecA.le_normalizer_sup hGzKz hGzC) hpow hTGz
  by_cases hY : twoResidual C = ⊥
  ·
    have hC2 : IsPGroup 2 C := CFSG.Quasithin.H.twoResidual_eq_bot_iff.mp hY
    have hCT : C ≤ T :=
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCGz hGzC hC2).trans
        (B6.pCoreOf_two_le_of_isSylowTwoOf hTGz)
    refine le_antisymm ?_ (sup_le hKzGz hTz)
    calc Subgroup.centralizer ({z} : Set G) = ch83Kz T L z ⊔ C ⊔ T := hsup.symm
      _ ≤ ch83Kz T L z ⊔ T := sup_le (sup_le le_sup_left (hCT.trans le_sup_right)) le_sup_right
  exfalso
  obtain ⟨hGz, -⟩ := h837 G T L I hyp h731 hc hrow z hz2 hzV
  have hMzN : fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := inf_le_right.trans hGzKz
  have hMzX : fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83X T L z : Set G) := fun m hm => by
    have h1 : m ∈ Subgroup.normalizer
        ((fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf hm.1 (Subgroup.le_normalizer hm.2)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [ch83X, E1.map_twoResidual, h1]
  have hOKz : pCoreOf 2 (ch83Kz T L z) ≤ Subgroup.normalizer (ch83X T L z : Set G) := by
    refine le_trans ?_ hTX
    refine le_trans ?_ (B6.pCoreOf_two_le_of_isSylowTwoOf hTGz)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKzGz)
      (hGzKz.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  obtain ⟨e, he, hz, hez⟩ := exists_model_eW00 hyp hV hrow hz1 hzV
  have hA5 : Nonempty (OTwoQuot K ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e₅⟩ := Ch8310.a5_of_psl25 hmod
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥K).symm).trans
      e₅⟩
  have hBM : ch83X T L z ⊔ (T ⊓ ch83Kz T L z) ≤ fsuM T L :=
    sup_le hXM (inf_le_left.trans hTM)
  obtain ⟨hdich, -, -⟩ := Ch8310.borel_setting hKc hTsyl hsT hsN hKz hGzKz hA5 hXKz (hTX hsT)
    (Ch8310.nine_dvd_card_ch83X hV hN e he hz hez) fun h => hKzM (h.trans hBM)
  have hCM : C ≤ fsuM T L := by
    intro c hcC
    have hc' := hCGz hcC
    rw [hGz] at hc'
    have hc'' : c ∈ ((ch83Kz T L z ⊔ (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) :
        Subgroup G) : Set G) := hc'
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hMzN] at hc''
    obtain ⟨k, hk, m, hm, rfl⟩ := hc''
    have hcX : k * m ∈ Subgroup.normalizer (ch83X T L z : Set G) :=
      Ch837.mem_normalizer_of_mem_centralizerSection hXKz hres hOKz hcC
    have hkX : k ∈ Subgroup.normalizer (ch83X T L z : Set G) := by
      have h1 := (Subgroup.normalizer (ch83X T L z : Set G)).mul_mem hcX
        ((Subgroup.normalizer (ch83X T L z : Set G)).inv_mem (hMzX hm))
      simpa using h1
    have hsY : s ∈ Subgroup.normalizer ((ch83Kz T L z ⊓
        Subgroup.normalizer (ch83X T L z : Set G) : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf (hGzKz hsGz) (Subgroup.le_normalizer (hTX hsT))
    rcases hdich _ (le_inf inf_le_right (inf_le_left.trans hTX)) inf_le_left hsY with h | h
    ·
      exfalso
      have hGzX : Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (ch83X T L z : Set G) := by
        rw [hGz]
        exact sup_le (h.trans inf_le_right) hMzX
      exact hKzM ((conjClosure_le fun g hg x hx =>
        (Subgroup.mem_normalizer_iff.mp (hGzX hg) x).mp hx).trans hXM)
    · exact (fsuM T L).mul_mem (hBM (h ⟨hk, hkX⟩)) hm.1
  obtain ⟨-, -, hXi, -, P, hP, hPc, -⟩ := Ch837.xi_data h37 h38 h326 hyp hV hrow hN hz2 hzV
  have hPe : IsElemAbelian 3 P := isElemAbelian_of_isXi hXi hP hPc
  have hPKz : P ≤ ch83Kz T L z := hP.le.trans hXKz
  have hPC : P ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxC⟩
    have hxO : x ∈ pCoreOf 2 (ch83Kz T L z) :=
      mem_pCoreOf_of_commutator_mem_pair hKz' hcommKK' hcen hcen' (hPKz hxP) hxC.2.2.2
    have hd := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 (ch83Kz T L z))
      hP.isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hd hxP hxO)
  have hPGz' : P ≤ Subgroup.centralizer ({z} : Set G) := hPKz.trans hKzGz
  have hC3 : ¬ 3 ∣ Nat.card C :=
    not_dvd_card_of_elemAbelian_sq_normalizes
      (fun q hq hq2 => pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hPGz hq hq2)
      (by norm_num) hPGz' hPe (by rw [hPc]; norm_num) hCGz (hPGz'.trans hGzC) hPC
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    have h1 : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      le_normalizer_conjClosure (fsuV T I) (fsuM T L)
    rwa [← hVVM] at h1
  have hYV : twoResidual C ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    refine (twoResidual_le_of_isTwoQuotient
      (N := C ⊓ Subgroup.centralizer (fsuV T I : Set G)) inf_le_left ?_ ?_).trans inf_le_right
    · intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        normalizer_le_normalizer_centralizer _ (hMV (hCM hg))⟩
    · intro y hy
      refine ⟨7, C.pow_mem hy _, pow_mem_centralizer_of_not_three_dvd h326 hyp hV hrow hz1 hzV
        (hCM hy) (hCGz hy) fun h3 => hC3 (h3.trans (Subgroup.orderOf_dvd_natCard C hy))⟩
  have hNY : ∀ g ∈ Subgroup.normalizer (C : Set G),
      g ∈ Subgroup.normalizer (twoResidual C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    rw [E1.map_twoResidual, hg]
  have hnn : ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hT => hrow.1.ne
    (le_antisymm (Vol2.Ch10.SecA.le_fsuL0 T L) (conjClosure_le fun s hs l hl =>
      (Subgroup.mem_normalizer_iff.mp (hT hs) l).mp hl))
  have hCL0 : fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [hVVM]
    exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37 h38 hyp.fsu hnn
  have hO0T : pCoreOf 2 (fsuL0 T L) ≤ T :=
    (Vol2.Ch10.SecA.pCoreOf_fsuL0_le_T0 hyp.fsu.sylow).trans inf_le_left
  have hTY : T ≤ Subgroup.normalizer (twoResidual C : Set G) := fun t ht => hNY t (hGzC (hTz ht))
  have hRY : twoResidual C ⊔ pCoreOf 2 (fsuL0 T L) ≤
      Subgroup.normalizer (twoResidual C : Set G) :=
    sup_le Subgroup.le_normalizer (hO0T.trans hTY)
  have hRres : twoResidual (twoResidual C ⊔ pCoreOf 2 (fsuL0 T L)) = twoResidual C := by
    apply le_antisymm
    · exact twoResidual_le_of_isTwoQuotient le_sup_left hRY
        (B6.isTwoQuotient_of_sup_eq (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hRY
          (sup_comm _ _))
    · calc twoResidual C = twoResidual (twoResidual C) := (twoResidual_twoResidual C).symm
        _ ≤ twoResidual (twoResidual C ⊔ pCoreOf 2 (fsuL0 T L)) := F6.twoResidual_mono le_sup_left
  have hL0N : fsuL0 T L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hN
  have key : ∀ l ∈ fsuL0 T L, twoResidual C ⊔ pCoreOf 2 (fsuL0 T L) ≤
      (twoResidual C ⊔ pCoreOf 2 (fsuL0 T L)).comap (MulAut.conj l).toMonoidHom := by
    intro l hl
    refine sup_le (fun y hy => ?_) (fun o ho => ?_)
    · change l * y * l⁻¹ ∈ twoResidual C ⊔ pCoreOf 2 (fsuL0 T L)
      have hyM : y ∈ fsuM T L := hCM (twoResidual_le C hy)
      have h1 : l * y * l⁻¹ * y⁻¹ ∈ fsuL0 T L := by
        have h2 : y * l⁻¹ * y⁻¹ ∈ fsuL0 T L :=
          (Subgroup.mem_normalizer_iff.mp hyM l⁻¹).mp ((fsuL0 T L).inv_mem hl)
        have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
        rw [e]
        exact (fsuL0 T L).mul_mem hl h2
      have h2 : l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
        refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (hYV hy))
        exact (Subgroup.mem_normalizer_iff.mp
          (normalizer_le_normalizer_centralizer _ (hL0N hl)) y).mp (hYV hy)
      have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hCL0 ⟨h1, h2⟩)) (Subgroup.mem_sup_left hy)
    · change l * o * l⁻¹ ∈ twoResidual C ⊔ pCoreOf 2 (fsuL0 T L)
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hl) o).mp ho)
  have hL0Y : fsuL0 T L ≤ Subgroup.normalizer (twoResidual C : Set G) := by
    intro l hl
    have hR : l ∈ Subgroup.normalizer
        ((twoResidual C ⊔ pCoreOf 2 (fsuL0 T L) : Subgroup G) : Set G) :=
      B6.mem_normalizer_of_forall_mem (fun r hr => key l hl hr) (fun r hr => by
        have := key l⁻¹ ((fsuL0 T L).inv_mem hl) hr
        simpa using this)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hR ⊢
    rw [← hRres, E1.map_twoResidual, hR]
  have hchar : CharTwo (Subgroup.centralizer ({z} : Set G)) :=
    charTwo_of_inH' hyp.fsu.qtke hyp.fsu.sylow ⟨hTz, hPGz⟩
  have hYGz : twoResidual C ≤ Subgroup.centralizer ({z} : Set G) := (twoResidual_le C).trans hCGz
  have hGzY : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (twoResidual C : Set G) :=
    fun g hg => hNY g (hGzC hg)
  have hOY : pCoreOf 2 (twoResidual C) ≠ ⊥ :=
    pCoreOf_ne_bot_of_charTwo (A4.charTwo_of_normal hYGz hGzY hchar) hY
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian
    (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38) (a39ForSQTK_of_cat h39) hyp.fsu.sylow
    hyp.fsu.maximal
  have hNR : Subgroup.normalizer (twoResidual C : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (twoResidual C) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (twoResidual C) : Set G) :=
    sup_le ((Vol2.Ch10.SecA.le_fsuL0 T L).trans (hL0Y.trans hNR)) (hTY.trans hNR)
  have hO2N : pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (twoResidual C) : Set G)) ≠ ⊥ := by
    intro h
    apply hOY
    have h1 : pCoreOf 2 (twoResidual C) ≤
        pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (twoResidual C) : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    rw [h] at h1
    exact le_bot_iff.mp h1
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO2N
  have hM'eq := hU.2 M' ⟨hM'.1, hLT.trans hM'.2⟩
  have hNM : Subgroup.normalizer (pCoreOf 2 (twoResidual C) : Set G) ≤ fsuM T L := fun g hg => by
    have h1 := hM'.2 hg
    rw [hM'eq] at h1
    exact h1
  exact hKzM (hKzGz.trans (hGzY.trans (hNR.trans hNM)))

end CFSG.Quasithin.H13
