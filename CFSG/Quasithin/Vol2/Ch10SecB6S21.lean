module

public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Vol2.Ch10SecB6C23
public import CFSG.Quasithin.Vol2.Ch10SecB6QS

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isSolvable_oTwoFIn' (H : Subgroup G) : Group.IsSolvable ↥(oTwoFIn H) := by
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hF
  set P : Subgroup ↥H := F.comap π with hP
  have hKP : CFSG.pCore 2 ↥H ≤ P := fun k hk => by
    show π k ∈ F
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact F.one_mem
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup (G := ↥H) (p := 2)
  have hKn : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) := hp.isNilpotent
  have hFs : Group.IsSolvable ↥F := inferInstance
  have hKs : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := inferInstance
  let f : ↥(CFSG.pCore 2 ↥H) →* ↥P := Subgroup.inclusion hKP
  let g : ↥P →* ↥F := (π.comp P.subtype).codRestrict F (fun x => x.2)
  have hker : g.ker ≤ f.range := by
    intro x hx
    have h1 : π (x : ↥H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, h2⟩, rfl⟩
  have hPs : Group.IsSolvable ↥P := Group.isSolvable_of_ker_le_range f g hker
  have hsurj : Function.Surjective
      (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).toMonoidHom :=
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).surjective
  exact Group.isSolvable_of_surjective hsurj

theorem isSolvable_oTwoFIn_sup' {H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R) :
    Group.IsSolvable ↥(oTwoFIn H ⊔ R) := by
  have hN : R ≤ Subgroup.normalizer (oTwoFIn H : Set G) := hRH.trans C2Six.le_normalizer_oTwoFIn
  have : Group.IsSolvable ↥(oTwoFIn H) := isSolvable_oTwoFIn' H
  have hRn : Group.IsNilpotent ↥R := hR.isNilpotent
  have : Group.IsSolvable ↥R := inferInstance
  exact A3.isSolvable_sup_of_le_normalizer hN

theorem c2_6_two' {H R M : Subgroup G} (h : HypC23 H R M) (hF : CharTwo (oTwoFIn H)) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G),
      (∀ i, IsBlock2 (oTwoFIn H) (Lb i) ∧ IsAltType (Lb i) 3) ∧
      ∀ x ∈ oTwoFIn H, ∃ m ∈ M ⊓ oTwoFIn H, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
        x = m * (List.ofFn y).prod := by
  have hRH : R ≤ H := h.radical.1
  have hRp : IsPGroup 2 R := h.radical.isPGroup
  have hXH : oTwoFIn H ⊔ R ≤ H := sup_le C2Six.oTwoFIn_le hRH
  have hYX : oTwoFIn H ≤ oTwoFIn H ⊔ R := le_sup_left
  have hcgs : cgsIn (oTwoFIn H ⊔ R) R ≤ M ⊓ (oTwoFIn H ⊔ R) :=
    le_inf ((C2Nine.cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le _ R)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := asc129StatementSolv G (oTwoFIn H ⊔ R) R
    (M ⊓ (oTwoFIn H ⊔ R)) (h.sqtk.mono hXH) (C2Six.charTwo_oTwoFIn_sup hRH hRp hF) (c2_6_one h)
    hcgs inf_le_right (isSolvable_oTwoFIn_sup' hRH hRp)
  have hLY : ∀ i, Lb i ≤ oTwoFIn H := fun i =>
    C2Six.le_oTwoFIn_of_isShort2 hRH hRp (hLb i).1.1.1 (hLb i).1.1.2.1
  refine ⟨r, Lb, fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨hchi, -, -⟩ := hLb i
    refine ⟨⟨hchi.1.1, hLY i, ?_⟩, C2Six.isAltType_three_of_isChi0Block hchi (hLY i)⟩
    have hsub : IsSubnormal (Lb i) (oTwoFIn H ⊔ R) := IsBlock2.isSubnormal hchi.1
    exact (isSubnormal_iff_subgroupOf (hLY i)).mp (A3.subnormal_of_le_of_le hsub (hLY i) hYX)
  · obtain ⟨m, hm, y, hy, hxy⟩ := hprod x (hYX hx)
    have hprodY : (List.ofFn y).prod ∈ oTwoFIn H := by
      refine Subgroup.list_prod_mem _ fun z hz => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hLY i (hy i)
    have hmY : m ∈ oTwoFIn H := by
      have : m = x * ((List.ofFn y).prod)⁻¹ := by rw [hxy]; group
      rw [this]
      exact (oTwoFIn H).mul_mem hx ((oTwoFIn H).inv_mem hprodY)
    exact ⟨m, ⟨hm.1, hmY⟩, y, hy, hxy⟩

theorem charTwo_oTwoFIn {H : Subgroup G} (hO : A37.oddCoreOf H = ⊥) : CharTwo (oTwoFIn H) := by
  set Y := oTwoFIn H with hYdef
  have hYH : Y ≤ H := C2Six.oTwoFIn_le
  have hYn : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr C2Six.le_normalizer_oTwoFIn
  have hOY : A37.oddCoreOf Y = ⊥ :=
    le_bot_iff.mp (hO ▸ A37.oddCoreOf_le_of_subnormal (A4.subnormal_of_normal hYH hYn))
  have hO' : CFSG.oddCore ↥Y = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hOY
  have hsol : Group.IsSolvable ↥Y := isSolvable_oTwoFIn' H
  have hE : CFSG.layer ↥Y = ⊥ := by
    refine sSup_eq_bot.mpr fun J hJ => ?_
    by_contra hJ1
    obtain ⟨hq, -⟩ := hJ
    obtain ⟨-, hs, a, b, hab⟩ := hq
    have : Group.IsSolvable ↥J := inferInstance
    have h2 : Group.IsSolvable (↥J ⧸ Subgroup.center ↥J) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr h2) a b)
  have hF : CFSG.generalizedFitting ↥Y ≤ CFSG.pCore 2 ↥Y := by
    rw [CFSG.generalizedFitting, hE, sup_bot_eq]
    refine (fittingSubgroup_le_pCore_sup_oddCore' ↥Y).trans ?_
    rw [hO', sup_bot_eq]
  intro x hx
  obtain ⟨hxY, hxC⟩ := hx
  have h1 : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ pCoreOf 2 Y := ⟨y, by exact hF hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hy')
  have h2 := hF (CFSG.centralizer_generalizedFitting_le ↥Y h1)
  exact ⟨_, by exact h2, rfl⟩

theorem hypC23_of_inM (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hS : IsSylowTwoOf (T1 T L) H) :
    HypC23 H (pCoreOf 2 (fsuL0 T L ⊔ T)) (fsuM T L ⊓ H) := by
  have h := hypC23Cat_of_inM hK h331 h37 h38 hyp hH hS
  exact ⟨G64.sqtkGroup_of_isSQTKCat h.sqtk, h.radical, h.le, h.cgs, h.sylow⟩

omit [Finite G] in
theorem exists_pow_eq_of_commute_coprime {X : Type*} [Group X] {x z : X} (hc : Commute x z)
    (hcop : (orderOf x).Coprime (orderOf z)) : ∃ k : ℕ, (x * z) ^ k = x := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨k, ?_⟩
  rw [hc.mul_pow, (pow_eq_pow_iff_modEq.mpr hk1 : x ^ k = x ^ 1),
    (pow_eq_pow_iff_modEq.mpr hk2 : z ^ k = z ^ 0), pow_one, pow_zero, mul_one]

theorem mk_pow_three_eq_one {H B : Subgroup G} (hB : IsBlock2 (oTwoFIn H) B)
    (h3 : IsAltType B 3) {y : G} (hy : y ∈ B) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨y, C2Six.oTwoFIn_le (hB.2.1 hy)⟩ : ↥H)) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBH : B ≤ H := hB.2.1.trans C2Six.oTwoFIn_le
  have hYn : ((oTwoFIn H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C2Six.oTwoFIn_le).mpr
      C2Six.le_normalizer_oTwoFIn
  have hsub : IsSubnormal B H := A4.subnormal_trans (IsBlock2.isSubnormal hB)
    (A4.subnormal_of_normal C2Six.oTwoFIn_le hYn)
  have hc := C2Six.natCard_pCore_quotient_of_isAltType_three h3
  have hn : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥B) (⟨y, hy⟩ : ↥B)) ^ 3 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 : y ^ 3 ∈ pCoreOf 2 B := by
    exact ⟨_, h1, rfl⟩
  have h3' := A4.pCoreOf_le_of_subnormal 2 hsub h2
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨z, hz, hzy⟩ := h3'
  have : z = (⟨y, hBH hy⟩ : ↥H) ^ 3 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hzy)
  rw [← this]
  exact hz

theorem mem_fsuM_of_coprime_three (hK : LocalSQTK G) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (hyp : Hyp10 G T L I) {H : Subgroup G} (hH : InM (fsuL0 T L ⊔ T1 T L) H)
    (hS : IsSylowTwoOf (T1 T L) H) {w : G} (hw : w ∈ oTwoFIn H)
    (hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (⟨w, C2Six.oTwoFIn_le hw⟩ : ↥H))).Coprime 3) : w ∈ fsuM T L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOH := oddCoreOf_eq_bot h37 h38 h331 h1011 hyp hH
  obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two' (hypC23_of_inM hK h331 h37 h38 hyp hH hS)
    (charTwo_oTwoFIn hOH)
  obtain ⟨m, hm, y, hy, hwy⟩ := hprod w hw
  have hO2M : pCoreOf 2 H ≤ fsuM T L :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS).trans (inf_le_left.trans (le_fsuM T L))
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
    have h3 := mk_pow_three_eq_one (hLb i).1 (hLb i).2 (hy i)
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
  obtain ⟨k, hk⟩ := exists_pow_eq_of_commute_coprime hc hcop'
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

theorem false_of_shape21 (hK : LocalSQTK G) (h36 : Vol2Native.A36CoreForSQTKCat)
    (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) {X H K : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) (hH : InM (fsuL0 T L ⊔ T1 T L) H)
    (hS : IsSylowTwoOf (T1 T L) H) (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K)
    (hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image H K))
    (h21 : modO2Image H K = modO2Image H X ⊔
      (CFSG.oddCore ↥(modO2Image H K)).map (modO2Image H K).subtype) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH2 : pCoreOf 2 H ≠ ⊥ := (inH_of_inM hH).2
  have hKH : K ≤ H := le_of_mem_cComp hKc
  set Kb := modO2Image H K with hKb
  obtain ⟨hcase, hcommon, -⟩ := Vol2Native.lemma_1_2_1_four_core hK h36 hH2 hKc
  have h3 : ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥Kb) := by
    rcases hcase with hc | ⟨p, hp, hp3, -, ⟨e⟩, -⟩ | ⟨-, -, -, hprimes⟩
    · exact absurd hc.1 hnq
    · intro h
      rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
        Nat.card_fin] at h
      have h3p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    · intro h
      have := (hprimes 3 Nat.prime_three h).1
      omega
  rw [← hcommon.1] at h21
  set Fb := (CFSG.fittingSubgroup ↥Kb).map Kb.subtype with hFb
  have hKbN : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have h1 := modO2Image_le_normalizer' (H := H) (A := H) (B := K) hKn
    have h2 : modO2Image H H = ⊤ := by
      rw [modO2Image, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rwa [h2] at h1
  have hFn : Fb.Normal := by
    refine ⟨fun f hf g => ?_⟩
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Kb) (CFSG.fittingSubgroup ↥Kb) (hKbN (Subgroup.mem_top g))
    exact (Subgroup.mem_normalizer_iff.mp h1 f).mp hf
  have hFnil : Group.IsNilpotent ↥Fb :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ Kb.subtype_injective)
  have hFF : Fb ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hFn, hFnil⟩
  have hFc : ¬ 3 ∣ Nat.card Fb := by
    rw [hFb, Subgroup.card_map_of_injective Kb.subtype_injective]
    exact h3
  apply not_le_fsuM hyp ht hX hKc hXK
  intro k hk
  have hkb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨k, hKH hk⟩ : ↥H) ∈ Kb :=
    Subgroup.mem_map_of_mem _ (show (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H from hk)
  rw [h21] at hkb
  obtain ⟨xb, hxb, fb, hfb, hxf⟩ := Subgroup.mem_sup_of_normal_right.mp hkb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hxb
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) fb
  have hfY : (f : G) ∈ oTwoFIn H := C2Six.mem_oTwoFIn_iff.mpr (hFF hfb)
  have hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (⟨(f : G), C2Six.oTwoFIn_le hfY⟩ : ↥H))).Coprime 3 := by
    have hd : orderOf (⟨_, hfb⟩ : ↥Fb) ∣ Nat.card Fb := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      fun h3' => hFc (h3'.trans ?_)))
    exact hd
  have hfM := mem_fsuM_of_coprime_three hK h331 h37 h38 h1011 hyp hH hS hfY hcop
  have hxM : (x : G) ∈ fsuM T L := by
    have hxX : (x : G) ∈ X := hx
    rcases hX with rfl | rfl
    · exact SecA.le_fsuL0 T X |>.trans (SecA.fsuL0_le_fsuM T X) |> fun h => h hxX
    · exact ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)) hxX
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxf
  have hO : ((x * f)⁻¹ * ⟨k, hKH hk⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
    exact hxf
  have hoM : (((x * f)⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) ∈ fsuM T L :=
    ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS).trans (inf_le_left.trans (le_fsuM T L)))
      ⟨_, hO, rfl⟩
  have hk' : k = (x : G) * (f : G) * (((x * f)⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) := by
    simp [mul_assoc]
  rw [hk']
  exact (fsuM T L).mul_mem ((fsuM T L).mul_mem hxM hfM) hoM

end CFSG.Quasithin.Vol2.Ch10.SecB
