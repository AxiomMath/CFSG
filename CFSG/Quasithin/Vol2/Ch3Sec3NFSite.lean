module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFStmt
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313FC
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.Vol2.GoldschmidtTDTmpL6
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ9
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.Background.F918J6
public import CFSG.Quasithin.Background.F918K8
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Holds
public import CFSG.Quasithin.Vol2.Ch3Sec3L2qCore
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)

@[expose] def Obl3_3_13D12On (P : NFSite) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D →
    P G T M L D H → InH T H → H ≤ L ⊔ T →
    Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) →
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

@[expose] def Obl3_3_13LTOn (P : NFSite) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D →
    P G T M L D H → InH T H → H ≤ L ⊔ T →
    Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) →
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

@[expose] def Stmt3_3_13LTOn (P : NFSite) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H : Subgroup G), Hyp331 G T M L D →
    P G T M L D H → InH T H → H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) →
      D ≤ Subgroup.normalizer (H : Set G)

namespace Lem3313F

open CFSG.Quasithin

theorem obl3_3_13D12On_of_nfOn {P : NFSite}
    (hNF : Obl3_3_13D12NFOn P) (hout : Obl3_3_13D12NF_outer) : Obl3_3_13D12On P := by
  intro G _ _ T M L D H K h hP hH hHLT he hO hK hKq hYK hTK hq
  by_cases hKf : quasithinIsFaithfulLocal T K
  · obtain ⟨q, hq, h24, hmod⟩ := hq
    exact (false_of_faithful lemma128Two_proved stmt3_2_3_proved VolI.a36ForSQTK_holds
      Vol2.Ch10.tmpL6_3_2_2_eight_proved Ch3T316W.theorem316Statement_holds d37_holds
      SmithD39Two.d36c_holds
      (insp5a_of_inputs asA21SQTKSection asB45_holds Vol2.Ch10.SecA.facts10_1_holds
        insp5aNonShape_holds)
      Vol2Native.a37ForSQTKCat_proved C129Native.a38ForSQTKCat_proved h
      (h.toSetup331.isUniqueM C129Native.a38ForSQTKCat_proved Vol2Native.a39ForSQTKCat_proved)
      hH hO hK hKq hTK hKf hq h24 hmod).elim
  · by_cases hin : InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K
    · exact (hNF G T M L D H K h hP hH hHLT he hO hK hKq hYK hTK hKf hin hq).elim
    · exact hout G T M L D H K h hH hHLT he hO hK hKq hYK hTK hq hin

end Lem3313F

namespace Lem3313Q

open CFSG.Quasithin.H13.BenC CFSG.Quasithin.H13.Lem3313B

theorem obl3_3_13LTOn_of_D12On {P : NFSite} (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hD : Obl3_3_13D12On P) : Obl3_3_13LTOn P := by
  intro G _ _ T M L D H K h hP hH hHLT ⟨e⟩ hO hK hKq hYK hTK ⟨q, hq, hq2, hmod⟩
  by_cases h24 : q % 24 = 11 ∨ q % 24 = 13
  · exact hD G T M L D H K h hP hH hHLT ⟨e⟩ hO hK hKq hYK hTK ⟨q, hq, h24, hmod⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  have hTH : T ≤ H := hH.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow hTH⟩
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hTH.trans le_sup_left)⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  set φ := oTwoQuotEquiv e with hφ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXi := Der6D.xi_of_iso hTsyl hH.2 φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hOHT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ T := fun x hx =>
    hOHT (C1Pack12.pow_three_mem_pCoreOf φ hx)
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHN : H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKc h37 h38 hO hT₀ hK
  set H₀ := H ⊔ D with hH₀
  have hHH₀ : H ≤ H₀ := le_sup_left
  have hDH₀ : D ≤ H₀ := le_sup_right
  have hTH₀ : T ≤ H₀ := hTH.trans hHH₀
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKc hO
  have h37Q := h37 _ hQ
  have h38Q := h38 _ hQ
  set π : ↥H₀ →* ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) with hπ
  have hker : ∀ x : ↥H₀, π x = 1 → (x : G) ∈ T := by
    intro x hx
    have h1 : x ∈ CFSG.Open.pCore 2 ↥H₀ := by
      exact (QuotientGroup.eq_one_iff x).mp hx
    exact pCoreOf_le_of_isSylowTwoOf hT₀ ⟨x, h1, rfl⟩
  set Ab := modO2Image H₀ K with hAb
  set Tb := modO2Image H₀ T with hTbdef
  have hAbc : Ab ∈ cComp (⊤ : Subgroup _) := modO2Image_mem_cComp hK
  have hTb : IsSylowTwoOf Tb ⊤ :=
    A312.isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective _)
      (isSylowTwoOf_top_subgroupOf hT₀)
  obtain ⟨-, hT38⟩ := h38Q Ab hAbc
  rcases hT38 Tb hTb with ⟨hnorm, -, -⟩ |
      ⟨tb, htb, htbn, hconjT, -, hcomm, hinf, hTbN, hsupT⟩
  ·
    exfalso
    apply hTK
    intro t ht
    have htH : t ∈ H₀ := hTH₀ ht
    have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
    have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) = modO2Image H₀ K := by
      refine (modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩).trans ?_
      refine A38.map_conj_eq_iff.mpr ?_
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top _
    exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
  set Ab' := Ab.map (MulAut.conj tb).toMonoidHom with hAb'
  have hAb'c : Ab' ∈ cComp (⊤ : Subgroup _) := C2A3Orbits.conj_mem_cComp_top hAbc tb
  have hne : Ab ≠ Ab' := fun h1 => htbn (A38.map_conj_eq_iff.mp h1.symm)
  have hcomm' : ∀ a ∈ Ab, ∀ b ∈ Ab', a * b = b * a := by
    intro a ha b hb
    have h1 : Ab ≤ Subgroup.centralizer (Ab' : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (h1 ha) b hb).symm
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : q ≠ 3 := by
    intro h3q
    apply hmod.1.2.2.2.2
    rw [h3q, pow_one]
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    have := hq.two_le
    omega
  have hF : Nat.card (GaloisField q 1) = q := by
    rw [GaloisField.card q 1 (by norm_num), pow_one]
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  obtain ⟨e₂⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2 q 1
    hmod
  let eA : ↥Ab ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q 1) := e₁.symm.trans e₂
  let eA' : ↥Ab' ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q 1) :=
    (Subgroup.equivMapOfInjective Ab (MulAut.conj tb).toMonoidHom
      (MulAut.conj tb).injective).symm.trans eA
  have hAN : Ab ≤ Subgroup.normalizer ((Ab ⊔ Ab' : Subgroup _) : Set _) := fun a ha =>
    Lem3313B.mem_normalizer_sup (Subgroup.le_normalizer ha) (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm' a ha b hb).symm))
  have hTbAT : IsSylowTwoOf Tb (Ab ⊔ Tb) := ⟨le_sup_right, hTb.2.1, fun h2 => hTb.2.2
    (h2.trans (by
      show Tb.relIndex (Ab ⊔ Tb) ∣ Tb.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hS0 : IsSylowTwoOf (Tb ⊓ (Ab ⊔ Ab')) (Ab ⊔ Ab') :=
    A4.isSylowTwoOf_inf_normal hTbAT (by rw [hsupT]; exact le_sup_left) (sup_le hAN hTbN)
  have hAAN : Ab ⊔ Ab' ≤ Subgroup.normalizer (Ab : Set _) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_comm hcomm')
  have hAAN' : Ab ⊔ Ab' ≤ Subgroup.normalizer (Ab' : Set _) :=
    sup_le (le_normalizer_of_comm (fun a ha b hb => (hcomm' b hb a ha).symm))
      Subgroup.le_normalizer
  have hS : IsSylowTwoOf (Tb ⊓ Ab) Ab := by
    have h1 := A4.isSylowTwoOf_inf_normal hS0 le_sup_left hAAN
    rwa [inf_assoc, inf_of_le_right (le_sup_left : Ab ≤ Ab ⊔ Ab')] at h1
  have hS' : IsSylowTwoOf (Tb ⊓ Ab') Ab' := by
    have h1 := A4.isSylowTwoOf_inf_normal hS0 le_sup_right hAAN'
    rwa [inf_assoc, inf_of_le_right (le_sup_right : Ab' ≤ Ab ⊔ Ab')] at h1
  obtain ⟨⟨t₀, ht₀H⟩, ht₀T, rfl⟩ := htb
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H₀ := map_conj_mem_cComp hK ht₀H
  have hK'b : modO2Image H₀ K' = Ab' := modO2Image_conj ⟨t₀, ht₀H⟩
  have hKK : conjClosure K T = K ⊔ K' := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (sup_le (le_conjClosure K T) ?_)
    · have htH : t ∈ H₀ := hTH₀ ht
      have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
      have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) ∈ conjSubgroupsBy Tb Ab := by
        rw [modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩]
        exact ⟨π ⟨t, htH⟩, mk_mem_img _ ht, rfl⟩
      rw [hconjT] at h2
      have hmem : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
      rcases h2 with h2 | h2
      · rw [modO2Image_injOn H₀ h1 hK h2] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [Set.mem_singleton_iff, ← hK'b] at h2
        rw [modO2Image_injOn H₀ h1 hK'c h2] at hmem
        exact Subgroup.mem_sup_right hmem
    · rintro _ ⟨k, hk, rfl⟩
      exact mem_conjClosure (show t₀ ∈ T from ht₀T) hk
  have hKKb : modO2Image H₀ (K ⊔ K') = Ab ⊔ Ab' := by
    rw [img_sup (le_of_mem_cComp hK) (le_of_mem_cComp hK'c), hK'b]
  set Yb := modO2Image H₀ (oTwoUpper H) with hYb
  set Pb := modO2Image H₀ P3 with hPb
  set Db := modO2Image H₀ D with hDb
  have hTY : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper H)
  have hYbA : Yb ≤ Ab ⊔ Ab' := by
    rw [← hKKb]
    exact img_mono (hYK.trans hKK.le)
  have hPbY : Pb ≤ Yb := img_mono hP3.1
  have hPb9 : Nat.card Pb = 9 := by
    rw [← hP3card]
    have hinj : Function.Injective (π.comp (P3.subgroupOf H₀).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ((x : ↥H₀) : G) ∈ T := hker _ hx
      have h2 : ((x : ↥H₀) : G) ∈ P3 := x.2
      have h3 : ((x : ↥H₀) : G) ∈ P3 ⊓ T := ⟨h2, h1⟩
      rw [(IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 T hP3.2.1 hT2).eq_bot,
        Subgroup.mem_bot] at h3
      exact Subtype.ext (Subtype.ext h3)
    have h1 : Pb = (π.comp (P3.subgroupOf H₀).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      try rfl
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP3.1.trans (hYH.trans hHH₀))).toEquiv
  have hYb3 : ∀ y ∈ Yb, y ^ 3 ∈ Tb := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    exact mk_mem_img _ (by simpa using hpow3 _ hy)
  have hDodd : ∀ x ∈ Db, Odd (orderOf x) := by
    rintro _ ⟨d, hd, rfl⟩
    refine Odd.of_dvd_nat h.Dodd ?_
    refine (orderOf_map_dvd π d).trans ?_
    have h1 : orderOf d = orderOf ((d : G)) := Subgroup.orderOf_coe d |>.symm
    have h2 : orderOf ((⟨d, hd⟩ : ↥D)) = orderOf (d : G) := Subgroup.orderOf_mk _ _
    rw [h1, ← h2]
    exact orderOf_dvd_natCard _
  have hDN : Db ≤ Subgroup.normalizer ((Ab ⊔ Ab' : Subgroup _) : Set _) := by
    rw [← hKKb]
    refine img_le_normalizer ?_
    rw [← hKK]
    exact hDH₀.trans hHN
  have hDA : Db ≤ Subgroup.normalizer (Ab : Set _) := fun x hx =>
    (mem_normalizer_of_odd h37Q hAbc hAb'c hne (hDN hx) (hDodd x hx)).1
  have hDA' : Db ≤ Subgroup.normalizer (Ab' : Set _) := fun x hx =>
    (mem_normalizer_of_odd h37Q hAbc hAb'c hne (hDN hx) (hDodd x hx)).2
  have hDT : Db ≤ Subgroup.normalizer (Tb : Set _) := img_le_normalizer h.DN
  have hcore : Db ≤ Subgroup.normalizer (Yb : Set _) := by
    rcases L2qC.le_normalizer_core eA eA' hF hq hq5 hcomm' hinf hS hS' hTb.2.1 hYbA
        (img_le_normalizer hTY) hPbY hPb9 hYb3 hDA hDA' hDT hDodd with hc | hc
    · exact hc
    · exact absurd hc h24
  set R := (Yb.comap π).map H₀.subtype with hR
  have hRmem : ∀ g : G, g ∈ R ↔ ∃ hg : g ∈ H₀, π ⟨g, hg⟩ ∈ Yb := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, hgR⟩
      exact ⟨⟨g, hg⟩, hgR, rfl⟩
  have hYR : oTwoUpper H ≤ R := fun y hy =>
    (hRmem y).mpr ⟨hHH₀ (hYH hy), mk_mem_img _ hy⟩
  have hRYT : R ≤ oTwoUpper H ⊔ T := by
    intro g hg
    obtain ⟨hgH, hgR⟩ := (hRmem g).mp hg
    obtain ⟨y, hy, hyg⟩ := hgR
    have h2 : π (y⁻¹ * ⟨g, hgH⟩) = 1 := by
      rw [map_mul, map_inv, hyg, inv_mul_cancel]
    have h3 := hker _ h2
    have e : g = (y : G) * (((y⁻¹ * ⟨g, hgH⟩ : ↥H₀)) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h3)
  have hO2R : oTwoUpper R = oTwoUpper H := by
    refine le_antisymm ?_ ?_
    · rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hx, ho⟩
      exact CZCore.mem_of_odd hTY hT2 (hRYT hx) ho
    · have h1 : oTwoUpper H = oTwoUpper (oTwoUpper H) := hXi.1
      rw [h1]
      exact oTwoUpper_mono hYR
  have hDR : D ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ d ∈ D, ∀ g ∈ R, d * g * d⁻¹ ∈ R := by
      intro d hd g hg
      obtain ⟨hgH, hgR⟩ := (hRmem g).mp hg
      have hdH : d ∈ H₀ := hDH₀ hd
      refine (hRmem _).mpr ⟨H₀.mul_mem (H₀.mul_mem hdH hgH) (H₀.inv_mem hdH), ?_⟩
      have e : (⟨d * g * d⁻¹, H₀.mul_mem (H₀.mul_mem hdH hgH) (H₀.inv_mem hdH)⟩ : ↥H₀) =
          ⟨d, hdH⟩ * ⟨g, hgH⟩ * (⟨d, hdH⟩ : ↥H₀)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hcore (mk_mem_img _ hd)) _).mp hgR
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key d hd g, fun hg => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hg
    simpa [mul_assoc] using this
  rw [← hO2R]
  exact hDR.trans (normalizer_le_normalizer_oTwoUpper R)

end Lem3313Q

theorem stmt3_3_13LTOn_of {P : NFSite} (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h10 : Stmt3_3_10)
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hFa : Vol2.Ch10.SecB.FactL33M11)
    (hFc : Vol2.Ch10.SecB.FactL4L5) (hAut : FactAutL45Sylow) (hHe : FactAutHeSylow)
    (hB : Step3_3_13Bender) (hObl : Obl3_3_13LTOn P) : Stmt3_3_13LTOn P := by
  intro G _ _ T M L D H h hP hH hHLT ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  have hTH : T ≤ H := hH.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow hTH⟩
  set φ := oTwoQuotEquiv e with hφ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  suffices hDY : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) by
    intro d hd
    rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow hTsyl]
    refine A38.map_conj_eq_iff.mp ?_
    rw [Subgroup.map_sup, A38.map_conj_eq_iff.mpr (hDY hd), A38.map_conj_eq_iff.mpr (h.DN hd)]
  by_contra hDY
  have hO : pCoreOf 2 (H ⊔ D) ≠ ⊥ :=
    (h10 G T M L D h).1 H hH ⟨T, Lem3313.maxOver_eq_of_iso hTsyl φ⟩
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hTH.trans le_sup_left)⟩
  have hXi := Der6D.xi_of_iso hTsyl hH.2 φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hYH (le_normalizer_oTwoUpper H)
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ pCoreOf 2 (oTwoUpper H) := fun x hx => by
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx 3, C1Pack12.pow_three_mem_pCoreOf φ hx⟩
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  rcases h134 G (H ⊔ D) T (oTwoUpper H) P3 (hKc _ hO) hO hT₀ (hYH.trans le_sup_left) hXi hrel
      hP3.le hP3.isPGroup hP3card with hN | ⟨K, hK, hKq, hYK', hcases⟩
  · exact hDY (le_sup_right.trans hN)
  have hHN : H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKc h37 h38 hO hT₀ hK
  rcases hcases with ⟨⟨t, ⟨htT, -⟩, htn, -, -⟩, htype⟩ | ⟨hTL, htype⟩ | ⟨-, -, hcyc⟩ |
      ⟨hTL, htype⟩ | ⟨hHK, he⟩
  ·
    have hTK : ¬ T ≤ Subgroup.normalizer (K : Set G) := fun hle => htn (hle htT)
    rcases htype with hn | hq
    · exact hDY (hB G T M L D H K h hH ⟨e⟩ hO hK hKq hYK' hTK hn)
    · exact hDY (hObl G T M L D H K h hP hH hHLT ⟨e⟩ hO hK hKq hYK' hTK hq)
  ·
    have hYK : oTwoUpper H ≤ K := hYK'.trans (Vol2.Ch10.SecB.conjClosure_eq_self hTL).le
    obtain ⟨s, hs, x, hx, hne⟩ := Vol2.Ch10.SecB.exists_pow_four_not_mem hFa hT₀ hK (by
      rcases htype with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)) hYK hXi.1 hXi.2.1 hpow3 hrel
    exact hne (Lem3313.pow_four_comm_mem_of_iso hTsyl φ hs hx)
  ·
    exact Der6D.not_autCyclic h.sylow hTsyl φ hXi hP3 hP3card hcyc
  ·
    have hYK : oTwoUpper H ≤ K := hYK'.trans (Vol2.Ch10.SecB.conjClosure_eq_self hTL).le
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
      have h1 := le_sup_right.trans hHN
      rwa [Vol2.Ch10.SecB.conjClosure_eq_self hTL] at h1
    rcases htype with hM | hk | hk
    · obtain ⟨s, hs, x, hx, hne⟩ := Vol2.Ch10.SecB.exists_pow_four_not_mem hFa hT₀ hK
        (Or.inr (Or.inr hM)) hYK hXi.1 hXi.2.1 hpow3 hrel
      exact hne (Lem3313.pow_four_comm_mem_of_iso hTsyl φ hs hx)
    · exact hDY (Lem3313.le_normalizer_of_lk2 hFc hAut h.sylow hTsyl φ hH.2 hK hTL hDK h.DN
        h.Dodd hYK (Or.inl rfl) hk)
    · exact hDY (Lem3313.le_normalizer_of_lk2 hFc hAut h.sylow hTsyl φ hH.2 hK hTL hDK h.DN
        h.Dodd hYK (Or.inr rfl) hk)
  ·
    have hTL : T ≤ Subgroup.normalizer (K : Set G) := (hTH.trans le_sup_left).trans hHK
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := le_sup_right.trans hHK
    have hYK : oTwoUpper H ≤ K := hYK'.trans (Vol2.Ch10.SecB.conjClosure_eq_self hTL).le
    exact hDY (Lem3313.le_normalizer_of_he hHe h.sylow hTsyl hTL hDK h.DN h.Dodd hYK he)

end CFSG.Quasithin.H13
