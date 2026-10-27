module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E
public import CFSG.Quasithin.Vol2.Ch8Sec2HFixSyl
public import CFSG.Quasithin.Vol2.Ch8Sec2HModelPf
public import CFSG.Quasithin.Vol2.Ch8Sec2HBParabHolds
public import CFSG.Quasithin.Vol2.Ch8Sec2KGCover
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210D
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8210F

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem isModel82_of_case82 [hc : IsMulCommutative ↥(fsuV T I)] (hL0 : fsuL0 T L = L)
    (hrow : Case8_2 T L I) (hn1 : ∀ n : ℕ, Row711L3Nine T L I n → n = 1) :
    IsModel82 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) := by
  rw [← hL0]
  rcases hrow with ⟨n, hn⟩ | h' | h' | h'
  · obtain rfl := hn1 n hn
    exact Or.inl hn.2
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr h'))

omit [Finite G] in
theorem isElemAbelian_of_le_conjSub_82 {V A : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ B6.conjSub h V) : IsElemAbelian 2 A := by
  have hAV : ∀ x ∈ A, h⁻¹ * x * h ∈ V := fun x hx => B6.mem_conjSub.mp (hA hx)
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have e := Subgroup.mem_centralizer_iff.mp (hVC (hAV b b.2)) _ (hAV a a.2)
    show (a : G) * b = b * a
    have e1 : (a : G) * b = h * ((h⁻¹ * a * h) * (h⁻¹ * b * h)) * h⁻¹ := by group
    have e2 : (b : G) * a = h * ((h⁻¹ * b * h) * (h⁻¹ * a * h)) * h⁻¹ := by group
    rw [e1, e2, e]
  · have hx2 := hV.2 _ (hAV x hx)
    have e : x ^ 2 = h * (h⁻¹ * x * h) ^ 2 * h⁻¹ := by
      rw [sq, sq]
      group
    rw [e, hx2]
    group

omit [Finite G] in
theorem le_normalizer_ch82A_82 {V LU : Subgroup G} {h : G}
    (hLUV : LU ≤ Subgroup.normalizer (V : Set G))
    (hh : h ∈ Subgroup.normalizer (LU : Set G))
    (hLUP : LU ≤ Subgroup.normalizer (pCoreOf 2 (ch82I V h) : Set G)) :
    LU ≤ Subgroup.normalizer (ch82A V h : Set G) := by
  intro l hl
  have hl' : h⁻¹ * l * h ∈ LU := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) l).mp hl
    simpa using this
  have hlV := hLUV hl'
  have hVh : ∀ x, x ∈ B6.conjSub h V ↔ l * x * l⁻¹ ∈ B6.conjSub h V := by
    intro x
    rw [B6.mem_conjSub, B6.mem_conjSub]
    have e : h⁻¹ * (l * x * l⁻¹) * h = (h⁻¹ * l * h) * (h⁻¹ * x * h) * (h⁻¹ * l * h)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hlV _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  show x ∈ B6.conjSub h V ⊓ pCoreOf 2 (ch82I V h) ↔
    l * x * l⁻¹ ∈ B6.conjSub h V ⊓ pCoreOf 2 (ch82I V h)
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hVh x, Subgroup.mem_normalizer_iff.mp (hLUP hl) x]

omit [Finite G] in
theorem autOn_preimage_82 {V : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G))
    {K : Subgroup (MulAut ↥V)} (hK : K ≤ autOn L V) :
    autOn (((K.subgroupOf (autOn L V)).comap (actHom82 hLN)).map L.subtype) V = K := by
  set C := (K.subgroupOf (autOn L V)).comap (actHom82 hLN) with hC
  have h1 := map_actHom82 (X := C.map L.subtype) hLN (Subgroup.map_subtype_le C)
  have h2 : (C.map L.subtype).subgroupOf L = C :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective C
  rw [h2, hC, Subgroup.map_comap_eq_self_of_surjective (actHom82_surjective hLN),
    Subgroup.map_subgroupOf_eq_of_le hK] at h1
  exact h1.symm

theorem pCoreOf_eq_fsuV_of_82 (hsimp : HSimple82) (hcent : HCent82) (htype : HType82)
    (hpar : HParab82) (hcovL : KG82CoverL34) (hcovM : KG82CoverM22) (hm24 : SchurMult2M24)
    (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8)
    (h829 : Stmt8_2_9_12) (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    pCoreOf 2 L = fsuV T I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [← hL0]
    exact le_sup_left.trans hN
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hVL : fsuV T I ≤ L := fsuV_le_of_82 hyp hTL hVT
  have hTp : IsPGroup 2 ↥T := hyp.fsu.sylow.1
  obtain ⟨H, h, k, hH, hh, h22⟩ := exists_concl822_of_82 h822 hyp h731 h821 hrow
  obtain ⟨-, -, hn1, hTabL, hTabM, hTab24, hTab24c, -, -, -, -, -, hIU⟩ :=
    h825 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨hNLU, hLUC, -, hLUP, -⟩ :=
    h828 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨-, -, hTVA⟩ := h829 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨-, hhI, -, -, -, hSyl, -, -, -, -, -, -, hA7, hAC, -, -, -, -, -⟩ := h22
  set V := fsuV T I with hVdef
  set A := ch82A V h with hAdef
  set U := ch82U V h with hUdef
  set LU := ch82LU L U with hLUdef
  have hmod : IsModel82 (V := ↥V) (autOn L V) := isModel82_of_case82 hL0 hrow hn1
  have hAT : A ≤ T := fun x hx =>
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl hx.2).1
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hA7]
    exact inf_le_right
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAT.trans hTL
  have hAC' : A ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rw [hAC]
    exact inf_le_left
  have hmA : mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) ≠ 0 := by
    rcases hrow with ⟨n, hn⟩ | h' | h' | h'
    · rw [(hTabL ⟨n, hn⟩).2.2.1]
      norm_num
    · rw [(hTabM h').2.2.1]
      norm_num
    · rw [(hTab24 h').2.2.1]
      norm_num
    · rw [(hTab24c h').2.2.1]
      norm_num
  have hAnC : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hmA
    rw [inf_eq_left.mpr hle]
    unfold mQuot
    rw [Subgroup.relIndex_self, padicValNat_one_right]
  have hQC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_82 hsimp hmod hLN
  have hQT : pCoreOf 2 L ≤ T := pCoreOf_le_T_of_82 hyp hTL
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hQA : ⁅pCoreOf 2 L, A⁆ ≤ V :=
    commutator_pCoreOf_le_of_82 hQT hQC hTQ hAT hTVA hAN hVC hAC'
  have hLA : ⁅L, A⁆ = L := commutator_L_eq_of_82 hsimp hcent hyp hmod hLN hAN hAL hAnC hQC
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQL : ⁅pCoreOf 2 L, L⁆ ≤ V :=
    commutator_Q_L_le_of_82 hLQ hLN (hAT.trans hTQ) hAN hQA hLA
  have hCQ : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L :=
    le_antisymm (inf_centralizer_le_pCoreOf_of_82 hyp.fsu.faithful.2.2.1 hV hLN hQL)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hQC)
  have hVQ : V ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLN
      (isPGroup_of_isElemAbelian_two hV)
  have hperf : ⁅L, L⁆ = L := hyp.fsu.faithful.1.2.1.2.1
  have hM24 : ∀ _ : IsSporadic .M24 ↥(autOn L V), pCoreOf 2 L = V := fun hiso =>
    pCoreOf_eq_of_m24_82 hsimp hm24 hmod hiso hLN hperf hVQ hQL hCQ
  have hcover : ∀ (_ : (BinaryNineTensor (V := ↥V) (autOn L V) ⊤ ⊥ 1 ∧
        mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = 4) ∨
        (MathieuCode22 (V := ↥V) (autOn L V) ⊤ ⊥ ∧
          mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = 5)) (_ : rk ↥U = 4),
      pCoreOf 2 L = V := by
    intro hcase hrkU
    have hUV : U ≤ V := inf_le_left
    have hAU : A ≤ Subgroup.centralizer (U : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hu.2 a ha).symm
    have hLU : LU ≤ L := (perfectCore_le _).trans inf_le_left
    have hLUN : LU ≤ Subgroup.normalizer (V : Set G) := hLU.trans hLN
    have hhLU : h ∈ Subgroup.normalizer (LU : Set G) :=
      hNLU (Subgroup.centralizer_le_normalizer _ (hIU hhI))
    have hLUA : LU ≤ Subgroup.normalizer (A : Set G) := le_normalizer_ch82A_82 hLUN hhLU hLUP
    have hYA : ⁅LU, A⁆ ≤ A := by
      rw [Subgroup.commutator_le]
      intro l hl a ha
      rw [commutatorElement_def]
      exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLUA hl) a).mp ha) (A.inv_mem ha)
    have hYQ : ⁅LU, A⁆ ⊓ pCoreOf 2 L ≤ V := fun y hy => hAC' ⟨hYA hy.1, hQC hy.2⟩
    have hYO : ⁅LU, A⁆ ≤ pCoreOf 2 LU := (Subgroup.commutator_mono le_rfl hAU).trans hLUC
    have hYN : LU ≤ Subgroup.normalizer ((⁅LU, A⁆ : Subgroup G) : Set G) :=
      Subgroup.normalizer_commutator_ge_left LU A
    have hAp : IsPGroup 2 ↥A := hTp.to_le hAT
    have hAe : IsElemAbelian 2 A := isElemAbelian_of_le_conjSub_82 hV fun x hx => hx.1
    have hXc : Nat.card ↥(autOn A V) = 2 ^ mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) :=
      card_autOn_82 hAN hAp
    have hfix : fixV (autOn A V) = U.subgroupOf V := fixV_autOn_82 hAN
    have hUc : Nat.card ↥(fixV (autOn A V)) = 2 ^ 4 := by
      rw [hfix, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv,
        card_eq_two_pow_of_isPGroup ((isPGroup_of_isElemAbelian_two hV).to_le hUV), hrkU]
    have hP : perfectCore (autOn L V ⊓ stabSub (fixV (autOn A V))) = autOn LU V := by
      rw [hfix, ← autOn_inf_normalizer_82 hUV, ← autOn_perfectCore_82 (inf_le_left.trans hLN)]
      rfl
    have hcase' : (BinaryNineTensor (V := ↥V) (autOn L V) ⊤ ⊥ 1 ∧
          Nat.card ↥(autOn A V) = 2 ^ 4) ∨
        (MathieuCode22 (V := ↥V) (autOn L V) ⊤ ⊥ ∧ Nat.card ↥(autOn A V) = 2 ^ 5) := by
      rw [hXc]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, by rw [h2]⟩
      · exact Or.inr ⟨h1, by rw [h2]⟩
    obtain ⟨h960, hO2, hK⟩ := hpar ↥V (autOn L V) (autOn A V) hcase'
      (autOn_le_normalizer_82 hAL) (isElemAbelian_autOn_82 hAe) hUc
    rw [hP] at h960 hO2 hK
    have hYimg : pCoreOf 2 (autOn LU V) ≤ autOn ⁅LU, A⁆ V := by
      rw [autOn_commutator_82 hLUN hAN, Subgroup.commutator_comm]
      exact hO2
    have htype' : IsPSL 3 2 2 ↥(autOn L V) ∨ (IsSporadic .M22 ↥(autOn L V) ∧
        ∃ X : Subgroup G, LU ≤ X ∧ X ≤ L ∧ IsPSL 3 2 2 ↥(autOn X V)) := by
      rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl ((htype ↥V (autOn L V)).1 h1)
      · obtain ⟨K, hPK, hKH, hK3⟩ := hK h1
        refine Or.inr ⟨(htype ↥V (autOn L V)).2.1 h1,
          ((K.subgroupOf (autOn L V)).comap (actHom82 hLN)).map L.subtype, ?_,
          Subgroup.map_subtype_le _, ?_⟩
        · intro u hu
          refine ⟨⟨u, hLU hu⟩, ?_, rfl⟩
          show actHom82 hLN ⟨u, hLU hu⟩ ∈ K.subgroupOf (autOn L V)
          rw [Subgroup.mem_subgroupOf]
          exact hPK ⟨⟨u, hLUN hu⟩, hu, rfl⟩
        · rw [autOn_preimage_82 hLN hKH]
          exact hK3
    exact pCoreOf_eq_of_cover_82 hsimp hcovL hcovM hmod hLN hperf hVQ hQL hCQ hLU hYO hYN hYQ
      h960 hYimg htype'
  rcases hrow with ⟨n, hn⟩ | h' | h' | h'
  · obtain rfl := hn1 n hn
    have hB : BinaryNineTensor (V := ↥V) (autOn L V) ⊤ ⊥ 1 := by
      rw [← hL0]
      exact hn.2
    exact hcover (Or.inl ⟨hB, (hTabL ⟨1, hn⟩).2.2.1⟩) (hTabL ⟨1, hn⟩).2.2.2
  · have hB : MathieuCode22 (V := ↥V) (autOn L V) ⊤ ⊥ := by
      rw [← hL0]
      exact h'
    exact hcover (Or.inr ⟨hB, (hTabM h').2.2.1⟩) (hTabM h').2.2.2
  · exact hM24 ((htype ↥V (autOn L V)).2.2 (Or.inl (by rw [← hL0]; exact h')))
  · exact hM24 ((htype ↥V (autOn L V)).2.2 (Or.inr (by rw [← hL0]; exact h')))

end L8210F

theorem stmt8_2_10_of
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12)
    (hm24 : SchurMult2M24) : Stmt8_2_10 := by
  have hcovL : KG82CoverL34 := kg82CoverL34_holds
  have hcovM : KG82CoverM22 := kg82CoverM22_holds
  have hfix : HFixSylow82 := hFixSylow82_holds
  have hsimp : HSimple82 := hSimple82_holds
  have hcent : HCent82 := hCent82_holds
  have htype : HType82 := hType82_holds
  have hpar : HParab82 := hParab82_holds
  intro G _ _ T L I hyp h731 h821 hc hrow
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTL := le_normalizer_of_case82 h711n hyp hrow
  obtain ⟨H, h, k, hH, hh, h22⟩ := exists_concl822_of_82 h822 hyp h731 h821 hrow
  have hn1 := (h825 G T L I hyp h731 h821 hc hrow H h k hH hh h22).2.2.1
  exact ⟨inf_centralizer_eq_bot_of_82 h3109 h37 h38 h39 hyp hV hN hTL,
    (pCoreOf_eq_fsuV_of_82 hsimp hcent htype hpar hcovL hcovM hm24 h711n h822 h825 h828 h829 hyp
      h731 h821 hrow hV hN).symm,
    exists_fixT_eq_zpowers_of_82 hfix hyp hV hrow hn1⟩

end CFSG.Quasithin.H13
