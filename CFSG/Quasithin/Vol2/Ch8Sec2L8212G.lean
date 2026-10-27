module

public import CFSG.Quasithin.Vol2.Ch8Sec2HCoc
public import CFSG.Quasithin.Vol2.Ch8Sec2L8211F
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212D
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8212G

variable {G : Type} [Group G] [Finite G]

theorem vz82_eq_82 {L V : Subgroup G} [hc : IsMulCommutative ↥V] {z : G} (hzV : z ∈ V)
    (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hCL : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    vz82 (autOn L V) ⟨z, hzV⟩ = (ch8Vz V L z).subgroupOf V := by
  have hLzL : ch8Lz L z ≤ L := (perfectCore_le _).trans inf_le_left
  have hLzN : ch8Lz L z ≤ Subgroup.normalizer (V : Set G) := hLzL.trans hLN
  have hCLz : IsPGroup 2 ↥(ch8Lz L z ⊓ Subgroup.centralizer (V : Set G)) :=
    hCL.to_le (inf_le_inf_right _ hLzL)
  have hRN : pCoreOf 2 (ch8Lz L z) ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hLzN
  have hPz : autOn (ch8Lz L z) V = parz82 (autOn L V) ⟨z, hzV⟩ := autOn_ch8Lz_82 hLN ⟨z, hzV⟩
  have hRbar : autOn (pCoreOf 2 (ch8Lz L z)) V = radz82 (autOn L V) ⟨z, hzV⟩ := by
    rw [autOn_pCoreOf_82 hLzN hCLz, hPz]
    rfl
  rw [vz82, ← hRbar, commV_autOn_82 hRN]
  rfl

theorem isTypeJ4Core_of_82 {C : Subgroup G} {z : G} (hzC : z ∈ C)
    (hchar : C ⊓ Subgroup.centralizer (pCoreOf 2 C : Set G) ≤ pCoreOf 2 C)
    (hext : IsExtraspecialPGroup 2 ↥(pCoreOf 2 C)) (hcard : Nat.card ↥(pCoreOf 2 C) = 2 ^ 13)
    (hcen : (Subgroup.center ↥(pCoreOf 2 C)).map (pCoreOf 2 C).subtype = Subgroup.zpowers z)
    (hiso : Nonempty (↥(pCoreOf 2 C) ≃* J4.D8CentralProduct 6)) :
    J4.IsTypeJ4Core ↥C ⟨z, hzC⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥C with hP
  have hPC : pCoreOf 2 C = P.map C.subtype := by
    rw [hP]
    rfl
  let e : ↥P ≃* ↥(pCoreOf 2 C) :=
    (Subgroup.equivMapOfInjective P C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hPC.symm)
  refine ⟨?_, J4.isExtraspecialPGroup_of_mulEquiv' e.symm hext, ?_, ?_, ?_⟩
  ·
    have h1 : CFSG.IsCharacteristicP 2 ↥C := by
      have h2 := CFSG.Quasithin.CT.charTwo_iff_internal.mp hchar
      exact h2
    exact ((CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥C 2).mp h1).symm
  · rw [Nat.card_congr e.toEquiv, hcard]
  · apply Subgroup.map_injective C.subtype_injective
    have h1 : (Subgroup.zpowers (⟨z, hzC⟩ : ↥C)).map C.subtype = Subgroup.zpowers z := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [h1, ← hcen, ← J4.center_map_mulEquiv' e, Subgroup.map_map, Subgroup.map_map]
    congr 1
  · exact ⟨e.trans (Classical.choice hiso)⟩

omit [Finite G] in
theorem ch8Vz_le_82 {L V : Subgroup G} {z : G} (hLN : L ≤ Subgroup.normalizer (V : Set G)) :
    ch8Vz V L z ≤ V := by
  have hRN : pCoreOf 2 (ch8Lz L z) ≤ Subgroup.normalizer (V : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans ((perfectCore_le _).trans inf_le_left)).trans
      hLN
  change ⁅V, pCoreOf 2 (ch8Lz L z)⁆ ≤ V
  rw [Subgroup.commutator_le]
  intro v hv r hr
  have h1 : r * v⁻¹ * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hRN hr) v⁻¹).mp (V.inv_mem hv)
  have := V.mul_mem hv h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using this

theorem stmt8_2_12_of
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12) (h8293 : Stmt8_2_9_three)
    (hm24 : SchurMult2M24) : Stmt8_2_12 := by
  have hcovL : KG82CoverL34 := kg82CoverL34_holds
  have hcovM : KG82CoverM22 := kg82CoverM22_holds
  have h8211 : Stmt8_2_11 :=
    stmt8_2_11_of h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hcovL hcovM hm24
  have hsimp : HSimple82 := hSimple82_holds
  have hcent : HCent82 := hCent82_holds
  have htype : HType82 := hType82_holds
  have hpar : HParab82 := hParab82_holds
  have hZ : HZ82 := hZ82_holds
  have hB : HB82 := hB82_holds
  have hcoc : HCoc82 := hCoc82_holds
  intro G _ _ T L I hyp h731 h821 hc hrow z hz hzV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hTL, hLN, hTV, hVT, hVL, hCLV, hTCL, hL0, hmod, hn1⟩ :=
    setup_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hsimp hcent htype hpar hcovL
      hcovM hm24 hyp h731 h821 hrow
  have hnot24 : ¬ Row711M24Code T L I := h8293 G T L I hyp h731 h821 hc hrow
  obtain ⟨H, h, k, hH, hh, h22⟩ := exists_concl822_of_82 h822 hyp h731 h821 hrow
  obtain ⟨-, -, -, hTabL, hTabM, -, hTab24c, hTU, -, hUA, -, -, hIU⟩ :=
    h825 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨-, -, -, -, hVLUB⟩ :=
    h828 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨-, hhI, -, -, -, hSyl, -, -, -, -, -, -, hA7, -, -, -, -, -, -⟩ := h22
  have h11 := h8211 G T L I hyp h731 h821 hc hrow hnot24 z hz hzV
  set V := fsuV T I with hVdef
  set A := ch82A V h with hAdef
  set U := ch82U V h with hUdef
  set LU := ch82LU L U with hLUdef
  have hzVT : z ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzV' : z ∈ V := hzVT.1
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := hzVT.2
  have hz2 : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  set z' : ↥V := ⟨z, hzV'⟩ with hz'def
  have hz'1 : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hchar := charTwo_centralizer_82 hyp.fsu.qtke.2.1 hyp.fsu.sylow hz hzT
  have hFC : quasithinGenFitting (Subgroup.centralizer ({z} : Set G)) =
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr hchar
  have hSc := card_autOn_inf_of_sylow (isSylowIn_top_of_fsu hyp.fsu) hTL hTV
  have hSz : z' ∈ fixV (autOn (T ⊓ L) V) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T := ht.1
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      Subgroup.mem_centralizer_iff.mp hzT t ht', mul_inv_cancel_right]
  have hSH : autOn (T ⊓ L) V ≤ autOn L V := Subgroup.map_mono fun x hx => hx.2
  have hSV : IsSylowVec82 (autOn L V) z' := ⟨_, hSH, hSc, hSz⟩
  have hAT : A ≤ T := fun x hx =>
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl hx.2).1
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hA7]
    exact inf_le_right
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAT.trans hTL
  have hAp : IsPGroup 2 ↥A := hyp.fsu.sylow.1.to_le hAT
  have hAe : IsElemAbelian 2 A := isElemAbelian_of_le_conjSub_82 hV fun x hx => hx.1
  have hUV : U ≤ V := inf_le_left
  have hUT : U ≤ T := hUV.trans hVT
  have hUp : IsPGroup 2 ↥U := (isPGroup_of_isElemAbelian_two hV).to_le hUV
  have hfixX : fixV (autOn A V) = U.subgroupOf V := fixV_autOn_82 hAN
  have hXc : Nat.card ↥(autOn A V) = 2 ^ mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) :=
    card_autOn_82 hAN hAp
  have hfixXc : Nat.card ↥(fixV (autOn A V)) = 2 ^ rk ↥U := by
    rw [hfixX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv,
      card_eq_two_pow_of_isPGroup hUp]
  have hSU : autOn (T ⊓ L) V ≤ stabSub (fixV (autOn A V)) := by
    rw [hfixX]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T := ht.1
    rw [mem_stabSub]
    intro u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hTU ht') u).symm
  have hLUbar : perfectCore (autOn L V ⊓ stabSub (fixV (autOn A V))) = autOn LU V := by
    rw [hfixX, ← autOn_inf_normalizer_82 hUV, ← autOn_perfectCore_82 (inf_le_left.trans hLN)]
    rfl
  have hLUN : LU ≤ Subgroup.normalizer (V : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans hLN
  have hCLp : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hCLV]
    exact isPGroup_of_isElemAbelian_two hV
  have hWbar : vz82 (autOn L V) z' = (ch8Vz V L z).subgroupOf V := vz82_eq_82 hzV' hLN hCLp
  have hrkU : 1 ≤ rk ↥U := by
    rcases hrow with ⟨n, hn⟩ | h' | h' | h'
    · rw [(hTabL ⟨n, hn⟩).2.2.2]
      norm_num
    · rw [(hTabM h').2.2.2]
      norm_num
    · exact absurd h' hnot24
    · rw [(hTab24c h').2.2.2]
      norm_num
  have hU1 : U ≠ ⊥ := by
    intro h1
    have h2 : rk ↥U = 0 := by
      rw [h1]
      exact rk_bot
    omega
  have hzU : z ∈ U := mem_of_le_of_normalizer_82 hyp.fsu.sylow.1 hUV hUT hTU hU1 hz hzV
  have hhU : h ∈ Subgroup.centralizer (U : Set G) := hIU hhI
  have hhC : h ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hhU z hzU).symm
  have core : ∀ e : ℕ, 1 ≤ e → IsModel82e (autOn L V) e →
      (BinaryNineTensor (autOn L V) ⊤ ⊥ 1 ∧ Nat.card ↥(autOn A V) = 2 ^ 4 ∧
          Nat.card ↥(fixV (autOn A V)) = 2 ^ 4 ∨
        MathieuCode22 (autOn L V) ⊤ ⊥ ∧ Nat.card ↥(autOn A V) = 2 ^ 5 ∧
          Nat.card ↥(fixV (autOn A V)) = 2 ^ 4 ∨
        MathieuCocode24 (autOn L V) ⊤ ⊥ ∧ Nat.card ↥(autOn A V) = 2 ^ 6 ∧
          Nat.card ↥(fixV (autOn A V)) = 2 ^ 3) →
      ch8E V L z = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        pCoreOf 2 (ch8Lz L z) = ch8E V L z ⊔ V ∧ ch8Vz V L z = ch8E V L z ⊓ V ∧
        IsExtraspecialPGroup 2 ↥(ch8E V L z) ∧
        (Subgroup.center ↥(ch8E V L z)).map (ch8E V L z).subtype = Subgroup.zpowers z ∧
        Nonempty (↥(ch8E V L z) ≃* J4.D8CentralProduct e) ∧
        Nat.card ↥(ch8E V L z) = 2 ^ (2 * e + 1) := by
    intro e he hmode hBc
    obtain ⟨hWc, hRc, hRP, hmin, hirr, hfixW, hVP⟩ := hZ ↥V (autOn L V) e z' hmode hz'1 hSV
    obtain ⟨hWB, hWU⟩ := hB ↥V (autOn L V) (autOn A V) z' hBc (autOn_le_normalizer_82 hAL)
      (isElemAbelian_autOn_82 hAe) hz'1 ⟨_, le_inf hSH hSU, hSc, hSz⟩
    have hcoc' := hcoc ↥V (autOn L V) e z' hmode hz'1 hSV
    have hVzV : ch8Vz V L z ≤ V := ch8Vz_le_82 hLN
    rw [hLUbar, commV_autOn_82 hLUN, hWbar] at hWB
    rw [hfixX, hWbar] at hWU
    have hVzB : ch8Vz V L z ≤ ch82B V h := by
      intro x hx
      have h1 : (⟨x, hVzV hx⟩ : ↥V) ∈ (ch8Vz V L z).subgroupOf V := hx
      exact hVLUB (hWB h1)
    have hVzU : ¬ ch8Vz V L z ≤ U := fun h1 => hWU fun x hx => h1 hx
    obtain ⟨x, hxVz, hxU⟩ : ∃ x ∈ ch8Vz V L z, x ∉ U := by
      by_contra h1
      push Not at h1
      exact hVzU h1
    have hI : h ∈ ch82I V h := hhI
    have hyA : h * x * h⁻¹ ∈ A := by
      refine ⟨B6.mem_conjSub.mpr (by simpa [mul_assoc] using hVzV hxVz), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hI) x).mp (hVzB hxVz).2
    have hyU : h * x * h⁻¹ ∉ U := by
      intro h1
      apply hxU
      have h2 : h * x * h⁻¹ = x := by
        have := Subgroup.mem_centralizer_iff.mp hhU _ h1
        have h3 : h⁻¹ * (h * x * h⁻¹) * h = h * x * h⁻¹ := by
          rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
        calc h * x * h⁻¹ = h⁻¹ * (h * x * h⁻¹) * h := h3.symm
          _ = x := by group
      rw [← h2]
      exact h1
    have hyC : h * x * h⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
      intro h1
      apply hyU
      rw [hUA]
      exact ⟨hyA, h1⟩
    have hyE : h * x * h⁻¹ ∈ ch8E V L z := mem_conjClosure hhC hxVz
    have hEV : ¬ ch8E V L z ≤ Subgroup.centralizer (V : Set G) := fun h1 => hyC (h1 hyE)
    obtain ⟨hEQ, hREV, hVzEV, hcommE, hsqE, hEc, hVzc, hnc⟩ :=
      structure_E_82 hyp.fsu.sylow hTL hLN hVL hCLV hV hTV hVT hTCL hzV' hzT hz2 he hchar hWc hRc
        hRP hmin hirr hfixW hVP hcoc' h11 hEV
    have hzVz : z ∈ ch8Vz V L z := by
      have h1 : z' ∈ vz82 (autOn L V) z' :=
        (hfixW.symm.le.trans inf_le_left) (Subgroup.mem_zpowers z')
      rw [hWbar, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hVC' : V ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hc
    have hzE : ∀ y ∈ ch8E V L z, y * z = z * y := by
      intro y hy
      rw [hEQ] at hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy)
    obtain ⟨hext, hcen, hiso⟩ := extraspecial_d8_82 hz1 hz2 he hEc (le_conjClosure _ _)
      (fun a ha a' ha' => (Subgroup.mem_centralizer_iff.mp (hVC' (hVzV ha')) a (hVzV ha)))
      (fun a ha => hV.2 a (hVzV ha)) hVzc hzVz hzE hcommE hsqE hnc
    exact ⟨hEQ, hREV, hVzEV, hext, hcen, hiso, hEc⟩
  have hL3 : ∀ n : ℕ, Row711L3Nine T L I n →
      BinaryNineTensor (V := ↥V) (autOn L V) ⊤ ⊥ 1 ∧ ∀ _ : Row711L3Nine T L I 1,
      Nat.card ↥(autOn A V) = 2 ^ 4 ∧ Nat.card ↥(fixV (autOn A V)) = 2 ^ 4 := by
    intro n hn
    obtain rfl := hn1 n hn
    refine ⟨?_, fun hn' => ?_⟩
    · rw [← hL0]
      exact hn.2
    · rw [hXc, hfixXc, (hTabL ⟨1, hn'⟩).2.2.1, (hTabL ⟨1, hn'⟩).2.2.2]
      exact ⟨rfl, rfl⟩
  have hcoreL3 : ∀ n : ℕ, Row711L3Nine T L I n → _ := fun n hn => by
    obtain ⟨hB9, hdat⟩ := hL3 n hn
    obtain rfl := hn1 n hn
    exact core 4 (by norm_num) (Or.inl ⟨hB9, rfl⟩) (Or.inl ⟨hB9, hdat hn⟩)
  have hcoreM22 : Row711M22Code T L I → _ := fun h' => by
    have hM : MathieuCode22 (V := ↥V) (autOn L V) ⊤ ⊥ := by
      rw [← hL0]
      exact h'
    refine core 4 (by norm_num) (Or.inr (Or.inl ⟨hM, rfl⟩)) (Or.inr (Or.inl ⟨hM, ?_, ?_⟩))
    · rw [hXc, (hTabM h').2.2.1]
    · rw [hfixXc, (hTabM h').2.2.2]
  have hcoreM24 : Row711M24Cocode T L I → _ := fun h' => by
    have hM : MathieuCocode24 (V := ↥V) (autOn L V) ⊤ ⊥ := by
      rw [← hL0]
      exact h'
    refine core 6 (by norm_num) (Or.inr (Or.inr ⟨hM, rfl⟩)) (Or.inr (Or.inr ⟨hM, ?_, ?_⟩))
    · rw [hXc, (hTab24c h').2.2.1]
    · rw [hfixXc, (hTab24c h').2.2.2]
  have hgen : ch8E V L z = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      pCoreOf 2 (ch8Lz L z) = ch8E V L z ⊔ V ∧ ch8Vz V L z = ch8E V L z ⊓ V := by
    rcases hrow with ⟨n, hn⟩ | h' | h' | h'
    · obtain ⟨h1, h2, h3, -⟩ := hcoreL3 n hn
      exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, -⟩ := hcoreM22 h'
      exact ⟨h1, h2, h3⟩
    · exact absurd h' hnot24
    · obtain ⟨h1, h2, h3, -⟩ := hcoreM24 h'
      exact ⟨h1, h2, h3⟩
  refine ⟨hFC, ⟨fun n hn => (hcoreL3 n hn).2.2.2.2.2.1, fun h' => (hcoreM22 h').2.2.2.2.2.1,
    fun h' => ⟨(hcoreM24 h').2.2.2.2.2.1, ?_⟩⟩, hgen⟩
  obtain ⟨hEQ, -, -, hext, hcen, hiso, hEc⟩ := hcoreM24 h'
  rw [hEQ] at hext hcen hiso hEc
  exact isTypeJ4Core_of_82 _ hchar hext hEc hcen hiso

end L8212G

end CFSG.Quasithin.H13
