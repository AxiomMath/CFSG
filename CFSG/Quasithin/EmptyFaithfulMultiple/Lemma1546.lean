module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.Input311Solvable
public import CFSG.Quasithin.EmptyFaithful.S1414

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L1546

theorem card_oTwoUpper_of_card_eq_six {X : Type*} [Group X] {L : Subgroup X}
    (hL : Nat.card L = 6) : Nat.card (oTwoUpper L) = 3 := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := L) 3 (n := 1)
    (by rw [hL, pow_one]; norm_num)
  rw [pow_one] at hP
  have hidx : P.index = 2 := by
    have h := P.index_mul_card
    rw [hP, hL] at h
    omega
  have heq : oTwoUpper L = P.map L.subtype := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxL, hxo⟩
      have hcop : Nat.Coprime 2 (orderOf (⟨x, hxL⟩ : L)) := by
        rw [Subgroup.orderOf_mk]
        exact Nat.coprime_two_left.mpr hxo
      have hmem : (⟨x, hxL⟩ : L) ∈ P :=
        (Subgroup.zpowers_le.mpr (Subgroup.sq_mem_of_index_two hidx _))
          (A4.mem_zpowers_pow_of_coprime hcop)
      exact ⟨⟨x, hxL⟩, hmem, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine mem_oTwoUpper_of_odd y.2 ?_
      have hdvd : orderOf y ∣ 3 := hP ▸ Subgroup.orderOf_dvd_natCard P hy
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat (by decide) hdvd
  rw [heq, Subgroup.card_map_of_injective L.subtype_injective, hP]

theorem mem_of_odd_of_blocks {W : Type*} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
    {𝓗 I : Finset (Subgroup (MulAut W))} (hb : IsTransvectionBlocks J 𝓗) (hI : I ⊆ 𝓗) :
    IsPGroup 3 ↥(⨆ L ∈ I, oTwoUpper L) ∧
      ∀ y ∈ ⨆ L ∈ I, L, Odd (orderOf y) → y ∈ ⨆ L ∈ I, oTwoUpper L := by
  have hcardY : Nat.card ↥(⨆ L ∈ I, L) = 6 ^ I.card := by
    have h := hb.card_biSup_eq_prod (fun L => L) (fun L _ => le_rfl) I hI
    beta_reduce at h
    rw [h, Finset.prod_congr rfl (fun L hL => hb.card_eq L (hI hL))]
    simp
  have hcardR : Nat.card ↥(⨆ L ∈ I, oTwoUpper L) = 3 ^ I.card := by
    have h := hb.card_biSup_eq_prod (fun L => oTwoUpper L) (fun L _ => oTwoUpper_le L) I hI
    beta_reduce at h
    rw [h, Finset.prod_congr rfl
      (fun L hL => card_oTwoUpper_of_card_eq_six (hb.card_eq L (hI hL)))]
    simp
  have hRY : (⨆ L ∈ I, oTwoUpper L) ≤ ⨆ L ∈ I, L := iSup₂_mono fun L _ => oTwoUpper_le L
  have hconj : ∀ L ∈ I, ∀ g ∈ L, ∀ L' ∈ I,
      (oTwoUpper L').map (MulAut.conj g).toMonoidHom = oTwoUpper L' := by
    intro L hL g hg L' hL'
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    by_cases hLL : L = L'
    · subst hLL
      exact le_normalizer_oTwoUpper L hg
    · refine Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
      exact (hb.comm L (hI hL) L' (hI hL') hLL g hg x (oTwoUpper_le L' hx)).symm
  have hYN : (⨆ L ∈ I, L) ≤
      Subgroup.normalizer ((⨆ L ∈ I, oTwoUpper L : Subgroup (MulAut W)) : Set (MulAut W)) := by
    refine iSup₂_le fun L hL g hg => ?_
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
    refine iSup_congr fun L' => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hL' => hconj L hL g hg L' hL'
  have hrel : (⨆ L ∈ I, oTwoUpper L).relIndex (⨆ L ∈ I, L) = 2 ^ I.card := by
    have h := Subgroup.relIndex_mul_card (⨆ L ∈ I, oTwoUpper L) (⨆ L ∈ I, L)
    rw [inf_eq_left.mpr hRY, hcardR, hcardY] at h
    have h6 : (6 : ℕ) ^ I.card = 2 ^ I.card * 3 ^ I.card := by
      rw [← mul_pow]
      norm_num
    rw [h6] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  refine ⟨IsPGroup.of_card hcardR, fun y hy hodd => ?_⟩
  have hpow := B6.pow_mem_of_relIndex_eq_two_pow hYN hrel y hy
  have hcop : Nat.Coprime (2 ^ I.card) (orderOf y) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact (Subgroup.zpowers_le.mpr hpow) (A4.mem_zpowers_pow_of_coprime hcop)

theorem mem_of_odd_of_mem_sup {X : Type*} [Group X] [Finite X] {Y T' : Subgroup X}
    (hT' : IsPGroup 2 T') (hN : T' ≤ Subgroup.normalizer (Y : Set X)) {y : X}
    (hy : y ∈ T' ⊔ Y) (hodd : Odd (orderOf y)) : y ∈ Y := by
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hT' Y
  have h1 : Y.relIndex (T' ⊔ Y) = 2 ^ n := (B6.relIndex_sup_eq_of_le_normalizer hN).trans hn
  have hle : T' ⊔ Y ≤ Subgroup.normalizer (Y : Set X) := sup_le hN Subgroup.le_normalizer
  have hpow := B6.pow_mem_of_relIndex_eq_two_pow hle h1 y hy
  have hcop : Nat.Coprime (2 ^ n) (orderOf y) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  exact (Subgroup.zpowers_le.mpr hpow) (A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_fixed_of_isPGroup {W : Type*} [CommGroup W] [Finite W]
    {S : Subgroup (MulAut W)} (hS : IsPGroup 2 S) {U : Subgroup W}
    (hU : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) (hUne : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ s ∈ S, s u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction S U :=
    { smul := fun s u => ⟨(s : MulAut W) u, hU s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun s t u => Subtype.ext rfl }
  have hdvd : 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hUne
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : U) ∈ MulAction.fixedPoints S U := fun s =>
    Subtype.ext (map_one (s : MulAut W))
  obtain ⟨b, hb, hb1⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hb ⟨s, hs⟩)

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_of_odd {T V X : Subgroup G} (hVe : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hT2 : IsPGroup 2 T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXZ : X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hodd : Odd (Nat.card (autI hVe X))) : X ≤ Subgroup.centralizer (V : Set G) := by
  have hW : ∀ w : IntMod V hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨hsup, hinf⟩ := coprime_decomp hodd hW (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  have hTs : IsPGroup 2 (autI hVe T) := B2F.isPGroup_autI hVe hT2 hTV
  have hTA : ∀ s ∈ autI hVe T, B1.conjAut s (autI hVe X) = autI hVe X := by
    intro s hs
    obtain ⟨t, htT, rfl⟩ := (mem_autI hVe).1 hs
    rw [conjAut_eq_map, autI_cjSub hVe t.2 X, B2F.cjSub_eq_of_mem_normalizer (hTX htT)]
  have hinv : ∀ s ∈ autI hVe T, ∀ u ∈ commSub (⊤ : Subgroup (IntMod V hVe)) (autI hVe X),
      s u ∈ commSub (⊤ : Subgroup (IntMod V hVe)) (autI hVe X) := by
    intro s hs u hu
    have h := IsTransvectionBlocks.map_commSub_conjAut (autI hVe X) s
    rw [hTA s hs] at h
    rw [← h]
    exact ⟨u, hu, rfl⟩
  have hcomm : commSub (⊤ : Subgroup (IntMod V hVe)) (autI hVe X) = ⊥ := by
    by_contra hne
    obtain ⟨u, hu, hu1, hfix⟩ := exists_fixed_of_isPGroup hTs hinv hne
      (fun w => ⟨1, Subtype.ext (by simpa using hW w)⟩)
    have huT : u.val ∈ Subgroup.centralizer (T : Set G) :=
      (mem_fixV_autI hVe hTV u).1 fun s hs => hfix s hs
    have huZ : u.val ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨hVT u.val_mem, huT⟩, hVe.2 _ u.val_mem⟩
    have huA : u ∈ fixV (autI hVe X) := by
      refine (mem_fixV_autI hVe hXV u).2 (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
      exact (Subgroup.mem_centralizer_iff.mp (hXZ hx) u.val huZ).symm
    have hmem : u ∈ commSub (⊤ : Subgroup (IntMod V hVe)) (autI hVe X) ⊓
        ((⊤ : Subgroup (IntMod V hVe)) ⊓ fixV (autI hVe X)) := ⟨hu, Subgroup.mem_top _, huA⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  rw [hcomm, bot_sup_eq] at hsup
  rw [← autI_eq_bot_iff hVe hXV, eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext w
  have hw : w ∈ (⊤ : Subgroup (IntMod V hVe)) ⊓ fixV (autI hVe X) := by
    rw [hsup]
    exact Subgroup.mem_top w
  exact hw.2 a ha

theorem le_or_le_of_forall_mul {P T N A B : Subgroup G} (hP : MinParabolic P T N)
    (hTA : T ≤ A) (hTB : T ≤ B) (hfact : ∀ h ∈ P, ∃ a ∈ P ⊓ A, ∃ b ∈ P ⊓ B, h = a * b) :
    P ≤ A ∨ P ≤ B := by
  have hTP : T ≤ P := hP.isSylow.1
  have key : ∀ C : Subgroup G, T ≤ C → ¬ P ≤ C → P ⊓ C ≤ N := by
    intro C hTC hPC
    obtain ⟨N', hN', hle⟩ := exists_isMaxSubgroupIn (inf_lt_left.mpr hPC)
    rw [← hP.eq_of_maximal hN' ((le_inf hTP hTC).trans hle)]
    exact hle
  by_contra hcon
  obtain ⟨hA, hB⟩ := not_or.mp hcon
  have hPN : P ≤ N := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfact h hh
    exact N.mul_mem (key A hTA hA ha) (key B hTB hB hb)
  exact not_le_of_gt hP.maximal.1 hPN

end L1546

open L1546 in
theorem stmt1546_of (h311 : Input311Solvable) {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T) :
    Stmt1546 G T := by
  intro M hMmax hJcomm M₁ hM₁
  have hsimple := hyp.simple
  have hnonab := hyp.nonabelian
  have hqtke := hyp.qtke
  have hsylow := hyp.sylow
  have hMM : InM T M := hMmax.1
  have hTM : T ≤ M := hMM.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hsylow
  have hEven : quasithinEvenCharacteristic G := hqtke.2.1
  have hT2 : IsPGroup 2 T := hsylow.1
  have hodd : ∀ {K : Subgroup G}, T ≤ K → ¬ 2 ∣ T.relIndex K := by
    intro K hTK hd
    apply hsylow.2
    refine dvd_trans hd ?_
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTK
  have hF : ∀ K : Subgroup G, InM T K →
      K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K := fun K hK =>
    hEven K hK.1.1 ⟨S, by rw [hS]; exact hK.2⟩
  have hT1 : T ≠ ⊥ := by
    intro hbot
    have hle : pCoreOf 2 M ≤ T := by
      have := pCoreOf_two_le_sylow M S (by rw [hS]; exact hTM)
      rwa [hS] at this
    exact pCoreOf_ne_bot_of_isTwoLocal hMM.1.1 (le_bot_iff.mp (hbot ▸ hle))
  have hV : ∀ K : Subgroup G, InM T K → IsTwoReducedIn K (VZ T K) := fun K hK =>
    isTwoReducedIn_conjClosure_of_sylowIn hK.2 hT2 (hodd hK.2) (hF K hK) le_rfl
  have hJM : thompsonJ T ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    refine le_inf ((C1GN.thompsonJ_le T).trans hTM) ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hJcomm
    exact Subgroup.le_centralizer_iff.mp hJcomm
  have h142 : IsUniqueM (M ⊓ Subgroup.normalizer (baum T : Set G)) M ∧ CGS (baum T) ≤ M := by
    have hmax : IsOrdMaximalIn T (InM T) M := hMmax
    have := lemma_14_1_2_two hEven S (by rw [hS]; exact hmax) (hV M hMM)
      (by rw [hS]; exact hJM) (Or.inl (by rw [hS]; rfl))
    rwa [hS] at this
  obtain ⟨hU, hCGS⟩ := h142
  have hNJ : Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS hT2 hT1).trans hCGS
  have hTM₁ : T ≤ M₁ := hM₁.2
  have hT₁ : IsSylowTwoOf T M₁ := ⟨hTM₁, hT2, hodd hTM₁⟩
  have hV₁ := hV M₁ hM₁
  have hMN : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G) := hV₁.2.1
  by_cases hJV : thompsonJ T ≤ Subgroup.centralizer (VZ T M₁ : Set G)
  · exact S1414.ordLE_of_le_centralizer hT₁ hMN hNJ hJV
  have hsolv₁ : Group.IsSolvable M₁ := h2 M₁ hM₁
  have hVe : IsElemAbelian 2 (VZ T M₁) := hV₁.2.2.1
  have hVT : VZ T M₁ ≤ T := by
    have := le_sylow_of_isTwoReducedIn S (by rw [hS]; exact hTM₁) hV₁
    rwa [hS] at this
  have hTN : T ≤ Subgroup.normalizer (VZ T M₁ : Set G) := hTM₁.trans hMN
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (((Subgroup.closure_le _).mpr fun _ hz => hz.1 :
        quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G)).trans inf_le_right)
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) := fun t ht =>
    normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer ht)
  set I : Subgroup G := thompsonJ M₁ with hI
  have hIM : I ≤ M₁ := C1GN.thompsonJ_le M₁
  have hMI : M₁ ≤ Subgroup.normalizer (I : Set G) := fun x hx =>
    normalizer_le_normalizer_thompsonJ M₁ (Subgroup.le_normalizer hx)
  have hJTI : thompsonJ T ≤ I := B6.thompsonJ_le_of_sylow hT₁
  set X : Subgroup G := thompsonJ M₁ ⊔ T with hX
  have hXM : X ≤ M₁ := sup_le hIM hTM₁
  have hTX : T ≤ X := le_sup_right
  have hIX : I ≤ X := le_sup_left
  have hTX' : IsSylowTwoOf T X := B6.isSylowTwoOf_mono hT₁ hTX hXM
  set K : Subgroup G := conjClosure T X with hK
  have hKX : K ≤ X :=
    conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem hh (hTX hz)) (X.inv_mem hh)
  have hTK : T ≤ K := le_conjClosure T X
  have hIK : I ≤ K := S1414.thompsonJ_le_conjClosure hT₁ hXM hTX hIX
  have hTK_lt : T < K := by
    refine lt_of_le_of_ne hTK fun hEq => hJV ?_
    have hIT : I ≤ T := hEq ▸ hIK
    have h1 : I ≤ Subgroup.centralizer (VZ T M₁ : Set G) := by
      refine hV₁.2.2.2 I hIM hMI fun d hd => ?_
      obtain ⟨k, hk⟩ := hT2 ⟨d, hIT hd⟩
      refine ⟨k, ?_⟩
      have : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [this]
      exact Subgroup.one_mem _
    exact hJTI.trans h1
  have hgen : ⨆ P ∈ uFamHat K T, P = K := S1414.gen_parabolics hTX' hTK_lt
  obtain ⟨𝓗, 𝓘, B⟩ := E2.exists_blocks hVe hV₁ hsolv₁ hT₁ hJV
  obtain ⟨hR3, hRodd⟩ := mem_of_odd_of_blocks B.hb B.sub
  have hTsN : autI hVe T ≤ Subgroup.normalizer
      ((autI hVe I : Subgroup (MulAut (IntMod (VZ T M₁) hVe))) :
        Set (MulAut (IntMod (VZ T M₁) hVe))) := by
    intro t ht
    have h := E2.conjAut_autI_thompsonJ (autI_mono hVe hTM₁ ht)
    rw [conjAut_eq_map] at h
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  have hXodd : ∀ φ ∈ autI hVe X, Odd (orderOf φ) → φ ∈ ⨆ L ∈ 𝓘, oTwoUpper L := by
    intro φ hφ hoddφ
    rw [hX, autI_sup hVe (hIM.trans hMN) hTN, sup_comm] at hφ
    have hφI := mem_of_odd_of_mem_sup (B2F.isPGroup_autI hVe hT2 hTN) hTsN hφ hoddφ
    rw [B.eq] at hφI
    exact hRodd φ hφI hoddφ
  have hRle : (⨆ L ∈ 𝓘, oTwoUpper L) ≤ autI hVe M₁ := by
    refine (iSup₂_mono fun L _ => oTwoUpper_le L).trans ?_
    rw [← B.eq]
    exact autI_mono hVe hIM
  have hP : ∀ P ∈ uFamHat K T,
      P ≤ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ (M₁ ⊓ M) := by
    intro P hPmem
    have hPX : P ≤ X := hPmem.1.1.trans hKX
    have hPM₁ : P ≤ M₁ := hPX.trans hXM
    have hTP : T ≤ P := hPmem.1.2.1.le
    obtain ⟨N, hN⟩ := Set.ncard_eq_one.mp hPmem.1.2.2
    have hPsyl : IsSylowTwoOf T P := B6.isSylowTwoOf_mono hT₁ hTP hPM₁
    have hMP : MinParabolic P T N := ⟨hPsyl, hPmem.2, hN⟩
    have hPsolv : Group.IsSolvable P :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPM₁)
    have hPH : InH T P := by
      have := inH_of_le S (by rw [hS]; exact hTP) hPM₁ (by rw [hS]; exact inH_of_inM hM₁)
      rwa [hS] at this
    have hPF : CharTwo P := charTwo_of_inH hEven S (by rw [hS]; exact hPH)
    obtain ⟨hUP, hredP, hcase, -⟩ := B2_16 hPsolv hPF hPsyl rfl
    rcases hcase with ⟨-, hfact⟩ | ⟨hJP, -⟩
    ·
      rcases le_or_le_of_forall_mul hMP hTJ hTZ hfact with hPJ | hPZ
      · exact le_sup_of_le_right (le_inf hPM₁ (hPJ.trans hNJ))
      ·
        have hOle : oTwoUpper P ≤ preI hVe M₁ hMN (⨆ L ∈ 𝓘, oTwoUpper L) := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro x ⟨hxP, hxo⟩
          refine (mem_preI hVe).2 ⟨hPM₁ hxP,
            hXodd _ (convI_mem_autI hVe (hPX hxP) (hMN (hPM₁ hxP))) ?_⟩
          refine Odd.of_dvd_nat hxo ((orderOf_map_dvd _ _).trans ?_)
          rw [Subgroup.orderOf_mk]
        have hA3 : IsPGroup 3 (autI hVe (oTwoUpper P)) := by
          refine hR3.to_le ((autI_mono hVe hOle).trans ?_)
          rw [autI_preI hVe hRle]
        have hAodd : Odd (Nat.card (autI hVe (oTwoUpper P))) := by
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA3
          rw [hk]
          exact Odd.pow (by decide)
        have hOC : oTwoUpper P ≤ Subgroup.centralizer (VZ T M₁ : Set G) :=
          le_centralizer_of_odd hVe hVT hT2 hTN ((oTwoUpper_le P).trans (hPM₁.trans hMN))
            (hTP.trans (le_normalizer_oTwoUpper P)) ((oTwoUpper_le P).trans hPZ) hAodd
        have hPeq : T ⊔ twoResidual P = P := sup_twoResidual_eq hPsyl
        rw [F6.twoResidual_eq_oTwoUpper] at hPeq
        rw [← hPeq]
        exact sup_le (le_sup_of_le_right (le_inf hTM₁ hTM))
          (le_sup_of_le_left (le_inf ((oTwoUpper_le P).trans hPM₁) hOC))
    ·
      have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2 := fun p hp hp2 =>
        pRank_le_two_of_pCoreOf_ne_bot_cat hqtke hPH.2 hp hp2
      have hSyl : IsSylowTwoOf (baum T) (oTwoUpper P ⊔ baum T) := by
        have := (E2_3_two_of_isSolvable hUP hMP hPsolv hSQT hredP hJP).2.2.1
        rwa [F6.twoResidual_eq_oTwoUpper] at this
      refine le_sup_of_le_right (le_inf hPM₁ ?_)
      have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
        fun t ht => normalizer_le_normalizer_baum T (Subgroup.le_normalizer ht)
      have hbaumT : baum T ≤ T := C1GN.baum_le T
      have hbaum1 : baum T ≠ ⊥ := fun hb =>
        S1414.thompsonJ_ne_bot hT2 hT1 (le_bot_iff.mp (hb ▸ S1414.thompsonJ_le_baum T))
      have hM₀ : InH T (M ⊓ Subgroup.normalizer (baum T : Set G)) := by
        refine ⟨le_inf hTM hTS, fun h0 => hbaum1 (le_bot_iff.mp ?_)⟩
        rw [← h0]
        exact le_pCoreOf_of_le_normalizer 2 (le_inf (hbaumT.trans hTM) Subgroup.le_normalizer)
          inf_le_right (hT2.to_le hbaumT)
      obtain ⟨R₀, hR₀1, hR₀S, hR₀N⟩ := h311 G T hsimple hnonab hqtke hsylow
        (M ⊓ Subgroup.normalizer (baum T : Set G)) P (baum T) hM₀ hPH hPsolv ⟨N, hN⟩ hbaum1
        hbaumT
        hSyl inf_le_right
      have hR₀2 : IsPGroup 2 R₀ := hT2.to_le (hR₀S.trans hbaumT)
      obtain ⟨M'', hM'', hNM''⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge
        (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀1, hR₀2, rfl⟩
      have hM''M : M'' = M := hU.2 M'' ⟨hM'', le_trans le_sup_left (hR₀N.trans hNM'')⟩
      exact hM''M ▸ (le_sup_right.trans hR₀N).trans hNM''
  have hKle : K ≤ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ (M₁ ⊓ M) := by
    rw [← hgen]
    exact iSup₂_le fun P hPmem => hP P hPmem
  have hIle := hIK.trans hKle
  refine S1414.ordLE_of_decomp hMN fun x hx => ?_
  obtain ⟨i, hi, y, hy, rfl⟩ := S1414.frattini_decomp hT₁ hIM hMI hJTI x hx
  have hle : M₁ ⊓ M ≤ Subgroup.normalizer
      ((M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (S1414.le_normalizer_inf_centralizer hMN)
  have hi' := hIle hi
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hi'
  obtain ⟨c, hc, a, ha, rfl⟩ := Set.mem_mul.mp hi'
  exact ⟨c, hc, a * y, ⟨M₁.mul_mem ha.1 hy.1, M.mul_mem ha.2 (hNJ hy.2)⟩, by rw [mul_assoc]⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
