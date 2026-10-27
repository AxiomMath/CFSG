module

public import CFSG.Quasithin.Vol2.Ch3xModule
public import CFSG.Quasithin.Vol2.Ch3xLemma1414
public import CFSG.Quasithin.EmptyFaithful.S1414
public import CFSG.Quasithin.EmptyFaithfulMultiple.Input311Solvable
public import CFSG.Quasithin.EmptyFaithful.S1414Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1414

variable {G : Type} [Group G] [Finite G]

theorem step1414_core {T M₁ P K₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT₁ : IsSylowTwoOf T M₁) (hVT : V ≤ T) (hMN : M₁ ≤ Subgroup.normalizer (V : Set G))
    (hsolvM : perfectCore M₁ ≤ Subgroup.centralizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hV)))}
    (hS : S1417.BlockSystem (autI hV M₁) (autI hV (thompsonJ M₁)) I)
    (hPmem : P ∈ uFamHat K₀ T) (hPM₁ : P ≤ M₁) (hPJ : P ≤ thompsonJ M₁ ⊔ T)
    (hPC : ¬ P ≤ (M₁ ⊓ Subgroup.centralizer (V : Set G)) ⊔ T)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2)
    (hJQ : ¬ thompsonJ T ≤ pCoreOf 2 P) :
    IsSylowTwoOf (baum T) (oTwoUpper P ⊔ baum T) := by
  obtain ⟨N, hmin⟩ := minParabolic_of_uFamHat hT₁ hPmem hPM₁
  have hsolvP := isSolvable_of_uFamHat hT₁ hPmem hPM₁ hMN hsolvM hPC
  have hTP : T ≤ P := hPmem.1.2.1.le
  have hVP : V ≤ P := hVT.trans hTP
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPM₁.trans hMN
  have hKP : oTwoUpper P ≤ P := oTwoUpper_le P
  have hKn : ∀ p ∈ P, ∀ k ∈ oTwoUpper P, p * k * p⁻¹ ∈ oTwoUpper P := fun p hp k hk =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper P hp) k).mp hk
  have hodd := Ch3x.odd_card_autI_oTwoUpper hV hT₁.2.1 hT₁.1 hPN hPJ hS
  have hKV : ¬ oTwoUpper P ≤ Subgroup.centralizer (V : Set G) := by
    intro hK
    apply hPC
    rw [hmin.eq_twoResidual_sup, F6.twoResidual_eq_oTwoUpper]
    exact sup_le_sup_right (le_inf (hKP.trans hPM₁) hK) T
  obtain ⟨W, hWV, hWel, hWred, hWnc⟩ :=
    Ch3x.exists_internal_twoReduced hV hPN hVP hKP hKn hodd hKV
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G) := by
    intro hle
    apply hJQ
    have := hmin.inf_centralizer_eq_pCoreOf hWred hWnc
    rw [← this]
    exact le_inf (B6.thompsonJ_le T) hle
  obtain ⟨-, -, hSyl, -⟩ := E2_3_two_of_isSolvable hWel hmin hsolvP hSQT hWred hJW
  rwa [F6.twoResidual_eq_oTwoUpper] at hSyl

theorem lemma_1414_core (h1413 : StageLemma1413)
    (h311 : EmptyFaithfulMultiple.Input311Solvable) : StageLemma1414 := by
  intro G _ _ T hsimple hnonab hqtke hsylow hfaith M hMmax hJM
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
  have h2 : IsUniqueM (M ⊓ Subgroup.normalizer (baum T : Set G)) M ∧ CGS (baum T) ≤ M := by
    have hmax : IsOrdMaximalIn T (InM T) M := hMmax
    have := lemma_14_1_2_two hEven S (by rw [hS]; exact hmax) (hV M hMM)
      (by rw [hS]; exact hJM) (Or.inl (by rw [hS]; rfl))
    rwa [hS] at this
  obtain ⟨hU, hCGS⟩ := h2
  have hNJ : Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
    (normalizer_thompsonJ_le_CGS hT2 hT1).trans hCGS
  refine ⟨hMM, fun M₁ hM₁ => ?_⟩
  have hTM₁ : T ≤ M₁ := hM₁.2
  have hT₁ : IsSylowTwoOf T M₁ := ⟨hTM₁, hT2, hodd hTM₁⟩
  have hV₁ := hV M₁ hM₁
  have hMN : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G) := hV₁.2.1
  have hJTM₁ : thompsonJ T ≤ M₁ := (C1GN.thompsonJ_le T).trans hTM₁
  by_cases hJV : thompsonJ T ≤ Subgroup.centralizer (VZ T M₁ : Set G)
  · exact ordLE_of_le_centralizer hT₁ hMN hNJ hJV
  set I : Subgroup G := thompsonJ M₁ with hI
  have hIM : I ≤ M₁ := C1GN.thompsonJ_le M₁
  have hMI : M₁ ≤ Subgroup.normalizer (I : Set G) := fun x hx =>
    normalizer_le_normalizer_thompsonJ M₁ (Subgroup.le_normalizer hx)
  have hJTI : thompsonJ T ≤ I := B6.thompsonJ_le_of_sylow hT₁
  have hTI : T ⊔ I ≤ M₁ := sup_le hTM₁ hIM
  set X : Subgroup G := thompsonJ M₁ ⊔ T with hX
  have hXM : X ≤ M₁ := sup_le hIM hTM₁
  have hTX : T ≤ X := le_sup_right
  have hIX : I ≤ X := le_sup_left
  have hTX' : IsSylowTwoOf T X := B6.isSylowTwoOf_mono hT₁ hTX hXM
  set K : Subgroup G := conjClosure T X with hK
  have hKX : K ≤ X :=
    conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem hh (hTX hz)) (X.inv_mem hh)
  have hTK : T ≤ K := le_conjClosure T X
  have hIK : I ≤ K := thompsonJ_le_conjClosure hT₁ hXM hTX hIX
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
  have hgen : ⨆ P ∈ uFamHat K T, P = K := gen_parabolics hTX' hTK_lt
  have hsolv : perfectCore M₁ ≤ Subgroup.centralizer (VZ T M₁ : Set G) :=
    h1413 G T hsimple hqtke hsylow hfaith M₁ (inH_of_inM hM₁) (VZ T M₁) hV₁
  have hblocks := blocks_of_solvable hqtke hsylow hM₁ hV₁ hJV hsolv
  have hP : ∀ P ∈ uFamHat K T, P ≤ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ (M₁ ⊓ M) := by
    intro P hPmem
    have hPK : P ≤ K := hPmem.1.1
    have hPM₁ : P ≤ M₁ := hPK.trans (hKX.trans hXM)
    by_cases hPC : P ≤ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ T
    · exact hPC.trans (sup_le le_sup_left (le_sup_of_le_right (le_inf hTM₁ hTM)))
    · refine le_sup_of_le_right (le_inf hPM₁ ?_)
      have hsylP : IsSylowTwoOf T P := B6.isSylowTwoOf_mono hT₁ hPmem.1.2.1.le hPM₁
      have hPH : InH T P := by
        have := inH_of_le S (by rw [hS]; exact hPmem.1.2.1.le) hPM₁
          (by rw [hS]; exact inH_of_inM hM₁)
        rwa [hS] at this
      by_cases hJQ : thompsonJ T ≤ pCoreOf 2 P
      ·
        have hJeq : thompsonJ (pCoreOf 2 P) = thompsonJ T :=
          B6.thompsonJ_eq_of_le hJQ (B6.pCoreOf_two_le_of_isSylowTwoOf hsylP)
        have hPNJ : P ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
          rw [← hJeq]
          exact (le_normalizer_pCoreOf 2 P).trans (normalizer_le_normalizer_thompsonJ _)
        exact fun x hx => hNJ (hPNJ hx)
      have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2 := fun p hp hp2 =>
        EmptyFaithfulMultiple.pRank_le_two_of_pCoreOf_ne_bot_cat hqtke hPH.2 hp hp2
      obtain ⟨hVe, I', hSb, -⟩ := hblocks
      have hVT : VZ T M₁ ≤ T :=
        (A4.le_pCoreOf_of_isTwoReducedIn hV₁).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT₁)
      have hSyl : IsSylowTwoOf (baum T) (oTwoUpper P ⊔ baum T) :=
        step1414_core hVe hT₁ hVT hMN hsolv hSb hPmem hPM₁ (hPK.trans hKX) hPC hSQT hJQ
      have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
        fun t ht => normalizer_le_normalizer_baum T (Subgroup.le_normalizer ht)
      have hbaumT : baum T ≤ T := C1GN.baum_le T
      have hbaum1 : baum T ≠ ⊥ := fun hb =>
        thompsonJ_ne_bot hT2 hT1 (le_bot_iff.mp (hb ▸ thompsonJ_le_baum T))
      have hM₀ : InH T (M ⊓ Subgroup.normalizer (baum T : Set G)) := by
        refine ⟨le_inf hTM hTS, fun h0 => hbaum1 (le_bot_iff.mp ?_)⟩
        rw [← h0]
        exact le_pCoreOf_of_le_normalizer 2 (le_inf (hbaumT.trans hTM) Subgroup.le_normalizer)
          inf_le_right (hT2.to_le hbaumT)
      have hPuniq : ∃ N : Subgroup G, IsUniqueMaxOver P T N := by
        obtain ⟨N, hN⟩ := Set.ncard_eq_one.mp hPmem.1.2.2
        exact ⟨N, hN⟩
      have hPsolv : Group.IsSolvable ↥P :=
        isSolvable_of_uFamHat hT₁ hPmem hPM₁ hMN hsolv hPC
      obtain ⟨R₀, hR₀1, hR₀S, hR₀N⟩ := h311 G T hsimple hnonab hqtke hsylow
        (M ⊓ Subgroup.normalizer (baum T : Set G)) P (baum T) hM₀ hPH hPsolv hPuniq hbaum1 hbaumT
        hSyl inf_le_right
      have hR₀2 : IsPGroup 2 R₀ := hT2.to_le (hR₀S.trans hbaumT)
      obtain ⟨M'', hM'', hNM''⟩ := exists_maxTwoLocal_ge
        (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀1, hR₀2, rfl⟩
      have hM''M : M'' = M := hU.2 M'' ⟨hM'', le_trans le_sup_left (hR₀N.trans hNM'')⟩
      exact hM''M ▸ (le_sup_right.trans hR₀N).trans hNM''
  have hKle : K ≤ (M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G)) ⊔ (M₁ ⊓ M) := by
    rw [← hgen]
    exact iSup₂_le fun P hPmem => hP P hPmem
  have hIle := hIK.trans hKle
  refine ordLE_of_decomp hMN fun x hx => ?_
  obtain ⟨i, hi, y, hy, rfl⟩ := frattini_decomp hT₁ hIM hMI hJTI x hx
  have hle : M₁ ⊓ M ≤ Subgroup.normalizer
      ((M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (le_normalizer_inf_centralizer hMN)
  have hi' := hIle hi
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hi'
  obtain ⟨c, hc, a, ha, rfl⟩ := Set.mem_mul.mp hi'
  exact ⟨c, hc, a * y, ⟨M₁.mul_mem ha.1 hy.1, M.mul_mem ha.2 (hNJ hy.2)⟩, by rw [mul_assoc]⟩

end S1414

end CFSG.Quasithin
