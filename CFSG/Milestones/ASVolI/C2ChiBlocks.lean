module

public import CFSG.Milestones.ASVolI.C2
public import CFSG.Quasithin.H13.U3LCE
public import CFSG.Quasithin.Background.C24PfProved
public import CFSG.Quasithin.MS93.MResOrd
public import CFSG.Quasithin.Background.SmithC27Holds
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideC2h_normalizer_le_normalizer_normalizer {G : Type} [Group G] (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ Subgroup.normalizer (S : Set G),
      g * x * g⁻¹ ∈ Subgroup.normalizer (S : Set G) := fun g hg x hx =>
    (Subgroup.normalizer (S : Set G)).mul_mem
      ((Subgroup.normalizer (S : Set G)).mul_mem hg hx) ((Subgroup.normalizer (S : Set G)).inv_mem hg)
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (S : Set G)).inv_mem hg) _ hx
  simpa [mul_assoc] using this

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits in
theorem burnsideC2h_asc24Two (G : Type) [Group G] [Finite G]
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hS : ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X)
    (hTC : ASC24TwoChar G) : ASC24Two G := by
  intro H R M L hyp hL hLc hLq
  by_cases hRN : R ≤ Subgroup.normalizer (L : Set G)
  · exact Or.inr hRN
  obtain ⟨ρ, hρR, hρN⟩ := SetLike.not_le_iff_exists.mp hRN
  have hR := hyp.radical
  have hRH : R ≤ H := hR.1
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  obtain ⟨T, hT, hRT⟩ := EscapingLocal.exists_isSylowTwoOf_ge hRH hR2
  obtain ⟨hHT, hcase⟩ := a3Orbits_of_a37_a38 (G := G) hA37 hA38 H T L hyp.sqtk hT hL
  rcases hcase with hTN | ⟨t, -, -, hTL, -, -, -⟩
  · exact absurd (hTN ρ (hRT hρR)) hρN
  have hρne : conjByElt ρ L ≠ L := fun he =>
    hρN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hmemT : ∀ σ ∈ T, conjByElt σ L = L ∨ conjByElt σ L = conjByElt t L := by
    intro σ hσ
    have h1 : conjByElt σ L ∈ conjSubgroupsBy T L := ⟨σ, hσ, rfl⟩
    rw [hTL] at h1
    exact h1
  have hρt : conjByElt ρ L = conjByElt t L := (hmemT ρ (hRT hρR)).resolve_left hρne
  have hmemH : ∀ h ∈ H, conjByElt h L = L ∨ conjByElt h L = conjByElt ρ L := by
    intro h hh
    have h1 : conjByElt h L ∈ conjSubgroupsBy H L := ⟨h, hh, rfl⟩
    rw [hHT, hTL] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans hρt.symm)
  have hLP : conjByElt ρ L ≤ conjClosure L R := by
    intro y hy
    have hy' : ρ⁻¹ * y * ρ ∈ L := mem_conjByElt.mp hy
    have := mem_conjClosure hρR hy'
    simpa [mul_assoc] using this
  have hPeq : conjClosure L R = conjClosure L H := by
    refine le_antisymm (conjClosure_mono le_rfl hRH) ?_
    refine conjClosure_le fun h hh z hz => ?_
    have hzh : h * z * h⁻¹ ∈ conjByElt h L := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hz
    rcases hmemH h hh with e | e
    · rw [e] at hzh
      exact le_conjClosure L R hzh
    · rw [e] at hzh
      exact hLP hzh
  have hPnorm : H ≤ Subgroup.normalizer (conjClosure L R : Set G) := by
    rw [hPeq]
    exact le_normalizer_conjClosure L H
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hYH : Y ≤ H := C2Push.conjClosure_sup_le hRH hLH
  have hRY : R ≤ Y := le_sup_right
  have hLY : L ≤ Y := (le_conjClosure L R).trans le_sup_left
  have hYc : CharTwo Y := C24Pf.charTwo_conjClosure_sup hA37 hA38 hS hyp.sqtk hR hL hLc hLq
  have hRadY : IsTwoRadicalIn Y R := by
    refine ⟨hRY, hR.2.1, le_antisymm (le_pCoreOf_inf_normalizer hRY hR2) ?_⟩
    have hNY : H ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
      fun n hn => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hPnorm hn.1, hn.2⟩
    have hQN : H ⊓ Subgroup.normalizer (R : Set G) ≤
        Subgroup.normalizer ((Y ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) :=
      fun n hn => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hNY hn, burnsideC2h_normalizer_le_normalizer_normalizer _ hn.2⟩
    have h2 : pCoreOf 2 (Y ⊓ Subgroup.normalizer (R : Set G)) ≤
        pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_le_normalizer 2
        ((pCoreOf_le 2 _).trans (inf_le_inf_right _ hYH))
        (fun n hn => normalizer_le_normalizer_pCoreOf 2 _ (hQN hn))
        (pCoreOf_isPGroup 2 _)
    exact h2.trans hR.2.2.symm.le
  have hYhyp : HypC23 Y R (Y ⊓ M) := by
    refine ⟨hyp.sqtk.mono hYH, hRadY, inf_le_left, ?_, ?_⟩
    · exact le_inf (cgsIn_le Y R) ((C2Nine.cgsIn_mono_left hYH R).trans hyp.cgs)
    · exact B6.isSylowTwoOf_mono hyp.sylow (le_conjClosure R (Y ⊓ M))
        (conjClosure_mono le_rfl inf_le_right)
  exact hTC Y R (Y ⊓ M) L hYhyp hYc (cComp_mem_of_le hL hLY hYH) hLc hLq

open CFSG.Quasithin.MS93.MRes in
theorem burnsideC2h_c27_of_desc
    (hdesc : S34RDescSp4) : C_2_7 :=
  fun G _ _ => CFSG.Quasithin.asc27Statement_of_c132 (asC132_of_descSp4 hdesc) G

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.MS93.MRes in
open scoped Pointwise in
@[expose] def burnsideC2h_C132At {G : Type} [Group G] [Finite G] (R K : Subgroup G) : Prop :=
  IsMSPair (K ⊔ R) R → K ∈ cComp (K ⊔ R) →
    ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) → C132Concl K



section BurnsideC2hCopies

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_three_of_residueRankTwo_of (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueRankTwo K V)
    (hr : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hBT : IsRadicalParabolic (autOn K V)) (hMax : MaxParabolicMaximal (autOn K V))
    (hHat : IsHatA6Block K → IsHat ↥(autOn K V) ↥(alternatingGroup (Fin 6)) →
      (∃ hV : IsElemAbelian 2 V, TripleA6Six (autI hV K) (commV (autI hV K))
        (fixV (autI hV K) ⊓ commV (autI hV K))) →
      IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) →
      pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V → C27Three H R M K V) :
    C27Three H R M K V := by
  obtain ⟨hmax, hO, hMS⟩ := maxParabolic_msPair h hs hBT hMax hJ hnS hr
  have hc := hC132 hMS h.mem_cComp_sup h.coe_sup
  have he : IsAltBlockType K 6 ∨ IsSp4Block K → C27Three H R M K V := fun hb =>
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hmax⟩))))
  rcases ht with ⟨n, F, iF, fF, hn, hF, ⟨e⟩, -⟩ | ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ |
    ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hhat, htr⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨n, F, iF, fF, hn, hF, ⟨e⟩⟩, hmax, hMS⟩))))))
  · exact he (blocks_of_statedSp hs hn hF e hc)
  · exact he (blocks_of_quasithinG2 hs hn hF e hc)
  · exact he (blocks_of_alt6 h hs e hc)
  · rcases blocks_of_isHat_alt6 hs hhat hc with hb | hb
    · exact he hb
    · exact hHat hb hhat htr hmax hO

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_three_of_residueRankTwo
    (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueRankTwo K V) : C27Three H R M K V :=
  burnsideC2h_three_of_residueRankTwo_of hC132 h hs hJ hnS ht (ResidueRankTwo.isRankTwoLie2Derived hs ht)
    ht.isRadicalParabolic ht.maxParabolicMaximal fun hb _ htr hmax hO =>
      Or.inr (Or.inr (Or.inl (c27_hat6 h hs hnS hb htr hmax hO hJ)))

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_three_of_residueTypeI
    (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueTypeI K V) : C27Three H R M K V := by
  rcases ht with ht | ht | ht
  · exact (false_of_residueRankOne h hs hJ hnS ht).elim
  · exact burnsideC2h_three_of_residueRankTwo hC132 h hs hJ hnS ht
  · exact three_of_residueRankThree h hs hJ hnS ht

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_three_of_caseII_six (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (C : CaseIICtx R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) 6) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hs := h.starHyp
  obtain ⟨T, hT, hTN⟩ := exists_sylow_le_normalizer_six (C.isPGroup_bar_R hs)
    (C.isRadSig_bar_R h.isTwoRadicalIn_sup hs)
  obtain ⟨T', hT', hT'R⟩ := C.exists_sylow_star_of_bar hT hTN
  obtain ⟨e⟩ := C.nonempty_equivK
  obtain ⟨e₀⟩ := hs.nonempty_quotCenterEquiv
  have hr : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (IsAlt.of_mulEquiv (e₀.trans (quotCenterCongr e)).symm isAlt_alternatingGroup_six)))))
  have hMS := isMSPair_of h hr (exists_sylow_le_normalizer_of_star hs hT' hT'R)
  have hb := blocks_of_alt6 h hs e (hC132 hMS h.mem_cComp_sup h.coe_sup)
  have hP := isParabolic2_MK_of_sylow h hs hT' hT'R (C.self_normalizing_K (Or.inl rfl))
  have hmax : MaxParabolicMaximal (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :=
    (maxParabolicMaximal_congr (e.trans Subgroup.topEquiv.symm)).mpr maxParabolicMaximal_alt6
  have hMP := (hmax _ hP (not_isBorelIn_MK h hs hnS) (autOn_MK_ne h hs)).1
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hMP⟩))))

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits Equiv Equiv.Perm in
theorem burnsideC2h_three_of_residueTypeII_sym (hC129 : ASC129Statement G) (hC132 : burnsideC2h_C132At R K)
    (h : Hyp27 H R M K) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hV : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hJK : ∀ T : Subgroup (MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)),
      IsSylowTwoOf T (jPStar hV R K) → jPStar hV R K = autI hV K ⊔ T)
    {n : ℕ} (hn : n = 6 ∨ n = 8) (π : Equiv.Perm (Fin n) →* ↥(jPStar hV R K))
    (hπ : (FFModel.symDn n).RealizesVia (jPStar hV R K) (commV (autI hV K))
      (fixV (autI hV K) ⊓ commV (autI hV K)) π)
    (hπK : ∀ σ : Equiv.Perm (Fin n),
      ((π σ : ↥(jPStar hV R K)) : MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)) ∈
        autI hV K ↔ σ ∈ alternatingGroup (Fin n)) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hs := h.starHyp
  have hKJ : autI hV K ≤ jPStar hV R K := by
    obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup _) ≤ jPStar hV R K)
      (IsPGroup.of_card (n := 0) (by simp))
    rw [hJK T hT]
    exact le_sup_left
  obtain ⟨C⟩ := nonempty_caseIICtx hs hV hn hKJ π hπ hπK
  rcases hn with rfl | rfl
  · exact burnsideC2h_three_of_caseII_six hC132 h hnS C
  · rcases radical_outer_eight (C.isPGroup_bar_R hs) (C.isRadSig_bar_R h.isTwoRadicalIn_sup hs)
      (C.not_bar_R_le_alt hs (by norm_num)) with ⟨T, hT, hTN⟩ | ⟨a, b, hab, hRab⟩ | ⟨g, hg⟩
    · exact three_of_caseII_eight_sylow h hnS C hT hTN
    · exact three_of_caseII_eight_swap hC129 h C hab hRab
    · exact (false_of_caseII_d8v4 h (C.conjB8 g) (by rw [CaseIICtx.bar_conjB8]; exact hg)).elim

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_G2StarData_three {R K V : Subgroup G} (hd : G2StarData R K V)
    (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V) :
    C27Three H R M K V := by
  have hB : IsG2Block K := isG2Block_of_card_autOn h hs hd.card_K
    (hC132 (hd.isMSPair h hs hnS hrad) h.mem_cComp_sup h.coe_sup)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hB, hd.g2Two, (hd.maxParabolic h hs hnS hrad).2⟩)))))

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_three_of_residueTypeII_g2_of_radical
    (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V)
    (hV : IsElemAbelian 2 V)
    (hKT : ∀ T : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf T (jPStar hV R K) →
      jPStar hV R K = autI hV K ⊔ T)
    (hG : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
        (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ g : ↥(quasithinG2 F),
          ((π g : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
            (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    C27Three H R M K V :=
  burnsideC2h_G2StarData_three (g2StarData_of hs hV hKT hG).2 hC132 h hs hnS hrad

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.LieType.BorelTits in
theorem burnsideC2h_three_of_residueTypeII_g2
    (hC132 : burnsideC2h_C132At R K) (h : Hyp27 H R M K) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hV : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hKT : ∀ T : Subgroup (MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)),
      IsSylowTwoOf T (jPStar hV R K) → jPStar hV R K = autI hV K ⊔ T)
    (hG : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
        (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ g : ↥(quasithinG2 F),
          ((π g : ↥(jPStar hV R K)) :
              MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)) ∈ autI hV K ↔
            (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  burnsideC2h_three_of_residueTypeII_g2_of_radical hC132 h h.starHyp hnS
    (pCore_autOn_inf_normalizer_R h.isTwoRadicalIn_sup h.starHyp) hV hKT hG


end BurnsideC2hCopies

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.MS93.MRes in
@[expose] def burnsideC2h_ResidueCaseII (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M K : Subgroup G, Hyp27 H R M K → ¬ IsChiBlock2 H K → ¬ IsExcA7Block K →
    ¬ IsSylowTwoOf R (K ⊔ R) → NoSp4Quot K →
    ResidueTypeII R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.MS93.MRes CFSG.LieType.BorelTits in
theorem burnsideC2h_residueCaseII_holds {G : Type} [Group G] [Finite G]
    (hC129 : ASC129Statement G)
    (hC132 : ∀ R K : Subgroup G, NoSp4Quot K → burnsideC2h_C132At R K) :
    burnsideC2h_ResidueCaseII G := by
  intro H R M K h _ _ hnS hSp hII
  obtain ⟨hV, -, hJK, ⟨n, hn, π, hπ, hπK⟩ | hG2⟩ := hII
  · exact burnsideC2h_three_of_residueTypeII_sym hC129 (hC132 R K hSp) h hnS hV hJK hn π hπ hπK
  · exact burnsideC2h_three_of_residueTypeII_g2 (hC132 R K hSp) h hnS hV hJK hG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.MS93.MRes CFSG.LieType.BorelTits in
theorem burnsideC2h_asc27Residue_of_caseII {G : Type} [Group G] [Finite G]
    (hC132 : ∀ R K : Subgroup G, NoSp4Quot K → burnsideC2h_C132At R K)
    (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    (hI : B5.B51IrrInputs) (hC124 : C124StatementSQTK (G := G))
    (hII : burnsideC2h_ResidueCaseII G) :
    ∀ H R M K V : Subgroup G, HypC23 H R M → K ∈ cComp H →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
      R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
      ¬ IsChiBlock2 H K → ¬ IsExcA7Block K → ¬ IsSylowTwoOf R (K ⊔ R) → NoSp4Quot K →
      C27Concl H R M K V := by
  intro H R M K V hyp hK hq hc hn hR hV hnchi hnexc hnS hSp
  subst hV
  have h : Hyp27 H R M K := Hyp27.mk' hyp hK hq hc hn hR
  refine c27Concl_of_parts (c27_one h) (c27_two h) ?_
  rcases residue_cases hA21 hB51 hI hC124 h h.starHyp hnchi hnexc with ⟨hJ, ht⟩ | ht
  · exact burnsideC2h_three_of_residueTypeI (hC132 R K hSp) h h.starHyp hJ hnS ht
  · exact hII H R M K h hnchi hnexc hnS hSp ht

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.MS93.MRes CFSG.LieType.BorelTits in
theorem burnsideC2h_c27_noSp4 (G : Type) [Group G] [Finite G]
    (hC132 : ∀ R K : Subgroup G, NoSp4Quot K → burnsideC2h_C132At R K) :
    ∀ H R M K V : Subgroup G, HypC23 H R M → K ∈ cComp H →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
      R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
      NoSp4Quot K → C27Concl H R M K V := by
  intro H R M K V hyp hK hq hc hn hR hV hSp
  have hres := burnsideC2h_asc27Residue_of_caseII hC132 asA21SQTKSection B5.asB51_holds
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
    (C124.c124StatementSQTK_of_e22 e22StatementNoN_proved G)
    (burnsideC2h_residueCaseII_holds (H13.VolI.asc129Statement_holds G) hC132)
  by_cases hcase : IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)
  · have h : Hyp27 H R M K := Hyp27.mk' hyp hK hq hc hn hR
    subst hV
    exact c27Concl_of_cases (H13.VolI.asc129Statement_holds G)
      (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
      asA21SQTKSection asA36NoOddCover_holds B5.asB51_holds h hcase
  · simp only [not_or] at hcase
    exact hres H R M K V hyp hK hq hc hn hR hV hcase.1 hcase.2.1 hcase.2.2 hSp

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.MS93.MRes in
@[expose] def burnsideC2h_C27NoSp4 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M K V : Subgroup G, HypC23 H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
    NoSp4Quot K → C27Concl H R M K V

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.MS93.MRes CFSG.LieType.BorelTits in
theorem burnsideC2h_c27_of_noSp4Quot (G : Type) [Group G] [Finite G]
    : burnsideC2h_C27NoSp4 G :=
  burnsideC2h_c27_noSp4 G fun R K hSp hMS hL hG => asC132NoSp4_holds G (K ⊔ R) R K hMS hL hG hSp

section



theorem as_C_2_4
    : C_2_4 := by
  intro G _ _ H R M L hyp hL hLc hLq
  have hA37 : ∀ (Y : Type) [Group Y], CFSG.Quasithin.SQTKHyp Y → CFSG.Quasithin.A37Statement Y :=
    CFSG.Quasithin.a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
  have hA38 : ∀ (Y : Type) [Group Y], CFSG.Quasithin.SQTKHyp Y → CFSG.Quasithin.A38Part3 Y :=
    CFSG.Quasithin.a38ForSQTK_of_cat (CFSG.QuasithinUnique.Vol2Native.a38ForSQTKCat_of_facts
      CFSG.Quasithin.mult2Fact CFSG.QuasithinUnique.Vol2Native.a134SQTKFactCat
      CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
      CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
  have hS : ∀ (X : Type) [Group X], CFSG.Quasithin.A38Types X → IsSimpleGroup X :=
    fun _ _ h => CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types h
  have h1 := CFSG.Quasithin.H13.U3.asc24One_holds G H R M L hyp hL hLc hLq
  have h2 := burnsideC2h_asc24Two G hA37 hA38 hS (CFSG.Quasithin.C24Pf.asc24TwoChar_proved G)
    H R M L hyp hL hLc hLq
  refine ⟨fun hsyl => ?_, h2⟩
  rcases h1 hsyl with hLM | ⟨hchi, ⟨V, hV, A, hA, hoff⟩, hborel⟩
  · exact Or.inl hLM
  · refine Or.inr ⟨hchi, ⟨CFSG.Quasithin.twoReducedJoin
      (L ⊔ (R ⊓ Subgroup.normalizer (L : Set G))), ⟨?_, fun W hW =>
        CFSG.Quasithin.A4.le_twoReducedJoin hW⟩, A, hA, hoff.1, fun hle => hoff.2 ?_⟩, hborel⟩
    · exact CFSG.Quasithin.A4.isTwoReducedIn_twoReducedJoin _
    · exact fun a ha => Subgroup.centralizer_le (CFSG.Quasithin.A4.le_twoReducedJoin hV) (hle ha)

end

end CFSG.ASVolI
