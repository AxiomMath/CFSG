module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1565B
public import CFSG.Quasithin.EmptyFaithful.S1565E
public import CFSG.Quasithin.EmptyFaithful.S1565J
public import CFSG.Quasithin.EmptyFaithful.S1565L17
public import CFSG.Quasithin.EmptyFaithful.S1565M11

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1565

section Elt

attribute [local instance] commGroupOfFact

theorem input15365TypesFour_of_eltC (h : Input15365TypesFourEltC) : Input15365TypesFourC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK I hV₁I hIU W hW hirr
  have hFU := factElem D.hF (le_conjClosure (ZS153 T M V₁) H)
  have hFI := factElem D.hF hIU
  obtain ⟨t₀, ht₀M, m, hodd, hpow, hgood⟩ := h G T Mc M V₁ V₂ H K t D hK I hV₁I hIU W hW hirr
  exact chiefFreeBelow15365_of_good_tilde D.hF D.H_eq M hV₁I hIU t₀ ht₀M hodd hpow hgood

theorem input15365FFnat_of_eltC (h : Input15365FFnatEltC) : Input15365FFnatC := by
  intro G _ _ T Mc M V₁ V₂ H K t D I hV₁I hIU W hW hirr hne hFF
  have hFU := factElem D.hF (le_conjClosure (ZS153 T M V₁) H)
  obtain ⟨t₀, ht₀M, m, hodd, hpow, hgood⟩ :=
    h G T Mc M V₁ V₂ H K t D I hV₁I hIU W hW hirr hne hFF
  intro a ha hb
  exact hgood a ha (hb t₀ (Subgroup.mem_subgroupOf.mpr ⟨t₀.2, ht₀M⟩))

end Elt

section Five

theorem input15365TypesFive_of_extC
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hOrth : OrthExcl) (hΩ : OmegaGood) : Input15365TypesFiveC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK I hV₁I hIU W hW hirr
  have hn := D.n_gt
  obtain ⟨hker, n, hn2, hshape, hB⟩ := e22CasesW_one_data D.e22 hn hK
  obtain ⟨hn3, hnodd⟩ := D.n_odd n hn2 (hshape.elim Or.inl fun h => Or.inr (Or.inl h)) hB
  exact typesFive_core hD36 hD37 hD321 hI5 hA37 hA38 hOrth hΩ D.hF D.sqtk D.H_eq hK M I
    D.ctx.hyp.T_le hV₁I hIU W hW hirr hker hn3 hnodd hshape hB

theorem input15365TypesFive_ofC
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) : Input15365TypesFiveC :=
  input15365TypesFive_of_extC hD36 hD37 hD321 hI5 hA37 hA38 orthExcl_of omegaGood_of

end Five

section Twist

attribute [local instance] commGroupOfFact

theorem input15365TwistFieldBig_ofC : Input15365TwistFieldBigC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr
  have hn := D.n_gt
  obtain ⟨hkerchar, hB⟩ := e22CasesW_two_data D.e22 hn hK0
  obtain ⟨n, hn2, hKs⟩ := e22CasesW_two_shape D.e22 hn hK0
  obtain ⟨hn3, -⟩ := D.n_odd n hn2 hKs hB
  have hFI := factElem D.hF hIU
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hirr' : subM (quasithinOmegaOneCenter T) (conjClosure I H) I ∈
      IrrPlusOn (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T))
        (orbSup (autIH (quasithinOmegaOneCenter T) I H T)
          (subM (quasithinOmegaOneCenter T) (conjClosure I H) I))
        (autIH (quasithinOmegaOneCenter T) I H T) := hIT
  have hnt := hnt_of_irrSec D.hF hIU hirr'.1.2.2.2.1
  exact twistFieldBig_of D.hF M I hIU hnt hkerchar hB D.three hn3 hKs

theorem input15365TypesFourTwist_of_bigC (hbig : Input15365TwistFieldBigC) :
    Input15365TypesFourTwistC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hshape
  have hn := D.n_gt
  obtain ⟨hkerchar, hB⟩ := e22CasesW_two_data D.e22 hn hK0
  have hFI := factElem D.hF hIU
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hirr' : subM (quasithinOmegaOneCenter T) (conjClosure I H) I ∈
      IrrPlusOn (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T))
        (orbSup (autIH (quasithinOmegaOneCenter T) I H T)
          (subM (quasithinOmegaOneCenter T) (conjClosure I H) I))
        (autIH (quasithinOmegaOneCenter T) I H T) := hIT
  have hnt := hnt_of_irrSec D.hF hIU hirr'.1.2.2.2.1
  exact typesFour_core_twist D.hF M I hIU hnt hK0 hkerchar hB
    (hbig G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr) hshape

theorem input15365TypesFourTwist_ofC : Input15365TypesFourTwistC :=
  input15365TypesFourTwist_of_bigC input15365TwistFieldBig_ofC

end Twist

section NatModule

attribute [local instance] commGroupOfFact

theorem input15365TypesFourElt_of_natmoduleC (h310 : D310)
    (h391 : D391) (hI4 : Insp4) (hNat : Input15365TypesFourNatModuleC) :
    Input15365TypesFourEltC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr
  have hn := D.n_gt
  obtain ⟨hkerchar, hB⟩ := e22CasesW_two_data D.e22 hn hK0
  obtain ⟨n, hn2, hKs⟩ := e22CasesW_two_shape D.e22 hn hK0
  obtain ⟨hn3, -⟩ := D.n_odd n hn2 hKs hB
  have hFI := factElem D.hF hIU
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hirr' : subM (quasithinOmegaOneCenter T) (conjClosure I H) I ∈
      IrrPlusOn (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T))
        (orbSup (autIH (quasithinOmegaOneCenter T) I H T)
          (subM (quasithinOmegaOneCenter T) (conjClosure I H) I))
        (autIH (quasithinOmegaOneCenter T) I H T) := hIT
  have hnt := hnt_of_irrSec D.hF hIU hirr'.1.2.2.2.1
  have hKH : K ≤ H := le_of_mem_cComp D.hF.K_cComp
  have hne : autIH (quasithinOmegaOneCenter T) I H K ≠ ⊥ := by
    rw [autIH_eq_map D.hF hKH]
    exact map_K_ne_bot D.hF hIU hnt
  have hfin : Finite ↥(autIH (quasithinOmegaOneCenter T) I H K) :=
    Finite.of_surjective _ (toAutI_surjective D.hF I)
  obtain ⟨σ, hσ, hz⟩ := exists_sigma_central D.hF hIU hne hkerchar
  obtain ⟨-, hF4⟩ := F918_4 D.hF D.sqtk hK0 hV₁I hIU hIT h310 h391 hI4
  have hNat' := hNat G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr
  rcases hF4 with hinv | hff | hD
  · exact typesFour_core_natW D.hF M I hIU hnt hK0 hkerchar hB (hNat' (Or.inl hinv))
  · exact typesFour_core_natW D.hF M I hIU hnt hK0 hkerchar hB (hNat' (Or.inr hff))
  · obtain ⟨hlist, ⟨t₀, ht₀T, ht₀V⟩, hsum⟩ := hD
    have hshape : ∀ n' : ℕ,
        (BinaryNaturalSL (autIH (quasithinOmegaOneCenter T) I H K)
            (subM (quasithinOmegaOneCenter T) (conjClosure I H) I)
            (subM (quasithinOmegaOneCenter T) (conjClosure I H) I ⊓
              fixV (autIH (quasithinOmegaOneCenter T) I H K)) 3 n' ∨
          BinaryNaturalSp4 (autIH (quasithinOmegaOneCenter T) I H K)
            (subM (quasithinOmegaOneCenter T) (conjClosure I H) I)
            (subM (quasithinOmegaOneCenter T) (conjClosure I H) I ⊓
              fixV (autIH (quasithinOmegaOneCenter T) I H K)) n') →
        TypesFourEltConcl D.hF M I hIU := by
      intro n' hn'
      exact input15365TypesFourTwist_ofC G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr
        ⟨_, t₀, ht₀T, hn'.imp (fun h => ⟨n', h⟩) (fun h => ⟨n', h⟩), (hsum t₀ ht₀T ht₀V).1⟩
    rcases hlist with ⟨n', h⟩ | ⟨n', h⟩ | h
    · exact hshape n' (Or.inl h)
    · exact hshape n' (Or.inr h)
    · exact absurd h (not_d310_exceptional hn3 hKs σ hσ hz)

end NatModule

theorem stage15365One_of_layer_inputsC (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hE22 : E2.E22StatementW) (i1 : Input15365Odd) (i2a : Input15365TypesFourC)
    (i2b : Input15365TypesFiveC) (i3 : Input15365FFnatC) : Stage15365One := by
  intro G _ _ T Mc M V₁ V₂ t c r45 r46 _r50 r49 r62 _r63 r64 H hH
  have hHTM : IsHTM153 T M H := ⟨hH.1, hH.2.1⟩
  refine le_antisymm ?_ (one_le_nParam hH.1.2)
  by_contra hlt
  have hn : 1 < E1.nParam H := not_le.mp hlt
  obtain ⟨K, hK, hHK, hq, hE⟩ := exists_e22_dataC hE22 h11 c hH hn
  have hF := hypF918_of_e22 h11 h113 c r45 r46 r49 r62 hHTM hK hHK hq
  have hthree := r49.threePrime_MH H hHTM
  have r47 : Res15347 T M V₁ := stage15347 G T Mc M V₁ V₂ t c r45 r46
  have hF91 := hypF91_of_stage15348 (stage15348 h11 h113) c r45 r46 r47 r49 hHTM
  have D : Data15365C G T Mc M V₁ V₂ H K t :=
    ⟨c, hH, (c.hyp.lemma_15_3_2_six h11).2 H hH, sqtkGroup_of_isHStar c hH, hthree, hHK, hF, hE, hn,
      odd_of_inputsC i1 hthree, r64 H hHTM hF91⟩
  obtain ⟨I, hV₁I, hIU, W, hW, hirr⟩ := exists_isIrrPlusTildeU hF
  have hIT := isIrrPlusTildeT_of_ambient hF hIU W hW hirr
  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hIT
  have hBelow : ChiefFreeBelow15365 hF M I := by
    by_cases hK0 : conjClosure K T = K
    · exact i2a G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr
    · exact i2b G T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr
  have hIHU : conjClosure I H ≤ conjClosure (ZS153 T M V₁) H :=
    conjClosure_le_conjClosure_U hIU le_rfl
  have hnf : NoFixedLayer15365 hF M I := by
    by_cases ha : tildeOf (quasithinOmegaOneCenter T) (conjClosure I H) =
        tildeOf (quasithinOmegaOneCenter T)
          ⁅conjClosure (ZS153 T M V₁) H, conjClosure K T⁆
    · exact noFixedLayer_of_eq hF M I ha
    · have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
        hF.K₀T_le_H.trans (le_normalizer_conjClosure I H)
      have hWK := hF.tilde_commutator_conjClosure hIU hI
      have hW0 := tildeOf_conjClosure_ne_bot hF hIU hI
      rcases hF.F918_6 (hV₁I.trans (le_conjClosure I H)) hIHU hIHN hW0 hWK with ha' | hb
      · exact absurd ha' ha
      · exact i3 G T Mc M V₁ V₂ H K t D I hV₁I hIU W hW hirr ha hb
  exact false_of_layer_inputs hF hHK M I (le_inf hH.1.1 c.hyp.T_le) hV₁I hIU hI hBelow hnf
    fun a ha b hb => commutator_MH_ZS153 c r49 hHTM ha hb

end CFSG.Quasithin
