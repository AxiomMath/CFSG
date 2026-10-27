module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15A318
public import CFSG.Quasithin.EmptyFaithful.S1421QA15SLe
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Core3SmallData : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Core3IsSmall X → A318Exclusion X ∧ A128FourList X

@[expose] def Core3KThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      Core3IsSmall (↥L ⧸ CFSG.pCore 2 ↥L) → oTwoUpper H ≤ oPrimeResidualOf 3 (oTwoUpper H)

theorem core3QuasiSmallLe_of_parts (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h2 : Lemma14215Step2) (h209 : Lemma14209Used)
    (h1284 : Lemma128Four) (hd : Core3SmallData) (hk : Core3KThree) : Core3QuasiSmallLe := by
  intro G _ _ T M H K1 L M₁ c hq hsm
  obtain ⟨hex, hlist⟩ := hd _ hsm
  have hL3 : L = oPrimeResidualOf 3 (S1421.g0Of T M H K1) :=
    c.eq_oPrimeResidualOf hF h36 h38 hq (MulEquiv.refl _) hex
  have hLS := c.g0Of_eq_sup_sOf hL3
  obtain ⟨M₁', hM₁'G, hT, hS, hKM⟩ := c.exists_inM_ge_oTwoUpper h2 h209 hq hLS
  have hLM : L ≤ M₁' := c.le_g0Of.trans hM₁'G.2
  have hSM : S1421.sOf T K1 ≤ M₁' := hS.1
  have hLcomp : L ∈ cComp (L ⊔ S1421.sOf T K1) := by
    have := c.mem
    rwa [hLS] at this
  have hSyl : IsSylowTwoOf (S1421.sOf T K1) (L ⊔ S1421.sOf T K1) := by
    have := S1421.isSylowTwoOf_g0 c.inM c.sylow
    rwa [hLS] at this
  have hpc : pCoreOf 2 (L ⊔ S1421.sOf T K1) ≠ ⊥ := by
    have := c.pCore_ne
    rwa [hLS] at this
  have hloc : quasithinIsLocal (S1421.sOf T K1) L := ⟨hSyl.2.1, hLcomp, hSyl.2.2, hpc⟩
  have hmax : quasithinIsMaximalLocal (S1421.sOf T K1) L :=
    h1284 G c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian _ L hloc hlist
  have hpcM : pCoreOf 2 M₁' ≠ ⊥ := by
    obtain ⟨P, hP, hP2, hPM⟩ := hM₁'G.1.1
    intro h
    have h1 := le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : P ≤ Subgroup.normalizer (P : Set G)) le_rfl hP2
    rw [← hPM, h] at h1
    exact hP (le_bot_iff.mp h1)
  obtain ⟨L', hL', hLL'⟩ := lemma_1_2_4_exists c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian
    h37 h39 hpcM hS hLM hLcomp
  have hL'S : L' ∈ lFamily (S1421.sOf T K1) := cComp_subset_lFamily hSM hL'
  have hL'loc : quasithinIsLocal (S1421.sOf T K1) L' := by
    have hle : L' ⊔ S1421.sOf T K1 ≤ M₁' := sup_le (le_of_mem_cComp hL') hSM
    refine ⟨hS.2.1, hL'S, ?_, ?_⟩
    · intro hdvd
      apply hS.2.2
      have h1 := Subgroup.relIndex_mul_relIndex (S1421.sOf T K1) (L' ⊔ S1421.sOf T K1) M₁'
        le_sup_right hle
      have h2 : 2 ∣ (S1421.sOf T K1).relIndex M₁' := by
        rw [← h1]
        exact Dvd.dvd.mul_right hdvd _
      exact h2
    · intro h0
      apply hpcM
      have hO2S : pCoreOf 2 M₁' ≤ S1421.sOf T K1 := pCoreOf_two_le_of_isSylowTwoOf hS
      have h3 : pCoreOf 2 M₁' ≤ pCoreOf 2 (L' ⊔ S1421.sOf T K1) :=
        le_pCoreOf_of_le_normalizer 2 (hO2S.trans le_sup_right)
          (hle.trans (le_normalizer_pCoreOf 2 M₁')) (pCoreOf_isPGroup 2 M₁')
      rw [h0] at h3
      exact le_bot_iff.mp h3
  have hLeq : L' = L := hmax.2 L' hL'loc hLL'
  have hLM' : L ∈ cComp M₁' := hLeq ▸ hL'
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := isQuasisimple_quotient_pCore hq
  have hL3' : L = oPrimeResidualOf 3 M₁' :=
    eq_oPrimeResidualOf_three_of_exclusion hF h36 h38
      (sqtkGroup_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple c.st.hyp.nonabelian hpcM)
      hLM' hQ (MulEquiv.refl _) hex
  calc oTwoUpper H ≤ oPrimeResidualOf 3 (oTwoUpper H) := hk G T M H K1 L M₁ c hq hsm
    _ ≤ oPrimeResidualOf 3 M₁' :=
        Subgroup.closure_mono fun x hx => ⟨hKM hx.1, hx.2⟩
    _ = L := hL3'.symm

end CFSG.Quasithin
