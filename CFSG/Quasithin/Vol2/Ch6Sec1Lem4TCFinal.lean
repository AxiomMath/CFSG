module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCMain
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFStruct

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def NZVNormalFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V M₁ K₁ X : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → K₁ ∈ cComp M₁ →
    IsTits (ModO2 K₁) → T ≤ Subgroup.normalizer (K₁ : Set G) →
    K₁ ≤ Subgroup.centralizer ((ZV614 T L V : Subgroup G) : Set G) →
    (K₁.subgroupOf (Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G))).Normal

theorem charTwo_sup614 {T M L V M₁ K₁ : Subgroup G} (h : Hyp611 G T M L V 4)
    (hM₁ : quasithinIsMaxTwoLocal M₁)
    (hCM₁ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁)
    (hK₁ : K₁ ∈ cComp M₁) : CharTwo (K₁ ⊔ T) := by
  have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mpr ((quasithinOmegaOneCenter_le_inf T).trans inf_le_right)
  have hTM₁ : T ≤ M₁ := hTC.trans hCM₁
  have hKM₁ : K₁ ≤ M₁ := le_of_mem_cComp hK₁
  have hsylM₁ : IsSylowTwoOf T M₁ := h.toHyp5_0_1.isSylowTwoOf hTM₁
  have hpc : pCoreOf 2 M₁ ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM₁.1
  have hpcT : pCoreOf 2 M₁ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hsylM₁
  have hKT : K₁ ⊔ T ≤ M₁ := sup_le hKM₁ hTM₁
  have hle : pCoreOf 2 M₁ ≤ pCoreOf 2 (K₁ ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hpcT.trans le_sup_right)
      (hKT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
  have hne : pCoreOf 2 (K₁ ⊔ T) ≠ ⊥ := fun h0 => hpc (le_bot_iff.mp (h0 ▸ hle))
  exact charTwo_of_inH' h.qtke h.sylow (show InH T (K₁ ⊔ T) from ⟨le_sup_right, hne⟩)

theorem not_mem_K614 (hB : TitsBasicFact) {K : Subgroup G} (htits : IsTits (ModO2 K))
    {d : G} (hord : orderOf d = 3) (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hΦ : actModO2_614 K ⟨d, hdK⟩ = 1) : d ∉ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdKm
  have h0 : actModO2_614 K ⟨d, hdK⟩ = MulAut.conj (mk614 K ⟨d, hdKm⟩) :=
    actModO2_614_of_mem K hdKm
  have h1 : MulAut.conj (mk614 K ⟨d, hdKm⟩) = MulAut.conj (1 : ModO2 K) := by
    rw [map_one, ← h0, hΦ]
  have hm : mk614 K ⟨d, hdKm⟩ = 1 := conj_inj614 (hB _ htits).2.2 h1
  have hpc := mem_pCoreOf_of_mk614_eq_one hdKm hm
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hpc⟩
  have hdk : d ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd := orderOf_dvd_of_pow_eq_one hdk
  rw [hord] at hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32

theorem normalizes_of_normal614 {H K : Subgroup G} (hn : (K.subgroupOf H).Normal) {d : G}
    (hd : d ∈ H) (hKH : K ≤ H) : d ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have := hn.conj_mem ⟨k, hKH hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨d, hd⟩
    have h1 : d * k * d⁻¹ ∈ K := Subgroup.mem_subgroupOf.mp this
    exact h1
  · intro hk
    have hd' : d⁻¹ ∈ H := H.inv_mem hd
    have := hn.conj_mem ⟨d * k * d⁻¹, hKH hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨d⁻¹, hd'⟩
    have e : d⁻¹ * (d * k * d⁻¹) * d⁻¹⁻¹ = k := by group
    have h2 : d⁻¹ * (d * k * d⁻¹) * d⁻¹⁻¹ ∈ K := Subgroup.mem_subgroupOf.mp this
    rwa [e] at h2

theorem res614TitsCore_of (hT0 : TitsOrderFact) (hB : TitsBasicFact) (hO5 : TitsOver5Fact)
    (hT2 : TitsRankThreeFact) (hT4 : TitsParabolicNormalizerFact)
    (hO2 : L216ModuleFact) (hO3 : L216CoreFact) (hO4 : L216NormalizerFact)
    (hFF : FFCentralizerFact) (hNZV : NZVNormalFact) : Res614TitsCore := by
  intro G _ _ T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ htits hK₁M hXL hXM₁ hX2 hX5 hXn hTX
    hXK₁ hTK hnot hL4
  classical
  have hsyl : IsSylowTwoOf T (K₁ ⊔ T) := h.toHyp5_0_1.isSylowTwoOf le_sup_right
  have hJnot := not_thompsonJ_le_centralizerMod614 hT0 hB hO5 htits hTK hsyl hXK₁ hTX hX5 hL4
  have hKC := hFF G T M L V M₁ K₁ h horth hM₁ hCM₁ hK₁ htits hTK hJnot
  have hCT := charTwo_sup614 h hM₁ hCM₁ hK₁
  have hZR := zV_le_omegaOne614 hO3 h horth hXL hX2 hX5 hXn hTX hXK₁ hTK hCT
  have hKZ : K₁ ≤ Subgroup.centralizer ((ZV614 T L V : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hKC hk)) z (hZR hz)
  have hZVcard : Nat.card ↥(ZV614 T L V) = 4 := (hO2 G T M L V h horth).2
  obtain ⟨d, hdL, hdTL, hdV, hord, hdX⟩ :=
    exists_cartan_three614 hO2 hO4 h horth hXL hX2 hX5 hXn hTX
  have hdZ : d ∈ Subgroup.normalizer ((ZV614 T L V : Subgroup G) : Set G) :=
    normalizer_ZV614 hdV hdTL
  have hNK := hNZV G T M L V M₁ K₁ X h horth hM₁ hCM₁ hK₁ htits hTK hKZ
  have hdK : d ∈ Subgroup.normalizer (K₁ : Set G) :=
    normalizes_of_normal614 hNK hdZ (fun k hk => centralizer_le_normalizer614 _ (hKZ hk))
  have hd3 : d ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one d
  have hΦ : actModO2_614 K₁ ⟨d, hdK⟩ = 1 :=
    actModO2_d_eq_one614 hT4 hT0 hB (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (pCoreOf_L_le614 h |>.trans inf_le_left) hTK hsyl hXK₁ hX2 hX5 hTX htits hd3 hdK hdX
  obtain ⟨E, hEel, hEcard⟩ := tits_three_rank_exists hT2 htits
  have hdA : d ∉ Aprime614 K₁ E := fun hmem => not_mem_K614 hB htits hord hdK hΦ (aprime_le_K614 E hmem)
  obtain ⟨hdec, hcardF, hcommF, hexpF⟩ :=
    FStruct.fstruct614 (normalizes_Aprime614 hdK hΦ) hd3 hdA
  exact step7_false614 hB h htits hEel hEcard hKZ hZVcard hord hdK hdTL hdV hΦ hdec hcardF
    hcommF hexpF

end CFSG.Quasithin.H13.T614

end
