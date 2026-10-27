module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggFixCompCyclic_ggGamma_x (hL : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hpJ : p ∣ Nat.card J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hxBs : x ∈ Bs) : GGFixCompCyclic p (ggGamma K hN ⟨x, hxBs⟩) := by
  classical
  obtain ⟨hI, -, hDJ⟩ := hcfg
  obtain ⟨hsimple, hnab, hKP, -, -, hβ, hS, hst⟩ := id hI
  have : IsSimpleGroup G := hsimple
  have hp : p.Prime := hβ.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hnb)
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyp : y ^ p = 1 := hS.1.1.2 y hyB
  have hxy : x * y = y * x :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨y, hyB⟩)
  have hyX : y ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  have hyL : y ∈ Subgroup.normalizer (L : Set G) := le_normalizer_of_largeEvenStandardType hst hyB
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hL hI hDJ hpJ hnb
  have hJZ : IsComponentOf J
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnb.2.1
  have hKZ : IsSubnormal (K ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hKc.2.1 _
  have hZc : Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := inf_comm _ _
  have hJZ' : IsComponentOf J
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← hZc]
    exact hJZ
  have hLx : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  have hLO : ¬ L ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({x} : Set G)) :=
    not_le_lBalancePrimeCore_of_dvd (hpJ.trans (Subgroup.card_dvd_of_le hJL))
  have hJO : ¬ J ≤ CFSG.Open.lBalancePrimeCore p
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :=
    not_le_lBalancePrimeCore_of_dvd hpJ
  have hXx : CFSG.Open.lBalanceIsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    lBalanceIsKGroup_of_kProper hKP (centralizer_singleton_ne_top_of_isSimpleGroup hnab hx1)
  have hbal : CFSG.Open.lBalancePLayer p
        (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({x} : Set G)) :=
    lBalancePLayer_inf_centralizer_le_of_input hL hp hXx hyX hyp
  have hLy : IsSubnormal (L ⊓ Subgroup.centralizer ({y} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :=
    LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hLx.2.1 _
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    have hCD : Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
      rw [hnb.2.1, Subgroup.centralizer_closure]
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx.1]
  set a := ggGamma K hN ⟨x, hxBs⟩ with ha
  have hfix : (ggFix a).map K.subtype = K ⊓ Subgroup.centralizer ({x} : Set G) :=
    map_ggFix_ggGamma K hN ⟨x, hxBs⟩
  have hJle : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJK (hJZ.1.trans inf_le_right)
  have hKxZ : K ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ hKy
  have hJ1 : IsComponentOf (J.comap K.subtype) (ggFix a) :=
    (isComponentOf_comap_of_injective K.subtype K.subtype_injective
      (by rw [hfix]; exact hJZ.of_le_of_le hJle hKxZ)).1
  have hsup : ∀ J₂ : Subgroup K, IsComponentOf J₂ (ggFix a) → J₂ ≠ J.comap K.subtype →
      p ∣ Nat.card J₂ → J₂.map K.subtype ≤ Subgroup.centralizer (L : Set G) := by
    intro J₂ hJ₂ hne hpJ₂
    have h1 : IsComponentOf (J₂.map K.subtype) (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [← hfix]
      exact isComponentOf_map_of_injective K.subtype K.subtype_injective hJ₂
    have hJ₂Z : IsComponentOf (J₂.map K.subtype)
        (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
      isComponentOf_of_isSubnormal_of_isComponentOf h1 hKZ
    have hJ₂Z' : IsComponentOf (J₂.map K.subtype)
        (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) := by
      rw [← hZc]
      exact hJ₂Z
    have hp₂ : p ∣ Nat.card (J₂.map K.subtype) := by
      rwa [Subgroup.card_map_of_injective K.subtype_injective]
    have hPc : CFSG.Open.lBalanceIsPComponent p
        (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G))
        (J₂.map K.subtype) :=
      lBalanceIsPComponent_of_isComponentOf hJ₂Z' (not_le_lBalancePrimeCore_of_dvd hp₂)
    have hJ₂E : J₂.map K.subtype ≤ CFSG.Open.lBalancePLayer p
        (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) := le_sSup hPc
    have hJ₂L : J₂.map K.subtype ≤ L ⊔ Subgroup.centralizer (L : Set G) :=
      hJ₂E.trans (hbal.trans (lBalancePLayer_le_sup_centralizer hLx hLO))
    rcases isComponentOf_le_or_commutator_eq_bot hJ₂Z' hLy with hle | hcomm
    ·
      exfalso
      have hcomp : IsComponentOf (J₂.map K.subtype) (L ⊓ Subgroup.centralizer ({y} : Set G)) :=
        hJ₂Z'.of_le_of_le hle (inf_le_inf_right _ hLx.1)
      have hJ₂J : J₂.map K.subtype ≤ J := by
        rw [hDJ.1.2.2.2.2.1, hLD]
        exact le_sSup hcomp
      rcases lBalanceIsPComponent_eq_or_commute hJZ' hJO hPc with h | h
      · apply hne
        have h' := congrArg (Subgroup.comap K.subtype) h
        rwa [Subgroup.comap_map_eq_self_of_injective K.subtype_injective] at h'
      · exact commutator_ne_bot_of_isQuasisimple hJ₂Z'.2.2
          (le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hJ₂J))
    · exact le_centralizer_of_le_sup_centralizer
        (commutator_self_eq_of_isQuasisimple hJ₂Z'.2.2) hJ₂L (hJ₂Z'.1.trans inf_le_right) hyL hcomm
  refine ⟨J.comap K.subtype, hJ1, fun P hP hPle => ?_⟩
  have hPC : P.map K.subtype ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine hPle.trans (iSup₂_le fun J₂ hJ₂ => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact hsup J₂ hJ₂.1 hJ₂.2.1 hJ₂.2.2
  have hcyc : IsCyclic ↥(P.map K.subtype) := hS.2.2.2.2 _ hPC (hP.map K.subtype)
  exact (MulEquiv.isCyclic (P.equivMapOfInjective K.subtype K.subtype_injective)).mpr hcyc

theorem ggNbrInnerWeyl_of_ggTorusNoLineComp (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hK : commutator K = ⊤) {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    {I : Set (MulAut R)} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma K hN).range) (hT : GGTorusNoLineComp p r R I) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  classical
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have h3 : p ^ 3 ≤ Nat.card γ.range := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWA : ∀ n ∈ W, ∀ a ∈ γ.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ γ.range := by
    rintro n hn _ ⟨b, rfl⟩
    exact ⟨⟨(n : G) * b * (n : G)⁻¹, hWB n hn b b.2⟩,
      (ggGamma_conj K hN n b (hWB n hn b b.2)).symm ▸ rfl⟩
  have hxγ : γ ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    rw [hγ, ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1
  obtain ⟨n, hn, hmv⟩ := hW2 hWA (γ ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hxγ
    (ggFixCompCyclic_ggGamma_x hL hcfg
      (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hxBs)
  refine ⟨(n : G), n.2, fun b hb => ?_, fun hmem => hmv ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun c hc =>
      IsElemAbelian.comm hBs hc (hWB n hn b hb)
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have e : (⟨(n : G) * x * (n : G)⁻¹, hWB n hn x hxBs⟩ : Bs) = (⟨x, hxBs⟩ : Bs) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [← ggGamma_conj K hN n ⟨x, hxBs⟩ (hWB n hn x hxBs), e, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

end Config

@[expose] def GGNbrWeylInnerKLevelComp (p : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) ∧
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLineComp p r R I

theorem ggNbrInnerWeylOn_of_labelsComp (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (GGNbrWeylInnerKLevelComp p)) :
    GGNbrInnerWeylOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hp2 hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hQ⟩
    refine ⟨hs, hna, θ, hPθ, fun _ _ => ?_⟩
    obtain ⟨hpow, r, hlift, hT⟩ := hQ hs hna
    have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I := by
      intro b hb
      apply hpow
      have e : (⟨b, hN hb⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hcfg.2.1.2.1.2 b hb)
      rw [← map_pow, e, map_one]
    have hr : p ^ r ≤ Nat.card (ggGamma K hN).range := by
      rcases hlift with hl | rfl
      · exact pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK θ hN hl
      · rw [pow_zero]
        exact Nat.card_pos
    exact ggNbrInnerWeyl_of_ggTorusNoLineComp hL hPJ hcfg hnb hK θ hN hBsI hr hT
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

theorem largeEvenLabelAll_weylInnerKLevelComp_of_noLineComp_or {p : ℕ} {lab : LargeEvenLabel}
    (hPow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hT : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLineComp p r R I) :
    LargeEvenLabelAll lab (GGNbrWeylInnerKLevelComp p) := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨hq, h1, h2⟩ =>
    ⟨hq, fun hs hna => ⟨h1 hs hna, h2 hs hna⟩⟩) (largeEvenLabelAll_and hPow hT Q hQ)

end CFSG.StandardType
