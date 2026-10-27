module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeRank
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrKGTwE6ThreeAtHolds
public import CFSG.LocalAnalysis.StandardType.GGKG82Holds
public import CFSG.LocalAnalysis.StandardType.GGKG84FTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

private theorem ggMarkingAll_rank {G : Type} [Group G] [Finite G]
    (hRk : GGTwE6ThreeNbrRankInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1) :
    GGMarkingAll (K := ↥K) fun lab _ _ I _ θ => S p lab →
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) →
      3 ^ 5 ≤ Nat.card (ggGamma K hN).range := by
  classical
  intro P' hP'
  by_cases hb5 : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ _ => hb5⟩) hP'
  have hDisj : LargeEvenMarking ↥K (fun lab R _ I F θ =>
      (P' lab R I F θ ∧ (S p lab ∧ ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)) ∨
      (P' lab R I F θ ∧ ¬ (S p lab ∧ ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I))) :=
    largeEvenMarking_mono (fun lab R _ I F θ hPθ => by
      by_cases hH : S p lab ∧ ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I
      · exact Or.inl ⟨hPθ, hH⟩
      · exact Or.inr ⟨hPθ, hH⟩) hP'
  rcases largeEvenMarking_or hDisj with hyes | hno
  · exfalso
    have hInnL : GGInnerDiagOnLab GGTwE6BadLabel p Bs K := by
      refine largeEvenMarking_mono (fun lab R _ I F θ hH => ?_) hyes
      obtain ⟨-, hSl, hBI⟩ := hH
      have hbad : GGTwE6BadLabel p lab := hS p lab hSl
      exact ⟨hbad, largeEvenSplit_of_twE6BadLabel hbad, hN, fun b hb =>
        ⟨_, hBI b⁻¹ (Bs.inv_mem hb), largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb))⟩⟩
    obtain ⟨lab, -, -, -, -, -, -, -, hbl, -⟩ := largeEvenMarking_exists_hasLabel hInnL
    have hp3 : p = 3 := hbl.2.1
    subst hp3
    exact hb5 (hRk G 3 B Bs x L D J hcfg rfl y K hnb hInnL hN
      (ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2))
  · exact largeEvenMarking_mono (fun lab R _ I F θ hPθ =>
      ⟨hPθ.1, fun hSl hBI => absurd ⟨hSl, hBI⟩ hPθ.2⟩) hno

theorem ggNbrInnerWeylOn_twE6Three_of_rank
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hRk : GGTwE6ThreeNbrRankInput) (hHeis : GGNbrKGFieldTwE6ThreeAddHeis)
    {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1) :
    GGNbrInnerWeylOn S := by
  classical
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  obtain ⟨hK, lab, hlab, hraw⟩ :=
    hG G p B Bs x L D J hcfg y K hnb hN _ (ggMarkingAll_rank hRk hcfg hnb hN hS P hP)
  by_cases hSl : S p lab
  swap
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, ⟨hPθ, -⟩, -⟩
    exact ⟨hs, hna, θ, hPθ, fun hS' => absurd hS' hSl⟩
  obtain ⟨ht, rfl, hd⟩ := hS p lab hSl
  have hn : 1 ≤ lab.n := hlab.1
  have hc5 : LargeEvenLabelAll lab fun R _ I _ => GGTorusNoLineComp 3 5 R I :=
    TwE6Delta.labelAll ht fun K _ _ hK => ggNbrKGTwE6ThreeAddFive_holds K lab.n hn hK hd
  have hrow := largeEvenLabelAll_and (largeEvenLabelAll_inn_twE6 ht)
    (largeEvenLabelAll_and hc5
      (largeEvenLabelAll_and
        (ggNbrKGTwE6ThreeAddTwoLocal_of_at ggNbrKGTwE6ThreeAddTwoLocalAt_holds lab hlab ht hd)
        (largeEvenLabelAll_and (ggNbrKGFieldTwE6ThreeAdd_holds lab hlab ht hd)
          (largeEvenLabelAll_and (hHeis lab hlab ht hd)
            (ggNbrKGFieldTwE6ThreeAddLiftFix_holds lab hlab ht hd)))))
  refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (hrow _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, ⟨hPθ, hQrk⟩, hgr⟩, hInn, hT5, h82, h84, h87, hLF⟩
  refine ⟨hs, hna, θ, hPθ, fun hS' hxI => ?_⟩
  obtain ⟨-, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have : Finite γ.range := Finite.of_surjective _ γ.rangeRestrict_surjective
  have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian 3 γ.range := isElemAbelian_range hBc hBp γ
  have hBsIF : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F) := by
    intro b hb
    obtain ⟨u, hu, f, hf, e⟩ := hgr b hb
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hu))
      (Subgroup.closure_mono Set.subset_union_right hf)
  have hlift' : ∀ (b : G) (hb : b ∈ Bs) (l : K),
      ggLAut K θ ⟨b, hN hb⟩ (ggQuotHom θ l) = ggQuotHom θ (γ ⟨b, hb⟩ l) :=
    fun b hb l => ggBeta_ggQuotHom K hN θ ⟨b, hb⟩ l
  have hψ := ggQuotHom_surjective θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center K := by rw [ker_ggQuotHom]
  have hxγ : γ ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    rw [hγ, ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1
  by_cases hall : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I
  · exact ggNbrInnerWeyl_of_ggTorusNoLineComp hL hPJ hcfg hnb hK θ hN hall (hQrk hS' hall) hT5
  push Not at hall
  obtain ⟨b₁, hb₁, hb₁I⟩ := hall
  have hb₁L : ¬ ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (γ ⟨b₁, hb₁⟩ l) := by
    rintro ⟨φ, hφ, hφl⟩
    exact hb₁I (TypeA.induced_unique _ hψ hφl (hlift' b₁ hb₁) ▸ hφ)
  have hb₁n : γ ⟨b₁, hb₁⟩ ∉ (MulAut.conj : K →* MulAut K).range := by
    intro h
    obtain ⟨r, hr⟩ := ggLAut_mem_range_conj_of_ggGamma hN θ hb₁ h
    exact hb₁I (hr ▸ hInn r)
  obtain ⟨h82, h84, h87, hLF⟩ := (⟨h82 hs hna, h84 hs hna, h87 hs hna, hLF hs hna⟩ :
    GGTwoLocalLift 3 5 6 R I F ∧ GGTorusNoLineFieldComp 3 5 R I F ∧ GGHeisFieldComp 3 5 R I F ∧
      GGTorusLiftFix 3 4 R I F)
  by_cases hz : 3 ∣ Nat.card (Subgroup.center K)
  ·
    have h5 : 3 ^ 5 ≤ Nat.card γ.range :=
      pow_succ_le_card_range_ggGamma_of_field hcfg hnb hK θ hN hInn hLF hBsIF ⟨b₁, hb₁, hb₁I⟩
    by_cases h6 : Nat.card γ.range = 3 ^ 5
    ·
      have hzker : 3 ∣ Nat.card (ggQuotHom θ).ker := by rw [ker_ggQuotHom]; exact hz
      obtain ⟨n, hn, hmv⟩ := h87 K (ggQuotHom θ) hψ hker hK hzker γ.range hA
        (by rintro _ ⟨b, rfl⟩; exact ⟨_, hBsIF b b.2, hlift' b b.2⟩)
        ⟨_, ⟨⟨b₁, hb₁⟩, rfl⟩, hb₁L⟩ h6 (ggTorusSelfCent_ggGamma hN hSC)
        (γ ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hxγ ⟨_, hxI, hlift' x hxBs⟩
        (ggFixCompCyclic_ggGamma_x hL hcfg
      (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hxBs)
      exact ggNbrInnerWeyl_of_good hcfg hnb hN hxBs hn hmv
    ·
      exact ggNbrInnerWeyl_of_ggTorusNoLineFieldComp hL hPJ hcfg hnb hK θ hN hBsIF hxK hxI
        (NbrTwE6Three.pow_succ_le_card_of_ne Nat.prime_three hA h5 h6) h84
  ·
    obtain ⟨E, hEle, hEel, hEloc, -, hE6⟩ := h82 K (ggQuotHom θ) hψ hker hK (γ ⟨b₁, hb₁⟩)
      (hA.2 _ ⟨⟨b₁, hb₁⟩, rfl⟩) ⟨_, hBsIF b₁ hb₁, hlift' b₁ hb₁⟩ hb₁n
    exact ggNbrInnerWeyl_of_ggTorusNoLineFieldComp hL hPJ hcfg hnb hK θ hN hBsIF hxK hxI
      ((hE6 hb₁L).trans (ggTwoLocalRankDom_ggGamma hcfg hnb hN hz E
        (hEle.trans (sup_le_sup_right
          (Subgroup.zpowers_le.mpr (show γ ⟨b₁, hb₁⟩ ∈ γ.range from ⟨⟨b₁, hb₁⟩, rfl⟩)) _))
        hEel hEloc)) h84

theorem ggNbrInnerWeylOn_residual_of_rank
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput)
    (hD : GGNbrInnerWeylOn GGNbrWeylResidualTriD4Label) (hRk : GGTwE6ThreeNbrRankInput)
    (hHeis : GGNbrKGFieldTwE6ThreeAddHeis) :
    GGNbrInnerWeylOn GGNbrWeylResidualLabel := by
  refine ggNbrInnerWeylOn_residual_of_open (ggNbrInnerWeylOn_residualOpen_of_split
    (ggNbrInnerWeylOn_twE6Three_of_rank hL hPJ hG hRk hHeis (fun p lab h => ?_)) hD)
  rcases h.1.1.2 with ⟨ht, hp, hd⟩ | ⟨ht, -, -⟩
  · subst hp
    exact ⟨ht, rfl, hd⟩
  · exact absurd (h.2.symm.trans ht) (by decide)

end CFSG.StandardType
