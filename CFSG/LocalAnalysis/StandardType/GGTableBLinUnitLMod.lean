module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModProof
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LocalAnalysis.ComponentInitial.LinearFlag

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBModule_of_SCr {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTableBModuleSCr p r R I) :
    ∃ B₂ : Subgroup G, GGTableBModule p Bs x L B₂ := by
  classical
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hN hlift
  obtain ⟨H, W, hHA, hHne, hcard, hHinv, hW1, hirr⟩ := hT L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3
    (ggTorusSelfCent_ggGamma hN hSC)
  have hker : ∀ c : Bs, γ c = 1 ↔ (c : G) ∈ Subgroup.zpowers x := by
    intro c
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs
      hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hNA : ∀ n (hn : n ∈ L ⊓ Subgroup.normalizer (Bs : Set G)),
      MulAut.conj (⟨n, (Subgroup.mem_inf.mp hn).1⟩ : L) ∈
        Subgroup.normalizer ((γ.range : Subgroup (MulAut L)) : Set (MulAut L)) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro e
    have hc : ∀ c : Bs, n * (c : G) * n⁻¹ ∈ Bs := fun c =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hn).2 c).mp c.2
    have hc' : ∀ c : Bs, n⁻¹ * (c : G) * n⁻¹⁻¹ ∈ Bs := fun c =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hn).2) c).mp c.2
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨⟨_, hc c⟩, ggGamma_conj L hN ⟨n, (Subgroup.mem_inf.mp hn).1⟩ c (hc c)⟩
    · rintro ⟨c, hce⟩
      refine ⟨⟨_, hc' c⟩, ?_⟩
      have hc'' : ((⟨n, (Subgroup.mem_inf.mp hn).1⟩⁻¹ : L) : G) * c *
          ((⟨n, (Subgroup.mem_inf.mp hn).1⟩⁻¹ : L) : G)⁻¹ ∈ Bs := by
        simpa using hc' c
      have h1 := ggGamma_conj L hN (⟨n, (Subgroup.mem_inf.mp hn).1⟩⁻¹ : L) c hc''
      have e2 : (⟨_, hc' c⟩ : Bs) = ⟨_, hc''⟩ := Subtype.ext (by simp)
      rw [e2, h1, hce, map_inv]
      group
  have hWN : ∀ w ∈ W, (w : G) ∈ L ⊓ Subgroup.normalizer (Bs : Set G) := fun w hw =>
    ⟨w.2, mem_normalizer_of_weyl hN hSC (hW1 w hw)⟩
  have himg : ∀ S : Subgroup G, Subgroup.zpowers x ≤ S → S ≤ Bs →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = Subgroup.zpowers x ∨ ∀ c : Bs, γ c ∈ H → (c : G) ∈ S := by
    intro S hxS hSBs hSinv
    set A' : Subgroup (MulAut L) := (S.subgroupOf Bs).map γ with hA'
    by_cases hA'b : A' = ⊥
    · left
      refine le_antisymm (fun s hs => ?_) hxS
      have h1 : γ ⟨s, hSBs hs⟩ ∈ A' := ⟨⟨s, hSBs hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      rw [hA'b, Subgroup.mem_bot] at h1
      exact (hker _).mp h1
    · right
      have hHA' : H ≤ A' := hirr A' (Subgroup.map_le_range _ _) hA'b (by
        rintro w hw _ ⟨c, hcS, rfl⟩
        have hcw : (w : G) * c * (w : G)⁻¹ ∈ Bs :=
          (Subgroup.mem_normalizer_iff.mp (hWN w hw).2 c).mp c.2
        refine ⟨⟨_, hcw⟩, Subgroup.mem_subgroupOf.mpr
          (hSinv w (hWN w hw) c (Subgroup.mem_subgroupOf.mp hcS)), ?_⟩
        exact ggGamma_conj L hN w c hcw)
      intro c hc
      obtain ⟨s, hsS, hsc⟩ := hHA' hc
      have h1 : γ (c * s⁻¹) = 1 := by rw [map_mul, map_inv, hsc, mul_inv_cancel]
      have h2 := hxS ((hker _).mp h1)
      have h3 : (c : G) = ((c * s⁻¹ : Bs) : G) * s := by simp
      rw [h3]
      exact S.mul_mem h2 (Subgroup.mem_subgroupOf.mp hsS)
  set B₂ : Subgroup G := (H.comap γ).map Bs.subtype with hB₂
  have hmem : ∀ c : Bs, (c : G) ∈ B₂ ↔ γ c ∈ H := by
    intro c
    constructor
    · rintro ⟨c', hc', hcc'⟩
      rw [← Subtype.ext hcc']
      exact hc'
    · intro h
      exact ⟨c, h, rfl⟩
  have hB₂Bs : B₂ ≤ Bs := Subgroup.map_subtype_le _
  refine ⟨B₂, (hmem ⟨x, hxBs⟩).mpr ?_, hB₂Bs, ?_, ?_, ?_, ?_⟩
  · rw [(hker _).mpr (Subgroup.mem_zpowers x)]
    exact H.one_mem
  ·
    set γ' := γ.rangeRestrict with hγ'
    set H' := H.subgroupOf γ.range with hH'
    have hidx : (H'.comap γ').index = H'.index :=
      Subgroup.index_comap_of_surjective H' γ.rangeRestrict_surjective
    have hcomap : H'.comap γ' = H.comap γ := by
      ext c
      simp [hH', hγ', Subgroup.mem_subgroupOf]
    have hH'card : Nat.card H' = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv
    have hidxp : H'.index ≤ p := by
      have h1 := H'.index_mul_card
      rw [hH'card] at h1
      have hHpos : 0 < Nat.card H := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : (p + 1) * Nat.card H ≤ Nat.card γ.range := by
        rw [← h1]
        exact Nat.mul_le_mul_right _ hlt
      nlinarith
    have hB₂card : Nat.card B₂ = Nat.card (H.comap γ) :=
      Subgroup.card_map_of_injective Bs.subtype_injective
    have h2 := (H.comap γ).index_mul_card
    rw [← hcomap, hidx] at h2
    rw [hB₂card, ← hcomap]
    calc Nat.card Bs = H'.index * Nat.card (H'.comap γ') := h2.symm
      _ ≤ p * Nat.card (H'.comap γ') := Nat.mul_le_mul_right _ hidxp
  ·
    rintro n hn s ⟨c, hc, rfl⟩
    have hcn : n * (c : G) * n⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hn).2 c).mp c.2
    refine (hmem ⟨_, hcn⟩).mpr ?_
    rw [ggGamma_conj L hN ⟨n, (Subgroup.mem_inf.mp hn).1⟩ c hcn]
    exact hHinv ⟨n, (Subgroup.mem_inf.mp hn).1⟩ (hNA n hn) _ hc
  ·
    intro S hxS hSB₂ hSinv
    rcases himg S hxS (hSB₂.trans hB₂Bs) hSinv with h | h
    · exact Or.inl h
    · refine Or.inr (le_antisymm hSB₂ fun b hb => ?_)
      exact h ⟨b, hB₂Bs hb⟩ ((hmem ⟨b, hB₂Bs hb⟩).mp hb)
  ·
    intro S T hxS hxT hSinv hTinv hST hsup
    have hSBs : S ≤ Bs := hsup ▸ le_sup_left
    have hTBs : T ≤ Bs := hsup ▸ le_sup_right
    by_contra hne
    push Not at hne
    obtain ⟨hS', hT'⟩ := hne
    have hSall := (himg S hxS hSBs hSinv).resolve_left hS'
    have hTall := (himg T hxT hTBs hTinv).resolve_left hT'
    obtain ⟨⟨h, hhH⟩, hh1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hHne
    have hh1' : h ≠ 1 := fun e => hh1 (Subtype.ext e)
    obtain ⟨c, rfl⟩ := hHA hhH
    have hcS := hSall c hhH
    have hcT := hTall c hhH
    have hcx : (c : G) ∈ Subgroup.zpowers x := by
      rw [← hST]
      exact ⟨hcS, hcT⟩
    exact hh1' ((hker c).mpr hcx)

end Config

theorem ggTableBModuleInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGBstarInnerDiagLInputOn S)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTableBModuleSCr p r R I) :
    GGTableBModuleInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1)
    (hD G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  exact ggTableBModule_of_SCr hcfg hL θ hBsN (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb)
    hlift hT

theorem largeEvenLabelAll_linDvd_module {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGLinDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTableBModuleSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hpd⟩ := h
  dsimp only at ht hl hpn hpd
  subst ht
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hlab.1 hpn
  have hd5 : 5 ≤ l + 1 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rcases hpd with ⟨k, hk⟩
    rcases k with _ | _ | k
    · omega
    · have : p ≠ 4 := by
        intro h4
        rw [h4] at hp
        exact absurd hp (by decide)
      omega
    · nlinarith
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', l + 1 - 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le hd5)),
    ggTableBModuleSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinUnitL.ggTableBModuleSCr_PSL hp hpK hd5 le_rfl)⟩

theorem ggTableBModuleInputOn_linDvd_holds : GGTableBModuleInputOn GGLinDvdLabel :=
  ggTableBModuleInputOn_of_labelsSCr ggBstarInnerDiagLInputOn_linDvd
    fun _ _ hp hlab h => largeEvenLabelAll_linDvd_module hp hlab h

end CFSG.StandardType

end
