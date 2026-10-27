module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLMod
public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredDef
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Nbr
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdMod

public section

namespace CFSG.StandardType.U63TB

open CFSG CFSG.Assembly CFSG.StandardType TableB NbrInnerRest

theorem mulAut_mem_center {L : Type*} [Group L] (f : MulAut L) {z : L}
    (hz : z ∈ Subgroup.center L) : f z ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro l
  have h := congrArg f (Subgroup.mem_center_iff.mp hz (f.symm l))
  simpa [map_mul] using h

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBCx_of_card {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma L hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hT : GGTorusNbrSCrK p r R I) {Y : Subgroup G}
    (hYx : Y ≤ Subgroup.centralizer ({x} : Set G)) (hYN : Y ≤ Subgroup.normalizer (Bs : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.zpowers x := by
  classical
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) := fun g hg =>
    mem_normalizer_of_sstar hS hnc (hYx hg)
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨W, hW1, hW2⟩ := hT L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hL γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := fun n hn b hb =>
    conj_mem_of_weyl hN hSC (hW1 n hn) hb
  have hWN : ∀ n ∈ W, (n : G) ∈ Subgroup.normalizer (Bs : Set G) := fun n hn =>
    mem_normalizer_of_weyl hN hSC (hW1 n hn)
  set Ybar : Subgroup (MulAut L) :=
    (Y.subgroupOf (Subgroup.normalizer (L : Set G))).map L.normalizerMonoidHom with hYbar
  have hgB : ∀ g ∈ Y, ∀ b : Bs, (g : G) * b * g⁻¹ ∈ Bs := fun g hg b =>
    (Subgroup.mem_normalizer_iff.mp (hYN hg) b).mp b.2
  have hYK : ∀ f ∈ Ybar, ∀ z ∈ (ggQuotHom θ).ker, f z ∈ (ggQuotHom θ).ker := by
    intro f _ z hz
    rw [ker_ggQuotHom] at hz ⊢
    exact mulAut_mem_center f hz
  have hWA : ∀ n ∈ W, ∀ a ∈ γ.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ γ.range := by
    rintro n hn _ ⟨b, rfl⟩
    exact ⟨⟨(n : G) * b * (n : G)⁻¹, hWB n hn b b.2⟩,
      (ggGamma_conj L hN n b (hWB n hn b b.2)).symm ▸ rfl⟩
  have hWY : ∀ n ∈ W, ∀ φ ∈ Ybar, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Ybar := by
    rintro n hn _ ⟨g, hg, rfl⟩
    rw [conj_mul_normalizerMonoidHom]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact hYn n ⟨hWN n hn, hLx n.2⟩ g (Subgroup.mem_subgroupOf.mp hg)
  have hYA : ∀ φ ∈ Ybar, ∀ a ∈ γ.range, φ * a * φ⁻¹ ∈ γ.range := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨_, (normalizerMonoidHom_mul_ggGamma L hN g b
      (hgB g (Subgroup.mem_subgroupOf.mp hg) b)).symm⟩
  have hYpA : ∀ φ ∈ Ybar, ∃ k : ℕ, ∀ a ∈ γ.range, φ ^ p ^ k * a = a * φ ^ p ^ k := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := hYp g (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨k, ?_⟩
    rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have hb' : ((g ^ p ^ k : Subgroup.normalizer (L : Set G)) : G) * b *
        ((g ^ p ^ k : Subgroup.normalizer (L : Set G)) : G)⁻¹ = b := by
      push_cast
      rw [(Subgroup.mem_centralizer_iff.mp hk b b.2).symm, mul_inv_cancel_right]
    have h1 := normalizerMonoidHom_mul_ggGamma L hN (g ^ p ^ k) b (hb'.symm ▸ b.2)
    have h2 : ggGamma L hN ⟨((g ^ p ^ k : Subgroup.normalizer (L : Set G)) : G) * b *
        ((g ^ p ^ k : Subgroup.normalizer (L : Set G)) : G)⁻¹, hb'.symm ▸ b.2⟩ = γ b := by
      congr 1
      exact Subtype.ext hb'
    rw [h2] at h1
    calc L.normalizerMonoidHom (g ^ p ^ k) * γ b
        = L.normalizerMonoidHom (g ^ p ^ k) * γ b * (L.normalizerMonoidHom (g ^ p ^ k))⁻¹ *
          L.normalizerMonoidHom (g ^ p ^ k) := by group
      _ = γ b * L.normalizerMonoidHom (g ^ p ^ k) := by rw [h1]
  have hcomm := hW2 Ybar hYK hWA hWY hYA hYpA
  intro g hg b hb
  have h1 := hcomm _ ⟨⟨g, hYL hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩ (γ ⟨b, hb⟩)
    ⟨⟨b, hb⟩, rfl⟩
  have h2 := normalizerMonoidHom_mul_ggGamma L hN ⟨g, hYL hg⟩ ⟨b, hb⟩ (hgB g hg ⟨b, hb⟩)
  rw [h1, mul_inv_cancel_right] at h2
  have h3' : γ (⟨g * b * g⁻¹, hgB g hg ⟨b, hb⟩⟩ * (⟨b, hb⟩ : Bs)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h2, mul_inv_cancel]
  have h4 := (ggGamma_eq_one_iff L hN _).mp h3'
  have h5 : g * b * g⁻¹ * b⁻¹ ∈ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨Bs.mul_mem (hgB g hg ⟨b, hb⟩) (Bs.inv_mem hb), h4⟩
  rwa [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2] at h5

theorem ggTableBModule_of_card {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma L hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hT : GGTableBModuleSCr p r R I) :
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

theorem ggTableBAction_of_card {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma L hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hT : GGTableBActionSCr p r R I) {B₂ : Subgroup G}
    (hM : GGTableBModule p Bs x L B₂) : GGTableBAction Bs x L B₂ := by
  classical
  obtain ⟨hp2, hT⟩ := hT
  obtain ⟨hp, hBs, hxBs, hLx, hcard4⟩ := hcfg.tableB_facts
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
  obtain ⟨H, W, hHA, hHne, hHinv, hW1, hW3, hW4, hW5, hW6, hW8, hW7⟩ := hT L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3
    (ggTorusSelfCent_ggGamma hN hSC)
  have hker : ∀ c : Bs, γ c = 1 ↔ (c : G) ∈ Subgroup.zpowers x := by
    intro c
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs
      hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hconjL : ∀ n : L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) → ∀ c : Bs,
      ∃ hnc : (n : G) * (c : G) * (n : G)⁻¹ ∈ Bs,
        γ ⟨(n : G) * (c : G) * (n : G)⁻¹, hnc⟩ = MulAut.conj n * γ c * (MulAut.conj n)⁻¹ := by
    intro n hn c
    have hcn : (n : G) * (c : G) * (n : G)⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn c).mp c.2
    exact ⟨hcn, ggGamma_conj L hN n c hcn⟩
  have hNA : ∀ n (hn : n ∈ L ⊓ Subgroup.normalizer (Bs : Set G)),
      MulAut.conj (⟨n, (Subgroup.mem_inf.mp hn).1⟩ : L) ∈
        Subgroup.normalizer ((γ.range : Subgroup (MulAut L)) : Set (MulAut L)) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro e
    have hc' : ∀ c : Bs, (n : G)⁻¹ * (c : G) * (n : G)⁻¹⁻¹ ∈ Bs := fun c =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hn).2) c).mp c.2
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨hnc, he⟩ := hconjL ⟨n, (Subgroup.mem_inf.mp hn).1⟩ (Subgroup.mem_inf.mp hn).2 c
      exact ⟨⟨_, hnc⟩, he⟩
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
  obtain ⟨hxB₂, hB₂Bs, hcardB₂, hB₂inv, hirr₂, -⟩ := hM
  set A₂ : Subgroup (MulAut L) := (B₂.subgroupOf Bs).map γ with hA₂
  have hmemA₂ : ∀ c : Bs, γ c ∈ A₂ ↔ (c : G) ∈ B₂ := by
    intro c
    constructor
    · rintro ⟨b, hb, hbc⟩
      have h1 : γ (c * b⁻¹) = 1 := by rw [map_mul, map_inv, ← hbc, mul_inv_cancel]
      have h3 : ((c * b⁻¹ : Bs) : G) ∈ B₂ := Subgroup.zpowers_le.mpr hxB₂ ((hker _).mp h1)
      have h4 : (c : G) = ((c * b⁻¹ : Bs) : G) * (b : G) := by simp
      rw [h4]
      exact B₂.mul_mem h3 (Subgroup.mem_subgroupOf.mp hb)
    · intro hc
      exact ⟨c, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
  have hHA₂ : H ≤ A₂ := by
    have hne : A₂ ≠ ⊥ := by
      intro hbot
      have hle : B₂ ≤ Subgroup.zpowers x := by
        intro g hg
        have hgBs : g ∈ Bs := hB₂Bs hg
        have h1 : γ ⟨g, hgBs⟩ ∈ A₂ := (hmemA₂ _).mpr hg
        rw [hbot, Subgroup.mem_bot] at h1
        exact (hker _).mp h1
      have hcB₂ : Nat.card B₂ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at hcB₂
      have hox : orderOf x ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hBs.2 x hxBs))
      have h5 : p ^ 4 ≤ p * p :=
        calc p ^ 4 ≤ Nat.card Bs := hcard4
          _ ≤ p * Nat.card B₂ := hcardB₂
          _ ≤ p * p := Nat.mul_le_mul_left p (hcB₂.trans hox)
      have hpp : 4 ≤ p * p := by nlinarith [hp.two_le]
      have h6 : p ^ 4 = (p * p) * (p * p) := by ring
      nlinarith [Nat.mul_le_mul_right (p * p) hpp]
    refine hW3 A₂ (Subgroup.map_le_range _ _) hne ?_
    rintro w hw _ ⟨c, hc, rfl⟩
    obtain ⟨hwc, he⟩ := hconjL w (hWN w hw).2 c
    rw [← he]
    exact (hmemA₂ _).mpr (hB₂inv w (hWN w hw) c (Subgroup.mem_subgroupOf.mp hc))
  have hHB₂ : ∀ c : Bs, γ c ∈ H ↔ (c : G) ∈ B₂ := by
    set S : Subgroup G := B₂ ⊓ (H.comap γ).map Bs.subtype with hS'
    have hxS : Subgroup.zpowers x ≤ S := by
      rw [Subgroup.zpowers_le]
      refine ⟨hxB₂, ⟨⟨x, hxBs⟩, ?_, rfl⟩⟩
      show γ ⟨x, hxBs⟩ ∈ H
      rw [(hker ⟨x, hxBs⟩).mpr (Subgroup.mem_zpowers x)]
      exact H.one_mem
    have hSinv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
      rintro n hn _ ⟨hsB₂, ⟨c, hc, rfl⟩⟩
      have hnL := (Subgroup.mem_inf.mp hn).1
      have hnN := (Subgroup.mem_inf.mp hn).2
      obtain ⟨hnc, he⟩ := hconjL ⟨n, hnL⟩ hnN c
      refine ⟨hB₂inv n hn _ hsB₂, ⟨⟨_, hnc⟩, ?_, rfl⟩⟩
      show γ ⟨_, hnc⟩ ∈ H
      rw [he]
      exact hHinv _ (hNA n hn) _ (Subgroup.mem_comap.mp hc)
    rcases hirr₂ S hxS inf_le_left hSinv with h | h
    · exfalso
      apply hHne
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨c, hc, rfl⟩ := hHA₂ ha
      have hcS : (c : G) ∈ S :=
        ⟨Subgroup.mem_subgroupOf.mp hc, ⟨c, Subgroup.mem_comap.mpr ha, rfl⟩⟩
      rw [h] at hcS
      exact Subgroup.mem_bot.mpr ((hker c).mpr hcS)
    · intro c
      refine ⟨fun hc => (hmemA₂ c).mp (hHA₂ hc), fun hc => ?_⟩
      have hcS : (c : G) ∈ S := h ▸ hc
      obtain ⟨-, ⟨c', hc', hcc'⟩⟩ := hcS
      have : c' = c := Subtype.ext hcc'
      subst this
      exact Subgroup.mem_comap.mp hc'
  refine ⟨?_, fun Hc hHcB₂ hHcinv hHcsup hHcinf => ⟨?_, ?_⟩⟩
  ·
    intro v hv hvN
    have h1 : γ ⟨v, hv⟩ = 1 := by
      apply hW4 _ ⟨⟨v, hv⟩, rfl⟩
      intro w hw
      obtain ⟨hvw, he⟩ := hconjL w (hWN w hw).2 ⟨v, hv⟩
      have hwv : (w : G) * v * (w : G)⁻¹ = v := by rw [hvN w (hWN w hw), mul_inv_cancel_right]
      rw [← he]
      congr 1
      exact Subtype.ext hwv
    exact (hker _).mp h1
  ·
    have hHcBs : Hc ≤ Bs := hHcB₂.trans hB₂Bs
    have hxHc : ∀ h ∈ Hc, x * h = h * x := fun h hh =>
      mul_comm_of_isElemAbelian hBs hxBs (hHcBs hh)
    have hnx : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), n * x = x * n := fun n hn =>
      (Subgroup.mem_centralizer_iff.mp (hLx (Subgroup.mem_inf.mp hn).1) x rfl).symm
    let Z : Subgroup G :=
      { carrier := {n | n ∈ L ⊓ Subgroup.normalizer (Bs : Set G) ∧
          ∀ v ∈ Bs, n * v * n⁻¹ * v⁻¹ ∈ Hc}
        mul_mem' := by
          rintro n n' ⟨hn, hZ⟩ ⟨hn', hZ'⟩
          refine ⟨Subgroup.mul_mem _ hn hn', fun v hv => ?_⟩
          have e : n * n' * v * (n * n')⁻¹ * v⁻¹ =
              (n * (n' * v * n'⁻¹ * v⁻¹) * n⁻¹) * (n * v * n⁻¹ * v⁻¹) := by group
          rw [e]
          exact Hc.mul_mem (hHcinv n hn _ (hZ' v hv)) (hZ v hv)
        one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp⟩
        inv_mem' := by
          rintro n ⟨hn, hZ⟩
          refine ⟨Subgroup.inv_mem _ hn, fun v hv => ?_⟩
          have e : n⁻¹ * v * n⁻¹⁻¹ * v⁻¹ = n⁻¹ * (n * v * n⁻¹ * v⁻¹)⁻¹ * n⁻¹⁻¹ := by group
          rw [e]
          exact hHcinv n⁻¹ (Subgroup.inv_mem _ hn) _ (Hc.inv_mem (hZ v hv)) }
    have hZmem : ∀ g, g ∈ Z ↔ g ∈ L ⊓ Subgroup.normalizer (Bs : Set G) ∧
        ∀ v ∈ Bs, g * v * g⁻¹ * v⁻¹ ∈ Hc := fun g => Iff.rfl
    have hWZ : ∀ w : L, w ∈ W → (w : G) ∈ Z := by
      have key : ∀ y : L, y ∈ Subgroup.closure {m | m ∈ W ∧ m * m = 1} → (y : G) ∈ Z := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem m hm =>
          obtain ⟨hmW, hmm⟩ := hm
          have hmN := hWN m hmW
          refine (hZmem _).mpr ⟨hmN, fun v hv => ?_⟩
          obtain ⟨hmv, he⟩ := hconjL m (Subgroup.mem_inf.mp hmN).2 ⟨v, hv⟩
          have hmm' : (m : G) * (m : G) = 1 := by
            have := congrArg Subtype.val hmm
            simpa using this
          have hzB : (m : G) * v * (m : G)⁻¹ * v⁻¹ ∈ Bs := Bs.mul_mem hmv (Bs.inv_mem hv)
          have hzB₂ : (m : G) * v * (m : G)⁻¹ * v⁻¹ ∈ B₂ := by
            have h1 : γ ⟨_, hzB⟩ ∈ H := by
              have e : (⟨_, hzB⟩ : Bs) =
                  ⟨(m : G) * v * (m : G)⁻¹, hmv⟩ * (⟨v, hv⟩ : Bs)⁻¹ := rfl
              rw [e, map_mul, map_inv, he]
              exact hW5 m hmW _ ⟨⟨v, hv⟩, rfl⟩
            exact (hHB₂ ⟨_, hzB⟩).mp h1
          obtain ⟨h, hh, j, hzj⟩ := exists_mem_mul_pow_of_mem_sup hxHc
            (by rw [hHcsup]; exact hzB₂)
          have hxj : x ^ j = 1 := LinIrred.pow_eq_one_of_involution hp hp2 hBs hxBs hHcBs hh
            (hHcinv _ hmN _ hh) (hnx _ hmN) hmm' hHcinf hzj
          rw [hzj, hxj, mul_one]
          exact hh
        | one => exact Z.one_mem
        | mul a b _ _ ha hb =>
          rw [Subgroup.coe_mul]
          exact Z.mul_mem ha hb
        | inv a _ ha =>
          rw [Subgroup.coe_inv]
          exact Z.inv_mem ha
      exact fun w hw => key w (hW8 w hw)
    intro n hn v hv
    have hnL := (Subgroup.mem_inf.mp hn).1
    have hnN := (Subgroup.mem_inf.mp hn).2
    have hnZ : n ∈ Z := by
      obtain ⟨w, hwW, hwfix⟩ := hW6 ⟨n, hnL⟩ (hNA n hn)
      have hwN := hWN w hwW
      have ht : ((⟨n, hnL⟩ * w⁻¹ : L) : G) ∈ Z := by
        have htG : ((⟨n, hnL⟩ * w⁻¹ : L) : G) = n * (w : G)⁻¹ := rfl
        refine (hZmem _).mpr ⟨⟨(⟨n, hnL⟩ * w⁻¹ : L).2, ?_⟩, fun v' hv' => ?_⟩
        · rw [htG]
          exact Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hwN).2)
        · have h1 := congrArg Subtype.val (hwfix (γ ⟨v', hv'⟩) ⟨⟨v', hv'⟩, rfl⟩)
          rw [hγ, ggGamma_coe] at h1
          rw [htG] at h1 ⊢
          have h3 : v' * (n * (w : G)⁻¹) = (n * (w : G)⁻¹) * v' := by
            calc v' * (n * (w : G)⁻¹) = v' * (n * (w : G)⁻¹) * v'⁻¹ * v' := by group
              _ = (n * (w : G)⁻¹) * v' := by rw [h1]
          rw [← h3]
          have : v' * (n * (w : G)⁻¹) * (n * (w : G)⁻¹)⁻¹ * v'⁻¹ = 1 := by group
          rw [this]
          exact Hc.one_mem
      have h5 := Z.mul_mem ht (hWZ w hwW)
      simpa using h5
    exact ((hZmem n).mp hnZ).2 v hv
  ·
    intro φ hφH hφmul hφN
    have hHcBs : Hc ≤ Bs := hHcB₂.trans hB₂Bs
    have hxHc : ∀ h ∈ Hc, x * h = h * x := fun h hh =>
      mul_comm_of_isElemAbelian hBs hxBs (hHcBs hh)
    have hH1 : ∀ h (hh : h ∈ Hc), γ ⟨h, hHcBs hh⟩ = 1 → h = 1 := by
      intro h hh h1
      have h2 : h ∈ Hc ⊓ Subgroup.zpowers x := ⟨hh, (hker _).mp h1⟩
      rw [hHcinf] at h2
      exact Subgroup.mem_bot.mp h2
    have huniq : ∀ h (hh : h ∈ Hc) h' (hh' : h' ∈ Hc),
        γ ⟨h, hHcBs hh⟩ = γ ⟨h', hHcBs hh'⟩ → h = h' := by
      intro h hh h' hh' he
      have h1 : γ ⟨h * h'⁻¹, hHcBs (Hc.mul_mem hh (Hc.inv_mem hh'))⟩ = 1 := by
        have e : (⟨h * h'⁻¹, hHcBs (Hc.mul_mem hh (Hc.inv_mem hh'))⟩ : Bs) =
            ⟨h, hHcBs hh⟩ * (⟨h', hHcBs hh'⟩ : Bs)⁻¹ := rfl
        rw [e, map_mul, map_inv, he, mul_inv_cancel]
      have h2 := hH1 _ (Hc.mul_mem hh (Hc.inv_mem hh')) h1
      rw [mul_inv_eq_one] at h2
      exact h2
    have hex : ∀ a ∈ H, ∃ h, ∃ hh : h ∈ Hc, γ ⟨h, hHcBs hh⟩ = a := by
      intro a ha
      obtain ⟨c, hc, rfl⟩ := hHA₂ ha
      have hcB₂ : (c : G) ∈ B₂ := Subgroup.mem_subgroupOf.mp hc
      obtain ⟨h, hh, j, hj⟩ := exists_mem_mul_pow_of_mem_sup hxHc (by rw [hHcsup]; exact hcB₂)
      refine ⟨h, hh, ?_⟩
      have e : c = ⟨h, hHcBs hh⟩ * (⟨x, hxBs⟩ : Bs) ^ j := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hj)
      have hx1 : γ ⟨x, hxBs⟩ = 1 := (hker _).mpr (Subgroup.mem_zpowers x)
      rw [e, map_mul, map_pow, hx1, one_pow, mul_one]
    have hHcH : ∀ h (hh : h ∈ Hc), γ ⟨h, hHcBs hh⟩ ∈ H := fun h hh =>
      (hHB₂ ⟨h, hHcBs hh⟩).mpr (hHcB₂ hh)
    let f : MulAut L → MulAut L := fun a =>
      if ha : ∃ h, ∃ hh : h ∈ Hc, γ ⟨h, hHcBs hh⟩ = a then
        γ ⟨φ ha.choose, hHcBs (hφH _ ha.choose_spec.choose)⟩
      else a
    have hf : ∀ h (hh : h ∈ Hc), f (γ ⟨h, hHcBs hh⟩) = γ ⟨φ h, hHcBs (hφH h hh)⟩ := by
      intro h hh
      have hex' : ∃ h', ∃ hh' : h' ∈ Hc, γ ⟨h', hHcBs hh'⟩ = γ ⟨h, hHcBs hh⟩ := ⟨h, hh, rfl⟩
      have heq : hex'.choose = h :=
        huniq _ hex'.choose_spec.choose _ hh hex'.choose_spec.choose_spec
      change (if ha : ∃ h', ∃ hh' : h' ∈ Hc, γ ⟨h', hHcBs hh'⟩ = γ ⟨h, hHcBs hh⟩ then
        γ ⟨φ ha.choose, hHcBs (hφH _ ha.choose_spec.choose)⟩ else γ ⟨h, hHcBs hh⟩) = _
      rw [dite_eq_left hex']
      congr 1
      exact Subtype.ext (congrArg φ heq)
    obtain ⟨c, hc⟩ := hW7 f
      (by
        intro a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        rw [hf h hh]
        exact hHcH _ (hφH h hh))
      (by
        intro a ha b hb
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨h', hh', rfl⟩ := hex b hb
        have e : γ ⟨h, hHcBs hh⟩ * γ ⟨h', hHcBs hh'⟩ = γ ⟨h * h', hHcBs (Hc.mul_mem hh hh')⟩ := by
          rw [← map_mul]
          rfl
        rw [e, hf _ (Hc.mul_mem hh hh'), hf h hh, hf h' hh', ← map_mul]
        congr 1
        exact Subtype.ext (hφmul h hh h' hh'))
      (by
        intro n hn a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨hnh, he⟩ := hconjL n (Subgroup.mem_inf.mp (hWN n hn)).2 ⟨h, hHcBs hh⟩
        have hnhH : (n : G) * h * (n : G)⁻¹ ∈ Hc := hHcinv n (hWN n hn) h hh
        obtain ⟨hnφ, he'⟩ := hconjL n (Subgroup.mem_inf.mp (hWN n hn)).2
          ⟨φ h, hHcBs (hφH h hh)⟩
        have e1 : γ ⟨(n : G) * h * (n : G)⁻¹, hnh⟩ =
            γ ⟨(n : G) * h * (n : G)⁻¹, hHcBs hnhH⟩ := rfl
        rw [← he, e1, hf _ hnhH, hf h hh, ← he']
        congr 1
        exact Subtype.ext (hφN n (hWN n hn) h hh))
    refine ⟨c, fun h hh => ?_⟩
    have h1 := hc _ (hHcH h hh)
    rw [hf h hh, ← map_pow] at h1
    have hhc : h ^ c ∈ Hc := Hc.pow_mem hh c
    have e : ((⟨h, hHcBs hh⟩ : Bs) ^ c) = ⟨h ^ c, hHcBs hhc⟩ := rfl
    rw [e] at h1
    exact huniq _ (hφH h hh) _ hhc h1

end Config

end CFSG.StandardType.U63TB

end
