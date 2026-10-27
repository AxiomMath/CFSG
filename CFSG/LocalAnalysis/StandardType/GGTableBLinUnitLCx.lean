module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvd
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB NbrInnerRest

@[expose] def GGLinDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_of_weyl {p : ℕ} {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {n : X}
    (hn : ∀ a ∈ (ggGamma X hN).range, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ (ggGamma X hN).range, a' (n * (a n)⁻¹) = n * (a n)⁻¹)
    {b : G} (hb : b ∈ Bs) : (n : G) * b * (n : G)⁻¹ ∈ Bs := by
  set γ := ggGamma X hN with hγ
  obtain ⟨htp, htA⟩ := hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
  have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
    push_cast
    rw [hγ, ggGamma_coe]
    group
  have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
    rw [hγ, ggGamma_coe] at h1
    calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G)
        = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b'⁻¹ * b' := by group
      _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b' := by rw [h1]
  have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ^ p = 1 := by
    have := congrArg Subtype.val htp
    simpa using this
  have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b := by
    rw [htG]
    group
  rw [e]
  exact Bs.mul_mem (hSC _ htC htp') hb

theorem mem_normalizer_of_weyl {p : ℕ} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {n : X}
    (hn : ∀ a ∈ (ggGamma X hN).range, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ (ggGamma X hN).range, a' (n * (a n)⁻¹) = n * (a n)⁻¹) :
    (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
    simpa using conj_mem_of_weyl hN hSC hn hw)
  simpa using Subgroup.inv_mem _ h

theorem card_range_ggGamma_bstar_ge {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlift : GGTorusLift p r R) :
    p ^ r ≤ Nat.card (ggGamma L hN).range ∧ p ^ 3 ≤ Nat.card (ggGamma L hN).range := by
  obtain ⟨hp, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
  have hcB := card_range_ggGamma_mul L hBN hp hS
  have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card (ggGamma L hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have h1 := succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma L hBN).range * p := by
      rw [hcB, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  · have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcB, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle

theorem ggTableBCx_of_ggTorusNbrSCr {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusNbrSCr p r R I) {Y : Subgroup G}
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
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hN hlift
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
  have hcomm := hW2 Ybar hWA hWY hYA hYpA
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

end Config

theorem ggTableBCxInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab) (hD : GGBstarInnerDiagLInputOn S)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCr p r R I) :
    GGTableBCxInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM Y hYx hYN _ hYn hYp
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInputOn_pilot G p B x L hcfg.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2⟩) hM)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1)
    (hD G p B Bs x L D J hcfg hM)
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  exact ggTableBCx_of_ggTorusNbrSCr hcfg hnc hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift hT hYx hYN hYn hYp

open LocalAnalysis.ComponentInitial.LinearFlag in
theorem largeEvenLabelAll_linDvd_torusNbrSCr {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGLinDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCr p r R I := by
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
    ggTorusNbrSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (ggTorusNbrSCr_PSL hp hpK hd5)⟩

theorem ggTableBCxInputOn_linDvd (hD : GGBstarInnerDiagLInputOn GGLinDvdLabel) :
    GGTableBCxInputOn GGLinDvdLabel :=
  ggTableBCxInputOn_of_labelsSCr (fun _ _ h => Or.inl h.1) hD
    fun _ _ hp hlab h => largeEvenLabelAll_linDvd_torusNbrSCr hp hlab h

end CFSG.StandardType

end
