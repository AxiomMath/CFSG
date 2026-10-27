module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLRound11

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def GGNoTransvectionSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∀ α : Subgroup.normalizer (A : Set (MulAut L')),
        (∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ ((α : MulAut L') l)) →
        ¬ GGIsTransvection p (A.normalizerMonoidHom α)

theorem ggNoTransvectionSCr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGNoTransvectionSCr p r R' I') :
    GGNoTransvectionSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc α hα
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc α ?_
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]
  · obtain ⟨φ, hφa⟩ := hα
    exact ⟨MulAut.congr e φ, fun l => by simp [MulAut.congr_apply, hφa l]⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_noTransvectionSCr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (htv : GGNoTransvectionSCr p r R I)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφt : GGIsTransvection p φ) (b : ↥Bs) : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  classical
  by_contra hb0
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hC.2.1.2.2.2
  obtain ⟨g, hgx, -, hφg⟩ := hφ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgx
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hC hL θ hN hlift
  set α : MulAut L := L.normalizerMonoidHom ⟨g, hgL⟩ with hα
  have hgc : ∀ c : Bs, g * (c : G) * g⁻¹ ∈ Bs := fun c => by rw [← hφg c]; exact (φ c).2
  have hconj : ∀ c : Bs, α * γ c * α⁻¹ = γ (φ c) := by
    intro c
    have h1 := normalizerMonoidHom_mul_ggGamma L hN ⟨g, hgL⟩ c (hgc c)
    rw [hα, h1]
    congr 1
    exact Subtype.ext (hφg c).symm
  have hNa : α ∈ Subgroup.normalizer ((γ.range : Subgroup (MulAut L)) : Set (MulAut L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨φ c, (hconj c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨φ.symm c, ?_⟩
      have h1 := hconj (φ.symm c)
      rw [MulEquiv.apply_symm_apply, hc] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  refine htv L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI
    hr h3 (ggTorusSelfCent_ggGamma hN hSC) ⟨α, hNa⟩
    ⟨ggLAut L θ ⟨g, hgL⟩, fun l => by rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]⟩ ?_
  have hkerγ : γ.rangeRestrict.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    rw [MonoidHom.ker_rangeRestrict]
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hγ, ggGamma_eq_one_iff,
      ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  refine isTransvection_of_center_ne hp (fun c c' => Subtype.ext (IsElemAbelian.comm hBs c.2
    c'.2)) γ.rangeRestrict γ.rangeRestrict_surjective ?_ hφt ?_ ?_ (b := b) ?_
  · rw [hkerγ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxBs) hS.2.2.1]
  · intro c hc
    rw [hkerγ, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    rw [hφg c, ← hk, (Commute.zpow_right hgx' k).eq, mul_inv_cancel_right]
  · intro c
    exact Subtype.ext (hconj c)
  · intro h1
    apply hb0
    have h2 : b⁻¹ * φ b ∈ γ.rangeRestrict.ker := h1
    rw [hkerγ, Subgroup.mem_subgroupOf] at h2
    exact h2

end Config

theorem ggLTransvectionCenterInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInputOn_pilot G p B x L hC.1 (largeEvenMarking_mono
    (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2.1, hC.2.1.1.trans hP.2.2.1,
      fun b hb => hP.2.2.2 b (hC.2.1.1 hb)⟩) hM)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionSCr hC hnc hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift htvt hφ htv b

@[expose] def GGTypeADvdNoTransvectionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (d p : ℕ), 5 ≤ d → p.Prime →
    p ∣ Nat.card K - 1 → p ∣ d →
      GGNoTransvectionSCr p (d - 2) (projectiveSL d K) (Set.range (conjAut d K))

theorem largeEvenLabelAll_linDvd_tv (hA : GGTypeADvdNoTransvectionInput) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGLinDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I := by
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
    ggNoTransvectionSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (hA K (l + 1) p hd5 hp hpK hpd)⟩

theorem ggLTransvectionCenterInputOn_linDvd (hA : GGTypeADvdNoTransvectionInput) :
    GGLTransvectionCenterInputOn GGLinDvdLabel :=
  ggLTransvectionCenterInputOn_of_labelsSCr (fun _ _ h => Or.inl h.1)
    fun _ _ hp hlab h => largeEvenLabelAll_linDvd_tv hA hp hlab h

end CFSG.StandardType

end
