module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Abstract

variable {G : Type*} [Group G]

namespace GGControlsStrongFusion

variable {H E F : Subgroup G}

theorem mono_of_le_fusion (h : GGControlsStrongFusion H E) (hFE : F ≤ E) :
    GGControlsStrongFusion H F := by
  refine ⟨hFE.trans h.1, fun g hg => h.2 g fun hbot => hg ?_⟩
  rw [eq_bot_iff] at hbot ⊢
  exact (inf_le_inf_right H (Subgroup.map_mono hFE)).trans hbot

theorem map_conj_fusion (h : GGControlsStrongFusion H E) {m : G} (hm : m ∈ H) :
    GGControlsStrongFusion H (E.map (MulAut.conj m).toMonoidHom) := by
  rw [ggControlsStrongFusion_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact H.mul_mem (H.mul_mem hm (h.1 he)) (H.inv_mem hm)
  · rintro _ ⟨e, he, rfl⟩ he1 g hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hg he1
    have he1' : e ≠ 1 := by
      rintro rfl
      simp at he1
    have hg' : (m⁻¹ * g)⁻¹ * e * (m⁻¹ * g) ∈ H := by
      simpa [mul_assoc] using hg
    simpa using H.mul_mem hm (h.2 e he he1' _ hg')

end GGControlsStrongFusion

theorem ggControlsStrongFusion_zpowers_conj {H : Subgroup G} {b m : G}
    (h : GGControlsStrongFusion H (Subgroup.zpowers b)) (hm : m ∈ H) :
    GGControlsStrongFusion H (Subgroup.zpowers (m⁻¹ * b * m)) := by
  have := h.map_conj_fusion (H.inv_mem hm)
  rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this

theorem mem_of_pow_two_pow_eq_one_of_odd_relIndex {G₀ M : Subgroup G}
    (hN : (G₀.subgroupOf M).Normal) (hodd : Odd (G₀.relIndex M)) {y : G} (hyM : y ∈ M)
    {k : ℕ} (hy : y ^ 2 ^ k = 1) : y ∈ G₀ := by
  let q : ↥M ⧸ G₀.subgroupOf M := QuotientGroup.mk ⟨y, hyM⟩
  have h2 : orderOf q ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have : (⟨y, hyM⟩ : M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hy)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hidx : orderOf q ∣ G₀.relIndex M := by
    have := orderOf_dvd_natCard q
    rwa [← Subgroup.index_eq_card] at this
  have h1 : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hodd).pow_left k) h2 hidx
  have hq : q = 1 := orderOf_eq_one_iff.mp h1
  have hmem : (⟨y, hyM⟩ : M) ∈ G₀.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hq
  exact Subgroup.mem_subgroupOf.mp hmem

theorem conj_mem_centralizer_of_commute {r g y : G}
    (hys : y * (g⁻¹ * r * g) = (g⁻¹ * r * g) * y) :
    g * y * g⁻¹ ∈ Subgroup.centralizer {r} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * y * g⁻¹ * r = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by rw [hys]
    _ = r * (g * y * g⁻¹) := by group

theorem mem_of_commute_of_controlsStrongFusion {M : Subgroup G} {r g y : G}
    (hC : Subgroup.centralizer {r} ≤ M) (hy1 : y ≠ 1)
    (hys : y * (g⁻¹ * r * g) = (g⁻¹ * r * g) * y)
    (hfus : GGControlsStrongFusion M (Subgroup.zpowers y)) : g ∈ M := by
  have hc := hC (conj_mem_centralizer_of_commute hys)
  have := hfus.mem_of_conj_mem (Subgroup.mem_zpowers y) hy1 (g := g⁻¹) (by simpa using hc)
  simpa using this

@[expose] def ggCentOTwoPrime (G₀ : Subgroup G) (s : G) : Subgroup G :=
  Subgroup.closure {y | y ∈ G₀ ∧ y * s = s * y ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}

theorem exists_injective_ggCentOTwoPrime {G₀ M : Subgroup G} (hN : (G₀.subgroupOf M).Normal)
    (hodd : Odd (G₀.relIndex M)) {r : G} (hC : Subgroup.centralizer {r} ≤ M) (g : G) :
    ∃ φ : ↥(ggCentOTwoPrime G₀ (g⁻¹ * r * g)) →* ↥(ggCentOTwoPrime G₀ r),
      Function.Injective φ := by
  have hle : ∀ y ∈ ggCentOTwoPrime G₀ (g⁻¹ * r * g), g * y * g⁻¹ ∈ ggCentOTwoPrime G₀ r := by
    have hcl : ggCentOTwoPrime G₀ (g⁻¹ * r * g) ≤
        (ggCentOTwoPrime G₀ r).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨-, hys, k, hyk⟩
      have hc := conj_mem_centralizer_of_commute hys
      have hk : (g * y * g⁻¹) ^ 2 ^ k = 1 := by
        rw [conj_pow, hyk, mul_one, mul_inv_cancel]
      refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨?_, ?_, k, ?_⟩)
      · exact mem_of_pow_two_pow_eq_one_of_odd_relIndex hN hodd (hC hc) hk
      · exact Subgroup.mem_centralizer_singleton_iff.mp hc
      · simpa [MulAut.conj_apply] using hk
    intro y hy
    simpa [MulAut.conj_apply] using hcl hy
  refine ⟨{ toFun := fun y => ⟨g * y * g⁻¹, hle y y.2⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext
    simp
  · intro a b
    ext
    simp [mul_assoc]
  · intro a b hab
    have h := congrArg Subtype.val hab
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h

@[expose] def GGRootFusionAlt (G₀ M : Subgroup G) (r s : G) : Prop :=
  (∃ m ∈ M, s = m⁻¹ * r * m) ∨
    (∃ y : G, y ≠ 1 ∧ y * s = s * y ∧ GGControlsStrongFusion M (Subgroup.zpowers y)) ∨
    ¬ ∃ φ : ↥(ggCentOTwoPrime G₀ s) →* ↥(ggCentOTwoPrime G₀ r), Function.Injective φ

theorem orderOf_inv_mul_mul (r g : G) : orderOf (g⁻¹ * r * g) = orderOf r := by
  have ho := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) r
  rwa [MulAut.conj_apply, inv_inv] at ho

theorem ggControlsStrongFusion_zpowers_of_alt {G₀ M : Subgroup G} (hle : G₀ ≤ M)
    (hN : (G₀.subgroupOf M).Normal) (hodd : Odd (G₀.relIndex M)) {r : G} (hrG₀ : r ∈ G₀)
    (hr : orderOf r = 2) (hC : Subgroup.centralizer {r} ≤ M)
    (halt : ∀ s ∈ G₀, orderOf s = 2 → GGRootFusionAlt G₀ M r s) :
    GGControlsStrongFusion M (Subgroup.zpowers r) := by
  have hprime : (orderOf r).Prime := hr ▸ Nat.prime_two
  refine (ggControlsStrongFusion_zpowers_iff hprime).mpr ⟨hle hrG₀, fun g hg => ?_⟩
  have hord : orderOf (g⁻¹ * r * g) = 2 := (orderOf_inv_mul_mul r g).trans hr
  have hsq : (g⁻¹ * r * g) ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  rcases halt _ (mem_of_sq_eq_one_of_odd_relIndex hN hodd hg hsq) hord with
    ⟨m, hm, heq⟩ | ⟨y, hy1, hys, hfus⟩ | hα
  · exact mem_of_conj_eq_conj hC hm heq
  · exact mem_of_commute_of_controlsStrongFusion hC hy1 hys hfus
  · exact absurd (exists_injective_ggCentOTwoPrime hN hodd hC g) hα

theorem ggControlsStrongFusion_zpowers_iff_forall_conj {G₀ M : Subgroup G} (hle : G₀ ≤ M)
    (hN : (G₀.subgroupOf M).Normal) (hodd : Odd (G₀.relIndex M)) {r : G} (hrG₀ : r ∈ G₀)
    (hr : orderOf r = 2) (hC : Subgroup.centralizer {r} ≤ M) :
    GGControlsStrongFusion M (Subgroup.zpowers r) ↔
      ∀ g : G, g⁻¹ * r * g ∈ G₀ → ∃ m ∈ M, g⁻¹ * r * g = m⁻¹ * r * m := by
  have hprime : (orderOf r).Prime := hr ▸ Nat.prime_two
  constructor
  · intro h g hg
    exact ⟨g, (ggControlsStrongFusion_zpowers_iff hprime).mp h |>.2 g (hle hg), rfl⟩
  · intro h
    refine (ggControlsStrongFusion_zpowers_iff hprime).mpr ⟨hle hrG₀, fun g hg => ?_⟩
    have hsq : (g⁻¹ * r * g) ^ 2 = 1 := by
      rw [← (orderOf_inv_mul_mul r g).trans hr]
      exact pow_orderOf_eq_one _
    obtain ⟨m, hm, heq⟩ := h g (mem_of_sq_eq_one_of_odd_relIndex hN hodd hg hsq)
    exact mem_of_conj_eq_conj hC hm heq

end Abstract

section Inputs

@[expose] def GGSixRootFusionCaseInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          ∀ s ∈ ggG0 p B x L D J, orderOf s = 2 →
            GGRootFusionAlt (ggG0 p B x L D J) (ggM p B x L D J) r s

theorem GGStepThreeChoice.mem_ggG0 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    r ∈ ggG0 p B x L D J := by
  obtain ⟨-, -, -, -, ⟨hrange, -⟩, -⟩ := hctx
  exact hrange ▸ hch.mem_range

theorem ggSixStepThreeDInput_of_caseInput (h : GGSixRootFusionCaseInput) :
    GGSixStepThreeDInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd
  exact ggControlsStrongFusion_zpowers_of_alt Subgroup.le_normalizer
    Subgroup.normal_in_normalizer hodd (hch.mem_ggG0 hctx) hch.2.2.2.2.1 hC
    (h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd)

@[expose] def GGSixRootClassInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          ∀ g : G, g⁻¹ * r * g ∈ ggG0 p B x L D J →
            ∃ m ∈ ggM p B x L D J, g⁻¹ * r * g = m⁻¹ * r * m

theorem ggSixStepThreeDInput_iff_classInput : GGSixStepThreeDInput ↔ GGSixRootClassInput := by
  constructor
  · intro h G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd
    exact (ggControlsStrongFusion_zpowers_iff_forall_conj Subgroup.le_normalizer
      Subgroup.normal_in_normalizer hodd (hch.mem_ggG0 hctx) hch.2.2.2.2.1 hC).mp
      (h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd)
  · intro h G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd
    exact (ggControlsStrongFusion_zpowers_iff_forall_conj Subgroup.le_normalizer
      Subgroup.normal_in_normalizer hodd (hch.mem_ggG0 hctx) hch.2.2.2.2.1 hC).mpr
      (h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd)

end Inputs

end CFSG.StandardType
