module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCases
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Group

variable {G : Type*} [Group G] [Finite G]

theorem ggIsPGroup_two_le_centralizer_eq_bot {J R : Subgroup G} (hRJ : R ≤ J)
    (hR2 : IsPGroup 2 R) (hZ : Odd (Nat.card (Subgroup.center ↥J)))
    (hc : R ≤ Subgroup.centralizer (J : Set G)) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : R.subgroupOf J ≤ Subgroup.center ↥J := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro j
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc hr) j j.2)
  have h2 : IsPGroup 2 (R.subgroupOf J) := hR2.comap_of_injective J.subtype J.subtype_injective
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd : Nat.card (R.subgroupOf J) ∣ Nat.card (Subgroup.center ↥J) :=
    Subgroup.card_dvd_of_le h1
  rw [hk] at hdvd
  have h3 : 2 ^ k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZ)) hdvd
  have h4 : R.subgroupOf J = ⊥ := Subgroup.card_eq_one.mp (by rw [hk, h3])
  rw [← Subgroup.map_subgroupOf_eq_of_le hRJ, h4, Subgroup.map_bot]

end Group

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem ggSR_le_normalizer (R : Subgroup G) :
    ggSR p B x L D J R ≤ Subgroup.normalizer (R : Set G) :=
  inf_le_left.trans (ggPR_le_normalizer R)

theorem ggSR_isPGroup (R : Subgroup G) : IsPGroup 2 (ggSR p B x L D J R) :=
  (ggPCoreOf_two_isPGroup _).to_le inf_le_left

theorem mem_normalizer_ggSR_inf_centralizer {R : Subgroup G} {d m : G}
    (hmG : m ∈ ggG0 p B x L D J) (hmd : m ∈ Subgroup.centralizer {d})
    (hmR : m ∈ Subgroup.normalizer (R : Set G)) :
    m ∈ Subgroup.normalizer
      ((ggSR p B x L D J R ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
  have hmP : m ∈ Subgroup.normalizer (ggPR R : Set G) := mem_normalizer_pCoreOf hmR
  have hmN₀ : m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨hmG, hmR⟩
  have hmQ : m ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) :=
    mem_normalizer_pCoreOf hmN₀
  have hmS : m ∈ Subgroup.normalizer (ggSR p B x L D J R : Set G) :=
    mem_normalizer_inf hmP (Subgroup.le_normalizer hmQ)
  exact mem_normalizer_inf hmS (Subgroup.le_normalizer hmd)

theorem GGSixCtxV2.ggKd_inf_normalizer_le_normalizer_ggSRd
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {d : G} (hd : d ∈ D) (R : Subgroup G) :
    ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((ggSR p B x L D J R ⊓ Subgroup.centralizer {d} : Subgroup G) :
        Set G) := by
  intro m hm
  obtain ⟨hmK, hmR⟩ := Subgroup.mem_inf.mp hm
  exact mem_normalizer_ggSR_inf_centralizer (h.ggKd_le_ggG0 hd hmK)
    (h.ggKd_le_centralizer hd hmK) hmR

theorem GGSixCtxV2.ggSRd_le_normalizer_ggKd (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {R : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hZJ : Odd (Nat.card (Subgroup.center ↥J))) {d : G}
    (hcomp : IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) :
    ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      Subgroup.normalizer (ggKd p B x L D J d : Set G) := by
  intro y hy
  obtain ⟨-, hyd⟩ := Subgroup.mem_inf.mp hy
  have hyR : y ∈ Subgroup.normalizer (R : Set G) :=
    (inf_le_left.trans (ggSR_le_normalizer R)) hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hKy := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp y
  have hydy : y * d * y⁻¹ = d := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyd
    rw [this]
    group
  rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hydy] at hKy
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hcomp hKy with
    heq | hcomm
  · exact heq.symm
  · exfalso
    have hRK : R ≤ ggKd p B x L D J d := hRJ.trans (le_ggKd p B x L D J d)
    have hRKy : R ≤ (ggKd p B x L D J d).map (MulAut.conj y).toMonoidHom := by
      have hRy : R.map (MulAut.conj y).toMonoidHom = R :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyR
      calc R = R.map (MulAut.conj y).toMonoidHom := hRy.symm
        _ ≤ _ := Subgroup.map_mono hRK
    have hcent : (ggKd p B x L D J d).map (MulAut.conj y).toMonoidHom ≤
        Subgroup.centralizer (ggKd p B x L D J d : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    exact hR1 (ggIsPGroup_two_le_centralizer_eq_bot hRJ hR2 hZJ
      ((hRKy.trans hcent).trans (Subgroup.centralizer_le (le_ggKd p B x L D J d))))

theorem GGSixCtxV2.ggSRd_le_sup_centralizer_of_inner
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {R : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) (hZJ : Odd (Nat.card (Subgroup.center ↥J))) {d : G} (hd : d ∈ D)
    (hcomp : IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    (hI : GGRootNormInner (R.subgroupOf (ggKd p B x L D J d))) :
    ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G) :=
  ggRootNormInner_le_sup_centralizer (hRJ.trans (le_ggKd p B x L D J d))
    (h.ggSRd_le_normalizer_ggKd hRJ hR1 hR2 hZJ hcomp)
    (inf_le_left.trans (ggSR_le_normalizer R))
    ((ggSR_isPGroup R).to_le inf_le_left)
    (h.ggKd_inf_normalizer_le_normalizer_ggSRd hd R) hI

theorem GGSixCtxV2.ggSRd_le_sup_centralizer_of_diag
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {R : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) (hZJ : Odd (Nat.card (Subgroup.center ↥J))) {d : G} (hd : d ∈ D)
    (hcomp : IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    {δ : G} (hδG : δ ∈ ggG0 p B x L D J) (hδd : δ ∈ Subgroup.centralizer {d})
    (hδR : δ ∈ Subgroup.normalizer (R : Set G))
    (hδK : δ ∈ Subgroup.normalizer (ggKd p B x L D J d : Set G))
    (hI : GGRootNormInnerDiag (R.subgroupOf (ggKd p B x L D J d))
      ((ggKd p B x L D J d).normalizerMonoidHom ⟨δ, hδK⟩)) :
    ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G) :=
  ggRootNormInnerDiag_le_sup_centralizer (hRJ.trans (le_ggKd p B x L D J d))
    (h.ggSRd_le_normalizer_ggKd hRJ hR1 hR2 hZJ hcomp)
    (inf_le_left.trans (ggSR_le_normalizer R))
    ((ggSR_isPGroup R).to_le inf_le_left)
    (h.ggKd_inf_normalizer_le_normalizer_ggSRd hd R) hδK hδR
    (mem_normalizer_ggSR_inf_centralizer hδG hδd hδR) hI

theorem GGSixCtxV2.ggSR_le_sup_centralizer_of_inner
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {R : Subgroup G} (hRJ : R ≤ J)
    (hSM : ggSR p B x L D J R ≤ ggM p B x L D J)
    (hI : GGRootNormInner (R.subgroupOf (ggG0 p B x L D J))) :
    ggSR p B x L D J R ≤
      ggG0 p B x L D J ⊔ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
  refine ggRootNormInner_le_sup_centralizer (hRJ.trans h.le_ggG0) hSM (ggSR_le_normalizer R)
    (ggSR_isPGroup R) ?_ hI
  intro m hm
  have hmP : m ∈ Subgroup.normalizer (ggPR R : Set G) :=
    mem_normalizer_pCoreOf (Subgroup.mem_inf.mp hm).2
  have hmQ : m ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) := mem_normalizer_pCoreOf hm
  exact mem_normalizer_inf hmP (Subgroup.le_normalizer hmQ)

theorem GGSixCtxV2.centralizer_le_ggM_of_rootNorm (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZ : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    {R J₀ : Subgroup G} (hRJ : R ≤ J) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hJ₀J : J₀ ≤ J)
    (hgen : ggQR p B x L D J R ⊔ J₀ = ggG0 p B x L D J)
    (h4 : ∀ U : Subgroup G, ggCenterOf (ggQR p B x L D J R) ≤ U → U ≤ ggQR p B x L D J R →
        U ≠ ggCenterOf (ggQR p B x L D J R) → U ≠ ggQR p B x L D J R →
        ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) ≤
          Subgroup.normalizer (U : Set G) →
        J ⊔ U = ggG0 p B x L D J)
    (hI₀ : GGRootNormInner (R.subgroupOf (ggG0 p B x L D J)))
    (hd : ∀ d ∈ D, d ≠ 1 →
      GGRootNormNoCentral (R.subgroupOf (ggKd p B x L D J d)) ∧
        (GGRootNormInner (R.subgroupOf (ggKd p B x L D J d)) ∨
          ∃ δ : ↥(Subgroup.normalizer (ggKd p B x L D J d : Set G)),
            (δ : G) ∈ ggG0 p B x L D J ∧ (δ : G) ∈ Subgroup.centralizer {d} ∧
              (δ : G) ∈ Subgroup.normalizer (R : Set G) ∧
              GGRootNormInnerDiag (R.subgroupOf (ggKd p B x L D J d))
                ((ggKd p B x L D J d).normalizerMonoidHom δ))) :
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J := by
  refine hctx.centralizer_le_ggM_of_lieData hodd hZ hRJ hR1 hR2 hJ₀J hgen ?_
    (fun hSM _ => hctx.ggSR_le_sup_centralizer_of_inner hRJ hSM hI₀) (Or.inr h4)
  intro d hd0 hd1
  refine ⟨?_, ggRootNormNoCentral_ambient (hRJ.trans (le_ggKd p B x L D J d)) (hd d hd0 hd1).1⟩
  rcases (hd d hd0 hd1).2 with hI | ⟨δ, hδG, hδd, hδR, hδI⟩
  · exact hctx.ggSRd_le_sup_centralizer_of_inner hRJ hR1 hR2 hZJ hd0 (hcomp d hd0 hd1) hI
  · exact hctx.ggSRd_le_sup_centralizer_of_diag hRJ hR1 hR2 hZJ hd0 (hcomp d hd0 hd1) hδG hδd
      hδR δ.2 hδI

end Ctx

end CFSG.StandardType
