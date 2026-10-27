module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.Open (IsElemAbelian)

@[expose] def GGFieldOuterInvModel (C : Type) [Group C] : Prop :=
  ∀ (p : ℕ) (b : C) (α : MulAut C), p.Prime → p ≠ 2 → b ≠ 1 → b ^ p = 1 →
    (∃ E : Subgroup C, IsElemAbelian p E ∧ b ∈ E ∧ p ^ 4 ≤ Nat.card E ∧
      ∀ A : Subgroup C, IsElemAbelian p A → Nat.card A ≤ Nat.card E) →
    α * α = 1 → (∀ c : C, α ≠ MulAut.conj c) → α b = b →
    (∃ L₁ : Subgroup C, IsComponentOf L₁ (Subgroup.centralizer {b})) →
    ¬ ∀ g ∈ Subgroup.centralizer {b}, α g = g

@[expose] def GGFieldOuterInvModelAt
    (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank → ¬ (t = .F4 ∧ Odd f) →
    ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C), Function.Surjective π ∧
      π.ker = Subgroup.center (ggU t n f).K ∧ GGFieldOuterInvModel C

@[expose] def GGFieldOuterInvF4Odd
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .F4 n f).K →* G), Odd f →
    GGSixCtxV2 p B Bs x L D J (ggU .F4 n f).D .F4 n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ∀ r ∈ ggM p B x L D J, orderOf r = 2 → r ∈ Subgroup.centralizer {b} →
          r ∉ ggG0 p B x L D J →
            ¬ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r}

private noncomputable def ggFieldOuterModel_modelEquiv
    {U C G : Type*} [Group U] [Group C] [Group G]
    (ψ : U →* G) (π : U →* C) (hπ : Function.Surjective π)
    (hker : π.ker = ψ.ker) : C ≃* ψ.range :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange ψ))

private theorem ggFieldOuterModel_modelEquiv_apply
    {U C G : Type*} [Group U] [Group C] [Group G]
    (ψ : U →* G) (π : U →* C) (hπ : Function.Surjective π)
    (hker : π.ker = ψ.ker) (y : U) :
    ((ggFieldOuterModel_modelEquiv ψ π hπ hker (π y) : ψ.range) : G) = ψ y := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π y) =
      (y : U ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [ggFieldOuterModel_modelEquiv, MulEquiv.trans_apply, e]
  rfl

private theorem ggFieldOuterModel_ker_eq_center
    {U G : Type*} [Group U] [Group G] (ψ : U →* G)
    (hker : ψ.ker ≤ Subgroup.center U)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ψ.ker = Subgroup.center U := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

theorem ggBs_four_le_card {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (h : GGThmIHyp p B x L) (hB : GGBstar p B Bs) : p ^ 4 ≤ Nat.card Bs := by
  obtain ⟨-, -, -, -, -, hbeta, hsstar, -⟩ := h
  obtain ⟨hBmax, -⟩ := hsstar
  have hprime : p.Prime := hbeta.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hbeta.2.2.2
  have hcardB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hBmax.2.1
  have hle : B ≤ Bs := hB.1
  calc
    p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hprime.pos h4
    _ = Nat.card B := hcardB.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hle

theorem ggFieldOuterInvAt_of_modelData
    {t : StatedLieTag} (hI : GGInnerTag t) {C : Type} [Group C]
    (hmodel : GGFieldOuterInvModel C)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {ψ : (ggU t n f).K →* G} (π : (ggU t n f).K →* C) (hπ : Function.Surjective π)
    (hπker : π.ker = Subgroup.center (ggU t n f).K)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    {b : G} {L₁ : Subgroup G} (hb : b ∈ Bs) (hb1 : b ≠ 1)
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}))
    {r : G} (hrM : r ∈ ggM p B x L D J) (hr2 : orderOf r = 2)
    (hrb : r ∈ Subgroup.centralizer {b}) (hrnot : r ∉ ggG0 p B x L D J) :
    ¬ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r} := by
  have hpsi : GGPsiDiagInnerAt t := ggPsiDiagInnerAt_of_ggInnerTag t hI
  have hBsG0 : Bs ≤ ggG0 p B x L D J := fun y hy =>
    ggG1_le_ggG0_of_diagInner hpsi hctx s1 (ggBs_le_ggG1 hctx hy)
  have hbG0 : b ∈ ggG0 p B x L D J := hBsG0 hb
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]; exact s1.1
  have hψ : ψ.ker = Subgroup.center (ggU t n f).K :=
    ggFieldOuterModel_ker_eq_center ψ hctx.2.2.2.2.1.2 hC'
  let Θ : C ≃* ↥(ggG0 p B x L D J) :=
    (ggFieldOuterModel_modelEquiv ψ π hπ (hπker.trans hψ.symm)).trans
      (MulEquiv.subgroupCongr hctx.range_eq)
  have hΘ : ∀ y, ((Θ (π y) : ↥(ggG0 p B x L D J)) : G) = ψ y := fun y =>
    ggFieldOuterModel_modelEquiv_apply ψ π hπ (hπker.trans hψ.symm) y
  let b' : C := Θ.symm ⟨b, hbG0⟩
  have hb'Θ : Θ b' = ⟨b, hbG0⟩ := Θ.apply_symm_apply _
  have hb'1 : b' ≠ 1 := by
    intro h1
    rw [h1, map_one] at hb'Θ
    exact hb1 (Subtype.ext_iff.mp hb'Θ.symm)
  have hb'p : b' ^ p = 1 := by
    apply Θ.injective
    rw [map_pow, map_one, hb'Θ]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hctx.bstar.2.1.2 b hb
  have hBs_ne_bot : Bs ≠ ⊥ := by
    intro hbot
    have hmem : b ∈ (⊥ : Subgroup G) := hbot ▸ hb
    rw [Subgroup.mem_bot] at hmem
    exact hb1 hmem
  have hBsSub : IsElemAbelian p (Bs.subgroupOf (ggG0 p B x L D J)) := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun y hy => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥Bs => (w : G))
        (hctx.bstar.2.1.1.is_comm.comm ⟨(a : G), a.2⟩ ⟨(b : G), b.2⟩)
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hctx.bstar.2.1.2 (y : G) hy
  let E' : Subgroup C := (Bs.subgroupOf (ggG0 p B x L D J)).map Θ.symm.toMonoidHom
  have hE'el : IsElemAbelian p E' :=
    CFSG.SectionRank.isElemAbelian_map hBsSub Θ.symm.toMonoidHom
  have hb'E' : b' ∈ E' := by
    rw [show E' = Subgroup.map Θ.symm.toMonoidHom
        (Bs.subgroupOf (ggG0 p B x L D J)) from rfl, Subgroup.mem_map]
    exact ⟨⟨b, hbG0⟩, hb, rfl⟩
  have hE'card : Nat.card E' = Nat.card Bs := by
    have h1 : Nat.card E' = Nat.card (Bs.subgroupOf (ggG0 p B x L D J)) := by
      change Nat.card ↥(Subgroup.map Θ.symm.toMonoidHom
        (Bs.subgroupOf (ggG0 p B x L D J))) = _
      rw [Subgroup.card_map_of_injective Θ.symm.injective]
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsG0).toEquiv
  have h4 : p ^ 4 ≤ Nat.card E' := by
    rw [hE'card]
    exact ggBs_four_le_card hctx.1 hctx.bstar
  have hbound : ∀ A : Subgroup C, IsElemAbelian p A → Nat.card A ≤ Nat.card E' := by
    intro A hA
    have hA'el : IsElemAbelian p
        ((A.map Θ.toMonoidHom).map (ggG0 p B x L D J).subtype) :=
      CFSG.SectionRank.isElemAbelian_map
        (CFSG.SectionRank.isElemAbelian_map hA Θ.toMonoidHom)
        (ggG0 p B x L D J).subtype
    have hA'M : (A.map Θ.toMonoidHom).map (ggG0 p B x L D J).subtype ≤
        ggM p B x L D J := by
      rintro _ ⟨y, -, rfl⟩
      exact Subgroup.le_normalizer y.2
    have hlek := ggAKF_card_le_card_bstar hctx.prime hctx.bstar.2.1 hBs_ne_bot s1
      hA'el hA'M
    have hcard : Nat.card ((A.map Θ.toMonoidHom).map
          (ggG0 p B x L D J).subtype) = Nat.card A := by
      rw [Subgroup.card_map_of_injective (ggG0 p B x L D J).subtype_injective,
        Subgroup.card_map_of_injective Θ.injective]
    rw [← hcard, hE'card]
    exact hlek
  have hrr : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr2, pow_two] at h
    exact h
  let φr : MulAut ↥(ggG0 p B x L D J) :=
    Subgroup.normalizerMonoidHom (ggG0 p B x L D J) ⟨r, hrM⟩
  have hφr2 : φr * φr = 1 := by
    change Subgroup.normalizerMonoidHom (ggG0 p B x L D J) ⟨r, hrM⟩ *
      Subgroup.normalizerMonoidHom (ggG0 p B x L D J) ⟨r, hrM⟩ = 1
    rw [← map_mul]
    have h2 : (⟨r, hrM⟩ : ↥(Subgroup.normalizer (ggG0 p B x L D J : Set G))) *
        ⟨r, hrM⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact hrr
    rw [h2, map_one]
  let α : MulAut C := (Θ.trans φr).trans Θ.symm
  have hα2 : α * α = 1 := by
    ext g
    rw [MulAut.mul_apply, MulAut.one_apply]
    change Θ.symm (φr (Θ (Θ.symm (φr (Θ g))))) = g
    rw [MulEquiv.apply_symm_apply, ← MulAut.mul_apply, hφr2, MulAut.one_apply,
      MulEquiv.symm_apply_apply]
  have hφrb : φr ⟨b, hbG0⟩ = ⟨b, hbG0⟩ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hrb' : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp hrb
    rw [hrb', mul_assoc, mul_inv_cancel, mul_one]
  have hαb' : α b' = b' := by
    change Θ.symm (φr (Θ b')) = b'
    rw [hb'Θ, hφrb]
  have hαout : ∀ c : C, α ≠ MulAut.conj c := by
    intro c hc
    have hrel : ∀ z : C, φr (Θ z) = Θ c * Θ z * (Θ c)⁻¹ := by
      intro z
      have h1 : α z = MulAut.conj c z := congrArg (fun f : MulAut C => f z) hc
      calc φr (Θ z) = Θ (α z) := by
            change φr (Θ z) = Θ (Θ.symm (φr (Θ z)))
            rw [MulEquiv.apply_symm_apply]
        _ = Θ (MulAut.conj c z) := by rw [h1]
        _ = Θ c * Θ z * (Θ c)⁻¹ := by
            rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hcentral : (Θ c : G)⁻¹ * r ∈
        Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hz := hrel (Θ.symm ⟨y, hy⟩)
      rw [MulEquiv.apply_symm_apply] at hz
      have hz' : r * y * r⁻¹ = (Θ c : G) * y * (Θ c : G)⁻¹ := by
        have h := congrArg (fun z : ↥(ggG0 p B x L D J) => (z : G)) hz
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
        exact h
      have hconj : ((Θ c : G)⁻¹ * r) * y * ((Θ c : G)⁻¹ * r)⁻¹ = y := by
        have h1 : ((Θ c : G)⁻¹ * r) * y * ((Θ c : G)⁻¹ * r)⁻¹ =
            (Θ c : G)⁻¹ * (r * y * r⁻¹) * (Θ c : G) := by group
        rw [h1, hz']
        group
      have hu : ((Θ c : G)⁻¹ * r) * y = y * ((Θ c : G)⁻¹ * r) := by
        calc ((Θ c : G)⁻¹ * r) * y =
              ((Θ c : G)⁻¹ * r) * y * ((Θ c : G)⁻¹ * r)⁻¹ *
                ((Θ c : G)⁻¹ * r) := by group
          _ = y * ((Θ c : G)⁻¹ * r) := by rw [hconj]
      exact hu.symm
    rw [s1.1, Subgroup.mem_bot] at hcentral
    apply hrnot
    have hr_eq : r = (Θ c : G) := by
      calc r = (Θ c : G) * ((Θ c : G)⁻¹ * r) := by group
        _ = (Θ c : G) * 1 := by rw [hcentral]
        _ = (Θ c : G) := mul_one _
    rw [hr_eq]
    exact (Θ c).2
  have hmapK : ((ggG0 p B x L D J ⊓ Subgroup.centralizer {b}).subgroupOf
      (ggG0 p B x L D J)).map Θ.symm.toMonoidHom = Subgroup.centralizer {b'} := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Θ.injective
      change Θ (Θ.symm y * b') = Θ (b' * Θ.symm y)
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb'Θ]
      apply Subtype.ext
      have hy' : (y : G) * b = b * (y : G) := by
        have hmem : (y : G) ∈ Subgroup.centralizer {b} := by
          have hy2 := hy
          change (y : G) ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} at hy2
          exact hy2.2
        exact Subgroup.mem_centralizer_singleton_iff.mp hmem
      simpa only [Subgroup.coe_mul] using hy'
    · intro hg
      refine ⟨Θ g, ?_, Θ.symm_apply_apply g⟩
      change (Θ g : G) ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer {b}
      refine ⟨(Θ g).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h := congrArg (fun x : C => Θ x) hg
      rw [map_mul, map_mul, hb'Θ] at h
      simpa only [Subgroup.coe_mul] using Subtype.ext_iff.mp h
  have hcomp : ∃ L₁' : Subgroup C, IsComponentOf L₁' (Subgroup.centralizer {b'}) := by
    refine ⟨(L₁.subgroupOf (ggG0 p B x L D J)).map Θ.symm.toMonoidHom, ?_⟩
    have hKQ : IsComponentOf (L₁.subgroupOf (ggG0 p B x L D J))
        ((ggG0 p B x L D J ⊓ Subgroup.centralizer {b}).subgroupOf
          (ggG0 p B x L D J)) := ggIsComponentOf_subgroupOf hL₁ inf_le_left
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Θ.symm.toMonoidHom) Θ.symm.injective).2 hKQ
    rw [hmapK] at h1
    exact h1
  have hmodel_concl : ¬ ∀ g ∈ Subgroup.centralizer {b'}, α g = g :=
    hmodel p b' α hctx.prime hctx.ne_two hb'1 hb'p ⟨E', hE'el, hb'E', h4, hbound⟩
      hα2 hαout hαb' hcomp
  intro hle
  refine hmodel_concl fun g hg => ?_
  have hgG0 : (Θ g : G) ∈ ggG0 p B x L D J := (Θ g).2
  have hgb : (Θ g : G) ∈ Subgroup.centralizer {b} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have h := congrArg (fun x : C => Θ x) hg
    rw [map_mul, map_mul, hb'Θ] at h
    simpa only [Subgroup.coe_mul] using Subtype.ext_iff.mp h
  have hgr : (Θ g : G) ∈ Subgroup.centralizer {r} :=
    hle (Subgroup.mem_inf.mpr ⟨hgG0, hgb⟩)
  have hfix : φr (Θ g) = Θ g := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hcomm : r * (Θ g : G) = (Θ g : G) * r :=
      Subgroup.mem_centralizer_iff.mp hgr r (Set.mem_singleton r)
    calc r * (Θ g : G) * r⁻¹ = (Θ g : G) * r * r⁻¹ := by rw [hcomm]
      _ = (Θ g : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  change Θ.symm (φr (Θ g)) = g
  rw [hfix, MulEquiv.symm_apply_apply]

theorem ggFieldOuterInvAt_of_model
    {t : StatedLieTag} (ht : t = .PSp ∨ t = .F4 ∨ t = .E7 ∨ t = .E8) (h : GGFieldOuterInvModelAt t)
    (hodd : t = .F4 → GGFieldOuterInvF4Odd) : GGFieldOuterInvAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb hrnot
  by_cases hF4odd : t = .F4 ∧ Odd f
  · obtain ⟨rfl, hf⟩ := hF4odd
    exact hodd rfl G p B Bs x L D J n f ψ hf hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb
      hrnot
  · obtain ⟨C, _, π, hπ, hπker, hmodel⟩ :=
      h n f hctx.2.2.2.1.1 hctx.2.2.2.1.2 hF4odd
    have hI : GGInnerTag t := by
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    exact ggFieldOuterInvAt_of_modelData hI hmodel π hπ hπker hctx s1 hb hb1 hL₁ hrM hr2 hrb
      hrnot

end CFSG.StandardType
