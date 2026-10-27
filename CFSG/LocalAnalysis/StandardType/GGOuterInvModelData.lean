module

public import CFSG.LocalAnalysis.StandardType.GGSteinbergCorrection
public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.Open (IsElemAbelian)

@[expose] def GGG1OddAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      Odd ((ggG0 p B x L D J).relIndex (ggG1 ψ))

@[expose] def GGOuterInvNoneAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ∀ r ∈ ggM p B x L D J, orderOf r = 2 → r ∈ Subgroup.centralizer {b} →
          r ∉ ggG0 p B x L D J →
            ¬ ggG1 ψ ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r}

theorem ggOuterInvAt_of_none
    {t : StatedLieTag} (hSt : GGSteinbergCorrectionAt t)
    (hodd : GGG1OddAt t) (h2 : GGO2CentralizerG0At t) (hN : GGOuterInvNoneAt t) :
    GGOuterInvAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC r hr hr2
  exfalso
  have hO2 := h2 G p B Bs x L D J n f ψ hctx s1 b hb hb1
  have hR1 := ggR_inf_ggG1_eq_bot hctx.range_eq (hodd G p B Bs x L D J n f ψ hctx s1) hO2
  have hP : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ :=
    ⟨hctx.2.2.2.1, ⟨hctx.range_eq, hctx.2.2.2.2.1.2⟩, hctx.perfect, hctx.lieModel⟩
  have hSt' : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), ∃ g ∈ ψ.range,
      GGRootAdmissible (ggU t n f).D ψ (m * g) := by
    intro m hm
    rw [hctx.range_eq] at hm ⊢
    exact hSt G n f ψ _ hP m hm
  have hNorm := ggG1_conj_mem_of_steinberg hctx.range_eq hSt'
  have hRC := ggR_le_centralizer_ggG1 hctx.range_eq hNorm hR1
  have hrM : r ∈ ggM p B x L D J :=
    (pCoreOf_le' 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) hr).1
  have hrb : r ∈ Subgroup.centralizer {b} :=
    (pCoreOf_le' 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) hr).2
  have hrG₀ : r ∉ ggG0 p B x L D J := by
    intro h
    have hmem : r ∈ pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓ ggG1 ψ :=
      ⟨hr, ggG0_le_ggG1 hctx.range_eq h⟩
    rw [hR1, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hle : ggG1 ψ ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r} := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hRC hr) c hc
  exact hN G p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb hrG₀ hle

@[expose] def GGOuterInvNoneModel (C : Type) [Group C] (I : Subgroup (MulAut C)) : Prop :=
  ∀ (p : ℕ) (β α : MulAut C) (E : Subgroup (MulAut C)), p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E →
    E ≤ I → IsElemAbelian p E → p ^ 4 ≤ Nat.card E → E ≤ Subgroup.centralizer {α} →
    α * α = 1 → α ∉ I →
    (∃ L₁ : Subgroup C, (∀ g ∈ L₁, β g = g) ∧ ¬ Group.IsSolvable L₁) →
    ¬ ∀ g : C, β g = g → α g = g

@[expose] def GGOuterInvModelDataAt
    (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C) (I : Subgroup (MulAut C)),
      Function.Surjective π ∧ π.ker = Subgroup.center (ggU t n f).K ∧
      (MulAut.conj : C →* MulAut C).range ≤ I ∧
      Odd ((MulAut.conj : C →* MulAut C).range.relIndex I) ∧
      (∀ (G : Type) [Group G] (ψ : (ggU t n f).K →* G), ψ.ker = Subgroup.center (ggU t n f).K →
        ∀ c ∈ Subgroup.normalizer (ψ.range : Set G), GGPsiInnerDiag (ggU t n f).D ψ c →
          ∃ φ ∈ I, ∀ u u', c * ψ u * c⁻¹ = ψ u' → φ (π u) = π u') ∧
      GGOuterInvNoneModel C I

theorem ggOuterInv_conj_range_normal (C : Type*) [Group C] : (MulAut.conj : C →* MulAut C).range.Normal :=
  ⟨by
    rintro _ ⟨c, rfl⟩ φ
    refine ⟨φ c, ?_⟩
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
      MulAut.apply_inv_self]⟩

theorem ggOuterInv_mem_of_mul_self_mem_of_odd {K : Type*} [Group K] {H I : Subgroup K} [H.Normal]
    (hodd : Odd (H.relIndex I)) {g : K} (hg : g ∈ I) (hg2 : g * g ∈ H) : g ∈ H := by
  let x : I ⧸ H.subgroupOf I := QuotientGroup.mk ⟨g, hg⟩
  have h2 : x ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hg2
  have hd2 : orderOf x ∣ Nat.card (I ⧸ H.subgroupOf I) := orderOf_dvd_natCard x
  have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd hd2
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ggOuterInv_not_isSolvable_of_isComponentOf {G : Type*} [Group G] {L K : Subgroup G}
    (h : IsComponentOf L K) : ¬ Group.IsSolvable L := by
  intro hs
  obtain ⟨-, -, hperf, hsimple⟩ := h
  haveI : Group.IsPerfect L := ⟨hperf⟩
  haveI : Nontrivial (L ⧸ Subgroup.center L) := hsimple.toNontrivial
  haveI : Nontrivial L := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    exact hxy (congrArg _ (Subsingleton.elim a b))
  exact Group.IsPerfect.not_isSolvable L hs

noncomputable def ggOuterInvModelEquiv {U C G : Type*} [Group U] [Group C] [Group G]
    (ψ : U →* G) (π : U →* C) (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) : C ≃* ψ.range :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange ψ))

theorem ggOuterInvModelEquiv_apply {U C G : Type*} [Group U] [Group C] [Group G]
    (ψ : U →* G) (π : U →* C) (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) (y : U) :
    ((ggOuterInvModelEquiv ψ π hπ hker (π y) : ψ.range) : G) = ψ y := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π y) = (y : U ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [ggOuterInvModelEquiv, MulEquiv.trans_apply, e]
  rfl

theorem ggOuterInv_ker_eq_center_of_centralizer {U G : Type*} [Group U] [Group G] (ψ : U →* G)
    (hker : ψ.ker ≤ Subgroup.center U) (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ψ.ker = Subgroup.center U := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

theorem ggOuterInv_exists_modelHom
    {U C G : Type*} [Group U] [Group C] [Group G] {G₀ : Subgroup G}
    (ψ : U →* G) (hr : ψ.range = G₀) (π : U →* C) (hπ : Function.Surjective π)
    (hker : π.ker = ψ.ker) (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) :
    ∃ (Θ : C ≃* G₀) (Φ : Subgroup.normalizer (G₀ : Set G) →* MulAut C),
      (∀ u, (Θ (π u) : G) = ψ u) ∧ Function.Injective Φ ∧
      ∀ m x, (Θ (Φ m x) : G) = (m : G) * Θ x * (m : G)⁻¹ := by
  let Θ : C ≃* G₀ := (ggOuterInvModelEquiv ψ π hπ hker).trans (MulEquiv.subgroupCongr hr)
  let Φ : Subgroup.normalizer (G₀ : Set G) →* MulAut C :=
    (MulAut.congr Θ.symm).toMonoidHom.comp (Subgroup.normalizerMonoidHom G₀)
  have hΦ : ∀ m x, (Θ (Φ m x) : G) = (m : G) * Θ x * (m : G)⁻¹ := by
    intro m x
    change ((Θ (Θ.symm (Subgroup.normalizerMonoidHom G₀ m (Θ x)))) : G) = _
    rw [MulEquiv.apply_symm_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  refine ⟨Θ, Φ, fun u => ggOuterInvModelEquiv_apply ψ π hπ hker u, ?_, hΦ⟩
  rw [injective_iff_map_eq_one]
  intro m hm
  have hcent : (m : G) ∈ Subgroup.centralizer (G₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hΦ m (Θ.symm ⟨y, hy⟩)
    rw [hm, MulAut.one_apply, MulEquiv.apply_symm_apply] at h
    calc y * (m : G) = (m : G) * y * (m : G)⁻¹ * (m : G) := by rw [← h]
      _ = (m : G) * y := by group
  rw [hC, Subgroup.mem_bot] at hcent
  exact Subtype.ext hcent

theorem ggOuterInv_modelHom_of_mem {C G : Type*} [Group C] [Group G] {G₀ : Subgroup G} (Θ : C ≃* G₀)
    (Φ : Subgroup.normalizer (G₀ : Set G) →* MulAut C)
    (hΦ : ∀ m x, (Θ (Φ m x) : G) = (m : G) * Θ x * (m : G)⁻¹) (y : G₀) :
    Φ ⟨y, Subgroup.le_normalizer y.2⟩ = MulAut.conj (Θ.symm y) := by
  ext x
  apply Θ.injective
  apply Subtype.ext
  rw [hΦ, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem ggOuterInv_exists_model_of_data
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGOuterInvModelDataAt t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J) :
    ∃ (C : Type) (_ : Group C) (I : Subgroup (MulAut C)) (Θ : C ≃* ggG0 p B x L D J)
      (Φ : Subgroup.normalizer (ggG0 p B x L D J : Set G) →* MulAut C),
      (MulAut.conj : C →* MulAut C).range ≤ I ∧
      Odd ((MulAut.conj : C →* MulAut C).range.relIndex I) ∧ GGOuterInvNoneModel C I ∧
      Function.Injective Φ ∧ (∀ m y, (Θ (Φ m y) : G) = (m : G) * Θ y * (m : G)⁻¹) ∧
      ∀ c : Subgroup.normalizer (ggG0 p B x L D J : Set G), (c : G) ∈ ggG1 ψ → Φ c ∈ I := by
  obtain ⟨C, _, π, I, hπ, hπker, hInn, hodd, hmark, hmodel⟩ :=
    h n f hctx.2.2.2.1.1 hctx.2.2.2.1.2
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]; exact s1.1
  have hψ : ψ.ker = Subgroup.center (ggU t n f).K :=
    ggOuterInv_ker_eq_center_of_centralizer ψ hctx.2.2.2.2.1.2 hC'
  obtain ⟨Θ, Φ, hΘ, hΦinj, hΦ⟩ :=
    ggOuterInv_exists_modelHom ψ hctx.range_eq π hπ (hπker.trans hψ.symm) s1.1
  refine ⟨C, inferInstance, I, Θ, Φ, hInn, hodd, hmodel, hΦinj, hΦ, fun c hc => ?_⟩
  have hcN : (c : G) ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]; exact c.2
  obtain ⟨φ, hφI, hφ⟩ := hmark G ψ hψ c hcN hc.2
  suffices Φ c = φ by rw [this]; exact hφI
  ext y
  obtain ⟨u, rfl⟩ := hπ y
  obtain ⟨u', hu'⟩ : (c : G) * ψ u * (c : G)⁻¹ ∈ ψ.range :=
    (Subgroup.mem_normalizer_iff.mp hcN (ψ u)).mp ⟨u, rfl⟩
  rw [hφ u u' hu'.symm]
  apply Θ.injective
  apply Subtype.ext
  rw [hΦ, hΘ, hΘ, hu']

theorem ggG1OddAt_of_modelData
    {t : StatedLieTag}
    (h : GGOuterInvModelDataAt t) : GGG1OddAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1
  obtain ⟨C, _, I, Θ, Φ, hInn, hodd, -, hΦinj, hΦ, hΦI⟩ := ggOuterInv_exists_model_of_data h hctx s1
  have hG1N : ggG1 ψ ≤ (Subgroup.normalizer (ggG0 p B x L D J : Set G)) := ggG1_le_ggM hctx.range_eq
  have hG01 : ggG0 p B x L D J ≤ ggG1 ψ := ggG0_le_ggG1 hctx.range_eq
  have hmap0 : ((ggG0 p B x L D J).subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))).map Φ =
      (MulAut.conj : C →* MulAut C).range := by
    ext φ
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Θ.symm ⟨y, hy⟩, ?_⟩
      rw [← ggOuterInv_modelHom_of_mem Θ Φ hΦ ⟨y, hy⟩]
    · rintro ⟨c, rfl⟩
      refine ⟨⟨Θ c, Subgroup.le_normalizer (Θ c).2⟩, (Θ c).2, ?_⟩
      rw [ggOuterInv_modelHom_of_mem Θ Φ hΦ (Θ c), MulEquiv.symm_apply_apply]
  have hmap1 : ((ggG1 ψ).subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))).map Φ ≤ I := by
    rintro _ ⟨c, hc, rfl⟩
    exact hΦI c hc
  have hle01 : (MulAut.conj : C →* MulAut C).range ≤ ((ggG1 ψ).subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))).map Φ := by
    rw [← hmap0]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hG01)
  have heq : (ggG0 p B x L D J).relIndex (ggG1 ψ) =
      (MulAut.conj : C →* MulAut C).range.relIndex (((ggG1 ψ).subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))).map Φ) := by
    rw [← hmap0, Subgroup.relIndex_map_map_of_injective _ _ hΦinj,
      Subgroup.relIndex_subgroupOf hG1N]
  rw [heq]
  exact Odd.of_dvd_nat hodd (Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ hle01 hmap1))

theorem ggOuterInvNoneAt_of_modelData
    {t : StatedLieTag}
    (h : GGOuterInvModelDataAt t) : GGOuterInvNoneAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb hrG₀ hle
  obtain ⟨C, _, I, Θ, Φ, -, hodd, hmodel, hΦinj, hΦ, hΦI⟩ := ggOuterInv_exists_model_of_data h hctx s1
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := fun y hy =>
    ggG1_le_ggM hctx.range_eq (ggBs_le_ggG1 hctx hy)
  have hrN : r ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := hrM
  let β : MulAut C := Φ ⟨b, hBsN hb⟩
  let α : MulAut C := Φ ⟨r, hrN⟩
  let E : Subgroup (MulAut C) :=
    (Bs.subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))).map Φ
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hb1
    have := hΦinj (h1.trans (map_one Φ).symm)
    exact congrArg Subtype.val this
  have hβE : β ∈ E := ⟨⟨b, hBsN hb⟩, hb, rfl⟩
  have hEI : E ≤ I := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΦI y (ggBs_le_ggG1 hctx hy)
  have hBsSub : IsElemAbelian p (Bs.subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))) := by
    refine ⟨IsMulCommutative.of_comm fun a c => ?_, fun y hy => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥Bs => (w : G))
        (hctx.bstar.2.1.1.is_comm.comm ⟨(a : G), a.2⟩ ⟨(c : G), c.2⟩)
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hctx.bstar.2.1.2 (y : G) hy
  have hEel : IsElemAbelian p E := CFSG.SectionRank.isElemAbelian_map hBsSub Φ
  have hE4 : p ^ 4 ≤ Nat.card E := by
    have h1 : Nat.card E =
        Nat.card (Bs.subgroupOf (Subgroup.normalizer (ggG0 p B x L D J : Set G))) :=
      Subgroup.card_map_of_injective hΦinj
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsN).toEquiv]
    exact ggBs_four_le_card hctx.1 hctx.bstar
  have hrcomm : ∀ y : G, y ∈ ggG1 ψ ⊓ Subgroup.centralizer {b} → r * y = y * r := by
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) r (Set.mem_singleton r))
  have hEα : E ≤ Subgroup.centralizer {α} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyb : (y : G) ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun w : ↥Bs => (w : G))
        (hctx.bstar.2.1.1.is_comm.comm ⟨(y : G), hy⟩ ⟨b, hb⟩)
    have hc := hrcomm y ⟨ggBs_le_ggG1 hctx hy, hyb⟩
    have hc' : y * (⟨r, hrN⟩ : Subgroup.normalizer (ggG0 p B x L D J : Set G)) = ⟨r, hrN⟩ * y :=
      Subtype.ext hc.symm
    change Φ y * Φ ⟨r, hrN⟩ = Φ ⟨r, hrN⟩ * Φ y
    rw [← map_mul, ← map_mul, hc']
  have hrr : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rwa [hr2, pow_two] at h
  have hα2 : α * α = 1 := by
    change Φ ⟨r, hrN⟩ * Φ ⟨r, hrN⟩ = 1
    rw [← map_mul]
    have : (⟨r, hrN⟩ : Subgroup.normalizer (ggG0 p B x L D J : Set G)) * ⟨r, hrN⟩ = 1 :=
      Subtype.ext hrr
    rw [this, map_one]
  have hαI : α ∉ I := by
    intro hαI
    haveI := ggOuterInv_conj_range_normal C
    obtain ⟨c, hc⟩ := ggOuterInv_mem_of_mul_self_mem_of_odd hodd hαI (by rw [hα2]; exact Subgroup.one_mem _)
    apply hrG₀
    have h1 : Φ ⟨r, hrN⟩ = Φ ⟨Θ c, Subgroup.le_normalizer (Θ c).2⟩ := by
      rw [ggOuterInv_modelHom_of_mem Θ Φ hΦ (Θ c), MulEquiv.symm_apply_apply]
      exact hc.symm
    have h2 := congrArg Subtype.val (hΦinj h1)
    change r = (Θ c : G) at h2
    rw [h2]
    exact (Θ c).2
  have hL₁G₀ : L₁ ≤ ggG0 p B x L D J := hL₁.1.trans inf_le_left
  let L' : Subgroup C := L₁.comap ((ggG0 p B x L D J).subtype.comp Θ.toMonoidHom)
  have hL'fix : ∀ g ∈ L', β g = g := by
    intro g hg
    have hgb : (Θ g : G) ∈ Subgroup.centralizer {b} := (hL₁.1 hg).2
    apply Θ.injective
    apply Subtype.ext
    change (Θ (Φ ⟨b, hBsN hb⟩ g) : G) = Θ g
    rw [hΦ]
    have hc : b * (Θ g : G) = (Θ g : G) * b :=
      (Subgroup.mem_centralizer_iff.mp hgb b (Set.mem_singleton b))
    change b * (Θ g : G) * b⁻¹ = Θ g
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hL'ns : ¬ Group.IsSolvable L' := by
    intro hs
    haveI := hs
    apply ggOuterInv_not_isSolvable_of_isComponentOf hL₁
    let φ : L₁ →* L' :=
      { toFun := fun y => ⟨Θ.symm ⟨y, hL₁G₀ y.2⟩, by
          change ((Θ (Θ.symm ⟨y, hL₁G₀ y.2⟩)) : G) ∈ L₁
          rw [MulEquiv.apply_symm_apply]
          exact y.2⟩
        map_one' := by
          apply Subtype.ext
          change Θ.symm ⟨1, _⟩ = 1
          exact (MulEquiv.symm_apply_eq Θ).mpr (by rw [map_one]; rfl)
        map_mul' := fun y z => by
          apply Subtype.ext
          change Θ.symm ⟨(y : G) * z, _⟩ = Θ.symm ⟨y, _⟩ * Θ.symm ⟨z, _⟩
          rw [← map_mul]
          rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := φ) fun y z hyz => ?_
    have h1 := congrArg (fun w : L' => (Θ (w : C) : G)) hyz
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.apply_symm_apply] at h1
    exact Subtype.ext h1
  refine hmodel p β α E hctx.prime hctx.ne_two hβ1 hβE hEI hEel hE4 hEα hα2 hαI
    ⟨L', hL'fix, hL'ns⟩ fun g hg => ?_
  have hgb : (Θ g : G) ∈ Subgroup.centralizer {b} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg (fun w : C => (Θ w : G)) hg
    change (Θ (Φ ⟨b, hBsN hb⟩ g) : G) = Θ g at h1
    rw [hΦ] at h1
    change b * (Θ g : G) * b⁻¹ = Θ g at h1
    calc (Θ g : G) * b = (b * (Θ g : G) * b⁻¹) * b := by rw [h1]
      _ = b * (Θ g : G) := by group
  have hc := hrcomm (Θ g) ⟨ggG0_le_ggG1 hctx.range_eq (Θ g).2, hgb⟩
  apply Θ.injective
  apply Subtype.ext
  change (Θ (Φ ⟨r, hrN⟩ g) : G) = Θ g
  rw [hΦ]
  change r * (Θ g : G) * r⁻¹ = Θ g
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem ggOuterInvAt_of_modelData
    {t : StatedLieTag}
    (hSt : GGSteinbergCorrectionAt t)
    (h2 : GGO2CentralizerG0At t) (h : GGOuterInvModelDataAt t) : GGOuterInvAt t :=
  ggOuterInvAt_of_none hSt (ggG1OddAt_of_modelData h) h2 (ggOuterInvNoneAt_of_modelData h)

theorem ggOuterInv_marking_of_closure
    {U C G : Type*} [Group U] [Group C] [Group G]
    (ψ : U →* G) (π : U →* C) (hπ : Function.Surjective π) (hker : π.ker = ψ.ker)
    {S : Set U} (hS : Subgroup.closure S = ⊤) (x : G) (δ : MulAut C)
    (h : ∀ s ∈ S, ∃ s', x⁻¹ * ψ s * x = ψ s' ∧ δ (π s) = π s') :
    ∀ u u', x⁻¹ * ψ u * x = ψ u' → δ (π u) = π u' := by
  let ι : C →* G := ψ.range.subtype.comp (ggOuterInvModelEquiv ψ π hπ hker).toMonoidHom
  have hι : ∀ y, ι (π y) = ψ y := ggOuterInvModelEquiv_apply ψ π hπ hker
  have hιinj : Function.Injective ι :=
    Subtype.val_injective.comp (ggOuterInvModelEquiv ψ π hπ hker).injective
  have heq : ι.comp (δ.toMonoidHom.comp π) = (MulAut.conj x⁻¹).toMonoidHom.comp ψ := by
    refine MonoidHom.eq_of_eqOn_dense hS fun s hs => ?_
    obtain ⟨s', h1, h2⟩ := h s hs
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [h2, hι, h1]
  intro u u' hu
  apply hιinj
  have h3 := DFunLike.congr_fun heq u
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h3
  rw [h3, hu, hι]

end CFSG.StandardType
