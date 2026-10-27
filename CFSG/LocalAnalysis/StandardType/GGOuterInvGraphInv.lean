module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatKGDefs
public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.StandardType.GGE0Frame

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

private theorem ggOIGI_isPGroup_pCoreOf {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    IsPGroup p (pCoreOf p H) :=
  (pCore_isPGroup (p := p) (G := H)).map H.subtype

private theorem ggOIGI_pCoreOf_le_self {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    pCoreOf p H ≤ H := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

private theorem ggOIGI_conj_mem_pCoreOf {G : Type} [Group G] {p : ℕ} {H : Subgroup G}
    {x z : G} (hx : x ∈ pCoreOf p H)
    (hz : z ∈ H) : z * x * z⁻¹ ∈ pCoreOf p H := by
  obtain ⟨h, hh, rfl⟩ := hx
  refine ⟨⟨z, hz⟩ * h * ⟨z, hz⟩⁻¹, (pCore_normal (p := p) (G := H)).conj_mem h hh _, ?_⟩
  simp

theorem xi_of_outer_involution {G : Type} [Group G] [Finite G] {M G₀ E₀ : Subgroup G} {b r : G}
    (hG₀M : G₀ ≤ M) (hnorm : M ≤ Subgroup.normalizer (G₀ : Set G))
    (hRG₀ : pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) ⊓ G₀ = ⊥)
    (hRC : pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) ≤
      Subgroup.centralizer ((G₀ ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G))
    (hE₀ : E₀ ≤ G₀ ⊓ Subgroup.centralizer {b})
    (hr : r ∈ pCoreOf 2 (M ⊓ Subgroup.centralizer {b})) (hr2 : orderOf r = 2)
    (hOut : ∀ Q : Subgroup G, Q ≤ M → IsPGroup 2 Q → (G₀.subgroupOf Q).index ≤ 2)
    (hO2 : ∀ N : Subgroup G, N ≤ G₀ ⊓ Subgroup.centralizer {r} → IsPGroup 2 N →
      (∀ x ∈ N, ∀ z ∈ G₀ ⊓ Subgroup.centralizer {r}, z * x * z⁻¹ ∈ N) → N = ⊥)
    (hnot2 : ¬ IsPGroup 2 ↥(G₀ ⊓ Subgroup.centralizer {r}))
    (hCC : G₀ ⊓ Subgroup.centralizer
      ((G₀ ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) = ⊥) :
    GGOTwoXi M E₀ b := by
  classical
  set R := pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) with hRdef
  have hRM : R ≤ M := (ggOIGI_pCoreOf_le_self 2 _).trans inf_le_left
  have hrM : r ∈ M := hRM hr
  have hr1 : r ≠ 1 := by
    rintro rfl
    simp at hr2
  have hrG₀ : r ∉ G₀ := by
    intro h
    have : r ∈ R ⊓ G₀ := ⟨hr, h⟩
    rw [hRG₀, Subgroup.mem_bot] at this
    exact hr1 this
  have hRcard : Nat.card R ≤ 2 := by
    have h := hOut R hRM (ggOIGI_isPGroup_pCoreOf 2 _)
    have hbot : G₀.subgroupOf R = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have : (x : G) ∈ R ⊓ G₀ := ⟨x.2, hx⟩
      rw [hRG₀, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subtype.ext this)
    rwa [hbot, Subgroup.index_bot] at h
  have hzR : Subgroup.zpowers r ≤ R := (Subgroup.zpowers_le).2 hr
  have hRz : R = Subgroup.zpowers r := by
    refine (Subgroup.eq_of_le_of_card_ge hzR ?_).symm
    rw [Nat.card_zpowers, hr2]
    exact hRcard
  refine ⟨r, hr2, hrM, hRz, ?_, ?_, ?_⟩
  ·
    exact Subgroup.centralizer_le hE₀ (hRC hr)
  ·
    set P := pCoreOf 2 (M ⊓ Subgroup.centralizer {r}) with hPdef
    have hPle : P ≤ M ⊓ Subgroup.centralizer {r} := ggOIGI_pCoreOf_le_self 2 _
    have hP2 : IsPGroup 2 P := ggOIGI_isPGroup_pCoreOf 2 _
    have hPG₀ : P ⊓ G₀ = ⊥ := by
      refine hO2 (P ⊓ G₀) ?_ (hP2.to_le inf_le_left) ?_
      · exact fun x hx => ⟨hx.2, (hPle hx.1).2⟩
      · intro x hx z hz
        refine ⟨ggOIGI_conj_mem_pCoreOf hx.1 ⟨hG₀M hz.1, hz.2⟩, ?_⟩
        exact G₀.mul_mem (G₀.mul_mem hz.1 hx.2) (G₀.inv_mem hz.1)
    have hPcomm : ∀ x ∈ P, ∀ z ∈ G₀ ⊓ Subgroup.centralizer {r}, x * z = z * x := by
      intro x hx z hz
      have hxM : x ∈ M := (hPle hx).1
      have hc : x * z * x⁻¹ * z⁻¹ ∈ P ⊓ G₀ := by
        refine ⟨?_, ?_⟩
        · have h1 : z * x⁻¹ * z⁻¹ ∈ P :=
            ggOIGI_conj_mem_pCoreOf (P.inv_mem hx) ⟨hG₀M hz.1, hz.2⟩
          simpa [mul_assoc] using P.mul_mem hx h1
        · have h2 : x * z * x⁻¹ ∈ G₀ := (Subgroup.mem_normalizer_iff.mp (hnorm hxM) z).mp hz.1
          exact G₀.mul_mem h2 (G₀.inv_mem hz.1)
      rw [hPG₀, Subgroup.mem_bot] at hc
      have := mul_inv_eq_one.mp hc
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    intro x hx
    have hrC : r ∈ M ⊓ Subgroup.centralizer {r} :=
      ⟨hrM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hzr2 : IsPGroup 2 (Subgroup.zpowers r) := by
      apply IsPGroup.of_card
      rw [Nat.card_zpowers, hr2]
      exact (pow_one 2).symm
    have hzN : Subgroup.zpowers r ≤ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact ggOIGI_conj_mem_pCoreOf hy hrC
      · intro hy
        have := ggOIGI_conj_mem_pCoreOf hy (Subgroup.inv_mem _ hrC)
        simpa [mul_assoc] using this
    set Q := P ⊔ Subgroup.zpowers r with hQdef
    have hQ2 : IsPGroup 2 Q := hP2.to_sup_of_normal_left' hzr2 hzN
    have hQM : Q ≤ M := sup_le (hPle.trans inf_le_left) ((Subgroup.zpowers_le).2 hrM)
    have hidx := hOut Q hQM hQ2
    have hxQ : x ∈ Q := le_sup_left (a := P) hx
    have hrQ : r ∈ Q := le_sup_right (a := P) (Subgroup.mem_zpowers r)
    have hrH : (⟨r, hrQ⟩ : Q) ∉ G₀.subgroupOf Q := by
      rw [Subgroup.mem_subgroupOf]
      exact hrG₀
    have hidx2 : (G₀.subgroupOf Q).index = 2 := by
      have hne1 : (G₀.subgroupOf Q).index ≠ 1 := by
        intro h1
        rw [Subgroup.index_eq_one] at h1
        exact hrH (h1 ▸ Subgroup.mem_top _)
      have hne0 : (G₀.subgroupOf Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    by_cases hxG : x ∈ G₀
    · have : x ∈ P ⊓ G₀ := ⟨hx, hxG⟩
      rw [hPG₀, Subgroup.mem_bot] at this
      rw [this]
      exact Subgroup.one_mem _
    ·
      have hxH : (⟨x, hxQ⟩ : Q) ∉ G₀.subgroupOf Q := by
        rw [Subgroup.mem_subgroupOf]
        exact hxG
      have hmul : (⟨x, hxQ⟩ : Q) * (⟨r, hrQ⟩ : Q)⁻¹ ∈ G₀.subgroupOf Q := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx2]
        simp only [inv_mem_iff]
        exact iff_of_false hxH hrH
      rw [Subgroup.mem_subgroupOf] at hmul
      have hg : x * r⁻¹ ∈ G₀ := by simpa using hmul
      have hgC : x * r⁻¹ ∈ Subgroup.centralizer
          ((G₀ ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have h1 : x * z = z * x := hPcomm x hx z hz
        have h2 : z * r = r * z := (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
        have h3 : z * r⁻¹ = r⁻¹ * z := (Commute.inv_right (show Commute z r from h2)).eq
        rw [← mul_assoc, ← h1, mul_assoc, h3, mul_assoc]
      have : x * r⁻¹ ∈ G₀ ⊓ Subgroup.centralizer
          ((G₀ ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) := ⟨hg, hgC⟩
      rw [hCC, Subgroup.mem_bot, mul_inv_eq_one] at this
      rw [this]
      exact Subgroup.mem_zpowers r
  ·
    intro h
    apply hnot2
    exact h.to_le (inf_le_inf_right _ hG₀M)

@[expose] def GGGraphInvInputAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        CFSG.Assembly.IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ∀ r ∈ ggM p B x L D J, orderOf r = 2 → r ∈ Subgroup.centralizer {b} →
          r ∉ ggG0 p B x L D J →
            ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r} →
            (∀ Q : Subgroup G, Q ≤ ggM p B x L D J → IsPGroup 2 Q →
                ((ggG0 p B x L D J).subgroupOf Q).index ≤ 2) ∧
            (∀ N : Subgroup G, N ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {r} → IsPGroup 2 N →
                (∀ y ∈ N, ∀ z ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer {r}, z * y * z⁻¹ ∈ N) →
                N = ⊥) ∧
            ¬ IsPGroup 2 ↥(ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) ∧
            ggG0 p B x L D J ⊓ Subgroup.centralizer
              ((ggG0 p B x L D J ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) = ⊥

theorem ggOuterInvAt_of_graphInv
    {t : StatedLieTag} (hd : GGPsiDiagInnerAt t)
    (h2 : GGO2CentralizerG0At t) (hX : GGGraphInvInputAt t) : GGOuterInvAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC r hr hr2
  have hO2 := h2 G p B Bs x L D J n f ψ hctx s1 b hb hb1
  obtain ⟨hRG₀, hRC⟩ := ggR_inf_ggG0_eq_bot_of_diagInner hd hctx s1 hO2
  have hE₀ := ggE0_le_ggG0_inf_centralizer_of_diagInner hd hctx s1 hm hEC
  have hrM : r ∈ ggM p B x L D J := (ggOIGI_pCoreOf_le_self 2 _ hr).1
  have hrb : r ∈ Subgroup.centralizer {b} := (ggOIGI_pCoreOf_le_self 2 _ hr).2
  have hrG₀ : r ∉ ggG0 p B x L D J := by
    intro h
    have : r ∈ pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓ ggG0 p B x L D J :=
      ⟨hr, h⟩
    rw [hRG₀, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hle : ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer {r} := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hRC hr)) z hz
  obtain ⟨hOut, hO2r, hnot2, hCC⟩ :=
    hX G p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb hrG₀ hle
  exact xi_of_outer_involution Subgroup.le_normalizer
    le_rfl hRG₀ hRC hE₀ hr hr2 hOut hO2r hnot2 hCC

end CFSG.StandardType
