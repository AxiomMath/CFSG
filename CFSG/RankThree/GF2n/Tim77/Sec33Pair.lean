module

public import CFSG.RankThree.GF2n.Tim77.Sec33Bender
public import CFSG.RankThree.GF2n.Tim77Prop24
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n Subgroup CFSG.CGT.Timmesfeld75

section PairData

variable {G : Type} [Group G] [Finite G]


theorem sec33_pair_partner {A₁ A₂ L₁ L₂ M₁ : Subgroup G} (S : Prop24Setup A₁ A₂ L₁ L₂ M₁)
    (hq : 2 < L₁.relIndex A₁) {Y : Subgroup G} (hA₁ : A₁ ≤ Y) (hA₂ : A₂ ≤ Y) {K : Type}
    [Group K] [Finite K] {n i : ℕ} (hK : BenderType K n i 1) (hi : i = 1 ∨ i = 2)
    (ψ : ↥Y →* K)
    (hψM : ∀ (m : G) (hm : m ∈ M₁), ψ ⟨m, (S.M_le_X.trans (sup_le hA₁ hA₂)) hm⟩ = 1)
    (hψA : ∃ (a₀ : G) (h : a₀ ∈ A₁), ψ ⟨a₀, hA₁ h⟩ ≠ 1) :
    ∀ (x : G) (hx : x ∈ A₂), ψ ⟨x, hA₂ hx⟩ ≠ 1 →
      ∃ (a : G) (ha : a ∈ A₁), ψ ⟨a, hA₁ ha⟩ ≠ 1 ∧ ψ ⟨a, hA₁ ha⟩ ≠ ψ ⟨x, hA₂ hx⟩ ∧
        (ψ ⟨a, hA₁ ha⟩ * ψ ⟨x, hA₂ hx⟩) ^ (2 * i + 1) = 1 := by
  classical
  have hXY : A₁ ⊔ A₂ ≤ Y := sup_le hA₁ hA₂
  obtain ⟨hN2, hO2, hmod⟩ := S.tim77_2_4_one CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  haveI := hN2
  have hJ : ∃ (f j : ℕ), (j = 1 ∨ j = 2) ∧
      BenderType (↥(A₁ ⊔ A₂) ⧸ M₁.subgroupOf (A₁ ⊔ A₂)) f j 1 := by
    rcases hmod with ⟨f, hf, hrel, ⟨e⟩⟩ | ⟨a, ha, hrel, ⟨e⟩⟩ | ⟨m, hm, h3, hrel, -⟩
    · exact ⟨f, 1, Or.inl rfl, .linear f hf e⟩
    · have e' := e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)
      exact ⟨2 * a + 1, 2, Or.inr rfl, .suzuki a ha e'⟩
    · rw [hrel] at hq
      exact absurd hq (by norm_num)
  obtain ⟨f, j, hj, hJ⟩ := hJ
  let πq : ↥(A₁ ⊔ A₂) →* ↥(A₁ ⊔ A₂) ⧸ M₁.subgroupOf (A₁ ⊔ A₂) :=
    QuotientGroup.mk' (M₁.subgroupOf (A₁ ⊔ A₂))
  have hS := S.strongWC_image
  have hT0 := S.image_ne_bot
  obtain ⟨Q, hQ⟩ := eq_rootCenter_of_strongWC hJ hS hT0
  obtain ⟨x₀, hx₀⟩ := S.exists_image_conj
  have hS' : StrongWC ((A₂.subgroupOf (A₁ ⊔ A₂)).map πq) := by
    rw [hx₀]; exact StrongWC.conj hS _
  have hT0' : (A₂.subgroupOf (A₁ ⊔ A₂)).map πq ≠ ⊥ := by
    rw [hx₀]
    intro hbot
    apply hT0
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (πq x₀)).injective).mp hbot
  obtain ⟨Q', hQ'⟩ := eq_rootCenter_of_strongWC hJ hS' hT0'
  have hQQ : Q ≠ Q' := by
    intro heq
    obtain ⟨b₀, hb₀, hb₀L⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
    apply S.mk_not_mem_image hb₀ hb₀L
    have h2 : πq ⟨b₀, Subgroup.mem_sup_right hb₀⟩ ∈ (A₂.subgroupOf (A₁ ⊔ A₂)).map πq :=
      ⟨_, hb₀, rfl⟩
    rw [hQ', ← heq, ← hQ] at h2
    exact h2
  let φ : (↥(A₁ ⊔ A₂) ⧸ M₁.subgroupOf (A₁ ⊔ A₂)) →* K :=
    QuotientGroup.lift (M₁.subgroupOf (A₁ ⊔ A₂)) (ψ.comp (Subgroup.inclusion hXY)) (by
      intro m hm
      rw [MonoidHom.mem_ker]
      exact hψM (m : G) hm)
  have hφmk : ∀ y : ↥(A₁ ⊔ A₂), φ (πq y) = ψ (Subgroup.inclusion hXY y) := fun y => rfl
  have hφinj : Function.Injective φ := by
    haveI := hJ.isSimple
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a₀, ha₀, ha₀1⟩ := hψA
      apply ha₀1
      have : πq ⟨a₀, Subgroup.mem_sup_left ha₀⟩ ∈ φ.ker := by rw [h1]; trivial
      exact this
  have hji : j = i := sec33_type_match hJ hK hj hi φ hφinj
  intro x hx hψx
  have hxX : x ∈ A₁ ⊔ A₂ := Subgroup.mem_sup_right hx
  have hxJT : πq ⟨x, hxX⟩ ∈ rootCenter (Q' : Subgroup _) := by
    rw [← hQ']
    exact ⟨_, hx, rfl⟩
  have hxJ1 : πq ⟨x, hxX⟩ ≠ 1 := fun h1 =>
    hψx ((hφmk ⟨x, hxX⟩).symm.trans (by rw [h1, map_one]))
  obtain ⟨aJ, haJR, haJ1, haJp⟩ := sec33_bender_partner_exists hJ hj hQQ hxJT hxJ1
  rw [← hQ] at haJR
  obtain ⟨a', ha', rfl⟩ := haJR
  have ha'A : (a' : G) ∈ A₁ := ha'
  refine ⟨(a' : G), ha'A, ?_, ?_, ?_⟩
  · intro h1
    apply haJ1
    apply hφinj
    rw [map_one]
    exact h1
  · intro h1
    have h2 : πq a' = πq ⟨x, hxX⟩ := hφinj h1
    have hR : πq a' ∈ rootCenter (Q : Subgroup _) := by
      rw [← hQ]; exact ⟨a', ha', rfl⟩
    have hR' : πq a' ∈ rootCenter (Q' : Subgroup _) := by rw [h2]; exact hxJT
    obtain ⟨tJ, hcJ⟩ := hJ.exists_benderCore Q
    apply hQQ
    refine (hcJ.sylow_eq_of_ne_bot (V := zpowers (πq a')) ?_ ?_ ?_).symm
    · intro hbot
      apply haJ1
      have : πq a' ∈ (⊥ : Subgroup _) := hbot ▸ Subgroup.mem_zpowers _
      exact Subgroup.mem_bot.mp this
    · exact Subgroup.zpowers_le.mpr (rootCenter_le _ hR)
    · exact Subgroup.zpowers_le.mpr (rootCenter_le _ hR')
  · have := congrArg φ haJp
    rw [map_pow, map_mul, map_one, hji] at this
    exact this

end PairData

end CFSG.RankThree.GF2n.Tim77
