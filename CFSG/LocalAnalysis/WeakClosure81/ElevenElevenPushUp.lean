module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenIndex
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenTransvComm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_lemmaK {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {N : Subgroup G} (hNQ : N ≤ Q)
    (hN : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hND : ¬ N ≤ centralizerModCore L) :
    ∃ t ∈ L ⊓ Q, t ∉ oTwoIn L ∧ ⁅Subgroup.zpowers t, blockU L⁆ ≤ N := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have h78 : IsLTwoBlockType L 2 := (eleven11_blockType_two hd h8).1
  obtain ⟨n, hnN, hnD⟩ := SetLike.not_le_iff_exists.1 hND
  obtain ⟨t, ht, d, hdD, hnt⟩ := eleven_nine_two hd.setting hUΓ hLb hLM h78 n (hNQ hnN)
  have ht0 : t ∉ oTwoIn L := by
    intro h
    exact hnD (hnt ▸ mul_mem (Glue.oTwoIn_le_centralizerModCore L h) (Subgroup.mem_inf.1 hdD).2)
  have hdC : d ∈ Subgroup.centralizer (blockU L : Set G) := by
    have h : d ∈ Q ⊓ Subgroup.centralizer (blockU L : Set G) := by
      rw [eleven11_cent_blockU_eq hd h8]
      exact hdD
    exact (Subgroup.mem_inf.1 h).2
  refine ⟨t, ht, ht0, fun r hr => ?_⟩
  obtain ⟨w, hw, rfl⟩ := (eleven11_mem_commutator_zpowers_iff hd h8 ht).1 hr
  have hwQ : w ∈ Q := eleven11_blockU_le_Q hd hw
  have hdw : w * d = d * w := Subgroup.mem_centralizer_iff.1 hdC w hw
  have h1 : t * w * t⁻¹ * w⁻¹ = n * (w * n⁻¹ * w⁻¹) := by
    rw [hnt]
    have : d * w * d⁻¹ = w := by rw [← hdw]; group
    calc t * w * t⁻¹ * w⁻¹ = t * (d * w * d⁻¹) * t⁻¹ * w⁻¹ := by rw [this]
      _ = t * d * (w * (t * d)⁻¹ * w⁻¹) := by group
  rw [h1]
  exact N.mul_mem hnN (hN w hwQ n⁻¹ (N.inv_mem hnN))

theorem eleven11_exists_conj_blockU {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∃ x ∈ Subgroup.normalizer (Q : Set G), ¬ MulAut.conj x • blockU L ≤ centralizerModCore L := by
  by_contra hcon
  have hcon' : ∀ x ∈ Subgroup.normalizer (Q : Set G),
      MulAut.conj x • blockU L ≤ centralizerModCore L := fun x hx => by
    by_contra h
    exact hcon ⟨x, hx, h⟩
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let F : N → Subgroup G := fun x => MulAut.conj (x : G) • blockU L
  let U₀ : Subgroup G := ⨆ x : N, F x
  have hF : ∀ x : N, F x ≤ U₀ := fun x => le_iSup F x
  have hmemF : ∀ (x : N) (g : G), g ∈ F x ↔ ∃ w ∈ blockU L, (x : G) * w * (x : G)⁻¹ = g := by
    intro x g
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply]
  have hW : blockU L ≤ U₀ := by
    intro w hw
    refine hF 1 ((hmemF 1 w).2 ⟨w, hw, by simp⟩)
  have hFQ : ∀ x : N, F x ≤ Q := by
    intro x g hg
    obtain ⟨w, hw, rfl⟩ := (hmemF x g).1 hg
    have hxN : (x : G) ∈ Subgroup.normalizer (Q : Set G) := x.2
    exact (Subgroup.mem_normalizer_iff.1 hxN w).1 (eleven11_blockU_le_Q hd hw)
  have hU₀D : U₀ ≤ Q ⊓ centralizerModCore L :=
    iSup_le fun x => le_inf (hFQ x) (hcon' x x.2)
  have hconjU : ∀ y ∈ N, ∀ u ∈ U₀, y * u * y⁻¹ ∈ U₀ := by
    intro y hy u hu
    refine Subgroup.iSup_induction F (C := fun u => y * u * y⁻¹ ∈ U₀) hu ?_ ?_ ?_
    · intro x g hg
      obtain ⟨w, hw, rfl⟩ := (hmemF x g).1 hg
      refine hF (⟨y, hy⟩ * x) ((hmemF _ _).2 ⟨w, hw, ?_⟩)
      simp only [Subgroup.coe_mul]
      group
    · simpa using U₀.one_mem
    · intro a b ha hb
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact U₀.mul_mem ha hb
  have hNU : Subgroup.normalizer (Q : Set G) ⊓ M ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro y hy
    have hyN : y ∈ N := (Subgroup.mem_inf.1 hy).1
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hconjU y hyN u, fun hu => ?_⟩
    have := hconjU y⁻¹ (N.inv_mem hyN) _ hu
    simpa [mul_assoc] using this
  have hLU : L ≤ Subgroup.normalizer (U₀ : Set G) := by
    have hcl : ∀ l ∈ L, ∀ u ∈ U₀, l * u * l⁻¹ ∈ U₀ := by
      intro l hl u hu
      have hc := eleven11_comm_D_le hd u (hU₀D hu) l hl
      have h2 : l * u * l⁻¹ = (u * l * u⁻¹ * l⁻¹)⁻¹ * u := by group
      rw [h2]
      exact U₀.mul_mem (U₀.inv_mem (hW hc)) hu
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hcl l hl u, fun hu => ?_⟩
    have := hcl l⁻¹ (L.inv_mem hl) _ hu
    simpa [mul_assoc] using this
  have hU0ne : U₀ ≠ ⊥ := fun h =>
    CFSG.CGT.PushingUpLit.blockU_ne_bot_of_short hLb.2.2.1 (le_bot_iff.1 (h ▸ hW))
  have hU02 : IsPGroup 2 U₀ := hd.setting.sylowQ.2.1.to_le (hU₀D.trans inf_le_left)
  have hNM := eleven_b hd.setting.uniqueMax hU0ne hU02 hNU
  exact hLM (hLU.trans hNM)

theorem eleven11_conj_not_le_centralizer {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G))
    (hxD : ¬ MulAut.conj x • blockU L ≤ centralizerModCore L) :
    ¬ MulAut.conj x • blockU L ≤ Subgroup.centralizer (blockU L : Set G) := by
  intro h
  apply hxD
  have hQ := ((eleven11_transvPair hd h8).conj hx).le
  have h1 : MulAut.conj x • blockU L ≤ Q ⊓ Subgroup.centralizer (blockU L : Set G) :=
    le_inf hQ h
  rw [eleven11_cent_blockU_eq hd h8] at h1
  exact h1.trans inf_le_right

end CFSG.LocalAnalysis.WeakClosure81
