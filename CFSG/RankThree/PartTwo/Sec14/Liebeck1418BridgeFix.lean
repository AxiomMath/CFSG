module

public import CFSG.RankThree.PartTwo.Sec14.Wales1418Off
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec10.Item1012Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late

theorem commutator_le_normalizer_of_forall {G : Type*} [Group G] {𝓢 : Set (Subgroup G)}
    {R : Subgroup G} {b : G}
    (hR : ∀ J ∈ 𝓢, ∀ r ∈ R, J.map (MulAut.conj r).toMonoidHom ∈ 𝓢)
    (hb : ∀ J ∈ 𝓢, b ∈ Subgroup.normalizer (J : Set G)) :
    ∀ J ∈ 𝓢, ⁅R, Subgroup.zpowers b⁆ ≤ Subgroup.normalizer (J : Set G) := by
  intro J hJ
  rw [Subgroup.commutator_le]
  intro r hr x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  set J' := J.map (MulAut.conj r⁻¹).toMonoidHom with hJ'
  have hJ'𝓢 : J' ∈ 𝓢 := hR J hJ r⁻¹ (inv_mem hr)
  have hbk : b ^ k ∈ Subgroup.normalizer (J' : Set G) := zpow_mem (hb J' hJ'𝓢) k
  have hbkJ : b ^ k ∈ Subgroup.normalizer (J : Set G) := zpow_mem (hb J hJ) k
  have hmemJ' : ∀ y : G, y ∈ J' ↔ r * y * r⁻¹ ∈ J := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have e : r * ((MulAut.conj r⁻¹).toMonoidHom x) * r⁻¹ = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hx
    · intro hy
      refine ⟨r * y * r⁻¹, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hconj : r * b ^ k * r⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := hmemJ' (r⁻¹ * y * r)
    have h2 := Subgroup.mem_normalizer_iff.mp hbk (r⁻¹ * y * r)
    have h3 := hmemJ' (b ^ k * (r⁻¹ * y * r) * (b ^ k)⁻¹)
    have e1 : r * (r⁻¹ * y * r) * r⁻¹ = y := by group
    have e2 : r * (b ^ k * (r⁻¹ * y * r) * (b ^ k)⁻¹) * r⁻¹ =
        r * b ^ k * r⁻¹ * y * (r * b ^ k * r⁻¹)⁻¹ := by group
    rw [e1] at h1
    rw [e2] at h3
    rw [← h1, h2, h3]
  rw [commutatorElement_def]
  exact mul_mem hconj (inv_mem hbkJ)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L S B : Subgroup G} {b : G}
  {E R : Subgroup G}

theorem off_centralizer_ne_top (h : Off1418 G A c L S B b E R) :
    Subgroup.centralizer (E : Set G) ≠ ⊤ := by
  have hTF := h.sec15R.toPartTwoStanding.toTheoremFourHyp
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hno
    push Not at hno
    have hEbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hno
    have := h.card_E
    rw [hEbot, Subgroup.card_bot] at this
    norm_num at this
  intro htop
  apply Sec6.centralizer_ne_top_of_ne_one hTF he1
  rw [eq_top_iff, ← htop]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heE)

theorem off_sectionFourHyp_centralizer (h : Off1418 G A c L S B b E R) :
    SectionFourHyp (Subgroup.centralizer (E : Set G)) :=
  h.sec15R.toPartTwoStanding.toTheoremFourHyp.sectionFourHyp (off_centralizer_ne_top h)

theorem off_le_centralizer_E (h : Off1418 G A c L S B b E R) :
    A ≤ Subgroup.centralizer (E : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact congrArg Subtype.val
    (h.isE27.1.1.is_comm.comm ⟨e, h.hyperplane_E.1 he⟩ ⟨a, ha⟩)

theorem off_le_normalizer_of_mem_thetaComponentsIn (h : Off1418 G A c L S B b E R)
    (h45 : Sec4.Item4_5) :
    ∀ J ∈ thetaComponentsIn (Subgroup.centralizer (E : Set G)),
      A ≤ Subgroup.normalizer (J : Set G) ∧ R ≤ Subgroup.normalizer (J : Set G) := by
  have hA := h.isE27
  have hAJ : ∀ J ∈ thetaComponentsIn (Subgroup.centralizer (E : Set G)),
      A ≤ Subgroup.normalizer (J : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 (off_sectionFourHyp_centralizer h)
      (off_le_centralizer_E h) hA.1 ⟨3, le_rfl, by rw [hA.2]; norm_num⟩
  have hRJ := commutator_le_normalizer_of_forall (𝓢 := thetaComponentsIn
      (Subgroup.centralizer (E : Set G))) (R := R) (b := b)
    (fun J hJ r hr => Sec10.Item1012Res2Proof.conj_mem_thetaComponentsIn hJ (h.R_le hr))
    (fun J hJ => hAJ J hJ h.b_mem_A)
  intro J hJ
  refine ⟨hAJ J hJ, ?_⟩
  have := hRJ J hJ
  rwa [h.R_comm] at this

end CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge
