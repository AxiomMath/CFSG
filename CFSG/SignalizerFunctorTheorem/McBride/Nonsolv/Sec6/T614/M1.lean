module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.Free

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem kOf_inf_centralizer_eq_kOf_sup
    (h : Counterexample p A θ) {E' F' : Subgroup G}
    (hE' : E' ∈ signalizerFunctorEk p 1 A) (hF' : F' ∈ signalizerFunctorEk p 1 A)
    (hfree : F' ⊓ bN A θ E' = ⊥) :
    kOf (thetaOf θ E') ⊓ Subgroup.centralizer (F' : Set G) = kOf (thetaOf θ (E' ⊔ F')) := by
  obtain ⟨e, he, he1, hEe⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hE'
  have hE'0 : E' ≠ ⊥ := h.ne_bot_of_mem_E1 hE'
  have hfree' : ∀ J ∈ lcal (thetaOf θ E'), F' ⊓ Subgroup.normalizer (J : Set G) ≤
      Subgroup.centralizer (J : Set G) := by
    intro J hJ
    have hb := h.lemma_6_9_b hE'.1 hE'0 J hJ
    have h1 : F' ⊓ Subgroup.normalizer (J : Set G) ≤ F' ⊓ bN A θ E' := fun x hx =>
      ⟨hx.1, by rw [hb]; exact ⟨hF'.1 hx.1, hx.2⟩⟩
    rw [hfree] at h1
    exact h1.trans bot_le
  have h1 := T613.kOf_inf_centralizer_eq_kOf_of_free (h.kSetting_thetaOf hE'.1 hE'0)
    (h.kDown_thetaOf hE'.1 hE'0) hF'.1 hfree'
  have key : thetaOf θ E' ⊓ Subgroup.centralizer (F' : Set G) = thetaOf θ (E' ⊔ F') := by
    rw [← hEe, h.isFunctor.thetaOf_zpowers he he1]
    exact h.isFunctor.inf_centralizer_eq_thetaOf he he1 hF'.1
  rw [h1, key]

theorem kOf_apply_inf_centralizer_eq
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥) {e f : G}
    (he : e ∈ B) (hf : f ∈ B) (he1 : e ≠ 1) (hf1 : f ≠ 1) (hef : f ∉ Subgroup.zpowers e) :
    kOf (θ e) ⊓ Subgroup.centralizer {f} =
      kOf (thetaOf θ (Subgroup.zpowers e ⊔ Subgroup.zpowers f)) := by
  have hEe := h.zpowers_mem_E1 (hB.1 he) he1
  have hFf := h.zpowers_mem_E1 (hB.1 hf) hf1
  have hfree : Subgroup.zpowers f ⊓ bN A θ (Subgroup.zpowers e) = ⊥ := by
    rw [S.bN_eq _ hEe, inf_comm]
    refine inf_eq_bot_of_not_le h.prime (hFf.2.trans (pow_one p)) ?_
    intro hle
    have hmem : f ∈ B ⊓ (Subgroup.zpowers e ⊔ E) := ⟨hf, hle (Subgroup.mem_zpowers f)⟩
    rw [h.inf_sup_eq_of_le S.mem.1 hB.1 hEB (Subgroup.zpowers_le.mpr he)] at hmem
    exact hef hmem
  have := h.kOf_inf_centralizer_eq_kOf_sup hEe hFf hfree
  rw [h.isFunctor.thetaOf_zpowers (hB.1 he) he1, centralizer_zpowers_eq_singleton] at this
  exact this

theorem kOf_thetaOf_inf_centralizer_eq
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {b : G} (hb : b ∈ A) (hbE : b ∉ E) :
    kOf (thetaOf θ E) ⊓ Subgroup.centralizer {b} =
      kOf (thetaOf θ (E ⊔ Subgroup.zpowers b)) := by
  have hb1 : b ≠ 1 := fun e => hbE (e ▸ E.one_mem)
  have hFb := h.zpowers_mem_E1 hb hb1
  have hfree : Subgroup.zpowers b ⊓ bN A θ E = ⊥ := by
    rw [S.bN_eq _ S.mem, sup_idem, inf_comm]
    exact inf_eq_bot_of_not_le h.prime (hFb.2.trans (pow_one p)) fun hle =>
      hbE (hle (Subgroup.mem_zpowers b))
  have := h.kOf_inf_centralizer_eq_kOf_sup S.mem hFb hfree
  rwa [centralizer_zpowers_eq_singleton] at this

theorem kOf_thetaOf_sup_le
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {E' : Subgroup G} (hE' : E' ≤ A) :
    kOf (thetaOf θ (Subgroup.zpowers a ⊔ E')) ≤ kOf (θ a) ⊓ Subgroup.centralizer (E' : Set G) := by
  rw [← h.isFunctor.inf_centralizer_eq_thetaOf ha ha1 hE']
  exact T515f.kOf_inf_centralizer_le_kOf (h.kSetting_apply ha ha1) (h.kDown_apply ha ha1) hE'

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
