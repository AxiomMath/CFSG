module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Setting

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_zpowers_symm (h : Counterexample p A θ) {a b : G} (hb : b ∈ A)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ∈ Subgroup.zpowers b) : b ∈ Subgroup.zpowers a := by
  have := h.line_eq_zpowers (h.zpowers_mem_E1 hb hb1) hab ha1
  rw [← this]
  exact Subgroup.mem_zpowers b

theorem apply_le_of_not_le
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) {a b : G} (ha : a ∈ A) (hb : b ∈ A) (hbE : b ∉ E)
    (haN : a ∉ Subgroup.zpowers b ⊔ E) {X : Subgroup G} (hX : X ∈ Msig p A θ)
    (haX : θ a ≤ X) (hnle : ¬ X ⊓ Subgroup.centralizer {b} ≤ θ a) : θ b ≤ X := by
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ E.one_mem)
  have ha1 : a ≠ 1 := fun h1 => haN (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hD, hN⟩ := h.diagSetting_apply core hb hbE
  have hAY : A ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
    have := (inf_centralizer_mem_signalizers hX (B := Subgroup.zpowers b)
      (Subgroup.zpowers_le.mpr hb) h.elemAbelian.1
      (fun _ hYX _ hP => hypB_mono hYX hP)).1
    rwa [centralizer_zpowers_eq_singleton] at this
  have hYθ : X ⊓ Subgroup.centralizer {b} ≤ θ b := hX.2.2.1 b hb hb1
  have hbal : θ b ⊓ Subgroup.centralizer {a} ≤ θ a := h.isFunctor.balance b hb hb1 a ha ha1
  have hθY : θ b ⊓ Subgroup.centralizer {a} ≤ X ⊓ Subgroup.centralizer {b} := fun u hu =>
    Subgroup.mem_inf.mpr ⟨haX (hbal hu),
      h.isFunctor.le_centralizer b hb hb1 (Subgroup.mem_inf.mp hu).1⟩
  rcases hD.eq_or_eq_top hN ha haN hYθ hθY hAY with heq | heq
  · exact absurd (by rw [heq]; exact hbal) hnle
  · rw [← heq]
    exact inf_le_left

theorem kOf_inf_centralizer_le (h : Counterexample p A θ) {E : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) :
    kOf (thetaOf θ E) ⊓ Subgroup.centralizer {x} ≤ θ x := by
  intro u hu
  obtain ⟨e, he, he1⟩ := h.exists_ne_one_of_mem_E1 hE
  obtain ⟨huK, huC⟩ := Subgroup.mem_inf.mp hu
  exact h.isFunctor.balance e (hE.1 he) he1 x hx hx1
    (Subgroup.mem_inf.mpr ⟨thetaOf_le_apply he he1 (kOf_le _ huK), huC⟩)

theorem kOf_thetaOf_le
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) {a b : G} (ha : a ∈ A) (hb : b ∈ A) (haE : a ∉ E)
    (hbE : b ∉ E) (hab : (Subgroup.zpowers a ⊔ E) ⊓ (Subgroup.zpowers b ⊔ E) = E)
    {X : Subgroup G} (haX : θ a ≤ X) (hbX : θ b ≤ X) : kOf (thetaOf θ E) ≤ X := by
  have ha1 : a ≠ 1 := fun h1 => haE (h1 ▸ E.one_mem)
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ E.one_mem)
  obtain ⟨hD, hN⟩ := h.diagSetting_kOf_E core
  rw [← hD.sup_eq_top hN ha hb haE hbE hab]
  exact sup_le ((h.kOf_inf_centralizer_le core.mem ha ha1).trans haX)
    ((h.kOf_inf_centralizer_le core.mem hb hb1).trans hbX)

theorem apply_le_of_kOf_le
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) {f a' : G} (hf : f ∈ A) (ha' : a' ∈ A) (hfE : f ∉ E)
    (ha'E : a' ∉ E) (ha'f : a' ∉ Subgroup.zpowers f ⊔ E)
    (hfa : (Subgroup.zpowers f ⊔ E) ⊓ (Subgroup.zpowers a' ⊔ E) = E) {X : Subgroup G}
    (hX₁ : θ f ⊓ Subgroup.centralizer {a'} ≤ X) (hX₂ : kOf (thetaOf θ E) ≤ X) : θ f ≤ X := by
  have hf1 : f ≠ 1 := fun h1 => hfE (h1 ▸ E.one_mem)
  have ha'1 : a' ≠ 1 := fun h1 => ha'E (h1 ▸ E.one_mem)
  obtain ⟨hD, hN⟩ := h.diagSetting_apply core hf hfE
  obtain ⟨hDE, hNE⟩ := h.diagSetting_kOf_E core
  have hAY : A ≤ Subgroup.normalizer
      (((θ f ⊓ Subgroup.centralizer {a'}) ⊔ (kOf (thetaOf θ E) ⊓ θ f) : Subgroup G) : Set G) := by
    intro g hg
    refine L69.mem_normalizer_sup (L514.mem_normalizer_inf ?_ ?_)
      (L514.mem_normalizer_inf (hDE.normalizes hg) ?_)
    · exact h.isFunctor.normalized f hf hf1 hg
    · exact mem_normalizer_centralizer_singleton
        (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_of_mem_A hg ha'))
    · exact h.isFunctor.normalized f hf hf1 hg
  rcases hD.eq_or_eq_top hN ha' ha'f
      (sup_le inf_le_left inf_le_right) le_sup_left hAY with heq | heq
  · exfalso
    have hle : kOf (thetaOf θ E) ⊓ Subgroup.centralizer {f} ≤ Subgroup.centralizer {a'} := by
      intro u hu
      have hu' : u ∈ kOf (thetaOf θ E) ⊓ θ f :=
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu).1,
          h.kOf_inf_centralizer_le core.mem hf hf1 hu⟩
      have : u ∈ θ f ⊓ Subgroup.centralizer {a'} := by
        rw [← heq]
        exact Subgroup.mem_sup_right hu'
      exact (Subgroup.mem_inf.mp this).2
    have hsup := hDE.sup_eq_top hNE hf ha' hfE ha'E hfa
    have hKle : kOf (thetaOf θ E) ≤ Subgroup.centralizer {a'} := by
      rw [← hsup]
      exact sup_le hle inf_le_right
    obtain ⟨J, hJ⟩ := hDE.nonempty
    have hJK : J ≤ kOf (thetaOf θ E) := lcal_le hJ
    have hcen : a' ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKle (hJK hy))
    have : a' ∈ A ⊓ Subgroup.normalizer (J : Set G) :=
      Subgroup.mem_inf.mpr ⟨ha', Subgroup.centralizer_le_normalizer _ hcen⟩
    rw [← hNE J hJ] at this
    exact ha'E this
  · rw [← heq]
    exact sup_le hX₁ (inf_le_left.trans hX₂)

theorem le_apply_of_apply_le
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) {a : G} (ha : a ∈ A) (haE : a ∉ E) {X : Subgroup G}
    (hX : X ∈ Msig p A θ) (haX : θ a ≤ X) : X ≤ θ a := by
  by_contra hXa
  have ha1 : a ≠ 1 := fun h1 => haE (h1 ▸ E.one_mem)
  obtain ⟨B, hBA, haB', hEB, hsup, hBcard⟩ := h.exists_complement_of_not_mem core.mem ha haE
  have haB : a ∈ B := haB' (Subgroup.mem_zpowers a)
  have hBrank : p ^ 2 ≤ Nat.card B := hBcard.ge
  have hgen := iSup_inf_centralizer h.prime (h.isElemAbelian_of_le hBA) hBrank
    (hBA.trans hX.1) hX.2.1
  obtain ⟨b, hbB, hb1, hnle⟩ : ∃ b ∈ B, b ≠ 1 ∧ ¬ X ⊓ Subgroup.centralizer {b} ≤ θ a := by
    by_contra! hcon
    exact hXa (hgen.symm.le.trans
      (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => hcon b hb hb1))
  have hbE : b ∉ E := not_mem_of_mem_complement hEB hbB hb1
  have hba : b ∉ Subgroup.zpowers a := by
    intro hb
    refine hnle ?_
    have hline := h.line_eq_zpowers (h.zpowers_mem_E1 ha ha1) hb hb1
    have hθ : θ b = θ a := h.isFunctor.eq_of_zpowers_eq (hBA hbB) hb1 ha ha1 hline.symm
    exact hθ ▸ hX.2.2.1 b (hBA hbB) hb1
  have hab : a ∉ Subgroup.zpowers b := fun hab' => hba (h.mem_zpowers_symm (hBA hbB) ha1 hb1 hab')
  have haN : a ∉ Subgroup.zpowers b ⊔ E :=
    h.not_mem_zpowers_sup_of_mem_complement core.mem hBA hEB hsup hbB hb1 haB hab
  have hbX : θ b ≤ X := h.apply_le_of_not_le core ha (hBA hbB) hbE haN hX haX hnle
  have hKX : kOf (thetaOf θ E) ≤ X :=
    h.kOf_thetaOf_le core ha (hBA hbB) haE hbE
      (h.sup_zpowers_inf_sup_zpowers core.mem hBA hEB hsup haB ha1 hbB hb1 hba) haX hbX
  have hall : ∀ f ∈ B, f ≠ 1 → θ f ≤ X := by
    intro f hfB hf1
    obtain ⟨a', ha'B, ha'f⟩ := h.exists_mem_complement_not_mem_zpowers hBA hBcard hfB hf1
    have ha'1 : a' ≠ 1 := fun h1 => ha'f (h1 ▸ Subgroup.one_mem _)
    have hfE : f ∉ E := not_mem_of_mem_complement hEB hfB hf1
    have ha'E : a' ∉ E := not_mem_of_mem_complement hEB ha'B ha'1
    have hsupB := h.zpowers_sup_eq_of_mem_complement hBA hBcard hfB hf1 ha'B ha'f
    have hX₁ : θ f ⊓ Subgroup.centralizer {a'} ≤ X := by
      rw [← centralizer_zpowers_eq_singleton,
        h.isFunctor.inf_centralizer_eq_thetaOf (hBA hfB) hf1 (Subgroup.zpowers_le.mpr (hBA ha'B)),
        hsupB]
      exact (thetaOf_le_apply haB ha1).trans haX
    exact h.apply_le_of_kOf_le core (hBA hfB) (hBA ha'B) hfE ha'E
      (h.not_mem_zpowers_sup_of_mem_complement core.mem hBA hEB hsup hfB hf1 ha'B ha'f)
      (h.sup_zpowers_inf_sup_zpowers core.mem hBA hEB hsup hfB hf1 ha'B ha'1 ha'f) hX₁ hKX
  obtain ⟨f, hfB, hf1, hfX⟩ := exists_apply_not_le_of_mem h.prime h.elemAbelian h.notComplete
    hBA hBrank hX
  exact hfX (hall f hfB hf1)

theorem maximal_of_core
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) :
    ∀ a ∈ A, a ∉ E → Maximal (· ∈ Msig p A θ) (thetaOf θ (Subgroup.zpowers a)) := by
  intro a ha haE
  have ha1 : a ≠ 1 := fun h1 => haE (h1 ▸ E.one_mem)
  rw [h.isFunctor.thetaOf_zpowers ha ha1]
  exact ⟨h.apply_mem_msig ha ha1, fun X hX haX => h.le_apply_of_apply_le core ha haE hX haX⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
