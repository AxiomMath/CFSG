module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeJ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeQ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {W : Type} [CommGroup W] [Finite W]

private theorem s15_Three_blocks_map {A : Subgroup (MulAut W)} {R₁ X : Subgroup W}
    {a : MulAut W} (ha : a ∈ A) (hX : X ∈ s15Blocks A R₁) :
    X.map a.toMonoidHom ∈ s15Blocks A R₁ := by
  obtain ⟨b, hb, rfl⟩ := hX
  refine ⟨a * b, A.mul_mem ha hb, ?_⟩
  rw [Subgroup.map_map]
  exact congrArg (fun f : W →* W => Subgroup.map f R₁) (MonoidHom.ext fun w => rfl)

private theorem s15_Three_tconj_fix {A : Subgroup (MulAut W)} {t a : MulAut W} {R₁ : Subgroup W}
    (ha : a ∈ A) (hfix : ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t))
    {X : Subgroup W} (hX : X ∈ s15Blocks A R₁) (haX : X.map a.toMonoidHom ≠ R₁) :
    ∀ x ∈ X, (a⁻¹ * t * a) x = x := by
  intro x hx
  have hX' : X.map a.toMonoidHom ∈ s15Blocks A R₁ := s15_Three_blocks_map ha hX
  have hmem : a x ∈ X.map a.toMonoidHom := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hta : t (a x) = a x :=
    (mem_fixV.1 ((hfix _ hX' haX) hmem)) t (Subgroup.mem_zpowers t)
  simp [MulAut.mul_apply, MulAut.inv_apply, hta]

private theorem s15_Three_stab_iff {R₁ : Subgroup W} {a : MulAut W}
    (hR₁ : R₁.map a.toMonoidHom = R₁) : R₁.map (a⁻¹).toMonoidHom = R₁ := by
  have hcomp : (a⁻¹).toMonoidHom.comp a.toMonoidHom = MonoidHom.id W := by
    ext w
    simp [MulAut.inv_apply]
  have h := congrArg (Subgroup.map (a⁻¹).toMonoidHom) hR₁
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
  exact h.symm

private theorem s15_Three_sSup_blocks_of_stab {A : Subgroup (MulAut W)} {R₁ : Subgroup W}
    (h : ∀ a ∈ A, R₁.map a.toMonoidHom = R₁) : sSup (s15Blocks A R₁) = R₁ := by
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext w; rfl
  have hset : s15Blocks A R₁ = {R₁} := by
    ext X
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact h a ha
    · rintro rfl
      exact ⟨1, A.one_mem, by rw [hone, Subgroup.map_id]⟩
  rw [hset, sSup_singleton]

theorem s15_Three_J_split {A : Subgroup (MulAut W)} {t : MulAut W} {R S R₁ : Subgroup W}
    (hRS' : R ⊔ S = ⊤) (hSfix : S ≤ fixV (s15TGroup A t))
    (hJ : IsIrrOn (s15TGroup A t) R₁ ⊥) (hsup : sSup (s15Blocks A R₁) = R)
    (hfix : ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t)) :
    ∃ J₁ K : Subgroup (MulAut W), J₁ ≤ s15TGroup A t ∧ K ≤ s15TGroup A t ∧
      (K.subgroupOf (s15TGroup A t)).Normal ∧ J₁ ⊓ K = ⊥ ∧ J₁ ⊔ K = s15TGroup A t ∧
      t ∈ J₁ ∧ ∀ a ∈ A, R₁.map a.toMonoidHom ≠ R₁ → a⁻¹ * t * a ∈ K := by
  set J₁ : Subgroup (MulAut W) :=
    Subgroup.closure {x | ∃ a ∈ A, R₁.map a.toMonoidHom = R₁ ∧ x = a⁻¹ * t * a} with hJ₁def
  set K : Subgroup (MulAut W) := s15TGroup A t ⊓ centSub R₁ with hKdef
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext w; rfl
  have hR₁mem : R₁ ∈ s15Blocks A R₁ := ⟨1, A.one_mem, by rw [hone, Subgroup.map_id]⟩
  have hJ₁J : J₁ ≤ s15TGroup A t := by
    rw [hJ₁def, Subgroup.closure_le]
    rintro g ⟨a, ha, -, rfl⟩
    exact Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hKJ : K ≤ s15TGroup A t := by rw [hKdef]; exact inf_le_left
  have hKn : (K.subgroupOf (s15TGroup A t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKJ]
    intro y j hy hj
    have hy' : y ∈ s15TGroup A t ⊓ centSub R₁ := by rw [← hKdef]; exact hy
    change j * y * j⁻¹ ∈ s15TGroup A t ⊓ centSub R₁
    refine ⟨(s15TGroup A t).mul_mem ((s15TGroup A t).mul_mem hj hy'.1)
      ((s15TGroup A t).inv_mem hj), ?_⟩
    intro u hu
    have hjinv : j⁻¹ u ∈ R₁ := hJ.2.1 j⁻¹ ((s15TGroup A t).inv_mem hj) u hu
    have hyu : y (j⁻¹ u) = j⁻¹ u := (mem_centSub.1 hy'.2) (j⁻¹ u) hjinv
    calc (j * y * j⁻¹) u = j (y (j⁻¹ u)) := rfl
      _ = j (j⁻¹ u) := by rw [hyu]
      _ = u := by simp [MulAut.inv_apply]
  have hmove : ∀ a ∈ A, R₁.map a.toMonoidHom ≠ R₁ → a⁻¹ * t * a ∈ K := by
    intro a ha haR
    rw [hKdef]
    exact ⟨Subgroup.subset_closure ⟨a, ha, rfl⟩,
      s15_Three_tconj_fix ha hfix hR₁mem haR⟩
  have htJ₁ : t ∈ J₁ := by
    rw [hJ₁def]
    refine Subgroup.subset_closure ⟨1, A.one_mem, ?_, ?_⟩
    · rw [hone, Subgroup.map_id]
    · simp
  have hsup' : J₁ ⊔ K = s15TGroup A t := by
    apply le_antisymm
    · exact sup_le hJ₁J hKJ
    · rw [s15TGroup, Subgroup.closure_le]
      rintro g ⟨a, ha, rfl⟩
      by_cases hR₁a : R₁.map a.toMonoidHom = R₁
      · refine Subgroup.mem_sup_left ?_
        rw [hJ₁def]
        exact Subgroup.subset_closure ⟨a, ha, hR₁a, rfl⟩
      · exact Subgroup.mem_sup_right (hmove a ha hR₁a)
  have hJ₁fix : ∀ g ∈ J₁, ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → ∀ u ∈ X, g u = u := by
    intro g hg
    rw [hJ₁def] at hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ X ∈ s15Blocks A R₁, X ≠ R₁ →
      ∀ u ∈ X, g u = u) ?_ ?_ ?_ ?_ hg
    · intro g hg X hX hXR u hu
      obtain ⟨a, ha, hR₁a, rfl⟩ := hg
      refine s15_Three_tconj_fix ha hfix hX ?_ u hu
      intro h
      apply hXR
      have h1 : (X.map a.toMonoidHom).map (a⁻¹).toMonoidHom =
          R₁.map (a⁻¹).toMonoidHom := by rw [h]
      have hcomp : (a⁻¹).toMonoidHom.comp a.toMonoidHom = MonoidHom.id W := by
        ext w; simp [MulAut.inv_apply]
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
      rw [h1, s15_Three_stab_iff hR₁a]
    · intro X hX hXR u hu
      rfl
    · intro g h _ _ hg hh X hX hXR u hu
      show g (h u) = u
      rw [hh X hX hXR u hu, hg X hX hXR u hu]
    · intro g _ hg X hX hXR u hu
      show g.symm u = u
      rw [MulEquiv.symm_apply_eq]
      exact (hg X hX hXR u hu).symm
  have hdisj : J₁ ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxK : x ∈ s15TGroup A t ⊓ centSub R₁ := by rw [← hKdef]; exact hx.2
    let T : Subgroup W :=
      { carrier := {u : W | x u = u}
        one_mem' := map_one x
        mul_mem' := by
          intro a b ha hb
          show x (a * b) = a * b
          rw [map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          show x a⁻¹ = a⁻¹
          rw [map_inv, show x a = a from ha] }
    have hTblocks : ∀ X ∈ s15Blocks A R₁, X ≤ T := by
      intro X hX
      by_cases hXR : X = R₁
      · rw [hXR]
        intro u hu
        exact (mem_centSub.1 hxK.2) u hu
      · intro u hu
        exact hJ₁fix x hx.1 X hX hXR u hu
    have hRfix : ∀ r ∈ R, x r = r := by
      have hRT : R ≤ T := by
        rw [← hsup]
        exact sSup_le hTblocks
      exact fun r hr => hRT hr
    exact s15_Three_tgroup_faithful hRS' hSfix x hxK.1 hRfix
  exact ⟨J₁, K, hJ₁J, hKJ, hKn, hdisj, hsup', htJ₁, hmove⟩

theorem s15_Three_one_block_quot (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {t : MulAut W} (ht : InducesTransvection t ⊤) {R S R₁ : Subgroup W} (hRS' : R ⊔ S = ⊤)
    (hSfix : S ≤ fixV (s15TGroup A t)) (hJ : IsIrrOn (s15TGroup A t) R₁ ⊥)
    (hsup : sSup (s15Blocks A R₁) = R)
    (hfix : ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t))
    (hBA : ⁅A, Subgroup.zpowers t⁆ ≤ A) (hBJ : ⁅A, Subgroup.zpowers t⁆ ≤ s15TGroup A t)
    (hBn : ((⁅A, Subgroup.zpowers t⁆).subgroupOf (s15TGroup A t)).Normal)
    (hidx : ((⁅A, Subgroup.zpowers t⁆).subgroupOf (s15TGroup A t)).index ≤ 2)
    (hno2 : ∀ N : Subgroup ↥(⁅A, Subgroup.zpowers t⁆), N.Normal → (∃ n : ℕ, N.index = 2 ^ n) →
      N = ⊤)
    (htB : t ∉ ⁅A, Subgroup.zpowers t⁆) : R₁ = R := by
  have hstab : ∀ a ∈ A, R₁.map a.toMonoidHom = R₁ := by
    intro a ha
    by_contra haR
    obtain ⟨J₁, K, hJ₁J, hKJ, hKn, hdisj, hsup', htJ₁, hmove⟩ :=
      s15_Three_J_split hRS' hSfix hJ hsup hfix
    have hkJ : a⁻¹ * t * a ∈ K := hmove a ha haR
    have hτJ₁ : t⁻¹ ∈ J₁ := J₁.inv_mem htJ₁
    have hτB : t⁻¹ ∉ ⁅A, Subgroup.zpowers t⁆ := by
      intro h
      exact htB (by simpa using (⁅A, Subgroup.zpowers t⁆).inv_mem h)
    have hb : a⁻¹ * t * a * t⁻¹ ∈ ⁅A, Subgroup.zpowers t⁆ := by
      have hmem : ⁅a⁻¹, t⁆ ∈ ⁅A, Subgroup.zpowers t⁆ :=
        Subgroup.commutator_mem_commutator (A.inv_mem ha) (Subgroup.mem_zpowers t)
      simpa [commutatorElement_def] using hmem
    have hbτ : ∃ k ∈ K, a⁻¹ * t * a * t⁻¹ = k * t⁻¹ :=
      ⟨a⁻¹ * t * a, hkJ, rfl⟩
    exact s15_Three_quot_group hBJ hBn hidx hKJ hKn hJ₁J hdisj hsup'
      hτJ₁ hτB hb hbτ hno2
  rw [← hsup, s15_Three_sSup_blocks_of_stab hstab]

theorem s15_Three_one_block (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hF : Fstar A = A)
    (hO : s15TwoCoreTrivial A) {R S R₁ : Subgroup W} (hRS' : R ⊔ S = ⊤)
    (hSfix : S ≤ fixV (s15TGroup A t)) (hJ : IsIrrOn (s15TGroup A t) R₁ ⊥)
    (htR₁ : commSub R₁ (Subgroup.zpowers t) ≠ ⊥) (hsup : sSup (s15Blocks A R₁) = R)
    (hfix : ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t)) : R₁ = R := by
  obtain ⟨hBA, hBJ, hBn, hidx, hno2⟩ := s15_Three_B_facts hW ht htA hF hO
  by_cases htB : t ∈ ⁅A, Subgroup.zpowers t⁆
  · refine s15_Three_one_block_conj hJ htR₁ hsup hfix fun a ha => ?_
    obtain ⟨e, he, h⟩ := s15_Three_conj_in_J hW ht htA hF hO htB a ha
    exact ⟨e, hBJ he, h⟩
  · exact s15_Three_one_block_quot hW ht hRS' hSfix hJ hsup hfix hBA hBJ hBn hidx hno2 htB

theorem s15_Three_irr_J (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hF : Fstar A = A)
    (hO : s15TwoCoreTrivial A) {R S : Subgroup W} (hR : IsIrrOn A R ⊥)
    (hRt : StableUnder (Subgroup.zpowers t) R) (hS : StableUnder A S)
    (hRS' : R ⊔ S = ⊤) (htS : S ≤ fixV (Subgroup.zpowers t))
    (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) : IsIrrOn (s15TGroup A t) R ⊥ := by
  obtain ⟨R₁, -, h2, h3, h4, h6⟩ := s15_Three_blocks hW ht hR hRt htR
  have := s15_Three_one_block hW ht htA hF hO hRS' (s15_Three_tgroup_fix_S hS htS) h2 h3 h4 h6
  subst this
  exact h2

theorem s15_Three_jnat (hMcL : RMcLaughlin) (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {t : MulAut W} (ht : InducesTransvection t ⊤) (htA : s15Normalizes t A) (hF : Fstar A = A)
    (hO : s15TwoCoreTrivial A) {R S : Subgroup W} (hR : IsIrrOn A R ⊥)
    (hRt : StableUnder (Subgroup.zpowers t) R) (hS : StableUnder A S)
    (hRS : R ⊓ S = ⊥) (hRS' : R ⊔ S = ⊤) (htS : S ≤ fixV (Subgroup.zpowers t))
    (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) : s15JNat (s15TGroup A t) R := by
  have hJ : s15TGroup A t ≠ ⊥ := by
    intro hbot
    have htJ : t ∈ s15TGroup A t :=
      Subgroup.subset_closure ⟨1, A.one_mem, by simp⟩
    have ht1 : t = 1 := by
      have := hbot ▸ htJ
      exact Subgroup.mem_bot.1 this
    apply htR
    rw [ht1]
    refine commSub_eq_bot_iff.2 fun r _ x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    simp
  exact hMcL W hW _ R hJ (s15_Three_irr_J hW ht htA hF hO hR hRt hS hRS' htS htR)
    (s15_Three_tgroup_faithful hRS' (s15_Three_tgroup_fix_S hS htS))
    (s15_Three_gen_transvections hW ht hR hRt hS hRS' htS htR)

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
