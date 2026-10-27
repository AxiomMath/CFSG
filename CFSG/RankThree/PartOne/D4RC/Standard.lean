module

public import CFSG.RankThree.PartOne.D4RC.Class
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

variable {K : Type} [Field K] {σ : K →+* K}

theorem rcg_commute_Uhat_Xh [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u y : twistedGroup σ}
    (hu : (u : adjointGroup d4 K) ∈ Uhat σ) (hy : y ∈ Xh σ) : Commute u y := by
  obtain ⟨c, -, hc⟩ := (mem_Xh_iff hσ y).1 hy
  exact Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact commute_Uhat_xH hσ hu c)

theorem rcg_borel_le_normalizer [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    borel (twistedDatum σ) (hHat σ) ≤ Subgroup.normalizer ((Xh σ : Subgroup (twistedGroup σ)) :
      Set (twistedGroup σ)) := by
  refine sup_le (Tt_normalizes σ (isRoot_rt (by norm_num))) ?_
  refine le_normalizer_of_commute fun x hx y hy => ?_
  rw [posUnipotent_twisted] at hx
  exact rcg_commute_Uhat_Xh hσ (Subgroup.mem_subgroupOf.1 hx) hy

theorem rcg_conj_nHat [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (i : Fin (Tag.rank .G2))
    {p q : ℕ} (hp : p < 12)
    (h : CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) i (rt p) = rt q) :
    conjSub (twistedRootGroup σ (rt p)) (nHat σ i) = twistedRootGroup σ (rt q) := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hγ : rt p ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_rt hp
  have := map_conj_rootGroup hct i hγ
  have e : ((CFSG.LieType.Steinberg.RootSystem.ofCartan (twistedDatum σ).isFiniteType
      (twistedDatum σ).divisible).refl i) (rt p) = rt q := h
  rw [e] at this
  exact this

theorem rcg_exists_standard_pair [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
    {A B : Subgroup (twistedGroup σ)} (hA : A ∈ longClass σ) (hB : B ∈ longClass σ) :
    ∃ g : twistedGroup σ, ∃ t ∈ longPos, conjSub A g = Xh σ ∧
      conjSub B g = twistedRootGroup σ (rt t) := by
  obtain ⟨g₁, rfl⟩ := hA
  obtain ⟨g₂, rfl⟩ := hB
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hh⟩ := exists_mem_bruhatCell hct hext (g₁⁻¹ * g₂)
  obtain ⟨t, ht, hrt0⟩ := weylAction_long (ZMod 2) w 7 (by simp [longPos])
  have hrt : weylAction (twistedDatum σ).isFiniteType w (rt 7) = rt t := hrt0
  have hr7 : rt 7 ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_rt (by norm_num)
  refine ⟨b₁⁻¹ * g₁⁻¹, t, ht, ?_, ?_⟩
  · rw [← conjSub_mul, show b₁⁻¹ * g₁⁻¹ * g₁ = b₁⁻¹ by group]
    exact conjSub_of_mem_normalizer (Subgroup.inv_mem _ (rcg_borel_le_normalizer hσ hb₁))
  · rw [← conjSub_mul]
    have e : b₁⁻¹ * g₁⁻¹ * g₂ = nrep hct w * b₂ := by
      have : g₁⁻¹ * g₂ = b₁ * nrep hct w * b₂ := hh
      calc b₁⁻¹ * g₁⁻¹ * g₂ = b₁⁻¹ * (g₁⁻¹ * g₂) := by group
        _ = b₁⁻¹ * (b₁ * nrep hct w * b₂) := by rw [this]
        _ = nrep hct w * b₂ := by group
    rw [e, conjSub_mul, conjSub_of_mem_normalizer (rcg_borel_le_normalizer hσ hb₂)]
    have hact := actsAs_nrep hct w (rt 7) hr7
    rw [hrt] at hact
    exact hact

theorem rcg_mem_Uhat {t : ℕ} (ht : t ∈ posT) {y : adjointGroup d4 K}
    (hy : y ∈ twistedRootSubgroupD4 σ (rt t)) : y ∈ Uhat σ :=
  (le_iSup₂_of_le (f := fun p (_ : p ∈ posT) => twistedRootSubgroupD4 σ (rt p)) t ht le_rfl) hy

theorem rcg_commuting_pos [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {t : ℕ} (ht : t = 0 ∨ t = 3) :
    Commuting (Xh σ) (twistedRootGroup σ (rt t)) := by
  intro x hx y hy
  have htp : t ∈ posT := by rcases ht with rfl | rfl <;> simp [posT]
  exact (rcg_commute_Uhat_Xh hσ (rcg_mem_Uhat htp (Subgroup.mem_subgroupOf.1 hy)) hx).symm

theorem rcg_comm_xB_xN [CharP K 2] (c c' : K) : ⁅xd 2 c, xd 19 c'⁆ = xd 22 (c * c') := by
  have h1 := swap_19_2 (K := K) c c'
  have hc2 : Commute (xd 22 (c * c')) (xd 2 c) := commute_22_2 _ _
  have hc19 : Commute (xd 22 (c * c')) (xd 19 c') := commute_22_19 _ _
  rw [commutatorElement_def, xd_inv, xd_inv]
  calc xd 2 c * xd 19 c' * xd 2 c * xd 19 c'
      = xd 2 c * (xd 19 c' * xd 2 c) * xd 19 c' := by group
    _ = xd 2 c * (xd 22 (c * c') * (xd 2 c * xd 19 c')) * xd 19 c' := by rw [h1]
    _ = xd 22 (c * c') * (xd 2 c * xd 2 c) * (xd 19 c' * xd 19 c') := by
        rw [show xd 2 c * (xd 22 (c * c') * (xd 2 c * xd 19 c')) * xd 19 c' =
          (xd 2 c * xd 22 (c * c')) * (xd 2 c * xd 19 c') * xd 19 c' by group,
          ← hc2.eq]
        group
    _ = xd 22 (c * c') := by rw [xd_mul_self, xd_mul_self, mul_one, mul_one]

theorem rcg_mem_XBg [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (x : twistedGroup σ) :
    x ∈ twistedRootGroup σ (rt 0) ↔ ∃ c, σ c = c ∧ (x : adjointGroup d4 K) = xd 2 c :=
  (Subgroup.mem_subgroupOf).trans (mem_XB hσ _)

theorem rcg_mem_XNg [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (x : twistedGroup σ) :
    x ∈ twistedRootGroup σ (rt 3) ↔ ∃ c, σ c = c ∧ (x : adjointGroup d4 K) = xd 19 c :=
  (Subgroup.mem_subgroupOf).trans (mem_XN hσ _)

theorem rcg_commutator_Xp0_Xp3 [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    ⁅twistedRootGroup σ (rt 0), twistedRootGroup σ (rt 3)⁆ = Xh σ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨c, hc, hac⟩ := (rcg_mem_XBg hσ a).1 ha
    obtain ⟨c', hc', hbc⟩ := (rcg_mem_XNg hσ b).1 hb
    refine (mem_Xh_iff hσ _).2 ⟨c * c', by rw [map_mul, hc, hc'], ?_⟩
    show ⁅(a : adjointGroup d4 K), (b : adjointGroup d4 K)⁆ = xd 22 (c * c')
    rw [hac, hbc]
    exact rcg_comm_xB_xN c c'
  · intro z hz
    obtain ⟨d, hd, hzd⟩ := (mem_Xh_iff hσ z).1 hz
    have hB : xd 2 d ∈ twistedRootSubgroupD4 σ (rt 0) := (mem_XB hσ _).2 ⟨d, hd, rfl⟩
    have hN : xd 19 (1 : K) ∈ twistedRootSubgroupD4 σ (rt 3) :=
      (mem_XN hσ _).2 ⟨1, map_one σ, rfl⟩
    set a : twistedGroup σ := ⟨xd 2 d, twistedRootSubgroupD4_le_twistedGroup σ
      (isRoot_rt (by norm_num)) hB⟩ with ha
    set b : twistedGroup σ := ⟨xd 19 (1 : K), twistedRootSubgroupD4_le_twistedGroup σ
      (isRoot_rt (by norm_num)) hN⟩ with hb
    have ha' : a ∈ twistedRootGroup σ (rt 0) := Subgroup.mem_subgroupOf.2 hB
    have hb' : b ∈ twistedRootGroup σ (rt 3) := Subgroup.mem_subgroupOf.2 hN
    have h := Subgroup.commutator_mem_commutator ha' hb'
    have e : ⁅a, b⁆ = z := by
      apply Subtype.ext
      show ⁅xd 2 d, xd 19 (1 : K)⁆ = (z : adjointGroup d4 K)
      rw [rcg_comm_xB_xN, mul_one, hzd]
      rfl
    rwa [e] at h

theorem rcg_special_base [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    Special (longClass σ) (twistedRootGroup σ (rt 0)) (twistedRootGroup σ (rt 3)) := by
  unfold Special
  rw [rcg_commutator_Xp0_Xp3 hσ]
  exact ⟨rcg_Xh_mem, rcg_commuting_pos hσ (t := 0) (Or.inl rfl),
    rcg_commuting_pos hσ (t := 3) (Or.inr rfl)⟩

theorem rcg_commuting_conj {G : Type*} [Group G] {A B : Subgroup G} (h : Commuting A B) (g : G) :
    Commuting (conjSub A g) (conjSub B g) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact (h a ha b hb).map (MulAut.conj g).toMonoidHom

theorem rcg_special_symm {G : Type*} [Group G] {R : Set (Subgroup G)} {A B : Subgroup G}
    (h : Special R A B) : Special R B A := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rw [Subgroup.commutator_comm]
  · exact h1
  · exact h3
  · exact h2

theorem rcg_special_conj {G : Type*} [Group G] {R : Set (Subgroup G)}
    (hR : ∀ A ∈ R, ∀ g : G, conjSub A g ∈ R) {A B : Subgroup G} (h : Special R A B) (g : G) :
    Special R (conjSub A g) (conjSub B g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : ⁅conjSub A g, conjSub B g⁆ = conjSub ⁅A, B⁆ g :=
    (Subgroup.map_commutator _ _ _).symm
  refine ⟨?_, ?_, ?_⟩ <;> rw [e]
  · exact hR _ h1 g
  · exact rcg_commuting_conj h2 g
  · exact rcg_commuting_conj h3 g

theorem rcg_conjSub_conj {G : Type*} [Group G] (H : Subgroup G) (g b : G) :
    conjSub (conjSub H g) (g * b * g⁻¹) = conjSub (conjSub H b) g := by
  rw [← conjSub_mul, show g * b * g⁻¹ * g = g * b by group, conjSub_mul]

theorem rcg_opposite_conj {G : Type*} [Group G] {A B : Subgroup G} (h : Opposite A B) (g : G) :
    Opposite (conjSub A g) (conjSub B g) := by
  obtain ⟨hne, h1, h2⟩ := h
  refine ⟨fun e => hne (conjSub_inj g e), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ hx1
    have ha1 : a ≠ 1 := fun e => hx1 (by rw [e]; simp)
    obtain ⟨b, hb, hb1, hab⟩ := h1 a ha ha1
    refine ⟨g * b * g⁻¹, ⟨b, hb, rfl⟩, ?_, ?_⟩
    · intro e
      apply hb1
      have : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      rw [this, e]
      group
    · have e : (MulAut.conj g).toMonoidHom a = g * a * g⁻¹ := rfl
      rw [e, rcg_conjSub_conj, rcg_conjSub_conj, hab]
  · rintro _ ⟨b, hb, rfl⟩ hx1
    have hb1 : b ≠ 1 := fun e => hx1 (by rw [e]; simp)
    obtain ⟨a, ha, ha1, hab⟩ := h2 b hb hb1
    refine ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, ?_, ?_⟩
    · intro e
      apply ha1
      have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
      rw [this, e]
      group
    · have e : (MulAut.conj g).toMonoidHom b = g * b * g⁻¹ := rfl
      rw [e, rcg_conjSub_conj, rcg_conjSub_conj, hab]

theorem rcg_refl_facts :
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 1) (rt 0) = rt 3 ∧
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 1) (rt 3) = rt 0 ∧
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 0) (rt 3) = rt 7 ∧
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 0) (rt 0) = rt 2 ∧
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 1) (rt 2) = rt 6 ∧
    CFSG.LieType.RootSystem.reflection (Tag.cartan .G2) (ng 1) (rt 7) = rt 7 := by
  decide +kernel

theorem rcg_special_2 [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    Special (longClass σ) (Xh σ) (twistedRootGroup σ (rt 2)) := by
  obtain ⟨r10, r13, r07, r02, -, -⟩ := rcg_refl_facts
  have hR : ∀ A ∈ longClass σ, ∀ g, conjSub A g ∈ longClass σ := fun A hA g => rcg_conjSub_mem hA g
  have h0 : conjSub (twistedRootGroup σ (rt 0)) (nHat σ (ng 0) * nHat σ (ng 1)) = Xh σ := by
    rw [conjSub_mul, rcg_conj_nHat hσ (ng 1) (by norm_num) r10,
      rcg_conj_nHat hσ (ng 0) (by norm_num) r07]
  have h3 : conjSub (twistedRootGroup σ (rt 3)) (nHat σ (ng 0) * nHat σ (ng 1)) =
      twistedRootGroup σ (rt 2) := by
    rw [conjSub_mul, rcg_conj_nHat hσ (ng 1) (by norm_num) r13,
      rcg_conj_nHat hσ (ng 0) (by norm_num) r02]
  have := rcg_special_conj hR (rcg_special_base hσ) (nHat σ (ng 0) * nHat σ (ng 1))
  rwa [h0, h3] at this

theorem rcg_special_6 [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    Special (longClass σ) (Xh σ) (twistedRootGroup σ (rt 6)) := by
  obtain ⟨-, -, r07, r02, r12, r17⟩ := rcg_refl_facts
  have hR : ∀ A ∈ longClass σ, ∀ g, conjSub A g ∈ longClass σ := fun A hA g => rcg_conjSub_mem hA g
  have h0 : conjSub (twistedRootGroup σ (rt 0)) (nHat σ (ng 1) * nHat σ (ng 0)) =
      twistedRootGroup σ (rt 6) := by
    rw [conjSub_mul, rcg_conj_nHat hσ (ng 0) (by norm_num) r02,
      rcg_conj_nHat hσ (ng 1) (by norm_num) r12]
  have h3 : conjSub (twistedRootGroup σ (rt 3)) (nHat σ (ng 1) * nHat σ (ng 0)) = Xh σ := by
    rw [conjSub_mul, rcg_conj_nHat hσ (ng 0) (by norm_num) r07,
      rcg_conj_nHat hσ (ng 1) (by norm_num) r17]
  have := rcg_special_conj hR (rcg_special_base hσ) (nHat σ (ng 1) * nHat σ (ng 0))
  rw [h0, h3] at this
  exact rcg_special_symm this

theorem rcg_dict_23 : proj (d4Root 23) = rt 10 ∧ rho (d4Root 23) = d4Root 23 := by
  decide +kernel

theorem rcg_mem_X10g [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (x : twistedGroup σ) :
    x ∈ twistedRootGroup σ (rt 10) ↔ ∃ c, σ c = c ∧ (x : adjointGroup d4 K) = xd 23 c :=
  (Subgroup.mem_subgroupOf).trans
    (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_d4 (by norm_num)) rcg_dict_23.1
      rcg_dict_23.2 _)

theorem rcg_opposite_10 [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    Opposite (Xh σ) (twistedRootGroup σ (rt 10)) := by
  refine opposite_of_sl2 (psiB σ hσ) (psiB_injective σ hσ) ?_ ?_
  · intro x
    constructor
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (mem_Xh_iff hσ x).1 hx
      exact ⟨⟨c, hc⟩, Subtype.ext (by rw [psiB_upper σ hσ]; exact hxc.symm)⟩
    · rintro ⟨c, rfl⟩
      exact (mem_Xh_iff hσ _).2 ⟨c, c.2, psiB_upper σ hσ c⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (rcg_mem_X10g hσ x).1 hx
      exact ⟨⟨c, hc⟩, Subtype.ext (by rw [psiB_lower σ hσ]; exact hxc.symm)⟩
    · rintro ⟨c, rfl⟩
      exact (rcg_mem_X10g hσ _).2 ⟨c, c.2, psiB_lower σ hσ c⟩

theorem rcg_long_pair_dichotomy [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
    {A B : Subgroup (twistedGroup σ)} (hA : A ∈ longClass σ) (hB : B ∈ longClass σ)
    (hne : A ≠ B) : Commuting A B ∨ Opposite A B ∨ Special (longClass σ) A B := by
  obtain ⟨g, t, ht, hgA, hgB⟩ := rcg_exists_standard_pair hσ hA hB
  have ht7 : t ≠ 7 := by
    rintro rfl
    exact hne (conjSub_inj g (hgA.trans hgB.symm))
  have hR : ∀ A ∈ longClass σ, ∀ g, conjSub A g ∈ longClass σ := fun A hA g => rcg_conjSub_mem hA g
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · left
    have h := rcg_commuting_conj (rcg_commuting_pos hσ (t := 0) (Or.inl rfl)) g⁻¹
    rwa [← hgA, ← hgB, conjSub_conjSub_inv', conjSub_conjSub_inv'] at h
  · right; right
    have h := rcg_special_conj hR (rcg_special_2 hσ) g⁻¹
    rwa [← hgA, ← hgB, conjSub_conjSub_inv', conjSub_conjSub_inv'] at h
  · left
    have h := rcg_commuting_conj (rcg_commuting_pos hσ (t := 3) (Or.inr rfl)) g⁻¹
    rwa [← hgA, ← hgB, conjSub_conjSub_inv', conjSub_conjSub_inv'] at h
  · right; right
    have h := rcg_special_conj hR (rcg_special_6 hσ) g⁻¹
    rwa [← hgA, ← hgB, conjSub_conjSub_inv', conjSub_conjSub_inv'] at h
  · exact absurd rfl ht7
  · right; left
    have h := rcg_opposite_conj (rcg_opposite_10 hσ) g⁻¹
    rwa [← hgA, ← hgB, conjSub_conjSub_inv', conjSub_conjSub_inv'] at h

end CFSG.RankThree.PartOne.D4RC
