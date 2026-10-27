module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped Pointwise
open MulAction

private def moved (X : Subgroup (alternatingGroup (Fin 10))) : Set (Fin 10) :=
  {w | ∃ x : ↥X, x • w ≠ w}

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem card_of_mulEquiv_alt5 {X : Subgroup (alternatingGroup (Fin 10))}
    (hX : Nonempty (↥X ≃* alternatingGroup (Fin 5))) : Nat.card ↥X = 60 :=
  (Nat.card_congr hX.some.toEquiv).trans card_alt_five

private lemma smul_apply (X : Subgroup (alternatingGroup (Fin 10))) (x : ↥X) (w : Fin 10) :
    x • w = x.1.1 w := by
  rw [Subgroup.smul_def, Subgroup.smul_def, Equiv.Perm.smul_def]

private lemma smul_comm_of_commute
    {X₁ X₂ : Subgroup (alternatingGroup (Fin 10))}
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (x : ↥X₁) (y : ↥X₂) (w : Fin 10) : x • (y • w) = y • (x • w) := by
  have hc : (x : alternatingGroup (Fin 10)) * (y : alternatingGroup (Fin 10)) =
      (y : alternatingGroup (Fin 10)) * (x : alternatingGroup (Fin 10)) :=
    hcomm x.1 x.2 y.1 y.2
  have hperm : x.1.1 * y.1.1 = y.1.1 * x.1.1 := by
    have := congrArg Subtype.val hc
    simpa using this
  rw [smul_apply, smul_apply, smul_apply, smul_apply]
  calc x.1.1 (y.1.1 w) = (x.1.1 * y.1.1) w := rfl
    _ = (y.1.1 * x.1.1) w := by rw [hperm]
    _ = y.1.1 (x.1.1 w) := rfl

private lemma smul_orbit_of_commute
    {X₁ X₂ : Subgroup (alternatingGroup (Fin 10))}
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (w : Fin 10) (g : ↥X₂) :
    g • (MulAction.orbit ↥X₁ w) = MulAction.orbit ↥X₁ (g • w) := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_smul_set] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [MulAction.mem_orbit_iff]
    exact ⟨x, smul_comm_of_commute hcomm x g w⟩
  · intro hz
    rw [MulAction.mem_orbit_iff] at hz
    obtain ⟨x, rfl⟩ := hz
    rw [Set.mem_smul_set]
    exact ⟨x • w, MulAction.mem_orbit w x, (smul_comm_of_commute hcomm x g w).symm⟩

private lemma orbit_subset_moved {X : Subgroup (alternatingGroup (Fin 10))} {w : Fin 10}
    (hw : w ∈ moved X) : MulAction.orbit ↥X w ⊆ moved X := by
  intro z hz
  rw [MulAction.mem_orbit_iff] at hz
  obtain ⟨x₁, rfl⟩ := hz
  obtain ⟨x₀, hx₀⟩ := hw
  refine ⟨x₁ * x₀ * x₁⁻¹, ?_⟩
  intro heq
  refine hx₀ (MulAction.injective x₁ ?_)
  simpa [mul_smul] using heq

private lemma moved_nonempty {X : Subgroup (alternatingGroup (Fin 10))}
    (hcard : Nat.card ↥X = 60) : (moved X).Nonempty := by
  classical
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have htriv : ∀ x : ↥X, x = 1 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro w
    have hw : x • w = w := by
      by_contra hne
      exact (Set.eq_empty_iff_forall_notMem.mp h w) ⟨x, hne⟩
    simpa [smul_apply] using hw
  have hsub : Subsingleton ↥X := ⟨fun a b => by rw [htriv a, htriv b]⟩
  have hle : Nat.card ↥X ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

private theorem orbit_card_ge_five {X : Subgroup (alternatingGroup (Fin 10))}
    (hX : Nonempty (↥X ≃* alternatingGroup (Fin 5))) {w : Fin 10} (hw : w ∈ moved X) :
    5 ≤ (MulAction.orbit ↥X w).ncard := by
  classical
  obtain ⟨e⟩ := hX
  have hsimple5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hsimple : IsSimpleGroup ↥X :=
    @MulEquiv.isSimpleGroup ↥X inferInstance (alternatingGroup (Fin 5)) inferInstance hsimple5 e
  have hcardX : Nat.card ↥X = 60 := card_of_mulEquiv_alt5 ⟨e⟩
  by_contra h
  have hYle : Nat.card (MulAction.orbit ↥X w) ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    omega
  let φ : ↥X →* Equiv.Perm ↥(MulAction.orbit ↥X w) :=
    MulAction.toPermHom ↥X ↥(MulAction.orbit ↥X w)
  rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
    have hcardle : Nat.card ↥X ≤ Nat.card (Equiv.Perm ↥(MulAction.orbit ↥X w)) :=
      Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm] at hcardle
    have hfac : Nat.factorial (Nat.card ↥(MulAction.orbit ↥X w)) ≤ Nat.factorial 4 :=
      Nat.factorial_le hYle
    rw [hcardX] at hcardle
    have h4 : Nat.factorial 4 = 24 := by decide
    omega
  · obtain ⟨x, hx⟩ := hw
    have hmem : x ∈ φ.ker := htop ▸ Subgroup.mem_top x
    have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hmem
    have hfix : x • w = w := by
      have h1 : x • (⟨w, MulAction.mem_orbit_self w⟩ : MulAction.orbit ↥X w) =
          (⟨w, MulAction.mem_orbit_self w⟩ : MulAction.orbit ↥X w) := by
        have := congrArg (fun p : Equiv.Perm ↥(MulAction.orbit ↥X w) =>
          p ⟨w, MulAction.mem_orbit_self w⟩) hx1
        simpa [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using this
      exact Subtype.ext_iff.mp h1
    exact hx hfix

private theorem disjoint_moved_of_commute
    (X₁ X₂ : Subgroup (alternatingGroup (Fin 10)))
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) :
    Disjoint (moved X₁) (moved X₂) := by
  classical
  obtain ⟨e₂⟩ := h₂
  have hsimple5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hsimple₂ : IsSimpleGroup ↥X₂ :=
    @MulEquiv.isSimpleGroup ↥X₂ inferInstance (alternatingGroup (Fin 5)) inferInstance hsimple5 e₂
  have hcard₂ : Nat.card ↥X₂ = 60 := card_of_mulEquiv_alt5 ⟨e₂⟩
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  set Y : Set (Fin 10) := MulAction.orbit ↥X₁ w with hY
  have hYge : 5 ≤ Y.ncard := by
    rw [hY]
    exact orbit_card_ge_five h₁ hw₁
  have hYw : w ∈ Y := by
    rw [hY]
    exact MulAction.mem_orbit_self w
  have hpres : ∀ g : ↥X₂, g • Y = Y := by
    intro g
    by_contra hg
    have hgY : g • Y = MulAction.orbit ↥X₁ (g • w) := by
      rw [hY]
      exact smul_orbit_of_commute hcomm w g
    have hdisj : Disjoint Y (g • Y) := by
      rcases MulAction.orbit.eq_or_disjoint (G := ↥X₁) w (g • w) with heq | hd
      · exact absurd (by rw [hgY, ← heq, ← hY]) hg
      · rw [hgY, hY]
        exact hd
    have hgYge : 5 ≤ (g • Y).ncard := by
      rw [Set.ncard_smul_set]
      exact hYge
    have hunion_card : (Y ∪ g • Y).ncard = Y.ncard + (g • Y).ncard :=
      Set.ncard_union_eq hdisj
    have hunion_le : (Y ∪ g • Y).ncard ≤ 10 := by
      have := Set.ncard_le_ncard (Set.subset_univ (Y ∪ g • Y))
      rw [Set.ncard_univ, Nat.card_fin] at this
      exact this
    have hYcard : Y.ncard = 5 := by omega
    have hgYcard : (g • Y).ncard = 5 := by omega
    have hunion_univ : Y ∪ g • Y = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [hunion_card, hYcard, hgYcard, Set.ncard_univ, Nat.card_fin]
    have hOsub : MulAction.orbit ↥X₂ Y ⊆ ({Y, g • Y} : Set (Set (Fin 10))) := by
      intro Z hZ
      rw [MulAction.mem_orbit_iff] at hZ
      obtain ⟨h, rfl⟩ := hZ
      rcases eq_or_ne (h • Y) Y with heq | hne
      · exact Or.inl heq
      · have hdisj' : Disjoint Y (h • Y) := by
          have hhY : h • Y = MulAction.orbit ↥X₁ (h • w) := by
            rw [hY]
            exact smul_orbit_of_commute hcomm w h
          rcases MulAction.orbit.eq_or_disjoint (G := ↥X₁) w (h • w) with heq' | hd'
          · exact absurd (by rw [hhY, ← heq', ← hY]) hne
          · rw [hhY, hY]
            exact hd'
        have hle : h • Y ⊆ g • Y := by
          intro z hz
          have hz' : z ∈ Y ∪ g • Y := by rw [hunion_univ]; trivial
          rcases hz' with hzy | hzg
          · exact absurd hzy (Set.disjoint_right.mp hdisj' hz)
          · exact hzg
        have hcard' : (h • Y).ncard = 5 := by
          rw [Set.ncard_smul_set]
          exact hYcard
        have heq2 : h • Y = g • Y :=
          Set.eq_of_subset_of_ncard_le hle (by rw [hcard', hgYcard])
        exact Or.inr heq2
    have hOcard : Nat.card (MulAction.orbit ↥X₂ Y) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc (MulAction.orbit ↥X₂ Y).ncard
            ≤ ({Y, g • Y} : Set (Set (Fin 10))).ncard := Set.ncard_le_ncard hOsub
        _ ≤ 2 := by
            have := Set.ncard_insert_le Y ({g • Y} : Set (Set (Fin 10)))
            simp only [Set.ncard_singleton] at this
            omega
    let φ : ↥X₂ →* Equiv.Perm ↥(MulAction.orbit ↥X₂ Y) :=
      MulAction.toPermHom ↥X₂ ↥(MulAction.orbit ↥X₂ Y)
    rcases hsimple₂.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
    · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
      have hcardle : Nat.card ↥X₂ ≤
          Nat.card (Equiv.Perm ↥(MulAction.orbit ↥X₂ Y)) :=
        Nat.card_le_card_of_injective φ hinj
      rw [Nat.card_perm] at hcardle
      have hfac : Nat.factorial (Nat.card ↥(MulAction.orbit ↥X₂ Y)) ≤ Nat.factorial 2 :=
        Nat.factorial_le hOcard
      rw [hcard₂] at hcardle
      have h2 : Nat.factorial 2 = 2 := by decide
      omega
    · have hgmem : g ∈ φ.ker := htop ▸ Subgroup.mem_top g
      have hg1 : φ g = 1 := MonoidHom.mem_ker.mp hgmem
      have hfix : g • Y = Y := by
        have h1 : g • (⟨Y, MulAction.mem_orbit_self Y⟩ : MulAction.orbit ↥X₂ Y) =
            (⟨Y, MulAction.mem_orbit_self Y⟩ : MulAction.orbit ↥X₂ Y) := by
          have := congrArg (fun p : Equiv.Perm ↥(MulAction.orbit ↥X₂ Y) =>
            p ⟨Y, MulAction.mem_orbit_self Y⟩) hg1
          simpa [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using this
        exact Subtype.ext_iff.mp h1
      exact hg hfix
  have hfix_of_fix : ∀ (x : ↥X₂) (y : ↥Y), x • (y : Fin 10) = (y : Fin 10) →
      ∀ z : ↥Y, x • (z : Fin 10) = (z : Fin 10) := by
    intro x y hxy z
    have hy : (y : Fin 10) ∈ MulAction.orbit ↥X₁ w := y.2
    have hz : (z : Fin 10) ∈ MulAction.orbit ↥X₁ w := z.2
    rw [MulAction.mem_orbit_iff] at hy hz
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    have hx1 : (b * a⁻¹) • (y : Fin 10) = (z : Fin 10) := by
      rw [← ha, ← hb]
      simp only [mul_smul, inv_smul_smul]
    calc x • (z : Fin 10) = x • ((b * a⁻¹) • (y : Fin 10)) := by rw [hx1]
      _ = (b * a⁻¹) • (x • (y : Fin 10)) :=
          (smul_comm_of_commute hcomm (b * a⁻¹) x (y : Fin 10)).symm
      _ = (b * a⁻¹) • (y : Fin 10) := by rw [hxy]
      _ = (z : Fin 10) := hx1
  let ψ : ↥X₂ →* Equiv.Perm ↥Y :=
  { toFun := fun x =>
      { toFun := fun z => ⟨x • (z : Fin 10), (hpres x).le (Set.smul_mem_smul_set z.2)⟩
        invFun := fun z => ⟨x⁻¹ • (z : Fin 10), by
          have hxY : x⁻¹ • Y = Y := by
            calc x⁻¹ • Y = x⁻¹ • (x • Y) := by rw [hpres x]
              _ = (x⁻¹ * x) • Y := by rw [smul_smul]
              _ = Y := by rw [inv_mul_cancel, one_smul]
          exact hxY.le (Set.smul_mem_smul_set z.2)⟩
        left_inv := fun z => Subtype.ext (by
          change x⁻¹ • (x • (z : Fin 10)) = (z : Fin 10)
          rw [inv_smul_smul])
        right_inv := fun z => Subtype.ext (by
          change x • (x⁻¹ • (z : Fin 10)) = (z : Fin 10)
          rw [smul_inv_smul]) }
    map_one' := by
      apply Equiv.ext
      intro z
      apply Subtype.ext
      simp [one_smul]
    map_mul' := by
      intro x y
      apply Equiv.ext
      intro z
      apply Subtype.ext
      simp [mul_smul] }
  rcases hsimple₂.eq_bot_or_eq_top_of_normal ψ.ker with hbot | htop
  ·
    have hstab_le : MulAction.stabilizer ↥X₂ w ≤ ψ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply Equiv.ext
      intro z
      apply Subtype.ext
      change x • (z : Fin 10) = (z : Fin 10)
      exact hfix_of_fix x ⟨w, hYw⟩ (MulAction.mem_stabilizer_iff.mp hx) z
    have hstab : MulAction.stabilizer ↥X₂ w = ⊥ := by
      rw [eq_bot_iff]
      exact hstab_le.trans hbot.le
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥X₂ w
    have hstabcard : Fintype.card (MulAction.stabilizer ↥X₂ w) = 1 := by
      rw [← Nat.card_eq_fintype_card, hstab]
      simp
    have hX₂card : Fintype.card ↥X₂ = 60 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard₂
    have horbit : Fintype.card (MulAction.orbit ↥X₂ w) = 60 := by
      rw [hstabcard, hX₂card] at hos
      omega
    have hle : Fintype.card (MulAction.orbit ↥X₂ w) ≤ 10 := by
      have : Fintype.card (MulAction.orbit ↥X₂ w) ≤ Fintype.card (Fin 10) :=
        Fintype.card_le_of_injective (fun z : MulAction.orbit ↥X₂ w => (z : Fin 10))
          (fun a b hab => Subtype.ext hab)
      simpa using this
    omega
  ·
    obtain ⟨x, hx⟩ := hw₂
    have hx1 : ψ x = 1 := by
      have hxmem : x ∈ ψ.ker := htop ▸ Subgroup.mem_top x
      exact MonoidHom.mem_ker.mp hxmem
    have hfix : x • w = w := by
      have h1 : (ψ x) ⟨w, hYw⟩ = ⟨w, hYw⟩ := by
        rw [hx1]
        rfl
      exact Subtype.ext_iff.mp h1
    exact hx hfix

theorem exists_split_of_commuting_alt5 (X₁ X₂ : Subgroup (alternatingGroup (Fin 10)))
    (h₁ : Nonempty (↥X₁ ≃* alternatingGroup (Fin 5)))
    (h₂ : Nonempty (↥X₂ ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) :
    ∃ S : Finset (Fin 10), S.card = 5 ∧ (∀ x ∈ X₁, ∀ i, i ∉ S → x.1 i = i) ∧
      ∀ y ∈ X₂, ∀ i, i ∈ S → y.1 i = i := by
  classical
  have hcard₁ : Nat.card ↥X₁ = 60 := card_of_mulEquiv_alt5 h₁
  have hcard₂ : Nat.card ↥X₂ = 60 := card_of_mulEquiv_alt5 h₂
  have hdj : Disjoint (moved X₁) (moved X₂) := disjoint_moved_of_commute X₁ X₂ h₁ h₂ hcomm
  obtain ⟨w₁, hw₁⟩ := moved_nonempty hcard₁
  obtain ⟨w₂, hw₂⟩ := moved_nonempty hcard₂
  have hge₁ : 5 ≤ (moved X₁).ncard :=
    (orbit_card_ge_five h₁ hw₁).trans (Set.ncard_le_ncard (orbit_subset_moved hw₁))
  have hge₂ : 5 ≤ (moved X₂).ncard :=
    (orbit_card_ge_five h₂ hw₂).trans (Set.ncard_le_ncard (orbit_subset_moved hw₂))
  have hsub : moved X₂ ⊆ (moved X₁)ᶜ := fun z hz hz₁ =>
    Set.disjoint_left.mp hdj hz₁ hz
  have hle₂ : (moved X₂).ncard ≤ ((moved X₁)ᶜ).ncard := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl, Nat.card_fin] at hle₂
  have hcard₁' : (moved X₁).ncard = 5 := by omega
  refine ⟨(moved X₁).toFinset, ?_, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card']
    exact hcard₁'
  · intro x hx i hi
    have hi₁ : i ∉ moved X₁ := by
      intro hmem
      exact hi (by simpa using hmem)
    have hfix : (⟨x, hx⟩ : ↥X₁) • i = i := by
      by_contra hne
      exact hi₁ (by rw [moved]; exact ⟨⟨x, hx⟩, hne⟩)
    rwa [smul_apply] at hfix
  · intro y hy i hi
    have hi₁ : i ∈ moved X₁ := by
      simpa using hi
    have hi₂ : i ∉ moved X₂ := Set.disjoint_left.mp hdj hi₁
    have hfix : (⟨y, hy⟩ : ↥X₂) • i = i := by
      by_contra hne
      exact hi₂ (by rw [moved]; exact ⟨⟨y, hy⟩, hne⟩)
    rwa [smul_apply] at hfix

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
