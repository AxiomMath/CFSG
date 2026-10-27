module

public import CFSG.RankThree.PartOne.S11d.LayerLink

public section

namespace CFSG.RankThree.PartOne.FOC.Alt

open Equiv Equiv.Perm Subgroup CFSG

section Perm

variable {α : Type} [Fintype α] [DecidableEq α]

theorem commute_cycleOf (σ : Perm α) (i : α) : Commute (σ.cycleOf i) σ := by
  ext y
  show σ.cycleOf i (σ y) = σ (σ.cycleOf i y)
  by_cases h : σ.SameCycle i y
  · have h' : σ.SameCycle i (σ y) := Equiv.Perm.sameCycle_apply_right.mpr h
    rw [h.cycleOf_apply, h'.cycleOf_apply]
  · have h' : ¬ σ.SameCycle i (σ y) := fun h'' => h (Equiv.Perm.sameCycle_apply_right.mp h'')
    rw [Equiv.Perm.cycleOf_apply_of_not_sameCycle h, Equiv.Perm.cycleOf_apply_of_not_sameCycle h']

theorem cycleOf_pow_apply (σ : Perm α) (i : α) (k : ℕ) (y : α) (h : σ.SameCycle i y) :
    (σ.cycleOf i ^ k) y = (σ ^ k) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply]
    have h' : σ.SameCycle i (σ y) := Equiv.Perm.sameCycle_apply_right.mpr h
    rw [h.cycleOf_apply]
    exact ih (σ y) h'

theorem cycleOf_pow_eq_one (σ : Perm α) (i : α) {p : ℕ} (hp : σ ^ p = 1) :
    σ.cycleOf i ^ p = 1 := by
  ext y
  by_cases h : σ.SameCycle i y
  · rw [cycleOf_pow_apply σ i p y h, hp]
  · have : ∀ k : ℕ, (σ.cycleOf i ^ k) y = y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Perm.mul_apply, Equiv.Perm.cycleOf_apply_of_not_sameCycle h, ih]
    rw [this p]
    rfl

theorem sign_cycleOf_eq_one (σ : Perm α) (i : α) {p : ℕ} (hp : σ ^ p = 1) (hodd : Odd p) :
    Perm.sign (σ.cycleOf i) = 1 := by
  have h1 : σ.cycleOf i ^ p = 1 := cycleOf_pow_eq_one σ i hp
  have h2 : (Perm.sign (σ.cycleOf i)) ^ p = 1 := by
    rw [← map_pow, h1, map_one]
  rcases Int.units_eq_one_or (Perm.sign (σ.cycleOf i)) with h | h
  · exact h
  · rw [h] at h2
    exact absurd h2 (by rw [hodd.neg_one_pow]; decide)

theorem sameCycle_apply_of_commute {σ e : Perm α} {i : α} (hi : σ i ≠ i)
    (hρe : e * σ.cycleOf i = σ.cycleOf i * e) {y : α} (hy : σ.SameCycle i y) :
    σ.SameCycle i (e y) := by
  by_contra hne
  have h1 : σ.cycleOf i (e y) = e y := Equiv.Perm.cycleOf_apply_of_not_sameCycle hne
  have h2 : σ.cycleOf i y = σ y := hy.cycleOf_apply
  have h3 : e (σ.cycleOf i y) = σ.cycleOf i (e y) := congrArg (fun f : Perm α => f y) hρe
  rw [h1, h2] at h3
  have h4 : σ y = y := e.injective h3
  exact hi ((hy.apply_eq_self_iff).mpr h4)

theorem commutator_fixes_cycle {σ e₁ e₂ : Perm α} {i : α} (hi : σ i ≠ i)
    (hσ₁ : e₁ * σ = σ * e₁) (hσ₂ : e₂ * σ = σ * e₂)
    (hρ₁ : e₁ * σ.cycleOf i = σ.cycleOf i * e₁) (hρ₂ : e₂ * σ.cycleOf i = σ.cycleOf i * e₂)
    {y : α} (hy : σ.SameCycle i y) : (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) y = y := by
  have hc₁ : ∀ a : ℤ, e₁ * σ ^ a = σ ^ a * e₁ := fun a =>
    ((show Commute e₁ σ from hσ₁).zpow_right a).eq
  have hc₂ : ∀ a : ℤ, e₂ * σ ^ a = σ ^ a * e₂ := fun a =>
    ((show Commute e₂ σ from hσ₂).zpow_right a).eq
  have hinv : ∀ {e : Perm α}, e * σ = σ * e → e * σ.cycleOf i = σ.cycleOf i * e →
      ∀ y, σ.SameCycle i y → σ.SameCycle i (e⁻¹ y) := by
    intro e heσ heρ y hy
    refine sameCycle_apply_of_commute (σ := σ) (e := e⁻¹) hi ?_ hy
    have := congrArg (fun f : Perm α => e⁻¹ * f * e⁻¹) heρ
    simpa [mul_assoc] using this.symm
  have hswap : ∀ z, σ.SameCycle i z → e₁ (e₂ z) = e₂ (e₁ z) := by
    intro z hz
    have hz₂ : σ.SameCycle i (e₂ z) := sameCycle_apply_of_commute hi hρ₂ hz
    have hz₁ : σ.SameCycle i (e₁ z) := sameCycle_apply_of_commute hi hρ₁ hz
    obtain ⟨a₂, ha₂⟩ : σ.SameCycle z (e₂ z) := hz.symm.trans hz₂
    obtain ⟨a₁, ha₁⟩ : σ.SameCycle z (e₁ z) := hz.symm.trans hz₁
    have h1 : e₁ (e₂ z) = (σ ^ a₂) (e₁ z) := by
      rw [← ha₂]
      exact congrArg (fun f : Perm α => f z) (hc₁ a₂)
    have h2 : e₂ (e₁ z) = (σ ^ a₁) (e₂ z) := by
      rw [← ha₁]
      exact congrArg (fun f : Perm α => f z) (hc₂ a₁)
    rw [h1, h2, ← ha₁, ← ha₂]
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← zpow_add, ← zpow_add, add_comm]
  have hz : σ.SameCycle i ((e₁⁻¹ * e₂⁻¹) y) := by
    have h1 := hinv hσ₂ hρ₂ y hy
    exact hinv hσ₁ hρ₁ _ h1
  have : (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) y = (e₁ * e₂) ((e₂ * e₁)⁻¹ y) := by
    simp [mul_assoc]
  rw [this]
  have h3 : (e₁ * e₂) ((e₂ * e₁)⁻¹ y) = (e₂ * e₁) ((e₂ * e₁)⁻¹ y) := by
    have hz' : σ.SameCycle i ((e₂ * e₁)⁻¹ y) := by
      have : (e₂ * e₁)⁻¹ y = (e₁⁻¹ * e₂⁻¹) y := by simp [mul_inv_rev]
      rw [this]
      exact hz
    exact hswap _ hz'
  rw [h3]
  simp

end Perm

section TLevel

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem zpow_comm_apply {σ g : Perm α} (h : g * σ = σ * g) (a : ℤ) (i : α) :
    g ((σ ^ a) i) = (σ ^ a) (g i) :=
  congrArg (fun f : Perm α => f i) (((show Commute g σ from h).zpow_right a).eq)

theorem coe_comm_of_mem_centralizer {b g : alternatingGroup α}
    (hg : g ∈ Subgroup.centralizer ({b} : Set (alternatingGroup α))) :
    (g : Perm α) * (b : Perm α) = (b : Perm α) * (g : Perm α) :=
  congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)

theorem coe_inv_apply {b : alternatingGroup α}
    (z : ↥(Subgroup.centralizer ({b} : Set (alternatingGroup α)))) (k : α) :
    ((z : alternatingGroup α) : Perm α) ((((z⁻¹ : _) : alternatingGroup α) : Perm α) k) = k := by
  simp

@[expose] def orbitPres (b : alternatingGroup α) :
    Subgroup ↥(Subgroup.centralizer ({b} : Set (alternatingGroup α))) where
  carrier := {y | ∀ i, ∃ j : ℤ,
    ((y : alternatingGroup α) : Perm α) i = ((b : Perm α) ^ j) i}
  one_mem' := fun i => ⟨0, by simp⟩
  mul_mem' := by
    intro y₁ y₂ h₁ h₂ i
    obtain ⟨j₂, hj₂⟩ := h₂ i
    obtain ⟨j₁, hj₁⟩ := h₁ i
    refine ⟨j₂ + j₁, ?_⟩
    show ((y₁ : alternatingGroup α) : Perm α) (((y₂ : alternatingGroup α) : Perm α) i) = _
    rw [hj₂, zpow_comm_apply (coe_comm_of_mem_centralizer y₁.2) j₂ i, hj₁, ← Perm.mul_apply,
      ← zpow_add]
  inv_mem' := by
    intro y hy i
    obtain ⟨k, hk⟩ : ∃ k, k = ((((y⁻¹ : _) : alternatingGroup α) : Perm α)) i := ⟨_, rfl⟩
    obtain ⟨j, hj⟩ := hy k
    refine ⟨-j, ?_⟩
    have h1 : ((y : alternatingGroup α) : Perm α) k = i := by
      rw [hk]
      exact coe_inv_apply y i
    rw [h1] at hj
    rw [← hk, hj, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero]
    rfl

theorem orbitPres_normal (b : alternatingGroup α) : (orbitPres b).Normal := by
  refine ⟨fun y hy z i => ?_⟩
  obtain ⟨j, hj⟩ := hy ((((z⁻¹ : _) : alternatingGroup α) : Perm α) i)
  refine ⟨j, ?_⟩
  show ((z : alternatingGroup α) : Perm α) (((y : alternatingGroup α) : Perm α)
    ((((z⁻¹ : _) : alternatingGroup α) : Perm α) i)) = _
  rw [hj, zpow_comm_apply (coe_comm_of_mem_centralizer z.2) j, coe_inv_apply z i]

theorem orbitPres_isSolvable (b : alternatingGroup α) : Group.IsSolvable ↥(orbitPres b) := by
  refine Group.isSolvable_of_comm ?_
  rintro ⟨y₁, h₁⟩ ⟨y₂, h₂⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i
  show ((y₁ : alternatingGroup α) : Perm α) (((y₂ : alternatingGroup α) : Perm α) i) =
    ((y₂ : alternatingGroup α) : Perm α) (((y₁ : alternatingGroup α) : Perm α) i)
  obtain ⟨j₂, hj₂⟩ := h₂ i
  obtain ⟨j₁, hj₁⟩ := h₁ i
  have e1 : ((y₁ : alternatingGroup α) : Perm α) (((y₂ : alternatingGroup α) : Perm α) i) =
      ((b : Perm α) ^ (j₂ + j₁)) i := by
    rw [hj₂, zpow_comm_apply (coe_comm_of_mem_centralizer y₁.2) j₂ i, hj₁, zpow_add,
      Perm.mul_apply]
  have e2 : ((y₂ : alternatingGroup α) : Perm α) (((y₁ : alternatingGroup α) : Perm α) i) =
      ((b : Perm α) ^ (j₁ + j₂)) i := by
    rw [hj₁, zpow_comm_apply (coe_comm_of_mem_centralizer y₂.2) j₁ i, hj₂, zpow_add,
      Perm.mul_apply]
  rw [e1, e2, add_comm]

open CFSG.RankThree.PartOne in
theorem component_fixes_support {b : alternatingGroup α} {p : ℕ} (hbp : b ^ p = 1) (hodd : Odd p)
    {E : Subgroup (alternatingGroup α)}
    (hE : IsComponentOf (Subgroup.centralizer ({b} : Set (alternatingGroup α))) E) :
    ∀ e ∈ E, ∀ i, (b : Perm α) i ≠ i → ((e : alternatingGroup α) : Perm α) i = i := by
  classical
  have hσp : (b : Perm α) ^ p = 1 := by
    have := congrArg Subtype.val hbp
    simpa using this
  set X := Subgroup.centralizer ({b} : Set (alternatingGroup α)) with hX
  have hK : CFSG.IsComponent (E.subgroupOf X) := isComponent_subgroupOf_of_isComponentOf hE
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer (orbitPres_isSolvable b)
    (orbitPres_normal b).isSubnormal).1 _ hK
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro e he i hi
  have hρT : (b : Perm α).cycleOf i ∈ alternatingGroup α :=
    Equiv.Perm.mem_alternatingGroup.mpr (sign_cycleOf_eq_one _ i hσp hodd)
  let ρT : alternatingGroup α := ⟨(b : Perm α).cycleOf i, hρT⟩
  have hρX : ρT ∈ X := by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (commute_cycleOf (b : Perm α) i).eq
  let ρ : ↥X := ⟨ρT, hρX⟩
  have hρR : ρ ∈ orbitPres b := by
    intro y
    by_cases h : (b : Perm α).SameCycle i y
    · exact ⟨1, by simp only [zpow_one]; exact h.cycleOf_apply⟩
    · exact ⟨0, by
        simp only [zpow_zero]
        exact Equiv.Perm.cycleOf_apply_of_not_sameCycle h⟩
  have hec : ∀ e ∈ E, ((e : alternatingGroup α) : Perm α) * (b : Perm α).cycleOf i =
      (b : Perm α).cycleOf i * ((e : alternatingGroup α) : Perm α) := by
    intro e he
    have h1 : (⟨e, hE.1 he⟩ : ↥X) ∈ E.subgroupOf X := he
    have h2 := Subgroup.mem_centralizer_iff.mp (hcent h1) ρ hρR
    have h3 := congrArg (fun z : ↥X => ((z : alternatingGroup α) : Perm α)) h2
    exact h3.symm
  have heσ : ∀ e ∈ E, ((e : alternatingGroup α) : Perm α) * (b : Perm α) =
      (b : Perm α) * ((e : alternatingGroup α) : Perm α) := fun e he =>
    coe_comm_of_mem_centralizer (hE.1 he)
  let H : Subgroup (alternatingGroup α) :=
    { carrier := {g | ∀ y, (b : Perm α).SameCycle i y → ((g : alternatingGroup α) : Perm α) y = y}
      one_mem' := fun y _ => rfl
      mul_mem' := fun {g h} hg hh y hy => by
        show (((g : alternatingGroup α) : Perm α) * ((h : alternatingGroup α) : Perm α)) y = y
        rw [Perm.mul_apply, hh y hy, hg y hy]
      inv_mem' := fun {g} hg y hy => by
        show (((g : alternatingGroup α) : Perm α)⁻¹) y = y
        exact Equiv.Perm.inv_eq_iff_eq.mpr (hg y hy).symm }
  have hEE : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hE.2.1.1
  have hcH : ⁅E, E⁆ ≤ H := by
    refine Subgroup.commutator_le.mpr fun e₁ he₁ e₂ he₂ y hy => ?_
    exact commutator_fixes_cycle hi (heσ e₁ he₁) (heσ e₂ he₂) (hec e₁ he₁) (hec e₂ he₂) hy
  have he' : e ∈ ⁅E, E⁆ := by rw [hEE]; exact he
  have heH : e ∈ H := hcH he'
  exact heH i (Equiv.Perm.SameCycle.refl _ _)

@[expose] def fixSupp (b : alternatingGroup α) : Subgroup (alternatingGroup α) where
  carrier := {g | ∀ i, (b : Perm α) i ≠ i → ((g : alternatingGroup α) : Perm α) i = i}
  one_mem' := fun i _ => rfl
  mul_mem' := fun {g h} hg hh i hi => by
    show (((g : alternatingGroup α) : Perm α) * ((h : alternatingGroup α) : Perm α)) i = i
    rw [Perm.mul_apply, hh i hi, hg i hi]
  inv_mem' := fun {g} hg i hi => by
    show (((g : alternatingGroup α) : Perm α)⁻¹) i = i
    exact Equiv.Perm.inv_eq_iff_eq.mpr (hg i hi).symm

theorem apply_fixed_of_mem_fixSupp {b g : alternatingGroup α} (hg : g ∈ fixSupp b) {i : α}
    (hi : (b : Perm α) i = i) : (b : Perm α) (((g : alternatingGroup α) : Perm α) i) =
      ((g : alternatingGroup α) : Perm α) i := by
  by_contra hne
  have h1 : ((g : alternatingGroup α) : Perm α) (((g : alternatingGroup α) : Perm α) i) =
      ((g : alternatingGroup α) : Perm α) i := hg _ hne
  have h2 : ((g : alternatingGroup α) : Perm α) i = i := ((g : alternatingGroup α) : Perm α).injective h1
  apply hne
  rw [h2]
  exact hi

theorem fixSupp_le_centralizer (b : alternatingGroup α) :
    fixSupp b ≤ Subgroup.centralizer ({b} : Set (alternatingGroup α)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  ext i
  show ((g : alternatingGroup α) : Perm α) ((b : Perm α) i) = (b : Perm α) (((g : alternatingGroup α) : Perm α) i)
  by_cases hi : (b : Perm α) i = i
  · rw [hi, apply_fixed_of_mem_fixSupp hg hi]
  · have hbi : (b : Perm α) ((b : Perm α) i) ≠ (b : Perm α) i := fun h =>
      hi ((b : Perm α).injective h)
    rw [hg _ hbi, hg i hi]

@[expose] noncomputable def fixSuppHom (b : alternatingGroup α) :
    alternatingGroup {i : α // (b : Perm α) i = i} →* ↥(fixSupp b) where
  toFun s := ⟨⟨Perm.ofSubtype (s : Perm {i : α // (b : Perm α) i = i}), by
      rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.mp s.2⟩, fun i hi =>
    Perm.ofSubtype_apply_of_not_mem _ hi⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one _
  map_mul' s t := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul Perm.ofSubtype _ _

theorem fixSuppHom_bijective (b : alternatingGroup α) : Function.Bijective (fixSuppHom b) := by
  constructor
  · intro s t h
    have h1 := congrArg (fun g : ↥(fixSupp b) => ((g : alternatingGroup α) : Perm α)) h
    apply Subtype.ext
    ext a
    have := congrFun (congrArg DFunLike.coe h1) (a : α)
    simpa [fixSuppHom, Perm.ofSubtype_apply_coe] using this
  · rintro ⟨⟨g, hgA⟩, hg⟩
    have hF : ∀ x, (b : Perm α) (g x) = g x ↔ (b : Perm α) x = x := by
      intro x
      constructor
      · intro h
        by_contra hx
        have h2 : g x = x := hg x hx
        rw [h2] at h
        exact hx h
      · exact fun h => apply_fixed_of_mem_fixSupp (b := b) (g := ⟨g, hgA⟩) hg h
    let s : Perm {i : α // (b : Perm α) i = i} := g.subtypePerm hF
    have hs : Perm.ofSubtype s = g :=
      Perm.ofSubtype_subtypePerm hF fun x hx => by
        by_contra hnot
        exact hx (hg x hnot)
    have hsign : Perm.sign s = 1 := by
      have := Equiv.Perm.mem_alternatingGroup.mp hgA
      rw [← hs, Perm.sign_ofSubtype] at this
      exact this
    refine ⟨⟨s, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hs

noncomputable def fixSuppEquiv (b : alternatingGroup α) :
    alternatingGroup {i : α // (b : Perm α) i = i} ≃* ↥(fixSupp b) :=
  MulEquiv.ofBijective (fixSuppHom b) (fixSuppHom_bijective b)

theorem fixSupp_isSimpleGroup (b : alternatingGroup α)
    (h : 5 ≤ Nat.card {i : α // (b : Perm α) i = i}) : IsSimpleGroup ↥(fixSupp b) := by
  have := alternatingGroup.isSimpleGroup h
  exact (fixSuppEquiv b).symm.isSimpleGroup

theorem fixSupp_isSolvable (b : alternatingGroup α)
    (h : Nat.card {i : α // (b : Perm α) i = i} ≤ 4) : Group.IsSolvable ↥(fixSupp b) := by
  have := alternatingGroup.isSolvable h
  exact Group.isSolvable_of_surjective (fixSuppEquiv b).surjective

open CFSG.RankThree.PartOne in
theorem component_eq_fixSupp {b : alternatingGroup α} {p : ℕ} (hbp : b ^ p = 1) (hodd : Odd p)
    {E : Subgroup (alternatingGroup α)}
    (hE : IsComponentOf (Subgroup.centralizer ({b} : Set (alternatingGroup α))) E) :
    E = fixSupp b := by
  have hle : E ≤ fixSupp b := fun e he i hi => component_fixes_support hbp hodd hE e he i hi
  by_cases hF : 5 ≤ Nat.card {i : α // (b : Perm α) i = i}
  · have hs := fixSupp_isSimpleGroup b hF
    set X := Subgroup.centralizer ({b} : Set (alternatingGroup α)) with hX
    have hFX : fixSupp b ≤ X := fixSupp_le_centralizer b
    have hK : CFSG.IsComponent (E.subgroupOf X) := isComponent_subgroupOf_of_isComponentOf hE
    have hKH : E.subgroupOf X ≤ (fixSupp b).subgroupOf X := fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hg))
    have hcomp := CFSG.LocalCores.component_overgroup hK hKH
    have hsimple : IsSimpleGroup ↥((fixSupp b).subgroupOf X) :=
      (Subgroup.subgroupOfEquivOfLe hFX).isSimpleGroup
    have hne : (E.subgroupOf X).subgroupOf ((fixSupp b).subgroupOf X) ≠ ⊥ := by
      intro hbot
      have := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
      rw [hbot] at this
      exact not_nontrivial_iff_subsingleton.mpr (inferInstance :
        Subsingleton (⊥ : Subgroup ↥((fixSupp b).subgroupOf X))) this
    have htop := (Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hcomp.2).resolve_left
      hne
    refine le_antisymm hle fun f hf => ?_
    have hf' : (⟨⟨f, hFX hf⟩, Subgroup.mem_subgroupOf.mpr hf⟩ : ↥((fixSupp b).subgroupOf X)) ∈
        (E.subgroupOf X).subgroupOf ((fixSupp b).subgroupOf X) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hf')
  · exfalso
    have hsolv := fixSupp_isSolvable b (by omega)
    have hEsolv : Group.IsSolvable ↥E :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    have : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE.2.1
    have : Group.IsPerfect ↥E := hE.2.1.1
    exact Group.IsPerfect.not_isSolvable ↥E hEsolv

theorem sign_eq_one_of_pow_eq_one {β : Type} [Fintype β] [DecidableEq β] (g : Perm β) {p : ℕ}
    (hodd : Odd p) (hg : g ^ p = 1) : Perm.sign g = 1 := by
  have h2 : (Perm.sign g) ^ p = 1 := by
    rw [← map_pow, hg, map_one]
  rcases Int.units_eq_one_or (Perm.sign g) with h | h
  · exact h
  · rw [h] at h2
    exact absurd h2 (by rw [hodd.neg_one_pow]; decide)

open CFSG.RankThree.PartOne in
theorem mem_sup_centralizer_of_component_alt {b x : alternatingGroup α} {p : ℕ} (hodd : Odd p)
    (hbp : b ^ p = 1) (hxp : x ^ p = 1) (hbx : b * x = x * b)
    {E : Subgroup (alternatingGroup α)}
    (hE : IsComponentOf (Subgroup.centralizer ({b} : Set (alternatingGroup α))) E) :
    x ∈ E ⊔ Subgroup.centralizer (E : Set (alternatingGroup α)) := by
  have hEeq := component_eq_fixSupp hbp hodd hE
  set σ : Perm α := (b : Perm α) with hσ
  set ξ : Perm α := (x : Perm α) with hξ
  have hcomm : σ * ξ = ξ * σ := congrArg Subtype.val hbx
  have hξp : ξ ^ p = 1 := by
    have := congrArg Subtype.val hxp
    simpa using this
  have hmove' : ∀ i, (σ (ξ i) ≠ ξ i) ↔ (σ i ≠ i) := by
    intro i
    have h1 : σ (ξ i) = ξ (σ i) := congrArg (fun f : Perm α => f i) hcomm
    rw [h1]
    constructor
    · intro h h2
      apply h
      rw [h2]
    · intro h h2
      exact h (ξ.injective h2)
  let xS : Perm α := Perm.ofSubtype (ξ.subtypePerm (p := fun i => σ i ≠ i) hmove')
  have hxS_apply : ∀ i, σ i ≠ i → xS i = ξ i := fun i hi => by
    show (Perm.ofSubtype (ξ.subtypePerm (p := fun i => σ i ≠ i) hmove')) i = ξ i
    rw [Perm.ofSubtype_apply_of_mem (p := fun i => σ i ≠ i) _ hi]
    rfl
  have hxS_fix : ∀ i, σ i = i → xS i = i := fun i hi =>
    Perm.ofSubtype_apply_of_not_mem (p := fun i => σ i ≠ i) _ (not_not.mpr hi)
  have hxSp : xS ^ p = 1 := by
    have h1 : (ξ.subtypePerm (p := fun i => σ i ≠ i) hmove') ^ p = 1 := by
      rw [Perm.subtypePerm_pow]
      ext ⟨i, hi⟩
      simp [hξp]
    show (Perm.ofSubtype (ξ.subtypePerm (p := fun i => σ i ≠ i) hmove')) ^ p = 1
    rw [← map_pow, h1, map_one]
  have hsS : Perm.sign xS = 1 := sign_eq_one_of_pow_eq_one xS hodd hxSp
  have hsξ : Perm.sign ξ = 1 := Equiv.Perm.mem_alternatingGroup.mp x.2
  let xF : Perm α := xS⁻¹ * ξ
  have hxF_fix : ∀ i, σ i ≠ i → xF i = i := fun i hi => by
    show xS⁻¹ (ξ i) = i
    rw [← hxS_apply i hi]
    simp
  have hsF : Perm.sign xF = 1 := by
    simp [xF, hsS, hsξ]
  let xS' : alternatingGroup α := ⟨xS, Equiv.Perm.mem_alternatingGroup.mpr hsS⟩
  let xF' : alternatingGroup α := ⟨xF, Equiv.Perm.mem_alternatingGroup.mpr hsF⟩
  have hxeq : x = xS' * xF' := by
    apply Subtype.ext
    show ξ = xS * (xS⁻¹ * ξ)
    group
  have hxF'E : xF' ∈ E := by
    rw [hEeq]
    exact hxF_fix
  have hxS'C : xS' ∈ Subgroup.centralizer (E : Set (alternatingGroup α)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ fixSupp b := hEeq ▸ hh
    apply Subtype.ext
    show (h : Perm α) * xS = xS * (h : Perm α)
    refine (Equiv.Perm.Disjoint.commute ?_).eq
    intro i
    by_cases hi : σ i = i
    · exact Or.inr (hxS_fix i hi)
    · exact Or.inl (hh' i hi)
  rw [hxeq, sup_comm]
  exact Subgroup.mul_mem_sup hxS'C hxF'E

end TLevel

end CFSG.RankThree.PartOne.FOC.Alt
