module

public import CFSG.Timmesfeld.RankTwo.SimplyLaced
import CFSG.Timmesfeld.ARS.FrameSL3Steinberg

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

namespace LevisExtras

section Roots

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

def stab (S : Set (Fin D.rank → ℤ)) : Subgroup (coxeterMatrix D.isFiniteType).Group where
  carrier := {u | ∀ γ, weylAction D.isFiniteType u γ ∈ S ↔ γ ∈ S}
  one_mem' := by simp
  mul_mem' {u v} hu hv γ := by
    simp only [Set.mem_ofPred_eq] at hu hv
    rw [weylAction_mul_apply, hu, hv]
  inv_mem' {u} hu γ := by
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [← hu, weylAction_apply_inv_apply]

theorem pairRoots_subset (hdiv : D.divisible = ∅) {i j : Fin D.rank}
    {S : Set (Fin D.rank → ℤ)} (hi : sroot i ∈ S) (hj : sroot j ∈ S)
    (hsi : ∀ γ ∈ S, reflection D.cartan i γ ∈ S) (hsj : ∀ γ ∈ S, reflection D.cartan j γ ∈ S) :
    pairRoots D i j ⊆ S := by
  rintro γ ⟨hγ, hsupp⟩
  rcases hγ with ⟨w, m, rfl⟩ | ⟨w, m, hm, -⟩
  · obtain ⟨z, hz, m', hm', hzm⟩ := exists_parabolic_of_support D.isFiniteType {i, j} w m
      (fun k hk => hsupp k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h)))
    have hle : (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {i, j} ≤ stab S := by
      rw [CoxeterSystem.parabolic_le_iff]
      intro k hk γ
      rw [weylAction_simple]
      have hsk : ∀ γ ∈ S, reflection D.cartan k γ ∈ S := by
        rcases hk with rfl | rfl
        exacts [hsi, hsj]
      refine ⟨fun h => ?_, hsk γ⟩
      have := hsk _ h
      rwa [← Module.End.mul_apply, reflection_mul_self (D.isFiniteType.apply_self k),
        Module.End.one_apply] at this
    have hS : (Pi.single m' 1 : Fin D.rank → ℤ) ∈ S := by
      rcases hm' with rfl | rfl
      exacts [hi, hj]
    rw [← hzm] at hS
    exact (hle hz _).1 hS
  · rw [hdiv] at hm
    exact absurd hm (Set.notMem_empty m)

def zA2 : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

def zA1A1 : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

theorem zA2_expPairs : ∀ z ∈ zA2, ∀ w ∈ zA2, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b →
    a • z + b • w ∈ zA2 → a = 1 ∧ b = 1 := by
  intro z hz w hw hzw a b ha hb h
  simp only [zA2, Finset.mem_insert, Finset.mem_singleton] at hz hw h
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Prod.ext_iff] at hzw h ⊢ <;> omega

theorem zA1A1_expPairs : ∀ z ∈ zA1A1, ∀ w ∈ zA1A1, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b →
    a • z + b • w ∈ zA1A1 → a = 1 ∧ b = 1 := by
  intro z hz w hw hzw a b ha hb h
  simp only [zA1A1, Finset.mem_insert, Finset.mem_singleton] at hz hw h
  rcases hz with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
    simp [Prod.ext_iff] at hzw h ⊢ <;> omega

theorem pair_injective {i j : Fin D.rank} (hij : i ≠ j) : Function.Injective (pair i j) := by
  intro z w h
  have hi := congrFun h i
  have hj := congrFun h j
  simp [pair_apply, hij, hij.symm] at hi hj
  exact Prod.ext hi hj

theorem pair_mem_pairRoots {i j : Fin D.rank} {z : ℤ × ℤ} (h : pair i j z ∈ D.roots) :
    pair i j z ∈ pairRoots D i j :=
  ⟨h, fun k hi hj => by simp [pair_apply, hi, hj]⟩

theorem mem_of_pair_mem {i j : Fin D.rank} (hij : i ≠ j) {Z : Finset (ℤ × ℤ)}
    (hsub : pairRoots D i j ⊆ pair i j '' Z) {z : ℤ × ℤ} (h : pair i j z ∈ D.roots) : z ∈ Z := by
  obtain ⟨w, hw, e⟩ := hsub (pair_mem_pairRoots h)
  rwa [pair_injective hij e] at hw

theorem reflection_mem_roots (i : Fin D.rank) {γ : Fin D.rank → ℤ} (h : γ ∈ D.roots) :
    reflection D.cartan i γ ∈ D.roots := by
  have := weylAction_mem_roots D.isFiniteType
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) h
  rwa [weylAction_simple] at this

theorem pairRoots_subset_pair (hdiv : D.divisible = ∅) {i j : Fin D.rank} {Z : Finset (ℤ × ℤ)}
    (h10 : (1, 0) ∈ Z) (h01 : (0, 1) ∈ Z)
    (hLi : ∀ z ∈ Z, (-z.1 - D.cartan i j * z.2, z.2) ∈ Z)
    (hLj : ∀ z ∈ Z, (z.1, -z.2 - D.cartan j i * z.1) ∈ Z) :
    pairRoots D i j ⊆ pair i j '' Z := by
  refine pairRoots_subset hdiv ⟨(1, 0), h10, by simp [pair_apply]⟩
    ⟨(0, 1), h01, by simp [pair_apply]⟩ ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, hLi z hz, (reflection_pair_left j (D.isFiniteType.apply_self i) z).symm⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, hLj z hz, (reflection_pair_right i (D.isFiniteType.apply_self j) z).symm⟩

theorem pair_one_zero (i j : Fin D.rank) : pair i j (1, 0) = sroot i := by simp [pair_apply]

theorem pair_zero_one (i j : Fin D.rank) : pair i j (0, 1) = sroot j := by simp [pair_apply]

theorem pair_neg_one_zero (i j : Fin D.rank) : pair i j (-1, 0) = -sroot i := by
  simp [pair_apply]

theorem pair_zero_neg_one (i j : Fin D.rank) : pair i j (0, -1) = -sroot j := by
  simp [pair_apply]

theorem pair_one_one (i j : Fin D.rank) : pair i j (1, 1) = sroot i + sroot j := by
  simp [pair_apply]

theorem pair_neg_one_neg_one (i j : Fin D.rank) : pair i j (-1, -1) = -(sroot i + sroot j) := by
  rw [pair_apply, neg_add, neg_one_zsmul, neg_one_zsmul]

theorem single_mem_roots (i : Fin D.rank) : sroot i ∈ D.roots := Or.inl ⟨1, i, by simp⟩

theorem neg_mem_roots {γ : Fin D.rank → ℤ} (h : γ ∈ D.roots) : -γ ∈ D.roots :=
  Steinberg.OfCartan.neg_mem_roots _ h

theorem pair_mem_roots_A2 {i j : Fin D.rank} (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) : ∀ z ∈ zA2, pair i j z ∈ D.roots := by
  have h10 : pair i j (1, 0) ∈ D.roots := by rw [pair_one_zero]; exact single_mem_roots i
  have h01 : pair i j (0, 1) ∈ D.roots := by rw [pair_zero_one]; exact single_mem_roots j
  have hLi : ∀ z, pair i j z ∈ D.roots → pair i j (-z.1 + z.2, z.2) ∈ D.roots := fun z h => by
    have := reflection_mem_roots i h
    rwa [reflection_pair_left j (D.isFiniteType.apply_self i), hcij, neg_one_mul, sub_neg_eq_add]
      at this
  have hLj : ∀ z, pair i j z ∈ D.roots → pair i j (z.1, -z.2 + z.1) ∈ D.roots := fun z h => by
    have := reflection_mem_roots j h
    rwa [reflection_pair_right i (D.isFiniteType.apply_self j), hcji, neg_one_mul,
      sub_neg_eq_add] at this
  simp only [zA2, Finset.mem_insert, Finset.mem_singleton]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact h10
  · simpa using hLi _ h10
  · exact h01
  · simpa using hLj _ h01
  · simpa using hLj _ h10
  · simpa using hLi _ (hLj _ h01)

theorem pair_mem_roots_A1A1 (i j : Fin D.rank) : ∀ z ∈ zA1A1, pair i j z ∈ D.roots := by
  simp only [zA1A1, Finset.mem_insert, Finset.mem_singleton]
  rintro z (rfl | rfl | rfl | rfl)
  · rw [pair_one_zero]; exact single_mem_roots i
  · rw [pair_neg_one_zero]; exact neg_mem_roots (single_mem_roots i)
  · rw [pair_zero_one]; exact single_mem_roots j
  · rw [pair_zero_neg_one]; exact neg_mem_roots (single_mem_roots j)

end Roots

section Commutator

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type*} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem x_zero (hE : Steinberg.ChevalleyExtras D F x C O) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : x γ 0 = 1 := by
  have h := (hE.param γ hγ).2.1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem list_eq_singleton {α : Type*} {l : List α} {q : α} (hl : l.Nodup)
    (h : ∀ p, p ∈ l ↔ p = q) : l = [q] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hl (List.nodup_singleton q)).2
    fun p => by rw [h, List.mem_singleton])

theorem commutator_eq (hE : Steinberg.ChevalleyExtras D F x C O) {α β : Fin D.rank → ℤ}
    (hα : α ∈ D.roots) (hβ : β ∈ D.roots) (hne : α + β ≠ 0)
    (hexp : ∀ a b : ℕ, 0 < a → 0 < b → a • α + b • β ∈ D.roots → a = 1 ∧ b = 1) (c d : F) :
    (α + β ∈ D.roots → ⁅x α c, x β d⁆ = x (α + β) (C α β (1, 1) * c * d)) ∧
      (α + β ∉ D.roots → ⁅x α c, x β d⁆ = 1) := by
  have hmem : ∀ p, p ∈ O.list α β ↔ α + β ∈ D.roots ∧ p = (1, 1) := by
    intro p
    rw [O.mem_iff α hα β hβ hne]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨e1, e2⟩ := hexp p.1 p.2 h1 h2 h3
      refine ⟨?_, Prod.ext e1 e2⟩
      have h3' : p.1 • α + p.2 • β ∈ D.roots := h3
      rwa [e1, e2, one_smul, one_smul] at h3'
    · rintro ⟨hr, rfl⟩
      refine ⟨one_pos, one_pos, ?_⟩
      change (1 : ℕ) • α + (1 : ℕ) • β ∈ D.roots
      rwa [one_smul, one_smul]
  rw [hE.comm α hα β hβ hne c d]
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · rw [list_eq_singleton (O.nodup α β) fun p => (hmem p).trans (and_iff_right hr)]
    simp
  · rw [List.eq_nil_iff_forall_not_mem.2 fun p hp => hr ((hmem p).1 hp).1]
    rfl

theorem intCast_eq_one [CharP F 2] {n : ℤ} (h : n.natAbs = 1) : (n : F) = 1 := by
  rcases Int.natAbs_eq_iff.1 h with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem commutator_eq_of_charTwo [CharP F 2] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    {α β : Fin D.rank → ℤ} (hα : α ∈ D.roots) (hβ : β ∈ D.roots) (hne : α + β ≠ 0)
    (hexp : ∀ a b : ℕ, 0 < a → 0 < b → a • α + b • β ∈ D.roots → a = 1 ∧ b = 1) (c d : F) :
    (α + β ∈ D.roots → β - α ∉ D.roots → ⁅x α c, x β d⁆ = x (α + β) (c * d)) ∧
      (α + β ∉ D.roots → ⁅x α c, x β d⁆ = 1) := by
  obtain ⟨h1, h2⟩ := commutator_eq hE hα hβ hne hexp c d
  refine ⟨fun hr hd => ?_, h2⟩
  rw [h1 hr, intCast_eq_one (hC α hα β hβ hr hd), one_mul]

theorem commutator_pair [CharP F 2] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    {i j : Fin D.rank} (hij : i ≠ j) {Z : Finset (ℤ × ℤ)}
    (hsub : pairRoots D i j ⊆ pair i j '' Z) (hroot : ∀ z ∈ Z, pair i j z ∈ D.roots)
    (hZ : ∀ z ∈ Z, ∀ w ∈ Z, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b → a • z + b • w ∈ Z →
      a = 1 ∧ b = 1)
    {z w : ℤ × ℤ} (hz : z ∈ Z) (hw : w ∈ Z) (hzw : z + w ≠ 0) (c d : F) :
    (z + w ∈ Z → w - z ∉ Z →
      ⁅x (pair i j z) c, x (pair i j w) d⁆ = x (pair i j (z + w)) (c * d)) ∧
      (z + w ∉ Z → ⁅x (pair i j z) c, x (pair i j w) d⁆ = 1) := by
  have hne : pair i j z + pair i j w ≠ 0 := by
    rw [← map_add, ← map_zero (pair i j)]
    exact fun h => hzw (pair_injective hij h)
  have hexp : ∀ a b : ℕ, 0 < a → 0 < b → a • pair i j z + b • pair i j w ∈ D.roots →
      a = 1 ∧ b = 1 := by
    intro a b ha hb h
    rw [← map_nsmul, ← map_nsmul, ← map_add] at h
    exact hZ z hz w hw hzw a b ha hb (mem_of_pair_mem hij hsub h)
  obtain ⟨h1, h2⟩ := commutator_eq_of_charTwo hE hC (hroot z hz) (hroot w hw) hne hexp c d
  rw [← map_add] at h1 h2
  refine ⟨fun hs hd => h1 (hroot _ hs) fun h => hd ?_,
    fun hs => h2 fun h => hs (mem_of_pair_mem hij hsub h)⟩
  rw [← map_sub] at h
  exact mem_of_pair_mem hij hsub h

end Commutator

section Torus

variable {F : Type} [Field F] {G : Type*} [Group G]

def wElt (u v : F → G) (t : F) : G := u t * v (-t⁻¹) * u t

def hElt (u v : F → G) (t : F) : G := wElt u v t * wElt u v (-1)

theorem map_hElt {H : Type*} [Group H] (φ : G →* H) (u v : F → G) (t : F) :
    φ (hElt u v t) = hElt (fun c => φ (u c)) (fun c => φ (v c)) t := by
  simp only [hElt, wElt, map_mul]

theorem commute_hElt {u v : F → G} {g : G} (hu : ∀ c, Commute (u c) g)
    (hv : ∀ c, Commute (v c) g) (t : F) : Commute (hElt u v t) g := by
  simp only [hElt, wElt]
  exact (((hu _).mul_left (hv _)).mul_left (hu _)).mul_left
    (((hu _).mul_left (hv _)).mul_left (hu _))

open Matrix

theorem cm_tv01 (c : F) : SpecialLinearGroup.coeMonoidHom
    (tv 0 1 c : SpecialLinearGroup (Fin 3) F) = !![1, c, 0; 0, 1, 0; 0, 0, 1] := by
  rw [SpecialLinearGroup.coeMonoidHom_apply, tv_of_ne (by decide),
    SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem cm_tv10 (c : F) : SpecialLinearGroup.coeMonoidHom
    (tv 1 0 c : SpecialLinearGroup (Fin 3) F) = !![1, 0, 0; c, 1, 0; 0, 0, 1] := by
  rw [SpecialLinearGroup.coeMonoidHom_apply, tv_of_ne (by decide),
    SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem cm_tv12 (c : F) : SpecialLinearGroup.coeMonoidHom
    (tv 1 2 c : SpecialLinearGroup (Fin 3) F) = !![1, 0, 0; 0, 1, c; 0, 0, 1] := by
  rw [SpecialLinearGroup.coeMonoidHom_apply, tv_of_ne (by decide),
    SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem cm_tv21 (c : F) : SpecialLinearGroup.coeMonoidHom
    (tv 2 1 c : SpecialLinearGroup (Fin 3) F) = !![1, 0, 0; 0, 1, 0; 0, c, 1] := by
  rw [SpecialLinearGroup.coeMonoidHom_apply, tv_of_ne (by decide),
    SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem cm_h01 {t : F} (ht : t ≠ 0) : SpecialLinearGroup.coeMonoidHom
    (hElt (tv 0 1) (tv 1 0) t : SpecialLinearGroup (Fin 3) F) =
      !![t, 0, 0; 0, t⁻¹, 0; 0, 0, 1] := by
  simp only [hElt, wElt, map_mul, cm_tv01, cm_tv10, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem cm_h12 {t : F} (ht : t ≠ 0) : SpecialLinearGroup.coeMonoidHom
    (hElt (tv 1 2) (tv 2 1) t : SpecialLinearGroup (Fin 3) F) =
      !![1, 0, 0; 0, t, 0; 0, 0, t⁻¹] := by
  simp only [hElt, wElt, map_mul, cm_tv12, cm_tv21, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem h01_mul_tv12 {t : F} (ht : t ≠ 0) (c : F) :
    hElt (tv 0 1) (tv 1 0) t * (tv 1 2 c : SpecialLinearGroup (Fin 3) F) =
      tv 1 2 (t⁻¹ * c) * hElt (tv 0 1) (tv 1 0) t := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul, cm_h01 ht, cm_tv12, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem h12_mul_tv01 {t : F} (ht : t ≠ 0) (c : F) :
    hElt (tv 1 2) (tv 2 1) t * (tv 0 1 c : SpecialLinearGroup (Fin 3) F) =
      tv 0 1 (t⁻¹ * c) * hElt (tv 1 2) (tv 2 1) t := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul, cm_h12 ht, cm_tv01, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp
  field_simp

theorem exists_eq_of_mem_center {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) :
    ∃ ω : F, ω ≠ 0 ∧ ω ^ 3 = 1 ∧ g = hElt (tv 0 1) (tv 1 0) ω * hElt (tv 1 2) (tv 2 1) (ω ^ 2) ∧
      (ω = 1 → g = 1) := by
  obtain ⟨ω, hω, hg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hω
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω
  refine ⟨ω, hω0, hω, ?_, fun h1 => ?_⟩
  · apply SpecialLinearGroup.coeMonoidHom_injective
    rw [map_mul, cm_h01 hω0, cm_h12 (pow_ne_zero 2 hω0), Matrix.mul_fin_three,
      SpecialLinearGroup.coeMonoidHom_apply, ← hg]
    have e1 : ω⁻¹ * ω ^ 2 = ω := by field_simp
    have e2 : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_left (by rw [← pow_succ', hω])
    ext a b
    fin_cases a <;> fin_cases b <;> simp [e1, e2]
  · apply SpecialLinearGroup.coeMonoidHom_injective
    rw [SpecialLinearGroup.coeMonoidHom_apply, ← hg, h1, map_one, map_one]

def Adjoins (u v w : F → G) : Prop :=
  (∃ ρ : SpecialLinearGroup (Fin 3) F →* G,
      ∀ c, ρ (tv 0 1 c) = u c ∧ ρ (tv 1 0 c) = v c ∧ ρ (tv 1 2 c) = w c) ∨
    ∃ ρ : SpecialLinearGroup (Fin 3) F →* G,
      ∀ c, ρ (tv 1 2 c) = u c ∧ ρ (tv 2 1 c) = v c ∧ ρ (tv 0 1 c) = w c

theorem eq_one_of_adjoins {u v w : F → G} (h : Adjoins u v w) (hw : Function.Injective w)
    {t : F} (ht : t ≠ 0) (hc : Commute (hElt u v t) (w 1)) : t = 1 := by
  have key : hElt u v t * w 1 = w t⁻¹ * hElt u v t := by
    rcases h with ⟨ρ, hρ⟩ | ⟨ρ, hρ⟩
    · have eu : (fun c => ρ (tv 0 1 c)) = u := funext fun c => (hρ c).1
      have ev : (fun c => ρ (tv 1 0 c)) = v := funext fun c => (hρ c).2.1
      rw [← eu, ← ev, ← map_hElt, ← (hρ 1).2.2, ← (hρ t⁻¹).2.2, ← map_mul, ← map_mul,
        h01_mul_tv12 ht, mul_one]
    · have eu : (fun c => ρ (tv 1 2 c)) = u := funext fun c => (hρ c).1
      have ev : (fun c => ρ (tv 2 1 c)) = v := funext fun c => (hρ c).2.1
      rw [← eu, ← ev, ← map_hElt, ← (hρ 1).2.2, ← (hρ t⁻¹).2.2, ← map_mul, ← map_mul,
        h12_mul_tv01 ht, mul_one]
  have e : w t⁻¹ = w 1 := mul_right_cancel (key.symm.trans hc.eq)
  exact inv_eq_one.1 (hw e)

theorem injective_of_adjoins {ρ : SpecialLinearGroup (Fin 3) F →* G} {ui vi uj vj w : F → G}
    (hi : ∀ c, ρ (tv 0 1 c) = ui c ∧ ρ (tv 1 0 c) = vi c)
    (hj : ∀ c, ρ (tv 1 2 c) = uj c ∧ ρ (tv 2 1 c) = vj c) (hnt : ∃ c, ui c ≠ 1)
    (hw : Function.Injective w)
    (h : ((∀ c, Commute (ui c) (w 1)) ∧ (∀ c, Commute (vi c) (w 1)) ∧ Adjoins uj vj w) ∨
      ((∀ c, Commute (uj c) (w 1)) ∧ (∀ c, Commute (vj c) (w 1)) ∧ Adjoins ui vi w)) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt' : ∃ g, ρ g ≠ 1 := by
    obtain ⟨c, hc⟩ := hnt
    exact ⟨tv 0 1 c, by rw [(hi c).1]; exact hc⟩
  have hker : g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) hnt' hg
  obtain ⟨ω, hω0, hω3, rfl, h1⟩ := exists_eq_of_mem_center hker
  apply h1
  have eui : (fun c => ρ (tv 0 1 c)) = ui := funext fun c => (hi c).1
  have evi : (fun c => ρ (tv 1 0 c)) = vi := funext fun c => (hi c).2
  have euj : (fun c => ρ (tv 1 2 c)) = uj := funext fun c => (hj c).1
  have evj : (fun c => ρ (tv 2 1 c)) = vj := funext fun c => (hj c).2
  rw [map_mul, map_hElt, map_hElt, eui, evi, euj, evj] at hg
  rcases h with ⟨hu, hv, ha⟩ | ⟨hu, hv, ha⟩
  · have hc : Commute (hElt uj vj (ω ^ 2)) (w 1) := by
      rw [eq_inv_of_mul_eq_one_right hg]
      exact (commute_hElt hu hv ω).inv_left
    have h2 := eq_one_of_adjoins ha hw (pow_ne_zero 2 hω0) hc
    rw [← hω3, pow_succ, h2, one_mul]
  · have hc : Commute (hElt ui vi ω) (w 1) := by
      rw [eq_inv_of_mul_eq_one_left hg]
      exact (commute_hElt hu hv (ω ^ 2)).inv_left
    exact eq_one_of_adjoins ha hw hω0 hc

end Torus

section SL2

variable {F : Type} [Field F]

open Matrix

theorem tv01_eq_sl2Upper (c : F) :
    (tv 0 1 c : SpecialLinearGroup (Fin 2) F) = Steinberg.sl2Upper c := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  rw [SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.coeMonoidHom_apply,
    tv_of_ne (by decide), SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Steinberg.sl2Upper]

theorem tv10_eq_sl2Lower (c : F) :
    (tv 1 0 c : SpecialLinearGroup (Fin 2) F) = Steinberg.sl2Lower c := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  rw [SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.coeMonoidHom_apply,
    tv_of_ne (by decide), SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Steinberg.sl2Lower]

theorem eq_one_of_mem_center_sl2 [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : g = 1 := by
  obtain ⟨r, hr, hg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : (r + 1) * (r + 1) = 0 := by linear_combination hr + (r + 1) * h2
  have hr1' : r = 1 := by
    rw [mul_self_eq_zero, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hr1
    exact hr1
  apply SpecialLinearGroup.coeMonoidHom_injective
  rw [SpecialLinearGroup.coeMonoidHom_apply, ← hg, hr1', map_one, map_one]

theorem injective_noncommCoprod [CharP F 2] {H : Type*} [Group H]
    {φ ψ : SpecialLinearGroup (Fin 2) F →* H} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (hc : ∀ a b, Commute (φ a) (ψ b)) :
    Function.Injective (φ.noncommCoprod ψ hc) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [MonoidHom.noncommCoprod_apply] at h
  have e : φ a = ψ b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have hb : b⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.2 fun y => hψ (by rw [map_mul, map_mul, ← e]; exact (hc a y).symm.eq)
  have hb1 : b = 1 := inv_eq_one.1 (eq_one_of_mem_center_sl2 hb)
  rw [hb1, inv_one, map_one] at e
  rw [hb1, (injective_iff_map_eq_one φ).1 hφ a e]
  rfl

end SL2

section Levis

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_sl3 [Finite F] [CharP F 2] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    (hdiv : D.divisible = ∅) {i j : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) F →* K, ∀ c, ρ (tv 0 1 c) = x (sroot i) c ∧
      ρ (tv 1 0 c) = x (-sroot i) c ∧ ρ (tv 1 2 c) = x (sroot j) c ∧
      ρ (tv 2 1 c) = x (-sroot j) c ∧ ρ (tv 0 2 c) = x (sroot i + sroot j) c ∧
      ρ (tv 2 0 c) = x (-(sroot i + sroot j)) c := by
  have hsub : pairRoots D i j ⊆ pair i j '' zA2 :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  have hroot := pair_mem_roots_A2 hcij hcji
  have hadd : ∀ z ∈ zA2, ∀ s t, x (pair i j z) (s + t) = x (pair i j z) s * x (pair i j z) t :=
    fun z hz => (hE.param _ (hroot z hz)).2.1
  have hcomm : ∀ z w, z ∈ zA2 → w ∈ zA2 → z + w ≠ 0 → z + w ∉ zA2 → ∀ s t,
      Commute (x (pair i j z) s) (x (pair i j w) t) := fun z w hz hw hzw hs s t =>
    commutatorElement_eq_one_iff_commute.1
      ((commutator_pair hE hC hij hsub hroot zA2_expPairs hz hw hzw s t).2 hs)
  have hrel : ∀ z w u, z ∈ zA2 → w ∈ zA2 → z + w = u → u ∈ zA2 → w - z ∉ zA2 → ∀ s t,
      ⁅x (pair i j z) s, x (pair i j w) t⁆ = x (pair i j u) (s * t) := by
    rintro z w u hz hw rfl hu hd s t
    exact (commutator_pair hE hC hij hsub hroot zA2_expPairs hz hw
      (fun h => by rw [h] at hu; exact absurd hu (by decide)) s t).1 hu hd
  obtain ⟨ρ, hρ⟩ := ARS.FrameSL3.exists_hom_of_steinberg
    (ARS.FrameSL3.fam_add (hadd (1, 0) (by decide)) (hadd (0, 1) (by decide))
      (hadd (1, 1) (by decide)) (hadd (-1, 0) (by decide)) (hadd (0, -1) (by decide))
      (hadd (-1, -1) (by decide)))
    (ARS.FrameSL3.fam_comm (hadd (1, 0) (by decide)) (hadd (0, 1) (by decide))
      (hadd (1, 1) (by decide)) (hadd (-1, 0) (by decide)) (hadd (0, -1) (by decide))
      (hadd (-1, -1) (by decide))
      (hcomm _ _ (by decide) (by decide) (by decide) (by decide))
      (hcomm _ _ (by decide) (by decide) (by decide) (by decide))
      (hcomm _ _ (by decide) (by decide) (by decide) (by decide))
      (hcomm _ _ (by decide) (by decide) (by decide) (by decide))
      (hcomm _ _ (by decide) (by decide) (by decide) (by decide))
      (hcomm _ _ (by decide) (by decide) (by decide) (by decide))
      (hrel _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hrel _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hrel _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hrel _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hrel _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hrel _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)))
  refine ⟨ρ, fun c => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tv_of_ne (by decide), hρ, ← pair_one_zero i j]; rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_neg_one_zero i j]; rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_zero_one i j]; rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_zero_neg_one i j]; rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_one_one i j]; rfl
  · rw [tv_of_ne (by decide), hρ, ← pair_neg_one_neg_one i j]; rfl

theorem commute_of_cartan_eq_zero [CharP F 2] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    (hdiv : D.divisible = ∅) {i j : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = 0)
    (hcji : D.cartan j i = 0) (s t : F) :
    Commute (x (sroot i) s) (x (sroot j) t) ∧ Commute (x (sroot i) s) (x (-sroot j) t) ∧
      Commute (x (-sroot i) s) (x (sroot j) t) ∧ Commute (x (-sroot i) s) (x (-sroot j) t) := by
  have hsub : pairRoots D i j ⊆ pair i j '' zA1A1 :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  have hcomm : ∀ z w, z ∈ zA1A1 → w ∈ zA1A1 → z + w ≠ 0 → z + w ∉ zA1A1 →
      Commute (x (pair i j z) s) (x (pair i j w) t) := fun z w hz hw hzw hs =>
    commutatorElement_eq_one_iff_commute.1 ((commutator_pair hE hC hij hsub
      (pair_mem_roots_A1A1 i j) zA1A1_expPairs hz hw hzw s t).2 hs)
  rw [← pair_neg_one_zero i j, ← pair_zero_neg_one i j, ← pair_one_zero i j, ← pair_zero_one i j]
  exact ⟨hcomm _ _ (by decide) (by decide) (by decide) (by decide),
    hcomm _ _ (by decide) (by decide) (by decide) (by decide),
    hcomm _ _ (by decide) (by decide) (by decide) (by decide),
    hcomm _ _ (by decide) (by decide) (by decide) (by decide)⟩

end Levis

end LevisExtras

open LevisExtras

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem simplyLacedLevis_of_chevalleyExtras [Finite F] [CharP F 2]
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    {adj : Fin D.rank → Fin D.rank → Prop} (hasymm : ∀ i j, adj i j → ¬ adj j i)
    (hadj : ∀ i j, adj i j → D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hnadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → D.cartan i j = 0 ∧ D.cartan j i = 0)
    (hnb : ∀ i j, adj i j → ∃ k, k ≠ i ∧ k ≠ j ∧
      ((adj j k ∨ adj k j) ∧ ¬ adj i k ∧ ¬ adj k i ∨
        (adj i k ∨ adj k i) ∧ ¬ adj j k ∧ ¬ adj k j)) :
    SimplyLacedLevis D F adj x := by
  have hne : ∀ i j, adj i j → i ≠ j := fun i j h e => by
    subst e
    have := (hadj i i h).1
    rw [D.isFiniteType.apply_self] at this
    norm_num at this
  have hsl3 := fun i j (h : adj i j) =>
    exists_sl3 hE hC hdiv (hne i j h) (hadj i j h).1 (hadj i j h).2
  have hcomm := fun i j (hij : i ≠ j) (h1 : ¬ adj i j) (h2 : ¬ adj j i) =>
    commute_of_cartan_eq_zero hE hC hdiv hij (hnadj i j hij h1 h2).1 (hnadj i j hij h1 h2).2
  have hinj : ∀ k, Function.Injective (x (sroot k)) := fun k =>
    (hE.param _ (single_mem_roots k)).2.2
  have hnt : ∀ k, ∃ c, x (sroot k) c ≠ 1 := fun k => ⟨1, fun h => one_ne_zero
    (hinj k (h.trans (x_zero hE (single_mem_roots k)).symm))⟩
  have hadjoins : ∀ l k, (adj l k ∨ adj k l) →
      Adjoins (x (sroot l)) (x (-sroot l)) (x (sroot k)) := by
    rintro l k (h | h)
    · obtain ⟨ρ, hρ⟩ := hsl3 l k h
      exact Or.inl ⟨ρ, fun c => ⟨(hρ c).1, (hρ c).2.1, (hρ c).2.2.1⟩⟩
    · obtain ⟨ρ, hρ⟩ := hsl3 k l h
      exact Or.inr ⟨ρ, fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1, (hρ c).1⟩⟩
  refine
    { asymm := hasymm
      ne := hne
      mem := fun γ hγ c => ((hE.param γ hγ).1 _).2 ⟨c, rfl⟩
      surj := fun γ hγ g hg => ((hE.param γ hγ).1 g).1 hg
      pairRoots_adj := fun i j h => ?_
      pairRoots_nonadj := fun i j h1 h2 => ?_
      sl3 := fun i j h => ?_
      sl2 := fun k => ?_
      sl2sl2 := fun i j hij h1 h2 => ?_ }
  · intro γ hγ
    obtain ⟨z, hz, rfl⟩ := pairRoots_subset_pair hdiv (Z := zA2) (by decide) (by decide)
      (by rw [(hadj i j h).1]; decide) (by rw [(hadj i j h).2]; decide) hγ
    rw [Finset.mem_coe] at hz
    simp only [zA2, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [pair_one_zero]; simp
    · rw [pair_neg_one_zero]; simp
    · rw [pair_zero_one]; simp
    · rw [pair_zero_neg_one]; simp
    · rw [pair_one_one]; simp
    · rw [pair_neg_one_neg_one]; simp
  · by_cases hij : i = j
    · subst hij
      refine (pairRoots_subset hdiv (S := {sroot i, -sroot i}) (by simp) (by simp) ?_ ?_).trans
        (by intro γ hγ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢; tauto) <;>
      · intro γ hγ
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
        rcases hγ with rfl | rfl
        · right
          exact reflection_single_self (D.isFiniteType.apply_self i)
        · left
          rw [map_neg, reflection_single_self (D.isFiniteType.apply_self i), neg_neg]
    · intro γ hγ
      obtain ⟨z, hz, rfl⟩ := pairRoots_subset_pair hdiv (Z := zA1A1) (by decide) (by decide)
        (by rw [(hnadj i j hij h1 h2).1]; decide) (by rw [(hnadj i j hij h1 h2).2]; decide) hγ
      rw [Finset.mem_coe] at hz
      simp only [zA1A1, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · rw [pair_one_zero]; simp
      · rw [pair_neg_one_zero]; simp
      · rw [pair_zero_one]; simp
      · rw [pair_zero_neg_one]; simp
  · obtain ⟨ρ, hρ⟩ := hsl3 i j h
    refine ⟨ρ, ?_, hρ⟩
    obtain ⟨k, hki, hkj, hk | hk⟩ := hnb i j h
    · obtain ⟨hjk, hik, hki'⟩ := hk
      have hc := hcomm i k (Ne.symm hki) hik hki'
      exact injective_of_adjoins (fun c => ⟨(hρ c).1, (hρ c).2.1⟩)
        (fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1⟩) (hnt i) (hinj k)
        (Or.inl ⟨fun c => (hc c 1).1, fun c => (hc c 1).2.2.1, hadjoins j k hjk⟩)
    · obtain ⟨hik, hjk, hkj'⟩ := hk
      have hc := hcomm j k (Ne.symm hkj) hjk hkj'
      exact injective_of_adjoins (fun c => ⟨(hρ c).1, (hρ c).2.1⟩)
        (fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1⟩) (hnt i) (hinj k)
        (Or.inr ⟨fun c => (hc c 1).1, fun c => (hc c 1).2.2.1, hadjoins i k hik⟩)
  · obtain ⟨φ, hφ, hup, hlow⟩ := hE.rankOne k
    exact ⟨φ, hφ, fun c => ⟨by rw [tv01_eq_sl2Upper, hup], by rw [tv10_eq_sl2Lower, hlow]⟩⟩
  · obtain ⟨φ, hφ, hupφ, hlowφ⟩ := hE.rankOne i
    obtain ⟨ψ, hψ, hupψ, hlowψ⟩ := hE.rankOne j
    have hc : ∀ a b, Commute (φ a) (ψ b) := commute_of_tv φ ψ fun c d => by
      rw [tv01_eq_sl2Upper, tv10_eq_sl2Lower, tv01_eq_sl2Upper, tv10_eq_sl2Lower, hupφ, hlowφ,
        hupψ, hlowψ]
      exact hcomm i j hij h1 h2 c d
    refine ⟨φ.noncommCoprod ψ hc, injective_noncommCoprod hφ hψ hc, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, tv01_eq_sl2Upper, hupφ]
    · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, tv10_eq_sl2Lower, hlowφ]
    · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, tv01_eq_sl2Upper, hupψ]
    · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, tv10_eq_sl2Lower, hlowψ]

end CFSG.Timmesfeld
