module

public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Background.E1Util
public import CFSG.Quasithin.Vol2.Ch10SecD211D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', a'⁻¹ * b * a' * b', ?_, by group⟩
        refine B.mul_mem ?_ hb'
        have := (Subgroup.mem_normalizer_iff.mp (hAB (A.inv_mem ha')) b).mp hb
        simpa using this
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hAB ha) b⁻¹).mp (B.inv_mem hb) }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

variable [Finite G]

omit [Finite G] in
theorem conjugate_mem_cComp {X L : Subgroup G} (hL : L ∈ cComp X) {s : G} (hs : s ∈ X) :
    CFSG.conjugate L s ∈ cComp X := by
  have h1 := cComp_map_mulEquiv (MulAut.conj s⁻¹) hL
  have h2 : X.map (MulAut.conj s⁻¹).toMonoidHom = X :=
    SecA.conjugate_eq_self_iff.mpr (Subgroup.le_normalizer hs)
  rw [h2] at h1
  exact h1

theorem commutator_cComp_le (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X K₁ : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G)) :
    ⁅K₁, CFSG.conjugate K₁ s⁆ ≤ pCoreOf 2 K₁ ⊓ pCoreOf 2 (CFSG.conjugate K₁ s) :=
  (Vol2Native.lemma_1_2_1_two hK h37 hX hK₁ (conjugate_mem_cComp hK₁ hs)
    (SecA.ne_conjugate hsn)).1

omit [Finite G] in
theorem mem_normalizer_pCoreOf {N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    g ∈ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N hg

theorem conjugate_sq_eq (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat) {X K₁ : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hsK : s ∈ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G)) :
    CFSG.conjugate (CFSG.conjugate K₁ s) s = K₁ := by
  set K₂ := CFSG.conjugate K₁ s with hK₂def
  set K₃ := CFSG.conjugate K₂ s with hK₃def
  have hK₂ : K₂ ∈ cComp X := conjugate_mem_cComp hK₁ hs
  have hK₃ : K₃ ∈ cComp X := conjugate_mem_cComp hK₂ hs
  have hKs : CFSG.conjugate (K₁ ⊔ K₂) s = K₁ ⊔ K₂ := SecA.conjugate_eq_self_iff.mpr hsK
  have hK₂le : K₂ ≤ K₁ ⊔ K₂ := le_sup_right
  have hK₃le : K₃ ≤ K₁ ⊔ K₂ := by
    rw [← hKs]
    exact SecA.conjugate_mono hK₂le s
  by_contra hne
  have hne2 : K₃ ≠ K₂ := by
    intro h32
    apply hsn
    rw [← SecA.conjugate_eq_self_iff]
    have h1 : CFSG.conjugate K₂ s = CFSG.conjugate K₁ s := h32
    have h2 := congrArg (fun Y => CFSG.conjugate Y s⁻¹) h1
    simp only [SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one] at h2
    exact h2
  have h31 := (Vol2Native.lemma_1_2_1_two hK h37 hX hK₃ hK₁ hne).1
  have h32 := (Vol2Native.lemma_1_2_1_two hK h37 hX hK₃ hK₂ hne2).1
  have hN : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₃ : Set G) :=
    sup_le (le_normalizer_of_mem_cComp hK₃ hK₁) (le_normalizer_of_mem_cComp hK₃ hK₂)
  have hcomm : ⁅K₃, K₁ ⊔ K₂⁆ ≤ pCoreOf 2 K₃ := by
    rw [SecA.commutator_sup_left_of_le hK₃le le_sup_left le_sup_right hN]
    exact sup_le (h31.trans inf_le_left) (h32.trans inf_le_left)
  have hle : K₃ ≤ pCoreOf 2 K₃ := by
    calc K₃ = ⁅K₃, K₃⁆ := (perfect_of_mem_cComp hK₃).symm
      _ ≤ ⁅K₃, K₁ ⊔ K₂⁆ := Subgroup.commutator_mono le_rfl hK₃le
      _ ≤ pCoreOf 2 K₃ := hcomm
  have h2 : IsPGroup 2 K₃ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₃).to_le hle
  exact not_isSolvable_of_mem_cComp hK₃ (E1.isSolvable_of_isPGroup_two h2)

theorem isSolvable_of_inf_sup (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat)
    {X K₁ : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ X)
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hsK : s ∈ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G))
    {Y : Subgroup G} (hYK : Y ≤ K₁ ⊔ CFSG.conjugate K₁ s)
    (hsY : s ∈ Subgroup.normalizer (Y : Set G))
    (hP : Group.IsSolvable ↥(K₁ ⊓ (Y ⊔ CFSG.conjugate K₁ s))) : Group.IsSolvable ↥Y := by
  set K₂ := CFSG.conjugate K₁ s with hK₂def
  have hK₂ : K₂ ∈ cComp X := conjugate_mem_cComp hK₁ hs
  have h12 : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := le_normalizer_of_mem_cComp hK₂ hK₁
  have h21 : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := le_normalizer_of_mem_cComp hK₁ hK₂
  have hsq := conjugate_sq_eq hK h37 hX hK₁ hs hsn hsK
  have hcomm := commutator_cComp_le hK h37 hX hK₁ hs hsn
  set P₁ := K₁ ⊓ (Y ⊔ K₂) with hP₁
  set P₂ := K₂ ⊓ (Y ⊔ K₁) with hP₂
  have hP₂eq : P₂ = CFSG.conjugate P₁ s := by
    rw [hP₁, hP₂, SecA.conjugate_eq_map, Subgroup.map_inf _ _ _ (MulAut.conj s⁻¹).injective,
      Subgroup.map_sup, ← SecA.conjugate_eq_map, ← SecA.conjugate_eq_map,
      ← SecA.conjugate_eq_map, SecA.conjugate_eq_self_iff.mpr hsY, hsq]
  have hP₂s : Group.IsSolvable ↥P₂ := by
    rw [hP₂eq, SecA.conjugate_eq_map]
    have : Group.IsSolvable ↥P₁ := hP
    exact Group.isSolvable_of_surjective
      (f := (P₁.equivMapOfInjective _ (MulAut.conj s⁻¹).injective).toMonoidHom)
      (MulEquiv.surjective _)
  set N := pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ with hN
  have hN2 : IsPGroup 2 N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁).to_sup_of_normal_right'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₂)
      ((Subgroup.map_subtype_le _).trans (h12.trans fun g hg => mem_normalizer_pCoreOf hg))
  have hNs : Group.IsSolvable ↥N := E1.isSolvable_of_isPGroup_two hN2
  have hK₁N : K₁ ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    mem_normalizer_sup (mem_normalizer_pCoreOf (Subgroup.le_normalizer hg))
      (mem_normalizer_pCoreOf (h12 hg))
  have hK₂N : K₂ ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    mem_normalizer_sup (mem_normalizer_pCoreOf (h21 hg))
      (mem_normalizer_pCoreOf (Subgroup.le_normalizer hg))
  have hNP₂ : Group.IsSolvable ↥(N ⊔ P₂) :=
    A3.isSolvable_sup_of_le_normalizer (inf_le_left.trans hK₂N)
  have hP₁N : P₁ ≤ Subgroup.normalizer ((N ⊔ P₂ : Subgroup G) : Set G) := by
    intro g hg
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : N ⊔ P₂ ≤ (N ⊔ P₂).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hK₁N hg.1) y).mp hy)
      · change g * y * g⁻¹ ∈ N ⊔ P₂
        have hc : g * y * g⁻¹ * y⁻¹ ∈ N := by
          have := Subgroup.commutator_mem_commutator hg.1 hy.1
          rw [commutatorElement_def] at this
          exact Subgroup.mem_sup_left ((hcomm this).1)
        have e : g * y * g⁻¹ = g * y * g⁻¹ * y⁻¹ * y := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hy)
    exact hle hx
  have hall : Group.IsSolvable ↥((N ⊔ P₂) ⊔ P₁) := A3.isSolvable_sup_of_le_normalizer hP₁N
  have hYP : Y ≤ (N ⊔ P₂) ⊔ P₁ := by
    intro y hy
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer h12 (hYK hy)
    have hk₁P : k₁ ∈ P₁ := by
      refine ⟨hk₁, ?_⟩
      have e : k₁ = k₁ * k₂ * k₂⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (K₂.inv_mem hk₂))
    have hk₂P : k₂ ∈ P₂ := by
      refine ⟨hk₂, ?_⟩
      have e : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (K₁.inv_mem hk₁)) (Subgroup.mem_sup_left hy)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk₁P)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hk₂P))
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYP)

end CFSG.Quasithin.Vol2.Ch10.SecD
