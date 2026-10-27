module

public import CFSG.Quasithin.MS93.S4ASL3

public section

namespace CFSG.Quasithin.MS93.S46.I467

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]
  {ψ : ↥K →* ↥(StatedSL 3 F)} (hψ : IsSumOfNaturalModulesVia K V Z ψ false 1)
include hψ

@[expose] noncomputable def qVec (v : ↥V) : Fin 3 → F :=
  Multiplicative.toAdd (Classical.choose hψ.2.2 v) 0

theorem qVec_mul (v w : ↥V) : qVec hψ (v * w) = qVec hψ v + qVec hψ w := by
  simp [qVec]

theorem qVec_one : qVec hψ 1 = 0 := by
  simp [qVec]

theorem qVec_inv (v : ↥V) : qVec hψ v⁻¹ = - qVec hψ v := by
  simp [qVec]

theorem qVec_eq_zero_iff (v : ↥V) : qVec hψ v = 0 ↔ (v : G) ∈ Z := by
  have hk := (Classical.choose_spec hψ.2.2).2.1
  constructor
  · intro h0
    have h1 : Classical.choose hψ.2.2 v = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0]
      exact h0
    have hv : v ∈ (Classical.choose hψ.2.2).ker := h1
    rw [hk, Subgroup.mem_subgroupOf] at hv
    exact hv
  · intro hv
    have h1 : v ∈ (Classical.choose hψ.2.2).ker := by
      rw [hk, Subgroup.mem_subgroupOf]
      exact hv
    rw [MonoidHom.mem_ker] at h1
    show Multiplicative.toAdd (Classical.choose hψ.2.2 v) 0 = 0
    rw [h1]
    rfl

theorem qVec_surjective : Function.Surjective (qVec hψ) := by
  intro x
  obtain ⟨v, hv⟩ := (Classical.choose_spec hψ.2.2).1 (Multiplicative.ofAdd fun _ => x)
  refine ⟨v, ?_⟩
  show Multiplicative.toAdd (Classical.choose hψ.2.2 v) 0 = x
  rw [hv]
  rfl

theorem qVec_conj (a : ↥K) (u v : ↥V) (huv : (v : G) = a * u * a⁻¹) :
    qVec hψ v = ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ qVec hψ u := by
  have := (Classical.choose_spec hψ.2.2).2.2 a u v huv 0
  rw [toSL3_mat]
  simpa [qVec, moduleAct] using this

theorem commutator_mem_of_natural (v : ↥V) (a : ↥K) : ⁅(v : G), (a : G)⁆ ∈ V := by
  have hmem : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hψ.1 a.2) v).mp v.2
  rw [commutatorElement_def]
  have e : (v : G) * a * (v : G)⁻¹ * (a : G)⁻¹ = v * ((a : G) * v * (a : G)⁻¹)⁻¹ := by group
  rw [e]
  exact V.mul_mem v.2 (V.inv_mem hmem)

theorem qVec_commutator (v : ↥V) (a : ↥K) :
    qVec hψ ⟨⁅(v : G), (a : G)⁆, commutator_mem_of_natural hψ v a⟩ =
      qVec hψ v - ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ qVec hψ v := by
  have hmem : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hψ.1 a.2) v).mp v.2
  have e : (⟨⁅(v : G), (a : G)⁆, commutator_mem_of_natural hψ v a⟩ : ↥V) =
      v * (⟨_, hmem⟩ : ↥V)⁻¹ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, qVec_mul, qVec_inv, qVec_conj hψ a v ⟨_, hmem⟩ rfl, sub_eq_add_neg]

theorem qVec_mem_fixN {A : Subgroup G} (n : ↥V) (hn : ∀ a : ↥K, (a : G) ∈ A →
    ⁅(n : G), (a : G)⁆ ∈ Z) : qVec hψ n ∈ fixN (natImage ψ A) := by
  intro g hg
  obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
  have h1 := qVec_commutator hψ n a
  rw [(qVec_eq_zero_iff hψ _).mpr (hn a haA)] at h1
  exact (sub_eq_zero.mp h1.symm).symm

theorem exists_qVec_eq_of_mem_commN {A W : Subgroup G}
    (hW : ∀ a : ↥K, (a : G) ∈ A → ∀ v : ↥V, ⁅(v : G), (a : G)⁆ ∈ W) {x : Fin 3 → F}
    (hx : x ∈ commN (natImage ψ A)) : ∃ w : ↥V, (w : G) ∈ W ∧ qVec hψ w = x := by
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ w : ↥V, (w : G) ∈ W ∧ qVec hψ w = x}
      add_mem' := by
        rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w * w', W.mul_mem hw hw', qVec_mul hψ w w'⟩
      zero_mem' := ⟨1, W.one_mem, qVec_one hψ⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, W.inv_mem hw, qVec_inv hψ w⟩ }
  let Sm : Submodule F (Fin 3 → F) :=
    { carrier := {x | ∀ c : F, c • x ∈ S}
      add_mem' := fun {x y} hx hy c => by
        rw [smul_add]
        exact S.add_mem (hx c) (hy c)
      zero_mem' := fun c => by
        rw [smul_zero]
        exact S.zero_mem
      smul_mem' := fun c x hx c' => by
        rw [smul_smul]
        exact hx _ }
  have hgen : commN (natImage ψ A) ≤ Sm := by
    rw [commN, Submodule.span_le]
    rintro _ ⟨g, hg, y, rfl⟩ c
    obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
    obtain ⟨v, hv⟩ := qVec_surjective hψ (c • y)
    refine ⟨(⟨_, commutator_mem_of_natural hψ v a⟩ : ↥V)⁻¹, W.inv_mem (hW a haA v), ?_⟩
    rw [qVec_inv, qVec_commutator, hv, Matrix.mulVec_smul, smul_sub]
    abel
  have := hgen hx 1
  rwa [one_smul] at this

theorem mem_of_forall_commutator_mem (n : ↥V)
    (hn : ∀ γ : SL3 F, ∃ a : ↥K, toSL3 ψ a = γ ∧ ⁅(n : G), (a : G)⁆ ∈ Z) : (n : G) ∈ Z := by
  rw [← qVec_eq_zero_iff hψ]
  have hfix : ∀ i j : Fin 3, i ≠ j → qVec hψ n ∈ fixN (rootGroup i j : Subgroup (SL3 F)) := by
    rintro i j - _ ⟨c, rfl⟩
    obtain ⟨a, ha, hZ⟩ := hn (rootElt i j c)
    have h1 := qVec_commutator hψ n a
    rw [(qVec_eq_zero_iff hψ _).mpr hZ, ha] at h1
    exact (sub_eq_zero.mp h1.symm).symm
  have h0 := hfix 1 0 (by decide)
  have h1 := hfix 0 1 (by decide)
  have h2 := hfix 0 2 (by decide)
  rw [fixN_rootGroup (by decide)] at h0 h1 h2
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem toSL3_eq_one_of_commutator_mem {a : ↥K} (ha : ∀ v : ↥V, ⁅(v : G), (a : G)⁆ ∈ Z) :
    toSL3 ψ a = 1 := by
  apply eq_one_of_mulVec_eq_self
  intro x
  obtain ⟨v, rfl⟩ := qVec_surjective hψ x
  have h1 := qVec_commutator hψ v a
  rw [(qVec_eq_zero_iff hψ _).mpr (ha v)] at h1
  exact (sub_eq_zero.mp h1.symm).symm

end CFSG.Quasithin.MS93.S46.I467
