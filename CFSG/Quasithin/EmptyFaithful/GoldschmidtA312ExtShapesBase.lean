module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin.A312ExtShapes

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

variable {G : Type} [Group G] [Finite G]

theorem eq_of_perfect_simple_quotient {T B Z A : Subgroup G} (hB : B ∈ lFamily T)
    (hZ : B ⊔ T = Z) (hAZ : A ≤ Z) (hcomm : ⁅Z, Z⁆ ≤ A) (hperf : ⁅A, A⁆ = A)
    {H : Type} [Group H] [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a)
    (f : ↥A →* H) (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker) : B = A := by
  have hpc : perfectCore (B ⊔ T) = A := by
    rw [hZ]
    exact le_antisymm ((Seven.perfectCore_le_commutator Z).trans hcomm)
      (le_perfectCore_of_perfect hAZ hperf)
  let eP : ↥(perfectCore (B ⊔ T)) ≃* ↥A := MulEquiv.subgroupCongr hpc
  let g : ↥(perfectCore (B ⊔ T)) →* H := f.comp eP.toMonoidHom
  have hg : Function.Surjective g := hf.comp eP.surjective
  have hsolv : Group.IsSolvable g.ker := by
    let φ : g.ker →* f.ker :=
      (eP.toMonoidHom.comp g.ker.subtype).codRestrict f.ker fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        exact hx
    have hφ : Function.Injective φ := fun x y hxy =>
      Subtype.ext (eP.injective (congrArg Subtype.val hxy))
    exact Group.isSolvable_of_isSolvable_injective hφ
  rw [lFamily_eq_perfectCore hB hnab g hg hsolv, hpc]

omit [Finite G] in
theorem isExt_of_eq_subgroup {A B : Subgroup G} (h : A = B)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hPY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (hA : IsExt ↥A PV PY) : IsExt ↥B PV PY :=
  A312.isExt_of_mulEquiv hPV hPY (MulEquiv.subgroupCongr h) hA

theorem isExt_of_perfect_simple_quotient {T B Z A : Subgroup G} (hB : B ∈ lFamily T)
    (hZ : B ⊔ T = Z) (hAZ : A ≤ Z) (hcomm : ⁅Z, Z⁆ ≤ A) (hperf : ⁅A, A⁆ = A)
    {H : Type} [Group H] [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a)
    (f : ↥A →* H) (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hPY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (V : Subgroup ↥A) [V.Normal] (hV : PV ↥V) (hQ : PY (↥A ⧸ V)) : IsExt ↥B PV PY :=
  isExt_of_eq_subgroup (eq_of_perfect_simple_quotient hB hZ hAZ hcomm hperf hnab f hf hker).symm
    hPV hPY ⟨V, inferInstance, hV, hQ⟩

end CFSG.Quasithin.A312ExtShapes
