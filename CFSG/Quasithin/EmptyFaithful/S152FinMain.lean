module

public import CFSG.Quasithin.EmptyFaithful.S151NotFF
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

@[expose] def Input152Kernel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → IsSylowTwoOf T H →
      Concl319 T M (V154 T Mc M) H True →
      Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) →
        H ⊓ Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G) ≤ pCoreOf 2 H

@[expose] def Input152Transvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → IsSylowTwoOf T H →
      Concl319 T M (V154 T Mc M) H True →
      Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) →
        ∀ X : Subgroup G, X ≤ H → IsElemAbelian 2 X →
          (Subgroup.centralizer (X : Set G)).relIndex (conjClosure (V154 T Mc M) H) ≤ 8 →
            (pCoreOf 2 H).relIndex X ≤ 2

namespace S152Fin

variable {G : Type} [Group G] [Finite G]

theorem not_isFFModule_of_lemma1518 {T Mc M : Subgroup G} (hV : IsElemAbelian 2 (V154 T Mc M))
    (h : Lemma1518Concl T Mc M) :
    ¬ @IsFFModule (V154 T Mc M) (commGroupOfElemAbelian hV) (autOn M (V154 T Mc M)) :=
  CFSG.Quasithin.S151.not_isFFModule_of_lemma1518 hV h

omit [Finite G] in
theorem commutator_le_of_le_normalizer {V X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) : ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have h1 : x * v⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hX hx) v⁻¹).mp (V.inv_mem hv)
  have : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
  rw [commutatorElement_def, this]
  exact V.mul_mem hv h1

end S152Fin

end CFSG.Quasithin
