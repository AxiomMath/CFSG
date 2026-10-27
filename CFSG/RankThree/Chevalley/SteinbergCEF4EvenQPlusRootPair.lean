module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6
open scoped Pointwise commutatorElement

namespace EvenF4QPlus

section Weyl

variable {k : Type} [Field k]

theorem F4_rootCharStabilizer_le_kernelReflectionGroup
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {a : Fin Tag.F4.rank → kˣ} (hap : a ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hai : ∀ j, a j ^ p = 1 := fun j => by simpa using congrFun hap j
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha1
  have hζ : orderOf (a i) = p := orderOf_eq_prime (hai i) hi
  choose x hx using fun j => exists_pow_val_eq_of_pow_eq_one hζ (hai j)
  have hax : ∀ v, rootChar a v = a i ^ (charVal x v).val := fun v => by
    rw [← rootChar_pow_val_eq hζ x v]
    congr 1
    exact (funext hx).symm
  intro w hw
  have hw' : ∀ v, rootChar a (w • v) = rootChar a v := hw
  have hwx : w ∈ charStabilizer x := fun v => by
    have h1 := hw' v
    rw [hax, hax] at h1
    exact eq_of_pow_val_eq_pow_val hζ h1
  rw [charStabilizer_eq_closure hp3 x] at hwx
  refine (Subgroup.closure_le _).2 ?_ hwx
  rintro _ ⟨β, hβ, rfl⟩
  have hβa : β ∈ rootCharKernel a := ⟨hβ.1, by rw [hax, hβ.2, ZMod.val_zero, pow_zero]⟩
  obtain ⟨w', j, hw'j⟩ := isRoot_iff_exists_smul_single.1 hβ.1
  rw [rootReflection_eq_conj hw'j]
  exact Subgroup.subset_closure ⟨w', j, by rw [hw'j]; exact hβa, rfl⟩

end Weyl

section Transport

variable {G G' : Type*} [Group G] [Group G'] {φ : G →* G'}

theorem map_inf_centralizer_of_injective (hφ : Function.Injective φ) (A : Subgroup G)
    (S : Set G) :
    (A ⊓ Subgroup.centralizer S).map φ = A.map φ ⊓ Subgroup.centralizer (φ '' S) := by
  ext y
  constructor
  · rintro ⟨y₀, ⟨hA, hC⟩, rfl⟩
    refine ⟨⟨y₀, hA, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hC s hs]
  · rintro ⟨⟨y₀, hA, rfl⟩, hC⟩
    refine ⟨y₀, ⟨hA, Subgroup.mem_centralizer_iff.2 fun s hs => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hC _ ⟨s, hs, rfl⟩

theorem map_map_center_subtype_of_injective (hφ : Function.Injective φ) (D : Subgroup G) :
    ((Subgroup.center D).map D.subtype).map φ =
      (Subgroup.center (D.map φ)).map (D.map φ).subtype := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨φ z, ⟨z, z.2, rfl⟩⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext ?_, rfl⟩
    obtain ⟨_, ⟨w₀, hw₀, rfl⟩⟩ := w
    change φ w₀ * φ z = φ z * φ w₀
    rw [← map_mul, ← map_mul]
    exact congrArg (fun t : D => φ t) (Subgroup.mem_center_iff.1 hz ⟨w₀, hw₀⟩)
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨_, ⟨w₀, hw₀, rfl⟩⟩ := w
    refine ⟨w₀, ⟨⟨w₀, hw₀⟩, Subgroup.mem_center_iff.2 fun t => Subtype.ext (hφ ?_), rfl⟩, rfl⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨φ t, ⟨t, t.2, rfl⟩⟩)
    change φ t * φ w₀ = φ w₀ * φ t at h1
    change φ ((t : G) * w₀) = φ (w₀ * (t : G))
    rw [map_mul, map_mul]
    exact h1

end Transport

end EvenF4QPlus

open EvenF4QPlus

end CFSG.RankThree.Chevalley
