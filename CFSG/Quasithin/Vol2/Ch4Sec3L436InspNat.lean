module

public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin.H13.Ch4.G2A

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem false_of_natural_comm_inf {G : Type} [Group G] {A V Z Z' : Subgroup G}
    {N : Subgroup ↥A} {F : Type} [Field F]
    (hnat : IsNaturalSection A V (V ⊓ Z') N (StatedSL 2 F)) (hZ : Z ≤ Z')
    (hc : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ Z) : False := by
  obtain ⟨hAV, α, hα, -, β, hβ, hβker, hequiv⟩ := hnat
  have hfix : ∀ (a : ↥A) (v : ↥V), Multiplicative.toAdd (β v) =
      ((α a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β v)) := by
    intro a v
    have hw : (a : G) * v * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) v).mp v.2
    have h1 := hequiv a v ⟨_, hw⟩ rfl
    have hk : (⟨_, hw⟩ : ↥V) * v⁻¹ ∈ β.ker := by
      rw [hβker, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr ⟨V.mul_mem hw (V.inv_mem v.2), hZ (hc a a.2 v v.2)⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    rw [hk] at h1
    exact h1
  have hα1 : ∀ a : ↥A, α a = 1 := by
    intro a
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro j
    obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd (Pi.single j 1))
    have h1 := hfix a v
    rw [hv, toAdd_ofAdd] at h1
    rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
    exact h1.symm
  have hdet : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two]
  let M1 : Matrix.GeneralLinearGroup (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _
    (by rw [hdet]; exact one_ne_zero)
  obtain ⟨a, ha⟩ := hα ⟨M1, Subgroup.subset_closure hdet⟩
  rw [hα1 a] at ha
  have h := congrArg (fun M : ↥(StatedSL 2 F) =>
    ((M : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1) ha
  simp [M1] at h

end CFSG.Quasithin.H13.Ch4.G2A
