module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Subfunctors
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Thm41AuxBasic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_signalizers_thetaSolFun_of_solvable (hθ : NearFunctor p A θ) {Q : Subgroup G}
    (hQ : Q ∈ mhat p A θ) (hQs : Group.IsSolvable ↥Q) :
    Q ∈ signalizers p A (thetaSolFun p A θ) (NearASolvable p A) := by
  obtain ⟨hAQ, hcop, hθQ, hnear⟩ := mem_assoc_iff.mp hQ.1
  refine ⟨hAQ, hcop, fun a ha ha1 => ?_, hnear⟩
  have hDb : dsub A θ ≤ Subgroup.centralizer {a} :=
    (dsub_le_centralizer hθ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAb : A ≤ Subgroup.centralizer {a} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hθ.elemAbelian.1 hg ha)
  have hadm : Admits (dsub A θ ⊔ A) (Q ⊓ Subgroup.centralizer {a}) :=
    Admits.inf (sup_le hQ.2 hAQ) (admits_centralizer_singleton (sup_le hDb hAb))
  have hle : Q ⊓ Subgroup.centralizer {a} ≤ θ a := hθQ a ha ha1
  have hmem : Q ⊓ Subgroup.centralizer {a} ∈
      {Z | Z ∈ mhat p A θ ∧ Z ≤ θ a ∧ Group.IsSolvable Z} :=
    ⟨mem_mhat_of_le_mtil hθ.prime (apply_mem_mtil hθ ha ha1) hle hadm, hle,
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left : Q ⊓ Subgroup.centralizer {a} ≤ Q))⟩
  exact le_iSup₂ (f := fun Z (_ : Z ∈ {Z | Z ∈ mhat p A θ ∧ Z ≤ θ a ∧ Group.IsSolvable Z}) => Z)
    _ hmem

theorem exists_ssol
    (hθ : NearFunctor p A θ) (hrank : p ^ 3 ≤ Nat.card A) :
    ∃ S : Subgroup G, S ∈ mhat p A θ ∧ Group.IsSolvable ↥S ∧
      ∀ Q ∈ mhat p A θ, Group.IsSolvable ↥Q → Q ≤ S := by
  obtain ⟨S, hS, hmax, hSsol⟩ := thetaSolFun_complete hθ hrank
  have hSassoc : S ∈ assoc p A θ :=
    ⟨hS.1, hS.2.1, fun a ha ha1 => (hS.2.2.1 a ha ha1).trans (thetaSol_le (θ a)), hS.2.2.2⟩
  have hDS : Admits (dsub A θ) S := by
    intro d hd
    have hdC : d ∈ Subgroup.centralizer (A : Set G) := dsub_le_centralizer hθ hd
    have hdA : d ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.centralizer_le_normalizer _ hdC
    set S' : Subgroup G := S.map ((MulAut.conj d : G ≃* G) : G →* G) with hS'
    have hAS' : Admits A S' :=
      (Thm41Aux.map_conj_mem_of_admits (T := ⊤) (M := S) hdA
        (Subgroup.mem_normalizer_iff.mpr fun h => by simp) ⟨le_top, hS.1⟩).2
    have hcard : Nat.card S' = Nat.card S :=
      Subgroup.card_map_of_injective (MulAut.conj d : G ≃* G).injective
    have hcop' : Nat.Coprime p (Nat.card S') := by
      rw [hcard]
      exact hS.2.1
    have hS'sol : Group.IsSolvable ↥S' := by
      have := hSsol
      exact Group.isSolvable_of_surjective
        (MonoidHom.subgroupMap_surjective ((MulAut.conj d : G ≃* G) : G →* G) S)
    have hS'mem : S' ∈ signalizers p A (thetaSolFun p A θ) (NearASolvable p A) := by
      refine ⟨hAS', hcop', fun a ha ha1 x hx => ?_, nearASolvable_of_isSolvable hS'sol hcop'⟩
      obtain ⟨hxS', hxa⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨s, hs, rfl⟩ := hxS'
      have hda : Commute d a := (Subgroup.mem_centralizer_iff.mp hdC a ha).symm
      have hax : Commute (d * s * d⁻¹) a := Subgroup.mem_centralizer_singleton_iff.mp hxa
      have hsa : s ∈ Subgroup.centralizer {a} := by
        have hcs : Commute (d⁻¹ * (d * s * d⁻¹) * d) a :=
          ((hda.inv_left).mul_left hax).mul_left hda
        have hs_eq : d⁻¹ * (d * s * d⁻¹) * d = s := by group
        rw [hs_eq] at hcs
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcs
      have hsS : s ∈ thetaSolFun p A θ a := hS.2.2.1 a ha ha1 ⟨hs, hsa⟩
      have hdn : d ∈ Subgroup.normalizer (thetaSol p A θ (θ a) : Set G) :=
        admits_thetaSol (θ a) (Subgroup.mem_sup_left hd)
      exact (Subgroup.mem_normalizer_iff.mp hdn s).mp hsS
    have hle : S' ≤ S := hmax S' hS'mem
    have heq : S' = S := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    exact Thm41Aux.mem_normalizer_of_map_conj_eq heq
  exact ⟨S, ⟨hSassoc, hDS⟩, hSsol, fun Q hQ hQs =>
    hmax Q (mem_signalizers_thetaSolFun_of_solvable hθ hQ hQs)⟩

theorem sol_mem_mhat (hθ : NearFunctor p A θ) {X : Subgroup G} (hX : X ∈ mtil p A θ) :
    sol X ∈ mhat p A θ :=
  mem_mhat_of_le_mtil hθ.prime hX (sol_le X)
    (sup_le (hX.2.trans (Thm41Aux.le_normalizer_sol X))
      (hX.1.1.trans (fun _ hg => Thm41Aux.mem_normalizer_sol_of_mem_normalizer hg)))

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
