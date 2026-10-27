module

public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction

public section

namespace CFSG.Sporadic.SchreierLemmas

open CFSG.LocalAnalysis.ComponentInitial

theorem isSolvable_pi_const {ι T : Type*} [Group T] (hT : Group.IsSolvable T) :
    Group.IsSolvable (ι → T) := by
  obtain ⟨n, hn⟩ := hT.solvable
  refine ⟨n, ?_⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext i
  have := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom (fun _ : ι => T) i) n
    (Subgroup.mem_map_of_mem _ hg)
  rw [hn, Subgroup.mem_bot] at this
  exact this

variable {L : Type*} [Group L]

theorem apply_mem_centralizer_of_mem_pointwiseFixingAut {Q : Subgroup L} {α : MulAut L}
    (hα : α ∈ pointwiseFixingAut Q) {t : L} (ht : t ∈ Subgroup.centralizer (Q : Set L)) :
    α t ∈ Subgroup.centralizer (Q : Set L) := by
  rw [Subgroup.mem_centralizer_iff] at ht ⊢
  intro q hq
  rw [← hα q hq, ← map_mul, ← map_mul, ht q hq]

theorem pointwiseFixingAut_le_pairAutSubgroup_centralizer (Q : Subgroup L) :
    pointwiseFixingAut Q ≤ pairAutSubgroup (Subgroup.centralizer (Q : Set L))
      (Subgroup.centralizer (Q : Set L)) := by
  intro α hα
  have h : (Subgroup.centralizer (Q : Set L)).map α.toMonoidHom =
      Subgroup.centralizer (Q : Set L) := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun t ht =>
      apply_mem_centralizer_of_mem_pointwiseFixingAut hα ht) fun t ht => ?_
    exact ⟨α⁻¹ t, apply_mem_centralizer_of_mem_pointwiseFixingAut (inv_mem hα) ht,
      α.apply_symm_apply t⟩
  exact ⟨h, h⟩

theorem centralizer_automorphism_kernel (Q : Subgroup L) [Q.Normal]
    (hT : Group.IsSolvable (Subgroup.centralizer (Q : Set L)))
    (hAT : Group.IsSolvable (MulAut (Subgroup.centralizer (Q : Set L)))) :
    (∀ α ∈ pointwiseFixingAut Q, (Subgroup.centralizer (Q : Set L)).map α.toMonoidHom =
      Subgroup.centralizer (Q : Set L)) ∧
    ∃ ρ : pointwiseFixingAut Q →* MulAut (Subgroup.centralizer (Q : Set L)),
      (∀ α t, (ρ α t : L) = (α : MulAut L) t) ∧
      (∃ f : ρ.ker →* (L → Subgroup.centralizer (Q : Set L)), Function.Injective f ∧
        ∀ α x, (f α x : L) = x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L) x) ∧
      Group.IsSolvable (pointwiseFixingAut Q) := by
  set T := Subgroup.centralizer (Q : Set L)
  have hle := pointwiseFixingAut_le_pairAutSubgroup_centralizer Q
  let ρ : pointwiseFixingAut Q →* MulAut T :=
    (pairAutRestrict T T).comp (Subgroup.inclusion hle)
  have hρ : ∀ α t, (ρ α t : L) = (α : MulAut L) t := fun _ _ => rfl
  have hfixT : ∀ α : ρ.ker, ∀ t ∈ T, ((α : pointwiseFixingAut Q) : MulAut L) t = t :=
    fun α t ht => by
      have h := DFunLike.congr_fun (MonoidHom.mem_ker.1 α.2) ⟨t, ht⟩
      exact congrArg Subtype.val h
  let f : ρ.ker →* (L → T) :=
    { toFun := fun α x => ⟨x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L) x,
        inv_mul_apply_mem_centralizer (α : pointwiseFixingAut Q).2 x⟩
      map_one' := funext fun x => Subtype.ext (by simp)
      map_mul' := fun α β => funext fun x => Subtype.ext (by
        have hβx := inv_mul_apply_mem_centralizer (β : pointwiseFixingAut Q).2 x
        have h := hfixT α _ hβx
        rw [map_mul, map_inv] at h
        change x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L)
            (((β : pointwiseFixingAut Q) : MulAut L) x) =
          x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L) x *
            (x⁻¹ * ((β : pointwiseFixingAut Q) : MulAut L) x)
        calc x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L)
              (((β : pointwiseFixingAut Q) : MulAut L) x) =
            x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L) x *
              ((((α : pointwiseFixingAut Q) : MulAut L) x)⁻¹ *
                ((α : pointwiseFixingAut Q) : MulAut L)
                  (((β : pointwiseFixingAut Q) : MulAut L) x)) := by
                group
          _ = _ := by rw [h]) }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro α hα
    refine Subtype.ext (Subtype.ext (MulEquiv.ext fun x => ?_))
    have h := congrArg Subtype.val (congrFun hα x)
    change x⁻¹ * ((α : pointwiseFixingAut Q) : MulAut L) x = 1 at h
    rw [inv_mul_eq_one] at h
    exact h.symm
  refine ⟨fun α hα => (hle hα).1, ρ, hρ, ⟨f, hf, fun _ _ => rfl⟩, ?_⟩
  have : Group.IsSolvable (L → T) := isSolvable_pi_const hT
  have : Group.IsSolvable ρ.ker := Group.isSolvable_of_isSolvable_injective hf
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ fun α hα => ⟨⟨α, hα⟩, rfl⟩

end CFSG.Sporadic.SchreierLemmas
